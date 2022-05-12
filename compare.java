package ch.ethz.rse.numerical;

import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Set;

import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import apron.Abstract1;
import apron.ApronException;
import apron.Environment;
import apron.Manager;
import apron.MpqScalar;
import apron.Polka;
import apron.Tcons1;
import apron.Texpr1BinNode;
import apron.Texpr1CstNode;
import apron.Texpr1Intern;
import apron.Texpr1Node;
import apron.Texpr1VarNode;
import ch.ethz.rse.VerificationProperty;
import ch.ethz.rse.pointer.EventInitializer;
import ch.ethz.rse.pointer.PointsToInitializer;
import ch.ethz.rse.utils.Constants;
import ch.ethz.rse.verify.EnvironmentGenerator;
import soot.ArrayType;
import soot.DoubleType;
import soot.Local;
import soot.RefType;
import soot.SootHelper;
import soot.SootMethod;
import soot.Unit;
import soot.Value;
import soot.jimple.AddExpr;
import soot.jimple.BinopExpr;
import soot.jimple.ConditionExpr;
import soot.jimple.DefinitionStmt;
import soot.jimple.IfStmt;
import soot.jimple.IntConstant;
import soot.jimple.InvokeExpr;
import soot.jimple.MulExpr;
import soot.jimple.ParameterRef;
import soot.jimple.Stmt;
import soot.jimple.SubExpr;
import soot.jimple.internal.AbstractBinopExpr;
import soot.jimple.internal.JAddExpr;
import soot.jimple.internal.JArrayRef;
import soot.jimple.internal.JEqExpr;
import soot.jimple.internal.JGeExpr;
import soot.jimple.internal.JGotoStmt;
import soot.jimple.internal.JGtExpr;
import soot.jimple.internal.JIfStmt;
import soot.jimple.internal.JInstanceFieldRef;
import soot.jimple.internal.JInvokeStmt;
import soot.jimple.internal.JLeExpr;
import soot.jimple.internal.JLtExpr;
import soot.jimple.internal.JMulExpr;
import soot.jimple.internal.JNeExpr;
import soot.jimple.internal.JReturnVoidStmt;
import soot.jimple.internal.JSpecialInvokeExpr;
import soot.jimple.internal.JSubExpr;
import soot.jimple.internal.JVirtualInvokeExpr;
import soot.jimple.internal.JimpleLocal;
import soot.jimple.toolkits.annotation.logic.Loop;
import soot.toolkits.graph.LoopNestTree;
import soot.toolkits.graph.UnitGraph;
import soot.toolkits.scalar.ForwardBranchedFlowAnalysis;

/**
 * Convenience class running a numerical analysis on a given {@link SootMethod}
 */
public class NumericalAnalysis extends ForwardBranchedFlowAnalysis<NumericalStateWrapper> {

	private static final Logger logger = LoggerFactory.getLogger(NumericalAnalysis.class);

	/**
	 * the property we are verifying
	 */
	private final VerificationProperty property;

	/**
	 * True by default, becomes false if property is dissatisfied
	 */ 
	private boolean flag;

	/**
	 * the pointer analysis result we are verifying
	 */
	private final PointsToInitializer pointsTo;

	/**
	 * all event initializers encountered until now
	 */
	private Set<EventInitializer> alreadyInit;

	/**
	 * number of times this loop head was encountered during analysis
	 */
	private HashMap<Unit, IntegerWrapper> loopHeads = new HashMap<Unit, IntegerWrapper>();
	/**
	 * Previously seen abstract state for each loop head
	 */
	private HashMap<Unit, NumericalStateWrapper> loopHeadState = new HashMap<Unit, NumericalStateWrapper>();

	/**
	 * Numerical abstract domain to use for analysis: Convex polyhedra
	 */
	public final Manager man = new Polka(true);

	public final Environment env;

	/**
	 * We apply widening after updating the state at a given merge point for the
	 * {@link WIDENING_THRESHOLD}th time
	 */
	private static final int WIDENING_THRESHOLD = 6;

	/**
	 * 
	 * @param method   method to analyze
	 * @param property the property we are verifying
	 */
	public NumericalAnalysis(SootMethod method, VerificationProperty property, PointsToInitializer pointsTo) {
		super(SootHelper.getUnitGraph(method));
		System.out.println("Hello kind sir, I just created a NumericalAnalysis oh and the property is " + property.toString());
		UnitGraph g = SootHelper.getUnitGraph(method);

		this.property = property;

		this.pointsTo = pointsTo;

		this.alreadyInit = new HashSet<EventInitializer>();

		this.env = new EnvironmentGenerator(method, pointsTo).getEnvironment();
		this.flag = true;

		// initialize counts for loop heads
		for (Loop l : new LoopNestTree(g.getBody())) {
			loopHeads.put(l.getHead(), new IntegerWrapper(0));
		}

		// perform analysis by calling into super-class
		logger.info("Analyzing {} in {}", method.getName(), method.getDeclaringClass().getName());
		doAnalysis(); // calls newInitialFlow, entryInitialFlow, merge, flowThrough, and stops when a fixed point is reached
	}

	/**
	 * Report unhandled instructions, types, cases, etc.
	 * 
	 * @param task description of current task
	 * @param what
	 */
	public static void unhandled(String task, Object what, boolean raiseException) {
		String description = task + ": Can't handle " + what.toString() + " of type " + what.getClass().getName();

		if (raiseException) {
			logger.error("Raising exception " + description);
			throw new UnsupportedOperationException(description);
		} else {
			logger.error(description);

			// print stack trace
			StackTraceElement[] stackTrace = Thread.currentThread().getStackTrace();
			for (int i = 1; i < stackTrace.length; i++) {
				logger.error(stackTrace[i].toString());
			}
		}
	}

	@Override
	protected void copy(NumericalStateWrapper source, NumericalStateWrapper dest) {
		source.copyInto(dest);
	}

	@Override
	protected NumericalStateWrapper newInitialFlow() {
		// should be bottom (only entry flows are not bottom originally)
		return NumericalStateWrapper.bottom(man, env);
	}

	@Override
	protected NumericalStateWrapper entryInitialFlow() {
		// state of entry points into function
		NumericalStateWrapper ret = NumericalStateWrapper.top(man, env);

		// TODO: MAYBE FILL THIS OUT

		return ret;
	}

	@Override
	protected void merge(Unit succNode, NumericalStateWrapper w1, NumericalStateWrapper w2, NumericalStateWrapper w3) {
		// merge the two states from w1 and w2 and store the result into w3
		logger.debug("in merge: " + succNode);
		IntegerWrapper counter = loopHeads.get(succNode);
		Abstract1 a1 = w1.get();
		Abstract1 a2 = w2.get();
		Abstract1 a3 = w3.get(); //We need to initialise otherwise setting w3 to a3 crashes
		try{ //joinCopy can throw ApronExpection
			if(counter==null || counter.value < WIDENING_THRESHOLD){
				//We've never seen this loop, or not often enough to apply widening
				a3 = a1.joinCopy(man, a2); 
				w3.set(a3);
			}else{
				//We are tired of this boring loop and we reached WIDENING_THRESHOLD
				a3 = a1.widening(man, a2);
			}
		}catch(ApronException e){
			System.out.println("Well... uhm this is awkward, idk how to handle this :/");
			e.printStackTrace(); //TODO: idk honestly maybe check if we can assume that this should never happen 
		}
	}

	@Override
	protected void merge(NumericalStateWrapper src1, NumericalStateWrapper src2, NumericalStateWrapper trg) {
		// this method is never called, we are using the other merge instead
		throw new UnsupportedOperationException();
	}

	@Override
	protected void flowThrough(NumericalStateWrapper inWrapper, Unit op, List<NumericalStateWrapper> fallOutWrappers,
			List<NumericalStateWrapper> branchOutWrappers) {
		logger.debug(inWrapper + " " + op + " => ?");

		Stmt s = (Stmt) op;

		// fallOutWrapper is the wrapper for the state after running op,
		// assuming we move to the next statement. Do not overwrite
		// fallOutWrapper, but use its .set method instead
		assert fallOutWrappers.size() <= 1;
		NumericalStateWrapper fallOutWrapper = null;
		if (fallOutWrappers.size() == 1) {
			fallOutWrapper = fallOutWrappers.get(0);
			inWrapper.copyInto(fallOutWrapper);
		}

		// branchOutWrapper is the wrapper for the state after running op,
		// assuming we follow a conditional jump. It is therefore only relevant
		// if op is a conditional jump. In this case, (i) fallOutWrapper
		// contains the state after "falling out" of the statement, i.e., if the
		// condition is false, and (ii) branchOutWrapper contains the state
		// after "branching out" of the statement, i.e., if the condition is
		// true.
		assert branchOutWrappers.size() <= 1;
		NumericalStateWrapper branchOutWrapper = null;
		if (branchOutWrappers.size() == 1) {
			branchOutWrapper = branchOutWrappers.get(0);
			inWrapper.copyInto(branchOutWrapper);
		}

		try {
			if (s instanceof DefinitionStmt) {
				// handle assignment

				DefinitionStmt sd = (DefinitionStmt) s;
				Value left = sd.getLeftOp();
				Value right = sd.getRightOp();
				// We are not handling these cases:
				if (!(left instanceof JimpleLocal)) {
					unhandled("Assignment to non-local variable", left, true);
				} else if (left instanceof JArrayRef) {
					unhandled("Assignment to a non-local array variable", left, true);
				} else if (left.getType() instanceof ArrayType) {
					unhandled("Assignment to Array", left, true);
				} else if (left.getType() instanceof DoubleType) {
					unhandled("Assignment to double", left, true);
				} else if (left instanceof JInstanceFieldRef) {
					unhandled("Assignment to field", left, true);
				}

				if (left.getType() instanceof RefType) {
					// assignments to references are handled by pointer analysis
					// no action necessary
				} else {
					// handle assignment
					handleDef(fallOutWrapper, left, right);
				}

			} else if (s instanceof JIfStmt) {
				// handle if
				JIfStmt j = (JIfStmt) s;
				BinopExpr cond = (BinopExpr)j.getCondition();
				Value left = cond.getOp1();
				Value right = cond.getOp2();
				Abstract1 n_fallout = fallOutWrapper.get();
				Abstract1 n_branchout = branchOutWrapper.get();
				Tcons1 constraint;
				Tcons1 constraint_neg;
				int opcode = 0, opcode_neg = 0;
				boolean swapops = false;
				//Deals only with with JEqExpr
				if(cond instanceof JEqExpr){
					opcode = Tcons1.EQ;
					opcode_neg = Tcons1.DISEQ;
				}
				else if(cond instanceof JGeExpr){
					opcode = Tcons1.SUPEQ;
					opcode_neg = Tcons1.SUP;
				}
				else if(cond instanceof JLeExpr){
					opcode = Tcons1.SUPEQ;
					opcode_neg = Tcons1.SUP;
					swapops = true;
				}
				else if(cond instanceof JGtExpr){
					opcode = Tcons1.SUPEQ;
					opcode_neg = Tcons1.SUP;
				}
				else if(cond instanceof JLtExpr){
					opcode = Tcons1.SUPEQ;
					opcode_neg = Tcons1.SUP;
					swapops = true;
				}
				Texpr1Node leftNode = eval(n_fallout, left);
				Texpr1Node rightNode = eval(n_fallout, right);
				Texpr1Node mergedNode = manageTexpr1Nodes(swapops, leftNode, rightNode);
				Texpr1Node mergedNode_neg = manageTexpr1Nodes(swapops, leftNode, rightNode);
				constraint = new Tcons1(env, opcode, mergedNode);
				constraint_neg = new Tcons1(env, opcode_neg, mergedNode_neg);
				if(n_fallout.satisfy(man, constraint)){
					List<NumericalStateWrapper> new_branchOutWrappers;
					new_branchOutWrappers = Collections.EMPTY_LIST;
					flowThrough(inWrapper, j.getTarget(), branchOutWrappers, new_branchOutWrappers);
				}
				else if(n_fallout.satisfy(man, constraint_neg)){
					//ye cool if statement won't be executed, no update neccesary. 
				}else{
					//part 1, if stmt taken
					Tcons1[] constraint_singleton = new Tcons1[]{constraint};
					Abstract1 a2 = new Abstract1(man, constraint_singleton);
					NumericalStateWrapper w2 = new NumericalStateWrapper(man, a2);
					merge(j.getTarget(), branchOutWrapper, w2, branchOutWrapper);						

					List<NumericalStateWrapper> new_branchOutWrappers;
					new_branchOutWrappers = Collections.EMPTY_LIST;
					flowThrough(inWrapper, j.getTarget(), branchOutWrappers, new_branchOutWrappers);

					//part 2, if stmt not taken
					Tcons1[] constraint_negated_singleton = new Tcons1[]{constraint};
					Abstract1 a2_negated = new Abstract1(man, constraint_negated_singleton);
					NumericalStateWrapper w2_negated = new NumericalStateWrapper(man, a2_negated);
					merge(op, fallOutWrapper, w2_negated, fallOutWrapper); //maybe change op if debugging necessary
				}

				// TODO: FILL THIS OUT hahagit p

			} else if (s instanceof JInvokeStmt) {
				// handle invocations
				JInvokeStmt jInvStmt = (JInvokeStmt) s;
				InvokeExpr invokeExpr = jInvStmt.getInvokeExpr();
				if (invokeExpr instanceof JVirtualInvokeExpr) {
					handleInvoke(jInvStmt, fallOutWrapper);
				} else if (invokeExpr instanceof JSpecialInvokeExpr) {
					// initializer for object
					handleInitialize(jInvStmt, fallOutWrapper);
				} else {
					unhandled("Unhandled invoke statement", invokeExpr, true);
				}
			} else if (s instanceof JGotoStmt) {
				// safe to ignore
			} else if (s instanceof JReturnVoidStmt) {
				// safe to ignore
			} else {
				unhandled("Unhandled statement", s, true);
			}

			// log outcome
			if (fallOutWrapper != null) {
				logger.debug(inWrapper.get() + " " + s + " =>[fallout] " + fallOutWrapper);
			}
			if (branchOutWrapper != null) {
				logger.debug(inWrapper.get() + " " + s + " =>[branchout] " + branchOutWrapper);
			}

		} catch (ApronException e) {
			throw new RuntimeException(e);
		}
	}

	/**
	 * Happens only if (invokeExpr instanceof JVirtualInvokeExpr) which happens only for new Event(s,e), so
	 * we want to remember the arguments.
	 * TODO: remember the object itself, as switchlights in handleInitialize would call this object and he has to
	 * know the arguments s,e too
	 */
	public void handleInvoke(JInvokeStmt jInvStmt, NumericalStateWrapper fallOutWrapper) throws ApronException {
		JVirtualInvokeExpr vie = (JVirtualInvokeExpr) jInvStmt.getInvokeExpr();
		int args_len = vie.getArgs().size();
		if(args_len != 1) System.out.println("Hmmm there is a little more to it than I thought :(");
		System.out.println("handleInvoke moment hermanito 2.");
	}

	public void handleInitialize(JInvokeStmt jInvStmt, NumericalStateWrapper fallOutWrapper) throws ApronException {
		JSpecialInvokeExpr sie = (JSpecialInvokeExpr) jInvStmt.getInvokeExpr();
		//Assumes there were two arguments, s and e.
		if(sie.getArgs().size()<2){
			return;
		}
		System.out.println("hurray");
		Value s = sie.getArg(0); 
		Value e = sie.getArg(1);
		Abstract1 n = fallOutWrapper.get();
		Texpr1Node startNode = eval(n,s);
		Texpr1Node endNode = eval(n, e);
		Texpr1Node mergedNode = manageTexpr1Nodes(false, startNode, startNode);
		if(startNode == null) System.out.println("startnode null");
		if(endNode == null) System.out.println("endnode null");
		if(mergedNode == null) System.out.println("merge null");
		Tcons1 constraint = new Tcons1(this.env, Tcons1.SUPEQ, mergedNode);
		System.out.println("Hello, life is amazing");
		if(property.toString().equals("START_END_ORDER")){
			flag = flag ? this.flag = n.satisfy(man, constraint) : false;
			System.out.println("property false though");
		}
	}

	// returns state of in after assignment
	private void handleDef(NumericalStateWrapper outWrapper, Value left, Value right) throws ApronException {
		Abstract1 n = outWrapper.copy().get();
		Environment e = n.getEnvironment();
		String x = left.toString();
		String[] integer_names = {x};
		String[] real_names = {};
		if(!e.hasVar(x)){ //I am proud of this line, however after implementing Environment Generator 
						 //it will never be run, and the genius behind it  will never be recognized :(
			e.add(integer_names, real_names);
		}
		//evaluates rhs
		Texpr1Node rhs = eval(n, right);
		Texpr1Intern rhhs = new Texpr1Intern(e, rhs);
		//Assigns rhs to lhs
		outWrapper.set(n.assignCopy(man, x, rhhs, null));
	}

	//Translates nested Jimple Expressions to an Apron Environment
	private Texpr1Node eval(Abstract1 n, Value right){
		if(right instanceof IntConstant){
			return new Texpr1CstNode(new MpqScalar( ((IntConstant)right).value));
		}
		else if(right instanceof JimpleLocal){
			return new Texpr1VarNode( ((JimpleLocal)right).getName());
		}
		else if(right instanceof JMulExpr){
			Value op1 = ((JMulExpr)right).getOp1();
			Value op2 = ((JMulExpr)right).getOp2();
			return new Texpr1BinNode(Texpr1BinNode.OP_MUL, Texpr1BinNode.RTYPE_INT, Texpr1BinNode.RDIR_ZERO, eval(n,op1),eval(n,op2) );
		}
		else if(right instanceof JSubExpr){
			Value op1 = ((JSubExpr)right).getOp1();
			Value op2 = ((JSubExpr)right).getOp2();
			return new Texpr1BinNode(Texpr1BinNode.OP_SUB, Texpr1BinNode.RTYPE_INT, Texpr1BinNode.RDIR_ZERO, eval(n,op1),eval(n,op2) );
		}
		else if(right instanceof JAddExpr){
			Value op1 = ((JAddExpr)right).getOp1();
			Value op2 = ((JAddExpr)right).getOp2();
			return new Texpr1BinNode(Texpr1BinNode.OP_ADD, Texpr1BinNode.RTYPE_INT, Texpr1BinNode.RDIR_ZERO, eval(n,op1),eval(n,op2) );
		}
		return null;
	}

	private Texpr1Node manageTexpr1Nodes(boolean flag, Texpr1Node left, Texpr1Node right){
		Texpr1Node mergedNode = 
		flag ? 
		new Texpr1BinNode(Texpr1BinNode.OP_SUB, Texpr1BinNode.RTYPE_INT, Texpr1BinNode.RDIR_ZERO, right, left)
		:
		new Texpr1BinNode(Texpr1BinNode.OP_SUB, Texpr1BinNode.RTYPE_INT, Texpr1BinNode.RDIR_ZERO, left, right);
		return mergedNode;
	}

	public boolean getFlag(){
		return this.flag;
	}



	// TODO: MAYBE FILL THIS OUT: add convenience methods
}
