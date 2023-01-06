package org.ggp.base.player.gamer.statemachine.sample;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Set;

import org.ggp.base.util.statemachine.MachineState;
import org.ggp.base.util.statemachine.Move;
import org.ggp.base.util.statemachine.Role;
import org.ggp.base.util.statemachine.StateMachine;
import org.ggp.base.util.statemachine.exceptions.GoalDefinitionException;
import org.ggp.base.util.statemachine.exceptions.MoveDefinitionException;
import org.ggp.base.util.statemachine.exceptions.TransitionDefinitionException;

public class MCTNode {

	private MachineState state;
	private StateMachine machine;
	private StateMapping mapping;
	private StateNode stateTree;
	private StateNode mappedStateTree;
	private Set<List<Integer>> stateSet;
	private Set<List<Integer>> mappedStateSet;
	private ReducedMCTNode nearestSourceNode;
	private double percentSharedStates; //how similar is this node to it's nearest, as a percentage of shared state components
	private int whoseTurn; //-3 if state is terminal, -2 if more than 1 player has multiple choices, -1 if nobody has more than 1 choice, otherwise the role index of the sole player with multiple choices
	private int whoseTurn2P; //same as whoseTurn, but will attempt to resolve -2 or -1 by checking the parent and assuming it's a 2 player game
	private int numVisits;
	private List<Double> totalReward; //list items are rewards for each Role, indexed in the same order as the Roles
	private List<Integer> goals;
	private double transferTerm;
	private double transferDif;
	private HashMap<Role, List<Move>> possibleMoves;
	private HashMap<List<Move>, MCTNode> children;
	private List<MCTNode> parents;
	private int numParentVisitsOld; //If parent has been set to null, this should contain the number of visits at that time. -1 when unset. Only the root should have null parents and 0 for this value.
	private int numVisitsOld; //Num visits at the time parent was set to null. -1 when unset.
	private int numSiblings;
	private int depth;
	private List<Integer> nearestWin;
	private List<Integer> nearestLoss;
	private boolean isTerminal;
//	private Set<List<Integer>> terminalFacts;
	private boolean isExpanded;

	public static final double TRANSFER_TERM_SENTINEL = -9999;
	public static final int STATE_TYPE = 1;   //0 for state trees, 1 for lists of components. 0 is deprecated. Don't use 0.



	public MCTNode(MachineState state, StateMachine machine, StateMapping mapping, MCTNode parent) {
		this(state, machine, mapping, parent, mapping.genTargetStateSet(state));
	}

	public MCTNode(MachineState state, StateMachine machine, StateMapping mapping, MCTNode parent, Set<List<Integer>> stateSet) {
		this.state = state;
		this.machine = machine;
		this.mapping = mapping;
		if(STATE_TYPE == 0) {
			this.stateTree = mapping.genTargetStateTree(state);
			this.stateSet = null;
		} else {
			this.stateTree = null;
			this.stateSet = stateSet;
		}
		this.mappedStateTree = null;
		this.mappedStateSet = null;
		this.nearestSourceNode = null;
		this.percentSharedStates = 0;
		this.whoseTurn = MCTNode.determineWhoseTurn(this.machine, this.state);
		if(this.whoseTurn == -1 || this.whoseTurn == -2) {
			if(parent != null) {
				if(parent.getWhoseTurnAssume2P() == 0) {
					this.whoseTurn2P = 1;
				} else {
					this.whoseTurn2P = 0;
				}
			} else {
				this.whoseTurn2P = 0;
			}
		} else {
			this.whoseTurn2P = this.whoseTurn;
		}
		this.numVisits = 0;
		this.numVisitsOld = -1;
		this.nearestWin = new ArrayList<Integer>();
		this.nearestLoss = new ArrayList<Integer>();
		List<Role> allRoles = this.machine.getRoles();
		this.totalReward = new ArrayList<Double>();
		for(Role r : allRoles) {
			this.totalReward.add(0.0);
			this.nearestWin.add(-1);
			this.nearestLoss.add(-1);
		}
		this.goals = null;
		this.transferTerm = TRANSFER_TERM_SENTINEL;
		this.transferDif = TRANSFER_TERM_SENTINEL;
//		Set<GdlSentence> gdlTerminalFacts = machine.isTerminalAnswers(state);
//		this.isTerminal = gdlTerminalFacts != null;
//		if(this.isTerminal) {
//			this.terminalFacts = this.mapping.genTargetStateSet(gdlTerminalFacts);
//		}
		this.isTerminal = machine.isTerminal(state);

//		System.out.println(this.isTerminal + " " + gdlTerminalFacts);
//		if(this.isTerminal) {
//			System.out.println("* " + this.terminalFacts);
//		}
		this.isExpanded = false;

		this.possibleMoves = new HashMap<Role, List<Move>>();
//		long startTime = System.nanoTime();
		if(!isTerminal) {
			for(Role r : allRoles) {
				try {
					this.possibleMoves.put(r, machine.getLegalMoves(state, r));
				} catch (MoveDefinitionException e) {
					this.possibleMoves.put(r, null);
					System.out.println(e);
				}
			}
		}
//		long endTime = System.nanoTime();
//		System.out.println("All possible move time: " + (endTime-startTime));


		this.children = new HashMap<List<Move>, MCTNode>();
		this.numSiblings = 0;
		if(parent != null) {
			this.parents = new ArrayList<MCTNode>();
			this.parents.add(parent);
			this.numSiblings = parent.getChildren().keySet().size() - 1;
			this.numParentVisitsOld = -1;
			this.depth = parent.getDepth() + 1;
		} else {
			this.parents = null;
			this.numParentVisitsOld = 0;
			this.depth = 0;
		}
	}

	public int getWhoseTurn() {
		return this.whoseTurn;
	}

	public int getWhoseTurnAssume2P() {
		return this.whoseTurn2P;
	}

	public int getNumVisits() {
		return numVisits;
	}

	public void setNumVisits(int numVisits) {
		this.numVisits = numVisits;
	}

	public int getNumVisitsOld() {
		return this.numVisitsOld;
	}

	public List<Integer> getNearestWin() {
		return this.nearestWin;
	}

	public void setNearestWin(int newNearest, int roleIndex) {
		this.nearestWin.set(roleIndex, newNearest);
	}

	public List<Integer> getNearestLoss() {
		return this.nearestLoss;
	}

	public void setNearestLoss(int newNearest, int roleIndex) {
		this.nearestLoss.set(roleIndex, newNearest);
	}

	public List<Double> getTotalReward() {
		return totalReward;
	}

	public void setTotalReward(int index, double value) {
		this.totalReward.set(index, value);
	}

	public double getTransferTerm() {
		return transferTerm;
	}

	public void setTransferTerm(double transferTerm) {
		this.transferTerm = transferTerm;
	}

	public double getTransferDif() {
		return transferDif;
	}

	public void setTransferDif(double transferDif) {
		this.transferDif = transferDif;
	}

	public List<MCTNode> getParents() {
		return this.parents;
	}

	public int getNumSiblings() {
		return this.numSiblings;
	}

	public int getDepth() {
		return this.depth;
	}

	public void setParents(List<MCTNode> newParents) {
		if(newParents == null) {
			this.numParentVisitsOld = this.getTotalParentVisits();
			this.numVisitsOld = this.getNumVisits();
		}
		this.parents = newParents;
		if(newParents != null) {
			this.numSiblings = 0;
			for(MCTNode parent : newParents) {
				if(parent != null) {
					this.addParent(parent);
				}
			}
		}
	}

	public void addParent(MCTNode parent) {
		this.parents.add(parent);
		if(parent != null) {
			this.numSiblings = Math.max(this.numSiblings, parent.getChildren().keySet().size() - 1); //This is fast, but possibly inaccurate
		}
	}

	public MachineState getState() {
		return state;
	}

	public StateNode getStateTree() {
		return stateTree;
	}

	public Set<List<Integer>> getStateSet() {
		return stateSet;
	}

	public StateNode getMappedStateTree() {
		return mappedStateTree;
	}

	public Set<List<Integer>> getMappedStateSet() {
		return mappedStateSet;
	}

	public ReducedMCTNode getNearestSourceNode(StateMapping sMap) {
		if(this.nearestSourceNode == null) {
			this.nearestSourceNode = sMap.findNearestSourceState(this);
			int sharedComps = 0;
			for(List<Integer> comp : this.mappedStateSet) {
				if(this.nearestSourceNode.getStateSet().contains(comp)) {
					sharedComps++;
				}
			}
			this.percentSharedStates = ((double)sharedComps) / this.stateSet.size(); //deliberately using stateSet instead of mappedStateSet here
		}
		return this.nearestSourceNode;
	}

	public double getPercentSharedStates() {
		return this.percentSharedStates;
	}

	public HashMap<Role, List<Move>> getPossibleMoves() {
		return possibleMoves;
	}

	public HashMap<List<Move>, MCTNode> getChildren() {
		return children;
	}

	public boolean isTerminal() {
		return this.isTerminal;//machine.isTerminal(state);
	}

	public boolean isExpanded() {
		return isExpanded;
	}

	public void genStateSet() {
		if(this.stateSet == null) {
			this.stateSet = mapping.genTargetStateSet(this.state);
		}
	}

	//return the sum of visits to all parent nodes
	public int getTotalParentVisits() {
		int total = 0;
		if(this.parents != null) {
			for(MCTNode parent : this.parents) {
				total += parent.getNumVisits();
			}
		} else {
			total = this.numParentVisitsOld;
		}
		return total;
	}

	@Override
	public String toString() {
		String outStr = "total reward: " + this.totalReward + "; # visits: " + this.numVisits + "; transfer term: " + this.transferTerm + "; terminal?: " + this.isTerminal + "; expanded?: " + this.isExpanded + "\n";
		if(STATE_TYPE == 0) {
			outStr += this.stateTree.toString();
		} else {
			outStr += this.stateSet.toString();
		}
		return outStr;
	}


	//produce the child node data needed for a ReducedMCTNode
	public HashMap<List<List<Integer>>, Pair<List<Double>, Integer>> produceChildData() {
		HashMap<List<List<Integer>>, Pair<List<Double>, Integer>> result = new HashMap<List<List<Integer>>, Pair<List<Double>, Integer>>();
		for(List<Move> move : this.children.keySet()) {
			MCTNode currChild = this.children.get(move);
			if(currChild != null) {
				List<List<Integer>> convertedMoveSet = this.mapping.convertMoveToList(move);
				Pair<List<Double>, Integer> currChildData = new Pair<List<Double>, Integer>(currChild.getTotalReward(), currChild.getNumVisits());
				result.put(convertedMoveSet, currChildData);
			}
		}
		return result;
	}


	public boolean isChildFullyExpanded(List<Move> moveCombo) {
		return this.children.containsKey(moveCombo) && this.children.get(moveCombo) != null;
	}


	//Do the expensive work of fully expanding a child node, including advancing the state machine. (Costs around 1 ms each)
	public void fullyExpandChild(List<Move> moveCombo, HashMap<Set<List<Integer>>, MCTNode> existingNodes, boolean trackExisting) {
		try {
//			long startTime = System.nanoTime();
			MachineState nextState = machine.getNextState(this.state, moveCombo);
//			long endTime = System.nanoTime();
//    		System.out.println("Time: " + (endTime-startTime)/1000000000.0);
			Set<List<Integer>> nextStateSet = mapping.genTargetStateSet(nextState);
			MCTNode newChild;
			if(trackExisting) {
				if(existingNodes.containsKey(nextStateSet)) {
					newChild = existingNodes.get(nextStateSet);
					newChild.addParent(this);
				} else {
					newChild = new MCTNode(nextState, machine, mapping, this, nextStateSet);
					existingNodes.put(nextStateSet, newChild);
				}
			} else {
				newChild = new MCTNode(nextState, machine, mapping, this, nextStateSet);
			}
			children.put(moveCombo, newChild);
		} catch (TransitionDefinitionException e) {
			System.out.println("ERROR: Bad state transition in fullyExpandChildren.");
			System.out.println(state);
			System.out.print("(");
			for (Move m : moveCombo) {
				System.out.print(m + " ");
			}
			System.out.println(")");
		}
	}

	//This getter ensures that the requested child has been fully expanded (including expensive state machine update)
	public MCTNode getExpandedChild(List<Move> moveCombo, HashMap<Set<List<Integer>>, MCTNode> existingNodes, boolean trackExisting) {
		if(!isChildFullyExpanded(moveCombo)) {
			fullyExpandChild(moveCombo, existingNodes, trackExisting);
		}
		return this.children.get(moveCombo);
	}

	//Generate a spot in the children HashMap for all valid move combos, but don't actually generate the MCTNode yet.
	public void expandChildren() {
		if(!isTerminal && !this.isExpanded) {
			List<Role> allRoles = this.machine.getRoles();
			List<List<Move>> movesByRole = new ArrayList<List<Move>>();
			for(Role r : allRoles) {
				movesByRole.add(this.possibleMoves.get(r));
			}
			List<List<Move>> moveCombos = MyUtil.<Move>allCombinations(movesByRole);

			for (List<Move> combo : moveCombos) {
				children.put(combo, null);
			}
		}
		this.isExpanded = true;
	}

	public List<Integer> getGoals() {
		if(this.goals == null) {
			try {
				this.goals = machine.getGoals(state);
			} catch (GoalDefinitionException e) {
				System.out.println("ERROR in getGoals: Looking for goal in non-goal state.");
				e.printStackTrace();
			}
		}
		return this.goals;
	}

	public void genMappedState() {
		if(STATE_TYPE == 0) {
			if(mappedStateTree == null) {
				mappedStateTree = stateTree.deepCopy();
				mapping.mapTargetStateTreeToSource(mappedStateTree);
			}
		} else {
			if(mappedStateSet == null) {
				mappedStateSet = mapping.mapTargetStateSetToSource(stateSet);
			}
		}
	}

	//returns -3 if state is terminal, -2 if more than 1 player has multiple choices for moves, -1 if nobody has more than 1 choice, otherwise the role index of the sole player with multiple choices
	public static int determineWhoseTurn(StateMachine m, MachineState s) {
		int returnVal = -3;
		if(!m.isTerminal(s)) {
			List<Role> roles = m.getRoles();
			List<Integer> roleIndicesWithChoices = new ArrayList<Integer>();
			for(int i=0;i<roles.size();i++) {
				Role r = roles.get(i);
				try {
					List<Move> currMoves = m.getLegalMoves(s, r);
					if(currMoves.size() > 1) {
						roleIndicesWithChoices.add(i);
					}
				} catch (MoveDefinitionException e) {
					System.out.println(e);
				}
			}
			if(roleIndicesWithChoices.size() > 1) {
				returnVal = -2;
			} else if (roleIndicesWithChoices.size() == 0) {
				returnVal = -1;
			} else {
				returnVal = roleIndicesWithChoices.get(0);
			}
		}
		return returnVal;
	}

}
