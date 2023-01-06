package org.ggp.base.player.gamer.statemachine.sample;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Set;

public class ReducedMCTNode {
	private int id;
	private StateNode stateTree;
	private Set<List<Integer>> stateSet;
	private List<Double> totalReward;
	private int numVisits;
	private int numParentVisits;
	private int numSiblings;
	private int numVisitsOld;
	private HashMap<List<List<Integer>>, Pair<List<Double>, Integer>> childData;

	public ReducedMCTNode(int id, StateNode stateTree, List<Double> totalReward, int numVisits, int numParentVisits, int numSiblings) {
		this.id = id;
		this.stateTree = stateTree;
		this.stateSet = null;
		this.totalReward = totalReward;
		this.numVisits = numVisits;
		this.numParentVisits = numParentVisits;
		this.numSiblings = numSiblings;
		this.numVisitsOld = -1;
		this.childData = new HashMap<List<List<Integer>>, Pair<List<Double>, Integer>>();
	}

	public ReducedMCTNode(int id, Set<List<Integer>> stateSet, List<Double> totalReward, int numVisits, int numParentVisits, int numSiblings) {
		this.id = id;
		this.stateTree = null;
		this.stateSet = stateSet;
		this.totalReward = totalReward;
		this.numVisits = numVisits;
		this.numParentVisits = numParentVisits;
		this.numSiblings = numSiblings;
		this.numVisitsOld = -1;
		this.childData = new HashMap<List<List<Integer>>, Pair<List<Double>, Integer>>();
	}

	public ReducedMCTNode(int id, Set<List<Integer>> stateSet, List<Double> totalReward, int numVisits, int numParentVisits, int numSiblings, int numVisitsOld) {
		this(id, stateSet, totalReward, numVisits, numParentVisits, numSiblings);
		this.numVisitsOld = numVisitsOld;
	}

	public ReducedMCTNode(MCTNode fullNode) {
		this.id =id -1;
		this.stateTree = null;
		this.stateSet = fullNode.getStateSet();
		this.totalReward = fullNode.getTotalReward();
		this.numVisits = fullNode.getNumVisits();
		this.numVisitsOld = fullNode.getNumVisitsOld();
		this.numParentVisits = fullNode.getTotalParentVisits();
		this.numSiblings = fullNode.getNumSiblings();
		this.childData = fullNode.produceChildData();
	}

	public void merge(ReducedMCTNode other) {
		if(!this.stateSet.equals(other.getStateSet())) {
			System.out.println("WARNING: Attempting to merge two ReducedMCTNodes with different IDs");
		}
		this.numVisits += other.numVisits;
		this.numVisitsOld += other.numVisitsOld;
		this.numParentVisits += other.numParentVisits;
		this.numSiblings = Math.max(this.numSiblings, other.numSiblings); //This may not always be exactly accurate, but it is a lot better than adding the numbers together
		for(int i=0;i<totalReward.size();i++) {
			this.totalReward.set(i, this.totalReward.get(i) + other.getTotalReward().get(i));
		}
		for(List<List<Integer>> otherMove : other.getChildData().keySet()) {
			if(!this.childData.containsKey(otherMove)) {
				this.childData.put(otherMove, other.getChildData().get(otherMove));
			} else {
				Pair<List<Double>, Integer> thisPair = this.childData.get(otherMove);
				Pair<List<Double>, Integer> otherPair = other.getChildData().get(otherMove);
				List<Double> newRewards = new ArrayList<Double>();
				for(int i=0;i<thisPair.getKey().size();i++) {
					newRewards.add(thisPair.getKey().get(i) + otherPair.getKey().get(i));
				}
				this.childData.put(otherMove, new Pair<List<Double>, Integer>(newRewards, thisPair.getValue()+otherPair.getValue()));
			}
		}
	}

	public int getID() {
		return id;
	}

	public StateNode getStateTree() {
		return stateTree;
	}

	public Set<List<Integer>> getStateSet() {
		return stateSet;
	}

	public List<Double> getTotalReward() {
		return totalReward;
	}

	public int getNumVisits() {
		return numVisits;
	}

	public int getNumVisitsOld() {
		return numVisitsOld;
	}

	public int getNumParentVisits() {
		return numParentVisits;
	}

	public int getNumSiblings() {
		return this.numSiblings;
	}

	public HashMap<List<List<Integer>>, Pair<List<Double>, Integer>> getChildData() {
		return childData;
	}

	public void putChildData(List<List<Integer>> moveCombo, Pair<List<Double>, Integer> newData) {
		childData.put(moveCombo, newData);
	}

	@Override
	public String toString() {
		String outStr = "id: " + this.id + "; total reward: " + this.totalReward + "; # visits: " + this.numVisits + "; # visits to parent: " + this.numParentVisits + "\n";
		if(MCTNode.STATE_TYPE == 0) {
			outStr += this.stateTree.toString();
		} else {
			outStr += this.stateSet.toString();
		}
		outStr += "\n" + childData;
		return outStr;
	}
}
