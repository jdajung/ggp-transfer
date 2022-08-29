package org.ggp.base.player.gamer.statemachine.sample;

import java.util.ArrayList;
import java.util.Random;

import org.ggp.base.player.gamer.statemachine.sample.RuleGraph.RuleNodeColour;

public class RuleGraphDestroyer {
	private RuleGraph g;
	private ArrayList<RuleNode> nonNumberOccs;
	private ArrayList<RuleNode> numberOccs;
	private ArrayList<RuleNode> nonTopLevelNodes;
	private ArrayList<RuleNode> removedNodes;
	private ArrayList<RuleNode> addedNodes;
	long randomSeed;
	Random rand;

	public RuleGraphDestroyer(RuleGraph g, long randomSeed) {
		this.g = g;
		this.nonNumberOccs = new ArrayList<RuleNode>();
		this.numberOccs = new ArrayList<RuleNode>();
		this.nonTopLevelNodes = new ArrayList<RuleNode>();
		this.removedNodes = new ArrayList<RuleNode>();
		this.addedNodes = new ArrayList<RuleNode>();
		this.randomSeed = randomSeed;
		this.rand = new Random(randomSeed);

		ArrayList<RuleNode> allNodes = g.getGraph();
		for(RuleNode currNode : allNodes) {
			if(currNode.getColour() == RuleNodeColour.FN_OC || currNode.getColour() == RuleNodeColour.PRED_OC) {
				if(MyUtil.isNat(currNode.getName())) {
					this.numberOccs.add(currNode);
				} else {
					this.nonNumberOccs.add(currNode);
				}
			}

			if(!g.getTopLevelNonVarIds().contains(currNode.getId())) {
				this.nonTopLevelNodes.add(currNode);
			}
		}
	}

	//Note: this will leave the parents' childColourNums field invalid, but it's deprecated anyway
	public void removeNonTopLevelNode(RuleNode toRemove) {
		this.removedNodes.add(toRemove);
		for(RuleNode parent : toRemove.getParents()) {
			parent.getChildren().remove(toRemove);
		}
		for(RuleNode child : toRemove.getChildren()) {
			child.getParents().remove(toRemove);
		}
		if(toRemove.getColour() == RuleNodeColour.FN_OC || toRemove.getColour() == RuleNodeColour.PRED_OC) {
			if(nonNumberOccs.contains(toRemove)) {
				nonNumberOccs.remove(toRemove);
			} else if(numberOccs.contains(toRemove)) {
				numberOccs.remove(toRemove);
			}
		}
		if(nonTopLevelNodes.contains(toRemove)) {
			nonTopLevelNodes.remove(toRemove);
		}
//		this.g.getGraph().remove(toRemove);
	}

	public void removeRandomNonTopLevelNode() {
		if(nonTopLevelNodes.size() > 0) {
			int removeIndex = rand.nextInt(nonTopLevelNodes.size());
			RuleNode toRemove = nonTopLevelNodes.get(removeIndex);
			removeNonTopLevelNode(toRemove);
		} else {
			System.out.println("ERROR: removeRandomNonTopLevelNode has no nodes left to remove");
		}
	}

	public void removeRandomNonNumberOccNode() {
		if(nonNumberOccs.size() > 0) {
			int removeIndex = rand.nextInt(nonNumberOccs.size());
			RuleNode toRemove = nonNumberOccs.get(removeIndex);
			removeNonTopLevelNode(toRemove);
		} else {
			System.out.println("ERROR: removeRandomNonNumberOccNode has no nodes left to remove");
		}
	}

	public int removeNNonTopLevel(int n) {
		int numRemoved = 0;
		if(n > nonTopLevelNodes.size()) {
			System.out.println("WARNING: removeNNonTopLevel can only remove " + nonTopLevelNodes.size() + " of the requested " + n + " nodes");
		}
		while(!nonTopLevelNodes.isEmpty() && numRemoved < n) {
			removeRandomNonTopLevelNode();
			numRemoved++;
		}
		return numRemoved;
	}

	public int removeNNonNumberOcc(int n) {
		int numRemoved = 0;
		if(n > nonNumberOccs.size()) {
			System.out.println("WARNING: removeNNonNumberOcc can only remove " + nonNumberOccs.size() + " of the requested " + n + " nodes");
		}
		while(!nonNumberOccs.isEmpty() && numRemoved < n) {
			removeRandomNonNumberOccNode();
			numRemoved++;
		}
		return numRemoved;
	}

	public void duplicateNonTopLevelNode(RuleNode toDup) {
		RuleNode dupedNode = new RuleNode(g.nextID(),toDup.getName(),toDup.getArgNum(),toDup.getColour());
		for(RuleNode parent : toDup.getParents()) {
			parent.addChild(dupedNode);
			dupedNode.addParent(parent);
		}
		for(RuleNode child : toDup.getChildren()) {
			child.addParent(dupedNode);
			dupedNode.addChild(child);
		}
		this.addedNodes.add(dupedNode);
//		this.g.getGraph().add(dupedNode);
	}

	public void duplicateRandomNonTopLevelNode() {
		int dupIndex = rand.nextInt(nonTopLevelNodes.size());
		RuleNode toDup = nonTopLevelNodes.get(dupIndex);
		duplicateNonTopLevelNode(toDup);
	}

	public void duplicateRandomNonNumberOcc() {
		int dupIndex = rand.nextInt(nonNumberOccs.size());
		RuleNode toDup = nonNumberOccs.get(dupIndex);
		duplicateNonTopLevelNode(toDup);
	}

	public void duplicateNNonTopLevel(int n) {
		for(int i=0;i<n;i++) {
			duplicateRandomNonTopLevelNode();
		}
	}

	public void duplicateNNonNumberOcc(int n) {
		for(int i=0;i<n;i++) {
			duplicateRandomNonNumberOcc();
		}
	}
}
