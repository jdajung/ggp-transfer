package org.ggp.base.player.gamer.statemachine.sample;

import java.io.File;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.LinkedList;
import java.util.List;
import java.util.Random;
import java.util.Set;
import java.util.TreeSet;

public class MCTMerger {

	public static int MAX_NODES = 10000;  //Number of nodes archived
	public static String PRIORITY_TYPE = "visits";  //options are: "visits", "non_monoscore", "random"
	public static String SAVE_FILE_NAME = "MCT_combined.txt";
	public static int MAX_FILES = 16;  //Number of MCT files to combine
	public static Random rand = new Random(3769460674928934938L);


	// This method is described by the "Archiving Information" subsection of the "Method" section of the paper
	// It combines MCT nodes saved during different game instances and saves those that are have the highest priority
	public static void main(String[] args) {
		LinkedList<ReducedMCTree> trees = new LinkedList<ReducedMCTree>();

    	File folder = new File(TestGamer.MCT_SAVE_DIR);
    	File[] listOfFiles = folder.listFiles();
    	List<String> fileNames = new LinkedList<String>();
    	int totalNodes = 0;

    	for (File file : listOfFiles) {
    	    if (file.isFile()) {
    	    	String name = file.getName();
    	    	if(name.length() >= 5 && Character.isDigit(name.charAt(4))) {
    	    		fileNames.add(name);
    	    	}
    	    }
    	}

    	for(String name : fileNames) {
    		if(trees.size() < MAX_FILES) {
	    		ReducedMCTree newTree = new ReducedMCTree();
	    		newTree.loadStatesFromFile(TestGamer.MCT_SAVE_DIR + "/" + name);
	    		trees.add(newTree);
    		} else {
    			break;
    		}
    	}

    	System.out.println("Found " + trees.size() + " MCT files.");

    	TreeSet<MCTMerger.PriorityItem<ReducedMCTNode>> sorted = new TreeSet<MCTMerger.PriorityItem<ReducedMCTNode>>();
    	List<HashMap<List<Integer>, Pair<Double, Long>>> allSpec = new ArrayList<HashMap<List<Integer>, Pair<Double, Long>>>();
    	List<HashMap<Integer, Pair<Double, Long>>> allGen = new ArrayList<HashMap<Integer, Pair<Double, Long>>>();
    	HashMap<Set<List<Integer>>, ReducedMCTNode> allNodes = new HashMap<Set<List<Integer>>, ReducedMCTNode>();

    	for(ReducedMCTree currTree : trees) {
    		totalNodes += currTree.getStates().size();
    		List<HashMap<List<Integer>, Pair<Double, Long>>> currSpec = currTree.getSpecificMoveTotalData();
    		List<HashMap<Integer, Pair<Double, Long>>> currGen = currTree.getGeneralMoveTotalData();
    		ArrayList<ReducedMCTNode> currNodes = currTree.getStates();

    		for(int i=0;i<currSpec.size();i++) {
    			if(allSpec.size()<=i) {
    				allSpec.add(new HashMap<List<Integer>, Pair<Double, Long>>());
    				allGen.add(new HashMap<Integer, Pair<Double, Long>>());
    			}

    			for(List<Integer> move : currSpec.get(i).keySet()) {
    				if(!allSpec.get(i).containsKey(move)) {
    					allSpec.get(i).put(move, currSpec.get(i).get(move));
    				} else {
    					Pair<Double, Long> oldPair = allSpec.get(i).get(move);
    					Pair<Double, Long> currPair = currSpec.get(i).get(move);
    					Pair<Double, Long> newPair = new Pair<Double, Long>(oldPair.getKey() + currPair.getKey(), oldPair.getValue() + currPair.getValue());
    					allSpec.get(i).put(move, newPair);
    				}
    			}

    			for(int move : currGen.get(i).keySet()) {
    				if(!allGen.get(i).containsKey(move)) {
    					allGen.get(i).put(move, currGen.get(i).get(move));
    				} else {
    					Pair<Double, Long> oldPair = allGen.get(i).get(move);
    					Pair<Double, Long> currPair = currGen.get(i).get(move);
    					Pair<Double, Long> newPair = new Pair<Double, Long>(oldPair.getKey() + currPair.getKey(), oldPair.getValue() + currPair.getValue());
    					allGen.get(i).put(move, newPair);
    				}
    			}
    		}

			for(ReducedMCTNode node : currNodes) {
				if(!allNodes.containsKey(node.getStateSet())) {
					allNodes.put(node.getStateSet(), node);
				} else {
					allNodes.get(node.getStateSet()).merge(node);
				}
			}
		}

		int maxVisits = 0;
		for(ReducedMCTNode node : allNodes.values()) {
			if(node.getNumVisits() > maxVisits) {
				maxVisits = node.getNumVisits();
			}
		}
		for(ReducedMCTNode node : allNodes.values()) {
			sorted.add(new PriorityItem<ReducedMCTNode>(priorityScore(node, maxVisits), node));
    		if(MAX_NODES >= 0 && sorted.size() > MAX_NODES) {
    			sorted.pollLast();  //bump the lowest priority node
    		}
		}

    	ArrayList<ReducedMCTNode> finalNodes = new ArrayList<ReducedMCTNode>();
    	for(PriorityItem<ReducedMCTNode> curr : sorted) {
    		finalNodes.add(curr.item);
    	}
    	ReducedMCTree finalTree = new ReducedMCTree(finalNodes, allSpec, allGen);

    	System.out.println("Saving " + sorted.size() + " nodes out of " + totalNodes + ".");
    	finalTree.saveToFile(SAVE_FILE_NAME);
    	System.out.println("Finished merging MCT data.");
	}


	//assigns a score to the given MCTNode
    //nodes with a higher score will prioritized for saving to file
    private static float priorityScore(ReducedMCTNode node, int maxVisits) {
    	float result = 0;

    	float visit_priority = 1.0f;

    	result += visit_priority*(node.getNumVisits()/((double)maxVisits));

    	//TODO: make this not reliant on zero-sumness
    	if(PRIORITY_TYPE.equals("non_monoscore")) {
	    	boolean zeroScore = false;
	    	for(int i=0;i<node.getTotalReward().size();i++) {
	    		if(node.getTotalReward().get(i) == 0) {
	    			zeroScore = true;
	    		}
	    	}
	    	if(zeroScore) {
	    		result /= 1e20;
	    	}
    	}

    	if(PRIORITY_TYPE.equals("random")) { //override priority with a random float in [0-1]
    		result = rand.nextFloat();
    	}

    	return result;
    }


	public static class PriorityItem<T> implements Comparable<PriorityItem> {

    	public float priority;
    	public T item;

    	public PriorityItem(float priority, T item) {
    		this.priority = priority;
    		this.item = item;
    	}

		@Override
		public int compareTo(PriorityItem o) {
			Float oPr = o.priority;
			int result = oPr.compareTo(this.priority);
			if(result != 0) {
				return result;
			} else {
				return -1; //if compareTo returns 0, a TreeSet won't store our new item
			}
		}

		@Override
		public String toString() {
			return "PriorityItem [priority=" + priority + ", item=" + item + "]";
		}

    }
}