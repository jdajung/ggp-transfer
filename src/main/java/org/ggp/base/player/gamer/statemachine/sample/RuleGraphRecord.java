package org.ggp.base.player.gamer.statemachine.sample;

import java.io.BufferedReader;
import java.io.BufferedWriter;
import java.io.File;
import java.io.FileReader;
import java.io.FileWriter;
import java.io.IOException;
import java.util.ArrayList;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Scanner;
import java.util.Set;
import java.util.StringTokenizer;

import org.ggp.base.player.gamer.statemachine.sample.RuleGraph.RuleNodeColour;

public class RuleGraphRecord {
	public static final int BUFFER_SIZE = 1048576;
	private ArrayList<RuleNode> ruleGraph;
	private ArrayList<Integer> topLevelNonVarIds;
	private HashSet<Integer> numberIDs;
	private List<Pair<Integer,List<Integer>>> numberIDChains; //key of pair is the ID of the successor function, value contains the ordered chain of number IDs
	private List<Integer> roleIds;

	public RuleGraphRecord() {
		this.ruleGraph = null;
		this.topLevelNonVarIds = null;
		this.numberIDs = new HashSet<Integer>();
		this.numberIDChains = new ArrayList<Pair<Integer,List<Integer>>>();
		this.roleIds = null;
	}

	public RuleGraphRecord(RuleGraph ruleGraph) {
		this.ruleGraph = ruleGraph.getGraph();
		this.topLevelNonVarIds = ruleGraph.getTopLevelNonVarIds();
		this.numberIDs = new HashSet<Integer>();
		this.numberIDChains = new ArrayList<Pair<Integer,List<Integer>>>();
		this.roleIds = ruleGraph.getRoleIds();

		this.numberIDs = ruleGraph.getNumberIDs();
		this.numberIDChains = ruleGraph.getNumberIDChains();
//		HashSet<String> numberNames = ruleGraph.getNumberNames();
//		List<Pair<String,List<String>>> numberNameChains = ruleGraph.getNumberChains();
//		HashMap<String, Integer> lookup = ruleGraph.getTopLevelNames();
//		for(String name : numberNames) {
//			this.numberIDs.add(lookup.get(name));
//		}
//		for(Pair<String,List<String>> chain : numberNameChains) {
//			int fnID = lookup.get(chain.getKey());
//			List<Integer> chainIDs = new ArrayList<Integer>();
//			for(String name : chain.getValue()) {
//				chainIDs.add(lookup.get(name));
//			}
//			this.numberChains.add(new Pair<Integer,List<Integer>>(fnID, chainIDs));
//		}
	}


	public void loadFromFile(String inFileName) {
		loadFromFile(inFileName, false);
	}

	public void loadFromFile(String inFileName, boolean debug) {
		ruleGraph = new ArrayList<RuleNode>();
		topLevelNonVarIds = new ArrayList<Integer>();
		roleIds = new ArrayList<Integer>();
		Scanner s = null;
		RuleNodeColour[] colourArr = RuleNodeColour.values();
		HashMap<Integer, Set<Integer>> childMap = new HashMap<Integer, Set<Integer>>();

        try {
            s = new Scanner(new BufferedReader(new FileReader(inFileName), BUFFER_SIZE));
            int lineIndex = 0;

            while (s.hasNext()) {
                String line = s.nextLine();
                if(line.length() > 0) {
	                StringTokenizer tok = new StringTokenizer(line);
	                if(lineIndex == 0) { //at top of file, read in IDs corresponding to roles
	                	while(tok.hasMoreTokens()) {
	                		this.roleIds.add(Integer.parseInt(tok.nextToken()));
	                	}

	                } else if(lineIndex == 1) { //line of number IDs
	                	while(tok.hasMoreTokens()) {
	                		this.numberIDs.add(Integer.parseInt(tok.nextToken()));
	                	}

	                } else if(lineIndex == 2) { //line of number ID chains, where first of each group is the successor function ID
	                	int fnName = -1;
	                	List<Integer> chain = new ArrayList<Integer>();
	                	while(tok.hasMoreTokens()) {
	                		String currTok = tok.nextToken();
	                		if(!currTok.equals("*")) {
	                			if(fnName == -1) {
	                				fnName = Integer.parseInt(currTok);
	                			} else {
	                				chain.add(Integer.parseInt(currTok));
	                			}
	                		} else {
	                			this.numberIDChains.add(new Pair<Integer,List<Integer>>(fnName,chain));
	                			fnName = -1;
	                			chain = new ArrayList<Integer> ();
	                		}
	                	}
	                	this.numberIDChains.add(new Pair<Integer,List<Integer>>(fnName,chain));

	                } else { //now read in all of the rule graph nodes
		                int newID = Integer.parseInt(tok.nextToken());
		                RuleNodeColour newColour = colourArr[Integer.parseInt(tok.nextToken())];
		                RuleNode newNode;
		                if(!debug) {
		                	newNode = new RuleNode(newID, newColour);
		                } else {
		                	String newName = tok.nextToken();
		                	int newArgNum = Integer.parseInt(tok.nextToken());
		                	newNode = new RuleNode(newID, newName, newArgNum, newColour);
		                }
		                ruleGraph.add(newNode);

		                if(newColour == RuleNodeColour.NON_VAR_SYM_CONST || newColour == RuleNodeColour.NON_VAR_SYM_FUNC|| newColour == RuleNodeColour.NON_VAR_SYM_PROP || newColour == RuleNodeColour.NON_VAR_SYM_RELATION) {
		                	topLevelNonVarIds.add(newID);
		                }

		                childMap.put(newID, new HashSet<Integer>());
		                while(tok.hasMoreTokens()) {
		                	int childID = Integer.parseInt(tok.nextToken());
		                	childMap.get(newID).add(childID);
		                }
	                }
	                lineIndex++;
                }
            }

	        for (RuleNode node : ruleGraph) {
	        	Set<Integer> childSet = childMap.get(node.getId());
	        	for (Integer childNum : childSet) {
	        		node.addChild(ruleGraph.get(childNum.intValue()));
	        	}
	        }
        } catch (Exception e) {
            e.printStackTrace();
        } finally {
            if (s != null) {
                s.close();
            }
        }
	}


	public void saveToFile(String outFileName) {
		saveToFile(outFileName, false);
	}

	public void saveToFile(String outFileName, boolean debug) {
		if(ruleGraph == null) {
			System.out.println("ERROR in saveToFile: rule graph has not been initialized.");
		}

		String outStr = "";

		//print IDs corresponding to roles at the top of the file, in the same order as they are indexed for goals, etc.
		for(int rid : this.roleIds) {
			outStr += rid + " ";
		}
		outStr += "\n";

		//print number IDs and number chains
		for(int numID : this.numberIDs) {
			outStr += numID + " ";
		}
		outStr += "\n";
		boolean firstChain = true;
		for(Pair<Integer,List<Integer>> chain : this.numberIDChains) {
			if(!firstChain) {
				outStr += "* ";
			}
			firstChain = false;
			outStr += chain.getKey() + " ";
			for(int id : chain.getValue()) {
				outStr += id + " ";
			}
		}
		outStr += "\n";

		//print all nodes in Rule Graph
		for (RuleNode node : ruleGraph) {
			outStr += node.getId() + " " + node.getColour().getVal() + " ";
			if(debug) {
				outStr += node.getName() + " " + node.getArgNum() + " ";
			}
//			HashMap<RuleNodeColour, Integer> childColourNums = node.getChildColourNums();
//			for(RuleNodeColour colour : RuleNodeColour.values()) {
//				outStr += childColourNums.get(colour) + " ";
//			}
			for (RuleNode child : node.getChildren()) {
				outStr += child.getId() + " ";
			}
			outStr += "\n";
		}

		File file = new File(outFileName);
        FileWriter fr = null;
        BufferedWriter br = null;
        try{
            fr = new FileWriter(file);
            br = new BufferedWriter(fr, BUFFER_SIZE);
            br.write(outStr);
        } catch (IOException e) {
            e.printStackTrace();
        } finally {
            try {
                br.close();
                fr.close();
            } catch (IOException e) {
                e.printStackTrace();
            }
        }
	}


	public ArrayList<RuleNode> getGraph() {
		if(ruleGraph == null) {
			System.out.println("ERROR in getGraph: rule graph has not been initialized.");
		}
		return ruleGraph;
	}

	public ArrayList<Integer> getTopLevelNonVarIds() {
		if(topLevelNonVarIds == null) {
			System.out.println("ERROR in getTopLevelNonVarIds: rule graph has not been initialized.");
		}
		return topLevelNonVarIds;
	}

	public HashSet<Integer> getNumberIDs() {
		return this.numberIDs;
	}

	public List<Pair<Integer,List<Integer>>> getNumberIDChains() {
		return this.numberIDChains;
	}

	public void printRuleGraphRecord() {
		System.out.println("Printing rule graph record...");
		for(RuleNode curr : ruleGraph) {
			System.out.println(curr);
			System.out.println();
		}
		System.out.println("Finished printing rule graph record.");
	}

	//produces the index of the given role ID if one exists, -1 otherwise
	public int getRoleIndex(int roleId) {
		int returnVal = -1;
		if(this.roleIds.contains(roleId)) {
			returnVal = this.roleIds.indexOf(roleId);
		}
		return returnVal;
	}

	//converts a state listed in IDs back to the human-readable names
	//used for debugging purposes
	public List<List<String>> stateIDsToStrings(Set<List<Integer>> stateIDs) {
		List<List<String>> stateStrs = new ArrayList<List<String>>();
		for(List<Integer> compIDs : stateIDs) {
			List<String> compStrs = new ArrayList<String>();
			for(int id : compIDs) {
				compStrs.add(this.ruleGraph.get(id).getName());
			}
			stateStrs.add(compStrs);
		}
		Collections.sort(stateStrs, new MyUtil.StringListComparator());
		return stateStrs;
	}

	//converts a state listed in IDs back to the human-readable names
	//used for debugging purposes
	public List<List<String>> moveIDsToStrings(List<List<Integer>> allMoves) {
		List<List<String>> moveStrs = new ArrayList<List<String>>();
		for(List<Integer> roleIDs : allMoves) {
			List<String> roleStrs = new ArrayList<String>();
			for(int id : roleIDs) {
				roleStrs.add(this.ruleGraph.get(id).getName());
			}
			moveStrs.add(roleStrs);
		}
		return moveStrs;
	}
}
