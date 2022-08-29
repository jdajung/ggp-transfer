package org.ggp.base.player.gamer.statemachine.sample;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;
import java.util.Set;

import org.ggp.base.util.gdl.grammar.Gdl;
import org.ggp.base.util.gdl.grammar.GdlConstant;
import org.ggp.base.util.gdl.grammar.GdlDistinct;
import org.ggp.base.util.gdl.grammar.GdlFunction;
import org.ggp.base.util.gdl.grammar.GdlLiteral;
import org.ggp.base.util.gdl.grammar.GdlNot;
import org.ggp.base.util.gdl.grammar.GdlOr;
import org.ggp.base.util.gdl.grammar.GdlProposition;
import org.ggp.base.util.gdl.grammar.GdlRelation;
import org.ggp.base.util.gdl.grammar.GdlRule;
import org.ggp.base.util.gdl.grammar.GdlTerm;
import org.ggp.base.util.gdl.grammar.GdlVariable;
import org.ggp.base.util.statemachine.Role;

public class RuleGraph {
	private static ArrayList<String> builtInArray = new ArrayList<String>(Arrays.asList("role", "base", "input", "init", "true", "does", "next", "legal", "goal", "terminal"));
	public static HashSet<String> builtIns = new HashSet<String>(builtInArray);
	public static final int MIN_NUMBER_CHAIN = 20;

	private List<Gdl> rules;
	private ArrayList<RuleNode> ruleGraph; //the whole rule graph
	private ArrayList<RuleNode> topLevel; //references to top level rather than occurrence vertices, used in step 3
	private HashMap<String, Integer> topLevelNames; //Names of nodes in the top level as keys, index in ruleGraph as values
	private ArrayList<Integer> topLevelNonVarIds;
	private HashSet<String> numberNames;
	private List<Pair<String,List<String>>> numberChains; //key of pair is the name of the successor function, value contains the ordered chain of number names
	private HashSet<Integer> numberIDs;
	private List<Pair<Integer,List<Integer>>> numberIDChains;
	private List<Role> roles;
	private List<Integer> roleIds; //IDs of symbols corresponding to roles, ordered the same way they are indexed for goals, etc.
//	private HashMap<String, HashSet<Integer>> nameTable; //records the IDs of all occurrences for a particular name
	private int nextID;


	public RuleGraph(List<Gdl> rules, List<Role> roles) {
		this.rules = rules;
		this.ruleGraph = null;
		this.topLevel = new ArrayList<RuleNode>();
		this.topLevelNames = new HashMap<String, Integer>();
		this.topLevelNonVarIds = null;
		this.numberNames = new HashSet<String>();
		this.numberChains = null;
		this.numberIDs = new HashSet<Integer>();
		this.numberIDChains = new ArrayList<Pair<Integer,List<Integer>>>();
		this.roles = roles;
		this.roleIds = null;
//		this.nameTable = new HashMap<String, HashSet<Integer>>();
		this.nextID = 0;
	}

	public enum RuleNodeType {
		LOG, PRED, FN, VAR
	}

	public enum RuleNodeColour {
		ENTAIL(0), DISTINCT(1), NOT(2), AND(3), OR(4), ROLE(5), BASE(6), INPUT(7), INIT(8), TRUE(9), DOES(10), NEXT(11), LEGAL(12), GOAL(13), TERMINAL(14), PRED_OC(15), FN_OC(16), VAR_OC(17), ARG(18), VAR_SYM(19), NON_VAR_SYM_PROP(20), NON_VAR_SYM_RELATION(21), NON_VAR_SYM_CONST(22), NON_VAR_SYM_FUNC(23), NUMBER_SYM(24);

		private final int val;

	    RuleNodeColour(int val) {
	        this.val = val;
	    }

	    public int getVal() {
	        return this.val;
	    }
	}

	public ArrayList<RuleNode> getGraph() {
		return this.ruleGraph;
	}


	public HashMap<String, Integer> getTopLevelNames() {
		return topLevelNames;
	}

	public ArrayList<Integer> getTopLevelNonVarIds() {
		if(this.topLevelNonVarIds == null) {
			this.topLevelNonVarIds = new ArrayList<Integer>();
			for(String name : this.topLevelNames.keySet()) {
				int currID = this.topLevelNames.get(name);
				RuleNode currNode = this.ruleGraph.get(currID);
				if(currNode.getColour() != RuleNodeColour.VAR_SYM) {
					this.topLevelNonVarIds.add(currID);
				}
			}
		}
		return this.topLevelNonVarIds;
	}


	public HashSet<String> getNumberNames() {
		return this.numberNames;
	}

	public List<Pair<String,List<String>>> getNumberChains() {
		return this.numberChains;
	}

	public HashSet<Integer> getNumberIDs() {
		return this.numberIDs;
	}

	public List<Pair<Integer,List<Integer>>> getNumberIDChains() {
		return this.numberIDChains;
	}


	public List<Integer> getRoleIds() {
		return roleIds;
	}



	public void setRoleIds(List<Integer> roleIds) {
		this.roleIds = roleIds;
	}


	public void printTopLevelByType() {

	}


	//produces triples that look like they could be part of a number chain
	//for each triple, first item is the name of the successor function, next item is first position child, and last item is second position child
	public List<List<String>> findNumberCandidates() {
		List<List<String>> result = new ArrayList<List<String>>();
		for(int currID : this.getTopLevelNonVarIds()) {
			RuleNode currNode = this.ruleGraph.get(currID);
			if(currNode.getColour() == RuleNodeColour.NON_VAR_SYM_RELATION && currNode.getChildColourNums().get(RuleNodeColour.ARG)==2) {
				List<RuleNode> argList = new ArrayList<RuleNode>();
				List<RuleNode> occList = new ArrayList<RuleNode>();
				for(RuleNode child : currNode.getChildren()) {
					if(child.getColour() == RuleNodeColour.ARG) {
						argList.add(child);
						if(argList.size() == 2 && argList.get(0).getArgNum() > argList.get(1).getArgNum()) {
							RuleNode temp = argList.get(0);
							argList.set(0, argList.get(1));
							argList.set(1, temp);
						}
					} else if(child.getColour() == RuleNodeColour.PRED_OC) {
						occList.add(child);
					}
				}

				for(RuleNode occ : occList) {
					if(occ.getChildColourNums().get(RuleNodeColour.FN_OC) == 2) {
						String firstPosition = null;
						String secondPosition = null;
						for(RuleNode child : occ.getChildren()) {
							if(child.getColour() == RuleNodeColour.FN_OC && child.getChildren().size() == 0) {
								for(RuleNode parent : child.getParents()) {
									if(parent.getColour() == RuleNodeColour.ARG) {
										if(parent.getArgNum() == argList.get(0).getArgNum()) {
											firstPosition = child.getName();
										} else if(parent.getArgNum() == argList.get(1).getArgNum()) {
											secondPosition = child.getName();
										}
									}
								}
							}
						}
						if(firstPosition != null && secondPosition != null) {
							List<String> newCand = new ArrayList<String>();
							newCand.add(currNode.getName());
							newCand.add(firstPosition);
							newCand.add(secondPosition);
							result.add(newCand);
						}
					}
				}
			}
		}
		return result;
	}


	private void assignNumberColours() {
		List<List<String>> candidates = findNumberCandidates();
		HashMap<String, List<List<String>>> candPerSuccessorFn = new HashMap<String, List<List<String>>>();
		List<Pair<String,List<String>>> allChains = new ArrayList<Pair<String,List<String>>>();

		for(List<String> cand : candidates) {
			String fnName = cand.get(0);
			if(!candPerSuccessorFn.containsKey(fnName)) {
				candPerSuccessorFn.put(fnName, new ArrayList<List<String>>());
			}
			candPerSuccessorFn.get(fnName).add(cand);
		}

		for(String fnName : candPerSuccessorFn.keySet()) {
			List<List<String>> fragments = candPerSuccessorFn.get(fnName);
			HashMap<String, List<String>> findByFirst = new HashMap<String, List<String>>();  //we're assuming that each String appears at most one time in each position
			HashMap<String, List<String>> findBySecond = new HashMap<String, List<String>>();
			LinkedList<List<String>> remaining = new LinkedList<List<String>>();
			for(List<String> frag : fragments) {
				findByFirst.put(frag.get(1), frag);
				findBySecond.put(frag.get(2), frag);
				remaining.add(frag);
			}
			while(!remaining.isEmpty()) {
				List<String> startFrag = remaining.pop();
				List<String> endFrag = startFrag;
				LinkedList<String> chain = new LinkedList<String>();
				chain.addFirst(startFrag.get(1));
				chain.addLast(endFrag.get(2));
				HashSet<String> used = new HashSet<String>();
				while(startFrag != null) {
					if(findBySecond.containsKey(startFrag.get(1)) && !used.contains(startFrag.get(1))) {
						used.add(startFrag.get(1));
						startFrag = findBySecond.get(startFrag.get(1));
						if(!used.contains(startFrag.get(1))) {
							chain.addFirst(startFrag.get(1));
						}
						remaining.remove(startFrag);
					} else {
						startFrag = null;
					}
				}

//				used = new HashSet<String>();
				while(endFrag != null) {
					if(findByFirst.containsKey(endFrag.get(2)) && !used.contains(endFrag.get(2))) {
						used.add(endFrag.get(2));
						endFrag = findByFirst.get(endFrag.get(2));
						if(!used.contains(endFrag.get(2))) {
							chain.addLast(endFrag.get(2));
						}
						remaining.remove(endFrag);
					} else {
						endFrag = null;
					}
				}
				if(chain.size() >= RuleGraph.MIN_NUMBER_CHAIN) {
					allChains.add(new Pair<String,List<String>>(fnName, chain));
					for(String name : chain) {
						this.numberNames.add(name);
					}
				}
			}
		}

		this.numberChains = allChains;
		for(String name : this.numberNames) {
			RuleNode node = ruleGraph.get(this.topLevelNames.get(name));
			node.setColour(RuleNodeColour.NUMBER_SYM);
		}

		HashMap<String, Integer> lookup = this.getTopLevelNames();
		for(String name : this.numberNames) {
			this.numberIDs.add(lookup.get(name));
		}
		for(Pair<String,List<String>> chain : this.numberChains) {
			int fnID = lookup.get(chain.getKey());
			List<Integer> chainIDs = new ArrayList<Integer>();
			for(String name : chain.getValue()) {
				chainIDs.add(lookup.get(name));
			}
			this.numberIDChains.add(new Pair<Integer,List<Integer>>(fnID, chainIDs));
		}
//		System.out.println(this.numberChains + "\n");
//		System.out.println(this.numberNames);
	}


	public int nextID() {
		int val = this.nextID;
		this.nextID++;
		return val;
	}


	private boolean isBuiltIn(String name) {
		return builtIns.contains(name);
	}

	private RuleNodeColour builtInNameToColour(String name) {
		RuleNodeColour col;
		if(name == "role") {
			col = RuleNodeColour.ROLE;
		} else if(name == "base") {
			col = RuleNodeColour.BASE;
		} else if(name == "input") {
			col = RuleNodeColour.INPUT;
		} else if(name == "init") {
			col = RuleNodeColour.INIT;
		} else if(name == "true") {
			col = RuleNodeColour.TRUE;
		} else if(name == "does") {
			col = RuleNodeColour.DOES;
		} else if(name == "next") {
			col = RuleNodeColour.NEXT;
		} else if(name == "legal") {
			col = RuleNodeColour.LEGAL;
		} else if(name == "goal") {
			col = RuleNodeColour.GOAL;
		} else if(name == "terminal") {
			col = RuleNodeColour.TERMINAL;
		} else {
			System.out.println("ERROR: name of non built-in passed to builtInNameToColour.");
			col = null;
		}
		return col;
	}


	private RuleNode getTopLevelNode(String name, int argNum, RuleNodeType type, RuleNodeColour colour) {
		RuleNode topNode = null;
		if(this.topLevelNames.containsKey(name)) {
			int index = this.topLevelNames.get(name).intValue();
			topNode = this.ruleGraph.get(index);
		} else {
			if(!isBuiltIn(name)) {
				topNode = new RuleNode(nextID(), name, argNum, type, colour);
			} else {
				RuleNodeColour builtInCol = builtInNameToColour(name);
				topNode = new RuleNode(nextID(), name, argNum, type, builtInCol);
			}
			this.ruleGraph.add(topNode.getId(), topNode);
			this.topLevel.add(topNode);
			this.topLevelNames.put(topNode.getName(), topNode.getId());
		}
		return topNode;
	}


	public RuleNode getArgNode(String name, int argNum) {
		RuleNode argNode = null;
		if(this.topLevelNames.containsKey(name)) {
			int topLevelId = this.topLevelNames.get(name);
			RuleNode topLevelNode = this.ruleGraph.get(topLevelId);
			for(RuleNode child : topLevelNode.getChildren()) {
				if(child.getColour() == RuleNodeColour.ARG && child.getName() == name && child.getArgNum() == argNum) {
					argNode = child;
					break;
				}
			}
		}
		return argNode;
	}


	private RuleNode genRuleNodesFromLine(Gdl line, HashMap<String, String> varDict, HashMap<String, Integer> varNums) {
		RuleNode node = null;

		if(line instanceof GdlRule) {
			GdlRule typed_line = ((GdlRule) line);
			node = new RuleNode(nextID(), "entail", -1, RuleNodeType.LOG, RuleNodeColour.ENTAIL);
			this.ruleGraph.add(node.getId(), node);
			RuleNode headNode = genRuleNodesFromLine(typed_line.getHead(), varDict, varNums);
			RuleNode bodyNode = genRuleNodesFromLine(new GdlAnd(typed_line.getBody()), varDict, varNums);
			node.addChild(headNode);
			node.addChild(bodyNode);
			headNode.addChild(bodyNode);
		} else if (line instanceof GdlDistinct) {
			GdlDistinct typed_line = ((GdlDistinct) line);
			node = new RuleNode(nextID(), "and", -1, RuleNodeType.LOG, RuleNodeColour.DISTINCT);
			this.ruleGraph.add(node.getId(), node);
			node.addChild(genRuleNodesFromLine(typed_line.getArg1(), varDict, varNums));
			node.addChild(genRuleNodesFromLine(typed_line.getArg2(), varDict, varNums));
		} else if (line instanceof GdlNot) {
			GdlNot typed_line = ((GdlNot) line);
			node = new RuleNode(nextID(), "not", -1, RuleNodeType.LOG, RuleNodeColour.NOT);
			this.ruleGraph.add(node.getId(), node);
			node.addChild(genRuleNodesFromLine(typed_line.getBody(), varDict, varNums));
		} else if (line instanceof GdlAnd) {
			GdlAnd typed_line = ((GdlAnd) line);
			if(typed_line.getConjuncts().size() > 1) {
				node = new RuleNode(nextID(), "and", -1, RuleNodeType.LOG, RuleNodeColour.AND);
				this.ruleGraph.add(node.getId(), node);
				Iterator<GdlLiteral> iter = typed_line.getConjuncts().iterator();
				while(iter.hasNext()) {
					node.addChild(genRuleNodesFromLine(iter.next(), varDict, varNums));
				}
			} else if(typed_line.getConjuncts().size() == 1) { //Don't bother generating an AND node if there is only 1 argument
				Iterator<GdlLiteral> iter = typed_line.getConjuncts().iterator();
				node = genRuleNodesFromLine(iter.next(), varDict, varNums);
			} else {
				System.out.println("ERROR: Found instance of AND with no arguments wile generating rule nodes.");
			}
		} else if (line instanceof GdlOr) {
			GdlOr typed_line = ((GdlOr) line);
			if(typed_line.getDisjuncts().size() > 1) {
				node = new RuleNode(nextID(), "or", -1, RuleNodeType.LOG, RuleNodeColour.OR);
				this.ruleGraph.add(node.getId(), node);
				Iterator<GdlLiteral> iter = typed_line.getDisjuncts().iterator();
				while(iter.hasNext()) {
					node.addChild(genRuleNodesFromLine(iter.next(), varDict, varNums));
				}
			} else if(typed_line.getDisjuncts().size() == 1) {
				Iterator<GdlLiteral> iter = typed_line.getDisjuncts().iterator();
				node = genRuleNodesFromLine(iter.next(), varDict, varNums);
			} else {
				System.out.println("ERROR: Found instance of OR with no arguments wile generating rule nodes.");
			}
		} else if (line instanceof GdlProposition) {
			GdlProposition typed_line = ((GdlProposition) line);
			node = new RuleNode(nextID(), typed_line.getName().getValue(), -1, RuleNodeType.PRED, RuleNodeColour.PRED_OC);
			this.ruleGraph.add(node.getId(), node);
			if(!isBuiltIn(node.getName())) {
				RuleNode topNode = getTopLevelNode(node.getName(), -1, node.getType(), RuleNodeColour.NON_VAR_SYM_PROP);
				topNode.addChild(node);
			} else {
				node.setColour(builtInNameToColour(node.getName()));
			}

		} else if (line instanceof GdlRelation) {
			GdlRelation typed_line = ((GdlRelation) line);
			node = new RuleNode(nextID(), typed_line.getName().getValue(), -1, RuleNodeType.PRED, RuleNodeColour.PRED_OC);
			this.ruleGraph.add(node.getId(), node);
			int argIndex = 1;
			ArrayList<RuleNode> argNodeList = new ArrayList<RuleNode>();
			Iterator<GdlTerm> iter = typed_line.getBody().iterator();
			ArrayList<RuleNode> newChildren = new ArrayList<RuleNode>();
			while(iter.hasNext()) {
				RuleNode actualArg = genRuleNodesFromLine(iter.next(), varDict, varNums);
				node.addChild(actualArg);
				newChildren.add(actualArg);
				if(!isBuiltIn(node.getName())) {
					RuleNode argNode = getArgNode(node.getName(), argIndex);
					if(argNode == null) {
						argNode = new RuleNode(nextID(), node.getName(), argIndex, RuleNodeType.PRED, RuleNodeColour.ARG);
						this.ruleGraph.add(argNode.getId(), argNode);
						argNodeList.add(argNode);
					}
					argNode.addChild(actualArg);
					argIndex++;
				}
			}
			if(!isBuiltIn(node.getName())) {
				RuleNode topNode = getTopLevelNode(node.getName(), -1, node.getType(), RuleNodeColour.NON_VAR_SYM_RELATION);
				topNode.addChild(node);
				for(RuleNode currArg: argNodeList) {
					topNode.addChild(currArg);
				}
			} else {
				node.setColour(builtInNameToColour(node.getName()));
				if(typed_line.arity() == 2) {
					newChildren.get(0).addChild(newChildren.get(1));
				}
			}
		} else if (line instanceof GdlConstant) {
			GdlConstant typed_line = ((GdlConstant) line);
			node = new RuleNode(nextID(), typed_line.getValue(), -1, RuleNodeType.FN, RuleNodeColour.FN_OC);
			this.ruleGraph.add(node.getId(), node);
			if(!isBuiltIn(node.getName())) {
				RuleNode topNode = getTopLevelNode(node.getName(), -1, node.getType(), RuleNodeColour.NON_VAR_SYM_CONST);
				topNode.addChild(node);
			} else {
				node.setColour(builtInNameToColour(node.getName()));
			}
		} else if (line instanceof GdlFunction) {
			GdlFunction typed_line = ((GdlFunction) line);
			node = new RuleNode(nextID(), typed_line.getName().getValue(), -1, RuleNodeType.FN, RuleNodeColour.FN_OC);
			this.ruleGraph.add(node.getId(), node);
			int argIndex = 1;
			ArrayList<RuleNode> argNodeList = new ArrayList<RuleNode>();
			Iterator<GdlTerm> iter = typed_line.getBody().iterator();
			ArrayList<RuleNode> newChildren = new ArrayList<RuleNode>();
			while(iter.hasNext()) {
				RuleNode actualArg = genRuleNodesFromLine(iter.next(), varDict, varNums);
				node.addChild(actualArg);
				newChildren.add(actualArg);
				if(!isBuiltIn(node.getName())) {
					RuleNode argNode = getArgNode(node.getName(), argIndex);
					if(argNode == null) {
						argNode = new RuleNode(nextID(), node.getName(), argIndex, RuleNodeType.FN, RuleNodeColour.ARG);
						this.ruleGraph.add(argNode.getId(), argNode);
						argNodeList.add(argNode);
					}
					argNode.addChild(actualArg);
					argIndex++;
				}
			}
			if(!isBuiltIn(node.getName())) {
				RuleNode topNode = getTopLevelNode(node.getName(), -1, node.getType(), RuleNodeColour.NON_VAR_SYM_FUNC);
				topNode.addChild(node);
				for(RuleNode currArg: argNodeList) {
					topNode.addChild(currArg);
				}
			} else {
				node.setColour(builtInNameToColour(node.getName()));
				if(typed_line.arity() == 2) {
					newChildren.get(0).addChild(newChildren.get(1));
				}
			}
		} else if (line instanceof GdlVariable) {
			GdlVariable typed_line = ((GdlVariable) line);
			String rawName = typed_line.getName();
			String convertedName;
			if(varDict.containsKey(rawName)) {
				convertedName = varDict.get(rawName);
			} else {
				if(!varNums.containsKey(rawName)) {
					varNums.put(rawName, 0);
				}
				int currVarNum = varNums.get(rawName).intValue();
				convertedName = rawName + "[" + currVarNum + "]";
				varDict.put(rawName, convertedName);
				varNums.put(rawName, varNums.get(rawName) + 1);
			}
			node = new RuleNode(nextID(), convertedName, -1, RuleNodeType.VAR, RuleNodeColour.VAR_OC);
			this.ruleGraph.add(node.getId(), node);
			if(!isBuiltIn(node.getName())) {
				RuleNode topNode = getTopLevelNode(node.getName(), -1, node.getType(), RuleNodeColour.VAR_SYM);
				topNode.addChild(node);
			} else {
				node.setColour(builtInNameToColour(node.getName()));
			}
		} else {
			System.out.println("ERROR in genRuleNodesFromLine: unrecognized Gdl input");
		}

		return node;
	}


	public void genRuleGraph() {
		if (ruleGraph == null) {
			this.ruleGraph = new ArrayList<RuleNode>();
			Iterator<Gdl> ruleIter = this.rules.iterator();
			HashMap<String, String> varDict;
			HashMap<String, Integer> varNums = new HashMap<String, Integer>();
			while(ruleIter.hasNext()) {
				varDict = new HashMap<String, String>();
				genRuleNodesFromLine(ruleIter.next(), varDict, varNums);
			}

			//make ordered list of role IDs
			this.roleIds = new ArrayList<Integer>();
			for(Role r : this.roles) {
				String roleName = r.getName().getValue();
				if(this.topLevelNames.containsKey(roleName)) {
					this.roleIds.add(this.topLevelNames.get(roleName));
				} else {
					System.out.println("ERROR: role name not found in graph.");
				}
			}

			this.assignNumberColours();
		}
	}



	public void printRuleGraph() {
		System.out.println("Printing rule graph...");
		for(RuleNode curr : ruleGraph) {
			System.out.println(curr);
			System.out.println();
		}
		System.out.println("Finished printing rule graph.");
	}

	public void printTopLevel() {
		ArrayList<Integer> ids = new ArrayList<Integer>();
		for (String name : topLevelNames.keySet()) {
			ids.add(topLevelNames.get(name));
		}
		Collections.sort(ids);
		for (int currID : ids) {
//			System.out.println(name + ":");
			RuleNode node = ruleGraph.get(currID);
			System.out.println(node.shortToString());
		}
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
//		Collections.sort(stateStrs, new Comparator<List<String>>(){
//
//	        @Override
//	        public int compare(List<String> s1, List<String> s2) {
//	            return s1.get(0).compareTo(s2.get(0));
//	        }
//
//	    });
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
