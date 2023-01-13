package org.ggp.base.player.gamer.statemachine.sample;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Set;
import java.util.StringTokenizer;

import org.ggp.base.util.gdl.grammar.GdlConstant;
import org.ggp.base.util.gdl.grammar.GdlFunction;
import org.ggp.base.util.gdl.grammar.GdlRelation;
import org.ggp.base.util.gdl.grammar.GdlSentence;
import org.ggp.base.util.gdl.grammar.GdlTerm;
import org.ggp.base.util.statemachine.MachineState;
import org.ggp.base.util.statemachine.Move;
import org.ggp.base.util.statemachine.Role;

public class StateMapping {
	private RuleGraph target;
	private RuleGraphRecord source;
//	private EditDistance edit;
	private ContextEditDistance edit;
	private ReducedMCTree sourceStates;

	public StateMapping(RuleGraph target, RuleGraphRecord source) {
		this.target = target;
		this.source = source;
		this.target.genRuleGraph();
//		this.edit = new EditDistance(this.target.getGraph(), source.getGraph());
		this.edit = new ContextEditDistance(target.getGraph(), source.getGraph(), target.getTopLevelNonVarIds(), source.getTopLevelNonVarIds(), target.getNumberIDs(), source.getNumberIDs(), target.getNumberIDChains(), source.getNumberIDChains());
//		this.edit.calcDistance(CostType.COLOUR_AND_KNOWN_EDGES);
		this.edit.calcDistance();
		this.sourceStates = new ReducedMCTree();
	}

	public StateMapping(RuleGraph target, RuleGraphRecord source, ContextEditDistance edit) {
		this.target = target;
		this.source = source;
		this.edit = edit;
		this.sourceStates = new ReducedMCTree();
	}

	//Use this one if you want to generate the target rule graph, but don't actually want to do any mapping or interact with a source game at all
	public StateMapping(RuleGraph target) {
		this.target = target;
		this.target.genRuleGraph();
		this.source = null;
		this.edit = null;
		this.sourceStates = new ReducedMCTree();
	}

	public RuleGraph getTarget() {
		return target;
	}

	public RuleGraphRecord getSource() {
		return source;
	}

	public ContextEditDistance getEdit() {
		return edit;
	}

	public ReducedMCTree getSourceStates() {
		return sourceStates;
	}

//	public static List<Integer> IDListToMove(List<String> IDList) {
//		Move result = null;
//		if(IDList.size() == 1) {
//			try{
//	            int constID = Integer.parseInt(IDList.get(0));
//	            String moveName = this.
//	        } catch (NumberFormatException e) {
//	            e.printStackTrace();
//	        }
//		}
//	}

	public void loadSourceStatesFromFile(String inFileName) {
		this.sourceStates.loadStatesFromFile(inFileName);
	}


	//convert a single state from the target game into a tree for comparisons
	public StateNode genTargetStateTree(MachineState mState) {
		StateNode root = new StateNode(StateNode.ROOT_ID);
		StateNode currPosn;
		Set<GdlSentence> gdl = mState.getContents();
		HashMap<String, Integer> nameToID = target.getTopLevelNames();
//		System.out.println(gdl);

		for(GdlSentence sentence : gdl) {
			if (sentence instanceof GdlRelation) {
				GdlRelation rel = (GdlRelation) sentence;
				if(rel.getName().getValue().equals("true") && rel.getBody().size() == 1) {
					if(rel.getBody().get(0) instanceof GdlFunction) {
						GdlFunction fun = (GdlFunction) rel.getBody().get(0);
						if(nameToID.containsKey(fun.getName().getValue())) {
							int funID = nameToID.get(fun.getName().getValue());
							if(!root.checkChild(funID)) {
								root.addChild(funID);
							}
							currPosn = root.getChildren().get(funID);
							for(GdlTerm arg : fun.getBody()) {
								if(arg instanceof GdlConstant) {
									GdlConstant con = (GdlConstant) arg;
									int conID = nameToID.get(con.getValue());
									if(!currPosn.checkChild(conID)) {
										currPosn.addChild(conID);
									}
									currPosn = currPosn.getChildren().get(conID);
								} else if(arg instanceof GdlFunction) {
									System.out.println("ERROR: nested functions in genTargetStateTree.");
								} else {
									System.out.println("ERROR: variable or something weird in genTargetStateTree.");
								}
							}
						} else {
							System.out.println("ERROR: function name not found in genTargetStateTree.");
						}
					} else if (rel.getBody().get(0) instanceof GdlConstant) {
						GdlConstant con = (GdlConstant) rel.getBody().get(0);
						if(nameToID.containsKey(con.getValue())) {
							int conID = nameToID.get(con.getValue());
							if(!root.checkChild(conID)) {
								root.addChild(conID);
							}
						} else {
							System.out.println("ERROR: constant name not found in genTargetStateTree.");
						}
					} else {
						System.out.println("ERROR: non function statement in genTargetStateTree - " + rel.getBody().get(0));
					}
				} else {
					System.out.println("ERROR: non \"true\" statement in genTargetStateTree.");
				}
			} else {
				System.out.println("ERROR: non relation in genTargetStateTree.");
			}
    	}

		return root;
	}


	//convert a single state from the target game into a set of state components for comparisons
	public Set<List<Integer>> genTargetStateSet(MachineState mState) {
		Set<GdlSentence> gdl = mState.getContents();
		return genTargetStateSet(gdl);
	}

	//convert a list of GDL facts into a set of state components for comparisons
	public Set<List<Integer>> genTargetStateSet(Set<GdlSentence> gdl) {
		Set<List<Integer>> stateSet = new HashSet<List<Integer>>();
		HashMap<String, Integer> nameToID = target.getTopLevelNames();

		for(GdlSentence sentence : gdl) {
			if (sentence instanceof GdlRelation) {
				GdlRelation rel = (GdlRelation) sentence;
				if(rel.getName().getValue().equals("true") && rel.getBody().size() == 1) {
					List<Integer> newList = new ArrayList<Integer>();
					if(rel.getBody().get(0) instanceof GdlFunction) {
						GdlFunction fun = (GdlFunction) rel.getBody().get(0);
						if(nameToID.containsKey(fun.getName().getValue())) {
							int funID = nameToID.get(fun.getName().getValue());
							newList.add(funID);
							for(GdlTerm arg : fun.getBody()) {
								if(arg instanceof GdlConstant) {
									GdlConstant con = (GdlConstant) arg;
									int conID = nameToID.get(con.getValue());
									newList.add(conID);
								} else if(arg instanceof GdlFunction) {
									System.out.println("ERROR: nested functions in genTargetStateTree.");
								} else {
									System.out.println("ERROR: variable or something weird in genTargetStateTree.");
								}
							}
						} else {
							System.out.println("ERROR: function name not found in genTargetStateTree.");
						}
					} else if (rel.getBody().get(0) instanceof GdlConstant) {
						GdlConstant con = (GdlConstant) rel.getBody().get(0);
						if(nameToID.containsKey(con.getValue())) {
							int conID = nameToID.get(con.getValue());
							newList.add(conID);
						} else {
							System.out.println("ERROR: constant name not found in genTargetStateTree.");
						}
					} else {
						System.out.println("ERROR: non function statement in genTargetStateTree - " + rel.getBody().get(0));
					}
					stateSet.add(newList);
				} else {
					System.out.println("ERROR: non \"true\" statement in genTargetStateTree.");
				}
			} else {
				System.out.println("ERROR: non relation in genTargetStateTree.");
			}
    	}

		return stateSet;
	}



	//specifically, generate a state tree from a String formatted like StateNode.toString()
	public StateNode genStateTreeFromString(String str) {
		StringTokenizer tok = new StringTokenizer(str);
		String currTok = tok.nextToken();
		StateNode root = null;
		StateNode currNode = null;
		if(currTok.equals("(")) {
			currTok = tok.nextToken();
			root = new StateNode(Integer.parseInt(currTok));
			currNode = root;
			while(tok.hasMoreTokens()) {
				currTok = tok.nextToken();
				if (currTok.equals("(")) {
					currTok = tok.nextToken();
					int newChildID = Integer.parseInt(currTok);
					currNode.addChild(newChildID);
					StateNode newChildNode = currNode.getChildren().get(newChildID);
					newChildNode.setParent(currNode);
					currNode = newChildNode;
				} else if (currTok.contentEquals(")")) {
					currNode = currNode.getParent();
				} else {
					System.out.println("ERROR: genStateTreeFromString received bad bracket pattern.");
				}
			}
		} else {
			System.out.println("ERROR: genStateTreeFromString received bad string.");
		}
		return root;
	}


	//convert given state tree from target to source game
	//NOTE: This changes the given tree. It does not produce a new tree.
	public int mapTargetStateTreeToSource(StateNode targetNode) {
		HashMap<Integer, Integer> mapping = this.edit.getMapping();
//		System.out.println("Mapping");
//		System.out.println(mapping);
//		System.out.println("Target Node");
//		System.out.println(targetNode);
//		System.out.println("Target ID");
//		System.out.println(targetNode.getIdNum());
		int newID = mapping.get(targetNode.getIdNum());
		targetNode.setIdNum(newID);
		if(targetNode.getChildren() != null) {
			HashMap<Integer, StateNode> newChildren = new HashMap<Integer, StateNode>();
			for(Integer childID : targetNode.getChildren().keySet()) {
				StateNode currChild = targetNode.getChildren().get(childID);
				int newChildID = mapTargetStateTreeToSource(currChild);
				newChildren.put(newChildID, currChild);
			}
			targetNode.setChildren(newChildren);
		}
		return newID;
	}


	public int mapSourceIDToTarget(int sourceID) {
		if(this.edit.getRevMapping().containsKey(sourceID)) {
			return this.edit.getRevMapping().get(sourceID);
		} else {
			return -1;
		}
	}


	//produce a state corresponding to the given target state in source game
	//Note: unlike it's tree counterpart, this method is non-destructive
	public Set<List<Integer>> mapTargetStateSetToSource(Set<List<Integer>> targetState) {
		HashMap<Integer, Integer> mapping = this.edit.getMapping();
		Set<List<Integer>> sourceState = new HashSet<List<Integer>>();
		for(List<Integer> targetComp : targetState) {
			List<Integer> sourceComp = new ArrayList<Integer>();
			for(int term : targetComp) {
				sourceComp.add(mapping.get(term));
			}
			sourceState.add(sourceComp);
		}
		return sourceState;
	}


	//count the differences between 2 state trees
	//not used for state lists
	public float countStateDifferences(StateNode state1, StateNode state2) {
		float count = 0;

		if(state1.getChildren() == null && state2.getChildren() == null) {
			//pass
		} else if (state1.getChildren() == null) {
			count += state2.numLeaves();
		} else if (state2.getChildren() == null) {
			count += state1.numLeaves();
		} else {
			for(int childID : state1.getChildren().keySet()) {
				if(state2.checkChild(childID)) {
					count += countStateDifferences(state1.getChildren().get(childID), state2.getChildren().get(childID));
				} else {
					count += state1.getChildren().get(childID).numLeaves();
				}
			}
			for(int childID : state2.getChildren().keySet()) {
				if(state1.checkChild(childID)) {
					//pass to avoid double counting
				} else {
					count += state2.getChildren().get(childID).numLeaves();
				}
			}
		}
		return count;
	}


	public ReducedMCTNode findNearestSourceState(MCTNode targetNode) {
		ReducedMCTNode nearest = null;
		targetNode.genMappedState();
		if(MCTNode.STATE_TYPE == 0) {
			float smallestDif = -1;
			StateNode mappedState = targetNode.getMappedStateTree();
	//		System.out.println(targetNode.getState().toString());
	//		System.out.println(targetNode.getStateTree().toString());
	//		System.out.println(mappedState.toString());

			for (ReducedMCTNode currNode : this.sourceStates.getStates()) {
				float currDif = countStateDifferences(mappedState, currNode.getStateTree());
	//			System.out.println(targetNode.getStateTree());
	//			System.out.println(mappedState);
	//			System.out.println(currNode.getStateTree());
	//			System.out.println("Differences: " + currDif);
				if (smallestDif == -1 || currDif < smallestDif) {
					smallestDif = currDif;
					nearest = currNode;
				}
			}
			targetNode.setTransferDif(smallestDif);
	//		System.out.println(smallestDif);
		} else {
			Set<List<Integer>> mappedState = targetNode.getMappedStateSet();
			HashMap<Integer,Integer> idToNumMatches = new HashMap<Integer,Integer>();
			int mostMatches = 0;
			int mostMatchID = 0;
			for(List<Integer> comp : mappedState) {
				if(this.sourceStates.getStateCompToOwnerIDs().containsKey(comp)) {
					List<Integer> owningIDs = this.sourceStates.getStateCompToOwnerIDs().get(comp);
					for(int currID : owningIDs) {
						if(!idToNumMatches.containsKey(currID)) {
							idToNumMatches.put(currID, 0);
						}
						int prev = idToNumMatches.get(currID);
						idToNumMatches.put(currID, prev + 1);
						if(prev+1 > mostMatches) {
							mostMatches = prev+1;
							mostMatchID = currID;
						}
					}
				}
			}
			nearest = this.sourceStates.getStates().get(mostMatchID);
		}
		return nearest;
	}



	public List<Integer> convertMoveToList(Move targetMove) {
		List<List<Integer>> converted = convertMoveToList(Arrays.asList(targetMove));
		if(converted.size() >= 1) {
			return converted.get(0);
		} else {
			return null;
		}
	}


	//changes types from a Move for each role to a list of IDs for each role
	public List<List<Integer>> convertMoveToList(List<Move> targetMove) {
		List<List<Integer>> result = new ArrayList<List<Integer>>();
		HashMap<String, Integer> nameToID = this.getTarget().getTopLevelNames();
		for(Move roleMove : targetMove) {
			List<Integer> convertedRoleMove = new ArrayList<Integer>();
			GdlTerm term = roleMove.getContents();
			if(term instanceof GdlFunction) {
	    		GdlFunction fun = (GdlFunction) term;
	    		if(nameToID.containsKey(fun.getName().getValue())) {
	    			int funID = nameToID.get(fun.getName().getValue());
	    			convertedRoleMove.add(funID);
	    			for(GdlTerm arg : fun.getBody()) {
	    				if(arg instanceof GdlConstant) {
	    					GdlConstant con = (GdlConstant) arg;
	    					int conID = nameToID.get(con.getValue());
	    					convertedRoleMove.add(conID);
	    				} else if(arg instanceof GdlFunction) {
	    					System.out.println("ERROR: nested functions in convertMoveToSource.");
	    				} else {
	    					System.out.println("ERROR: variable or something weird in convertMoveToSource.");
	    				}
	    			}
	    		} else {
	    			System.out.println("ERROR: function name not found in convertMoveToSource.");
	    		}
	    	} else if (term instanceof GdlConstant) {
	    		GdlConstant con = (GdlConstant) term;
	    		if(nameToID.containsKey(con.getValue())) {
	    			int conID = nameToID.get(con.getValue());
	    			convertedRoleMove.add(conID);
	    		} else {
	    			System.out.println("ERROR: constant name not found in convertMoveToSource.");
	    		}
	    	} else {
	    		System.out.println("ERROR: non function statement in convertMoveToSource - " + term);
	    	}
			result.add(convertedRoleMove);
		}
		return result;
	}


	//converts a given move  in the target game to the source
	//also changes types from a Move for each role to a list of IDs for each role
	public List<List<Integer>> convertMoveToSource(List<Move> targetMove) {
		List<List<Integer>> typeConverted = convertMoveToList(targetMove);
		List<List<Integer>> result = new ArrayList<List<Integer>>();
		for(List<Integer> roleMove : typeConverted) {
			List<Integer> newList = new ArrayList<Integer>();
			for(int id : roleMove) {
				newList.add(this.edit.targetIDToSource(id));
			}
			result.add(newList);
		}
		return result;
	}


	//produces the a move that exactly corresponds to targetMove from sourceNode, if it exists
	//produces null otherwise
	public List<List<Integer>> findNearestSourceMove(List<Move> targetMove, ReducedMCTNode sourceNode) {
		List<List<Integer>> result = null;
		List<List<Integer>> convertedMove = convertMoveToSource(targetMove);
//		System.out.println("Converted move: " + convertedMove);
//		System.out.println("Stored move set: " + sourceNode.getChildData().keySet());
		if(sourceNode.getChildData().containsKey(convertedMove)) {
			result = convertedMove;
		}
		return result;
	}


	//returns a list of role indices after mapping
	//-1 indicates that there was no corresponding role in the recorded game
	//this is important to get the correct mapped reward values
	public List<Integer> getMappedRoleIndices(List<Role> roles) {
		List<Integer> mappedIndices = new ArrayList<Integer>();
		for(Role r : roles) {
			String roleName = r.getName().getValue();
			int roleId = this.edit.getG1IdFromName(roleName);
			if(roleId != -1) {
				int mappedId = this.edit.getMapping().get(roleId);
				mappedIndices.add(this.source.getRoleIndex(mappedId));
			} else {
				mappedIndices.add(-1);
			}
		}
		return mappedIndices;
	}


	//given the id of a node in the target game, produce its name (used for debugging)
	public String getTargetName(int id) {
		return this.target.getGraph().get(id).getName();
	}

	//given a list of ids of nodes in the source game, produce a list of their names (used for debugging)
	public List<String> getTargetName(List<Integer> ids) {
		List<String> result = new ArrayList<String>();
		for(int id : ids) {
			result.add(getTargetName(id));
		}
		return result;
	}


	//given the id of a node in the source game, produce its name (used for debugging)
	public String getSourceName(int id) {
		return this.source.getGraph().get(id).getName();
	}

	//given a list of ids of nodes in the source game, produce a list of their names (used for debugging)
	public List<String> getSourceName(List<Integer> ids) {
		List<String> result = new ArrayList<String>();
		for(int id : ids) {
			result.add(getSourceName(id));
		}
		return result;
	}
}
