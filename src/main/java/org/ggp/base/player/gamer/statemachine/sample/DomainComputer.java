package org.ggp.base.player.gamer.statemachine.sample;

import java.util.ArrayList;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.List;
import java.util.ListIterator;
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
import org.ggp.base.util.gdl.grammar.GdlSentence;
import org.ggp.base.util.gdl.grammar.GdlTerm;
import org.ggp.base.util.gdl.grammar.GdlVariable;

public class DomainComputer {
	private List<Gdl> rules;

	public DomainComputer(List<Gdl> rules) {
		this.rules = rules;
	}

	public final class DomainPair {
		private final String name;
		private final int index;

		public DomainPair(String name, int index) {
			this.name = name;
			this.index = index;
		}

		public String getName() {return name;}
		public int getIndex() {return index;}

		@Override
		public int hashCode() {
			final int prime = 31;
			int result = 1;
			result = prime * result + getEnclosingInstance().hashCode();
			result = prime * result + index;
			result = prime * result + ((name == null) ? 0 : name.hashCode());
			return result;
		}

		@Override
		public boolean equals(Object obj) {
			if (this == obj)
				return true;
			if (obj == null)
				return false;
			if (getClass() != obj.getClass())
				return false;
			DomainPair other = (DomainPair) obj;
			if (!getEnclosingInstance().equals(other.getEnclosingInstance()))
				return false;
			if (index != other.index)
				return false;
			if (name == null) {
				if (other.name != null)
					return false;
			} else if (!name.equals(other.name))
				return false;
			return true;
		}

		private DomainComputer getEnclosingInstance() {
			return DomainComputer.this;
		}

		@Override
		public String toString() {
			return "DomainPair [name=" + name + ", index=" + index + "]";
		}
	}

	//builds up the list of vars found in the head of a rule
	private void ruleHeadDomainGraph(HashMap<DomainPair, HashSet<DomainPair>> graph, HashMap<String, HashSet<DomainPair>> vars, Gdl currGdl) {
		int arity = 0;
		String name = "";
		List<GdlTerm> body = null;
		DomainPair parentPair;
		if (currGdl instanceof GdlSentence) {
			GdlSentence curr = ((GdlSentence) currGdl);
			arity = curr.arity();
			name = curr.getName().getValue();
			body = curr.getBody();
		} else if (currGdl instanceof GdlFunction) {
			GdlFunction curr = ((GdlFunction) currGdl);
			arity = curr.arity();
			name = curr.getName().getValue();
			body = curr.getBody();
		} else {
			System.out.println("ERROR in ruleHeadDomainGraph: given unrecognized Gdl");
		}
		for (int i=0;i<arity;i++) {
			parentPair = new DomainPair(name,i+1);
			DomainPair bodyPair = null;
			Gdl bodyTerm = body.get(i);
			boolean isVariable = false;
			if(bodyTerm instanceof GdlVariable) {
				isVariable = true;
				String varName = ((GdlVariable) bodyTerm).getName();
				if (!vars.containsKey(varName)) {
					vars.put(varName, new HashSet<DomainPair>());
				}
				if (!vars.get(varName).contains(parentPair)) {
					vars.get(varName).add(parentPair);
				}
			} else if (bodyTerm instanceof GdlConstant) {
				String currConstant = ((GdlConstant) bodyTerm).getValue();
				bodyPair = new DomainPair(currConstant, 0);
			} else if (bodyTerm instanceof GdlFunction) {
				String currFunction = ((GdlFunction) bodyTerm).getName().getValue();
				bodyPair = new DomainPair(currFunction, -1);
				ruleHeadDomainGraph(graph, vars, bodyTerm);
			} else {
				System.out.println("ERROR in ruleHeadDomainGraph: body term is unrecognized Gdl");
			}

			if(!isVariable) {
    			if (!graph.containsKey(bodyPair)) {
    				graph.put(bodyPair, new HashSet<DomainPair>());
    			}
    			if(!graph.containsKey(parentPair)) {
    				graph.put(parentPair, new HashSet<DomainPair>());
    			}
    			if(!graph.get(parentPair).contains(bodyPair)) {
    				graph.get(parentPair).add(bodyPair);
    			}
			}
		}
	}

	//searches for matches in the given literal to variables in vars
	private void ruleBodyDomainGraph(HashMap<DomainPair, HashSet<DomainPair>> graph, HashMap<String, HashSet<DomainPair>> vars, Gdl currGdl) {
		if(currGdl instanceof GdlDistinct) {
			GdlDistinct curr = ((GdlDistinct) currGdl);
			ruleBodyDomainGraph(graph, vars, curr.getArg1());
			ruleBodyDomainGraph(graph, vars, curr.getArg2());
		} else if(currGdl instanceof GdlNot) {
			GdlNot curr = ((GdlNot) currGdl);
			ruleBodyDomainGraph(graph, vars, curr.getBody());
		} else if(currGdl instanceof GdlOr) {
			GdlOr curr = ((GdlOr) currGdl);
			List<GdlLiteral> disjuncts = curr.getDisjuncts();
			Iterator<GdlLiteral> iter = disjuncts.iterator();
			while(iter.hasNext()) {
				ruleBodyDomainGraph(graph, vars, iter.next());
			}
		} else if(currGdl instanceof GdlProposition) {
//			GdlProposition curr = ((GdlProposition) currGdl);
//			pass, there cannot be variables in a proposition
		} else if(currGdl instanceof GdlRelation) {
			GdlRelation curr = ((GdlRelation) currGdl);
			String name = curr.getName().getValue();
    		for(int i=0;i<curr.arity();i++) {
    			DomainPair relPair = new DomainPair(name,i+1);
    			GdlTerm currTerm = curr.get(i);
    			if (currTerm instanceof GdlConstant) {
//    				pass
    			} else if (currTerm instanceof GdlVariable) {
    				String varName = ((GdlVariable) currTerm).getName();
    				if (vars.containsKey(varName)) {
    					Iterator<DomainPair> varIter = vars.get(varName).iterator();
    					while (varIter.hasNext()) {
    						DomainPair headPair = varIter.next();
    						if (!graph.containsKey(relPair)) {
    		    				graph.put(relPair, new HashSet<DomainPair>());
    		    			}
    						if (!graph.containsKey(headPair)) {
    		    				graph.put(headPair, new HashSet<DomainPair>());
    		    			}
    						if(!graph.get(headPair).contains(relPair)) {
    		    				graph.get(headPair).add(relPair);
    		    			}
    					}
    				}
    			} else if (currTerm instanceof GdlFunction) {
    				ruleBodyDomainGraph(graph, vars, currTerm);
    			} else {
    				System.out.println("ERROR in ruleBodyDomainGraph: Unexpected argument of a relation");
    				System.out.println("Type: " + currTerm.getClass().getName());
    			}
    		}
		} else if(currGdl instanceof GdlConstant) {
//			GdlConstant curr = ((GdlConstant) currGdl);
//			pass, there cannot be variables in a constant
		} else if(currGdl instanceof GdlFunction) {
			GdlFunction curr = ((GdlFunction) currGdl);
			String name = curr.getName().getValue();
    		for(int i=0;i<curr.arity();i++) {
    			DomainPair funPair = new DomainPair(name,i+1);
    			GdlTerm currTerm = curr.get(i);
    			if (currTerm instanceof GdlConstant) {
//    				pass
    			} else if (currTerm instanceof GdlVariable) {
    				String varName = ((GdlVariable) currTerm).getName();
    				if (vars.containsKey(varName)) {
    					Iterator<DomainPair> varIter = vars.get(varName).iterator();
    					while (varIter.hasNext()) {
    						DomainPair headPair = varIter.next();
    						if (!graph.containsKey(funPair)) {
    		    				graph.put(funPair, new HashSet<DomainPair>());
    		    			}
    						if (!graph.containsKey(headPair)) {
    		    				graph.put(headPair, new HashSet<DomainPair>());
    		    			}
    						if(!graph.get(headPair).contains(funPair)) {
    		    				graph.get(headPair).add(funPair);
    		    			}
    					}
    				}
    			} else if (currTerm instanceof GdlFunction) {
    				ruleBodyDomainGraph(graph, vars, currTerm);
    			} else {
    				System.out.println("ERROR in ruleBodyDomainGraph: Unexpected argument of a function");
    				System.out.println("Type: " + currTerm.getClass().getName());
    			}
    		}
		} else if(currGdl instanceof GdlVariable) {
//			GdlVariable curr = ((GdlVariable) currGdl);
//			System.out.println("ERROR in ruleBodyDomainGraph: passed a GdlVariable");
//			System.out.println(currGdl);
		} else {
			System.out.println("ERROR in ruleBodyDomainGraph: passed unrecognized type");
		}
	}

	//index -1 indicates whole function is contained
	//index 0 indicates value is a constant
	//index 1,2,... indicate a specific index
	private void singleLineDomainGraph(HashMap<DomainPair, HashSet<DomainPair>> graph, HashMap<String, HashSet<DomainPair>> vars, Gdl currGdl) {
		if(currGdl instanceof GdlRelation) {
    		GdlRelation curr = ((GdlRelation) currGdl);
    		String name = curr.getName().getValue();
    		for(int i=0;i<curr.arity();i++) {
    			DomainPair relPair = new DomainPair(name,i+1);
    			DomainPair argPair = new DomainPair("ERROR", 0);
    			GdlTerm currTerm = curr.get(i);
    			if (currTerm instanceof GdlConstant) {
    				String currConstant = ((GdlConstant) currTerm).getValue();
    				argPair = new DomainPair(currConstant, 0);
    			} else if (currTerm instanceof GdlFunction) {
    				String currFunction = ((GdlFunction) currTerm).getName().getValue();
    				argPair = new DomainPair(currFunction, -1);
    				singleLineDomainGraph(graph, vars, currTerm);
    			} else {
    				System.out.println("ERROR in singleLineDomainGraph: Unexpected argument of a relation");
    				System.out.println("Type: " + currTerm.getClass().getName());
    			}

    			if (!graph.containsKey(argPair)) {
    				graph.put(argPair, new HashSet<DomainPair>()); //null);
    			}
    			if(!graph.containsKey(relPair)) {
    				graph.put(relPair, new HashSet<DomainPair>());
    			}
    			if(!graph.get(relPair).contains(argPair)) {
    				graph.get(relPair).add(argPair);
    			}
    		}
    	} else if (currGdl instanceof GdlFunction) {
    		GdlFunction curr = ((GdlFunction) currGdl);
    		String name = curr.getName().getValue();
    		boolean isVariable = false;
    		for(int i=0;i<curr.arity();i++) {
    			DomainPair funPair = new DomainPair(name,i+1);
    			DomainPair argPair = new DomainPair("ERROR", 0);
    			GdlTerm currTerm = curr.get(i);
    			if (currTerm instanceof GdlConstant) {
    				String currConstant = ((GdlConstant) currTerm).getValue();
    				argPair = new DomainPair(currConstant, 0);
    			} else if (currTerm instanceof GdlVariable) {
    				isVariable = true;
    				String varName = ((GdlVariable) currTerm).getName();
    				if (vars.containsKey(varName)) {
    					Iterator<DomainPair> varIter = vars.get(varName).iterator();
    					while (varIter.hasNext()) {
    						DomainPair headPair = varIter.next();
    						if (!graph.containsKey(funPair)) {
    		    				graph.put(funPair, new HashSet<DomainPair>());
    		    			}
    						if (!graph.containsKey(headPair)) {
    		    				graph.put(headPair, new HashSet<DomainPair>());
    		    			}
    						if(!graph.get(headPair).contains(funPair)) {
    		    				graph.get(headPair).add(funPair);
    		    			}
    					}
    				}
    			} else if (currTerm instanceof GdlFunction) {
    				String currFunction = ((GdlFunction) currTerm).getName().getValue();
    				argPair = new DomainPair(currFunction, -1);
    				singleLineDomainGraph(graph, vars, currTerm);
    			} else {
    				System.out.println("ERROR in singleLineDomainGraph: Unexpected argument of a function");
    				System.out.println("Type: " + currTerm.getClass().getName());
    			}

    			if(!isVariable) {
	    			if (!graph.containsKey(argPair)) {
	    				graph.put(argPair, new HashSet<DomainPair>()); //null);
	    			}
	    			if(!graph.containsKey(funPair)) {
	    				graph.put(funPair, new HashSet<DomainPair>());
	    			}
	    			if(!graph.get(funPair).contains(argPair)) {
	    				graph.get(funPair).add(argPair);
	    			}
    			}
    		}
    	} else if (currGdl instanceof GdlRule) {
    		GdlRule rule = ((GdlRule) currGdl);
    		GdlSentence head = rule.getHead();
    		List<GdlLiteral> body = rule.getBody();
    		//create a map of variable bindings in head
    		ruleHeadDomainGraph(graph, vars, head);
    		//find matching bindings in body
    		Iterator<GdlLiteral> iter = body.iterator();
    		while (iter.hasNext()) {
    			ruleBodyDomainGraph(graph, vars, iter.next());
    		}
    	} else {
    		System.out.println("ERROR in singleLineDomainGraph: Unrecognized GDL");
    		System.out.println("Type: " + currGdl.getClass().getName());
    	}
	}

	public HashMap<DomainPair, HashSet<DomainPair>> getDomainGraph() {
    	HashMap<DomainPair, HashSet<DomainPair>> graph = new HashMap<DomainPair, HashSet<DomainPair>>();
    	HashMap<String, HashSet<DomainPair>> vars;

    	if(rules == null) {
    		System.out.println("ERROR in getDomainGraph: rules have not been initialized");
    	} else {
    		ListIterator<Gdl> iterator = rules.listIterator();
            while(iterator.hasNext()) {
            	Gdl currGdl = iterator.next();
            	vars = new HashMap<String, HashSet<DomainPair>>();
            	singleLineDomainGraph(graph, vars, currGdl);
            }

            //Final hard-coded rules
            DomainPair truePair = new DomainPair("true", 1);
            DomainPair base1 = new DomainPair("base", 1);
            DomainPair input1 = new DomainPair("input", 1);
            DomainPair input2 = new DomainPair("input", 2);
            DomainPair does1 = new DomainPair("does", 1);
            DomainPair does2 = new DomainPair("does", 2);
            if(!graph.containsKey(truePair)) {
            	HashSet<DomainPair> tempSet = new HashSet<DomainPair>();
            	tempSet.add(base1);
            	graph.put(truePair, tempSet);
            } else {
            	graph.get(truePair).add(base1);
            }
            if(!graph.containsKey(does1)) {
            	HashSet<DomainPair> tempSet = new HashSet<DomainPair>();
            	tempSet.add(input1);
            	graph.put(does1, tempSet);
            } else {
            	graph.get(does1).add(input1);
            }
            if(!graph.containsKey(does2)) {
            	HashSet<DomainPair> tempSet = new HashSet<DomainPair>();
            	tempSet.add(input2);
            	graph.put(does2, tempSet);
            } else {
            	graph.get(does2).add(input2);
            }
    	}

    	return graph;
    }

	private String flattenFnDomainToString(String fnName, Set<String> fnDomain) {
		String ans = fnName + "(";
		Iterator<String> iter = fnDomain.iterator();
		while(iter.hasNext()) {
			ans += iter.next();
			if (iter.hasNext()) {
				ans += " X ";
			}
		}
		ans += ")";
		return ans;
	}

	private String flattenSetToString(Set<String> domain) {
		String ans = "{";
		Iterator<String> iter = domain.iterator();
		while(iter.hasNext()) {
			ans += iter.next();
			if (iter.hasNext()) {
				ans += ", ";
			}
		}
		ans += "}";
		return ans;
	}

	//This function is inefficient because it searches top-down. For greater efficiency, it should be re-done so that the graph edges are reversed and it works bottom-up
	private Set<String> traceDomain(HashMap<DomainPair, HashSet<DomainPair>> domainGraph, HashMap<DomainPair, Set<String>> memos, HashSet<DomainPair> visited, DomainPair interest) {
		visited.add(interest);
		if(memos.containsKey(interest)) {
			return memos.get(interest);
		} else {
//			System.out.println(interest);
			String name = interest.getName();
			int index = interest.getIndex();
			Set<String> ans = new HashSet<String>();
			if(index == 0) {
				ans.add(name);
				return ans;
			} else if(index > 0) {
				HashSet<DomainPair> children = domainGraph.get(interest);
//				ArrayList<String> tempList = new ArrayList<String>();
				Iterator<DomainPair> iter = children.iterator();
				while(iter.hasNext()) {
					DomainPair currChild = iter.next();
//					if(!interest.equals(currChild)) {
					if(!visited.contains(currChild)) {
						Set<String> tracedSet = traceDomain(domainGraph, memos, visited, currChild);
						if(currChild.getIndex() == -1) {
//							tempList.add(currChild.getName() + "(" + tracedString + ")");
//							ans.add(flattenFnDomainToString(currChild.getName(), tracedSet)); //HashSet removes duplicates
							ans.add(currChild.getName() + "()");
						} else {
							Iterator<String> tracedIter = tracedSet.iterator();
							while(tracedIter.hasNext()) {
								ans.add(tracedIter.next()); //HashSet removes duplicates
							}
//							tempList.add(tracedString);
						}
					}
				}
//				Collections.sort(tempList);
//				String outStr = "{";
//				for(int j=0;j<tempList.size();j++) {
//					outStr += tempList.get(j);
//					if(j<tempList.size()-1) {
//						outStr += ", ";
//					}
//				}
//				outStr += "}";
//				return outStr;
				return ans;
			} else if(index == -1) {
				ans.add(name + "()");

				//This is an attempt to write everything out for a function, but it doesn't work properly because that function might not be fully explored
//				ans = new TreeSet<String>();
////				ArrayList<String> dimList = new ArrayList<String>();
//				int searchIndex = 1;
//				DomainPair searchPair = new DomainPair(name, searchIndex);
//				while(domainGraph.containsKey(searchPair)) {
//					Set<String> tracedSet = traceDomain(domainGraph, memos, visited, searchPair);
//					ans.add(flattenSetToString(tracedSet));
////					dimList.add(tracedString);
//					searchIndex ++;
//					searchPair = new DomainPair(name, searchIndex);
//				}


//				String outStr = "";
//				for(int i=0;i<dimList.size();i++) {
//					outStr += dimList.get(i);
//					if (i<dimList.size()-1) {
//						outStr += " X ";
//					}
//				}
//				visited.remove(interest);
//				return outStr;
				return ans;
			} else {
				System.out.println("ERROR in traceDomain: unrecognized index");
				visited.remove(interest);
				return ans;
			}
		}
	}

	//If the int i in a domain pair is > 0, it refers to the ith argument,
	//if  i = 0, the pair is for a constant
	//if i = -1, the pair is for a function that was an argument for something else
	public HashMap<DomainPair, Set<String>> getDomainMap() {
		HashMap<DomainPair, HashSet<DomainPair>> domainGraph = getDomainGraph();
		HashMap<DomainPair, Set<String>> memos = new HashMap<DomainPair, Set<String>>();
		HashSet<DomainPair> visited;
		Iterator<DomainPair> iter = domainGraph.keySet().iterator();
		while(iter.hasNext()) {
			DomainPair curr = iter.next();
			visited = new HashSet<DomainPair>();
			memos.put(curr, traceDomain(domainGraph, memos, visited, curr));
		}
		return memos;
	}


	public void printAllDomains() {
		HashMap<DomainPair, Set<String>> memos = getDomainMap();

		HashSet<String> uniqueKeys = new HashSet<String>();
		Iterator<DomainPair> memoIter = memos.keySet().iterator();
		while(memoIter.hasNext()) {
			DomainPair curr = memoIter.next();
			if (curr.getIndex() != 0 && !uniqueKeys.contains(curr.getName())) {
				uniqueKeys.add(curr.getName());
			}
		}
		ArrayList<String> keys = new ArrayList<String>(uniqueKeys);
		Collections.sort(keys);
		Iterator<String> stringIter = keys.iterator();
		System.out.println("Printing all domains...");
		while(stringIter.hasNext()) {
			String currString = stringIter.next();
			int currIndex = 1;
			DomainPair currPair = new DomainPair(currString, currIndex);
			System.out.print(currString + ": {");
			while (memos.containsKey(currPair)) {
				ArrayList<String> memoVals = new ArrayList<String>(memos.get(currPair));
				Collections.sort(memoVals);
				Iterator<String> memoValsIter = memoVals.iterator();
				while(memoValsIter.hasNext()) {
					System.out.print(memoValsIter.next());
					if (memoValsIter.hasNext()) {
						System.out.print(", ");
					}
				}
//				System.out.print(memos.get(currPair));
				currIndex++;
				currPair = new DomainPair(currString, currIndex);
				if (memos.containsKey(currPair)) {
					System.out.print("} X {");
				}
			}
			System.out.println("}");
//			System.out.println(currString + ": " + memos.get(new DomainPair(currString,-1)));
		}
		System.out.println("Finished printing all domains.\n");
	}
}
