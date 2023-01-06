package org.ggp.base.player.gamer.statemachine.sample;

import java.io.BufferedReader;
import java.io.BufferedWriter;
import java.io.File;
import java.io.FileReader;
import java.io.FileWriter;
import java.io.IOException;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Scanner;
import java.util.Set;
import java.util.StringTokenizer;

public class ReducedMCTree {

	private ArrayList<ReducedMCTNode> states;
	private HashMap<Integer,List<Integer>> stateCompLookUp;
	private HashMap<List<Integer>, List<Integer>> stateCompToOwnerIDs;
	private List<HashMap<List<Integer>, Pair<Double, Long>>> specificMoveTotalData;
	private List<HashMap<Integer, Pair<Double, Long>>> generalMoveTotalData;
	private List<Double> totalReward;
	private List<Long> totalVisits;
	private List<Double> bestSpecificRatio;
	private List<Double> bestGeneralRatio;

	public ReducedMCTree() {
		this.states = new ArrayList<ReducedMCTNode>();
		this.stateCompLookUp = new HashMap<Integer,List<Integer>>();
		this.stateCompToOwnerIDs = new HashMap<List<Integer>, List<Integer>>();
		this.specificMoveTotalData = new ArrayList<HashMap<List<Integer>, Pair<Double, Long>>>();
		this.generalMoveTotalData = new ArrayList<HashMap<Integer, Pair<Double, Long>>>();
		this.totalReward = new ArrayList<Double>();
		this.totalVisits = new ArrayList<Long>();
		this.bestSpecificRatio = new ArrayList<Double>();
		this.bestGeneralRatio = new ArrayList<Double>();
	}

	public ReducedMCTree(ArrayList<ReducedMCTNode> states, List<HashMap<List<Integer>, Pair<Double, Long>>> specificMoveTotalData, List<HashMap<Integer, Pair<Double, Long>>> generalMoveTotalData) {
		this.states = states;
		this.stateCompLookUp = new HashMap<Integer,List<Integer>>();
		this.stateCompToOwnerIDs = new HashMap<List<Integer>, List<Integer>>();
		this.specificMoveTotalData = specificMoveTotalData;
		this.generalMoveTotalData = generalMoveTotalData;
		this.totalReward = new ArrayList<Double>();
		this.totalVisits = new ArrayList<Long>();
		this.bestSpecificRatio = new ArrayList<Double>();
		this.bestGeneralRatio = new ArrayList<Double>();
	}


	public ArrayList<ReducedMCTNode> getStates() {
		return this.states;
	}

	public HashMap<List<Integer>, List<Integer>> getStateCompToOwnerIDs() {
		return this.stateCompToOwnerIDs;
	}


	public HashMap<List<Integer>, Pair<Double, Long>> getSpecificMoveTotalData(int roleIndex) {
		return this.specificMoveTotalData.get(roleIndex);
	}

	public HashMap<Integer, Pair<Double, Long>> getGeneralMoveTotalData(int roleIndex) {
		return this.generalMoveTotalData.get(roleIndex);
	}

	public List<HashMap<List<Integer>, Pair<Double, Long>>> getSpecificMoveTotalData() {
		return this.specificMoveTotalData;
	}

	public List<HashMap<Integer, Pair<Double, Long>>> getGeneralMoveTotalData() {
		return this.generalMoveTotalData;
	}

	public Double getTotalReward(int roleIndex) {
		return this.totalReward.get(roleIndex);
	}

	public Long getTotalVisits(int roleIndex) {
		return this.totalVisits.get(roleIndex);
	}

	public Double getBestSpecificRatio(int roleIndex) {
		return this.bestSpecificRatio.get(roleIndex);
	}

	public Double getBestGeneralRatio(int roleIndex) {
		return this.bestGeneralRatio.get(roleIndex);
	}

	public void loadStatesFromFile(String inFileName) {
		this.states = new ArrayList<ReducedMCTNode>();
		Scanner s = null;

        try {
            s = new Scanner(new BufferedReader(new FileReader(inFileName), RuleGraphRecord.BUFFER_SIZE));
            int lineNumber = 0;
            int numPlayers = 0;
            ArrayList<HashMap<Integer,List<Integer>>> moveLookUp = new ArrayList<HashMap<Integer,List<Integer>>>(); //for each role, keep a HashMap of move IDs to their full list of components (IDs do NOT correspond to rule graph IDs)

            while (s.hasNext()) {
                String line = s.nextLine();
                if(line.length() > 0) {
                	StringTokenizer tok = new StringTokenizer(line);

                	if(lineNumber <= 0) { //unique line(s) at top of file
                		numPlayers = Integer.parseInt(tok.nextToken());
                		for(int i=0;i<numPlayers;i++) {
                			this.specificMoveTotalData.add(new HashMap<List<Integer>, Pair<Double, Long>>());
                			this.generalMoveTotalData.add(new HashMap<Integer, Pair<Double, Long>>());
                			this.totalReward.add(0.0);
                			this.totalVisits.add(0l);
                		}

                	} else if(lineNumber <= numPlayers) { //one line for each player giving general move data
                		int roleIndex = lineNumber - 1;
                		while(tok.hasMoreTokens()) {
                			double reward = Double.parseDouble(tok.nextToken());
                			long visits = Long.parseLong(tok.nextToken());
                			int id = Integer.parseInt(tok.nextToken());
                			if(tok.hasMoreTokens()) {
                				tok.nextToken(); //pitch the *
                			}
                			this.generalMoveTotalData.get(roleIndex).put(id, new Pair<Double,Long>(reward, visits));
                		}

                	} else if(lineNumber <= 2*numPlayers) { //one line for each player giving specific move data
                		int roleIndex = lineNumber - numPlayers - 1;
                		while(tok.hasMoreTokens()) {
                			double reward = Double.parseDouble(tok.nextToken());
                			long visits = Long.parseLong(tok.nextToken());
                			List<Integer> specIDs = new ArrayList<Integer>();
                			String currTok = tok.nextToken();
                			while(!currTok.equals("*")) {
                				specIDs.add(Integer.parseInt(currTok));
                				if(tok.hasMoreTokens()) {
                					currTok = tok.nextToken();
                				} else {
                					break;
                				}
                			}
                			this.specificMoveTotalData.get(roleIndex).put(specIDs, new Pair<Double,Long>(reward, visits));
                		}

                	} else if(lineNumber <= 3*numPlayers) { // one line for each player assigning an ID to each unique move
                		moveLookUp.add(new HashMap<Integer,List<Integer>>());
                		int currRole = lineNumber - 2*numPlayers - 1;
                		while(tok.hasMoreTokens()) {
                			String currTok = tok.nextToken();
                			int moveID = -1;
                			ArrayList<Integer> moveList = new ArrayList<Integer>();
                			try{
                	            moveID = Integer.parseInt(currTok);
                	        } catch (NumberFormatException e) {
                	            System.out.println("Encountered bad move ID in loadSourceStatesFromFile.");
                	            System.out.println(e);
                	        }
                			currTok = tok.nextToken();
                			if(currTok.equals("(")) { //move is a function
                				currTok = tok.nextToken();
                				while(!currTok.equals(")")) {
                					try{
                        	            moveList.add(Integer.parseInt(currTok));
                        	        } catch (NumberFormatException e) {
                        	            System.out.println("Encountered bad function or unexpected symbol in loadSourceStatesFromFile.");
                        	            System.out.println(e);
                        	        }
                					currTok = tok.nextToken();
                				}
                			} else { //move is a constant
                				try{
                    	            moveList.add(Integer.parseInt(currTok));
                    	        } catch (NumberFormatException e) {
                    	            System.out.println("Encountered bad constant or unexpected symbol in loadSourceStatesFromFile.");
                    	            System.out.println(e);
                    	        }
                			}
                			moveLookUp.get(currRole).put(moveID, moveList);
                		}

                	} else if(lineNumber <= 3*numPlayers + 1) { //one line assigning an ID to each unique state component
                		int currCompNum = 0;
                		List<Integer> currComp = new ArrayList<Integer>();
                		while(tok.hasMoreTokens()) {
                			String currTok = tok.nextToken();
                			if(currTok.equals("*")) {
                				this.stateCompLookUp.put(currCompNum, currComp);
                				currCompNum++;
                				currComp = new ArrayList<Integer>();
                			} else {
                				currComp.add(Integer.parseInt(currTok));
                			}
                		}
                		if(currComp.size() > 0) {
                			this.stateCompLookUp.put(currCompNum, currComp);
            				currCompNum++;
                		}

                	} else { //regular node lines
		                List<Double> totalReward = new ArrayList<Double>();
		                int id = Integer.parseInt(tok.nextToken());
		                for(int i=0;i<numPlayers;i++) { //read in a reward value for each player
		                	totalReward.add(Double.parseDouble(tok.nextToken()));
		                }
		                int numVisits = Integer.parseInt(tok.nextToken());
		                int numParentVisits = Integer.parseInt(tok.nextToken());
		                int numSiblings = Integer.parseInt(tok.nextToken());
		                int numVisitsOld = Integer.parseInt(tok.nextToken());

		                //this block assumes states are represented as lists of components
		                Set<List<Integer>> newStateList = new HashSet<List<Integer>>();
		                String currTok = tok.nextToken();
		                while(!currTok.equals("*")) {
		                	Integer currID = Integer.parseInt(currTok);
		                	List<Integer> fullComp = this.stateCompLookUp.get(currID);
		                	newStateList.add(fullComp);
		                	if(!stateCompToOwnerIDs.containsKey(fullComp)) {
		                		this.stateCompToOwnerIDs.put(fullComp, new ArrayList<Integer>());
		                	}
		                	this.stateCompToOwnerIDs.get(fullComp).add(id);
		                	currTok = tok.nextToken();
		                }

//		                System.out.println("*** " + currTok);
//		                StateNode newStateTree = genStateTreeFromString(currTok); // <---- If you want state trees to work, you need to change this line to something that parses the new state format
		                ReducedMCTNode newState = new ReducedMCTNode(id, newStateList, totalReward, numVisits, numParentVisits, numSiblings, numVisitsOld);

		                while(tok.hasMoreTokens()) { //read moves after state
		                	List<Integer> currMoveIDs = new ArrayList<Integer>();
		                	List<Double> currChildRewards = new ArrayList<Double>();
		                	int currNumChildVisits = 0;
		                	for(int i=0;i<numPlayers;i++) {
		                		currTok = tok.nextToken(); //"* \t\n\r\f");
//		                		System.out.println(currTok);
		                		currMoveIDs.add(Integer.parseInt(currTok));
		                	}
		                	for(int i=0;i<numPlayers;i++) {
		                		currTok = tok.nextToken();
		                		currChildRewards.add(Double.parseDouble(currTok));
		                	}
		                	currTok = tok.nextToken();
		                	currNumChildVisits = Integer.parseInt(currTok);

		                	List<List<Integer>> unPackedMoves = new ArrayList<List<Integer>>();
		                	for(int i=0;i<numPlayers;i++) {
		                		int moveID = currMoveIDs.get(i);
		                		unPackedMoves.add(moveLookUp.get(i).get(moveID));
		                	}
		                	newState.putChildData(unPackedMoves, new Pair<List<Double>,Integer>(currChildRewards, currNumChildVisits));

		                	//This chunk is deprecated
//		                	for(int i=0;i<numPlayers;i++) {
//		                		if(!this.specificMoveTotalData.get(i).containsKey(unPackedMoves.get(i))) {
//		                			this.specificMoveTotalData.get(i).put(unPackedMoves.get(i), new Pair<Double, Integer>(0.0,0));
//		                		}
//		                		if(!this.generalMoveTotalData.get(i).containsKey(unPackedMoves.get(i).get(0))) {
//		                			this.generalMoveTotalData.get(i).put(unPackedMoves.get(i).get(0), new Pair<Double, Integer>(0.0,0));
//		                		}
//		                		Pair<Double, Integer> currSpecific = this.specificMoveTotalData.get(i).get(unPackedMoves.get(i));
//		                		Pair<Double, Integer> newSpecific = new Pair<Double, Integer>(currSpecific.getKey()+currChildRewards.get(i), currSpecific.getValue()+currNumChildVisits);
//		                		this.specificMoveTotalData.get(i).put(unPackedMoves.get(i), newSpecific);
//		                		Pair<Double, Integer> currGeneral = this.generalMoveTotalData.get(i).get(unPackedMoves.get(i).get(0));
//		                		Pair<Double, Integer> newGeneral = new Pair<Double, Integer>(currGeneral.getKey()+currChildRewards.get(i), currGeneral.getValue()+currNumChildVisits);
//		                		this.generalMoveTotalData.get(i).put(unPackedMoves.get(i).get(0), newGeneral);
//		                		this.totalReward.set(i, this.totalReward.get(i) + currChildRewards.get(i));
//		                		this.totalVisits.set(i, this.totalVisits.get(i) + currNumChildVisits);
//		                	}
		                }
		                this.states.add(newState);
                	}
                }
                lineNumber++;
            }
            for(int i=0;i<numPlayers;i++) {
            	this.bestSpecificRatio.add(0.0);
            	this.bestGeneralRatio.add(0.0);
                for(List<Integer> specific : this.specificMoveTotalData.get(i).keySet()) {
                	Pair<Double, Long> currData = this.specificMoveTotalData.get(i).get(specific);
                	double currRatio = currData.getKey() / currData.getValue();
                	if(currRatio > this.bestSpecificRatio.get(i)) {
                		this.bestSpecificRatio.set(i, currRatio);
                	}
                }
                for(int general : this.generalMoveTotalData.get(i).keySet()) {
                	Pair<Double, Long> currData = this.generalMoveTotalData.get(i).get(general);
                	double currRatio = currData.getKey() / currData.getValue();
                	if(currRatio > this.bestGeneralRatio.get(i)) {
                		this.bestGeneralRatio.set(i, currRatio);
                	}
                }
            }

        } catch (Exception e) {
            System.out.println("ERROR loading states from file");
            System.out.println(e);
        } finally {
            if (s != null) {
                s.close();
            }
        }

	}


	//convert a Move into a String of the form "( X Y1 Y2... )" for functions or "X" for constants where Xs and Ys correspond to the ID of the top level node for that name
    //used when writing moves to the MCT file - IDs should match with those in the rule graph file
	public static String moveToIDString(List<Integer> move) {
		String result = "";
		if(move.size() == 1) {
			result += move.get(0);
		} else {
			result += "( ";
			for(int i : move) {
				result += i + " ";
			}
			result += ")";
		}
		return result;
	}


    public int saveToFile(String outFileName) {
		int count = 0;
		int numRoles = this.specificMoveTotalData.size();
		String headerStr = "";
		String outStr = "";
		String stateStr = "";
		String[] moveIDStr = new String[numRoles];
		HashMap<List<Integer>, Integer> compIDLookUp = new HashMap<List<Integer>, Integer>();
		int nextCompID = 0;
		ArrayList<List<Integer>> compsInOrder = new ArrayList<List<Integer>>();

		//Assign IDs to each move seen with a look-up table at the top to save file size
		int[] nextMoveID = new int[numRoles];
		List<HashMap<List<Integer>, Integer>> moveToID = new ArrayList<HashMap<List<Integer>,Integer>>();
		for(int i=0;i<numRoles;i++) {
			nextMoveID[i] = 0;
			moveToID.add(new HashMap<List<Integer>,Integer>());
			moveIDStr[i] = "";
		}

		headerStr += numRoles + "\n"; //At the top, print the number of players on a line by itself

		for(ReducedMCTNode currNode : this.states) {
			outStr += count + " "; //assigns an ascending ID value to each node
			for(int i=0;i<numRoles;i++) {
				outStr += currNode.getTotalReward().get(i) + " "; //Print the reward for each player
			}
			outStr += currNode.getNumVisits() + " "; //Print visits to node
			outStr += currNode.getNumParentVisits() + " "; //Print total visits to all of node's parents
			outStr += currNode.getNumSiblings() + " ";

			Set<List<Integer>> currState = currNode.getStateSet();
			for(List<Integer> comp : currState) { //replace whole state components with IDs and add to outStr
				int currCompID;
				if(!compIDLookUp.containsKey(comp)) {
					currCompID = nextCompID;
					compIDLookUp.put(comp, currCompID);
					nextCompID++;
					compsInOrder.add(comp);
				} else {
					currCompID = compIDLookUp.get(comp);
				}
				outStr += currCompID + " ";
			}

			outStr += "* "; //mark the end of state and beginning of list of moves linking to child states

			//Store UCT relevant child info pointed to by each possible move combination
			HashMap<List<List<Integer>>, Pair<List<Double>, Integer>> childData = currNode.getChildData();
			for(List<List<Integer>> move : childData.keySet()) {
				for(int i=0;i<move.size();i++) {
					int currMoveID;
					HashMap<List<Integer>, Integer> roleMoveToID = moveToID.get(i);
					List<Integer> roleMove = move.get(i);
					if(roleMoveToID.containsKey(roleMove)) {
						currMoveID = roleMoveToID.get(roleMove);
					} else {
						currMoveID = nextMoveID[i];
						nextMoveID[i] += 1;
						roleMoveToID.put(roleMove, currMoveID);
						moveIDStr[i] += currMoveID + " " + moveToIDString(roleMove) + " ";
					}
					outStr += currMoveID + " ";
				}

				for(int i=0;i<numRoles;i++) {
					outStr += childData.get(move).getKey().get(i) + " ";
				}
				outStr += childData.get(move).getValue() + "  "; //Double spaces will indicate a new move being recorded
			}
			outStr += "\n";

			count++;
			if(count%1000 == 0) {
				System.out.println(count + " nodes...");
			}
		}

		for(List<Integer> comp : compsInOrder) {
			if(!stateStr.equals("")) {
				stateStr += "* ";
			}
			for(int i : comp) {
				stateStr += i + " ";
			}
		}

		//Record move data - 2 lines per role
		String genMoveStr = "";
		String specMoveStr = "";
		for(int i=0;i<numRoles;i++) {
			boolean first = true;
			for(int genID : this.generalMoveTotalData.get(i).keySet()) {
				if(!first) {
					genMoveStr += "* ";
				}
				first = false;
				Pair<Double,Long> genData = this.generalMoveTotalData.get(i).get(genID);
				genMoveStr += genData.getKey() + " " + genData.getValue() + " " + genID + " ";
			}
			genMoveStr += "\n";

			first = true;
			for(List<Integer> specID : this.specificMoveTotalData.get(i).keySet()) {
				if(!first) {
					specMoveStr += "* ";
				}
				first = false;
				Pair<Double,Long> specData = this.specificMoveTotalData.get(i).get(specID);
				specMoveStr += specData.getKey() + " " + specData.getValue() + " ";
				for(int id : specID) {
					specMoveStr += id + " ";
				}
			}
			specMoveStr += "\n";
		}


		//Write data to file
		File file = new File(TestGamer.MCT_SAVE_DIR + "/" + outFileName);
        FileWriter fr = null;
        BufferedWriter br = null;
        try{
            fr = new FileWriter(file);
            br = new BufferedWriter(fr, RuleGraphRecord.BUFFER_SIZE);
            br.write(headerStr);
            br.write(genMoveStr);
            br.write(specMoveStr);
            for(int i=0;i<numRoles;i++) {
            	br.write(moveIDStr[i] + "\n");
            }
            br.write(stateStr + "\n");
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

        return count;
	}
}
