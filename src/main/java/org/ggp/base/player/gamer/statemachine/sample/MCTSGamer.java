//package org.ggp.base.player.gamer.statemachine.sample;
//
//import java.io.BufferedWriter;
//import java.io.File;
//import java.io.FileWriter;
//import java.io.IOException;
//import java.util.ArrayList;
//import java.util.Iterator;
//import java.util.List;
//import java.util.Random;
//
//import org.ggp.base.apps.player.detail.DetailPanel;
//import org.ggp.base.apps.player.detail.SimpleDetailPanel;
//import org.ggp.base.player.gamer.exception.GamePreviewException;
//import org.ggp.base.player.gamer.statemachine.StateMachineGamer;
//import org.ggp.base.util.game.Game;
//import org.ggp.base.util.gdl.grammar.Gdl;
//import org.ggp.base.util.gdl.grammar.GdlTerm;
//import org.ggp.base.util.statemachine.MachineState;
//import org.ggp.base.util.statemachine.Move;
//import org.ggp.base.util.statemachine.Role;
//import org.ggp.base.util.statemachine.StateMachine;
//import org.ggp.base.util.statemachine.cache.CachedStateMachine;
//import org.ggp.base.util.statemachine.exceptions.GoalDefinitionException;
//import org.ggp.base.util.statemachine.exceptions.MoveDefinitionException;
//import org.ggp.base.util.statemachine.exceptions.TransitionDefinitionException;
//import org.ggp.base.util.statemachine.implementation.prover.ProverStateMachine;
//
//
//
// ***** THIS CLASS IS DEPRECATED. *****
// If you want a pure MCTS player, use TestGamer with USE_TRANSFER = false
//
//
//public class MCTSGamer extends StateMachineGamer
//{
//	private List<Gdl> rules;
//	private MCTNode root;
//	private MCTNode origRoot;
//	private Random rand;
//	private int roleIndex;
//
//	private int numRollouts;
//	private long startTime;
//
//	public static final boolean SAVE_MCT_TO_FILE = false;
//	public static final long TIME_THRESHOLD = 1000;
//	public static final double EXPLORE_PARAM = Math.sqrt(2);
//	public static final double NEW_EXPLORE_VALUE = 1000000;
//	public static final int ROLLOUT_MAX_DEPTH = 200;
//
//	public MCTSGamer() {
//		super();
//		this.rules = null;
//		this.root = null;
//		this.origRoot = null;
//		this.rand = new Random();
//	}
//
//	public double mean(ArrayList<Long> lst) {
//		double sum = 0;
//		for(double val : lst) {
//			sum += val;
//		}
//		return sum / lst.size();
//	}
//
//	public double std(ArrayList<Long> lst) {
//		double mean = mean(lst);
//		double sum = 0;
//		for(double val : lst) {
//			sum += Math.pow(val-mean, 2);
//		}
//		return Math.sqrt(sum / lst.size());
//	}
//
//
//    @Override
//    public void stateMachineMetaGame(long timeout) throws TransitionDefinitionException, MoveDefinitionException, GoalDefinitionException
//    {
//    	System.out.println("*** NEW GAME START ***")
//    	rules = this.getMatch().getGame().getRules();
//    	this.roleIndex = -2;
//    	List<Role> allRoles = this.getStateMachine().getRoles();
//    	for(int i=0;i<allRoles.size();i++) {
//    		if(allRoles.get(i).equals(this.getRole())) {
//    			this.roleIndex = i;
//    		}
//    	}
//
//    	RuleGraph g = new RuleGraph(this.rules);
//    	g.genRuleGraph();
//    	RuleGraphRecord rec1 = new RuleGraphRecord(g);
//    	rec1.saveToFile("graph_record.txt", true);
//    	StateMapping basicMapping = new StateMapping(g, null, null);
//    	root = new MCTNode(this.getCurrentState(), this.getStateMachine(), basicMapping, null);
//    	origRoot = root;
//    	startTime = System.currentTimeMillis();
//    	numRollouts = 0;
//    	buildTreeForTime(timeout);
//
////    	System.out.println(root.getNumVisits());
////        System.out.println(root.getTotalReward());
//    }
//
//
//
//
//    @Override
//    public Move stateMachineSelectMove(long timeout) throws TransitionDefinitionException, MoveDefinitionException, GoalDefinitionException
//    {
//    	//start by finding out what actually happened in the last move and shifting our MCT forward appropriately
//    	List<GdlTerm> lastMoveTerms = this.getMatch().getMostRecentMoves();
//    	if (lastMoveTerms != null) {
//    		List<Move> lastMove = new ArrayList<Move>();
//    		for(GdlTerm term : lastMoveTerms) {
//    			lastMove.add(new Move(term));
//    		}
//    		root = root.getChildren().get(lastMove);
//            root.setParent(null);
//    	}
//
//    	//now continue building the MCT
//        buildTreeForTime(timeout);
//        List<Move> selectedMove = selectBestMove();
//        System.out.println("Move: " + selectedMove);
//        System.out.println("All Moves: " + root.getChildren().keySet());
////        System.out.println("Root: " + root);
////        System.out.println("Child: " + root.getChildren().get(selectedMove));
//
////        System.out.println(root.getNumVisits());
////        System.out.println(root.getTotalReward());
//
////        notifyObservers(new GamerSelectedMoveEvent(moves, selection, stop - start));
//        return selectedMove.get(roleIndex);
//    }
//
//    private void buildTreeForTime(long timeout) {
//    	while(System.currentTimeMillis() + TIME_THRESHOLD < timeout) {
//    		MCTNode currNode = root;
//    		while(currNode.isExpanded() && !currNode.isTerminal()) {
//    			currNode = selectChild(currNode);
//    		}
//    		currNode.expandChildren();
//    		if(!currNode.isTerminal()) {
//    			currNode = rollout(currNode);
//    		}
////    		if(currNode.isTerminal()) {
////    			try {
////					System.out.println("Goal: " + currNode.getGoal());
////				} catch (GoalDefinitionException e) {
////					// TODO Auto-generated catch block
////					e.printStackTrace();
////				}
////    		}
//    		if(currNode.isTerminal() && currNode.getNumVisits() == 0) { //if numVisits > 0, just ignore, since we've been at this leaf before
//    			List<Integer> goals = null;
//				try {
//					goals = currNode.getGoals();
//				} catch (GoalDefinitionException e) {
//					System.out.println("ERROR in buildTreeForTime: Looking for goal in non-goal state.");
//					e.printStackTrace();
//				}
//    			backprop(currNode, goals);
//    		}
//    	}
//    }
//
//
//    //give -1 to numNodes to queue the whole MCT
//    private LinkedNode queueNodes(int numNodes) {
//    	LinkedNode linkedRoot = new LinkedNode(origRoot);
//    	LinkedNode currNode = linkedRoot;
//    	LinkedNode lastNode = linkedRoot;
//    	int nodesRemaining = numNodes;
//
//    	while (nodesRemaining != 0 && currNode != null) {
//    		for (MCTNode child : currNode.getValue().getChildren().values()) {
//    			if(nodesRemaining != 0) {
//    				if(child.getNumVisits() > 0) {
//	    				LinkedNode tempNode = new LinkedNode(child);
//	    				lastNode.setNext(tempNode);
//	    				lastNode = lastNode.getNext();
//	    				nodesRemaining--;
//    				}
//    			}
//    		}
//    		currNode = currNode.getNext();
//    	}
//    	return linkedRoot;
//    }
//
//    //give -1 to numNodes to save the whole MCT
//    public void saveMctToFile(String outFileName, int numNodes) {
//		if(origRoot == null) {
//			System.out.println("ERROR in saveMctToFile: MCT has not been initialized.");
//		}
//
//		String outStr = "";
//		LinkedNode q = queueNodes(numNodes);
//		LinkedNode currNode = q;
//
//		while(currNode != null) {
//			MCTNode currMCTNode = currNode.getValue();
//			outStr += currMCTNode.getTotalReward() + " " + currMCTNode.getNumVisits() + " ";
//			if(currMCTNode.getParent() != null) {
//				outStr += currMCTNode.getParent().getNumVisits() + " ";
//			} else {
//				outStr += currMCTNode.getNumVisits() + " "; //this is a hack for root nodes to avoid division by zero or sentinels
//			}
//			outStr += currMCTNode.getStateTree().toString() + "\n";
//			currNode = currNode.getNext();
//		}
//
//		File file = new File(outFileName);
//        FileWriter fr = null;
//        BufferedWriter br = null;
//        try{
//            fr = new FileWriter(file);
//            br = new BufferedWriter(fr, RuleGraphRecord.BUFFER_SIZE);
//            br.write(outStr);
//        } catch (IOException e) {
//            e.printStackTrace();
//        } finally {
//            try {
//                br.close();
//                fr.close();
//            } catch (IOException e) {
//                e.printStackTrace();
//            }
//        }
//	}
//
//
//    private List<Move> selectBestMove() {
//    	List<Move> bestMove = null;
//    	double bestScore = -1000;
//    	for(List<Move> move : root.getChildren().keySet()) {
//    		MCTNode currNode = root.getChildren().get(move);
//    		double currScore = 0;
//    		if (currNode.getNumVisits() > 0) {
//    			currScore = currNode.getTotalReward() / currNode.getNumVisits();
//    		}
//    		if(currScore > bestScore) {
//    			bestMove = move;
//    			bestScore = currScore;
//    		}
//    	}
//    	return bestMove;
//    }
//
//    private MCTNode selectChild(MCTNode currNode) {
////    	System.out.println("selectChild");
//    	MCTNode selected = null;
//    	double bestScore = -1000;
//    	ArrayList<MCTNode> bestNodes = new ArrayList<MCTNode>();
//    	for(MCTNode child : currNode.getChildren().values()) {
//    		double currScore = ucb1(child);
//    		if (currScore > bestScore) {
//    			bestNodes = new ArrayList<MCTNode>();
//    			bestNodes.add(child);
//    			bestScore = currScore;
//    		} else if (currScore == bestScore) {
//    			bestNodes.add(child);
//    		}
//    	}
//    	selected = bestNodes.get(rand.nextInt(bestNodes.size()));
//    	return selected;
//    }
//
//    private double ucb1 (MCTNode currNode) {
//    	if(currNode.getNumVisits() == 0) {
//    		return NEW_EXPLORE_VALUE;
//    	} else {
//    		double r = currNode.getTotalReward();
//    		double n = currNode.getNumVisits();
//    		if(currNode.getParent() == null) {
//    			System.out.println("ERROR: null parent in UCB1");
//    		}
//    		double bigN = currNode.getParent().getNumVisits();
//    		return r/n + EXPLORE_PARAM*Math.sqrt(Math.log(bigN)/n);
//    	}
//    }
//
//    private List<Move> randomMove(MCTNode node) {
//    	List<Move> result = null;
//    	int numMoves = node.getChildren().size();
//    	int selectedIndex = rand.nextInt(numMoves);
//    	int counter = 0;
//    	Iterator<List<Move>> iter = node.getChildren().keySet().iterator();
//    	while(iter.hasNext() && counter <= selectedIndex) {
//    		List<Move> tempMove = iter.next();
//    		if(counter == selectedIndex) {
//    			result = tempMove;
//    		}
//    		counter++;
//    	}
//    	return result;
//    }
//
//    private MCTNode rollout (MCTNode startNode) {
//    	MCTNode currNode = startNode;
//    	int depth = 0;
//    	this.numRollouts ++;
//    	while(!currNode.isTerminal() && depth < ROLLOUT_MAX_DEPTH) {
//    		currNode.expandChildren();
//    		List<Move> randMove = randomMove(currNode);
//    		currNode = currNode.getChildren().get(randMove);
//    		depth++;
//    	}
//    	if(depth == ROLLOUT_MAX_DEPTH) {
//    		System.out.println("ERROR in rollout: max depth exceeded.");
//    	}
////    	System.out.println("Rollout, depth " + depth);
//    	try {
//			if(currNode.isTerminal() && currNode.getGoal() == 100) {
//				System.out.println("Found goal. " + this.numRollouts + " rollouts. " + (System.currentTimeMillis() - this.startTime) + " ms.");
//			}
//		} catch (GoalDefinitionException e) {
//			// TODO Auto-generated catch block
//			e.printStackTrace();
//		}
//    	return currNode;
//    }
//
//    private void backprop (MCTNode startNode, double reward) {
//    	MCTNode currNode = startNode;
//    	while(currNode != null) {
//    		currNode.setTotalReward(currNode.getTotalReward() + reward);
//    		currNode.setNumVisits(currNode.getNumVisits() + 1);
//    		currNode = currNode.getParent();
//    	}
//    }
//
//    private int[] depth = new int[1];
//    int performDepthChargeFromMove(MachineState theState, Move myMove) {
//        StateMachine theMachine = getStateMachine();
//        try {
//            MachineState finalState = theMachine.performDepthCharge(theMachine.getRandomNextState(theState, getRole(), myMove), depth);
//            return theMachine.getGoal(finalState, getRole());
//        } catch (Exception e) {
//            e.printStackTrace();
//            return 0;
//        }
//    }
//
//    /** This will currently return "SampleGamer"
//     * If you are working on : public abstract class MyGamer extends SampleGamer
//     * Then this function would return "MyGamer"
//     */
//    @Override
//    public String getName() {
//    	return getClass().getSimpleName();
//    }
//
//    // This is the default State Machine
//    @Override
//    public StateMachine getInitialStateMachine() {
//        return new CachedStateMachine(new ProverStateMachine());
//    }
//
//    // This is the default Sample Panel
//    @Override
//    public DetailPanel getDetailPanel() {
//        return new SimpleDetailPanel();
//    }
//
//
//
//    @Override
//    public void stateMachineStop() {
//    	if(SAVE_MCT_TO_FILE) {
//        	saveMctToFile("MCT.txt", -1);
//        }
//    }
//
//    @Override
//    public void stateMachineAbort() {
//        // Sample gamers do no special cleanup when the match ends abruptly.
//    }
//
//    @Override
//    public void preview(Game g, long timeout) throws GamePreviewException {
//        // Sample gamers do no game previewing.
//    	System.out.println("Preview was called");
//    }
//}