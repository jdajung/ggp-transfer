package org.ggp.base.player.gamer.statemachine.sample;

import java.io.BufferedWriter;
import java.io.File;
import java.io.FileWriter;
import java.io.IOException;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;
import java.util.Random;
import java.util.Set;
import java.util.TreeMap;
import java.util.TreeSet;

import org.ggp.base.apps.player.detail.DetailPanel;
import org.ggp.base.apps.player.detail.SimpleDetailPanel;
import org.ggp.base.player.gamer.exception.GamePreviewException;
import org.ggp.base.player.gamer.statemachine.StateMachineGamer;
import org.ggp.base.player.gamer.statemachine.sample.RuleGraph.RuleNodeColour;
import org.ggp.base.util.game.Game;
import org.ggp.base.util.gdl.grammar.Gdl;
import org.ggp.base.util.gdl.grammar.GdlConstant;
import org.ggp.base.util.gdl.grammar.GdlFunction;
import org.ggp.base.util.gdl.grammar.GdlTerm;
import org.ggp.base.util.statemachine.Move;
import org.ggp.base.util.statemachine.Role;
import org.ggp.base.util.statemachine.StateMachine;
import org.ggp.base.util.statemachine.cache.CachedStateMachine;
import org.ggp.base.util.statemachine.exceptions.GoalDefinitionException;
import org.ggp.base.util.statemachine.exceptions.MoveDefinitionException;
import org.ggp.base.util.statemachine.exceptions.TransitionDefinitionException;
import org.ggp.base.util.statemachine.implementation.prover.ProverStateMachine;


public class TestGamerSRA extends StateMachineGamer
{
	private List<Gdl> rules;
	private MCTNode root;
	private MCTNode origRoot;
	private HashMap<Set<List<Integer>>, MCTNode> existingNodes;
	private StateMapping sMap;
	private Random rand;
	private List<Role> allRoles;
	private int roleIndex;
	private List<Integer> mappedRoleIndices;

	private int numTurns;
	private int numRollouts;
	private long startTime;
//	private boolean goalReported;
	private int nextTupleIndex;
	private HashMap<Integer, String> tuplesByIndex = new HashMap<Integer, String>();
	private HashMap<String, Integer> indicesByTuple = new HashMap<String, Integer>();
	private List<HashMap<List<Integer>, Pair<Double, Long>>> specMoveData;
	private List<HashMap<Integer, Pair<Double, Long>>> genMoveData;
	private LinkedList<Set<List<Integer>>> stateHistory;

	//These are initialization parameters explained in and set by AutoPlayer
	public boolean USE_TRANSFER;
	public boolean USE_PLAY_TRANSFER;
	public boolean USE_SELECTION_TRANSFER;
	public boolean USE_ROLLOUT_TRANSFER;
	public double PLAY_TRANSFER_RATIO;
	public double SELECTION_TRANSFER_RATIO;
	public boolean SAVE_RULE_GRAPH_TO_FILE;
	public boolean SAVE_MCT_TO_FILE;
	public String MCT_READ_DIR;
	public String EXPERIMENT_SAVE_DIR;

	public int NUM_SAVED_MCT_NODES = -1; //10000; //-1 to save all (may be way too many to do this)

	public static final long TIME_THRESHOLD = 2000;
	public static final double EXPLORE_PARAM = Math.sqrt(2);
	public static final double NEW_EXPLORE_VALUE = 1000000;
	public static final int ROLLOUT_MAX_DEPTH = 220;
	public static final double MAX_REWARD_VALUE = 100.0;
	public static final double DISCOUNT_FACTOR = 0.98;
	public static final double CERTAINTY_OFFSET = 4.0;
	public static final double CERTAINTY_STEEPNESS = 1.0;
	public static final double STATE_CERTAINTY_OFFSET = 0.8;
	public static final double STATE_CERTAINTY_STEEPNESS = 20;
	public static final String PLAY_SELECT_MODE = "reward";  //one of "visits", or "reward"
	public static final String RULE_GRAPH_FILE = "checkers_debug.txt";
	public static final String MCT_SAVE_DIR = "MCTs/checkers";
	public static final String EXP_SUMMARY_FILE = "summary.txt";

	public static final double HEURISTIC_WEIGHT = 10.0;
	public static final double TRANSFER_WEIGHT = 1.0;
	public static final double TRANSFER_DECAY_PER_VISIT = 0.9;
	public static final double TRANSFER_THRESHOLD = 0.1; //To save time, ignore transfer completely when it decays beyond this value

	public static final double FLOAT_THRESH = 0.00001;

	public TestGamerSRA() {
		super();
		this.rules = null;
		this.root = null;
		this.origRoot = null;
		this.existingNodes = new HashMap<Set<List<Integer>>, MCTNode>();
		this.sMap = null;
		this.rand = new Random();
		this.allRoles = null;
		this.numTurns = 0;
		this.numRollouts = 0;
		this.nextTupleIndex = 0;
		this.tuplesByIndex = new HashMap<Integer, String>();
		this.indicesByTuple = new HashMap<String, Integer>();
		this.stateHistory = new LinkedList<Set<List<Integer>>>();

		this.USE_TRANSFER = false;
		this.SAVE_RULE_GRAPH_TO_FILE = true;
		this.SAVE_MCT_TO_FILE = true;
	}

	//This is a janky hack to set parameters that should be set in the constructor
	//But the GGP library only allows default constructors, so whatever
	public void initParams(List<?> params) {
		this.USE_TRANSFER = (Boolean)(params.get(0));
		this.USE_PLAY_TRANSFER = (Boolean)(params.get(1));
		this.USE_SELECTION_TRANSFER = (Boolean)(params.get(2));
		this.USE_ROLLOUT_TRANSFER = (Boolean)(params.get(3));
		this.PLAY_TRANSFER_RATIO = (Double) params.get(4);
		this.SELECTION_TRANSFER_RATIO = (Double) params.get(5);
		this.SAVE_RULE_GRAPH_TO_FILE = (Boolean)(params.get(6));
		this.SAVE_MCT_TO_FILE = (Boolean)(params.get(7));
		this.MCT_READ_DIR = (String)(params.get(8));
		this.EXPERIMENT_SAVE_DIR = (String)(params.get(9));
//		System.out.println(params);
	}


	//This method initializes our agent. It will be called once at the beginning of a game.
    @Override
    public void stateMachineMetaGame(long timeout) throws TransitionDefinitionException, MoveDefinitionException, GoalDefinitionException
    {
    	System.out.println("*** NEW GAME START ***");
    	rules = this.getMatch().getGame().getRules(); //always need this line

//    	RuleGraph g = new RuleGraph(this.rules);
//    	g.genRuleGraph();
//    	RuleGraphRecord rec1 = new RuleGraphRecord(g);
//    	rec1.saveToFile("test.txt", true);



    	//Mapping experiment stuff
//    	MappingExperiment experiment = new MappingExperiment(rules, 8288034731336811092L);
//    	experiment.runTrials(20, "two_lines", "8_queens_debug.txt", "none", 0);
////    	experiment.runTrialSuite(20, "two_lines", "8_queens_debug.txt", "dup_any", 0, 1000, 20);
//    	Scanner scan = new Scanner(System.in);
//    	scan.nextLine(); //do nothing until you get keyboard input



//    	numRollouts = 0;
//    	goalReported = false;

//    	for(Gdl rule : rules) {
//    		System.out.println(rule);
//    	}
//    	System.out.println("\n\n\n\n\n\n\n\n\n\n");

//    	RuleGraph g = new RuleGraph(this.rules);

    	//10 billion operations is pretty slow. 100 million is pretty doable.
//    	long k = 0;
//    	for(long j=0;j<1000000000000l;j++) {
//    		if (k % 10000000000l == 0) {
//    			System.out.println(k);
//    		}
//    		k++;
//    	}

    	//Print rules
//    	System.out.println("Rules:");
//        System.out.println(rules);


        //Domain graph stuff
//        DomainComputer dc = new DomainComputer(this.rules);
//        HashMap<DomainPair, HashSet<DomainPair>> domainGraph = dc.getDomainGraph();
//
//        Iterator<DomainPair> iter = domainGraph.keySet().iterator();
//        while (iter.hasNext()) {
//        	DomainPair currKey = iter.next();
//        	System.out.println("Key: " + currKey);
//        	System.out.println("Edges:");
//        	HashSet<DomainPair> edges = domainGraph.get(currKey);
//        	Iterator<DomainPair> edgeIterator = edges.iterator();
//        	while (edgeIterator.hasNext()) {
//        		System.out.println(edgeIterator.next());
//        	}
//        	System.out.println();
//        }
//
//        dc.printAllDomains();


        //Rule graph stuff
//        g.genRuleGraph();
//        g.printRuleGraph();


        //Rule graph record stuff
//        RuleGraphRecord rec1 = new RuleGraphRecord(g);
//        RuleGraphRecord rec2 = new RuleGraphRecord();
//        rec1.saveToFile("test.txt", true);
//        System.out.println("************************* Record 1 ********************************");
//        rec1.printRuleGraphRecord();
//        rec2.loadFromFile("test.txt", true);
//        System.out.println("************************* Record 2 ********************************");
//        rec2.printRuleGraphRecord();


    	//Edit Distance Timing Stuff
//    	ArrayList<Long> genTimes = new ArrayList<Long>();
//        int numTrials = 10;
//        g.genRuleGraph();
//    	RuleGraphRecord rec = new RuleGraphRecord();
//    	rec.loadFromFile("chess.txt");
//        for(int i=0;i<numTrials;i++) {
//        	long startTime = System.nanoTime();
//        	EditDistance edit = new EditDistance(g.getGraph(), rec.getGraph());
//        	float dist = edit.calcDistance(CostType.COLOUR_ONLY);
//        	long endTime = System.nanoTime();
//        	genTimes.add(endTime - startTime);
//        	System.out.println(endTime - startTime);
//        }
//        System.out.println("Gen: " + genTimes);
//        System.out.println("Gen Mean: " + mean(genTimes)/1000000.0);
//        System.out.println("Gen STD: " + std(genTimes)/1000000);



        //Edit Distance Stuff
//    	g.genRuleGraph();
//    	Collections.reverse(g.getGraph());
//    	RuleGraphRecord rec = new RuleGraphRecord();
//    	rec.loadFromFile("tictactoe.txt");
//    	System.out.println(g.getGraph().size());
//    	System.out.println(rec.getGraph().size());
//    	EditDistance edit = new EditDistance(g.getGraph(), rec.getGraph());
//    	float dist = edit.calcDistance(CostType.COLOUR_ONLY);
//    	HashMap<Integer, Integer> mapping = edit.getMapping();
//    	HashMap<Integer, Integer> revMapping = edit.getRevMapping();
//
//    	System.out.println("Distance: " + dist + "\n");
//    	System.out.println("Mapping:");
//    	ArrayList<Integer> indices = new ArrayList<Integer>();
//    	for (int index : mapping.keySet()) {
//    		indices.add(index);
//    	}
//    	Collections.sort(indices);
//    	for (int index : indices) {
//    		int g1Index = -1;
//    		int g2Index = -1;
//    		if(index != -1) {
//    			g1Index = edit.getG1().get(index).getId();
//    		}
//    		if (mapping.get(index) != -1) {
//    			g2Index = edit.getG2().get(mapping.get(index)).getId();
//    		}
//    		System.out.print("(" + g1Index + ", " + g2Index + ") ");
//    	}
//    	System.out.println("\n");
//    	System.out.println("Reverse Mapping:");
//    	indices = new ArrayList<Integer>();
//    	for (int index : revMapping.keySet()) {
//    		indices.add(index);
//    	}
//    	Collections.sort(indices);
//    	for (int index : indices) {
//    		int g1Index = -1;
//    		int g2Index = -1;
//    		if(index != -1) {
//    			g2Index = edit.getG2().get(index).getId();
//    		}
//    		if (revMapping.get(index) != -1) {
//    			g1Index = edit.getG1().get(revMapping.get(index)).getId();
//    		}
//    		System.out.print("(" + g2Index + ", " + g1Index + ") ");
//    	}
//    	System.out.println("\n");



    	//State stuff
//    	MachineState currState = getCurrentState();
//    	System.out.println(currState.getContents());
//    	for(GdlSentence sentence : currState.getContents()) {
//    		if (sentence instanceof GdlProposition) {
//    			GdlProposition prop = (GdlProposition) sentence;
//    			System.out.println("Prop: " + prop.getName());
//    		} else if (sentence instanceof GdlRelation){
//    			GdlRelation rel = (GdlRelation) sentence;
//    			System.out.println("Relation: " + rel.getName() + " - " + rel.getBody());
//    			for(GdlTerm term : rel.getBody()) {
//    				System.out.println(term.getClass());
//    			}
//    		} else {
//    			System.out.println("ERROR: unrecognized sentence");
//    		}
//    	}
//    	g.genRuleGraph();
//    	System.out.println(g.getTopLevelNames());
//    	System.out.println(g.getGraph().get(g.getTopLevelNames().get("cell")));



    	//StateMapping stuff
//    	RuleGraphRecord rec = new RuleGraphRecord();
//    	rec.loadFromFile("tictactoe.txt");
//    	StateMapping sMap = new StateMapping(g, rec);
//    	System.out.println(getCurrentState().getContents());
//    	System.out.println(sMap.genTargetStateTree(getCurrentState()).toString());
//
//    	StateNode node1 = sMap.genStateTreeFromString("( -1 ( 34 ( 16 ( 16 ( 33  )  ) ( 20 ( 33  )  ) ( 11 ( 33  )  )  ) ( 20 ( 16 ( 33  )  ) ( 20 ( 33  )  ) ( 11 ( 33  )  )  ) ( 11 ( 16 ( 33  )  ) ( 20 ( 33  )  ) ( 11 ( 33  )  )  )  ) ( 89 ( 3  )  )  ) ");
//    	StateNode node2 = sMap.genStateTreeFromString("( -1 ( 34 ( 16 ( 16 ( 33  )  ) ( 20 ( 33  )  ) ( 11 ( 99  )  )  ) ( 20 ( 16 ( 33  )  ) ( 20 ( 33  )  ) ( 11 ( 33  )  )  ) ( 11 ( 16 ( 33  )  ) ( 20 ( 33  )  ) ( 11 ( 33  )  )  )  ) ( 89 ( 3  )  )  ) ");
//    	StateNode node3 = sMap.genStateTreeFromString("( -1 ( 34 ( 16 ( 16 ( 33  )  ) ( 20 ( 33  )  ) ( 99 ( 33  )  )  ) ( 20 ( 16 ( 33  )  ) ( 20 ( 33  )  ) ( 11 ( 33  )  )  ) ( 11 ( 16 ( 33  )  ) ( 20 ( 33  )  ) ( 11 ( 33  )  )  )  ) ( 89 ( 3  )  )  ) ");
//    	StateNode node4 = sMap.genStateTreeFromString("( -1 ( 34 ( 99 ( 16 ( 33  )  ) ( 20 ( 33  )  ) ( 11 ( 33  )  )  ) ( 20 ( 16 ( 33  )  ) ( 20 ( 33  )  ) ( 11 ( 33  )  )  ) ( 11 ( 16 ( 33  )  ) ( 20 ( 33  )  ) ( 11 ( 33  )  )  )  ) ( 89 ( 3  )  )  ) ");
//    	StateNode node5 = sMap.genStateTreeFromString("( -1 ( 99 ( 16 ( 16 ( 33  )  ) ( 20 ( 33  )  ) ( 11 ( 33  )  )  ) ( 20 ( 16 ( 33  )  ) ( 20 ( 33  )  ) ( 11 ( 33  )  )  ) ( 11 ( 16 ( 33  )  ) ( 20 ( 33  )  ) ( 11 ( 33  )  )  )  ) ( 89 ( 3  )  )  ) ");
//    	System.out.println(sMap.countStateDifferences(node1, node1));
//    	System.out.println(sMap.countStateDifferences(node1, node2));
//    	System.out.println(sMap.countStateDifferences(node1, node3));
//    	System.out.println(sMap.countStateDifferences(node1, node4));
//    	System.out.println(sMap.countStateDifferences(node1, node5));



        //Print out rules of a particular type
//        ListIterator<Gdl> iterator = rules.listIterator();
//        while(iterator.hasNext()) {
//        	Gdl currRule = iterator.next();
//        	System.out.print(currRule.getClass().getName() + " ");
//        	if(currRule instanceof GdlRule) {
//        		System.out.print(" RULE ");
//        	}
//        }



        //Timing Stuff
//        ArrayList<Long> genTimes = new ArrayList<Long>();
//        ArrayList<Long> loadTimes = new ArrayList<Long>();
//        int numTrials = 100;
//        for(int i=0;i<numTrials;i++) {
//	        long startTime = System.nanoTime();
//	        g.genRuleGraph();
//	        long endTime = System.nanoTime();
//	        genTimes.add(endTime - startTime);
//	        RuleGraphRecord timeRec1 = new RuleGraphRecord(g);
//	        RuleGraphRecord timeRec2 = new RuleGraphRecord();
//	        if(i==0) {
//	        	timeRec1.saveToFile("test.txt");
//	        }
//	        startTime = System.nanoTime();
//	        timeRec2.loadFromFile("test.txt");
//	        endTime = System.nanoTime();
//	        loadTimes.add(endTime - startTime);
//        }
//        System.out.println("Gen: " + genTimes);
//        System.out.println("Load: " + loadTimes);
//        System.out.println("Gen Mean: " + MyUtil.mean(genTimes)/1000000.0);
//        System.out.println("Gen STD: " + MyUtil.std(genTimes)/1000000);
//        System.out.println("Load Mean: " + MyUtil.mean(loadTimes)/1000000);
//        System.out.println("Load STD: " + MyUtil.std(loadTimes)/1000000);

    	//Determine our role in the game
    	roleIndex = -2;
    	this.allRoles = this.getStateMachine().getRoles();
    	for(int i=0;i<allRoles.size();i++) {
    		if(allRoles.get(i).equals(this.getRole())) {
    			roleIndex = i;
    		}
    	}
//    	System.out.println("Transfer: " + USE_TRANSFER + "  Role: " + this.getRole());

    	//initialize data structures to hold move archives (Note: these are for saving data from the current game, not influencing MCTS. Those archives are stored with sMap.)
    	this.specMoveData = new ArrayList<HashMap<List<Integer>, Pair<Double, Long>>>();
    	this.genMoveData = new ArrayList<HashMap<Integer, Pair<Double, Long>>>();
    	for(int i=0;i<this.allRoles.size();i++) {
    		this.specMoveData.add(new HashMap<List<Integer>, Pair<Double, Long>>());
    		this.genMoveData.add(new HashMap<Integer, Pair<Double, Long>>());
    	}

    	//turn game description into a rule graph
    	RuleGraph g = new RuleGraph(this.rules, allRoles);
    	g.genRuleGraph();

    	//save target rule graph to file
    	if(SAVE_RULE_GRAPH_TO_FILE) {
	    	RuleGraphRecord saveRec = new RuleGraphRecord(g); //Uncomment these 2 lines to save rule graph to file
	    	saveRec.saveToFile("last_rule_graph.txt", true);
    	}

    	long transferStartTime = 0;
    	if(USE_TRANSFER) {
    		transferStartTime = System.currentTimeMillis();
	    	RuleGraphRecord rec = new RuleGraphRecord();
	    	rec.loadFromFile(RULE_GRAPH_FILE, true);  //Load source rule graph from file

	//    	RuleGraphViewer viewer = new RuleGraphViewer(g);
	//    	viewer.drawRuleGraph();
	//    	viewer.drawTopLevel(5, "graph_images_test/");
	//    	RuleGraphViewer recordViewer = new RuleGraphViewer(rec);
	//    	recordViewer.drawTopLevel(2, "record_images/");

	    	//Do symbol mapping
	    	this.sMap = new StateMapping(g, rec);
	    	System.out.println(sMap.getEdit().mappedNamesToString());

	    	//Load archived MCT data from file
	    	this.sMap.loadSourceStatesFromFile(MCT_READ_DIR + "/" + "MCT_combined.txt");

	    	this.mappedRoleIndices = this.sMap.getMappedRoleIndices(allRoles);
//	    	System.out.println("l339 - role indices: " + this.mappedRoleIndices);

	    	//Make the root of our MCT
	    	root = new MCTNode(this.getCurrentState(), this.getStateMachine(), sMap, null);
	    	root.genStateSet();
	    	if(SAVE_MCT_TO_FILE) {
	    		existingNodes.put(root.getStateSet(), root);
	    	}

    	} else { //If we're not doing transfer, initialization can be greatly simplified
//    		this.sMap = new StateMapping(g, null, null);    //This version of the line doesn't generate the rule graph
    		this.sMap = new StateMapping(g);                //This version of the line DOES generate a rule graph
        	root = new MCTNode(this.getCurrentState(), this.getStateMachine(), sMap, null);
        	root.genStateSet();
        	if(SAVE_MCT_TO_FILE) {
        		existingNodes.put(root.getStateSet(), root);
        	}
    	}

    	//If we're saving the MCT data, keep a pointer to the original root to prevent garbage collection from deleting everything
    	if(SAVE_MCT_TO_FILE) {
    		origRoot = root;
    	}

    	startTime = System.currentTimeMillis();

    	//Start MCTS
    	buildTreeForTime(timeout);
    }


    //This method is called once per move. It does MCTS for as long as possible, then produces the best move to play
    @Override
    public Move stateMachineSelectMove(long timeout) throws TransitionDefinitionException, MoveDefinitionException, GoalDefinitionException
    {
    	//start by finding out what actually happened in the last move and shifting our MCT forward appropriately
    	List<GdlTerm> lastMoveTerms = this.getMatch().getMostRecentMoves();
    	if (lastMoveTerms != null) {
    		List<Move> lastMove = new ArrayList<Move>();
    		for(GdlTerm term : lastMoveTerms) {
    			lastMove.add(new Move(term));
    		}
    		root = root.getChildren().get(lastMove);
            root.setParents(null);
    	}

    	if(EXPERIMENT_SAVE_DIR != null && !EXPERIMENT_SAVE_DIR.equals("")) {
    		this.stateHistory.addLast(root.getStateSet());
    	}

    	//now continue building the MCT
        buildTreeForTime(timeout);

        //Once we've done as much search as we have time for, select the best move to play
        List<Move> selectedMove = selectBestMove();

        System.out.println(root.getNumVisits());
        System.out.println(root.getTotalReward());
        System.out.println(getCurrentState().getContents());

//        notifyObservers(new GamerSelectedMoveEvent(moves, selection, stop - start));
        this.numTurns++;
        return selectedMove.get(roleIndex);
    }


    //Do MCTS for as long as we can
    private void buildTreeForTime(long timeout) {
    	long startTime = System.currentTimeMillis();
    	long stopTime = timeout - TIME_THRESHOLD;
//    	long duration = stopTime - startTime;
    	long currentTime = startTime;

    	while(currentTime < stopTime) {
    		MCTNode currNode = root;
    		Set<Set<List<Integer>>> statesOnPath = new HashSet<Set<List<Integer>>>();
    		ArrayList<MCTNode> pathInOrder = new ArrayList<MCTNode>();
    		ArrayList<List<Move>> movesInOrder = new ArrayList<List<Move>>();
    		statesOnPath.add(currNode.getStateSet());
    		pathInOrder.add(currNode);

    		while(currNode.isExpanded() && !currNode.isTerminal()) {
    			int turnIndex = currNode.getWhoseTurn();
    			if(turnIndex == -1 || turnIndex == -2) { //If nobody has an option, or there are simultaneous turns, just assume our own perspective (NOTE: will need to be changed to better handle simultaneous turns)
    				turnIndex = this.roleIndex;
    			} //turnIndex cannot be -3 because state is not terminal
    			List<Move> selectedMove = selectChild(currNode, turnIndex);
    			currNode = currNode.getChildren().get(selectedMove); //, (currentTime - startTime)/(double)duration);
//    			movesInOrder.add(selectedMove);
    			statesOnPath.add(currNode.getStateSet());
        		pathInOrder.add(currNode);
    		}
    		currNode.expandChildren();
    		if(!currNode.isTerminal()) {
    			currNode = rollout(currNode, statesOnPath, pathInOrder);
    		}

    		if(currNode.isTerminal() ) {

    			List<Integer> goals = null;
				goals = currNode.getGoals();
				List<Double> goalDoubles = new ArrayList<Double>();
				for(Integer i : goals) { //convert goal values to double type
					goalDoubles.add(i.doubleValue());
				}
    			backprop(goalDoubles, pathInOrder);
    		}
    		currentTime = System.currentTimeMillis();
    	}
    }


    //assigns a score to the given MCTNode
    //nodes with a higher score will prioritized for saving to file
    //currently, this method is only called when saving the nodes from a single game instance. It doesn't really affect anything because we save all of the nodes with at least 2 visits.
    private float MCTNodePriorityScore(MCTNode node, int maxVisits) {
    	float result = 0;

    	float visit_priority = 1.0f;

    	result += visit_priority*(node.getNumVisits()/((double)maxVisits));

    	return result;
    }


    //This function queues up all of the MCT nodes with at least 2 visits for saving.
    //It also calculates the general and specific move data described in the "Archiving Information" subsection
    //give -1 to numNodes to queue the whole MCT (except nodes with only 1 visit)
    private LinkedList<MCTNode> queueNodes(int numNodes) {
    	LinkedList<MCTNode> result = new LinkedList<MCTNode>();
    	TreeSet<MCTMerger.PriorityItem<MCTNode>> sorted = new TreeSet<MCTMerger.PriorityItem<MCTNode>>();
    	LinkedList<MCTNode> q = new LinkedList<MCTNode>();
    	HashSet<Set<List<Integer>>> usedStates = new HashSet<Set<List<Integer>>>();
    	q.add(origRoot);
    	int maxVisits = origRoot.getNumVisits();
    	TreeMap<Integer, Integer> visitMap = new TreeMap<Integer,Integer>();

    	while(!q.isEmpty()) {
    		MCTNode currNode = q.pop();
    		if(!usedStates.contains(currNode.getStateSet())) {
    			List<Double> bestMoveScore = new ArrayList<Double>();
    			List<Double> worstMoveScore = new ArrayList<Double>();
    			List<HashSet<Integer>> genMovesSeen = new ArrayList<HashSet<Integer>>();
    			List<HashSet<List<Integer>>> specMovesSeen = new ArrayList<HashSet<List<Integer>>>();
    			for(int i=0;i<this.allRoles.size();i++) {
    				bestMoveScore.add(0.0);
    				worstMoveScore.add(1.0);
    				genMovesSeen.add(new HashSet<Integer>());
    				specMovesSeen.add(new HashSet<List<Integer>>());
    			}

    			for(List<Move> moveSet : currNode.getChildren().keySet()) { //find the best score for any move from this node to normalize the rest
    				MCTNode child = currNode.getChildren().get(moveSet);
    				if(child != null && child.getNumVisits() > 0) {
    					List<List<Integer>> convertedMove = this.sMap.convertMoveToList(moveSet);
    					for(int i=0;i<this.allRoles.size();i++) {
    						double moveScore = child.getTotalReward().get(i) / child.getNumVisits();
    						genMovesSeen.get(i).add(convertedMove.get(i).get(0));
    						specMovesSeen.get(i).add(convertedMove.get(i));
    						if(moveScore > bestMoveScore.get(i)) {
    							bestMoveScore.set(i, moveScore);
    						}
    						if(moveScore < worstMoveScore.get(i)) {
    							worstMoveScore.set(i, moveScore);
    						}
    					}
    				}
    			}

    			for(List<Move> moveSet : currNode.getChildren().keySet()) { //move data is calculated here
    				MCTNode child = currNode.getChildren().get(moveSet);
    				if(child != null && child.getNumVisits() > 0) {
    					List<List<Integer>> convertedMove = this.sMap.convertMoveToList(moveSet);
    					for(int i=0;i<this.allRoles.size();i++) {
    						if(bestMoveScore.get(i) > worstMoveScore.get(i)) {
	    						double moveScore = child.getTotalReward().get(i) / child.getNumVisits();
	        					double normalizedScore = 1.0;
	        					if(bestMoveScore.get(i) > this.FLOAT_THRESH) {
	        						normalizedScore = moveScore / bestMoveScore.get(i);
	        					} else {
	        						if(moveScore > this.FLOAT_THRESH) {
	        							System.out.println("What? How did this happen?");
	        						}
	        					}
	        					if(specMovesSeen.get(i).size() > 1) {
		    						if(!this.specMoveData.get(i).containsKey(convertedMove.get(i))) {
		    							this.specMoveData.get(i).put(convertedMove.get(i), new Pair<Double,Long>(0.0, 0l));
		    						}
		    						Pair<Double, Long> currSpecific = this.specMoveData.get(i).get(convertedMove.get(i));
			                		Pair<Double, Long> newSpecific = new Pair<Double, Long>(currSpecific.getKey() + normalizedScore, currSpecific.getValue() + 1);
			                		this.specMoveData.get(i).put(convertedMove.get(i), newSpecific);
	        					}
		    					if(genMovesSeen.get(i).size() > 1) {
		    						if(!this.genMoveData.get(i).containsKey(convertedMove.get(i).get(0))) {
		    							this.genMoveData.get(i).put(convertedMove.get(i).get(0), new Pair<Double,Long>(0.0, 0l));
		    						}

			                		Pair<Double, Long> currGeneral = this.genMoveData.get(i).get(convertedMove.get(i).get(0));
			                		Pair<Double, Long> newGeneral = new Pair<Double, Long>(currGeneral.getKey() + normalizedScore, currGeneral.getValue() + 1);
			                		this.genMoveData.get(i).put(convertedMove.get(i).get(0), newGeneral);
		    					}
    						}
    					}
    				}
    			}

    			if(!visitMap.containsKey(currNode.getNumVisits())) {
    				visitMap.put(currNode.getNumVisits(), 0);
    			}
    			visitMap.put(currNode.getNumVisits(), visitMap.get(currNode.getNumVisits())+1);

    			if(currNode.getNumVisits() > 1) { //don't bother saving nodes that were only hit once by a rollout
		    		sorted.add(new MCTMerger.PriorityItem<MCTNode>(MCTNodePriorityScore(currNode, maxVisits), currNode));
		    		if(numNodes >= 0 && sorted.size() > numNodes) {
		    			sorted.pollLast();  //bump the lowest priority node
		    		}
    			}

    			usedStates.add(currNode.getStateSet());
	    		for(MCTNode child : currNode.getChildren().values()) {
	    			if(child != null) {
	    				q.addLast(child);
	    			}
	    		}
    		}
    	}

    	for(int visits : visitMap.keySet()) {
    		System.out.println(visits + " visits - " + visitMap.get(visits) + " nodes");
    	}

    	for(MCTMerger.PriorityItem<MCTNode> item : sorted) {
    		result.add(item.item);
    	}

    	System.out.println(usedStates.size() + " total nodes");
    	System.out.println("Queued " + result.size() + " nodes.");

    	return result;
    }


    //deprecated method
    public int getAndAdvanceTupleIndex() {
    	int currIndex = this.nextTupleIndex;
    	this.nextTupleIndex++;
    	return currIndex;
    }

    //deprecated method
    public void registerStateTuples(StateNode state) {
		for(StateNode child : state.getChildren().values()) {
			String tuple = child.toString();
			if (!this.indicesByTuple.containsKey(tuple)) {
				int nextIndex = getAndAdvanceTupleIndex();
				this.indicesByTuple.put(tuple, nextIndex);
				this.tuplesByIndex.put(nextIndex, tuple);
			}
		}
    }


    //convert a Move into a String of the form "( X Y1 Y2... )" for functions or "X" for constants where Xs and Ys correspond to the ID of the top level node for that name
    //used when writing moves to the MCT file - IDs should match with those in the rule graph file
    public String moveToIDString(Move move) {
    	HashMap<String, Integer> nameToID = this.sMap.getTarget().getTopLevelNames();
    	GdlTerm term = move.getContents();
    	String result = "";

        if(term instanceof GdlFunction) {
    		GdlFunction fun = (GdlFunction) term;
    		if(nameToID.containsKey(fun.getName().getValue())) {
    			int funID = nameToID.get(fun.getName().getValue());
    			result += "( " + funID + " ";
    			for(GdlTerm arg : fun.getBody()) {
    				if(arg instanceof GdlConstant) {
    					GdlConstant con = (GdlConstant) arg;
    					int conID = nameToID.get(con.getValue());
    					result += conID + " ";
    				} else if(arg instanceof GdlFunction) {
    					System.out.println("ERROR: nested functions in moveToIDString.");
    				} else {
    					System.out.println("ERROR: variable or something weird in moveToIDString.");
    				}
    			}
    			result += ")";
    		} else {
    			System.out.println("ERROR: function name not found in moveToIDString.");
    		}
    	} else if (term instanceof GdlConstant) {
    		GdlConstant con = (GdlConstant) term;
    		if(nameToID.containsKey(con.getValue())) {
    			int conID = nameToID.get(con.getValue());
    			result += conID;
    		} else {
    			System.out.println("ERROR: constant name not found in moveToIDString.");
    		}
    	} else {
    		System.out.println("ERROR: non function statement in moveToIDString - " + term);
    	}

        return result;
    }


    //get the file name of the next MCT to be saved based on the names of files already in the directory
    public String getNextMCTSaveName() {
    	String result = "";
    	File folder = new File(MCT_SAVE_DIR);
    	File[] listOfFiles = folder.listFiles();
    	List<String> fileNames = new LinkedList<String>();
    	int biggestIndex = 0;

    	for (File file : listOfFiles) {
    	    if (file.isFile()) {
    	        fileNames.add(file.getName());
    	    }
    	}

    	for(String name : fileNames) {
    		if(name.length() >= 5 && Character.isDigit(name.charAt(4))) {
	    		try {
	    			String numStr = name.substring(4, 8);
	    			int currIndex = Integer.parseInt(numStr);
	    			if(currIndex > biggestIndex) {
	    				biggestIndex = currIndex;
	    			}
	    		} catch (Exception e) {
	                System.out.println(e.getStackTrace());
	            }
    		}
    	}

    	int newIndex = biggestIndex + 1;
    	result = "MCT_";
    	if(newIndex < 10) {
    		result += "000";
    	} else if(newIndex < 100) {
    		result += "00";
    	} else if(newIndex < 1000) {
    		result += "0";
    	}
    	result += newIndex + ".txt";

    	return result;
    }


    //give -1 to numNodes to save the whole MCT
    //returns the number of nodes saved to file
    //This method saves an MCT to file for one instance of a game. The archives built in the "Archiving Information" subsection will be built from these files.
    public int saveMctToFile(String outFileName, int numNodes) {
		if(origRoot == null) {
			System.out.println("ERROR in saveMctToFile: MCT has not been initialized.");
		}

		LinkedList<MCTNode> q = queueNodes(numNodes);
		int count = 0;
		int numRoles = this.getStateMachine().getRoles().size();
		String headerStr = "";
		String outStr = "";
		String stateStr = "";
		String[] moveIDStr = new String[numRoles];
		HashMap<List<Integer>, Integer> compIDLookUp = new HashMap<List<Integer>, Integer>();
		int nextCompID = 0;
		ArrayList<List<Integer>> compsInOrder = new ArrayList<List<Integer>>();

		//Assign IDs to each move seen with a look-up table at the top to save file size
		int[] nextMoveID = new int[numRoles];
		List<HashMap<Move, Integer>> moveToID = new ArrayList<HashMap<Move,Integer>>();
		for(int i=0;i<numRoles;i++) {
			nextMoveID[i] = 0;
			moveToID.add(new HashMap<Move,Integer>());
			moveIDStr[i] = "";
		}

		if(!q.isEmpty()) {
			headerStr += numRoles + "\n"; //At the top, print the number of players on a line by itself
		}

		while(!q.isEmpty()) {
			MCTNode currMCTNode = q.pop();
			outStr += count + " "; //assigns an ascending ID value to each node
			for(int i=0;i<numRoles;i++) {
				outStr += currMCTNode.getTotalReward().get(i) + " "; //Print the reward for each player
			}
			outStr += currMCTNode.getNumVisits() + " "; //Print visits to node
			outStr += currMCTNode.getTotalParentVisits() + " "; //Print total visits to all of node's parents
			outStr += currMCTNode.getNumSiblings() + " "; //Print number of siblings
			outStr += currMCTNode.getNumVisitsOld() + " "; //Print the number of visits at the time the parent was disconnected, if that happened (i.e. if this state was actually played)

			Set<List<Integer>> currState = currMCTNode.getStateSet();
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
//			outStr += currMCTNode.getStateTree().toString() + "  "; //Print out state tree

			outStr += "* "; //mark the end of state and beginning of list of moves linking to child states

			//Store UCT relevant child info pointed to by each possible move combination
			HashMap<List<Move>,MCTNode> currChildren = currMCTNode.getChildren();
			for(List<Move> move : currChildren.keySet()) {
				MCTNode currChild = currChildren.get(move);
				if(currChild != null) {
					for(int i=0;i<move.size();i++) {
						int currMoveID;
						HashMap<Move, Integer> roleMoveToID = moveToID.get(i);
						Move roleMove = move.get(i);
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
						outStr += currChild.getTotalReward().get(i) + " ";
					}
					outStr += currChild.getNumVisits() + "  "; //Double spaces will indicate a new move being recorded
				} else {
//					for(int i=0;i<numRoles;i++) {
//						outStr += "0 ";
//					}
//					outStr += "0  ";
				}
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
		for(int i=0;i<this.allRoles.size();i++) {
			boolean first = true;
			for(int genID : this.genMoveData.get(i).keySet()) {
				if(!first) {
					genMoveStr += "* ";
				}
				first = false;
				Pair<Double,Long> genData = this.genMoveData.get(i).get(genID);
				genMoveStr += genData.getKey() + " " + genData.getValue() + " " + genID + " ";
			}
			genMoveStr += "\n";

			first = true;
			for(List<Integer> specID : this.specMoveData.get(i).keySet()) {
				if(!first) {
					specMoveStr += "* ";
				}
				first = false;
				Pair<Double,Long> specData = this.specMoveData.get(i).get(specID);
				specMoveStr += specData.getKey() + " " + specData.getValue() + " ";
				for(int id : specID) {
					specMoveStr += id + " ";
				}
			}
			specMoveStr += "\n";
		}


		//Write data to file
		File file = new File(outFileName);
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

        System.out.println(this.sMap.getTarget().getTopLevelNames());
        return count;
	}


    //pick the immediate best move for us
    //This method implements transfer for the Action Taken (A) described in the "Knowledge Transfer" subsection
    private List<Move> selectBestMove() {
    	List<Move> bestMove = null;
    	double bestScore = -1000;
		ReducedMCTNode sourceNodeFrom = null;

		if(USE_TRANSFER && USE_PLAY_TRANSFER) {
			sourceNodeFrom = root.getNearestSourceNode(this.sMap);
		}

		int maxVisits = 0;
		if(PLAY_SELECT_MODE.equals("visits")) {
			for(List<Move> move : root.getChildren().keySet()) {
				MCTNode currNode = root.getExpandedChild(move, this.existingNodes, SAVE_MCT_TO_FILE);
				if(currNode.getNumVisits() > maxVisits) {
					maxVisits = currNode.getNumVisits();
				}
			}
		}

    	for(List<Move> move : root.getChildren().keySet()) { //consider the value of each possible child state
    		MCTNode currNode = root.getExpandedChild(move, this.existingNodes, SAVE_MCT_TO_FILE);
    		double currScore = 0;

    		if(PLAY_SELECT_MODE.equals("reward")) {
	    		if (currNode.getNumVisits() > 0) {
	    			currScore = currNode.getTotalReward().get(this.roleIndex) / currNode.getNumVisits() / MAX_REWARD_VALUE;
	    			if(currNode.isTerminal() && Math.abs(currNode.getTotalReward().get(this.roleIndex) - MAX_REWARD_VALUE) < FLOAT_THRESH) {
	    				currScore += 1000000;  //if we see an immediate win, just take it
	    			}
	    		}
    		} else if(PLAY_SELECT_MODE.equals("visits")){
    			if(maxVisits > 0) {
    				currScore = currNode.getNumVisits() / maxVisits;
    			}
    		} else {
    			System.out.println("ERROR: Invalid mode for selecting best move.");
    		}

    		if(USE_TRANSFER && USE_PLAY_TRANSFER) { // This is where the transfer happens
    			ReducedMCTNode sourceNodeTo = currNode.getNearestSourceNode(this.sMap);
    			double currMoveHeuristic = transferHeuristic(sourceNodeFrom, sourceNodeTo, move, currNode.getPercentSharedStates(), this.roleIndex);
//    			System.out.println("! " + currScore + " " + currMoveHeuristic + " " + move);

	    		currScore = currMoveHeuristic*PLAY_TRANSFER_RATIO + currScore*(1-PLAY_TRANSFER_RATIO);
    		}

    		System.out.println("! " + currNode.getTotalReward().get(this.roleIndex) / currNode.getNumVisits() + " " + currNode.getTotalReward().get(this.roleIndex) + " " + currNode.getNumVisits() + " " + move);
//    		System.out.println(ucb1Basic(currNode, this.roleIndex));
//    		System.out.println("# " + currNode.getNumSiblings());

    		if(bestMove == null || currScore > bestScore+FLOAT_THRESH) {
    			bestMove = move;
    			bestScore = currScore;
    		}
    	}

    	System.out.println("Best Score: " + bestScore + " " + bestMove);
    	return bestMove;
    }


    //select a child of the currNode to explore during the selection phase of MCTS
    //This method implements Selection (S) transfer, described in the "Knowledge Transfer" subsection
    //turnIndex gives the index of the role whose turn it is (negatives denote special cases)
    //timeFraction gives the % of time allotted for MCT expansion that has already passed
    private List<Move> selectChild(MCTNode currNode, int turnIndex) {
    	MCTNode selected = null;
    	List<Move> selectedCombo = null;
    	double bestScore = -1000;
    	ArrayList<List<Move>> bestCombos = new ArrayList<List<Move>>();
    	ReducedMCTNode sourceNodeFrom = null;

    	if(USE_TRANSFER && USE_SELECTION_TRANSFER) {
    		sourceNodeFrom = currNode.getNearestSourceNode(this.sMap);
    	}

    	for(List<Move> moveCombo : currNode.getChildren().keySet()) { //consider each possible child node
    		MCTNode child = currNode.getChildren().get(moveCombo);
    		ReducedMCTNode sourceNodeTo = null;
    		double currScore;
    		if(USE_TRANSFER && USE_SELECTION_TRANSFER && child != null) { //if selection transfer is enabled, use a modified UCB1
    			sourceNodeTo = child.getNearestSourceNode(this.sMap);
    			currScore = ucb1WithTransfer(child, sourceNodeFrom, sourceNodeTo, moveCombo, turnIndex);
    		} else { //if selection transfer is disabled, just use regular UCB1
    			currScore = ucb1Basic(child, turnIndex);
    		}
    		if (currScore > bestScore) {
    			bestCombos = new ArrayList<List<Move>>();
    			bestCombos.add(moveCombo);
    			bestScore = currScore;
    		} else if (currScore == bestScore) {
    			bestCombos.add(moveCombo);
    		}
    	}
    	selectedCombo = bestCombos.get(rand.nextInt(bestCombos.size()));
    	selected = currNode.getExpandedChild(selectedCombo, this.existingNodes, SAVE_MCT_TO_FILE);
//    	System.out.println("Selected UCB1: " + bestScore + " Reward: " + selected.getTotalReward().get(turnIndex) + " Visits: " + selected.getNumVisits() + " Transfer: " + selected.getTransferTerm());
    	return selectedCombo;
    }


    //vanilla UCB1, where parameters are read out of the given MCTNode
    public static double ucb1Basic(MCTNode currNode, int turnIndex) {
    	double result;
    	if(currNode == null) {
    		result = NEW_EXPLORE_VALUE;
    	} else {
    		double r = currNode.getTotalReward().get(turnIndex);
        	double n = currNode.getNumVisits();
        	double bigN = currNode.getTotalParentVisits();
        	double c = EXPLORE_PARAM;
        	result = ucb1Basic(r, n, bigN, c);
    	}
    	return result;
    }


    //vanilla UCB1, where all parameters must be provided
    public static double ucb1Basic(double r, double n, double bigN, double c) {
    	double result;
    	if(n < FLOAT_THRESH) {
    		result = NEW_EXPLORE_VALUE;
    	} else {
    		result = (r / MAX_REWARD_VALUE)/n + c*Math.sqrt(Math.log(bigN)/n);
//    		System.out.println("***" + (r / MAX_REWARD_VALUE)/n + " " + c*Math.sqrt(Math.log(bigN)/n));
    	}
//    	System.out.println(r + " " + n + " " + bigN + " " + c + " " + result);
		return result;
    }


    //This method produces a UCB1 value guided by selection transfer, as described in Equation 2 of the "Knowledge Transfer" subsection
    private double ucb1WithTransfer (MCTNode currNode, ReducedMCTNode sourceNodeFrom, ReducedMCTNode sourceNodeTo, List<Move> targetMoveSet, int turnIndex) {
    	double regularValue, regularExplore;
    	if(currNode == null || currNode.getNumVisits() == 0) {
    		regularValue = 0;
    		regularExplore = NEW_EXPLORE_VALUE;
    	} else {
    		regularValue = (currNode.getTotalReward().get(turnIndex) / MAX_REWARD_VALUE) / currNode.getNumVisits();
    		regularExplore = EXPLORE_PARAM*Math.sqrt(Math.log(currNode.getTotalParentVisits())/currNode.getNumVisits());
    	}
    	double transferValue = transferHeuristic(sourceNodeFrom, sourceNodeTo, targetMoveSet, currNode.getPercentSharedStates(), turnIndex);
    	double combinedValue = SELECTION_TRANSFER_RATIO*transferValue + (1-SELECTION_TRANSFER_RATIO)*regularValue;
//    	System.out.println("### " + targetMoveSet + " " + regularValue + " " + transferValue + " " + regularExplore + " " + combinedValue);
    	return combinedValue + regularExplore;
    }


    //Pick a move at random from those available
    private List<Move> randomMove(MCTNode node) {
    	List<Move> result = null;
    	int numMoves = node.getChildren().size();
    	int selectedIndex = rand.nextInt(numMoves);
    	int counter = 0;
    	Iterator<List<Move>> iter = node.getChildren().keySet().iterator();
    	while(iter.hasNext() && counter <= selectedIndex) {
    		List<Move> tempMove = iter.next();
    		if(counter == selectedIndex) {
    			result = tempMove;
    		}
    		counter++;
    	}
    	return result;
    }


    //This function produces the transfer values shown in Figure 3 of the "Knowledge Transfer" subsection
    //produces a value in [0,1] based on how good this move looks in the source game
    //sourceNodeTo is the node in the source game that most closely matches the state that will be reached in the target game if the move is taken
    //if sourceNodeTo is provided, this heuristic will consider its total reward and number of visits
    //if sourceNodeTo is null, this contribution will be replaced by a best approximation using a matching move from sourceNodeFrom, if one exists
    private double transferHeuristic(ReducedMCTNode sourceNodeFrom, ReducedMCTNode sourceNodeTo, List<Move> targetMoveSet, double fromSimilarity, int roleIndex) {
    	double result = 0.0;
    	double normalize = 0.0;
    	HashMap<List<Integer>, Pair<Double, Long>> specific = this.sMap.getSourceStates().getSpecificMoveTotalData(roleIndex);
    	HashMap<Integer, Pair<Double, Long>> general = this.sMap.getSourceStates().getGeneralMoveTotalData(roleIndex);
    	List<List<Integer>> convertedMove = this.sMap.convertMoveToSource(targetMoveSet);

//    	System.out.println("**** " + convertedMove.get(roleIndex));

    	if(specific.containsKey(convertedMove.get(roleIndex))) { //generate value for specific move
			Pair<Double, Long> specificData = specific.get(convertedMove.get(roleIndex));
			double value = (specificData.getKey() / specificData.getValue());
			double certainty = logistic(specificData.getValue());
			result += value*certainty; // / bestSpecific;
			normalize += certainty;
//			System.out.println("*** Using specific move " + targetMoveSet + " value: " + value + " certainty: " + certainty + " <- " + specificData.getKey() + " " + specificData.getValue());
		}

    	if(general.containsKey(convertedMove.get(roleIndex).get(0))) { //generate value for general move
			Pair<Double, Long> generalData = general.get(convertedMove.get(roleIndex).get(0));
			double value = (generalData.getKey() / generalData.getValue());
			double certainty = logistic(generalData.getValue());
			result += value*certainty; // / bestGeneral;
			normalize += certainty;
//			System.out.println("*** Using general move " + targetMoveSet + " value: " + value + " certainty: " + certainty + " <- " + generalData.getKey() + " " + generalData.getValue());
		}

    	if(sourceNodeTo != null && sourceNodeTo.getNumVisits() > 0) { //generate value for state
    		double value = sourceNodeTo.getTotalReward().get(roleIndex) / MAX_REWARD_VALUE / sourceNodeTo.getNumVisits();
    		double certainty = logistic(sourceNodeTo.getNumVisits()) * stateLogistic(fromSimilarity);
    		result += value*certainty;
    		normalize += certainty;
//    		System.out.println("*** Using node similar to child " + targetMoveSet + " value: " + value + " certainty: " + certainty + " <- " + sourceNodeTo.getTotalReward().get(roleIndex) / MAX_REWARD_VALUE + " " + sourceNodeTo.getNumVisits() + " " + fromSimilarity);
    	} else { //generate value for state for rollouts
	    	if(sourceNodeFrom.getChildData().containsKey(convertedMove)) { //nearest state has data on this specific move
	    		Pair<List<Double>, Integer> childData = sourceNodeFrom.getChildData().get(convertedMove);
	    		double value = (childData.getKey().get(roleIndex) / MAX_REWARD_VALUE) / childData.getValue();
	    		double certainty = logistic(childData.getValue()) * stateLogistic(fromSimilarity);
				result += value*certainty;
				normalize += certainty;
//				System.out.println("*** Using exact move in position " + targetMoveSet + " value: " + value + " certainty: " + certainty + " <- " + childData.getKey().get(roleIndex) / MAX_REWARD_VALUE + " " + childData.getValue() + " " + fromSimilarity);
			}
    	}

		if(normalize > 0) {
			result = result / normalize;
		} else {
			result = 0.5;
		}

    	return result;
    }


    //Perform a rollout. If Rollout Transfer (R) is enabled, then influence rollouts as described in the "Knowledge Transfer" subsection
    private MCTNode rollout (MCTNode startNode, Set<Set<List<Integer>>> statesOnPath, ArrayList<MCTNode> pathInOrder) {
    	MCTNode currNode = startNode;
    	int depth = 0;
    	this.numRollouts ++;
//    	if(this.numRollouts % 10 == 0) {
//    		System.out.println(this.numRollouts + " rollouts");
//    	}
    	while(!currNode.isTerminal() && depth < ROLLOUT_MAX_DEPTH) {
    		currNode.expandChildren();
    		List<Move> selectedMove;
    		if(USE_TRANSFER && USE_ROLLOUT_TRANSFER) {
    			ReducedMCTNode nearestNode = currNode.getNearestSourceNode(this.sMap);
    			selectedMove = null;
    			List<List<Integer>> nearestMove = null;
    			double bestScore = 0.0;
    			List<List<Integer>> bestNearestMove = null;

    			for(List<Move> currMove : currNode.getChildren().keySet()) { //find a transfer value for each possible move
    				int turnIndex = currNode.getWhoseTurn();
    				if(turnIndex < 0) {
    					turnIndex = 0;
    				}
    				double currTransfer = transferHeuristic(nearestNode, null, currMove, currNode.getPercentSharedStates(), turnIndex);
    				if(currTransfer > bestScore) {
    					bestScore = currTransfer;
    					selectedMove = currMove;
    				}
    			}

    			if(selectedMove == null) {
    				selectedMove = randomMove(currNode);
    			}
    		} else {
    			selectedMove = randomMove(currNode);
    		}
    		currNode = currNode.getExpandedChild(selectedMove, this.existingNodes, SAVE_MCT_TO_FILE);
    		statesOnPath.add(currNode.getStateSet());
    		pathInOrder.add(currNode);
    		depth++;
    	}
    	if(depth == ROLLOUT_MAX_DEPTH) {
    		System.out.println("ERROR in rollout: max depth exceeded.");
    	}

    	if(this.numRollouts % 10 == 0) {
    		System.out.println(USE_PLAY_TRANSFER + " " + USE_SELECTION_TRANSFER + " " + USE_ROLLOUT_TRANSFER + " " + MCT_READ_DIR + " " + this.getRole() + " " + this.numRollouts + " rollouts. " + (System.currentTimeMillis() - this.startTime) + " ms.");
    	}

    	return currNode;
    }


    // Do MCTS backpropagation
    private void backprop (List<Double> reward, ArrayList<MCTNode> pathInOrder) {
    	for(int i=0;i<pathInOrder.size();i++) {
    		int index = pathInOrder.size() - 1 - i;
    		MCTNode currNode = pathInOrder.get(index);
    		for(int j=0;j<reward.size();j++) {
    			currNode.setTotalReward(j, currNode.getTotalReward().get(j) + Math.pow(DISCOUNT_FACTOR, i)*reward.get(j));
    		}
    		currNode.setNumVisits(currNode.getNumVisits() + 1);
    	}
    }


    //Produce a String that represents a state for writing to file
    public static String stateToPrintString(Set<List<Integer>> state) {
    	String result = "";
    	for(List<Integer> stateComp : state) {
    		if(!result.equals("")) {
    			result += "* ";
    		}
    		for(int id : stateComp) {
    			result += id + " ";
    		}
    	}
    	return result;
    }


    //Save experiment data to file
    //For each game played, saves one file that specifies every state that was played, and adds a line to summary.txt
    //summary.txt contains one line for each game. The first number of each line is the amount of reward received by the agent that did the saving. The second number is the number of turns played. The remaining numbers indicate the final game state.
    public void saveExperimentToFile() {

    	String historyFileName = "";
    	File folder = new File(EXPERIMENT_SAVE_DIR);
    	File[] listOfFiles = folder.listFiles();
    	List<String> fileNames = new LinkedList<String>();
    	int biggestIndex = 0;

    	//figure out last state and reward values
    	List<GdlTerm> lastMoveTerms = this.getMatch().getMostRecentMoves();
    	if (lastMoveTerms != null) {
    		List<Move> lastMove = new ArrayList<Move>();
    		for(GdlTerm term : lastMoveTerms) {
    			lastMove.add(new Move(term));
    		}
    		root = root.getChildren().get(lastMove);
    	}

    	List<Integer> goals = null;
		goals = root.getGoals();
		List<Double> goalDoubles = new ArrayList<Double>();
		for(Integer i : goals) { //convert goal values to double type
			goalDoubles.add(i.doubleValue());
		}
		double reward = goalDoubles.get(this.roleIndex);
		Set<List<Integer>> finalState = root.getStateSet();
		System.out.println("Finished experiment with reward: " + reward);
		System.out.println("final state: " + finalState + "\n");
		String summaryLine = reward + " " + this.numTurns + " " + stateToPrintString(finalState) + "\n";


    	//determine file name for new history file
    	for (File file : listOfFiles) {
    	    if (file.isFile()) {
    	        fileNames.add(file.getName());
    	    }
    	}
    	for(String name : fileNames) {
    		if(name.length() >= 1 && Character.isDigit(name.charAt(0))) {
	    		try {
	    			String numStr = name.substring(0, 4);
	    			int currIndex = Integer.parseInt(numStr);
	    			if(currIndex > biggestIndex) {
	    				biggestIndex = currIndex;
	    			}
	    		} catch (Exception e) {
	                System.out.println(e.getStackTrace());
	            }
    		}
    	}

    	int newIndex = biggestIndex + 1;
    	if(newIndex < 10) {
    		historyFileName += "000";
    	} else if(newIndex < 100) {
    		historyFileName += "00";
    	} else if(newIndex < 1000) {
    		historyFileName += "0";
    	}
    	historyFileName += newIndex + ".txt";

    	//write history file
    	String outStr = "";
    	File file = new File(EXPERIMENT_SAVE_DIR + "/" + historyFileName);
        FileWriter fr = null;
        BufferedWriter br = null;
        for(Set<List<Integer>> state : this.stateHistory) {
        	outStr += stateToPrintString(state) + "\n";
        }
        try{
            fr = new FileWriter(file);
            br = new BufferedWriter(fr, RuleGraphRecord.BUFFER_SIZE);
            br.write(summaryLine);
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


        //append to summary file
        try {
            FileWriter fw = new FileWriter(EXPERIMENT_SAVE_DIR + "/" + EXP_SUMMARY_FILE,true); //the true will append the new data
            fw.write(summaryLine);
            fw.close();
        }
        catch(IOException e) {
            System.out.println("IOException: " + e.getMessage());
        }
    }


    //method that checks a state mapping, used for debugging purposes
    private void verifyStateMapping(StateMapping sMap) {
    	ArrayList<RuleNode> sourceGraph = sMap.getSource().getGraph();
    	ArrayList<RuleNode> targetGraph = sMap.getTarget().getGraph();
    	int sourceParentEdges = 0;
    	int sourceChildEdges = 0;
    	int targetParentEdges = 0;
    	int targetChildEdges = 0;
    	int edgeMatches = 0;
    	int colourMatches = 0;
    	ArrayList<Pair<Integer,Integer>> sourceParentEdgePairs = new ArrayList<Pair<Integer,Integer>>();
    	ArrayList<Pair<Integer,Integer>> sourceChildEdgePairs = new ArrayList<Pair<Integer,Integer>>();
    	ArrayList<Pair<Integer,RuleNodeColour>> sourceColours = new ArrayList<Pair<Integer,RuleNodeColour>>();
    	for(RuleNode node : sourceGraph) {
    		sourceParentEdges += node.getParents().size();
    		sourceChildEdges += node.getChildren().size();
    		for(RuleNode parent : node.getParents()) {
    			sourceParentEdgePairs.add(new Pair<Integer,Integer>(node.getId(),parent.getId()));
    		}
    		for(RuleNode child : node.getChildren()) {
    			sourceChildEdgePairs.add(new Pair<Integer,Integer>(node.getId(),child.getId()));
    		}
    		sourceColours.add(new Pair<Integer,RuleNodeColour>(node.getId(),node.getColour()));
    	}
    	for(RuleNode node : targetGraph) {
    		targetParentEdges += node.getParents().size();
    		targetChildEdges += node.getChildren().size();
    		for(RuleNode parent : node.getParents()) {
    			Pair<Integer,Integer> currPair = new Pair<Integer,Integer>(node.getId(),parent.getId());
    			if(sourceParentEdgePairs.contains(currPair)) {
    				edgeMatches++;
    			} else {
    				System.out.println("Missing parent " + currPair.getKey() + " -> " + currPair.getValue());
    			}
    		}
    		for(RuleNode child : node.getChildren()) {
    			Pair<Integer,Integer> currPair = new Pair<Integer,Integer>(node.getId(),child.getId());
    			if(sourceChildEdgePairs.contains(currPair)) {
    				edgeMatches++;
    			} else {
    				System.out.println("Missing child " + currPair.getKey() + " -> " + currPair.getValue());
    			}
    		}
    		Pair<Integer,RuleNodeColour> colourPair = new Pair<Integer,RuleNodeColour>(node.getId(),node.getColour());
			if(sourceColours.contains(colourPair)) {
				colourMatches++;
			} else {
				System.out.println("Missing colour " + node.getId() + " : " + node.getColour());
			}
    	}
    	System.out.println("Source size: " + sMap.getSource().getGraph().size() + "; " + sourceParentEdges + " parent edges; " + sourceChildEdges + " child edges");
    	System.out.println("Target size: " + sMap.getTarget().getGraph().size() + "; " + targetParentEdges + " parent edges; " + targetChildEdges + " child edges");
    	System.out.println("Edge Matches: " + edgeMatches);
    	System.out.println("Colour Matches: " + colourMatches);
    }


    public double logistic(double x) {
    	return MyUtil.logistic(x, CERTAINTY_OFFSET, CERTAINTY_STEEPNESS);
    }

    public double stateLogistic(double x) {
    	return MyUtil.logistic(x, STATE_CERTAINTY_OFFSET, STATE_CERTAINTY_STEEPNESS);
    }


    @Override
    public String getName() {
    	return getClass().getSimpleName();
    }

    // This is the default State Machine
    @Override
    public StateMachine getInitialStateMachine() {
        return new CachedStateMachine(new ProverStateMachine());
    }

    // This is the default Sample Panel
    @Override
    public DetailPanel getDetailPanel() {
        return new SimpleDetailPanel();
    }



    //This method is called at the end of a game. Saves data to file and cleans up data structures.
    @Override
    public void stateMachineStop() {
    	if(SAVE_MCT_TO_FILE) {
    		System.out.println("Saving MCT...");
        	int nodeCount = saveMctToFile(MCT_SAVE_DIR + "/" + this.getNextMCTSaveName(), NUM_SAVED_MCT_NODES);
        	System.out.println("Saved MCT with " + nodeCount + " nodes.");
        }
    	if(EXPERIMENT_SAVE_DIR != null && !EXPERIMENT_SAVE_DIR.equals("")) {
    		System.out.println("Saving experiment data...");
    		saveExperimentToFile();
    		System.out.println("Finished saving experiment data.");
    	}

    	this.rules = null;
		this.root = null;
		this.origRoot = null;
		this.existingNodes = new HashMap<Set<List<Integer>>, MCTNode>();
		this.sMap = null;
		this.rand = new Random();
		this.numTurns = 0;
		this.numRollouts = 0;
		this.nextTupleIndex = 0;
		this.tuplesByIndex = new HashMap<Integer, String>();
		this.indicesByTuple = new HashMap<String, Integer>();
		this.stateHistory = new LinkedList<Set<List<Integer>>>();

		System.out.println("All cleaned up.");
    }

    //Clean up data structures if the game ends abruptly
    @Override
    public void stateMachineAbort() {
    	this.rules = null;
		this.root = null;
		this.origRoot = null;
		this.existingNodes = new HashMap<Set<List<Integer>>, MCTNode>();
		this.sMap = null;
		this.rand = new Random();
		this.numTurns = 0;
		this.numRollouts = 0;
		this.nextTupleIndex = 0;
		this.tuplesByIndex = new HashMap<Integer, String>();
		this.indicesByTuple = new HashMap<String, Integer>();
		this.stateHistory = new LinkedList<Set<List<Integer>>>();
    }


    @Override
    public void preview(Game g, long timeout) throws GamePreviewException {
    	System.out.println("Preview was called");
    }
}