package org.ggp.base.player.gamer.statemachine.sample;

import java.io.BufferedReader;
import java.io.BufferedWriter;
import java.io.File;
import java.io.FileNotFoundException;
import java.io.FileReader;
import java.io.FileWriter;
import java.io.IOException;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Random;
import java.util.Scanner;
import java.util.Set;
import java.util.StringTokenizer;
import java.util.TreeMap;
import java.util.TreeSet;

import org.apache.commons.math4.legacy.stat.regression.SimpleRegression;
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


public class TestGamer extends StateMachineGamer
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
	private Map<Integer, Map<SymbolCountKey, Set<Integer>>> uniqueSymOccs; //stores unique numbers of occurrences for symbol keys at each depth in the game tree
	private List<FullRolloutData> symCountData;
	private Map<SymbolCountKey, Integer> maxSCVals;
	private Map<SymbolCountKey, Integer> minSCVals;
	private Map<Integer, Set<List<Integer>>> playedStates;
	private Map<SymbolCountKey, SymbolCountGameData> combinedPlayedCounts;
	private Map<Set<List<Integer>>, Map<SymbolCountKey, Integer>> symCountCache;
	private Set<SymbolCountKey> usefulSymKeys;
	private Set<Set<List<Integer>>> seenTerminalStates;
	private List<MobilityData> mobilityData;
	private List<Integer> maxMobility;
	private List<Integer> minMobility;
	private MobilityData playedMobility;
	private List<Map<List<Integer>, HistoryData>> historyData;
	private List<Map<Integer, HistoryData>> genHistoryData;
	private List<Set<List<Integer>>> playedMoves;
	private Map<SymbolCountKey, List<SymbolCountHeurData>> compiledSCData;
	private List<MobilityHeurData> compiledMobData;
	private List<SCRegressionContainer> scRegression;
	private List<SimpleRegression> mobRegression;
	private List<SimpleRegression> nearestWinRegression;
	private List<LoadedSCRegContainer> loadedSCRegression;
	private List<RegressionRecord> loadedMobRegression;
	private List<RegressionRecord> loadedNWRegression;

	private boolean recordSymOccs;
	private boolean recordMobility;
	private boolean recordNearestWin;
	private boolean recordHistory;
	private boolean heuristicsReady;

	//These are initialization parameters explained in and set by AutoPlayer
	public boolean USE_TRANSFER = false;
	public boolean ROLLOUT_ORDERING;
	public boolean USE_PLAY_TRANSFER = false;
	public boolean NW_ENABLED;
	public boolean USE_SELECTION_TRANSFER = false;
	public boolean SELECTION_HEURISTIC;
	public boolean USE_ROLLOUT_TRANSFER = false;
	public boolean EARLY_ROLLOUT_EVAL;
	public double PLAY_TRANSFER_RATIO = 0.5;
	public boolean LOAD_HEUR_FILE;
	public double SELECTION_TRANSFER_RATIO;
	public boolean SAVE_RULE_GRAPH_TO_FILE;
	public boolean SAVE_MCT_TO_FILE;
	public String MCT_READ_DIR;
	public boolean SAVE_EXPERIMENT;
	public String EXPERIMENT_SAVE_DIR;
	public boolean INITIAL_HEUR_RECORD;
	public boolean USE_ALT_HIST_HEUR;

	public int NUM_SAVED_MCT_NODES = -1; //10000; //-1 to save all (may be way too many to do this)

	public static final long TIME_THRESHOLD = 5000;
	public static final double EXPLORE_PARAM = 0.8;//0.4;//Math.sqrt(2);
	public static final double NEW_EXPLORE_VALUE = 1000000;
	public static final int ROLLOUT_MAX_DEPTH = 220;
	public static final double MAX_REWARD_VALUE = 100.0;
	public static final double MIN_REWARD_VALUE = 0.0;
	public static final double DISCOUNT_FACTOR = 0.999;
	public static final double CERTAINTY_OFFSET = 4.0;
	public static final double CERTAINTY_STEEPNESS = 1.0;
	public static final double STATE_CERTAINTY_OFFSET = 0.8;
	public static final double STATE_CERTAINTY_STEEPNESS = 20;
	public static final String PLAY_SELECT_MODE = "visits";  //one of "visits", or "reward"
	public String RULE_GRAPH_FILE = "";
	public String MCT_SAVE_DIR = "MCTs/checkers";
	public static final String EXP_SUMMARY_FILE = "summary.txt";
	public static final String HEUR_FILE_NAME = "heuristic_data.txt";

	public static final double HEURISTIC_WEIGHT = 10.0;
	public static final double TRANSFER_WEIGHT = 1.0;
	public static final double TRANSFER_DECAY_PER_VISIT = 0.9;
	public static final double TRANSFER_THRESHOLD = 0.1; //To save time, ignore transfer completely when it decays beyond this value

	public static final double HEURISTIC_INITIAL = 0.9;
	public static final double HEURISTIC_DECAY = 0.9;

	public static final double FLOAT_THRESH = 0.00001;
	public static final int WIN_THRESH = 80;
	public static final int LOSE_THRESH = 20;
	public static final int MIN_VISITS_FOR_SAVE = 4;
	public static final int ROLLOUT_EVAL_DEPTH = 10;
	public static final int ROLLOUT_GUIDE_DEPTH = 6;

	public TestGamer() {
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
		this.uniqueSymOccs = new HashMap<Integer, Map<SymbolCountKey, Set<Integer>>>();
		this.symCountData = new LinkedList<FullRolloutData>();
		this.maxSCVals = new HashMap<SymbolCountKey, Integer>();
		this.minSCVals = new HashMap<SymbolCountKey, Integer>();
		this.playedStates = new HashMap<Integer, Set<List<Integer>>>();
		this.combinedPlayedCounts = new HashMap<SymbolCountKey, SymbolCountGameData>();
		this.symCountCache = new HashMap<Set<List<Integer>>, Map<SymbolCountKey, Integer>>();
		this.usefulSymKeys = null;
		this.seenTerminalStates = new HashSet<Set<List<Integer>>>();
		this.mobilityData = new LinkedList<MobilityData>();
		this.maxMobility = new ArrayList<Integer>();
		this.minMobility = new ArrayList<Integer>();
		this.playedMobility = new MobilityData();
		this.historyData = new ArrayList<Map<List<Integer>, HistoryData>>();
		this.genHistoryData = new ArrayList<Map<Integer, HistoryData>>();
		this.playedMoves = new ArrayList<Set<List<Integer>>>();
		this.compiledSCData = new HashMap<SymbolCountKey, List<SymbolCountHeurData>>();
		this.compiledMobData = new ArrayList<MobilityHeurData>();
		this.scRegression = null;
		this.mobRegression = null;
		this.nearestWinRegression = null;
		this.loadedSCRegression = null;
		this.loadedMobRegression = null;
		this.loadedNWRegression = null;

		this.USE_TRANSFER = false;
		this.SAVE_RULE_GRAPH_TO_FILE = true;
		this.SAVE_MCT_TO_FILE = true;
	}

	//This is a janky hack to set parameters that should be set in the constructor
	//But the GGP library only allows default constructors, so whatever
	public void initParams(List<?> params) {

//		this.USE_TRANSFER = (Boolean)(params.get(0));
//		this.USE_PLAY_TRANSFER = (Boolean)(params.get(1));
		this.NW_ENABLED = (Boolean)(params.get(0));
//		this.USE_SELECTION_TRANSFER = (Boolean)(params.get(2));
		this.SELECTION_HEURISTIC = (Boolean)(params.get(1));
		this.ROLLOUT_ORDERING = (Boolean)(params.get(2));
//		this.USE_ROLLOUT_TRANSFER = (Boolean)(params.get(3));
		this.EARLY_ROLLOUT_EVAL = (Boolean)(params.get(3));
//		this.PLAY_TRANSFER_RATIO = (Double) params.get(4);
		this.LOAD_HEUR_FILE = (Boolean)(params.get(4));
//		this.SELECTION_TRANSFER_RATIO = (Double) params.get(5);
		this.RULE_GRAPH_FILE = (String)(params.get(5));
		this.SAVE_RULE_GRAPH_TO_FILE = (Boolean)(params.get(6));
		this.SAVE_MCT_TO_FILE = (Boolean)(params.get(7));
		this.MCT_READ_DIR = (String)(params.get(8));
		this.SAVE_EXPERIMENT = (Boolean)(params.get(9));
		this.EXPERIMENT_SAVE_DIR = (String)(params.get(10));

		this.MCT_SAVE_DIR = this.MCT_READ_DIR;
		this.INITIAL_HEUR_RECORD = (ROLLOUT_ORDERING || SELECTION_HEURISTIC || EARLY_ROLLOUT_EVAL) && !LOAD_HEUR_FILE;
		this.USE_ALT_HIST_HEUR = this.RULE_GRAPH_FILE.equals("connect_four_debug.txt");
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
    	this.heuristicsReady = false;

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

    	for(int i=0;i<this.allRoles.size();i++) {
    		this.playedMobility.numEntriesPerPlayer.add(0);
    		this.playedMobility.totalMobPerPlayer.add(0f);
    		this.maxMobility.add(-1000000); //sentinel value
    		this.minMobility.add(1000000);
    		this.playedMoves.add(new HashSet<List<Integer>>());
    		this.historyData.add(new HashMap<List<Integer>, HistoryData>());
    		this.genHistoryData.add(new HashMap<Integer, HistoryData>());
    	}

    	long transferStartTime = 0;
    	if(USE_TRANSFER || LOAD_HEUR_FILE) {
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
	    	if(USE_TRANSFER) {
	    		this.sMap.loadSourceStatesFromFile(MCT_READ_DIR + "/" + "MCT_combined.txt");
//	    		for(int i=0;i<this.allRoles.size();i++) {
//		    		HashMap<List<Integer>, Pair<Double, Long>> specific = this.sMap.getSourceStates().getSpecificMoveTotalData(i);
//		        	HashMap<Integer, Pair<Double, Long>> general = this.sMap.getSourceStates().getGeneralMoveTotalData(i);
//		        	System.out.println("*********** General Data for " + i + " ***********");
//		        	for(int genMove : general.keySet()) {
//		        		Pair<Double, Long> genData = general.get(genMove);
//		        		double value = (genData.getKey() / genData.getValue());
//		        		System.out.println(this.sMap.getSourceName(genMove) + ": " + value);
//		        	}
//		        	System.out.println("*********** Specific Data for " + i + " ***********");
//		        	for(List<Integer> specMove : specific.keySet()) {
//		        		Pair<Double, Long> specificData = specific.get(specMove);
//		        		double value = (specificData.getKey() / specificData.getValue());
//		        		System.out.println(this.sMap.getSourceName(specMove) + ": " + value);
//		        	}
//    			}
	    	}

	    	//Load heuristic file
	    	if(LOAD_HEUR_FILE) {
	    		this.loadHeuristicFile();
	    		System.out.println("$$$$$$$$$$$$$$$$$ Heuristic Load $$$$$$$$$$$$$$$$$");
	    		System.out.println(loadedSCRegression.get(0).avgR + " " + loadedSCRegression.get(0).regMap);
	    		System.out.println(loadedMobRegression.get(0).getR() + " " + loadedMobRegression.get(0).getN());
	    		System.out.println(loadedNWRegression.get(0).getR() + " " + loadedNWRegression.get(0).getN());
	    		System.out.println(genHistoryData.get(0));
	    		System.out.println(historyData.get(0));
	    		for(SymbolCountKey key : loadedSCRegression.get(0).regMap.keySet()) {
	    			System.out.println("$ " + key.toNameString(this.sMap));
	    		}
	    		for(int i=0;i<this.allRoles.size();i++) {
		    		System.out.println("*********** General History Data for " + i + " ***********");
		        	for(int genMove : genHistoryData.get(i).keySet()) {
		        		HistoryData genData = genHistoryData.get(i).get(genMove);
		        		double value = (genData.totalReward / (double)genData.numOccs);
		        		double winPercent = (genData.numWins / (double)genData.numOccs);
		        		System.out.println(this.sMap.getTargetName(genMove) + ": " + value + " " + winPercent);
		        	}
//		        	System.out.println("*********** Specific History Data for " + i + " ***********");
//		        	for(List<Integer> specMove : historyData.get(i).keySet()) {
//		        		HistoryData specData = historyData.get(i).get(specMove);
//		        		double value = (specData.totalReward / (double)specData.numOccs);
//		        		double winPercent = (specData.numWins / (double)specData.numOccs);
//		        		System.out.println(this.sMap.getTargetName(specMove) + ": " + specMove + " " + value + " " + winPercent);
//		        	}
	    		}
	    	}

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

    	if(INITIAL_HEUR_RECORD || SAVE_MCT_TO_FILE) {
	    	recordSymOccs = true;
	    	recordMobility = true;
	    	recordNearestWin = true;
	    	recordHistory = true;
    	} else {
    		recordSymOccs = false;
	    	recordMobility = false;
	    	recordNearestWin = true;
	    	recordHistory = false;
    	}

    	startTime = System.currentTimeMillis();

    	//Start MCTS
    	buildTreeForTime(timeout);

    	if(INITIAL_HEUR_RECORD) {
	    	System.out.println("^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^");
	    	long heurTimeStart = System.currentTimeMillis();
	    	this.prepHeuristics();
	    	long heurTimeEnd = System.currentTimeMillis();
	    	this.recordSymOccs = false;
	    	this.recordMobility = false;
	    	this.recordHistory = false;
	    	System.out.println(heurTimeEnd - heurTimeStart);
	    	System.out.println("SC: " + this.scRegression.get(0).toNameString(this.sMap));
	    	System.out.println("Gen History:");
	    	for(int moveID : this.genHistoryData.get(0).keySet()) {
	    		HistoryData data = this.genHistoryData.get(0).get(moveID);
	    		System.out.println(this.sMap.getTargetName(moveID) + ": " + ((double)data.totalReward) / data.numOccs);
	    	}
	    	System.out.println();
    	}
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

    		this.playedStates.put(root.getDepth(), root.getStateSet());
    		if(this.recordSymOccs) {
	    		Map<SymbolCountKey, Integer> justPlayedSymOcc = getSymOccFromState(root.getStateSet());
	    		updateSymbolCounts(this.combinedPlayedCounts, justPlayedSymOcc);
    		}
    		if(this.recordMobility && root.getDepth() > 0) {
    			int turnIndex = root.getWhoseTurnAssume2P();
    			int mobValue = root.getChildren().size() - root.getNumSiblings();
    			this.playedMobility.totalMobPerPlayer.set(turnIndex, this.playedMobility.totalMobPerPlayer.get(turnIndex) + mobValue);
    			this.playedMobility.numEntriesPerPlayer.set(turnIndex, this.playedMobility.numEntriesPerPlayer.get(turnIndex) + 1);
    		}
    		if(this.recordHistory) {
    			List<List<Integer>> convertedMove = this.sMap.convertMoveToList(lastMove);
    			for(int i=0;i<convertedMove.size();i++) {
    				this.playedMoves.get(i).add(convertedMove.get(i));
    			}
    		}

    		root = root.getChildren().get(lastMove);
            root.setParents(null);
    	}

    	if(SAVE_EXPERIMENT) {
    		this.stateHistory.addLast(root.getStateSet());
    	}

    	//now continue building the MCT
        buildTreeForTime(timeout);

        //Once we've done as much search as we have time for, select the best move to play
        List<Move> selectedMove = selectBestMove();

        System.out.println(root.getNumVisits());
        System.out.println(root.getTotalReward());
        System.out.println(getCurrentState().getContents());

//        System.out.println("Nearest Win: " + root.getChildren().get(selectedMove).getNearestWin() + " Loss: " + root.getChildren().get(selectedMove).getNearestLoss());

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
    		int numPlayers = this.allRoles.size();
    		ArrayList<Set<List<Integer>>> movesTaken = new ArrayList<Set<List<Integer>>>();
    		for(int i=0;i<numPlayers;i++) {
    			movesTaken.add(new HashSet<List<Integer>>());
    		}

    		while(currNode.isExpanded() && !currNode.isTerminal()) {
    			int turnIndex = currNode.getWhoseTurnAssume2P();
    			if(turnIndex == -1 || turnIndex == -2) { //If nobody has an option, or there are simultaneous turns, just assume our own perspective (NOTE: will need to be changed to better handle simultaneous turns)
    				turnIndex = this.roleIndex;
    			} //turnIndex cannot be -3 because state is not terminal
    			List<Move> selectedMove = selectChild(currNode, turnIndex);
    			List<List<Integer>> convertedMove = this.sMap.convertMoveToList(selectedMove);
    			for(int i=0;i<numPlayers;i++) {
    				movesTaken.get(i).add(convertedMove.get(i));
    			}

    			currNode = currNode.getChildren().get(selectedMove); //, (currentTime - startTime)/(double)duration);
//    			movesInOrder.add(selectedMove);
    			statesOnPath.add(currNode.getStateSet());
        		pathInOrder.add(currNode);
    		}
    		currNode.expandChildren();
    		if(!currNode.isTerminal()) {
    			if(EARLY_ROLLOUT_EVAL && this.heuristicsReady) {
    				currNode = rolloutEarlyEval(currNode, statesOnPath, pathInOrder, movesTaken);
    			} else if(ROLLOUT_ORDERING && this.heuristicsReady) { //Note: early rollout evaluation and rollout ordering cannot currently be used together
    				currNode = rolloutHeuristicOrdered(currNode, statesOnPath, pathInOrder, movesTaken);
    			} else {
    				currNode = rollout(currNode, statesOnPath, pathInOrder, movesTaken);
    			}
    		}

    		List<Integer> goals = null;
    		List<Double> goalDoubles;
    		if(currNode.isTerminal() ) {
				goals = currNode.getGoals();
				goalDoubles = new ArrayList<Double>();
				for(Integer i : goals) { //convert goal values to double type
					goalDoubles.add(i.doubleValue());
				}
				backprop(goalDoubles, pathInOrder, currNode);
    		} else {
    			goalDoubles = currNode.getHeuristicGoals();
    			earlyBackprop(goalDoubles, pathInOrder);
    		}


			if(currNode.isTerminal() ) {
    			if(this.recordHistory && !this.seenTerminalStates.contains(currNode.getStateSet())) {
    				for(int i=0;i<numPlayers;i++) {
    					movesTaken.get(i).addAll(this.playedMoves.get(i));
    					HashSet<Integer> genSet = new HashSet<Integer>();
    					for(List<Integer> move : movesTaken.get(i)) {
    						int genMoveVal = move.get(0);
    						if(!this.historyData.get(i).containsKey(move)) {
    							this.historyData.get(i).put(move, new HistoryData());
    						}
    						HistoryData currData = this.historyData.get(i).get(move);
    						currData.numOccs += 1;
    						currData.totalReward += goals.get(i);
    						if(goals.get(i) >= WIN_THRESH) {
    							currData.numWins += 1;
    						} else if(goals.get(i) <= LOSE_THRESH) {
    							currData.numLosses += 1;
    						} else {
    							currData.numOther += 1;
    						}
    						if(!genSet.contains(genMoveVal)) {
    							if(!this.genHistoryData.get(i).containsKey(genMoveVal)) {
    								this.genHistoryData.get(i).put(genMoveVal, new HistoryData());
    							}
    							HistoryData currGenData = this.genHistoryData.get(i).get(genMoveVal);
    							currGenData.numOccs += 1;
    							currGenData.totalReward += goals.get(i);
    							if(goals.get(i) >= WIN_THRESH) {
        							currGenData.numWins += 1;
        						} else if(goals.get(i) <= LOSE_THRESH) {
        							currGenData.numLosses += 1;
        						} else {
        							currGenData.numOther += 1;
        						}
    							genSet.add(genMoveVal);
    						}
    					}
    				}
    			}

    			this.seenTerminalStates.add(currNode.getStateSet());
    		}
    		currentTime = System.currentTimeMillis();
    	}
    }

    public static double clampRewardVal(double val) {
    	if(val < MIN_REWARD_VALUE) {
    		return MIN_REWARD_VALUE;
    	} else if(val > MAX_REWARD_VALUE) {
    		return MAX_REWARD_VALUE;
    	} else {
    		return val;
    	}
    }

    public double calcHeuristicValue(Move m, MCTNode node, int roleIndex, Set<List<Move>> allMoveCombos, boolean verbose) {
    	List<Integer> moveList = this.sMap.convertMoveToList(m);
    	int genID = moveList.get(0);

    	Map<SymbolCountKey, Integer> symCounts = this.getSymOccFromState(node.getStateSet());
    	PredictionPackage scPackage;
    	if(LOAD_HEUR_FILE) {
    		scPackage = this.loadedSCRegression.get(roleIndex).combinedPredict(symCounts);
    	} else {
    		scPackage = this.scRegression.get(roleIndex).combinedPredict(symCounts);
    	}
    	double scVal = scPackage.prediction;
    	double scWeight = scPackage.maxR;

    	double mobVal = 0;
    	double mobWeight = 0;

    	int mobDif = -node.getMobility2P();
    	if(LOAD_HEUR_FILE) {
    		mobVal = clampRewardVal(this.loadedMobRegression.get(roleIndex).predict(mobDif));
	    	mobWeight = Math.abs(this.loadedMobRegression.get(roleIndex).getR());
    	} else {
	    	mobVal = clampRewardVal(this.mobRegression.get(roleIndex).predict(mobDif));
	    	mobWeight = Math.abs(this.mobRegression.get(roleIndex).getR());
    	}
    	if(Double.isNaN(mobVal)) {
    		mobVal = 0.0;
    		mobWeight = 0.0;
    	}

    	double nearestWinVal = 0;
    	double nearestWinWeight = 0;
    	if(NW_ENABLED) {
	    	int nearestWin = node.getNearestWin().get(roleIndex);
	    	if(nearestWin >= 0) {
	    		if(LOAD_HEUR_FILE) {
	    			nearestWinVal = clampRewardVal(this.loadedNWRegression.get(roleIndex).predict(nearestWin));
		    		nearestWinWeight = Math.abs(this.loadedNWRegression.get(roleIndex).getR());
	    		} else {
		    		nearestWinVal = clampRewardVal(this.nearestWinRegression.get(roleIndex).predict(nearestWin));
		    		nearestWinWeight = Math.abs(this.nearestWinRegression.get(roleIndex).getR());
	    		}
	    	}
    	}

    	double genHistVal = 0;
    	double genHistWeight = 0;
    	double specHistVal = 0;
    	double specHistWeight = 0;

    	if(USE_ALT_HIST_HEUR) {
    		Set<Integer> availableGenMoves = new HashSet<Integer>();
    		Set<List<Integer>> availableSpecMoves = new HashSet<List<Integer>>();
    		for(List<Move> moveCombo : allMoveCombos) {
    			List<Integer> currMove = this.sMap.convertMoveToList(moveCombo.get(roleIndex));
    			if(this.genHistoryData.get(roleIndex).containsKey(currMove.get(0))) {
    				availableGenMoves.add(currMove.get(0));
    			}
    			if(this.historyData.get(roleIndex).containsKey(currMove)) {
    				availableSpecMoves.add(currMove);
    			}
    		}

    		if(availableGenMoves.size() > 1) {
	    		double minGenVal = 1000;
	    		double maxGenVal = -1000;
	    		for(int currMoveID : availableGenMoves) {
	    			HistoryData data = this.genHistoryData.get(roleIndex).get(currMoveID);
	    			double genMoveVal = data.totalReward / (double)data.numOccs;
	    			if(genMoveVal > maxGenVal) {
	    				maxGenVal = genMoveVal;
	    			}
	    			if(genMoveVal < minGenVal) {
	    				minGenVal = genMoveVal;
	    			}
	    		}
		    	double interval = maxGenVal - minGenVal;
		    	if(this.genHistoryData.get(roleIndex).containsKey(genID) && interval > 0) {
		    		HistoryData data = this.genHistoryData.get(roleIndex).get(genID);
		    		genHistVal = MAX_REWARD_VALUE * ((((double)data.totalReward) / data.numOccs) - minGenVal) / interval;
		    		genHistWeight = Math.abs(genHistVal/(double)MAX_REWARD_VALUE - 0.5) * 2;
		    	}
    		}

    		if(availableSpecMoves.size() > 1) {
	    		double minSpecVal = 1000;
	    		double maxSpecVal = -1000;
	    		for(List<Integer> currMoveID : availableSpecMoves) {
	    			HistoryData data = this.historyData.get(roleIndex).get(currMoveID);
	    			double specMoveVal = data.totalReward / (double)data.numOccs;
	    			if(specMoveVal > maxSpecVal) {
	    				maxSpecVal = specMoveVal;
	    			}
	    			if(specMoveVal < minSpecVal) {
	    				minSpecVal = specMoveVal;
	    			}
	    		}
		    	double interval = maxSpecVal - minSpecVal;
		    	if(this.historyData.get(roleIndex).containsKey(moveList) && interval > 0) {
		    		HistoryData data = this.historyData.get(roleIndex).get(moveList);
		    		specHistVal = MAX_REWARD_VALUE * ((((double)data.totalReward) / data.numOccs) - minSpecVal) / interval;
		    		specHistWeight = Math.abs(specHistVal/(double)MAX_REWARD_VALUE - 0.5) * 2;
		    	}
    		}

    	} else {
	    	double midVal = (MAX_REWARD_VALUE + MIN_REWARD_VALUE) / 2.0;
	    	double divisor = (MAX_REWARD_VALUE - MIN_REWARD_VALUE) / 2.0;
	    	if(this.genHistoryData.get(roleIndex).containsKey(genID)) {
	    		HistoryData data = this.genHistoryData.get(roleIndex).get(genID);
	    		genHistVal = ((double)data.totalReward) / data.numOccs;
	//    		genHistWeight = Math.pow(Math.abs(genHistVal - midVal)/divisor, 2);
	    		genHistWeight = Math.abs(genHistVal - midVal)/divisor;
	    	}

	    	if(this.historyData.get(roleIndex).containsKey(moveList)) {
	    		HistoryData data = this.historyData.get(roleIndex).get(moveList);
	    		specHistVal = ((double)data.totalReward) / data.numOccs;
	    		specHistWeight = Math.abs(specHistVal - midVal)/divisor;
	    	}
    	}

    	double totalWeight = scWeight + mobWeight + nearestWinWeight + genHistWeight + specHistWeight;
    	double result = 0;
    	if(totalWeight > 0) {
    		result = (scVal*scWeight + mobVal*mobWeight + nearestWinVal*nearestWinWeight + genHistVal*genHistWeight + specHistVal*specHistWeight) / totalWeight;
    	}

    	if(verbose) {
	    	System.out.println("*** Heuristic Calculation ***");
	    	System.out.println(result);
	    	System.out.println("SC: " + scVal + " " + scWeight);
	    	System.out.println("Mob: " + mobVal + " " + mobWeight + " " + mobDif);
	    	System.out.println("NW: " + nearestWinVal + " " + nearestWinWeight + " " + node.getNearestWin().get(roleIndex));
	    	System.out.println("Gen Hist: " + genHistVal + " " + genHistWeight);
	    	System.out.println("Spec Hist: " + specHistVal + " " + specHistWeight);
	    	System.out.println("");
    	}

    	node.getHeuristicGoals().set(roleIndex, result);
    	return result;
    }
//
//    public float calcSCValue(MCTNode node, int roleIndex) {
//
//    }
//
//    public float calcSCWeight(int roleIndex) {
//
//    }

    public void prepHeuristics() {
    	this.usefulSymKeys = trimUnchangingSyms();
    	this.scRegression = new ArrayList<SCRegressionContainer>();
    	this.mobRegression = new ArrayList<SimpleRegression>();
    	this.nearestWinRegression = new ArrayList<SimpleRegression>();
    	for(int i=0; i<this.allRoles.size(); i++) {
    		this.scRegression.add(doSCRegression(this.symCountData, this.usefulSymKeys, i));
    		this.mobRegression.add(doMobilityRegression(this.mobilityData, i));
    		this.nearestWinRegression.add(doNearestWinRegression(this.root, i));
    	}
    	this.heuristicsReady = true;
    }

//    public float calcMobValue(MCTNode node, int roleIndex) {
//    	int currMob = node.getChildren().size() - node.getNumSiblings();
//    	float result = 0;
//    	if(this.compiledMobData.size() > 0) {
//    		MobilityHeurData data = this.compiledMobData.get(roleIndex);
//    		if(data.numWins > 0 && data.numLosses > 0) { //There is no useful information if there aren't at least some wins and some losses
//    			float winAvg = ((float)data.totalWinValue)/data.numWins;
//    			float lossAvg = ((float)data.totalLossValue)/data.numLosses;
//    			float winDist = Math.abs(currMob - winAvg);
//    			float lossDist = Math.abs(currMob - lossAvg);
//    			if(Math.abs(winAvg - lossAvg) > FLOAT_THRESH) { //No useful information if win and lost avgs are equal
//    				result = lossDist / (winDist + lossDist);
//    			}
//    		}
//    	}
//    	return result;
//    }
//
//    public float calcMobWeight(int roleIndex) {
//    	float result = 0;
//    	if(this.compiledMobData.size() > 0) {
//    		MobilityHeurData data = this.compiledMobData.get(roleIndex);
//    		if(data.numWins > 0 && data.numLosses > 0) { //There is no useful information if there aren't at least some wins and some losses
//    			float winAvg = ((float)data.totalWinValue)/data.numWins;
//    			float lossAvg = ((float)data.totalLossValue)/data.numLosses;
//    			float intervalSize = Math.abs(data.maxValue - data.minValue);
//    			if(intervalSize > FLOAT_THRESH) {
//    				result = Math.abs(winAvg - lossAvg) / intervalSize;
//    			}
//    		}
//    	}
//    	return result;
//    }


    public static SCRegressionContainer doSCRegression(List<FullRolloutData> scData, Set<SymbolCountKey> usefulKeys, int roleIndex) {
    	return doSCRegression(scData, usefulKeys, roleIndex, new SCRegressionContainer());
    }

    //if usefulKeys = null, then assume all keys are useful
    public static SCRegressionContainer doSCRegression(List<FullRolloutData> scData, Set<SymbolCountKey> usefulKeys, int roleIndex, SCRegressionContainer container) {
//    	SCRegressionContainer container = new SCRegressionContainer();
    	for(FullRolloutData data : scData) {
    		int reward = data.finalReward.get(roleIndex);
    		if (usefulKeys != null) {
	    		for(SymbolCountKey key : usefulKeys) {
	    			if(data.symCountData.containsKey(key)) {
	    				SymbolCountGameData curr = data.symCountData.get(key);
	    				if(curr.numSteps > 0) {
		    				if(!container.regMap.containsKey(key)) {
		    					container.regMap.put(key, new SimpleRegression());
		    					container.occMap.put(key, 0);
		    				}
		    				double x = ((double)curr.totalOcc) / curr.numSteps;
		    				double y = reward;
		    				container.regMap.get(key).addData(x, y);
		    				container.occMap.put(key, container.occMap.get(key) + 1); //weighting based on number of rollouts it appeared in
	    				}
	    			}
	    		}
    		} else {
    			for(SymbolCountKey key : data.symCountData.keySet()) {
    				SymbolCountGameData curr = data.symCountData.get(key);
    				if(curr.numSteps > 0) {
	    				if(!container.regMap.containsKey(key)) {
	    					container.regMap.put(key, new SimpleRegression());
	    					container.occMap.put(key, 0);
	    				}
	    				double x = ((double)curr.totalOcc) / curr.numSteps;
	    				double y = reward;
	    				container.regMap.get(key).addData(x, y);
	    				container.occMap.put(key, container.occMap.get(key) + 1); //weighting based on number of rollouts it appeared in
    				}
	    		}
    		}
    	}

    	double sumR = 0;
    	int totalWeight = 0;
    	for(SymbolCountKey key : container.regMap.keySet()) {
    		SimpleRegression currReg = container.regMap.get(key);
    		double currWeight = container.occMap.get(key);
    		sumR += currReg.getR() * currWeight;
    		totalWeight += currWeight;
    	}
    	container.avgR = sumR / totalWeight;
    	container.totalOcc = totalWeight;

    	return container;
    }


    public static SimpleRegression doMobilityRegression(List<MobilityData> mobData, int roleIndex) {
    	return doMobilityRegression(mobData, roleIndex, new SimpleRegression());
    }

    public static SimpleRegression doMobilityRegression(List<MobilityData> mobData, int roleIndex, SimpleRegression reg) {
//    	SimpleRegression reg = new SimpleRegression();
    	for(MobilityData currData : mobData) {
    		if(currData.numEntriesPerPlayer.get(roleIndex) > 0) {
    			double x = currData.totalMobPerPlayer.get(roleIndex) / currData.numEntriesPerPlayer.get(roleIndex);
    			double y = currData.finalReward.get(roleIndex);
    			reg.addData(x, y);
    		}
    	}
    	return reg;
    }


    public static SimpleRegression doNearestWinRegression(MCTNode root, int roleIndex) {
    	return doNearestWinRegression(root, roleIndex, new SimpleRegression());
    }

//    public static SimpleRegression doNearestWinRegression(MCTNode root, int roleIndex, SimpleRegression reg) {
//    	List<MCTNode> allNodes = queueNoPriority(-1, root);
//    	return doNearestWinRegression(allNodes, roleIndex, reg);
//    }

    public static SimpleRegression doNearestWinRegression(MCTNode root, int roleIndex, SimpleRegression reg) {
    	List<MCTNode> allNodes = queueNoPriority(-1, root);
//    	SimpleRegression reg = new SimpleRegression();
    	for(MCTNode currNode : allNodes) {
    		double x = currNode.getNearestWin().get(roleIndex);
    		if(x >= 0) {
    			double y = currNode.getTotalReward().get(roleIndex) / currNode.getNumVisits();
    			reg.addData(x, y);
    		}
    	}
    	return reg;
    }

    public static SimpleRegression doNearestWinRegression(List<ReducedMCTNode> allNodes, int roleIndex, SimpleRegression reg) {
//    	List<MCTNode> allNodes = queueNoPriority(-1, root);
//    	SimpleRegression reg = new SimpleRegression();
    	for(ReducedMCTNode currNode : allNodes) {
    		double x = currNode.getNearestWin().get(roleIndex);
    		if(x >= 0) {
    			double y = currNode.getTotalReward().get(roleIndex) / currNode.getNumVisits();
    			reg.addData(x, y);
    		}
    	}
    	return reg;
    }


//    public static GenHistoryRegressionContainer doGenHistoryRegression(List<Map<Integer, HistoryData>> histData, int roleIndex) {
//    	GenHistoryRegressionContainer container = new GenHistoryRegressionContainer();
//    	for(int moveID : histData.get(roleIndex).keySet()) {
//    		HistoryData currData = histData.get(roleIndex).get(moveID);
//    		if(!container.regMap.containsKey(moveID)) {
//    			container.regMap.put(moveID, new SimpleRegression());
//    		}
//    		SimpleRegression reg = container.regMap.get(moveID);
//
//    	}
//    }


    //Just put all the nodes in the subtree rooted at root into a List with no particular ordering
    public static LinkedList<MCTNode> queueNoPriority(int numNodes, MCTNode root) {
    	LinkedList<MCTNode> result = new LinkedList<MCTNode>();
    	LinkedList<MCTNode> q = new LinkedList<MCTNode>();
//    	HashSet<Set<List<Integer>>> usedStates = new HashSet<Set<List<Integer>>>();
    	q.add(root);

    	while(!q.isEmpty()) {
    		MCTNode currNode = q.pop();
    		result.add(currNode);
    		if(numNodes >= 0 && result.size() >= numNodes) {
    			break;
    		}
    		for(MCTNode child : currNode.getChildren().values()) {
    			if(child != null) {
    				q.addLast(child);
    			}
    		}
    	}
    	return result;
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

    			if(currNode.getNumVisits() >= MIN_VISITS_FOR_SAVE) { //don't bother saving nodes that were only hit once by a rollout
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



    public String moveToIDString(List<Integer> move) {
    	String result = "( ";
    	for(int item : move) {
    		result += item + " ";
    	}
    	result += ")";
    	return result;
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


    public void compileSCData() {
    	this.compiledSCData = new HashMap<SymbolCountKey, List<SymbolCountHeurData>>(); //Inner list contains data for each player
    	int numRoles = this.allRoles.size();
		if(this.usefulSymKeys == null) {
			this.usefulSymKeys = trimUnchangingSyms();
		}
		for(SymbolCountKey key : this.usefulSymKeys) {
			for(FullRolloutData gameData : this.symCountData) {
				if(!this.compiledSCData.containsKey(key)) {
					this.compiledSCData.put(key, new ArrayList<SymbolCountHeurData>());
					for(int i=0;i<numRoles;i++) {
						this.compiledSCData.get(key).add(new SymbolCountHeurData());
					}
				}
				for(int playerNum=0;playerNum<numRoles;playerNum++) {
					int playerReward = gameData.finalReward.get(playerNum);
					SymbolCountGameData keyedGameData = gameData.symCountData.get(key);
					SymbolCountHeurData currData = this.compiledSCData.get(key).get(playerNum);
					if(gameData.symCountData.containsKey(key) && gameData.symCountData.get(key).numSteps > 0) {
						float symValue = ((float)keyedGameData.totalOcc) / keyedGameData.numSteps;
						currData.maxValue = Math.max(symValue, currData.maxValue);
						if(playerReward >= WIN_THRESH) {
							currData.totalWinValue += symValue;
							currData.numWins ++;
						} else if (playerReward <= LOSE_THRESH) {
							currData.totalLossValue += symValue;
							currData.numLosses ++;
						} else {
							currData.totalOtherValue += symValue;
							currData.numOther ++;
						}
					}
				}
			}
		}
    }


    public void compileMobilityData() {
    	this.compiledMobData = new ArrayList<MobilityHeurData>();
    	int numRoles = this.allRoles.size();

		for(int i=0;i<numRoles;i++) {
			this.compiledMobData.add(new MobilityHeurData());
			this.compiledMobData.get(i).maxValue = this.maxMobility.get(i);
			this.compiledMobData.get(i).minValue = this.minMobility.get(i);
		}
		for(MobilityData datum : this.mobilityData) {
			for(int i=0;i<numRoles;i++) {
				MobilityHeurData currHeur = this.compiledMobData.get(i);
				if(datum.numEntriesPerPlayer.get(i) > 0) {
					float avg = ((float)datum.totalMobPerPlayer.get(i)) / datum.numEntriesPerPlayer.get(i);
					int playerReward = datum.finalReward.get(i);
					if(playerReward >= WIN_THRESH) {
						currHeur.totalWinValue += avg;
						currHeur.numWins += 1;
					} else if (playerReward <= LOSE_THRESH) {
						currHeur.totalLossValue += avg;
						currHeur.numLosses += 1;
					} else {
						currHeur.totalOtherValue += avg;
						currHeur.numOther += 1;
					}
				}
			}
		}
    }


    //give -1 to numNodes to save the whole MCT
    //returns the number of nodes saved to file
    //This method saves an MCT to file for one instance of a game. The archives built in the "Archiving Information" subsection will be built from these files.
    public int saveMctToFile(String outFileName, int numNodes) {
		if(origRoot == null) {
			System.out.println("ERROR in saveMctToFile: MCT has not been initialized.");
		}

		LinkedList<MCTNode> q = queueNodes(numNodes);
		int numRoles = this.allRoles.size();

		//Symbol Counting Heuristic
//		String symbolCountStr[] = new String[numRoles];
//		for(int i=0;i<numRoles;i++) {
//
//		}

		if(this.usefulSymKeys == null) {
			this.usefulSymKeys = trimUnchangingSyms();
		}
//		for(SymbolCountKey key : this.usefulSymKeys) {
//			System.out.println(key.toNameString(this.sMap));
//		}

		String scMaxMinStr = "";
		String symbolCountStr = "";
		if(!this.usefulSymKeys.isEmpty()) {
			for(SymbolCountKey key : this.usefulSymKeys) {
				scMaxMinStr += key.mainSym + " " + key.parentSym + " " + key.posn + " " + this.maxSCVals.get(key) + " " + this.minSCVals.get(key) + " * ";
			}

			for(FullRolloutData currData : this.symCountData) {
				for(int i=0;i<numRoles;i++) {
					symbolCountStr += currData.finalReward.get(i) + " ";
				}
				for(SymbolCountKey key : this.usefulSymKeys) {
					if(currData.symCountData.containsKey(key)) {
						SymbolCountGameData value = currData.symCountData.get(key);
						symbolCountStr += key.mainSym + " " + key.parentSym + " " + key.posn + " " + value.totalOcc + " " + value.numSteps + " # ";
					}
				}
				if(symbolCountStr.charAt(symbolCountStr.length() - 2) == '#') {
					symbolCountStr = symbolCountStr.substring(0, symbolCountStr.length() - 2);
					symbolCountStr += "* ";
				}
			}
		}
		scMaxMinStr += "\n";
		symbolCountStr += "\n";
//		this.compileSCData();
//		Map<SymbolCountKey, List<SymbolCountHeurData>> allSCData = this.compiledSCData;
//
//		String symbolCountStr = "";
//		for(SymbolCountKey key : this.usefulSymKeys) {
//			symbolCountStr += key.mainSym + " " + key.parentSym + " " + key.posn + " ";
//			for(int i=0;i<numRoles;i++) {
//				SymbolCountHeurData currData = allSCData.get(key).get(i);
//				symbolCountStr += currData.totalWinValue + " " + currData.totalLossValue + " " + currData.totalOtherValue + " " + currData.numWins +
//						" " + currData.numLosses + " " + currData.numOther + " " + currData.maxValue + " ";
//				if(i < numRoles-1) {
//					symbolCountStr += "& ";
//				}
//			}
//			symbolCountStr += "* ";
//		}
//		symbolCountStr += "\n";

		//Mobility Heuristic
//		this.compileMobilityData();

		String mobilityStr = "";
		for(MobilityData data : this.mobilityData) {
			for(int i=0;i<numRoles;i++) {
				mobilityStr += data.finalReward.get(i) + " " + data.totalMobPerPlayer.get(i) + " " + data.numEntriesPerPlayer.get(i) + " ";
			}
			mobilityStr += "* ";
		}
		mobilityStr += "\n";

//		for(int i=0;i<numRoles;i++) {
//			MobilityHeurData currData = this.compiledMobData.get(i);
//			mobilityStr += currData.totalWinValue + " " + currData.totalLossValue + " " + currData.totalOtherValue + " " + currData.numWins +
//					" " + currData.numLosses + " " + currData.numOther + " " + currData.maxValue + " " + currData.minValue + " ";
//			if(i < numRoles-1) {
//				mobilityStr += "& ";
//			}
//		}
//		mobilityStr += "\n";


		System.out.println("********************");
//		System.out.println(this.usefulSymKeys);
//		System.out.println(this.symCountData);
//		System.out.println(allSCData);

//		for(SymbolCountKey key : this.usefulSymKeys) {
//			System.out.println(key.toNameString(sMap));
//			for(int i=0;i<numRoles;i++) {
//				System.out.println(allSCData.get(key).get(i));
//			}
//		}

//		for(int i=0;i<numRoles;i++) {
//			MobilityHeurData currHeur = this.compiledMobData.get(i);
//			System.out.println("Player " + i);
//			System.out.println("Max Mobility: " + currHeur.maxValue + ", Min Mobility: " + currHeur.minValue);
//			if(currHeur.numWins > 0) {
//				System.out.println("Avg. Win Mobility: " + currHeur.totalWinValue/currHeur.numWins + ", # Wins: " + currHeur.numWins);
//			} else {
//				System.out.println("No win mobility data.");
//			}
//			if(currHeur.numLosses > 0) {
//				System.out.println("Avg. Loss Mobility: " + currHeur.totalLossValue/currHeur.numLosses + ", # Losses: " + currHeur.numLosses);
//			} else {
//				System.out.println("No loss mobility data.");
//			}
//			if(currHeur.numOther > 0) {
//				System.out.println("Avg. Other Mobility: " + currHeur.totalOtherValue/currHeur.numOther + ", # Other: " + currHeur.numOther);
//			} else {
//				System.out.println("No other mobility data.");
//			}
//		}

//		for(int i=0;i<numRoles;i++) {
//			System.out.println("Player " + i);
//			System.out.println("General History Values:");
//			for(int genValue : this.genHistoryData.get(i).keySet()) {
//				HistoryData currData = this.genHistoryData.get(i).get(genValue);
//				System.out.println(this.sMap.getTargetName(genValue) + " avg: " + ((float)currData.totalReward)/currData.numOccs + " #: " + currData.numOccs);
//			}
//			System.out.println("Specific History Values:");
//			for(List<Integer> move : this.historyData.get(i).keySet()) {
//				HistoryData currData = this.historyData.get(i).get(move);
//				System.out.println(this.sMap.getTargetName(move) + " avg: " + ((float)currData.totalReward)/currData.numOccs + " #: " + currData.numOccs);
//			}
//		}


		int count = 0;
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
		List<HashMap<List<Integer>, Integer>> convertedMoveToID = new ArrayList<HashMap<List<Integer>, Integer>>();
		for(int i=0;i<numRoles;i++) {
			nextMoveID[i] = 0;
			moveToID.add(new HashMap<Move,Integer>());
			convertedMoveToID.add(new HashMap<List<Integer>, Integer>());
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
			outStr += currMCTNode.getDepth() + " "; //Print depth of the node in the game tree (root is 0)
			for(int i=0;i<numRoles;i++) { //Print the distance to the nearest win and loss for each player
				outStr += currMCTNode.getNearestWin().get(i) + " " + currMCTNode.getNearestLoss().get(i) + " ";
			}

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
							convertedMoveToID.get(i).put(this.sMap.convertMoveToList(roleMove), currMoveID);
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


		//History Heuristic
		String specHistoryStr[] = new String[numRoles];
		String genHistoryStr[] = new String[numRoles];
		for(int i=0;i<numRoles;i++) {
			genHistoryStr[i] = "";
			specHistoryStr[i] = "";
			for(int genValue : this.genHistoryData.get(i).keySet()) {
				HistoryData currData = this.genHistoryData.get(i).get(genValue);
				genHistoryStr[i] += genValue + " " + currData.totalReward + " " + currData.numWins + " " + currData.numLosses + " "
						+ currData.numOther + " " + currData.numOccs + " * ";
			}

			for(List<Integer> move : this.historyData.get(i).keySet()) {
				int currMoveID;
				HashMap<List<Integer>, Integer> roleMoveToID = convertedMoveToID.get(i);
				if(roleMoveToID.containsKey(move)) {
					currMoveID = roleMoveToID.get(move);
				} else {
					currMoveID = nextMoveID[i];
					nextMoveID[i] += 1;
					roleMoveToID.put(move, currMoveID);
					moveIDStr[i] += currMoveID + " " + moveToIDString(move) + " ";
				}
				HistoryData currData = this.historyData.get(i).get(move);
				specHistoryStr[i] += currMoveID + " " + currData.totalReward + " " + currData.numWins + " " + currData.numLosses + " "
						+ currData.numOther + " " + currData.numOccs + " * ";
			}
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
            br.write(scMaxMinStr);
            br.write(symbolCountStr);
            br.write(mobilityStr);
            for(int i=0;i<numRoles;i++) {
            	br.write(moveIDStr[i] + "\n");
            }
            for(int i=0;i<numRoles;i++) {
            	br.write(genHistoryStr[i] + "\n");
            }
            for(int i=0;i<numRoles;i++) {
            	br.write(specHistoryStr[i] + "\n");
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
    	double bestHeuristic = -1000;
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


    		System.out.println("! " + currNode.getTotalReward().get(this.roleIndex) / currNode.getNumVisits() + " " + currNode.getHeuristicGoals().get(this.roleIndex) + " " + currNode.getNumVisits() + " " + move);
//    		System.out.println(ucb1Basic(currNode, this.roleIndex));
//    		System.out.println("# " + currNode.getNumSiblings());

    		if(bestMove == null || currScore > bestScore+FLOAT_THRESH) {
    			bestMove = move;
    			bestScore = currScore;
    		} else if(SELECTION_HEURISTIC && this.heuristicsReady && Math.abs(bestScore - currScore) < FLOAT_THRESH) {
    			if(bestHeuristic < 0) {
    				bestHeuristic = this.calcHeuristicValue(bestMove.get(this.roleIndex), root.getChildren().get(bestMove), this.roleIndex, root.getChildren().keySet(), false);
    			}
    			double currHeuristic = this.calcHeuristicValue(move.get(this.roleIndex), root.getChildren().get(move), this.roleIndex, root.getChildren().keySet(), false);
    			if(currHeuristic > bestHeuristic) {
    				bestMove = move;
        			bestScore = currScore;
    			}
    		}
    	}

    	System.out.println("Best Score: " + bestScore + " " + bestMove);
    	System.out.println("Role: " + this.getRole());
    	if(this.heuristicsReady) {
    		this.calcHeuristicValue(bestMove.get(roleIndex), this.root.getChildren().get(bestMove), this.roleIndex, this.root.getChildren().keySet(), true);
    	}
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
    		} else if(SELECTION_HEURISTIC && this.heuristicsReady) {
    			currScore = ucb1HeuristicGuided(child, moveCombo.get(turnIndex), turnIndex, currNode.getChildren().keySet());
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
//    		System.out.println("% " + currScore);
    	}
//    	System.out.println("%%% " + bestCombos.size() + " " + currNode.getChildren().keySet().size());
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


    private double ucb1HeuristicGuided (MCTNode currNode, Move m, int turnIndex, Set<List<Move>> allMoveCombos) {
    	double regularValue, regularExplore, finalValue;
    	if(currNode == null || currNode.getNumVisits() == 0) {
    		regularValue = 0;
    		regularExplore = NEW_EXPLORE_VALUE;
    		finalValue = regularValue;
    	} else {
    		regularValue = (currNode.getTotalReward().get(turnIndex) / MAX_REWARD_VALUE) / currNode.getNumVisits();
    		regularExplore = EXPLORE_PARAM*Math.sqrt(Math.log(currNode.getTotalParentVisits())/currNode.getNumVisits());
    		double heuristicWeight = HEURISTIC_INITIAL * Math.pow(HEURISTIC_DECAY, currNode.getNumVisits()-1);
    		double regularWeight = 1 - heuristicWeight;
    		double heuristicValue = calcHeuristicValue(m, currNode, turnIndex, allMoveCombos, false) / MAX_REWARD_VALUE;
    		finalValue = heuristicValue*heuristicWeight + regularValue*regularWeight;
    	}

//    		System.out.println("&& " + heuristicValue + " " + regularValue + " " + heuristicWeight + " " + regularWeight + " " + regularExplore);
    	return finalValue + regularExplore;
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


    private MCTNode rolloutHeuristicOrdered (MCTNode startNode, Set<Set<List<Integer>>> statesOnPath, ArrayList<MCTNode> pathInOrder, ArrayList<Set<List<Integer>>> movesTaken) {
    	MCTNode currNode = startNode;
    	int depth = 0;
    	this.numRollouts ++;

    	while(!currNode.isTerminal() && depth < ROLLOUT_MAX_DEPTH) {
    		currNode.expandChildren();
    		List<Move> selectedMove = null;
			double bestScore = 0.0;
			List<List<Integer>> bestNearestMove = null;

			if(depth < ROLLOUT_GUIDE_DEPTH) {
				for(List<Move> currMove : currNode.getChildren().keySet()) {
					int turnIndex = currNode.getWhoseTurnAssume2P();
					if(turnIndex < 0) {
						turnIndex = 0;
					}
					MCTNode currChild = currNode.getExpandedChild(currMove, this.existingNodes, SAVE_MCT_TO_FILE);

					double heurScore = this.calcHeuristicValue(currMove.get(turnIndex), currChild, turnIndex, currNode.getChildren().keySet(), false);
					if(heurScore > bestScore) {
						bestScore = heurScore;
						selectedMove = currMove;
					}
				}
			}
			if(selectedMove == null) {
				selectedMove = randomMove(currNode);
			}

    		List<List<Integer>> convertedMove = this.sMap.convertMoveToList(selectedMove);
			for(int i=0;i<convertedMove.size();i++) {
				movesTaken.get(i).add(convertedMove.get(i));
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
    		System.out.println(NW_ENABLED + " " + SELECTION_HEURISTIC + " " + ROLLOUT_ORDERING + " " + EARLY_ROLLOUT_EVAL + " " + MCT_READ_DIR + " " + this.getRole() + " " + this.numRollouts + " rollouts. " + (System.currentTimeMillis() - this.startTime) + " ms.");
    	}

    	return currNode;
    }


    private MCTNode rolloutEarlyEval (MCTNode startNode, Set<Set<List<Integer>>> statesOnPath, ArrayList<MCTNode> pathInOrder, ArrayList<Set<List<Integer>>> movesTaken) {
    	MCTNode currNode = startNode;
    	int depth = 0;
    	this.numRollouts ++;
    	List<Move> selectedMove = null;
    	Set<List<Move>> allMoves = null;

    	while(!currNode.isTerminal() && depth < ROLLOUT_EVAL_DEPTH) {
    		currNode.expandChildren();
			selectedMove = randomMove(currNode);
			allMoves = currNode.getChildren().keySet();

    		List<List<Integer>> convertedMove = this.sMap.convertMoveToList(selectedMove);
			for(int i=0;i<convertedMove.size();i++) {
				movesTaken.get(i).add(convertedMove.get(i));
			}
    		currNode = currNode.getExpandedChild(selectedMove, this.existingNodes, SAVE_MCT_TO_FILE);
    		statesOnPath.add(currNode.getStateSet());
    		pathInOrder.add(currNode);
    		depth++;
    	}
    	if(!currNode.isTerminal() && depth >= ROLLOUT_EVAL_DEPTH) {
    		List<Double> heurRewards = new ArrayList<Double>();
    		currNode.expandChildren();
    		for(int i=0;i<this.allRoles.size();i++) {
    			double heur = this.calcHeuristicValue(selectedMove.get(i), currNode, i, allMoves, false);
    			heurRewards.add(heur);
    		}
//    		System.out.println("H: " + heurRewards);
    		currNode.setHeuristicGoals(heurRewards);
    	}

    	if(this.numRollouts % 10 == 0) {
    		System.out.println(USE_PLAY_TRANSFER + " " + USE_SELECTION_TRANSFER + " " + USE_ROLLOUT_TRANSFER + " " + MCT_READ_DIR + " " + this.getRole() + " " + this.numRollouts + " rollouts. " + (System.currentTimeMillis() - this.startTime) + " ms.");
    	}

    	return currNode;
    }


    //Perform a rollout. If Rollout Transfer (R) is enabled, then influence rollouts as described in the "Knowledge Transfer" subsection
    //movesTaken will be altered by the addition of moves taken during the rollout
    private MCTNode rollout (MCTNode startNode, Set<Set<List<Integer>>> statesOnPath, ArrayList<MCTNode> pathInOrder, ArrayList<Set<List<Integer>>> movesTaken) {
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
    		List<List<Integer>> convertedMove = this.sMap.convertMoveToList(selectedMove);
			for(int i=0;i<convertedMove.size();i++) {
				movesTaken.get(i).add(convertedMove.get(i));
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


    private Set<SymbolCountKey> trimUnchangingSyms() {
    	Set<SymbolCountKey> resultList = new HashSet<SymbolCountKey>();
    	for(int depth : this.uniqueSymOccs.keySet()) {
    		Map<SymbolCountKey, Set<Integer>> currMap = this.uniqueSymOccs.get(depth);
    		for(SymbolCountKey key : currMap.keySet()) {
    			if(currMap.get(key).size() > 1) {
    				resultList.add(key);
    			}
    		}
    	}
    	return resultList;
    }


    private void earlyBackprop(List<Double> reward, ArrayList<MCTNode> pathInOrder) {
    	MCTNode currNode = null;

    	for(int i=0;i<pathInOrder.size();i++) {
    		int index = pathInOrder.size() - 1 - i;
    		currNode = pathInOrder.get(index);
    		for(int j=0;j<reward.size();j++) {
    			currNode.setTotalReward(j, currNode.getTotalReward().get(j) + Math.pow(DISCOUNT_FACTOR, i)*reward.get(j));
    		}
    		currNode.setNumVisits(currNode.getNumVisits() + 1);
    	}
    }

    // Do MCTS backpropagation
    private void backprop (List<Double> reward, ArrayList<MCTNode> pathInOrder, MCTNode terminalNode) {
    	MCTNode currNode = null;
    	Map<SymbolCountKey, SymbolCountGameData> gameData = new HashMap<SymbolCountKey, SymbolCountGameData>();
    	MobilityData mobData = new MobilityData();
    	List<Integer> finalReward = terminalNode.getGoals();
    	boolean terminalStateSeen = this.seenTerminalStates.contains(terminalNode.getStateSet());
    	List<Boolean> terminalWin = new ArrayList<Boolean>();
    	List<Boolean> terminalLoss = new ArrayList<Boolean>();
    	int numPlayers = finalReward.size();
    	mobData.finalReward = finalReward;
    	for(int goal : finalReward) {
    		mobData.totalMobPerPlayer.add(0f);
    		mobData.numEntriesPerPlayer.add(0);
    		if(goal >= WIN_THRESH) {
    			terminalWin.add(true);
    		} else {
    			terminalWin.add(false);
    		}
    		if(goal <= LOSE_THRESH) {
    			terminalLoss.add(true);
    		} else {
    			terminalLoss.add(false);
    		}
    	}

    	for(int i=0;i<pathInOrder.size();i++) {
    		int index = pathInOrder.size() - 1 - i;
    		currNode = pathInOrder.get(index);
    		int turnIndex = currNode.getWhoseTurnAssume2P();
    		for(int j=0;j<reward.size();j++) {
    			currNode.setTotalReward(j, currNode.getTotalReward().get(j) + Math.pow(DISCOUNT_FACTOR, i)*reward.get(j));
    		}
    		currNode.setNumVisits(currNode.getNumVisits() + 1);

    		if(this.recordSymOccs && !terminalStateSeen) {
    			updateSymbolOccTrackers(gameData, currNode);
//    			if(currNode.isTerminal()) {
//    				finalReward = currNode.getGoals();
//    			}
    		}

    		if(this.recordMobility && !terminalStateSeen) {
    			if(!currNode.isTerminal() && currNode.getDepth() > 0) {
    				int mobValue = currNode.getMobility2P();
    				mobData.totalMobPerPlayer.set(turnIndex, mobData.totalMobPerPlayer.get(turnIndex) + mobValue);
    				mobData.numEntriesPerPlayer.set(turnIndex, mobData.numEntriesPerPlayer.get(turnIndex) + 1);
    				if(mobValue > this.maxMobility.get(turnIndex)) {
    					this.maxMobility.set(turnIndex, mobValue);
    				}
    				if(mobValue < this.minMobility.get(turnIndex)) {
    					this.minMobility.set(turnIndex, mobValue);
    				}
    			}
    		}

    		if(this.recordNearestWin) {
    			for(int j=0;j<numPlayers;j++) {
    				int dist = terminalNode.getDepth() - currNode.getDepth();
    				if(terminalWin.get(j)) {
    					if(dist < currNode.getNearestWin().get(j) || currNode.getNearestWin().get(j) == -1) {
    						currNode.setNearestWin(dist, j);
    					}
    				}
    				if(terminalLoss.get(j)) {
    					if(dist < currNode.getNearestLoss().get(j) || currNode.getNearestLoss().get(j) == -1) {
    						currNode.setNearestLoss(dist, j);
    					}
    				}
    			}
    		}
    	}

    	if(this.recordSymOccs && !terminalStateSeen) {
	    	//update game data with states that have already been played (not just simulated)
	    	for(SymbolCountKey playedKey : this.combinedPlayedCounts.keySet()) {
	    		if(!gameData.containsKey(playedKey)) {
	    			gameData.put(playedKey, new SymbolCountGameData());
	    		}
	    		SymbolCountGameData playedData = this.combinedPlayedCounts.get(playedKey);
	    		SymbolCountGameData currData = gameData.get(playedKey);
	    		currData.totalOcc += playedData.totalOcc;
	    		currData.numSteps += playedData.numSteps;
//	    		currData.maxOcc = Math.max(currData.maxOcc, playedData.maxOcc);
	    	}

	    	FullRolloutData finalData = new FullRolloutData();
	    	finalData.symCountData = gameData;
	    	finalData.finalReward = finalReward;
	    	this.symCountData.add(finalData);
    	}

    	if(this.recordMobility && !terminalStateSeen) {
    		for(int i=0;i<mobData.totalMobPerPlayer.size();i++) {
    			mobData.totalMobPerPlayer.set(i, mobData.totalMobPerPlayer.get(i) + this.playedMobility.totalMobPerPlayer.get(i));
    			mobData.numEntriesPerPlayer.set(i, mobData.numEntriesPerPlayer.get(i) + this.playedMobility.numEntriesPerPlayer.get(i));
    		}
    		this.mobilityData.add(mobData);
    	}

//    	if(this.recordNearestWin) {
//
//    	}
    }


    public Map<SymbolCountKey, Integer> getSymOccFromState(Set<List<Integer>> stateSet) {
    	Map<SymbolCountKey, Integer> symbolOccs;
    	if(this.symCountCache.containsKey(stateSet)) {
			symbolOccs = this.symCountCache.get(stateSet);
		} else {
			symbolOccs = new HashMap<SymbolCountKey, Integer>();
			//for each symbol at each position in the state, count the total number of occurrences
			for(List<Integer> fact : stateSet) {
				int parentValue = -1;
				for(int posn=0;posn<fact.size();posn++) {
					int symValue = fact.get(posn);
					SymbolCountKey currKey = new SymbolCountKey(symValue, parentValue, posn);
					if(!symbolOccs.containsKey(currKey)) {
						symbolOccs.put(currKey, 0);
					}
					symbolOccs.put(currKey, symbolOccs.get(currKey) + 1);

					if(posn == 0) {
						parentValue = symValue;
					}
				}
			}
			this.symCountCache.put(stateSet, symbolOccs);
		}
    	return symbolOccs;
    }


    public void updateSymbolOccTrackers(Map<SymbolCountKey, SymbolCountGameData> gameData, MCTNode currNode) {
		Set<List<Integer>> stateSet = currNode.getStateSet();
		Map<SymbolCountKey, Integer> symbolOccs = getSymOccFromState(stateSet);
//		System.out.println(targetStateToString(currNode.getStateSet()));

		for(SymbolCountKey key : symbolOccs.keySet()) {
			//Add any unique occurrence numbers to the global tracker
			if(!this.uniqueSymOccs.containsKey(currNode.getDepth())) {
				this.uniqueSymOccs.put(currNode.getDepth(), new HashMap<SymbolCountKey, Set<Integer>>());
			}
			Map<SymbolCountKey, Set<Integer>> uniquesAtDepth = this.uniqueSymOccs.get(currNode.getDepth());
			if(!uniquesAtDepth.containsKey(key)) {
				uniquesAtDepth.put(key, new HashSet<Integer>());
			}
			Set<Integer> uniques = uniquesAtDepth.get(key);
			uniques.add(symbolOccs.get(key));
		}

		updateSymbolCounts(gameData, symbolOccs);
    }


    public void updateSymbolCounts(Map<SymbolCountKey, SymbolCountGameData> gameData, Map<SymbolCountKey, Integer> symbolOccs) {
    	for(SymbolCountKey key : symbolOccs.keySet()) {
			if(!gameData.containsKey(key)) {
				gameData.put(key, new SymbolCountGameData());
			}
			SymbolCountGameData currData = gameData.get(key);

			currData.totalOcc += symbolOccs.get(key);
			currData.numSteps += 1;
			if(!maxSCVals.containsKey(key) || symbolOccs.get(key) > this.maxSCVals.get(key)) {
				this.maxSCVals.put(key, symbolOccs.get(key));
			}
			if(!minSCVals.containsKey(key) || symbolOccs.get(key) < this.minSCVals.get(key)) {
				this.minSCVals.put(key, symbolOccs.get(key));
			}
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


    	if(SAVE_EXPERIMENT) {

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


        //if heuristics were generated during initialization, save them
        if(INITIAL_HEUR_RECORD) {
        	String savePath = EXPERIMENT_SAVE_DIR + "/heur_" + this.getRole() + "_" + historyFileName;
        	HeuristicDataLibrary.writeHeuristicFile(scRegression, mobRegression, nearestWinRegression, historyData, genHistoryData, savePath);
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

    public String targetStateToString(Set<List<Integer>> state) {
		String outStr = "< ";
		for(List<Integer> fact : state) {
			outStr += "[ ";
			for(int word : fact) {
				outStr += this.sMap.getTargetName(word) + " ";
			}
			outStr += "] ";
		}
		outStr += ">";
		return outStr;
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
    	if(SAVE_EXPERIMENT || INITIAL_HEUR_RECORD) {
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
		this.uniqueSymOccs = new HashMap<Integer, Map<SymbolCountKey, Set<Integer>>>();
		this.symCountData = new LinkedList<FullRolloutData>();
		this.maxSCVals = new HashMap<SymbolCountKey, Integer>();
		this.minSCVals = new HashMap<SymbolCountKey, Integer>();
		this.playedStates = new HashMap<Integer, Set<List<Integer>>>();
		this.combinedPlayedCounts = new HashMap<SymbolCountKey, SymbolCountGameData>();
		this.symCountCache = new HashMap<Set<List<Integer>>, Map<SymbolCountKey, Integer>>();
		this.usefulSymKeys = null;
		this.seenTerminalStates = new HashSet<Set<List<Integer>>>();
		this.mobilityData = new LinkedList<MobilityData>();
		this.maxMobility = new ArrayList<Integer>();
		this.minMobility = new ArrayList<Integer>();
		this.playedMobility = new MobilityData();
		this.historyData = new ArrayList<Map<List<Integer>, HistoryData>>();
		this.genHistoryData = new ArrayList<Map<Integer, HistoryData>>();
		this.playedMoves = new ArrayList<Set<List<Integer>>>();
		this.compiledSCData = new HashMap<SymbolCountKey, List<SymbolCountHeurData>>();
		this.compiledMobData = new ArrayList<MobilityHeurData>();
		this.scRegression = null;
		this.mobRegression = null;
		this.nearestWinRegression = null;
		this.loadedSCRegression = null;
		this.loadedMobRegression = null;
		this.loadedNWRegression = null;

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
		this.uniqueSymOccs = new HashMap<Integer, Map<SymbolCountKey, Set<Integer>>>();
		this.symCountData = new LinkedList<FullRolloutData>();
		this.maxSCVals = new HashMap<SymbolCountKey, Integer>();
		this.minSCVals = new HashMap<SymbolCountKey, Integer>();
		this.playedStates = new HashMap<Integer, Set<List<Integer>>>();
		this.combinedPlayedCounts = new HashMap<SymbolCountKey, SymbolCountGameData>();
		this.symCountCache = new HashMap<Set<List<Integer>>, Map<SymbolCountKey, Integer>>();
		this.usefulSymKeys = null;
		this.seenTerminalStates = new HashSet<Set<List<Integer>>>();
		this.mobilityData = new LinkedList<MobilityData>();
		this.maxMobility = new ArrayList<Integer>();
		this.minMobility = new ArrayList<Integer>();
		this.playedMobility = new MobilityData();
		this.historyData = new ArrayList<Map<List<Integer>, HistoryData>>();
		this.genHistoryData = new ArrayList<Map<Integer, HistoryData>>();
		this.playedMoves = new ArrayList<Set<List<Integer>>>();
		this.compiledSCData = new HashMap<SymbolCountKey, List<SymbolCountHeurData>>();
		this.compiledMobData = new ArrayList<MobilityHeurData>();
		this.scRegression = null;
		this.mobRegression = null;
		this.nearestWinRegression = null;
		this.loadedSCRegression = null;
		this.loadedMobRegression = null;
		this.loadedNWRegression = null;

    }


    @Override
    public void preview(Game g, long timeout) throws GamePreviewException {
    	System.out.println("Preview was called");
    }


    public void loadHeuristicFile() {
    	String inFileName = MCT_READ_DIR + "/" + HEUR_FILE_NAME;
    	Scanner s = null;
    	this.loadedSCRegression = new ArrayList<LoadedSCRegContainer>();
    	this.loadedMobRegression = new ArrayList<RegressionRecord>();
    	this.loadedNWRegression = new ArrayList<RegressionRecord>();
    	this.genHistoryData = new ArrayList<Map<Integer, HistoryData>>();
    	this.historyData = new ArrayList<Map<List<Integer>, HistoryData>>();

        try {
            s = new Scanner(new BufferedReader(new FileReader(inFileName), RuleGraphRecord.BUFFER_SIZE));
            int lineNumber = 0;
            int numPlayers = 0;
            int[] lineNumberBound = new int[5];
            lineNumberBound[0] = 1; //unique line(s) at top of file

            while (s.hasNext()) {
                String line = s.nextLine();
                if(line.length() > 0) {
                	StringTokenizer tok = new StringTokenizer(line);

                	if(lineNumber < lineNumberBound[0]) { //unique line(s) at top of file
                		numPlayers = Integer.parseInt(tok.nextToken());
                		lineNumberBound[1] = lineNumberBound[0] + numPlayers;
                        lineNumberBound[2] = lineNumberBound[1] + numPlayers;
                        lineNumberBound[3] = lineNumberBound[2] + numPlayers;
                        lineNumberBound[4] = lineNumberBound[3] + numPlayers;
//                		for(int i=0;i<numPlayers;i++) {
//
//                		}

                	} else if(lineNumber < lineNumberBound[1]) { //symbol count data
//                		int roleIndex = lineNumber - lineNumberBound[0];
                		LoadedSCRegContainer newSC = new LoadedSCRegContainer();
                		if(tok.hasMoreTokens()) {
                			double avgR = Double.parseDouble(tok.nextToken());
                			newSC.avgR = avgR;
                			while(tok.hasMoreTokens()) {
                				int mainSym = this.sMap.mapSourceIDToTarget(Integer.parseInt(tok.nextToken()));
                				int parentSym = this.sMap.mapSourceIDToTarget(Integer.parseInt(tok.nextToken()));
                				int posn = Integer.parseInt(tok.nextToken());
                				double slope = Double.parseDouble(tok.nextToken());
                				double intercept = Double.parseDouble(tok.nextToken());
                				double numPoints = Double.parseDouble(tok.nextToken());
                				double r = Double.parseDouble(tok.nextToken());
                				tok.nextToken(); //throw away *
                				if(mainSym != -1 && parentSym != -1) {
	                				SymbolCountKey currKey = new SymbolCountKey(mainSym, parentSym, posn);
	                				RegressionRecord currReg = new RegressionRecord(slope, intercept, numPoints, r);
	                				newSC.regMap.put(currKey, currReg);
                				}
                			}
                		}
                		this.loadedSCRegression.add(newSC);

                	} else if(lineNumber < lineNumberBound[2]) { //mobility data
                		if(tok.hasMoreTokens()) {
                			double slope = Double.parseDouble(tok.nextToken());
            				double intercept = Double.parseDouble(tok.nextToken());
            				double numPoints = Double.parseDouble(tok.nextToken());
            				double r = Double.parseDouble(tok.nextToken());
            				RegressionRecord currReg = new RegressionRecord(slope, intercept, numPoints, r);
            				this.loadedMobRegression.add(currReg);
                		}
                	} else if(lineNumber < lineNumberBound[3]) { //nearest win data
                		if(tok.hasMoreTokens()) {
                			double slope = Double.parseDouble(tok.nextToken());
            				double intercept = Double.parseDouble(tok.nextToken());
            				double numPoints = Double.parseDouble(tok.nextToken());
            				double r = Double.parseDouble(tok.nextToken());
            				RegressionRecord currReg = new RegressionRecord(slope, intercept, numPoints, r);
            				this.loadedNWRegression.add(currReg);
                		}
                	} else if(lineNumber < lineNumberBound[4]) { //general history data
                		Map<Integer, HistoryData> newGenHist = new HashMap<Integer, HistoryData>();
                		while(tok.hasMoreTokens()) {
                			int id = this.sMap.mapSourceIDToTarget(Integer.parseInt(tok.nextToken()));
                			int totalReward = Integer.parseInt(tok.nextToken());
                			int numWins = Integer.parseInt(tok.nextToken());
                			int numLosses = Integer.parseInt(tok.nextToken());
                			int numOther = Integer.parseInt(tok.nextToken());
                			int numOccs = Integer.parseInt(tok.nextToken());
                			tok.nextToken(); //throw away *
                			if(id != -1) {
	                			HistoryData currData = new HistoryData();
	                			currData.totalReward = totalReward;
	                			currData.numWins = numWins;
	                			currData.numLosses = numLosses;
	                			currData.numOther = numOther;
	                			currData.numOccs = numOccs;
	                			newGenHist.put(id, currData);
                			}
                		}
                		this.genHistoryData.add(newGenHist);
                	} else { //specific history data
                		Map<List<Integer>, HistoryData> newSpecHist = new HashMap<List<Integer>, HistoryData>();
                		while(tok.hasMoreTokens()) {
                			int moveSize = Integer.parseInt(tok.nextToken());
                			List<Integer> moveList = new ArrayList<Integer>();
                			boolean mapSuccessful = true;
                			for(int i=0;i<moveSize;i++) {
                				int currMoveVal = this.sMap.mapSourceIDToTarget(Integer.parseInt(tok.nextToken()));
                				moveList.add(currMoveVal);
                				if(currMoveVal == -1) {
                					mapSuccessful = false;
                				}
                			}
                			int totalReward = Integer.parseInt(tok.nextToken());
                			int numWins = Integer.parseInt(tok.nextToken());
                			int numLosses = Integer.parseInt(tok.nextToken());
                			int numOther = Integer.parseInt(tok.nextToken());
                			int numOccs = Integer.parseInt(tok.nextToken());
                			tok.nextToken(); //throw away *
                			if(mapSuccessful) {
	                			HistoryData currData = new HistoryData();
	                			currData.totalReward = totalReward;
	                			currData.numWins = numWins;
	                			currData.numLosses = numLosses;
	                			currData.numOther = numOther;
	                			currData.numOccs = numOccs;
	                			newSpecHist.put(moveList, currData);
                			}
                		}
                		this.historyData.add(newSpecHist);
                	}
                }
                lineNumber++;
            }
            this.heuristicsReady = true;
        } catch (FileNotFoundException e) {
            System.out.println("ERROR loading states from file");
            System.out.println(e);
        } finally {
            if (s != null) {
                s.close();
            }
        }
    }


    public static class SymbolCountKey {
    	public int mainSym;
    	public int parentSym;
    	public int posn;

		public SymbolCountKey(int mainSym, int parentSym, int posn) {
			this.mainSym = mainSym;
			this.parentSym = parentSym;
			this.posn = posn;
		}

		@Override
		public int hashCode() {
			final int prime = 31;
			int result = 1;
			result = prime * result + mainSym;
			result = prime * result + parentSym;
			result = prime * result + posn;
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
			SymbolCountKey other = (SymbolCountKey) obj;
			if (mainSym != other.mainSym)
				return false;
			if (parentSym != other.parentSym)
				return false;
			if (posn != other.posn)
				return false;
			return true;
		}

		public String toNameString(StateMapping mapping) {
			String outStr = "(";
			if(parentSym != -1) {
				outStr += mapping.getTargetName(parentSym) + " ";
			} else {
				outStr += "-1 ";
			}
			outStr += mapping.getTargetName(mainSym) + " ";
			outStr += posn + ")";
			return outStr;
		}

		@Override
		public String toString() {
			String outStr = "(" + parentSym + " " + mainSym + " " + posn + ")";
			return outStr;
		}
    }

    public static class SymbolCountGameData {
    	public int totalOcc = 0;
    	public int numSteps = 0;

    	@Override
		public String toString() {
    		return totalOcc + " " + numSteps;
    	}
    }

    public static class FullRolloutData {
    	public Map<SymbolCountKey, SymbolCountGameData> symCountData = new HashMap<SymbolCountKey, SymbolCountGameData>();
    	public List<Integer> finalReward = Arrays.asList(-1, -1);

    	@Override
		public String toString() {
    		return finalReward.toString() + ", " + symCountData.toString();
    	}
    }

    public static class MobilityData {
    	public List<Float> totalMobPerPlayer = new ArrayList<Float>();
    	public List<Integer> numEntriesPerPlayer = new ArrayList<Integer>();
    	public List<Integer> finalReward = Arrays.asList(-1, -1);

    	@Override
		public String toString() {
    		return totalMobPerPlayer + ", " + numEntriesPerPlayer + ", " + finalReward;
    	}
    }

    public static class HistoryData {
    	public int totalReward = 0;
    	public int numWins = 0;
    	public int numLosses = 0;
    	public int numOther = 0;
    	public int numOccs = 0;

    	@Override
		public String toString() {
    		return totalReward + " " + numWins + " " + numLosses + " " + numOther + " " + numOccs;
    	}
    }

    public static class SymbolCountHeurData {
    	public float totalWinValue = 0;
    	public float totalLossValue = 0;
    	public float totalOtherValue = 0;
    	public int numWins = 0;
    	public int numLosses = 0;
    	public int numOther = 0;
    	public float maxValue = 0;
    	private float weight = -1f;

    	public float getWeight() {
    		if (this.weight < 0) {
    			this.calcWeight();
    		}
    		return this.weight;
    	}

    	public void calcWeight() {
    		this.weight = 0f;
    		if(this.numWins > 0 && this.numLosses > 0 && this.maxValue > 0) {
				float winAvg = this.totalWinValue / this.numWins;
				float lossAvg = this.totalLossValue / this.numLosses;
				this.weight = Math.abs(winAvg - lossAvg) / this.maxValue;
			}
    	}

    	@Override
		public String toString() {
    		String outStr = "";
    		if(numWins > 0) {
    			outStr += "win avg: " + totalWinValue/numWins + ", ";
    		} else {
    			outStr += "No win data. ";
    		}
    		if(numLosses > 0) {
    			outStr += "loss avg: " + totalLossValue/numLosses + ", ";
    		} else {
    			outStr += "No loss data. ";
    		}
    		if(numOther > 0) {
    			outStr += "other avg: " + totalOtherValue/numOther + ", ";
    		} else {
    			outStr += "No other data. ";
    		}
    		outStr += "# wins: " + numWins + " ";
    		outStr += "# losses: " + numLosses + " ";
    		outStr += "# other: " + numOther + " ";
    		outStr += "max: " + maxValue;
    		return outStr;
    	}
    }

    public static class MobilityHeurData {
    	public float totalWinValue = 0;
    	public float totalLossValue = 0;
    	public float totalOtherValue = 0;
    	public int numWins = 0;
    	public int numLosses = 0;
    	public int numOther = 0;
    	public float maxValue = 0;
    	public float minValue = 0;
    }

    public static class SCRegressionContainer {
    	public Map<SymbolCountKey, SimpleRegression> regMap = new HashMap<SymbolCountKey, SimpleRegression>();
    	public Map<SymbolCountKey, Integer> occMap = new HashMap<SymbolCountKey, Integer>();
    	public double avgR = 0;
//    	public double totalR = 0;
    	public int totalOcc = 0;

    	public PredictionPackage combinedPredict(Map<SymbolCountKey, Integer> symCounts) {
    		double result = 0;
    		double totalWeight = 0;
    		double maxR = 0;
    		for(SymbolCountKey key : symCounts.keySet()) {
    			if(this.regMap.containsKey(key)) {
    				double currPredict = clampRewardVal(this.regMap.get(key).predict(symCounts.get(key)));
    				double currR = Math.abs(this.regMap.get(key).getR());
    				if(currR > maxR) {
    					maxR = currR;
    				}
    				result += currPredict * currR;
    				totalWeight += currR;
    			}
    		}
    		result = result / totalWeight;
    		return new PredictionPackage(result, maxR);
    	}

		public String toNameString(StateMapping mapping) {
    		String result = "";
    		for(SymbolCountKey key : regMap.keySet()) {
    			result += key.toNameString(mapping) + ": R=" + regMap.get(key).getR() + " ";
    		}
    		return result;
    	}
    }

    public static class LoadedSCRegContainer {
    	public Map<SymbolCountKey, RegressionRecord> regMap = new HashMap<SymbolCountKey, RegressionRecord>();
    	public double avgR = 0;

    	public PredictionPackage combinedPredict(Map<SymbolCountKey, Integer> symCounts) {
    		double result = 0;
    		double totalWeight = 0;
    		double maxR = 0;
    		for(SymbolCountKey key : symCounts.keySet()) {
    			if(this.regMap.containsKey(key)) {
    				double currPredict = clampRewardVal(this.regMap.get(key).predict(symCounts.get(key)));
    				double currR = Math.abs(this.regMap.get(key).getR());
    				if(currR > maxR) {
    					maxR = currR;
    				}
    				result += currPredict * currR;
    				totalWeight += currR;
    			}
    		}
    		result = result / totalWeight;
    		return new PredictionPackage(result, maxR);
    	}

		public String toNameString(StateMapping mapping) {
    		String result = "";
    		for(SymbolCountKey key : regMap.keySet()) {
    			result += key.toNameString(mapping) + ": R=" + regMap.get(key).getR() + " ";
    		}
    		return result;
    	}
    }

    public static class PredictionPackage {
    	public double prediction;
    	public double maxR;

    	PredictionPackage(double prediction, double maxR) {
    		this.prediction = prediction;
    		this.maxR = maxR;
    	}
    }

//    public static class GenHistoryRegressionContainer {
//    	public Map<Integer, SimpleRegression> regMap = new HashMap<Integer, SimpleRegression>();
////    	public Map<Integer, Integer> occMap = new HashMap<Integer, Integer>();
//    	public double avgR = 0;
////    	public int totalOcc = 0;
//
//    	public PredictionPackage combinedPredict(int moveID) {
//    		double result = 0;
//    		double maxR = 0;
//    		double prediction = 0;
//    		if(this.regMap.containsKey(moveID)) {
//    			prediction = this.regMap.get(moveID).predict(1);
//				if(prediction > MAX_REWARD_VALUE) {
//					prediction = MAX_REWARD_VALUE;
//				} else if(prediction < MIN_REWARD_VALUE) {
//					prediction = MIN_REWARD_VALUE;
//				}
//				maxR = this.regMap.get(moveID).getR();
//    		}
//    		return new PredictionPackage(result, maxR);
//    	}
//    }
//
//    public static class SpecHistoryRegressionContainer {
//    	public Map<List<Integer>, SimpleRegression> regMap = new HashMap<List<Integer>, SimpleRegression>();
////    	public Map<List<Integer>, Integer> occMap = new HashMap<List<Integer>, Integer>();
//    	public double avgR = 0;
//    	public int totalOcc = 0;
//
//    	public PredictionPackage combinedPredict(List<Integer> moveList) {
//    		double result = 0;
//    		double maxR = 0;
//    		double prediction = 0;
//    		if(this.regMap.containsKey(moveList)) {
//    			prediction = this.regMap.get(moveList).predict(1);
//				if(prediction > MAX_REWARD_VALUE) {
//					prediction = MAX_REWARD_VALUE;
//				} else if(prediction < MIN_REWARD_VALUE) {
//					prediction = MIN_REWARD_VALUE;
//				}
//				maxR = this.regMap.get(moveList).getR();
//    		}
//    		return new PredictionPackage(result, maxR);
//    	}
//    }
}