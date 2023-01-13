package org.ggp.base.player.gamer.statemachine.sample;

import java.io.BufferedWriter;
import java.io.File;
import java.io.FileWriter;
import java.io.IOException;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Random;

import org.apache.commons.math4.legacy.stat.regression.SimpleRegression;
import org.ggp.base.player.gamer.statemachine.sample.TestGamer.HistoryData;
import org.ggp.base.player.gamer.statemachine.sample.TestGamer.SCRegressionContainer;
import org.ggp.base.player.gamer.statemachine.sample.TestGamer.SymbolCountKey;

public class HeuristicDataLibrary {

	public static String SAVE_FILE_NAME = "heuristic_data.txt";
	public static String MCT_READ_DIR = "MCTs/reversi";
	public static String HEUR_SAVE_DIR = "MCTs/reversi";
	public static int MAX_FILES = 1000;  //Number of MCT files to combine
	public static Random rand = new Random(3769460674928934938L);


	public static void main(String[] args) {
//		LinkedList<ReducedMCTree> trees = new LinkedList<ReducedMCTree>();

    	File folder = new File(MCT_READ_DIR);
    	File[] listOfFiles = folder.listFiles();
    	List<String> fileNames = new LinkedList<String>();
    	int totalNodes = 0;

    	for (File file : listOfFiles) {
//    		System.out.println(file.getName());
    	    if (file.isFile()) {
    	    	String name = file.getName();
    	    	if(name.length() >= 5 && Character.isDigit(name.charAt(4))) {
    	    		fileNames.add(name);
    	    	}
    	    }
    	}

    	List<SCRegressionContainer> scRegression = new ArrayList<SCRegressionContainer>();
    	List<SimpleRegression> mobRegression = new ArrayList<SimpleRegression>();
    	List<SimpleRegression> nearestWinRegression = new ArrayList<SimpleRegression>();
    	List<Map<List<Integer>, HistoryData>> historyData = new ArrayList<Map<List<Integer>, HistoryData>>();
    	List<Map<Integer, HistoryData>> genHistoryData = new ArrayList<Map<Integer, HistoryData>>();
    	int numPlayers = 0;

    	int fileNum = 0;
    	for(String name : fileNames) {
    		if(fileNum < MAX_FILES) {
	    		ReducedMCTree currTree = new ReducedMCTree();
	    		System.out.println("Reading file # " + fileNum);
	    		currTree.loadStatesFromFile(MCT_READ_DIR + "/" + name);
//	    		trees.add(currTree);

	    		if(fileNum == 0) {
		    		numPlayers = currTree.numPlayers;
		        	for(int i=0; i<numPlayers; i++) {
		        		scRegression.add(new SCRegressionContainer());
		        		mobRegression.add(new SimpleRegression());
		        		nearestWinRegression.add(new SimpleRegression());
		        		historyData.add(new HashMap<List<Integer>, HistoryData>());
		        		genHistoryData.add(new HashMap<Integer, HistoryData>());
		        	}
	    		}

	        	for(int i=0;i<numPlayers;i++) {
	    			TestGamer.doSCRegression(currTree.symCountData, null, i, scRegression.get(i));
	    			TestGamer.doMobilityRegression(currTree.mobilityData, i, mobRegression.get(i));
	    			TestGamer.doNearestWinRegression(currTree.getStates(), i, nearestWinRegression.get(i));
	    			Map<Integer, HistoryData> currGenHistory = currTree.genHistoryData.get(i);
	    			for(int key : currGenHistory.keySet()) {
	    				if(!genHistoryData.get(i).containsKey(key)) {
	    					genHistoryData.get(i).put(key, new HistoryData());
	    				}
	    				HistoryData histFrom = currGenHistory.get(key);
	    				HistoryData histTo = genHistoryData.get(i).get(key);
	    				histTo.totalReward += histFrom.totalReward;
	    				histTo.numWins += histFrom.numWins;
	    				histTo.numLosses += histFrom.numLosses;
	    				histTo.numOther += histFrom.numOther;
	    				histTo.numOccs += histFrom.numOccs;
	    			}
	    			Map<List<Integer>, HistoryData> currSpecHistory = currTree.historyData.get(i);
	    			for(List<Integer> key : currSpecHistory.keySet()) {
	    				if(!historyData.get(i).containsKey(key)) {
	    					historyData.get(i).put(key, new HistoryData());
	    				}
	    				HistoryData histFrom = currSpecHistory.get(key);
	    				HistoryData histTo = historyData.get(i).get(key);
	    				histTo.totalReward += histFrom.totalReward;
	    				histTo.numWins += histFrom.numWins;
	    				histTo.numLosses += histFrom.numLosses;
	    				histTo.numOther += histFrom.numOther;
	    				histTo.numOccs += histFrom.numOccs;
	    			}
	    		}
	    		System.out.println("***************** " + fileNum + " *****************");
	    		System.out.println(scRegression.get(0).avgR + " " + scRegression.get(0).totalOcc);
	    		System.out.println(mobRegression.get(0).getR() + " " + mobRegression.get(0).getN());
	    		System.out.println(nearestWinRegression.get(0).getR() + " " + nearestWinRegression.get(0).getN());
	    		System.out.println(genHistoryData.get(0));
	    		System.out.println(historyData.get(0));
	    		fileNum++;
    		} else {
    			break;
    		}
    	}

    	System.out.println("Found " + (fileNum+1) + " MCT files.");


//    	int treeNum = 1;
//    	for(ReducedMCTree currTree : trees) {
//    		System.out.println("***************** " + treeNum + " *****************");
//    		System.out.println(currTree.maxSCVals);
//    		System.out.println(currTree.minSCVals);
//    		System.out.println(currTree.symCountData);
//    		System.out.println(currTree.mobilityData);
//    		System.out.println(currTree.shortKeyHistoryData);
//    		System.out.println(currTree.historyData);
//    		System.out.println(currTree.genHistoryData);
//    		treeNum++;
//    	}


    	//Prepare data for writing to file
    	String headerStr = "" + numPlayers;
    	String[] scStr = new String[numPlayers];
    	String[] mobStr = new String[numPlayers];
    	String[] nwStr = new String[numPlayers];
    	String[] genHistStr = new String[numPlayers];
    	String[] specHistStr = new String[numPlayers];
    	for(int i=0;i<numPlayers;i++) {
    		scStr[i] = "";
    		mobStr[i] = "";
    		nwStr[i] = "";
    		genHistStr[i] = "";
    		specHistStr[i] = "";

    		scStr[i] += scRegression.get(i).avgR + " ";
    		for(SymbolCountKey key : scRegression.get(i).regMap.keySet()) {
    			SimpleRegression reg = scRegression.get(i).regMap.get(key);
    			scStr[i] += key.mainSym + " " + key.parentSym + " " + key.posn + " " + reg.getSlope() + " " + reg.getIntercept() + " " + reg.getN() + " " + reg.getR() + " * ";
    		}

    		mobStr[i] += mobRegression.get(i).getSlope() + " " + mobRegression.get(i).getIntercept() + " " + mobRegression.get(i).getN() + " " + mobRegression.get(i).getR();

    		nwStr[i] += nearestWinRegression.get(i).getSlope() + " " + nearestWinRegression.get(i).getIntercept() + " " + nearestWinRegression.get(i).getN() + " " + nearestWinRegression.get(i).getR();

    		for(int key : genHistoryData.get(i).keySet()) {
    			HistoryData currData = genHistoryData.get(i).get(key);
    			genHistStr[i] += key + " " + currData.totalReward + " " + currData.numWins + " " + currData.numLosses + " " + currData.numOther + " " + currData.numOccs + " * ";
    		}
    		for(List<Integer> key : historyData.get(i).keySet()) {
    			HistoryData currData = historyData.get(i).get(key);
    			specHistStr[i] += key.size() + " ";
    			for(int keyPiece : key) {
    				specHistStr[i] += keyPiece + " ";
    			}
    			specHistStr[i] += currData.totalReward + " " + currData.numWins + " " + currData.numLosses + " " + currData.numOther + " " + currData.numOccs + " * ";
    		}
    	}


		//Write data to file
		File file = new File(HEUR_SAVE_DIR + "/" + SAVE_FILE_NAME);
        FileWriter fr = null;
        BufferedWriter br = null;
        try{
            fr = new FileWriter(file);
            br = new BufferedWriter(fr, RuleGraphRecord.BUFFER_SIZE);
            br.write(headerStr + "\n");
            for(int i=0;i<numPlayers;i++) {
            	br.write(scStr[i] + "\n");
            }
            for(int i=0;i<numPlayers;i++) {
            	br.write(mobStr[i] + "\n");
            }
            for(int i=0;i<numPlayers;i++) {
            	br.write(nwStr[i] + "\n");
            }
            for(int i=0;i<numPlayers;i++) {
            	br.write(genHistStr[i] + "\n");
            }
            for(int i=0;i<numPlayers;i++) {
            	br.write(specHistStr[i] + "\n");
            }
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
}
