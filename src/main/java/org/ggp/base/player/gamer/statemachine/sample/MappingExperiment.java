package org.ggp.base.player.gamer.statemachine.sample;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;

import org.ggp.base.player.gamer.statemachine.sample.ContextEditDistance.CostPair;
import org.ggp.base.util.gdl.grammar.Gdl;

public class MappingExperiment {
	private List<Gdl> rules;
	long randomSeed;

	public MappingExperiment(List<Gdl> rules, long randomSeed) {
		this.rules = rules;
		this.randomSeed = randomSeed;
	}

	public void runTrialSuite(int numTrials, String mappingAlg, String recordFile, String testMode, int startParam, int endParam, int paramIncrease) {
		int currParam = startParam;
		ArrayList<Double> percentCorrect = new ArrayList<Double>();
		while(currParam <= endParam) {
			percentCorrect.add(runTrials(numTrials, mappingAlg, recordFile, testMode, currParam));
			currParam += paramIncrease;
		}
		String toPrint = "";
		int index = 0;
		for(int i=startParam;i<=endParam;i+=paramIncrease) {
			toPrint += String.format("(%d,%.2f)", i, percentCorrect.get(index));
			index++;
		}
		System.out.println(toPrint);
	}

	public double runTrials(int numTrials, String mappingAlg, String recordFile, String testMode, int param) {
		int trialNum = 0;
		long[] trialSeeds = MyUtil.genLongs(numTrials, this.randomSeed);
        ArrayList<Long> times = new ArrayList<Long>();
        ArrayList<Long> genTimes = new ArrayList<Long>();
        double[] distances = new double[numTrials];
        int[][] correctness = new int[6][numTrials];
        int[][] numCorrectness = new int[6][numTrials];
        ArrayList<String> numbers = genNumberStrings(300);
        numbers.addAll(genNumberStrings(300,"c"));
        numbers.addAll(genNumberStrings(100,"m"));
        HashSet<String> numberSet = new HashSet<String>(numbers);
        HashMap<String,String> numberMap = new HashMap<String,String>();
        for(String numStr : numbers) {
        	numberMap.put(numStr, numStr);
        }

        HashMap<String,String> handMappings = new HashMap<String,String>();
        HashSet<String> ignoreList = numberSet;

		while(trialNum < numTrials) {
//			System.out.println("Trial " + trialNum + "...");
			RuleGraph g = new RuleGraph(this.rules, null);
			long genStartTime = System.nanoTime();
			g.genRuleGraph();
			long genEndTime = System.nanoTime();
			genTimes.add(genEndTime - genStartTime);
			RuleGraphRecord rec = new RuleGraphRecord();
	    	rec.loadFromFile(recordFile, true);
	    	RuleGraphDestroyer destroyer = new RuleGraphDestroyer(g, trialSeeds[trialNum]);

	    	//graph destruction here
	    	if(testMode.equals("remove_occ")) {
	    		destroyer.removeNNonNumberOcc(param);
	    	} else if(testMode.equals("remove_any")) {
	    		destroyer.removeNNonTopLevel(param);
	    	} else if(testMode.equals("dup_occ")) {
	    		destroyer.duplicateNNonNumberOcc(param);
	    	} else if(testMode.equals("dup_any")) {
	    		destroyer.duplicateNNonTopLevel(param);
	    	}

	    	//Actual timed part
	    	long startTime = System.nanoTime();
	    	ContextEditDistance edit = new ContextEditDistance(g.getGraph(), rec.getGraph(), g.getTopLevelNonVarIds(), rec.getTopLevelNonVarIds(), null, null, null, null, trialSeeds[trialNum]);
	    	ArrayList<CostPair<RuleNode,RuleNode>> distList = edit.calcDistance(mappingAlg);
			long endTime = System.nanoTime();

			//finding total distance
			float totalDist = 0;
			int numDist = 0;
			for(CostPair<RuleNode,RuleNode> curr : distList) {
				if(curr.getFirst() != null && curr.getSecond() != null) {
					if(!numberSet.contains(curr.getFirst().getName()) && !numberSet.contains(curr.getSecond().getName())) {
						totalDist += curr.getCostVector()[0];
						numDist++;
//						System.out.println("** " + curr.getCostVector()[0]);
					}
				} else if(curr.getFirst() != null && !numberSet.contains(curr.getFirst().getName())) {
					totalDist += curr.getCostVector()[0];
					numDist++;
//					System.out.println("* " + curr.getCostVector()[0] + " " + curr.getFirst().getName());
				} else if(curr.getSecond() != null && !numberSet.contains(curr.getSecond().getName())) {
					totalDist += curr.getCostVector()[0];
					numDist++;
//					System.out.println("* " + curr.getCostVector()[0] + " " + curr.getSecond().getName());
				}
			}
			if(numDist > 0) {
				distances[trialNum] = totalDist / numDist;
			} else {
				System.out.println("ERROR: No distances between non-number symbols found while running trials");
			}

	        times.add(endTime - startTime);
	        int[] tempCorrectness = checkCorrectness(edit.getMapping(), edit.getRevMapping(), g.getGraph(), rec.getGraph(), topLevelNames(g), topLevelNames(rec), handMappings, ignoreList);
	        int[] tempNumCorrectness = checkCorrectnessSubset(edit.getMapping(), edit.getRevMapping(), g.getGraph(), rec.getGraph(), numberMap);
	        for(int i=0;i<tempCorrectness.length;i++) {
	        	correctness[i][trialNum] = tempCorrectness[i];
	        	numCorrectness[i][trialNum] = tempNumCorrectness[i];
	        }
//	        System.out.println(Arrays.toString(correctness));

			trialNum++;
		}

		RuleGraph g = new RuleGraph(this.rules, null);
		g.genRuleGraph();
		RuleGraphRecord rec = new RuleGraphRecord();
    	rec.loadFromFile(recordFile, true);
    	int[] maxCorrectnessVals = maxCorrect(topLevelNames(g), topLevelNames(rec), handMappings, ignoreList);
    	int maxNumMaps = maxNumberMappings(topLevelNames(g), topLevelNames(rec), numberSet);

		double[] meanTotalCorrect = new double[3];
		double[] stdTotalCorrect = new double[3];
		double[] meanPercentCorrect = new double[3];
		double[] stdPercentCorrect = new double[3];
		double[][] correctnessPercent = new double[3][numTrials];

		for(int i=0;i<3;i++) {
			for(int j=0;j<numTrials;j++) {
				if(maxCorrectnessVals[i] != 0) {
					correctnessPercent[i][j] = ((double)correctness[i][j])/maxCorrectnessVals[i]*100;
				} else {
					correctnessPercent[i][j] = 0;
				}
			}
			meanTotalCorrect[i] = MyUtil.mean(correctness[i]);
			stdTotalCorrect[i] = MyUtil.std(correctness[i]);
			meanPercentCorrect[i] = MyUtil.mean(correctnessPercent[i]);
			stdPercentCorrect[i] = MyUtil.std(correctnessPercent[i]);
		}

		//calculations for nodes representing numbers
		double numberMeanTotalCorrect = MyUtil.mean(numCorrectness[0]);
		double numberStdTotalCorrect = MyUtil.std(numCorrectness[0]);
		double[] numberCorrectnessPercent = new double[numTrials];
		for(int i=0;i<numTrials;i++) {
			if(numCorrectness[3][i] != 0) {
				numberCorrectnessPercent[i] = ((double)numCorrectness[0][i] / maxNumMaps)*100;
			} else {
				numberCorrectnessPercent[i] = 0;
			}
		}
		double numberMeanPercentCorrect = MyUtil.mean(numberCorrectnessPercent);
		double numberStdPercentCorrect = MyUtil.std(numberCorrectnessPercent);

		HashSet<String> g1NonNumberNames = setMinus(topLevelNames(g),numberSet);
		HashSet<String> g2NonNumberNames = setMinus(topLevelNames(rec),numberSet);
//		System.out.println(g1NonNumberNames);
//		System.out.println(g2NonNumberNames);
		double percentSharedNames = ((double) maxCorrectnessVals[0])*2 / (g1NonNumberNames.size()+g2NonNumberNames.size())*100;

		System.out.println("Settings: " + numTrials + " trials - " + mappingAlg + " - " + testMode + " - " + param);
		System.out.println();
		System.out.println("Rule graph size: " + g.getGraph().size() + " nodes");
		System.out.println();
        System.out.format("Mean graph gen time (ms): %.2f\n", MyUtil.mean(genTimes)/1000000.0);
        System.out.format("                     STD: %.2f\n", MyUtil.std(genTimes)/1000000.0);
		System.out.println();
        System.out.format("Mean time (ms): %.2f\n", MyUtil.mean(times)/1000000.0);
        System.out.format("           STD: %.2f\n", MyUtil.std(times)/1000000.0);
        System.out.println();
        System.out.format("Mean distance: %.4f\n", MyUtil.mean(distances));
        System.out.format("          STD: %.4f\n", MyUtil.std(distances));
        System.out.println();
        System.out.format("Mean correct G1->G2: %.2f +/- %.2f\n", meanTotalCorrect[0], stdTotalCorrect[0]);
        System.out.format("     Percent G1->G2: %.2f +/- %.2f\n", meanPercentCorrect[0], stdPercentCorrect[0]);
        System.out.format("Mean correct G1->-1: %.2f +/- %.2f\n", meanTotalCorrect[1], stdTotalCorrect[1]);
        System.out.format("     Percent G1->-1: %.2f +/- %.2f\n", meanPercentCorrect[1], stdPercentCorrect[1]);
        System.out.format("Mean correct -1->G2: %.2f +/- %.2f\n", meanTotalCorrect[2], stdTotalCorrect[2]);
        System.out.format("     Percent -1->G2: %.2f +/- %.2f\n", meanPercentCorrect[2], stdPercentCorrect[2]);
        System.out.println();
        System.out.format("# Shared Names: %d,  Percent: %.2f\n",maxCorrectnessVals[0],percentSharedNames);
        System.out.println();
        System.out.format("Mean correct numbers G1->G2: %.2f +/- %.2f\n", numberMeanTotalCorrect, numberStdTotalCorrect);
        System.out.format("     Percent numbers G1->G2: %.2f +/- %.2f\n", numberMeanPercentCorrect, numberStdPercentCorrect);
        System.out.println();
        System.out.println("All times: " + times);
        System.out.println("All distances: " + Arrays.toString(distances));
        System.out.println("All correctness:");
        for(int i=0;i<6;i++) {
        	System.out.println(Arrays.toString(correctness[i]));
        }
        System.out.println("All number correctness:");
        for(int i=0;i<6;i++) {
        	System.out.println(Arrays.toString(numCorrectness[i]));
        }
        System.out.println();
        System.out.println();

        return meanPercentCorrect[0];
	}


	//correctness[0] = # correct mappings from G1->G2
	//correctness[1] = # correct mappings from G1->-1
	//correctness[2] = # correct mappings from -1->G2
	//correctness[3] = total mappings from G1->G2
	//correctness[4] = total mappings from G1->-1
	//correctness[5] = total mappings from -1->G2
	public static int[] checkCorrectness(HashMap<Integer, Integer> mapping, HashMap<Integer, Integer> revMapping, ArrayList<RuleNode> g1, ArrayList<RuleNode> g2,
			HashSet<String> g1Names, HashSet<String> g2Names, HashMap<String, String> handMappings, HashSet<String> ignoreList) {

		int[] correctness = new int[6];

		for(int g1Index : mapping.keySet()) {
//			System.out.println("AAAAAAAAAAAA " + g1Index);
			RuleNode g1Node = g1.get(g1Index);
			if(!ignoreList.contains(g1Node.getName())) {
				int g2Index = mapping.get(g1Index);
				if(g2Index != -1) {
					correctness[3]++;
					RuleNode g2Node = g2.get(g2Index);
					if(g1Node.getColour() == g2Node.getColour() && (g1Node.getName().equals(g2Node.getName()) || (handMappings.containsKey(g1Node.getName()) && handMappings.get(g1Node.getName()).equals(g2Node.getName())))) {
						correctness[0]++;
//						System.out.println("Good mapping: " + g1Node.getName() + " -> " + g2Node.getName());
					} else {
//						System.out.println("Incorrect mapping: " + g1Node.getName() + " -> " + g2Node.getName());
					}
				} else {
					correctness[4]++;
					if(!g2Names.contains(g1Node.getName()) && !handMappings.containsKey(g1Node.getName())) {
						correctness[1]++;
					} else {
//						System.out.println("Incorrect mapping: " + g1Node.getName() + " -> -1");
					}
				}
			}
		}
		for(int g2Index : revMapping.keySet()) {
			RuleNode g2Node = g2.get(g2Index);
			if(!ignoreList.contains(g2Node.getName())) {
				if(revMapping.get(g2Index) == -1) {
					correctness[5]++;
					if(!g1Names.contains(g2Node.getName()) && !handMappings.containsValue(g2Node.getName())) {
						correctness[2]++;
					} else {
//						System.out.println("Incorrect mapping: -1 -> " + g2Node.getName());
					}
				}
			}
		}

		return correctness;
	}

	//correctness[0] = # correct mappings from G1->G2
	//correctness[1] = # correct mappings from G1->-1 //not used
	//correctness[2] = # correct mappings from -1->G2 //not used
	//correctness[3] = total mappings from G1->G2
	//correctness[4] = total mappings from G1->-1 //not used
	//correctness[5] = total mappings from -1->G2 //not used
	public static int[] checkCorrectnessSubset(HashMap<Integer, Integer> mapping, HashMap<Integer, Integer> revMapping, ArrayList<RuleNode> g1, ArrayList<RuleNode> g2, HashMap<String, String> subset) {
		int[] correctness = new int[6];

		for(int g1Index : mapping.keySet()) {
			RuleNode g1Node = g1.get(g1Index);
			if(subset.containsKey(g1Node.getName())) {
				int g2Index = mapping.get(g1Index);
				if(g2Index != -1) {
					correctness[3]++;
					RuleNode g2Node = g2.get(g2Index);
					if(g1Node.getColour() == g2Node.getColour() && subset.get(g1Node.getName()).equals(g2Node.getName())) {
						correctness[0]++;
					} else {
//						System.out.println("Incorrect mapping: " + g1Node.getName() + " -> " + g2Node.getName());
					}
				}
			}
		}
		return correctness;
	}

	//maxVals[0] = total possible correct mappings from G1->G2
	//maxVals[1] = total possible correct mappings from G1->-1
	//maxVals[2] = total possible correct mappings from -1->G2
	public static int[] maxCorrect(HashSet<String> g1Names, HashSet<String> g2Names, HashMap<String, String> handMappings, HashSet<String> ignoreList) {
		int[] maxVals = new int[3];

		for(String g1Name : g1Names) {
			if(!ignoreList.contains(g1Name)) {
				if(handMappings.containsKey(g1Name) || g2Names.contains(g1Name)) {
					maxVals[0]++;
				} else {
					maxVals[1]++;
				}
			}
		}
		for(String g2Name : g2Names) {
			if(!ignoreList.contains(g2Name) && !handMappings.containsValue(g2Name) && !g1Names.contains(g2Name)) {
				maxVals[2]++;
			}
		}

		return maxVals;
	}

	public static int maxNumberMappings(HashSet<String> g1Names, HashSet<String> g2Names, HashSet<String> nums) {
		int result = 0;
		for(String numName : nums) {
			if(g1Names.contains(numName) && g2Names.contains(numName)) {
				result++;
			}
		}
		return result;
	}

	public static ArrayList<String> genNumberStrings(int howMany, String prefix) {
		ArrayList<String> result = new ArrayList<String>();
		for(int i=0;i<howMany;i++) {
			result.add(prefix + i);
		}
		return result;
	}

	public static ArrayList<String> genNumberStrings(int howMany) {
		return genNumberStrings(howMany, "");
	}


	public static HashSet<String> topLevelNames (RuleGraph graph) {
		HashSet<String> result = new HashSet<String>();
		for(int id : graph.getTopLevelNonVarIds()) {
			result.add(graph.getGraph().get(id).getName());
		}
		return result;
	}

	public static HashSet<String> topLevelNames (RuleGraphRecord record) {
		HashSet<String> result = new HashSet<String>();
		for(int id : record.getTopLevelNonVarIds()) {
			result.add(record.getGraph().get(id).getName());
		}
		return result;
	}

	public static HashSet<String> setMinus(HashSet<String> set1, HashSet<String> set2) {
		HashSet<String> result = new HashSet<String>();
		for(String item : set1) {
			if(!set2.contains(item)) {
				result.add(item);
			}
		}
		return result;
	}
}
