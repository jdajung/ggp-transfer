package org.ggp.base.player.gamer.statemachine.sample;

import java.util.ArrayList;
import java.util.Comparator;
import java.util.List;
import java.util.Random;

public abstract class MyUtil {

	public static boolean isNat(String str) {
		boolean ans = true;
	    if (str == null) {
	    	ans =  false;
	    } else {
		    for (char c : str.toCharArray()) {
		        if (c < '0' || c > '9') {
		            ans = false;
		            break;
		        }
		    }
	    }
	    return ans;
	}

	public static double mean(double[] arr) {
		double sum = 0;
		for(int i=0;i<arr.length;i++) {
			sum += arr[i];
		}
		return sum / arr.length;
	}

	public static double mean(ArrayList<Long> lst) {
		double sum = 0;
		for(double val : lst) {
			sum += val;
		}
		return sum / lst.size();
	}

	public static double mean(int[] arr) {
		ArrayList<Long> lst = new ArrayList<Long>();
		for(int i=0;i<arr.length;i++) {
			lst.add((long)arr[i]);
		}
		return mean(lst);
	}

	public static double std(double[] arr) {
		double mean = mean(arr);
		double sum = 0;
		for(int i=0;i<arr.length;i++) {
			sum += Math.pow(arr[i]-mean, 2);
		}
		return Math.sqrt(sum / arr.length);
	}

	public static double std(ArrayList<Long> lst) {
		double mean = mean(lst);
		double sum = 0;
		for(double val : lst) {
			sum += Math.pow(val-mean, 2);
		}
		return Math.sqrt(sum / lst.size());
	}

	public static double std(int[] arr) {
		ArrayList<Long> lst = new ArrayList<Long>();
		for(int i=0;i<arr.length;i++) {
			lst.add((long)arr[i]);
		}
		return std(lst);
	}

	public static double logistic(double x, double offset, double steepness) {
		return 1.0 / (1 + Math.exp(-steepness*(x - offset)));
	}

	public static long[] genLongs(int numLongs, long seed) {
		long[] result = new long[numLongs];
		Random rand = new Random(seed);
		for(int i=0;i<numLongs;i++) {
			result[i] = rand.nextLong();
		}
		return result;
	}


	// produces all combinations where item 1 is chosen from list 1 in itemsByPosition, item 2 is from list 2, and so on
	public static <T> List<List<T>> allCombinations(List<List<T>> itemsByPosition) {
		List<List<T>> result = new ArrayList<List<T>>();

		int[] currPosn = new int[itemsByPosition.size()];
		int[] bounds = new int[itemsByPosition.size()];
		for(int i=0;i<currPosn.length;i++) {
			currPosn[i] = 0;
			bounds[i] = itemsByPosition.get(i).size() - 1;
			if(bounds[i] < 0) {
				System.out.println("ERROR: allCombinations was given a position with no items.");
			}
		}
		boolean finished = false;

		while(!finished) {
			ArrayList<T> newCombo = new ArrayList<T>();
			for(int i=0;i<itemsByPosition.size();i++) {
				List<T> position = itemsByPosition.get(i);
				newCombo.add(position.get(currPosn[i]));
			}
			result.add(newCombo);

			int updateIndex = 0;
			boolean updateFinished = false;
			while(!updateFinished && updateIndex < currPosn.length) {
				if(currPosn[updateIndex] < bounds[updateIndex]) {
					currPosn[updateIndex]++;
					for(int i=0;i<updateIndex;i++) {
						currPosn[i] = 0;
					}
					updateFinished = true;
				} else {
					updateIndex++;
				}
			}
			if(updateIndex >= currPosn.length) {
				finished = true;
			}
		}

		return result;
	}

	//for testing stuff - should normally be commented out
//	public static void main(String[] args) {
//		List<List<Integer>> testByPosition = new ArrayList<List<Integer>>();
//		testByPosition.add(new ArrayList<Integer>(Arrays.asList(1,2,3)));
//		testByPosition.add(new ArrayList<Integer>(Arrays.asList(4,5)));
//		testByPosition.add(new ArrayList<Integer>(Arrays.asList(6)));
//		testByPosition.add(new ArrayList<Integer>(Arrays.asList(7,8,9)));
//
//		List<List<Integer>> combos = allCombinations(testByPosition);
//		for(List<Integer> c : combos) {
//			System.out.println(c);
//		}
//	}

	public static class StringListComparator implements Comparator<List<String>> {

	  @Override
	  public int compare(List<String> o1, List<String> o2) {
	    for (int i = 0; i < Math.min(o1.size(), o2.size()); i++) {
	      int c = o1.get(i).compareTo(o2.get(i));
	      if (c != 0) {
	        return c;
	      }
	    }
	    return Integer.compare(o1.size(), o2.size());
	  }

	}

	//sorts lists from smallest to largest
	public static class ListSizeComparator<T> implements Comparator<List<T>> {

		@Override
		public int compare(List<T> o1, List<T> o2) {
			return o1.size() - o2.size();
		}
	}
}
