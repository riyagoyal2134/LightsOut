package Research;

import java.math.BigInteger;
import java.util.ArrayList;
import java.util.Collections;
import java.util.List;
import java.util.Random;
import java.util.Scanner;

/**
 * Graph Generation Algorithm using Random Orbits and Newton's Method for
 * generating unlabeled graphs with n vertices and m edges and analyzing the
 * invertibility.
 * 
 */

public class algorithm {

	static Scanner sc = new Scanner(System.in);
	static Random rand = new Random();

	public static void main(String[] args) {

		long start = System.nanoTime();
		int n;
		System.out.print("Enter the number of vertices (n): ");
		n = sc.nextInt();
		double N = 33 * (n - 1) * 0.5;
		double p, q;
		double r = 0;

		for (int m = 1; m < N; m++) {
			p = m / N;
			q = 1 - p;
			double B1 = Math.pow(p, -m) * Math.pow(q, m - N);
			double Bi = 0;
			double B = B1;
			List<Double> R = new ArrayList<>(); // List to store Bi values
			List<Double> P = new ArrayList<>(); // list to store p values
			List<Double> Q = new ArrayList<>(); // list to store q values
			R.add(B1);

			for (int i = 2; i <= n; i++) {
				double H = i * (n * 0.5 - (i + 2) * 0.25);
				double initialGuess = p;
				int maxIterations = 1000;
				double tolerance = 1e-6;
				r = solveNewton((int) N, m, H, initialGuess, maxIterations, tolerance);
				
				p = r / (r + 1);
				P.add(p);

				q = 1 - p;
				Q.add(q);

				Bi = Math.pow(p, -m) * Math.pow(q, m - N) * Math.pow((Math.pow(p, 2) + Math.pow(q, 2)), H)
						* factorial(n) * (1.0 / factorial(n - i));

				R.add(Bi);
				B += Bi;
			}

			int count = 0;
			List<Integer> permutation = new ArrayList<>();
			ArrayList<ArrayList<Integer>> Graph = new ArrayList<ArrayList<Integer>>();
			ArrayList<ArrayList<Integer>> cycles = new ArrayList<ArrayList<Integer>>();
			ArrayList<ArrayList<ArrayList<Integer>>> orbits = new ArrayList<ArrayList<ArrayList<Integer>>>();

			int numberOfRuns = 1000000;
			int invertibleCount = 0;

			for (int run = 1; run <= numberOfRuns; run++) {
				double H_value;
				double B_value;
				double result;
				double[] h = new double[(int) N];
				double fraction = 0;
				double Probability = 0;
				double randomValue = 1;
				double sum = 0;
				double R_value = 0;

				while (randomValue > Probability) {
					randomValue = rand.nextDouble();
					Graph.clear();
					while (Graph.size() != m) {
						R_value = 0;
						R_value = rand.nextDouble();
						List<Integer> permutation2 = new ArrayList<>();
						permutation = permutation2;
						sum = 0;
						count = 0;
						while (sum < R_value) {
							sum = sum + R.get(count) / B;
							count++;
						}
						if (count == 1) {
							for (int i = 1; i <= n; i++) {
								permutation.add(i);
							}
						} 
						else {
							for (int i = 1; i <= count; i++) {
								permutation.add(i);
							}
							Collections.shuffle(permutation);
							while (checkPermutation(permutation) == false) {
								Collections.shuffle(permutation);

							}
							for (int i = count + 1; i <= n; i++) {
								permutation.add(i);
							}
						}
						cycles = convertCycle(permutation);
						orbits = orbits(cycles);

						if (count == 1) {
							p = m / N;
							q = 1 - p;
						} 
						else {
							p = P.get(count - 2);
							q = 1 - p;
						}
						Graph = choosefix(orbits, p, q, m);
					}

					H_value = count * (n * 0.5 - (count + 2) * 0.25);
					B_value = Math.pow((Math.pow(p, 2) + Math.pow(q, 2)), H_value);
					result = 1;
					for (int i = 0; i < N; i++) {
						h[i] = 0;
					}
					fraction = 0;

					if (count == 1) {
						Probability = 1;
					} 
					else {

						for (int i = 0; i < orbits.size(); i++) {
							h[orbits.get(i).size() - 1]++;

						}
						for (int i = 1; i <= N; i++) {
							result *= Math.pow((Math.pow(p, i) + Math.pow(q, i)), h[i - 1]);
						}
						for (int j = 2; j <= count; j++) {
							fraction += Math.pow(-1, j) * (1.0 / factorial(j));
						}
						Probability = fraction * result * (1.0 / B_value);
					}
				}

				int[][] matrixGraph = convertToAdjacencyMatrix(Graph, n);

				if (rowOfZeros(matrixGraph)) {
					invertibleCount++;
				}
			}
			System.out.println("m:" + m);
			System.out.println("Probability of Invertible Graphs: " + invertibleCount);
			long duration = (System.nanoTime() - start) / 1000000;
			System.out.println(duration + "ms");
		}
	}

	/**
	 * Solves a cubic equation using Newton method.
	 * 
	 * @param N             Number of potential edges
	 * @param m             Current edge count
	 * @param H             H value computed per count
	 * @param initialGuess  Initial guess for r
	 * @param maxIterations Maximum number of iterations allowed
	 * @param tolerance     Acceptable convergence tolerance
	 * @return Converged value of r
	 */

	public static double solveNewton(int N, int m, double H, double initialGuess, int maxIterations, double tolerance) {
		double r = initialGuess;
		for (int i = 0; i < maxIterations; i++) {
			double f = N * r * (r * r + 1) - m * (r + 1) * (r * r + 1) + 2 * H * r * (r - 1);
			double fPrime = 3 * N * r * r + N - m * ((r * r + 1) + 2 * r * (r + 1)) + 2 * H * (2 * r - 1);
			if (Math.abs(fPrime) < 1e-6)
				break;
			double rNext = r - f / fPrime;
			if (Math.abs(rNext - r) < tolerance)
				return rNext;
			r = rNext;
		}
		return r;
	}

	/**
	 * Converts a permutation to disjoint cycle representation.
	 * 
	 * @param permutation A permutation list
	 * @return List of cycles
	 */

	public static ArrayList<ArrayList<Integer>> convertCycle(List<Integer> permutation) {
		int n = permutation.size();
		boolean[] visited = new boolean[n];
		ArrayList<ArrayList<Integer>> cycles = new ArrayList<>();
		for (int i = 0; i < n; i++) {
			if (!visited[i]) {
				ArrayList<Integer> cycle = new ArrayList<>();
				int current = i;
				do {
					visited[current] = true;
					cycle.add(current + 1);
					current = permutation.get(current) - 1;
				} while (current != i);
				cycles.add(cycle);
			}
		}
		return cycles;
	}

	/**
	 * Generates intra-cycle orbits (self-orbits).
	 * 
	 * @param list Cycle list
	 * @return List of orbit sets within each cycle
	 */

	public static ArrayList<ArrayList<ArrayList<Integer>>> orbitsFromSelf(ArrayList<ArrayList<Integer>> list) {
		ArrayList<ArrayList<ArrayList<Integer>>> returnList = new ArrayList<>();
		for (ArrayList<Integer> l : list) {
			int size = l.size();
			if (size == 2) {
				ArrayList<ArrayList<Integer>> set = new ArrayList<>();
				set.add(l);
				returnList.add(set);
			} else if (size > 2) {
				double value = (Math.floor((size - 2) / 2)) + (1.0);
				for (int i = 0; i < value; i++) {
					ArrayList<ArrayList<Integer>> set2 = new ArrayList<>();
					int index = size;
					if ((2 * (i + 1) == size)) {
						index = size / 2;
					}
					for (int j = 0; j < index; j++) {
						ArrayList<Integer> set1 = new ArrayList<>();
						int a = mod(j, size);
						int b = mod(j + i + 1, size);
						set1.add(l.get(a));
						set1.add(l.get(b));
						set2.add(set1);
					}
					returnList.add(set2);
				}
			}
		}
		return returnList;
	}

	/**
	 * Computes all orbit sets from disjoint cycles.
	 * 
	 * @param cycle Disjoint cycle partition
	 * @return List of orbits generated from the cycle
	 */
	public static ArrayList<ArrayList<ArrayList<Integer>>> orbits(ArrayList<ArrayList<Integer>> cycle) {
		ArrayList<ArrayList<ArrayList<Integer>>> set3 = orbitsFromSelf(cycle);
		ArrayList<ArrayList<Integer>> representative = (ArrayList<ArrayList<Integer>>) cycle.clone();
		for (ArrayList<Integer> l : cycle) {
			representative.remove(l);
			if (representative.isEmpty() == true) {
				break;
			} else {
				int lena = l.size();
				for (ArrayList<Integer> r : representative) {
					int lenb = r.size();
					for (int j = 0; j < gcd(lena, lenb); j++) {
						ArrayList<ArrayList<Integer>> set2 = new ArrayList<>();
						for (int i = 0; i < lcm(lena, lenb); i++) {
							ArrayList<Integer> set1 = new ArrayList<>();
							int a = mod(i, lena);
							int b = mod(i + j, lenb);
							set1.add(l.get(a));
							set1.add(r.get(b));
							set2.add(set1);
						}
						set3.add(set2);
					}
				}
			}
		}
		return set3;
	}

	/**
	 * Chooses a subset of orbits based on probability function.
	 * 
	 * @param orbits List of all orbits
	 * @param p      Probability p
	 * @param q      Complement probability q
	 * @param m      Number of required edges
	 * @return List of selected edges
	 */

	public static ArrayList<ArrayList<Integer>> choosefix(ArrayList<ArrayList<ArrayList<Integer>>> orbits, double p,
			double q, int m) {
		ArrayList<ArrayList<Integer>> L = new ArrayList<ArrayList<Integer>>();
		for (int i = 0; i < orbits.size(); i++) {
			int sizeoforbit;
			sizeoforbit = orbits.get(i).size();
			double probabilityInclude = Math.pow(p, sizeoforbit)
					/ (Math.pow(p, sizeoforbit) + Math.pow(q, sizeoforbit));
			double randomValue = rand.nextDouble();
			if (randomValue < probabilityInclude) {
				for (int j = 0; j < sizeoforbit; j++) {
					L.add(orbits.get(i).get(j));
				}
			}
		}
		return L;
	}

	/**
	 * Converts an edge list to adjacency matrix.
	 * 
	 * @param graph Edge list
	 * @param n     Number of vertices
	 * @return Adjacency matrix
	 */

	public static int[][] convertToAdjacencyMatrix(ArrayList<ArrayList<Integer>> graph, int n) {
		int[][] Matrix = new int[n][n];
		for (int t = 0; t < n; t++) {
			for (int s = 0; s < n; s++) {
				if (s == t) {
					Matrix[s][t] = 1;
				} else {
					Matrix[s][t] = 0;
				}
			}
		}
		for (int i = 0; i < graph.size(); i++) {
			ArrayList<Integer> edges = graph.get(i);
			Matrix[edges.get(0) - 1][edges.get(1) - 1] = 1;
			Matrix[edges.get(1) - 1][edges.get(0) - 1] = 1;
		}
		return Matrix;
	}

	/**
	 * Traverses a graph using DFS.
	 * 
	 * @param u       Current node
	 * @param visited Visited array
	 * @param node    Total number of nodes
	 * @param Matrix  Adjacency matrix
	 */

	public static void traverse(int u, int[] visited, int node, int[][] Matrix) {
		visited[u] = 1;
		for (int v = 0; v <= node; v++) {
			if (Matrix[u][v] == 1) {
				if (visited[v] == 0) {
					traverse(v, visited, node, Matrix);
				}
			}
		}
	}

	/**
	 * Checks whether the graph is connected.
	 * 
	 * @param Matrix Adjacency matrix
	 * @return True if connected, false otherwise
	 */

	public static boolean isConnected(int[][] Matrix) {
		boolean connected = true;
		int node = Matrix[0].length - 1;
		int[] visited = new int[node + 1];
		traverse(0, visited, node, Matrix);
		for (int i = 0; i <= node; i++) {
			if (visited[i] == 0) {
				connected = false;
			}
		}
		return connected;
	}

	/**
	 * Computes row-reduced echelon form.
	 * 
	 * @param a Matrix to reduce
	 * @return Reduced matrix
	 */

	public static int[][] rref(int[][] a) {
		int lead = 0;
		int[][] m = copyMatrix(a);
		int rowCount = m.length;
		int colCount = m[0].length;
		int index;
		boolean quit = false;
		for (int row = 0; row < rowCount && !quit; row++) {
			if (colCount <= lead) {
				quit = true;
				break;
			}
			index = row;
			while (!quit && m[index][lead] == 0) {
				index++;
				if (rowCount == index) {
					index = row;
					lead++;
					if (colCount == lead) {
						quit = true;
						break;
					}
				}
			}
			if (!quit) {
				swapRows(m, index, row);
				for (index = 0; index < rowCount; index++) {
					if (index != row) {
						subtractRows(m, m[index][lead], row, index);
					}
				}
			}
		}
		return m;
	}

	/**
	 * Checks if RREF matrix contains an all-zero row (i.e., not invertible).
	 * 
	 * @param a Matrix to check
	 * @return True if no zero row (invertible), false otherwise
	 */

	public static boolean rowOfZeros(int[][] a) {
		int[][] rreA = rref(a);
		boolean zero = true;
		for (int i = 0; i < rreA.length; i++) {
			int count = 0;
			for (int j = 0; j < rreA[i].length; j++) {
				if (rreA[i][j] == 0) {
					count++;
				}
			}
			if (count == a.length) {
				zero = false;
				break;
			}
		}
		return zero;
	}

	/**
	 * Swaps two rows in a matrix.
	 * 
	 * @param m    Matrix
	 * @param row1 First row of matrix
	 * @param row2 Second row of matrix
	 */

	static void swapRows(int[][] m, int row1, int row2) {
		int[] swap = new int[m[0].length];
		for (int c1 = 0; c1 < m[0].length; c1++)
			swap[c1] = m[row1][c1];
		for (int c1 = 0; c1 < m[0].length; c1++) {
			m[row1][c1] = m[row2][c1];
			m[row2][c1] = swap[c1];
		}
	}

	/**
	 * Subtracts scalar multiple of one row from another.
	 * 
	 * @param m    Matrix
	 * @param s    Scalar
	 * @param row1 Row to multiply
	 * @param row2 Row to subtract from
	 */

	static void subtractRows(int[][] m, double s, int row1, int row2) {
		for (int i = 0; i < m[0].length; i++) {
			m[row2][i] -= s * m[row1][i];
			if (m[row2][i] % 2 == 0) {
				m[row2][i] = 0;
			} else {
				m[row2][i] = 1;
			}
		}
	}

	/**
	 * Returns a deep copy of a matrix.
	 * 
	 * @param a Matrix to copy
	 * @return Copied matrix
	 */

	public static int[][] copyMatrix(int[][] a) {
		int[][] copy = new int[a.length][];
		for (int i = 0; i < a.length; i++) {
			copy[i] = a[i].clone();
		}
		return copy;
	}

	/**
	 * Checks if permutation has no fixed points (i.e., is not the identity).
	 * 
	 * @param permutation Permutation list
	 * @return True if valid, false if identity
	 */

	public static boolean checkPermutation(List<Integer> permutation) {
		for (int i = 1; i <= permutation.size(); i++) {
			if (i == permutation.get(i - 1)) {
				return false;
			}
		}
		return true;
	}

	/**
	 * Computes modulo operation.
	 * 
	 * @param a Dividend
	 * @param b Divisor
	 * @return a mod b
	 */

	public static int mod(int a, int b) {
		return ((a % b) + b) % b;
	}

	/**
	 * Computes least common multiple.
	 * 
	 * @param a First number
	 * @param b Second number
	 * @return LCM of a and b
	 */

	public static int lcm(int a, int b) {
		return a * b / gcd(a, b);
	}

	/**
	 * Computes greatest common divisor.
	 * 
	 * @param a First number
	 * @param b Second number
	 * @return GCD of a and b
	 */

	public static int gcd(int a, int b) {
		BigInteger b1 = BigInteger.valueOf(a);
		BigInteger b2 = BigInteger.valueOf(b);
		BigInteger gcd = b1.gcd(b2);
		return gcd.intValue();
	}

	/**
	 * Computes factorial of a number.
	 * 
	 * @param n Number to factorial
	 * @return n!
	 */

	public static double factorial(int n) {
		double res = 1;
		for (int i = 2; i <= n; i++) {
			res *= i;
		}
		return res;
	}
}
