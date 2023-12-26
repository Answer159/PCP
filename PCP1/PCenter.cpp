#include "PCenter.h"
#include <random>
#include <algorithm>
#include <iostream>
#include <set>
#include <chrono>
#include<fstream>

using namespace std;


namespace szx {

	class Solver {
		int* cover_count;  //每个结点被center覆盖的次数
		int** interact;
		//int** coverMatrix;
		int* interact_size,* interact_sum;
		int* tabu;
		int iter = 1;
		int* left, * left_pos;
		int left_size;
		int* res, * res_pos;
		int res_size;
		int* sigma, * sigma1;
		int* weight;
		int v1 = -1, v2 = -2;
		int res_start = 0;
		int flag1 = 0;


		// random number generator.
		mt19937 pseudoRandNumGen;
		void initRand(int seed) { pseudoRandNumGen = mt19937(seed); }
		int fastRand(int lb, int ub) { return (pseudoRandNumGen() % (ub - lb)) + lb; }
		int fastRand(int ub) { return pseudoRandNumGen() % ub; }
		int rand(int lb, int ub) { return uniform_int_distribution<int>(lb, ub - 1)(pseudoRandNumGen); }
		int rand(int ub) { return uniform_int_distribution<int>(0, ub - 1)(pseudoRandNumGen); }

		void TryToOpenCenter(PCenter& input, int i) {
			for (auto j = input.coverages[i].begin(); j != input.coverages[i].end(); j++) {
				//int temp = input.coverages[i][j];
				if (interact_size[*j] == 1) {
					sigma1[interact_sum[*j]] -= weight[*j];
				}
			}
		}
		void FindPair(int iter, PCenter& input) {
			v1 = -2, v2 = -2;
			int obj = LONG_MAX;
			int solCount = 1;
			int index = left[fastRand(left_size)];
			int temp = 0;
			for (int i = 0; i < input.nodeNum; i++) {
				sigma1[i] = sigma[i];
			}
			for (auto i = input.coverages[index].begin(); i < input.coverages[index].end(); i++) {
				//int t = input.coverages[index][i];
				if (tabu[*i] >= iter) { //没有被禁忌并且能够覆盖index的服务点
					continue;
				}
				TryToOpenCenter(input,*i);
				for (int j = res_start; j < res_size; j++) {
					int b = res[j];
					if (tabu[b] < iter) {
						temp = sigma1[b] - sigma1[*i];
						if (temp < obj) {
							obj = temp;
							v1 = *i;
							v2 = b;
							//solCount = 1;
						}
						else if (temp == obj) {
							//solCount++;
							if (fastRand(++solCount) == 0) {
								v1 = *i;
								v2 = b;
							}
						}
					}
					
				}
				for (int j = 0; j < input.centerNum; j++) {
					sigma1[res[j]] = sigma[res[j]];
				}
				
			}
		}
		void MakeMove(int i, int j, PCenter& input) {
			//对于i可覆盖的所有结点v1，如果v1被其他中心结点覆盖过一次，该中心结点的sigma减去v1的权重
			for (auto v = input.coverages[i].begin(); v < input.coverages[i].end(); v++) {
				//int temp = input.coverages[i][v];
				if (interact_size[*v] == 1) {
					sigma[interact_sum[*v]] -= weight[*v];
				}
				//对于i可覆盖的所有结点v1，如果v1没有被中心结点覆盖，其他能够覆盖v1的结点的sigma减去v1的权重
				else if (interact_size[*v] == 0) {
					for (int l = 0; l < input.coverages[*v].size(); l++) {
						if (input.coverages[*v][l] != i) {
							sigma[input.coverages[*v][l]] -= weight[*v];
						}
					}
					
				}

			}
			//从结果集中移除j,加入i
			int pos = res_pos[j];
			if (input.coverages[i].size() == 1) {
				res[pos] = res[res_start];
				res_pos[j] = -1;
				res_pos[res[res_start]] = pos;
				res[res_start] = i;
				res_pos[i] = res_start;
				res_start++;
			}
			else {
				res[pos] = i;
				res_pos[j] = -1;
				res_pos[i] = pos;
			}
			
			//加入i结点的影响
			for (auto a = input.coverages[i].begin(); a < input.coverages[i].end(); a++) {
				//int temp = input.coverages[i][a];
				int pos = left_pos[*a];
				if (pos != -1) {
					left_size--;
					left[pos] = left[left_size];
					left_pos[left[left_size]] = pos;
					left_pos[*a] = -1;
				}
				interact_size[*a]++;
				interact[*a][i] = 1;
				interact_sum[*a] += i;
			}
			//消除j结点的影响
			for (auto a = input.coverages[j].begin(); a < input.coverages[j].end(); a++) {
				//int temp = input.coverages[j][a];
				if (interact_size[*a] == 1) {
					left[left_size] = *a;
					left_pos[*a] = left_size;
					left_size++;
				}
				interact_size[*a]--;
				interact[*a][j] = -1;
				interact_sum[*a] -= j;

				//int temp = input.coverages[j][v];
				//对于j可覆盖的每个结点v1，如果去掉j的影响后，还有一个中心结点覆盖v1，该中心结点的sigma加上v1的权重
				if (interact_size[*a] == 1) {
					sigma[interact_sum[*a]] += weight[*a];
				}
				//对于j可覆盖的每个结点v1，如果去掉j的影响后，没有中心结点可以覆盖v1，所有可覆盖v1的结点的sigma加v1的权重
				else if (interact_size[*a] == 0) {
					for (int l = 0; l < input.coverages[*a].size(); l++) {
						if (input.coverages[*a][l] != j) {
							sigma[input.coverages[*a][l]] += weight[*a];
						}
					}

				}
			}
		}

	public:
		void solve(Centers& output, PCenter& input, function<long long()> restMilliSec, int seed) {
			initRand(seed);
			int nodeNum = input.nodeNum;
			int centerNum = input.centerNum;
			interact = new int* [nodeNum];
			interact_size = new int[nodeNum];
			interact_sum = new int[nodeNum];
			tabu = new int[nodeNum];
			left = new int[nodeNum];
			left_pos = new int[nodeNum];
			sigma = new int[nodeNum];
			sigma1 = new int[nodeNum];
			weight = new int[nodeNum];
			res = new int[centerNum];
			res_pos = new int[nodeNum];
			left_size = nodeNum;
			res_size = 0;
			cover_count = new int[nodeNum];
			for (int i = 0; i < nodeNum; i++) {
				interact[i] = new int[nodeNum];
			}

			coverAllNodesUnderFixedRadius(output, input, restMilliSec, seed);
			for (auto r = input.nodesWithDrops.begin(); restMilliSec() > 0 && (r != input.nodesWithDrops.end()); ++r) {
				reduceRadius(input, *r,output, restMilliSec,seed);
				coverAllNodesUnderFixedRadius(output, input, restMilliSec, seed);
			}
		}

		void coverAllNodesUnderFixedRadius(Centers& output, PCenter& input, function<long long()> restMilliSec, int seed) {
			
			int nodeNum = input.nodeNum;
			int centerNum = input.centerNum;
			iter = 1;
			if (flag1 == 0) {
				res_size = 0;
				res_start = 0;
				left_size = nodeNum;
				for (int i = 0; i < nodeNum; i++) {
					left[i] = i;
					left_pos[i] = i;
					weight[i] = 1;
					tabu[i] = 0;
					res_pos[i] = -1;
					interact_size[i] = 0;
					interact_sum[i] = 0;
					cover_count[i] = input.coverages[i].size();
					sigma[i] = input.coverages[i].size();
					for (int j = 0; j < nodeNum; j++) {
						interact[i][j] = -1;
					}
				}
				//贪心策略获取k个中心
				for (int j = 0; j < centerNum; j++) {
					int coverMax = 0;
					vector<int> candi;
					int candi_size = 0;
					for (int i = 0; i < nodeNum; i++) {
						if (res_pos[i] == -1) {
							if (cover_count[i] > coverMax) {
								candi.clear();
								coverMax = cover_count[i];
								candi_size = 0;
								candi.push_back(i);
								candi_size++;
							}
							else if (cover_count[i] == coverMax) {
								candi.push_back(i);
								candi_size++;
							}
						}
					}
					//加入结点index到解集中,更新result
					int index = candi[fastRand(candi_size)];
					res[j] = index;
					res_pos[index] = j;
					res_size++;
					//更新其他结点的覆盖数
					for (auto a = 0; a < input.coverages[index].size(); a++) {
						int a1 = input.coverages[index][a];
						if (interact_size[a1] == 0) {  //a1被index覆盖，但是其他结点没有覆盖，其他能够覆盖a1的结点的cover_count减一
							for (int b = 0; b < input.coverages[a1].size(); b++) {
								if (input.coverages[a1][b] != index) {
									cover_count[input.coverages[a1][b]]--;
								}
							}
							
						}
					}
					//更新sigma和剩余结点
					for (auto a = 0; a < input.coverages[index].size(); a++) {
						int a1 = input.coverages[index][a];
						//之前有一个中心结点覆盖了a1，覆盖a1的这个中心点的weight减少
						if (interact_size[a1] == 1) {
							sigma[interact_sum[a1]] -= 1;

						}
						//之前没有中心点覆盖a1点，其他能够覆盖a1点的结点的weight减1
						else if (interact_size[a1] == 0) {
							for (int b = 0; b < input.coverages[a1].size(); b++) {
								if (input.coverages[a1][b] != index) {
									sigma[input.coverages[a1][b]] -= 1;
								}
							}

						}
						//之前没有被覆盖的点，全部从剩余结点中移除
						if (interact_size[a1] == 0) {
							//cout << a1 << "变零,互换" << a1 << "和" << left_size << endl;

							int pos = left_pos[a1];  //pos:a1在left中的下标
							if (pos != -1) {
								left_size--;
								left[pos] = left[left_size];  //将left末尾的元素换到pos位置
								left_pos[left[left_size]] = pos;   //
								left_pos[a1] = -1;
							}

						}
						interact[a1][index] = 1;
						interact_size[a1]++;
						interact_sum[a1] += index;

					}

				}
				flag1 = 1;
			}
			int left_size1 = left_size, best_left = left_size;
			
			while (left_size > 0 && restMilliSec() > 0) {
				FindPair(iter, input);
				if (v2 == -2) {
					iter++;
					//未覆盖点权重加一，所有可覆盖该点的结点的sigma加一
					for (int* i = left; i != left + left_size; i++) {
						weight[*i]++;
						for (int j = 0; j < input.coverages[*i].size(); j++) {
							sigma[input.coverages[*i][j]]++;
						}
						
					}
					continue;
				}
				
				tabu[v1] = iter + 1;
				tabu[v2] = iter + 1;
				MakeMove(v1, v2, input);
				if (left_size < best_left) {
					best_left = left_size;
				}
				else if (left_size >= left_size1) {
					//未覆盖点权重加一，所有可覆盖该点的结点的sigma加一
					for (int i = 0; i < left_size; i++) {
						weight[left[i]]++;
						for (int j = 0; j < input.coverages[left[i]].size(); j++) {
							sigma[input.coverages[left[i]][j]]++;
						}
					}
				}
				left_size1 = left_size;
				iter++;
			}
			if (restMilliSec() > 0 && left_size == 0) {
				for (int i = 0; i < input.centerNum; i++) {
					output[i] = res[i];
				}
			}

			// TODO: implement your own solver which fills the `output` to replace the following trivial solver.
			// sample solver: pick center randomly (the solution can be infeasible).

			//                      +----[ exit before timeout ]
			//                      |
			//for (NodeId n = 0; (restMilliSec() > 0) && (n < input.centerNum); ++n) { output[n] = rand(input.nodeNum); }
			//                                                                                    |
			//               [ use the random number generator initialized by the given seed ]----+

			// TODO: the following code in this function is for illustration only and can be deleted.
			// print some information for debugging.
			
		}

		void reduceRadius(PCenter& input, Nodes nodesWithDrop,Centers& output, function<long long()> restMilliSec,int seed) {
			for (auto n = nodesWithDrop.begin(); n != nodesWithDrop.end(); ++n) {
				int p = input.coverages[*n].back();
				// 如果*n作为中心结点，它单独覆盖的点vi，要变成未覆盖；同时修改对于p点的覆盖数
				if (res_pos[*n] != -1) {
					if (interact_size[p] == 1) {
						left[left_size] = p;
						left_pos[p] = left_size;
						left_size++;
						
					}
					interact_size[p]--;
					interact_sum[p] -= *n;
				}
				//无论是不是中心结点，都要修改的
				interact[p][*n] = -1;
				input.coverages[*n].pop_back();
			}
			for (int i = 0; i < input.nodeNum; i++) {
				weight[i] = 0;
				sigma[i] = 0;
				tabu[i] = 0;
			}
		}
	};

	// solver.
	void solvePCenter(Centers& output, PCenter& input, function<long long()> restMilliSec, int seed) {
		Solver().solve(output, input, restMilliSec, seed);
	}

}
