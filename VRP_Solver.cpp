// Authors :	Ph. Lacomme (placomme@isima.fr)
//
// Date : 2019, august 24
//
// Validation on Visual Studio 2017
//
//
// Show how to use the solver ORTOOLS for the VRP using the modelezation introduced in
//
//
//
// See :   "De la programmation linéaire à la programmation par contraites"
//         authors : Bourreau, Gondran, Lacomme, Vinot
//         Ed. Ellipses - ISBN-10 : 9782340-029460
//         Published : February 2019
// and
//         "Programmation par contraites : démarches de modélisation pour des problèmes d'optimisation"
//         authors : Bourreau, Gondran, Lacomme, Vinot
//         Ed. Ellipses
//         Published : to appear in february 2020
//
//
// Note : this model is exactly the same model used in VRP_SAT_Solver.cpp
//
//


#include <iostream>
using namespace std;

#define _SECURE_SCL 0
#define _ALLOW_ITERATOR_DEBUG_LEVEL_MISMATCH
#define NOMINMAX

#define _SILENCE_CXX17_OLD_ALLOCATOR_MEMBERS_DEPRECATION_WARNING
#define _SILENCE_ALL_CXX17_DEPRECATION_WARNINGS


#include "ortools/base/logging.h"

// PPC Solveur
#include "ortools/constraint_solver/constraint_solver.h"


using namespace operations_research;


void VRP()
{
	const int N = 10;						// number of nodes
	const int V = 4;						// number of vehicles
	const int H = 100;						// upper bound of the distance
	const int nb_total_nodes = N + V * 2;	// total number of nodes including one depot per vehicle
	const int Q = 10;                       // identical vehicle of capacity 10

	Solver solver("VRP");

	//  data
	int T[N][N] = {
					{0, 1, 3, 5, 1, 4, 4, 3, 4, 3},
					{1, 0, 4, 4, 3, 4, 3, 1, 2, 1},
					{3, 4, 0, 4, 1, 1, 3, 1, 1, 1},
					{5, 4, 4, 0, 3, 4, 9, 3, 1, 2},
					{1, 3, 1, 3, 0, 2, 2, 1, 3, 5},
					{4, 4, 1, 4, 2, 0, 4, 5, 1, 2},
					{4, 3, 3, 9, 2, 4, 0, 2, 1, 1},
					{3, 1, 1, 3, 1, 5, 2, 0, 2, 1},
					{4, 2, 1, 1, 3, 1, 1, 2, 0, 1},
					{3, 1, 1, 2, 4, 2, 1, 1, 1, 0}
	};

	// demands
	int D[nb_total_nodes] = { 0 };

	D[0] = 0; D[1] = 1; D[2] = 3; D[3] = 5; D[4] = 1;
	D[5] = 4; D[6] = 4; D[7] = 3; D[8] = 4; D[9] = 3;

	for (int i = N; i < nb_total_nodes; i++) {
		D[i] = 0;
	}

	// vehicles capacity
	int C[V + 1];
	C[1] = Q;
	C[2] = Q;
	C[3] = Q;
	C[4] = Q;

	// array T_prime that encompasses the "normal" distance and the distance from/to the depot
	int T_prime[nb_total_nodes][nb_total_nodes];
	for (int i = 0; i < N; i++) {
		for (int j = 0; j < N; j++) {
			T_prime[i][j] = T[i][j];
		}
		for (int j = 0; j < V * 2; j++) {
			int position = N + j;
			T_prime[i][position] = T[i][0];
		}
	}
	// extra lines
	for (int i = N; i < nb_total_nodes; i++) {
		for (int j = 0; j < V * 2; j++) {
			int position = N + j;
			T_prime[i][position] = 0;
		}
		for (int j = 0; j < N; j++) {
			T_prime[i][j] = T[0][j];
		}
	}

	//Solution Collector
	SolutionCollector* const collector = solver.MakeBestValueSolutionCollector(false);

	// variables
	IntVar** s;		// list of successor for nodes 0..N+2V-1
	IntVar** s_first;	// list of successor for nodes 0..N+V-1
	IntVar** a;		// assignment
	IntVar** p;			// rank in trip
	IntVar* d;			// total distance
	IntVar** dp;		// distance between two successive node in a trip
	IntVar** q;			// quantite
	IntVar** y;			// branching variable
	IntVar** pred;		// list of predecessor for nodes 0..N+2V-1

	// constraint 1 and 2 definition of s
	s = solver.MakeIntVarArray(nb_total_nodes, -1, nb_total_nodes, "s");
	collector->Add(s[0]);
	// s[0] = -1
	Constraint* C1 = solver.MakeEquality(s[0], -1);
	solver.AddConstraint(C1);

	for (int i = 1; i < nb_total_nodes; ++i) {
		if (i < N + V) {
			Constraint* Ci = solver.MakeLessOrEqual(s[i], nb_total_nodes);
			solver.AddConstraint(Ci);
			Constraint* Cj = solver.MakeGreaterOrEqual(s[i], 1);
			solver.AddConstraint(Cj);
		} else {
			Constraint* C0 = solver.MakeEquality(s[i], 0);
			solver.AddConstraint(C0);
		}
		collector->Add(s[i]);
	}


	// definition of s_first
	s_first = solver.MakeIntVarArray(N + V, -1, nb_total_nodes, "s_first");
	Constraint* C0_s_first = solver.MakeEquality(s_first[0], -1);
	solver.AddConstraint(C0_s_first);
	for (int i = 1; i < N + V; i++) {
		Constraint* Cj_s_first = solver.MakeGreaterOrEqual(s_first[i], 1);
		solver.AddConstraint(Cj_s_first);

	}

	// constraint 3. definition of a
	a = solver.MakeIntVarArray(nb_total_nodes, 0, V, "a");
	collector->Add(a[0]);
	// a[0]=0
	Constraint* C0_a = solver.MakeEquality(a[0], 0);
	solver.AddConstraint(C0_a);
	for (int i = 1; i < nb_total_nodes; ++i) {
		Constraint* Cj_a_first = solver.MakeGreaterOrEqual(a[i], 1);
		solver.AddConstraint(Cj_a_first);
		collector->Add(a[i]);
	}

	// constraint 4. starting depot and ending depot are pre-assigned to vehicle
	for (int i = 1; i <= V; i++) {
		int position = N + i - 1; // vehicle i --> assign to starting depot number N + i - 1
		Constraint* Ci_a = solver.MakeEquality(a[position], i);
		solver.AddConstraint(Ci_a);

		position = N + i + V - 1; // vehicle i --> assign to ending depot number N + i + V - 1
		Constraint* Cj_a = solver.MakeEquality(a[position], i);
		solver.AddConstraint(Cj_a);
	}

	// constraint 5 : rank definition
	p = solver.MakeIntVarArray(nb_total_nodes, -1, nb_total_nodes, "p");
	Constraint* C0_p = solver.MakeEquality(p[0], -1);
	solver.AddConstraint(C0_p);
	collector->Add(p[0]);

	for (int i = 1; i < N; i++) {
		Constraint* Cj_p = solver.MakeGreaterOrEqual(p[i], 1);
		solver.AddConstraint(Cj_p);
		collector->Add(p[i]);
	}

	for (int i = N; i < N + V; i++) {
		Constraint* Cj_p = solver.MakeGreaterOrEqual(p[i], 0);
		solver.AddConstraint(Cj_p);
		collector->Add(p[i]);
	}

	for (int i = N + V; i < nb_total_nodes; i++) {
		Constraint* Cj_p = solver.MakeGreaterOrEqual(p[i], 1);
		solver.AddConstraint(Cj_p);
		collector->Add(p[i]);
	}

	// constraint 6 : starting depot have the rank equal to 0
	for (int i = 0; i < V; i++) {
		int position = N + i;
		Constraint* C0_p = solver.MakeEquality(p[position], 0);
		solver.AddConstraint(C0_p);
	}

	// constraint 7 : the successor are all different for s_first only (node 1 to N+V-1)
	std::vector<IntVar*> vars;
	for (int i = 1; i < N + V; i++) {
		vars.push_back(s[i]);
	}
	Constraint* C0_s = solver.MakeAllDifferent(vars);
	solver.AddConstraint(C0_s);

	// constraint 8. Node i and s_i have the same assignment ==>  a[ s[i] ] == a_i
	std::vector<IntVar*> vars_a;
	for (int i = 0; i < nb_total_nodes; i++) {
		vars_a.push_back(a[i]);
	}
	for (int i = 1; i < N + V; i++) {
		// deux sol similaires
		// sol 1.
		// IntExpr* t = solver.MakeElement(vars_a, s[i]);
		//Constraint *C0 = solver.MakeEquality(a[i], t);
		//solver.AddConstraint(C0);
		// sol 2
		Constraint* C0 = solver.MakeElementEquality(vars_a, s[i], a[i]);
		solver.AddConstraint(C0);
	}

	// constraint 9. s_i != i
	for (int i = 1; i < N + V; i++) {
		Constraint* C0 = solver.MakeNonEquality(s[i], i);
		solver.AddConstraint(C0);
	}

	// constraint 10. p[ s[i] ] = p[i] + 1 i.e. p[ s[i] ] =t
	std::vector<IntVar*> vars_p;
	for (int i = 0; i < nb_total_nodes; i++) {
		vars_p.push_back(p[i]);
	}
	for (int i = 1; i < N + V; i++) {
		IntVar* t = solver.MakeSum(p[i], 1)->Var();
		Constraint* C0 = solver.MakeElementEquality(vars_p, s[i], t);
		solver.AddConstraint(C0);
	}

	// constraint 11 : definition of q
	q = solver.MakeIntVarArray(nb_total_nodes, 0, Q, "q");
	Constraint* C0_q = solver.MakeEquality(q[0], 0);
	solver.AddConstraint(C0_q);

	for (int i = 1; i < nb_total_nodes; ++i) {
		if ((i >= N) && (i < N + V)) {// for a starting depot --> q_i = 0
			Constraint* Ci_p = solver.MakeEquality(q[i], 0);
			solver.AddConstraint(Ci_p);
		} else {
			Constraint* Cj_p = solver.MakeGreaterOrEqual(q[i], 0);
			solver.AddConstraint(Cj_p);
		}
	}

	// constraint 12
	// q [i] + D[ S[i] ] = q [ S[i] ]
	//   i.e. q [i] + u = t
	std::vector<IntVar*> vars_q;
	for (int i = 0; i < nb_total_nodes; i++) {
		vars_q.push_back(q[i]);
	}

	std::vector<int64> vars_D;
	for (int i = 0; i < nb_total_nodes; i++) {
		vars_D.push_back(D[i]);
	}

	for (int i = 1; i < N + V; i++) {
		// t = q [ S[i] ]
		IntExpr* t = solver.MakeElement(vars_q, s[i]);
		//D[ S[i] ] = u
		IntExpr* u = solver.MakeElement(vars_D, s[i]);
		// q[i] + u - t = 0
		IntExpr* somme = solver.MakeSum(q[i], u);
		Constraint* C0 = solver.MakeEquality(t, somme);
		solver.AddConstraint(C0);
	}

	// constraint 13. T = sum T_i, s_i
	// 13.1. dp_i definition
	dp = solver.MakeIntVarArray(nb_total_nodes, 0, H, "dp");
	Constraint* C0_dp = solver.MakeEquality(dp[0], 0);
	collector->Add(dp[0]);

	for (int i = 1; i < nb_total_nodes; ++i) {
		Constraint* Cj_dp = solver.MakeGreaterOrEqual(dp[i], 0);
		solver.AddConstraint(Cj_dp);
		collector->Add(dp[i]);
	}
	//13.2. definition of d
	d = solver.MakeIntVar(0, H, "d");

	// Note : we can  to help the solver...with d = solver.MakeIntVar(25, H, "d");
	//  since we know the optimal solution of this basic instance

	// 13.3
	// dp_i = T_i_s(i)
	for (int i = 1; i < nb_total_nodes; i++) {  //nb_total_nodes
		std::vector<int64> vars_Ti;

		for (int j = 0; j < nb_total_nodes; j++) {
			vars_Ti.push_back(T_prime[i][j]);
		}
		IntExpr* u = solver.MakeElement(vars_Ti, s[i]);
		//dp_i = T_i_s(i)
		Constraint* C0_u = solver.MakeEquality(dp[i], u);
		solver.AddConstraint(C0_u);
	}

	// constraint 14. d = sum dp_i
	std::vector<IntVar*> vars_somme;
	for (int i = 1; i < nb_total_nodes; i++) {
		vars_somme.push_back(dp[i]);
	}
	d = solver.MakeSum(vars_somme)->Var();

	// first improvement : break symetrie
	// S[i] < S[i+1] --> S[i] - S[i+1]  < 0
	for (int i = N; i < N + V - 1; ++i) {
		Constraint* C0 = solver.MakeLess(s[i], s[i + 1]);
		solver.AddConstraint(C0);
	}

	// second improvement :
	//  defined y_i = 100xa_i + s_i and branch on y_i

	y = solver.MakeIntVarArray(N, 0, V * 100 + N, "s");
	Constraint* C0_y = solver.MakeEquality(y[0], 0);
	solver.AddConstraint(C0_y);
	for (int i = 1; i < N; ++i) {
		IntExpr* somme = solver.MakeProd(a[i], 100);
		IntVar* somme2 = solver.MakeSum(somme, s[i])->Var();
		y[i] = somme2;
	}

	// third improvement : channeling... propagation in two directions

	// see this page
	// https://github.com/google/or-tools/blob/4a0e9b1860276a021335aacb8b69e10a0d08942c/ortools/sat/samples/channeling_sample_sat.cc
	// for a full description of channeling idea
	//
	//     S[i] =j <--> pred[j] = i
	//   
	// useful only for large instances and not for small scale instances
	//

	pred = solver.MakeIntVarArray(nb_total_nodes, 0, nb_total_nodes, "pred");
	// pred[0] = 0
	Constraint* Cp = solver.MakeEquality(pred[0], 0);
	solver.AddConstraint(Cp);

	for (int i = 1; i < nb_total_nodes; ++i) {
		if ((i >= N) && (i < N + V)) {
			pred[i] = solver.MakeIntVar(0, 0, "pred_" + i);
		} else {
			pred[i] = solver.MakeIntVar(1, nb_total_nodes, "pred_" + i);
		}
	}

	/* if we want to evaluate the optimal solution, add these lines */
	/*
	Constraint *a0 = solver.MakeEquality(s[0], -1);
	solver.AddConstraint(a0);
	Constraint *a10 = solver.MakeEquality(s[10], 1);
	solver.AddConstraint(a10);
	Constraint *a1 = solver.MakeEquality(s[1], 9);
	solver.AddConstraint(a1);
	Constraint *a9 = solver.MakeEquality(s[9], 6);
	solver.AddConstraint(a9);
	Constraint *a6 = solver.MakeEquality(s[6], 4);
	solver.AddConstraint(a6);
	Constraint *a4 = solver.MakeEquality(s[4], 14);
	solver.AddConstraint(a4);

	Constraint *a11 = solver.MakeEquality(s[11], 7);
	solver.AddConstraint(a11);
	Constraint *a7 = solver.MakeEquality(s[7], 2);
	solver.AddConstraint(a7);
	Constraint *a2 = solver.MakeEquality(s[2], 5);
	solver.AddConstraint(a2);
	Constraint *a5 = solver.MakeEquality(s[5], 15);
	solver.AddConstraint(a5);

	Constraint *a12 = solver.MakeEquality(s[12], 8);
	solver.AddConstraint(a12);
	Constraint *a8 = solver.MakeEquality(s[8], 3);
	solver.AddConstraint(a8);
	Constraint *a3 = solver.MakeEquality(s[3], 16);
	solver.AddConstraint(a3);

	Constraint *a14 = solver.MakeEquality(s[13], 17);
	solver.AddConstraint(a14);

	Constraint *aff0 = solver.MakeEquality(a[0], 0);
	solver.AddConstraint(aff0);
	Constraint *aff10 = solver.MakeEquality(a[10], 1);
	solver.AddConstraint(aff10);
	Constraint *aff1 = solver.MakeEquality(a[1], 1);
	solver.AddConstraint(aff1);
	Constraint *aff9 = solver.MakeEquality(a[9], 1);
	solver.AddConstraint(aff9);
	Constraint *aff6 = solver.MakeEquality(a[6], 1);
	solver.AddConstraint(aff6);
	Constraint *aff4 = solver.MakeEquality(a[4], 1);
	solver.AddConstraint(aff4);

	Constraint *aff11 = solver.MakeEquality(a[11], 2);
	solver.AddConstraint(aff11);
	Constraint *aff7 = solver.MakeEquality(a[7], 2);
	solver.AddConstraint(aff7);
	Constraint *aff2 = solver.MakeEquality(a[2], 2);
	solver.AddConstraint(aff2);
	Constraint *aff5 = solver.MakeEquality(a[5], 2);
	solver.AddConstraint(aff5);

	Constraint *aff12 = solver.MakeEquality(a[12], 3);
	solver.AddConstraint(aff12);
	Constraint *aff8 = solver.MakeEquality(a[8], 3);
	solver.AddConstraint(aff8);
	Constraint *aff3 = solver.MakeEquality(a[3], 3);
	solver.AddConstraint(aff3);

	*/

	// objective function
	OptimizeVar* const obj = solver.MakeMinimize(d, 1);
	collector->AddObjective(d);
	// define strategy
	//
	std::vector<IntVar*> vars_decision;
	for (int i = 1; i < N; i++) {
		vars_decision.push_back(y[i]);
	}
	DecisionBuilder* const db = solver.MakePhase(vars_decision,
		Solver::CHOOSE_FIRST_UNBOUND,
		Solver::ASSIGN_MIN_VALUE);

	solver.NewSearch(db, collector);

	int ancienne_val = H;
	solver.NextSolution();
	while (solver.NextSolution() == true) {
		int makespan = collector->objective_value(0);
		if (makespan < ancienne_val) {
			cout << "Cost " << collector->objective_value(0);
			std::cout << endl;
			int makespan = d->Value();
			std::cout << "Solution : " << makespan << endl;
			for (int j = 0; j < nb_total_nodes; j++) {
				cout << "    ";
				cout << j << "  s[" << j << "]= " << collector->Value(0, s[j]) << " ";
				cout << "    ";
				cout << "  a[" << j << "]= " << collector->Value(0, a[j]) << " ";
				cout << "    ";
				cout << "  p[" << j << "]= " << collector->Value(0, p[j]) << " ";

				if (j > 0) {
					cout << "    ";
					cout << "  dp[" << j << "]= " << collector->Value(0, dp[j]) << " ";
				}
				cout << endl;
			}
			cout << endl;
			ancienne_val = makespan;
		}
	}

	solver.EndSearch();

	cout << "Solve terminated " << endl;
	cout << "Cost " << collector->solution(0)->ObjectiveValue();
	std::cout << endl;
	int makespan = collector->objective_value(0);
	for (int j = 0; j < nb_total_nodes; j++) {
		cout << "    ";
		cout << j << "  s[" << j << "]= " << collector->solution(0)->Value(s[j]) << " ";
		cout << "    ";
		cout << "  a[" << j << "]= " << collector->solution(0)->Value(a[j]) << " ";
		cout << "    ";
		cout << "  p[" << j << "]= " << collector->solution(0)->Value(p[j]) << " ";

		if (j > 0) {
			cout << "    ";
			cout << "  dp[" << j << "]= " << collector->solution(0)->Value(dp[j]) << " ";
		}
		cout << endl;
	}
	cout << endl;

	// Statistics

	cout << "Solutions: " << solver.solutions() << endl;
	cout << "Failures: " << solver.failures() << endl;
	cout << "Branches: " << solver.branches() << endl;
	int duree = solver.wall_time();
	float duree_s = (float)duree / (float)1000;
	cout << "Wall time: " << duree_s << "s " << endl;
	cout << "Memory usage: " << Solver::MemoryUsage() << " bytes" << endl;
}

//-------------------------------------------------------------------------------//
//-------------------------------------------------------------------------------//
//-------------------------------------------------------------------------------//

int main(int argc, char** argv) {

	google::InitGoogleLogging(argv[0]);
	FLAGS_logtostderr = 1;

	cout << endl;
	cout << "Example of the VRP " << endl;
	VRP();

	int lu;
	cout << "presser 1";
	cin >> lu;

	return EXIT_SUCCESS;
}
