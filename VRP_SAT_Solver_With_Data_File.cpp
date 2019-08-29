
// Authors :	Ph. Lacomme (placomme@isima.fr)
//				Gwénaël Rault (gwenael.rault@mapotempo.com)
//
//
// Validation on Visual Studio 2017
//
//
// Show how to use the SAT solver for the VRP using the modelezation introduced in
//
// See :   "De la programmation linéaire à la programmation par contraites "
//         authors : Bourreau, Gondran, Lacomme, Vinot
//         Ed. Ellipses - ISBN-10 : 9782340-029460
//         Published : February 2019
// and
//         "Programmation par contraites : démarches de modélisation pour des problèmes d'optimisation "
//         authors : Bourreau, Gondran, Lacomme, Vinot
//         Ed. Ellipses 
//         Published : to appear in february 2020
//
// for efficient approaches description.
//

#include <iostream>
using namespace std;

#define _SECURE_SCL 0
#define _ALLOW_ITERATOR_DEBUG_LEVEL_MISMATCH
#define NOMINMAX

#define _SILENCE_CXX17_OLD_ALLOCATOR_MEMBERS_DEPRECATION_WARNING
#define _SILENCE_ALL_CXX17_DEPRECATION_WARNINGS


// solver PPC Sat
#include "ortools/sat/cp_model.h"
#include "ortools/util/sorted_interval_list.h"
#include "ortools/sat/sat_decision.h"

#include <cstdlib>
#include <sstream>
#include <fstream> 

using namespace operations_research;
using namespace sat;


const int Nmax = 200;				// maximal number of nodes
const int Vmax = 30;				// maximal number of vehicles

typedef struct t_instance {
	int N = -1;						// number of nodes
	int V = -1;						// number of vehicles
	int H = -1;						// upper bound of the distance
	int nb_total_nodes;				// total number of nodes including one depot per vehicle
	int Q = -1;                     // capacity of vehicle
	int T[Nmax][Nmax];
	int D[Nmax];
	int C[Vmax + 1];
	int T_prime[Nmax][Nmax];
}t_instance;

void lire_instance(string nom,
	t_instance &une_instance)
{
	std::ifstream f(nom.c_str());
	string ligne;

	getline(f, ligne);
	getline(f, ligne);
	getline(f, ligne);
	getline(f, ligne);
	getline(f, ligne);
	getline(f, ligne);

	f >> une_instance.N;
	une_instance.N++;
	f >> une_instance.V;
	f >> une_instance.Q;
	getline(f, ligne);
	getline(f, ligne);

	for (int i = 0; i < une_instance.N; i++) 
	{
		for (int j = 0; j < une_instance.N; j++)
		{
			int lu;
			f >> lu;
			une_instance.T[i][j] = lu;
		}
	}
	getline(f, ligne);
	getline(f, ligne);
	une_instance.D[0] = 0;
	for (int i = 1; i < une_instance.N; i++)
	{
		int lu;
		f >> lu;
		f >> lu;
		une_instance.D[i] = lu;
	}

	f.close();
}


void compute_values(t_instance &une_instance)
{
	une_instance.H = 10000;

	une_instance.nb_total_nodes = une_instance.N + une_instance.V * 2;
	for (int i = une_instance.N; i < une_instance.nb_total_nodes; i++) {
		une_instance.D[i] = 0;
	}
	for (int i=1; i<= une_instance.V; i++)
	  une_instance.C[i] = une_instance.Q;
	int &nb_total_nodes = une_instance.nb_total_nodes;
	int &N = une_instance.N;
	int &V = une_instance.V;

	// array T_prime that encompasses the "normal" distance and the distance from/to the depot
	for (int i = 0; i < N; i++) {
		for (int j = 0; j < N; j++) {
			une_instance.T_prime[i][j] = une_instance.T[i][j];
		}
		for (int j = 0; j < V * 2; j++) {
			int position = N + j;
			une_instance.T_prime[i][position] = une_instance.T[i][0];
		}
	}
	// extra lines
	for (int i = N; i < nb_total_nodes; i++) {
		for (int j = 0; j < V * 2; j++) {
			int position = N + j;
			une_instance.T_prime[i][position] = 0;
		}
		for (int j = 0; j < N; j++) {
			une_instance.T_prime[i][j] = une_instance.T[0][j];
		}
	}
}

void VRP_resolution(t_instance &une_instance)
{
	int &nb_total_nodes = une_instance.nb_total_nodes;
	int &N = une_instance.N;
	int &V = une_instance.V;
	int &H = une_instance.H;
	int &Q = une_instance.Q;

	CpModelBuilder cp_model;

	const Domain domain_successor(1, nb_total_nodes);
	const Domain domain_assignment(1, V);
	const Domain domain_rank(0, nb_total_nodes);
	const Domain domain_0(0, 0);
	const Domain domain_null(-1, -1);
	const Domain domain_N_1(1, N);
	const Domain domain_N_0(0, N);
	const Domain domain_N(1, N + 1);
	const Domain domain_distance(0, H);
	const Domain domain_volume(0, Q);
	const Domain domain_large(0, V * 100 + N);

	// variables
	std::vector<IntVar> s;		// list of successor for nodes 0..N+2V-1
	std::vector<IntVar> s_first; // list of successor for nodes 0..N+V-1
	std::vector<IntVar> a;		// assignment
	std::vector<IntVar> p;		// rank in trip 
	IntVar d;					// total distance
	std::vector<IntVar> dp;     // distance between two successive node in a trip
	std::vector<IntVar> q;      // quantite
	std::vector<IntVar> y;      // branching variable
	std::vector<IntVar> pred;	// list of predecessor for nodes 0..N+2V-1

	// constraint 1 and 2 definition of s

	s.push_back(
		cp_model.NewIntVar(domain_null).WithName(absl::StrCat("S_0"))
	);
	for (int i = 1; i < nb_total_nodes; ++i) {
		if (i < N + V)
		{
			s.push_back(
				cp_model.NewIntVar(domain_successor).WithName(absl::StrCat("S_", i))
			);
		}
		else
		{
			s.push_back(
				cp_model.NewIntVar(domain_0).WithName(absl::StrCat("S_", i))
			);
		}

	}

	// s_first = s limited to position 1...N+V-1
	s_first.push_back(
		cp_model.NewIntVar(domain_null).WithName(absl::StrCat("S_first_0"))
	);
	for (int i = 1; i < N + V; ++i) {
		s_first.push_back(
			cp_model.NewIntVar(domain_successor).WithName(absl::StrCat("S_first_", i))
		);
	}



	// constraint 3. definition of a

	a.push_back(
		cp_model.NewIntVar(domain_0).WithName(absl::StrCat("a_0"))
	);
	for (int i = 1; i < nb_total_nodes; ++i) {
		a.push_back(
			cp_model.NewIntVar(domain_assignment).WithName(absl::StrCat("a_", i))
		);
	}

	// constraint 4. starting depot and ending depot are pre-assigned to vehicle

	for (int i = 1; i <= V; i++) {
		int position = N + i - 1; // vehicle i --> assign to starting depot number N + i - 1
		cp_model.AddEquality({ a[position] }, i);
		position = N + i + V - 1; // vehicle i --> assign to ending depot number N + i + V - 1
		cp_model.AddEquality({ a[position] }, i);
	}


	// constraint 5 : rank definition

	p.push_back(
		cp_model.NewIntVar(domain_null).WithName(absl::StrCat("p_0"))
	);
	for (int i = 1; i < N; i++) {
		p.push_back(
			cp_model.NewIntVar(domain_N_1).WithName(absl::StrCat("p_", i))
		);
	}

	for (int i = N; i < N + V; i++) {
		p.push_back(
			cp_model.NewIntVar(domain_N_0).WithName(absl::StrCat("p_", i))
		);
	}

	for (int i = N + V; i < nb_total_nodes; i++) {
		p.push_back(
			cp_model.NewIntVar(domain_N_1).WithName(absl::StrCat("p_", i))
		);
	}

	// constraint 6 : starting depot have the rank equal to 0
	for (int i = 0; i < V; i++) {
		int position = N + i;
		cp_model.AddEquality({ p[position] }, 0);
	}


	// constraint 7 : the successor are all different for s_first only (node 1 to N+V-1)
	for (int i = 1; i < N + V; i++) {
		cp_model.AddEquality({ s[i] }, { s_first[i] });
	}
	cp_model.AddAllDifferent(s_first);

	// constraint 8. Node i and s_i have the same assignment ==>  a[ s[i] ] == a_i
	std::vector<IntVar> liste_var;
	for (int i = 0; i < nb_total_nodes; i++)
	{
		liste_var.push_back((IntVar)a[i]);
	}
	auto span_variables = absl::Span<const IntVar>(liste_var);

	for (int i = 1; i < N + V; i++) {
		cp_model.AddVariableElement(s[i], span_variables, a[i]);
	}


	// constraint 9. s_i != i
	for (int i = 1; i < N + V; i++) {
		cp_model.AddNotEqual({ s[i] }, i);
	}


	// constraint 10. p[ s[i] ] = p[i] + 1 i.e. p[ s[i] ] =t
	std::vector<IntVar> liste_var_p;
	for (int i = 0; i < nb_total_nodes; i++)
	{
		liste_var_p.push_back((IntVar)p[i]);
	}
	auto span_variables_p = absl::Span<const IntVar>(liste_var_p);


	for (int i = 1; i < N + V; i++) {
		// t = p[i] + 1
		IntVar t;
		t = cp_model.NewIntVar(domain_rank).WithName(absl::StrCat("t"));
		LinearExpr left_part = LinearExpr::ScalProd({ t, p[i] }, { 1, -1 });
		cp_model.AddEquality(left_part, 1);
		// p[s[i]] = t
		cp_model.AddVariableElement(s[i], span_variables_p, t);
	}


	// constraint 11 
	//   definition of q

	q.push_back(
		cp_model.NewIntVar(domain_null).WithName(absl::StrCat("q_0"))
	);
	for (int i = 1; i < nb_total_nodes; ++i) {
		if ((i >= N) && (i < N + V)) // for a starting depot --> q_i = 0
		{
			q.push_back(
				cp_model.NewIntVar(domain_0).WithName(absl::StrCat("q_", i))
			);
		}
		else
		{
			q.push_back(
				cp_model.NewIntVar(domain_volume).WithName(absl::StrCat("q_", i))
			);
		}
	}



	// constraint 12
	//
	// q [i] + D[ S[i] ] = q [ S[i] ]
	//   i.e. q [i] + u = t

	std::vector<IntVar> liste_var_q;
	for (int i = 0; i < nb_total_nodes; i++)
	{
		liste_var_q.push_back((IntVar)q[i]);
	}
	auto span_variables_q = absl::Span<const IntVar>(liste_var_q);

	std::vector<int64> liste_coeff_D;
	for (int i = 0; i < nb_total_nodes; i++)
	{
		liste_coeff_D.push_back((int64)une_instance.D[i]);
	}
	auto span_coeff_D = absl::Span<const int64>(liste_coeff_D);

	for (int i = 1; i < N + V; i++) {
		// t = q [ S[i] ]
		IntVar t;
		t = cp_model.NewIntVar(domain_volume).WithName(absl::StrCat("t"));
		cp_model.AddVariableElement(s[i], span_variables_q, t);

		//D[ S[i] ] = u
		IntVar u;
		u = cp_model.NewIntVar(domain_volume).WithName(absl::StrCat("u"));
		cp_model.AddElement(s[i], span_coeff_D, u);

		// q[i] + u - t = 0
		LinearExpr partie_gauche = LinearExpr::ScalProd({ q[i], u, t }, { 1, 1, -1 });
		cp_model.AddEquality(partie_gauche, 0);

	}


	// constraint 13. T = sum T_i, s_i
	// 13.1

	dp.push_back(
		cp_model.NewIntVar(domain_0).WithName(absl::StrCat("dp_", 0))
	);
	for (int i = 1; i < nb_total_nodes; ++i) {
		dp.push_back(
			cp_model.NewIntVar(domain_distance).WithName(absl::StrCat("dp_", i))
		);
	}

	//13.2
	d = cp_model.NewIntVar(domain_distance).WithName(absl::StrCat("d"));
	// 13.3
	// dp_i = T_i_s(i)
	for (int i = 1; i < nb_total_nodes; i++) {  //nb_total_nodes
		std::vector<int64> liste_coeffs;
		int64 v = 0;
		liste_coeffs.push_back((int64)v);

		for (int j = 1; j < nb_total_nodes; j++)
		{
			liste_coeffs.push_back((int64)une_instance.T_prime[i][j]);
		}
		auto span_coefficient = absl::Span<const int64>(liste_coeffs);
		cp_model.AddElement(s[i], span_coefficient, dp[i]);
	}

	// constraint 14. d = sum dp_i
	std::vector<IntVar> liste_variables;
	std::vector<int64> liste_coeffs;

	for (int i = 1; i < nb_total_nodes; ++i) {
		liste_variables.push_back(dp[i]);
		liste_coeffs.push_back(1);
	}
	liste_variables.push_back(d);
	liste_coeffs.push_back(-1);

	auto span_variable = absl::Span<const IntVar>(liste_variables);
	auto span_coefficient = absl::Span<const int64>(liste_coeffs);
	LinearExpr Left_Part = LinearExpr::ScalProd(span_variable, span_coefficient);
	cp_model.AddEquality(Left_Part, 0);

	// first improvement : break symetrie
	// S[i] < S[i+1] --> S[i] - S[i+1]  < 0
	for (int i = N; i < N + V - 1; ++i) {
		LinearExpr partie_gauche = LinearExpr::ScalProd({ s[i], s[i + 1] }, { 1, -1 });
		cp_model.AddLessThan(partie_gauche, 0);
	}

	// second improvement : 
	//  defined y_i = 100xa_i + s_i and branch on y_i

	y.push_back(
		cp_model.NewIntVar(domain_0).WithName(absl::StrCat("y_", 0))
	);
	for (int i = 1; i < N; ++i) {
		y.push_back(
			cp_model.NewIntVar(domain_large).WithName(absl::StrCat("y_", i))
		);
		LinearExpr ai_si = LinearExpr::ScalProd({ a[i], s[i] }, { 100, 1 });
		cp_model.AddEquality({ y[i] }, { ai_si });
	}

	// definition of the strategy
	cp_model.AddDecisionStrategy(y, DecisionStrategyProto::CHOOSE_FIRST,
		DecisionStrategyProto::SELECT_MIN_VALUE
	);

	// third improvement : channeling... propagation in two directions

	// see this page
	// https://github.com/google/or-tools/blob/4a0e9b1860276a021335aacb8b69e10a0d08942c/ortools/sat/samples/channeling_sample_sat.cc
	// for a full description of channeling idea
	//
	//     S[i] =j <--> pred[j] = i
	//    
	// useful only for large instances and not for small scale instances
	//

	pred.push_back(
		cp_model.NewIntVar(domain_null).WithName(absl::StrCat("pred_0"))
	);
	for (int i = 1; i < nb_total_nodes; ++i) {
		if ((i >= N) && (i < N + V))
		{
			pred.push_back(
				cp_model.NewIntVar(domain_0).WithName(absl::StrCat("pred_", i))
			);
		}
		else
		{
			pred.push_back(
				cp_model.NewIntVar(domain_successor).WithName(absl::StrCat("pred_", i))
			);
		}

	}


	std::vector<IntVar> liste_var_suiv;
	for (int i = 0; i < nb_total_nodes; i++)
	{
		liste_var_suiv.push_back((IntVar)s[i]);
	}
	auto span_variables_suiv = absl::Span<const IntVar>(liste_var_suiv);

	std::vector<IntVar> liste_var_pred;
	for (int i = 0; i < nb_total_nodes; i++)
	{
		liste_var_pred.push_back((IntVar)pred[i]);
	}
	auto span_variables_pred = absl::Span<const IntVar>(liste_var_pred);

	for (int i = 1; i < N + V; i++) {
		IntVar suiv;
		suiv = cp_model.NewIntVar(domain_successor).WithName(absl::StrCat("suiv"));
		IntVar cour;
		const Domain domain_i(i, i);
		cour = cp_model.NewIntVar(domain_i).WithName(absl::StrCat("cour"));

		// suiv = s[cour]
		cp_model.AddVariableElement(cour, span_variables_suiv, suiv);

		// pred[suiv] = cour
		cp_model.AddVariableElement(suiv, span_variables_pred, cour);
	}

	

	/* Solution of cost 1200 provided by the CP routing library
	cp_model.AddEquality(s[41], 3);
	cp_model.AddEquality(s[3], 4);
	cp_model.AddEquality(s[4], 6);
	cp_model.AddEquality(s[6], 51);

	cp_model.AddEquality(s[42], 7);
	cp_model.AddEquality(s[7], 27);
	cp_model.AddEquality(s[27], 36);
	cp_model.AddEquality(s[36], 29);
	cp_model.AddEquality(s[29], 52);
	
	cp_model.AddEquality(s[43], 23);
	cp_model.AddEquality(s[23], 25);
	cp_model.AddEquality(s[25], 30);
	cp_model.AddEquality(s[30], 8);
	cp_model.AddEquality(s[8], 11);
	cp_model.AddEquality(s[11], 28);
	cp_model.AddEquality(s[28], 53);
	

	cp_model.AddEquality(s[44], 24);
	cp_model.AddEquality(s[24], 1);
	cp_model.AddEquality(s[1], 31);
	cp_model.AddEquality(s[31], 13);
	cp_model.AddEquality(s[13], 54);


	
	cp_model.AddEquality(s[45], 32);
	cp_model.AddEquality(s[32], 26);
	cp_model.AddEquality(s[26], 40);
	cp_model.AddEquality(s[40], 14);
	cp_model.AddEquality(s[14], 15);
	cp_model.AddEquality(s[15], 10);
	cp_model.AddEquality(s[10], 20); 
	cp_model.AddEquality(s[20], 9);
	cp_model.AddEquality(s[9], 19);
	cp_model.AddEquality(s[19], 55);
	
	cp_model.AddEquality(s[46], 35);
	cp_model.AddEquality(s[35], 34);
	cp_model.AddEquality(s[34], 56);

	cp_model.AddEquality(s[47], 38);
	cp_model.AddEquality(s[38], 17);
	cp_model.AddEquality(s[17], 5);
	cp_model.AddEquality(s[5], 22);
	cp_model.AddEquality(s[22], 37);
	cp_model.AddEquality(s[37], 12);
	cp_model.AddEquality(s[12], 16);
	cp_model.AddEquality(s[16], 21);
	cp_model.AddEquality(s[21], 2);
	cp_model.AddEquality(s[2], 57);

	cp_model.AddEquality(s[48], 39);
	cp_model.AddEquality(s[39], 18);
	cp_model.AddEquality(s[18], 33);
	cp_model.AddEquality(s[33], 58);
	
	*/


	//cp_model.AddLessOrEqual(d, 556);
	// objective
	cp_model.Minimize(d);

	Model model;

	// Sets a time limit of 10 seconds.
	SatParameters parameters;
	parameters.set_max_time_in_seconds(300);

	model.Add(NewSatParameters(parameters));

	// to display all solution that improve the best known solution

	model.Add(NewFeasibleSolutionObserver([&](const CpSolverResponse& r) {
		float CPU_Time = r.deterministic_time();
		cout << CPU_Time << " : Best solution found =" << SolutionIntegerValue(r, d) << endl;
		}
	)
	);


	const CpSolverResponse response = SolveCpModel(cp_model.Build(), &model);



	if (response.status() == CpSolverStatus::OPTIMAL)
	{
		cout << "Optimal solution found..." << endl << endl;
		cout << "information on the search..." << endl << endl;
		std::cout << CpSolverResponseStats(response) << std::endl;

		const int64 makespan = SolutionIntegerValue(response, d);
		cout << endl;
		cout << "Makespan = " << makespan << endl;

		for (int i = 1; i < nb_total_nodes; i++)
		{
			const int64 s_val = SolutionIntegerValue(response, s[i]);
			const int64 dp_val = SolutionIntegerValue(response, dp[i]);
			const int64 p_val = SolutionIntegerValue(response, p[i]);
			const int64 a_val = SolutionIntegerValue(response, a[i]);
			const int64 q_val = SolutionIntegerValue(response, q[i]);

			stringstream ss;
			ss << i << " :     s_val= " << s_val << " dp_val= " << dp_val << "  p_val = " << p_val << " a_val= " << a_val << " q_val= " << q_val << endl;
			cout << ss.str();
		}
		cout << endl;
	}
	else
		if (response.status() == CpSolverStatus::FEASIBLE)
		{
			cout << "solution found..." << endl << endl;
			cout << "information on the search..." << endl << endl;
			std::cout << CpSolverResponseStats(response) << std::endl;

			const int64 makespan = SolutionIntegerValue(response, d);
			cout << endl;
			cout << "Makespan = " << makespan << endl;

			for (int i = 1; i < nb_total_nodes; i++)
			{
				const int64 s_val = SolutionIntegerValue(response, s[i]);
				const int64 dp_val = SolutionIntegerValue(response, dp[i]);
				const int64 p_val = SolutionIntegerValue(response, p[i]);
				const int64 a_val = SolutionIntegerValue(response, a[i]);
				const int64 q_val = SolutionIntegerValue(response, q[i]);

				stringstream ss;
				ss << i << " :     s_val= " << s_val << " dp_val= " << dp_val << "  p_val = " << p_val << " a_val= " << a_val << " q_val= " << q_val << endl;
				cout << ss.str();
			}
			cout << endl;
		}
	else
		cout << "sorry, no optimal solution found" << endl;

}


//************************************************//
void VRP()
{


	const int N = 10;						// number of nodes
	const int V = 4;						// number of vehicles
	const int H = 100;						// upper bound of the distance
	const int nb_total_nodes = N + V * 2;	// total number of nodes including one depot per vehicle
	const int Q = 10;                       // identical vehicle of capacity 10

	CpModelBuilder cp_model;

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

	const Domain domain_successor(1, nb_total_nodes);
	const Domain domain_assignment(1, V);
	const Domain domain_rank(0, nb_total_nodes);
	const Domain domain_0(0, 0);
	const Domain domain_null(-1, -1);
	const Domain domain_N_1(1, N);
	const Domain domain_N_0(0, N);
	const Domain domain_N(1, N+1);
	const Domain domain_distance(0, H);
	const Domain domain_volume(0, Q);
	const Domain domain_large(0, V * 100 + N);

	// variables
	std::vector<IntVar> s;		// list of successor for nodes 0..N+2V-1
	std::vector<IntVar> s_first; // list of successor for nodes 0..N+V-1
	std::vector<IntVar> a;		// assignment
	std::vector<IntVar> p;		// rank in trip 
	IntVar d;					// total distance
	std::vector<IntVar> dp;     // distance between two successive node in a trip
	std::vector<IntVar> q;      // quantite
	std::vector<IntVar> y;      // branching variable
	std::vector<IntVar> pred;	// list of predecessor for nodes 0..N+2V-1

	// constraint 1 and 2 definition of s
	
	s.push_back(
		cp_model.NewIntVar(domain_null).WithName(absl::StrCat("S_0"))
	);
	for (int i = 1; i < nb_total_nodes; ++i) {
		if (i < N + V)
		{
			s.push_back(
				cp_model.NewIntVar(domain_successor).WithName(absl::StrCat("S_", i))
			);
		}
		else
		{
			s.push_back(
				cp_model.NewIntVar(domain_0).WithName(absl::StrCat("S_", i))
			);
		}

	}

	// s_first = s limited to position 1...N+V-1
	s_first.push_back(
		cp_model.NewIntVar(domain_null).WithName(absl::StrCat("S_first_0"))
	);
	for (int i = 1; i < N + V; ++i) {
		s_first.push_back(
				cp_model.NewIntVar(domain_successor).WithName(absl::StrCat("S_first_", i))
			);
	}



	// constraint 3. definition of a
	
	a.push_back(
		cp_model.NewIntVar(domain_0).WithName(absl::StrCat("a_0"))
	);
	for (int i = 1; i < nb_total_nodes; ++i) {
		a.push_back(
			cp_model.NewIntVar(domain_assignment).WithName(absl::StrCat("a_", i))
		);
	}
	
	// constraint 4. starting depot and ending depot are pre-assigned to vehicle
	
	 for (int i = 1; i <= V; i++) {
		int position = N + i - 1; // vehicle i --> assign to starting depot number N + i - 1
		cp_model.AddEquality({ a[position] }, i);
		position = N + i + V - 1; // vehicle i --> assign to ending depot number N + i + V - 1
		cp_model.AddEquality({ a[position] }, i);
	}
	

	// constraint 5 : rank definition
	
	p.push_back(
		cp_model.NewIntVar(domain_null).WithName(absl::StrCat("p_0"))
	);
	for (int i = 1; i < N; i++) {
		p.push_back(
			cp_model.NewIntVar(domain_N_1).WithName(absl::StrCat("p_", i))
		);
	}

	for (int i = N ; i < N+V; i++) {
		p.push_back(
			cp_model.NewIntVar(domain_N_0).WithName(absl::StrCat("p_", i))
		);
	}

	for (int i = N + V; i < nb_total_nodes; i++) {
		p.push_back(
			cp_model.NewIntVar(domain_N_1).WithName(absl::StrCat("p_", i))
		);
	}

	// constraint 6 : starting depot have the rank equal to 0
	 for (int i = 0; i < V; i++) {
		int position = N + i;
		cp_model.AddEquality({ p[position] }, 0);
	}
	

	// constraint 7 : the successor are all different for s_first only (node 1 to N+V-1)
	 for (int i = 1; i < N+V; i++) {
		 cp_model.AddEquality({ s[i] }, { s_first[i] });
	 }
	 cp_model.AddAllDifferent(s_first);

	// constraint 8. Node i and s_i have the same assignment ==>  a[ s[i] ] == a_i
	 std::vector<IntVar> liste_var;
	 for (int i = 0; i < nb_total_nodes; i++)
	 {
		 liste_var.push_back((IntVar)a[i]);
	 }
	 auto span_variables = absl::Span<const IntVar>(liste_var);

	for (int i = 1; i < N+V; i++) {
		cp_model.AddVariableElement(s[i], span_variables, a[i]);
	} 


	// constraint 9. s_i != i
	 for (int i = 1; i < N + V; i++) {
		cp_model.AddNotEqual({ s[i] }, i);
	}
	

	// constraint 10. p[ s[i] ] = p[i] + 1 i.e. p[ s[i] ] =t
	 std::vector<IntVar> liste_var_p;
	 for (int i = 0; i < nb_total_nodes; i++)
	 {
		 liste_var_p.push_back((IntVar)p[i]);
	 }
	 auto span_variables_p = absl::Span<const IntVar>(liste_var_p);


	for (int i = 1; i < N + V; i++) {
		// t = p[i] + 1
		IntVar t;
		t = cp_model.NewIntVar(domain_rank).WithName(absl::StrCat("t"));
		LinearExpr left_part = LinearExpr::ScalProd({ t, p[i] }, { 1, -1 });
		cp_model.AddEquality(left_part, 1);
		// p[s[i]] = t
		cp_model.AddVariableElement(s[i], span_variables_p, t);
	}
	

	// constraint 11 
	//   definition of q
	 
	q.push_back(
		cp_model.NewIntVar(domain_null).WithName(absl::StrCat("q_0"))
	);
	for (int i = 1; i < nb_total_nodes; ++i) {
		if ((i >= N) && (i < N + V)) // for a starting depot --> q_i = 0
		{
			q.push_back(
				cp_model.NewIntVar(domain_0).WithName(absl::StrCat("q_", i))
			);
		}
		else
		{
			q.push_back(
				cp_model.NewIntVar(domain_volume).WithName(absl::StrCat("q_", i))
			);
		}
	}



	// constraint 12
	//
	// q [i] + D[ S[i] ] = q [ S[i] ]
	//   i.e. q [i] + u = t

	std::vector<IntVar> liste_var_q;
	for (int i = 0; i < nb_total_nodes; i++)
	{
		liste_var_q.push_back((IntVar)q[i]);
	}
	auto span_variables_q = absl::Span<const IntVar>(liste_var_q);

	std::vector<int64> liste_coeff_D;
	for (int i = 0; i < nb_total_nodes; i++)
	{
		liste_coeff_D.push_back((int64)D[i]);
	}
	auto span_coeff_D = absl::Span<const int64>(liste_coeff_D);

	for (int i = 1; i< N+V; i++) {
		// t = q [ S[i] ]
		IntVar t;
		t = cp_model.NewIntVar(domain_volume).WithName(absl::StrCat("t"));
		cp_model.AddVariableElement(s[i], span_variables_q, t);

		//D[ S[i] ] = u
		IntVar u;
		u = cp_model.NewIntVar(domain_volume).WithName(absl::StrCat("u"));
		cp_model.AddElement(s[i], span_coeff_D, u);

		// q[i] + u - t = 0
		LinearExpr partie_gauche = LinearExpr::ScalProd({ q[i], u, t }, { 1, 1, -1 });
		cp_model.AddEquality(partie_gauche, 0);

	}
	

	// constraint 13. T = sum T_i, s_i
	// 13.1
	
	dp.push_back(
		cp_model.NewIntVar(domain_0).WithName(absl::StrCat("dp_", 0))
	);
	for (int i = 1; i < nb_total_nodes; ++i) {
		dp.push_back(
			cp_model.NewIntVar(domain_distance).WithName(absl::StrCat("dp_", i))
		);
	}
	
	//13.2
	d = cp_model.NewIntVar(domain_distance).WithName(absl::StrCat("d"));
	// 13.3
	// dp_i = T_i_s(i)
	for (int i = 1; i < nb_total_nodes; i++) {  //nb_total_nodes
		std::vector<int64> liste_coeffs;
		int64 v = 0;
		liste_coeffs.push_back((int64)v);

		for (int j = 1; j < nb_total_nodes; j++)
		{
			liste_coeffs.push_back((int64)T_prime[i][j]);
		}
		auto span_coefficient = absl::Span<const int64>(liste_coeffs);
		cp_model.AddElement(s[i], span_coefficient, dp[i]);
	}
	
	// constraint 14. d = sum dp_i
	std::vector<IntVar> liste_variables;
	std::vector<int64> liste_coeffs;

	for (int i = 1; i < nb_total_nodes; ++i) {
		liste_variables.push_back(dp[i]);
		liste_coeffs.push_back(1);
	}
	liste_variables.push_back(d);
	liste_coeffs.push_back(-1);

	auto span_variable = absl::Span<const IntVar>(liste_variables);
	auto span_coefficient = absl::Span<const int64>(liste_coeffs);
	LinearExpr Left_Part = LinearExpr::ScalProd(span_variable, span_coefficient);
	cp_model.AddEquality(Left_Part, 0);
	
	// first improvement : break symetrie
	// S[i] < S[i+1] --> S[i] - S[i+1]  < 0
	for (int i = N; i < N+V-1; ++i) {
		LinearExpr partie_gauche = LinearExpr::ScalProd({ s[i], s[i+1]}, { 1, -1 });
		cp_model.AddLessThan(partie_gauche, 0);
	}
	
	// second improvement : 
	//  defined y_i = 100xa_i + s_i and branch on y_i

	y.push_back(
		cp_model.NewIntVar(domain_0).WithName(absl::StrCat("y_", 0))
	);
	for (int i = 1; i < N; ++i) {
		y.push_back(
			cp_model.NewIntVar(domain_large).WithName(absl::StrCat("y_", i))
		);
		LinearExpr ai_si = LinearExpr::ScalProd({ a[i], s[i] }, { 100, 1 });
		cp_model.AddEquality({ y[i] }, { ai_si });
	}

	// definition of the strategy
	cp_model.AddDecisionStrategy(	y, DecisionStrategyProto::CHOOSE_FIRST,
									DecisionStrategyProto::SELECT_MIN_VALUE
								);
	
	// third improvement : channeling... propagation in two directions

	// see this page
    // https://github.com/google/or-tools/blob/4a0e9b1860276a021335aacb8b69e10a0d08942c/ortools/sat/samples/channeling_sample_sat.cc
	// for a full description of channeling idea
	//
	//     S[i] =j <--> pred[j] = i
	//    
	// useful only for large instances and not for small scale instances
	//

	pred.push_back(
		cp_model.NewIntVar(domain_null).WithName(absl::StrCat("pred_0"))
	);
	for (int i = 1; i < nb_total_nodes; ++i) {
		if ( (i>=N) && (i < N + V) )
		{
			pred.push_back(
				cp_model.NewIntVar(domain_0).WithName(absl::StrCat("pred_", i))
			);
		}
		else
		{
			pred.push_back(
				cp_model.NewIntVar(domain_successor).WithName(absl::StrCat("pred_", i))
			);
		}

	}


	std::vector<IntVar> liste_var_suiv;
	for (int i = 0; i < nb_total_nodes; i++)
	{
		liste_var_suiv.push_back((IntVar)s[i]);
	}
	auto span_variables_suiv = absl::Span<const IntVar>(liste_var_suiv);

	std::vector<IntVar> liste_var_pred;
	for (int i = 0; i < nb_total_nodes; i++)
	{
		liste_var_pred.push_back((IntVar)pred[i]);
	}
	auto span_variables_pred = absl::Span<const IntVar>(liste_var_pred);

	for (int i = 1; i < N+V; i++) {
		IntVar suiv;
		suiv = cp_model.NewIntVar(domain_successor).WithName(absl::StrCat("suiv"));
		IntVar cour;
		const Domain domain_i(i, i);
		cour = cp_model.NewIntVar(domain_i).WithName(absl::StrCat("cour"));

		// suiv = s[cour]
		cp_model.AddVariableElement(cour, span_variables_suiv, suiv);

		// pred[suiv] = cour
		cp_model.AddVariableElement(suiv, span_variables_pred, cour);
	}



	// objective
	cp_model.Minimize(d);

	Model model;

	// Sets a time limit of 10 seconds.
	SatParameters parameters;
	parameters.set_max_time_in_seconds(10.0);
	
	model.Add(NewSatParameters(parameters));

	// to display all solution that improve the best known solution

	model.Add(	NewFeasibleSolutionObserver(	[&](const CpSolverResponse& r) {
													float CPU_Time = r.deterministic_time();
													cout << CPU_Time << " : Best solution found =" << SolutionIntegerValue(r, d) << endl;
												}
											)
	);


	const CpSolverResponse response = SolveCpModel(cp_model.Build(), &model);



	if (response.status() == CpSolverStatus::OPTIMAL)
	{
		cout << "solution found..." << endl << endl;
		cout << "information on the search..." << endl << endl;
		std::cout << CpSolverResponseStats(response) << std::endl;

		const int64 makespan = SolutionIntegerValue(response, d);
		cout << endl;
		cout << "Makespan = " << makespan << endl;

		for (int i = 1; i < nb_total_nodes; i++)
		{
			const int64 s_val = SolutionIntegerValue(response, s[i]);
			const int64 dp_val = SolutionIntegerValue(response, dp[i]);
			const int64 p_val = SolutionIntegerValue(response, p[i]);
			const int64 a_val = SolutionIntegerValue(response, a[i]);
			const int64 q_val = SolutionIntegerValue(response, q[i]);

			stringstream ss;
			ss << i << " :     s_val= " << s_val << " dp_val= " << dp_val << "  p_val = " << p_val << " a_val= " << a_val << " q_val= " << q_val << endl;
			cout << ss.str();
		}
		cout << endl;
	}
	else
		cout << "sorry, no optimal solution found" << endl;

}




//-------------------------------------------------------------------------------//
//-------------------------------------------------------------------------------//
//-------------------------------------------------------------------------------//
//
// model performances for the widget instance
//
// Machine used for benchmark :  Xeon E5-1630 3.70Ghz with 32 GO of memory (Windows 7 OS)
//
// with no improvement : solved to optimality in 10 s
// with improvement 1 : solved to optimality in 5 s
// with improvement 1 + 2 : solved to optimality in 1.55 s 
// with improvement 1 + 2 + 3 : solved to optimality in 1.78 s 
//
// for the DLP_01.txt instance with a maximal computation time of 600s
//
// CpSolverResponse:
// status: FEASIBLE
// objective: 556
// best_bound: 338
// booleans: 554425
// conflicts: 230580
// branches: 582717
// propagations: 3910598662
// integer_propagations: 532700850
// walltime: 600.057
// usertime: 600.057
// deterministic_time: 713.721
// 
// 
//------------------------------------------------------------------------

int main(int argc, char** argv) {

	cout << "VRP resolution of a widget" << endl;

	VRP();




	t_instance une_instance;
	lire_instance("..\\Instances\\DLP_01.txt", une_instance);
	compute_values(une_instance);

	cout << "VRP resolution on one instance with 41 nodes" << endl;

	VRP_resolution(une_instance);

	int lu;
	cout << "presser 1";
	cin >> lu;


	return EXIT_SUCCESS;
}
