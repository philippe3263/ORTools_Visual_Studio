
// Authors : Ph. Lacomme (placomme@isima.fr)
//
// Date : 2019, august 11th - wenesday
//
// Validation on Visual Studio 2017
//
//
// Show how to use the SAT solver for the Job-Shop
//
//
// Note: this is a formulation based on the Cumulative global constraint and non overlap constraint
// that is not the best approach indeed but an acceptable one....
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
//
// with a  Xeon E5-1630 3.70Ghz with 32 GO of memory (Windows 7 OS)
// the following high quality results are obtained with this formulation
// 
// -------------------------------------- -
// | Int | LB | BF | Opt | User Time |
// -------------------------------------- -
// | la01 | 666 | 666 | *| 0.194011  |
// | la02 | 655 | 655 | *| 0.0450025 |
// | la03 | 597 | 597 | *| 0.0950054 |
// | la04 | 590 | 590 | *| 0.119007  |
// | la05 | 593 | 593 | *| 0.0343419 |
// | la06 | 926 | 926 | *| 0.53877   |
// | la07 | 890 | 890 | *| 0.127967  |
// | la08 | 863 | 863 | *| 0.185568  |
// | la09 | 951 | 951 | *| 0.148624  |
// | la10 | 958 | 958 | *| 0.236286  |
// | la11 | 1222 | 1222 | *| 0.140723  |
// | la12 | 1039 | 1039 | *| 0.619397  |
// | la13 | 1150 | 1150 | *| 0.311179  |
// | la14 | 1292 | 1292 | *| 1.86133   |
// | la15 | 1207 | 1207 | *| 1.52313   |
// | la16 | 945 | 945 | *| 0.186183  |
// | la17 | 784 | 784 | *| 0.222295  |
// | la18 | 848 | 848 | *| 0.573652  |
// | la19 | 842 | 842 | *| 1.20389   |
// | la20 | 902 | 902 | *| 0.478844  |
// | la21 | 1046 | 1046 | *| 76.2214   |
// | la22 | 927 | 927 | *| 4.37004   |
// | la23 | 1032 | 1032 | *| 1.62997   |
// | la24 | 935 | 935 | *| 27.613    |
// | la25 | 977 | 977 | *| 13.6576   |
// | la26 | 1218 | 1218 | *| 18.9807   |
// | la27 | 1235 | 1240 |   | 120.003   |
// | la28 | 1216 | 1216 | *| 10.7508   |
// | la29 | 1152 | 1177 |   | 120.004   |
// | la30 | 1355 | 1355 | *| 4.52326   |
// | la31 | 1784 | 1784 | *| 35.5261   |
// | la32 | 1850 | 1853 |   | 120.005   |
// | la33 | 1719 | 1719 | *| 21.5469   |
// | la34 | 1721 | 1721 | *| 56.5498   |
// | la35 | 1888 | 1888 | *| 23.7264   |
// | la36 | 1268 | 1268 | *| 9.53905   |
// | la37 | 1397 | 1397 | *| 6.0415    |
// | la38 | 1196 | 1196 | *| 113.654   |
// | la39 | 1233 | 1233 | *| 4.62964   |
// | la40 | 1222 | 1222 | *| 25.363 |
// ---------------------------------------
//
// test40 : instance LA040
// -----------------------
// CpSolverResponse:
// status: OPTIMAL
// objective: 1222
// best_bound: 1222
// booleans: 6068
// conflicts: 30281
// branches: 104822
// propagations: 13943778
// integer_propagations: 25454243
// walltime: 23.7522
// usertime: 23.7522
// deterministic_time: 2.0248
// 
// Optimal solution found...
// Makespan = 1222


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
#include <cstdlib>
#include <sstream>
#include <fstream> 

using namespace operations_research;
using namespace sat;
    
    // to avoid dynamic memory allocation
    //
    const int nmax = 50; //50 jobs max
	const int mmax = 50; //50 machine max

	typedef struct t_instance {
		string nom;
		int n;            // number of jobs
		int m;            // number of machines
		int h;            // maximal lenght of the planning (upper bound of the solution)
		int BKS;				// lower bound (most of the time LB = optimal solution)
		int M[nmax][mmax];		// machine
		int P[nmax][mmax];		// processing times
		int Tab[nmax][mmax];	// ref.
	}t_instance;

	
	void lire_instance(	string nom, 
						t_instance &une_instance)
	{
		std::ifstream f(nom.c_str());
		string ligne;
		
		//getline(f, ligne);
		//cout << ligne << endl;

		f >> une_instance.n;
		f >> une_instance.m;
		f >> une_instance.BKS;
		int k = 0;

		for (int i = 1; i <= une_instance.n; i++)
		{
			for (int j = 1; j <= une_instance.m; j++)
			{
				int machine;
				int duree;
				f >> machine;
				f >> duree;
				une_instance.M[i-1][j-1] = machine;
				une_instance.P[i - 1][j - 1] = duree;
				une_instance.Tab[i - 1][j - 1] = k;
				k++;
			}
		}
		f.close();
	}

	
	void instance_widget(t_instance &une_instance)
	{
		une_instance.n = 3;             // number of jobs
		une_instance.m = 3;             // number of machines
		une_instance.h = 68;            // maximal lenght of the planning (upper bound of the solution)
		une_instance.BKS = 0;            // lower bound

		//  data
		une_instance.M[0][0] = 1;		une_instance.M[0][1] = 2;		une_instance.M[0][2] = 3;
		une_instance.M[1][0] = 2;		une_instance.M[1][1] = 3;		une_instance.M[1][2] = 1;
		une_instance.M[2][0] = 3;		une_instance.M[2][1] = 1;		une_instance.M[2][2] = 2;

		une_instance.P[0][0] = 10;		une_instance.P[0][1] = 20;		une_instance.P[0][2] = 30;
		une_instance.P[1][0] = 5; 		une_instance.P[1][1] = 4;		une_instance.P[1][2] = 10;
		une_instance.P[2][0] = 12;		une_instance.P[2][1] = 7;		une_instance.P[2][2] = 4;

		une_instance.Tab[0][0] = 0;		une_instance.Tab[0][1] = 1;		une_instance.Tab[0][2] = 2;
		une_instance.Tab[1][0] = 3;		une_instance.Tab[1][1] = 4;		une_instance.Tab[1][2] = 5;
		une_instance.Tab[2][0] = 6;		une_instance.Tab[2][1] = 7;		une_instance.Tab[2][2] = 8;
	}

	void Job_Shop(t_instance une_instance)
	{
		std::ofstream f_res("result.txt", std::ios::app); // output file

		f_res << " | " << une_instance.nom << " | ";
		f_res << une_instance.BKS << " | ";


		int &n = une_instance.n;
		int &m = une_instance.m;
		int &h = une_instance.h;
		int &bks = une_instance.BKS;

		CpModelBuilder cp_model;

		// instance definition

		const Domain domain(0, h);

		// variables
		std::vector<IntVar> St; // starting times
		std::vector<IntVar> Ft; // Finishing times
		std::vector<IntervalVar> Operation; 
		IntVar z;  // makespan
		
		
		// constraint 1. + constraint 2
		for (int i = 0; i < n; ++i) {
			for (int j = 0; j < m; ++j) {
				int rang = une_instance.Tab[i][j];

				St.push_back(
					cp_model.NewIntVar(domain).WithName(absl::StrCat("St_", rang))
				);

				Ft.push_back(
					cp_model.NewIntVar(domain).WithName(absl::StrCat("St_", rang))
				);
			}
		}

		for (int i = 0; i < n; ++i) {
			for (int j = 0; j < m; ++j) {
				int rang = une_instance.Tab[i][j];
				const Domain domain_duree(une_instance.P[i][j], une_instance.P[i][j]);

				// domains should be improved...
				IntVar start = cp_model.NewIntVar(domain).WithName(absl::StrCat("start"));
				IntVar duree = cp_model.NewIntVar(domain_duree).WithName(absl::StrCat("duree"));
				IntVar fin = cp_model.NewIntVar(domain).WithName(absl::StrCat("end"));

				Operation.push_back(
					   cp_model.NewIntervalVar(St[rang], duree, Ft[rang])
				   );
			}
		}
		// basic definition of the makespan domain and....
		z = cp_model.NewIntVar(domain).WithName(absl::StrCat("z"));


		// constraint 2. St_ij >= Ft_i_(j-1)	
				//   i.e. St_ij - Ft_i_(j-1) >=0
				//
		for (int i = 0; i < n; i++)
		{
			for (int j =1; j < m; j++)
			{
				int rang_current_operation = une_instance.Tab[i][j];
				int rang_previous_operation = une_instance.Tab[i][j - 1];

				std::vector<IntVar> liste_variables;
				std::vector<int64> liste_coeffs;

				liste_variables.push_back(St[rang_current_operation]);
				liste_variables.push_back(Ft[rang_previous_operation]);
				auto span_variable = absl::Span<const IntVar>(liste_variables);

				liste_coeffs.push_back(1);   // St_ij
				liste_coeffs.push_back(-1);  // - Ft_i_(j-1)
				auto span_coefficient = absl::Span<const int64>(liste_coeffs);

				LinearExpr Left_Part = LinearExpr::ScalProd(span_variable, span_coefficient);
				cp_model.AddGreaterOrEqual(Left_Part, 0);
			}
		}



		// constraint 3. non overlap	
		for (int machine = 0; machine < m; machine++)
		{
			std::vector<IntervalVar> liste_variables;
			for (int i = 0; i < n; i++)
			{
				for (int j = 0; j < m; j++)
				{
					if (une_instance.M[i][j] == machine)
					{
						int rang = une_instance.Tab[i][j];
						liste_variables.push_back(Operation[rang]);
					}
				}
			}
			auto span_variable = absl::Span<const IntervalVar>(liste_variables);
			cp_model.AddNoOverlap(span_variable);

		}


		// constraint 4. Cumulative
		const Domain domain_capacity(m, m);
		IntVar capacity = cp_model.NewIntVar(domain_capacity).WithName(absl::StrCat("capacity"));
		cp_model.AddCumulative(capacity);
		
		// constraint 5.  
		for (int i = 0; i < n; i++)
		{
			int rang = une_instance.Tab[i][m-1];

			cp_model.AddLessOrEqual({ Ft[rang] }, z);
		}
	   
		// objective
		cp_model.Minimize(z);

		// stop if lower bound found
		//cp_model.AddLessOrEqual(z, bks);

		Model model;

		// Sets a time limit of 10 seconds.
		SatParameters parameters;
		parameters.set_max_time_in_seconds(120.0);
		model.Add(NewSatParameters(parameters));

		const CpSolverResponse response = SolveCpModel(cp_model.Build(), &model);
		std::cout << CpSolverResponseStats(response) << std::endl;

		

		if (response.status() == CpSolverStatus::OPTIMAL)
		{

			

			cout << "Optimal solution found..." << endl;
			const int64 makespan = SolutionIntegerValue(response, z);
			cout << "Makespan = " << makespan << endl;
			cout << endl;


			f_res <<  makespan << " | * | " << response.user_time() << " | " << endl;

			if (n*m < 10) // for small scale instance --> display solution
			{
				for (int i = 0; i < n; i++)
				{
					for (int j = 0; j < m; j++)
					{
						int rang = une_instance.Tab[i][j];

						const int64 date_deb = SolutionIntegerValue(response, St[rang]);
						const int64 date_fin = SolutionIntegerValue(response, Ft[rang]);

						stringstream ss;
						ss << "St_" << i << "_" << j << "  =  ";
						string str = ss.str();
						cout << str << " = " << date_deb << endl;

						stringstream ss2;
						ss2 << "Ft_" << i << "_" << j << "  =  ";
						string str2 = ss2.str();
						cout << str2 << " = " << date_fin << endl;

					}
				}
				cout << endl;
			}
		}
		else
			if (response.status() == CpSolverStatus::FEASIBLE)
			{
				cout << "solution found..." << endl;
				const int64 makespan = SolutionIntegerValue(response, z);
				cout << "Makespan = " << makespan << endl;
				cout << endl;

				f_res << makespan << " |   | " << response.user_time() << " | " << endl;


				if (n*m < 10) // for small scale instance --> display solution
				{
					for (int i = 0; i < n; i++)
					{
						for (int j = 0; j < m; j++)
						{
							int rang = une_instance.Tab[i][j];

							const int64 date_deb = SolutionIntegerValue(response, St[rang]);
							const int64 date_fin = SolutionIntegerValue(response, Ft[rang]);

							stringstream ss;
							ss << "St_" << i << "_" << j << "  =  ";
							string str = ss.str();
							cout << str << " = " << date_deb << endl;

							stringstream ss2;
							ss2 << "Ft_" << i << "_" << j << "  =  ";
							string str2 = ss2.str();
							cout << str2 << " = " << date_fin << endl;

						}
					}
					cout << endl;
				}
			}
			else
				cout << "sorry, no optimal solution found" << endl;


		f_res.close();

	}

	


//-------------------------------------------------------------------------------//
//-------------------------------------------------------------------------------//
//-------------------------------------------------------------------------------//

 int main(int argc, char** argv) {


	cout << "Job-Shop resolution with an efficient modeling approach" << endl;

	t_instance une_instance;

	/*
	cout << "test1 : instance widget" << endl;
	cout << "-----------------------" << endl;
	instance_widget(une_instance);
	une_instance.h = 100; // borne sup.
	Job_Shop(une_instance);
	*/
	
	std::ofstream f_res("result.txt"); // output file
	f_res << "---------------------------------------------------------" << endl;
	f_res << " | instance |    LB    |   Best bound | Opt | User Time | " << endl;
	f_res << "---------------------------------------------------------" << endl;
	f_res.close();

	for (int i = 1; i <= 40; i++)
	{

		cout << "test"<< i <<" : instance LA0" << i << endl;
		cout << "-----------------------" << endl;

		stringstream ss;
		if (i<10)
		   ss << "..\\instance\\la0";
		else
			ss << "..\\instance\\la";
		ss << i << ".txt";
		string str = ss.str();

		stringstream ss2;
		if (i < 10)
			ss2 << "la0";
		else
			ss2 << "la";
		ss2 << i;
		une_instance.nom = ss2.str();

		lire_instance(str, une_instance);
		une_instance.h = 2000; // borne sup.
		Job_Shop(une_instance);

	}


	

	//int touch;
//	cin >> touch;

	return EXIT_SUCCESS;
 }
