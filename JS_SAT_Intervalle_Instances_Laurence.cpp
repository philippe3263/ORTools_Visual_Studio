
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
//			BI			BFS			TTb(s)
//      -----------------------------------------------------------------------------
//		La01	666			666			0.0019 s
//		La02	655			655			0.00045 s
//		La03	597			597			0.0008 s
//		La04	590			590			0.001 s
//		La05	593			593			0.0001 s
//		La06	926			926			0.003  s
//		La07	890			890			0.004  s
//		La08	863			863			0.004 s
//		La09	951			951			0.0001 s
//		La10	958			958			0.003 s
//		La11	1222			1222			0.0006 s
//		La12	1039			1039			0.7192 s
//		La13	1150			1150			0.0022 s
//		La14	1292			1292			0.04401 s
//		La15	1207			1207			0.02696 s
//		La16	945			945			0.00399 s
//		La17	784			784			0.00431 s
//		La18	848			848			0.01514 s
//		La19	842			842			0.073204 s
//		La20	902			902			0.01910 s


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
			cout << "solution found..." << endl;
			const int64 makespan = SolutionIntegerValue(response, z);
			cout << "Makespan = " << makespan << endl;
			cout << endl;

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

	}

	


//-------------------------------------------------------------------------------//
//-------------------------------------------------------------------------------//
//-------------------------------------------------------------------------------//

 int main(int argc, char** argv) {


	cout << "Job-Shop resolution with an efficient modeling approach" << endl;

	t_instance une_instance;

	cout << "test1 : instance widget" << endl;
	cout << "-----------------------" << endl;
	instance_widget(une_instance);
	une_instance.h = 100; // borne sup.
	Job_Shop(une_instance);
	

	for (int i = 1; i <= 20; i++)
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

		lire_instance(str, une_instance);
		une_instance.h = 2000; // borne sup.
		Job_Shop(une_instance);

	}


	

	int touch;
	cin >> touch;

	return EXIT_SUCCESS;
 }
