
// Authors : Ph. Lacomme (placomme@isima.fr)
//
// Date : 2019, august 14th - wenesday
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

using namespace operations_research;
using namespace sat;
    
    
	void Job_Shop()
	{

		const int n = 3;             // number of jobs
		const int m = 3;             // number of machines
		const int h = 68;            // maximal lenght of the planning (upper bound of the solution)

		CpModelBuilder cp_model;

		// instance definition
		
		int M[n][m] = { 0 };   // machine
		int P[n][m] = { 0 };   // processing times
		int Tab[n][m] = { 0 }; // ref.

		//  data
		M[0][0] = 1;		M[0][1] = 2;		M[0][2] = 3;
		M[1][0] = 2;		M[1][1] = 3;		M[1][2] = 1;
		M[2][0] = 3;		M[2][1] = 1;		M[2][2] = 2;

		P[0][0] = 10;		P[0][1] = 20;		P[0][2] = 30;
		P[1][0] = 5; 		P[1][1] = 4;		P[1][2] = 10;
		P[2][0] = 12;		P[2][1] = 7;		P[2][2] = 4;

		Tab[0][0] = 0;	Tab[0][1] = 1;	Tab[0][2] = 2;
		Tab[1][0] = 3;	Tab[1][1] = 4;	Tab[1][2] = 5;
		Tab[2][0] = 6;	Tab[2][1] = 7;	Tab[2][2] = 8;



		const Domain domain(0, h);

		// variables
		std::vector<IntVar> St; // starting times
		std::vector<IntVar> Ft; // Finishing times
		std::vector<IntervalVar> Operation; 
		IntVar z;  // makespan
		
		
		// constraint 1. + constraint 2
		for (int i = 0; i < n; ++i) {
			for (int j = 0; j < m; ++j) {
				int rang = Tab[i][j];

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
				int rang = Tab[i][j];
				const Domain domain_duree(P[i][j], P[i][j]);

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
				int rang_current_operation = Tab[i][j];
				int rang_previous_operation = Tab[i][j - 1];

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



		// constraint 3. one cumulative for each machine	
		for (int machine = 0; machine < m; machine++)
		{
			std::vector<IntervalVar> liste_variables;
			for (int i = 0; i < n; i++)
			{
				for (int j = 0; j < m; j++)
				{
					if (M[i][j] == machine)
					{
						int rang = Tab[i][j];
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
			int rang = Tab[i][m-1];

			cp_model.AddLessOrEqual({ Ft[rang] }, z);
		}
	   
		// objective
		cp_model.Minimize(z);

		Model model;

		// Sets a time limit of 10 seconds.
		SatParameters parameters;
		parameters.set_max_time_in_seconds(10.0);
		model.Add(NewSatParameters(parameters));

		const CpSolverResponse response = SolveCpModel(cp_model.Build(), &model);
		std::cout << CpSolverResponseStats(response) << std::endl;

		

		if (response.status() == CpSolverStatus::OPTIMAL)
		{
			cout << "solution found..." << endl;
			const int64 makespan = SolutionIntegerValue(response, z);
			cout << "Makespan = " << makespan << endl;

			for (int i = 0; i < n; i++)
			{
				for (int j = 0; j < m; j++)
				{
					int rang = Tab[i][j];

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
		else
			cout << "sorry, no optimal solution found" << endl;

	}

	


//-------------------------------------------------------------------------------//
//-------------------------------------------------------------------------------//
//-------------------------------------------------------------------------------//

 int main(int argc, char** argv) {

     
	cout << "Job-Shop resolution with an efficient modeling approach" << endl;

    Job_Shop();
	
	return EXIT_SUCCESS;
 }
