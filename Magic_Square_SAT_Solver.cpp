
// Authors : Ph. Lacomme (placomme@isima.fr)
//
// Date : 2019, august 11th - sunday
//
// Validation on Visual Studio 2017
//
//
// Show how to use the SAT solver for the Magic Square problem
//
// Remark : could be shorten... but provides a readable program


#include <iostream>
using namespace std;

#define _SECURE_SCL 0
#define _ALLOW_ITERATOR_DEBUG_LEVEL_MISMATCH
#define NOMINMAX

#define _SILENCE_CXX17_OLD_ALLOCATOR_MEMBERS_DEPRECATION_WARNING
#define _SILENCE_ALL_CXX17_DEPRECATION_WARNINGS


// solver PPC Sat
#include "ortools/sat/cp_model.h"

using namespace operations_research;
using namespace sat;

    void Magic_Square()
	{
		const int n = 4;  // size of the problem
		const int nb_total_valeur = n * n;

		CpModelBuilder cp_model;

		// each line, each column and each diagonal
		// must have a sum equal to : S =  n * (n*n + 1) / 2;
		int S = n * (n*n + 1) / 2;

		const Domain domain(1, n*n);

		std::vector<IntVar> Q;
		int nb = 0;

		for (int i = 0; i < nb_total_valeur; ++i) {
			Q.push_back(
					cp_model.NewIntVar(domain).WithName(absl::StrCat("var_", nb)));
			nb++;
		}

       	// constraint 1. All Q[i][j] have different values		
		cp_model.AddAllDifferent({ Q });

		// constraint 2. The sum of each line is equal to Somme
		for (int i = 0; i < n; i++)
		{
			std::vector<IntVar> liste_variables;
			std::vector<int64> liste_coeffs;
			for (int j = 0; j < n; j++)
			{
				int rang = n * i + j;
				liste_variables.push_back(Q[rang]);
				liste_coeffs.push_back(1);
			}
			auto span_variable = absl::Span<const IntVar>(liste_variables);
			auto span_coefficient = absl::Span<const int64>(liste_coeffs);
			LinearExpr partie_gauche = LinearExpr::ScalProd(span_variable, span_coefficient);
			cp_model.AddEquality(partie_gauche, S);
		}

		// constraint 3. The sum of each column is equal to S
		for (int j = 0; j < n; j++)
		{
			std::vector<IntVar> liste_variables;
			std::vector<int64> liste_coeffs;
			for (int i = 0; i < n; i++)
			{
				int rang = j + n*i;
				liste_variables.push_back(Q[rang]);
				liste_coeffs.push_back(1);
			}
			auto span_variable = absl::Span<const IntVar>(liste_variables);
			auto span_coefficient = absl::Span<const int64>(liste_coeffs);
			LinearExpr partie_gauche = LinearExpr::ScalProd(span_variable, span_coefficient);
			cp_model.AddEquality(partie_gauche, S);
		}

		
		{   // constraint 4. The sum of the first diagonal
			std::vector<IntVar> liste_variables;
			std::vector<int64> liste_coeffs;
			for (int i = 0; i < n; i++)
			{
				int rang = (i)*(n + 1);
				liste_variables.push_back(Q[rang]);
				liste_coeffs.push_back(1);
			}
			auto span_variable = absl::Span<const IntVar>(liste_variables);
			auto span_coefficient = absl::Span<const int64>(liste_coeffs);
			LinearExpr partie_gauche = LinearExpr::ScalProd(span_variable, span_coefficient);
			cp_model.AddEquality(partie_gauche, S);
		}

		{	// constraint 5. The sum of the second diagonal
			std::vector<IntVar> liste_variables;
			std::vector<int64> liste_coeffs;
			for (int i = 0; i < n; i++)
			{
				int rang = (i+1)*(n - 1);
				liste_variables.push_back(Q[rang]);
				liste_coeffs.push_back(1);
			}
			auto span_variable = absl::Span<const IntVar>(liste_variables);
			auto span_coefficient = absl::Span<const int64>(liste_coeffs);
			LinearExpr partie_gauche = LinearExpr::ScalProd(span_variable, span_coefficient);
			cp_model.AddEquality(partie_gauche, S);
		}

		Model model;

		// Sets a time limit of 10 seconds.
		SatParameters parameters;
		parameters.set_max_time_in_seconds(10.0);
		model.Add(NewSatParameters(parameters));

		const CpSolverResponse response = SolveCpModel(cp_model.Build(), &model);
		std::cout << CpSolverResponseStats(response) << std::endl;

		if (response.status() == CpSolverStatus::FEASIBLE)
	
			for (int i = 0; i < n; i++)
			{
				cout << "line number " << i + 1 << endl;
				for (int j = 0; j < n; j++)
				{
					int rang = n * i + j;
					const int64 valeur_Q = SolutionIntegerValue(response, Q[rang]);

					stringstream ss;
					ss << "Q_" << i+1 << "_" << j+1 << "  =  ";
					string str = ss.str();

					cout << str << " = " << valeur_Q << endl;
				}
				cout <<  endl;
			}
		}

	


//-------------------------------------------------------------------------------//
//-------------------------------------------------------------------------------//
//-------------------------------------------------------------------------------//

 int main(int argc, char** argv) {

    // Magic_Square resolution
	 Magic_Square();

	
	return EXIT_SUCCESS;
}
