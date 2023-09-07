//------------------------------------------------------------------------------------
// Relabeling Algorithm (for R)
// Audrey Q. Fu
//
// Implementing Algorithm 2 in Matthew Stephens (2000) JRSSB.
// Step 2 is solved using Munkres' algorithm to the assignment problem.
// Implementation of Munkres' algorithm is based on code by Dariush Lotfi (June 2008)
//
// Compile C code before loading into R
// In console, type in following command:
// $ R CMD SHLIB relabel_R.c -o relabel_R.so -lm 
//
// Input:
// Output:
//----------------------------------------------------------------------------

# include <R.h>
#include <stdio.h>
#include <stdlib.h>
#include <math.h>
#include <time.h>
//#include <munkres.h>
# define INF (1000000)

void findOptimalQ (double **Qmtx, double ***Pmtx, int H, int N, int K)
{
	int h, n, k;
	
	for (n=0; n<N; n++) 
		for (k=0; k<K; k++) 
			Qmtx[n][k] = 0.0;

	// In Algorithm 2 with the KL distance as loss function,
	// optimal Q for current permutation is average over all MCMC samples
	for (h=0; h<H; h++) 
		for (n=0; n<N; n++) 
			for (k=0; k<K; k++) 
				Qmtx[n][k] += Pmtx[h][n][k];
	
	for (n=0; n<N; n++) 
		for (k=0; k<K; k++) 
			Qmtx[n][k] /= H;
}

void reorderPmtx (double **PmtxReordered, double ** Pmtx, int * Vmtx, int N, int K)
{
	int n, k;
	
	for (n=0; n<N; n++) 
		for (k=0; k<K; k++) 
			PmtxReordered[n][k] = Pmtx[n][Vmtx[k]];
	
}

// Pmtx should be reordered already
// for one iteration
void computeCostMtx (double **Cmtx, double **Pmtx, double **Qmtx, int N, int K, int PRINT)
{
	int i, j, l, k;
	
    /*
	if (PRINT)
	{
		printf("In function computeCostMtx: reordered P mtx\n");
		for (i=0;i<N;i++)
		{
			for (k=0;k<K;k++)
				printf("%3.2lf ", Pmtx[i][k]);
			printf("\n");
		}
		printf("In function computeCostMtx: Q mtx\n");
		for (i=0;i<N;i++)
		{
			for (k=0;k<K;k++)
				printf("%3.2lf ", Qmtx[i][k]);
			printf("\n");
		}
	}
    */

	// Initialize cost matrix
	for (i=0; i<K; i++) 
		for (k=0; k<K; k++) 
			Cmtx[i][k] = 0.0;
		
	// Compute cost matrix
	for (j=0; j<K; j++) 
		for (l=0; l<K; l++) 
			for (i=0; i<N; i++) 
			{
				if (Pmtx[i][l] == 0)
					Cmtx[j][l] += 0.0;
				else if (Qmtx[i][l] == 0)
					Cmtx[j][l] += INF;
				else
					Cmtx[j][l] += Pmtx[i][l] * (log (Pmtx[i][l]) - log (Qmtx[i][j]));
                /*
				if (PRINT)
					printf("%3.2lf ", Cmtx[j][l]);
                 */
			}
    /*
	if (PRINT)
		printf("\n");
	

	if (PRINT)
	{
		printf("In function computeCostMtx: cost matrix\n");
		for (i=0;i<K;i++)
		{
			for (k=0;k<K;k++)
				printf("%3.2lf ", Cmtx[i][k]);
			printf("\n");
		}
	}
	*/
}

// computes loss for a pair of p and q
double computeLossInd (double p, double q)
{
	double loss;
	
	if (p == 0)
		loss = 0.0;
	else if (q==0)
		loss = INF;
	else
		loss = p * (log (p) - log (q));
	
	return (loss);
}

// computes total risk for P and Q matrices
double computeRisk (double ***Pmtx, double **Qmtx, int **Vmtx, int H, int N, int K, int PRINT)
{
	int h, n, k;
	double risk = 0.0;
	double **Preordered;
	
	Preordered = (double **) malloc (sizeof(double *) * N);
	for (n=0; n<N; n++) 
		Preordered[n] = (double *) malloc (sizeof(double) * K);
	
	for (h=0; h<H; h++) 
	{
		// Reorder P matrix for this MCMC sample
		reorderPmtx (Preordered, Pmtx[h], Vmtx[h], N, K);
        /*
		if (PRINT) 
		{
			printf("MCMC sample=%d\n", h);
			printf("reordered P\n");
			for (n=0; n<N; n++) 
			{
				for (k=0; k<K; k++) 
					printf("%3.2lf ", Preordered[n][k]);
				printf("\n");
			}
		}
         */
		
		// Compute KL distance between reordered P matrix and Q matrix
		// And add rows and columns up
		for (n=0; n<N; n++) 
		{
			for (k=0; k<K; k++) 
			{
				risk += computeLossInd (Preordered[n][k], Qmtx[n][k]);
			}
		}
	}
	
	for (n=0; n<N; n++)
		free (Preordered[n]);
	free (Preordered);
	
	return (risk);
}

//----------------------------------------------------------------------------
// Munkres (Hungarian) Algorithm - A solution to assignment problem
//
// Dariush Lotfi - June 2008
// Modified by Audrey Fu - March 2010
//----------------------------------------------------------------------------
#define MAXINT 0x7FFF

//Converts original cost matrix to reduced cost matrix by subtracting the minimum
//of each row from every elements of that row and minimum of each column from
//every elements of that column.
void MakeReducedCostMatrix(double **M,int n)
{
	int i,j;
	double min;
	
	for (i=0;i<n;i++)
	{
        min = MAXINT;
        for (j=0;j<n;j++)
			if (M[i][j] < min) min = M[i][j];
        for (j=0;j<n;j++)
			M[i][j] = M[i][j] - min;
	}
	for (j=0;j<n;j++)
	{
        min = MAXINT;
        for (i=0;i<n;i++)
			if (M[i][j] < min) min = M[i][j];
        for (i=0;i<n;i++)
			M[i][j] = M[i][j] - min;
	}
}

//Marks some independent zeros with star before starting the iterative
//part of the algorithm and then returns the number of starred zeros.
//"Independent zeros" means that no two zeros are in the same row or column.
//Note that it's not important how many zeros being starred in this step.
int StarZerosForFirstTime(double **M, int *Starred, int n)
{
	int i,j,starred_count = 0;
	
	for (i=0;i<n;i++)
        for (j=0;j<n;j++)
			if (Starred[i] == -1 && M[n][j] == 0.0 && M[i][j] == 0.0)
			{
                M[n][j] = 1.0;
                Starred[i] = j;
                starred_count++;
			}
	
	return starred_count;
}

//Looks for an uncovered zero in cost matrix and returns true if one is found.
int FindUncoveredZero(double **M, int n, int *row, int *col)
{
	int i,j;
	for (i=0;i<n;i++)
        for (j=0;j<n;j++)
			if (M[i][n] == 0.0 && M[n][j] == 0.0 && M[i][j] == 0.0)
			{
                *row = i;
                *col = j;
                return 1;
			}
	return 0;
}


//Covers uncovered zeros by changing the cover lines or adding new lines (starred
//zeros) until there are no uncovered zeros left.
int CoverUncoveredZeros(double **M, int *Starred, int *Primed, int n, int *covers)
{
	int i,row,col;
	
	//Repeating until there are no uncovered zeros left
	while (FindUncoveredZero(M,n,&row,&col))
        if (Starred[row] != -1) //If there is a starred zero in the same row of uncovered zero
        {
			//Priming the uncovered zero
			Primed[row] = col;
			//Covering the row of uncovered zero
			M[row][n] = 1.0;
			//Uncovering the column containing the starred zero
			M[n][Starred[row]] = 0.0;
        }
        else //If there is no starred zero in the same row of uncovered zero
        {
			//According to the algorithm uncovered zero should be primed first, but
			//because it will be starred later, I don't prime it.
			
			//Looking for a starred zero in the same column of uncovered (primed) zero
			for (i=0;i<n;i++)
                if (Starred[i] == col) break;
			//Repeating until there is no starred zero in the same column of primed zero
			while (i != n)
			{
                //Starring the primed zero
                Starred[row] = col;
                //Unstarring the starred zero in the same column of primed zero
                Starred[i] = -1;
                //Finding the primed zero in the same row of that starred zero
                //(there will always be one)
                col = Primed[i];
                row = i;
                //Looking for a starred zero in the same column of the found primed zero
                for (i=0;i<n;i++)
					if (Starred[i] == col) break;
			}
			//Starring the last primed zero that has no starred zero in its column
			Starred[row] = col;
			//Erasing all primes and uncover every rows in the matrix while covering
			//all columns containing a starred zero
			for (i=0;i<n;i++)
			{
                Primed[i] = -1;
                M[i][n] = 0.0;
                if (Starred[i] != -1) M[n][Starred[i]] = 1.0;
			}
			(*covers)++;
			if (*covers == n) 
				return n;
        }
	
	return 0;
	//	return *covers;
}


void solveMunkres(double **M, int *Result, int n, int PRINT)
{
	int i,j,covers;
	double min;
	/* int tmp;  */
	int *Starred,*Primed;
	
	//Starred zeros indicates assignment pairs (Result) when the algorithm
	//is finished; so there is no need to define a new vector.
	Starred = Result;
	//Allocating memory for primed
	Primed = (int *) malloc (sizeof (int) * n);
	
	//Initializing Starred and Primed and covered-flag row & column of M
	//(i.e. row & column having index n. They indicate which rows or columns
	// are covered.)
	//If M[i][j] is a starred zero, Starred[i] has the value of j and if
	//there is no starred zero at the row i, Starred[i] has the value of -1.
	//The same is true for primed zeros and Primed vector values.
	for (i=0;i<n;i++)
	{
        Starred[i] = -1;
        Primed[i] = -1;
	}
	for (i=0;i<n;i++)
        M[i][n] = 0.0;
	for (j=0;j<n;j++)
        M[n][j] = 0.0;
	
	
	//Step 0: Making reduced cost matrix
	MakeReducedCostMatrix(M,n);
	
    /*
	if (PRINT)
	{
		printf("subtracting min from rows and cols\n");
		for (i=0; i<n+1; i++)
		{
			for (j=0; j<n+1; j++) 
			{
				printf("%lf ", M[i][j]);
			}
			printf("\n");
		}
		printf("Starred:\n");
		for (i=0; i<n; i++) {
			printf("%d ", Starred[i]);
		}
		printf("\n");
		printf("Primed:\n");
		for (i=0; i<n; i++) {
			printf("%d ", Primed[i]);
		}
		printf("\n");
		printf("covers: %d\n", covers);
	}
     */
	
	//Step 1: Marking some zeros with star for beginning
	covers = StarZerosForFirstTime(M,Starred,n);
	
    /*
	if (PRINT)
	{
		printf("marking zeros for the first time\n");
		for (i=0; i<n+1; i++)
		{
			for (j=0; j<n+1; j++) 
			{
				printf("%lf ", M[i][j]);
			}
			printf("\n");
		}
		printf("Starred:\n");
		for (i=0; i<n; i++) {
			printf("%d ", Starred[i]);
		}
		printf("\n");
		printf("Primed:\n");
		for (i=0; i<n; i++) {
			printf("%d ", Primed[i]);
		}
		printf("\n");
		printf("covers: %d\n", covers);
	}
     */
	
	while (covers != n)
	{
        //Steps 2&3: Changing or adding the cover lines until all zeros are covered
     /* tmp = CoverUncoveredZeros(M,Starred,Primed,n,&covers);  */
        CoverUncoveredZeros(M,Starred,Primed,n,&covers);
        if (covers == n) break;
		
        /*
		if (PRINT)
		{
			printf("covering zeros\n");
			for (i=0; i<n+1; i++)
			{
				for (j=0; j<n+1; j++) 
				{
					printf("%lf ", M[i][j]);
				}
				printf("\n");
			}
			printf("Starred:\n");
			for (i=0; i<n; i++) {
				printf("%d ", Starred[i]);
			}
			printf("\n");
			printf("Primed:\n");
			for (i=0; i<n; i++) {
				printf("%d ", Primed[i]);
			}
			printf("\n");
			printf("covers: %d\n", covers);
		}
         */
		
        //Step 4: Finding smallest uncovered value, then subtracting it from
        //              uncovered values and adding it to doubly covered values
        //              (= adding it to every element of each covered row, and
        //               subtracting it from every element of each uncovered column)
        min = MAXINT;
        for (i=0;i<n;i++)
			for (j=0;j<n;j++)
                if (M[i][n] != 1.0 && M[n][j] != 1.0 && M[i][j] < min) min = M[i][j];
		
        for (i=0;i<n;i++)
			if (M[i][n] == 1.0)
                for (j=0;j<n;j++)
					M[i][j] = M[i][j] + min;
        for (j=0;j<n;j++)
			if (M[n][j] == 0.0)
                for (i=0;i<n;i++)
					M[i][j] = M[i][j] - min;
		
        /*
		if (PRINT)
		{
			printf("subtracting new min\n");
			for (i=0; i<n+1; i++)
			{
				for (j=0; j<n+1; j++) 
				{
					printf("%lf ", M[i][j]);
				}
				printf("\n");
			}
			printf("Starred:\n");
			for (i=0; i<n; i++) {
				printf("%d ", Starred[i]);
			}
			printf("\n");
			printf("Primed:\n");
			for (i=0; i<n; i++) {
				printf("%d ", Primed[i]);
			}
			printf("\n");
			printf("covers: %d\n", covers);
		}
         */
		
		//  for (i=0;i<n;i++)
		//      for (j=0;j<n;j++)
		//        if (M[i][n] != 1 && M[n][j] != 1)
		//              M[i][j] = M[i][j] - min;
		//        else if (M[i][n] == 1 && M[n][j] == 1)
		//              M[i][j] = M[i][j] + min;
	}
	
	//Freeing memory of Primed
	free (Primed);
}


double Munkres (double **M, int *Result, int n, int PRINT)
{
	double **C;
	int i, j;
	double cost=0.0;
	C = (double **) malloc (sizeof(double *) * n);
	for(i=0;i<n;i++)
		C[i] = (double *) malloc (sizeof(double) * n);
	for (i=0; i<n; i++) 
		for (j=0; j<n; j++) 
			C[i][j] = M[i][j];
	
	solveMunkres (M, Result, n, PRINT);
	for (i=0; i<n; i++) 
		cost += C[i][Result[i]];
	
	for (i=0; i<n; i++) 
		free (C[i]);
	free (C);
	
	return (cost);
}


void relabel_R (int * perm_mtx, double * prob_mtx, int * niter_mcmc, int * nitem, int * nclust, double * threshold, int * print_flag)
{
	int H=niter_mcmc[0], N=nitem[0], K=nclust[0];
	double THRESHOLD=threshold[0];
	/* int PRINT=print_flag[0]; */
	double ***Pmtx;		// H-by-N-by-K; containing H posterior probability matrices, each of N-by-K
	double **Qmtx;		// N-by-K; optimal posterior probability matrix in each iteration
	double **Cmtx;		// K+1-by-K+1; cost matrix for each MCMC sample
	int **Vmtx;			// H-by-K; permutation matrix, each row a permutation for an MCMC sample in each iteration
	int **VmtxUpdated;		// H-by-K; updated permutation matrix, each row a permutation for an MCMC sample in each iteration
	double **PmtxReordered;	// N-by-K; posterior probability matrix reordered according to current permutations
	int *Result;			// int pointer vector of length K; storing permutation for an MCMC sample
	int h, n, k;
	/* int i; */
	double riskCurr, riskNew;
	double converge = INF;
//	int niter = 1;
		
	// Initialize
	//printf("no of iterations: %d\n", H);
	//printf("no of items: %d\n", N);
	//printf("no of clusers: %d\n", K);
	
	Pmtx = (double ***) malloc (sizeof(double **) * H);
	for(h=0;h<H;h++)
	{
		Pmtx[h] = (double **) malloc (sizeof(double *) * N);
		for (n=0; n<N; n++) 
		{
			Pmtx[h][n] = (double *) malloc (sizeof(double) * K);
		}
	}
	for (h=0; h<H; h++) 
	{
		for (n=0;n<N;n++)
			for (k=0;k<K;k++)
				Pmtx[h][n][k] = prob_mtx[N*K*h+K*n+k];
	}
	
    /*
	if (PRINT)
	{
		printf("posterior prob matrix:\n");
		for (h=0; h<H; h++) 
		{
			for (n=0;n<N;n++)
			{
				for (k=0;k<K;k++)
					printf("%3.2lf ", Pmtx[h][n][k]);
				printf("\n");
			}
		}
	}
     */
	
//	printf("posterior prob matrix:\n");
//	for (n=0;n<N;n++)
//	{
//		for (k=0;k<K;k++)
//			printf("%3.2lf ", Pmtx[0][n][k]);
//		printf("\n");
//	}

	Qmtx = (double **) malloc (sizeof(double *) * N);
	for (n=0; n<N; n++) 
		Qmtx[n] = (double *) malloc (sizeof(double) * K);
	Vmtx = (int **) malloc (sizeof(int *) * H);
	for (h=0; h<H; h++) 
		Vmtx[h] = (int *) malloc (sizeof(int) * K);
	VmtxUpdated = (int **) malloc (sizeof(int *) * H);
	for (h=0; h<H; h++) 
		VmtxUpdated[h] = (int *) malloc (sizeof(int) * K);
	Cmtx = (double **) malloc (sizeof(double *) * (K+1));
	for (k=0; k<(K+1); k++) 
		Cmtx[k] = (double *) malloc (sizeof(double) * (K+1));
	PmtxReordered = (double **) malloc (sizeof(double *) * N);
	for (n=0; n<N; n++) 
		PmtxReordered[n] = (double *) malloc (sizeof(double) * K);
	Result = (int *) malloc (sizeof(int *) * K);
	
	for (h=0; h<H; h++) 
		for (k=0; k<K; k++) 
			Vmtx[h][k] = k;
	
	// Loop while fixed point is not reached
	//printf("Relabeling...\n");
	while (converge > THRESHOLD)
	{
		//printf("%d\n", niter);
		riskNew = 0.0;
		// Step 1: Find Q to minimize Monte Carlo risk for current permutations
		// Q found to be average of P over MCMC samples
		findOptimalQ (Qmtx, Pmtx, H, N, K);
        
        /*
		if (PRINT)
		{
			printf("Step 1: find optimal Q\n");
			for (n=0;n<N;n++)
			{
				for (k=0;k<K;k++)
					printf("%3.2lf ", Qmtx[n][k]);
				printf("\n");
			}
		}
         */

		// Compute current risk
		riskCurr = computeRisk (Pmtx, Qmtx, Vmtx, H, N, K, 0);
        /*
		if (PRINT)
			printf("risk before update: %3.2lf\n", riskCurr);
		*/
        
		// Step 2: Find optimal permutation for each MCMC sample
		for (h=0; h<H; h++) 
		{
            /*
			if (PRINT) 
				printf("h=%d\n", h);
            */ 
             
			// Reorder each row of the P matrix
			reorderPmtx (PmtxReordered, Pmtx[h], Vmtx[h], N, K);
            /*
			if (PRINT)
			{
				printf("Step 2a: reorder P mtx\n");
				for (n=0;n<N;n++)
				{
					for (k=0;k<K;k++)
						printf("%3.2lf ", PmtxReordered[n][k]);
					printf("\n");
				}
			}
             */

			// Compute the K-by-K cost matrix for current permutation
			computeCostMtx (Cmtx, PmtxReordered, Qmtx, N, K, 0);
            /*
			if (PRINT)
			{
				printf("Step 2b: compute cost matrix\n");
				for (i=0;i<K;i++)
				{
					for (k=0;k<K;k++)
						printf("%3.2lf ", Cmtx[i][k]);
					printf("\n");
				}
			}
             */

			// Find optimal permutation (applying Munkres' algorithm)
			riskNew += Munkres (Cmtx, Result, K, 0);
            /*
			if (PRINT)
				printf("updated permutation:\n");
             */
			for (k=0; k<K; k++)
			{
				VmtxUpdated[h][k] = Result[k];
                /*
				if (PRINT)
					printf("%d ", VmtxUpdated[h][k]);
                 */
			}
            /*
			if (PRINT)
				printf("\ncurrent risk: %3.2lf\n", riskNew);
             */
		}
		
        /*
		if (PRINT)
		{
			printf("Step 3: updated permutation matrix\n");
			for (h=0;h<H;h++)
			{
				for (k=0;k<K;k++)
					printf("%d ", VmtxUpdated[h][k]);
				printf("\n");
			}
		}
         */
		
//		risk = computeRisk (Pmtx, Qmtx, VmtxUpdated, H, N, K, 1);
//		if (PRINT)
//			printf("recalc risk: %3.2lf\n", risk);

		// Compute change in risk
		converge = riskCurr - riskNew;
        /*
		if (PRINT)
			printf("log (distance): %3.2lf\n", log(converge));
         */
		
		//printf("current risk: %3.2lf\n", riskCurr);
		// Update Vmtx
		if (converge>THRESHOLD)
		{
			for (h=0;h<H;h++)
				for (k=0;k<K;k++)
					Vmtx[h][k] = VmtxUpdated[h][k];
		}
		
//		niter++;
	}
	
    /*
	if (PRINT)
	{
		printf("Final permutation matrix\n");
		for (h=0;h<H;h++)
		{
			for (k=0;k<K;k++)
				printf("%d ", Vmtx[h][k]);
			printf("\n");
		}
	}
     */

	//Writing result to perm_mtx 
	for (h=0;h<H;h++)
	{
		for (k=0;k<K;k++)
			perm_mtx[K*h+k] = Vmtx[h][k]+1;
	}
	
	
	// Free memory
	for (h=0; h<H; h++) 
	{
		for (n=0; n<N; n++) 
			free (Pmtx[h][n]);
		free (Pmtx[h]);
	}
	free (Pmtx);
	for (n=0; n<N; n++) 
	{
		free (Qmtx[n]);
		free (PmtxReordered[n]);
	}
	free (Qmtx);
	free (PmtxReordered);
	for (h=0; h<H; h++) 
	{
		free (Vmtx[h]);
		free (VmtxUpdated[h]);
	}
	free (Vmtx);
	free (VmtxUpdated);
	for (k=0; k<(K+1); k++) 
		free (Cmtx[k]);
	free (Cmtx);
	free (Result);
}
