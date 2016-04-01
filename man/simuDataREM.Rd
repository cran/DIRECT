\name{simuDataREM}
\alias{simuDataREM}
%- Also NEED an '\alias' for EACH other topic documented here.
\title{
Data Simulation Under the Random-Effects Mixture Model
}
\description{
Function \code{simuDataREM} simulates data under the Ornstein-Uhlenbeck (OU) (or Brownian Motion; BM) process-based random-effects mixture (REM) model.
}
\usage{
simuDataREM(pars.mtx, dt, T, ntime, nrep, nsize, times, 
    method = c("eigen", "svd", "chol"), model = c("OU", "BM"))
}
%- maybe also 'usage' for other objects documented here.
\arguments{
  \item{pars.mtx}{
A \eqn{K \times 8} matrix, where \eqn{K} is the number of clusters.  Each row contains 8 parameters: standard deviation of within-cluster variability, of variability across time points, and of replicates, respectively; mean and standard deviation for the value at the first time point; the overall mean, standard deviation and mean-reverting rate of the OU process.
}
  \item{dt}{
Increment in times.
}
  \item{T}{
Maximum time.
}
  \item{ntime}{
Number of time points to simulate data for.  Needs to be same as the length of vector \code{times}.
}
  \item{nrep}{
Number of replicates.
}
  \item{nsize}{
An integer vector containing sizes of simulated clusters.
}
  \item{times}{
Vector of length \code{ntime} indicating at which time points to simulate data.
}
  \item{method}{
Method to compute the determinant of the covariance matrix in the calculation of the multivariate normal density.  Required.  Method choices are: "chol" for Choleski decomposition, "eigen" for eigenvalue decomposition, and "svd" for singular value decomposition.
}
  \item{model}{
Model to generate realizations of the mean vector of a mixture component.  Required.  Choices are: "OU" for an Ornstein-Uhlenbeck process (a.k.a. the mean-reverting process) and "BM" for a Brown motion (without drift).
}
}
\value{
  \item{means}{
A matrix of \code{ntime} columns.  The number of rows is the same as that of \code{pars.mtx}, which is the number of clusters.  Each row contains the true mean vector of the corresponding cluster.
}
  \item{data}{
A matrix of \eqn{N} rows and \code{ntime}*\code{nrep}+1 columns, where \eqn{N} is the sum of cluster sizes \code{nsize}.  The first column contains the true cluster membership of the corresponding item.  The rest of the columns in each row is formatted as follows: values for replicate 1 through \code{nrep} at time 1; values for replicate 1 through \code{nrep} at time 2, ...
}
}
\references{
Fu, A. Q., Russell, S., Bray, S. and Tavare, S. (2013) Bayesian clustering of replicated time-course gene expression data with weak signals. The Annals of Applied Statistics. 7(3) 1334-1361.
}
\author{
Audrey Q. Fu
}
\seealso{
\code{\link{plotSimulation}} for plotting simulated data.

\code{\link{outputData}} for writing simulated data and parameter values used in simulation into external files.

\code{\link{DIRECT}} for clustering the data.
}
\examples{
\dontrun{
# Simulate replicated time-course gene expression profiles
# from OU processes

# Simulation parameters
times = c(0,5,10,15,20,25,30,35,40,50,60,70,80,90,100,110,120,150)
ntime=length (times)
nrep=4

nclust = 6
npars = 8
pars.mtx = matrix (0, nrow=nclust, ncol=npars)
# late weak upregulation or downregulation
pars.mtx[1,] = c(0.05, 0.1, 0.5, 0, 0.16, 0.1, 0.4, 0.05)		
# repression
pars.mtx[2,] = c(0.05, 0.1, 0.5, 1, 0.16, -1.0, 0.1, 0.05)	        
# early strong upregulation
pars.mtx[3,] = c(0.05, 0.5, 0.2, 0, 0.16, 2.5, 0.4, 0.15)	        
# strong repression
pars.mtx[4,] = c(0.05, 0.5, 0.2, 1, 0.16, -1.5, 0.4, 0.1)	        
# low upregulation
pars.mtx[5,] = c(0.05, 0.3, 0.3, -0.5, 0.16, 0.5, 0.2, 0.08)		
# late strong upregulation
pars.mtx[6,] = c(0.05, 0.3, 0.3, -0.5, 0.16, 0.1, 1, 0.1)	        

nsize = rep(40, nclust)

# Generate data
simudata = simuDataREM (pars=pars.mtx, dt=1, T=150, 
    ntime=ntime, nrep=nrep, nsize=nsize, times=times, method="svd", model="OU")

# Display simulated data
plotSimulation (simudata, times=times, 
    nsize=nsize, nrep=nrep, lty=1, ylim=c(-4,4), type="l", col="black")

# Write simulation parameters and simulated data
# to external files
outputData (datafilename= "simu_test.dat", parfilename= "simu_test.par", 
    meanfilename= "simu_test_mean.dat", simudata=simudata, pars=pars.mtx, 
    nitem=sum(nsize), ntime=ntime, nrep=nrep)
}
}
% Add one or more standard keywords, see file 'KEYWORDS' in the
% R documentation directory.
