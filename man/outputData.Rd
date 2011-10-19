\name{outputData}
\alias{outputData}
%- Also NEED an '\alias' for EACH other topic documented here.
\title{
Writing Simulation Parameters and Data to Files
}
\description{
Write simulation parameters and simulated data to files with user-specified filenames.
}
\usage{
outputData(datafilename, parfilename, meanfilename, 
    simudata, pars, nitem, ntime, nrep)
}
%- maybe also 'usage' for other objects documented here.
\arguments{
  \item{datafilename}{
Name of text file containing simulated data.
}
  \item{parfilename}{
Name of text file containing simulation parameters, which include number of items, number of time points, number of replicates, true cluster-specific mean vectors, true standard deviations of three types of variability (random effects).
}
  \item{meanfilename}{
Name of text file containing sample means (averaged over replicates) of simulated data.
}
  \item{simudata}{
List produced by \code{\link{simuDataREM}}.  Contains simulated data.
}
  \item{pars}{
Matrix of simulation parameters.  Same object as \code{pars.mtx} in \code{\link{simuDataREM}}.
}
  \item{nitem}{
Number of items.
}
  \item{ntime}{
Number of time points.
}
  \item{nrep}{
Number of replicates.
}
}
\value{
Three files are generated and placed under the current working directory or directories specified in filenames:
\itemize{
  \item Complete simulated data: Matrix of \code{nitem} by \code{ntime}*\code{nrep}+1.  The first column contains the true cluster labels.  In the rest of the columns, data are stored as Replicates 1 through \code{nrep} at Time 1, Replicates 1 through \code{nrep} at Time 2, ..., Replicates 1 through \code{nrep} at Time \code{ntime}.
  \item Simulated mean data: Matrix of \code{nitem} by \code{ntime}.  Each row contains the sample means at Times 1 through \code{ntime}.
  \item Simulation parameters: 
  \itemize{
    \item First row: \code{nitem}.
    \item Second row: \code{ntime}.
    \item Third row: \code{nrep}.
    \item Rest of file: Matrix.  Each row corresponds to a cluster, and contains cluster label, true mean vector of length \code{ntime}, standard deviations of within-cluster variability, variability across time points and residual variability.
  }
}
}
\references{
Fu, A. Q., Russell, S., Bray, S. J. and Tavare, S. Bayesian clustering with the Dirichlet-process prior.  
}
\author{
Audrey Q. Fu
}
\seealso{
\code{\link{simuDataREM}} for simulating data.

\code{\link{plotSimulation}} for plotting simulated data.

\code{\link{DIRECT}} for clustering the data.
}
\examples{
## See example for simuDataREM.
}
% Add one or more standard keywords, see file 'KEYWORDS' in the
% R documentation directory.
