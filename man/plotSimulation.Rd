\name{plotSimulation}
\alias{plotSimulation}
%- Also NEED an '\alias' for EACH other topic documented here.
\title{
Plotting Data Simulated Under A Random-Effects Mixture Model}
\description{
Function \code{plotSimulation} displays sample means of data simulated under a random-effects mixture model.  Each plot  corresponds to a cluster.  May need to partition the plotting area to display all in one plot.
}
\usage{
plotSimulation(simudata, times = 1:ntime, nsize, 
    ntime = length(times), nrep, skip = 0, ...)
}
%- maybe also 'usage' for other objects documented here.
\arguments{
  \item{simudata}{
List produced by \code{\link{simuDataREM}}.  Contains simulated data.
}
  \item{times}{
Vector of length \code{ntime} indicating at which time points data are simulated.
}
  \item{nsize}{
An integer vector containing sizes of simulated clusters.
}
  \item{ntime}{
Number of time points.
}
  \item{nrep}{
Number of replicates.
}
  \item{skip}{
Not for use.
}
  \item{\dots}{
Addition arguments for \code{plot}.
}
}
\value{
None.
}
\references{
Fu, A. Q., Russell, S., Bray, S. and Tavare, S. (2013) Bayesian clustering of replicated time-course gene expression data with weak signals. The Annals of Applied Statistics. 7(3) 1334-1361.
}
\author{
Audrey Q. Fu
}
\seealso{
\code{\link{simuDataREM}} for simulating data.

\code{\link{outputData}} for writing simulated data and parameter values used in simulation into external files.

\code{\link{DIRECT}} for clustering the data.
}
\examples{
## See example for simuDataREM.
}
% Add one or more standard keywords, see file 'KEYWORDS' in the
% R documentation directory.
