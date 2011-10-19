\name{plotClustersMean}
\alias{plotClustersMean}
%- Also NEED an '\alias' for EACH other topic documented here.
\title{
Plotting Clustered Mean Vectors
}
\description{
Function \code{plotClustersMean} produces a plot of multiple panels.  Each panel displays for a inferred cluster the mean vectors of items allocated to this cluster, as well as the inferred cluster mean vector.  See figures in Fu, Russell, Bray and Tavare.
}
\usage{
plotClustersMean(data, data.summary, 
    SKIP, nTime = length(times), times = 1:nTime, ...)
}
%- maybe also 'usage' for other objects documented here.
\arguments{
  \item{data}{
An \eqn{N \times JR} matrix of continuous values, or a data frame containing such a matrix.  \eqn{N} is the number if items, \eqn{J} the number of time points (or experimental conditions) and \eqn{R} the number of replicates.  Each row contains values for Replicates 1 through \eqn{R} under Condition 1, values for Replicates 1 through \eqn{R} under Condition 2, and so on.
}
  \item{data.summary}{
The list generated from \code{\link{summaryDIRECT}} that contains processed posterior estimates.
}
  \item{SKIP}{
Number of columns in \code{data} to be skipped when processing the data.
}
  \item{nTime}{
Number of time points (or experimental conditions).
}
  \item{times}{
An integer vector of length \code{nTime}, indicating times (or experimental conditions).
}
  \item{\dots}{
Additional arguments for \code{plot}.
}
}
\value{
None.
}
\author{
Audrey Q. Fu
}
\references{
Fu, A. Q., Russell, S., Bray, S. J. and Tavare, S. Bayesian clustering with the Dirichlet-process prior.  
}
\seealso{
\code{\link{summaryDIRECT}} for processing MCMC estimates for clustering and generating the list \code{data.summary} used here.

\code{\link{plotClustersPCA}}, \code{\link{plotClustersSD}}, \code{\link{plotSimulation}}.
}
\examples{
## See example in DIRECT.
}
% Add one or more standard keywords, see file 'KEYWORDS' in the
% R documentation directory.
