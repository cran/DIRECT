\name{summaryDIRECT}
\alias{summaryDIRECT}
%- Also NEED an '\alias' for EACH other topic documented here.
\title{
Processing Posterior Estimates for Clustering Under DIRECT
}
\description{
Function \code{summaryDIRECT} processes posterior estimates in the output files from \code{\link{DIRECT}} for clustering and parameter estimation.
}
\usage{
summaryDIRECT(data.name, PERM.ADJUST = FALSE)
}
%- maybe also 'usage' for other objects documented here.
\arguments{
  \item{data.name}{
A character string indicating the prefix of output files.  
}
  \item{PERM.ADJUST}{
If TRUE, add 1 to labels of mixture components such that the labels start from 1 instead of 0.
}
}
\details{
Output files from \code{\link{DIRECT}} include MCMC samples before relabeling and permuted labels of mixture components after relabeling.  Function \code{summaryDIRECT} uses permuted labels stored in output file *_mcmc_perms.out to reorganize the MCMC samples stored in other output files *_mcmc_cs.out, *_mcmc_pars.out and *_mcmc_probs.out.  It defines each mixture component as a cluster.
}
\value{
A list with components:
  \item{nitem}{
The number of items in the data.
}
  \item{nclust}{
The number of inferred clusters.
}
  \item{top.clust.alloc}{
A vector of length \code{nitem}, each component being the maximum posterior probability of allocating the corresponding item to a cluster.
}
  \item{cluster.sizes}{
Vector of cluster sizes.
}
  \item{top.clust.labels}{
An integer vector of labels of inferred clusters.  The integers are not necessarily consecutive; that is, an inferred mixture component that is associated with items at small posterior allocation probabilities is dropped from the final list of cluster labels.
}
  \item{top2allocations}{
A data frame containing "first", the most likely allocation; "second", the second most likely allocation; "prob1", the posterior allocation probability associated with "first"; and "prob2", the posterior allocation probability associated with "second".
}
  \item{post.alloc.probs}{
A \code{nitem}-by-\code{nclust} matrix of mean posterior allocation probability matrix.
}
  \item{post.clust.pars.mean}{
A matrix of \code{nclust} rows.  Each row, corresponding to an inferred cluster, contains the posterior mean estimates of cluster-specific parameters.
}
  \item{post.clust.pars.median}{
A matrix of \code{nclust} rows.  Each row, corresponding to an inferred cluster, contains the posterior median estimates of cluster-specific parameters.
}
  \item{misc}{A list containing two components:
\itemize{
  \item \code{post.pars.mean}: Matrix each row of which contains the posterior mean estimates of parameters for a mixture component.
  \item \code{post.pars.median}: Matrix each row of which contains the posterior median estimates of parameters for a mixture component. 
}
}
}
\references{
Fu, A. Q., Russell, S., Bray, S. J. and Tavare, S. (2011) Bayesian clustering with the Dirichlet-process prior.  
}
\author{
Audrey Q. Fu
}
\seealso{
\code{\link{DIRECT}} for what output files are produced.

\code{\link{simuDataREM}} for simulating data under the mixture random-effects model.
}
\examples{
## See example in DIRECT.
}
% Add one or more standard keywords, see file 'KEYWORDS' in the
% R documentation directory.
