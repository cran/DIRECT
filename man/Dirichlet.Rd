\name{Dirichlet}
\alias{rDirichlet}
\alias{dDirichlet}
%- Also NEED an '\alias' for EACH other topic documented here.
\title{
The Dirichlet Distribution
}
\description{
Functions to compute the density of a Dirichlet distribution and to generate random realizations from such a distribution.
}
\usage{
dDirichlet (x, alpha, log=FALSE)
rDirichlet (n, alpha)
}
%- maybe also 'usage' for other objects documented here.
\arguments{
  \item{alpha}{
Shape parameter vector.  
}
  \item{x}{
Vector of the same length as \code{alpha}.
}
  \item{n}{
Number of realizations (vectors) to generate.
}
  \item{log}{
Logical value.  TRUE if computing the log density.  Default is FALSE.
}
}
\value{
\code{rDirichlet} returns a vector of the same length as \code{alpha} if \code{n}=1, or a matrix with each row being an independent realization otherwise.
}
\author{
Audrey Q. Fu coded \code{dDirichlet}.  

The code for \code{rDirichlet} is taken from a similar function in R package \code{gregmisc} by Gregory R. Warnes. His code was based on code posted by Ben Bolker to R-News on 15 Dec 2000.  See documentation in gregmisc for further information.
}
\examples{
\dontrun{
x <- rDirichlet (5, rep (0.5, 3))
dDirichlet (x[1, ], rep (0.5, 3))
}
}
% Add one or more standard keywords, see file 'KEYWORDS' in the
% R documentation directory.
