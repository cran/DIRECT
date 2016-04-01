\name{tc.data}
\alias{tc.data}
\docType{data}
\title{
Time-Course Microarray Gene Expression Data
}
\description{
This data set contains quantile-normalized microarray gene expression measurements of 163 genes from four replicates at 18 time points.  These data are part of the time-course experiment performed on Drosophila with a 5-min pulse of Notch activation (Housden et al. 2013).  The experiment was carried out by Sarah Bray, Ben Housden, Alena Krejci and Bettina Fischer; see details in Housden et al. (2013).
}
\usage{data(tc.data)}
\format{
  A data frame with 163 observations on the 74 variables.  The first two variables are \code{GeneID} and \code{GeneName}.
  
  Other variables are log2 fold change of treated cells over control cells for 4 biological replicates at 18 time points.  They are organized as follows: values for replicates 1 through 4 at time 1; values for replicates 1 through 4 at time 2; and so on.
}
\details{
The 18 time points are (in min):

0,5,10,15,20,25,30,35,40,50,60,70,80,90,100,110,120,150.

Microarray data have been cleaned and normalized.  Missing values are imputed.  See supplementary material for Fu, Russell, Bray and Tavare for detail on data pre-processing and missing value imputation.
}
\references{
Fu, A. Q., Russell, S., Bray, S. and Tavare, S. (2013) Bayesian clustering of replicated time-course gene expression data with weak signals.  The Annals of Applied Statistics. 7(3) 1334-1361.  

Housden, B. E., Fu, A. Q., Krejci, A., Bernard, F., Fischer, B., Tavare, S., Russell, S. and Bray, S. J. (2013)  Transcriptional dynamics elicited by a short pulse of Notch activation involves feed-forward regulation by E(spl)/Hes genes. PLoS Genetics 9 1 e1003162.
}
\examples{
\dontrun{
# Compute mean profiles for genes
# and plot the means as a heatmap with the color scale on the side

library (fields)	# to use function image.plot

data (tc.data)
times = c(0,5,10,15,20,25,30,35,40,50,60,70,80,90,100,110,120,150)

# Organize data into array of nGene-by-nTime-by-nRep
SKIP=2
nTime=length (times)
nGene = nrow (tc.data)
nRep = (ncol (tc.data) - SKIP) / nTime

ts = array (0, dim = c(nGene, nTime, nRep))
for (r in 1:nRep) {
    ts[,,r] = as.matrix (tc.data[,SKIP + (0:(nTime-1))*nRep + r])
}

# Compute mean profile for each gene
ts.mean = apply (ts, c(1,2), mean)

# Plot heatmap for mean profiles
image.plot (1:nGene, times, as.matrix(ts.mean), 
    xlab="gene", ylab="time (min)", 
    cex=1.5, cex.axis = 1.6, cex.lab = 1.6, 
    legend.shrink=1, legend.width=2, col=topo.colors(8))
}
}
\keyword{datasets}
