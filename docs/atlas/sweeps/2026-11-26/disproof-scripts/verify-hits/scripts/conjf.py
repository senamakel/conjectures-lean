from fractions import Fraction as F
def conj(k):
    r = k % 9
    return {0:F(4*k,9*k+9),1:F(4,9),2:F(4*k+1,9*k+9),3:F(4*k+24,9*k+72),4:F(4*k+2,9*k+9),
            5:F(4*k+1,9*k+16),6:F(4*k+3,9*k+9),7:F(4*k-1,9*k+9),8:F(4,9)}[r]
