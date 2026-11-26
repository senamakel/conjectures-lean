"""Curated conjectures of Cazenave arXiv:2611.03879 sec. 7, as (name, lhs, rhs) meaning lhs <= rhs."""
import math
C = [
 ('C1  lam2+1 <= R',            lambda I: I['l2'] + 1,                 lambda I: I['R']),
 ('C1s1 l1^2+(l2+1)^2 <= 2m',   lambda I: I['l1']**2 + (I['l2']+1)**2, lambda I: 2*I['m']),
 ('C1s2 l1(l2+1) <= m',         lambda I: I['l1']*(I['l2']+1),         lambda I: I['m']),
 ('C2  lam2 <= mu1-2',          lambda I: I['l2'],                     lambda I: I['mu1'] - 2),
 ('C3  2R <= rk*l1',            lambda I: 2*I['R'],                    lambda I: I['rA']*I['l1']),
 ('C4  l1 <= R+mu2',            lambda I: I['l1'],                     lambda I: I['R'] + I['mu2']),
 ('C5  mu2+rk <= 2m',           lambda I: I['mu2'] + I['rA'],          lambda I: 2*I['m']),
 ('C6i (m+1)/2 <= R^2',         lambda I: (I['m']+1)/2,                lambda I: I['R']**2),
 ('C6ii 4l2+1 <= mu2^2',        lambda I: 4*I['l2'] + 1,               lambda I: I['mu2']**2),
 ('C6iii 4l2+8 <= mu1^2',       lambda I: 4*I['l2'] + 8,               lambda I: I['mu1']**2),
 ('C6iv-a 2/3 sqrt m+1/3 <= R', lambda I: 2/3*math.sqrt(I['m']) + 1/3, lambda I: I['R']),
 ('C6iv-b 3/2sqrt rk+1-3/sqrt2... <= R', lambda I: 1.5*math.sqrt(I['rA']) + 1 - 1.5*math.sqrt(2), lambda I: I['R']),
 ('C7  rad+sqrt2-3/2 <= R',     lambda I: I['rad'] + math.sqrt(2) - 1.5, lambda I: I['R']),
]
