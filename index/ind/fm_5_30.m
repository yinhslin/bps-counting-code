f = SeriesData[x, 0, {1, 0, s^2 + s^2/b^2 + b^2*s^2, -(s/b) - b*s + s^3/b^3 + 
       b^3*s^3, s^2 + 2*s^4 + (2*s^4)/b^4 + s^4/b^2 + b^2*s^4 + 2*b^4*s^4, 
      (2*s^5)/b^5 + 2*b^5*s^5 + (-s - 2*s^3 + s^5)/b + b*(-s - 2*s^3 + s^5) + 
       (-s^3 + s^5)/b^3 + b^3*(-s^3 + s^5), 2*s^2 + s^4 + 2*s^6 + 
       (3*s^6)/b^6 + (2*s^6)/b^2 + 2*b^2*s^6 + 3*b^6*s^6 + (-s^4 + s^6)/b^4 + 
       b^4*(-s^4 + s^6), (3*s^7)/b^7 + 3*b^7*s^7 + 
       (-s - 3*s^3 - 2*s^5 + 2*s^7)/b + b*(-s - 3*s^3 - 2*s^5 + 2*s^7) + 
       (-s^5 + 2*s^7)/b^5 + b^5*(-s^5 + 2*s^7) + (-s^3 - s^5 + 2*s^7)/b^3 + 
       b^3*(-s^3 - s^5 + 2*s^7), (5*s^8)/b^8 + 5*b^8*s^8 + 
       (2*s^6*(-1 + s^2))/b^6 + 2*b^6*s^6*(-1 + s^2) + 
       (s^4*(-1 - s^2 + 3*s^4))/b^4 + b^4*s^4*(-1 - s^2 + 3*s^4) + 
       s^2*(3 + 3*s^2 + s^4 + 3*s^6) + (s^2 + s^4 + 2*s^8)/b^2 + 
       b^2*(s^2 + s^4 + 2*s^8), (5*s^9)/b^9 + 5*b^9*s^9 + 
       (2*s^7*(-1 + s^2))/b^7 + 2*b^7*s^7*(-1 + s^2) + 
       (s^5*(-1 + 3*s^4))/b^5 + b^5*s^5*(-1 + 3*s^4) + 
       (s^3*(-1 - 2*s^2 + 3*s^6))/b^3 + b^3*s^3*(-1 - 2*s^2 + 3*s^6) + 
       (s*(-1 - 4*s^2 - 5*s^4 + 3*s^8))/b + b*s*(-1 - 4*s^2 - 5*s^4 + 3*s^8), 
      (7*s^10)/b^10 + 7*b^10*s^10 + (s^8*(-2 + 3*s^2))/b^8 + 
       b^8*s^8*(-2 + 3*s^2) + (s^6*(-2 - s^2 + 3*s^4))/b^4 + 
       b^4*s^6*(-2 - s^2 + 3*s^4) + (s^6*(-3 - s^2 + 4*s^4))/b^6 + 
       b^6*s^6*(-3 - s^2 + 4*s^4) + s^2*(4 + 7*s^2 + s^4 + 3*s^8) + 
       (s^2 + 3*s^4 - s^6 + 4*s^10)/b^2 + b^2*(s^2 + 3*s^4 - s^6 + 4*s^10), 
      (7*s^11)/b^11 + 7*b^11*s^11 + (3*s^9*(-1 + s^2))/b^9 + 
       3*b^9*s^9*(-1 + s^2) + (s^7*(-2 - s^2 + 4*s^4))/b^7 + 
       b^7*s^7*(-2 - s^2 + 4*s^4) + (s^3*(-1 - 2*s^2 - 2*s^4 + s^6 + 4*s^8))/
        b^3 + b^3*s^3*(-1 - 2*s^2 - 2*s^4 + s^6 + 4*s^8) + 
       (s*(-1 - 6*s^2 - 7*s^4 - 4*s^6 + s^8 + 4*s^10))/b + 
       b*s*(-1 - 6*s^2 - 7*s^4 - 4*s^6 + s^8 + 4*s^10) + (s^9 + 4*s^11)/b^5 + 
       b^5*(s^9 + 4*s^11), (10*s^12)/b^12 + 10*b^12*s^12 + 
       (s^10*(-3 + 4*s^2))/b^10 + b^10*s^10*(-3 + 4*s^2) + 
       (s^8*(-3 + 5*s^4))/b^8 + b^8*s^8*(-3 + 5*s^4) + 
       (2*s^6*(-1 - 2*s^2 + 2*s^6))/b^6 + 2*b^6*s^6*(-1 - 2*s^2 + 2*s^6) + 
       (s^6*(-1 - 5*s^2 + 5*s^6))/b^4 + b^4*s^6*(-1 - 5*s^2 + 5*s^6) + 
       (s^2*(2 + 5*s^2 + 3*s^4 - 3*s^6 - s^8 + 4*s^10))/b^2 + 
       b^2*s^2*(2 + 5*s^2 + 3*s^4 - 3*s^6 - s^8 + 4*s^10) + 
       s^2*(5 + 11*s^2 + 7*s^4 - s^6 - s^8 + 6*s^10), 
      (10*s^13)/b^13 + 10*b^13*s^13 + (4*s^11*(-1 + s^2))/b^11 + 
       4*b^11*s^11*(-1 + s^2) + (s^9*(-3 + 5*s^4))/b^7 + 
       b^7*s^9*(-3 + 5*s^4) + (s^9*(-4 - s^2 + 5*s^4))/b^9 + 
       b^9*s^9*(-4 - s^2 + 5*s^4) + (s^7*(3 + s^4 + 6*s^6))/b^5 + 
       b^5*s^7*(3 + s^4 + 6*s^6) + (s^3*(-1 - 3*s^2 - s^4 + 5*s^10))/b^3 + 
       b^3*s^3*(-1 - 3*s^2 - s^4 + 5*s^10) + 
       (s*(-1 - 8*s^2 - 12*s^4 - 7*s^6 + s^8 + 5*s^12))/b + 
       b*s*(-1 - 8*s^2 - 12*s^4 - 7*s^6 + s^8 + 5*s^12), 
      (13*s^14)/b^14 + 13*b^14*s^14 + (s^12*(-4 + 5*s^2))/b^12 + 
       b^12*s^12*(-4 + 5*s^2) + (s^10*(-4 + s^2 + 7*s^4))/b^10 + 
       b^10*s^10*(-4 + s^2 + 7*s^4) + (s^8*(-1 - 2*s^2 + s^4 + 5*s^6))/b^8 + 
       b^8*s^8*(-1 - 2*s^2 + s^4 + 5*s^6) + 
       (s^6*(-3 - 5*s^2 - 3*s^4 + 6*s^8))/b^6 + 
       b^6*s^6*(-3 - 5*s^2 - 3*s^4 + 6*s^8) + 
       (s^4*(1 - s^2 - 7*s^4 - 3*s^6 - s^8 + 5*s^10))/b^4 + 
       b^4*s^4*(1 - s^2 - 7*s^4 - 3*s^6 - s^8 + 5*s^10) + 
       s^2*(6 + 17*s^2 + 15*s^4 - s^6 - 2*s^8 + 6*s^12) + 
       (s^2*(2 + 8*s^2 + 6*s^4 - 3*s^6 - s^8 + 7*s^12))/b^2 + 
       b^2*s^2*(2 + 8*s^2 + 6*s^4 - 3*s^6 - s^8 + 7*s^12), 
      (14*s^15)/b^15 + 14*b^15*s^15 + (5*s^13*(-1 + s^2))/b^13 + 
       5*b^13*s^13*(-1 + s^2) + (s^11*(-6 - s^2 + 6*s^4))/b^11 + 
       b^11*s^11*(-6 - s^2 + 6*s^4) + (s^9*(-2 - 5*s^2 + 6*s^6))/b^9 + 
       b^9*s^9*(-2 - 5*s^2 + 6*s^6) + (s^7*(1 - s^2 - 3*s^4 + s^6 + 7*s^8))/
        b^7 + b^7*s^7*(1 - s^2 - 3*s^4 + s^6 + 7*s^8) + 
       (s^5*(1 + 6*s^2 + 3*s^4 + 2*s^6 + s^8 + 7*s^10))/b^5 + 
       b^5*s^5*(1 + 6*s^2 + 3*s^4 + 2*s^6 + s^8 + 7*s^10) + 
       (s^3*(-2 - 4*s^2 - s^4 - s^6 + 2*s^8 + 7*s^12))/b^3 + 
       b^3*s^3*(-2 - 4*s^2 - s^4 - s^6 + 2*s^8 + 7*s^12) + 
       (s*(-1 - 11*s^2 - 18*s^4 - 12*s^6 - 3*s^8 + 2*s^10 - s^12 + 6*s^14))/
        b + b*s*(-1 - 11*s^2 - 18*s^4 - 12*s^6 - 3*s^8 + 2*s^10 - s^12 + 
         6*s^14), (17*s^16)/b^16 + 17*b^16*s^16 + (s^14*(-5 + 6*s^2))/b^14 + 
       b^14*s^14*(-5 + 6*s^2) + (s^12*(-6 + s^2 + 8*s^4))/b^12 + 
       b^12*s^12*(-6 + s^2 + 8*s^4) + (s^10*(-1 - s^2 + 2*s^4 + 7*s^6))/
        b^10 + b^10*s^10*(-1 - s^2 + 2*s^4 + 7*s^6) + 
       (s^8*(-2 - s^2 + 8*s^8))/b^8 + b^8*s^8*(-2 - s^2 + 8*s^8) + 
       (s^6*(-2 - 8*s^2 - 8*s^4 - s^6 - 2*s^8 + 6*s^10))/b^6 + 
       b^6*s^6*(-2 - 8*s^2 - 8*s^4 - s^6 - 2*s^8 + 6*s^10) + 
       (s^2*(3 + 11*s^2 + 14*s^4 + s^6 - 8*s^8 - s^10 + 7*s^14))/b^2 + 
       b^2*s^2*(3 + 11*s^2 + 14*s^4 + s^6 - 8*s^8 - s^10 + 7*s^14) + 
       s^2*(7 + 24*s^2 + 27*s^4 + 6*s^6 - 7*s^8 + s^10 + 2*s^12 + 9*s^14) + 
       (s^4 - 10*s^8 - 10*s^10 - s^14 + 8*s^16)/b^4 + 
       b^4*(s^4 - 10*s^8 - 10*s^10 - s^14 + 8*s^16), 
      (18*s^17)/b^17 + 18*b^17*s^17 + (s^15*(-6 + 7*s^2))/b^15 + 
       b^15*s^15*(-6 + 7*s^2) + (s^13*(-7 + 8*s^4))/b^13 + 
       b^13*s^13*(-7 + 8*s^4) + (s^11*(-4 - 6*s^2 + 7*s^6))/b^11 + 
       b^11*s^11*(-4 - 6*s^2 + 7*s^6) + (s^9*(-2 - 6*s^2 - 3*s^4 + 8*s^8))/
        b^9 + b^9*s^9*(-2 - 6*s^2 - 3*s^4 + 8*s^8) + 
       (s^7*(4 + 2*s^2 - 6*s^4 + s^6 + s^8 + 8*s^10))/b^7 + 
       b^7*s^7*(4 + 2*s^2 - 6*s^4 + s^6 + s^8 + 8*s^10) + 
       (s^7*(10 + 11*s^2 + s^4 + 3*s^6 + 2*s^8 + 9*s^10))/b^5 + 
       b^5*s^7*(10 + 11*s^2 + s^4 + 3*s^6 + 2*s^8 + 9*s^10) + 
       (s^3*(-2 - 7*s^2 - s^4 + 3*s^6 + s^8 + 8*s^14))/b^3 + 
       b^3*s^3*(-2 - 7*s^2 - s^4 + 3*s^6 + s^8 + 8*s^14) + 
       (s*(-1 - 14*s^2 - 29*s^4 - 20*s^6 - 4*s^8 + 2*s^10 - 2*s^12 - 2*s^14 + 
          8*s^16))/b + b*s*(-1 - 14*s^2 - 29*s^4 - 20*s^6 - 4*s^8 + 2*s^10 - 
         2*s^12 - 2*s^14 + 8*s^16), (22*s^18)/b^18 + 22*b^18*s^18 + 
       (7*s^16*(-1 + s^2))/b^16 + 7*b^16*s^16*(-1 + s^2) + 
       (s^14*(-8 + s^2 + 9*s^4))/b^14 + b^14*s^14*(-8 + s^2 + 9*s^4) + 
       (s^12*(-3 - s^4 + 8*s^6))/b^8 + b^8*s^12*(-3 - s^4 + 8*s^6) + 
       (s^12*(-2 - 3*s^2 + 2*s^4 + 8*s^6))/b^12 + 
       b^12*s^12*(-2 - 3*s^2 + 2*s^4 + 8*s^6) + 
       (s^10*(-1 + s^2 + 3*s^4 + 2*s^6 + 10*s^8))/b^10 + 
       b^10*s^10*(-1 + s^2 + 3*s^4 + 2*s^6 + 10*s^8) + 
       (s^6*(-4 - 12*s^2 - 13*s^4 - 5*s^6 - 2*s^8 - 2*s^10 + 10*s^12))/b^6 + 
       b^6*s^6*(-4 - 12*s^2 - 13*s^4 - 5*s^6 - 2*s^8 - 2*s^10 + 10*s^12) + 
       (s^4*(2 - 12*s^4 - 18*s^6 - 5*s^8 - 3*s^10 - 2*s^12 + 8*s^14))/b^4 + 
       b^4*s^4*(2 - 12*s^4 - 18*s^6 - 5*s^8 - 3*s^10 - 2*s^12 + 8*s^14) + 
       s^2*(8 + 33*s^2 + 42*s^4 + 19*s^6 - 9*s^8 + s^10 + 4*s^12 + 2*s^14 + 
         9*s^16) + (s^2*(3 + 16*s^2 + 21*s^4 + 7*s^6 - 14*s^8 - 2*s^10 + 
          s^12 + s^14 + 10*s^16))/b^2 + b^2*s^2*(3 + 16*s^2 + 21*s^4 + 
         7*s^6 - 14*s^8 - 2*s^10 + s^12 + s^14 + 10*s^16), 
      (23*s^19)/b^19 + 23*b^19*s^19 + (s^17*(-7 + 8*s^2))/b^17 + 
       b^17*s^17*(-7 + 8*s^2) + (s^15*(-9 + 2*s^2 + 10*s^4))/b^15 + 
       b^15*s^15*(-9 + 2*s^2 + 10*s^4) + (s^13*(-4 - 5*s^2 + s^4 + 9*s^6))/
        b^13 + b^13*s^13*(-4 - 5*s^2 + s^4 + 9*s^6) + 
       (s^11*(-5 - 9*s^2 - 3*s^4 - s^6 + 10*s^8))/b^11 + 
       b^11*s^11*(-5 - 9*s^2 - 3*s^4 - s^6 + 10*s^8) + 
       (s^9*(1 - 6*s^2 - 11*s^4 - s^6 - s^8 + 9*s^10))/b^9 + 
       b^9*s^9*(1 - 6*s^2 - 11*s^4 - s^6 - s^8 + 9*s^10) + 
       (s^7*(4 + 8*s^2 - 4*s^4 - 2*s^6 + 3*s^8 + s^10 + 10*s^12))/b^7 + 
       b^7*s^7*(4 + 8*s^2 - 4*s^4 - 2*s^6 + 3*s^8 + s^10 + 10*s^12) + 
       (s^5*(1 + 13*s^2 + 25*s^4 + 6*s^6 + 5*s^8 + 4*s^10 + 2*s^12 + 
          10*s^14))/b^5 + b^5*s^5*(1 + 13*s^2 + 25*s^4 + 6*s^6 + 5*s^8 + 
         4*s^10 + 2*s^12 + 10*s^14) + (s^3*(-3 - 10*s^2 - 5*s^4 + 11*s^6 + 
          s^8 + 2*s^10 + 10*s^16))/b^3 + b^3*s^3*(-3 - 10*s^2 - 5*s^4 + 
         11*s^6 + s^8 + 2*s^10 + 10*s^16) + 
       (s*(-1 - 18*s^2 - 41*s^4 - 37*s^6 - 6*s^8 - 2*s^10 - s^12 - 5*s^14 - 
          2*s^16 + 10*s^18))/b + b*s*(-1 - 18*s^2 - 41*s^4 - 37*s^6 - 6*s^8 - 
         2*s^10 - s^12 - 5*s^14 - 2*s^16 + 10*s^18), 
      (28*s^20)/b^20 + 28*b^20*s^20 + (s^18*(-8 + 9*s^2))/b^18 + 
       b^18*s^18*(-8 + 9*s^2) + (s^16*(-11 + s^2 + 11*s^4))/b^16 + 
       b^16*s^16*(-11 + s^2 + 11*s^4) + (s^14*(-4 - 4*s^2 + s^4 + 9*s^6))/
        b^14 + b^14*s^14*(-4 - 4*s^2 + s^4 + 9*s^6) + 
       (s^12*(-2 - 3*s^2 + 3*s^4 + s^6 + 11*s^8))/b^12 + 
       b^12*s^12*(-2 - 3*s^2 + 3*s^4 + s^6 + 11*s^8) + 
       (s^10*(3 + 6*s^2 + s^4 + 4*s^6 + s^8 + 10*s^10))/b^10 + 
       b^10*s^10*(3 + 6*s^2 + s^4 + 4*s^6 + s^8 + 10*s^10) + 
       (s^8*(-3 + s^2 - 2*s^4 + s^6 - s^8 + 12*s^12))/b^8 + 
       b^8*s^8*(-3 + s^2 - 2*s^4 + s^6 - s^8 + 12*s^12) + 
       (s^6*(-3 - 20*s^2 - 19*s^4 - 15*s^6 - 4*s^8 - 6*s^10 - 2*s^12 + 
          10*s^14))/b^6 + b^6*s^6*(-3 - 20*s^2 - 19*s^4 - 15*s^6 - 4*s^8 - 
         6*s^10 - 2*s^12 + 10*s^14) + (s^4*(2 + 2*s^2 - 19*s^4 - 25*s^6 - 
          17*s^8 - 3*s^10 - 4*s^12 - s^14 + 12*s^16))/b^4 + 
       b^4*s^4*(2 + 2*s^2 - 19*s^4 - 25*s^6 - 17*s^8 - 3*s^10 - 4*s^12 - 
         s^14 + 12*s^16) + (s^2*(4 + 21*s^2 + 35*s^4 + 15*s^6 - 11*s^8 - 
          13*s^10 + 3*s^12 + 2*s^14 + 10*s^18))/b^2 + 
       b^2*s^2*(4 + 21*s^2 + 35*s^4 + 15*s^6 - 11*s^8 - 13*s^10 + 3*s^12 + 
         2*s^14 + 10*s^18) + s^2*(9 + 44*s^2 + 66*s^4 + 38*s^6 - 2*s^8 - 
         10*s^10 + 8*s^12 + 6*s^14 + 2*s^16 + 12*s^18), 
      (29*s^21)/b^21 + 29*b^21*s^21 + (9*s^19*(-1 + s^2))/b^19 + 
       9*b^19*s^19*(-1 + s^2) + (s^17*(-11 + 2*s^2 + 11*s^4))/b^17 + 
       b^17*s^17*(-11 + 2*s^2 + 11*s^4) + 
       (s^15*(-5 - 3*s^2 + 3*s^4 + 11*s^6))/b^15 + 
       b^15*s^15*(-5 - 3*s^2 + 3*s^4 + 11*s^6) + 
       (s^13*(-4 - 7*s^2 + s^6 + 12*s^8))/b^13 + 
       b^13*s^13*(-4 - 7*s^2 + s^6 + 12*s^8) + 
       (s^11*(-2 - 12*s^2 - 12*s^4 - 3*s^6 - s^8 + 11*s^10))/b^11 + 
       b^11*s^11*(-2 - 12*s^2 - 12*s^4 - 3*s^6 - s^8 + 11*s^10) + 
       (s^9*(-1 - 5*s^2 - 18*s^4 - 3*s^6 - s^8 - s^10 + 12*s^12))/b^9 + 
       b^9*s^9*(-1 - 5*s^2 - 18*s^4 - 3*s^6 - s^8 - s^10 + 12*s^12) + 
       (s^7*(8 + 14*s^2 + 5*s^4 - 11*s^6 + 5*s^8 + 3*s^10 + 11*s^14))/b^7 + 
       b^7*s^7*(8 + 14*s^2 + 5*s^4 - 11*s^6 + 5*s^8 + 3*s^10 + 11*s^14) + 
       (s^7*(18 + 40*s^2 + 25*s^4 + 3*s^6 + 8*s^8 + 6*s^10 + s^12 + 12*s^14))/
        b^5 + b^5*s^7*(18 + 40*s^2 + 25*s^4 + 3*s^6 + 8*s^8 + 6*s^10 + s^12 + 
         12*s^14) + (s^3*(-4 - 15*s^2 - 9*s^4 + 15*s^6 + 14*s^8 + 12*s^18))/
        b^3 + b^3*s^3*(-4 - 15*s^2 - 9*s^4 + 15*s^6 + 14*s^8 + 12*s^18) + 
       (s*(-1 - 22*s^2 - 59*s^4 - 59*s^6 - 17*s^8 + 6*s^10 - 6*s^12 - 
          11*s^14 - 6*s^16 - s^18 + 12*s^20))/b + 
       b*s*(-1 - 22*s^2 - 59*s^4 - 59*s^6 - 17*s^8 + 6*s^10 - 6*s^12 - 
         11*s^14 - 6*s^16 - s^18 + 12*s^20), (34*s^22)/b^22 + 34*b^22*s^22 + 
       (s^20*(-9 + 11*s^2))/b^20 + b^20*s^20*(-9 + 11*s^2) + 
       (s^18*(-13 + 3*s^2 + 13*s^4))/b^18 + b^18*s^18*
        (-13 + 3*s^2 + 13*s^4) + (s^16*(-7 - 6*s^2 + s^4 + 11*s^6))/b^16 + 
       b^16*s^16*(-7 - 6*s^2 + s^4 + 11*s^6) + 
       (s^14*(-5 - 6*s^2 + s^4 - s^6 + 13*s^8))/b^14 + 
       b^14*s^14*(-5 - 6*s^2 + s^4 - s^6 + 13*s^8) + 
       (s^12*(5 - 2*s^4 + 2*s^6 - s^8 + 11*s^10))/b^12 + 
       b^12*s^12*(5 - 2*s^4 + 2*s^6 - s^8 + 11*s^10) + 
       (s^10*(1 + 14*s^2 + 5*s^4 + 10*s^6 + 5*s^8 + s^10 + 14*s^12))/b^10 + 
       b^10*s^10*(1 + 14*s^2 + 5*s^4 + 10*s^6 + 5*s^8 + s^10 + 14*s^12) + 
       (s^8*(-2 - 2*s^2 + 7*s^4 - 5*s^6 - 2*s^8 - s^10 + 12*s^14))/b^8 + 
       b^8*s^8*(-2 - 2*s^2 + 7*s^4 - 5*s^6 - 2*s^8 - s^10 + 12*s^14) + 
       (s^6*(-5 - 29*s^2 - 37*s^4 - 19*s^6 - 10*s^8 - 11*s^10 - 5*s^12 + 
          14*s^16))/b^6 + b^6*s^6*(-5 - 29*s^2 - 37*s^4 - 19*s^6 - 10*s^8 - 
         11*s^10 - 5*s^12 + 14*s^16) + 
       (s^4*(3 + 3*s^2 - 25*s^4 - 43*s^6 - 29*s^8 - 8*s^10 - 7*s^12 - 
          4*s^14 - s^16 + 12*s^18))/b^4 + b^4*s^4*(3 + 3*s^2 - 25*s^4 - 
         43*s^6 - 29*s^8 - 8*s^10 - 7*s^12 - 4*s^14 - s^16 + 12*s^18) + 
       s^2*(10 + 57*s^2 + 96*s^4 + 68*s^6 + 5*s^8 - 14*s^10 + 16*s^12 + 
         14*s^14 + 6*s^16 + 12*s^20) + 
       (s^2*(4 + 28*s^2 + 50*s^4 + 30*s^6 - 14*s^8 - 18*s^10 + 7*s^12 + 
          5*s^14 + s^16 + 14*s^20))/b^2 + b^2*s^2*(4 + 28*s^2 + 50*s^4 + 
         30*s^6 - 14*s^8 - 18*s^10 + 7*s^12 + 5*s^14 + s^16 + 14*s^20), 
      (36*s^23)/b^23 + 36*b^23*s^23 + (11*s^21*(-1 + s^2))/b^21 + 
       11*b^21*s^21*(-1 + s^2) + (s^19*(-14 + 2*s^2 + 13*s^4))/b^19 + 
       b^19*s^19*(-14 + 2*s^2 + 13*s^4) + (2*s^17*(-3 - 2*s^2 + s^4 + 6*s^6))/
        b^17 + 2*b^17*s^17*(-3 - 2*s^2 + s^4 + 6*s^6) + 
       (s^15*(-5 - 4*s^2 + 6*s^4 + 2*s^6 + 14*s^8))/b^15 + 
       b^15*s^15*(-5 - 4*s^2 + 6*s^4 + 2*s^6 + 14*s^8) + 
       (s^13*(1 - 7*s^2 - 7*s^4 + s^6 + s^8 + 13*s^10))/b^13 + 
       b^13*s^13*(1 - 7*s^2 - 7*s^4 + s^6 + s^8 + 13*s^10) + 
       (s^11*(-7 - 15*s^2 - 23*s^4 - 5*s^6 - 2*s^8 + 14*s^12))/b^11 + 
       b^11*s^11*(-7 - 15*s^2 - 23*s^4 - 5*s^6 - 2*s^8 + 14*s^12) + 
       (s^9*(3 - 7*s^2 - 21*s^4 - 19*s^6 - 4*s^8 - 3*s^10 - s^12 + 13*s^14))/
        b^9 + b^9*s^9*(3 - 7*s^2 - 21*s^4 - 19*s^6 - 4*s^8 - 3*s^10 - s^12 + 
         13*s^14) + (s^7*(22 + 64*s^2 + 51*s^4 + 9*s^6 + 15*s^8 + 13*s^10 + 
          4*s^12 + 14*s^16))/b^5 + b^5*s^7*(22 + 64*s^2 + 51*s^4 + 9*s^6 + 
         15*s^8 + 13*s^10 + 4*s^12 + 14*s^16) + 
       (s^7*(9 + 25*s^2 + 13*s^4 - 8*s^6 + 5*s^8 + 7*s^10 + s^12 - s^14 + 
          14*s^16))/b^7 + b^7*s^7*(9 + 25*s^2 + 13*s^4 - 8*s^6 + 5*s^8 + 
         7*s^10 + s^12 - s^14 + 14*s^16) + 
       (s^3*(-5 - 21*s^2 - 18*s^4 + 23*s^6 + 30*s^8 + 2*s^12 + s^14 + 
          14*s^20))/b^3 + b^3*s^3*(-5 - 21*s^2 - 18*s^4 + 23*s^6 + 30*s^8 + 
         2*s^12 + s^14 + 14*s^20) + (s*(-1 - 27*s^2 - 81*s^4 - 94*s^6 - 
          35*s^8 + 9*s^10 - 15*s^12 - 15*s^14 - 13*s^16 - 4*s^18 + 14*s^22))/
        b + b*s*(-1 - 27*s^2 - 81*s^4 - 94*s^6 - 35*s^8 + 9*s^10 - 15*s^12 - 
         15*s^14 - 13*s^16 - 4*s^18 + 14*s^22), (42*s^24)/b^24 + 
       42*b^24*s^24 + (s^22*(-11 + 12*s^2))/b^22 + b^22*s^22*(-11 + 12*s^2) + 
       (5*s^20*(-3 + s^2 + 3*s^4))/b^20 + 5*b^20*s^20*(-3 + s^2 + 3*s^4) + 
       (s^18*(-8 - 4*s^2 + 3*s^4 + 13*s^6))/b^18 + 
       b^18*s^18*(-8 - 4*s^2 + 3*s^4 + 13*s^6) + 
       (s^16*(-9 - 11*s^2 + s^4 + 15*s^8))/b^16 + 
       b^16*s^16*(-9 - 11*s^2 + s^4 + 15*s^8) + 
       (s^14*(2 - 7*s^2 - 8*s^4 - 3*s^6 - 2*s^8 + 13*s^10))/b^14 + 
       b^14*s^14*(2 - 7*s^2 - 8*s^4 - 3*s^6 - 2*s^8 + 13*s^10) + 
       (s^12*(3 + 8*s^2 - 5*s^4 + 8*s^6 + s^8 - s^10 + 16*s^12))/b^12 + 
       b^12*s^12*(3 + 8*s^2 - 5*s^4 + 8*s^6 + s^8 - s^10 + 16*s^12) + 
       (s^10*(5 + 21*s^2 + 23*s^4 + 8*s^6 + 8*s^8 + 3*s^10 + 14*s^14))/b^10 + 
       b^10*s^10*(5 + 21*s^2 + 23*s^4 + 8*s^6 + 8*s^8 + 3*s^10 + 14*s^14) + 
       (s^8*(-6 - 5*s^2 + 8*s^4 + s^6 - 3*s^10 + s^12 + s^14 + 16*s^16))/
        b^8 + b^8*s^8*(-6 - 5*s^2 + 8*s^4 + s^6 - 3*s^10 + s^12 + s^14 + 
         16*s^16) + (s^6*(-5 - 42*s^2 - 60*s^4 - 34*s^6 - 25*s^8 - 17*s^10 - 
          12*s^12 - 2*s^14 + 14*s^18))/b^6 + b^6*s^6*(-5 - 42*s^2 - 60*s^4 - 
         34*s^6 - 25*s^8 - 17*s^10 - 12*s^12 - 2*s^14 + 14*s^18) + 
       (s^4*(4 + 6*s^2 - 34*s^4 - 68*s^6 - 51*s^8 - 24*s^10 - 10*s^12 - 
          10*s^14 - 3*s^16 + 16*s^20))/b^4 + 
       b^4*s^4*(4 + 6*s^2 - 34*s^4 - 68*s^6 - 51*s^8 - 24*s^10 - 10*s^12 - 
         10*s^14 - 3*s^16 + 16*s^20) + 
       (s^2*(5 + 36*s^2 + 74*s^4 + 52*s^6 - 9*s^8 - 26*s^10 - 6*s^12 + 
          10*s^14 + 4*s^16 - s^20 + 14*s^22))/b^2 + 
       b^2*s^2*(5 + 36*s^2 + 74*s^4 + 52*s^6 - 9*s^8 - 26*s^10 - 6*s^12 + 
         10*s^14 + 4*s^16 - s^20 + 14*s^22) + 
       s^2*(11 + 73*s^2 + 137*s^4 + 113*s^6 + 23*s^8 - 14*s^10 + 15*s^12 + 
         33*s^14 + 16*s^16 + 2*s^18 + 17*s^22), (44*s^25)/b^25 + 
       44*b^25*s^25 + (s^23*(-12 + 13*s^2))/b^23 + b^23*s^23*(-12 + 13*s^2) + 
       (3*s^21*(-6 + s^2 + 5*s^4))/b^21 + 3*b^21*s^21*(-6 + s^2 + 5*s^4) + 
       (s^19*(-9 - 6*s^2 + s^4 + 14*s^6))/b^19 + 
       b^19*s^19*(-9 - 6*s^2 + s^4 + 14*s^6) + 
       (2*s^17*(-3 - 3*s^2 + 2*s^4 + 8*s^8))/b^17 + 
       2*b^17*s^17*(-3 - 3*s^2 + 2*s^4 + 8*s^8) + 
       (s^15*(3 - 2*s^2 + 2*s^4 + 5*s^6 + s^8 + 15*s^10))/b^15 + 
       b^15*s^15*(3 - 2*s^2 + 2*s^4 + 5*s^6 + s^8 + 15*s^10) + 
       (s^13*(-4 - 3*s^2 - 14*s^4 + 4*s^6 + 4*s^8 + s^10 + 16*s^12))/b^13 + 
       b^13*s^13*(-4 - 3*s^2 - 14*s^4 + 4*s^6 + 4*s^8 + s^10 + 16*s^12) + 
       (s^11*(-4 - 25*s^2 - 29*s^4 - 21*s^6 - 9*s^8 - s^10 + 15*s^14))/b^11 + 
       b^11*s^11*(-4 - 25*s^2 - 29*s^4 - 21*s^6 - 9*s^8 - s^10 + 15*s^14) + 
       (s^9*(2 - 7*s^2 - 33*s^4 - 34*s^6 - 5*s^8 - 7*s^10 - 3*s^12 - s^14 + 
          16*s^16))/b^9 + b^9*s^9*(2 - 7*s^2 - 33*s^4 - 34*s^6 - 5*s^8 - 
         7*s^10 - 3*s^12 - s^14 + 16*s^16) + 
       (s^7*(12 + 38*s^2 + 33*s^4 - 3*s^6 - 5*s^8 + 16*s^10 + 5*s^12 - 
          2*s^14 - s^16 + 16*s^18))/b^7 + b^7*s^7*(12 + 38*s^2 + 33*s^4 - 
         3*s^6 - 5*s^8 + 16*s^10 + 5*s^12 - 2*s^14 - s^16 + 16*s^18) + 
       (s^5*(-1 + 27*s^2 + 93*s^4 + 96*s^6 + 32*s^8 + 16*s^10 + 25*s^12 + 
          12*s^14 + s^16 + 17*s^20))/b^5 + b^5*s^5*(-1 + 27*s^2 + 93*s^4 + 
         96*s^6 + 32*s^8 + 16*s^10 + 25*s^12 + 12*s^14 + s^16 + 17*s^20) + 
       (s^3*(-6 - 29*s^2 - 31*s^4 + 28*s^6 + 60*s^8 + 14*s^10 - 5*s^12 + 
          s^16 + 16*s^22))/b^3 + b^3*s^3*(-6 - 29*s^2 - 31*s^4 + 28*s^6 + 
         60*s^8 + 14*s^10 - 5*s^12 + s^16 + 16*s^22) + 
       (s*(-1 - 32*s^2 - 109*s^4 - 143*s^6 - 69*s^8 + 15*s^10 - 14*s^12 - 
          34*s^14 - 28*s^16 - 10*s^18 - s^20 + 16*s^24))/b + 
       b*s*(-1 - 32*s^2 - 109*s^4 - 143*s^6 - 69*s^8 + 15*s^10 - 14*s^12 - 
         34*s^14 - 28*s^16 - 10*s^18 - s^20 + 16*s^24), 
      (50*s^26)/b^26 + 50*b^26*s^26 + (s^24*(-13 + 14*s^2))/b^24 + 
       b^24*s^24*(-13 + 14*s^2) + (s^22*(-18 + 5*s^2 + 17*s^4))/b^22 + 
       b^22*s^22*(-18 + 5*s^2 + 17*s^4) + (s^20*(-9 - s^2 + 4*s^4 + 15*s^6))/
        b^20 + b^20*s^20*(-9 - s^2 + 4*s^4 + 15*s^6) + 
       (s^18*(-10 - 8*s^2 + 7*s^4 + s^6 + 17*s^8))/b^18 + 
       b^18*s^18*(-10 - 8*s^2 + 7*s^4 + s^6 + 17*s^8) + 
       (s^16*(-1 - 16*s^2 - 11*s^4 - 2*s^6 - s^8 + 15*s^10))/b^16 + 
       b^16*s^16*(-1 - 16*s^2 - 11*s^4 - 2*s^6 - s^8 + 15*s^10) + 
       (s^14*(-3 - 3*s^2 - 17*s^4 - 2*s^6 - 3*s^8 - s^10 + 18*s^12))/b^14 + 
       b^14*s^14*(-3 - 3*s^2 - 17*s^4 - 2*s^6 - 3*s^8 - s^10 + 18*s^12) + 
       (s^12*(12 + 15*s^2 + 4*s^4 + 4*s^6 - 3*s^10 - s^12 + 16*s^14))/b^12 + 
       b^12*s^12*(12 + 15*s^2 + 4*s^4 + 4*s^6 - 3*s^10 - s^12 + 16*s^14) + 
       (s^10*(3 + 32*s^2 + 44*s^4 + 18*s^6 + 24*s^8 + 8*s^10 + 2*s^12 + 
          s^14 + 19*s^16))/b^10 + b^10*s^10*(3 + 32*s^2 + 44*s^4 + 18*s^6 + 
         24*s^8 + 8*s^10 + 2*s^12 + s^14 + 19*s^16) + 
       (s^8*(-8 - 13*s^2 + 14*s^4 + 15*s^6 - 9*s^8 - 4*s^10 + 3*s^12 + 
          2*s^14 + 16*s^18))/b^8 + b^8*s^8*(-8 - 13*s^2 + 14*s^4 + 15*s^6 - 
         9*s^8 - 4*s^10 + 3*s^12 + 2*s^14 + 16*s^18) + 
       (s^6*(-6 - 58*s^2 - 100*s^4 - 60*s^6 - 37*s^8 - 29*s^10 - 26*s^12 - 
          7*s^14 + 18*s^20))/b^6 + b^6*s^6*(-6 - 58*s^2 - 100*s^4 - 60*s^6 - 
         37*s^8 - 29*s^10 - 26*s^12 - 7*s^14 + 18*s^20) + 
       (s^4*(5 + 10*s^2 - 44*s^4 - 108*s^6 - 81*s^8 - 41*s^10 - 17*s^12 - 
          22*s^14 - 8*s^16 - s^18 - s^20 + 16*s^22))/b^4 + 
       b^4*s^4*(5 + 10*s^2 - 44*s^4 - 108*s^6 - 81*s^8 - 41*s^10 - 17*s^12 - 
         22*s^14 - 8*s^16 - s^18 - s^20 + 16*s^22) + 
       s^2*(12 + 91*s^2 + 191*s^4 + 177*s^6 + 52*s^8 - 5*s^10 + 22*s^12 + 
         59*s^14 + 31*s^16 + 8*s^18 + 17*s^24) + 
       (s^2*(5 + 46*s^2 + 103*s^4 + 84*s^6 - 7*s^8 - 33*s^10 - 11*s^12 + 
          26*s^14 + 12*s^16 + 2*s^18 - 2*s^20 + 19*s^24))/b^2 + 
       b^2*s^2*(5 + 46*s^2 + 103*s^4 + 84*s^6 - 7*s^8 - 33*s^10 - 11*s^12 + 
         26*s^14 + 12*s^16 + 2*s^18 - 2*s^20 + 19*s^24), 
      (53*s^27)/b^27 + 53*b^27*s^27 + (s^25*(-14 + 15*s^2))/b^25 + 
       b^25*s^25*(-14 + 15*s^2) + (s^23*(-20 + 5*s^2 + 17*s^4))/b^23 + 
       b^23*s^23*(-20 + 5*s^2 + 17*s^4) + 
       (s^21*(-13 - 7*s^2 + 2*s^4 + 16*s^6))/b^21 + 
       b^21*s^21*(-13 - 7*s^2 + 2*s^4 + 16*s^6) + 
       (s^19*(-10 - 11*s^2 + 2*s^4 + 18*s^8))/b^19 + 
       b^19*s^19*(-10 - 11*s^2 + 2*s^4 + 18*s^8) + 
       (s^17*(5 - 6*s^2 - 3*s^4 + 17*s^10))/b^17 + 
       b^17*s^17*(5 - 6*s^2 - 3*s^4 + 17*s^10) + 
       (s^15*(-2 + 7*s^2 + 2*s^4 + 15*s^6 + 6*s^8 + s^10 + 19*s^12))/b^15 + 
       b^15*s^15*(-2 + 7*s^2 + 2*s^4 + 15*s^6 + 6*s^8 + s^10 + 19*s^12) + 
       (s^13*(1 - 4*s^2 - 13*s^4 - 4*s^6 + 3*s^8 + 3*s^10 + 17*s^14))/b^13 + 
       b^13*s^13*(1 - 4*s^2 - 13*s^4 - 4*s^6 + 3*s^8 + 3*s^10 + 17*s^14) + 
       (s^11*(-9 - 37*s^2 - 47*s^4 - 42*s^6 - 13*s^8 - 5*s^10 - s^14 + 
          18*s^16))/b^11 + b^11*s^11*(-9 - 37*s^2 - 47*s^4 - 42*s^6 - 
         13*s^8 - 5*s^10 - s^14 + 18*s^16) + 
       (s^9*(4 - 8*s^2 - 44*s^4 - 54*s^6 - 25*s^8 - 13*s^10 - 7*s^12 - 
          3*s^14 - s^16 + 18*s^18))/b^9 + b^9*s^9*(4 - 8*s^2 - 44*s^4 - 
         54*s^6 - 25*s^8 - 13*s^10 - 7*s^12 - 3*s^14 - s^16 + 18*s^18) + 
       (s^7*(15 + 57*s^2 + 58*s^4 + 14*s^6 - 11*s^8 + 27*s^10 + 11*s^12 - 
          2*s^14 - 3*s^16 + 19*s^20))/b^7 + b^7*s^7*(15 + 57*s^2 + 58*s^4 + 
         14*s^6 - 11*s^8 + 27*s^10 + 11*s^12 - 2*s^14 - 3*s^16 + 19*s^20) + 
       (s^5*(-1 + 32*s^2 + 132*s^4 + 158*s^6 + 80*s^8 + 18*s^10 + 48*s^12 + 
          27*s^14 + 5*s^16 + s^20 + 19*s^22))/b^5 + 
       b^5*s^5*(-1 + 32*s^2 + 132*s^4 + 158*s^6 + 80*s^8 + 18*s^10 + 
         48*s^12 + 27*s^14 + 5*s^16 + s^20 + 19*s^22) + 
       (s^3*(-8 - 39*s^2 - 49*s^4 + 30*s^6 + 92*s^8 + 48*s^10 - 17*s^12 + 
          7*s^14 + 4*s^16 + 2*s^18 + 19*s^24))/b^3 + 
       b^3*s^3*(-8 - 39*s^2 - 49*s^4 + 30*s^6 + 92*s^8 + 48*s^10 - 17*s^12 + 
         7*s^14 + 4*s^16 + 2*s^18 + 19*s^24) + 
       (s*(-1 - 38*s^2 - 143*s^4 - 208*s^6 - 123*s^8 + 6*s^10 - 4*s^12 - 
          70*s^14 - 48*s^16 - 25*s^18 - 4*s^20 - s^24 + 18*s^26))/b + 
       b*s*(-1 - 38*s^2 - 143*s^4 - 208*s^6 - 123*s^8 + 6*s^10 - 4*s^12 - 
         70*s^14 - 48*s^16 - 25*s^18 - 4*s^20 - s^24 + 18*s^26), 
      (60*s^28)/b^28 + 60*b^28*s^28 + (s^26*(-15 + 16*s^2))/b^26 + 
       b^26*s^26*(-15 + 16*s^2) + (s^24*(-22 + 6*s^2 + 19*s^4))/b^24 + 
       b^24*s^24*(-22 + 6*s^2 + 19*s^4) + 
       (s^22*(-11 - 3*s^2 + 3*s^4 + 17*s^6))/b^22 + 
       b^22*s^22*(-11 - 3*s^2 + 3*s^4 + 17*s^6) + 
       (s^20*(-11 - 3*s^2 + 11*s^4 + s^6 + 20*s^8))/b^20 + 
       b^20*s^20*(-11 - 3*s^2 + 11*s^4 + s^6 + 20*s^8) + 
       (s^18*(1 - 11*s^2 - 2*s^4 + 2*s^6 - s^8 + 17*s^10))/b^18 + 
       b^18*s^18*(1 - 11*s^2 - 2*s^4 + 2*s^6 - s^8 + 17*s^10) + 
       (s^16*(-9 - 17*s^2 - 24*s^4 - s^6 - s^10 + 20*s^12))/b^16 + 
       b^16*s^16*(-9 - 17*s^2 - 24*s^4 - s^6 - s^10 + 20*s^12) + 
       (s^14*(5 - 4*s^2 - 22*s^4 - 15*s^6 - 12*s^8 - 4*s^10 - s^12 + 
          18*s^14))/b^14 + b^14*s^14*(5 - 4*s^2 - 22*s^4 - 15*s^6 - 12*s^8 - 
         4*s^10 - s^12 + 18*s^14) + (s^12*(12 + 29*s^2 + 14*s^4 + 4*s^6 + 
          12*s^8 - 4*s^10 - 2*s^12 + s^14 + 21*s^16))/b^12 + 
       b^12*s^12*(12 + 29*s^2 + 14*s^4 + 4*s^6 + 12*s^8 - 4*s^10 - 2*s^12 + 
         s^14 + 21*s^16) + (s^10*(4 + 43*s^2 + 83*s^4 + 45*s^6 + 31*s^8 + 
          19*s^10 + 8*s^12 + 2*s^14 + s^16 + 19*s^18))/b^10 + 
       b^10*s^10*(4 + 43*s^2 + 83*s^4 + 45*s^6 + 31*s^8 + 19*s^10 + 8*s^12 + 
         2*s^14 + s^16 + 19*s^18) + (s^8*(-12 - 25*s^2 + 8*s^4 + 39*s^6 - 
          12*s^8 - 2*s^10 + 2*s^12 + 5*s^14 + s^16 + 21*s^20))/b^8 + 
       b^8*s^8*(-12 - 25*s^2 + 8*s^4 + 39*s^6 - 12*s^8 - 2*s^10 + 2*s^12 + 
         5*s^14 + s^16 + 21*s^20) + (s^6*(-6 - 77*s^2 - 154*s^4 - 114*s^6 - 
          46*s^8 - 62*s^10 - 46*s^12 - 20*s^14 - s^16 - 2*s^20 + 18*s^22))/
        b^6 + b^6*s^6*(-6 - 77*s^2 - 154*s^4 - 114*s^6 - 46*s^8 - 62*s^10 - 
         46*s^12 - 20*s^14 - s^16 - 2*s^20 + 18*s^22) + 
       (s^4*(6 + 16*s^2 - 53*s^4 - 162*s^6 - 146*s^8 - 59*s^10 - 45*s^12 - 
          34*s^14 - 17*s^16 - 3*s^18 - 2*s^20 - s^22 + 21*s^24))/b^4 + 
       b^4*s^4*(6 + 16*s^2 - 53*s^4 - 162*s^6 - 146*s^8 - 59*s^10 - 45*s^12 - 
         34*s^14 - 17*s^16 - 3*s^18 - 2*s^20 - s^22 + 21*s^24) + 
       (s^2*(6 + 57*s^2 + 143*s^4 + 134*s^6 + 8*s^8 - 54*s^10 - 5*s^12 + 
          27*s^14 + 26*s^16 + 4*s^18 - 3*s^20 - s^22 + 19*s^26))/b^2 + 
       b^2*s^2*(6 + 57*s^2 + 143*s^4 + 134*s^6 + 8*s^8 - 54*s^10 - 5*s^12 + 
         27*s^14 + 26*s^16 + 4*s^18 - 3*s^20 - s^22 + 19*s^26) + 
       s^2*(13 + 113*s^2 + 260*s^4 + 272*s^6 + 104*s^8 - 2*s^10 + 48*s^12 + 
         85*s^14 + 66*s^16 + 23*s^18 + 2*s^20 + 2*s^24 + 22*s^26), 
      (63*s^29)/b^29 + 63*b^29*s^29 + (s^27*(-16 + 17*s^2))/b^27 + 
       b^27*s^27*(-16 + 17*s^2) + (s^25*(-23 + 7*s^2 + 20*s^4))/b^25 + 
       b^25*s^25*(-23 + 7*s^2 + 20*s^4) + 
       (s^23*(-14 - 4*s^2 + 3*s^4 + 18*s^6))/b^23 + 
       b^23*s^23*(-14 - 4*s^2 + 3*s^4 + 18*s^6) + 
       (s^21*(-16 - 15*s^2 + 5*s^4 + 20*s^8))/b^21 + 
       b^21*s^21*(-16 - 15*s^2 + 5*s^4 + 20*s^8) + 
       (s^19*(2 - 15*s^2 - 11*s^4 - 2*s^6 + 19*s^10))/b^19 + 
       b^19*s^19*(2 - 15*s^2 - 11*s^4 - 2*s^6 + 19*s^10) + 
       (s^19*(3 - 6*s^2 + 6*s^4 + 2*s^6 + s^8 + 21*s^10))/b^17 + 
       b^17*s^19*(3 - 6*s^2 + 6*s^4 + 2*s^6 + s^8 + 21*s^10) + 
       (s^15*(8 + 15*s^2 + 11*s^4 + 19*s^6 + 9*s^8 + 3*s^10 + s^12 + 
          20*s^14))/b^15 + b^15*s^15*(8 + 15*s^2 + 11*s^4 + 19*s^6 + 9*s^8 + 
         3*s^10 + s^12 + 20*s^14) + (s^13*(-5 - 4*s^2 - 13*s^4 - 12*s^6 + 
          12*s^8 + 7*s^10 + s^12 - s^14 + 21*s^16))/b^13 + 
       b^13*s^13*(-5 - 4*s^2 - 13*s^4 - 12*s^6 + 12*s^8 + 7*s^10 + s^12 - 
         s^14 + 21*s^16) + (s^11*(-11 - 58*s^2 - 69*s^4 - 69*s^6 - 35*s^8 - 
          14*s^10 - 2*s^14 - 2*s^16 + 20*s^18))/b^11 + 
       b^11*s^11*(-11 - 58*s^2 - 69*s^4 - 69*s^6 - 35*s^8 - 14*s^10 - 
         2*s^14 - 2*s^16 + 20*s^18) + (s^9*(6 - 8*s^2 - 69*s^4 - 79*s^6 - 
          57*s^8 - 17*s^10 - 18*s^12 - 7*s^14 - 3*s^16 - s^18 + 21*s^20))/
        b^9 + b^9*s^9*(6 - 8*s^2 - 69*s^4 - 79*s^6 - 57*s^8 - 17*s^10 - 
         18*s^12 - 7*s^14 - 3*s^16 - s^18 + 21*s^20) + 
       (s^7*(19 + 82*s^2 + 100*s^4 + 33*s^6 - s^8 + 22*s^10 + 28*s^12 - 
          s^14 - 6*s^16 - s^18 + s^20 + 21*s^22))/b^7 + 
       b^7*s^7*(19 + 82*s^2 + 100*s^4 + 33*s^6 - s^8 + 22*s^10 + 28*s^12 - 
         s^14 - 6*s^16 - s^18 + s^20 + 21*s^22) + 
       (s^5*(-3 + 37*s^2 + 182*s^4 + 249*s^6 + 146*s^8 + 52*s^10 + 66*s^12 + 
          55*s^14 + 18*s^16 + 2*s^18 + 2*s^20 + 2*s^22 + 22*s^24))/b^5 + 
       b^5*s^5*(-3 + 37*s^2 + 182*s^4 + 249*s^6 + 146*s^8 + 52*s^10 + 
         66*s^12 + 55*s^14 + 18*s^16 + 2*s^18 + 2*s^20 + 2*s^22 + 22*s^24) + 
       (s^3*(-9 - 52*s^2 - 75*s^4 + 31*s^6 + 142*s^8 + 91*s^10 - 9*s^12 - 
          2*s^14 + 7*s^16 + 5*s^18 + s^20 + 21*s^26))/b^3 + 
       b^3*s^3*(-9 - 52*s^2 - 75*s^4 + 31*s^6 + 142*s^8 + 91*s^10 - 9*s^12 - 
         2*s^14 + 7*s^16 + 5*s^18 + s^20 + 21*s^26) + 
       (s*(-1 - 44*s^2 - 186*s^4 - 297*s^6 - 204*s^8 - 10*s^10 - s^12 - 
          99*s^14 - 93*s^16 - 52*s^18 - 13*s^20 - 2*s^24 - 2*s^26 + 21*s^28))/
        b + b*s*(-1 - 44*s^2 - 186*s^4 - 297*s^6 - 204*s^8 - 10*s^10 - s^12 - 
         99*s^14 - 93*s^16 - 52*s^18 - 13*s^20 - 2*s^24 - 2*s^26 + 21*s^28), 
      (71*s^30)/b^30 + 71*b^30*s^30 + (s^28*(-17 + 18*s^2))/b^28 + 
       b^28*s^28*(-17 + 18*s^2) + (s^26*(-26 + 7*s^2 + 21*s^4))/b^26 + 
       b^26*s^26*(-26 + 7*s^2 + 21*s^4) + 
       (s^24*(-15 - 4*s^2 + 3*s^4 + 19*s^6))/b^24 + 
       b^24*s^24*(-15 - 4*s^2 + 3*s^4 + 19*s^6) + 
       (s^22*(-13 - 7*s^2 + 9*s^4 + s^6 + 22*s^8))/b^22 + 
       b^22*s^22*(-13 - 7*s^2 + 9*s^4 + s^6 + 22*s^8) + 
       (s^20*(3 - 3*s^2 + 5*s^4 + 3*s^6 + 20*s^10))/b^20 + 
       b^20*s^20*(3 - 3*s^2 + 5*s^4 + 3*s^6 + 20*s^10) + 
       (s^18*(-8 - 8*s^2 - 7*s^4 + 11*s^6 + 2*s^8 - s^10 + 23*s^12))/b^18 + 
       b^18*s^18*(-8 - 8*s^2 - 7*s^4 + 11*s^6 + 2*s^8 - s^10 + 23*s^12) + 
       (s^16*(-1 - 25*s^2 - 40*s^4 - 18*s^6 - 7*s^8 - 3*s^10 - 2*s^12 + 
          20*s^14))/b^16 + b^16*s^16*(-1 - 25*s^2 - 40*s^4 - 18*s^6 - 7*s^8 - 
         3*s^10 - 2*s^12 + 20*s^14) + (s^14*(1 - 2*s^2 - 31*s^4 - 32*s^6 - 
          15*s^8 - 10*s^10 - 2*s^12 + 23*s^16))/b^14 + 
       b^14*s^14*(1 - 2*s^2 - 31*s^4 - 32*s^6 - 15*s^8 - 10*s^10 - 2*s^12 + 
         23*s^16) + (s^12*(19 + 46*s^2 + 43*s^4 + 9*s^6 + 14*s^8 - 5*s^10 - 
          3*s^12 + s^14 + s^16 + 21*s^18))/b^12 + 
       b^12*s^12*(19 + 46*s^2 + 43*s^4 + 9*s^6 + 14*s^8 - 5*s^10 - 3*s^12 + 
         s^14 + s^16 + 21*s^18) + (s^10*(4 + 57*s^2 + 128*s^4 + 102*s^6 + 
          46*s^8 + 46*s^10 + 17*s^12 + 5*s^14 + 3*s^16 + 2*s^18 + 24*s^20))/
        b^10 + b^10*s^10*(4 + 57*s^2 + 128*s^4 + 102*s^6 + 46*s^8 + 46*s^10 + 
         17*s^12 + 5*s^14 + 3*s^16 + 2*s^18 + 24*s^20) + 
       (s^8*(-16 - 42*s^2 + s^4 + 62*s^6 + 15*s^8 - 19*s^10 + 3*s^12 + 
          10*s^14 + 4*s^16 - s^20 + 21*s^22))/b^8 + 
       b^8*s^8*(-16 - 42*s^2 + s^4 + 62*s^6 + 15*s^8 - 19*s^10 + 3*s^12 + 
         10*s^14 + 4*s^16 - s^20 + 21*s^22) + 
       (s^6*(-8 - 100*s^2 - 230*s^4 - 198*s^6 - 83*s^8 - 79*s^10 - 78*s^12 - 
          44*s^14 - 4*s^16 + s^18 - 4*s^20 - 2*s^22 + 24*s^24))/b^6 + 
       b^6*s^6*(-8 - 100*s^2 - 230*s^4 - 198*s^6 - 83*s^8 - 79*s^10 - 
         78*s^12 - 44*s^14 - 4*s^16 + s^18 - 4*s^20 - 2*s^22 + 24*s^24) + 
       (s^4*(8 + 23*s^2 - 63*s^4 - 234*s^6 - 238*s^8 - 105*s^10 - 72*s^12 - 
          57*s^14 - 42*s^16 - 12*s^18 - 4*s^20 - 3*s^22 - 2*s^24 + 21*s^26))/
        b^4 + b^4*s^4*(8 + 23*s^2 - 63*s^4 - 234*s^6 - 238*s^8 - 105*s^10 - 
         72*s^12 - 57*s^14 - 42*s^16 - 12*s^18 - 4*s^20 - 3*s^22 - 2*s^24 + 
         21*s^26) + s^2*(14 + 137*s^2 + 347*s^4 + 398*s^6 + 185*s^8 + 
         18*s^10 + 81*s^12 + 139*s^14 + 133*s^16 + 55*s^18 + 8*s^20 + 
         4*s^24 + 2*s^26 + 22*s^28) + (s^2*(6 + 71*s^2 + 191*s^4 + 203*s^6 + 
          30*s^8 - 77*s^10 - 8*s^12 + 46*s^14 + 56*s^16 + 12*s^18 - 2*s^20 - 
          2*s^22 + s^26 + 24*s^28))/b^2 + b^2*s^2*(6 + 71*s^2 + 191*s^4 + 
         203*s^6 + 30*s^8 - 77*s^10 - 8*s^12 + 46*s^14 + 56*s^16 + 12*s^18 - 
         2*s^20 - 2*s^22 + s^26 + 24*s^28)}, 0, 31, 1]