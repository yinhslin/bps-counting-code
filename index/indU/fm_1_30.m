f = SeriesData[x, 0, {1, s/b + b*s, -1 + s^2/b^2 + b^2*s^2, 
      s^3/b^3 + b^3*s^3, -1 + s^2 + s^4/b^4 + b^4*s^4, 
      -(s/b) - b*s + s^5/b^5 + b^5*s^5, s^2 + s^6/b^6 + b^6*s^6, 
      s^7/b^7 + b^7*s^7 + (-s + s^3)/b + b*(-s + s^3), 
      -(s^2/b^2) - b^2*s^2 + s^8/b^8 + b^8*s^8, s^9/b^9 + b^9*s^9 + 
       (-s + s^3)/b + b*(-s + s^3), 1 - s^2 + s^10/b^10 + b^10*s^10 + 
       (-s^2 + s^4)/b^2 + b^2*(-s^2 + s^4), -(s^3/b^3) + s^3/b + b*s^3 - 
       b^3*s^3 + s^11/b^11 + b^11*s^11, -2*s^2 + s^4 + s^12/b^12 + 
       b^12*s^12 + (-s^2 + s^4)/b^2 + b^2*(-s^2 + s^4), 
      s^13/b^13 + b^13*s^13 + (-s^3 + s^5)/b^3 + b^3*(-s^3 + s^5), 
      -(s^4/b^4) - b^4*s^4 + s^14/b^14 + b^14*s^14 + (s^2*(-1 + s^2))/b^2 + 
       b^2*s^2*(-1 + s^2) + (-1 + s^2)^2, s^15/b^15 + b^15*s^15 + 
       (s - s^3)/b + b*(s - s^3) + (-s^3 + s^5)/b^3 + b^3*(-s^3 + s^5), 
      s^4/b^2 + b^2*s^4 + s^16/b^16 + b^16*s^16 + 2*s^2*(-1 + s^2) + 
       (s^4*(-1 + s^2))/b^4 + b^4*s^4*(-1 + s^2), -(s^5/b^5) - b^5*s^5 + 
       s^17/b^17 + b^17*s^17 + (s^3*(-1 + s^2))/b^3 + b^3*s^3*(-1 + s^2) + 
       (s*(-1 + s^2)^2)/b + b*s*(-1 + s^2)^2, -s^2 + s^4 + s^18/b^18 + 
       b^18*s^18 + (-s^4 + s^6)/b^4 + b^4*(-s^4 + s^6), 
      s^19/b^19 + b^19*s^19 + (s - 3*s^3 + s^5)/b + b*(s - 3*s^3 + s^5) + 
       (-s^3 + s^5)/b^3 + b^3*(-s^3 + s^5) + (-s^5 + s^7)/b^5 + 
       b^5*(-s^5 + s^7), s^4 - s^6/b^6 - b^6*s^6 + s^20/b^20 + b^20*s^20 + 
       (s^2 - s^4)/b^2 + b^2*(s^2 - s^4) + (-s^4 + s^6)/b^4 + 
       b^4*(-s^4 + s^6), s^5/b^3 + b^3*s^5 + s^21/b^21 + b^21*s^21 + 
       (s - 3*s^3 + 2*s^5)/b + b*(s - 3*s^3 + 2*s^5) + (-s^5 + s^7)/b^5 + 
       b^5*(-s^5 + s^7), s^2 - s^4 + s^22/b^22 + b^22*s^22 + 
       (s^4*(-1 + s^2))/b^4 + b^4*s^4*(-1 + s^2) + (s^6*(-1 + s^2))/b^6 + 
       b^6*s^6*(-1 + s^2) + (s^2*(-1 + s^2)^2)/b^2 + b^2*s^2*(-1 + s^2)^2, 
      -(s^7/b^7) - b^7*s^7 + s^23/b^23 + b^23*s^23 + (s - 3*s^3 + 2*s^5)/b + 
       b*(s - 3*s^3 + 2*s^5) + (-s^5 + s^7)/b^5 + b^5*(-s^5 + s^7), 
      -1 + 2*s^2 - 2*s^4 + s^6 + s^24/b^24 + b^24*s^24 + 
       (2*s^2 - 3*s^4 + s^6)/b^2 + b^2*(2*s^2 - 3*s^4 + s^6) + 
       (-s^4 + s^6)/b^4 + b^4*(-s^4 + s^6) + (-s^6 + s^8)/b^6 + 
       b^6*(-s^6 + s^8), s^25/b^25 + b^25*s^25 + (2*s^3*(-1 + s^2))/b + 
       2*b*s^3*(-1 + s^2) + (s^5*(-1 + s^2))/b^5 + b^5*s^5*(-1 + s^2) + 
       (s^7*(-1 + s^2))/b^7 + b^7*s^7*(-1 + s^2) + (s^3 - s^5)/b^3 + 
       b^3*(s^3 - s^5), 3*s^2 - 4*s^4 + s^6 + s^6/b^4 + b^4*s^6 - s^8/b^8 - 
       b^8*s^8 + s^26/b^26 + b^26*s^26 + (s^2 - 4*s^4 + 2*s^6)/b^2 + 
       b^2*(s^2 - 4*s^4 + 2*s^6) + (-s^6 + s^8)/b^6 + b^6*(-s^6 + s^8), 
      s^27/b^27 + b^27*s^27 + (s^3*(-1 + s^2))/b + b*s^3*(-1 + s^2) + 
       (s^5*(-1 + s^2))/b^5 + b^5*s^5*(-1 + s^2) + (s^7*(-1 + s^2))/b^7 + 
       b^7*s^7*(-1 + s^2) + (s^3*(-1 + s^2)^2)/b^3 + b^3*s^3*(-1 + s^2)^2, 
      s^28/b^28 + b^28*s^28 + (s^6*(-1 + s^2))/b^6 + b^6*s^6*(-1 + s^2) + 
       (s^8*(-1 + s^2))/b^8 + b^8*s^8*(-1 + s^2) + (2*s^2*(-1 + s^2)^2)/b^2 + 
       2*b^2*s^2*(-1 + s^2)^2 + s^2*(3 - 5*s^2 + 2*s^4), 
      s^3/b + b*s^3 - s^9/b^9 - b^9*s^9 + s^29/b^29 + b^29*s^29 + 
       (2*s^3 - 3*s^5 + s^7)/b^3 + b^3*(2*s^3 - 3*s^5 + s^7) + 
       (-s^5 + s^7)/b^5 + b^5*(-s^5 + s^7) + (-s^7 + s^9)/b^7 + 
       b^7*(-s^7 + s^9), -1 + 3*s^2 - 6*s^4 + 3*s^6 + s^30/b^30 + b^30*s^30 + 
       (s^6*(-1 + s^2))/b^6 + b^6*s^6*(-1 + s^2) + (s^8*(-1 + s^2))/b^8 + 
       b^8*s^8*(-1 + s^2) + (s^4 - s^6)/b^4 + b^4*(s^4 - s^6) + 
       (s^2 - 4*s^4 + 3*s^6)/b^2 + b^2*(s^2 - 4*s^4 + 3*s^6)}, 0, 31, 1]
