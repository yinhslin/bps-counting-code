f = SeriesData[x, 0, {1, 0, 1 + b^(-2) + b^2, b^(-3) - b^(-1) - b + b^3, 
      2 + b^(-4) + b^4, b^(-5) + b^(-3) - 2/b - 2*b + b^3 + b^5, 
      5 + 2/b^6 - b^(-4) - b^4 + 2*b^6, b^(-7) + 3/b^3 - 4/b - 4*b + 3*b^3 + 
       b^7, 8 + 2/b^8 + b^(-6) - 3/b^4 - b^(-2) - b^2 - 3*b^4 + b^6 + 2*b^8, 
      2/b^9 - b^(-7) + 6/b^3 - 7/b - 7*b + 6*b^3 - b^7 + 2*b^9, 
      16 + 2/b^10 + 3/b^6 - 6/b^4 - b^(-2) - b^2 - 6*b^4 + 3*b^6 + 2*b^10, 
      2/b^11 + b^(-9) - 3/b^7 + 13/b^3 - 13/b - 13*b + 13*b^3 - 3*b^7 + b^9 + 
       2*b^11, 28 + 3/b^12 - b^(-10) + 7/b^6 - 13/b^4 - 6/b^2 - 6*b^2 - 
       13*b^4 + 7*b^6 - b^10 + 3*b^12, 2/b^13 + 3/b^9 - 7/b^7 - b^(-5) + 
       25/b^3 - 22/b - 22*b + 25*b^3 - b^5 - 7*b^7 + 3*b^9 + 2*b^13, 
      51 + 3/b^14 + b^(-12) - 3/b^10 + 15/b^6 - 23/b^4 - 11/b^2 - 11*b^2 - 
       23*b^4 + 15*b^6 - 3*b^10 + b^12 + 3*b^14, 3/b^15 - b^(-13) + 7/b^9 - 
       15/b^7 - 2/b^5 + 47/b^3 - 39/b - 39*b + 47*b^3 - 2*b^5 - 15*b^7 + 
       7*b^9 - b^13 + 3*b^15, 89 + 3/b^16 + 3/b^12 - 7/b^10 + 30/b^6 - 
       44/b^4 - 23/b^2 - 23*b^2 - 44*b^4 + 30*b^6 - 7*b^10 + 3*b^12 + 3*b^16, 
      3/b^17 + b^(-15) - 3/b^13 + 16/b^9 - 30/b^7 - 6/b^5 + 85/b^3 - 66/b - 
       66*b + 85*b^3 - 6*b^5 - 30*b^7 + 16*b^9 - 3*b^13 + b^15 + 3*b^17, 
      150 + 4/b^18 - b^(-16) + 7/b^12 - 16/b^10 - b^(-8) + 59/b^6 - 77/b^4 - 
       41/b^2 - 41*b^2 - 77*b^4 + 59*b^6 - b^8 - 16*b^10 + 7*b^12 - b^16 + 
       4*b^18, 3/b^19 + 3/b^15 - 7/b^13 + 32/b^9 - 57/b^7 - 13/b^5 + 
       149/b^3 - 110/b - 110*b + 149*b^3 - 13*b^5 - 57*b^7 + 32*b^9 - 
       7*b^13 + 3*b^15 + 3*b^19, 248 + 4/b^20 + b^(-18) - 3/b^16 + 16/b^12 - 
       32/b^10 - 2/b^8 + 106/b^6 - 133/b^4 - 75/b^2 - 75*b^2 - 133*b^4 + 
       106*b^6 - 2*b^8 - 32*b^10 + 16*b^12 - 3*b^16 + b^18 + 4*b^20, 
      4/b^21 - b^(-19) + 7/b^15 - 16/b^13 + 63/b^9 - 103/b^7 - 27/b^5 + 
       254/b^3 - 181/b - 181*b + 254*b^3 - 27*b^5 - 103*b^7 + 63*b^9 - 
       16*b^13 + 7*b^15 - b^19 + 4*b^21, 412 + 4/b^22 + 3/b^18 - 7/b^16 + 
       33/b^12 - 63/b^10 - 5/b^8 + 189/b^6 - 221/b^4 - 125/b^2 - 125*b^2 - 
       221*b^4 + 189*b^6 - 5*b^8 - 63*b^10 + 33*b^12 - 7*b^16 + 3*b^18 + 
       4*b^22, 4/b^23 + b^(-21) - 3/b^19 + 16/b^15 - 33/b^13 - b^(-11) + 
       117/b^9 - 181/b^7 - 51/b^5 + 426/b^3 - 295/b - 295*b + 426*b^3 - 
       51*b^5 - 181*b^7 + 117*b^9 - b^11 - 33*b^13 + 16*b^15 - 3*b^19 + 
       b^21 + 4*b^23, 664 + 5/b^24 - b^(-22) + 7/b^18 - 16/b^16 + 65/b^12 - 
       116/b^10 - 13/b^8 + 328/b^6 - 366/b^4 - 218/b^2 - 218*b^2 - 366*b^4 + 
       328*b^6 - 13*b^8 - 116*b^10 + 65*b^12 - 16*b^16 + 7*b^18 - b^22 + 
       5*b^24, 4/b^25 + 3/b^21 - 7/b^19 + 33/b^15 - 65/b^13 - 2/b^11 + 
       212/b^9 - 310/b^7 - 97/b^5 + 700/b^3 - 471/b - 471*b + 700*b^3 - 
       97*b^5 - 310*b^7 + 212*b^9 - 2*b^11 - 65*b^13 + 33*b^15 - 7*b^19 + 
       3*b^21 + 4*b^25, 1066 + 5/b^26 + b^(-24) - 3/b^22 + 16/b^18 - 
       33/b^16 + 122/b^12 - 208/b^10 - 29/b^8 + 554/b^6 - 590/b^4 - 356/b^2 - 
       356*b^2 - 590*b^4 + 554*b^6 - 29*b^8 - 208*b^10 + 122*b^12 - 33*b^16 + 
       16*b^18 - 3*b^22 + b^24 + 5*b^26, 5/b^27 - b^(-25) + 7/b^21 - 
       16/b^19 + 66/b^15 - 122/b^13 - 6/b^11 + 370/b^9 - 517/b^7 - 170/b^5 + 
       1129/b^3 - 745/b - 745*b + 1129*b^3 - 170*b^5 - 517*b^7 + 370*b^9 - 
       6*b^11 - 122*b^13 + 66*b^15 - 16*b^19 + 7*b^21 - b^25 + 5*b^27, 
      1680 + 5/b^28 + 3/b^24 - 7/b^22 + 33/b^18 - 66/b^16 - b^(-14) + 
       223/b^12 - 362/b^10 - 55/b^8 + 919/b^6 - 938/b^4 - 582/b^2 - 582*b^2 - 
       938*b^4 + 919*b^6 - 55*b^8 - 362*b^10 + 223*b^12 - b^14 - 66*b^16 + 
       33*b^18 - 7*b^22 + 3*b^24 + 5*b^28, 5/b^29 + b^(-27) - 3/b^25 + 
       16/b^21 - 33/b^19 + 124/b^15 - 222/b^13 - 13/b^11 + 634/b^9 - 
       847/b^7 - 296/b^5 + 1798/b^3 - 1164/b - 1164*b + 1798*b^3 - 296*b^5 - 
       847*b^7 + 634*b^9 - 13*b^11 - 222*b^13 + 124*b^15 - 33*b^19 + 
       16*b^21 - 3*b^25 + b^27 + 5*b^29, 2631 + 6/b^30 - b^(-28) + 7/b^24 - 
       16/b^22 + 66/b^18 - 124/b^16 - 2/b^14 + 394/b^12 - 616/b^10 - 
       107/b^8 + 1496/b^6 - 1477/b^4 - 926/b^2 - 926*b^2 - 1477*b^4 + 
       1496*b^6 - 107*b^8 - 616*b^10 + 394*b^12 - 2*b^14 - 124*b^16 + 
       66*b^18 - 16*b^22 + 7*b^24 - b^28 + 6*b^30, 5/b^31 + 3/b^27 - 7/b^25 + 
       33/b^21 - 66/b^19 + 228/b^15 - 390/b^13 - 29/b^11 + 1059/b^9 - 
       1363/b^7 - 496/b^5 + 2825/b^3 - 1802/b - 1802*b + 2825*b^3 - 496*b^5 - 
       1363*b^7 + 1059*b^9 - 29*b^11 - 390*b^13 + 228*b^15 - 66*b^19 + 
       33*b^21 - 7*b^25 + 3*b^27 + 5*b^31, 4054 + 6/b^32 + b^(-30) - 3/b^28 + 
       16/b^24 - 33/b^22 + 125/b^18 - 228/b^16 - 6/b^14 + 678/b^12 - 
       1020/b^10 - 192/b^8 + 2397/b^6 - 2295/b^4 - 1464/b^2 - 1464*b^2 - 
       2295*b^4 + 2397*b^6 - 192*b^8 - 1020*b^10 + 678*b^12 - 6*b^14 - 
       228*b^16 + 125*b^18 - 33*b^22 + 16*b^24 - 3*b^28 + b^30 + 6*b^32, 
      6/b^33 - b^(-31) + 7/b^27 - 16/b^25 + 66/b^21 - 125/b^19 - b^(-17) + 
       404/b^15 - 670/b^13 - 57/b^11 + 1740/b^9 - 2160/b^7 - 822/b^5 + 
       4385/b^3 - 2756/b - 2756*b + 4385*b^3 - 822*b^5 - 2160*b^7 + 
       1740*b^9 - 57*b^11 - 670*b^13 + 404*b^15 - b^17 - 125*b^19 + 66*b^21 - 
       16*b^25 + 7*b^27 - b^31 + 6*b^33, 6209 + 6/b^34 + 3/b^30 - 7/b^28 + 
       33/b^24 - 66/b^22 + 230/b^18 - 403/b^16 - 12/b^14 + 1141/b^12 - 
       1664/b^10 - 342/b^8 + 3787/b^6 - 3520/b^4 - 2271/b^2 - 2271*b^2 - 
       3520*b^4 + 3787*b^6 - 342*b^8 - 1664*b^10 + 1141*b^12 - 12*b^14 - 
       403*b^16 + 230*b^18 - 66*b^22 + 33*b^24 - 7*b^28 + 3*b^30 + 6*b^34, 
      6/b^35 + b^(-33) - 3/b^31 + 16/b^27 - 33/b^25 + 125/b^21 - 230/b^19 - 
       2/b^17 + 701/b^15 - 1123/b^13 - 111/b^11 + 2806/b^9 - 3375/b^7 - 
       1328/b^5 + 6734/b^3 - 4184/b - 4184*b + 6734*b^3 - 1328*b^5 - 
       3375*b^7 + 2806*b^9 - 111*b^11 - 1123*b^13 + 701*b^15 - 2*b^17 - 
       230*b^19 + 125*b^21 - 33*b^25 + 16*b^27 - 3*b^31 + b^33 + 6*b^35}, 0, 
     36, 1]