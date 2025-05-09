f = SeriesData[x, 0, {1, 0, 1 + b^(-2) + b^2, b^(-3) - b^(-1) - b + b^3, 
      3 + 2/b^4 + b^(-2) + b^2 + 2*b^4, 2/b^5 - 2/b - 2*b + 2*b^5, 
      6 + 4/b^6 + b^(-4) + 3/b^2 + 3*b^2 + b^4 + 4*b^6, 
      3/b^7 - b^(-5) - b^(-3) - 5/b - 5*b - b^3 - b^5 + 3*b^7, 
      13 + 6/b^8 + 3/b^6 + 4/b^4 + 6/b^2 + 6*b^2 + 4*b^4 + 3*b^6 + 6*b^8, 
      6/b^9 - 2/b^7 - 3/b^5 - 2/b^3 - 11/b - 11*b - 2*b^3 - 3*b^5 - 2*b^7 + 
       6*b^9, 24 + 9/b^10 + 3/b^8 + 9/b^6 + 7/b^4 + 14/b^2 + 14*b^2 + 7*b^4 + 
       9*b^6 + 3*b^8 + 9*b^10, 9/b^11 - b^(-9) - 6/b^7 - 8/b^5 - 7/b^3 - 
       23/b - 23*b - 7*b^3 - 8*b^5 - 6*b^7 - b^9 + 9*b^11, 
      47 + 14/b^12 + 3/b^10 + 9/b^8 + 19/b^6 + 17/b^4 + 25/b^2 + 25*b^2 + 
       17*b^4 + 19*b^6 + 9*b^8 + 3*b^10 + 14*b^12, 13/b^13 - 2/b^11 - 3/b^9 - 
       15/b^7 - 19/b^5 - 17/b^3 - 45/b - 45*b - 17*b^3 - 19*b^5 - 15*b^7 - 
       3*b^9 - 2*b^11 + 13*b^13, 81 + 19/b^14 + 6/b^12 + 10/b^10 + 18/b^8 + 
       40/b^6 + 31/b^4 + 50/b^2 + 50*b^2 + 31*b^4 + 40*b^6 + 18*b^8 + 
       10*b^10 + 6*b^12 + 19*b^14, 20/b^15 - 4/b^13 - 7/b^11 - 9/b^9 - 
       35/b^7 - 45/b^5 - 37/b^3 - 87/b - 87*b - 37*b^3 - 45*b^5 - 35*b^7 - 
       9*b^9 - 7*b^11 - 4*b^13 + 20*b^15, 151 + 26/b^16 + 6/b^14 + 18/b^12 + 
       20/b^10 + 42/b^8 + 77/b^6 + 67/b^4 + 91/b^2 + 91*b^2 + 67*b^4 + 
       77*b^6 + 42*b^8 + 20*b^10 + 18*b^12 + 6*b^14 + 26*b^16, 
      27/b^17 - 2/b^15 - 11/b^13 - 19/b^11 - 25/b^9 - 75/b^7 - 90/b^5 - 
       78/b^3 - 159/b - 159*b - 78*b^3 - 90*b^5 - 75*b^7 - 25*b^9 - 19*b^11 - 
       11*b^13 - 2*b^15 + 27*b^17, 260 + 36/b^18 + 6/b^16 + 18/b^14 + 
       38/b^12 + 45/b^10 + 78/b^8 + 152/b^6 + 120/b^4 + 169/b^2 + 169*b^2 + 
       120*b^4 + 152*b^6 + 78*b^8 + 45*b^10 + 38*b^12 + 18*b^14 + 6*b^16 + 
       36*b^18, 36/b^19 - 4/b^17 - 7/b^15 - 30/b^13 - 46/b^11 - 60/b^9 - 
       149/b^7 - 181/b^5 - 154/b^3 - 289/b - 289*b - 154*b^3 - 181*b^5 - 
       149*b^7 - 60*b^9 - 46*b^11 - 30*b^13 - 7*b^15 - 4*b^17 + 36*b^19, 
      457 + 47/b^20 + 10/b^18 + 19/b^16 + 38/b^14 + 84/b^12 + 87/b^10 + 
       157/b^8 + 274/b^6 + 234/b^4 + 299/b^2 + 299*b^2 + 234*b^4 + 274*b^6 + 
       157*b^8 + 87*b^10 + 84*b^12 + 38*b^14 + 19*b^16 + 10*b^18 + 47*b^20, 
      49/b^21 - 6/b^19 - 12/b^17 - 21/b^15 - 71/b^13 - 107/b^11 - 123/b^9 - 
       290/b^7 - 338/b^5 - 287/b^3 - 510/b - 510*b - 287*b^3 - 338*b^5 - 
       290*b^7 - 123*b^9 - 107*b^11 - 71*b^13 - 21*b^15 - 12*b^17 - 6*b^19 + 
       49*b^21, 773 + 60/b^22 + 10/b^20 + 30/b^18 + 39/b^16 + 85/b^14 + 
       162/b^12 + 177/b^10 + 287/b^8 + 502/b^6 + 415/b^4 + 531/b^2 + 
       531*b^2 + 415*b^4 + 502*b^6 + 287*b^8 + 177*b^10 + 162*b^12 + 
       85*b^14 + 39*b^16 + 30*b^18 + 10*b^20 + 60*b^22, 
      63/b^23 - 4/b^21 - 18/b^19 - 35/b^17 - 55/b^15 - 158/b^13 - 216/b^11 - 
       253/b^9 - 532/b^7 - 618/b^5 - 531/b^3 - 883/b - 883*b - 531*b^3 - 
       618*b^5 - 532*b^7 - 253*b^9 - 216*b^11 - 158*b^13 - 55*b^15 - 
       35*b^17 - 18*b^19 - 4*b^21 + 63*b^23, 1323 + 78/b^24 + 10/b^22 + 
       30/b^20 + 65/b^18 + 89/b^16 + 164/b^14 + 324/b^12 + 326/b^10 + 
       534/b^8 + 883/b^6 + 749/b^4 + 913/b^2 + 913*b^2 + 749*b^4 + 883*b^6 + 
       534*b^8 + 326*b^10 + 324*b^12 + 164*b^14 + 89*b^16 + 65*b^18 + 
       30*b^20 + 10*b^22 + 78*b^24, 80/b^25 - 6/b^23 - 12/b^21 - 50/b^19 - 
       85/b^17 - 131/b^15 - 314/b^13 - 430/b^11 - 480/b^9 - 956/b^7 - 
       1092/b^5 - 941/b^3 - 1499/b - 1499*b - 941*b^3 - 1092*b^5 - 956*b^7 - 
       480*b^9 - 430*b^11 - 314*b^13 - 131*b^15 - 85*b^17 - 50*b^19 - 
       12*b^21 - 6*b^23 + 80*b^25, 2183 + 97/b^26 + 15/b^24 + 31/b^22 + 
       64/b^20 + 143/b^18 + 173/b^16 + 330/b^14 + 593/b^12 + 617/b^10 + 
       946/b^8 + 1533/b^6 + 1295/b^4 + 1566/b^2 + 1566*b^2 + 1295*b^4 + 
       1533*b^6 + 946*b^8 + 617*b^10 + 593*b^12 + 330*b^14 + 173*b^16 + 
       143*b^18 + 64*b^20 + 31*b^22 + 15*b^24 + 97*b^26, 
      102/b^27 - 9/b^25 - 19/b^23 - 38/b^21 - 120/b^19 - 199/b^17 - 
       268/b^15 - 620/b^13 - 807/b^11 - 891/b^9 - 1677/b^7 - 1905/b^5 - 
       1639/b^3 - 2526/b - 2526*b - 1639*b^3 - 1905*b^5 - 1677*b^7 - 
       891*b^9 - 807*b^11 - 620*b^13 - 268*b^15 - 199*b^17 - 120*b^19 - 
       38*b^21 - 19*b^23 - 9*b^25 + 102*b^27, 3614 + 120/b^28 + 15/b^26 + 
       45/b^24 + 66/b^22 + 145/b^20 + 281/b^18 + 353/b^16 + 610/b^14 + 
       1099/b^12 + 1108/b^10 + 1667/b^8 + 2600/b^6 + 2244/b^4 + 2629/b^2 + 
       2629*b^2 + 2244*b^4 + 2600*b^6 + 1667*b^8 + 1108*b^10 + 1099*b^12 + 
       610*b^14 + 353*b^16 + 281*b^18 + 145*b^20 + 66*b^22 + 45*b^24 + 
       15*b^26 + 120*b^28, 126/b^29 - 6/b^27 - 26/b^25 - 56/b^23 - 97/b^21 - 
       270/b^19 - 402/b^17 - 547/b^15 - 1145/b^13 - 1473/b^11 - 1600/b^9 - 
       2875/b^7 - 3225/b^5 - 2803/b^3 - 4165/b - 4165*b - 2803*b^3 - 
       3225*b^5 - 2875*b^7 - 1600*b^9 - 1473*b^11 - 1145*b^13 - 547*b^15 - 
       402*b^17 - 270*b^19 - 97*b^21 - 56*b^23 - 26*b^25 - 6*b^27 + 126*b^29, 
      5876 + 149/b^30 + 15/b^28 + 45/b^26 + 98/b^24 + 148/b^22 + 282/b^20 + 
       564/b^18 + 655/b^16 + 1139/b^14 + 1945/b^12 + 1974/b^10 + 2849/b^8 + 
       4372/b^6 + 3758/b^4 + 4367/b^2 + 4367*b^2 + 3758*b^4 + 4372*b^6 + 
       2849*b^8 + 1974*b^10 + 1945*b^12 + 1139*b^14 + 655*b^16 + 564*b^18 + 
       282*b^20 + 148*b^22 + 98*b^24 + 45*b^26 + 15*b^28 + 149*b^30, 
      154/b^31 - 9/b^29 - 19/b^27 - 75/b^25 - 137/b^23 - 232/b^21 - 
       544/b^19 - 807/b^17 - 1035/b^15 - 2077/b^13 - 2612/b^11 - 2810/b^9 - 
       4833/b^7 - 5408/b^5 - 4720/b^3 - 6812/b - 6812*b - 4720*b^3 - 
       5408*b^5 - 4833*b^7 - 2810*b^9 - 2612*b^11 - 2077*b^13 - 1035*b^15 - 
       807*b^17 - 544*b^19 - 232*b^21 - 137*b^23 - 75*b^25 - 19*b^27 - 
       9*b^29 + 154*b^31, 9492 + 180/b^32 + 21/b^30 + 46/b^28 + 98/b^26 + 
       219/b^24 + 292/b^22 + 572/b^20 + 1046/b^18 + 1240/b^16 + 2036/b^14 + 
       3402/b^12 + 3413/b^10 + 4840/b^8 + 7195/b^6 + 6277/b^4 + 7163/b^2 + 
       7163*b^2 + 6277*b^4 + 7195*b^6 + 4840*b^8 + 3413*b^10 + 3402*b^12 + 
       2036*b^14 + 1240*b^16 + 1046*b^18 + 572*b^20 + 292*b^22 + 219*b^24 + 
       98*b^26 + 46*b^28 + 21*b^30 + 180*b^32, 189/b^33 - 12/b^31 - 27/b^29 - 
       60/b^27 - 181/b^25 - 320/b^23 - 474/b^21 - 1078/b^19 - 1513/b^17 - 
       1913/b^15 - 3646/b^13 - 4535/b^11 - 4808/b^9 - 8013/b^7 - 8892/b^5 - 
       7794/b^3 - 10991/b - 10991*b - 7794*b^3 - 8892*b^5 - 8013*b^7 - 
       4808*b^9 - 4535*b^11 - 3646*b^13 - 1913*b^15 - 1513*b^17 - 1078*b^19 - 
       474*b^21 - 320*b^23 - 181*b^25 - 60*b^27 - 27*b^29 - 12*b^31 + 
       189*b^33, 15115 + 216/b^34 + 21/b^32 + 63/b^30 + 99/b^28 + 220/b^26 + 
       432/b^24 + 596/b^22 + 1066/b^20 + 1946/b^18 + 2231/b^16 + 3589/b^14 + 
       5796/b^12 + 5846/b^10 + 8027/b^8 + 11733/b^6 + 10271/b^4 + 11614/b^2 + 
       11614*b^2 + 10271*b^4 + 11733*b^6 + 8027*b^8 + 5846*b^10 + 5796*b^12 + 
       3589*b^14 + 2231*b^16 + 1946*b^18 + 1066*b^20 + 596*b^22 + 432*b^24 + 
       220*b^26 + 99*b^28 + 63*b^30 + 21*b^32 + 216*b^34, 
      227/b^35 - 9/b^33 - 36/b^31 - 82/b^29 - 152/b^27 - 413/b^25 - 
       652/b^23 - 969/b^21 - 2009/b^19 - 2776/b^17 - 3426/b^15 - 6282/b^13 - 
       7683/b^11 - 8123/b^9 - 13081/b^7 - 14450/b^5 - 12746/b^3 - 17566/b - 
       17566*b - 12746*b^3 - 14450*b^5 - 13081*b^7 - 8123*b^9 - 7683*b^11 - 
       6282*b^13 - 3426*b^15 - 2776*b^17 - 2009*b^19 - 969*b^21 - 652*b^23 - 
       413*b^25 - 152*b^27 - 82*b^29 - 36*b^31 - 9*b^33 + 227*b^35}, 0, 36, 1]
