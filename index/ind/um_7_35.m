f = SeriesData[x, 0, {1, 0, 3*s^2, 2*s*(-1 + s^2), s^2 + 8*s^4, 
      -2*s - 6*s^3 + 8*s^5, s^2*(2 - s^2 + 21*s^4), 
      2*s*(-1 - 4*s^2 - 7*s^4 + 12*s^6), s^2*(5 + 3*s^2 - 8*s^4 + 42*s^6), 
      2*s*(-1 - 5*s^2 - 9*s^4 - 13*s^6 + 28*s^8), 
      s^2*(6 + 13*s^2 - s^4 - 22*s^6 + 85*s^8), 
      2*s*(-1 - 7*s^2 - 10*s^4 - 19*s^6 - 18*s^8 + 55*s^10), 
      s^2*(9 + 21*s^2 + 23*s^4 - 28*s^6 - 44*s^8 + 159*s^10), 
      2*s*(-1 - 9*s^2 - 16*s^4 - 17*s^6 - 31*s^8 - 26*s^10 + 100*s^12), 
      s^2*(10 + 35*s^2 + 39*s^4 + 20*s^6 - 84*s^8 - 63*s^10 + 274*s^12), 
      2*s*(-1 - 13*s^2 - 22*s^4 - 28*s^6 - 17*s^8 - 54*s^10 - 36*s^12 + 
        171*s^14), s^2*(13 + 48*s^2 + 75*s^4 + 45*s^6 - 30*s^8 - 160*s^10 - 
        90*s^12 + 450*s^14), 2*s*(-1 - 16*s^2 - 37*s^4 - 37*s^6 - 24*s^8 - 
        22*s^10 - 85*s^12 - 54*s^14 + 276*s^16), 
      s^2*(14 + 69*s^2 + 104*s^4 + 116*s^6 - 7*s^8 - 111*s^10 - 225*s^12 - 
        117*s^14 + 708*s^16), 2*s*(-1 - 21*s^2 - 51*s^4 - 70*s^6 - 24*s^8 - 
        8*s^10 - 55*s^12 - 126*s^14 - 72*s^16 + 428*s^18), 
      s^2*(17 + 90*s^2 + 166*s^4 + 159*s^6 + 77*s^8 - 108*s^10 - 233*s^12 - 
        296*s^14 - 157*s^16 + 1068*s^18), 2*s*(-1 - 26*s^2 - 75*s^4 - 
        99*s^6 - 73*s^8 + 37*s^10 - 14*s^12 - 116*s^14 - 181*s^16 - 93*s^18 + 
        641*s^20), s^2*(18 + 119*s^2 + 228*s^4 + 283*s^6 + 90*s^8 - 
        265*s^12 - 307*s^14 - 393*s^16 - 205*s^18 + 1566*s^20), 
      2*s*(-1 - 32*s^2 - 103*s^4 - 157*s^6 - 107*s^8 + 5*s^10 + 110*s^12 - 
        95*s^14 - 193*s^16 - 238*s^18 - 117*s^20 + 928*s^22), 
      s^2*(21 + 153*s^2 + 327*s^4 + 400*s^6 + 225*s^8 - 97*s^10 - 92*s^12 - 
        439*s^14 - 399*s^16 - 529*s^18 - 261*s^20 + 2237*s^22), 
      -2*s - 76*s^3 - 280*s^5 - 454*s^7 - 402*s^9 + 44*s^11 + 238*s^13 + 
       272*s^15 - 528*s^17 - 528*s^19 - 614*s^21 - 292*s^23 + 2622*s^25, 
      s^2*(22 + 193*s^2 + 449*s^4 + 604*s^6 + 337*s^8 - 30*s^10 - 309*s^12 - 
        91*s^14 - 596*s^16 - 540*s^18 - 689*s^20 - 323*s^22 + 3115*s^24), 
      -2*s - 92*s^3 - 368*s^5 - 650*s^7 - 638*s^9 - 84*s^11 + 498*s^13 + 
       376*s^15 - 20*s^17 - 826*s^19 - 688*s^21 - 770*s^23 - 360*s^25 + 
       3624*s^27, s^2*(25 + 239*s^2 + 614*s^4 + 871*s^6 + 566*s^8 - 
        119*s^10 - 333*s^12 - 348*s^14 - 140*s^16 - 779*s^18 - 751*s^20 - 
        867*s^22 - 395*s^24 + 4252*s^26), 2*s*(-1 - 53*s^2 - 242*s^4 - 
        451*s^6 - 489*s^8 - 121*s^10 + 288*s^12 + 488*s^14 + 31*s^16 - 
        246*s^18 - 529*s^20 - 427*s^22 - 481*s^24 - 219*s^26 + 2452*s^28), 
      s^2*(26 + 295*s^2 + 811*s^4 + 1245*s^6 + 919*s^8 - 104*s^10 - 
        749*s^12 - 246*s^14 - 198*s^16 - 309*s^18 - 1110*s^20 - 983*s^22 - 
        1067*s^24 - 475*s^26 + 5703*s^28), 
      2*s*(-1 - 62*s^2 - 307*s^4 - 626*s^6 - 725*s^8 - 253*s^10 + 378*s^12 + 
        648*s^14 + 452*s^16 - 327*s^18 - 385*s^20 - 659*s^22 - 542*s^24 - 
        592*s^26 - 262*s^28 + 3263*s^30), s^2*(29 + 358*s^2 + 1079*s^4 + 
        1717*s^6 + 1431*s^8 - 46*s^10 - 1175*s^12 - 974*s^14 + 461*s^16 - 
        440*s^18 - 503*s^20 - 1540*s^22 - 1231*s^24 - 1297*s^26 - 569*s^28 + 
        7518*s^30), 2*s*(-1 - 71*s^2 - 389*s^4 - 836*s^6 - 1069*s^8 - 
        461*s^10 + 480*s^12 + 998*s^14 + 597*s^16 + 177*s^18 - 774*s^20 - 
        385*s^22 - 833*s^24 - 682*s^26 - 716*s^28 - 311*s^30 + 4276*s^32), 
      s^2*(30 + 429*s^2 + 1396*s^4 + 2388*s^6 + 2129*s^8 + 149*s^10 - 
        1763*s^12 - 1737*s^14 + 3*s^16 + 1116*s^18 - 1107*s^20 - 876*s^22 - 
        1958*s^24 - 1505*s^26 - 1559*s^28 - 671*s^30 + 9773*s^32), 
      2*s*(-1 - 81*s^2 - 486*s^4 - 1115*s^6 - 1497*s^8 - 825*s^10 + 
        595*s^12 + 1457*s^14 + 1049*s^16 + 124*s^18 - 203*s^20 - 962*s^22 - 
        452*s^24 - 1065*s^26 - 842*s^28 - 854*s^30 - 365*s^32 + 5523*s^34)}, 
     0, 36, 1]