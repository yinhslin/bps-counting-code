f = SeriesData[x, 0, {1, 0, 1 + b^(-2) + b^2, b^(-3) - b^(-1) - b + b^3, 
      3 + 2/b^4 + b^(-2) + b^2 + 2*b^4, 2/b^5 - 2/b - 2*b + 2*b^5, 
      6 + 4/b^6 + b^(-4) + 3/b^2 + 3*b^2 + b^4 + 4*b^6, 
      4/b^7 - 4/b - 4*b + 4*b^7, 13 + 7/b^8 + 2/b^6 + 4/b^4 + 6/b^2 + 6*b^2 + 
       4*b^4 + 2*b^6 + 7*b^8, 7/b^9 - b^(-7) - b^(-5) - b^(-3) - 9/b - 9*b - 
       b^3 - b^5 - b^7 + 7*b^9, 22 + 11/b^10 + 4/b^8 + 7/b^6 + 7/b^4 + 
       14/b^2 + 14*b^2 + 7*b^4 + 7*b^6 + 4*b^8 + 11*b^10, 
      12/b^11 - b^(-9) - 2/b^7 - 2/b^5 - 4/b^3 - 18/b - 18*b - 4*b^3 - 
       2*b^5 - 2*b^7 - b^9 + 12*b^11, 45 + 18/b^12 + 4/b^10 + 12/b^8 + 
       13/b^6 + 17/b^4 + 24/b^2 + 24*b^2 + 17*b^4 + 13*b^6 + 12*b^8 + 
       4*b^10 + 18*b^12, 19/b^13 - 3/b^9 - 7/b^7 - 7/b^5 - 12/b^3 - 35/b - 
       35*b - 12*b^3 - 7*b^5 - 7*b^7 - 3*b^9 + 19*b^13, 
      73 + 27/b^14 + 6/b^12 + 14/b^10 + 23/b^8 + 29/b^6 + 29/b^4 + 50/b^2 + 
       50*b^2 + 29*b^4 + 29*b^6 + 23*b^8 + 14*b^10 + 6*b^12 + 27*b^14, 
      30/b^15 - b^(-13) - b^(-11) - 9/b^9 - 17/b^7 - 20/b^5 - 25/b^3 - 67/b - 
       67*b - 25*b^3 - 20*b^5 - 17*b^7 - 9*b^9 - b^11 - b^13 + 30*b^15, 
      134 + 40/b^16 + 8/b^14 + 19/b^12 + 26/b^10 + 51/b^8 + 49/b^6 + 61/b^4 + 
       84/b^2 + 84*b^2 + 61*b^4 + 49*b^6 + 51*b^8 + 26*b^10 + 19*b^12 + 
       8*b^14 + 40*b^16, 44/b^17 - b^(-13) - 7/b^11 - 25/b^9 - 43/b^7 - 
       42/b^5 - 60/b^3 - 121/b - 121*b - 60*b^3 - 42*b^5 - 43*b^7 - 25*b^9 - 
       7*b^11 - b^13 + 44*b^17, 221 + 58/b^18 + 10/b^16 + 24/b^14 + 35/b^12 + 
       57/b^10 + 87/b^8 + 102/b^6 + 100/b^4 + 156/b^2 + 156*b^2 + 100*b^4 + 
       102*b^6 + 87*b^8 + 57*b^10 + 35*b^12 + 24*b^14 + 10*b^16 + 58*b^18, 
      64/b^19 - 10/b^13 - 20/b^11 - 64/b^9 - 86/b^7 - 91/b^5 - 116/b^3 - 
       217/b - 217*b - 116*b^3 - 91*b^5 - 86*b^7 - 64*b^9 - 20*b^11 - 
       10*b^13 + 64*b^19, 382 + 82/b^20 + 13/b^18 + 33/b^16 + 45/b^14 + 
       76/b^12 + 100/b^10 + 175/b^8 + 169/b^6 + 198/b^4 + 265/b^2 + 265*b^2 + 
       198*b^4 + 169*b^6 + 175*b^8 + 100*b^10 + 76*b^12 + 45*b^14 + 33*b^16 + 
       13*b^18 + 82*b^20, 91/b^21 - b^(-17) - 11/b^15 - 29/b^13 - 63/b^11 - 
       125/b^9 - 183/b^7 - 179/b^5 - 222/b^3 - 383/b - 383*b - 222*b^3 - 
       179*b^5 - 183*b^7 - 125*b^9 - 63*b^11 - 29*b^13 - 11*b^15 - b^17 + 
       91*b^21, 617 + 113/b^22 + 17/b^20 + 41/b^18 + 61/b^16 + 97/b^14 + 
       126/b^12 + 202/b^10 + 296/b^8 + 318/b^6 + 332/b^4 + 469/b^2 + 
       469*b^2 + 332*b^4 + 318*b^6 + 296*b^8 + 202*b^10 + 126*b^12 + 
       97*b^14 + 61*b^16 + 41*b^18 + 17*b^20 + 113*b^22, 
      126/b^23 + b^(-21) + 2/b^19 - 16/b^17 - 36/b^15 - 86/b^13 - 127/b^11 - 
       265/b^9 - 335/b^7 - 340/b^5 - 415/b^3 - 654/b - 654*b - 415*b^3 - 
       340*b^5 - 335*b^7 - 265*b^9 - 127*b^11 - 86*b^13 - 36*b^15 - 16*b^17 + 
       2*b^19 + b^21 + 126*b^23, 1050 + 155/b^24 + 19/b^22 + 51/b^20 + 
       75/b^18 + 133/b^16 + 164/b^14 + 257/b^12 + 341/b^10 + 543/b^8 + 
       545/b^6 + 596/b^4 + 773/b^2 + 773*b^2 + 596*b^4 + 545*b^6 + 543*b^8 + 
       341*b^10 + 257*b^12 + 164*b^14 + 133*b^16 + 75*b^18 + 51*b^20 + 
       19*b^22 + 155*b^24, 171/b^25 + 3/b^23 + 4/b^21 - 16/b^19 - 49/b^17 - 
       114/b^15 - 171/b^13 - 285/b^11 - 491/b^9 - 626/b^7 - 621/b^5 - 
       749/b^3 - 1106/b - 1106*b - 749*b^3 - 621*b^5 - 626*b^7 - 491*b^9 - 
       285*b^11 - 171*b^13 - 114*b^15 - 49*b^17 - 16*b^19 + 4*b^21 + 3*b^23 + 
       171*b^25, 1669 + 207/b^26 + 25/b^24 + 61/b^22 + 94/b^20 + 160/b^18 + 
       226/b^16 + 332/b^14 + 425/b^12 + 638/b^10 + 918/b^8 + 955/b^6 + 
       1000/b^4 + 1323/b^2 + 1323*b^2 + 1000*b^4 + 955*b^6 + 918*b^8 + 
       638*b^10 + 425*b^12 + 332*b^14 + 226*b^16 + 160*b^18 + 94*b^20 + 
       61*b^22 + 25*b^24 + 207*b^26, 230/b^27 + 2/b^25 + 8/b^23 - 16/b^21 - 
       51/b^19 - 154/b^17 - 229/b^15 - 382/b^13 - 537/b^11 - 900/b^9 - 
       1111/b^7 - 1114/b^5 - 1288/b^3 - 1853/b - 1853*b - 1288*b^3 - 
       1114*b^5 - 1111*b^7 - 900*b^9 - 537*b^11 - 382*b^13 - 229*b^15 - 
       154*b^17 - 51*b^19 - 16*b^21 + 8*b^23 + 2*b^25 + 230*b^27, 
      2727 + 274/b^28 + 30/b^26 + 77/b^24 + 110/b^22 + 199/b^20 + 269/b^18 + 
       456/b^16 + 558/b^14 + 795/b^12 + 1088/b^10 + 1590/b^8 + 1595/b^6 + 
       1735/b^4 + 2159/b^2 + 2159*b^2 + 1735*b^4 + 1595*b^6 + 1590*b^8 + 
       1088*b^10 + 795*b^12 + 558*b^14 + 456*b^16 + 269*b^18 + 199*b^20 + 
       110*b^22 + 77*b^24 + 30*b^26 + 274*b^28, 303/b^29 + 5/b^27 + 9/b^25 - 
       16/b^23 - 58/b^21 - 171/b^19 - 307/b^17 - 519/b^15 - 708/b^13 - 
       1014/b^11 - 1595/b^9 - 1942/b^7 - 1918/b^5 - 2233/b^3 - 3036/b - 
       3036*b - 2233*b^3 - 1918*b^5 - 1942*b^7 - 1595*b^9 - 1014*b^11 - 
       708*b^13 - 519*b^15 - 307*b^17 - 171*b^19 - 58*b^21 - 16*b^23 + 
       9*b^25 + 5*b^27 + 303*b^29, 4347 + 358/b^30 + 35/b^28 + 91/b^26 + 
       140/b^24 + 234/b^22 + 330/b^20 + 545/b^18 + 767/b^16 + 1035/b^14 + 
       1353/b^12 + 1899/b^10 + 2622/b^8 + 2730/b^6 + 2837/b^4 + 3557/b^2 + 
       3557*b^2 + 2837*b^4 + 2730*b^6 + 2622*b^8 + 1899*b^10 + 1353*b^12 + 
       1035*b^14 + 767*b^16 + 545*b^18 + 330*b^20 + 234*b^22 + 140*b^24 + 
       91*b^26 + 35*b^28 + 358*b^30, 395/b^31 + 7/b^29 + 16/b^27 - 22/b^25 - 
       63/b^23 - 207/b^21 - 342/b^19 - 682/b^17 - 966/b^15 - 1336/b^13 - 
       1815/b^11 - 2770/b^9 - 3265/b^7 - 3280/b^5 - 3738/b^3 - 4927/b - 
       4927*b - 3738*b^3 - 3280*b^5 - 3265*b^7 - 2770*b^9 - 1815*b^11 - 
       1336*b^13 - 966*b^15 - 682*b^17 - 342*b^19 - 207*b^21 - 63*b^23 - 
       22*b^25 + 16*b^27 + 7*b^29 + 395*b^31, 6940 + 462/b^32 + 42/b^30 + 
       110/b^28 + 165/b^26 + 296/b^24 + 389/b^22 + 663/b^20 + 911/b^18 + 
       1431/b^16 + 1773/b^14 + 2358/b^12 + 3172/b^10 + 4417/b^8 + 4449/b^6 + 
       4738/b^4 + 5732/b^2 + 5732*b^2 + 4738*b^4 + 4449*b^6 + 4417*b^8 + 
       3172*b^10 + 2358*b^12 + 1773*b^14 + 1431*b^16 + 911*b^18 + 663*b^20 + 
       389*b^22 + 296*b^24 + 165*b^26 + 110*b^28 + 42*b^30 + 462*b^32, 
      509/b^33 + 8/b^31 + 20/b^29 - 17/b^27 - 83/b^25 - 244/b^23 - 412/b^21 - 
       786/b^19 - 1273/b^17 - 1822/b^15 - 2384/b^13 - 3218/b^11 - 4643/b^9 - 
       5504/b^7 - 5487/b^5 - 6175/b^3 - 7934/b - 7934*b - 6175*b^3 - 
       5487*b^5 - 5504*b^7 - 4643*b^9 - 3218*b^11 - 2384*b^13 - 1822*b^15 - 
       1273*b^17 - 786*b^19 - 412*b^21 - 244*b^23 - 83*b^25 - 17*b^27 + 
       20*b^29 + 8*b^31 + 509*b^33, 10868 + 589/b^34 + 51/b^32 + 129/b^30 + 
       196/b^28 + 347/b^26 + 490/b^24 + 787/b^22 + 1106/b^20 + 1694/b^18 + 
       2443/b^16 + 3097/b^14 + 3932/b^12 + 5374/b^10 + 7128/b^8 + 7329/b^6 + 
       7669/b^4 + 9229/b^2 + 9229*b^2 + 7669*b^4 + 7329*b^6 + 7128*b^8 + 
       5374*b^10 + 3932*b^12 + 3097*b^14 + 2443*b^16 + 1694*b^18 + 
       1106*b^20 + 787*b^22 + 490*b^24 + 347*b^26 + 196*b^28 + 129*b^30 + 
       51*b^32 + 589*b^34, 649/b^35 + 11/b^33 + 28/b^31 - 18/b^29 - 80/b^27 - 
       306/b^25 - 492/b^23 - 954/b^21 - 1458/b^19 - 2389/b^17 - 3252/b^15 - 
       4197/b^13 - 5437/b^11 - 7777/b^9 - 9005/b^7 - 9005/b^5 - 10068/b^3 - 
       12610/b - 12610*b - 10068*b^3 - 9005*b^5 - 9005*b^7 - 7777*b^9 - 
       5437*b^11 - 4197*b^13 - 3252*b^15 - 2389*b^17 - 1458*b^19 - 954*b^21 - 
       492*b^23 - 306*b^25 - 80*b^27 - 18*b^29 + 28*b^31 + 11*b^33 + 
       649*b^35}, 0, 36, 1]