f = SeriesData[x, 0, {1, s/b + b*s, -1 + s^2 + (2*s^2)/b^2 + 2*b^2*s^2, 
      (3*s^3)/b^3 + 3*b^3*s^3 + (-s + 2*s^3)/b + b*(-s + 2*s^3), 
      -1 - s^2 + 4*s^4 + (5*s^4)/b^4 + 5*b^4*s^4 + (-2*s^2 + 3*s^4)/b^2 + 
       b^2*(-2*s^2 + 3*s^4), (7*s^5)/b^5 + 7*b^5*s^5 + (-3*s^3 + 5*s^5)/b^3 + 
       b^3*(-3*s^3 + 5*s^5) + (-s - 2*s^3 + 6*s^5)/b + 
       b*(-s - 2*s^3 + 6*s^5), (11*s^6)/b^6 + 11*b^6*s^6 + 
       (s^4*(-5 + 7*s^2))/b^4 + b^4*s^4*(-5 + 7*s^2) + 
       s^2*(-1 - 4*s^2 + 9*s^4) + (s^2*(-2 - 3*s^2 + 10*s^4))/b^2 + 
       b^2*s^2*(-2 - 3*s^2 + 10*s^4), (15*s^7)/b^7 + 15*b^7*s^7 + 
       (-7*s^5 + 11*s^7)/b^5 + b^5*(-7*s^5 + 11*s^7) + 
       (-3*s^3 - 5*s^5 + 14*s^7)/b^3 + b^3*(-3*s^3 - 5*s^5 + 14*s^7) + 
       (-2*s^3 - 6*s^5 + 15*s^7)/b + b*(-2*s^3 - 6*s^5 + 15*s^7), 
      -4*s^4 - 9*s^6 + 25*s^8 + (22*s^8)/b^8 + 22*b^8*s^8 + 
       (-11*s^6 + 15*s^8)/b^6 + b^6*(-11*s^6 + 15*s^8) + 
       (-3*s^4 - 10*s^6 + 21*s^8)/b^2 + b^2*(-3*s^4 - 10*s^6 + 21*s^8) + 
       (-5*s^4 - 7*s^6 + 22*s^8)/b^4 + b^4*(-5*s^4 - 7*s^6 + 22*s^8), 
      (30*s^9)/b^9 + 30*b^9*s^9 + (-15*s^7 + 22*s^9)/b^7 + 
       b^7*(-15*s^7 + 22*s^9) + (-7*s^5 - 11*s^7 + 30*s^9)/b^5 + 
       b^5*(-7*s^5 - 11*s^7 + 30*s^9) + (-5*s^5 - 14*s^7 + 33*s^9)/b^3 + 
       b^3*(-5*s^5 - 14*s^7 + 33*s^9) + (-6*s^5 - 15*s^7 + 35*s^9)/b + 
       b*(-6*s^5 - 15*s^7 + 35*s^9), 1 - 9*s^6 - 25*s^8 + 49*s^10 + 
       (42*s^10)/b^10 + 42*b^10*s^10 + (2*s^8*(-11 + 15*s^2))/b^8 + 
       2*b^8*s^8*(-11 + 15*s^2) + (s^6*(-11 - 15*s^2 + 44*s^4))/b^6 + 
       b^6*s^6*(-11 - 15*s^2 + 44*s^4) + (s^6*(-7 - 22*s^2 + 45*s^4))/b^4 + 
       b^4*s^6*(-7 - 22*s^2 + 45*s^4) + (s^6*(-10 - 21*s^2 + 55*s^4))/b^2 + 
       b^2*s^6*(-10 - 21*s^2 + 55*s^4), (55*s^11)/b^11 + 55*b^11*s^11 + 
       (s^9*(-30 + 41*s^2))/b^9 + b^9*s^9*(-30 + 41*s^2) + 
       (s^7*(-15 - 22*s^2 + 59*s^4))/b^7 + b^7*s^7*(-15 - 22*s^2 + 59*s^4) + 
       (s^7*(-11 - 30*s^2 + 65*s^4))/b^5 + b^5*s^7*(-11 - 30*s^2 + 65*s^4) + 
       (s^7*(-14 - 33*s^2 + 74*s^4))/b^3 + b^3*s^7*(-14 - 33*s^2 + 74*s^4) + 
       (s - 15*s^7 - 35*s^9 + 76*s^11)/b + b*(s - 15*s^7 - 35*s^9 + 76*s^11), 
      s^2 - 25*s^8 - 48*s^10 + 118*s^12 + (75*s^12)/b^12 + 75*b^12*s^12 + 
       (s^10*(-41 + 54*s^2))/b^10 + b^10*s^10*(-41 + 54*s^2) + 
       (s^8*(-22 - 29*s^2 + 81*s^4))/b^8 + b^8*s^8*(-22 - 29*s^2 + 81*s^4) + 
       (s^8*(-15 - 43*s^2 + 87*s^4))/b^6 + b^6*s^8*(-15 - 43*s^2 + 87*s^4) + 
       (s^8*(-22 - 44*s^2 + 107*s^4))/b^4 + 
       b^4*s^8*(-22 - 44*s^2 + 107*s^4) + 
       (s^2*(2 - 21*s^6 - 54*s^8 + 102*s^10))/b^2 + 
       b^2*s^2*(2 - 21*s^6 - 54*s^8 + 102*s^10), (97*s^13)/b^13 + 
       97*b^13*s^13 + (s^11*(-54 + 73*s^2))/b^11 + b^11*s^11*(-54 + 73*s^2) + 
       (2*s^9*(-15 - 31*s^2 + 71*s^4))/b^5 + 
       2*b^5*s^9*(-15 - 31*s^2 + 71*s^4) + (s^9*(-30 - 39*s^2 + 106*s^4))/
        b^9 + b^9*s^9*(-30 - 39*s^2 + 106*s^4) + 
       (s^9*(-22 - 56*s^2 + 119*s^4))/b^7 + 
       b^7*s^9*(-22 - 56*s^2 + 119*s^4) + 
       (s^3*(3 - 33*s^6 - 71*s^8 + 146*s^10))/b^3 + 
       b^3*s^3*(3 - 33*s^6 - 71*s^8 + 146*s^10) + 
       (s^3*(2 - 35*s^6 - 73*s^8 + 157*s^10))/b + 
       b*s^3*(2 - 35*s^6 - 73*s^8 + 157*s^10), 1 + 4*s^4 - 50*s^10 - 
       110*s^12 + 207*s^14 + (128*s^14)/b^14 + 128*b^14*s^14 + 
       (s^12*(-73 + 94*s^2))/b^12 + b^12*s^12*(-73 + 94*s^2) + 
       (s^10*(-42 - 51*s^2 + 143*s^4))/b^10 + 
       b^10*s^10*(-42 - 51*s^2 + 143*s^4) + (s^10*(-31 - 76*s^2 + 155*s^4))/
        b^8 + b^8*s^10*(-31 - 76*s^2 + 155*s^4) + 
       (s^10*(-45 - 80*s^2 + 194*s^4))/b^6 + 
       b^6*s^10*(-45 - 80*s^2 + 194*s^4) + 
       (s^4*(5 - 46*s^6 - 99*s^8 + 193*s^10))/b^4 + 
       b^4*s^4*(5 - 46*s^6 - 99*s^8 + 193*s^10) + 
       (s^4*(3 - 56*s^6 - 94*s^8 + 224*s^10))/b^2 + 
       b^2*s^4*(3 - 56*s^6 - 94*s^8 + 224*s^10), (164*s^15)/b^15 + 
       164*b^15*s^15 + (s^13*(-94 + 123*s^2))/b^13 + 
       b^13*s^13*(-94 + 123*s^2) + (2*s^11*(-21 - 49*s^2 + 104*s^4))/b^9 + 
       2*b^9*s^11*(-21 - 49*s^2 + 104*s^4) + (s^11*(-55 - 68*s^2 + 183*s^4))/
        b^11 + b^11*s^11*(-55 - 68*s^2 + 183*s^4) + 
       (s^11*(-61 - 108*s^2 + 251*s^4))/b^7 + 
       b^7*s^11*(-61 - 108*s^2 + 251*s^4) + 
       (s^5*(7 - 68*s^6 - 127*s^8 + 262*s^10))/b^5 + 
       b^5*s^5*(7 - 68*s^6 - 127*s^8 + 262*s^10) + 
       (s^5*(5 - 77*s^6 - 129*s^8 + 294*s^10))/b^3 + 
       b^3*s^5*(5 - 77*s^6 - 129*s^8 + 294*s^10) + 
       (s + 6*s^5 - 79*s^11 - 139*s^13 + 293*s^15)/b + 
       b*(s + 6*s^5 - 79*s^11 - 139*s^13 + 293*s^15), 
      s^2 + 9*s^6 - s^10 - 126*s^12 - 171*s^14 + 414*s^16 + (212*s^16)/b^16 + 
       212*b^16*s^16 + (s^14*(-123 + 157*s^2))/b^14 + 
       b^14*s^14*(-123 + 157*s^2) + (s^12*(-75 - 86*s^2 + 239*s^4))/b^12 + 
       b^12*s^12*(-75 - 86*s^2 + 239*s^4) + 
       (s^10*(-1 - 56*s^2 - 130*s^4 + 265*s^6))/b^10 + 
       b^10*s^10*(-1 - 56*s^2 - 130*s^4 + 265*s^6) + 
       (s^10*(-1 - 83*s^2 - 137*s^4 + 336*s^6))/b^8 + 
       b^8*s^10*(-1 - 83*s^2 - 137*s^4 + 336*s^6) + 
       (s^6*(11 - s^4 - 92*s^6 - 170*s^8 + 337*s^10))/b^6 + 
       b^6*s^6*(11 - s^4 - 92*s^6 - 170*s^8 + 337*s^10) + 
       (s^6*(7 - s^4 - 114*s^6 - 163*s^8 + 398*s^10))/b^4 + 
       b^4*s^6*(7 - s^4 - 114*s^6 - 163*s^8 + 398*s^10) + 
       (s^2*(2 + 10*s^4 - s^8 - 110*s^10 - 189*s^12 + 383*s^14))/b^2 + 
       b^2*s^2*(2 + 10*s^4 - s^8 - 110*s^10 - 189*s^12 + 383*s^14), 
      (267*s^17)/b^17 + 267*b^17*s^17 + (s^15*(-157 + 201*s^2))/b^15 + 
       b^15*s^15*(-157 + 201*s^2) + (s^13*(-97 - 111*s^2 + 303*s^4))/b^13 + 
       b^13*s^13*(-97 - 111*s^2 + 303*s^4) + 
       (s^11*(-1 - 76*s^2 - 163*s^4 + 344*s^6))/b^11 + 
       b^11*s^11*(-1 - 76*s^2 - 163*s^4 + 344*s^6) + 
       (s^11*(-2 - 110*s^2 - 180*s^4 + 425*s^6))/b^9 + 
       b^9*s^11*(-2 - 110*s^2 - 180*s^4 + 425*s^6) + 
       (s^7*(15 - 4*s^4 - 126*s^6 - 213*s^8 + 448*s^10))/b^7 + 
       b^7*s^7*(15 - 4*s^4 - 126*s^6 - 213*s^8 + 448*s^10) + 
       (s^7*(11 - 3*s^4 - 152*s^6 - 215*s^8 + 509*s^10))/b^5 + 
       b^5*s^7*(11 - 3*s^4 - 152*s^6 - 215*s^8 + 509*s^10) + 
       (s^3*(3 + 14*s^4 - 3*s^8 - 161*s^10 - 237*s^12 + 515*s^14))/b^3 + 
       b^3*s^3*(3 + 14*s^4 - 3*s^8 - 161*s^10 - 237*s^12 + 515*s^14) + 
       (s^3*(2 + 15*s^4 - 3*s^8 - 174*s^10 - 230*s^12 + 538*s^14))/b + 
       b*s^3*(2 + 15*s^4 - 3*s^8 - 174*s^10 - 230*s^12 + 538*s^14), 
      (340*s^18)/b^18 + 340*b^18*s^18 + (3*s^16*(-67 + 84*s^2))/b^16 + 
       3*b^16*s^16*(-67 + 84*s^2) + (s^14*(-128 - 139*s^2 + 387*s^4))/b^14 + 
       b^14*s^14*(-128 - 139*s^2 + 387*s^4) + 
       (s^12*(-2 - 99*s^2 - 209*s^4 + 434*s^6))/b^12 + 
       b^12*s^12*(-2 - 99*s^2 - 209*s^4 + 434*s^6) + 
       (s^10*(-1 - 3*s^2 - 149*s^4 - 222*s^6 + 550*s^8))/b^10 + 
       b^10*s^10*(-1 - 3*s^2 - 149*s^4 - 222*s^6 + 550*s^8) + 
       (s^8*(22 - 6*s^4 - 167*s^6 - 277*s^8 + 564*s^10))/b^8 + 
       b^8*s^8*(22 - 6*s^4 - 167*s^6 - 277*s^8 + 564*s^10) + 
       (s^8*(15 - 8*s^4 - 209*s^6 - 264*s^8 + 675*s^10))/b^6 + 
       b^6*s^8*(15 - 8*s^4 - 209*s^6 - 264*s^8 + 675*s^10) + 
       (s^4*(5 + 22*s^4 - 9*s^8 - 215*s^10 - 310*s^12 + 655*s^14))/b^4 + 
       b^4*s^4*(5 + 22*s^4 - 9*s^8 - 215*s^10 - 310*s^12 + 655*s^14) + 
       s^4*(4 + 25*s^4 - 8*s^8 - 239*s^10 - 309*s^12 + 697*s^14) + 
       (s^4*(3 + 21*s^4 - 8*s^8 - 252*s^10 - 284*s^12 + 722*s^14))/b^2 + 
       b^2*s^4*(3 + 21*s^4 - 8*s^8 - 252*s^10 - 284*s^12 + 722*s^14), 
      (423*s^19)/b^19 + 423*b^19*s^19 + (6*s^17*(-42 + 53*s^2))/b^17 + 
       6*b^17*s^17*(-42 + 53*s^2) + (s^15*(-164 - 175*s^2 + 482*s^4))/b^15 + 
       b^15*s^15*(-164 - 175*s^2 + 482*s^4) + 
       (s^13*(-3 - 130*s^2 - 259*s^4 + 551*s^6))/b^13 + 
       b^13*s^13*(-3 - 130*s^2 - 259*s^4 + 551*s^6) + 
       (s^11*(-1 - 5*s^2 - 192*s^4 - 281*s^6 + 690*s^8))/b^11 + 
       b^11*s^11*(-1 - 5*s^2 - 192*s^4 - 281*s^6 + 690*s^8) + 
       (s^9*(30 - s^2 - 10*s^4 - 226*s^6 - 338*s^8 + 725*s^10))/b^9 + 
       b^9*s^9*(30 - s^2 - 10*s^4 - 226*s^6 - 338*s^8 + 725*s^10) + 
       (s^9*(22 - s^2 - 11*s^4 - 275*s^6 - 339*s^8 + 845*s^10))/b^7 + 
       b^7*s^9*(22 - s^2 - 11*s^4 - 275*s^6 - 339*s^8 + 845*s^10) + 
       (s^5*(7 + 30*s^4 - 18*s^8 - 295*s^10 - 377*s^12 + 864*s^14))/b^5 + 
       b^5*s^5*(7 + 30*s^4 - 18*s^8 - 295*s^10 - 377*s^12 + 864*s^14) + 
       (s^5*(5 + 33*s^4 - 19*s^8 - 333*s^10 - 367*s^12 + 914*s^14))/b^3 + 
       b^3*s^5*(5 + 33*s^4 - 19*s^8 - 333*s^10 - 367*s^12 + 914*s^14) + 
       (s^5*(6 + 35*s^4 - 19*s^8 - 340*s^10 - 380*s^12 + 931*s^14))/b + 
       b*s^5*(6 + 35*s^4 - 19*s^8 - 340*s^10 - 380*s^12 + 931*s^14), 
      (530*s^20)/b^20 + 530*b^20*s^20 + (3*s^18*(-106 + 131*s^2))/b^18 + 
       3*b^18*s^18*(-106 + 131*s^2) + (s^16*(-212 - 215*s^2 + 606*s^4))/
        b^16 + b^16*s^16*(-212 - 215*s^2 + 606*s^4) + 
       (s^14*(-5 - 168*s^2 - 324*s^4 + 683*s^6))/b^14 + 
       b^14*s^14*(-5 - 168*s^2 - 324*s^4 + 683*s^6) + 
       (s^12*(-2 - 8*s^2 - 252*s^4 - 343*s^6 + 873*s^8))/b^12 + 
       b^12*s^12*(-2 - 8*s^2 - 252*s^4 - 343*s^6 + 873*s^8) + 
       (s^10*(41 - s^2 - 16*s^4 - 292*s^6 - 424*s^8 + 905*s^10))/b^10 + 
       b^10*s^10*(41 - s^2 - 16*s^4 - 292*s^6 - 424*s^8 + 905*s^10) + 
       (s^10*(30 - 3*s^2 - 19*s^4 - 371*s^6 - 406*s^8 + 1083*s^10))/b^8 + 
       b^8*s^10*(30 - 3*s^2 - 19*s^4 - 371*s^6 - 406*s^8 + 1083*s^10) + 
       (s^6*(11 + 44*s^4 - 3*s^6 - 27*s^8 - 387*s^10 - 482*s^12 + 1076*s^14))/
        b^6 + b^6*s^6*(11 + 44*s^4 - 3*s^6 - 27*s^8 - 387*s^10 - 482*s^12 + 
         1076*s^14) + (s^6*(10 + 55*s^4 - 41*s^8 - 447*s^10 - 490*s^12 + 
          1174*s^14))/b^2 + b^2*s^6*(10 + 55*s^4 - 41*s^8 - 447*s^10 - 
         490*s^12 + 1174*s^14) + (s^6*(7 + 45*s^4 - s^6 - 34*s^8 - 454*s^10 - 
          439*s^12 + 1203*s^14))/b^4 + b^4*s^6*(7 + 45*s^4 - s^6 - 34*s^8 - 
         454*s^10 - 439*s^12 + 1203*s^14) + s^6*(9 + 49*s^4 - 40*s^8 - 
         477*s^10 - 463*s^12 + 1240*s^14), (653*s^21)/b^21 + 653*b^21*s^21 + 
       (s^19*(-393 + 488*s^2))/b^19 + b^19*s^19*(-393 + 488*s^2) + 
       (s^17*(-267 - 266*s^2 + 745*s^4))/b^17 + 
       b^17*s^17*(-267 - 266*s^2 + 745*s^4) + 
       (s^15*(-7 - 216*s^2 - 394*s^4 + 854*s^6))/b^15 + 
       b^15*s^15*(-7 - 216*s^2 - 394*s^4 + 854*s^6) + 
       (s^13*(-3 - 12*s^2 - 322*s^4 - 424*s^6 + 1076*s^8))/b^13 + 
       b^13*s^13*(-3 - 12*s^2 - 322*s^4 - 424*s^6 + 1076*s^8) + 
       (s^11*(54 - 2*s^2 - 25*s^4 - 382*s^6 - 513*s^8 + 1138*s^10))/b^11 + 
       b^11*s^11*(54 - 2*s^2 - 25*s^4 - 382*s^6 - 513*s^8 + 1138*s^10) + 
       (s^11*(40 - 4*s^2 - 29*s^4 - 474*s^6 - 502*s^8 + 1346*s^10))/b^9 + 
       b^9*s^11*(40 - 4*s^2 - 29*s^4 - 474*s^6 - 502*s^8 + 1346*s^10) + 
       (s^7*(15 + 59*s^4 - 5*s^6 - 44*s^8 - 517*s^10 - 573*s^12 + 1372*s^14))/
        b^7 + b^7*s^7*(15 + 59*s^4 - 5*s^6 - 44*s^8 - 517*s^10 - 573*s^12 + 
         1372*s^14) + (s^7*(11 + 65*s^4 - 6*s^6 - 52*s^8 - 588*s^10 - 
          557*s^12 + 1492*s^14))/b^5 + b^5*s^7*(11 + 65*s^4 - 6*s^6 - 
         52*s^8 - 588*s^10 - 557*s^12 + 1492*s^14) + 
       (s^7*(14 + 74*s^4 - 2*s^6 - 67*s^8 - 602*s^10 - 584*s^12 + 1539*s^14))/
        b^3 + b^3*s^7*(14 + 74*s^4 - 2*s^6 - 67*s^8 - 602*s^10 - 584*s^12 + 
         1539*s^14) + (s^7*(15 + 76*s^4 - s^6 - 77*s^8 - 620*s^10 - 
          593*s^12 + 1557*s^14))/b + b*s^7*(15 + 76*s^4 - s^6 - 77*s^8 - 
         620*s^10 - 593*s^12 + 1557*s^14), (807*s^22)/b^22 + 807*b^22*s^22 + 
       (2*s^20*(-244 + 299*s^2))/b^20 + 2*b^20*s^20*(-244 + 299*s^2) + 
       (2*s^18*(-170 - 161*s^2 + 461*s^4))/b^18 + 
       2*b^18*s^18*(-170 - 161*s^2 + 461*s^4) + 
       (s^16*(-11 - 274*s^2 - 485*s^4 + 1045*s^6))/b^16 + 
       b^16*s^16*(-11 - 274*s^2 - 485*s^4 + 1045*s^6) + 
       (s^14*(-5 - 18*s^2 - 412*s^4 - 508*s^6 + 1341*s^8))/b^14 + 
       b^14*s^14*(-5 - 18*s^2 - 412*s^4 - 508*s^6 + 1341*s^8) + 
       (s^12*(73 - 3*s^2 - 37*s^4 - 487*s^6 - 629*s^8 + 1396*s^10))/b^12 + 
       b^12*s^12*(73 - 3*s^2 - 37*s^4 - 487*s^6 - 629*s^8 + 1396*s^10) + 
       (s^12*(53 - 7*s^2 - 45*s^4 - 616*s^6 - 598*s^8 + 1688*s^10))/b^10 + 
       b^10*s^12*(53 - 7*s^2 - 45*s^4 - 616*s^6 - 598*s^8 + 1688*s^10) + 
       (s^8*(22 + s^2 + 79*s^4 - 8*s^6 - 69*s^8 - 658*s^10 - 707*s^12 + 
          1698*s^14))/b^8 + b^8*s^8*(22 + s^2 + 79*s^4 - 8*s^6 - 69*s^8 - 
         658*s^10 - 707*s^12 + 1698*s^14) + 
       (s^8*(15 + s^2 + 86*s^4 - 9*s^6 - 83*s^8 - 777*s^10 - 653*s^12 + 
          1898*s^14))/b^6 + b^6*s^8*(15 + s^2 + 86*s^4 - 9*s^6 - 83*s^8 - 
         777*s^10 - 653*s^12 + 1898*s^14) + 
       (s^8*(22 + s^2 + 107*s^4 - 10*s^6 - 104*s^8 - 771*s^10 - 742*s^12 + 
          1902*s^14))/b^4 + b^4*s^8*(22 + s^2 + 107*s^4 - 10*s^6 - 104*s^8 - 
         771*s^10 - 742*s^12 + 1902*s^14) + s^8*(25 + s^2 + 118*s^4 - 4*s^6 - 
         137*s^8 - 803*s^10 - 757*s^12 + 1947*s^14) + 
       (s^8*(21 + s^2 + 102*s^4 - 8*s^6 - 120*s^8 - 826*s^10 - 700*s^12 + 
          2036*s^14))/b^2 + b^2*s^8*(21 + s^2 + 102*s^4 - 8*s^6 - 120*s^8 - 
         826*s^10 - 700*s^12 + 2036*s^14), (984*s^23)/b^23 + 984*b^23*s^23 + 
       (2*s^21*(-299 + 366*s^2))/b^21 + 2*b^21*s^21*(-299 + 366*s^2) + 
       (s^19*(-423 - 393*s^2 + 1123*s^4))/b^19 + 
       b^19*s^19*(-423 - 393*s^2 + 1123*s^4) + 
       (s^17*(-15 - 347*s^2 - 583*s^4 + 1286*s^6))/b^17 + 
       b^17*s^17*(-15 - 347*s^2 - 583*s^4 + 1286*s^6) + 
       (s^15*(-7 - 26*s^2 - 516*s^4 - 619*s^6 + 1632*s^8))/b^15 + 
       b^15*s^15*(-7 - 26*s^2 - 516*s^4 - 619*s^6 + 1632*s^8) + 
       (s^13*(94 - 5*s^2 - 55*s^4 - 620*s^6 - 748*s^8 + 1730*s^10))/b^13 + 
       b^13*s^13*(94 - 5*s^2 - 55*s^4 - 620*s^6 - 748*s^8 + 1730*s^10) + 
       (s^13*(71 - 11*s^2 - 66*s^4 - 776*s^6 - 725*s^8 + 2062*s^10))/b^11 + 
       b^11*s^13*(71 - 11*s^2 - 66*s^4 - 776*s^6 - 725*s^8 + 2062*s^10) + 
       (s^9*(30 + s^2 + 104*s^4 - 13*s^6 - 103*s^8 - 845*s^10 - 841*s^12 + 
          2119*s^14))/b^9 + b^9*s^9*(30 + s^2 + 104*s^4 - 13*s^6 - 103*s^8 - 
         845*s^10 - 841*s^12 + 2119*s^14) + 
       (s^9*(22 + 3*s^2 + 115*s^4 - 15*s^6 - 127*s^8 - 974*s^10 - 801*s^12 + 
          2341*s^14))/b^7 + b^7*s^9*(22 + 3*s^2 + 115*s^4 - 15*s^6 - 
         127*s^8 - 974*s^10 - 801*s^12 + 2341*s^14) + 
       (s^9*(30 + 3*s^2 + 139*s^4 - 15*s^6 - 161*s^8 - 1004*s^10 - 870*s^12 + 
          2410*s^14))/b^5 + b^5*s^9*(30 + 3*s^2 + 139*s^4 - 15*s^6 - 
         161*s^8 - 1004*s^10 - 870*s^12 + 2410*s^14) + 
       (s^9*(33 + 3*s^2 + 146*s^4 - 22*s^6 - 184*s^8 - 1044*s^10 - 888*s^12 + 
          2506*s^14))/b^3 + b^3*s^9*(33 + 3*s^2 + 146*s^4 - 22*s^6 - 
         184*s^8 - 1044*s^10 - 888*s^12 + 2506*s^14) + 
       (s^9*(35 + 3*s^2 + 157*s^4 - 18*s^6 - 203*s^8 - 1060*s^10 - 890*s^12 + 
          2537*s^14))/b + b*s^9*(35 + 3*s^2 + 157*s^4 - 18*s^6 - 203*s^8 - 
         1060*s^10 - 890*s^12 + 2537*s^14), -1 + 49*s^10 + 8*s^12 + 
       207*s^14 - 50*s^16 - 294*s^18 - 1381*s^20 - 1034*s^22 + 3299*s^24 + 
       (1204*s^24)/b^24 + 1204*b^24*s^24 + (s^22*(-732 + 887*s^2))/b^22 + 
       b^22*s^22*(-732 + 887*s^2) + (s^20*(-529 - 471*s^2 + 1370*s^4))/b^20 + 
       b^20*s^20*(-529 - 471*s^2 + 1370*s^4) + 
       (s^18*(-22 - 432*s^2 - 706*s^4 + 1559*s^6))/b^18 + 
       b^18*s^18*(-22 - 432*s^2 - 706*s^4 + 1559*s^6) + 
       (s^16*(-11 - 37*s^2 - 647*s^4 - 732*s^6 + 2002*s^8))/b^16 + 
       b^16*s^16*(-11 - 37*s^2 - 647*s^4 - 732*s^6 + 2002*s^8) + 
       (s^14*(123 - 7*s^2 - 79*s^4 - 773*s^6 - 904*s^8 + 2096*s^10))/b^14 + 
       b^14*s^14*(123 - 7*s^2 - 79*s^4 - 773*s^6 - 904*s^8 + 2096*s^10) + 
       (s^14*(91 - 17*s^2 - 97*s^4 - 978*s^6 - 848*s^8 + 2549*s^10))/b^12 + 
       b^12*s^14*(91 - 17*s^2 - 97*s^4 - 978*s^6 - 848*s^8 + 2549*s^10) + 
       (s^10*(42 + 2*s^2 + 139*s^4 - 21*s^6 - 152*s^8 - 1054*s^10 - 
          1017*s^12 + 2578*s^14))/b^10 + b^10*s^10*(42 + 2*s^2 + 139*s^4 - 
         21*s^6 - 152*s^8 - 1054*s^10 - 1017*s^12 + 2578*s^14) + 
       (s^10*(30 + 3*s^2 + 150*s^4 - 25*s^6 - 187*s^8 - 1232*s^10 - 
          942*s^12 + 2915*s^14))/b^8 + b^8*s^10*(30 + 3*s^2 + 150*s^4 - 
         25*s^6 - 187*s^8 - 1232*s^10 - 942*s^12 + 2915*s^14) + 
       (s^10*(44 + 7*s^2 + 187*s^4 - 26*s^6 - 243*s^8 - 1242*s^10 - 
          1067*s^12 + 2963*s^14))/b^6 + b^6*s^10*(44 + 7*s^2 + 187*s^4 - 
         26*s^6 - 243*s^8 - 1242*s^10 - 1067*s^12 + 2963*s^14) + 
       (s^10*(55 + 8*s^2 + 223*s^4 - 42*s^6 - 306*s^8 - 1327*s^10 - 
          1126*s^12 + 3111*s^14))/b^2 + b^2*s^10*(55 + 8*s^2 + 223*s^4 - 
         42*s^6 - 306*s^8 - 1327*s^10 - 1126*s^12 + 3111*s^14) + 
       (s^10*(45 + 8*s^2 + 188*s^4 - 35*s^6 - 275*s^8 - 1342*s^10 - 
          1030*s^12 + 3167*s^14))/b^4 + b^4*s^10*(45 + 8*s^2 + 188*s^4 - 
         35*s^6 - 275*s^8 - 1342*s^10 - 1030*s^12 + 3167*s^14), 
      (1455*s^25)/b^25 + 1455*b^25*s^25 + (s^23*(-887 + 1076*s^2))/b^23 + 
       b^23*s^23*(-887 + 1076*s^2) + (s^21*(-652 - 565*s^2 + 1651*s^4))/
        b^21 + b^21*s^21*(-652 - 565*s^2 + 1651*s^4) + 
       (s^19*(-30 - 538*s^2 - 839*s^4 + 1892*s^6))/b^19 + 
       b^19*s^19*(-30 - 538*s^2 - 839*s^4 + 1892*s^6) + 
       (s^17*(-15 - 53*s^2 - 798*s^4 - 876*s^6 + 2415*s^8))/b^17 + 
       b^17*s^17*(-15 - 53*s^2 - 798*s^4 - 876*s^6 + 2415*s^8) + 
       (s^15*(157 - 11*s^2 - 112*s^4 - 966*s^6 - 1061*s^8 + 2558*s^10))/
        b^15 + b^15*s^15*(157 - 11*s^2 - 112*s^4 - 966*s^6 - 1061*s^8 + 
         2558*s^10) + (s^15*(118 - 25*s^2 - 137*s^4 - 1206*s^6 - 1014*s^8 + 
          3077*s^10))/b^13 + b^13*s^15*(118 - 25*s^2 - 137*s^4 - 1206*s^6 - 
         1014*s^8 + 3077*s^10) + (s^11*(55 + 3*s^2 + 177*s^4 - 32*s^6 - 
          218*s^8 - 1315*s^10 - 1188*s^12 + 3174*s^14))/b^11 + 
       b^11*s^11*(55 + 3*s^2 + 177*s^4 - 32*s^6 - 218*s^8 - 1315*s^10 - 
         1188*s^12 + 3174*s^14) + (s^11*(41 + 6*s^2 + 199*s^4 - 40*s^6 - 
          273*s^8 - 1518*s^10 - 1132*s^12 + 3535*s^14))/b^9 + 
       b^9*s^11*(41 + 6*s^2 + 199*s^4 - 40*s^6 - 273*s^8 - 1518*s^10 - 
         1132*s^12 + 3535*s^14) + (s^11*(60 + 8*s^2 + 241*s^4 - 44*s^6 - 
          350*s^8 - 1552*s^10 - 1256*s^12 + 3676*s^14))/b^7 + 
       b^7*s^11*(60 + 8*s^2 + 241*s^4 - 44*s^6 - 350*s^8 - 1552*s^10 - 
         1256*s^12 + 3676*s^14) + (s^11*(65 + 14*s^2 + 253*s^4 - 60*s^6 - 
          404*s^8 - 1644*s^10 - 1258*s^12 + 3881*s^14))/b^5 + 
       b^5*s^11*(65 + 14*s^2 + 253*s^4 - 60*s^6 - 404*s^8 - 1644*s^10 - 
         1258*s^12 + 3881*s^14) + (s^11*(74 + 17*s^2 + 284*s^4 - 68*s^6 - 
          443*s^8 - 1694*s^10 - 1300*s^12 + 3918*s^14))/b^3 + 
       b^3*s^11*(74 + 17*s^2 + 284*s^4 - 68*s^6 - 443*s^8 - 1694*s^10 - 
         1300*s^12 + 3918*s^14) + (s*(-1 + 76*s^10 + 18*s^12 + 291*s^14 - 
          92*s^16 - 440*s^18 - 1714*s^20 - 1306*s^22 + 4032*s^24))/b + 
       b*s*(-1 + 76*s^10 + 18*s^12 + 291*s^14 - 92*s^16 - 440*s^18 - 
         1714*s^20 - 1306*s^22 + 4032*s^24), (1761*s^26)/b^26 + 
       1761*b^26*s^26 + (s^24*(-1076 + 1291*s^2))/b^24 + 
       b^24*s^24*(-1076 + 1291*s^2) + (5*s^22*(-161 - 134*s^2 + 399*s^4))/
        b^22 + 5*b^22*s^22*(-161 - 134*s^2 + 399*s^4) + 
       (s^20*(-42 - 665*s^2 - 1001*s^4 + 2269*s^6))/b^20 + 
       b^20*s^20*(-42 - 665*s^2 - 1001*s^4 + 2269*s^6) + 
       (s^18*(-22 - 72*s^2 - 987*s^4 - 1026*s^6 + 2921*s^8))/b^18 + 
       b^18*s^18*(-22 - 72*s^2 - 987*s^4 - 1026*s^6 + 2921*s^8) + 
       (s^16*(201 - 15*s^2 - 155*s^4 - 1188*s^6 - 1262*s^8 + 3072*s^10))/
        b^16 + b^16*s^16*(201 - 15*s^2 - 155*s^4 - 1188*s^6 - 1262*s^8 + 
         3072*s^10) + (s^16*(150 - 38*s^2 - 191*s^4 - 1494*s^6 - 1173*s^8 + 
          3746*s^10))/b^14 + b^14*s^16*(150 - 38*s^2 - 191*s^4 - 1494*s^6 - 
         1173*s^8 + 3746*s^10) + (s^12*(75 + 5*s^2 + 229*s^4 - 49*s^6 - 
          306*s^8 - 1608*s^10 - 1422*s^12 + 3816*s^14))/b^12 + 
       b^12*s^12*(75 + 5*s^2 + 229*s^4 - 49*s^6 - 306*s^8 - 1608*s^10 - 
         1422*s^12 + 3816*s^14) + (s^10*(1 + 54*s^2 + 9*s^4 + 251*s^6 - 
          62*s^8 - 382*s^10 - 1872*s^12 - 1309*s^14 + 4343*s^16))/b^10 + 
       b^10*s^10*(1 + 54*s^2 + 9*s^4 + 251*s^6 - 62*s^8 - 382*s^10 - 
         1872*s^12 - 1309*s^14 + 4343*s^16) + 
       (s^10*(1 + 82*s^2 + 15*s^4 + 319*s^6 - 71*s^8 - 499*s^10 - 1894*s^12 - 
          1510*s^14 + 4444*s^16))/b^8 + b^8*s^10*(1 + 82*s^2 + 15*s^4 + 
         319*s^6 - 71*s^8 - 499*s^10 - 1894*s^12 - 1510*s^14 + 4444*s^16) + 
       (s^10*(1 + 108*s^2 + 27*s^4 + 381*s^6 - 116*s^8 - 634*s^10 - 
          2065*s^12 - 1585*s^14 + 4786*s^16))/b^4 + 
       b^4*s^10*(1 + 108*s^2 + 27*s^4 + 381*s^6 - 116*s^8 - 634*s^10 - 
         2065*s^12 - 1585*s^14 + 4786*s^16) + 
       (s^10*(1 + 89*s^2 + 18*s^4 + 323*s^6 - 102*s^8 - 563*s^10 - 
          2036*s^12 - 1469*s^14 + 4803*s^16))/b^6 + 
       b^6*s^10*(1 + 89*s^2 + 18*s^4 + 323*s^6 - 102*s^8 - 563*s^10 - 
         2036*s^12 - 1469*s^14 + 4803*s^16) + 
       s^2*(-1 + s^8 + 118*s^10 + 36*s^12 + 402*s^14 - 156*s^16 - 653*s^18 - 
         2110*s^20 - 1650*s^22 + 4911*s^24) + 
       (s^2*(-2 + s^8 + 102*s^10 + 35*s^12 + 366*s^14 - 148*s^16 - 624*s^18 - 
          2170*s^20 - 1493*s^22 + 5067*s^24))/b^2 + 
       b^2*s^2*(-2 + s^8 + 102*s^10 + 35*s^12 + 366*s^14 - 148*s^16 - 
         624*s^18 - 2170*s^20 - 1493*s^22 + 5067*s^24), 
      (2112*s^27)/b^27 + 2112*b^27*s^27 + (s^25*(-1291 + 1549*s^2))/b^25 + 
       b^25*s^25*(-1291 + 1549*s^2) + (s^23*(-981 - 796*s^2 + 2381*s^4))/
        b^23 + b^23*s^23*(-981 - 796*s^2 + 2381*s^4) + 
       (s^21*(-55 - 816*s^2 - 1177*s^4 + 2728*s^6))/b^21 + 
       b^21*s^21*(-55 - 816*s^2 - 1177*s^4 + 2728*s^6) + 
       (s^19*(-30 - 97*s^2 - 1204*s^4 - 1210*s^6 + 3487*s^8))/b^19 + 
       b^19*s^19*(-30 - 97*s^2 - 1204*s^4 - 1210*s^6 + 3487*s^8) + 
       (s^17*(252 - 23*s^2 - 208*s^4 - 1460*s^6 - 1469*s^8 + 3698*s^10))/
        b^17 + b^17*s^17*(252 - 23*s^2 - 208*s^4 - 1460*s^6 - 1469*s^8 + 
         3698*s^10) + (s^17*(190 - 54*s^2 - 257*s^4 - 1813*s^6 - 1381*s^8 + 
          4484*s^10))/b^15 + b^15*s^17*(190 - 54*s^2 - 257*s^4 - 1813*s^6 - 
         1381*s^8 + 4484*s^10) + (s^13*(97 + 7*s^2 + 289*s^4 - 73*s^6 - 
          415*s^8 - 1969*s^10 - 1645*s^12 + 4628*s^14))/b^13 + 
       b^13*s^13*(97 + 7*s^2 + 289*s^4 - 73*s^6 - 415*s^8 - 1969*s^10 - 
         1645*s^12 + 4628*s^14) + (s^11*(1 + 73*s^2 + 14*s^4 + 322*s^6 - 
          95*s^8 - 523*s^10 - 2259*s^12 - 1559*s^14 + 5206*s^16))/b^11 + 
       b^11*s^11*(1 + 73*s^2 + 14*s^4 + 322*s^6 - 95*s^8 - 523*s^10 - 
         2259*s^12 - 1559*s^14 + 5206*s^16) + 
       (s^11*(2 + 108*s^2 + 22*s^4 + 398*s^6 - 112*s^8 - 675*s^10 - 
          2311*s^12 - 1747*s^14 + 5442*s^16))/b^9 + 
       b^9*s^11*(2 + 108*s^2 + 22*s^4 + 398*s^6 - 112*s^8 - 675*s^10 - 
         2311*s^12 - 1747*s^14 + 5442*s^16) + 
       (s^11*(3 + 120*s^2 + 31*s^4 + 425*s^6 - 161*s^8 - 775*s^10 - 
          2467*s^12 - 1758*s^14 + 5788*s^16))/b^7 + 
       b^7*s^11*(3 + 120*s^2 + 31*s^4 + 425*s^6 - 161*s^8 - 775*s^10 - 
         2467*s^12 - 1758*s^14 + 5788*s^16) + 
       (s^11*(3 + 147*s^2 + 38*s^4 + 482*s^6 - 193*s^8 - 854*s^10 - 
          2542*s^12 - 1846*s^14 + 5904*s^16))/b^5 + 
       b^5*s^11*(3 + 147*s^2 + 38*s^4 + 482*s^6 - 193*s^8 - 854*s^10 - 
         2542*s^12 - 1846*s^14 + 5904*s^16) + 
       (s^3*(-2 + 3*s^8 + 158*s^10 + 63*s^12 + 499*s^14 - 244*s^16 - 
          904*s^18 - 2651*s^20 - 1883*s^22 + 6152*s^24))/b + 
       b*s^3*(-2 + 3*s^8 + 158*s^10 + 63*s^12 + 499*s^14 - 244*s^16 - 
         904*s^18 - 2651*s^20 - 1883*s^22 + 6152*s^24) + 
       (s^3*(-3 + 3*s^8 + 148*s^10 + 52*s^12 + 489*s^14 - 236*s^16 - 
          870*s^18 - 2623*s^20 - 1814*s^22 + 6173*s^24))/b^3 + 
       b^3*s^3*(-3 + 3*s^8 + 148*s^10 + 52*s^12 + 489*s^14 - 236*s^16 - 
         870*s^18 - 2623*s^20 - 1814*s^22 + 6173*s^24), 
      (2534*s^28)/b^28 + 2534*b^28*s^28 + (s^26*(-1549 + 1845*s^2))/b^26 + 
       b^26*s^26*(-1549 + 1845*s^2) + (s^24*(-1199 - 933*s^2 + 2846*s^4))/
        b^24 + b^24*s^24*(-1199 - 933*s^2 + 2846*s^4) + 
       (s^22*(-75 - 995*s^2 - 1390*s^4 + 3241*s^6))/b^22 + 
       b^22*s^22*(-75 - 995*s^2 - 1390*s^4 + 3241*s^6) + 
       (s^20*(-42 - 130*s^2 - 1464*s^4 - 1402*s^6 + 4179*s^8))/b^20 + 
       b^20*s^20*(-42 - 130*s^2 - 1464*s^4 - 1402*s^6 + 4179*s^8) + 
       (s^18*(318 - 32*s^2 - 279*s^4 - 1771*s^6 - 1723*s^8 + 4396*s^10))/
        b^18 + b^18*s^18*(318 - 32*s^2 - 279*s^4 - 1771*s^6 - 1723*s^8 + 
         4396*s^10) + (s^18*(237 - 80*s^2 - 345*s^4 - 2205*s^6 - 1587*s^8 + 
          5385*s^10))/b^16 + b^16*s^18*(237 - 80*s^2 - 345*s^4 - 2205*s^6 - 
         1587*s^8 + 5385*s^10) + (s^14*(128 + 11*s^2 + 365*s^4 - 108*s^6 - 
          559*s^8 - 2366*s^10 - 1940*s^12 + 5520*s^14))/b^14 + 
       b^14*s^14*(128 + 11*s^2 + 365*s^4 - 108*s^6 - 559*s^8 - 2366*s^10 - 
         1940*s^12 + 5520*s^14) + (s^12*(2 + 94*s^2 + 20*s^4 + 402*s^6 - 
          144*s^8 - 699*s^10 - 2735*s^12 - 1785*s^14 + 6301*s^16))/b^12 + 
       b^12*s^12*(2 + 94*s^2 + 20*s^4 + 402*s^6 - 144*s^8 - 699*s^10 - 
         2735*s^12 - 1785*s^14 + 6301*s^16) + 
       (s^12*(5 + 158*s^2 + 46*s^4 + 527*s^6 - 256*s^8 - 1019*s^10 - 
          2990*s^12 - 2017*s^14 + 7072*s^16))/b^8 + 
       b^8*s^12*(5 + 158*s^2 + 46*s^4 + 527*s^6 - 256*s^8 - 1019*s^10 - 
         2990*s^12 - 2017*s^14 + 7072*s^16) + 
       (s^12*(8 + 198*s^2 + 61*s^4 + 630*s^6 - 303*s^8 - 1150*s^10 - 
          3068*s^12 - 2205*s^14 + 7093*s^16))/b^6 + 
       b^6*s^12*(8 + 198*s^2 + 61*s^4 + 630*s^6 - 303*s^8 - 1150*s^10 - 
         3068*s^12 - 2205*s^14 + 7093*s^16) + 
       (s^10*(1 + 3*s^2 + 146*s^4 + 34*s^6 + 509*s^8 - 176*s^10 - 908*s^12 - 
          2764*s^14 - 2082*s^16 + 6504*s^18))/b^10 + 
       b^10*s^10*(1 + 3*s^2 + 146*s^4 + 34*s^6 + 509*s^8 - 176*s^10 - 
         908*s^12 - 2764*s^14 - 2082*s^16 + 6504*s^18) + 
       (s^4*(-3 + 8*s^8 + 231*s^10 + 90*s^12 + 660*s^14 - 384*s^16 - 
          1244*s^18 - 3186*s^20 - 2288*s^22 + 7473*s^24))/b^2 + 
       b^2*s^4*(-3 + 8*s^8 + 231*s^10 + 90*s^12 + 660*s^14 - 384*s^16 - 
         1244*s^18 - 3186*s^20 - 2288*s^22 + 7473*s^24) + 
       (s^4*(-5 + 8*s^8 + 200*s^10 + 75*s^12 + 610*s^14 - 380*s^16 - 
          1152*s^18 - 3204*s^20 - 2097*s^22 + 7600*s^24))/b^4 + 
       b^4*s^4*(-5 + 8*s^8 + 200*s^10 + 75*s^12 + 610*s^14 - 380*s^16 - 
         1152*s^18 - 3204*s^20 - 2097*s^22 + 7600*s^24) + 
       s^4*(-4 + 8*s^8 + 211*s^10 + 103*s^12 + 613*s^14 - 391*s^16 - 
         1225*s^18 - 3312*s^20 - 2127*s^22 + 7690*s^24), 
      (3015*s^29)/b^29 + 3015*b^29*s^29 + (s^27*(-1845 + 2194*s^2))/b^27 + 
       b^27*s^27*(-1845 + 2194*s^2) + (4*s^25*(-362 - 274*s^2 + 843*s^4))/
        b^25 + 4*b^25*s^25*(-362 - 274*s^2 + 843*s^4) + 
       (s^23*(-97 - 1210*s^2 - 1618*s^4 + 3855*s^6))/b^23 + 
       b^23*s^23*(-97 - 1210*s^2 - 1618*s^4 + 3855*s^6) + 
       (s^21*(-55 - 172*s^2 - 1764*s^4 - 1638*s^6 + 4943*s^8))/b^21 + 
       b^21*s^21*(-55 - 172*s^2 - 1764*s^4 - 1638*s^6 + 4943*s^8) + 
       (2*s^19*(148 - 54*s^2 - 228*s^4 - 1320*s^6 - 922*s^8 + 3191*s^10))/
        b^17 + 2*b^17*s^19*(148 - 54*s^2 - 228*s^4 - 1320*s^6 - 922*s^8 + 
         3191*s^10) + (s^19*(393 - 44*s^2 - 370*s^4 - 2141*s^6 - 1986*s^8 + 
          5245*s^10))/b^19 + b^19*s^19*(393 - 44*s^2 - 370*s^4 - 2141*s^6 - 
         1986*s^8 + 5245*s^10) + (s^15*(164 + 15*s^2 + 452*s^4 - 153*s^6 - 
          739*s^8 - 2846*s^10 - 2234*s^12 + 6605*s^14))/b^15 + 
       b^15*s^15*(164 + 15*s^2 + 452*s^4 - 153*s^6 - 739*s^8 - 2846*s^10 - 
         2234*s^12 + 6605*s^14) + (s^13*(3 + 123*s^2 + 30*s^4 + 503*s^6 - 
          207*s^8 - 926*s^10 - 3249*s^12 - 2095*s^14 + 7495*s^16))/b^13 + 
       b^13*s^13*(3 + 123*s^2 + 30*s^4 + 503*s^6 - 207*s^8 - 926*s^10 - 
         3249*s^12 - 2095*s^14 + 7495*s^16) + 
       (s^11*(1 + 5*s^2 + 188*s^4 + 48*s^6 + 629*s^8 - 261*s^10 - 1186*s^12 - 
          3320*s^14 - 2386*s^16 + 7848*s^18))/b^11 + 
       b^11*s^11*(1 + 5*s^2 + 188*s^4 + 48*s^6 + 629*s^8 - 261*s^10 - 
         1186*s^12 - 3320*s^14 - 2386*s^16 + 7848*s^18) + 
       (s^11*(1 + 8*s^2 + 212*s^4 + 67*s^6 + 670*s^8 - 384*s^10 - 1335*s^12 - 
          3554*s^14 - 2395*s^16 + 8427*s^18))/b^9 + 
       b^9*s^11*(1 + 8*s^2 + 212*s^4 + 67*s^6 + 670*s^8 - 384*s^10 - 
         1335*s^12 - 3554*s^14 - 2395*s^16 + 8427*s^18) + 
       (s^11*(1 + 12*s^2 + 260*s^4 + 88*s^6 + 773*s^8 - 464*s^10 - 
          1476*s^12 - 3701*s^14 - 2524*s^16 + 8642*s^18))/b^7 + 
       b^7*s^11*(1 + 12*s^2 + 260*s^4 + 88*s^6 + 773*s^8 - 464*s^10 - 
         1476*s^12 - 3701*s^14 - 2524*s^16 + 8642*s^18) + 
       (s^5*(-7 + 17*s^8 + 268*s^10 + 114*s^12 + 788*s^14 - 562*s^16 - 
          1524*s^18 - 3843*s^20 - 2496*s^22 + 9107*s^24))/b^5 + 
       b^5*s^5*(-7 + 17*s^8 + 268*s^10 + 114*s^12 + 788*s^14 - 562*s^16 - 
         1524*s^18 - 3843*s^20 - 2496*s^22 + 9107*s^24) + 
       (s^5*(-5 + 17*s^8 + 309*s^10 + 129*s^12 + 810*s^14 - 595*s^16 - 
          1620*s^18 - 3869*s^20 - 2645*s^22 + 9173*s^24))/b^3 + 
       b^3*s^5*(-5 + 17*s^8 + 309*s^10 + 129*s^12 + 810*s^14 - 595*s^16 - 
         1620*s^18 - 3869*s^20 - 2645*s^22 + 9173*s^24) + 
       (s^5*(-6 + 18*s^8 + 309*s^10 + 140*s^12 + 807*s^14 - 603*s^16 - 
          1650*s^18 - 3959*s^20 - 2577*s^22 + 9317*s^24))/b + 
       b*s^5*(-6 + 18*s^8 + 309*s^10 + 140*s^12 + 807*s^14 - 603*s^16 - 
         1650*s^18 - 3959*s^20 - 2577*s^22 + 9317*s^24), 
      -1 - 9*s^6 + 36*s^14 + 456*s^16 + 184*s^18 + 1050*s^20 - 912*s^22 - 
       2188*s^24 - 4711*s^26 - 3121*s^28 + 11260*s^30 + (3590*s^30)/b^30 + 
       3590*b^30*s^30 + (2*s^28*(-1097 + 1296*s^2))/b^28 + 
       2*b^28*s^28*(-1097 + 1296*s^2) + (5*s^26*(-350 - 255*s^2 + 799*s^4))/
        b^26 + 5*b^26*s^26*(-350 - 255*s^2 + 799*s^4) + 
       (s^24*(-128 - 1459*s^2 - 1890*s^4 + 4547*s^6))/b^24 + 
       b^24*s^24*(-128 - 1459*s^2 - 1890*s^4 + 4547*s^6) + 
       (s^22*(-75 - 224*s^2 - 2122*s^4 - 1880*s^6 + 5861*s^8))/b^22 + 
       b^22*s^22*(-75 - 224*s^2 - 2122*s^4 - 1880*s^6 + 5861*s^8) + 
       (s^20*(487 - 59*s^2 - 483*s^4 - 2563*s^6 - 2310*s^8 + 6180*s^10))/
        b^20 + b^20*s^20*(487 - 59*s^2 - 483*s^4 - 2563*s^6 - 2310*s^8 + 
         6180*s^10) + (s^20*(362 - 148*s^2 - 598*s^4 - 3156*s^6 - 2099*s^8 + 
          7598*s^10))/b^18 + b^18*s^20*(362 - 148*s^2 - 598*s^4 - 3156*s^6 - 
         2099*s^8 + 7598*s^10) + (s^16*(212 + 22*s^2 + 559*s^4 - 210*s^6 - 
          968*s^8 - 3373*s^10 - 2601*s^12 + 7801*s^14))/b^16 + 
       b^16*s^16*(212 + 22*s^2 + 559*s^4 - 210*s^6 - 968*s^8 - 3373*s^10 - 
         2601*s^12 + 7801*s^14) + (s^14*(5 + 157*s^2 + 41*s^4 + 614*s^6 - 
          290*s^8 - 1201*s^10 - 3868*s^12 - 2391*s^14 + 8950*s^16))/b^14 + 
       b^14*s^14*(5 + 157*s^2 + 41*s^4 + 614*s^6 - 290*s^8 - 1201*s^10 - 
         3868*s^12 - 2391*s^14 + 8950*s^16) + 
       (s^12*(2 + 8*s^2 + 246*s^4 + 70*s^6 + 780*s^8 - 374*s^10 - 1537*s^12 - 
          3915*s^14 - 2802*s^16 + 9309*s^18))/b^12 + 
       b^12*s^12*(2 + 8*s^2 + 246*s^4 + 70*s^6 + 780*s^8 - 374*s^10 - 
         1537*s^12 - 3915*s^14 - 2802*s^16 + 9309*s^18) + 
       (s^12*(3 + 20*s^2 + 350*s^4 + 125*s^6 + 969*s^8 - 679*s^10 - 
          1903*s^12 - 4381*s^14 - 2994*s^16 + 10268*s^18))/b^8 + 
       b^8*s^12*(3 + 20*s^2 + 350*s^4 + 125*s^6 + 969*s^8 - 679*s^10 - 
         1903*s^12 - 4381*s^14 - 2994*s^16 + 10268*s^18) + 
       (s^10*(1 + s^2 + 13*s^4 + 272*s^6 + 94*s^8 + 818*s^10 - 558*s^12 - 
          1700*s^14 - 4247*s^16 - 2722*s^18 + 10147*s^20))/b^10 + 
       b^10*s^10*(1 + s^2 + 13*s^4 + 272*s^6 + 94*s^8 + 818*s^10 - 558*s^12 - 
         1700*s^14 - 4247*s^16 - 2722*s^18 + 10147*s^20) + 
       (s^6*(-7 + s^6 + 34*s^8 + 417*s^10 + 188*s^12 + 1026*s^14 - 862*s^16 - 
          2115*s^18 - 4620*s^20 - 3148*s^22 + 10961*s^24))/b^4 + 
       b^4*s^6*(-7 + s^6 + 34*s^8 + 417*s^10 + 188*s^12 + 1026*s^14 - 
         862*s^16 - 2115*s^18 - 4620*s^20 - 3148*s^22 + 10961*s^24) + 
       (s^6*(-11 + 2*s^6 + 25*s^8 + 351*s^10 + 162*s^12 + 948*s^14 - 
          828*s^16 - 1926*s^18 - 4605*s^20 - 2835*s^22 + 11076*s^24))/b^6 + 
       b^6*s^6*(-11 + 2*s^6 + 25*s^8 + 351*s^10 + 162*s^12 + 948*s^14 - 
         828*s^16 - 1926*s^18 - 4605*s^20 - 2835*s^22 + 11076*s^24) + 
       (s^6*(-10 + 36*s^8 + 413*s^10 + 196*s^12 + 974*s^14 - 922*s^16 - 
          2108*s^18 - 4783*s^20 - 2956*s^22 + 11414*s^24))/b^2 + 
       b^2*s^6*(-10 + 36*s^8 + 413*s^10 + 196*s^12 + 974*s^14 - 922*s^16 - 
         2108*s^18 - 4783*s^20 - 2956*s^22 + 11414*s^24)}, 0, 31, 1]