f = SeriesData[x, 0, {1, 2*s, -1 + 5*s^2, 2*s*(-1 + 5*s^2), 
      -1 - 5*s^2 + 20*s^4, 2*s*(-1 - 5*s^2 + 18*s^4), 
      5*s^2*(-1 - 4*s^2 + 13*s^4), 2*s^3*(-5 - 18*s^2 + 55*s^4), 
      5*s^4*(-4 - 13*s^2 + 37*s^4), 2*s^5*(-18 - 55*s^2 + 145*s^4), 
      1 - 65*s^6 - 176*s^8 + 452*s^10, 2*(s - 55*s^7 - 133*s^9 + 339*s^11), 
      s^2*(5 - 192*s^6 - 394*s^8 + 1005*s^10), 
      2*s^3*(5 - 154*s^6 - 280*s^8 + 723*s^10), 1 + 20*s^4 - 9*s^8 - 
       492*s^10 - 779*s^12 + 2059*s^14, 2*(s + 18*s^5 - 13*s^9 - 377*s^11 - 
        525*s^13 + 1432*s^15), s^2*(5 + 65*s^4 - 2*s^6 - 64*s^8 - 1137*s^10 - 
        1390*s^12 + 3945*s^14), 2*s^3*(5 + 55*s^4 - 3*s^6 - 67*s^8 - 
        826*s^10 - 899*s^12 + 2667*s^14), s^4*(20 + 183*s^4 - 20*s^6 - 
        264*s^8 - 2356*s^10 - 2303*s^12 + 7148*s^14), 
      2*s^5*(18 + 143*s^4 - 23*s^6 - 239*s^8 - 1621*s^10 - 1457*s^12 + 
        4719*s^14), s^6*(65 + 7*s^2 + 440*s^4 - 104*s^6 - 833*s^8 - 
        4347*s^10 - 3641*s^12 + 12363*s^14), 
      2*s^7*(55 + 10*s^2 + 325*s^4 - 106*s^6 - 691*s^8 - 2854*s^10 - 
        2249*s^12 + 7996*s^14), s^8*(185 + 48*s^2 + 945*s^4 - 418*s^6 - 
        2177*s^8 - 7387*s^10 - 5511*s^12 + 20539*s^14), 
      2*s^9*(146 + 48*s^2 + 665*s^4 - 387*s^6 - 1609*s^8 - 4693*s^10 - 
        3343*s^12 + 13053*s^14), -1 + 9*s^8 + 460*s^10 + 178*s^12 + 
       1833*s^14 - 1420*s^16 - 4613*s^18 - 11791*s^20 - 8057*s^22 + 
       32966*s^24, 2*s*(-1 + 12*s^8 + 350*s^10 + 153*s^12 + 1228*s^14 - 
        1190*s^16 - 3185*s^18 - 7308*s^20 - 4817*s^22 + 20629*s^24), 
      s^2*(-5 + 2*s^6 + 60*s^8 + 1057*s^10 + 499*s^12 + 3168*s^14 - 
        3818*s^16 - 8563*s^18 - 17947*s^20 - 11446*s^22 + 51337*s^24), 
      2*s^3*(-5 + 3*s^6 + 62*s^8 + 778*s^10 + 382*s^12 + 1965*s^14 - 
        2909*s^16 - 5605*s^18 - 10916*s^20 - 6756*s^22 + 31693*s^24), 
      s^4*(-20 + 2*s^4 + 18*s^6 + 242*s^8 + 2283*s^10 + 1088*s^12 + 
        4670*s^14 - 8540*s^16 - 14404*s^18 - 26356*s^20 - 15868*s^22 + 
        77853*s^24), 2*s^5*(-18 + 2*s^4 + 22*s^6 + 215*s^8 + 1647*s^10 + 
        727*s^12 + 2644*s^14 - 5999*s^16 - 9087*s^18 - 15777*s^20 - 
        9263*s^22 + 47489*s^24), -1 - 65*s^6 + 2*s^8 + 12*s^10 + 100*s^12 + 
       739*s^14 + 4717*s^16 + 1793*s^18 + 5600*s^20 - 16349*s^22 - 
       22686*s^24 - 37534*s^26 - 21532*s^28 + 115316*s^30, 
      2*s*(-1 - 55*s^6 + 2*s^8 + 13*s^10 + 102*s^12 + 600*s^14 + 3296*s^16 + 
        1011*s^18 + 2733*s^20 - 10762*s^22 - 13987*s^24 - 22170*s^26 - 
        12453*s^28 + 69591*s^30), s^2*(-5 - 183*s^6 + 10*s^8 + 58*s^10 + 
        402*s^12 + 1918*s^14 + 9063*s^16 + 1954*s^18 + 4695*s^20 - 
        27731*s^22 - 34126*s^24 - 52082*s^26 - 28685*s^28 + 167260*s^30), 
      2*s^3*(-5 - 143*s^6 + 11*s^8 + 57*s^10 + 373*s^12 + 1476*s^14 + 
        6078*s^16 + 668*s^18 + 1627*s^20 - 17589*s^22 - 20618*s^24 - 
        30416*s^26 - 16450*s^28 + 99970*s^30), 
      s^4*(-20 - 7*s^4 - 442*s^6 + 46*s^8 + 222*s^10 + 1353*s^12 + 
        4460*s^14 + 15991*s^16 - 232*s^18 + 1246*s^20 - 44033*s^22 - 
        49444*s^24 - 70711*s^26 - 37601*s^28 + 238060*s^30), 
      2*s^5*(-18 - 10*s^4 - 329*s^6 + 44*s^8 + 200*s^10 + 1139*s^12 + 
        3258*s^14 + 10254*s^16 - 1558*s^18 - 659*s^20 - 27171*s^22 - 
        29397*s^24 - 40885*s^26 - 21402*s^28 + 141058*s^30)}, 0, 36, 1]