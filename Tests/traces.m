traces := AssociativeArray();



levels := [1..5];
weights := [2..12 by 2];
heckes := [1..5];
Discs := [d : d in [1..100] | IsFundamentalDiscriminant(d) ];

/*
// Generate tests
load "config.m";
for d in Discs do
    
    // initialize
    F := QuadraticField(d);
    ZF := Integers(F);
    Z := Integers();

    // precompute
    M := GradedRingOfHMFs(F,1);
    HMFTracePrecomputation(M, [i*ZF : i in heckes] );

    // Hecke Character group
    // H := HeckeCharacterGroup(1*ZF,[1,2]);
    // f := H.1;

    // Generate traces
    traces[d] := [[ Z ! Trace( HMFSpace(M, n*ZF, [k,k]), m*ZF : precomp := true) : m in heckes] : k in weights, n in levels];
end for;

// printing 
d := 60;
print Sprintf("traces[%o] := %o;\n", d, traces[d]);
*/


traces[5] := [
[ 0, 0, 0, 0, 0 ],
[ 0, 0, 0, 0, 0 ],
[ 1, 20, 90, -624, 4975 ],
[ 1, 140, 3330, 3216, -55625 ],
[ 2, 340, 45180, 989712, 2568350 ],
[ 3, 540, 76230, 11593488, 231309525 ],
[ 0, 0, 0, 0, 0 ],
[ 1, -4, 50, 16, -25 ],
[ 3, 4, 470, -1392, 18925 ],
[ 5, 76, 3410, -880, 97075 ],
[ 7, 84, 78710, 662032, 7445625 ],
[ 11, -484, 359750, 4253456, 335173325 ],
[ 0, 0, 0, 0, 0 ],
[ 2, 7, -18, 81, 506 ],
[ 5, 55, 9, 993, 7811 ],
[ 9, 255, 2601, 71985, 311391 ],
[ 14, 1063, 32058, 1809537, 8629646 ],
[ 21, 3855, 17181, 38440401, 383330451 ],
[ 0, 0, 0, 0, 0 ],
[ 3, -4, 78, 16, 21 ],
[ 9, 4, 570, -1392, 23591 ],
[ 17, 76, 3690, -880, 403911 ],
[ 27, 84, 83742, 662032, 15895781 ],
[ 41, -484, 495930, 4253456, 556205951 ],
[ 0, 0, 0, 0, 0 ],
[ 5, 0, -50, 130, 25 ],
[ 13, -20, -290, 5138, 2475 ],
[ 25, 60, 5770, 120850, -86875 ],
[ 41, -100, 30550, 3721746, 615225 ],
[ 61, -2500, -44750, 73913106, 153184525 ]
];


traces[8] := [
[ 0, 0, 0, 0, 0 ],
[ 1, -4, 26, -16, 138 ],
[ 2, 84, 404, -624, 7028 ],
[ 3, 500, 5102, 99344, 214718 ],
[ 4, 1620, 59048, 1015056, 6600808 ],
[ 6, 9204, 358748, 26608656, 149061948 ],
[ 0, 0, 0, 0, 0 ],
[ 3, -12, 78, 16, 414 ],
[ 7, 20, 870, -3312, 17750 ],
[ 13, 180, 6450, 39440, 299234 ],
[ 21, 340, 63762, 382224, 10986210 ],
[ 31, 1012, 605670, 11953168, 152734454 ],
[ 1, 2, -1, -4, 6 ],
[ 5, 32, -1, 344, 598 ],
[ 12, 244, 242, 6088, 17236 ],
[ 22, 1796, 3644, 185864, 380328 ],
[ 35, 10628, 39365, 3424712, 9598786 ],
[ 52, 58436, 240650, 81707912, 257273508 ],
[ 0, 0, 0, 0, 0 ],
[ 9, -12, 42, 16, 90 ],
[ 25, 20, 1050, -3312, 14186 ],
[ 49, 180, 3930, 39440, 349130 ],
[ 81, 340, 58218, 382224, 7452666 ],
[ 121, 1012, 651210, 11953168, 44456570 ],
[ 2, 4, 4, 16, -2 ],
[ 11, 56, 82, 328, 63 ],
[ 29, 532, 1042, 6744, 5153 ],
[ 55, 3972, 6790, 322456, 167843 ],
[ 89, 24452, 94222, 7671384, 5428933 ],
[ 133, 142404, 765106, 175642392, 119765073 ]
];



traces[12] := [
[ 0, 0, 0, 0, 0 ],
[ 2, 8, 42, -160, 340 ],
[ 4, 136, 948, 6688, 11816 ],
[ 6, 792, 14238, 87072, 442620 ],
[ 8, 3752, 143592, 2085920, 14253136 ],
[ 12, 19512, 1647804, 51447072, 269062200 ],
[ 0, 0, 0, 0, 0 ],
[ 6, -8, 126, -224, 1020 ],
[ 14, 8, 2646, 2336, 28780 ],
[ 26, 152, 34434, -6112, 839620 ],
[ 42, 1192, 407394, 558112, 14215620 ],
[ 62, 3128, 4436694, 19875104, 603579820 ],
[ 1, -2, 0, 4, 8 ],
[ 10, 52, -12, 136, 986 ],
[ 27, 612, 138, 15336, 15372 ],
[ 51, 3588, 5490, 273768, 573276 ],
[ 82, 22948, 64860, 7976296, 29525882 ],
[ 123, 133188, 584922, 174893928, 440915916 ],
[ 1, 0, -3, 0, 10 ],
[ 19, -8, 223, -224, 878 ],
[ 51, 8, 4855, 2336, 39038 ],
[ 99, 152, 88543, -6112, 895598 ],
[ 163, 1192, 1176343, 558112, 16912958 ],
[ 243, 3128, 14593567, 19875104, 574267118 ],
[ 4, 6, 8, -2, -4 ],
[ 22, 110, 346, 754, 190 ],
[ 58, 1110, 6502, 24322, 8066 ],
[ 110, 7750, 97690, 648674, 348870 ],
[ 178, 48470, 1312438, 13874050, 11909386 ],
[ 266, 283750, 17166406, 326419490, 210468450 ]
];



traces[13] := [
[ 0, 0, 0, 0, 0 ],
[ 1, 7, 1, -15, 169 ],
[ 3, 31, 1162, 2817, 10732 ],
[ 5, -49, -1928, 79665, 208574 ],
[ 7, 1055, 46489, 50913, 6596777 ],
[ 11, 1519, 718912, 16132113, 12953254 ],
[ 1, -1, 1, 1, 1 ],
[ 4, -1, 115, -47, 549 ],
[ 12, -1, 697, 1281, 14103 ],
[ 22, -177, 5113, 46897, 282699 ],
[ 34, 543, 123235, -473375, 10363473 ],
[ 52, -529, 1083793, 1452049, 137943999 ],
[ 1, 1, 1, -3, 10 ],
[ 12, 24, -23, 30, 720 ],
[ 34, 96, 856, 10446, 26820 ],
[ 66, 384, -1982, 330174, 350820 ],
[ 108, 1536, 54913, 6679854, 18922320 ],
[ 162, 6144, 578458, 175872798, 175418820 ],
[ 2, -1, 2, 1, 2 ],
[ 15, -1, 148, -47, 394 ],
[ 43, -1, 658, 1281, 12748 ],
[ 83, -177, 7522, 46897, 326044 ],
[ 135, 543, 133492, -473375, 8791018 ],
[ 203, -529, 1112482, 1452049, 87555244 ],
[ 3, 1, 12, 7, -3 ],
[ 20, 18, 94, 258, 69 ],
[ 56, 66, 1348, 17986, 8232 ],
[ 108, 354, 2812, 542434, 146074 ],
[ 176, 1602, 69886, 11328642, 5034277 ],
[ 264, 5154, 1336012, 294822178, -26109246 ]
];



traces[17] := [
[ 0, 0, 0, 0, 0 ],
[ 2, 17, 34, 17, 20 ],
[ 5, -35, 682, 8937, 8514 ],
[ 9, 389, -1622, 112169, 352090 ],
[ 14, 1413, 34882, 97737, 2127484 ],
[ 21, 10389, 221002, 54144489, 62095410 ],
[ 1, 1, -2, 1, 2 ],
[ 14, 5, 56, 233, 196 ],
[ 38, 5, 728, 905, 11956 ],
[ 74, 245, 4712, 43433, 515116 ],
[ 122, 1445, 50024, 387017, 5440876 ],
[ 182, 2645, 492632, 23610857, 105005236 ],
[ 2, 5, -2, 5, 11 ],
[ 16, 26, -2, 230, 264 ],
[ 43, 74, 439, 20710, 15093 ],
[ 83, 746, -3809, 491366, 535229 ],
[ 136, 3914, 8638, 9237734, 7723608 ],
[ 203, 9386, 43855, 262681190, 185813069 ],
[ 5, 1, -4, 1, 10 ],
[ 54, 5, 54, 233, 36 ],
[ 150, 5, 486, 905, 12996 ],
[ 294, 245, 4374, 43433, 695556 ],
[ 486, 1445, 39366, 387017, 4639716 ],
[ 726, 2645, 354294, 23610857, 62821476 ],
[ 5, 5, 2, -3, -1 ],
[ 40, 26, 84, 1126, -30 ],
[ 110, 74, 972, 34278, 7264 ],
[ 214, 746, 5388, 1035110, 320840 ],
[ 352, 3914, 84756, 24016102, 1346234 ],
[ 526, 9386, 758988, 605909606, 42564160 ]
];



traces[21] := [
[ 0, 0, 0, 0, 0 ],
[ 3, 14, 123, 66, 204 ],
[ 6, 94, 966, 5442, 22656 ],
[ 10, 430, 12186, 68418, 489504 ],
[ 15, 2750, 188871, 1187394, 15097236 ],
[ 22, 6478, 2183070, 43362882, 330957144 ],
[ 2, -2, 6, 2, 12 ],
[ 10, -2, 294, -62, 1068 ],
[ 24, 30, 3108, 2370, 37812 ],
[ 44, 174, 48456, 2882, 895188 ],
[ 70, 1726, 601314, -123326, 26073132 ],
[ 104, 2382, 8194548, 14002754, 522445908 ],
[ 2, 0, 0, 6, 0 ],
[ 18, 28, 42, 486, 408 ],
[ 52, 196, -6, 18822, 27576 ],
[ 100, 388, 522, 502086, 1050408 ],
[ 162, 2980, 51090, 11096838, 21848376 ],
[ 244, 8260, 529698, 302361798, 353713608 ],
[ 5, -2, 9, 2, 24 ],
[ 33, -2, 517, -62, 1080 ],
[ 87, 30, 8131, 2370, 41856 ],
[ 167, 174, 139243, 2882, 1096800 ],
[ 273, 1726, 1935661, -123326, 30162456 ],
[ 407, 2382, 26066155, 14002754, 442057920 ],
[ 6, 4, 16, 12, 6 ],
[ 56, 50, 704, 1046, 164 ],
[ 152, 242, 13034, 46326, 15656 ],
[ 296, 770, 229034, 1261782, 386504 ],
[ 488, 3794, 3385712, 32540342, 10917236 ],
[ 728, 13346, 45274538, 772511382, 315557144 ]
];




traces[24] := [
[ 1, -2, 1, 4, 0 ],
[ 5, 44, 133, 200, 648 ],
[ 9, 276, 2185, 8616, 31248 ],
[ 15, 1380, 25855, 227304, 655128 ],
[ 23, 8468, 248983, 4749224, 25582368 ],
[ 33, 41028, 3165721, 57849960, 457610928 ],
[ 3, -4, 3, 8, 0 ],
[ 17, 4, 353, -152, 1560 ],
[ 41, 52, 5345, 808, 43128 ],
[ 77, 100, 72509, 91624, 1135080 ],
[ 125, 1300, 975125, 1593256, 26145768 ],
[ 185, 2116, 12361481, 3184744, 618737400 ],
[ 5, 2, -2, 20, 12 ],
[ 30, 144, 16, 1008, 876 ],
[ 79, 1408, 808, 30640, 45012 ],
[ 151, 10240, 9088, 854128, 570036 ],
[ 246, 64512, 45592, 18772272, 35640012 ],
[ 367, 385024, 744712, 438007792, 652204596 ],
[ 6, -4, 6, 8, 0 ],
[ 56, 4, 656, -152, 1224 ],
[ 152, 52, 14576, 808, 29448 ],
[ 296, 100, 228800, 91624, 1536264 ],
[ 488, 1300, 3349376, 1593256, 14184648 ],
[ 728, 2116, 44485808, 3184744, 560812104 ],
[ 12, 10, 28, 38, 8 ],
[ 86, 378, 1022, 1914, 478 ],
[ 230, 3858, 20366, 72682, 24898 ],
[ 446, 29058, 345782, 2169034, 568378 ],
[ 734, 190674, 5054774, 51876330, 21486118 ],
[ 1094, 1129506, 66806846, 1187043850, 304692178 ]
];



traces[28] := [
[ 1, -1, 0, -1, 10 ],
[ 5, 33, 160, 281, 514 ],
[ 11, 241, 1504, 9009, 27630 ],
[ 19, 1761, 16720, 172657, 353534 ],
[ 29, 9681, 152464, 3164881, 19759730 ],
[ 43, 51137, 1683856, 70629297, 411941454 ],
[ 3, -3, 0, 1, 30 ],
[ 21, 1, 96, 49, 1890 ],
[ 53, -15, 2400, 2833, 34258 ],
[ 101, 225, 17952, 4593, 1140130 ],
[ 165, 1489, 176928, -87855, 34885458 ],
[ 245, 1985, 1308768, 5746609, 749823970 ],
[ 8, 6, 4, 2, 52 ],
[ 52, 240, 112, 1432, 1292 ],
[ 138, 2368, 982, 48984, 51624 ],
[ 266, 17664, 15478, 1227224, 1053352 ],
[ 436, 113664, 112288, 32154712, 37847084 ],
[ 650, 675840, 1031158, 721131224, 858545512 ],
[ 11, -3, -24, 1, 54 ],
[ 77, 1, 72, 49, 2138 ],
[ 205, -15, 648, 2833, 46282 ],
[ 397, 225, 5832, 4593, 1376698 ],
[ 653, 1489, 52488, -87855, 41972522 ],
[ 973, 1985, 472392, 5746609, 1017804058 ],
[ 12, 20, 14, 28, 0 ],
[ 82, 354, 328, 1866, 214 ],
[ 222, 3682, 2686, 70010, 20130 ],
[ 430, 28610, 29614, 1965690, 166034 ],
[ 706, 185250, 289192, 51099066, 15072230 ],
[ 1054, 1093506, 2488414, 1155278330, 294753954 ]
];



traces[29] := [
[ 1, -1, 1, -3, 9 ],
[ 3, 10, 101, 202, 387 ],
[ 8, 34, -103, 4106, 20867 ],
[ 14, 226, 3059, 79786, 95377 ],
[ 21, 1090, 53381, 1590858, 8690627 ],
[ 32, 3106, 681683, 42399210, 23918937 ],
[ 3, -2, 7, -6, 19 ],
[ 12, 2, 149, 106, 871 ],
[ 34, 2, 617, 522, 21451 ],
[ 64, 98, 6233, -2134, 375031 ],
[ 102, 578, 138821, 17994, 13892011 ],
[ 154, 1058, 1063553, 2553322, 301531891 ],
[ 4, 3, -1, 1, 30 ],
[ 24, 20, 47, 616, 974 ],
[ 65, 68, -346, 19528, 28614 ],
[ 125, 452, 872, 582664, 503274 ],
[ 204, 2180, 14015, 13908424, 18006734 ],
[ 305, 6212, 504536, 342664072, 326246394 ],
[ 6, -2, 12, -6, 30 ],
[ 45, 2, 202, 106, 606 ],
[ 127, 2, 982, 522, 22386 ],
[ 247, 98, 10438, -2134, 630066 ],
[ 405, 578, 172858, 17994, 12299646 ],
[ 607, 1058, 1348678, 2553322, 228490626 ],
[ 11, 1, 10, 7, 12 ],
[ 84, 24, 80, 1572, 467 ],
[ 228, 96, 20, 61540, 16767 ],
[ 444, 384, 3380, 1868452, -2623 ],
[ 732, 1536, 109520, 48875748, 6925627 ],
[ 1092, 6144, 1280180, 1161540388, 64593937 ]
];



traces[33] := [
[ 1, 0, -2, 4, -1 ],
[ 7, 2, 111, 1010, 262 ],
[ 15, 186, 1656, 8034, 17679 ],
[ 27, 522, 22812, 366882, 559047 ],
[ 43, 5930, 380955, 4300706, 3439534 ],
[ 63, 810, 5088636, 120337698, 250502907 ],
[ 6, 2, -6, 18, 12 ],
[ 44, 10, 472, 546, 1144 ],
[ 116, 106, 10528, 3746, 33448 ],
[ 224, 298, 169804, 191522, 1123984 ],
[ 368, 3178, 2488252, 1819554, 18750448 ],
[ 548, 5290, 33107920, 35743010, 480972424 ],
[ 9, -14, -3, 50, -11 ],
[ 58, 16, -6, 1944, -672 ],
[ 155, 64, -45, 58264, 27353 ],
[ 299, 256, -1245, 1635160, 555953 ],
[ 490, 1024, 59466, 37026072, -7431072 ],
[ 731, 4096, 1014255, 867162328, 329933153 ],
[ 19, 2, 1, 18, 56 ],
[ 165, 10, 1539, 546, 1836 ],
[ 453, 106, 37179, 3746, 57996 ],
[ 885, 298, 649539, 191522, 1820556 ],
[ 1461, 3178, 9624987, 1819554, 32764716 ],
[ 2181, 5290, 129140163, 35743010, 765946476 ],
[ 16, 6, 34, 38, -11 ],
[ 122, 48, 1194, 3340, -38 ],
[ 330, 240, 27612, 102124, 10179 ],
[ 642, 1104, 474276, 3143692, 371547 ],
[ 1058, 6960, 7139202, 74593324, -1247966 ],
[ 1578, 16656, 95916420, 1749845836, 133315407 ]
];



traces[37] := [
[ 1, 0, 1, -4, 6 ],
[ 4, 14, 109, 250, 569 ],
[ 12, 50, 937, 2890, 15374 ],
[ 22, 290, 5113, 129002, 128204 ],
[ 34, 1346, 122941, 1744522, 8675609 ],
[ 52, 4130, 1094113, 71091754, 67777964 ],
[ 4, -2, 13, -6, 17 ],
[ 19, 2, 213, 170, 745 ],
[ 55, 2, 1269, -1462, 22615 ],
[ 105, 98, 9381, 18410, 293035 ],
[ 169, 578, 219237, -549238, 15690805 ],
[ 255, 1058, 1842381, 11322922, 211920175 ],
[ 7, 5, 4, -5, 38 ],
[ 60, 40, 37, 996, 1312 ],
[ 168, 160, 613, 44132, 46912 ],
[ 328, 640, 2197, 1360548, 661312 ],
[ 540, 2560, 70453, 35506404, 32775712 ],
[ 808, 10240, 857917, 855356196, 343170112 ],
[ 10, -2, 16, -6, 14 ],
[ 75, 2, 280, 170, 490 ],
[ 211, 2, 1312, -1462, 18760 ],
[ 411, 98, 14368, 18410, 273880 ],
[ 675, 578, 245080, -549238, 12555850 ],
[ 1011, 1058, 1968928, 11322922, 122468920 ],
[ 13, 5, 18, 11, -1 ],
[ 98, 28, 218, 1736, 369 ],
[ 274, 100, 1874, 73288, 10374 ],
[ 534, 580, 10226, 2262024, 3204 ],
[ 878, 2692, 245882, 57817544, 5550609 ],
[ 1314, 8260, 2188226, 1401725832, -10347036 ]
];



traces[40] := [
[ 2, 0, 4, -8, 6 ],
[ 8, 68, 268, 376, 976 ],
[ 18, 388, 2524, 13528, 37926 ],
[ 32, 2868, 19828, 283672, 1209736 ],
[ 50, 14564, 257236, 5107928, 42797526 ],
[ 74, 86676, 1819804, 112940184, 1218246046 ],
[ 6, -4, 12, -8, 18 ],
[ 36, 20, 348, -104, 2100 ],
[ 92, 4, 3804, 4184, 108188 ],
[ 176, 436, 28716, 23064, 3537320 ],
[ 288, 740, 281292, 665816, 144292728 ],
[ 428, 4756, 2658876, 6730904, 4615389740 ],
[ 14, 14, 10, -2, 58 ],
[ 90, 410, 178, 2058, 3894 ],
[ 240, 4002, 1876, 69434, 202904 ],
[ 464, 30674, 13996, 2068378, 8217784 ],
[ 762, 197282, 191626, 51886650, 345124614 ],
[ 1136, 1177202, 1347412, 1239994330, 11815571224 ],
[ 12, -4, 24, -8, 36 ],
[ 126, 20, 312, -104, 3618 ],
[ 350, 4, 5496, 4184, 277874 ],
[ 686, 436, 27384, 23064, 11422418 ],
[ 1134, 740, 337848, 665816, 478405314 ],
[ 1694, 4756, 3549624, 6730904, 16684065218 ],
[ 18, 14, 26, 38, -4 ],
[ 160, 692, 182, 3580, 426 ],
[ 440, 7108, 2378, 117340, 15426 ],
[ 860, 55972, 33482, 3668380, 428486 ],
[ 1420, 364868, 359318, 95767900, 17797526 ],
[ 2120, 2182372, 1271162, 2309398300, 319808546 ]
];



traces[41] := [
[ 1, 1, -2, 1, 4 ],
[ 7, 19, 50, 851, 648 ],
[ 18, 55, 488, 3523, 13688 ],
[ 34, 535, 3032, 231843, 386088 ],
[ 55, 2791, 53330, 4157955, 4041688 ],
[ 82, 6775, 507512, 127698019, 158299288 ],
[ 6, 3, -2, 11, 20 ],
[ 55, 7, 56, 355, 392 ],
[ 151, 7, 728, 1347, 23912 ],
[ 295, 343, 4712, 61347, 1030232 ],
[ 487, 2023, 50024, 635395, 10881752 ],
[ 727, 3703, 492632, 36185187, 210010472 ],
[ 8, 11, -4, 15, 28 ],
[ 62, 38, 14, 1778, 976 ],
[ 169, 110, 245, 50834, 30976 ],
[ 329, 1070, 845, 1552914, 854176 ],
[ 542, 5582, 27086, 37255058, 18123376 ],
[ 809, 13550, 330365, 923126034, 378148576 ],
[ 23, 3, -4, 11, 36 ],
[ 216, 7, 54, 355, 72 ],
[ 600, 7, 486, 1347, 25992 ],
[ 1176, 343, 4374, 61347, 1391112 ],
[ 1944, 2023, 39366, 635395, 9279432 ],
[ 2904, 3703, 354294, 36185187, 125642952 ],
[ 27, -1, 2, 47, 3 ],
[ 220, 32, 48, 4724, 388 ],
[ 604, 128, 12, 151796, 12988 ],
[ 1180, 512, 2028, 4923700, 364588 ],
[ 1948, 2048, 65712, 129133684, 7499188 ],
[ 2908, 8192, 768108, 3086172084, 150011788 ]
];



traces[44] := [
[ 2, 0, 6, -8, 2 ],
[ 8, 52, 150, 664, 1182 ],
[ 18, 388, 1218, 10776, 29198 ],
[ 32, 2628, 15930, 248568, 758402 ],
[ 50, 14980, 163806, 5439320, 21124698 ],
[ 74, 84036, 1106994, 119900344, 428756462 ],
[ 6, -4, 18, -8, 6 ],
[ 36, 4, 102, 312, 1734 ],
[ 92, 4, 1974, 1432, 46374 ],
[ 176, 196, 27030, 18680, 1252014 ],
[ 288, 1156, 205446, 784216, 28113054 ],
[ 428, 2116, 900102, 19097784, 689533494 ],
[ 10, 16, 0, 20, 44 ],
[ 58, 272, 60, 2040, 2412 ],
[ 152, 2600, 570, 48216, 66908 ],
[ 292, 19720, 10098, 1511960, 1260452 ],
[ 478, 126728, 98196, 35475672, 43251588 ],
[ 712, 743560, 634602, 815074712, 870792092 ],
[ 15, -4, 20, -8, 42 ],
[ 129, 4, 104, 312, 1986 ],
[ 353, 4, 1448, 1432, 61746 ],
[ 689, 196, 32744, 18680, 1914306 ],
[ 1137, 1156, 213800, 784216, 35108466 ],
[ 1697, 2116, 489320, 19097784, 824540226 ],
[ 28, 28, 28, 16, -2 ],
[ 198, 840, 248, 4012, 892 ],
[ 534, 8736, 1520, 146220, 28548 ],
[ 1038, 67200, 22448, 4438092, 412152 ],
[ 1710, 440832, 276728, 115210348, 18723448 ],
[ 2550, 2623488, 2485232, 2720213388, 305200212 ]
];



traces[53] := [
[ 2, 2, 2, -2, 8 ],
[ 6, 16, 109, 280, 711 ],
[ 17, 52, 772, 6984, 9740 ],
[ 31, 388, 4828, 193544, 196566 ],
[ 48, 1924, 103501, 3488200, 7686295 ],
[ 73, 5188, 758788, 98345864, 172282246 ],
[ 6, 0, 11, -8, 31 ],
[ 27, 4, 215, 136, 903 ],
[ 77, 4, 1181, 584, 20253 ],
[ 147, 196, 9149, 33800, 364953 ],
[ 237, 1156, 191015, 145864, 12947403 ],
[ 357, 2116, 1310069, 13411208, 325238853 ],
[ 8, 9, -2, 11, 38 ],
[ 54, 32, 19, 1196, 1186 ],
[ 149, 104, 367, 42028, 25816 ],
[ 289, 776, 1183, 1295724, 457696 ],
[ 474, 3848, 37891, 31632044, 16859626 ],
[ 709, 10376, 463543, 777884652, 429690856 ],
[ 14, 0, 18, -8, 42 ],
[ 105, 4, 302, 136, 638 ],
[ 295, 4, 1628, 584, 21188 ],
[ 575, 196, 15932, 33800, 619988 ],
[ 945, 1156, 240638, 145864, 11355038 ],
[ 1415, 2116, 1693052, 13411208, 252197588 ],
[ 19, 9, 14, 27, 5 ],
[ 138, 32, 218, 2540, 611 ],
[ 384, 104, 1544, 103468, 7240 ],
[ 748, 776, 9656, 3196268, 134066 ],
[ 1230, 3848, 207002, 81177260, 6123795 ],
[ 1840, 10376, 1517576, 1969066988, 133219746 ]
];



traces[56] := [
[ 3, 3, 6, -9, 12 ],
[ 11, 81, 214, 777, 1548 ],
[ 25, 577, 1450, 16225, 49964 ],
[ 45, 3633, 19066, 351777, 869428 ],
[ 71, 20769, 160198, 7073793, 36078404 ],
[ 105, 119313, 1481194, 160180833, 452138748 ],
[ 9, -3, 18, -15, 36 ],
[ 51, 17, 342, 225, 1884 ],
[ 131, 65, 3078, 2369, 70812 ],
[ 251, 305, 27702, 42401, 1383084 ],
[ 411, 1313, 249318, 765441, 43499532 ],
[ 611, 4625, 2243862, 18588257, 715079484 ],
[ 14, 24, -2, 36, 72 ],
[ 82, 402, 106, 2442, 2984 ],
[ 216, 3778, 640, 73210, 86112 ],
[ 416, 28002, 11776, 2012922, 1592784 ],
[ 682, 179778, 81466, 49303098, 56185592 ],
[ 1016, 1061922, 890704, 1151397498, 1076664384 ],
[ 24, -3, 24, -15, 24 ],
[ 186, 17, 396, 225, 672 ],
[ 506, 65, 3564, 2369, 40992 ],
[ 986, 305, 32076, 42401, 1766112 ],
[ 1626, 1313, 288684, 765441, 18654432 ],
[ 2426, 4625, 2598156, 18588257, 360017952 ],
[ 38, 42, 26, 34, 14 ],
[ 280, 1184, 316, 5320, 1308 ],
[ 760, 12416, 2110, 207048, 39064 ],
[ 1480, 95744, 26926, 6260040, 612928 ],
[ 2440, 628736, 265276, 163287496, 27688404 ],
[ 3640, 3743744, 2721694, 3874973256, 392426248 ]
];


traces[57] := [
[ 2, 4, -2, 0, 10 ],
[ 13, 40, 187, 684, 1278 ],
[ 32, 304, 3724, 18252, 18458 ],
[ 60, 784, 50056, 373996, 661898 ],
[ 97, 6736, 788407, 8711436, 13225158 ],
[ 144, 14608, 9333412, 256546348, 491197118 ],
[ 12, 8, 6, 12, 52 ],
[ 98, 16, 1012, 428, 2240 ],
[ 266, 208, 23164, 3020, 56432 ],
[ 518, 400, 388504, 130796, 1841720 ],
[ 854, 5200, 5716264, 1144076, 32869592 ],
[ 1274, 8464, 76331788, 43169324, 920406800 ],
[ 14, 8, -8, 44, 20 ],
[ 126, 56, -20, 2880, 1884 ],
[ 352, 560, 322, 100192, 35784 ],
[ 688, 656, -974, 2957152, 1364904 ],
[ 1134, 8336, 86380, 77124960, 24470364 ],
[ 1696, 18704, 239866, 1903741792, 746288424 ],
[ 43, 8, 31, 12, 128 ],
[ 381, 16, 3537, 428, 3636 ],
[ 1053, 208, 86265, 3020, 102996 ],
[ 2061, 400, 1511217, 130796, 2945556 ],
[ 3405, 5200, 22418937, 1144076, 60889716 ],
[ 5085, 8464, 300972753, 43169324, 1469071476 ],
[ 34, 18, 42, 102, -12 ],
[ 278, 72, 2706, 5184, 678 ],
[ 764, 408, 64476, 215104, 3458 ],
[ 1492, 1560, 1104276, 6363648, 286898 ],
[ 2462, 10584, 16348938, 165356736, 3850158 ],
[ 3676, 24984, 219054492, 4042193280, 256822118 ]
];




traces[60] := [
[ 4, 2, 8, 6, 20 ],
[ 16, 130, 428, 1042, 1912 ],
[ 32, 834, 5828, 23074, 86040 ],
[ 56, 4722, 74444, 596098, 2086752 ],
[ 88, 28642, 906116, 11823394, 72620560 ],
[ 128, 149970, 9503780, 220346050, 2310545592 ],
[ 12, -6, 24, 2, 60 ],
[ 64, 18, 988, 66, 5128 ],
[ 160, 130, 18076, 1506, 189160 ],
[ 304, 370, 259084, 171906, 7267288 ],
[ 496, 3042, 3627052, 2139426, 249034840 ],
[ 736, 6610, 46890364, 34842306, 9059107048 ],
[ 18, 22, -4, 38, 82 ],
[ 116, 582, 104, 3358, 5016 ],
[ 310, 5318, 1616, 101070, 288014 ],
[ 598, 40694, 19040, 3015918, 11003966 ],
[ 980, 255462, 197528, 69522382, 450699384 ],
[ 1462, 1530710, 764528, 1656146862, 15906079166 ],
[ 34, -6, 34, 2, 110 ],
[ 230, 18, 2502, 66, 10138 ],
[ 614, 130, 53622, 1506, 486282 ],
[ 1190, 370, 902502, 171906, 21376698 ],
[ 1958, 3042, 13161366, 2139426, 841972522 ],
[ 2918, 6610, 175139334, 34842306, 30392804058 ],
[ 32, 38, 64, 106, 0 ],
[ 276, 1174, 2804, 5950, 612 ],
[ 756, 12726, 65156, 220910, 43540 ],
[ 1476, 95334, 1128884, 6349070, 649252 ],
[ 2436, 633046, 16475396, 168606190, 24183060 ],
[ 3636, 3745734, 216667364, 3960509390, 708983092 ]
];



traces[61] := [
[ 2, 0, 8, -2, 6 ],
[ 9, 17, 137, 289, 947 ],
[ 25, 65, 944, 8513, 20612 ],
[ 47, 305, 6296, 230817, 91542 ],
[ 75, 1313, 161273, 5352961, 16848747 ],
[ 113, 4625, 1542176, 136028769, 383790302 ],
[ 7, -3, 27, -7, 33 ],
[ 42, 1, 269, 97, 1131 ],
[ 118, 1, 1283, 321, 39561 ],
[ 228, 49, 11747, 9633, 538341 ],
[ 372, 289, 295901, 241153, 27320271 ],
[ 558, 529, 2738507, 10199649, 295703601 ],
[ 15, 5, 11, 7, 56 ],
[ 132, 40, 65, 2184, 1760 ],
[ 368, 160, 620, 95432, 70460 ],
[ 720, 640, 3380, 2966856, 802460 ],
[ 1188, 2560, 108785, 78090696, 50516960 ],
[ 1776, 10240, 1305980, 1874290248, 370006460 ],
[ 20, -3, 30, -7, 40 ],
[ 165, 1, 336, 97, 766 ],
[ 461, 1, 1326, 321, 37996 ],
[ 901, 49, 16734, 9633, 730876 ],
[ 1485, 289, 321744, 241153, 24165406 ],
[ 2221, 529, 2865054, 10199649, 183599836 ],
[ 35, 1, 44, 35, 7 ],
[ 300, 24, 240, 5064, 557 ],
[ 828, 96, 60, 215240, 18812 ],
[ 1620, 384, 10140, 6686024, 221792 ],
[ 2676, 1536, 328560, 176394696, 13272497 ],
[ 3996, 6144, 3840540, 4210517576, 141484052 ]
];



traces[65] := [
[ 2, 2, 4, 2, -2 ],
[ 14, 70, 106, 998, 924 ],
[ 36, 110, 1720, 25862, 36932 ],
[ 68, 1550, 11704, 534534, 1754884 ],
[ 110, 4750, 159082, 10428934, 55661292 ],
[ 164, 18830, 1086616, 299846150, 1915348444 ],
[ 12, 6, 26, 22, 14 ],
[ 110, 46, 398, 774, 3292 ],
[ 302, 14, 3806, 12294, 216412 ],
[ 590, 1166, 32414, 119814, 10342732 ],
[ 974, 3214, 299342, 2155014, 393694252 ],
[ 1454, 12686, 2736494, 93424134, 14467822972 ],
[ 16, 18, -8, 46, 40 ],
[ 124, 104, -38, 3540, 4632 ],
[ 338, 216, 586, 118004, 250790 ],
[ 658, 2424, 1498, 3103444, 11540182 ],
[ 1084, 9176, 54106, 76020660, 446506680 ],
[ 1618, 30264, 259930, 1886559124, 16390244182 ],
[ 46, 6, 64, 22, 58 ],
[ 432, 46, 756, 774, 10872 ],
[ 1200, 14, 6804, 12294, 775992 ],
[ 2352, 1166, 61236, 119814, 38141112 ],
[ 3888, 3214, 551124, 2155014, 1528029432 ],
[ 5808, 12686, 4960116, 93424134, 56844392952 ],
[ 40, 0, 4, 88, -8 ],
[ 362, 112, 176, 7776, 324 ],
[ 1002, 168, 1784, 270336, 5682 ],
[ 1962, 1992, 12536, 8122176, 473634 ],
[ 3242, 3208, 171824, 218710656, 8786292 ],
[ 4842, 25032, 1208216, 5254082496, 177067194 ]
];



traces[69] := [
[ 3, 0, 9, 12, 0 ],
[ 13, 28, 239, 484, 1000 ],
[ 29, 148, 2951, 13092, 26736 ],
[ 53, 484, 55235, 316932, 634440 ],
[ 85, 2836, 707063, 7850212, 19061176 ],
[ 125, 8260, 9162035, 163004868, 470408760 ],
[ 10, -4, 30, 4, 44 ],
[ 52, 4, 712, 68, 1700 ],
[ 132, 52, 12496, 2340, 44804 ],
[ 252, 100, 200104, 46596, 1264820 ],
[ 412, 1300, 2960848, 1427684, 37960244 ],
[ 612, 2116, 38895664, 18301380, 557847140 ],
[ 19, -6, 2, 62, -40 ],
[ 114, 16, 32, 2360, 584 ],
[ 309, 64, -208, 90488, 25184 ],
[ 597, 256, 9308, 2721272, 245984 ],
[ 978, 1024, 83768, 67000952, 18331784 ],
[ 1461, 4096, 1190420, 1585614584, 101127584 ],
[ 27, -4, 45, 4, 68 ],
[ 189, 4, 1959, 68, 1484 ],
[ 509, 52, 42711, 2340, 53900 ],
[ 989, 100, 738159, 46596, 1657964 ],
[ 1629, 1300, 10937391, 1427684, 40988780 ],
[ 2429, 2116, 146029119, 18301380, 502795244 ],
[ 38, 8, 78, 88, 6 ],
[ 328, 66, 3288, 5658, 920 ],
[ 904, 306, 74568, 243514, 20936 ],
[ 1768, 1026, 1308648, 7631578, 636440 ],
[ 2920, 4818, 19525944, 194756730, 18231176 ],
[ 4360, 17442, 261470856, 4602066970, 307858760 ]
];



traces[73] := [
[ 2, 3, 3, 3, 1 ],
[ 17, 27, 100, 763, 492 ],
[ 47, 87, 1459, 17163, 15627 ],
[ 91, 663, 6571, 492779, 356187 ],
[ 149, 3303, 122500, 10896331, 9833172 ],
[ 223, 8823, 1227691, 292522667, 172813707 ],
[ 16, 3, 4, 19, 10 ],
[ 149, 7, 116, 427, 396 ],
[ 413, 7, 1940, 1547, 16956 ],
[ 809, 343, 10100, 62699, 640116 ],
[ 1337, 2023, 121364, 869323, 8565876 ],
[ 1997, 3703, 1261940, 44010155, 183130236 ],
[ 29, 7, 4, 19, 34 ],
[ 264, 64, 28, 4476, 1320 ],
[ 734, 256, 973, 191164, 41820 ],
[ 1438, 1024, 2197, 5935740, 725820 ],
[ 2376, 4096, 70012, 156532284, 28297320 ],
[ 3550, 16384, 873397, 3760317948, 409793820 ],
[ 65, 3, -4, 19, 10 ],
[ 594, 7, 108, 427, 36 ],
[ 1650, 7, 972, 1547, 12996 ],
[ 3234, 343, 8748, 62699, 695556 ],
[ 5346, 2023, 78732, 869323, 4639716 ],
[ 7986, 3703, 708588, 44010155, 62821476 ],
[ 49, 15, 22, 71, -8 ],
[ 430, 54, 200, 7610, 242 ],
[ 1194, 174, 2918, 315226, 9377 ],
[ 2338, 1326, 13142, 9811802, 199937 ],
[ 3862, 6606, 245000, 254544218, 5926922 ],
[ 5770, 17646, 2455382, 6140276570, 75157457 ]
];



traces[76] := [
[ 4, 2, 14, -2, 18 ],
[ 18, 98, 230, 922, 1574 ],
[ 44, 834, 2150, 10186, 41422 ],
[ 82, 5858, 28046, 490954, 754354 ],
[ 132, 35906, 276062, 10963466, 33767282 ],
[ 196, 209954, 1859894, 263868234, 643081134 ],
[ 12, -6, 42, -6, 54 ],
[ 90, 2, 138, 330, 2550 ],
[ 242, 2, 4026, -7286, 61398 ],
[ 470, 98, 49242, 44234, 1792350 ],
[ 774, 578, 390378, 837130, 47287758 ],
[ 1154, 1058, 1742826, 31014730, 1145269350 ],
[ 30, 32, 20, 28, 104 ],
[ 234, 984, 140, 4464, 2888 ],
[ 640, 10464, 1502, 174992, 81392 ],
[ 1248, 80768, 22214, 5286544, 1643888 ],
[ 2058, 529920, 210452, 137700240, 81609992 ],
[ 3072, 3160064, 1387502, 3280915600, 1266679088 ],
[ 39, -6, 40, -6, 90 ],
[ 345, 2, 136, 330, 3186 ],
[ 953, 2, 2248, -7286, 91746 ],
[ 1865, 98, 59656, 44234, 2664306 ],
[ 3081, 578, 375112, 837130, 53858466 ],
[ 4601, 1058, 506248, 31014730, 1293290226 ],
[ 64, 64, 40, 56, 22 ],
[ 522, 2136, 320, 9072, 1124 ],
[ 1434, 23136, 1736, 376720, 30172 ],
[ 2802, 180096, 31880, 11627152, 473104 ],
[ 4626, 1187328, 404672, 305996688, 26736032 ],
[ 6906, 7084032, 3513608, 7294864528, 467299884 ]
];



traces[77] := [
[ 3, 1, 8, 5, 20 ],
[ 11, 41, 198, 557, 870 ],
[ 29, 161, 2136, 11853, 24060 ],
[ 53, 689, 21588, 388237, 641160 ],
[ 83, 2849, 132606, 7375821, 22945350 ],
[ 125, 10769, 1866684, 156563981, 490948200 ],
[ 10, -3, 20, -3, 60 ],
[ 48, 17, 492, 269, 1852 ],
[ 132, 65, 2952, 1101, 57952 ],
[ 252, 305, 34536, 117901, 1011472 ],
[ 408, 1313, 283884, 1477581, 31747372 ],
[ 612, 4625, 3043080, 11860493, 892285792 ],
[ 14, 12, 0, 28, 68 ],
[ 94, 82, 54, 2498, 2196 ],
[ 256, 322, 1326, 75394, 64536 ],
[ 496, 1378, 14298, 2272258, 1114296 ],
[ 814, 5698, 27630, 56661890, 36442836 ],
[ 1216, 21538, 1276194, 1326933250, 1018534296 ],
[ 27, -3, 24, -3, 100 ],
[ 185, 17, 560, 269, 2132 ],
[ 509, 65, 3116, 1101, 75032 ],
[ 989, 305, 39692, 117901, 1747352 ],
[ 1625, 1313, 315056, 1477581, 39520052 ],
[ 2429, 4625, 3238796, 11860493, 1042293272 ],
[ 32, 12, 24, 48, 10 ],
[ 238, 82, 468, 4606, 570 ],
[ 658, 322, 3660, 179742, 16560 ],
[ 1282, 1378, 31404, 5478654, 453660 ],
[ 2110, 5698, 331380, 141045982, 18257850 ],
[ 3154, 21538, 2999436, 3364594110, 373760700 ]
];



traces[85] := [
[ 4, 0, 12, 12, 20 ],
[ 16, 44, 186, 256, 1244 ],
[ 42, 100, 2904, 16480, 61310 ],
[ 78, 820, 11916, 399456, 1840634 ],
[ 124, 2276, 353514, 9608544, 64713200 ],
[ 186, 10900, 1320396, 251231584, 2445227374 ],
[ 12, -4, 42, 0, 56 ],
[ 70, 20, 486, -160, 3638 ],
[ 194, 4, 4794, 1632, 190306 ],
[ 374, 436, 21306, 14432, 6804478 ],
[ 610, 740, 619974, 826720, 267895946 ],
[ 914, 4756, 3425226, 39419232, 9766838818 ],
[ 32, 4, 12, 40, 90 ],
[ 224, 66, 102, 4186, 7984 ],
[ 610, 194, 1950, 166138, 472808 ],
[ 1186, 1106, 3870, 5015194, 19776584 ],
[ 1952, 3234, 220998, 130315834, 817668208 ],
[ 2914, 15986, 1329630, 3105177562, 29212556984 ],
[ 32, -4, 60, 0, 72 ],
[ 270, 20, 696, -160, 8178 ],
[ 754, 4, 6012, 1632, 533846 ],
[ 1474, 436, 37788, 14432, 23984918 ],
[ 2430, 740, 745464, 826720, 973344786 ],
[ 3634, 4756, 4427388, 39419232, 36169967558 ],
[ 44, 0, 24, 100, 0 ],
[ 406, 60, 264, 6492, 494 ],
[ 1126, 100, 3096, 290172, 18810 ],
[ 2206, 1060, 11544, 9041212, 215634 ],
[ 3646, 1860, 430536, 241738492, 10806950 ],
[ 5446, 13540, 2301624, 5811702972, 374914874 ]
];




traces[88] := [
[ 5, 6, 16, -4, 22 ],
[ 21, 108, 364, 976, 1458 ],
[ 53, 996, 3256, 21392, 42878 ],
[ 99, 7108, 35776, 613296, 843938 ],
[ 159, 43140, 321700, 12808528, 30427038 ],
[ 237, 254020, 2142232, 299252208, 595229918 ],
[ 17, -4, 38, -16, 56 ],
[ 111, 4, 582, 368, 2100 ],
[ 295, 4, 5910, 784, 73188 ],
[ 571, 196, 47670, 72112, 1349820 ],
[ 939, 1156, 451878, 813392, 45855228 ],
[ 1399, 2116, 4194150, 18094576, 787264740 ],
[ 40, 44, 16, 36, 104 ],
[ 286, 1192, 202, 5224, 3196 ],
[ 778, 12704, 2122, 211656, 81564 ],
[ 1514, 97920, 25570, 6399304, 1972476 ],
[ 2494, 641536, 203602, 166040008, 64515484 ],
[ 3722, 3827712, 1315546, 3960956488, 1408466556 ],
[ 50, -4, 44, -16, 32 ],
[ 420, 4, 492, 368, 1236 ],
[ 1156, 4, 7116, 784, 42996 ],
[ 2260, 196, 41964, 72112, 1445556 ],
[ 3732, 1156, 469068, 813392, 23389716 ],
[ 5572, 2116, 4730604, 18094576, 531571476 ],
[ 58, 72, 52, 88, -2 ],
[ 456, 1872, 716, 8308, 808 ],
[ 1256, 20392, 6212, 336884, 26628 ],
[ 2452, 158472, 61460, 10419988, 437688 ],
[ 4044, 1040136, 582908, 269019700, 20270788 ],
[ 6040, 6207624, 4278116, 6426282580, 341323668 ]
];



traces[89] := [
[ 3, 7, 1, 11, 11 ],
[ 21, 31, 56, 1055, 698 ],
[ 56, 91, 731, 20719, 21743 ],
[ 108, 859, 3539, 607823, 606863 ],
[ 177, 4459, 69464, 13284527, 12615458 ],
[ 264, 10939, 709859, 348158735, 273209903 ],
[ 20, 7, 0, 23, 46 ],
[ 177, 11, 58, 527, 538 ],
[ 489, 11, 970, 2031, 34618 ],
[ 957, 539, 5050, 95823, 1514098 ],
[ 1581, 3179, 60682, 898223, 15541378 ],
[ 2361, 5819, 630970, 53508879, 295484458 ],
[ 24, 23, -1, 55, 58 ],
[ 198, 62, 20, 4354, 1396 ],
[ 545, 182, 488, 150306, 43486 ],
[ 1065, 1718, 1352, 4667938, 1213726 ],
[ 1758, 8918, 43220, 117762850, 25230916 ],
[ 2625, 21878, 532712, 2862551074, 546419806 ],
[ 77, 7, -4, 23, 72 ],
[ 702, 11, 54, 527, 108 ],
[ 1950, 11, 486, 2031, 38988 ],
[ 3822, 539, 4374, 95823, 2086668 ],
[ 6318, 3179, 39366, 898223, 13919148 ],
[ 9438, 5819, 354294, 53508879, 188464428 ],
[ 83, 3, 6, 111, 18 ],
[ 708, 48, 64, 12348, 598 ],
[ 1956, 192, 16, 513724, 19243 ],
[ 3828, 768, 2704, 15880828, 544363 ],
[ 6324, 3072, 87616, 418414140, 11052958 ],
[ 9444, 12288, 1024144, 9980470780, 234147403 ]
];



traces[92] := [
[ 5, 10, 10, 4, 22 ],
[ 19, 104, 216, 880, 1618 ],
[ 47, 904, 1902, 20368, 34954 ],
[ 87, 6536, 20526, 584720, 802938 ],
[ 139, 39176, 206280, 11568016, 24433314 ],
[ 207, 225416, 1333470, 280856336, 651092858 ],
[ 17, 0, 20, -16, 62 ],
[ 99, 8, 168, 272, 2850 ],
[ 259, 8, 3048, 1168, 71250 ],
[ 499, 392, 23784, 67600, 1781250 ],
[ 819, 2312, 229416, 291728, 44531250 ],
[ 1219, 4232, 1781160, 26822416, 1113281250 ],
[ 24, 42, 0, 62, 80 ],
[ 158, 688, 72, 3608, 2956 ],
[ 426, 7056, 930, 122456, 75972 ],
[ 826, 54544, 11778, 3789528, 1584036 ],
[ 1358, 354832, 101304, 93680984, 48342892 ],
[ 2026, 2097424, 624882, 2231609304, 1121561316 ],
[ 53, 0, -4, -16, 122 ],
[ 375, 8, 144, 272, 4350 ],
[ 1015, 8, 1296, 1168, 108750 ],
[ 1975, 392, 11664, 67600, 2718750 ],
[ 3255, 2312, 104976, 291728, 67968750 ],
[ 4855, 4232, 944784, 26822416, 1699218750 ],
[ 52, 74, 32, 102, 4 ],
[ 398, 1648, 424, 7448, 1118 ],
[ 1094, 17808, 3604, 296536, 22454 ],
[ 2134, 138512, 34324, 9196248, 490438 ],
[ 3518, 907792, 372232, 235238744, 16620814 ],
[ 5254, 5406992, 2662708, 5628995544, 455780358 ]
];



traces[93] := [
[ 4, 6, 8, 6, 24 ],
[ 17, 40, 317, 636, 1330 ],
[ 42, 232, 5270, 11676, 25120 ],
[ 78, 712, 69434, 448380, 878380 ],
[ 125, 4648, 987761, 9607260, 22924330 ],
[ 186, 12424, 12736886, 247701564, 509675380 ],
[ 14, 0, 38, -4, 74 ],
[ 74, 8, 970, 188, 2034 ],
[ 196, 104, 18724, -2660, 42582 ],
[ 376, 200, 296776, 71548, 1521534 ],
[ 614, 2600, 4318630, 694364, 38376522 ],
[ 916, 4232, 57063316, 37986364, 733398534 ],
[ 22, 12, -4, 48, 48 ],
[ 162, 64, 38, 3024, 1984 ],
[ 456, 424, 734, 122544, 39748 ],
[ 888, 904, 2366, 3719088, 1782244 ],
[ 1458, 6472, 75782, 96955056, 36436288 ],
[ 2184, 18568, 927086, 2355914160, 724723204 ],
[ 39, 0, 67, -4, 92 ],
[ 279, 8, 2899, 188, 1932 ],
[ 761, 104, 64573, -2660, 53904 ],
[ 1481, 200, 1108597, 71548, 1672752 ],
[ 2439, 2600, 16326091, 694364, 44493324 ],
[ 3641, 4232, 218147317, 37986364, 691252272 ],
[ 46, 18, 78, 62, 10 ],
[ 358, 76, 3550, 6396, 930 ],
[ 984, 364, 83440, 261308, 15120 ],
[ 1920, 1420, 1424824, 8087612, 628380 ],
[ 3166, 7852, 21107398, 209593788, 16674330 ],
[ 4728, 22732, 282691216, 5018227004, 353425380 ]
];



traces[97] := [
[ 3, 6, 6, 6, 3 ],
[ 26, 33, 106, 957, 524 ],
[ 72, 105, 1702, 23805, 16589 ],
[ 140, 825, 7078, 710045, 361229 ],
[ 230, 4137, 138634, 16219197, 10547444 ],
[ 344, 10905, 1430038, 424149725, 180178109 ],
[ 25, 5, 6, 21, 10 ],
[ 230, 9, 118, 477, 396 ],
[ 638, 9, 2182, 1789, 16956 ],
[ 1250, 441, 10438, 79261, 640116 ],
[ 2066, 2601, 132022, 883773, 8565876 ],
[ 3086, 4761, 1400278, 48759517, 183130236 ],
[ 45, 11, 7, 35, 38 ],
[ 408, 80, 34, 6780, 1384 ],
[ 1134, 320, 1216, 293564, 45184 ],
[ 2222, 1280, 2704, 9147004, 745984 ],
[ 3672, 5120, 86146, 241466940, 30831784 ],
[ 5486, 20480, 1075744, 5790361084, 413627584 ],
[ 101, 5, -4, 21, 10 ],
[ 918, 9, 108, 477, 36 ],
[ 2550, 9, 972, 1789, 12996 ],
[ 4998, 441, 8748, 79261, 695556 ],
[ 8262, 2601, 78732, 883773, 4639716 ],
[ 12342, 4761, 708588, 48759517, 62821476 ],
[ 75, 21, 28, 101, -6 ],
[ 664, 66, 212, 11454, 274 ],
[ 1844, 210, 3404, 482110, 10339 ],
[ 3612, 1650, 14156, 15063230, 204979 ],
[ 5968, 8274, 277268, 392591934, 6641194 ],
[ 8916, 21810, 2860076, 9448595390, 82521859 ]
];





////// Checks New ///////

levels := [1..5];
weights := [2..12 by 2];
heckes := [1..5];
Discs := [d : d in [1..100] | IsFundamentalDiscriminant(d)];

printf "Checking Trace at 1*ZF...d=";
function check(d)
    printf "%o ", d;
    F := QuadraticField(d);
    ZF := Integers(F);
    prec := 50;
    R := GradedRingOfHMFs(F, prec);
    trs := [[Trace( HMFSpace(R, n*ZF, [k,k]), m*ZF : precomp := true) : m in heckes] : k in weights, n in levels];
    assert traces[d] eq trs;
    k := Random(weights);
    n := Random(levels);
    m := Random(heckes);
    // tr := Trace(HMFSpace(R, n*ZF, [k, k]), m*ZF);
    // assert Trace(HMFSpace(R, n*ZF, [k, k]), m*ZF : precomp := true) eq tr;
    return true;
end function;

ds := [];
for counter in [1..5] do
    if Set(ds) eq Keys(traces) then
        break;
    end if;
    d := Random(Keys(traces));
    while d in ds do
        d := Random(Keys(traces));
    end while;
    Append(~ds, d);
    _ := check(d);
end for;

// adding this one since it was wrong before

