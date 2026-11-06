(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* The read-only bytes of fuzz_command.asan-ubsan that the program loads as constants: one list per object of the listing
   that lies in a non-writable part of the image, and cmd_ro_ok, the conjunction a contract takes as a premise.
   The instance discharges it from arodata_okP by computation. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Rt Require Import RtDefs.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG0f.
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase.
Import ListNotations.
Open Scope Z_scope.
Definition RO_lit_10330 : list byte := map (Z_to_bv 8) [37; 35; 34; 132; 228; 156; 242; 203; 0].
Definition RO_lit_13794 : list byte := map (Z_to_bv 8) [50; 32; 51; 50; 32; 53; 49; 50; 32; 55; 32; 116; 111; 107; 58; 50; 49; 57; 32; 54; 48; 56; 32; 56; 32; 56; 32; 115; 97; 118; 101; 58; 50; 49; 57; 0].
Definition RO_lit_15923 : list byte := map (Z_to_bv 8) [49; 32; 51; 50; 32; 49; 54; 32; 55; 32; 98; 46; 105; 58; 50; 51; 55; 0].
Definition RO_lit_15fd2 : list byte := map (Z_to_bv 8) [49; 32; 51; 50; 32; 56; 57; 54; 32; 57; 32; 102; 105; 114; 115; 116; 58; 52; 54; 50; 0].
Definition RO_lit_176c8 : list byte := map (Z_to_bv 8) [49; 32; 51; 50; 32; 51; 50; 32; 55; 32; 98; 117; 102; 58; 53; 48; 51; 0].
Definition RO_lit_17f1b : list byte := map (Z_to_bv 8) [49; 32; 51; 50; 32; 56; 32; 54; 32; 101; 110; 100; 58; 57; 54; 0].
Definition RO_lit_18ebf : list byte := map (Z_to_bv 8) [49; 32; 51; 50; 32; 50; 52; 32; 55; 32; 109; 115; 103; 58; 49; 56; 50; 0].
Definition RO_lit_18ed1 : list byte := map (Z_to_bv 8) [49; 32; 51; 50; 32; 51; 50; 32; 49; 49; 32; 114; 101; 102; 117; 115; 97; 108; 58; 50; 50; 55; 0].
Definition RO_lit_1b056 : list byte := map (Z_to_bv 8) [49; 32; 51; 50; 32; 49; 54; 32; 49; 48; 32; 110; 117; 109; 98; 101; 114; 58; 51; 57; 51; 0].
Definition RO_lit_1b074 : list byte := map (Z_to_bv 8) [49; 32; 51; 50; 32; 51; 50; 32; 55; 32; 98; 117; 102; 58; 50; 56; 49; 0].
Definition RO_lit_1dfad : list byte := map (Z_to_bv 8) [50; 32; 51; 50; 32; 49; 54; 32; 57; 32; 98; 46; 105; 50; 56; 58; 50; 51; 55; 32; 54; 52; 32; 49; 54; 32; 55; 32; 98; 46; 105; 58; 50; 51; 55; 0].
Definition RO_lit_1ea5a : list byte := map (Z_to_bv 8) [50; 32; 51; 50; 32; 49; 54; 32; 55; 32; 98; 46; 105; 58; 50; 51; 55; 32; 54; 52; 32; 51; 50; 32; 55; 32; 98; 117; 102; 58; 50; 57; 53; 0].
Definition RO_lit_1f29a : list byte := map (Z_to_bv 8) [49; 32; 51; 50; 32; 50; 53; 54; 32; 55; 32; 105; 100; 115; 58; 49; 48; 56; 0].
Definition RO_lit_20814 : list byte := map (Z_to_bv 8) [50; 32; 51; 50; 32; 55; 54; 57; 32; 56; 32; 108; 105; 115; 116; 58; 51; 53; 56; 32; 57; 52; 52; 32; 49; 54; 32; 57; 32; 99; 111; 117; 110; 116; 58; 51; 53; 56; 0].
Definition RO_lit_20852 : list byte := map (Z_to_bv 8) [49; 32; 51; 50; 32; 52; 48; 57; 54; 32; 55; 32; 98; 117; 102; 58; 50; 53; 52; 0].
Definition RO_lit_210e0 : list byte := map (Z_to_bv 8) [32; 9; 0].
Definition RO_lit_21100 : list byte := map (Z_to_bv 8) [114; 101; 115; 112; 32; 37; 100; 0].
Definition RO_lit_21120 : list byte := map (Z_to_bv 8) [114; 101; 115; 112; 32; 48; 0].
Definition RO_lit_21140 : list byte := map (Z_to_bv 8) [113; 117; 105; 116; 0].
Definition RO_lit_21160 : list byte := map (Z_to_bv 8) [32; 0].
Definition RO_lit_21180 : list byte := map (Z_to_bv 8) [112; 105; 110; 95; 108; 97; 121; 111; 117; 116; 0].
Definition RO_lit_211a0 : list byte := map (Z_to_bv 8) [112; 105; 110; 95; 101; 120; 112; 101; 99; 116; 0].
Definition RO_lit_211c0 : list byte := map (Z_to_bv 8) [99; 111; 110; 110; 101; 99; 116; 32; 37; 115; 32; 37; 115; 0].
Definition RO_lit_211e0 : list byte := map (Z_to_bv 8) [100; 105; 115; 99; 111; 110; 110; 101; 99; 116; 32; 37; 115; 32; 37; 115; 0].
Definition RO_lit_21220 : list byte := map (Z_to_bv 8) [97; 100; 100; 0].
Definition RO_lit_21240 : list byte := map (Z_to_bv 8) [60; 117; 114; 105; 62; 32; 60; 105; 110; 115; 116; 97; 110; 99; 101; 62; 32; 91; 111; 119; 110; 32; 124; 32; 112; 111; 111; 108; 58; 60; 110; 97; 109; 101; 62; 32; 124; 32; 100; 101; 102; 97; 117; 108; 116; 93; 32; 91; 99; 108; 105; 101; 110; 116; 95; 110; 97; 109; 101; 93; 0].
Definition RO_lit_212a0 : list byte := map (Z_to_bv 8) [119; 111; 114; 107; 101; 114; 95; 108; 105; 115; 116; 0].
Definition RO_lit_212c0 : list byte := map (Z_to_bv 8) [0].
Definition RO_lit_212e0 : list byte := map (Z_to_bv 8) [105; 110; 115; 116; 97; 110; 99; 101; 95; 105; 110; 102; 111; 0].
Definition RO_lit_21300 : list byte := map (Z_to_bv 8) [60; 105; 110; 115; 116; 97; 110; 99; 101; 62; 0].
Definition RO_lit_21320 : list byte := map (Z_to_bv 8) [115; 117; 112; 101; 114; 118; 105; 115; 111; 114; 95; 114; 101; 115; 101; 116; 0].
Definition RO_lit_21360 : list byte := map (Z_to_bv 8) [91; 60; 119; 111; 114; 107; 101; 114; 62; 32; 124; 32; 97; 108; 108; 93; 0].
Definition RO_lit_213a0 : list byte := map (Z_to_bv 8) [113; 117; 97; 114; 97; 110; 116; 105; 110; 101; 95; 99; 108; 101; 97; 114; 0].
Definition RO_lit_213e0 : list byte := map (Z_to_bv 8) [60; 105; 110; 115; 116; 97; 110; 99; 101; 62; 32; 124; 32; 97; 108; 108; 0].
Definition RO_lit_21420 : list byte := map (Z_to_bv 8) [112; 111; 108; 105; 99; 121; 95; 115; 101; 116; 0].
Definition RO_lit_21440 : list byte := map (Z_to_bv 8) [60; 102; 111; 114; 109; 97; 116; 32; 124; 32; 42; 62; 32; 111; 119; 110; 32; 124; 32; 112; 111; 111; 108; 58; 60; 110; 97; 109; 101; 62; 0].
Definition RO_lit_21480 : list byte := map (Z_to_bv 8) [112; 111; 111; 108; 95; 99; 111; 110; 102; 105; 103; 0].
Definition RO_lit_214a0 : list byte := map (Z_to_bv 8) [60; 110; 97; 109; 101; 62; 32; 60; 109; 97; 120; 95; 105; 110; 115; 116; 97; 110; 99; 101; 115; 62; 0].
Definition RO_lit_214e0 : list byte := map (Z_to_bv 8) [119; 111; 114; 107; 101; 114; 95; 101; 110; 118; 0].
Definition RO_lit_21500 : list byte := map (Z_to_bv 8) [60; 102; 111; 114; 109; 97; 116; 32; 124; 32; 42; 62; 32; 60; 99; 112; 117; 45; 108; 105; 115; 116; 124; 45; 62; 32; 60; 110; 105; 99; 101; 124; 45; 62; 0].
Definition RO_lit_21560 : list byte := map (Z_to_bv 8) [112; 105; 110; 95; 115; 101; 116; 0].
Definition RO_lit_21580 : list byte := map (Z_to_bv 8) [60; 117; 114; 105; 62; 32; 60; 112; 97; 116; 104; 62; 61; 60; 115; 104; 97; 50; 53; 54; 62; 91; 44; 60; 112; 97; 116; 104; 62; 61; 60; 115; 104; 97; 50; 53; 54; 62; 46; 46; 46; 93; 32; 60; 115; 99; 104; 101; 109; 101; 62; 58; 60; 115; 104; 97; 50; 53; 54; 62; 32; 91; 118; 101; 114; 100; 105; 99; 116; 61; 60; 118; 101; 114; 100; 105; 99; 116; 62; 93; 0].
Definition RO_lit_21600 : list byte := map (Z_to_bv 8) [112; 105; 110; 95; 99; 108; 101; 97; 114; 0].
Definition RO_lit_21620 : list byte := map (Z_to_bv 8) [60; 117; 114; 105; 62; 32; 124; 32; 97; 108; 108; 0].
Definition RO_lit_21640 : list byte := map (Z_to_bv 8) [108; 118; 50; 95; 119; 111; 114; 107; 101; 114; 95; 115; 101; 116; 0].
Definition RO_lit_21660 : list byte := map (Z_to_bv 8) [60; 117; 114; 105; 62; 32; 60; 109; 111; 100; 45; 104; 111; 115; 116; 32; 124; 32; 111; 109; 120; 45; 99; 108; 97; 112; 45; 104; 111; 115; 116; 32; 124; 32; 97; 117; 116; 111; 32; 124; 32; 45; 62; 0].
Definition RO_lit_216c0 : list byte := map (Z_to_bv 8) [112; 105; 110; 95; 97; 99; 99; 101; 112; 116; 0].
Definition RO_lit_216e0 : list byte := map (Z_to_bv 8) [60; 117; 114; 105; 62; 0].
Definition RO_lit_21700 : list byte := map (Z_to_bv 8) [60; 105; 110; 115; 116; 97; 110; 99; 101; 62; 32; 60; 115; 99; 104; 101; 109; 101; 62; 58; 60; 115; 104; 97; 50; 53; 54; 62; 0].
Definition RO_lit_21740 : list byte := map (Z_to_bv 8) [99; 104; 97; 105; 110; 0].
Definition RO_lit_21760 : list byte := map (Z_to_bv 8) [60; 99; 104; 97; 105; 110; 62; 32; 60; 105; 110; 115; 116; 97; 110; 99; 101; 62; 32; 91; 60; 105; 110; 115; 116; 97; 110; 99; 101; 62; 32; 46; 46; 46; 93; 0].
Definition RO_lit_217c0 : list byte := map (Z_to_bv 8) [99; 104; 97; 105; 110; 95; 99; 108; 101; 97; 114; 0].
Definition RO_lit_217e0 : list byte := map (Z_to_bv 8) [60; 99; 104; 97; 105; 110; 62; 0].
Definition RO_lit_21800 : list byte := map (Z_to_bv 8) [100; 101; 115; 99; 114; 105; 112; 116; 111; 114; 95; 103; 101; 116; 0].
Definition RO_lit_21820 : list byte := map (Z_to_bv 8) [112; 97; 110; 101; 108; 95; 103; 101; 116; 0].
Definition RO_lit_21840 : list byte := map (Z_to_bv 8) [114; 101; 109; 111; 118; 101; 0].
Definition RO_lit_21860 : list byte := map (Z_to_bv 8) [114; 101; 109; 111; 118; 101; 32; 37; 105; 0].
Definition RO_lit_21880 : list byte := map (Z_to_bv 8) [99; 111; 110; 110; 101; 99; 116; 0].
Definition RO_lit_218a0 : list byte := map (Z_to_bv 8) [100; 105; 115; 99; 111; 110; 110; 101; 99; 116; 0].
Definition RO_lit_218c0 : list byte := map (Z_to_bv 8) [46; 46; 46; 0].
Definition RO_lit_218e0 : list byte := map (Z_to_bv 8) [37; 100; 0].
Definition RO_lit_21900 : list byte := map (Z_to_bv 8) [49; 32; 35; 50; 32; 42; 32; 42; 0].
Definition RO_lit_21920 : list byte := map (Z_to_bv 8) [35; 49; 32; 76; 0].
Definition RO_lit_21940 : list byte := map (Z_to_bv 8) [35; 49; 0].
Definition RO_lit_21960 : list byte := map (Z_to_bv 8) [48; 32; 76; 32; 49; 32; 50; 0].
Definition RO_lit_21980 : list byte := map (Z_to_bv 8) [76; 0].
Definition RO_lit_219a0 : list byte := map (Z_to_bv 8) [76; 32; 42; 32; 42; 0].
Definition RO_lit_219c0 : list byte := map (Z_to_bv 8) [76; 32; 42; 0].
Definition RO_lit_219e0 : list byte := map (Z_to_bv 8) [63; 49; 0].
Definition RO_lit_21a00 : list byte := map (Z_to_bv 8) [49; 0].
Definition RO_lit_21a20 : list byte := map (Z_to_bv 8) [49; 32; 50; 0].
Definition RO_lit_21a40 : list byte := map (Z_to_bv 8) [49; 32; 35; 50; 0].
Definition RO_lit_21a60 : list byte := map (Z_to_bv 8) [49; 32; 50; 32; 51; 0].
Definition RO_lit_21a80 : list byte := map (Z_to_bv 8) [35; 49; 32; 42; 32; 42; 0].
Definition RO_lit_21aa0 : list byte := map (Z_to_bv 8) [35; 49; 32; 48; 0].
Definition RO_lit_21ac0 : list byte := map (Z_to_bv 8) [49; 32; 50; 32; 51; 32; 42; 0].
Definition RO_lit_21ae0 : list byte := map (Z_to_bv 8) [42; 0].
Definition RO_lit_21b00 : list byte := map (Z_to_bv 8) [45; 0].
Definition RO_lit_21b20 : list byte := map (Z_to_bv 8) [111; 119; 110; 0].
Definition RO_lit_21b40 : list byte := map (Z_to_bv 8) [100; 101; 102; 97; 117; 108; 116; 0].
Definition RO_lit_21b60 : list byte := map (Z_to_bv 8) [112; 111; 111; 108; 58; 0].
Definition RO_lit_21b80 : list byte := map (Z_to_bv 8) [32; 37; 100; 0].
Definition RO_lit_21ba0 : list byte := map (Z_to_bv 8) [118; 101; 114; 100; 105; 99; 116; 61; 0].
Definition RO_rec_codes : list byte := map (Z_to_bv 8) [255; 255; 255; 255; 254; 255; 255; 255; 253; 255; 255; 255; 252; 255; 255; 255; 155; 255; 255; 255; 154; 255; 255; 255; 153; 255; 255; 255; 152; 255; 255; 255; 151; 255; 255; 255; 55; 255; 255; 255; 54; 255; 255; 255; 53; 255; 255; 255; 52; 255; 255; 255; 51; 255; 255; 255; 50; 255; 255; 255; 49; 255; 255; 255; 211; 254; 255; 255; 210; 254; 255; 255; 209; 254; 255; 255; 208; 254; 255; 255; 207; 254; 255; 255; 111; 254; 255; 255; 110; 254; 255; 255; 109; 254; 255; 255; 108; 254; 255; 255; 123; 252; 255; 255; 122; 252; 255; 255; 11; 254; 255; 255; 10; 254; 255; 255; 9; 254; 255; 255; 8; 254; 255; 255; 7; 254; 255; 255; 6; 254; 255; 255; 5; 254; 255; 255; 4; 254; 255; 255; 3; 254; 255; 255; 2; 254; 255; 255; 1; 254; 255; 255; 0; 254; 255; 255; 255; 253; 255; 255; 254; 253; 255; 255; 253; 253; 255; 255; 252; 253; 255; 255; 251; 253; 255; 255; 250; 253; 255; 255; 249; 253; 255; 255; 248; 253; 255; 255; 247; 253; 255; 255; 246; 253; 255; 255; 245; 253; 255; 255; 244; 253; 255; 255; 243; 253; 255; 255; 242; 253; 255; 255; 241; 253; 255; 255; 240; 253; 255; 255; 239; 253; 255; 255; 238; 253; 255; 255; 237; 253; 255; 255].
Definition RO_rec_ncodes : list byte := map (Z_to_bv 8) [58; 0; 0; 0].
Definition RO_lit_21d20 : list byte := map (Z_to_bv 8) [114; 101; 115; 112; 32; 48; 0].
Definition RO_lit_21d40 : list byte := map (Z_to_bv 8) [114; 101; 115; 112; 32; 37; 100; 0].
Definition RO_lit_21d60 : list byte := map (Z_to_bv 8) [114; 101; 115; 112; 32; 0].
Definition RO_lit_21d80 : list byte := map (Z_to_bv 8) [45; 0].
Definition RO_lit_21da0 : list byte := map (Z_to_bv 8) [32; 9; 0].
Definition RO_lit_21dc0 : list byte := map (Z_to_bv 8) [119; 111; 114; 107; 101; 114; 95; 108; 105; 115; 116; 0].
Definition RO_lit_21de0 : list byte := map (Z_to_bv 8) [105; 110; 115; 116; 97; 110; 99; 101; 95; 105; 110; 102; 111; 0].
Definition RO_lit_21e00 : list byte := map (Z_to_bv 8) [115; 117; 112; 101; 114; 118; 105; 115; 111; 114; 95; 114; 101; 115; 101; 116; 0].
Definition RO_lit_21e40 : list byte := map (Z_to_bv 8) [113; 117; 97; 114; 97; 110; 116; 105; 110; 101; 95; 99; 108; 101; 97; 114; 0].
Definition RO_lit_21e80 : list byte := map (Z_to_bv 8) [112; 111; 108; 105; 99; 121; 95; 115; 101; 116; 0].
Definition RO_lit_21ea0 : list byte := map (Z_to_bv 8) [112; 105; 110; 95; 97; 99; 99; 101; 112; 116; 0].
Definition RO_lit_21ec0 : list byte := map (Z_to_bv 8) [112; 111; 111; 108; 95; 99; 111; 110; 102; 105; 103; 0].
Definition RO_lit_21ee0 : list byte := map (Z_to_bv 8) [108; 118; 50; 95; 119; 111; 114; 107; 101; 114; 95; 115; 101; 116; 0].
Definition RO_lit_21f00 : list byte := map (Z_to_bv 8) [119; 111; 114; 107; 101; 114; 95; 101; 110; 118; 0].
Definition RO_lit_21f20 : list byte := map (Z_to_bv 8) [32; 37; 100; 0].
Definition RO_lit_21f40 : list byte := map (Z_to_bv 8) [37; 100; 0].
Definition RO_lit_21f60 : list byte := map (Z_to_bv 8) [99; 104; 97; 105; 110; 0].
Definition RO_lit_21f80 : list byte := map (Z_to_bv 8) [99; 104; 97; 105; 110; 95; 99; 108; 101; 97; 114; 0].
Definition RO_lit_21fa0 : list byte := map (Z_to_bv 8) [100; 101; 115; 99; 114; 105; 112; 116; 111; 114; 95; 103; 101; 116; 0].
Definition RO_lit_21fc0 : list byte := map (Z_to_bv 8) [112; 97; 110; 101; 108; 95; 103; 101; 116; 0].
Definition RO_lit_21fe0 : list byte := map (Z_to_bv 8) [42; 0].
Definition RO_lit_22000 : list byte := map (Z_to_bv 8) [97; 100; 100; 0].
Definition RO_lit_22020 : list byte := map (Z_to_bv 8) [114; 101; 115; 112; 32; 60; 105; 110; 115; 116; 97; 110; 99; 101; 62; 0].
Definition RO_lit_22040 : list byte := map (Z_to_bv 8) [114; 101; 115; 112; 32; 60; 110; 62; 32; 60; 119; 111; 114; 107; 101; 114; 62; 58; 60; 112; 105; 100; 62; 58; 60; 102; 111; 114; 109; 97; 116; 62; 58; 60; 115; 116; 97; 116; 101; 62; 58; 60; 112; 108; 97; 99; 101; 62; 58; 60; 105; 62; 44; 60; 105; 62; 44; 46; 46; 46; 0].
Definition RO_lit_220a0 : list byte := map (Z_to_bv 8) [114; 101; 115; 112; 32; 48; 32; 60; 119; 111; 114; 107; 101; 114; 62; 32; 60; 112; 105; 100; 62; 32; 60; 115; 116; 97; 116; 101; 62; 32; 60; 99; 114; 97; 115; 104; 101; 115; 62; 32; 60; 113; 117; 97; 114; 97; 110; 116; 105; 110; 101; 100; 62; 0].
Definition RO_lit_22100 : list byte := map (Z_to_bv 8) [112; 105; 110; 95; 115; 101; 116; 0].
Definition RO_lit_22120 : list byte := map (Z_to_bv 8) [112; 105; 110; 95; 99; 108; 101; 97; 114; 0].
Definition RO_lit_22140 : list byte := map (Z_to_bv 8) [112; 105; 110; 95; 108; 97; 121; 111; 117; 116; 0].
Definition RO_lit_22160 : list byte := map (Z_to_bv 8) [114; 101; 115; 112; 32; 48; 32; 60; 115; 99; 104; 101; 109; 101; 62; 58; 60; 115; 104; 97; 50; 53; 54; 62; 0].
Definition RO_lit_221a0 : list byte := map (Z_to_bv 8) [112; 105; 110; 95; 101; 120; 112; 101; 99; 116; 0].
Definition RO_lit_221c0 : list byte := map (Z_to_bv 8) [114; 101; 115; 112; 32; 48; 32; 34; 60; 112; 97; 116; 104; 62; 34; 0].
Definition RO_lit_221e0 : list byte := map (Z_to_bv 8) [116; 114; 97; 99; 107; 95; 105; 110; 102; 111; 0].
Definition RO_lit_22200 : list byte := map (Z_to_bv 8) [114; 101; 109; 111; 116; 101; 95; 112; 97; 103; 101; 115; 0].
Definition RO_lit_22220 : list byte := map (Z_to_bv 8) [114; 101; 115; 112; 32; 60; 99; 111; 117; 110; 116; 62; 0].
Definition RO_lit_22240 : list byte := map (Z_to_bv 8) [114; 101; 109; 111; 116; 101; 95; 112; 97; 103; 101; 95; 103; 101; 116; 0].
Definition RO_lit_22260 : list byte := map (Z_to_bv 8) [114; 101; 115; 112; 32; 48; 32; 60; 112; 97; 103; 101; 95; 105; 100; 62; 32; 60; 115; 101; 99; 116; 105; 111; 110; 62; 32; 60; 112; 97; 103; 101; 95; 110; 97; 109; 101; 62; 32; 60; 115; 49; 62; 32; 60; 115; 50; 62; 32; 60; 115; 51; 62; 32; 60; 115; 52; 62; 32; 60; 115; 53; 62; 32; 60; 115; 54; 62; 32; 60; 115; 55; 62; 32; 60; 115; 56; 62; 0].
Definition RO_lit_222e0 : list byte := map (Z_to_bv 8) [112; 97; 114; 97; 109; 95; 105; 110; 102; 111; 0].
Definition RO_lit_22300 : list byte := map (Z_to_bv 8) [114; 101; 115; 112; 32; 48; 32; 60; 117; 110; 105; 116; 62; 32; 60; 115; 99; 97; 108; 101; 62; 32; 60; 109; 105; 110; 62; 32; 60; 109; 97; 120; 62; 32; 60; 100; 101; 102; 97; 117; 108; 116; 62; 32; 60; 115; 116; 101; 112; 62; 32; 60; 115; 116; 97; 98; 108; 101; 95; 115; 121; 109; 98; 111; 108; 62; 0].
Definition RO_lit_22380 : list byte := map (Z_to_bv 8) [112; 114; 101; 115; 101; 116; 95; 108; 105; 115; 116; 0].
Definition RO_lit_223a0 : list byte := map (Z_to_bv 8) [112; 114; 101; 115; 101; 116; 95; 103; 101; 116; 0].
Definition RO_lit_223c0 : list byte := map (Z_to_bv 8) [114; 101; 115; 112; 32; 48; 32; 60; 108; 111; 97; 100; 95; 107; 101; 121; 62; 32; 60; 110; 97; 109; 101; 62; 0].
Definition RO_lit_22400 : list byte := map (Z_to_bv 8) [110; 111; 116; 101; 95; 105; 110; 112; 117; 116; 0].
Definition RO_lit_22420 : list byte := map (Z_to_bv 8) [114; 101; 115; 112; 32; 48; 32; 60; 112; 111; 114; 116; 32; 124; 32; 45; 62; 0].
Definition RO_lit_22460 : list byte := map (Z_to_bv 8) [110; 111; 116; 101; 95; 111; 110; 0].
Definition RO_lit_22480 : list byte := map (Z_to_bv 8) [110; 111; 116; 101; 95; 111; 102; 102; 0].
Definition RO_lit_224a0 : list byte := map (Z_to_bv 8) [97; 108; 108; 95; 110; 111; 116; 101; 115; 95; 111; 102; 102; 0].
Definition RO_lit_224c0 : list byte := map (Z_to_bv 8) [40; 110; 117; 108; 108; 41; 0].
Definition RO_lit_22500 : list byte := map (Z_to_bv 8) [32; 9; 0].
Definition RO_lit_22520 : list byte := map (Z_to_bv 8) [112; 114; 101; 115; 101; 116; 95; 108; 111; 97; 100; 32; 37; 105; 32; 37; 115; 0].
Definition RO_lit_22560 : list byte := map (Z_to_bv 8) [112; 97; 116; 99; 104; 95; 115; 101; 116; 32; 37; 105; 32; 37; 115; 32; 37; 115; 0].
Definition RO_lit_225a0 : list byte := map (Z_to_bv 8) [97; 100; 100; 0].
Definition RO_lit_225c0 : list byte := map (Z_to_bv 8) [100; 101; 115; 99; 114; 105; 112; 116; 111; 114; 95; 103; 101; 116; 0].
Definition RO_lit_225e0 : list byte := map (Z_to_bv 8) [112; 97; 110; 101; 108; 95; 103; 101; 116; 0].
Definition RO_lit_22600 : list byte := map (Z_to_bv 8) [114; 101; 109; 111; 118; 101; 32; 37; 105; 0].
Definition RO_lit_22620 : list byte := map (Z_to_bv 8) [119; 111; 114; 107; 101; 114; 95; 108; 105; 115; 116; 0].
Definition RO_lit_22640 : list byte := map (Z_to_bv 8) [105; 110; 115; 116; 97; 110; 99; 101; 95; 105; 110; 102; 111; 0].
Definition RO_lit_22660 : list byte := map (Z_to_bv 8) [115; 117; 112; 101; 114; 118; 105; 115; 111; 114; 95; 114; 101; 115; 101; 116; 0].
Definition RO_lit_226a0 : list byte := map (Z_to_bv 8) [97; 108; 108; 0].
Definition RO_lit_226c0 : list byte := map (Z_to_bv 8) [113; 117; 97; 114; 97; 110; 116; 105; 110; 101; 95; 99; 108; 101; 97; 114; 0].
Definition RO_lit_22700 : list byte := map (Z_to_bv 8) [112; 111; 108; 105; 99; 121; 95; 115; 101; 116; 0].
Definition RO_lit_22720 : list byte := map (Z_to_bv 8) [108; 118; 50; 95; 119; 111; 114; 107; 101; 114; 95; 115; 101; 116; 0].
Definition RO_lit_22740 : list byte := map (Z_to_bv 8) [112; 111; 111; 108; 95; 99; 111; 110; 102; 105; 103; 0].
Definition RO_lit_22760 : list byte := map (Z_to_bv 8) [119; 111; 114; 107; 101; 114; 95; 101; 110; 118; 0].
Definition RO_lit_22780 : list byte := map (Z_to_bv 8) [99; 104; 97; 105; 110; 0].
Definition RO_lit_227a0 : list byte := map (Z_to_bv 8) [99; 104; 97; 105; 110; 95; 99; 108; 101; 97; 114; 0].
Definition RO_lit_227c0 : list byte := map (Z_to_bv 8) [112; 105; 110; 95; 115; 101; 116; 0].
Definition RO_lit_227e0 : list byte := map (Z_to_bv 8) [112; 105; 110; 95; 97; 99; 99; 101; 112; 116; 0].
Definition RO_lit_22800 : list byte := map (Z_to_bv 8) [112; 105; 110; 95; 99; 108; 101; 97; 114; 0].
Definition RO_lit_22820 : list byte := map (Z_to_bv 8) [113; 117; 105; 116; 0].
Definition RO_lit_22840 : list byte := map (Z_to_bv 8) [99; 111; 110; 110; 101; 99; 116; 32; 37; 115; 32; 37; 115; 0].
Definition RO_lit_22860 : list byte := map (Z_to_bv 8) [100; 105; 115; 99; 111; 110; 110; 101; 99; 116; 32; 37; 115; 32; 37; 115; 0].
Definition RO_lit_228a0 : list byte := map (Z_to_bv 8) [111; 119; 110; 0].
Definition RO_lit_228c0 : list byte := map (Z_to_bv 8) [100; 101; 102; 97; 117; 108; 116; 0].
Definition RO_lit_228e0 : list byte := map (Z_to_bv 8) [112; 111; 111; 108; 58; 0].
Definition RO_lit_22900 : list byte := map (Z_to_bv 8) [118; 101; 114; 100; 105; 99; 116; 61; 0].
Definition RO_lit_22920 : list byte := map (Z_to_bv 8) [116; 114; 97; 99; 107; 95; 105; 110; 102; 111; 0].
Definition RO_lit_22940 : list byte := map (Z_to_bv 8) [114; 101; 109; 111; 116; 101; 95; 112; 97; 103; 101; 115; 0].
Definition RO_lit_22960 : list byte := map (Z_to_bv 8) [114; 101; 109; 111; 116; 101; 95; 112; 97; 103; 101; 95; 103; 101; 116; 0].
Definition RO_lit_22980 : list byte := map (Z_to_bv 8) [112; 97; 114; 97; 109; 95; 105; 110; 102; 111; 0].
Definition RO_lit_229a0 : list byte := map (Z_to_bv 8) [112; 114; 101; 115; 101; 116; 95; 108; 105; 115; 116; 0].
Definition RO_lit_229c0 : list byte := map (Z_to_bv 8) [112; 114; 101; 115; 101; 116; 95; 103; 101; 116; 0].
Definition RO_lit_229e0 : list byte := map (Z_to_bv 8) [110; 111; 116; 101; 95; 105; 110; 112; 117; 116; 0].
Definition RO_lit_22a00 : list byte := map (Z_to_bv 8) [110; 111; 116; 101; 95; 111; 110; 0].
Definition RO_lit_22a20 : list byte := map (Z_to_bv 8) [110; 111; 116; 101; 95; 111; 102; 102; 0].
Definition RO_lit_22a40 : list byte := map (Z_to_bv 8) [97; 108; 108; 95; 110; 111; 116; 101; 115; 95; 111; 102; 102; 0].
Definition RO_lit_22a60 : list byte := map (Z_to_bv 8) [112; 114; 101; 115; 101; 116; 95; 115; 97; 118; 101; 32; 37; 105; 32; 37; 115; 32; 37; 115; 32; 37; 115; 0].
Definition RO_lit_22aa0 : list byte := map (Z_to_bv 8) [98; 121; 112; 97; 115; 115; 32; 37; 105; 32; 37; 105; 0].
Definition RO_lit_22ac0 : list byte := map (Z_to_bv 8) [112; 97; 114; 97; 109; 95; 115; 101; 116; 32; 37; 105; 32; 37; 115; 32; 37; 115; 0].
Definition RO_lit_22b00 : list byte := map (Z_to_bv 8) [112; 97; 114; 97; 109; 95; 103; 101; 116; 32; 37; 105; 32; 37; 115; 0].
Definition RO_lit_22b20 : list byte := map (Z_to_bv 8) [112; 97; 114; 97; 109; 95; 109; 111; 110; 105; 116; 111; 114; 32; 37; 105; 32; 37; 115; 32; 37; 115; 32; 37; 102; 0].
Definition RO_lit_22b60 : list byte := map (Z_to_bv 8) [112; 97; 116; 99; 104; 95; 103; 101; 116; 32; 37; 105; 32; 37; 115; 0].
Definition RO_lit_22b80 : list byte := map (Z_to_bv 8) [108; 105; 99; 101; 110; 115; 101; 101; 32; 37; 105; 0].
Definition RO_lit_22ba0 : list byte := map (Z_to_bv 8) [109; 111; 110; 105; 116; 111; 114; 95; 111; 117; 116; 112; 117; 116; 32; 37; 105; 32; 37; 115; 0].
Definition RO_lit_22be0 : list byte := map (Z_to_bv 8) [109; 105; 100; 105; 95; 108; 101; 97; 114; 110; 32; 37; 105; 32; 37; 115; 32; 37; 102; 32; 37; 102; 0].
Definition RO_lit_22c20 : list byte := map (Z_to_bv 8) [109; 105; 100; 105; 95; 109; 97; 112; 32; 37; 105; 32; 37; 115; 32; 37; 105; 32; 37; 105; 32; 37; 102; 32; 37; 102; 0].
Definition RO_lit_22c60 : list byte := map (Z_to_bv 8) [109; 105; 100; 105; 95; 117; 110; 109; 97; 112; 32; 37; 105; 32; 37; 115; 0].
Definition RO_lit_22ca0 : list byte := map (Z_to_bv 8) [99; 99; 95; 109; 97; 112; 32; 37; 105; 32; 37; 115; 32; 37; 105; 32; 37; 105; 32; 37; 115; 32; 37; 102; 32; 37; 102; 32; 37; 102; 32; 37; 105; 32; 37; 105; 32; 37; 115; 32; 37; 105; 32; 46; 46; 46; 0].
Definition RO_lit_22d00 : list byte := map (Z_to_bv 8) [99; 99; 95; 117; 110; 109; 97; 112; 32; 37; 105; 32; 37; 115; 0].
Definition RO_lit_22d20 : list byte := map (Z_to_bv 8) [99; 99; 95; 118; 97; 108; 117; 101; 95; 115; 101; 116; 32; 37; 105; 32; 37; 115; 32; 37; 102; 0].
Definition RO_lit_22d60 : list byte := map (Z_to_bv 8) [99; 118; 95; 109; 97; 112; 32; 37; 105; 32; 37; 115; 32; 37; 115; 32; 37; 102; 32; 37; 102; 32; 37; 115; 0].
Definition RO_lit_22da0 : list byte := map (Z_to_bv 8) [99; 118; 95; 117; 110; 109; 97; 112; 32; 37; 105; 32; 37; 115; 0].
Definition RO_lit_22dc0 : list byte := map (Z_to_bv 8) [32; 0].
Definition RO_lit_86bf8 : list byte := map (Z_to_bv 8) [19; 1; 1; 250; 35; 48; 1; 0].
Definition RO_lit_86e64 : list byte := map (Z_to_bv 8) [19; 1; 1; 248; 35; 48; 1; 0].
Definition RO_lit_87ae8 : list byte := map (Z_to_bv 8) [19; 1; 1; 236; 35; 48; 1; 0].
Definition RO_lit_882d8 : list byte := map (Z_to_bv 8) [19; 1; 1; 240; 35; 48; 1; 0].
Definition RO_lit_890e0 : list byte := map (Z_to_bv 8) [19; 1; 1; 242; 35; 48; 1; 0].
Definition RO_lit_8a188 : list byte := map (Z_to_bv 8) [19; 1; 1; 250; 35; 48; 1; 0].
Definition RO_lit_8a400 : list byte := map (Z_to_bv 8) [19; 1; 1; 248; 35; 48; 1; 0].
Definition RO_lit_8aa10 : list byte := map (Z_to_bv 8) [19; 1; 1; 248; 35; 48; 1; 0].
Definition RO_lit_8af34 : list byte := map (Z_to_bv 8) [19; 1; 1; 250; 35; 48; 1; 0].
Definition RO_lit_8b258 : list byte := map (Z_to_bv 8) [19; 1; 1; 250; 35; 48; 1; 0].
Definition RO_lit_8b53c : list byte := map (Z_to_bv 8) [19; 1; 1; 246; 35; 48; 1; 0].
Definition RO_lit_8b8f8 : list byte := map (Z_to_bv 8) [19; 1; 1; 250; 35; 48; 1; 0].
Definition RO_lit_8bb70 : list byte := map (Z_to_bv 8) [19; 1; 1; 250; 35; 48; 1; 0].
Definition RO_lit_8bed0 : list byte := map (Z_to_bv 8) [19; 1; 1; 250; 35; 48; 1; 0].
Definition RO_lit_8c1c4 : list byte := map (Z_to_bv 8) [19; 1; 1; 244; 35; 48; 1; 0].
Definition RO_lit_8c570 : list byte := map (Z_to_bv 8) [19; 1; 1; 250; 35; 48; 1; 0].
Definition RO_lit_8c758 : list byte := map (Z_to_bv 8) [19; 1; 1; 250; 35; 48; 1; 0].
Definition RO_lit_8c9f8 : list byte := map (Z_to_bv 8) [19; 1; 1; 250; 35; 48; 1; 0].
Definition RO_lit_8ce4c : list byte := map (Z_to_bv 8) [19; 1; 1; 244; 35; 48; 1; 0].
Definition RO_lit_8da84 : list byte := map (Z_to_bv 8) [19; 1; 1; 246; 35; 48; 1; 0].
Definition RO_lit_8df2c : list byte := map (Z_to_bv 8) [19; 1; 1; 250; 35; 48; 1; 0].
Definition RO_g_parsed : list byte := map (Z_to_bv 8) [32; 18; 2; 0; 0; 0; 0; 0; 64; 18; 2; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 160; 18; 2; 0; 0; 0; 0; 0; 192; 18; 2; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 224; 18; 2; 0; 0; 0; 0; 0; 0; 19; 2; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 32; 19; 2; 0; 0; 0; 0; 0; 96; 19; 2; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 160; 19; 2; 0; 0; 0; 0; 0; 224; 19; 2; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 32; 20; 2; 0; 0; 0; 0; 0; 64; 20; 2; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 128; 20; 2; 0; 0; 0; 0; 0; 160; 20; 2; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 224; 20; 2; 0; 0; 0; 0; 0; 0; 21; 2; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 96; 21; 2; 0; 0; 0; 0; 0; 128; 21; 2; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 22; 2; 0; 0; 0; 0; 0; 32; 22; 2; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 64; 22; 2; 0; 0; 0; 0; 0; 96; 22; 2; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 192; 22; 2; 0; 0; 0; 0; 0; 224; 22; 2; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 128; 17; 2; 0; 0; 0; 0; 0; 0; 19; 2; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 160; 17; 2; 0; 0; 0; 0; 0; 0; 23; 2; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 64; 23; 2; 0; 0; 0; 0; 0; 96; 23; 2; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 192; 23; 2; 0; 0; 0; 0; 0; 224; 23; 2; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 24; 2; 0; 0; 0; 0; 0; 224; 22; 2; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 32; 24; 2; 0; 0; 0; 0; 0; 224; 22; 2; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 64; 24; 2; 0; 0; 0; 0; 0; 96; 24; 2; 0; 0; 0; 0; 0; 1; 0; 0; 0; 0; 0; 0; 0; 128; 24; 2; 0; 0; 0; 0; 0; 192; 17; 2; 0; 0; 0; 0; 0; 1; 0; 0; 0; 0; 0; 0; 0; 160; 24; 2; 0; 0; 0; 0; 0; 224; 17; 2; 0; 0; 0; 0; 0; 1; 0; 0; 0; 0; 0; 0; 0; 64; 17; 2; 0; 0; 0; 0; 0; 64; 17; 2; 0; 0; 0; 0; 0; 1; 0; 0; 0; 0; 0; 0; 0].
Definition RO_g_call_words : list byte := map (Z_to_bv 8) [0; 25; 2; 0; 0; 0; 0; 0; 32; 25; 2; 0; 0; 0; 0; 0; 64; 25; 2; 0; 0; 0; 0; 0; 192; 18; 2; 0; 0; 0; 0; 0; 96; 25; 2; 0; 0; 0; 0; 0; 128; 25; 2; 0; 0; 0; 0; 0; 160; 25; 2; 0; 0; 0; 0; 0; 192; 25; 2; 0; 0; 0; 0; 0; 192; 18; 2; 0; 0; 0; 0; 0; 64; 25; 2; 0; 0; 0; 0; 0; 224; 25; 2; 0; 0; 0; 0; 0; 0; 26; 2; 0; 0; 0; 0; 0; 32; 26; 2; 0; 0; 0; 0; 0; 0; 26; 2; 0; 0; 0; 0; 0; 64; 26; 2; 0; 0; 0; 0; 0; 32; 26; 2; 0; 0; 0; 0; 0; 96; 26; 2; 0; 0; 0; 0; 0; 128; 26; 2; 0; 0; 0; 0; 0; 64; 25; 2; 0; 0; 0; 0; 0; 160; 26; 2; 0; 0; 0; 0; 0; 192; 26; 2; 0; 0; 0; 0; 0; 0; 26; 2; 0; 0; 0; 0; 0; 0; 26; 2; 0; 0; 0; 0; 0; 0; 26; 2; 0; 0; 0; 0; 0; 0; 26; 2; 0; 0; 0; 0; 0; 224; 26; 2; 0; 0; 0; 0; 0].
Definition RO_g_shapes : list byte := map (Z_to_bv 8) [0; 32; 2; 0; 0; 0; 0; 0; 32; 32; 2; 0; 0; 0; 0; 0; 192; 29; 2; 0; 0; 0; 0; 0; 64; 32; 2; 0; 0; 0; 0; 0; 224; 29; 2; 0; 0; 0; 0; 0; 160; 32; 2; 0; 0; 0; 0; 0; 0; 30; 2; 0; 0; 0; 0; 0; 32; 29; 2; 0; 0; 0; 0; 0; 64; 30; 2; 0; 0; 0; 0; 0; 32; 29; 2; 0; 0; 0; 0; 0; 128; 30; 2; 0; 0; 0; 0; 0; 32; 29; 2; 0; 0; 0; 0; 0; 192; 30; 2; 0; 0; 0; 0; 0; 32; 29; 2; 0; 0; 0; 0; 0; 0; 31; 2; 0; 0; 0; 0; 0; 32; 29; 2; 0; 0; 0; 0; 0; 0; 33; 2; 0; 0; 0; 0; 0; 32; 29; 2; 0; 0; 0; 0; 0; 32; 33; 2; 0; 0; 0; 0; 0; 32; 29; 2; 0; 0; 0; 0; 0; 224; 30; 2; 0; 0; 0; 0; 0; 32; 29; 2; 0; 0; 0; 0; 0; 160; 30; 2; 0; 0; 0; 0; 0; 32; 29; 2; 0; 0; 0; 0; 0; 64; 33; 2; 0; 0; 0; 0; 0; 96; 33; 2; 0; 0; 0; 0; 0; 160; 33; 2; 0; 0; 0; 0; 0; 32; 29; 2; 0; 0; 0; 0; 0; 96; 31; 2; 0; 0; 0; 0; 0; 32; 29; 2; 0; 0; 0; 0; 0; 128; 31; 2; 0; 0; 0; 0; 0; 32; 29; 2; 0; 0; 0; 0; 0; 160; 31; 2; 0; 0; 0; 0; 0; 192; 33; 2; 0; 0; 0; 0; 0; 192; 31; 2; 0; 0; 0; 0; 0; 192; 33; 2; 0; 0; 0; 0; 0; 224; 33; 2; 0; 0; 0; 0; 0; 32; 29; 2; 0; 0; 0; 0; 0; 0; 34; 2; 0; 0; 0; 0; 0; 32; 34; 2; 0; 0; 0; 0; 0; 64; 34; 2; 0; 0; 0; 0; 0; 96; 34; 2; 0; 0; 0; 0; 0; 224; 34; 2; 0; 0; 0; 0; 0; 0; 35; 2; 0; 0; 0; 0; 0; 128; 35; 2; 0; 0; 0; 0; 0; 32; 34; 2; 0; 0; 0; 0; 0; 160; 35; 2; 0; 0; 0; 0; 0; 192; 35; 2; 0; 0; 0; 0; 0; 0; 36; 2; 0; 0; 0; 0; 0; 32; 36; 2; 0; 0; 0; 0; 0; 96; 36; 2; 0; 0; 0; 0; 0; 32; 29; 2; 0; 0; 0; 0; 0; 128; 36; 2; 0; 0; 0; 0; 0; 32; 29; 2; 0; 0; 0; 0; 0; 160; 36; 2; 0; 0; 0; 0; 0; 32; 29; 2; 0; 0; 0; 0; 0].
Definition RO_ptr_a5a28 : list byte := map (Z_to_bv 8) [32; 32; 2; 0; 0; 0; 0; 0].
Definition RO_g_instance_info_verbs : list byte := map (Z_to_bv 8) [32; 41; 2; 0; 0; 0; 0; 0; 1; 0; 0; 0; 0; 0; 0; 0; 64; 41; 2; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 96; 41; 2; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 128; 41; 2; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 160; 41; 2; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 192; 41; 2; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 224; 41; 2; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 42; 2; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 32; 42; 2; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 64; 42; 2; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0].
Definition RO_g_instance_verbs : list byte := map (Z_to_bv 8) [32; 37; 2; 0; 0; 0; 0; 0; 96; 42; 2; 0; 0; 0; 0; 0; 160; 42; 2; 0; 0; 0; 0; 0; 192; 42; 2; 0; 0; 0; 0; 0; 0; 43; 2; 0; 0; 0; 0; 0; 32; 43; 2; 0; 0; 0; 0; 0; 96; 37; 2; 0; 0; 0; 0; 0; 96; 43; 2; 0; 0; 0; 0; 0; 128; 43; 2; 0; 0; 0; 0; 0; 160; 43; 2; 0; 0; 0; 0; 0; 224; 43; 2; 0; 0; 0; 0; 0; 32; 44; 2; 0; 0; 0; 0; 0; 96; 44; 2; 0; 0; 0; 0; 0; 160; 44; 2; 0; 0; 0; 0; 0; 0; 45; 2; 0; 0; 0; 0; 0; 32; 45; 2; 0; 0; 0; 0; 0; 96; 45; 2; 0; 0; 0; 0; 0; 160; 45; 2; 0; 0; 0; 0; 0].
Definition RO_ptr_a6bc8 : list byte := map (Z_to_bv 8) [192; 50; 94; 0; 0; 0; 0; 0].
Definition RO_ptr_a6bd0 : list byte := map (Z_to_bv 8) [0; 29; 2; 0; 0; 0; 0; 0].
Definition RO_ptr_a6bd8 : list byte := map (Z_to_bv 8) [224; 27; 2; 0; 0; 0; 0; 0].
Definition RO_ptr_a6be0 : list byte := map (Z_to_bv 8) [224; 55; 94; 0; 0; 0; 0; 0].
Definition cmd_ro_bytes (rd : reader) : Prop :=
abytes_atR rd 0x10330 RO_lit_10330
/\ abytes_atR rd 0x13794 RO_lit_13794
/\ abytes_atR rd 0x15923 RO_lit_15923
/\ abytes_atR rd 0x15fd2 RO_lit_15fd2
/\ abytes_atR rd 0x176c8 RO_lit_176c8
/\ abytes_atR rd 0x17f1b RO_lit_17f1b
/\ abytes_atR rd 0x18ebf RO_lit_18ebf
/\ abytes_atR rd 0x18ed1 RO_lit_18ed1
/\ abytes_atR rd 0x1b056 RO_lit_1b056
/\ abytes_atR rd 0x1b074 RO_lit_1b074
/\ abytes_atR rd 0x1dfad RO_lit_1dfad
/\ abytes_atR rd 0x1ea5a RO_lit_1ea5a
/\ abytes_atR rd 0x1f29a RO_lit_1f29a
/\ abytes_atR rd 0x20814 RO_lit_20814
/\ abytes_atR rd 0x20852 RO_lit_20852
/\ abytes_atR rd 0x210e0 RO_lit_210e0
/\ abytes_atR rd 0x21100 RO_lit_21100
/\ abytes_atR rd 0x21120 RO_lit_21120
/\ abytes_atR rd 0x21140 RO_lit_21140
/\ abytes_atR rd 0x21160 RO_lit_21160
/\ abytes_atR rd 0x21180 RO_lit_21180
/\ abytes_atR rd 0x211a0 RO_lit_211a0
/\ abytes_atR rd 0x211c0 RO_lit_211c0
/\ abytes_atR rd 0x211e0 RO_lit_211e0
/\ abytes_atR rd 0x21220 RO_lit_21220
/\ abytes_atR rd 0x21240 RO_lit_21240
/\ abytes_atR rd 0x212a0 RO_lit_212a0
/\ abytes_atR rd 0x212c0 RO_lit_212c0
/\ abytes_atR rd 0x212e0 RO_lit_212e0
/\ abytes_atR rd 0x21300 RO_lit_21300
/\ abytes_atR rd 0x21320 RO_lit_21320
/\ abytes_atR rd 0x21360 RO_lit_21360
/\ abytes_atR rd 0x213a0 RO_lit_213a0
/\ abytes_atR rd 0x213e0 RO_lit_213e0
/\ abytes_atR rd 0x21420 RO_lit_21420
/\ abytes_atR rd 0x21440 RO_lit_21440
/\ abytes_atR rd 0x21480 RO_lit_21480
/\ abytes_atR rd 0x214a0 RO_lit_214a0
/\ abytes_atR rd 0x214e0 RO_lit_214e0
/\ abytes_atR rd 0x21500 RO_lit_21500
/\ abytes_atR rd 0x21560 RO_lit_21560
/\ abytes_atR rd 0x21580 RO_lit_21580
/\ abytes_atR rd 0x21600 RO_lit_21600
/\ abytes_atR rd 0x21620 RO_lit_21620
/\ abytes_atR rd 0x21640 RO_lit_21640
/\ abytes_atR rd 0x21660 RO_lit_21660
/\ abytes_atR rd 0x216c0 RO_lit_216c0
/\ abytes_atR rd 0x216e0 RO_lit_216e0
/\ abytes_atR rd 0x21700 RO_lit_21700
/\ abytes_atR rd 0x21740 RO_lit_21740
/\ abytes_atR rd 0x21760 RO_lit_21760
/\ abytes_atR rd 0x217c0 RO_lit_217c0
/\ abytes_atR rd 0x217e0 RO_lit_217e0
/\ abytes_atR rd 0x21800 RO_lit_21800
/\ abytes_atR rd 0x21820 RO_lit_21820
/\ abytes_atR rd 0x21840 RO_lit_21840
/\ abytes_atR rd 0x21860 RO_lit_21860
/\ abytes_atR rd 0x21880 RO_lit_21880
/\ abytes_atR rd 0x218a0 RO_lit_218a0
/\ abytes_atR rd 0x218c0 RO_lit_218c0
/\ abytes_atR rd 0x218e0 RO_lit_218e0
/\ abytes_atR rd 0x21900 RO_lit_21900
/\ abytes_atR rd 0x21920 RO_lit_21920
/\ abytes_atR rd 0x21940 RO_lit_21940
/\ abytes_atR rd 0x21960 RO_lit_21960
/\ abytes_atR rd 0x21980 RO_lit_21980
/\ abytes_atR rd 0x219a0 RO_lit_219a0
/\ abytes_atR rd 0x219c0 RO_lit_219c0
/\ abytes_atR rd 0x219e0 RO_lit_219e0
/\ abytes_atR rd 0x21a00 RO_lit_21a00
/\ abytes_atR rd 0x21a20 RO_lit_21a20
/\ abytes_atR rd 0x21a40 RO_lit_21a40
/\ abytes_atR rd 0x21a60 RO_lit_21a60
/\ abytes_atR rd 0x21a80 RO_lit_21a80
/\ abytes_atR rd 0x21aa0 RO_lit_21aa0
/\ abytes_atR rd 0x21ac0 RO_lit_21ac0
/\ abytes_atR rd 0x21ae0 RO_lit_21ae0
/\ abytes_atR rd 0x21b00 RO_lit_21b00
/\ abytes_atR rd 0x21b20 RO_lit_21b20
/\ abytes_atR rd 0x21b40 RO_lit_21b40
/\ abytes_atR rd 0x21b60 RO_lit_21b60
/\ abytes_atR rd 0x21b80 RO_lit_21b80
/\ abytes_atR rd 0x21ba0 RO_lit_21ba0
/\ abytes_atR rd 0x21be0 RO_rec_codes
/\ abytes_atR rd 0x21d00 RO_rec_ncodes
/\ abytes_atR rd 0x21d20 RO_lit_21d20
/\ abytes_atR rd 0x21d40 RO_lit_21d40
/\ abytes_atR rd 0x21d60 RO_lit_21d60
/\ abytes_atR rd 0x21d80 RO_lit_21d80
/\ abytes_atR rd 0x21da0 RO_lit_21da0
/\ abytes_atR rd 0x21dc0 RO_lit_21dc0
/\ abytes_atR rd 0x21de0 RO_lit_21de0
/\ abytes_atR rd 0x21e00 RO_lit_21e00
/\ abytes_atR rd 0x21e40 RO_lit_21e40
/\ abytes_atR rd 0x21e80 RO_lit_21e80
/\ abytes_atR rd 0x21ea0 RO_lit_21ea0
/\ abytes_atR rd 0x21ec0 RO_lit_21ec0
/\ abytes_atR rd 0x21ee0 RO_lit_21ee0
/\ abytes_atR rd 0x21f00 RO_lit_21f00
/\ abytes_atR rd 0x21f20 RO_lit_21f20
/\ abytes_atR rd 0x21f40 RO_lit_21f40
/\ abytes_atR rd 0x21f60 RO_lit_21f60
/\ abytes_atR rd 0x21f80 RO_lit_21f80
/\ abytes_atR rd 0x21fa0 RO_lit_21fa0
/\ abytes_atR rd 0x21fc0 RO_lit_21fc0
/\ abytes_atR rd 0x21fe0 RO_lit_21fe0
/\ abytes_atR rd 0x22000 RO_lit_22000
/\ abytes_atR rd 0x22020 RO_lit_22020
/\ abytes_atR rd 0x22040 RO_lit_22040
/\ abytes_atR rd 0x220a0 RO_lit_220a0
/\ abytes_atR rd 0x22100 RO_lit_22100
/\ abytes_atR rd 0x22120 RO_lit_22120
/\ abytes_atR rd 0x22140 RO_lit_22140
/\ abytes_atR rd 0x22160 RO_lit_22160
/\ abytes_atR rd 0x221a0 RO_lit_221a0
/\ abytes_atR rd 0x221c0 RO_lit_221c0
/\ abytes_atR rd 0x221e0 RO_lit_221e0
/\ abytes_atR rd 0x22200 RO_lit_22200
/\ abytes_atR rd 0x22220 RO_lit_22220
/\ abytes_atR rd 0x22240 RO_lit_22240
/\ abytes_atR rd 0x22260 RO_lit_22260
/\ abytes_atR rd 0x222e0 RO_lit_222e0
/\ abytes_atR rd 0x22300 RO_lit_22300
/\ abytes_atR rd 0x22380 RO_lit_22380
/\ abytes_atR rd 0x223a0 RO_lit_223a0
/\ abytes_atR rd 0x223c0 RO_lit_223c0
/\ abytes_atR rd 0x22400 RO_lit_22400
/\ abytes_atR rd 0x22420 RO_lit_22420
/\ abytes_atR rd 0x22460 RO_lit_22460
/\ abytes_atR rd 0x22480 RO_lit_22480
/\ abytes_atR rd 0x224a0 RO_lit_224a0
/\ abytes_atR rd 0x224c0 RO_lit_224c0
/\ abytes_atR rd 0x22500 RO_lit_22500
/\ abytes_atR rd 0x22520 RO_lit_22520
/\ abytes_atR rd 0x22560 RO_lit_22560
/\ abytes_atR rd 0x225a0 RO_lit_225a0
/\ abytes_atR rd 0x225c0 RO_lit_225c0
/\ abytes_atR rd 0x225e0 RO_lit_225e0
/\ abytes_atR rd 0x22600 RO_lit_22600
/\ abytes_atR rd 0x22620 RO_lit_22620
/\ abytes_atR rd 0x22640 RO_lit_22640
/\ abytes_atR rd 0x22660 RO_lit_22660
/\ abytes_atR rd 0x226a0 RO_lit_226a0
/\ abytes_atR rd 0x226c0 RO_lit_226c0
/\ abytes_atR rd 0x22700 RO_lit_22700
/\ abytes_atR rd 0x22720 RO_lit_22720
/\ abytes_atR rd 0x22740 RO_lit_22740
/\ abytes_atR rd 0x22760 RO_lit_22760
/\ abytes_atR rd 0x22780 RO_lit_22780
/\ abytes_atR rd 0x227a0 RO_lit_227a0
/\ abytes_atR rd 0x227c0 RO_lit_227c0
/\ abytes_atR rd 0x227e0 RO_lit_227e0
/\ abytes_atR rd 0x22800 RO_lit_22800
/\ abytes_atR rd 0x22820 RO_lit_22820
/\ abytes_atR rd 0x22840 RO_lit_22840
/\ abytes_atR rd 0x22860 RO_lit_22860
/\ abytes_atR rd 0x228a0 RO_lit_228a0
/\ abytes_atR rd 0x228c0 RO_lit_228c0
/\ abytes_atR rd 0x228e0 RO_lit_228e0
/\ abytes_atR rd 0x22900 RO_lit_22900
/\ abytes_atR rd 0x22920 RO_lit_22920
/\ abytes_atR rd 0x22940 RO_lit_22940
/\ abytes_atR rd 0x22960 RO_lit_22960
/\ abytes_atR rd 0x22980 RO_lit_22980
/\ abytes_atR rd 0x229a0 RO_lit_229a0
/\ abytes_atR rd 0x229c0 RO_lit_229c0
/\ abytes_atR rd 0x229e0 RO_lit_229e0
/\ abytes_atR rd 0x22a00 RO_lit_22a00
/\ abytes_atR rd 0x22a20 RO_lit_22a20
/\ abytes_atR rd 0x22a40 RO_lit_22a40
/\ abytes_atR rd 0x22a60 RO_lit_22a60
/\ abytes_atR rd 0x22aa0 RO_lit_22aa0
/\ abytes_atR rd 0x22ac0 RO_lit_22ac0
/\ abytes_atR rd 0x22b00 RO_lit_22b00
/\ abytes_atR rd 0x22b20 RO_lit_22b20
/\ abytes_atR rd 0x22b60 RO_lit_22b60
/\ abytes_atR rd 0x22b80 RO_lit_22b80
/\ abytes_atR rd 0x22ba0 RO_lit_22ba0
/\ abytes_atR rd 0x22be0 RO_lit_22be0
/\ abytes_atR rd 0x22c20 RO_lit_22c20
/\ abytes_atR rd 0x22c60 RO_lit_22c60
/\ abytes_atR rd 0x22ca0 RO_lit_22ca0
/\ abytes_atR rd 0x22d00 RO_lit_22d00
/\ abytes_atR rd 0x22d20 RO_lit_22d20
/\ abytes_atR rd 0x22d60 RO_lit_22d60
/\ abytes_atR rd 0x22da0 RO_lit_22da0
/\ abytes_atR rd 0x22dc0 RO_lit_22dc0
/\ abytes_atR rd 0x86bf8 RO_lit_86bf8
/\ abytes_atR rd 0x86e64 RO_lit_86e64
/\ abytes_atR rd 0x87ae8 RO_lit_87ae8
/\ abytes_atR rd 0x882d8 RO_lit_882d8
/\ abytes_atR rd 0x890e0 RO_lit_890e0
/\ abytes_atR rd 0x8a188 RO_lit_8a188
/\ abytes_atR rd 0x8a400 RO_lit_8a400
/\ abytes_atR rd 0x8aa10 RO_lit_8aa10
/\ abytes_atR rd 0x8af34 RO_lit_8af34
/\ abytes_atR rd 0x8b258 RO_lit_8b258
/\ abytes_atR rd 0x8b53c RO_lit_8b53c
/\ abytes_atR rd 0x8b8f8 RO_lit_8b8f8
/\ abytes_atR rd 0x8bb70 RO_lit_8bb70
/\ abytes_atR rd 0x8bed0 RO_lit_8bed0
/\ abytes_atR rd 0x8c1c4 RO_lit_8c1c4
/\ abytes_atR rd 0x8c570 RO_lit_8c570
/\ abytes_atR rd 0x8c758 RO_lit_8c758
/\ abytes_atR rd 0x8c9f8 RO_lit_8c9f8
/\ abytes_atR rd 0x8ce4c RO_lit_8ce4c
/\ abytes_atR rd 0x8da84 RO_lit_8da84
/\ abytes_atR rd 0x8df2c RO_lit_8df2c
/\ abytes_atR rd 0xa5680 RO_g_parsed
/\ abytes_atR rd 0xa5920 RO_g_call_words
/\ abytes_atR rd 0xa5a20 RO_g_shapes
/\ abytes_atR rd 0xa5a28 RO_ptr_a5a28
/\ abytes_atR rd 0xa5c40 RO_g_instance_info_verbs
/\ abytes_atR rd 0xa5d00 RO_g_instance_verbs
/\ abytes_atR rd 0xa6bc8 RO_ptr_a6bc8
/\ abytes_atR rd 0xa6bd0 RO_ptr_a6bd0
/\ abytes_atR rd 0xa6bd8 RO_ptr_a6bd8
/\ abytes_atR rd 0xa6be0 RO_ptr_a6be0.
Definition cmd_ro_ends : list Z := [0x10338; 0x137b7; 0x15934; 0x15fe6; 0x176d9; 0x17f2a; 0x18ed0; 0x18ee7; 0x1b06b; 0x1b085; 0x1dfd0; 0x1ea7b; 0x1f2ac; 0x2083a; 0x20865; 0x210e2; 0x21107; 0x21126; 0x21144; 0x21161; 0x2118a; 0x211aa; 0x211cd; 0x211f0; 0x21223; 0x2127c; 0x212ab; 0x212c0; 0x212ed; 0x2130a; 0x21330; 0x21370; 0x213b0; 0x213f0; 0x2142a; 0x2145e; 0x2148b; 0x214b6; 0x214ea; 0x21522; 0x21567; 0x215d0; 0x21609; 0x2162b; 0x2164e; 0x2168b; 0x216ca; 0x216e5; 0x2171c; 0x21745; 0x21783; 0x217cb; 0x217e7; 0x2180e; 0x21829; 0x21846; 0x21869; 0x21887; 0x218aa; 0x218c3; 0x218e2; 0x21908; 0x21924; 0x21942; 0x21967; 0x21981; 0x219a5; 0x219c3; 0x219e2; 0x21a01; 0x21a23; 0x21a44; 0x21a65; 0x21a86; 0x21aa4; 0x21ac7; 0x21ae1; 0x21b01; 0x21b23; 0x21b47; 0x21b65; 0x21b83; 0x21ba8; 0x21d26; 0x21d47; 0x21d65; 0x21d81; 0x21da2; 0x21dcb; 0x21ded; 0x21e10; 0x21e50; 0x21e8a; 0x21eaa; 0x21ecb; 0x21eee; 0x21f0a; 0x21f23; 0x21f42; 0x21f65; 0x21f8b; 0x21fae; 0x21fc9; 0x21fe1; 0x22003; 0x2202f; 0x2207c; 0x220d5; 0x22107; 0x22129; 0x2214a; 0x22178; 0x221aa; 0x221cf; 0x221ea; 0x2220c; 0x2222c; 0x2224f; 0x222ae; 0x222ea; 0x22342; 0x2238b; 0x223aa; 0x223d8; 0x2240a; 0x22431; 0x22467; 0x22488; 0x224ad; 0x224c6; 0x22502; 0x22531; 0x22572; 0x225a3; 0x225ce; 0x225e9; 0x22609; 0x2262b; 0x2264d; 0x22670; 0x226a3; 0x226d0; 0x2270a; 0x2272e; 0x2274b; 0x2276a; 0x22785; 0x227ab; 0x227c7; 0x227ea; 0x22809; 0x22824; 0x2284d; 0x22870; 0x228a3; 0x228c7; 0x228e5; 0x22908; 0x2292a; 0x2294c; 0x2296f; 0x2298a; 0x229ab; 0x229ca; 0x229ea; 0x22a07; 0x22a28; 0x22a4d; 0x22a77; 0x22aac; 0x22ad2; 0x22b0f; 0x22b39; 0x22b6f; 0x22b8b; 0x22bb4; 0x22bf6; 0x22c3a; 0x22c70; 0x22cce; 0x22d0e; 0x22d35; 0x22d78; 0x22dae; 0x22dc1; 0x86bff; 0x86e6b; 0x87aef; 0x882df; 0x890e7; 0x8a18f; 0x8a407; 0x8aa17; 0x8af3b; 0x8b25f; 0x8b543; 0x8b8ff; 0x8bb77; 0x8bed7; 0x8c1cb; 0x8c577; 0x8c75f; 0x8c9ff; 0x8ce53; 0x8da8b; 0x8df33].
Definition cmd_ro_tails (rd : reader) : Prop :=
forall e, In e cmd_ro_ends -> forall a, e < a < e - e mod 8 + 8 -> rd a <> None.
Definition cmd_ro_ok (rd : reader) : Prop := cmd_ro_bytes rd /\ cmd_ro_tails rd.
Definition cmd_ro_in (ro : Z -> Prop) : Prop :=
(forall i, 0 <= i < 9 -> ro (0x10330 + i))
/\ (forall i, 0 <= i < 36 -> ro (0x13794 + i))
/\ (forall i, 0 <= i < 18 -> ro (0x15923 + i))
/\ (forall i, 0 <= i < 21 -> ro (0x15fd2 + i))
/\ (forall i, 0 <= i < 18 -> ro (0x176c8 + i))
/\ (forall i, 0 <= i < 16 -> ro (0x17f1b + i))
/\ (forall i, 0 <= i < 18 -> ro (0x18ebf + i))
/\ (forall i, 0 <= i < 23 -> ro (0x18ed1 + i))
/\ (forall i, 0 <= i < 22 -> ro (0x1b056 + i))
/\ (forall i, 0 <= i < 18 -> ro (0x1b074 + i))
/\ (forall i, 0 <= i < 36 -> ro (0x1dfad + i))
/\ (forall i, 0 <= i < 34 -> ro (0x1ea5a + i))
/\ (forall i, 0 <= i < 19 -> ro (0x1f29a + i))
/\ (forall i, 0 <= i < 39 -> ro (0x20814 + i))
/\ (forall i, 0 <= i < 20 -> ro (0x20852 + i))
/\ (forall i, 0 <= i < 3 -> ro (0x210e0 + i))
/\ (forall i, 0 <= i < 8 -> ro (0x21100 + i))
/\ (forall i, 0 <= i < 7 -> ro (0x21120 + i))
/\ (forall i, 0 <= i < 5 -> ro (0x21140 + i))
/\ (forall i, 0 <= i < 2 -> ro (0x21160 + i))
/\ (forall i, 0 <= i < 11 -> ro (0x21180 + i))
/\ (forall i, 0 <= i < 11 -> ro (0x211a0 + i))
/\ (forall i, 0 <= i < 14 -> ro (0x211c0 + i))
/\ (forall i, 0 <= i < 17 -> ro (0x211e0 + i))
/\ (forall i, 0 <= i < 4 -> ro (0x21220 + i))
/\ (forall i, 0 <= i < 61 -> ro (0x21240 + i))
/\ (forall i, 0 <= i < 12 -> ro (0x212a0 + i))
/\ (forall i, 0 <= i < 1 -> ro (0x212c0 + i))
/\ (forall i, 0 <= i < 14 -> ro (0x212e0 + i))
/\ (forall i, 0 <= i < 11 -> ro (0x21300 + i))
/\ (forall i, 0 <= i < 17 -> ro (0x21320 + i))
/\ (forall i, 0 <= i < 17 -> ro (0x21360 + i))
/\ (forall i, 0 <= i < 17 -> ro (0x213a0 + i))
/\ (forall i, 0 <= i < 17 -> ro (0x213e0 + i))
/\ (forall i, 0 <= i < 11 -> ro (0x21420 + i))
/\ (forall i, 0 <= i < 31 -> ro (0x21440 + i))
/\ (forall i, 0 <= i < 12 -> ro (0x21480 + i))
/\ (forall i, 0 <= i < 23 -> ro (0x214a0 + i))
/\ (forall i, 0 <= i < 11 -> ro (0x214e0 + i))
/\ (forall i, 0 <= i < 35 -> ro (0x21500 + i))
/\ (forall i, 0 <= i < 8 -> ro (0x21560 + i))
/\ (forall i, 0 <= i < 81 -> ro (0x21580 + i))
/\ (forall i, 0 <= i < 10 -> ro (0x21600 + i))
/\ (forall i, 0 <= i < 12 -> ro (0x21620 + i))
/\ (forall i, 0 <= i < 15 -> ro (0x21640 + i))
/\ (forall i, 0 <= i < 44 -> ro (0x21660 + i))
/\ (forall i, 0 <= i < 11 -> ro (0x216c0 + i))
/\ (forall i, 0 <= i < 6 -> ro (0x216e0 + i))
/\ (forall i, 0 <= i < 29 -> ro (0x21700 + i))
/\ (forall i, 0 <= i < 6 -> ro (0x21740 + i))
/\ (forall i, 0 <= i < 36 -> ro (0x21760 + i))
/\ (forall i, 0 <= i < 12 -> ro (0x217c0 + i))
/\ (forall i, 0 <= i < 8 -> ro (0x217e0 + i))
/\ (forall i, 0 <= i < 15 -> ro (0x21800 + i))
/\ (forall i, 0 <= i < 10 -> ro (0x21820 + i))
/\ (forall i, 0 <= i < 7 -> ro (0x21840 + i))
/\ (forall i, 0 <= i < 10 -> ro (0x21860 + i))
/\ (forall i, 0 <= i < 8 -> ro (0x21880 + i))
/\ (forall i, 0 <= i < 11 -> ro (0x218a0 + i))
/\ (forall i, 0 <= i < 4 -> ro (0x218c0 + i))
/\ (forall i, 0 <= i < 3 -> ro (0x218e0 + i))
/\ (forall i, 0 <= i < 9 -> ro (0x21900 + i))
/\ (forall i, 0 <= i < 5 -> ro (0x21920 + i))
/\ (forall i, 0 <= i < 3 -> ro (0x21940 + i))
/\ (forall i, 0 <= i < 8 -> ro (0x21960 + i))
/\ (forall i, 0 <= i < 2 -> ro (0x21980 + i))
/\ (forall i, 0 <= i < 6 -> ro (0x219a0 + i))
/\ (forall i, 0 <= i < 4 -> ro (0x219c0 + i))
/\ (forall i, 0 <= i < 3 -> ro (0x219e0 + i))
/\ (forall i, 0 <= i < 2 -> ro (0x21a00 + i))
/\ (forall i, 0 <= i < 4 -> ro (0x21a20 + i))
/\ (forall i, 0 <= i < 5 -> ro (0x21a40 + i))
/\ (forall i, 0 <= i < 6 -> ro (0x21a60 + i))
/\ (forall i, 0 <= i < 7 -> ro (0x21a80 + i))
/\ (forall i, 0 <= i < 5 -> ro (0x21aa0 + i))
/\ (forall i, 0 <= i < 8 -> ro (0x21ac0 + i))
/\ (forall i, 0 <= i < 2 -> ro (0x21ae0 + i))
/\ (forall i, 0 <= i < 2 -> ro (0x21b00 + i))
/\ (forall i, 0 <= i < 4 -> ro (0x21b20 + i))
/\ (forall i, 0 <= i < 8 -> ro (0x21b40 + i))
/\ (forall i, 0 <= i < 6 -> ro (0x21b60 + i))
/\ (forall i, 0 <= i < 4 -> ro (0x21b80 + i))
/\ (forall i, 0 <= i < 9 -> ro (0x21ba0 + i))
/\ (forall i, 0 <= i < 232 -> ro (0x21be0 + i))
/\ (forall i, 0 <= i < 4 -> ro (0x21d00 + i))
/\ (forall i, 0 <= i < 7 -> ro (0x21d20 + i))
/\ (forall i, 0 <= i < 8 -> ro (0x21d40 + i))
/\ (forall i, 0 <= i < 6 -> ro (0x21d60 + i))
/\ (forall i, 0 <= i < 2 -> ro (0x21d80 + i))
/\ (forall i, 0 <= i < 3 -> ro (0x21da0 + i))
/\ (forall i, 0 <= i < 12 -> ro (0x21dc0 + i))
/\ (forall i, 0 <= i < 14 -> ro (0x21de0 + i))
/\ (forall i, 0 <= i < 17 -> ro (0x21e00 + i))
/\ (forall i, 0 <= i < 17 -> ro (0x21e40 + i))
/\ (forall i, 0 <= i < 11 -> ro (0x21e80 + i))
/\ (forall i, 0 <= i < 11 -> ro (0x21ea0 + i))
/\ (forall i, 0 <= i < 12 -> ro (0x21ec0 + i))
/\ (forall i, 0 <= i < 15 -> ro (0x21ee0 + i))
/\ (forall i, 0 <= i < 11 -> ro (0x21f00 + i))
/\ (forall i, 0 <= i < 4 -> ro (0x21f20 + i))
/\ (forall i, 0 <= i < 3 -> ro (0x21f40 + i))
/\ (forall i, 0 <= i < 6 -> ro (0x21f60 + i))
/\ (forall i, 0 <= i < 12 -> ro (0x21f80 + i))
/\ (forall i, 0 <= i < 15 -> ro (0x21fa0 + i))
/\ (forall i, 0 <= i < 10 -> ro (0x21fc0 + i))
/\ (forall i, 0 <= i < 2 -> ro (0x21fe0 + i))
/\ (forall i, 0 <= i < 4 -> ro (0x22000 + i))
/\ (forall i, 0 <= i < 16 -> ro (0x22020 + i))
/\ (forall i, 0 <= i < 61 -> ro (0x22040 + i))
/\ (forall i, 0 <= i < 54 -> ro (0x220a0 + i))
/\ (forall i, 0 <= i < 8 -> ro (0x22100 + i))
/\ (forall i, 0 <= i < 10 -> ro (0x22120 + i))
/\ (forall i, 0 <= i < 11 -> ro (0x22140 + i))
/\ (forall i, 0 <= i < 25 -> ro (0x22160 + i))
/\ (forall i, 0 <= i < 11 -> ro (0x221a0 + i))
/\ (forall i, 0 <= i < 16 -> ro (0x221c0 + i))
/\ (forall i, 0 <= i < 11 -> ro (0x221e0 + i))
/\ (forall i, 0 <= i < 13 -> ro (0x22200 + i))
/\ (forall i, 0 <= i < 13 -> ro (0x22220 + i))
/\ (forall i, 0 <= i < 16 -> ro (0x22240 + i))
/\ (forall i, 0 <= i < 79 -> ro (0x22260 + i))
/\ (forall i, 0 <= i < 11 -> ro (0x222e0 + i))
/\ (forall i, 0 <= i < 67 -> ro (0x22300 + i))
/\ (forall i, 0 <= i < 12 -> ro (0x22380 + i))
/\ (forall i, 0 <= i < 11 -> ro (0x223a0 + i))
/\ (forall i, 0 <= i < 25 -> ro (0x223c0 + i))
/\ (forall i, 0 <= i < 11 -> ro (0x22400 + i))
/\ (forall i, 0 <= i < 18 -> ro (0x22420 + i))
/\ (forall i, 0 <= i < 8 -> ro (0x22460 + i))
/\ (forall i, 0 <= i < 9 -> ro (0x22480 + i))
/\ (forall i, 0 <= i < 14 -> ro (0x224a0 + i))
/\ (forall i, 0 <= i < 7 -> ro (0x224c0 + i))
/\ (forall i, 0 <= i < 3 -> ro (0x22500 + i))
/\ (forall i, 0 <= i < 18 -> ro (0x22520 + i))
/\ (forall i, 0 <= i < 19 -> ro (0x22560 + i))
/\ (forall i, 0 <= i < 4 -> ro (0x225a0 + i))
/\ (forall i, 0 <= i < 15 -> ro (0x225c0 + i))
/\ (forall i, 0 <= i < 10 -> ro (0x225e0 + i))
/\ (forall i, 0 <= i < 10 -> ro (0x22600 + i))
/\ (forall i, 0 <= i < 12 -> ro (0x22620 + i))
/\ (forall i, 0 <= i < 14 -> ro (0x22640 + i))
/\ (forall i, 0 <= i < 17 -> ro (0x22660 + i))
/\ (forall i, 0 <= i < 4 -> ro (0x226a0 + i))
/\ (forall i, 0 <= i < 17 -> ro (0x226c0 + i))
/\ (forall i, 0 <= i < 11 -> ro (0x22700 + i))
/\ (forall i, 0 <= i < 15 -> ro (0x22720 + i))
/\ (forall i, 0 <= i < 12 -> ro (0x22740 + i))
/\ (forall i, 0 <= i < 11 -> ro (0x22760 + i))
/\ (forall i, 0 <= i < 6 -> ro (0x22780 + i))
/\ (forall i, 0 <= i < 12 -> ro (0x227a0 + i))
/\ (forall i, 0 <= i < 8 -> ro (0x227c0 + i))
/\ (forall i, 0 <= i < 11 -> ro (0x227e0 + i))
/\ (forall i, 0 <= i < 10 -> ro (0x22800 + i))
/\ (forall i, 0 <= i < 5 -> ro (0x22820 + i))
/\ (forall i, 0 <= i < 14 -> ro (0x22840 + i))
/\ (forall i, 0 <= i < 17 -> ro (0x22860 + i))
/\ (forall i, 0 <= i < 4 -> ro (0x228a0 + i))
/\ (forall i, 0 <= i < 8 -> ro (0x228c0 + i))
/\ (forall i, 0 <= i < 6 -> ro (0x228e0 + i))
/\ (forall i, 0 <= i < 9 -> ro (0x22900 + i))
/\ (forall i, 0 <= i < 11 -> ro (0x22920 + i))
/\ (forall i, 0 <= i < 13 -> ro (0x22940 + i))
/\ (forall i, 0 <= i < 16 -> ro (0x22960 + i))
/\ (forall i, 0 <= i < 11 -> ro (0x22980 + i))
/\ (forall i, 0 <= i < 12 -> ro (0x229a0 + i))
/\ (forall i, 0 <= i < 11 -> ro (0x229c0 + i))
/\ (forall i, 0 <= i < 11 -> ro (0x229e0 + i))
/\ (forall i, 0 <= i < 8 -> ro (0x22a00 + i))
/\ (forall i, 0 <= i < 9 -> ro (0x22a20 + i))
/\ (forall i, 0 <= i < 14 -> ro (0x22a40 + i))
/\ (forall i, 0 <= i < 24 -> ro (0x22a60 + i))
/\ (forall i, 0 <= i < 13 -> ro (0x22aa0 + i))
/\ (forall i, 0 <= i < 19 -> ro (0x22ac0 + i))
/\ (forall i, 0 <= i < 16 -> ro (0x22b00 + i))
/\ (forall i, 0 <= i < 26 -> ro (0x22b20 + i))
/\ (forall i, 0 <= i < 16 -> ro (0x22b60 + i))
/\ (forall i, 0 <= i < 12 -> ro (0x22b80 + i))
/\ (forall i, 0 <= i < 21 -> ro (0x22ba0 + i))
/\ (forall i, 0 <= i < 23 -> ro (0x22be0 + i))
/\ (forall i, 0 <= i < 27 -> ro (0x22c20 + i))
/\ (forall i, 0 <= i < 17 -> ro (0x22c60 + i))
/\ (forall i, 0 <= i < 47 -> ro (0x22ca0 + i))
/\ (forall i, 0 <= i < 15 -> ro (0x22d00 + i))
/\ (forall i, 0 <= i < 22 -> ro (0x22d20 + i))
/\ (forall i, 0 <= i < 25 -> ro (0x22d60 + i))
/\ (forall i, 0 <= i < 15 -> ro (0x22da0 + i))
/\ (forall i, 0 <= i < 2 -> ro (0x22dc0 + i))
/\ (forall i, 0 <= i < 8 -> ro (0x86bf8 + i))
/\ (forall i, 0 <= i < 8 -> ro (0x86e64 + i))
/\ (forall i, 0 <= i < 8 -> ro (0x87ae8 + i))
/\ (forall i, 0 <= i < 8 -> ro (0x882d8 + i))
/\ (forall i, 0 <= i < 8 -> ro (0x890e0 + i))
/\ (forall i, 0 <= i < 8 -> ro (0x8a188 + i))
/\ (forall i, 0 <= i < 8 -> ro (0x8a400 + i))
/\ (forall i, 0 <= i < 8 -> ro (0x8aa10 + i))
/\ (forall i, 0 <= i < 8 -> ro (0x8af34 + i))
/\ (forall i, 0 <= i < 8 -> ro (0x8b258 + i))
/\ (forall i, 0 <= i < 8 -> ro (0x8b53c + i))
/\ (forall i, 0 <= i < 8 -> ro (0x8b8f8 + i))
/\ (forall i, 0 <= i < 8 -> ro (0x8bb70 + i))
/\ (forall i, 0 <= i < 8 -> ro (0x8bed0 + i))
/\ (forall i, 0 <= i < 8 -> ro (0x8c1c4 + i))
/\ (forall i, 0 <= i < 8 -> ro (0x8c570 + i))
/\ (forall i, 0 <= i < 8 -> ro (0x8c758 + i))
/\ (forall i, 0 <= i < 8 -> ro (0x8c9f8 + i))
/\ (forall i, 0 <= i < 8 -> ro (0x8ce4c + i))
/\ (forall i, 0 <= i < 8 -> ro (0x8da84 + i))
/\ (forall i, 0 <= i < 8 -> ro (0x8df2c + i))
/\ (forall i, 0 <= i < 528 -> ro (0xa5680 + i))
/\ (forall i, 0 <= i < 208 -> ro (0xa5920 + i))
/\ (forall i, 0 <= i < 448 -> ro (0xa5a20 + i))
/\ (forall i, 0 <= i < 8 -> ro (0xa5a28 + i))
/\ (forall i, 0 <= i < 160 -> ro (0xa5c40 + i))
/\ (forall i, 0 <= i < 144 -> ro (0xa5d00 + i))
/\ (forall i, 0 <= i < 8 -> ro (0xa6bc8 + i))
/\ (forall i, 0 <= i < 8 -> ro (0xa6bd0 + i))
/\ (forall i, 0 <= i < 8 -> ro (0xa6bd8 + i))
/\ (forall i, 0 <= i < 8 -> ro (0xa6be0 + i)).
