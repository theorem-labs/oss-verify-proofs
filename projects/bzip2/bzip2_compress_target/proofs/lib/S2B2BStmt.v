(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require Import PropExec ShapeAlg.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import MState Mem Cells Step Frame Image.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Heap Require Import AllocIface.
From Stdlib Require Lia. Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require Import ACeil RunW.
(* [comment removed for export] *)
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import CpsOpen.
Section ACeilS1. Context {ACEIL__ : ACeil} {RUNW__ : RunW}.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Record B2BImg := {
  bi_entry   : Z;      (* [comment removed for export] *)
  bi_crc     : Z;      (* [comment removed for export] *)
  bi_rnums   : Z;      (* [comment removed for export] *)
  bi_got     : Z;      (* [comment removed for export] *)
  bi_stderrp : Z       (* [comment removed for export] *)
}.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition b2b_got (segs : list Segment) (I : B2BImg) (m : word -> option byte) (g1 sv : word) : Prop :=
  rw_cells segs m (bi_got I) [C8 (Z_to_bv 64 (bi_stderrp I)); C8 g1; C8 (Z_to_bv 64 (bi_crc I)); C8 (Z_to_bv 64 (bi_rnums I))]
  /\ rw_cells segs m (bi_stderrp I) [C8 sv].

Definition CRC_BYTES : nat := 1024.
Definition RNUMS_BYTES : nat := 2048.

(* [comment removed for export] *)
Definition crc_table_Z : list Z :=
  [0; 0; 0; 0; 183; 29; 193; 4; 110; 59; 130; 9; 217; 38; 67; 13; 220; 118; 4; 19; 107; 107; 197; 23; 178; 77; 134; 26; 5; 80; 71; 30;
   184; 237; 8; 38; 15; 240; 201; 34; 214; 214; 138; 47; 97; 203; 75; 43; 100; 155; 12; 53; 211; 134; 205; 49; 10; 160; 142; 60; 189; 189; 79; 56;
   112; 219; 17; 76; 199; 198; 208; 72; 30; 224; 147; 69; 169; 253; 82; 65; 172; 173; 21; 95; 27; 176; 212; 91; 194; 150; 151; 86; 117; 139; 86; 82;
   200; 54; 25; 106; 127; 43; 216; 110; 166; 13; 155; 99; 17; 16; 90; 103; 20; 64; 29; 121; 163; 93; 220; 125; 122; 123; 159; 112; 205; 102; 94; 116;
   224; 182; 35; 152; 87; 171; 226; 156; 142; 141; 161; 145; 57; 144; 96; 149; 60; 192; 39; 139; 139; 221; 230; 143; 82; 251; 165; 130; 229; 230; 100; 134;
   88; 91; 43; 190; 239; 70; 234; 186; 54; 96; 169; 183; 129; 125; 104; 179; 132; 45; 47; 173; 51; 48; 238; 169; 234; 22; 173; 164; 93; 11; 108; 160;
   144; 109; 50; 212; 39; 112; 243; 208; 254; 86; 176; 221; 73; 75; 113; 217; 76; 27; 54; 199; 251; 6; 247; 195; 34; 32; 180; 206; 149; 61; 117; 202;
   40; 128; 58; 242; 159; 157; 251; 246; 70; 187; 184; 251; 241; 166; 121; 255; 244; 246; 62; 225; 67; 235; 255; 229; 154; 205; 188; 232; 45; 208; 125; 236;
   119; 112; 134; 52; 192; 109; 71; 48; 25; 75; 4; 61; 174; 86; 197; 57; 171; 6; 130; 39; 28; 27; 67; 35; 197; 61; 0; 46; 114; 32; 193; 42;
   207; 157; 142; 18; 120; 128; 79; 22; 161; 166; 12; 27; 22; 187; 205; 31; 19; 235; 138; 1; 164; 246; 75; 5; 125; 208; 8; 8; 202; 205; 201; 12;
   7; 171; 151; 120; 176; 182; 86; 124; 105; 144; 21; 113; 222; 141; 212; 117; 219; 221; 147; 107; 108; 192; 82; 111; 181; 230; 17; 98; 2; 251; 208; 102;
   191; 70; 159; 94; 8; 91; 94; 90; 209; 125; 29; 87; 102; 96; 220; 83; 99; 48; 155; 77; 212; 45; 90; 73; 13; 11; 25; 68; 186; 22; 216; 64;
   151; 198; 165; 172; 32; 219; 100; 168; 249; 253; 39; 165; 78; 224; 230; 161; 75; 176; 161; 191; 252; 173; 96; 187; 37; 139; 35; 182; 146; 150; 226; 178;
   47; 43; 173; 138; 152; 54; 108; 142; 65; 16; 47; 131; 246; 13; 238; 135; 243; 93; 169; 153; 68; 64; 104; 157; 157; 102; 43; 144; 42; 123; 234; 148;
   231; 29; 180; 224; 80; 0; 117; 228; 137; 38; 54; 233; 62; 59; 247; 237; 59; 107; 176; 243; 140; 118; 113; 247; 85; 80; 50; 250; 226; 77; 243; 254;
   95; 240; 188; 198; 232; 237; 125; 194; 49; 203; 62; 207; 134; 214; 255; 203; 131; 134; 184; 213; 52; 155; 121; 209; 237; 189; 58; 220; 90; 160; 251; 216;
   238; 224; 12; 105; 89; 253; 205; 109; 128; 219; 142; 96; 55; 198; 79; 100; 50; 150; 8; 122; 133; 139; 201; 126; 92; 173; 138; 115; 235; 176; 75; 119;
   86; 13; 4; 79; 225; 16; 197; 75; 56; 54; 134; 70; 143; 43; 71; 66; 138; 123; 0; 92; 61; 102; 193; 88; 228; 64; 130; 85; 83; 93; 67; 81;
   158; 59; 29; 37; 41; 38; 220; 33; 240; 0; 159; 44; 71; 29; 94; 40; 66; 77; 25; 54; 245; 80; 216; 50; 44; 118; 155; 63; 155; 107; 90; 59;
   38; 214; 21; 3; 145; 203; 212; 7; 72; 237; 151; 10; 255; 240; 86; 14; 250; 160; 17; 16; 77; 189; 208; 20; 148; 155; 147; 25; 35; 134; 82; 29;
   14; 86; 47; 241; 185; 75; 238; 245; 96; 109; 173; 248; 215; 112; 108; 252; 210; 32; 43; 226; 101; 61; 234; 230; 188; 27; 169; 235; 11; 6; 104; 239;
   182; 187; 39; 215; 1; 166; 230; 211; 216; 128; 165; 222; 111; 157; 100; 218; 106; 205; 35; 196; 221; 208; 226; 192; 4; 246; 161; 205; 179; 235; 96; 201;
   126; 141; 62; 189; 201; 144; 255; 185; 16; 182; 188; 180; 167; 171; 125; 176; 162; 251; 58; 174; 21; 230; 251; 170; 204; 192; 184; 167; 123; 221; 121; 163;
   198; 96; 54; 155; 113; 125; 247; 159; 168; 91; 180; 146; 31; 70; 117; 150; 26; 22; 50; 136; 173; 11; 243; 140; 116; 45; 176; 129; 195; 48; 113; 133;
   153; 144; 138; 93; 46; 141; 75; 89; 247; 171; 8; 84; 64; 182; 201; 80; 69; 230; 142; 78; 242; 251; 79; 74; 43; 221; 12; 71; 156; 192; 205; 67;
   33; 125; 130; 123; 150; 96; 67; 127; 79; 70; 0; 114; 248; 91; 193; 118; 253; 11; 134; 104; 74; 22; 71; 108; 147; 48; 4; 97; 36; 45; 197; 101;
   233; 75; 155; 17; 94; 86; 90; 21; 135; 112; 25; 24; 48; 109; 216; 28; 53; 61; 159; 2; 130; 32; 94; 6; 91; 6; 29; 11; 236; 27; 220; 15;
   81; 166; 147; 55; 230; 187; 82; 51; 63; 157; 17; 62; 136; 128; 208; 58; 141; 208; 151; 36; 58; 205; 86; 32; 227; 235; 21; 45; 84; 246; 212; 41;
   121; 38; 169; 197; 206; 59; 104; 193; 23; 29; 43; 204; 160; 0; 234; 200; 165; 80; 173; 214; 18; 77; 108; 210; 203; 107; 47; 223; 124; 118; 238; 219;
   193; 203; 161; 227; 118; 214; 96; 231; 175; 240; 35; 234; 24; 237; 226; 238; 29; 189; 165; 240; 170; 160; 100; 244; 115; 134; 39; 249; 196; 155; 230; 253;
   9; 253; 184; 137; 190; 224; 121; 141; 103; 198; 58; 128; 208; 219; 251; 132; 213; 139; 188; 154; 98; 150; 125; 158; 187; 176; 62; 147; 12; 173; 255; 151;
   177; 16; 176; 175; 6; 13; 113; 171; 223; 43; 50; 166; 104; 54; 243; 162; 109; 102; 180; 188; 218; 123; 117; 184; 3; 93; 54; 181; 180; 64; 247; 177 ]%Z.

Definition rnums_table_Z : list Z :=
  [107; 2; 0; 0; 208; 2; 0; 0; 127; 0; 0; 0; 225; 1; 0; 0; 163; 3; 0; 0; 48; 3; 0; 0; 45; 3; 0; 0; 233; 0; 0; 0;
   54; 2; 0; 0; 247; 0; 0; 0; 217; 3; 0; 0; 212; 2; 0; 0; 205; 0; 0; 0; 198; 1; 0; 0; 95; 3; 0; 0; 235; 1; 0; 0;
   229; 2; 0; 0; 242; 0; 0; 0; 181; 3; 0; 0; 214; 0; 0; 0; 221; 2; 0; 0; 91; 3; 0; 0; 79; 1; 0; 0; 196; 2; 0; 0;
   109; 2; 0; 0; 62; 2; 0; 0; 73; 0; 0; 0; 142; 2; 0; 0; 218; 2; 0; 0; 216; 1; 0; 0; 163; 1; 0; 0; 180; 1; 0; 0;
   22; 1; 0; 0; 240; 1; 0; 0; 99; 3; 0; 0; 210; 0; 0; 0; 143; 1; 0; 0; 168; 2; 0; 0; 224; 1; 0; 0; 51; 0; 0; 0;
   110; 3; 0; 0; 209; 1; 0; 0; 43; 3; 0; 0; 169; 0; 0; 0; 101; 3; 0; 0; 163; 2; 0; 0; 99; 2; 0; 0; 185; 2; 0; 0;
   99; 3; 0; 0; 49; 2; 0; 0; 94; 3; 0; 0; 175; 2; 0; 0; 251; 1; 0; 0; 27; 1; 0; 0; 226; 1; 0; 0; 129; 0; 0; 0;
   39; 3; 0; 0; 79; 2; 0; 0; 221; 2; 0; 0; 111; 2; 0; 0; 150; 0; 0; 0; 238; 0; 0; 0; 59; 0; 0; 0; 123; 1; 0; 0;
   172; 2; 0; 0; 109; 3; 0; 0; 113; 2; 0; 0; 169; 0; 0; 0; 131; 2; 0; 0; 105; 0; 0; 0; 170; 0; 0; 0; 95; 2; 0; 0;
   8; 2; 0; 0; 164; 3; 0; 0; 215; 2; 0; 0; 220; 1; 0; 0; 181; 2; 0; 0; 169; 1; 0; 0; 174; 0; 0; 0; 135; 2; 0; 0;
   73; 0; 0; 0; 122; 0; 0; 0; 79; 1; 0; 0; 18; 2; 0; 0; 186; 1; 0; 0; 85; 3; 0; 0; 183; 2; 0; 0; 249; 0; 0; 0;
   189; 1; 0; 0; 3; 2; 0; 0; 141; 3; 0; 0; 33; 2; 0; 0; 191; 2; 0; 0; 151; 3; 0; 0; 106; 3; 0; 0; 218; 1; 0; 0;
   114; 3; 0; 0; 244; 1; 0; 0; 82; 2; 0; 0; 100; 2; 0; 0; 129; 2; 0; 0; 33; 3; 0; 0; 220; 0; 0; 0; 162; 0; 0; 0;
   51; 3; 0; 0; 216; 3; 0; 0; 77; 2; 0; 0; 1; 2; 0; 0; 239; 1; 0; 0; 31; 3; 0; 0; 161; 0; 0; 0; 92; 2; 0; 0;
   190; 3; 0; 0; 21; 2; 0; 0; 221; 0; 0; 0; 144; 1; 0; 0; 130; 1; 0; 0; 99; 3; 0; 0; 88; 2; 0; 0; 14; 3; 0; 0;
   126; 1; 0; 0; 84; 2; 0; 0; 158; 1; 0; 0; 171; 0; 0; 0; 4; 2; 0; 0; 119; 1; 0; 0; 170; 2; 0; 0; 229; 1; 0; 0;
   143; 3; 0; 0; 20; 1; 0; 0; 98; 0; 0; 0; 41; 2; 0; 0; 163; 0; 0; 0; 98; 1; 0; 0; 154; 2; 0; 0; 165; 3; 0; 0;
   168; 1; 0; 0; 85; 1; 0; 0; 21; 2; 0; 0; 102; 3; 0; 0; 227; 0; 0; 0; 218; 2; 0; 0; 219; 1; 0; 0; 186; 0; 0; 0;
   7; 1; 0; 0; 135; 2; 0; 0; 25; 2; 0; 0; 174; 2; 0; 0; 88; 2; 0; 0; 224; 0; 0; 0; 213; 1; 0; 0; 68; 0; 0; 0;
   2; 3; 0; 0; 151; 3; 0; 0; 190; 0; 0; 0; 117; 1; 0; 0; 38; 1; 0; 0; 54; 3; 0; 0; 40; 3; 0; 0; 206; 0; 0; 0;
   184; 0; 0; 0; 175; 3; 0; 0; 27; 3; 0; 0; 128; 1; 0; 0; 127; 1; 0; 0; 205; 1; 0; 0; 148; 1; 0; 0; 246; 2; 0; 0;
   71; 3; 0; 0; 119; 3; 0; 0; 203; 2; 0; 0; 67; 0; 0; 0; 106; 2; 0; 0; 20; 1; 0; 0; 204; 0; 0; 0; 150; 3; 0; 0;
   105; 3; 0; 0; 9; 3; 0; 0; 92; 2; 0; 0; 48; 2; 0; 0; 183; 3; 0; 0; 160; 0; 0; 0; 66; 2; 0; 0; 210; 2; 0; 0;
   79; 0; 0; 0; 36; 3; 0; 0; 96; 0; 0; 0; 153; 1; 0; 0; 201; 2; 0; 0; 172; 3; 0; 0; 140; 2; 0; 0; 166; 3; 0; 0;
   202; 3; 0; 0; 191; 1; 0; 0; 62; 1; 0; 0; 97; 1; 0; 0; 91; 3; 0; 0; 160; 2; 0; 0; 112; 0; 0; 0; 17; 3; 0; 0;
   133; 2; 0; 0; 95; 3; 0; 0; 35; 3; 0; 0; 94; 1; 0; 0; 139; 0; 0; 0; 93; 0; 0; 0; 98; 1; 0; 0; 99; 0; 0; 0;
   52; 3; 0; 0; 140; 3; 0; 0; 97; 2; 0; 0; 4; 3; 0; 0; 154; 0; 0; 0; 18; 1; 0; 0; 68; 2; 0; 0; 184; 0; 0; 0;
   79; 0; 0; 0; 114; 2; 0; 0; 118; 2; 0; 0; 230; 2; 0; 0; 141; 2; 0; 0; 26; 1; 0; 0; 250; 2; 0; 0; 111; 2; 0; 0;
   168; 2; 0; 0; 81; 0; 0; 0; 159; 3; 0; 0; 114; 2; 0; 0; 21; 3; 0; 0; 125; 0; 0; 0; 155; 1; 0; 0; 9; 2; 0; 0;
   170; 3; 0; 0; 44; 1; 0; 0; 53; 3; 0; 0; 78; 0; 0; 0; 87; 1; 0; 0; 175; 0; 0; 0; 128; 0; 0; 0; 250; 0; 0; 0;
   170; 0; 0; 0; 6; 3; 0; 0; 204; 3; 0; 0; 19; 1; 0; 0; 231; 3; 0; 0; 127; 2; 0; 0; 239; 1; 0; 0; 78; 0; 0; 0;
   96; 1; 0; 0; 126; 0; 0; 0; 89; 3; 0; 0; 188; 3; 0; 0; 102; 1; 0; 0; 107; 2; 0; 0; 68; 2; 0; 0; 124; 0; 0; 0;
   225; 2; 0; 0; 82; 2; 0; 0; 189; 2; 0; 0; 100; 2; 0; 0; 157; 2; 0; 0; 112; 0; 0; 0; 134; 0; 0; 0; 182; 2; 0; 0;
   107; 1; 0; 0; 224; 3; 0; 0; 41; 3; 0; 0; 231; 2; 0; 0; 168; 0; 0; 0; 206; 3; 0; 0; 176; 3; 0; 0; 119; 1; 0; 0;
   236; 2; 0; 0; 52; 0; 0; 0; 88; 2; 0; 0; 235; 2; 0; 0; 130; 2; 0; 0; 182; 0; 0; 0; 94; 3; 0; 0; 81; 0; 0; 0;
   88; 1; 0; 0; 37; 3; 0; 0; 220; 3; 0; 0; 227; 2; 0; 0; 255; 1; 0; 0; 143; 2; 0; 0; 46; 3; 0; 0; 78; 1; 0; 0;
   249; 0; 0; 0; 3; 2; 0; 0; 129; 3; 0; 0; 187; 3; 0; 0; 152; 2; 0; 0; 213; 3; 0; 0; 137; 2; 0; 0; 113; 0; 0; 0;
   206; 3; 0; 0; 203; 1; 0; 0; 125; 3; 0; 0; 228; 0; 0; 0; 177; 1; 0; 0; 69; 3; 0; 0; 41; 2; 0; 0; 12; 1; 0; 0;
   158; 3; 0; 0; 240; 0; 0; 0; 102; 0; 0; 0; 142; 2; 0; 0; 203; 1; 0; 0; 51; 0; 0; 0; 174; 2; 0; 0; 242; 2; 0; 0;
   38; 3; 0; 0; 248; 2; 0; 0; 237; 1; 0; 0; 147; 1; 0; 0; 159; 1; 0; 0; 138; 1; 0; 0; 175; 2; 0; 0; 188; 2; 0; 0;
   178; 3; 0; 0; 158; 2; 0; 0; 144; 2; 0; 0; 98; 2; 0; 0; 226; 2; 0; 0; 136; 1; 0; 0; 248; 2; 0; 0; 31; 3; 0; 0;
   119; 3; 0; 0; 141; 2; 0; 0; 210; 3; 0; 0; 65; 1; 0; 0; 64; 2; 0; 0; 105; 2; 0; 0; 114; 2; 0; 0; 246; 1; 0; 0;
   126; 3; 0; 0; 167; 2; 0; 0; 243; 0; 0; 0; 184; 1; 0; 0; 168; 2; 0; 0; 111; 3; 0; 0; 194; 0; 0; 0; 60; 2; 0; 0;
   128; 2; 0; 0; 212; 2; 0; 0; 158; 3; 0; 0; 56; 0; 0; 0; 204; 0; 0; 0; 188; 2; 0; 0; 195; 2; 0; 0; 151; 0; 0; 0;
   201; 1; 0; 0; 193; 1; 0; 0; 29; 3; 0; 0; 195; 0; 0; 0; 23; 3; 0; 0; 46; 2; 0; 0; 177; 3; 0; 0; 167; 2; 0; 0;
   41; 1; 0; 0; 59; 0; 0; 0; 87; 0; 0; 0; 56; 3; 0; 0; 201; 2; 0; 0; 151; 2; 0; 0; 156; 1; 0; 0; 181; 2; 0; 0;
   86; 1; 0; 0; 94; 2; 0; 0; 134; 0; 0; 0; 108; 0; 0; 0; 59; 2; 0; 0; 108; 1; 0; 0; 119; 2; 0; 0; 212; 0; 0; 0;
   174; 0; 0; 0; 131; 2; 0; 0; 48; 1; 0; 0; 73; 1; 0; 0; 87; 1; 0; 0; 97; 0; 0; 0; 174; 1; 0; 0; 239; 2; 0; 0;
   241; 1; 0; 0; 58; 1; 0; 0; 215; 3; 0; 0; 118; 1; 0; 0; 54; 3; 0; 0; 160; 3; 0; 0; 140; 0; 0; 0; 206; 0; 0; 0;
   73; 0; 0; 0; 7; 1; 0; 0; 212; 3; 0; 0; 224; 2; 0; 0; 108; 3; 0; 0; 222; 1; 0; 0; 174; 1; 0; 0; 49; 1; 0; 0;
   170; 0; 0; 0; 2; 2; 0; 0; 108; 1; 0; 0; 180; 2; 0; 0; 61; 3; 0; 0; 82; 0; 0; 0; 87; 3; 0; 0; 185; 3; 0; 0;
   164; 2; 0; 0; 246; 0; 0; 0; 113; 1; 0; 0; 202; 3; 0; 0; 38; 1; 0; 0; 238; 2; 0; 0; 39; 3; 0; 0; 59; 3; 0; 0;
   150; 0; 0; 0; 22; 3; 0; 0; 32; 1; 0; 0; 155; 3; 0; 0; 36; 3; 0; 0; 122; 1; 0; 0; 215; 0; 0; 0; 60; 3; 0; 0;
   80; 2; 0; 0; 25; 1; 0; 0; 53; 2; 0; 0; 43; 2; 0; 0; 198; 2; 0; 0; 82; 0; 0; 0; 128; 3; 0; 0; 63; 3; 0; 0;
   35; 2; 0; 0; 5; 1; 0; 0; 12; 2; 0; 0; 206; 1; 0; 0; 37; 1; 0; 0; 209; 1; 0; 0; 246; 1; 0; 0; 56; 0; 0; 0;
   149; 2; 0; 0; 53; 3; 0; 0; 208; 3; 0; 0; 223; 3; 0; 0; 146; 2; 0; 0; 101; 3; 0; 0; 137; 3; 0; 0; 246; 2; 0; 0;
   233; 2; 0; 0; 193; 0; 0; 0; 0; 3; 0; 0; 38; 2; 0; 0; 96; 2; 0; 0; 165; 3; 0; 0; 122; 1; 0; 0; 30; 1; 0; 0;
   215; 0; 0; 0; 211; 3; 0; 0; 24; 3; 0; 0; 193; 3; 0; 0; 61; 0; 0; 0; 176; 2; 0; 0; 25; 3; 0; 0; 132; 2; 0; 0;
   218; 3; 0; 0; 147; 1; 0; 0; 106; 0; 0; 0; 110; 1; 0; 0; 137; 3; 0; 0; 132; 2; 0; 0; 116; 1; 0; 0; 55; 2; 0; 0;
   210; 1; 0; 0; 178; 1; 0; 0; 133; 2; 0; 0; 210; 0; 0; 0; 133; 1; 0; 0; 38; 2; 0; 0; 151; 3; 0; 0; 135; 0; 0; 0;
   12; 3; 0; 0; 5; 3; 0; 0; 123; 2; 0; 0; 133; 1; 0; 0; 195; 2; 0; 0; 100; 0; 0; 0; 114; 2; 0; 0; 190; 3; 0; 0;
   165; 0; 0; 0; 248; 1; 0; 0; 152; 3; 0; 0; 176; 0; 0; 0; 193; 0; 0; 0; 201; 2; 0; 0; 89; 3; 0; 0; 9; 1; 0; 0;
   203; 0; 0; 0; 50; 0; 0; 0; 156; 2; 0; 0; 108; 0; 0; 0; 133; 2; 0; 0; 222; 3; 0; 0; 114; 2; 0; 0; 197; 0; 0; 0;
   254; 1; 0; 0; 101; 1; 0; 0; 102; 1; 0; 0; 82; 3; 0; 0; 90; 3; 0; 0; 108; 1; 0; 0; 168; 3; 0; 0; 126; 2; 0; 0 ]%Z.
Definition crc_table_bytes : list byte := map (Z_to_bv 8) crc_table_Z.
Definition rnums_table_bytes : list byte := map (Z_to_bv 8) rnums_table_Z.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition B2B_STACK : Z := 16384.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section Stmt.
  Variable segs : list Segment.
  Variable L : alloc_layout.
  Variable AI : AllocIface segs L.
  Variable I : B2BImg.

  (* [comment removed for export] *)
  Definition b2b_out (dst dn dl : Z) (a : Z) : Prop :=
    (dst <= a < dst + dn) \/ (dl <= a < dl + 4).

  (* [comment removed for export] *)
  Definition b2b_pres (LB : list ablock) (SP : Z) (dst dn dl : Z) (m m' : word -> option byte) : Prop :=
    forall a : Z, 0 <= a < 2 ^ 64 -> client_addr L LB SP a -> ~ b2b_out dst dn dl a ->
      m' (wa a) = m (wa a) /\ (wview segs m (wa a) <> None -> wview segs m' (wa a) <> None).

  (* [comment removed for export] *)
  Definition b2b_post
      (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (LB : list ablock) (m : word -> option byte) (MD : Model)
      (dst dn dl lo B : Z) (g1 sv : word)
      (ms' : machine_state) (MD' : Model) : Prop :=
    exists (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 errv' : word) (m' : word -> option byte)
           (s' : ai_AS AI) (dlv : Z) (junk' : list byte),
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (ret_pc ra) fc None m' (seg_rom segs)
      (* [comment removed for export] *)
      /\ ai_inv AI s' LB m' MD'
      /\ vm_only MD MD'
      /\ mem_inv segs m'
      /\ stk segs m' lo (bv_unsigned sp)
      /\ rw_cells segs m' (errno_cell L) [C4 errv']
      /\ ai_aux AI m' B
      (* [comment removed for export] *)
      /\ b2b_pres LB (bv_unsigned sp) dst dn dl m m'
      (* [comment removed for export] *)
      /\ rw_cells segs m' dst [CB (Z.to_nat dn) junk']
      /\ rw_cells segs m' dl [C4 (Z_to_bv 64 dlv)] /\ 0 <= dlv <= dn
      (* [comment removed for export] *)
      /\ rw_cells segs m' (bi_crc I) [CB CRC_BYTES crc_table_bytes]
      /\ rw_cells segs m' (bi_rnums I) [CB RNUMS_BYTES rnums_table_bytes]
      /\ b2b_got segs I m' g1 sv.

  (* [comment removed for export] *)
  Definition b2b_spec : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (MD : Model)
           (s : ai_AS AI) (LB : list ablock) (p : bid)
           (dst dn dl src len lo B : Z) (payload junk : list byte) (errv g1 sv : word)
           (K : TSet),
      (* [comment removed for export] *)
      a0 = Z_to_bv 64 dst -> a1 = Z_to_bv 64 dl -> a2 = Z_to_bv 64 src ->
      a3 = Z_to_bv 64 len -> a4 = Z_to_bv 64 (len mod 2) -> a5 = Z_to_bv 64 0 ->
      tp = Z_to_bv 64 (al_tp L) ->
      0 <= len < 2 ^ 26 -> dn = 2 * len ->
      (* [comment removed for export] *)
      ai_inv AI s LB m MD ->
      ai_aux AI m B -> bv_unsigned sp <= B ->
      (* [comment removed for export] *)
      In (p, dst, dn) LB ->
      rw_cells segs m dst [CB (Z.to_nat dn) junk] ->
      (* [comment removed for export] *)
      rw_cells segs m dl [C4 (Z_to_bv 64 dn)] ->
      bv_unsigned sp <= dl -> dl + 4 <= 2 ^ 64 -> dl mod 4 = 0 ->   (* [comment removed for export] *)
      dl + 4 <= B ->                        (* [comment removed for export] *)
      src + len <= alloc_ceiling -> src mod 16 = 0 ->   (* [comment removed for export] *)
      bv_unsigned sp + 48 <= 2 ^ 47 ->      (* [comment removed for export] *)
      (* [comment removed for export] *)
      bytes_at segs m src payload -> Z.of_nat (length payload) = len ->
      client_range L LB (bv_unsigned sp) src len ->
      (src + len <= dst \/ dst + dn <= src) -> (src + len <= dl \/ dl + 4 <= src) ->
      (* [comment removed for export] *)
      stk segs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - B2B_STACK ->
      bv_unsigned sp mod 16 = 0 ->
      (* [comment removed for export] *)
      rw_cells segs m (errno_cell L) [C4 errv] ->
      mem_inv segs m ->
      rw_cells segs m (bi_crc I) [CB CRC_BYTES crc_table_bytes] ->
      rw_cells segs m (bi_rnums I) [CB RNUMS_BYTES rnums_table_bytes] ->
      b2b_got segs I m g1 sv ->
      (* [comment removed for export] *)
      (forall ms' MD',
         b2b_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc LB m MD dst dn dl lo B g1 sv ms' MD' ->
         realizes segs (mkCfg ms' MD') K) ->
      realizes segs
        (mkCfg (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                   F (Z_to_bv 64 (bi_entry I)) fc None m (seg_rom segs)) MD)
        K.
End Stmt.
End ACeilS1.


Arguments b2b_spec {ACEIL__ segs L} AI I.
Arguments b2b_post {ACEIL__ segs L} AI I.
Section ACeilS2. Context {ACEIL__ : ACeil} {RUNW__ : RunW}.


(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section Lemmas.
  Variable segs : list Segment.
  Variable L : alloc_layout.

  (* [comment removed for export] *)

  (* [comment removed for export] *)
  (* [comment removed for export] *)

  (* [comment removed for export] *)

  (* [comment removed for export] *)
  (* [comment removed for export] *)

  (* [comment removed for export] *)

  (* [comment removed for export] *)

  (* [comment removed for export] *)
End Lemmas.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

End ACeilS2.
