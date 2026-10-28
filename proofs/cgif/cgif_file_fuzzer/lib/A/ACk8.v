(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn YP0b YP0a.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YN3v YI04 YI09 YI08 YI0m YI0n YI0s YCbw.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YG0v.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YP0d YP0c YI0w YI0y YC4a.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YC80 YC1f YC1g YC1h YC81 YC4b YC44 YC44.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import ACbk.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YC20.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AC8h AC8j ACab ACai ACaj.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YI16 YE00 YE01 YI00 YI0j YI0k.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import ACai ACaj ACak.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require YO07.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YC5d YC7z YC7y YC85.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import ACa3 ACa4 ACa5.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.
Definition ra_deads_Gc : list (bv 5) := [].
Definition ss_GLX : sstate :=
(mkSS 3852
   [SLit 0; SOff 1175 0; SOff 2 (-320); SOff 3 0; 
    SOff 4 0; SOff 1176 0; SOff 1177 0; SOff 1178 0; 
    SOff 2 0; SOff 2 (-320); SLit 0; SOff 1180 0; 
    SOff 1181 0; SOff 1182 0; SOff 1183 0; SOff 1184 0; 
    SOff 1185 0; SOff 1186 0; SOff 516 0;
    SAlu ALU_ADD (SAlu ALU_SRL (SOff 10 0) (SLit 3)) (SOff 40 0); 
    SOff 529 0; SOff 10 8; SLit 0; SOff 49 0; SLit 0;
    SAlu ALU_ADD (SAlu ALU_SRL (SOff 10 8) (SLit 3)) (SOff 40 0); 
    SOff 516 0; SOff 10 0; SOff 1187 0; SOff 1188 0; 
    SOff 1189 0; SOff 1190 0]
   [{|
      r_base := Some 2%nat;
      r_lo := -120;
      r_hi := -104;
      r_wlo := -120;
      r_whi := -104;
      r_chunks :=
        [{| c_off := -120; YP09.c_val := CVal 8 (SOff 1059 0) |};
         {| c_off := -112; YP09.c_val := CVal 4 (SOff 1060 0) |}]
    |};
    {|
      r_base := Some 2%nat;
      r_lo := -320;
      r_hi := -120;
      r_wlo := -320;
      r_whi := -120;
      r_chunks :=
        [{| c_off := -240; YP09.c_val := CVal 8 (SOff 10 40) |};
         {| c_off := -176; YP09.c_val := CVal 8 (SOff 516 80) |};
         {| c_off := -256; YP09.c_val := CVal 8 (SOff 516 32) |};
         {| c_off := -224; YP09.c_val := CVal 8 (SOff 516 48) |};
         {| c_off := -216; YP09.c_val := CVal 8 (SOff 516 112) |};
         {| c_off := -192; YP09.c_val := CVal 8 (SOff 814 0) |};
         {| c_off := -152; YP09.c_val := CVal 8 (SOff 11 0) |};
         {| c_off := -184; YP09.c_val := CVal 8 (SOff 815 0) |};
         {|
           c_off := -144;
           YP09.c_val :=
             CVal 8
               (SAlu ALU_ADD (SAlu ALU_SRL (SOff 10 40) (SLit 3)) (SOff 40 0))
         |}; {| c_off := -208; YP09.c_val := CVal 8 (SOff 10 24) |};
         {|
           c_off := -232;
           YP09.c_val :=
             CVal 8
               (SAlu ALU_ADD (SAlu ALU_SRL (SOff 10 24) (SLit 3)) (SOff 40 0))
         |}; {| c_off := -264; YP09.c_val := CVal 8 (SOff 662 0) |};
         {| c_off := -160; YP09.c_val := CVal 8 (SOff 11 30) |};
         {|
           c_off := -248;
           YP09.c_val :=
             CVal 8
               (SAlu ALU_ADD (SAlu ALU_SRL (SOff 11 30) (SLit 3)) (SOff 40 0))
         |}; {| c_off := -200; YP09.c_val := CVal 8 (SOff 11 16) |};
         {|
           c_off := -168;
           YP09.c_val :=
             CVal 8
               (SAlu ALU_ADD (SAlu ALU_SRL (SOff 11 16) (SLit 3)) (SOff 40 0))
         |}; {| c_off := -136; YP09.c_val := CVal 8 (SOff 40 0) |};
         {| c_off := -128; YP09.c_val := CVal 8 (SOff 516 0) |};
         {| c_off := -320; YP09.c_val := CVal 8 (SLit 0) |}]
    |};
    {|
      r_base := Some 516%nat;
      r_lo := 49;
      r_hi := 58;
      r_wlo := 49;
      r_whi := 58;
      r_chunks :=
        [{|
           c_off := 52;
           YP09.c_val := CVal 1 (SAlu ALU_SRL (SOff 46 0) (SLit 8))
         |}; {| c_off := 51; YP09.c_val := CVal 1 (SOff 46 0) |};
         {|
           c_off := 50;
           YP09.c_val :=
             CVal 1 (SAlu ALU_SRL (SExt true 16 (SOff 47 0)) (SLit 8))
         |};
         {| c_off := 49; YP09.c_val := CVal 1 (SExt true 16 (SOff 47 0)) |};
         {|
           c_off := 56;
           YP09.c_val := CVal 1 (SAlu ALU_SRL (SOff 45 0) (SLit 8))
         |}; {| c_off := 55; YP09.c_val := CVal 1 (SOff 45 0) |};
         {|
           c_off := 54;
           YP09.c_val := CVal 1 (SAlu ALU_SRL (SOff 44 0) (SLit 8))
         |}; {| c_off := 53; YP09.c_val := CVal 1 (SOff 44 0) |};
         {|
           c_off := 57;
           YP09.c_val :=
             CVal 1
               (SAlu ALU_OR (SOff 661 0)
                  (SAlu ALU_SLL (SAlu ALU_AND (SOff 43 0) (SLit 2)) (SLit 5)))
         |}]
    |};
    {|
      r_base := Some 529%nat;
      r_lo := 0;
      r_hi := 16;
      r_wlo := 0;
      r_whi := 0;
      r_chunks :=
        [{| c_off := 14; YP09.c_val := CVal 1 (SLit 1) |};
         {| c_off := 7; YP09.c_val := CVal 1 (SLit 2) |};
         {| c_off := 6; YP09.c_val := CVal 1 (SLit 0) |};
         {| c_off := 5; YP09.c_val := CVal 1 (SLit 18446744073709551602) |};
         {| c_off := 4; YP09.c_val := CVal 1 (SLit 18446744073709551608) |};
         {| c_off := 11; YP09.c_val := CVal 1 (SLit 18446744073709551602) |};
         {| c_off := 10; YP09.c_val := CVal 1 (SLit 0) |};
         {| c_off := 9; YP09.c_val := CVal 1 (SLit 18446744073709551602) |};
         {| c_off := 8; YP09.c_val := CVal 1 (SLit 18446744073709551602) |};
         {| c_off := 15; YP09.c_val := CVal 1 (SLit 18446744073709551603) |};
         {| c_off := 13; YP09.c_val := CVal 1 (SLit 18446744073709551602) |};
         {| c_off := 12; YP09.c_val := CVal 1 (SLit 18446744073709551602) |};
         {| c_off := 3; YP09.c_val := CVal 1 (SLit 18446744073709551601) |};
         {| c_off := 2; YP09.c_val := CVal 1 (SLit 18446744073709551601) |};
         {| c_off := 1; YP09.c_val := CVal 1 (SLit 18446744073709551601) |};
         {| c_off := 0; YP09.c_val := CVal 1 (SLit 18446744073709551601) |}]
    |};
    {|
      r_base := Some 516%nat;
      r_lo := 0;
      r_hi := 49;
      r_wlo := 0;
      r_whi := 49;
      r_chunks :=
        [{| c_off := 48; YP09.c_val := CVal 1 (SLit 44) |};
         {| c_off := 16; YP09.c_val := CVal 8 (SOff 240 1820) |};
         {| c_off := 8; YP09.c_val := CVal 8 (SOff 249 0) |};
         {| c_off := 0; YP09.c_val := CVal 8 (SLit 1102416563) |}]
    |};
    {|
      r_base := Some 516%nat;
      r_lo := 58;
      r_hi := 128;
      r_wlo := 58;
      r_whi := 128;
      r_chunks :=
        [{|
           c_off := 112;
           YP09.c_val :=
             CVal 1
               (SAlu ALU_ADD (SAlu ALU_AND (SOff 759 0) (SLit 255))
                  (SLit (-1)))
         |}; {| c_off := 120; YP09.c_val := CVal 8 (SOff 528 0) |}]
    |};
    {|
      r_base := Some 2%nat;
      r_lo := -104;
      r_hi := 0;
      r_wlo := -104;
      r_whi := 0;
      r_chunks :=
        [{| c_off := -104; YP09.c_val := CVal 8 (SOff 27 0) |};
         {| c_off := -96; YP09.c_val := CVal 8 (SOff 26 0) |};
         {| c_off := -88; YP09.c_val := CVal 8 (SOff 25 0) |};
         {| c_off := -80; YP09.c_val := CVal 8 (SOff 24 0) |};
         {| c_off := -72; YP09.c_val := CVal 8 (SOff 23 0) |};
         {| c_off := -64; YP09.c_val := CVal 8 (SOff 22 0) |};
         {| c_off := -56; YP09.c_val := CVal 8 (SOff 21 0) |};
         {| c_off := -48; YP09.c_val := CVal 8 (SOff 20 0) |};
         {| c_off := -40; YP09.c_val := CVal 8 (SOff 19 0) |};
         {| c_off := -32; YP09.c_val := CVal 8 (SOff 18 0) |};
         {| c_off := -24; YP09.c_val := CVal 8 (SOff 9 0) |};
         {| c_off := -16; YP09.c_val := CVal 8 (SOff 8 0) |};
         {| c_off := -8; YP09.c_val := CVal 8 (SOff 1 0) |}]
    |};
    {|
      r_base := Some 241%nat;
      r_lo := 0;
      r_hi := 8;
      r_wlo := 0;
      r_whi := 0;
      r_chunks := [{| c_off := 0; YP09.c_val := CVal 8 (SOff 253 0) |}]
    |};
    {|
      r_base := Some 253%nat;
      r_lo := 0;
      r_hi := 8;
      r_wlo := 0;
      r_whi := 0;
      r_chunks := [{| c_off := 0; YP09.c_val := CVal 8 (SOff 40 0) |}]
    |};
    {|
      r_base := Some 242%nat;
      r_lo := 0;
      r_hi := 8;
      r_wlo := 0;
      r_whi := 0;
      r_chunks := [{| c_off := 0; YP09.c_val := CVal 8 (SOff 55 0) |}]
    |};
    {|
      r_base := Some 55%nat;
      r_lo := 0;
      r_hi := 4;
      r_wlo := 0;
      r_whi := 0;
      r_chunks := [{| c_off := 0; YP09.c_val := CVal 4 (SLit 1) |}]
    |};
    {|
      r_base := Some 250%nat;
      r_lo := 0;
      r_hi := 8;
      r_wlo := 0;
      r_whi := 0;
      r_chunks := [{| c_off := 0; YP09.c_val := CVal 8 (SOff 240 1820) |}]
    |};
    {|
      r_base := Some 10%nat;
      r_lo := 0;
      r_hi := 48;
      r_wlo := 40;
      r_whi := 44;
      r_chunks :=
        [{| c_off := 0; YP09.c_val := CVal 8 (SOff 53 0) |};
         {| c_off := 8; YP09.c_val := CVal 8 (SOff 32 0) |};
         {| c_off := 16; YP09.c_val := CVal 8 (SOff 33 0) |};
         {| c_off := 24; YP09.c_val := CVal 4 (SOff 34 0) |};
         {| c_off := 28; YP09.c_val := CVal 2 (SOff 35 0) |};
         {| c_off := 30; YP09.c_val := CVal 2 (SOff 36 0) |};
         {| c_off := 32; YP09.c_val := CVal 2 (SOff 37 0) |};
         {| c_off := 34; YP09.c_val := CVal 2 (SOff 38 0) |};
         {| c_off := 40; YP09.c_val := CVal 4 (SOff 39 0) |}]
    |};
    {|
      r_base := Some 11%nat;
      r_lo := 0;
      r_hi := 40;
      r_wlo := 0;
      r_whi := 0;
      r_chunks :=
        [{| c_off := 0; YP09.c_val := CVal 8 (SOff 41 0) |};
         {| c_off := 8; YP09.c_val := CVal 8 (SOff 42 0) |};
         {| c_off := 16; YP09.c_val := CVal 4 (SOff 43 0) |};
         {| c_off := 20; YP09.c_val := CVal 2 (SOff 44 0) |};
         {| c_off := 22; YP09.c_val := CVal 2 (SOff 45 0) |};
         {| c_off := 24; YP09.c_val := CVal 2 (SOff 46 0) |};
         {| c_off := 26; YP09.c_val := CVal 2 (SOff 47 0) |};
         {| c_off := 28; YP09.c_val := CVal 2 (SOff 48 0) |};
         {| c_off := 30; YP09.c_val := CVal 2 (SOff 49 0) |};
         {| c_off := 32; YP09.c_val := CVal 1 (SOff 50 0) |};
         {| c_off := 33; YP09.c_val := CVal 1 (SOff 51 0) |}]
    |};
    {|
      r_base := Some 32%nat;
      r_lo := 0;
      r_hi := 96;
      r_wlo := 0;
      r_whi := 0;
      r_chunks :=
        [{| c_off := 56; YP09.c_val := CVal 8 (SOff 54 0) |};
         {| c_off := 64; YP09.c_val := CVal 8 (SOff 52 0) |};
         {| c_off := 80; YP09.c_val := CVal 8 (SOff 56 0) |}]
    |}]
   None
   {|
     f_atoms :=
       [(529%nat,
         {| af_lo := 2147451392; af_hi := 17594333495296; af_al2 := 2 |});
        (528%nat, {| af_lo := 4096; af_hi := 140737479966720; af_al2 := 0 |});
        (516%nat, {| af_lo := 4096; af_hi := 140737479966720; af_al2 := 5 |});
        (2%nat,
         {| af_lo := 70368744177664; af_hi := 140737488355328; af_al2 := 5 |});
        (10%nat, {| af_lo := 4096; af_hi := 140737479966720; af_al2 := 4 |});
        (11%nat, {| af_lo := 4096; af_hi := 140737479966720; af_al2 := 3 |});
        (32%nat, {| af_lo := 4096; af_hi := 140737479966720; af_al2 := 4 |});
        (33%nat, {| af_lo := 0; af_hi := 18446744073709551615; af_al2 := 0 |});
        (34%nat, {| af_lo := 0; af_hi := 4294967295; af_al2 := 0 |});
        (35%nat, {| af_lo := 0; af_hi := 65535; af_al2 := 0 |});
        (36%nat, {| af_lo := 0; af_hi := 65535; af_al2 := 0 |});
        (37%nat, {| af_lo := 0; af_hi := 256; af_al2 := 0 |});
        (38%nat, {| af_lo := 0; af_hi := 65535; af_al2 := 0 |});
        (39%nat, {| af_lo := 0; af_hi := 4294967295; af_al2 := 0 |});
        (40%nat, {| af_lo := 2147450880; af_hi := 2147450880; af_al2 := 0 |});
        (41%nat, {| af_lo := 0; af_hi := 18446744073709551615; af_al2 := 0 |});
        (42%nat, {| af_lo := 4096; af_hi := 140737479966720; af_al2 := 4 |});
        (43%nat, {| af_lo := 0; af_hi := 4294967295; af_al2 := 0 |});
        (44%nat, {| af_lo := 1; af_hi := 65535; af_al2 := 0 |});
        (45%nat, {| af_lo := 1; af_hi := 65535; af_al2 := 0 |});
        (46%nat, {| af_lo := 0; af_hi := 65535; af_al2 := 0 |});
        (47%nat, {| af_lo := 0; af_hi := 65535; af_al2 := 0 |});
        (48%nat, {| af_lo := 0; af_hi := 65535; af_al2 := 0 |});
        (49%nat, {| af_lo := 0; af_hi := 256; af_al2 := 0 |});
        (50%nat, {| af_lo := 0; af_hi := 255; af_al2 := 0 |});
        (51%nat, {| af_lo := 0; af_hi := 255; af_al2 := 0 |});
        (52%nat, {| af_lo := 0; af_hi := 18446744073709551615; af_al2 := 0 |});
        (660%nat, {| af_lo := 0; af_hi := 256; af_al2 := 0 |});
        (662%nat, {| af_lo := 0; af_hi := 8; af_al2 := 0 |});
        (710%nat, {| af_lo := 0; af_hi := 256; af_al2 := 0 |});
        (759%nat, {| af_lo := 3; af_hi := 9; af_al2 := 0 |});
        (814%nat, {| af_lo := 4; af_hi := 256; af_al2 := 0 |});
        (815%nat, {| af_lo := 3; af_hi := 9; af_al2 := 0 |})];
     f_conds := [{| ac_c := BC_NE; ac_a := SOff 49 0; ac_b := SLit 0 |}];
     f_alias :=
       [(SAlu ALU_ADD (SAlu ALU_SRL (SOff 516 0) (SLit 3)) (SOff 40 0),
         SOff 529 0)]
   |}).
Definition ss_GDX : sstate :=
(mkSS 4048
   [SLit 0; SOff 1191 0; SOff 2 (-320); SOff 3 0; 
    SOff 4 0; SOff 1192 0; SOff 1193 0; SOff 1194 0; 
    SOff 2 0; SOff 2 (-320); SOff 49 0; SLit 0;
    SAluw ALU_SLL (SLit 1) (SOff 662 0);
    SAlu ALU_AND (SAluw ALU_SLL (SLit 1) (SOff 662 0)) (SLit 65535);
    SLit 65535; SOff 1200 0; SOff 1201 0; SOff 1202 0; 
    SLit 0; SAlu ALU_ADD (SAlu ALU_SRL (SOff 10 0) (SLit 3)) (SOff 40 0);
    SOff 529 0; SOff 10 8; SOff 10 0; SOff 32 0; SOff 516 32;
    SAlu ALU_ADD (SAlu ALU_SRL (SOff 10 8) (SLit 3)) (SOff 40 0); 
    SOff 53 0; SOff 10 0; SOff 1203 0; SOff 1204 0; 
    SOff 1205 0; SOff 1206 0]
   [{|
      r_base := Some 2%nat;
      r_lo := -120;
      r_hi := -104;
      r_wlo := -120;
      r_whi := -104;
      r_chunks :=
        [{| c_off := -120; YP09.c_val := CVal 8 (SOff 1059 0) |};
         {| c_off := -112; YP09.c_val := CVal 4 (SOff 1060 0) |}]
    |};
    {|
      r_base := Some 2%nat;
      r_lo := -320;
      r_hi := -120;
      r_wlo := -320;
      r_whi := -120;
      r_chunks :=
        [{| c_off := -280; YP09.c_val := CVal 8 (SOff 516 0) |};
         {| c_off := -288; YP09.c_val := CVal 8 (SOff 516 0) |};
         {| c_off := -152; YP09.c_val := CVal 8 (SLit 0) |};
         {| c_off := -136; YP09.c_val := CVal 8 (SLit 0) |};
         {| c_off := -240; YP09.c_val := CVal 8 (SOff 10 40) |};
         {| c_off := -176; YP09.c_val := CVal 8 (SOff 516 80) |};
         {| c_off := -256; YP09.c_val := CVal 8 (SOff 516 32) |};
         {| c_off := -224; YP09.c_val := CVal 8 (SOff 516 48) |};
         {| c_off := -216; YP09.c_val := CVal 8 (SOff 516 112) |};
         {| c_off := -192; YP09.c_val := CVal 8 (SOff 814 0) |};
         {| c_off := -184; YP09.c_val := CVal 8 (SOff 815 0) |};
         {|
           c_off := -144;
           YP09.c_val :=
             CVal 8
               (SAlu ALU_ADD (SAlu ALU_SRL (SOff 10 40) (SLit 3)) (SOff 40 0))
         |}; {| c_off := -208; YP09.c_val := CVal 8 (SOff 10 24) |};
         {|
           c_off := -232;
           YP09.c_val :=
             CVal 8
               (SAlu ALU_ADD (SAlu ALU_SRL (SOff 10 24) (SLit 3)) (SOff 40 0))
         |}; {| c_off := -264; YP09.c_val := CVal 8 (SOff 662 0) |};
         {| c_off := -160; YP09.c_val := CVal 8 (SOff 11 30) |};
         {|
           c_off := -248;
           YP09.c_val :=
             CVal 8
               (SAlu ALU_ADD (SAlu ALU_SRL (SOff 11 30) (SLit 3)) (SOff 40 0))
         |}; {| c_off := -200; YP09.c_val := CVal 8 (SOff 11 16) |};
         {|
           c_off := -168;
           YP09.c_val :=
             CVal 8
               (SAlu ALU_ADD (SAlu ALU_SRL (SOff 11 16) (SLit 3)) (SOff 40 0))
         |}; {| c_off := -128; YP09.c_val := CVal 8 (SOff 516 0) |};
         {| c_off := -320; YP09.c_val := CVal 8 (SLit 0) |}]
    |};
    {|
      r_base := Some 516%nat;
      r_lo := 49;
      r_hi := 58;
      r_wlo := 49;
      r_whi := 58;
      r_chunks :=
        [{|
           c_off := 52;
           YP09.c_val := CVal 1 (SAlu ALU_SRL (SOff 46 0) (SLit 8))
         |}; {| c_off := 51; YP09.c_val := CVal 1 (SOff 46 0) |};
         {|
           c_off := 50;
           YP09.c_val :=
             CVal 1 (SAlu ALU_SRL (SExt true 16 (SOff 47 0)) (SLit 8))
         |};
         {| c_off := 49; YP09.c_val := CVal 1 (SExt true 16 (SOff 47 0)) |};
         {|
           c_off := 56;
           YP09.c_val := CVal 1 (SAlu ALU_SRL (SOff 45 0) (SLit 8))
         |}; {| c_off := 55; YP09.c_val := CVal 1 (SOff 45 0) |};
         {|
           c_off := 54;
           YP09.c_val := CVal 1 (SAlu ALU_SRL (SOff 44 0) (SLit 8))
         |}; {| c_off := 53; YP09.c_val := CVal 1 (SOff 44 0) |};
         {|
           c_off := 57;
           YP09.c_val :=
             CVal 1
               (SAlu ALU_OR (SOff 661 0)
                  (SAlu ALU_SLL (SAlu ALU_AND (SOff 43 0) (SLit 2)) (SLit 5)))
         |}]
    |};
    {|
      r_base := Some 529%nat;
      r_lo := 0;
      r_hi := 16;
      r_wlo := 0;
      r_whi := 0;
      r_chunks :=
        [{| c_off := 4; YP09.c_val := CVal 1 (SLit 1) |};
         {| c_off := 14; YP09.c_val := CVal 1 (SLit 1) |};
         {| c_off := 7; YP09.c_val := CVal 1 (SLit 2) |};
         {| c_off := 6; YP09.c_val := CVal 1 (SLit 0) |};
         {| c_off := 5; YP09.c_val := CVal 1 (SLit 18446744073709551602) |};
         {| c_off := 11; YP09.c_val := CVal 1 (SLit 18446744073709551602) |};
         {| c_off := 10; YP09.c_val := CVal 1 (SLit 0) |};
         {| c_off := 9; YP09.c_val := CVal 1 (SLit 18446744073709551602) |};
         {| c_off := 8; YP09.c_val := CVal 1 (SLit 18446744073709551602) |};
         {| c_off := 15; YP09.c_val := CVal 1 (SLit 18446744073709551603) |};
         {| c_off := 13; YP09.c_val := CVal 1 (SLit 18446744073709551602) |};
         {| c_off := 12; YP09.c_val := CVal 1 (SLit 18446744073709551602) |};
         {| c_off := 3; YP09.c_val := CVal 1 (SLit 18446744073709551601) |};
         {| c_off := 2; YP09.c_val := CVal 1 (SLit 18446744073709551601) |};
         {| c_off := 1; YP09.c_val := CVal 1 (SLit 18446744073709551601) |};
         {| c_off := 0; YP09.c_val := CVal 1 (SLit 18446744073709551601) |}]
    |};
    {|
      r_base := Some 516%nat;
      r_lo := 0;
      r_hi := 49;
      r_wlo := 0;
      r_whi := 49;
      r_chunks :=
        [{| c_off := 32; YP09.c_val := CVal 1 (SLit 0) |};
         {| c_off := 48; YP09.c_val := CVal 1 (SLit 44) |};
         {| c_off := 16; YP09.c_val := CVal 8 (SOff 240 1820) |};
         {| c_off := 8; YP09.c_val := CVal 8 (SOff 249 0) |};
         {| c_off := 0; YP09.c_val := CVal 8 (SLit 1102416563) |}]
    |};
    {|
      r_base := Some 516%nat;
      r_lo := 58;
      r_hi := 128;
      r_wlo := 58;
      r_whi := 128;
      r_chunks :=
        [{|
           c_off := 112;
           YP09.c_val :=
             CVal 1
               (SAlu ALU_ADD (SAlu ALU_AND (SOff 759 0) (SLit 255))
                  (SLit (-1)))
         |}; {| c_off := 120; YP09.c_val := CVal 8 (SOff 528 0) |}]
    |};
    {|
      r_base := Some 2%nat;
      r_lo := -104;
      r_hi := 0;
      r_wlo := -104;
      r_whi := 0;
      r_chunks :=
        [{| c_off := -104; YP09.c_val := CVal 8 (SOff 27 0) |};
         {| c_off := -96; YP09.c_val := CVal 8 (SOff 26 0) |};
         {| c_off := -88; YP09.c_val := CVal 8 (SOff 25 0) |};
         {| c_off := -80; YP09.c_val := CVal 8 (SOff 24 0) |};
         {| c_off := -72; YP09.c_val := CVal 8 (SOff 23 0) |};
         {| c_off := -64; YP09.c_val := CVal 8 (SOff 22 0) |};
         {| c_off := -56; YP09.c_val := CVal 8 (SOff 21 0) |};
         {| c_off := -48; YP09.c_val := CVal 8 (SOff 20 0) |};
         {| c_off := -40; YP09.c_val := CVal 8 (SOff 19 0) |};
         {| c_off := -32; YP09.c_val := CVal 8 (SOff 18 0) |};
         {| c_off := -24; YP09.c_val := CVal 8 (SOff 9 0) |};
         {| c_off := -16; YP09.c_val := CVal 8 (SOff 8 0) |};
         {| c_off := -8; YP09.c_val := CVal 8 (SOff 1 0) |}]
    |};
    {|
      r_base := Some 241%nat;
      r_lo := 0;
      r_hi := 8;
      r_wlo := 0;
      r_whi := 0;
      r_chunks := [{| c_off := 0; YP09.c_val := CVal 8 (SOff 253 0) |}]
    |};
    {|
      r_base := Some 253%nat;
      r_lo := 0;
      r_hi := 8;
      r_wlo := 0;
      r_whi := 0;
      r_chunks := [{| c_off := 0; YP09.c_val := CVal 8 (SOff 40 0) |}]
    |};
    {|
      r_base := Some 242%nat;
      r_lo := 0;
      r_hi := 8;
      r_wlo := 0;
      r_whi := 0;
      r_chunks := [{| c_off := 0; YP09.c_val := CVal 8 (SOff 55 0) |}]
    |};
    {|
      r_base := Some 55%nat;
      r_lo := 0;
      r_hi := 4;
      r_wlo := 0;
      r_whi := 0;
      r_chunks := [{| c_off := 0; YP09.c_val := CVal 4 (SLit 1) |}]
    |};
    {|
      r_base := Some 250%nat;
      r_lo := 0;
      r_hi := 8;
      r_wlo := 0;
      r_whi := 0;
      r_chunks := [{| c_off := 0; YP09.c_val := CVal 8 (SOff 240 1820) |}]
    |};
    {|
      r_base := Some 10%nat;
      r_lo := 0;
      r_hi := 48;
      r_wlo := 40;
      r_whi := 44;
      r_chunks :=
        [{| c_off := 0; YP09.c_val := CVal 8 (SOff 53 0) |};
         {| c_off := 8; YP09.c_val := CVal 8 (SOff 32 0) |};
         {| c_off := 16; YP09.c_val := CVal 8 (SOff 33 0) |};
         {| c_off := 24; YP09.c_val := CVal 4 (SOff 34 0) |};
         {| c_off := 28; YP09.c_val := CVal 2 (SOff 35 0) |};
         {| c_off := 30; YP09.c_val := CVal 2 (SOff 36 0) |};
         {| c_off := 32; YP09.c_val := CVal 2 (SOff 37 0) |};
         {| c_off := 34; YP09.c_val := CVal 2 (SOff 38 0) |};
         {| c_off := 40; YP09.c_val := CVal 4 (SOff 39 0) |}]
    |};
    {|
      r_base := Some 11%nat;
      r_lo := 0;
      r_hi := 40;
      r_wlo := 0;
      r_whi := 0;
      r_chunks :=
        [{| c_off := 0; YP09.c_val := CVal 8 (SOff 41 0) |};
         {| c_off := 8; YP09.c_val := CVal 8 (SOff 42 0) |};
         {| c_off := 16; YP09.c_val := CVal 4 (SOff 43 0) |};
         {| c_off := 20; YP09.c_val := CVal 2 (SOff 44 0) |};
         {| c_off := 22; YP09.c_val := CVal 2 (SOff 45 0) |};
         {| c_off := 24; YP09.c_val := CVal 2 (SOff 46 0) |};
         {| c_off := 26; YP09.c_val := CVal 2 (SOff 47 0) |};
         {| c_off := 28; YP09.c_val := CVal 2 (SOff 48 0) |};
         {| c_off := 30; YP09.c_val := CVal 2 (SOff 49 0) |};
         {| c_off := 32; YP09.c_val := CVal 1 (SOff 50 0) |};
         {| c_off := 33; YP09.c_val := CVal 1 (SOff 51 0) |}]
    |};
    {|
      r_base := Some 32%nat;
      r_lo := 0;
      r_hi := 96;
      r_wlo := 0;
      r_whi := 0;
      r_chunks :=
        [{| c_off := 56; YP09.c_val := CVal 8 (SOff 54 0) |};
         {| c_off := 64; YP09.c_val := CVal 8 (SOff 52 0) |};
         {| c_off := 80; YP09.c_val := CVal 8 (SOff 56 0) |}]
    |}]
   None
   {|
     f_atoms :=
       [(529%nat,
         {| af_lo := 2147451392; af_hi := 17594333495296; af_al2 := 2 |});
        (528%nat, {| af_lo := 4096; af_hi := 140737479966720; af_al2 := 0 |});
        (516%nat, {| af_lo := 4096; af_hi := 140737479966720; af_al2 := 5 |});
        (2%nat,
         {| af_lo := 70368744177664; af_hi := 140737488355328; af_al2 := 5 |});
        (10%nat, {| af_lo := 4096; af_hi := 140737479966720; af_al2 := 4 |});
        (11%nat, {| af_lo := 4096; af_hi := 140737479966720; af_al2 := 3 |});
        (32%nat, {| af_lo := 4096; af_hi := 140737479966720; af_al2 := 4 |});
        (33%nat, {| af_lo := 0; af_hi := 18446744073709551615; af_al2 := 0 |});
        (34%nat, {| af_lo := 0; af_hi := 4294967295; af_al2 := 0 |});
        (35%nat, {| af_lo := 0; af_hi := 65535; af_al2 := 0 |});
        (36%nat, {| af_lo := 0; af_hi := 65535; af_al2 := 0 |});
        (37%nat, {| af_lo := 0; af_hi := 256; af_al2 := 0 |});
        (38%nat, {| af_lo := 0; af_hi := 65535; af_al2 := 0 |});
        (39%nat, {| af_lo := 0; af_hi := 4294967295; af_al2 := 0 |});
        (40%nat, {| af_lo := 2147450880; af_hi := 2147450880; af_al2 := 0 |});
        (41%nat, {| af_lo := 0; af_hi := 18446744073709551615; af_al2 := 0 |});
        (42%nat, {| af_lo := 4096; af_hi := 140737479966720; af_al2 := 4 |});
        (43%nat, {| af_lo := 0; af_hi := 4294967295; af_al2 := 0 |});
        (44%nat, {| af_lo := 1; af_hi := 65535; af_al2 := 0 |});
        (45%nat, {| af_lo := 1; af_hi := 65535; af_al2 := 0 |});
        (46%nat, {| af_lo := 0; af_hi := 65535; af_al2 := 0 |});
        (47%nat, {| af_lo := 0; af_hi := 65535; af_al2 := 0 |});
        (48%nat, {| af_lo := 0; af_hi := 65535; af_al2 := 0 |});
        (49%nat, {| af_lo := 0; af_hi := 256; af_al2 := 0 |});
        (50%nat, {| af_lo := 0; af_hi := 255; af_al2 := 0 |});
        (51%nat, {| af_lo := 0; af_hi := 255; af_al2 := 0 |});
        (52%nat, {| af_lo := 0; af_hi := 18446744073709551615; af_al2 := 0 |});
        (660%nat, {| af_lo := 0; af_hi := 256; af_al2 := 0 |});
        (662%nat, {| af_lo := 0; af_hi := 8; af_al2 := 0 |});
        (710%nat, {| af_lo := 0; af_hi := 256; af_al2 := 0 |});
        (759%nat, {| af_lo := 3; af_hi := 9; af_al2 := 0 |});
        (814%nat, {| af_lo := 4; af_hi := 256; af_al2 := 0 |});
        (815%nat, {| af_lo := 3; af_hi := 9; af_al2 := 0 |})];
     f_conds :=
       [{|
          ac_c := BC_NE;
          ac_a := SOff 49 0;
          ac_b :=
            SAlu ALU_AND (SAluw ALU_SLL (SLit 1) (SOff 662 0)) (SLit 65535)
        |}; {| ac_c := BC_NE; ac_a := SOff 49 0; ac_b := SLit 0 |}];
     f_alias :=
       [(SAlu ALU_ADD (SAlu ALU_SRL (SOff 516 0) (SLit 3)) (SOff 40 0),
         SOff 529 0)]
   |}).
Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section b.
Context {PI : PAImg lib_asan3_1_listing}.
Context {RO : YC20.ro_below_ofl (@pa_segs _ lib_asan3_1_listing PI) (@pa_relro_lo _ lib_asan3_1_listing PI) (@pa_relro_hi _ lib_asan3_1_listing PI)}.
#[local] Notation SEGS := (@pa_segs _ lib_asan3_1_listing PI).
#[local] Notation VAL := (@pa_val _ lib_asan3_1_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ lib_asan3_1_listing PI).
#[local] Notation BASE := (@pa_val _ lib_asan3_1_listing PI A_TEXT).
Section c.
Variable K : asink_syms.
Variable MT : ameter_ops.
Variable XN : xnums.
Definition INV_GLX (B : asyms) : racx -> raxx -> env -> Z -> alayout -> astate -> world SEGS -> machine_state -> Model -> Prop :=
fun cx xx E k ly3 S3 W3 ms3 md3 => INV_T0 B cx E k ly3 S3 W3 ms3 md3 /\ XC cx /\ XV_F cx E /\
XLZW_ok cx xx E (mrestrict (w_H W3) (ms_mem ms3)) /\ XMET MT XN cx S3 (mo_free MT) (mo_free MT) /\
asink_at SEGS K (mrestrict (w_H W3) (ms_mem ms3)) md3 (x_pf xx) ((x_Sg xx ++ rx_gce cx) ++ rx_hdr cx) /\
c_slct cx <> 0.
Definition INV_GDX (B : asyms) : racx -> raxx -> env -> Z -> alayout -> astate -> world SEGS -> machine_state -> Model -> Prop :=
fun cx xx E k ly3 S3 W3 ms3 md3 => INV_T0 B cx E k ly3 S3 W3 ms3 md3 /\ XC cx /\ XV_F cx E /\
XLZW_ok cx xx E (mrestrict (w_H W3) (ms_mem ms3)) /\ XMET MT XN cx S3 (mo_free MT) (mo_free MT) /\
asink_at SEGS K (mrestrict (w_H W3) (ms_mem ms3)) md3 (x_pf xx) (((x_Sg xx ++ rx_gce cx) ++ rx_hdr cx) ++ firstn (Z.to_nat (c_slct cx * 3)) (x_LCT xx)) /\
c_slct cx <> 0 /\ (forall K1, ew E 662 = Z_to_bv 64 K1 -> 0 <= K1 <= 8 -> c_slct cx <> 2 ^ K1).
End c.
End b.
End a.
