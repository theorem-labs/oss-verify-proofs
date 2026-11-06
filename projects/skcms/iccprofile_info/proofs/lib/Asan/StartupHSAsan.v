(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool.
From LinuxProcessSemantics.Riscv Require Import Instr.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.Asan Require Import AxSymExec3 AsanPlanCore AsanPlan.
Import ListNotations. Import AX2. Import APC. Import AP.
Open Scope Z_scope.
Definition HS0 : option acs :=
Some
  {|
    a_ss :=
      SS 522824
        [ELit 0; ELit 581384;
         EAlu Instr.ALU_ADD (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 32768) (EVar 0)) (EMd Instr.M_MUL (ELit 16) (EVar 6))) (ELit (-48));
         ELit 67584; ELit 6134640; EVar 607; EVar 608; EVar 609;
         EAlu Instr.ALU_ADD (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 32768) (EVar 0)) (EMd Instr.M_MUL (ELit 16) (EVar 6))) (ELit 8); 
         EVar 1; EVar 1;
         EAlu Instr.ALU_ADD (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 32768) (EVar 0)) (EMd Instr.M_MUL (ELit 16) (EVar 6))) (ELit 8);
         EAlu Instr.ALU_ADD
           (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 32768) (EVar 0))
              (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 8) (EVar 1)) (EMd Instr.M_MUL (ELit 16) (EVar 6))))
           (ELit 16);
         EVar 610; EVar 611; EVar 612; EVar 613; EVar 614; ELit 522824;
         EAlu Instr.ALU_ADD
           (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 32768) (EVar 0))
              (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 8) (EVar 1)) (EMd Instr.M_MUL (ELit 16) (EVar 6))))
           (ELit 16);
         ELit 0; ELit 0; ELit 0; ELit 0; ELit 0; ELit 0; ELit 0; ELit 0; EVar 615; EVar 616; EVar 617; EVar 618]
        []
        [KRange (EVar 368) 0 8;
         KRange
           (EAlu Instr.ALU_ADD (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 16) (EVar 6)) (EMd Instr.M_MUL (ELit (-4096)) (EVar 368))) (ELit 3935)) 0
           4095;
         KRange (EVar 621) 6275072 2153766912; KRange (EVar 620) 1 34359736319;
         KDisj {| a_base := EMd Instr.M_MUL (ELit 4096) (EVar 620); a_off := 0 |} (ELit 4096)
           {| a_base := EMd Instr.M_MUL (ELit 4096) (EVar 470); a_off := 0 |} (ELit 4096);
         KDisj {| a_base := EMd Instr.M_MUL (ELit 4096) (EVar 620); a_off := 0 |} (ELit 4096)
           {| a_base := EMd Instr.M_MUL (ELit 4096) (EVar 453); a_off := 0 |} (ELit 8388608);
         KDisj {| a_base := EMd Instr.M_MUL (ELit 4096) (EVar 620); a_off := 0 |} (ELit 4096)
           {| a_base := EMd Instr.M_MUL (ELit 4096) (EVar 452); a_off := 0 |} (ELit 1048576);
         KDisj {| a_base := EMd Instr.M_MUL (ELit 4096) (EVar 620); a_off := 0 |} (ELit 4096) {| a_base := ELit 2147446784; a_off := 0 |}
           (ELit 17592186048512);
         KDisj {| a_base := EMd Instr.M_MUL (ELit 4096) (EVar 620); a_off := 0 |} (ELit 4096) {| a_base := ELit 65536; a_off := 0 |} (ELit 6209536);
         KDisj {| a_base := EMd Instr.M_MUL (ELit 4096) (EVar 620); a_off := 0 |} (ELit 4096)
           {|
             a_base :=
               EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 32768) (EVar 0)) (EMd Instr.M_MUL (ELit 4096) (EAlu Instr.ALU_SRL (EVar 6) (ELit 8)));
             a_off := -8388608
           |} (ELit 2155876352);
         KRange (EVar 619) 1 34359736319;
         KDisj {| a_base := EMd Instr.M_MUL (ELit 4096) (EVar 619); a_off := 0 |} (ELit 8192)
           {| a_base := EMd Instr.M_MUL (ELit 4096) (EVar 470); a_off := 0 |} (ELit 4096);
         KDisj {| a_base := EMd Instr.M_MUL (ELit 4096) (EVar 619); a_off := 0 |} (ELit 8192)
           {| a_base := EMd Instr.M_MUL (ELit 4096) (EVar 453); a_off := 0 |} (ELit 8388608);
         KDisj {| a_base := EMd Instr.M_MUL (ELit 4096) (EVar 619); a_off := 0 |} (ELit 8192)
           {| a_base := EMd Instr.M_MUL (ELit 4096) (EVar 452); a_off := 0 |} (ELit 1048576);
         KDisj {| a_base := EMd Instr.M_MUL (ELit 4096) (EVar 619); a_off := 0 |} (ELit 8192) {| a_base := ELit 2147446784; a_off := 0 |}
           (ELit 17592186048512);
         KWord {| a_base := ELit 0; a_off := 672880 |} 8 (ELit 0); KWord {| a_base := ELit 0; a_off := 668936 |} 1 (ELit 1);
         KWord {| a_base := ELit 0; a_off := 668928 |} 8 (ELit 1); KFill {| a_base := ELit 0; a_off := 2147534452 |} (ELit 40) 249;
         KWord {| a_base := ELit 0; a_off := 2148217416 |} 1 (ELit 4); KFill {| a_base := ELit 0; a_off := 2148217417 |} (ELit 3) 249;
         KWord {| a_base := ELit 0; a_off := 2147467745 |} 1 (ELit 3); KFill {| a_base := ELit 0; a_off := 2147467746 |} (ELit 2) 249;
         KWord {| a_base := ELit 0; a_off := 2147467740 |} 1 (ELit 6); KFill {| a_base := ELit 0; a_off := 2147467741 |} (ELit 3) 249;
         KWord {| a_base := ELit 0; a_off := 2147467734 |} 1 (ELit 4); KFill {| a_base := ELit 0; a_off := 2147467735 |} (ELit 5) 249;
         KWord {| a_base := ELit 0; a_off := 2147467725 |} 1 (ELit 5); KFill {| a_base := ELit 0; a_off := 2147467726 |} (ELit 6) 249;
         KDisj {| a_base := EMd Instr.M_MUL (ELit 512) (EVar 470); a_off := 2147450880 |} (ELit 512)
           {|
             a_base := EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 4096) (EVar 0)) (EMd Instr.M_MUL (ELit 512) (EAlu Instr.ALU_SRL (EVar 6) (ELit 8)));
             a_off := 2146402304
           |}
           (EAlu Instr.ALU_ADD
              (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit (-4096)) (EVar 0)) (EMd Instr.M_MUL (ELit (-512)) (EAlu Instr.ALU_SRL (EVar 6) (ELit 8))))
              (ELit 17592187092992));
         KDisj {| a_base := EMd Instr.M_MUL (ELit 512) (EVar 470); a_off := 2147450880 |} (ELit 512) {| a_base := ELit 0; a_off := 2147459072 |}
           (ELit 776192);
         KWr {| a_base := EMd Instr.M_MUL (ELit 512) (EVar 470); a_off := 2147450880 |} (ELit 512);
         KZero {| a_base := EMd Instr.M_MUL (ELit 512) (EVar 470); a_off := 2147450880 |} (ELit 512);
         KWr {| a_base := EMd Instr.M_MUL (ELit 4096) (EVar 470); a_off := 0 |} (ELit 4096); KRange (EVar 470) 1 34359736319;
         KDisj {| a_base := EMd Instr.M_MUL (ELit 4096) (EVar 453); a_off := 0 |} (ELit 8388608)
           {| a_base := EMd Instr.M_MUL (ELit 4096) (EVar 470); a_off := 0 |} (ELit 4096);
         KDisj {| a_base := EMd Instr.M_MUL (ELit 4096) (EVar 452); a_off := 0 |} (ELit 1048576)
           {| a_base := EMd Instr.M_MUL (ELit 4096) (EVar 470); a_off := 0 |} (ELit 4096);
         KDisj {| a_base := EMd Instr.M_MUL (ELit 4096) (EVar 401); a_off := 0 |} (ELit 11571200)
           {| a_base := EMd Instr.M_MUL (ELit 4096) (EVar 470); a_off := 0 |} (ELit 4096);
         KDisj {| a_base := EMd Instr.M_MUL (ELit 4096) (EVar 334); a_off := 0 |} (ELit 4096)
           {| a_base := EMd Instr.M_MUL (ELit 4096) (EVar 470); a_off := 0 |} (ELit 4096);
         KDisj {| a_base := EMd Instr.M_MUL (ELit 4096) (EVar 269); a_off := 0 |} (ELit 4096)
           {| a_base := EMd Instr.M_MUL (ELit 4096) (EVar 470); a_off := 0 |} (ELit 4096);
         KDisj {| a_base := EMd Instr.M_MUL (ELit 4096) (EVar 243); a_off := 0 |} (ELit 65536)
           {| a_base := EMd Instr.M_MUL (ELit 4096) (EVar 470); a_off := 0 |} (ELit 4096);
         KDisj {| a_base := EMd Instr.M_MUL (ELit 4096) (EVar 242); a_off := 0 |} (ELit 4096)
           {| a_base := EMd Instr.M_MUL (ELit 4096) (EVar 470); a_off := 0 |} (ELit 4096);
         KDisj {| a_base := EMd Instr.M_MUL (ELit 4096) (EVar 241); a_off := 0 |} (ELit 8388608)
           {| a_base := EMd Instr.M_MUL (ELit 4096) (EVar 470); a_off := 0 |} (ELit 4096);
         KDisj {| a_base := EMd Instr.M_MUL (ELit 4096) (EVar 223); a_off := 0 |} (ELit 137439023104)
           {| a_base := EMd Instr.M_MUL (ELit 4096) (EVar 470); a_off := 0 |} (ELit 4096);
         KDisj {| a_base := EMd Instr.M_MUL (ELit 4096) (EVar 222); a_off := 0 |} (ELit 3727360)
           {| a_base := EMd Instr.M_MUL (ELit 4096) (EVar 470); a_off := 0 |} (ELit 4096);
         KDisj {| a_base := EMd Instr.M_MUL (ELit 4096) (EVar 93); a_off := 0 |} (ELit 65536)
           {| a_base := EMd Instr.M_MUL (ELit 4096) (EVar 470); a_off := 0 |} (ELit 4096);
         KDisj {| a_base := EMd Instr.M_MUL (ELit 4096) (EVar 470); a_off := 0 |} (ELit 4096) {| a_base := ELit 2147446784; a_off := 0 |}
           (ELit 17592186048512);
         KDisj {| a_base := EMd Instr.M_MUL (ELit 4096) (EVar 470); a_off := 0 |} (ELit 4096) {| a_base := ELit 65536; a_off := 0 |} (ELit 6209536);
         KDisj {| a_base := EMd Instr.M_MUL (ELit 4096) (EVar 470); a_off := 0 |} (ELit 4096)
           {|
             a_base :=
               EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 32768) (EVar 0)) (EMd Instr.M_MUL (ELit 4096) (EAlu Instr.ALU_SRL (EVar 6) (ELit 8)));
             a_off := -8388608
           |} (ELit 2155876352);
         KInv 0 [ELit 1608344; ELit 1542792; ELit 100; EMd Instr.M_MUL (ELit 4096) (EVar 452); EMd Instr.M_MUL (ELit 4096) (EVar 453)];
         KWord {| a_base := EMd Instr.M_MUL (ELit 4096) (EVar 453); a_off := 8 |} 8 (ELit 255564);
         KWord {| a_base := ELit 0; a_off := 1542820 |} 1 (ELit 0);
         KWord {| a_base := ELit 0; a_off := 1542808 |} 8 (EMd Instr.M_MUL (ELit 4096) (EVar 453));
         KDisj {| a_base := EMd Instr.M_MUL (ELit 512) (EVar 453); a_off := 2147450880 |} (ELit 1048576)
           {|
             a_base := EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 4096) (EVar 0)) (EMd Instr.M_MUL (ELit 512) (EAlu Instr.ALU_SRL (EVar 6) (ELit 8)));
             a_off := 2146402304
           |}
           (EAlu Instr.ALU_ADD
              (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit (-4096)) (EVar 0)) (EMd Instr.M_MUL (ELit (-512)) (EAlu Instr.ALU_SRL (EVar 6) (ELit 8))))
              (ELit 17592187092992));
         KDisj {| a_base := EMd Instr.M_MUL (ELit 512) (EVar 453); a_off := 2147450880 |} (ELit 1048576) {| a_base := ELit 0; a_off := 2147459072 |}
           (ELit 776192);
         KWr {| a_base := EMd Instr.M_MUL (ELit 512) (EVar 453); a_off := 2147450880 |} (ELit 1048576);
         KZero {| a_base := EMd Instr.M_MUL (ELit 512) (EVar 453); a_off := 2147450880 |} (ELit 1048576);
         KWr {| a_base := EMd Instr.M_MUL (ELit 4096) (EVar 453); a_off := 0 |} (ELit 8388608); KRange (EVar 453) 1532 34359734272;
         KDisj {| a_base := EMd Instr.M_MUL (ELit 4096) (EVar 452); a_off := 0 |} (ELit 1048576)
           {| a_base := EMd Instr.M_MUL (ELit 4096) (EVar 453); a_off := 0 |} (ELit 8388608);
         KDisj {| a_base := EMd Instr.M_MUL (ELit 4096) (EVar 401); a_off := 0 |} (ELit 11571200)
           {| a_base := EMd Instr.M_MUL (ELit 4096) (EVar 453); a_off := 0 |} (ELit 8388608);
         KDisj {| a_base := EMd Instr.M_MUL (ELit 4096) (EVar 334); a_off := 0 |} (ELit 4096)
           {| a_base := EMd Instr.M_MUL (ELit 4096) (EVar 453); a_off := 0 |} (ELit 8388608);
         KDisj {| a_base := EMd Instr.M_MUL (ELit 4096) (EVar 269); a_off := 0 |} (ELit 4096)
           {| a_base := EMd Instr.M_MUL (ELit 4096) (EVar 453); a_off := 0 |} (ELit 8388608);
         KDisj {| a_base := EMd Instr.M_MUL (ELit 4096) (EVar 243); a_off := 0 |} (ELit 65536)
           {| a_base := EMd Instr.M_MUL (ELit 4096) (EVar 453); a_off := 0 |} (ELit 8388608);
         KDisj {| a_base := EMd Instr.M_MUL (ELit 4096) (EVar 242); a_off := 0 |} (ELit 4096)
           {| a_base := EMd Instr.M_MUL (ELit 4096) (EVar 453); a_off := 0 |} (ELit 8388608);
         KDisj {| a_base := EMd Instr.M_MUL (ELit 4096) (EVar 241); a_off := 0 |} (ELit 8388608)
           {| a_base := EMd Instr.M_MUL (ELit 4096) (EVar 453); a_off := 0 |} (ELit 8388608);
         KDisj {| a_base := EMd Instr.M_MUL (ELit 4096) (EVar 223); a_off := 0 |} (ELit 137439023104)
           {| a_base := EMd Instr.M_MUL (ELit 4096) (EVar 453); a_off := 0 |} (ELit 8388608);
         KDisj {| a_base := EMd Instr.M_MUL (ELit 4096) (EVar 222); a_off := 0 |} (ELit 3727360)
           {| a_base := EMd Instr.M_MUL (ELit 4096) (EVar 453); a_off := 0 |} (ELit 8388608);
         KDisj {| a_base := EMd Instr.M_MUL (ELit 4096) (EVar 93); a_off := 0 |} (ELit 65536)
           {| a_base := EMd Instr.M_MUL (ELit 4096) (EVar 453); a_off := 0 |} (ELit 8388608);
         KDisj {| a_base := EMd Instr.M_MUL (ELit 4096) (EVar 453); a_off := 0 |} (ELit 8388608) {| a_base := ELit 2147446784; a_off := 0 |}
           (ELit 17592186048512);
         KDisj {| a_base := EMd Instr.M_MUL (ELit 4096) (EVar 453); a_off := 0 |} (ELit 8388608) {| a_base := ELit 65536; a_off := 0 |}
           (ELit 6209536);
         KDisj {| a_base := EMd Instr.M_MUL (ELit 4096) (EVar 453); a_off := 0 |} (ELit 8388608)
           {|
             a_base :=
               EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 32768) (EVar 0)) (EMd Instr.M_MUL (ELit 4096) (EAlu Instr.ALU_SRL (EVar 6) (ELit 8)));
             a_off := -8388608
           |} (ELit 2155876352);
         KWord {| a_base := ELit 0; a_off := 1542800 |} 8 (ELit 8388608); KWord {| a_base := ELit 0; a_off := 1542821 |} 3 (ELit 0);
         KWord {| a_base := ELit 0; a_off := 5802656 |} 1 (ELit 0);
         KWord {| a_base := ELit 0; a_off := 5802664 |} 8 (EMd Instr.M_MUL (ELit 4096) (EVar 452));
         KDisj {| a_base := EMd Instr.M_MUL (ELit 512) (EVar 452); a_off := 2147450880 |} (ELit 131072)
           {|
             a_base := EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 4096) (EVar 0)) (EMd Instr.M_MUL (ELit 512) (EAlu Instr.ALU_SRL (EVar 6) (ELit 8)));
             a_off := 2146402304
           |}
           (EAlu Instr.ALU_ADD
              (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit (-4096)) (EVar 0)) (EMd Instr.M_MUL (ELit (-512)) (EAlu Instr.ALU_SRL (EVar 6) (ELit 8))))
              (ELit 17592187092992));
         KDisj {| a_base := EMd Instr.M_MUL (ELit 512) (EVar 452); a_off := 2147450880 |} (ELit 131072) {| a_base := ELit 0; a_off := 2147459072 |}
           (ELit 776192);
         KWr {| a_base := EMd Instr.M_MUL (ELit 512) (EVar 452); a_off := 2147450880 |} (ELit 131072);
         KZero {| a_base := EMd Instr.M_MUL (ELit 512) (EVar 452); a_off := 2147450880 |} (ELit 131072);
         KWr {| a_base := EMd Instr.M_MUL (ELit 4096) (EVar 452); a_off := 0 |} (ELit 1048576); KRange (EVar 452) 1532 34359736064;
         KDisj {| a_base := EMd Instr.M_MUL (ELit 4096) (EVar 401); a_off := 0 |} (ELit 11571200)
           {| a_base := EMd Instr.M_MUL (ELit 4096) (EVar 452); a_off := 0 |} (ELit 1048576);
         KDisj {| a_base := EMd Instr.M_MUL (ELit 4096) (EVar 334); a_off := 0 |} (ELit 4096)
           {| a_base := EMd Instr.M_MUL (ELit 4096) (EVar 452); a_off := 0 |} (ELit 1048576);
         KDisj {| a_base := EMd Instr.M_MUL (ELit 4096) (EVar 269); a_off := 0 |} (ELit 4096)
           {| a_base := EMd Instr.M_MUL (ELit 4096) (EVar 452); a_off := 0 |} (ELit 1048576);
         KDisj {| a_base := EMd Instr.M_MUL (ELit 4096) (EVar 243); a_off := 0 |} (ELit 65536)
           {| a_base := EMd Instr.M_MUL (ELit 4096) (EVar 452); a_off := 0 |} (ELit 1048576);
         KDisj {| a_base := EMd Instr.M_MUL (ELit 4096) (EVar 242); a_off := 0 |} (ELit 4096)
           {| a_base := EMd Instr.M_MUL (ELit 4096) (EVar 452); a_off := 0 |} (ELit 1048576);
         KDisj {| a_base := EMd Instr.M_MUL (ELit 4096) (EVar 241); a_off := 0 |} (ELit 8388608)
           {| a_base := EMd Instr.M_MUL (ELit 4096) (EVar 452); a_off := 0 |} (ELit 1048576);
         KDisj {| a_base := EMd Instr.M_MUL (ELit 4096) (EVar 223); a_off := 0 |} (ELit 137439023104)
           {| a_base := EMd Instr.M_MUL (ELit 4096) (EVar 452); a_off := 0 |} (ELit 1048576);
         KDisj {| a_base := EMd Instr.M_MUL (ELit 4096) (EVar 222); a_off := 0 |} (ELit 3727360)
           {| a_base := EMd Instr.M_MUL (ELit 4096) (EVar 452); a_off := 0 |} (ELit 1048576);
         KDisj {| a_base := EMd Instr.M_MUL (ELit 4096) (EVar 93); a_off := 0 |} (ELit 65536)
           {| a_base := EMd Instr.M_MUL (ELit 4096) (EVar 452); a_off := 0 |} (ELit 1048576);
         KDisj {| a_base := EMd Instr.M_MUL (ELit 4096) (EVar 452); a_off := 0 |} (ELit 1048576) {| a_base := ELit 2147446784; a_off := 0 |}
           (ELit 17592186048512);
         KDisj {| a_base := EMd Instr.M_MUL (ELit 4096) (EVar 452); a_off := 0 |} (ELit 1048576) {| a_base := ELit 65536; a_off := 0 |}
           (ELit 6209536);
         KDisj {| a_base := EMd Instr.M_MUL (ELit 4096) (EVar 452); a_off := 0 |} (ELit 1048576)
           {|
             a_base :=
               EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 32768) (EVar 0)) (EMd Instr.M_MUL (ELit 4096) (EAlu Instr.ALU_SRL (EVar 6) (ELit 8)));
             a_off := -8388608
           |} (ELit 2155876352);
         KWord {| a_base := ELit 0; a_off := 5802657 |} 3 (ELit 0); KWord {| a_base := ELit 0; a_off := 5802648 |} 4 (ELit 1);
         KWord {| a_base := EMd Instr.M_MUL (ELit 4096) (EVar 242); a_off := 3168 |} 1 (ELit 0);
         KWord {| a_base := ELit 0; a_off := 686234 |} 1 (ELit 0);
         KWord {| a_base := ELit 0; a_off := 6134640 |} 8 (EMd Instr.M_MUL (ELit 4096) (EVar 401));
         KWord {| a_base := EMd Instr.M_MUL (ELit 4096) (EVar 242); a_off := 72 |} 8 (EMd Instr.M_MUL (ELit 4096) (EVar 401));
         KWord {| a_base := EMd Instr.M_MUL (ELit 4096) (EVar 401); a_off := 88 |} 8 (ELit 20);
         KDisj {| a_base := EMd Instr.M_MUL (ELit 512) (EVar 401); a_off := 2147450880 |} (ELit 1446400)
           {|
             a_base := EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 4096) (EVar 0)) (EMd Instr.M_MUL (ELit 512) (EAlu Instr.ALU_SRL (EVar 6) (ELit 8)));
             a_off := 2146402304
           |}
           (EAlu Instr.ALU_ADD
              (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit (-4096)) (EVar 0)) (EMd Instr.M_MUL (ELit (-512)) (EAlu Instr.ALU_SRL (EVar 6) (ELit 8))))
              (ELit 17592187092992));
         KDisj {| a_base := EMd Instr.M_MUL (ELit 512) (EVar 401); a_off := 2147450880 |} (ELit 1446400) {| a_base := ELit 0; a_off := 2147459072 |}
           (ELit 776192);
         KWr {| a_base := EMd Instr.M_MUL (ELit 512) (EVar 401); a_off := 2147450880 |} (ELit 1446400);
         KZero {| a_base := EMd Instr.M_MUL (ELit 512) (EVar 401); a_off := 2147450880 |} (ELit 1446400);
         KWr {| a_base := EMd Instr.M_MUL (ELit 4096) (EVar 401); a_off := 0 |} (ELit 11571200);
         KZero {| a_base := EMd Instr.M_MUL (ELit 4096) (EVar 401); a_off := 0 |} (ELit 88);
         KZero {| a_base := EMd Instr.M_MUL (ELit 4096) (EVar 401); a_off := 96 |} (ELit 11571104); KRange (EVar 401) 1532 34359733495;
         KDisj {| a_base := EMd Instr.M_MUL (ELit 4096) (EVar 334); a_off := 0 |} (ELit 4096)
           {| a_base := EMd Instr.M_MUL (ELit 4096) (EVar 401); a_off := 0 |} (ELit 11571200);
         KDisj {| a_base := EMd Instr.M_MUL (ELit 4096) (EVar 269); a_off := 0 |} (ELit 4096)
           {| a_base := EMd Instr.M_MUL (ELit 4096) (EVar 401); a_off := 0 |} (ELit 11571200);
         KDisj {| a_base := EMd Instr.M_MUL (ELit 4096) (EVar 243); a_off := 0 |} (ELit 65536)
           {| a_base := EMd Instr.M_MUL (ELit 4096) (EVar 401); a_off := 0 |} (ELit 11571200);
         KDisj {| a_base := EMd Instr.M_MUL (ELit 4096) (EVar 242); a_off := 0 |} (ELit 4096)
           {| a_base := EMd Instr.M_MUL (ELit 4096) (EVar 401); a_off := 0 |} (ELit 11571200);
         KDisj {| a_base := EMd Instr.M_MUL (ELit 4096) (EVar 241); a_off := 0 |} (ELit 8388608)
           {| a_base := EMd Instr.M_MUL (ELit 4096) (EVar 401); a_off := 0 |} (ELit 11571200);
         KDisj {| a_base := EMd Instr.M_MUL (ELit 4096) (EVar 223); a_off := 0 |} (ELit 137439023104)
           {| a_base := EMd Instr.M_MUL (ELit 4096) (EVar 401); a_off := 0 |} (ELit 11571200);
         KDisj {| a_base := EMd Instr.M_MUL (ELit 4096) (EVar 222); a_off := 0 |} (ELit 3727360)
           {| a_base := EMd Instr.M_MUL (ELit 4096) (EVar 401); a_off := 0 |} (ELit 11571200);
         KDisj {| a_base := EMd Instr.M_MUL (ELit 4096) (EVar 93); a_off := 0 |} (ELit 65536)
           {| a_base := EMd Instr.M_MUL (ELit 4096) (EVar 401); a_off := 0 |} (ELit 11571200);
         KDisj {| a_base := EMd Instr.M_MUL (ELit 4096) (EVar 401); a_off := 0 |} (ELit 11571200) {| a_base := ELit 2147446784; a_off := 0 |}
           (ELit 17592186048512);
         KDisj {| a_base := EMd Instr.M_MUL (ELit 4096) (EVar 401); a_off := 0 |} (ELit 11571200) {| a_base := ELit 65536; a_off := 0 |}
           (ELit 6209536);
         KDisj {| a_base := EMd Instr.M_MUL (ELit 4096) (EVar 401); a_off := 0 |} (ELit 11571200)
           {|
             a_base :=
               EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 32768) (EVar 0)) (EMd Instr.M_MUL (ELit 4096) (EAlu Instr.ALU_SRL (EVar 6) (ELit 8)));
             a_off := -8388608
           |} (ELit 2155876352);
         KWord {| a_base := EMd Instr.M_MUL (ELit 4096) (EVar 242); a_off := 64 |} 8 (ELit 6134648);
         KWord {| a_base := EMd Instr.M_MUL (ELit 4096) (EVar 242); a_off := 16 |} 8
           (EAlu Instr.ALU_ADD (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 32768) (EVar 0)) (EMd Instr.M_MUL (ELit 4096) (EVar 368)))
              (ELit (-8388608)));
         KWord {| a_base := EMd Instr.M_MUL (ELit 4096) (EVar 242); a_off := 8 |} 8
           (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 32768) (EVar 0)) (EMd Instr.M_MUL (ELit 4096) (EVar 368)));
         KWord {| a_base := EMd Instr.M_MUL (ELit 4096) (EVar 242); a_off := 56 |} 8 (ELit 6136708);
         KWord {| a_base := EMd Instr.M_MUL (ELit 4096) (EVar 242); a_off := 48 |} 8 (ELit 6136488);
         KDisj {| a_base := EMd Instr.M_MUL (ELit 512) (EVar 335); a_off := 2147450880 |} (ELit 512)
           {|
             a_base := EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 4096) (EVar 0)) (EMd Instr.M_MUL (ELit 512) (EAlu Instr.ALU_SRL (EVar 6) (ELit 8)));
             a_off := 2146402304
           |}
           (EAlu Instr.ALU_ADD
              (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit (-4096)) (EVar 0)) (EMd Instr.M_MUL (ELit (-512)) (EAlu Instr.ALU_SRL (EVar 6) (ELit 8))))
              (ELit 17592187092992));
         KDisj {| a_base := EMd Instr.M_MUL (ELit 512) (EVar 335); a_off := 2147450880 |} (ELit 512) {| a_base := ELit 0; a_off := 2147459072 |}
           (ELit 776192);
         KRange (EVar 335) 1 34359736319;
         KDisj {| a_base := EMd Instr.M_MUL (ELit 4096) (EVar 334); a_off := 0 |} (ELit 4096)
           {| a_base := EMd Instr.M_MUL (ELit 4096) (EVar 335); a_off := 0 |} (ELit 4096);
         KDisj {| a_base := EMd Instr.M_MUL (ELit 4096) (EVar 269); a_off := 0 |} (ELit 4096)
           {| a_base := EMd Instr.M_MUL (ELit 4096) (EVar 335); a_off := 0 |} (ELit 4096);
         KDisj {| a_base := EMd Instr.M_MUL (ELit 4096) (EVar 243); a_off := 0 |} (ELit 65536)
           {| a_base := EMd Instr.M_MUL (ELit 4096) (EVar 335); a_off := 0 |} (ELit 4096);
         KDisj {| a_base := EMd Instr.M_MUL (ELit 4096) (EVar 242); a_off := 0 |} (ELit 4096)
           {| a_base := EMd Instr.M_MUL (ELit 4096) (EVar 335); a_off := 0 |} (ELit 4096);
         KDisj {| a_base := EMd Instr.M_MUL (ELit 4096) (EVar 241); a_off := 0 |} (ELit 8388608)
           {| a_base := EMd Instr.M_MUL (ELit 4096) (EVar 335); a_off := 0 |} (ELit 4096);
         KDisj {| a_base := EMd Instr.M_MUL (ELit 4096) (EVar 223); a_off := 0 |} (ELit 137439023104)
           {| a_base := EMd Instr.M_MUL (ELit 4096) (EVar 335); a_off := 0 |} (ELit 4096);
         KDisj {| a_base := EMd Instr.M_MUL (ELit 4096) (EVar 222); a_off := 0 |} (ELit 3727360)
           {| a_base := EMd Instr.M_MUL (ELit 4096) (EVar 335); a_off := 0 |} (ELit 4096);
         KDisj {| a_base := EMd Instr.M_MUL (ELit 4096) (EVar 93); a_off := 0 |} (ELit 65536)
           {| a_base := EMd Instr.M_MUL (ELit 4096) (EVar 335); a_off := 0 |} (ELit 4096);
         KDisj {| a_base := EMd Instr.M_MUL (ELit 4096) (EVar 335); a_off := 0 |} (ELit 4096) {| a_base := ELit 2147446784; a_off := 0 |}
           (ELit 17592186048512);
         KDisj {| a_base := EMd Instr.M_MUL (ELit 4096) (EVar 335); a_off := 0 |} (ELit 4096) {| a_base := ELit 65536; a_off := 0 |} (ELit 6209536);
         KDisj {| a_base := EMd Instr.M_MUL (ELit 4096) (EVar 335); a_off := 0 |} (ELit 4096)
           {|
             a_base :=
               EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 32768) (EVar 0)) (EMd Instr.M_MUL (ELit 4096) (EAlu Instr.ALU_SRL (EVar 6) (ELit 8)));
             a_off := -8388608
           |} (ELit 2155876352);
         KWord {| a_base := EMd Instr.M_MUL (ELit 4096) (EVar 334); a_off := 32 |} 8 (ELit 0);
         KWord {| a_base := EMd Instr.M_MUL (ELit 4096) (EVar 334); a_off := 24 |} 8 (ELit 6134640);
         KWord {| a_base := ELit 0; a_off := 669696 |} 1 (ELit 0); KWord {| a_base := ELit 0; a_off := 669697 |} 3 (ELit 0);
         KWord {| a_base := ELit 0; a_off := 6134648 |} 8 (EMd Instr.M_MUL (ELit 4096) (EVar 334));
         KDisj {| a_base := EMd Instr.M_MUL (ELit 512) (EVar 334); a_off := 2147450880 |} (ELit 512)
           {|
             a_base := EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 4096) (EVar 0)) (EMd Instr.M_MUL (ELit 512) (EAlu Instr.ALU_SRL (EVar 6) (ELit 8)));
             a_off := 2146402304
           |}
           (EAlu Instr.ALU_ADD
              (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit (-4096)) (EVar 0)) (EMd Instr.M_MUL (ELit (-512)) (EAlu Instr.ALU_SRL (EVar 6) (ELit 8))))
              (ELit 17592187092992));
         KDisj {| a_base := EMd Instr.M_MUL (ELit 512) (EVar 334); a_off := 2147450880 |} (ELit 512) {| a_base := ELit 0; a_off := 2147459072 |}
           (ELit 776192);
         KWr {| a_base := EMd Instr.M_MUL (ELit 4096) (EVar 334); a_off := 0 |} (ELit 4096);
         KZero {| a_base := EMd Instr.M_MUL (ELit 4096) (EVar 334); a_off := 0 |} (ELit 24); KRange (EVar 334) 1 34359736319;
         KDisj {| a_base := EMd Instr.M_MUL (ELit 4096) (EVar 269); a_off := 0 |} (ELit 4096)
           {| a_base := EMd Instr.M_MUL (ELit 4096) (EVar 334); a_off := 0 |} (ELit 4096);
         KDisj {| a_base := EMd Instr.M_MUL (ELit 4096) (EVar 243); a_off := 0 |} (ELit 65536)
           {| a_base := EMd Instr.M_MUL (ELit 4096) (EVar 334); a_off := 0 |} (ELit 4096);
         KDisj {| a_base := EMd Instr.M_MUL (ELit 4096) (EVar 242); a_off := 0 |} (ELit 4096)
           {| a_base := EMd Instr.M_MUL (ELit 4096) (EVar 334); a_off := 0 |} (ELit 4096);
         KDisj {| a_base := EMd Instr.M_MUL (ELit 4096) (EVar 241); a_off := 0 |} (ELit 8388608)
           {| a_base := EMd Instr.M_MUL (ELit 4096) (EVar 334); a_off := 0 |} (ELit 4096);
         KDisj {| a_base := EMd Instr.M_MUL (ELit 4096) (EVar 223); a_off := 0 |} (ELit 137439023104)
           {| a_base := EMd Instr.M_MUL (ELit 4096) (EVar 334); a_off := 0 |} (ELit 4096);
         KDisj {| a_base := EMd Instr.M_MUL (ELit 4096) (EVar 222); a_off := 0 |} (ELit 3727360)
           {| a_base := EMd Instr.M_MUL (ELit 4096) (EVar 334); a_off := 0 |} (ELit 4096);
         KDisj {| a_base := EMd Instr.M_MUL (ELit 4096) (EVar 93); a_off := 0 |} (ELit 65536)
           {| a_base := EMd Instr.M_MUL (ELit 4096) (EVar 334); a_off := 0 |} (ELit 4096);
         KDisj {| a_base := EMd Instr.M_MUL (ELit 4096) (EVar 334); a_off := 0 |} (ELit 4096) {| a_base := ELit 2147446784; a_off := 0 |}
           (ELit 17592186048512);
         KDisj {| a_base := EMd Instr.M_MUL (ELit 4096) (EVar 334); a_off := 0 |} (ELit 4096) {| a_base := ELit 65536; a_off := 0 |} (ELit 6209536);
         KDisj {| a_base := EMd Instr.M_MUL (ELit 4096) (EVar 334); a_off := 0 |} (ELit 4096)
           {|
             a_base :=
               EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 32768) (EVar 0)) (EMd Instr.M_MUL (ELit 4096) (EAlu Instr.ALU_SRL (EVar 6) (ELit 8)));
             a_off := -8388608
           |} (ELit 2155876352);
         KWord {| a_base := EMd Instr.M_MUL (ELit 4096) (EVar 242); a_off := 40 |} 1 (ELit 0);
         KWord {| a_base := EMd Instr.M_MUL (ELit 4096) (EVar 242); a_off := 32 |} 8 (ELit 0);
         KWord {| a_base := EMd Instr.M_MUL (ELit 4096) (EVar 242); a_off := 24 |} 8 (ELit 0);
         KWord {| a_base := ELit 0; a_off := 6270744 |} 8 (EMd Instr.M_MUL (ELit 4096) (EVar 243));
         KWord {| a_base := EMd Instr.M_MUL (ELit 4096) (EVar 242); a_off := 0 |} 8 (EMd Instr.M_MUL (ELit 4096) (EVar 243));
         KWord {| a_base := EMd Instr.M_MUL (ELit 4096) (EVar 243); a_off := 152 |} 8 (EMd Instr.M_MUL (ELit 4096) (EVar 242));
         KWord {| a_base := EMd Instr.M_MUL (ELit 4096) (EVar 243); a_off := 16 |} 8 (ELit 0);
         KDisj {| a_base := EMd Instr.M_MUL (ELit 512) (EVar 269); a_off := 2147450880 |} (ELit 512)
           {|
             a_base := EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 4096) (EVar 0)) (EMd Instr.M_MUL (ELit 512) (EAlu Instr.ALU_SRL (EVar 6) (ELit 8)));
             a_off := 2146402304
           |}
           (EAlu Instr.ALU_ADD
              (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit (-4096)) (EVar 0)) (EMd Instr.M_MUL (ELit (-512)) (EAlu Instr.ALU_SRL (EVar 6) (ELit 8))))
              (ELit 17592187092992));
         KDisj {| a_base := EMd Instr.M_MUL (ELit 512) (EVar 269); a_off := 2147450880 |} (ELit 512) {| a_base := ELit 0; a_off := 2147459072 |}
           (ELit 776192);
         KWr {| a_base := EMd Instr.M_MUL (ELit 4096) (EVar 269); a_off := 0 |} (ELit 4096); KRange (EVar 269) 1 34359736319;
         KDisj {| a_base := EMd Instr.M_MUL (ELit 4096) (EVar 243); a_off := 0 |} (ELit 65536)
           {| a_base := EMd Instr.M_MUL (ELit 4096) (EVar 269); a_off := 0 |} (ELit 4096);
         KDisj {| a_base := EMd Instr.M_MUL (ELit 4096) (EVar 242); a_off := 0 |} (ELit 4096)
           {| a_base := EMd Instr.M_MUL (ELit 4096) (EVar 269); a_off := 0 |} (ELit 4096);
         KDisj {| a_base := EMd Instr.M_MUL (ELit 4096) (EVar 241); a_off := 0 |} (ELit 8388608)
           {| a_base := EMd Instr.M_MUL (ELit 4096) (EVar 269); a_off := 0 |} (ELit 4096);
         KDisj {| a_base := EMd Instr.M_MUL (ELit 4096) (EVar 223); a_off := 0 |} (ELit 137439023104)
           {| a_base := EMd Instr.M_MUL (ELit 4096) (EVar 269); a_off := 0 |} (ELit 4096);
         KDisj {| a_base := EMd Instr.M_MUL (ELit 4096) (EVar 222); a_off := 0 |} (ELit 3727360)
           {| a_base := EMd Instr.M_MUL (ELit 4096) (EVar 269); a_off := 0 |} (ELit 4096);
         KDisj {| a_base := EMd Instr.M_MUL (ELit 4096) (EVar 93); a_off := 0 |} (ELit 65536)
           {| a_base := EMd Instr.M_MUL (ELit 4096) (EVar 269); a_off := 0 |} (ELit 4096);
         KDisj {| a_base := EMd Instr.M_MUL (ELit 4096) (EVar 269); a_off := 0 |} (ELit 4096) {| a_base := ELit 2147446784; a_off := 0 |}
           (ELit 17592186048512);
         KDisj {| a_base := EMd Instr.M_MUL (ELit 4096) (EVar 269); a_off := 0 |} (ELit 4096) {| a_base := ELit 65536; a_off := 0 |} (ELit 6209536);
         KDisj {| a_base := EMd Instr.M_MUL (ELit 4096) (EVar 269); a_off := 0 |} (ELit 4096)
           {|
             a_base :=
               EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 32768) (EVar 0)) (EMd Instr.M_MUL (ELit 4096) (EAlu Instr.ALU_SRL (EVar 6) (ELit 8)));
             a_off := -8388608
           |} (ELit 2155876352);
         KWord {| a_base := EMd Instr.M_MUL (ELit 4096) (EVar 243); a_off := 0 |} 8 (ELit 648728);
         KWord {| a_base := EMd Instr.M_MUL (ELit 4096) (EVar 243); a_off := 148 |} 2 (ELit 1024);
         KWord {| a_base := EMd Instr.M_MUL (ELit 4096) (EVar 243); a_off := 144 |} 4 (ELit 0);
         KWord {| a_base := EMd Instr.M_MUL (ELit 4096) (EVar 243); a_off := 8 |} 4 (ELit 0);
         KDisj {| a_base := EMd Instr.M_MUL (ELit 512) (EVar 243); a_off := 2147450880 |} (ELit 8192)
           {|
             a_base := EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 4096) (EVar 0)) (EMd Instr.M_MUL (ELit 512) (EAlu Instr.ALU_SRL (EVar 6) (ELit 8)));
             a_off := 2146402304
           |}
           (EAlu Instr.ALU_ADD
              (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit (-4096)) (EVar 0)) (EMd Instr.M_MUL (ELit (-512)) (EAlu Instr.ALU_SRL (EVar 6) (ELit 8))))
              (ELit 17592187092992));
         KDisj {| a_base := EMd Instr.M_MUL (ELit 512) (EVar 243); a_off := 2147450880 |} (ELit 8192) {| a_base := ELit 0; a_off := 2147459072 |}
           (ELit 776192);
         KWr {| a_base := EMd Instr.M_MUL (ELit 4096) (EVar 243); a_off := 0 |} (ELit 65536);
         KZero {| a_base := EMd Instr.M_MUL (ELit 4096) (EVar 243); a_off := 12 |} (ELit 4);
         KZero {| a_base := EMd Instr.M_MUL (ELit 4096) (EVar 243); a_off := 150 |} (ELit 2);
         KZero {| a_base := EMd Instr.M_MUL (ELit 4096) (EVar 243); a_off := 160 |} (ELit 65376); KRange (EVar 243) 1532 34359736304;
         KDisj {| a_base := EMd Instr.M_MUL (ELit 4096) (EVar 242); a_off := 0 |} (ELit 4096)
           {| a_base := EMd Instr.M_MUL (ELit 4096) (EVar 243); a_off := 0 |} (ELit 65536);
         KDisj {| a_base := EMd Instr.M_MUL (ELit 4096) (EVar 241); a_off := 0 |} (ELit 8388608)
           {| a_base := EMd Instr.M_MUL (ELit 4096) (EVar 243); a_off := 0 |} (ELit 65536);
         KDisj {| a_base := EMd Instr.M_MUL (ELit 4096) (EVar 223); a_off := 0 |} (ELit 137439023104)
           {| a_base := EMd Instr.M_MUL (ELit 4096) (EVar 243); a_off := 0 |} (ELit 65536);
         KDisj {| a_base := EMd Instr.M_MUL (ELit 4096) (EVar 222); a_off := 0 |} (ELit 3727360)
           {| a_base := EMd Instr.M_MUL (ELit 4096) (EVar 243); a_off := 0 |} (ELit 65536);
         KDisj {| a_base := EMd Instr.M_MUL (ELit 4096) (EVar 93); a_off := 0 |} (ELit 65536)
           {| a_base := EMd Instr.M_MUL (ELit 4096) (EVar 243); a_off := 0 |} (ELit 65536);
         KDisj {| a_base := EMd Instr.M_MUL (ELit 4096) (EVar 243); a_off := 0 |} (ELit 65536) {| a_base := ELit 2147446784; a_off := 0 |}
           (ELit 17592186048512);
         KDisj {| a_base := EMd Instr.M_MUL (ELit 4096) (EVar 243); a_off := 0 |} (ELit 65536) {| a_base := ELit 65536; a_off := 0 |} (ELit 6209536);
         KDisj {| a_base := EMd Instr.M_MUL (ELit 4096) (EVar 243); a_off := 0 |} (ELit 65536)
           {|
             a_base :=
               EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 32768) (EVar 0)) (EMd Instr.M_MUL (ELit 4096) (EAlu Instr.ALU_SRL (EVar 6) (ELit 8)));
             a_off := -8388608
           |} (ELit 2155876352);
         KDisj {| a_base := EMd Instr.M_MUL (ELit 512) (EVar 242); a_off := 2147450880 |} (ELit 512)
           {|
             a_base := EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 4096) (EVar 0)) (EMd Instr.M_MUL (ELit 512) (EAlu Instr.ALU_SRL (EVar 6) (ELit 8)));
             a_off := 2146402304
           |}
           (EAlu Instr.ALU_ADD
              (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit (-4096)) (EVar 0)) (EMd Instr.M_MUL (ELit (-512)) (EAlu Instr.ALU_SRL (EVar 6) (ELit 8))))
              (ELit 17592187092992));
         KDisj {| a_base := EMd Instr.M_MUL (ELit 512) (EVar 242); a_off := 2147450880 |} (ELit 512) {| a_base := ELit 0; a_off := 2147459072 |}
           (ELit 776192);
         KWr {| a_base := EMd Instr.M_MUL (ELit 4096) (EVar 242); a_off := 0 |} (ELit 4096);
         KZero {| a_base := EMd Instr.M_MUL (ELit 4096) (EVar 242); a_off := 41 |} (ELit 7);
         KZero {| a_base := EMd Instr.M_MUL (ELit 4096) (EVar 242); a_off := 80 |} (ELit 3088);
         KZero {| a_base := EMd Instr.M_MUL (ELit 4096) (EVar 242); a_off := 3169 |} (ELit 927); KRange (EVar 242) 1 34359736319;
         KDisj {| a_base := EMd Instr.M_MUL (ELit 4096) (EVar 241); a_off := 0 |} (ELit 8388608)
           {| a_base := EMd Instr.M_MUL (ELit 4096) (EVar 242); a_off := 0 |} (ELit 4096);
         KDisj {| a_base := EMd Instr.M_MUL (ELit 4096) (EVar 223); a_off := 0 |} (ELit 137439023104)
           {| a_base := EMd Instr.M_MUL (ELit 4096) (EVar 242); a_off := 0 |} (ELit 4096);
         KDisj {| a_base := EMd Instr.M_MUL (ELit 4096) (EVar 222); a_off := 0 |} (ELit 3727360)
           {| a_base := EMd Instr.M_MUL (ELit 4096) (EVar 242); a_off := 0 |} (ELit 4096);
         KDisj {| a_base := EMd Instr.M_MUL (ELit 4096) (EVar 93); a_off := 0 |} (ELit 65536)
           {| a_base := EMd Instr.M_MUL (ELit 4096) (EVar 242); a_off := 0 |} (ELit 4096);
         KDisj {| a_base := EMd Instr.M_MUL (ELit 4096) (EVar 242); a_off := 0 |} (ELit 4096) {| a_base := ELit 2147446784; a_off := 0 |}
           (ELit 17592186048512);
         KDisj {| a_base := EMd Instr.M_MUL (ELit 4096) (EVar 242); a_off := 0 |} (ELit 4096) {| a_base := ELit 65536; a_off := 0 |} (ELit 6209536);
         KDisj {| a_base := EMd Instr.M_MUL (ELit 4096) (EVar 242); a_off := 0 |} (ELit 4096)
           {|
             a_base :=
               EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 32768) (EVar 0)) (EMd Instr.M_MUL (ELit 4096) (EAlu Instr.ALU_SRL (EVar 6) (ELit 8)));
             a_off := -8388608
           |} (ELit 2155876352);
         KWord {| a_base := ELit 0; a_off := 6265800 |} 4 (ELit 1); KWord {| a_base := ELit 0; a_off := 6266080 |} 8 (ELit 455848);
         KWord {| a_base := ELit 0; a_off := 6265824 |} 8 (ELit 583092); KWord {| a_base := ELit 0; a_off := 6265808 |} 8 (ELit 6265816);
         KWord {| a_base := ELit 0; a_off := 1280600 |} 1 (ELit 0); KWord {| a_base := ELit 0; a_off := 686232 |} 1 (ELit 1);
         KWord {| a_base := ELit 0; a_off := 686233 |} 1 (ELit 1); KWord {| a_base := ELit 0; a_off := 672632 |} 8 (ELit 1099511627776);
         KWord {| a_base := ELit 0; a_off := 672642 |} 2 (ELit 2048); KWord {| a_base := ELit 0; a_off := 672640 |} 2 (ELit 16);
         KWord {| a_base := ELit 0; a_off := 672644 |} 1 (ELit 1); KWord {| a_base := ELit 0; a_off := 669897 |} 1 (ELit 0);
         KWord {| a_base := ELit 0; a_off := 669896 |} 1 (ELit 0); KWord {| a_base := ELit 0; a_off := 669824 |} 8 (ELit 1048576);
         KWord {| a_base := ELit 0; a_off := 669816 |} 8 (ELit 241591905); KWord {| a_base := ELit 0; a_off := 669808 |} 8 (ELit 268435456);
         KWord {| a_base := ELit 0; a_off := 669088 |} 8 (EMd Instr.M_MUL (ELit 4096) (EVar 241));
         KWord {| a_base := ELit 0; a_off := 669112 |} 8 (ELit 102840); KWord {| a_base := ELit 0; a_off := 669104 |} 8 (ELit 8388608);
         KWord {| a_base := ELit 0; a_off := 669096 |} 8 (EMd Instr.M_MUL (ELit 4096) (EVar 241));
         KDisj {| a_base := EMd Instr.M_MUL (ELit 512) (EVar 241); a_off := 2147450880 |} (ELit 1048576)
           {|
             a_base := EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 4096) (EVar 0)) (EMd Instr.M_MUL (ELit 512) (EAlu Instr.ALU_SRL (EVar 6) (ELit 8)));
             a_off := 2146402304
           |}
           (EAlu Instr.ALU_ADD
              (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit (-4096)) (EVar 0)) (EMd Instr.M_MUL (ELit (-512)) (EAlu Instr.ALU_SRL (EVar 6) (ELit 8))))
              (ELit 17592187092992));
         KDisj {| a_base := EMd Instr.M_MUL (ELit 512) (EVar 241); a_off := 2147450880 |} (ELit 1048576) {| a_base := ELit 0; a_off := 2147459072 |}
           (ELit 776192);
         KRange (EVar 241) 1532 34359734272;
         KDisj {| a_base := EMd Instr.M_MUL (ELit 4096) (EVar 223); a_off := 0 |} (ELit 137439023104)
           {| a_base := EMd Instr.M_MUL (ELit 4096) (EVar 241); a_off := 0 |} (ELit 8388608);
         KDisj {| a_base := EMd Instr.M_MUL (ELit 4096) (EVar 222); a_off := 0 |} (ELit 3727360)
           {| a_base := EMd Instr.M_MUL (ELit 4096) (EVar 241); a_off := 0 |} (ELit 8388608);
         KDisj {| a_base := EMd Instr.M_MUL (ELit 4096) (EVar 93); a_off := 0 |} (ELit 65536)
           {| a_base := EMd Instr.M_MUL (ELit 4096) (EVar 241); a_off := 0 |} (ELit 8388608);
         KDisj {| a_base := EMd Instr.M_MUL (ELit 4096) (EVar 241); a_off := 0 |} (ELit 8388608) {| a_base := ELit 2147446784; a_off := 0 |}
           (ELit 17592186048512);
         KDisj {| a_base := EMd Instr.M_MUL (ELit 4096) (EVar 241); a_off := 0 |} (ELit 8388608) {| a_base := ELit 65536; a_off := 0 |}
           (ELit 6209536);
         KDisj {| a_base := EMd Instr.M_MUL (ELit 4096) (EVar 241); a_off := 0 |} (ELit 8388608)
           {|
             a_base :=
               EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 32768) (EVar 0)) (EMd Instr.M_MUL (ELit 4096) (EAlu Instr.ALU_SRL (EVar 6) (ELit 8)));
             a_off := -8388608
           |} (ELit 2155876352);
         KWord {| a_base := ELit 0; a_off := 669080 |} 8 (ELit 4096); KWord {| a_base := ELit 0; a_off := 669056 |} 4 (ELit 18446744073709551615);
         KWr
           {|
             a_base := EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 4096) (EVar 223)) (EMd Instr.M_MUL (ELit (-4096)) (EVar 224)); a_off := 137439019008
           |} (ELit 4096);
         KZero
           {|
             a_base := EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 4096) (EVar 223)) (EMd Instr.M_MUL (ELit (-4096)) (EVar 224)); a_off := 137439019008
           |} (ELit 4096);
         KWord {| a_base := ELit 0; a_off := 669064 |} 8
           (EAlu Instr.ALU_ADD (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 4096) (EVar 223)) (EMd Instr.M_MUL (ELit (-4096)) (EVar 224)))
              (ELit 137439019008));
         KWord {| a_base := ELit 0; a_off := 669048 |} 8
           (EAlu Instr.ALU_ADD (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 4096) (EVar 223)) (EMd Instr.M_MUL (ELit (-4096)) (EVar 224))) (ELit 65536));
         KRange (EVar 224) 0 15;
         KRange
           (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit (-4096)) (EVar 224)) (EAlu Instr.ALU_AND (EMd Instr.M_MUL (ELit 4096) (EVar 223)) (ELit 65535)))
           0 0;
         KWord {| a_base := ELit 0; a_off := 669032 |} 8 (ELit 92859); KWord {| a_base := ELit 0; a_off := 669024 |} 8 (ELit 137439023104);
         KWord {| a_base := ELit 0; a_off := 669016 |} 8 (EMd Instr.M_MUL (ELit 4096) (EVar 223));
         KDisj {| a_base := EMd Instr.M_MUL (ELit 512) (EVar 223); a_off := 2147450880 |} (ELit 17179877888)
           {|
             a_base := EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 4096) (EVar 0)) (EMd Instr.M_MUL (ELit 512) (EAlu Instr.ALU_SRL (EVar 6) (ELit 8)));
             a_off := 2146402304
           |}
           (EAlu Instr.ALU_ADD
              (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit (-4096)) (EVar 0)) (EMd Instr.M_MUL (ELit (-512)) (EAlu Instr.ALU_SRL (EVar 6) (ELit 8))))
              (ELit 17592187092992));
         KDisj {| a_base := EMd Instr.M_MUL (ELit 512) (EVar 223); a_off := 2147450880 |} (ELit 17179877888)
           {| a_base := ELit 0; a_off := 2147459072 |} (ELit 776192);
         KRange (EVar 223) 4295491576 34326181871;
         KDisj {| a_base := EMd Instr.M_MUL (ELit 4096) (EVar 222); a_off := 0 |} (ELit 3727360)
           {| a_base := EMd Instr.M_MUL (ELit 4096) (EVar 223); a_off := 0 |} (ELit 137439023104);
         KDisj {| a_base := EMd Instr.M_MUL (ELit 4096) (EVar 93); a_off := 0 |} (ELit 65536)
           {| a_base := EMd Instr.M_MUL (ELit 4096) (EVar 223); a_off := 0 |} (ELit 137439023104);
         KDisj {| a_base := EMd Instr.M_MUL (ELit 4096) (EVar 223); a_off := 0 |} (ELit 137439023104) {| a_base := ELit 2147446784; a_off := 0 |}
           (ELit 17592186048512);
         KDisj {| a_base := EMd Instr.M_MUL (ELit 4096) (EVar 223); a_off := 0 |} (ELit 137439023104) {| a_base := ELit 65536; a_off := 0 |}
           (ELit 6209536);
         KDisj {| a_base := EMd Instr.M_MUL (ELit 4096) (EVar 223); a_off := 0 |} (ELit 137439023104)
           {|
             a_base :=
               EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 32768) (EVar 0)) (EMd Instr.M_MUL (ELit 4096) (EAlu Instr.ALU_SRL (EVar 6) (ELit 8)));
             a_off := -8388608
           |} (ELit 2155876352);
         KWord {| a_base := ELit 0; a_off := 669072 |} 1 (ELit 0); KWord {| a_base := ELit 0; a_off := 1216033 |} 1 (ELit 1);
         KWord {| a_base := ELit 0; a_off := 680996 |} 4 (ELit 0); KWord {| a_base := ELit 0; a_off := 6134552 |} 8 (ELit 6270744);
         KWord {| a_base := ELit 0; a_off := 680992 |} 1 (ELit 1); KWord {| a_base := ELit 0; a_off := 682936 |} 8 (ELit 2147450880);
         KDisj {| a_base := EMd Instr.M_MUL (ELit 512) (EVar 222); a_off := 2147450880 |} (ELit 465920)
           {|
             a_base := EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 4096) (EVar 0)) (EMd Instr.M_MUL (ELit 512) (EAlu Instr.ALU_SRL (EVar 6) (ELit 8)));
             a_off := 2146402304
           |}
           (EAlu Instr.ALU_ADD
              (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit (-4096)) (EVar 0)) (EMd Instr.M_MUL (ELit (-512)) (EAlu Instr.ALU_SRL (EVar 6) (ELit 8))))
              (ELit 17592187092992));
         KDisj {| a_base := EMd Instr.M_MUL (ELit 512) (EVar 222); a_off := 2147450880 |} (ELit 465920) {| a_base := ELit 0; a_off := 2147459072 |}
           (ELit 776192);
         KWr {| a_base := EMd Instr.M_MUL (ELit 4096) (EVar 222); a_off := 0 |} (ELit 3727360); KRange (EVar 222) 1532 34359735410;
         KDisj {| a_base := EMd Instr.M_MUL (ELit 4096) (EVar 93); a_off := 0 |} (ELit 65536)
           {| a_base := EMd Instr.M_MUL (ELit 4096) (EVar 222); a_off := 0 |} (ELit 3727360);
         KDisj {| a_base := EMd Instr.M_MUL (ELit 4096) (EVar 222); a_off := 0 |} (ELit 3727360) {| a_base := ELit 2147446784; a_off := 0 |}
           (ELit 17592186048512);
         KDisj {| a_base := EMd Instr.M_MUL (ELit 4096) (EVar 222); a_off := 0 |} (ELit 3727360) {| a_base := ELit 65536; a_off := 0 |}
           (ELit 6209536);
         KDisj {| a_base := EMd Instr.M_MUL (ELit 4096) (EVar 222); a_off := 0 |} (ELit 3727360)
           {|
             a_base :=
               EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 32768) (EVar 0)) (EMd Instr.M_MUL (ELit 4096) (EAlu Instr.ALU_SRL (EVar 6) (ELit 8)));
             a_off := -8388608
           |} (ELit 2155876352);
         KWord {| a_base := ELit 0; a_off := 1216024 |} 8 (ELit 365856); KWord {| a_base := ELit 0; a_off := 657808 |} 8 (ELit 8);
         KWord {| a_base := ELit 0; a_off := 682944 |} 4 (ELit 1); KWord {| a_base := ELit 0; a_off := 686240 |} 8 (ELit 140737488355327);
         KWord {| a_base := ELit 0; a_off := 686268 |} 4 (ELit 30); KWord {| a_base := ELit 0; a_off := 680988 |} 1 (ELit 1);
         KWord {| a_base := ELit 0; a_off := 680984 |} 4 (ELit 2); KWord {| a_base := ELit 0; a_off := 672774 |} 1 (ELit 1);
         KWord {| a_base := ELit 0; a_off := 1279744 |} 8 (ELit 81553); KWord {| a_base := ELit 0; a_off := 1279752 |} 8 (ELit 128849084416);
         KWord {| a_base := ELit 0; a_off := 1279760 |} 8 (ELit 0); KWord {| a_base := ELit 0; a_off := 1279768 |} 8 (ELit 0);
         KWord {| a_base := ELit 0; a_off := 1279776 |} 8 (ELit 0); KWord {| a_base := ELit 0; a_off := 1279784 |} 8 (ELit 0);
         KWord {| a_base := ELit 0; a_off := 1279792 |} 8 (ELit 1103823372545); KWord {| a_base := ELit 0; a_off := 1279800 |} 8 (ELit 4294967296);
         KWord {| a_base := ELit 0; a_off := 1279808 |} 8 (ELit 0); KWord {| a_base := ELit 0; a_off := 1279816 |} 8 (ELit 0);
         KWord {| a_base := ELit 0; a_off := 1279824 |} 8 (ELit 0); KWord {| a_base := ELit 0; a_off := 1279832 |} 8 (ELit 65537);
         KWord {| a_base := ELit 0; a_off := 1279840 |} 8 (ELit 18446744073709551615); KWord {| a_base := ELit 0; a_off := 1279848 |} 8 (ELit 71687);
         KWord {| a_base := ELit 0; a_off := 1279856 |} 8 (ELit 256); KWord {| a_base := ELit 0; a_off := 1279864 |} 8 (ELit 0);
         KWord {| a_base := ELit 0; a_off := 1279872 |} 8 (ELit 0); KWord {| a_base := ELit 0; a_off := 1279960 |} 8 (ELit 72339073309605888);
         KWord {| a_base := ELit 0; a_off := 1279968 |} 8 (ELit 72340172838076673); KWord {| a_base := ELit 0; a_off := 1279976 |} 8 (ELit 16843009);
         KWord {| a_base := ELit 0; a_off := 1279984 |} 8 (ELit 1103806595073); KWord {| a_base := ELit 0; a_off := 1271384 |} 4 (ELit 0);
         KWord {| a_base := ELit 0; a_off := 672786 |} 1 (ELit 0); KWord {| a_base := ELit 0; a_off := 672716 |} 1 (ELit 0);
         KWord {| a_base := ELit 0; a_off := 672788 |} 4 (ELit 0); KWord {| a_base := ELit 0; a_off := 672784 |} 2 (ELit 1);
         KWord {| a_base := ELit 0; a_off := 672776 |} 8 (ELit 72340172838010881); KWord {| a_base := ELit 0; a_off := 672768 |} 6 (ELit 4294967296);
         KWord {| a_base := ELit 0; a_off := 672775 |} 1 (ELit 0); KWord {| a_base := ELit 0; a_off := 672740 |} 4 (ELit 4096);
         KWord {| a_base := ELit 0; a_off := 672736 |} 1 (ELit 0); KWord {| a_base := ELit 0; a_off := 672728 |} 8 (ELit 85899345936);
         KWord {| a_base := ELit 0; a_off := 672720 |} 8 (ELit 72340168526266369); KWord {| a_base := ELit 0; a_off := 672712 |} 4 (ELit 2048);
         KWord {| a_base := ELit 0; a_off := 672760 |} 8 (ELit 0); KWord {| a_base := ELit 0; a_off := 672756 |} 1 (ELit 1);
         KWord {| a_base := ELit 0; a_off := 672752 |} 4 (ELit 85); KWord {| a_base := ELit 0; a_off := 672744 |} 8 (ELit 816043786240);
         KDisj {| a_base := EMd Instr.M_MUL (ELit 512) (EVar 93); a_off := 2147450880 |} (ELit 8192)
           {|
             a_base := EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 4096) (EVar 0)) (EMd Instr.M_MUL (ELit 512) (EAlu Instr.ALU_SRL (EVar 6) (ELit 8)));
             a_off := 2146402304
           |}
           (EAlu Instr.ALU_ADD
              (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit (-4096)) (EVar 0)) (EMd Instr.M_MUL (ELit (-512)) (EAlu Instr.ALU_SRL (EVar 6) (ELit 8))))
              (ELit 17592187092992));
         KDisj {| a_base := EMd Instr.M_MUL (ELit 512) (EVar 93); a_off := 2147450880 |} (ELit 8192) {| a_base := ELit 0; a_off := 2147459072 |}
           (ELit 776192);
         KWr {| a_base := EMd Instr.M_MUL (ELit 4096) (EVar 93); a_off := 0 |} (ELit 65536); KRange (EVar 93) 1532 34359736304;
         KDisj {| a_base := EMd Instr.M_MUL (ELit 4096) (EVar 93); a_off := 0 |} (ELit 65536) {| a_base := ELit 2147446784; a_off := 0 |}
           (ELit 17592186048512);
         KDisj {| a_base := EMd Instr.M_MUL (ELit 4096) (EVar 93); a_off := 0 |} (ELit 65536) {| a_base := ELit 65536; a_off := 0 |} (ELit 6209536);
         KDisj {| a_base := EMd Instr.M_MUL (ELit 4096) (EVar 93); a_off := 0 |} (ELit 65536)
           {|
             a_base :=
               EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 32768) (EVar 0)) (EMd Instr.M_MUL (ELit 4096) (EAlu Instr.ALU_SRL (EVar 6) (ELit 8)));
             a_off := -8388608
           |} (ELit 2155876352);
         KWord {| a_base := ELit 0; a_off := 1271392 |} 8 (ELit 4096); KWord {| a_base := ELit 0; a_off := 686264 |} 1 (ELit 1);
         KWr
           {|
             a_base := EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 4096) (EVar 0)) (EMd Instr.M_MUL (ELit 512) (EAlu Instr.ALU_SRL (EVar 6) (ELit 8)));
             a_off := 2146402304
           |}
           (EAlu Instr.ALU_ADD
              (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit (-4096)) (EVar 0)) (EMd Instr.M_MUL (ELit (-512)) (EAlu Instr.ALU_SRL (EVar 6) (ELit 8))))
              (ELit 17592187092992));
         KZero
           {|
             a_base := EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 4096) (EVar 0)) (EMd Instr.M_MUL (ELit 512) (EAlu Instr.ALU_SRL (EVar 6) (ELit 8)));
             a_off := 2146402304
           |}
           (EAlu Instr.ALU_ADD
              (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit (-4096)) (EVar 0)) (EMd Instr.M_MUL (ELit (-512)) (EAlu Instr.ALU_SRL (EVar 6) (ELit 8))))
              (ELit 17592187092992));
         KWr {| a_base := EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 4096) (EVar 0)) (EMd Instr.M_MUL (ELit 2) (EVar 6)); a_off := 2146402304 |}
           (EAlu Instr.ALU_ADD (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit (-4096)) (EVar 0)) (EMd Instr.M_MUL (ELit (-2)) (EVar 6)))
              (ELit 17592187092992));
         KZero {| a_base := EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 4096) (EVar 0)) (EMd Instr.M_MUL (ELit 2) (EVar 6)); a_off := 2146402304 |}
           (EAlu Instr.ALU_ADD (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit (-4096)) (EVar 0)) (EMd Instr.M_MUL (ELit (-2)) (EVar 6)))
              (ELit 17592187092992));
         KWr {| a_base := ELit 0; a_off := 2147459072 |} (ELit 776192); KZero {| a_base := ELit 0; a_off := 2147459072 |} (ELit 8653);
         KZero {| a_base := ELit 0; a_off := 2147467732 |} (ELit 2); KZero {| a_base := ELit 0; a_off := 2147467744 |} (ELit 1);
         KZero {| a_base := ELit 0; a_off := 2147467748 |} (ELit 66704); KZero {| a_base := ELit 0; a_off := 2147534492 |} (ELit 682924);
         KZero {| a_base := ELit 0; a_off := 2148217420 |} (ELit 17844);
         KWord {| a_base := ELit 0; a_off := 1271376 |} 8
           (EAlu Instr.ALU_ADD (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 32768) (EVar 0)) (EMd Instr.M_MUL (ELit 16) (EVar 6))) (ELit (-160)));
         KWord {| a_base := ELit 0; a_off := 686235 |} 1 (ELit 0); KWord {| a_base := ELit 0; a_off := 6134624 |} 8 (EVar 60);
         KWord {| a_base := ELit 0; a_off := 6265776 |} 8 (EVar 60); KWord {| a_base := ELit 0; a_off := 6265777 |} 1 (ELit 0); KWord {| a_base := ELit 0; a_off := 6134464 |} 8 (ELit 0);
         KWord {| a_base := ELit 0; a_off := 6134560 |} 8 (ELit 6134560); KWord {| a_base := ELit 0; a_off := 6134472 |} 4 (EVar 43);
         KRange (EVar 43) 1 4194303; KWord {| a_base := ELit 0; a_off := 6134480 |} 4 (ELit 2);
         KWord {| a_base := ELit 0; a_off := 6266368 |} 1 (ELit 1); KWord {| a_base := ELit 0; a_off := 6134632 |} 8 (ELit 6134672);
         KWord {| a_base := ELit 0; a_off := 6134672 |} 8 (ELit 1); KWord {| a_base := ELit 0; a_off := 6134680 |} 8 (ELit 6136688);
         KWord {| a_base := ELit 0; a_off := 6266360 |} 8
           (EAlu Instr.ALU_ADD
              (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 32768) (EVar 0))
                 (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 8) (EVar 1))
                    (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 8) (EVar 2)) (EMd Instr.M_MUL (ELit 16) (EVar 6)))))
              (ELit 184));
         KWord {| a_base := ELit 0; a_off := 6266376 |} 8
           (EAlu Instr.ALU_ADD
              (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 32768) (EVar 0))
                 (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 8) (EVar 1))
                    (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 8) (EVar 2)) (EMd Instr.M_MUL (ELit 16) (EVar 6)))))
              (ELit 24));
         KWord
           {|
             a_base :=
               EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 32768) (EVar 0))
                 (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 8) (EVar 1))
                    (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 8) (EVar 2)) (EMd Instr.M_MUL (ELit 16) (EVar 6))));
             a_off := 72
           |} 8 (ELit 16);
         KWord
           {|
             a_base :=
               EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 32768) (EVar 0))
                 (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 8) (EVar 1))
                    (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 8) (EVar 2)) (EMd Instr.M_MUL (ELit 16) (EVar 6))));
             a_off := 80
           |} 8 (EVar 9);
         KRange (EVar 0) 4294901760 4294967295; KRange (EVar 6) 0 2047;
         KRange
           (EAlu Instr.ALU_ADD
              (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 32768) (EVar 0))
                 (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 8) (EVar 1))
                    (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 8) (EVar 2))
                       (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 8) (EVar 4)) (EMd Instr.M_MUL (ELit 16) (EVar 6))))))
              (ELit 200))
           140735340871872 140737488355328;
         KRange
           (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 4096) (EVar 0))
              (EAlu Instr.ALU_ADD (EVar 1) (EAlu Instr.ALU_ADD (EVar 2) (EAlu Instr.ALU_ADD (EVar 4) (EMd Instr.M_MUL (ELit 2) (EVar 6))))))
           17591917608961 17592186044393;
         KRange (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 32768) (EVar 0)) (EMd Instr.M_MUL (ELit 16) (EVar 6))) 140735340871680 140737488355136;
         KRange (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 4096) (EVar 0)) (EMd Instr.M_MUL (ELit 2) (EVar 6))) 17591917608960 17592186044392;
         KRange (EVar 1) 1 1024; KRange (EVar 2) 0 256; KRange (EVar 3) 0 131071; KRange (EVar 7) 0 131071; KRange (EVar 8) 0 4294967294;
         KRange (EVar 4) 0 280000; KRange (EVar 5) 1532 525820;
         KRange
           (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit (-1)) (EVar 3))
              (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 8) (EVar 4)) (EMd Instr.M_MUL (ELit (-1)) (EVar 7))))
           1 2240000;
         KRange
           (EAlu Instr.ALU_ADD
              (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 32768) (EVar 0))
                 (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 8) (EVar 1))
                    (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 8) (EVar 2)) (EAlu Instr.ALU_ADD (EVar 3) (EMd Instr.M_MUL (ELit 16) (EVar 6))))))
              (ELit 185))
           140735340871865 140737488355312;
         KRange
           (EAlu Instr.ALU_ADD
              (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 32768) (EVar 0))
                 (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 8) (EVar 1))
                    (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 8) (EVar 2))
                       (EAlu Instr.ALU_ADD (EVar 3) (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 16) (EVar 6)) (EVar 7))))))
              (ELit 185))
           140735340871865 140737488355312;
         KWr {| a_base := EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 32768) (EVar 0)) (EMd Instr.M_MUL (ELit 16) (EVar 6)); a_off := -8388608 |}
           (ELit 8388608);
         KWord {| a_base := EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 32768) (EVar 0)) (EMd Instr.M_MUL (ELit 16) (EVar 6)); a_off := 0 |} 8 (EVar 1);
         KWord {| a_base := EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 32768) (EVar 0)) (EMd Instr.M_MUL (ELit 16) (EVar 6)); a_off := 8 |} 8
           (EAlu Instr.ALU_ADD
              (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 32768) (EVar 0))
                 (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 8) (EVar 1))
                    (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 8) (EVar 2)) (EMd Instr.M_MUL (ELit 16) (EVar 6)))))
              (ELit 184));
         KWord {| a_base := EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 32768) (EVar 0)) (EMd Instr.M_MUL (ELit 16) (EVar 6)); a_off := 16 |} 8
           (EMd Instr.M_MUL (EAlu Instr.ALU_SLTU (ELit 1) (EVar 1))
              (EAlu Instr.ALU_ADD
                 (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 32768) (EVar 0))
                    (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 8) (EVar 1))
                       (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 8) (EVar 2)) (EAlu Instr.ALU_ADD (EVar 3) (EMd Instr.M_MUL (ELit 16) (EVar 6))))))
                 (ELit 185)));
         KWord
           {|
             a_base :=
               EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 32768) (EVar 0))
                 (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 8) (EVar 1))
                    (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 8) (EVar 2)) (EMd Instr.M_MUL (ELit 16) (EVar 6))));
             a_off := 24
           |} 8 (ELit 3);
         KWord
           {|
             a_base :=
               EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 32768) (EVar 0))
                 (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 8) (EVar 1))
                    (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 8) (EVar 2)) (EMd Instr.M_MUL (ELit 16) (EVar 6))));
             a_off := 32
           |} 8 (ELit 65600);
         KWord
           {|
             a_base :=
               EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 32768) (EVar 0))
                 (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 8) (EVar 1))
                    (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 8) (EVar 2)) (EMd Instr.M_MUL (ELit 16) (EVar 6))));
             a_off := 40
           |} 8 (ELit 4);
         KWord
           {|
             a_base :=
               EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 32768) (EVar 0))
                 (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 8) (EVar 1))
                    (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 8) (EVar 2)) (EMd Instr.M_MUL (ELit 16) (EVar 6))));
             a_off := 48
           |} 8 (ELit 56);
         KWord
           {|
             a_base :=
               EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 32768) (EVar 0))
                 (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 8) (EVar 1))
                    (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 8) (EVar 2)) (EMd Instr.M_MUL (ELit 16) (EVar 6))));
             a_off := 56
           |} 8 (ELit 5);
         KWord
           {|
             a_base :=
               EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 32768) (EVar 0))
                 (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 8) (EVar 1))
                    (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 8) (EVar 2)) (EMd Instr.M_MUL (ELit 16) (EVar 6))));
             a_off := 64
           |} 8 (ELit 11);
         KWord
           {|
             a_base :=
               EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 32768) (EVar 0))
                 (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 8) (EVar 1))
                    (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 8) (EVar 2)) (EMd Instr.M_MUL (ELit 16) (EVar 6))));
             a_off := 88
           |} 8 (ELit 6);
         KWord
           {|
             a_base :=
               EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 32768) (EVar 0))
                 (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 8) (EVar 1))
                    (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 8) (EVar 2)) (EMd Instr.M_MUL (ELit 16) (EVar 6))));
             a_off := 96
           |} 8 (ELit 4096);
         KWord
           {|
             a_base :=
               EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 32768) (EVar 0))
                 (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 8) (EVar 1))
                    (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 8) (EVar 2)) (EMd Instr.M_MUL (ELit 16) (EVar 6))));
             a_off := 104
           |} 8 (ELit 11);
         KWord
           {|
             a_base :=
               EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 32768) (EVar 0))
                 (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 8) (EVar 1))
                    (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 8) (EVar 2)) (EMd Instr.M_MUL (ELit 16) (EVar 6))));
             a_off := 112
           |} 8 (EVar 8);
         KWord
           {|
             a_base :=
               EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 32768) (EVar 0))
                 (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 8) (EVar 1))
                    (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 8) (EVar 2)) (EMd Instr.M_MUL (ELit 16) (EVar 6))));
             a_off := 120
           |} 8 (ELit 12);
         KWord
           {|
             a_base :=
               EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 32768) (EVar 0))
                 (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 8) (EVar 1))
                    (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 8) (EVar 2)) (EMd Instr.M_MUL (ELit 16) (EVar 6))));
             a_off := 128
           |} 8 (EVar 8);
         KWord
           {|
             a_base :=
               EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 32768) (EVar 0))
                 (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 8) (EVar 1))
                    (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 8) (EVar 2)) (EMd Instr.M_MUL (ELit 16) (EVar 6))));
             a_off := 136
           |} 8 (ELit 23);
         KWord
           {|
             a_base :=
               EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 32768) (EVar 0))
                 (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 8) (EVar 1))
                    (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 8) (EVar 2)) (EMd Instr.M_MUL (ELit 16) (EVar 6))));
             a_off := 144
           |} 8 (ELit 0);
         KWord
           {|
             a_base :=
               EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 32768) (EVar 0))
                 (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 8) (EVar 1))
                    (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 8) (EVar 2)) (EMd Instr.M_MUL (ELit 16) (EVar 6))));
             a_off := 152
           |} 8 (ELit 25);
         KWord
           {|
             a_base :=
               EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 32768) (EVar 0))
                 (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 8) (EVar 1))
                    (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 8) (EVar 2)) (EMd Instr.M_MUL (ELit 16) (EVar 6))));
             a_off := 160
           |} 8
           (EAlu Instr.ALU_ADD
              (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 32768) (EVar 0))
                 (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 8) (EVar 1))
                    (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 8) (EVar 2))
                       (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 8) (EVar 4)) (EMd Instr.M_MUL (ELit 16) (EVar 6))))))
              (ELit 184));
         KWord
           {|
             a_base :=
               EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 32768) (EVar 0))
                 (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 8) (EVar 1))
                    (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 8) (EVar 2)) (EMd Instr.M_MUL (ELit 16) (EVar 6))));
             a_off := 168
           |} 8 (ELit 0);
         KWord
           {|
             a_base :=
               EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 32768) (EVar 0))
                 (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 8) (EVar 1))
                    (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 8) (EVar 2)) (EMd Instr.M_MUL (ELit 16) (EVar 6))));
             a_off := 176
           |} 8 (ELit 0);
         KImg 65536 657808; KImg 657824 657832; KImg 657836 668928; KImg 668937 669016; KImg 669040 669048; KImg 669060 669064; 
         KImg 669073 669080; KImg 669120 669696; KImg 669700 669808; KImg 669832 669896; KImg 669898 672632; KImg 672645 672696; 
         KImg 672717 672720; KImg 672737 672740; KImg 672757 672760; KImg 672787 672788; KImg 672793 672796; KImg 672812 672816; 
         KImg 672817 672824; KImg 672856 672880; KImg 672888 672952; KImg 677736 680952; KImg 680955 680956; KImg 680976 680984; 
         KImg 680989 680992; KImg 680993 680996; KImg 681000 682936; KImg 682948 686232; KImg 686236 686240; KImg 686248 686264; 
         KImg 686265 686268; KImg 686272 686384; KImg 686400 687104; KImg 687112 687168; KImg 687180 687184; KImg 687213 687272; 
         KImg 687273 687280; KImg 687281 687288; KImg 687312 687320; KImg 687404 687408; KImg 687548 1216008; KImg 1216032 1216033;
         KImg 1216034 1271376; KImg 1271388 1271392; KImg 1271400 1271424; KImg 1275519 1275520; KImg 1279615 1279712; KImg 1279716 1279720;
         KImg 1280008 1280208; KImg 1280216 1280248; KImg 1280256 1280272; KImg 1280296 1280328; KImg 1280329 1280600; KImg 1280601 1542792;
         KImg 5802652 5802656; KImg 5802660 5802664; KImg 5802672 6066048; KImg 6066049 6066052; KImg 6066071 6066072; KImg 6066076 6066080;
         KImg 6066092 6066496; KImg 6066504 6066560; KImg 6066572 6066576; KImg 6066638 6066664; KImg 6066665 6066672; KImg 6066676 6066680;
         KImg 6066682 6066688; KImg 6066698 6134432; KImg 6134476 6134480; KImg 6134484 6134490; KImg 6134491 6134552; KImg 6134568 6134592;
         KImg 6134600 6134624; KImg 6134656 6134672; KImg 6134688 6265736; KImg 6265784 6265800; KImg 6265804 6265808; KImg 6265816 6265824;
         KImg 6265832 6266080; KImg 6266088 6266352; KImg 6266369 6266376; KImg 6266424 6266472; KImg 6266480 6266496; KImg 6266512 6266520;
         KImg 6266576 6266592; KImg 6266600 6266696; KImg 6266704 6266728; KImg 6266736 6266760; KImg 6266768 6266976; KImg 6266984 6267080;
         KImg 6267088 6267112; KImg 6267120 6267144; KImg 6267152 6267408; KImg 6267409 6267416; KImg 6267424 6269640; KImg 6269648 6269656;
         KImg 6269664 6270680; KImg 6270684 6270688; KImg 6270692 6270744; KImg 6270752 6275072;
         KWr {| a_base := ELit 0; a_off := 647168 |} (ELit 5627904)]
        622;
    a_maps :=
      [{| am_base := EMd Instr.M_MUL (ELit 4096) (EVar 470); am_len := ELit 4096; am_kind := KRW |};
       {| am_base := EMd Instr.M_MUL (ELit 4096) (EVar 453); am_len := ELit 8388608; am_kind := KRWLAZY |};
       {| am_base := EMd Instr.M_MUL (ELit 4096) (EVar 452); am_len := ELit 1048576; am_kind := KRW |};
       {| am_base := ELit 0; am_len := ELit 8192; am_kind := KFOG |}; {| am_base := ELit 0; am_len := ELit 8192; am_kind := KFOG |};
       {| am_base := EMd Instr.M_MUL (ELit 4096) (EVar 401); am_len := ELit 11571200; am_kind := KRW |};
       {| am_base := EMd Instr.M_MUL (ELit 4096) (EVar 334); am_len := ELit 4096; am_kind := KRW |};
       {| am_base := EMd Instr.M_MUL (ELit 4096) (EVar 269); am_len := ELit 4096; am_kind := KRW |};
       {| am_base := EMd Instr.M_MUL (ELit 4096) (EVar 243); am_len := ELit 65536; am_kind := KRW |};
       {| am_base := EMd Instr.M_MUL (ELit 4096) (EVar 242); am_len := ELit 4096; am_kind := KRW |};
       {| am_base := EMd Instr.M_MUL (ELit 4096) (EVar 241); am_len := ELit 8388608; am_kind := KNONELAZY |};
       {| am_base := EMd Instr.M_MUL (ELit 4096) (EVar 223); am_len := ELit 137439023104; am_kind := KRW |};
       {| am_base := EMd Instr.M_MUL (ELit 4096) (EVar 222); am_len := ELit 3727360; am_kind := KRW |};
       {| am_base := EMd Instr.M_MUL (ELit 4096) (EVar 93); am_len := ELit 65536; am_kind := KRW |};
       {| am_base := ELit 2201439137792; am_len := ELit 15392894357504; am_kind := KRWLAZY |};
       {| am_base := ELit 2415882240; am_len := ELit 2199023255552; am_kind := KNONELAZY |};
       {| am_base := ELit 2147446784; am_len := ELit 268435456; am_kind := KRWLAZY |}];
    a_totsz := 17729664569344;
    a_ylo := 23387528589312;
    a_eager := 16515072;
    a_vis :=
      [(EMd Instr.M_MUL (ELit 4096) (EVar 470), ELit 4096); (EMd Instr.M_MUL (ELit 4096) (EVar 453), ELit 8388608);
       (EMd Instr.M_MUL (ELit 4096) (EVar 452), ELit 1048576); (EMd Instr.M_MUL (ELit 4096) (EVar 401), ELit 11571200);
       (EMd Instr.M_MUL (ELit 4096) (EVar 334), ELit 4096); (EMd Instr.M_MUL (ELit 4096) (EVar 269), ELit 4096);
       (EMd Instr.M_MUL (ELit 4096) (EVar 243), ELit 65536); (EMd Instr.M_MUL (ELit 4096) (EVar 242), ELit 4096);
       (EAlu Instr.ALU_ADD (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 4096) (EVar 223)) (EMd Instr.M_MUL (ELit (-4096)) (EVar 224)))
          (ELit 137439019008),
        ELit 4096);
       (EMd Instr.M_MUL (ELit 4096) (EVar 222), ELit 3727360); (EMd Instr.M_MUL (ELit 4096) (EVar 93), ELit 65536); (ELit 65536, ELit 6209536);
       (EAlu Instr.ALU_ADD
          (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 32768) (EVar 0)) (EMd Instr.M_MUL (ELit 4096) (EAlu Instr.ALU_SRL (EVar 6) (ELit 8))))
          (ELit (-8388608)),
        EAlu Instr.ALU_ADD
          (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit (-32768)) (EVar 0)) (EMd Instr.M_MUL (ELit (-4096)) (EAlu Instr.ALU_SRL (EVar 6) (ELit 8))))
          (ELit 140737496743936));
       (EAlu Instr.ALU_ADD (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 32768) (EVar 0)) (EMd Instr.M_MUL (ELit 16) (EVar 6))) (ELit (-8388608)),
        EAlu Instr.ALU_ADD (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit (-32768)) (EVar 0)) (EMd Instr.M_MUL (ELit (-16)) (EVar 6)))
          (ELit 140737496743936))];
    a_ghost :=
      [(EMd Instr.M_MUL (ELit 4096) (EVar 335), ELit 4096); (EMd Instr.M_MUL (ELit 4096) (EVar 619), ELit 8192);
       (EMd Instr.M_MUL (ELit 4096) (EVar 620), ELit 4096)];
    a_abytes := 4886044672;
    a_brk := EVar 621;
    a_fd := FdStd;
    a_tidset := true
  |}.

(* [comment removed for export] *)
Definition HS_asan (h : nat) : option acs := match h with O => HS0 | _ => None end.
