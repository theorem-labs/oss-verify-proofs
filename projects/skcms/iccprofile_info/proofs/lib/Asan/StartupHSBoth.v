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
      SS 522868
        [ELit 0; ELit 585016;
         EAlu Instr.ALU_ADD (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 32768) (EVar 0)) (EMd Instr.M_MUL (ELit 16) (EVar 6))) (ELit (-48));
         ELit 67584; ELit 6138224; EVar 607; EVar 608; EVar 609;
         EAlu Instr.ALU_ADD (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 32768) (EVar 0)) (EMd Instr.M_MUL (ELit 16) (EVar 6))) (ELit 8); 
         EVar 1; EVar 1;
         EAlu Instr.ALU_ADD (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 32768) (EVar 0)) (EMd Instr.M_MUL (ELit 16) (EVar 6))) (ELit 8);
         EAlu Instr.ALU_ADD
           (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 32768) (EVar 0))
              (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 8) (EVar 1)) (EMd Instr.M_MUL (ELit 16) (EVar 6))))
           (ELit 16);
         EVar 610; EVar 611; EVar 612; EVar 613; EVar 614; ELit 522868;
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
         KRange (EVar 621) 6279168 2153771008; KRange (EVar 620) 1 34359736319;
         KDisj {| a_base := EMd Instr.M_MUL (ELit 4096) (EVar 620); a_off := 0 |} (ELit 4096)
           {| a_base := EMd Instr.M_MUL (ELit 4096) (EVar 470); a_off := 0 |} (ELit 4096);
         KDisj {| a_base := EMd Instr.M_MUL (ELit 4096) (EVar 620); a_off := 0 |} (ELit 4096)
           {| a_base := EMd Instr.M_MUL (ELit 4096) (EVar 453); a_off := 0 |} (ELit 8388608);
         KDisj {| a_base := EMd Instr.M_MUL (ELit 4096) (EVar 620); a_off := 0 |} (ELit 4096)
           {| a_base := EMd Instr.M_MUL (ELit 4096) (EVar 452); a_off := 0 |} (ELit 1048576);
         KDisj {| a_base := EMd Instr.M_MUL (ELit 4096) (EVar 620); a_off := 0 |} (ELit 4096) {| a_base := ELit 2147446784; a_off := 0 |}
           (ELit 17592186048512);
         KDisj {| a_base := EMd Instr.M_MUL (ELit 4096) (EVar 620); a_off := 0 |} (ELit 4096) {| a_base := ELit 65536; a_off := 0 |} (ELit 6213632);
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
         KWord {| a_base := ELit 0; a_off := 676464 |} 8 (ELit 0); KWord {| a_base := ELit 0; a_off := 672520 |} 1 (ELit 1);
         KWord {| a_base := ELit 0; a_off := 672512 |} 8 (ELit 1); KFill {| a_base := ELit 0; a_off := 2147534906 |} (ELit 32) 249;
         KWord {| a_base := ELit 0; a_off := 2148217864 |} 1 (ELit 4); KFill {| a_base := ELit 0; a_off := 2148217865 |} (ELit 3) 249;
         KWord {| a_base := ELit 0; a_off := 2147467741 |} 1 (ELit 3); KFill {| a_base := ELit 0; a_off := 2147467742 |} (ELit 2) 249;
         KWord {| a_base := ELit 0; a_off := 2147467736 |} 1 (ELit 6); KFill {| a_base := ELit 0; a_off := 2147467737 |} (ELit 3) 249;
         KWord {| a_base := ELit 0; a_off := 2147467730 |} 1 (ELit 4); KFill {| a_base := ELit 0; a_off := 2147467731 |} (ELit 5) 249;
         KDisj {| a_base := EMd Instr.M_MUL (ELit 512) (EVar 470); a_off := 2147450880 |} (ELit 512)
           {|
             a_base := EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 4096) (EVar 0)) (EMd Instr.M_MUL (ELit 512) (EAlu Instr.ALU_SRL (EVar 6) (ELit 8)));
             a_off := 2146402304
           |}
           (EAlu Instr.ALU_ADD
              (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit (-4096)) (EVar 0)) (EMd Instr.M_MUL (ELit (-512)) (EAlu Instr.ALU_SRL (EVar 6) (ELit 8))))
              (ELit 17592187092992));
         KDisj {| a_base := EMd Instr.M_MUL (ELit 512) (EVar 470); a_off := 2147450880 |} (ELit 512) {| a_base := ELit 0; a_off := 2147459072 |}
           (ELit 776704);
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
         KDisj {| a_base := EMd Instr.M_MUL (ELit 4096) (EVar 470); a_off := 0 |} (ELit 4096) {| a_base := ELit 65536; a_off := 0 |} (ELit 6213632);
         KDisj {| a_base := EMd Instr.M_MUL (ELit 4096) (EVar 470); a_off := 0 |} (ELit 4096)
           {|
             a_base :=
               EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 32768) (EVar 0)) (EMd Instr.M_MUL (ELit 4096) (EAlu Instr.ALU_SRL (EVar 6) (ELit 8)));
             a_off := -8388608
           |} (ELit 2155876352);
         KInv 0 [ELit 1611928; ELit 1546376; ELit 100; EMd Instr.M_MUL (ELit 4096) (EVar 452); EMd Instr.M_MUL (ELit 4096) (EVar 453)];
         KWord {| a_base := EMd Instr.M_MUL (ELit 4096) (EVar 453); a_off := 8 |} 8 (ELit 255608);
         KWord {| a_base := ELit 0; a_off := 1546404 |} 1 (ELit 0);
         KWord {| a_base := ELit 0; a_off := 1546392 |} 8 (EMd Instr.M_MUL (ELit 4096) (EVar 453));
         KDisj {| a_base := EMd Instr.M_MUL (ELit 512) (EVar 453); a_off := 2147450880 |} (ELit 1048576)
           {|
             a_base := EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 4096) (EVar 0)) (EMd Instr.M_MUL (ELit 512) (EAlu Instr.ALU_SRL (EVar 6) (ELit 8)));
             a_off := 2146402304
           |}
           (EAlu Instr.ALU_ADD
              (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit (-4096)) (EVar 0)) (EMd Instr.M_MUL (ELit (-512)) (EAlu Instr.ALU_SRL (EVar 6) (ELit 8))))
              (ELit 17592187092992));
         KDisj {| a_base := EMd Instr.M_MUL (ELit 512) (EVar 453); a_off := 2147450880 |} (ELit 1048576) {| a_base := ELit 0; a_off := 2147459072 |}
           (ELit 776704);
         KWr {| a_base := EMd Instr.M_MUL (ELit 512) (EVar 453); a_off := 2147450880 |} (ELit 1048576);
         KZero {| a_base := EMd Instr.M_MUL (ELit 512) (EVar 453); a_off := 2147450880 |} (ELit 1048576);
         KWr {| a_base := EMd Instr.M_MUL (ELit 4096) (EVar 453); a_off := 0 |} (ELit 8388608); KRange (EVar 453) 1533 34359734272;
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
           (ELit 6213632);
         KDisj {| a_base := EMd Instr.M_MUL (ELit 4096) (EVar 453); a_off := 0 |} (ELit 8388608)
           {|
             a_base :=
               EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 32768) (EVar 0)) (EMd Instr.M_MUL (ELit 4096) (EAlu Instr.ALU_SRL (EVar 6) (ELit 8)));
             a_off := -8388608
           |} (ELit 2155876352);
         KWord {| a_base := ELit 0; a_off := 1546384 |} 8 (ELit 8388608); KWord {| a_base := ELit 0; a_off := 1546405 |} 3 (ELit 0);
         KWord {| a_base := ELit 0; a_off := 5806240 |} 1 (ELit 0);
         KWord {| a_base := ELit 0; a_off := 5806248 |} 8 (EMd Instr.M_MUL (ELit 4096) (EVar 452));
         KDisj {| a_base := EMd Instr.M_MUL (ELit 512) (EVar 452); a_off := 2147450880 |} (ELit 131072)
           {|
             a_base := EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 4096) (EVar 0)) (EMd Instr.M_MUL (ELit 512) (EAlu Instr.ALU_SRL (EVar 6) (ELit 8)));
             a_off := 2146402304
           |}
           (EAlu Instr.ALU_ADD
              (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit (-4096)) (EVar 0)) (EMd Instr.M_MUL (ELit (-512)) (EAlu Instr.ALU_SRL (EVar 6) (ELit 8))))
              (ELit 17592187092992));
         KDisj {| a_base := EMd Instr.M_MUL (ELit 512) (EVar 452); a_off := 2147450880 |} (ELit 131072) {| a_base := ELit 0; a_off := 2147459072 |}
           (ELit 776704);
         KWr {| a_base := EMd Instr.M_MUL (ELit 512) (EVar 452); a_off := 2147450880 |} (ELit 131072);
         KZero {| a_base := EMd Instr.M_MUL (ELit 512) (EVar 452); a_off := 2147450880 |} (ELit 131072);
         KWr {| a_base := EMd Instr.M_MUL (ELit 4096) (EVar 452); a_off := 0 |} (ELit 1048576); KRange (EVar 452) 1533 34359736064;
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
           (ELit 6213632);
         KDisj {| a_base := EMd Instr.M_MUL (ELit 4096) (EVar 452); a_off := 0 |} (ELit 1048576)
           {|
             a_base :=
               EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 32768) (EVar 0)) (EMd Instr.M_MUL (ELit 4096) (EAlu Instr.ALU_SRL (EVar 6) (ELit 8)));
             a_off := -8388608
           |} (ELit 2155876352);
         KWord {| a_base := ELit 0; a_off := 5806241 |} 3 (ELit 0); KWord {| a_base := ELit 0; a_off := 5806232 |} 4 (ELit 1);
         KWord {| a_base := EMd Instr.M_MUL (ELit 4096) (EVar 242); a_off := 3168 |} 1 (ELit 0);
         KWord {| a_base := ELit 0; a_off := 689818 |} 1 (ELit 0);
         KWord {| a_base := ELit 0; a_off := 6138224 |} 8 (EMd Instr.M_MUL (ELit 4096) (EVar 401));
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
           (ELit 776704);
         KWr {| a_base := EMd Instr.M_MUL (ELit 512) (EVar 401); a_off := 2147450880 |} (ELit 1446400);
         KZero {| a_base := EMd Instr.M_MUL (ELit 512) (EVar 401); a_off := 2147450880 |} (ELit 1446400);
         KWr {| a_base := EMd Instr.M_MUL (ELit 4096) (EVar 401); a_off := 0 |} (ELit 11571200);
         KZero {| a_base := EMd Instr.M_MUL (ELit 4096) (EVar 401); a_off := 0 |} (ELit 88);
         KZero {| a_base := EMd Instr.M_MUL (ELit 4096) (EVar 401); a_off := 96 |} (ELit 11571104); KRange (EVar 401) 1533 34359733495;
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
           (ELit 6213632);
         KDisj {| a_base := EMd Instr.M_MUL (ELit 4096) (EVar 401); a_off := 0 |} (ELit 11571200)
           {|
             a_base :=
               EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 32768) (EVar 0)) (EMd Instr.M_MUL (ELit 4096) (EAlu Instr.ALU_SRL (EVar 6) (ELit 8)));
             a_off := -8388608
           |} (ELit 2155876352);
         KWord {| a_base := EMd Instr.M_MUL (ELit 4096) (EVar 242); a_off := 64 |} 8 (ELit 6138232);
         KWord {| a_base := EMd Instr.M_MUL (ELit 4096) (EVar 242); a_off := 16 |} 8
           (EAlu Instr.ALU_ADD (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 32768) (EVar 0)) (EMd Instr.M_MUL (ELit 4096) (EVar 368)))
              (ELit (-8388608)));
         KWord {| a_base := EMd Instr.M_MUL (ELit 4096) (EVar 242); a_off := 8 |} 8
           (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 32768) (EVar 0)) (EMd Instr.M_MUL (ELit 4096) (EVar 368)));
         KWord {| a_base := EMd Instr.M_MUL (ELit 4096) (EVar 242); a_off := 56 |} 8 (ELit 6140292);
         KWord {| a_base := EMd Instr.M_MUL (ELit 4096) (EVar 242); a_off := 48 |} 8 (ELit 6140072);
         KDisj {| a_base := EMd Instr.M_MUL (ELit 512) (EVar 335); a_off := 2147450880 |} (ELit 512)
           {|
             a_base := EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 4096) (EVar 0)) (EMd Instr.M_MUL (ELit 512) (EAlu Instr.ALU_SRL (EVar 6) (ELit 8)));
             a_off := 2146402304
           |}
           (EAlu Instr.ALU_ADD
              (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit (-4096)) (EVar 0)) (EMd Instr.M_MUL (ELit (-512)) (EAlu Instr.ALU_SRL (EVar 6) (ELit 8))))
              (ELit 17592187092992));
         KDisj {| a_base := EMd Instr.M_MUL (ELit 512) (EVar 335); a_off := 2147450880 |} (ELit 512) {| a_base := ELit 0; a_off := 2147459072 |}
           (ELit 776704);
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
         KDisj {| a_base := EMd Instr.M_MUL (ELit 4096) (EVar 335); a_off := 0 |} (ELit 4096) {| a_base := ELit 65536; a_off := 0 |} (ELit 6213632);
         KDisj {| a_base := EMd Instr.M_MUL (ELit 4096) (EVar 335); a_off := 0 |} (ELit 4096)
           {|
             a_base :=
               EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 32768) (EVar 0)) (EMd Instr.M_MUL (ELit 4096) (EAlu Instr.ALU_SRL (EVar 6) (ELit 8)));
             a_off := -8388608
           |} (ELit 2155876352);
         KWord {| a_base := EMd Instr.M_MUL (ELit 4096) (EVar 334); a_off := 32 |} 8 (ELit 0);
         KWord {| a_base := EMd Instr.M_MUL (ELit 4096) (EVar 334); a_off := 24 |} 8 (ELit 6138224);
         KWord {| a_base := ELit 0; a_off := 673280 |} 1 (ELit 0); KWord {| a_base := ELit 0; a_off := 673281 |} 3 (ELit 0);
         KWord {| a_base := ELit 0; a_off := 6138232 |} 8 (EMd Instr.M_MUL (ELit 4096) (EVar 334));
         KDisj {| a_base := EMd Instr.M_MUL (ELit 512) (EVar 334); a_off := 2147450880 |} (ELit 512)
           {|
             a_base := EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 4096) (EVar 0)) (EMd Instr.M_MUL (ELit 512) (EAlu Instr.ALU_SRL (EVar 6) (ELit 8)));
             a_off := 2146402304
           |}
           (EAlu Instr.ALU_ADD
              (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit (-4096)) (EVar 0)) (EMd Instr.M_MUL (ELit (-512)) (EAlu Instr.ALU_SRL (EVar 6) (ELit 8))))
              (ELit 17592187092992));
         KDisj {| a_base := EMd Instr.M_MUL (ELit 512) (EVar 334); a_off := 2147450880 |} (ELit 512) {| a_base := ELit 0; a_off := 2147459072 |}
           (ELit 776704);
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
         KDisj {| a_base := EMd Instr.M_MUL (ELit 4096) (EVar 334); a_off := 0 |} (ELit 4096) {| a_base := ELit 65536; a_off := 0 |} (ELit 6213632);
         KDisj {| a_base := EMd Instr.M_MUL (ELit 4096) (EVar 334); a_off := 0 |} (ELit 4096)
           {|
             a_base :=
               EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 32768) (EVar 0)) (EMd Instr.M_MUL (ELit 4096) (EAlu Instr.ALU_SRL (EVar 6) (ELit 8)));
             a_off := -8388608
           |} (ELit 2155876352);
         KWord {| a_base := EMd Instr.M_MUL (ELit 4096) (EVar 242); a_off := 40 |} 1 (ELit 0);
         KWord {| a_base := EMd Instr.M_MUL (ELit 4096) (EVar 242); a_off := 32 |} 8 (ELit 0);
         KWord {| a_base := EMd Instr.M_MUL (ELit 4096) (EVar 242); a_off := 24 |} 8 (ELit 0);
         KWord {| a_base := ELit 0; a_off := 6274328 |} 8 (EMd Instr.M_MUL (ELit 4096) (EVar 243));
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
           (ELit 776704);
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
         KDisj {| a_base := EMd Instr.M_MUL (ELit 4096) (EVar 269); a_off := 0 |} (ELit 4096) {| a_base := ELit 65536; a_off := 0 |} (ELit 6213632);
         KDisj {| a_base := EMd Instr.M_MUL (ELit 4096) (EVar 269); a_off := 0 |} (ELit 4096)
           {|
             a_base :=
               EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 32768) (EVar 0)) (EMd Instr.M_MUL (ELit 4096) (EAlu Instr.ALU_SRL (EVar 6) (ELit 8)));
             a_off := -8388608
           |} (ELit 2155876352);
         KWord {| a_base := EMd Instr.M_MUL (ELit 4096) (EVar 243); a_off := 0 |} 8 (ELit 652360);
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
           (ELit 776704);
         KWr {| a_base := EMd Instr.M_MUL (ELit 4096) (EVar 243); a_off := 0 |} (ELit 65536);
         KZero {| a_base := EMd Instr.M_MUL (ELit 4096) (EVar 243); a_off := 12 |} (ELit 4);
         KZero {| a_base := EMd Instr.M_MUL (ELit 4096) (EVar 243); a_off := 150 |} (ELit 2);
         KZero {| a_base := EMd Instr.M_MUL (ELit 4096) (EVar 243); a_off := 160 |} (ELit 65376); KRange (EVar 243) 1533 34359736304;
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
         KDisj {| a_base := EMd Instr.M_MUL (ELit 4096) (EVar 243); a_off := 0 |} (ELit 65536) {| a_base := ELit 65536; a_off := 0 |} (ELit 6213632);
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
           (ELit 776704);
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
         KDisj {| a_base := EMd Instr.M_MUL (ELit 4096) (EVar 242); a_off := 0 |} (ELit 4096) {| a_base := ELit 65536; a_off := 0 |} (ELit 6213632);
         KDisj {| a_base := EMd Instr.M_MUL (ELit 4096) (EVar 242); a_off := 0 |} (ELit 4096)
           {|
             a_base :=
               EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 32768) (EVar 0)) (EMd Instr.M_MUL (ELit 4096) (EAlu Instr.ALU_SRL (EVar 6) (ELit 8)));
             a_off := -8388608
           |} (ELit 2155876352);
         KWord {| a_base := ELit 0; a_off := 6269384 |} 4 (ELit 1); KWord {| a_base := ELit 0; a_off := 6269664 |} 8 (ELit 455892);
         KWord {| a_base := ELit 0; a_off := 6269408 |} 8 (ELit 586724); KWord {| a_base := ELit 0; a_off := 6269392 |} 8 (ELit 6269400);
         KWord {| a_base := ELit 0; a_off := 1284184 |} 1 (ELit 0); KWord {| a_base := ELit 0; a_off := 689816 |} 1 (ELit 1);
         KWord {| a_base := ELit 0; a_off := 689817 |} 1 (ELit 1); KWord {| a_base := ELit 0; a_off := 676216 |} 8 (ELit 1099511627776);
         KWord {| a_base := ELit 0; a_off := 676226 |} 2 (ELit 2048); KWord {| a_base := ELit 0; a_off := 676224 |} 2 (ELit 16);
         KWord {| a_base := ELit 0; a_off := 676228 |} 1 (ELit 1); KWord {| a_base := ELit 0; a_off := 673481 |} 1 (ELit 0);
         KWord {| a_base := ELit 0; a_off := 673480 |} 1 (ELit 0); KWord {| a_base := ELit 0; a_off := 673408 |} 8 (ELit 1048576);
         KWord {| a_base := ELit 0; a_off := 673400 |} 8 (ELit 241591905); KWord {| a_base := ELit 0; a_off := 673392 |} 8 (ELit 268435456);
         KWord {| a_base := ELit 0; a_off := 672672 |} 8 (EMd Instr.M_MUL (ELit 4096) (EVar 241));
         KWord {| a_base := ELit 0; a_off := 672696 |} 8 (ELit 102840); KWord {| a_base := ELit 0; a_off := 672688 |} 8 (ELit 8388608);
         KWord {| a_base := ELit 0; a_off := 672680 |} 8 (EMd Instr.M_MUL (ELit 4096) (EVar 241));
         KDisj {| a_base := EMd Instr.M_MUL (ELit 512) (EVar 241); a_off := 2147450880 |} (ELit 1048576)
           {|
             a_base := EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 4096) (EVar 0)) (EMd Instr.M_MUL (ELit 512) (EAlu Instr.ALU_SRL (EVar 6) (ELit 8)));
             a_off := 2146402304
           |}
           (EAlu Instr.ALU_ADD
              (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit (-4096)) (EVar 0)) (EMd Instr.M_MUL (ELit (-512)) (EAlu Instr.ALU_SRL (EVar 6) (ELit 8))))
              (ELit 17592187092992));
         KDisj {| a_base := EMd Instr.M_MUL (ELit 512) (EVar 241); a_off := 2147450880 |} (ELit 1048576) {| a_base := ELit 0; a_off := 2147459072 |}
           (ELit 776704);
         KRange (EVar 241) 1533 34359734272;
         KDisj {| a_base := EMd Instr.M_MUL (ELit 4096) (EVar 223); a_off := 0 |} (ELit 137439023104)
           {| a_base := EMd Instr.M_MUL (ELit 4096) (EVar 241); a_off := 0 |} (ELit 8388608);
         KDisj {| a_base := EMd Instr.M_MUL (ELit 4096) (EVar 222); a_off := 0 |} (ELit 3727360)
           {| a_base := EMd Instr.M_MUL (ELit 4096) (EVar 241); a_off := 0 |} (ELit 8388608);
         KDisj {| a_base := EMd Instr.M_MUL (ELit 4096) (EVar 93); a_off := 0 |} (ELit 65536)
           {| a_base := EMd Instr.M_MUL (ELit 4096) (EVar 241); a_off := 0 |} (ELit 8388608);
         KDisj {| a_base := EMd Instr.M_MUL (ELit 4096) (EVar 241); a_off := 0 |} (ELit 8388608) {| a_base := ELit 2147446784; a_off := 0 |}
           (ELit 17592186048512);
         KDisj {| a_base := EMd Instr.M_MUL (ELit 4096) (EVar 241); a_off := 0 |} (ELit 8388608) {| a_base := ELit 65536; a_off := 0 |}
           (ELit 6213632);
         KDisj {| a_base := EMd Instr.M_MUL (ELit 4096) (EVar 241); a_off := 0 |} (ELit 8388608)
           {|
             a_base :=
               EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 32768) (EVar 0)) (EMd Instr.M_MUL (ELit 4096) (EAlu Instr.ALU_SRL (EVar 6) (ELit 8)));
             a_off := -8388608
           |} (ELit 2155876352);
         KWord {| a_base := ELit 0; a_off := 672664 |} 8 (ELit 4096); KWord {| a_base := ELit 0; a_off := 672640 |} 4 (ELit 18446744073709551615);
         KWr
           {|
             a_base := EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 4096) (EVar 223)) (EMd Instr.M_MUL (ELit (-4096)) (EVar 224)); a_off := 137439019008
           |} (ELit 4096);
         KZero
           {|
             a_base := EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 4096) (EVar 223)) (EMd Instr.M_MUL (ELit (-4096)) (EVar 224)); a_off := 137439019008
           |} (ELit 4096);
         KWord {| a_base := ELit 0; a_off := 672648 |} 8
           (EAlu Instr.ALU_ADD (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 4096) (EVar 223)) (EMd Instr.M_MUL (ELit (-4096)) (EVar 224)))
              (ELit 137439019008));
         KWord {| a_base := ELit 0; a_off := 672632 |} 8
           (EAlu Instr.ALU_ADD (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 4096) (EVar 223)) (EMd Instr.M_MUL (ELit (-4096)) (EVar 224))) (ELit 65536));
         KRange (EVar 224) 0 15;
         KRange
           (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit (-4096)) (EVar 224)) (EAlu Instr.ALU_AND (EMd Instr.M_MUL (ELit 4096) (EVar 223)) (ELit 65535)))
           0 0;
         KWord {| a_base := ELit 0; a_off := 672616 |} 8 (ELit 92859); KWord {| a_base := ELit 0; a_off := 672608 |} 8 (ELit 137439023104);
         KWord {| a_base := ELit 0; a_off := 672600 |} 8 (EMd Instr.M_MUL (ELit 4096) (EVar 223));
         KDisj {| a_base := EMd Instr.M_MUL (ELit 512) (EVar 223); a_off := 2147450880 |} (ELit 17179877888)
           {|
             a_base := EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 4096) (EVar 0)) (EMd Instr.M_MUL (ELit 512) (EAlu Instr.ALU_SRL (EVar 6) (ELit 8)));
             a_off := 2146402304
           |}
           (EAlu Instr.ALU_ADD
              (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit (-4096)) (EVar 0)) (EMd Instr.M_MUL (ELit (-512)) (EAlu Instr.ALU_SRL (EVar 6) (ELit 8))))
              (ELit 17592187092992));
         KDisj {| a_base := EMd Instr.M_MUL (ELit 512) (EVar 223); a_off := 2147450880 |} (ELit 17179877888)
           {| a_base := ELit 0; a_off := 2147459072 |} (ELit 776704);
         KRange (EVar 223) 4295491576 34326181871;
         KDisj {| a_base := EMd Instr.M_MUL (ELit 4096) (EVar 222); a_off := 0 |} (ELit 3727360)
           {| a_base := EMd Instr.M_MUL (ELit 4096) (EVar 223); a_off := 0 |} (ELit 137439023104);
         KDisj {| a_base := EMd Instr.M_MUL (ELit 4096) (EVar 93); a_off := 0 |} (ELit 65536)
           {| a_base := EMd Instr.M_MUL (ELit 4096) (EVar 223); a_off := 0 |} (ELit 137439023104);
         KDisj {| a_base := EMd Instr.M_MUL (ELit 4096) (EVar 223); a_off := 0 |} (ELit 137439023104) {| a_base := ELit 2147446784; a_off := 0 |}
           (ELit 17592186048512);
         KDisj {| a_base := EMd Instr.M_MUL (ELit 4096) (EVar 223); a_off := 0 |} (ELit 137439023104) {| a_base := ELit 65536; a_off := 0 |}
           (ELit 6213632);
         KDisj {| a_base := EMd Instr.M_MUL (ELit 4096) (EVar 223); a_off := 0 |} (ELit 137439023104)
           {|
             a_base :=
               EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 32768) (EVar 0)) (EMd Instr.M_MUL (ELit 4096) (EAlu Instr.ALU_SRL (EVar 6) (ELit 8)));
             a_off := -8388608
           |} (ELit 2155876352);
         KWord {| a_base := ELit 0; a_off := 672656 |} 1 (ELit 0); KWord {| a_base := ELit 0; a_off := 1219617 |} 1 (ELit 1);
         KWord {| a_base := ELit 0; a_off := 684580 |} 4 (ELit 0); KWord {| a_base := ELit 0; a_off := 6138136 |} 8 (ELit 6274328);
         KWord {| a_base := ELit 0; a_off := 684576 |} 1 (ELit 1); KWord {| a_base := ELit 0; a_off := 686520 |} 8 (ELit 2147450880);
         KDisj {| a_base := EMd Instr.M_MUL (ELit 512) (EVar 222); a_off := 2147450880 |} (ELit 465920)
           {|
             a_base := EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 4096) (EVar 0)) (EMd Instr.M_MUL (ELit 512) (EAlu Instr.ALU_SRL (EVar 6) (ELit 8)));
             a_off := 2146402304
           |}
           (EAlu Instr.ALU_ADD
              (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit (-4096)) (EVar 0)) (EMd Instr.M_MUL (ELit (-512)) (EAlu Instr.ALU_SRL (EVar 6) (ELit 8))))
              (ELit 17592187092992));
         KDisj {| a_base := EMd Instr.M_MUL (ELit 512) (EVar 222); a_off := 2147450880 |} (ELit 465920) {| a_base := ELit 0; a_off := 2147459072 |}
           (ELit 776704);
         KWr {| a_base := EMd Instr.M_MUL (ELit 4096) (EVar 222); a_off := 0 |} (ELit 3727360); KRange (EVar 222) 1533 34359735410;
         KDisj {| a_base := EMd Instr.M_MUL (ELit 4096) (EVar 93); a_off := 0 |} (ELit 65536)
           {| a_base := EMd Instr.M_MUL (ELit 4096) (EVar 222); a_off := 0 |} (ELit 3727360);
         KDisj {| a_base := EMd Instr.M_MUL (ELit 4096) (EVar 222); a_off := 0 |} (ELit 3727360) {| a_base := ELit 2147446784; a_off := 0 |}
           (ELit 17592186048512);
         KDisj {| a_base := EMd Instr.M_MUL (ELit 4096) (EVar 222); a_off := 0 |} (ELit 3727360) {| a_base := ELit 65536; a_off := 0 |}
           (ELit 6213632);
         KDisj {| a_base := EMd Instr.M_MUL (ELit 4096) (EVar 222); a_off := 0 |} (ELit 3727360)
           {|
             a_base :=
               EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 32768) (EVar 0)) (EMd Instr.M_MUL (ELit 4096) (EAlu Instr.ALU_SRL (EVar 6) (ELit 8)));
             a_off := -8388608
           |} (ELit 2155876352);
         KWord {| a_base := ELit 0; a_off := 1219608 |} 8 (ELit 365900); KWord {| a_base := ELit 0; a_off := 661440 |} 8 (ELit 8);
         KWord {| a_base := ELit 0; a_off := 686528 |} 4 (ELit 1); KWord {| a_base := ELit 0; a_off := 689824 |} 8 (ELit 140737488355327);
         KWord {| a_base := ELit 0; a_off := 689852 |} 4 (ELit 30); KWord {| a_base := ELit 0; a_off := 684572 |} 1 (ELit 1);
         KWord {| a_base := ELit 0; a_off := 684568 |} 4 (ELit 2); KWord {| a_base := ELit 0; a_off := 676358 |} 1 (ELit 1);
         KWord {| a_base := ELit 0; a_off := 1283328 |} 8 (ELit 81553); KWord {| a_base := ELit 0; a_off := 1283336 |} 8 (ELit 128849084416);
         KWord {| a_base := ELit 0; a_off := 1283344 |} 8 (ELit 0); KWord {| a_base := ELit 0; a_off := 1283352 |} 8 (ELit 0);
         KWord {| a_base := ELit 0; a_off := 1283360 |} 8 (ELit 0); KWord {| a_base := ELit 0; a_off := 1283368 |} 8 (ELit 0);
         KWord {| a_base := ELit 0; a_off := 1283376 |} 8 (ELit 1103823372545); KWord {| a_base := ELit 0; a_off := 1283384 |} 8 (ELit 4294967296);
         KWord {| a_base := ELit 0; a_off := 1283392 |} 8 (ELit 0); KWord {| a_base := ELit 0; a_off := 1283400 |} 8 (ELit 0);
         KWord {| a_base := ELit 0; a_off := 1283408 |} 8 (ELit 0); KWord {| a_base := ELit 0; a_off := 1283416 |} 8 (ELit 65537);
         KWord {| a_base := ELit 0; a_off := 1283424 |} 8 (ELit 18446744073709551615); KWord {| a_base := ELit 0; a_off := 1283432 |} 8 (ELit 71687);
         KWord {| a_base := ELit 0; a_off := 1283440 |} 8 (ELit 256); KWord {| a_base := ELit 0; a_off := 1283448 |} 8 (ELit 0);
         KWord {| a_base := ELit 0; a_off := 1283456 |} 8 (ELit 0); KWord {| a_base := ELit 0; a_off := 1283544 |} 8 (ELit 72339073309605888);
         KWord {| a_base := ELit 0; a_off := 1283552 |} 8 (ELit 72340172838076673); KWord {| a_base := ELit 0; a_off := 1283560 |} 8 (ELit 16843009);
         KWord {| a_base := ELit 0; a_off := 1283568 |} 8 (ELit 1103806595073); KWord {| a_base := ELit 0; a_off := 1274968 |} 4 (ELit 0);
         KWord {| a_base := ELit 0; a_off := 676370 |} 1 (ELit 0); KWord {| a_base := ELit 0; a_off := 676300 |} 1 (ELit 0);
         KWord {| a_base := ELit 0; a_off := 676372 |} 4 (ELit 0); KWord {| a_base := ELit 0; a_off := 676368 |} 2 (ELit 1);
         KWord {| a_base := ELit 0; a_off := 676360 |} 8 (ELit 72340172838010881); KWord {| a_base := ELit 0; a_off := 676352 |} 6 (ELit 4294967296);
         KWord {| a_base := ELit 0; a_off := 676359 |} 1 (ELit 0); KWord {| a_base := ELit 0; a_off := 676324 |} 4 (ELit 4096);
         KWord {| a_base := ELit 0; a_off := 676320 |} 1 (ELit 0); KWord {| a_base := ELit 0; a_off := 676312 |} 8 (ELit 85899345936);
         KWord {| a_base := ELit 0; a_off := 676304 |} 8 (ELit 72340168526266369); KWord {| a_base := ELit 0; a_off := 676296 |} 4 (ELit 2048);
         KWord {| a_base := ELit 0; a_off := 676344 |} 8 (ELit 0); KWord {| a_base := ELit 0; a_off := 676340 |} 1 (ELit 1);
         KWord {| a_base := ELit 0; a_off := 676336 |} 4 (ELit 85); KWord {| a_base := ELit 0; a_off := 676328 |} 8 (ELit 816043786240);
         KDisj {| a_base := EMd Instr.M_MUL (ELit 512) (EVar 93); a_off := 2147450880 |} (ELit 8192)
           {|
             a_base := EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 4096) (EVar 0)) (EMd Instr.M_MUL (ELit 512) (EAlu Instr.ALU_SRL (EVar 6) (ELit 8)));
             a_off := 2146402304
           |}
           (EAlu Instr.ALU_ADD
              (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit (-4096)) (EVar 0)) (EMd Instr.M_MUL (ELit (-512)) (EAlu Instr.ALU_SRL (EVar 6) (ELit 8))))
              (ELit 17592187092992));
         KDisj {| a_base := EMd Instr.M_MUL (ELit 512) (EVar 93); a_off := 2147450880 |} (ELit 8192) {| a_base := ELit 0; a_off := 2147459072 |}
           (ELit 776704);
         KWr {| a_base := EMd Instr.M_MUL (ELit 4096) (EVar 93); a_off := 0 |} (ELit 65536); KRange (EVar 93) 1533 34359736304;
         KDisj {| a_base := EMd Instr.M_MUL (ELit 4096) (EVar 93); a_off := 0 |} (ELit 65536) {| a_base := ELit 2147446784; a_off := 0 |}
           (ELit 17592186048512);
         KDisj {| a_base := EMd Instr.M_MUL (ELit 4096) (EVar 93); a_off := 0 |} (ELit 65536) {| a_base := ELit 65536; a_off := 0 |} (ELit 6213632);
         KDisj {| a_base := EMd Instr.M_MUL (ELit 4096) (EVar 93); a_off := 0 |} (ELit 65536)
           {|
             a_base :=
               EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 32768) (EVar 0)) (EMd Instr.M_MUL (ELit 4096) (EAlu Instr.ALU_SRL (EVar 6) (ELit 8)));
             a_off := -8388608
           |} (ELit 2155876352);
         KWord {| a_base := ELit 0; a_off := 1274976 |} 8 (ELit 4096); KWord {| a_base := ELit 0; a_off := 689848 |} 1 (ELit 1);
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
         KWr {| a_base := ELit 0; a_off := 2147459072 |} (ELit 776704); KZero {| a_base := ELit 0; a_off := 2147459072 |} (ELit 8658);
         KZero {| a_base := ELit 0; a_off := 2147467740 |} (ELit 1); KZero {| a_base := ELit 0; a_off := 2147467744 |} (ELit 67162);
         KZero {| a_base := ELit 0; a_off := 2147534938 |} (ELit 682926); KZero {| a_base := ELit 0; a_off := 2148217868 |} (ELit 17908);
         KWord {| a_base := ELit 0; a_off := 1274960 |} 8
           (EAlu Instr.ALU_ADD (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 32768) (EVar 0)) (EMd Instr.M_MUL (ELit 16) (EVar 6))) (ELit (-160)));
         KWord {| a_base := ELit 0; a_off := 689819 |} 1 (ELit 0); KWord {| a_base := ELit 0; a_off := 6138208 |} 8 (EVar 60);
         KWord {| a_base := ELit 0; a_off := 6269360 |} 8 (EVar 60); KWord {| a_base := ELit 0; a_off := 6269361 |} 1 (ELit 0); KWord {| a_base := ELit 0; a_off := 6138048 |} 8 (ELit 0);
         KWord {| a_base := ELit 0; a_off := 6138144 |} 8 (ELit 6138144); KWord {| a_base := ELit 0; a_off := 6138056 |} 4 (EVar 43);
         KRange (EVar 43) 1 4194303; KWord {| a_base := ELit 0; a_off := 6138064 |} 4 (ELit 2);
         KWord {| a_base := ELit 0; a_off := 6269952 |} 1 (ELit 1); KWord {| a_base := ELit 0; a_off := 6138216 |} 8 (ELit 6138256);
         KWord {| a_base := ELit 0; a_off := 6138256 |} 8 (ELit 1); KWord {| a_base := ELit 0; a_off := 6138264 |} 8 (ELit 6140272);
         KWord {| a_base := ELit 0; a_off := 6269944 |} 8
           (EAlu Instr.ALU_ADD
              (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 32768) (EVar 0))
                 (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 8) (EVar 1))
                    (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 8) (EVar 2)) (EMd Instr.M_MUL (ELit 16) (EVar 6)))))
              (ELit 184));
         KWord {| a_base := ELit 0; a_off := 6269960 |} 8
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
         KRange (EVar 4) 0 280000; KRange (EVar 5) 1533 525821;
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
         KImg 65536 661440; KImg 661456 661464; KImg 661468 672512; KImg 672521 672600; KImg 672624 672632; KImg 672644 672648; 
         KImg 672657 672664; KImg 672704 673280; KImg 673284 673392; KImg 673416 673480; KImg 673482 676216; KImg 676229 676280; 
         KImg 676301 676304; KImg 676321 676324; KImg 676341 676344; KImg 676371 676372; KImg 676377 676380; KImg 676396 676400; 
         KImg 676401 676408; KImg 676440 676464; KImg 676472 676536; KImg 681320 684536; KImg 684539 684540; KImg 684560 684568; 
         KImg 684573 684576; KImg 684577 684580; KImg 684584 686520; KImg 686532 689816; KImg 689820 689824; KImg 689832 689848; 
         KImg 689849 689852; KImg 689856 689968; KImg 689984 690688; KImg 690696 690752; KImg 690764 690768; KImg 690797 690856; 
         KImg 690857 690864; KImg 690865 690872; KImg 690896 690904; KImg 690988 690992; KImg 691132 1219592; KImg 1219616 1219617;
         KImg 1219618 1274960; KImg 1274972 1274976; KImg 1274984 1275008; KImg 1279103 1279104; KImg 1283199 1283296; KImg 1283300 1283304;
         KImg 1283592 1283792; KImg 1283800 1283832; KImg 1283840 1283856; KImg 1283880 1283912; KImg 1283913 1284184; KImg 1284185 1546376;
         KImg 5806236 5806240; KImg 5806244 5806248; KImg 5806256 6069632; KImg 6069633 6069636; KImg 6069655 6069656; KImg 6069660 6069664;
         KImg 6069676 6070080; KImg 6070088 6070144; KImg 6070156 6070160; KImg 6070222 6070248; KImg 6070249 6070256; KImg 6070260 6070264;
         KImg 6070266 6070272; KImg 6070282 6138016; KImg 6138060 6138064; KImg 6138068 6138074; KImg 6138075 6138136; KImg 6138152 6138176;
         KImg 6138184 6138208; KImg 6138240 6138256; KImg 6138272 6269320; KImg 6269368 6269384; KImg 6269388 6269392; KImg 6269400 6269408;
         KImg 6269416 6269664; KImg 6269672 6269936; KImg 6269953 6269960; KImg 6270008 6270056; KImg 6270064 6270080; KImg 6270096 6270104;
         KImg 6270160 6270176; KImg 6270184 6270280; KImg 6270288 6270312; KImg 6270320 6270344; KImg 6270352 6270560; KImg 6270568 6270664;
         KImg 6270672 6270696; KImg 6270704 6270728; KImg 6270736 6270992; KImg 6270993 6271000; KImg 6271008 6273224; KImg 6273232 6273240;
         KImg 6273248 6274264; KImg 6274268 6274272; KImg 6274276 6274328; KImg 6274336 6279168;
         KWr {| a_base := ELit 0; a_off := 651264 |} (ELit 5627904)]
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
    a_totsz := 17729664573440;
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
       (EMd Instr.M_MUL (ELit 4096) (EVar 222), ELit 3727360); (EMd Instr.M_MUL (ELit 4096) (EVar 93), ELit 65536); (ELit 65536, ELit 6213632);
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
    a_abytes := 4886049280;
    a_brk := EVar 621;
    a_fd := FdStd;
    a_tidset := true
  |}.

(* [comment removed for export] *)
Definition HS_both (h : nat) : option acs := match h with O => HS0 | _ => None end.
