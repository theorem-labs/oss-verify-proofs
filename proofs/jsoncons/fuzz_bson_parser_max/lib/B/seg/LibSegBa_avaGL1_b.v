(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.jsoncons.fuzz_bson_parser_max.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PropExec AxSymExec3 AxSymExec3B AxSymExec3Sound AsanPlanCore LibSym SegRun SegPlan SegPlanAuto SegPlanJoin. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import Ba0PlanKit_b Ba0PlanKitIt_b.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B.seg Require SegItab_Ba_b2a9b0_b.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require SegPlanFast.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := AsanUbsan.M.loaded_segments.
Definition ITR : list (Z * nat) := SegItab_Ba_b2a9b0_b.ITR.
Definition IT : itab := SegItab_Ba_b2a9b0_b.IT.
Definition ENDS : list Z := [744532; 744632].
Definition STOPS1 : list Z := [744532; 744632] ++ ENDS.
Definition NX0 : nat := 70.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := [ELit 0; ELit 743604; (EAlu Instr.ALU_ADD (EVar 2) (ELit (-80))); EVar 3; EVar 4; (EAlu Instr.ALU_ADD (EAlu Instr.ALU_SRL (EAlu Instr.ALU_ADD (EVar 2) (ELit (-32))) (ELit 3)) (ELit 2147450880)); ELit 18446744073709551615; (EAlu Instr.ALU_ADD (EAlu Instr.ALU_SRL (EAlu Instr.ALU_ADD (EVar 44) (EVar 56)) (ELit 3)) (ELit 2147450880)); EVar 37; EVar 43; (EAlu Instr.ALU_ADD (EVar 2) (ELit (-48))); (EAlu Instr.ALU_ADD (EAlu Instr.ALU_ADD (EVar 41) (EVar 43)) (EMd Instr.M_MUL (ELit (-1)) (EVar 56))); (EAlu Instr.ALU_ADD (EVar 2) (ELit (-32))); (EAlu Instr.ALU_ADD (EVar 44) (EVar 56)); (EAlu Instr.ALU_ADD (EAlu Instr.ALU_SRL (EAlu Instr.ALU_ADD (EVar 2) (ELit (-48))) (ELit 3)) (ELit 2147450880)); ELit 2147450880; (EAlu Instr.ALU_ADD (EVar 44) (EVar 56)); (EAlu Instr.ALU_ADD (EVar 41) (EAlu Instr.ALU_ADD (EVar 43) (EVar 44))); EVar 51; EVar 52; EVar 53; EVar 54; EVar 22; EVar 23; EVar 24; EVar 25; EVar 26; EVar 27; EVar 28; EVar 29; EVar 30; EVar 31].
Definition kn0 : list kentry := [KWord (SA (EVar 2) (-72)) 8 (ELit 743604);
    KWord (SA (EVar 2) (-40)) 8 (EAlu Instr.ALU_ADD (EVar 44) (EVar 46));
    KWord (SA (EVar 2) (-56)) 8 (EAlu Instr.ALU_ADD (EVar 41) (EVar 44));
    KWord (SA (EVar 2) (-48)) 8 (EAlu Instr.ALU_ADD (EVar 41) (EVar 44));
    KWord (SA (EVar 2) (-64)) 8 (EVar 44);
    KImg 1249280 1282048;
    KWord (SA (ELit 0) 1309752) 8 (ELit 2147450880);
    KWord (SA (ELit 0) 1309760) 4 (ELit 1);
    KRange (EVar 2) 140735332487264 140737488355328;
    KAlign (EVar 2) 16;
    KWr (SA (EVar 2) (-128)) (ELit 128);
    KRange (EVar 37) 6905856 140737488355304;
    KAlign (EVar 37) 8;
    KDisj (SA (ELit 0) 2147446784) (ELit 17592186048512) (SA (EVar 37) 0) (ELit 24);
    KZero (SA (EAlu Instr.ALU_SRL (EVar 37) (ELit 3)) 2147450880) (ELit 3);
    KWr (SA (EVar 37) 0) (ELit 24);
    KDisj (SA (EVar 2) (-128)) (ELit 128) (SA (EVar 37) 0) (ELit 24);
    KRange (EVar 43) 1 134217728;
    KRange (EVar 44) 4096 140737488355328;
    KRange (EVar 41) 0 134217728;
    KRange (EVar 46) 1 134217728;
    KWr (SA (EVar 44) 0) (EVar 46);
    KDisj (SA (EVar 2) (-128)) (ELit 128) (SA (EVar 44) 0) (EVar 46);
    KDisj (SA (ELit 0) 2147446784) (ELit 17592186048512) (SA (EVar 44) 0) (EVar 46);
    KDisj (SA (EVar 37) 0) (ELit 24) (SA (EVar 44) 0) (EVar 46);
    KRange (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit (-1)) (EVar 41)) (EVar 46)) 1 134217728;
    KZero (SA (EAlu Instr.ALU_SRL (EVar 2) (ELit 3)) 2147450368) (ELit 512);
    KWord (SA (EVar 2) (-8)) 8 (EVar 48);
    KWord (SA (EVar 2) (-16)) 8 (EVar 49);
    KWord (SA (EVar 2) (-24)) 8 (EVar 50);
    KWord (SA (EVar 2) (-32)) 8 (EVar 37);
    KWord (SA (EVar 2) (-80)) 8 (EVar 37);
    KWord (SA (EVar 2) (-88)) 8 (EVar 43);
    KWord (SA (EVar 2) (-96)) 8 (EVar 51);
    KWord (SA (EVar 2) (-104)) 8 (EVar 52);
    KWord (SA (EVar 2) (-112)) 8 (EVar 53);
    KWord (SA (EVar 2) (-120)) 8 (EVar 54);
    KRange (EVar 56) 0 134217728;
    KRange (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit (-1)) (EVar 41)) (EVar 56)) 0 134217728;
    KRange (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit (-1)) (EVar 56)) (EAlu Instr.ALU_ADD (EVar 41) (EVar 43))) 1 134217728;
    KRange (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit (-1)) (EVar 56)) (EVar 46)) 1 134217728;
    KWord (SA (EAlu Instr.ALU_SRL (EAlu Instr.ALU_ADD (EVar 44) (EVar 56)) (ELit 3)) 2147450880) 1 (EVar 55);
    KRange (EVar 55) 1 7;
    KRange (EAlu Instr.ALU_ADD (EVar 55) (EMd Instr.M_MUL (ELit (-1)) (EAlu Instr.ALU_AND (EAlu Instr.ALU_ADD (EVar 44) (EVar 56)) (ELit 7)))) 1 7].
Definition ss0 : sym_state := SS 744532 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 2), (-128), ELit 128); ((EAlu Instr.ALU_ADD (EVar 44) (EVar 56)), 0, ELit 1)].
Definition F0L : list SR.region := [((EVar 2), (-128), 128)].
Definition BF : nat := 1000.
Definition BR : list SGP.bfact := [].
Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition s1 : sym_state :=
  (SS 744560 [ELit 0; ELit 743604; EAlu Instr.ALU_ADD (EVar 2) (ELit (-80)); EVar 3; EVar 4; EAlu Instr.ALU_ADD (EAlu Instr.ALU_SRL (EAlu Instr.ALU_ADD (EVar 2) (ELit (-32))) (ELit 3)) (ELit 2147450880); ELit 18446744073709551615; EVar 55; EVar 37; EVar 43; EAlu Instr.ALU_ADD (EVar 2) (ELit (-48)); EAlu Instr.ALU_ADD (EAlu Instr.ALU_ADD (EVar 41) (EAlu Instr.ALU_ADD (EVar 43) (EMd Instr.M_MUL (ELit (-1)) (EVar 56)))) (ELit (-1)); EAlu Instr.ALU_ADD (EVar 2) (ELit (-32)); EAlu Instr.ALU_ADD (EAlu Instr.ALU_ADD (EVar 44) (EVar 56)) (ELit 1); EAlu Instr.ALU_ADD (EAlu Instr.ALU_SRL (EAlu Instr.ALU_ADD (EVar 2) (ELit (-48))) (ELit 3)) (ELit 2147450880); ELit 2147450880; EAlu Instr.ALU_ADD (EAlu Instr.ALU_ADD (EVar 44) (EVar 56)) (ELit 1); EAlu Instr.ALU_ADD (EVar 41) (EAlu Instr.ALU_ADD (EVar 43) (EVar 44)); EVar 51; EVar 52; EVar 53; EVar 54; EVar 22; EVar 23; EVar 24; EVar 25; EVar 26; EVar 27; EAlu Instr.ALU_AND (EAlu Instr.ALU_ADD (EVar 44) (EVar 56)) (ELit 7); EVar 29; EVar 30; EVar 31] [] [KWord {| a_base := EAlu Instr.ALU_ADD (EVar 44) (EVar 56); a_off := 0 |} 1 (ELit 0); KWord {| a_base := EVar 2; a_off := -72 |} 8 (ELit 743604); KWord {| a_base := EVar 2; a_off := -40 |} 8 (EAlu Instr.ALU_ADD (EVar 44) (EVar 46)); KWord {| a_base := EVar 2; a_off := -56 |} 8 (EAlu Instr.ALU_ADD (EVar 41) (EVar 44)); KWord {| a_base := EVar 2; a_off := -48 |} 8 (EAlu Instr.ALU_ADD (EVar 41) (EVar 44)); KWord {| a_base := EVar 2; a_off := -64 |} 8 (EVar 44); KRange (EVar 2) 140735332487264 140737488355328; KAlign (EVar 2) 16; KWr {| a_base := EVar 2; a_off := -128 |} (ELit 128); KRange (EVar 37) 6905856 140737488355304; KAlign (EVar 37) 8; KDisj {| a_base := ELit 0; a_off := 2147446784 |} (ELit 17592186048512) {| a_base := EVar 37; a_off := 0 |} (ELit 24); KZero {| a_base := EAlu Instr.ALU_SRL (EVar 37) (ELit 3); a_off := 2147450880 |} (ELit 3); KWr {| a_base := EVar 37; a_off := 0 |} (ELit 24); KDisj {| a_base := EVar 2; a_off := -128 |} (ELit 128) {| a_base := EVar 37; a_off := 0 |} (ELit 24); KRange (EVar 43) 1 134217728; KRange (EVar 44) 4096 140737488355328; KRange (EVar 41) 0 134217728; KRange (EVar 46) 1 134217728; KWr {| a_base := EVar 44; a_off := 0 |} (EVar 46); KDisj {| a_base := EVar 2; a_off := -128 |} (ELit 128) {| a_base := EVar 44; a_off := 0 |} (EVar 46); KDisj {| a_base := ELit 0; a_off := 2147446784 |} (ELit 17592186048512) {| a_base := EVar 44; a_off := 0 |} (EVar 46); KDisj {| a_base := EVar 37; a_off := 0 |} (ELit 24) {| a_base := EVar 44; a_off := 0 |} (EVar 46); KRange (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit (-1)) (EVar 41)) (EVar 46)) 1 134217728; KZero {| a_base := EAlu Instr.ALU_SRL (EVar 2) (ELit 3); a_off := 2147450368 |} (ELit 512); KWord {| a_base := EVar 2; a_off := -8 |} 8 (EVar 48); KWord {| a_base := EVar 2; a_off := -16 |} 8 (EVar 49); KWord {| a_base := EVar 2; a_off := -24 |} 8 (EVar 50); KWord {| a_base := EVar 2; a_off := -32 |} 8 (EVar 37); KWord {| a_base := EVar 2; a_off := -80 |} 8 (EVar 37); KWord {| a_base := EVar 2; a_off := -88 |} 8 (EVar 43); KWord {| a_base := EVar 2; a_off := -96 |} 8 (EVar 51); KWord {| a_base := EVar 2; a_off := -104 |} 8 (EVar 52); KWord {| a_base := EVar 2; a_off := -112 |} 8 (EVar 53); KWord {| a_base := EVar 2; a_off := -120 |} 8 (EVar 54); KRange (EVar 56) 0 134217728; KRange (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit (-1)) (EVar 41)) (EVar 56)) 0 134217728; KRange (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit (-1)) (EVar 56)) (EAlu Instr.ALU_ADD (EVar 41) (EVar 43))) 1 134217728; KRange (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit (-1)) (EVar 56)) (EVar 46)) 1 134217728; KRange (EVar 55) 1 7; KRange (EAlu Instr.ALU_ADD (EVar 55) (EMd Instr.M_MUL (ELit (-1)) (EAlu Instr.ALU_AND (EAlu Instr.ALU_ADD (EVar 44) (EVar 56)) (ELit 7)))) 1 7] 70).
Definition ex2 : list SGA.aitem * (Z * sym_state) :=
  (([], (91, SS 744560 [ELit 0; ELit 743604; EAlu Instr.ALU_ADD (EVar 2) (ELit (-80)); EVar 3; EVar 4; EAlu Instr.ALU_ADD (EAlu Instr.ALU_SRL (EAlu Instr.ALU_ADD (EVar 2) (ELit (-32))) (ELit 3)) (ELit 2147450880); ELit 18446744073709551615; EVar 55; EVar 37; EVar 43; EAlu Instr.ALU_ADD (EVar 2) (ELit (-48)); EAlu Instr.ALU_ADD (EAlu Instr.ALU_ADD (EVar 41) (EAlu Instr.ALU_ADD (EVar 43) (EMd Instr.M_MUL (ELit (-1)) (EVar 56)))) (ELit (-1)); EAlu Instr.ALU_ADD (EVar 2) (ELit (-32)); EAlu Instr.ALU_ADD (EAlu Instr.ALU_ADD (EVar 44) (EVar 56)) (ELit 1); EAlu Instr.ALU_ADD (EAlu Instr.ALU_SRL (EAlu Instr.ALU_ADD (EVar 2) (ELit (-48))) (ELit 3)) (ELit 2147450880); ELit 2147450880; EAlu Instr.ALU_ADD (EAlu Instr.ALU_ADD (EVar 44) (EVar 56)) (ELit 1); EAlu Instr.ALU_ADD (EVar 41) (EAlu Instr.ALU_ADD (EVar 43) (EVar 44)); EVar 51; EVar 52; EVar 53; EVar 54; EVar 22; EVar 23; EVar 24; EVar 25; EVar 26; EVar 27; EAlu Instr.ALU_AND (EAlu Instr.ALU_ADD (EVar 44) (EVar 56)) (ELit 7); EVar 29; EVar 30; EVar 31] [] [KWord {| a_base := EAlu Instr.ALU_ADD (EVar 44) (EVar 56); a_off := 0 |} 1 (ELit 0); KWord {| a_base := EVar 2; a_off := -72 |} 8 (ELit 743604); KWord {| a_base := EVar 2; a_off := -40 |} 8 (EAlu Instr.ALU_ADD (EVar 44) (EVar 46)); KWord {| a_base := EVar 2; a_off := -56 |} 8 (EAlu Instr.ALU_ADD (EVar 41) (EVar 44)); KWord {| a_base := EVar 2; a_off := -48 |} 8 (EAlu Instr.ALU_ADD (EVar 41) (EVar 44)); KWord {| a_base := EVar 2; a_off := -64 |} 8 (EVar 44); KRange (EVar 2) 140735332487264 140737488355328; KAlign (EVar 2) 16; KWr {| a_base := EVar 2; a_off := -128 |} (ELit 128); KRange (EVar 37) 6905856 140737488355304; KAlign (EVar 37) 8; KDisj {| a_base := ELit 0; a_off := 2147446784 |} (ELit 17592186048512) {| a_base := EVar 37; a_off := 0 |} (ELit 24); KZero {| a_base := EAlu Instr.ALU_SRL (EVar 37) (ELit 3); a_off := 2147450880 |} (ELit 3); KWr {| a_base := EVar 37; a_off := 0 |} (ELit 24); KDisj {| a_base := EVar 2; a_off := -128 |} (ELit 128) {| a_base := EVar 37; a_off := 0 |} (ELit 24); KRange (EVar 43) 1 134217728; KRange (EVar 44) 4096 140737488355328; KRange (EVar 41) 0 134217728; KRange (EVar 46) 1 134217728; KWr {| a_base := EVar 44; a_off := 0 |} (EVar 46); KDisj {| a_base := EVar 2; a_off := -128 |} (ELit 128) {| a_base := EVar 44; a_off := 0 |} (EVar 46); KDisj {| a_base := ELit 0; a_off := 2147446784 |} (ELit 17592186048512) {| a_base := EVar 44; a_off := 0 |} (EVar 46); KDisj {| a_base := EVar 37; a_off := 0 |} (ELit 24) {| a_base := EVar 44; a_off := 0 |} (EVar 46); KRange (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit (-1)) (EVar 41)) (EVar 46)) 1 134217728; KZero {| a_base := EAlu Instr.ALU_SRL (EVar 2) (ELit 3); a_off := 2147450368 |} (ELit 512); KWord {| a_base := EVar 2; a_off := -8 |} 8 (EVar 48); KWord {| a_base := EVar 2; a_off := -16 |} 8 (EVar 49); KWord {| a_base := EVar 2; a_off := -24 |} 8 (EVar 50); KWord {| a_base := EVar 2; a_off := -32 |} 8 (EVar 37); KWord {| a_base := EVar 2; a_off := -80 |} 8 (EVar 37); KWord {| a_base := EVar 2; a_off := -88 |} 8 (EVar 43); KWord {| a_base := EVar 2; a_off := -96 |} 8 (EVar 51); KWord {| a_base := EVar 2; a_off := -104 |} 8 (EVar 52); KWord {| a_base := EVar 2; a_off := -112 |} 8 (EVar 53); KWord {| a_base := EVar 2; a_off := -120 |} 8 (EVar 54); KRange (EVar 56) 0 134217728; KRange (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit (-1)) (EVar 41)) (EVar 56)) 0 134217728; KRange (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit (-1)) (EVar 56)) (EAlu Instr.ALU_ADD (EVar 41) (EVar 43))) 1 134217728; KRange (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit (-1)) (EVar 56)) (EVar 46)) 1 134217728; KRange (EVar 55) 1 7; KRange (EAlu Instr.ALU_ADD (EVar 55) (EMd Instr.M_MUL (ELit (-1)) (EAlu Instr.ALU_AND (EAlu Instr.ALU_ADD (EVar 44) (EVar 56)) (ELit 7)))) 1 7] 70))).
Definition s2 : sym_state := snd (snd ex2).
Definition arms3 := Eval vm_compute in (match SGP.branch_probe IT s2 with Some e => SGP.case_arms s2 e 0 | None => None end).
Definition f3 : sym_state := match arms3 with Some (Some s, _) => s | _ => s2 end.
Definition t3 : sym_state := match arms3 with Some (_, Some s) => s | _ => s2 end.
Definition ex4 : list SGA.aitem * (Z * sym_state) :=
  (([SGA.AStep (SR.SBlock [744532; 744632; 744532; 744632])], (93, SS 744632 [ELit 0; ELit 743616; EAlu Instr.ALU_ADD (EVar 2) (ELit (-64)); EVar 3; EVar 4; EAlu Instr.ALU_ADD (EAlu Instr.ALU_SRL (EAlu Instr.ALU_ADD (EVar 2) (ELit (-32))) (ELit 3)) (ELit 2147450880); ELit 18446744073709551615; EVar 55; EVar 37; EVar 43; EVar 37; EAlu Instr.ALU_ADD (EVar 2) (ELit (-64)); EAlu Instr.ALU_ADD (EVar 2) (ELit (-32)); EAlu Instr.ALU_ADD (EAlu Instr.ALU_ADD (EVar 44) (EVar 56)) (ELit 1); EAlu Instr.ALU_ADD (EAlu Instr.ALU_SRL (EAlu Instr.ALU_ADD (EVar 2) (ELit (-48))) (ELit 3)) (ELit 2147450880); ELit 2147450880; EAlu Instr.ALU_ADD (EVar 41) (EAlu Instr.ALU_ADD (EVar 43) (EVar 44)); EAlu Instr.ALU_ADD (EVar 41) (EAlu Instr.ALU_ADD (EVar 43) (EVar 44)); EVar 51; EVar 52; EVar 53; EVar 54; EVar 22; EVar 23; EVar 24; EVar 25; EVar 26; EVar 27; EAlu Instr.ALU_AND (EAlu Instr.ALU_ADD (EVar 44) (EVar 56)) (ELit 7); EVar 29; EVar 30; EVar 31] [] [KWord {| a_base := EVar 2; a_off := -48 |} 8 (EAlu Instr.ALU_ADD (EVar 41) (EAlu Instr.ALU_ADD (EVar 43) (EVar 44))); KRange (EAlu Instr.ALU_SLTU (EAlu Instr.ALU_SUB (EAlu Instr.ALU_ADD (EAlu Instr.ALU_ADD (EVar 41) (EAlu Instr.ALU_ADD (EVar 43) (EMd Instr.M_MUL (ELit (-1)) (EVar 56)))) (ELit (-1))) (ELit 0)) (ELit 1)) 1 1; KWord {| a_base := EAlu Instr.ALU_ADD (EVar 44) (EVar 56); a_off := 0 |} 1 (ELit 0); KWord {| a_base := EVar 2; a_off := -72 |} 8 (ELit 743604); KWord {| a_base := EVar 2; a_off := -40 |} 8 (EAlu Instr.ALU_ADD (EVar 44) (EVar 46)); KWord {| a_base := EVar 2; a_off := -56 |} 8 (EAlu Instr.ALU_ADD (EVar 41) (EVar 44)); KWord {| a_base := EVar 2; a_off := -64 |} 8 (EVar 44); KRange (EVar 2) 140735332487264 140737488355328; KAlign (EVar 2) 16; KWr {| a_base := EVar 2; a_off := -128 |} (ELit 128); KRange (EVar 37) 6905856 140737488355304; KAlign (EVar 37) 8; KDisj {| a_base := ELit 0; a_off := 2147446784 |} (ELit 17592186048512) {| a_base := EVar 37; a_off := 0 |} (ELit 24); KZero {| a_base := EAlu Instr.ALU_SRL (EVar 37) (ELit 3); a_off := 2147450880 |} (ELit 3); KWr {| a_base := EVar 37; a_off := 0 |} (ELit 24); KDisj {| a_base := EVar 2; a_off := -128 |} (ELit 128) {| a_base := EVar 37; a_off := 0 |} (ELit 24); KRange (EVar 43) 1 134217728; KRange (EVar 44) 4096 140737488355328; KRange (EVar 41) 0 134217728; KRange (EVar 46) 1 134217728; KWr {| a_base := EVar 44; a_off := 0 |} (EVar 46); KDisj {| a_base := EVar 2; a_off := -128 |} (ELit 128) {| a_base := EVar 44; a_off := 0 |} (EVar 46); KDisj {| a_base := ELit 0; a_off := 2147446784 |} (ELit 17592186048512) {| a_base := EVar 44; a_off := 0 |} (EVar 46); KDisj {| a_base := EVar 37; a_off := 0 |} (ELit 24) {| a_base := EVar 44; a_off := 0 |} (EVar 46); KRange (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit (-1)) (EVar 41)) (EVar 46)) 1 134217728; KZero {| a_base := EAlu Instr.ALU_SRL (EVar 2) (ELit 3); a_off := 2147450368 |} (ELit 512); KWord {| a_base := EVar 2; a_off := -8 |} 8 (EVar 48); KWord {| a_base := EVar 2; a_off := -16 |} 8 (EVar 49); KWord {| a_base := EVar 2; a_off := -24 |} 8 (EVar 50); KWord {| a_base := EVar 2; a_off := -32 |} 8 (EVar 37); KWord {| a_base := EVar 2; a_off := -80 |} 8 (EVar 37); KWord {| a_base := EVar 2; a_off := -88 |} 8 (EVar 43); KWord {| a_base := EVar 2; a_off := -96 |} 8 (EVar 51); KWord {| a_base := EVar 2; a_off := -104 |} 8 (EVar 52); KWord {| a_base := EVar 2; a_off := -112 |} 8 (EVar 53); KWord {| a_base := EVar 2; a_off := -120 |} 8 (EVar 54); KRange (EVar 56) 0 134217728; KRange (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit (-1)) (EVar 41)) (EVar 56)) 0 134217728; KRange (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit (-1)) (EVar 56)) (EAlu Instr.ALU_ADD (EVar 41) (EVar 43))) 1 134217728; KRange (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit (-1)) (EVar 56)) (EVar 46)) 1 134217728; KRange (EVar 55) 1 7; KRange (EAlu Instr.ALU_ADD (EVar 55) (EMd Instr.M_MUL (ELit (-1)) (EAlu Instr.ALU_AND (EAlu Instr.ALU_ADD (EVar 44) (EVar 56)) (ELit 7)))) 1 7] 70))).
Definition s4 : sym_state := snd (snd ex4).
Definition ex5 : list SGA.aitem * (Z * sym_state) :=
  (([SGA.AStep (SR.SBlock [744532; 744632; 744532; 744632])], (93, SS 744532 [ELit 0; ELit 743604; EAlu Instr.ALU_ADD (EVar 2) (ELit (-80)); EVar 3; EVar 4; EAlu Instr.ALU_ADD (EAlu Instr.ALU_SRL (EAlu Instr.ALU_ADD (EVar 2) (ELit (-32))) (ELit 3)) (ELit 2147450880); ELit 18446744073709551615; EAlu Instr.ALU_ADD (EAlu Instr.ALU_SRL (EAlu Instr.ALU_ADD (EAlu Instr.ALU_ADD (EVar 44) (EVar 56)) (ELit 1)) (ELit 3)) (ELit 2147450880); EVar 37; EVar 43; EAlu Instr.ALU_ADD (EVar 2) (ELit (-48)); EAlu Instr.ALU_ADD (EAlu Instr.ALU_ADD (EVar 41) (EAlu Instr.ALU_ADD (EVar 43) (EMd Instr.M_MUL (ELit (-1)) (EVar 56)))) (ELit (-1)); EAlu Instr.ALU_ADD (EVar 2) (ELit (-32)); EAlu Instr.ALU_ADD (EAlu Instr.ALU_ADD (EVar 44) (EVar 56)) (ELit 1); EAlu Instr.ALU_ADD (EAlu Instr.ALU_SRL (EAlu Instr.ALU_ADD (EVar 2) (ELit (-48))) (ELit 3)) (ELit 2147450880); ELit 2147450880; EAlu Instr.ALU_ADD (EAlu Instr.ALU_ADD (EVar 44) (EVar 56)) (ELit 1); EAlu Instr.ALU_ADD (EVar 41) (EAlu Instr.ALU_ADD (EVar 43) (EVar 44)); EVar 51; EVar 52; EVar 53; EVar 54; EVar 22; EVar 23; EVar 24; EVar 25; EVar 26; EVar 27; EAlu Instr.ALU_AND (EAlu Instr.ALU_ADD (EVar 44) (EVar 56)) (ELit 7); EVar 29; EVar 30; EVar 31] [] [KRange (EAlu Instr.ALU_SLTU (EAlu Instr.ALU_SUB (EAlu Instr.ALU_ADD (EAlu Instr.ALU_ADD (EVar 41) (EAlu Instr.ALU_ADD (EVar 43) (EMd Instr.M_MUL (ELit (-1)) (EVar 56)))) (ELit (-1))) (ELit 0)) (ELit 1)) 0 0; KWord {| a_base := EAlu Instr.ALU_ADD (EVar 44) (EVar 56); a_off := 0 |} 1 (ELit 0); KWord {| a_base := EVar 2; a_off := -72 |} 8 (ELit 743604); KWord {| a_base := EVar 2; a_off := -40 |} 8 (EAlu Instr.ALU_ADD (EVar 44) (EVar 46)); KWord {| a_base := EVar 2; a_off := -56 |} 8 (EAlu Instr.ALU_ADD (EVar 41) (EVar 44)); KWord {| a_base := EVar 2; a_off := -48 |} 8 (EAlu Instr.ALU_ADD (EVar 41) (EVar 44)); KWord {| a_base := EVar 2; a_off := -64 |} 8 (EVar 44); KRange (EVar 2) 140735332487264 140737488355328; KAlign (EVar 2) 16; KWr {| a_base := EVar 2; a_off := -128 |} (ELit 128); KRange (EVar 37) 6905856 140737488355304; KAlign (EVar 37) 8; KDisj {| a_base := ELit 0; a_off := 2147446784 |} (ELit 17592186048512) {| a_base := EVar 37; a_off := 0 |} (ELit 24); KZero {| a_base := EAlu Instr.ALU_SRL (EVar 37) (ELit 3); a_off := 2147450880 |} (ELit 3); KWr {| a_base := EVar 37; a_off := 0 |} (ELit 24); KDisj {| a_base := EVar 2; a_off := -128 |} (ELit 128) {| a_base := EVar 37; a_off := 0 |} (ELit 24); KRange (EVar 43) 1 134217728; KRange (EVar 44) 4096 140737488355328; KRange (EVar 41) 0 134217728; KRange (EVar 46) 1 134217728; KWr {| a_base := EVar 44; a_off := 0 |} (EVar 46); KDisj {| a_base := EVar 2; a_off := -128 |} (ELit 128) {| a_base := EVar 44; a_off := 0 |} (EVar 46); KDisj {| a_base := ELit 0; a_off := 2147446784 |} (ELit 17592186048512) {| a_base := EVar 44; a_off := 0 |} (EVar 46); KDisj {| a_base := EVar 37; a_off := 0 |} (ELit 24) {| a_base := EVar 44; a_off := 0 |} (EVar 46); KRange (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit (-1)) (EVar 41)) (EVar 46)) 1 134217728; KZero {| a_base := EAlu Instr.ALU_SRL (EVar 2) (ELit 3); a_off := 2147450368 |} (ELit 512); KWord {| a_base := EVar 2; a_off := -8 |} 8 (EVar 48); KWord {| a_base := EVar 2; a_off := -16 |} 8 (EVar 49); KWord {| a_base := EVar 2; a_off := -24 |} 8 (EVar 50); KWord {| a_base := EVar 2; a_off := -32 |} 8 (EVar 37); KWord {| a_base := EVar 2; a_off := -80 |} 8 (EVar 37); KWord {| a_base := EVar 2; a_off := -88 |} 8 (EVar 43); KWord {| a_base := EVar 2; a_off := -96 |} 8 (EVar 51); KWord {| a_base := EVar 2; a_off := -104 |} 8 (EVar 52); KWord {| a_base := EVar 2; a_off := -112 |} 8 (EVar 53); KWord {| a_base := EVar 2; a_off := -120 |} 8 (EVar 54); KRange (EVar 56) 0 134217728; KRange (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit (-1)) (EVar 41)) (EVar 56)) 0 134217728; KRange (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit (-1)) (EVar 56)) (EAlu Instr.ALU_ADD (EVar 41) (EVar 43))) 1 134217728; KRange (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit (-1)) (EVar 56)) (EVar 46)) 1 134217728; KRange (EVar 55) 1 7; KRange (EAlu Instr.ALU_ADD (EVar 55) (EMd Instr.M_MUL (ELit (-1)) (EAlu Instr.ALU_AND (EAlu Instr.ALU_ADD (EVar 44) (EVar 56)) (ELit 7)))) 1 7] 70))).
Definition s5 : sym_state := snd (snd ex5).

Definition plan : SGP.splan := SGP.PStep (SR.SBlock STOPS1) (SGA.mkplan (fst ex2) (SGP.PBranch (SGA.mkplan (fst ex4) (SGP.PEnd 0)) (SGA.mkplan (fst ex5) (SGP.PEnd 1)))).
Definition in_foot (b : expr) (k : Z) (w : Z) : bool :=
  existsb (fun r : SR.region => let '(rb, rlo, rlen) := r in (expr_eqb rb b && Z.leb rlo k && Z.leb (k + w) (rlo + rlen))%bool) F0L.
Definition in_kn0 (K : kentry) : bool := existsb (APC.kentry_eqb K) kn0.
Definition SPV : nat := 0%nat.
Definition live (spoff : Z) (b : expr) (k : Z) : bool := (negb (expr_eqb b (EVar SPV)) || Z.leb spoff k)%bool.
Definition cells_of (sF : sym_state) (spoff : Z) : list kentry :=
  List.filter (fun K => match K with
     | KWord (SA b k) w _ => live spoff b k && (in_foot b k (Z.of_nat w) || negb (in_kn0 K))
     | KZero (SA b k) (ELit n) | KFill (SA b k) (ELit n) _ | KBlob (SA b k) (ELit n) _ => live spoff b k && (in_foot b k n || negb (in_kn0 K))
     | KZero (SA b k) _ | KFill (SA b k) _ _ | KBlob (SA b k) _ _ => live spoff b k && (in_foot b k 1 || negb (in_kn0 K))
     | KUnk (SA b k) (ELit n) => live spoff b k && (in_foot b k n || negb (in_kn0 K))
     | KRange _ _ _ | KAlign _ _ => negb (in_kn0 K)
     | _ => false end)%bool (s_know sF).
Definition spoff_of (sF : sym_state) : Z := match nth 2 (s_regs sF) (ELit 0) with EAlu _ (EVar v) (ELit k) => if Nat.eqb v SPV then k else 0 | _ => 0 end.

Definition regs_out0 : list expr := Eval vm_compute in (s_regs s4).
Definition exit_sp_off0 : Z := Eval vm_compute in (spoff_of s4).
Definition cells0 : list kentry := Eval vm_compute in (cells_of s4 exit_sp_off0).
Definition nfresh0 : nat := Eval vm_compute in (s_next s4 - NX0)%nat.
Definition exit_pc0 : Z := Eval vm_compute in (s_pc s4).
Definition ps0 : SR.post_spec := SR.PS 744632 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition regs_out1 : list expr := Eval vm_compute in (s_regs s5).
Definition exit_sp_off1 : Z := Eval vm_compute in (spoff_of s5).
Definition cells1 : list kentry := Eval vm_compute in (cells_of s5 exit_sp_off1).
Definition nfresh1 : nat := Eval vm_compute in (s_next s5 - NX0)%nat.
Definition exit_pc1 : Z := Eval vm_compute in (s_pc s5).
Definition ps1 : SR.post_spec := SR.PS 744532 (map (fun i => (i, nth i regs_out1 (ELit 0))) (seq 1 31)) F0L cells1.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0; ps1] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS SegItab_Ba_b2a9b0_b.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 744532 regs0 kn0 = true.
Proof. apply SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it SegItab_Ba_b2a9b0_b.IT SegItab_Ba_b2a9b0_b.IT_sound BF NX0 BR XSTEP F0 PSS plan 744532 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
