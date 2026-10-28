(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BvWfKernel.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.jsoncons.fuzz_bson_parser_max.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PropExec AxSymExec3 AxSymExec3B AxSymExec3Sound AsanPlanCore LibSym SegRun SegPlan SegPlanAuto SegPlanJoin SegPlanAutoX. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import Ba0PlanKit_b Ba0PlanKitIt_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B.asan Require Import XIcptA_b XIcptAs0Kit_b.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B.seg Require SegItab_Ba_6baeff_b.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require SegPlanFast. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B.asan Require XIcptAFast_b.   (* [comment removed for export] *)
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := AsanUbsan.M.loaded_segments.
Definition ITR : list (Z * nat) := SegItab_Ba_6baeff_b.ITR.
Definition IT : itab := SegItab_Ba_6baeff_b.IT.
Definition ENDS : list Z := [1044072].
Definition STOPS1 : list Z := [1044072; 490632; 490640] ++ ENDS.
Definition NX0 : nat := 60.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := [ELit 0; EVar 1; EVar 2; EVar 3; EVar 4; EVar 5; EVar 6; EVar 7; EVar 8; EVar 9; (EVar 33); (EAlu Instr.ALU_ADD (EVar 33) (ELit (-64))); ELit 8; EVar 13; EVar 14; EVar 15; EVar 16; EVar 17; EVar 18; EVar 19; EVar 20; EVar 21; EVar 22; EVar 23; EVar 24; EVar 25; EVar 26; EVar 27; EVar 28; EVar 29; EVar 30; EVar 31].
Definition kn0 : list kentry := [KRange (EVar 2) 140735332491264 140737488355328;
   KAlign (EVar 2) 16;
   KWr (SA (EVar 2) (-4096)) (ELit 4096);
   KImg 1249280 1282048;
   KWord (SA (ELit 0) 1309752) 8 (ELit 2147450880);
   KWord (SA (ELit 0) 1309760) 4 (ELit 1);
   KRange (EVar 33) 6905920 2147446512;
   KAlign (EVar 33) 8;
   KDisj (SA (ELit 0) 2147446784) (ELit 17592186048512) (SA (EVar 33) 0) (ELit 272);
   KZero (SA (EAlu Instr.ALU_SRL (EVar 33) (ELit 3)) 2147450880) (ELit 34);
   KWr (SA (EVar 33) 0) (ELit 272);
   KDisj (SA (EVar 2) (-4096)) (ELit 4096) (SA (EVar 33) 0) (ELit 272);
   KDisj (SA (ELit 0) 65536) (ELit 6840320) (SA (EVar 33) 0) (ELit 272);
   KDisj (SA (EVar 2) (-4096)) (ELit 4096) (SA (EVar 33) (-64)) (ELit 24);
   KDisj (SA (ELit 0) 65536) (ELit 6840320) (SA (EVar 33) (-64)) (ELit 24);
   KWord (SA (ELit 0) 1275072) 8 (ELit 1309752);
   KWord (SA (ELit 0) 1309752) 8 (ELit 2147450880);
   KWord (SA (ELit 0) 1275080) 8 (ELit 1313064);
   KWord (SA (ELit 0) 1313064) 8 (ELit 0);
   KWord (SA (ELit 0) 1275088) 8 (ELit 1313072);
   KWord (SA (ELit 0) 1313072) 8 (ELit 0);
   KWord (SA (ELit 0) 1275096) 8 (ELit 1313056);
   KWord (SA (ELit 0) 1313056) 8 (ELit 140737488355327);
   KWord (SA (ELit 0) 1277992) 8 (ELit 1313049);
   KWord (SA (ELit 0) 1313049) 1 (ELit 1);
   KWord (SA (ELit 0) 1283280) 8 (ELit 1219844);
   KWord (SA (ELit 0) 1283272) 8 (ELit 1218816);
   KZero (SA (ELit 0) 2147609117) (ELit 32);
   KZero (SA (EAlu Instr.ALU_SRL (EVar 2) (ELit 3)) 2147450368) (ELit 512)].
Definition ss0 : sym_state := SS 691060 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 2), (-4096), ELit 4096); ((EVar 33), (0), ELit 16); ((EVar 33), (120), ELit 136)].
Definition F0L : list SR.region := [((EVar 2), (-4096), 4096); ((EVar 33), (0), 16); ((EVar 33), (120), 136)].
Definition BF : nat := 1000.
(* [comment removed for export] *)
Definition BR : list SGP.bfact := [].
(* [comment removed for export] *)
Definition XSTEP := XIAS0.xstep.
Definition XSTEP2 := SGP.xstep2_none.
Definition PXA : list (Z * nat) := [(490632, 0%nat); (490640, 1%nat)].
Definition AUTO := SGAX.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0 XSTEP PXA.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

(* [comment removed for export] *)
Definition ex1 : list SGAX.aitem * (Z * sym_state) :=
  (([SGAX.AStep (SR.SBlock [1044072; 490632; 490640; 1044072]); SGAX.APX 0; SGAX.AStep (SR.SBlock [1044072; 490632; 490640; 1044072])], (93, SS 1044072 [ELit 0; ELit 691404; EAlu Instr.ALU_ADD (EVar 2) (ELit (-112)); EVar 3; EVar 4; EVar 61; EVar 62; EVar 63; EVar 33; EAlu Instr.ALU_ADD (EVar 33) (ELit 120); EAlu Instr.ALU_ADD (EVar 33) (ELit 168); EVar 65; EVar 66; EVar 67; EVar 68; EVar 69; EVar 70; EVar 71; ELit 8; EAlu Instr.ALU_ADD (EVar 33) (ELit (-64)); ELit 1266032; EAlu Instr.ALU_ADD (EVar 33) (ELit 16); EAlu Instr.ALU_ADD (EVar 33) (ELit 120); EAlu Instr.ALU_ADD (EAlu Instr.ALU_SRL (EVar 33) (ELit 3)) (ELit 2147450880); ELit 2147450880; ELit 1265968; EAlu Instr.ALU_ADD (EAlu Instr.ALU_SRL (EAlu Instr.ALU_ADD (EVar 33) (ELit 120)) (ELit 3)) (ELit 2147450880); ELit 1266008; EVar 72; EVar 73; EVar 74; EVar 75] [] [KZero {| a_base := EVar 33; a_off := 176 |} (ELit 80); KWord {| a_base := EVar 33; a_off := 152 |} 4 (ELit 0); KWord {| a_base := EVar 33; a_off := 144 |} 8 (ELit 0); KWord {| a_base := EVar 33; a_off := 136 |} 8 (ELit 6); KWord {| a_base := EVar 33; a_off := 128 |} 4 (ELit 4098); KWord {| a_base := EVar 33; a_off := 160 |} 8 (EAlu Instr.ALU_ADD (EVar 33) (ELit 16)); KWord {| a_base := EVar 33; a_off := 156 |} 4 (ELit 0); KWord {| a_base := EVar 2; a_off := -128 |} 8 (EVar 33); KWord {| a_base := EVar 2; a_off := -120 |} 8 (ELit 691404); KWord {| a_base := EVar 33; a_off := 8 |} 8 (ELit 0); KWord {| a_base := EVar 33; a_off := 120 |} 8 (ELit 1266120); KWord {| a_base := EVar 33; a_off := 0 |} 8 (ELit 1266080); KWord {| a_base := EVar 33; a_off := 168 |} 8 (ELit 0); KWord {| a_base := EVar 2; a_off := -104 |} 8 (EVar 27); KWord {| a_base := EVar 2; a_off := -96 |} 8 (EVar 26); KWord {| a_base := EVar 2; a_off := -88 |} 8 (EVar 25); KWord {| a_base := EVar 2; a_off := -80 |} 8 (EVar 24); KWord {| a_base := EVar 2; a_off := -72 |} 8 (EVar 23); KWord {| a_base := EVar 2; a_off := -64 |} 8 (EVar 22); KWord {| a_base := EVar 2; a_off := -56 |} 8 (EVar 21); KWord {| a_base := EVar 2; a_off := -48 |} 8 (EVar 20); KWord {| a_base := EVar 2; a_off := -40 |} 8 (EVar 19); KWord {| a_base := EVar 2; a_off := -32 |} 8 (EVar 18); KWord {| a_base := EVar 2; a_off := -24 |} 8 (EVar 9); KWord {| a_base := EVar 2; a_off := -16 |} 8 (EVar 8); KWord {| a_base := EVar 2; a_off := -8 |} 8 (EVar 1); KRange (EVar 2) 140735332491264 140737488355328; KAlign (EVar 2) 16; KWr {| a_base := EVar 2; a_off := -4096 |} (ELit 4096); KImg 1249280 1282048; KWord {| a_base := ELit 0; a_off := 1309752 |} 8 (ELit 2147450880); KWord {| a_base := ELit 0; a_off := 1309760 |} 4 (ELit 1); KRange (EVar 33) 6905920 2147446512; KAlign (EVar 33) 8; KDisj {| a_base := ELit 0; a_off := 2147446784 |} (ELit 17592186048512) {| a_base := EVar 33; a_off := 0 |} (ELit 272); KZero {| a_base := EAlu Instr.ALU_SRL (EVar 33) (ELit 3); a_off := 2147450880 |} (ELit 34); KWr {| a_base := EVar 33; a_off := 0 |} (ELit 272); KDisj {| a_base := EVar 2; a_off := -4096 |} (ELit 4096) {| a_base := EVar 33; a_off := 0 |} (ELit 272); KDisj {| a_base := ELit 0; a_off := 65536 |} (ELit 6840320) {| a_base := EVar 33; a_off := 0 |} (ELit 272); KDisj {| a_base := EVar 2; a_off := -4096 |} (ELit 4096) {| a_base := EVar 33; a_off := -64 |} (ELit 24); KDisj {| a_base := ELit 0; a_off := 65536 |} (ELit 6840320) {| a_base := EVar 33; a_off := -64 |} (ELit 24); KWord {| a_base := ELit 0; a_off := 1275072 |} 8 (ELit 1309752); KWord {| a_base := ELit 0; a_off := 1309752 |} 8 (ELit 2147450880); KWord {| a_base := ELit 0; a_off := 1275080 |} 8 (ELit 1313064); KWord {| a_base := ELit 0; a_off := 1313064 |} 8 (ELit 0); KWord {| a_base := ELit 0; a_off := 1275088 |} 8 (ELit 1313072); KWord {| a_base := ELit 0; a_off := 1313072 |} 8 (ELit 0); KWord {| a_base := ELit 0; a_off := 1275096 |} 8 (ELit 1313056); KWord {| a_base := ELit 0; a_off := 1313056 |} 8 (ELit 140737488355327); KWord {| a_base := ELit 0; a_off := 1277992 |} 8 (ELit 1313049); KWord {| a_base := ELit 0; a_off := 1313049 |} 1 (ELit 1); KWord {| a_base := ELit 0; a_off := 1283280 |} 8 (ELit 1219844); KWord {| a_base := ELit 0; a_off := 1283272 |} 8 (ELit 1218816); KZero {| a_base := ELit 0; a_off := 2147609117 |} (ELit 32); KZero {| a_base := EAlu Instr.ALU_SRL (EVar 2) (ELit 3); a_off := 2147450368 |} (ELit 512)] 76))).
Definition s1 : sym_state := snd (snd ex1).

Definition plan : SGP.splan := SGAX.mkplan (fst ex1) (SGP.PEnd 0).
Definition in_foot (b : expr) (k : Z) (w : Z) : bool :=
  existsb (fun r : SR.region => let '(rb, rlo, rlen) := r in (expr_eqb rb b && Z.leb rlo k && Z.leb (k + w) (rlo + rlen))%bool) F0L.
Definition in_kn0 (K : kentry) : bool := existsb (APC.kentry_eqb K) kn0.
Definition SPV : nat := 2%nat.   (* [comment removed for export] *)
Definition live (spoff : Z) (b : expr) (k : Z) : bool := (negb (expr_eqb b (EVar SPV)) || Z.leb spoff k)%bool.
(* [comment removed for export] *)
Definition cells_of (sF : sym_state) (spoff : Z) : list kentry :=
  List.filter (fun K => match K with
     | KWord (SA b k) w _ => live spoff b k && (in_foot b k (Z.of_nat w) || negb (in_kn0 K))
     | KZero (SA b k) (ELit n) | KFill (SA b k) (ELit n) _ | KBlob (SA b k) (ELit n) _ => live spoff b k && (in_foot b k n || negb (in_kn0 K))
     | KZero (SA b k) _ | KFill (SA b k) _ _ | KBlob (SA b k) _ _ => live spoff b k && (in_foot b k 1 || negb (in_kn0 K))
     | KUnk (SA b k) (ELit n) => live spoff b k && (in_foot b k n || negb (in_kn0 K))
     | KRange _ _ _ | KAlign _ _ => negb (in_kn0 K)      (* [comment removed for export] *)
     | _ => false end)%bool (s_know sF).
Definition spoff_of (sF : sym_state) : Z := match nth 2 (s_regs sF) (ELit 0) with EAlu _ (EVar v) (ELit k) => if Nat.eqb v SPV then k else 0 | _ => 0 end.

(* [comment removed for export] *)
Definition regs_out0 : list expr := Eval vm_compute in (s_regs s1).
Definition exit_sp_off0 : Z := Eval vm_compute in (spoff_of s1).
Definition cells0 : list kentry := Eval vm_compute in (cells_of s1 exit_sp_off0).
Definition nfresh0 : nat := Eval vm_compute in (s_next s1 - NX0)%nat.
Definition exit_pc0 : Z := Eval vm_compute in (s_pc s1).
Definition ps0 : SR.post_spec := SR.PS 1044072 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

(* [comment removed for export] *)
Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS SegItab_Ba_6baeff_b.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 691060 regs0 kn0 = true.
Proof. apply (SegPlanFast.SGF.cert_by_fast _ _ XIcptAFast_b.XIAS0F.xstep_f_eq). vm_cast_no_check (@eq_refl bool true). Qed.

(* [comment removed for export] *)
Section XH.
Hypothesis HFILL : XIAS0.fill_spec.
Hypothesis HCOPY : XIAS0.copy_spec.
Hypothesis HTLS : XIAS0.tls_spec.
Definition seg_sound_ax := as0_plan_sound_it SegItab_Ba_6baeff_b.IT SegItab_Ba_6baeff_b.IT_sound BF NX0 BR XSTEP F0 PSS plan 691060 regs0 kn0 cert (XIAS0.xstep_ok HFILL HCOPY HTLS NX0 BR F0).
End XH.
