(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BvWfKernel.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.jsoncons.fuzz_bson_parser_max.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PropExec AxSymExec3 AxSymExec3B AxSymExec3Sound AsanPlanCore LibSym SegRun SegPlan SegPlanAuto SegPlanJoin. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import Ba0PlanKit_b Ba0PlanKitIt_b.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B.seg Require SegItab_Ba_21abd1_b.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require SegPlanFast.   (* [comment removed for export] *)
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := AsanUbsan.M.loaded_segments.
Definition ITR : list (Z * nat) := SegItab_Ba_21abd1_b.ITR.
Definition IT : itab := SegItab_Ba_21abd1_b.IT.
Definition ENDS : list Z := [1180172].
Definition STOPS1 : list Z := [1180172] ++ ENDS.
Definition NX0 : nat := 140.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := [ELit 0; EVar 1; EVar 2; EVar 3; EVar 4; EVar 5; EVar 6; EVar 7; ELit 37; ELit 2147483647; (EVar 33); (EVar 34); ELit 1293512; EVar 13; EVar 14; EVar 15; EVar 16; EVar 17; ELit 0; ELit 7; ELit 1293512; ELit 90403; ELit 0; EVar 23; EVar 24; EVar 25; EVar 26; EVar 27; EVar 28; EVar 29; EVar 30; EVar 31].
Definition kn0 : list kentry := [KRange (EVar 2) 140735332552704 140737488355328;
   KAlign (EVar 2) 16;
   KWr (SA (EVar 2) (-112)) (ELit 112);
   KUnk (SA (EVar 2) (-112)) (ELit 112);
   KImg 65536 1282048;
   KRange (EVar 33) 140735332552704 140737488355311;
   KRange (EVar 34) 74 131071;
   KDisj (SA (EVar 2) (-112)) (ELit 112) (SA (EVar 33) 0) (EAlu Instr.ALU_ADD (EVar 34) (ELit 1));
   KWord (SA (ELit 0) (1293544)) 8 ((EAlu Instr.ALU_ADD (EVar 2) (ELit (640))));
   KWord (SA (ELit 0) (1293552)) 8 ((EAlu Instr.ALU_ADD (EVar 2) (ELit (567))));
   KWord (SA (ELit 0) (1293584)) 8 (ELit 1180112);
   KWord (SA (ELit 0) (6896960)) 8 (EVar 40)].
Definition ss0 : sym_state := SS 1187372 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [(EVar 2, (-112), ELit 112)].
Definition F0L : list SR.region := [(EVar 2, (-112), 112)].
Definition BF : nat := 200000.
(* [comment removed for export] *)
Definition BR : list SGP.bfact := [].
(* [comment removed for export] *)
Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

(* [comment removed for export] *)
Definition ex1 : list SGA.aitem * (Z * sym_state) :=
  (([SGA.AStep (SR.SBlock [1180172; 1180172])], (93, SS 1180172 [ELit 0; ELit 1187376; EAlu Instr.ALU_ADD (EVar 2) (ELit (-112)); EVar 3; EVar 4; EVar 5; ELit 1180112; EVar 7; EVar 34; ELit 1293512; EVar 40; EVar 33; EVar 34; EVar 13; EVar 14; EVar 15; EVar 16; EVar 17; ELit 0; ELit 7; ELit 1293512; ELit 6896960; ELit 0; EVar 23; EVar 24; EVar 25; EVar 26; EVar 27; EVar 28; EVar 29; EVar 30; EVar 31] [] [KWord {| a_base := EVar 2; a_off := -72 |} 8 (EVar 40); KWord {| a_base := EVar 2; a_off := -64 |} 8 (ELit 0); KWord {| a_base := EVar 2; a_off := -56 |} 8 (ELit 90403); KWord {| a_base := EVar 2; a_off := -48 |} 8 (ELit 1293512); KWord {| a_base := EVar 2; a_off := -40 |} 8 (ELit 7); KWord {| a_base := EVar 2; a_off := -32 |} 8 (ELit 0); KWord {| a_base := EVar 2; a_off := -24 |} 8 (ELit 2147483647); KWord {| a_base := EVar 2; a_off := -16 |} 8 (ELit 37); KWord {| a_base := EVar 2; a_off := -8 |} 8 (ELit 1187376); KRange (EVar 2) 140735332552704 140737488355328; KAlign (EVar 2) 16; KWr {| a_base := EVar 2; a_off := -112 |} (ELit 112); KUnk {| a_base := EVar 2; a_off := -112 |} (ELit 40); KImg 65536 1282048; KRange (EVar 33) 140735332552704 140737488355311; KRange (EVar 34) 74 131071; KDisj {| a_base := EVar 2; a_off := -112 |} (ELit 112) {| a_base := EVar 33; a_off := 0 |} (EAlu Instr.ALU_ADD (EVar 34) (ELit 1)); KWord {| a_base := ELit 0; a_off := 1293544 |} 8 (EAlu Instr.ALU_ADD (EVar 2) (ELit 640)); KWord {| a_base := ELit 0; a_off := 1293552 |} 8 (EAlu Instr.ALU_ADD (EVar 2) (ELit 567)); KWord {| a_base := ELit 0; a_off := 1293584 |} 8 (ELit 1180112); KWord {| a_base := ELit 0; a_off := 6896960 |} 8 (EVar 40)] 140))).
Definition s1 : sym_state := snd (snd ex1).

Definition plan : SGP.splan := SGA.mkplan (fst ex1) (SGP.PEnd 0).
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
Definition ps0 : SR.post_spec := SR.PS 1180172 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

(* [comment removed for export] *)
Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS SegItab_Ba_21abd1_b.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 1187372 regs0 kn0 = true.
Proof. apply SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

(* [comment removed for export] *)
Definition seg_sound_ax := as0_plan_sound_it SegItab_Ba_21abd1_b.IT SegItab_Ba_21abd1_b.IT_sound BF NX0 BR XSTEP F0 PSS plan 1187372 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
