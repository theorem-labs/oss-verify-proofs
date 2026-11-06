(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.jsoncons.fuzz_bigint.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib Require Import PropExec AxSymExec3 AxSymExec3B AxSymExec3Sound AsanPlanCore LibSym SegRun SegPlan SegPlanAuto SegPlanJoin SegPlanAutoX As0PlanKit As0PlanKitIt XIcptA XIcptAs0Kit.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib.seg Require SegItab_A_629ddd.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := SegItab_A_629ddd.ITR.
Definition IT : itab := SegItab_A_629ddd.IT.
Definition ENDS : list Z := [392276].
Definition STOPS1 : list Z := [385224; 385232; 318384; 392280; 392276; 392288; 422120; 318480; 385228; 318468; 318464] ++ ENDS.
Definition NX0 : nat := 56.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := [ELit 0; EVar 1; EAlu Instr.ALU_ADD (EVar 2) (ELit (-16)); ELit 67584; ELit 6360328; EVar 5; EVar 6; EVar 7; EVar 10; EVar 9; EVar 40; EVar 11; EVar 12; EVar 13; EVar 14; EVar 15; EVar 16; EVar 17; EVar 18; EVar 19; EVar 20; EVar 21; EVar 22; EVar 23; EVar 24; EVar 25; EVar 26; EVar 27; EVar 28; EVar 29; EVar 30; EVar 31].
Definition kn0 : list kentry := [KRange (EVar 2) 140735332552704 140737488355264;
   KAlign (EVar 2) 16;
   KWr (SA (EVar 2) (-80)) (ELit 64);
   KUnk (SA (EVar 2) (-80)) (ELit 64);
   KRange (EVar 10) 6500480 140737488355328;
   KAlign (EVar 10) 16;
   KWr (SA (EVar 10) (-128)) (ELit 160);
   KUnk (SA (EVar 10) (-128)) (ELit 160);
   KDisj (SA (ELit 0) 2147446784) (ELit 17592186048512) (SA (EVar 10) (-128)) (ELit 160);
   KZero (SA (EAlu Instr.ALU_SRL (EVar 10) (ELit 3)) (2147450864)) (ELit 20);
   KDisj (SA (EVar 2) (-80)) (ELit 4160) (SA (EVar 10) (-128)) (ELit 160);
   KDisj (SA (EVar 10) (-128)) (ELit 160) (SA (ELit 0) 65536) (ELit 6434816);
   KZero (SA (EAlu Instr.ALU_SRL (EVar 2) (ELit 3)) (2147450870)) (ELit 8);
   KImg 65536 880640;
   KImg 892736 892768;
   KWord (SA (EVar 2) (-8)) 8 (ELit 722996);
   KWord (SA (EVar 2) (-16)) 8 (EAlu Instr.ALU_ADD (EVar 10) (ELit (-128)))].
Definition ss0 : sym_state := SS 718792 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [(EVar 2, (-80), ELit 64)].
Definition F0L : list SR.region := [(EVar 2, (-80), 64)].
Definition BF : nat := 200000.
(* [comment removed for export] *)
Definition BR : list SGP.bfact := [].
(* [comment removed for export] *)
Definition XSTEP := XIAS0.xstep.
Definition XSTEP2 := SGP.xstep2_none.
Definition PXA : list (Z * nat) := [(385224, 0%nat); (385232, 1%nat); (318480, 2%nat)].
Definition AUTO := SGAX.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0 XSTEP PXA.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

(* [comment removed for export] *)
Definition ex1 : list SGAX.aitem * (Z * sym_state) :=
  (([SGAX.AStep (SR.SBlock [385224; 385232; 318384; 392280; 392276; 392288; 422120; 318480; 385228; 318468; 318464; 392276])], (93, SS 392276 [ELit 0; ELit 723004; EVar 2; ELit 67584; ELit 6360328; EVar 5; EVar 6; EVar 7; EAlu Instr.ALU_ADD (EVar 10) (ELit (-128)); EVar 9; EAlu Instr.ALU_ADD (EVar 10) (ELit (-128)); ELit 6357472; ELit 6357488; EVar 13; ELit 6358000; EVar 15; EVar 16; EVar 17; EVar 18; EVar 19; EVar 20; EVar 21; EVar 22; EVar 23; EVar 24; EVar 25; EVar 26; EVar 27; EVar 28; EVar 29; EVar 30; EVar 31] [] [KRange (EVar 2) 140735332552704 140737488355264; KAlign (EVar 2) 16; KWr {| a_base := EVar 2; a_off := -80 |} (ELit 64); KUnk {| a_base := EVar 2; a_off := -80 |} (ELit 64); KRange (EVar 10) 6500480 140737488355328; KAlign (EVar 10) 16; KWr {| a_base := EVar 10; a_off := -128 |} (ELit 160); KUnk {| a_base := EVar 10; a_off := -128 |} (ELit 160); KDisj {| a_base := ELit 0; a_off := 2147446784 |} (ELit 17592186048512) {| a_base := EVar 10; a_off := -128 |} (ELit 160); KZero {| a_base := EAlu Instr.ALU_SRL (EVar 10) (ELit 3); a_off := 2147450864 |} (ELit 20); KDisj {| a_base := EVar 2; a_off := -80 |} (ELit 4160) {| a_base := EVar 10; a_off := -128 |} (ELit 160); KDisj {| a_base := EVar 10; a_off := -128 |} (ELit 160) {| a_base := ELit 0; a_off := 65536 |} (ELit 6434816); KZero {| a_base := EAlu Instr.ALU_SRL (EVar 2) (ELit 3); a_off := 2147450870 |} (ELit 8); KImg 65536 880640; KImg 892736 892768; KWord {| a_base := EVar 2; a_off := -8 |} 8 (ELit 722996); KWord {| a_base := EVar 2; a_off := -16 |} 8 (EAlu Instr.ALU_ADD (EVar 10) (ELit (-128)))] 56))).
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
Definition ps0 : SR.post_spec := SR.PS 392276 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

(* [comment removed for export] *)
Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS SegItab_A_629ddd.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 718792 regs0 kn0 = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.

(* [comment removed for export] *)
Section XH.
Hypothesis HFILL : XIAS0.fill_spec.
Hypothesis HCOPY : XIAS0.copy_spec.
Hypothesis HTLS : XIAS0.tls_spec.
Definition seg_sound_ax := as0_plan_sound_it SegItab_A_629ddd.IT SegItab_A_629ddd.IT_sound BF NX0 BR XSTEP F0 PSS plan 718792 regs0 kn0 cert (XIAS0.xstep_ok HFILL HCOPY HTLS NX0 BR F0).
End XH.
