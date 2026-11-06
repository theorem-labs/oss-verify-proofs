(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3 Require Import A3Img.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import MState Mem Cells Step.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA Require Import AsanEmbed.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.AS Require MainExport MainAux. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.AS Require MainEntry__AS. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.AS.MainExport OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.AS.MainAux OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.AS.MainEntry__AS.MainReady.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Definition pfact_eqb (f g : pfact) : bool :=
  match f, g with
  | PVar n lo hi, PVar n' lo' hi' => Nat.eqb n n' && Z.eqb lo lo' && Z.eqb hi hi'
  | PRange e lo hi, PRange e' lo' hi' => zexp_eqb e e' && Z.eqb lo lo' && Z.eqb hi hi'
  | PDisj a1 n1 a2 n2, PDisj a1' n1' a2' n2' => zexp_eqb a1 a1' && Z.eqb n1 n1' && zexp_eqb a2 a2' && Z.eqb n2 n2'
  | _, _ => false
  end.
Lemma pfact_eqb_eq : forall f g, pfact_eqb f g = true -> f = g.
Proof.
  intros f g H. destruct f, g; cbn in H; try discriminate;
    repeat (apply andb_prop in H as [H ?X]);
    repeat match goal with
    | K : zexp_eqb _ _ = true |- _ => apply zexp_eqb_eq in K
    | K : Z.eqb _ _ = true |- _ => apply Z.eqb_eq in K
    | K : Nat.eqb _ _ = true |- _ => apply Nat.eqb_eq in K
    end; subst; reflexivity.
Qed.
Lemma pfact_find : forall V (l : list pfact) f,
  Forall (pfact_ok V) l -> existsb (pfact_eqb f) l = true -> pfact_ok V f.
Proof.
  intros V l f HF HE. apply existsb_exists in HE as (g & Hin & Hg). apply pfact_eqb_eq in Hg. subst g.
  exact (proj1 (Forall_forall _ _) HF f Hin).
Qed.
Local Ltac pf V HP f H := pose proof (pfact_find V _ f HP ltac:(vm_compute; reflexivity)) as H; cbn [pfact_ok zv] in H.

Definition aspace_beg (V : nat -> Z) : Z := 4096 * V 208%nat - 4096 * V 209%nat + 65536.

(* [comment removed for export] *)
Lemma shadow_disj : forall SB b n a, SB mod 8 = 0 -> (SB + 2 ^ 37 <= b \/ b + n <= SB) ->
  2147450880 + SB / 8 <= a < 2147450880 + SB / 8 + 2 ^ 34 -> 2147450880 + b / 8 <= a < 2147450880 + (b + n) / 8 -> False.
Proof. intros SB b n a H8 HD H1 H2. Z.div_mod_to_equations. lia. Qed.

Theorem primary_shadow0 : forall (V : nat -> Z) (m : word -> option byte),
  ashadow0 V m -> Forall (pfact_ok V) asan_pure_facts ->
  (forall i, 0 <= i < 2^34 -> m (wa (shad (aspace_beg V) + i)) = Some (Z_to_bv 8 0))
  /\ wr_at SEGS m (shad (aspace_beg V)) (2^34).
Proof.
  intros V m SH HP.
  pf V HP (PVar 208 4295491576 34326181871) P208. pf V HP (PVar 209 0 15) P209.
  pf V HP (PVar 0 4294901760 4294967295) P0. pf V HP (PVar 10 0 7) P10.
  pf V HP (PDisj (ZMul (ZLit 4096) (ZV 208)) 137439023104 (ZMul (ZLit 4096) (ZV 568)) 4096) D568.
  pf V HP (PDisj (ZMul (ZLit 4096) (ZV 208)) 137439023104 (ZMul (ZLit 4096) (ZV 487)) 4096) D487.
  pf V HP (PDisj (ZMul (ZLit 4096) (ZV 208)) 137439023104 (ZMul (ZLit 4096) (ZV 470)) 8388608) D470.
  pf V HP (PDisj (ZMul (ZLit 4096) (ZV 208)) 137439023104 (ZMul (ZLit 4096) (ZV 469)) 1048576) D469.
  pf V HP (PDisj (ZMul (ZLit 4096) (ZV 208)) 137439023104 (ZMul (ZLit 4096) (ZV 393)) 11571200) D393.
  pf V HP (PDisj (ZMul (ZLit 4096) (ZV 208)) 137439023104 (ZMul (ZLit 4096) (ZV 310)) 4096) D310.
  pf V HP (PDisj (ZMul (ZLit 4096) (ZV 208)) 137439023104 (ZMul (ZLit 4096) (ZV 245)) 4096) D245.
  pf V HP (PDisj (ZMul (ZLit 4096) (ZV 208)) 137439023104 (ZMul (ZLit 4096) (ZV 228)) 65536) D228.
  pf V HP (PDisj (ZMul (ZLit 4096) (ZV 208)) 137439023104 (ZMul (ZLit 4096) (ZV 227)) 4096) D227.
  pf V HP (PDisj (ZMul (ZLit 4096) (ZV 208)) 137439023104 (ZMul (ZLit 4096) (ZV 207)) 3727360) D207.
  pf V HP (PDisj (ZMul (ZLit 4096) (ZV 208)) 137439023104 (ZMul (ZLit 4096) (ZV 78)) 65536) D78.
  pf V HP (PDisj (ZMul (ZLit 4096) (ZV 208)) 137439023104 (ZV 1103) 4096) D1103.
  pf V HP (PDisj (ZMul (ZLit 4096) (ZV 208)) 137439023104 (ZV 1102) 8192) D1102.
  pf V HP (PDisj (ZMul (ZLit 4096) (ZV 208)) 137439023104 STKWIN_BASE STKWIN_LEN) DW. cbn [zv STKWIN_BASE] in DW. unfold STKWIN_LEN in DW.
  set (SB := aspace_beg V).
  assert (SBR : 4096 * V 208%nat + 4096 <= SB /\ SB + 2^37 + 4096 <= 4096 * V 208%nat + 137439023104 /\ SB mod 8 = 0).
  { subst SB. unfold aspace_beg. split; [lia|]. split; [lia|]. clear. Z.div_mod_to_equations. lia. }
  destruct SBR as (S1 & S2 & S8).
  assert (SHE : shad SB = 2147450880 + SB / 8) by (unfold shad, AsanEmbed.ASHOFF; rewrite Z.shiftr_div_pow2 by lia; reflexivity).
  destruct (ashadow0_range V m (shad SB) (2^34) SH ltac:(lia)) as (Z0 & W0 & _); [| split; [exact Z0| exact W0]].
  intros a Ha. rewrite SHE in Ha.
  split.
  - unfold ashadow. right. clear - Ha P208 S1 S2. Z.div_mod_to_equations. lia.
  - assert (HELP : forall b n, (4096 * V 208%nat + 137439023104 <= b \/ b + n <= 4096 * V 208%nat) -> SB + 2 ^ 37 <= b \/ b + n <= SB)
      by (intros b n [H|H]; [left | right]; clear - H S1 S2; lia).
    intros (bn & Hin & Hr). unfold asan_vis_app in Hin. cbn [In] in Hin. unfold ASHOFF in Hr.
    repeat (destruct Hin as [<-|Hin]; [cbn [fst snd zv] in Hr; exfalso; eapply (shadow_disj SB _ _ a S8); [ | exact Ha | exact Hr] |]); [..| destruct Hin].
    + apply HELP. exact D568.
    + apply HELP. exact D487.
    + apply HELP. exact D470.
    + apply HELP. exact D469.
    + apply HELP. exact D393.
    + apply HELP. exact D310.
    + apply HELP. exact D245.
    + apply HELP. exact D228.
    + apply HELP. exact D227.
    + (* [comment removed for export] *) left. subst SB. unfold aspace_beg. clear. lia.
    + apply HELP. exact D207.
    + apply HELP. exact D78.
    + (* [comment removed for export] *) right. clear - S1 P208. lia.
    + (* [comment removed for export] *) apply HELP. clear - DW P0 P10. lia.
    + apply HELP. exact D1103.
    + apply HELP. exact D1102.
Qed.

(* [comment removed for export] *)
Lemma sb_align : forall (V : nat -> Z), (forall n, 0 <= V n < 2 ^ 64) -> Forall (pfact_ok V) asan_pure_facts ->
  (4096 * V 208%nat) mod 65536 = 4096 * V 209%nat /\ aspace_beg V mod 65536 = 0.
Proof.
  intros V HVR HP.
  pf V HP (PVar 209 0 15) P209.
  pf V HP (PRange (ZAdd (ZMul (ZLit (-4096)) (ZV 209)) (ZAnd (ZMul (ZLit 4096) (ZV 208)) (ZLit 65535))) 0 0) PA.
  change 65535 with (Z.ones 16) in PA. rewrite Z.land_ones in PA by lia. change (2 ^ 16) with 65536 in PA.
  pose proof (HVR 208%nat) as R208. pose proof (Z.mod_pos_bound (4096 * V 208%nat) 65536 ltac:(lia)) as MB.
  assert (E : -4096 * V 209%nat + (4096 * V 208%nat) mod 65536 = 0).
  { unfold MainExport.two64 in PA. set (t := -4096 * V 209%nat + (4096 * V 208%nat) mod 65536) in *.
    assert (TR : -61440 <= t < 65536) by (unfold t; lia). clearbody t. clear - PA TR. Z.div_mod_to_equations. lia. }
  split; [lia|]. unfold aspace_beg. clear - E. Z.div_mod_to_equations. lia.
Qed.

(* [comment removed for export] *)

Module TwB.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.A3Img.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.MState OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Mem OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Cells OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Step.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA.AsanEmbed.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.AS.MainExport.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.AS.MainAux.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.AS.MainEntry__AS.MainReady.TwB.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Definition pfact_eqb (f g : pfact) : bool :=
  match f, g with
  | PVar n lo hi, PVar n' lo' hi' => Nat.eqb n n' && Z.eqb lo lo' && Z.eqb hi hi'
  | PRange e lo hi, PRange e' lo' hi' => zexp_eqb e e' && Z.eqb lo lo' && Z.eqb hi hi'
  | PDisj a1 n1 a2 n2, PDisj a1' n1' a2' n2' => zexp_eqb a1 a1' && Z.eqb n1 n1' && zexp_eqb a2 a2' && Z.eqb n2 n2'
  | _, _ => false
  end.
Lemma pfact_eqb_eq : forall f g, pfact_eqb f g = true -> f = g.
Proof.
  intros f g H. destruct f, g; cbn in H; try discriminate;
    repeat (apply andb_prop in H as [H ?X]);
    repeat match goal with
    | K : zexp_eqb _ _ = true |- _ => apply zexp_eqb_eq in K
    | K : Z.eqb _ _ = true |- _ => apply Z.eqb_eq in K
    | K : Nat.eqb _ _ = true |- _ => apply Nat.eqb_eq in K
    end; subst; reflexivity.
Qed.
Lemma pfact_find : forall V (l : list pfact) f,
  Forall (pfact_ok V) l -> existsb (pfact_eqb f) l = true -> pfact_ok V f.
Proof.
  intros V l f HF HE. apply existsb_exists in HE as (g & Hin & Hg). apply pfact_eqb_eq in Hg. subst g.
  exact (proj1 (Forall_forall _ _) HF f Hin).
Qed.
Local Ltac pf V HP f H := pose proof (pfact_find V _ f HP ltac:(vm_compute; reflexivity)) as H; cbn [pfact_ok zv] in H.

Definition aspace_beg (V : nat -> Z) : Z := 4096 * V 208%nat - 4096 * V 209%nat + 65536.

(* [comment removed for export] *)
Lemma shadow_disj : forall SB b n a, SB mod 8 = 0 -> (SB + 2 ^ 37 <= b \/ b + n <= SB) ->
  2147450880 + SB / 8 <= a < 2147450880 + SB / 8 + 2 ^ 34 -> 2147450880 + b / 8 <= a < 2147450880 + (b + n) / 8 -> False.
Proof. intros SB b n a H8 HD H1 H2. Z.div_mod_to_equations. lia. Qed.

Theorem primary_shadow0 : forall (V : nat -> Z) (m : word -> option byte),
  ashadow0 V m -> Forall (pfact_ok V) asan_pure_facts ->
  (forall i, 0 <= i < 2^34 -> m (wa (shad (aspace_beg V) + i)) = Some (Z_to_bv 8 0))
  /\ wr_at SEGS m (shad (aspace_beg V)) (2^34).
Proof.
  intros V m SH HP.
  pf V HP (PVar 208 4295491576 34326181871) P208. pf V HP (PVar 209 0 15) P209.
  pf V HP (PVar 0 4294901760 4294967295) P0. pf V HP (PVar 10 0 7) P10.
  pf V HP (PDisj (ZMul (ZLit 4096) (ZV 208)) 137439023104 (ZMul (ZLit 4096) (ZV 568)) 4096) D568.
  pf V HP (PDisj (ZMul (ZLit 4096) (ZV 208)) 137439023104 (ZMul (ZLit 4096) (ZV 487)) 4096) D487.
  pf V HP (PDisj (ZMul (ZLit 4096) (ZV 208)) 137439023104 (ZMul (ZLit 4096) (ZV 470)) 8388608) D470.
  pf V HP (PDisj (ZMul (ZLit 4096) (ZV 208)) 137439023104 (ZMul (ZLit 4096) (ZV 469)) 1048576) D469.
  pf V HP (PDisj (ZMul (ZLit 4096) (ZV 208)) 137439023104 (ZMul (ZLit 4096) (ZV 393)) 11571200) D393.
  pf V HP (PDisj (ZMul (ZLit 4096) (ZV 208)) 137439023104 (ZMul (ZLit 4096) (ZV 310)) 4096) D310.
  pf V HP (PDisj (ZMul (ZLit 4096) (ZV 208)) 137439023104 (ZMul (ZLit 4096) (ZV 245)) 4096) D245.
  pf V HP (PDisj (ZMul (ZLit 4096) (ZV 208)) 137439023104 (ZMul (ZLit 4096) (ZV 228)) 65536) D228.
  pf V HP (PDisj (ZMul (ZLit 4096) (ZV 208)) 137439023104 (ZMul (ZLit 4096) (ZV 227)) 4096) D227.
  pf V HP (PDisj (ZMul (ZLit 4096) (ZV 208)) 137439023104 (ZMul (ZLit 4096) (ZV 207)) 3727360) D207.
  pf V HP (PDisj (ZMul (ZLit 4096) (ZV 208)) 137439023104 (ZMul (ZLit 4096) (ZV 78)) 65536) D78.
  pf V HP (PDisj (ZMul (ZLit 4096) (ZV 208)) 137439023104 (ZV 1103) 4096) D1103.
  pf V HP (PDisj (ZMul (ZLit 4096) (ZV 208)) 137439023104 (ZV 1102) 8192) D1102.
  pf V HP (PDisj (ZMul (ZLit 4096) (ZV 208)) 137439023104 STKWIN_BASE STKWIN_LEN) DW. cbn [zv STKWIN_BASE] in DW. unfold STKWIN_LEN in DW.
  set (SB := aspace_beg V).
  assert (SBR : 4096 * V 208%nat + 4096 <= SB /\ SB + 2^37 + 4096 <= 4096 * V 208%nat + 137439023104 /\ SB mod 8 = 0).
  { subst SB. unfold aspace_beg. split; [lia|]. split; [lia|]. clear. Z.div_mod_to_equations. lia. }
  destruct SBR as (S1 & S2 & S8).
  assert (SHE : shad SB = 2147450880 + SB / 8) by (unfold shad, AsanEmbed.ASHOFF; rewrite Z.shiftr_div_pow2 by lia; reflexivity).
  destruct (ashadow0_range V m (shad SB) (2^34) SH ltac:(lia)) as (Z0 & W0 & _); [| split; [exact Z0| exact W0]].
  intros a Ha. rewrite SHE in Ha.
  split.
  - unfold ashadow. right. clear - Ha P208 S1 S2. Z.div_mod_to_equations. lia.
  - assert (HELP : forall b n, (4096 * V 208%nat + 137439023104 <= b \/ b + n <= 4096 * V 208%nat) -> SB + 2 ^ 37 <= b \/ b + n <= SB)
      by (intros b n [H|H]; [left | right]; clear - H S1 S2; lia).
    intros (bn & Hin & Hr). unfold asan_vis_app in Hin. cbn [In] in Hin. unfold ASHOFF in Hr.
    repeat (destruct Hin as [<-|Hin]; [cbn [fst snd zv] in Hr; exfalso; eapply (shadow_disj SB _ _ a S8); [ | exact Ha | exact Hr] |]); [..| destruct Hin].
    + apply HELP. exact D568.
    + apply HELP. exact D487.
    + apply HELP. exact D470.
    + apply HELP. exact D469.
    + apply HELP. exact D393.
    + apply HELP. exact D310.
    + apply HELP. exact D245.
    + apply HELP. exact D228.
    + apply HELP. exact D227.
    + (* [comment removed for export] *) left. subst SB. unfold aspace_beg. clear. lia.
    + apply HELP. exact D207.
    + apply HELP. exact D78.
    + (* [comment removed for export] *) right. clear - S1 P208. lia.
    + (* [comment removed for export] *) apply HELP. clear - DW P0 P10. lia.
    + apply HELP. exact D1103.
    + apply HELP. exact D1102.
Qed.

(* [comment removed for export] *)
Lemma sb_align : forall (V : nat -> Z), (forall n, 0 <= V n < 2 ^ 64) -> Forall (pfact_ok V) asan_pure_facts ->
  (4096 * V 208%nat) mod 65536 = 4096 * V 209%nat /\ aspace_beg V mod 65536 = 0.
Proof.
  intros V HVR HP.
  pf V HP (PVar 209 0 15) P209.
  pf V HP (PRange (ZAdd (ZMul (ZLit (-4096)) (ZV 209)) (ZAnd (ZMul (ZLit 4096) (ZV 208)) (ZLit 65535))) 0 0) PA.
  change 65535 with (Z.ones 16) in PA. rewrite Z.land_ones in PA by lia. change (2 ^ 16) with 65536 in PA.
  pose proof (HVR 208%nat) as R208. pose proof (Z.mod_pos_bound (4096 * V 208%nat) 65536 ltac:(lia)) as MB.
  assert (E : -4096 * V 209%nat + (4096 * V 208%nat) mod 65536 = 0).
  { unfold AS.MainExport.TwB.two64 in PA. set (t := -4096 * V 209%nat + (4096 * V 208%nat) mod 65536) in *.
    assert (TR : -61440 <= t < 65536) by (unfold t; lia). clearbody t. clear - PA TR. Z.div_mod_to_equations. lia. }
  split; [lia|]. unfold aspace_beg. clear - E. Z.div_mod_to_equations. lia.
Qed.
End TwB.
