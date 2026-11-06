(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.openssl.pem.lib.Lib Require Import Tac Mem Frame Cells ImageA.
From OSSVerify.Proofs.openssl.pem.lib.Start Require Import AsanRegModel AsanGshModel B_RegConsts B_Gsh.
From OSSVerify.Proofs.openssl.pem.lib.A Require Import Shadow.
From OSSVerify.Proofs.openssl.pem.lib.B Require Import Layout RT_iface RT_iface_pem RT_state RT_rep RT_gshacc RT_iclifts_pem.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Definition GAP_FILE : Z := 0x9f1c0.
Definition GAP_FILE_SZ : Z := 24.
Definition B_GOBJ (b s : Z) : Prop := A_GOBJ b s \/ (b = GAP_FILE /\ s = GAP_FILE_SZ).

Lemma gobj_lift : forall b s, A_GOBJ b s -> B_GOBJ b s.
Proof. intros b s H. left. exact H. Qed.
Lemma gap_gobj : B_GOBJ GAP_FILE GAP_FILE_SZ.
Proof. right. split; reflexivity. Qed.
Lemma gobj_lift_exact : forall l : list (Z * Z), Forall (fun p => A_GOBJ (fst p) (snd p)) l -> Forall (fun p => B_GOBJ (fst p) (snd p)) l.
Proof. intros l H. eapply Forall_impl; [| exact H]. intros p Hp. exact (gobj_lift _ _ Hp). Qed.
Lemma gobj_lift_cover : forall l : list (Z * Z),
  Forall (fun p => exists b sz, A_GOBJ b sz /\ b <= fst p /\ fst p + snd p <= b + sz) l ->
  Forall (fun p => exists b sz, B_GOBJ b sz /\ b <= fst p /\ fst p + snd p <= b + sz) l.
Proof. intros l H. eapply Forall_impl; [| exact H]. intros p (b & sz & G & H1 & H2). exists b, sz. split; [exact (gobj_lift _ _ G)| split; assumption]. Qed.

(* [comment removed for export] *)
Lemma gshw_gap0 : GSM.gshw B_RGC B_GTAB (shad 0x9f1c0) = 0.
Proof. vm_compute. reflexivity. Qed.
Lemma gshw_gap1 : GSM.gshw B_RGC B_GTAB (shad 0x9f1c8) = 0.
Proof. vm_compute. reflexivity. Qed.
Lemma gshw_gap2 : GSM.gshw B_RGC B_GTAB (shad 0x9f1d0) = 0.
Proof. vm_compute. reflexivity. Qed.

Lemma gap_shadow_cell : forall (m : mem) (x : Z), gsh_rep m -> GAP_FILE <= x < GAP_FILE + GAP_FILE_SZ -> m (Z_to_bv 64 (shad x)) = Some (Z_to_bv 8 0).
Proof.
  intros m x GS Hx. unfold GAP_FILE, GAP_FILE_SZ in Hx.
  assert (C : shad x = shad 0x9f1c0 \/ shad x = shad 0x9f1c8 \/ shad x = shad 0x9f1d0).
  { unfold shad. destruct (Z_lt_ge_dec x 0x9f1c8) as [L1|G1]; [left| destruct (Z_lt_ge_dec x 0x9f1d0) as [L2|G2]; [right; left| right; right]];
      f_equal; Z.div_mod_to_equations; lia. }
  assert (R : forall g, (g = 0x9f1c0 \/ g = 0x9f1c8 \/ g = 0x9f1d0) -> shad 0x10000 <= shad g < shad SEGTOP_A).
  { intros g [-> | [-> | ->] ]; (split; [apply Z.leb_le | apply Z.ltb_lt]; vm_compute; reflexivity). }
  destruct C as [E | [E | E] ]; rewrite E.
  - rewrite (GS (shad 0x9f1c0) (R _ (or_introl eq_refl))), gshw_gap0. reflexivity.
  - rewrite (GS (shad 0x9f1c8) (R _ (or_intror (or_introl eq_refl)))), gshw_gap1. reflexivity.
  - rewrite (GS (shad 0x9f1d0) (R _ (or_intror (or_intror eq_refl)))), gshw_gap2. reflexivity.
Qed.

Theorem rta_acc_global_B : RT_iface_pem.acc_global_fact RTA B_GOBJ.
Proof.
  intros Σ m b s a n HA [G | [-> ->] ] H1 H2; [exact (rta_acc_global Σ m b s a n HA G H1 H2)|].
  destruct (ART_shadow Σ m HA) as (_ & _ & _ & _ & _ & GS).
  intros i Hi. pose proof (gap_shadow_cell m (a + i) GS ltac:(lia)) as CELL.
  exists (Z_to_bv 8 0). split; [| left; reflexivity].
  unfold GAP_FILE, GAP_FILE_SZ in *.
  split; [unfold shad, SHB; clear - H1 Hi; Z.div_mod_to_equations; lia|]. split; [unfold shad, SHB; cbn [length]; clear - H1 H2 Hi; Z.div_mod_to_equations; lia|].
  intros j Hj. cbn [length] in Hj. assert (j = 0%nat) by lia. subst j. cbn [nth_error Z.of_nat]. rewrite Z.add_0_r. unfold mrd, wa. rewrite CELL. reflexivity.
Qed.

Theorem rta_gsh_byte_B : RT_iface_pem.gsh_byte_fact RTA B_GOBJ.
Proof.
  intros Σ m b s g HA [G | [-> ->] ] H1 H2 G8; [exact (rta_gsh_byte Σ m b s g HA G H1 H2 G8)|].
  destruct (ART_shadow Σ m HA) as (_ & _ & _ & _ & _ & GS).
  pose proof (gap_shadow_cell m g GS ltac:(lia)) as CELL. unfold GAP_FILE, GAP_FILE_SZ in *.
  replace (651712 + 24 - g <? 8) with false by (symmetry; apply Z.ltb_ge; clear - H1 H2 G8; Z.div_mod_to_equations; lia).
  change (g / 8 + 2147450880) with (shad g).
  unfold ro_cells, cells_at. cbn [cells_wf cells_bytes cbytes]. rewrite app_nil_r. split; [split; [reflexivity| exact I]|].
  split; [unfold shad, SHB; clear - H1 H2; Z.div_mod_to_equations; lia|]. split; [unfold shad, SHB; cbn [length]; clear - H1 H2; Z.div_mod_to_equations; lia|].
  intros j Hj. cbn [length] in Hj. assert (j = 0%nat) by lia. subst j. cbn [nth_error Z.of_nat]. rewrite Z.add_0_r. unfold mrd, wa. rewrite CELL. reflexivity.
Qed.

Theorem rta_art_facts_pem_B : art_facts_pem RTA B_GOBJ.
Proof. exact (mkAFP RTA B_GOBJ rta_acc_global_B rta_gsh_byte_B rta_live_mem rta_live_hi rta_frame_mem). Qed.
