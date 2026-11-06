(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP Mem Cells Frame RunConst InitMem.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.AS Require Import MainExport MainFactsAsan MainEntry.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Spec Require Import AsanProgDeps AsanEmbed.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.LibA Require Import Shadow.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Common Require Import RunDraw.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.AsanW Require Import AImg ABase AU_kit AU_iface AU_consts AHarnessU_iface AAtexit_iface F_module_dtor_pre
     AD_handoff_md AD_hokit AD_handoff_exit AD_handoff0 ADriver_iface.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Section Bytes. Context {rc : runConstT}.
Definition byte_factb (A b : Z) (f : mfact) : bool :=
  match f with
  | MZero (ZLit a) n => (a <=? A) && (A <? a + n) && (b =? 0)
  | MFill (ZLit a) n c => (a <=? A) && (A <? a + n) && (b =? c)
  | MCell (ZLit a) 1 (ZLit v) => (a =? A) && (v =? b)
  | _ => false
  end.
Lemma byte_fact_sound : forall V (m : word -> option byte) l A b, Forall (mfact_ok asegs V m) l ->
  existsb (byte_factb A b) l = true -> mrd asegs m (wa A) = Some (Z_to_bv 8 b).
Proof.
  intros V m l A b HM HE. apply existsb_exists in HE as (f & Hin & Hf).
  pose proof (proj1 (Forall_forall _ _) HM f Hin) as K.
  destruct f as [a w v|a n|a w v|a n|a n c|l' h|a n|a n|a n|a n]; cbn [byte_factb] in Hf; try discriminate.
  - destruct a as [z| | | | |]; try discriminate. destruct w as [|[|w]]; try discriminate. destruct v as [vz| | | | |]; try discriminate.
    apply andb_prop in Hf as [H1 H2]. apply Z.eqb_eq in H1. apply Z.eqb_eq in H2. subst.
    cbn [mfact_ok zv cellw] in K. destruct K as [[_ B] _]. destruct B as (_ & _ & B). specialize (B 0%nat ltac:(cbn; lia)).
    cbn in B. rewrite Z.add_0_r in B. exact B.
  - destruct a as [z| | | | |]; try discriminate. apply andb_prop in Hf as [H1 H3]. apply andb_prop in H1 as [H1 H2].
    apply Z.leb_le in H1. apply Z.ltb_lt in H2. apply Z.eqb_eq in H3. subst b. cbn [mfact_ok zv] in K.
    specialize (K (A - z) ltac:(lia)). replace (z + (A - z)) with A in K by lia. unfold mrd. rewrite K. reflexivity.
  - destruct a as [z| | | | |]; try discriminate. apply andb_prop in Hf as [H1 H3]. apply andb_prop in H1 as [H1 H2].
    apply Z.leb_le in H1. apply Z.ltb_lt in H2. apply Z.eqb_eq in H3. subst b. cbn [mfact_ok zv] in K.
    specialize (K (A - z) ltac:(lia)). replace (z + (A - z)) with A in K by lia. unfold mrd. rewrite K. reflexivity.
Qed.
Fixpoint bytes_factb (l : list mfact) (A : Z) (bs : list Z) : bool :=
  match bs with [] => true | b :: bs' => existsb (byte_factb A b) l && bytes_factb l (A + 1) bs' end.
Lemma bytes_fact_sound : forall V (m : word -> option byte) l bs A, Forall (mfact_ok asegs V m) l ->
  bytes_factb l A bs = true -> forall i, (i < length bs)%nat -> mrd asegs m (wa (A + Z.of_nat i)) = nth_error (map (Z_to_bv 8) bs) i.
Proof.
  intros V m l bs. induction bs as [|b bs IH]; intros A HM HE i Hi; cbn [length] in Hi; [lia|].
  cbn [bytes_factb] in HE. apply andb_prop in HE as [H1 H2].
  destruct i as [|i]; cbn [nth_error map].
  - rewrite Z.add_0_r. exact (byte_fact_sound V m l A b HM H1).
  - replace (A + Z.of_nat (S i)) with ((A + 1) + Z.of_nat i) by lia. apply (IH (A + 1) HM H2 i). lia.
Qed.
Lemma rw_cells_of_facts : forall V (m : word -> option byte) l A (bs : list Z), Forall (mfact_ok asegs V m) l ->
  0 <= A -> A + Z.of_nat (length bs) <= 2^64 ->
  bytes_factb l A bs = true -> wr_covb l A (Z.of_nat (length bs)) = true ->
  rw_cells asegs m A [CB (length bs) (map (Z_to_bv 8) bs)].
Proof.
  intros V m l A bs HM H0 H1 HB HW. pose proof (wr_cov V m l A _ HM HW ltac:(lia)) as W. split.
  - split; [cbn; split; [rewrite length_map; reflexivity| exact I]|].
    cbn [cells_bytes cbytes]. rewrite app_nil_r. split; [lia|]. split; [rewrite length_map; lia|].
    intros i Hi. rewrite length_map in Hi. exact (bytes_fact_sound V m l bs A HM HB i Hi).
  - cbn [cells_size csize]. rewrite Nat.add_0_r. exact W.
Qed.
(* [comment removed for export] *)
Lemma zero_chunk_of_facts : forall V (m : word -> option byte) l A n, Forall (mfact_ok asegs V m) l ->
  0x665000 <= A -> 0 <= n -> A + n <= 2^64 ->
  existsb (mzero_covb A n) l = true -> wr_covb l A n = true ->
  rw_cells asegs m A [CB (Z.to_nat n) (repeat (Z_to_bv 8 0) (Z.to_nat n))].
Proof.
  intros V m l A n HM HA Hn HT HZ HW. pose proof (wr_cov V m l A n HM HW Hn) as W.
  split; [split|].
  - cbn. split; [rewrite repeat_length; reflexivity| exact I].
  - cbn [cells_bytes cbytes]. rewrite app_nil_r. split; [lia|]. split; [rewrite repeat_length; lia|].
    intros i Hi. rewrite repeat_length in Hi. rewrite ref_mrd_overlay by (rewrite wa_unsigned by lia; lia).
    rewrite nth_error_repeat by lia. exact (mzero_cover V m l A n HM HZ (Z.of_nat i) ltac:(lia)).
  - cbn [cells_size csize]. rewrite Nat.add_0_r, Z2Nat.id by lia. exact W.
Qed.
End Bytes.

Section CANSEC1. Context {rc : runConstT} {XP : ExitParams}.
Section Handoff.
  Variables (V : nat -> Z) (m : word -> option byte).
  Hypothesis HM : Forall (mfact_ok asegs V m) asan_mem_facts.
  Ltac go := repeat match goal with |- _ /\ _ => split end; ho_cells V m HM.

  (* [comment removed for export] *)
  Lemma client_x_init : client_x m.
  Proof.
    unfold client_x. split; [unfold rt_real_mc, AREAL_MC; ho_cells V m HM|].
    split; [unfold rt_fmin, AFMIN; ho_cells V m HM|].
    split.
    - unfold rt_bom_sh. let a := eval vm_compute in (shad ABOM) in change (shad ABOM) with a.
      apply (rw_cells_recast asegs m _ [CB 8 (map (Z_to_bv 8) [0; 5; 249; 249; 4; 249; 249; 249])]);
        [ apply (rw_cells_of_facts V m asan_mem_facts _ [0; 5; 249; 249; 4; 249; 249; 249] HM); [lia | cbn; lia | vm_compute; reflexivity | vm_compute; reflexivity]
        | cbn; repeat split; exact I | vm_compute; reflexivity | reflexivity ].
    - split.
      + unfold rt_ctab_sh. let a := eval vm_compute in (shad ACTAB) in change (shad ACTAB) with a;
          exact (mfact_find asegs V m asan_mem_facts (MZeroC (ZLit a) 32) HM ltac:(vm_compute; reflexivity)).
      + (* [comment removed for export] *)
        unfold img_sh, IMG_TABS.
        repeat (apply Forall_cons;
                [ unfold tab_sh; cbn [fst snd];
                  lazymatch goal with |- rw_cells _ _ (shad ?lo) [CB (Z.to_nat ((?hi - ?lo) / 8)) _] =>
                    let A := eval vm_compute in (shad lo) in let N := eval vm_compute in ((hi - lo) / 8) in
                    change (shad lo) with A; change ((hi - lo) / 8) with N;
                    apply (zero_chunk_of_facts V m asan_mem_facts A N HM); [lia | lia | lia | vm_compute; reflexivity | vm_compute; reflexivity]
                  end
                |]).
        apply Forall_nil.
  Qed.
  Lemma client_img_init : client_img m.
  Proof.
    unfold client_img. split; [| split; [| split]]; [| | | exact client_x_init];
    unfold AGOT_SUAR, ASUAR, AVTAB_IMPL, AVTAB_DOM, vtab_impl_cells, vtab_dom_cells; ho_cells V m HM.
  Qed.

  (* [comment removed for export] *)
  Ltac sh0 :=
    match goal with |- m (wa ?A) = _ =>
      let a := eval vm_compute in A in change A with a; replace a with (a + 0) by lia;
      first [ apply (mzero_cover V m asan_mem_facts a 1 HM); [vm_compute; reflexivity | lia]
            | apply (zchunk_pointwise m a 1); [apply rw_C1_CB; ho_cells V m HM | lia | lia] ] end.
  Lemma client_sh_init : client_sh m.
  Proof.
    intros X HX. unfold client_sh_addrs in HX. cbn [In] in HX.
    repeat (destruct HX as [<-|HX]; [sh0|]). destruct HX.
  Qed.

  Lemma harness_invA_init : harness_invA m.
  Proof. split; [exact client_img_init | exact client_sh_init]. Qed.

  Lemma client_static0_init : forall (s : APS) (LB : list ablock), aps_cl s = None -> client_static s LB m.
  Proof.
    intros s LB HN. split; [exact HN|]. left. unfold client_static0, AACTIVE, AACTIVE_GUARD, AFALLBACK, AFALLBACK_GUARD, guard0, w0.
    repeat match goal with |- rw_cells _ _ _ _ /\ _ => split; [ho_cells V m HM|] end. ho_cells V m HM.
  Qed.

  Lemma harness_inv0_init : harness_inv0 m.
  Proof. split; [exact harness_invA_init | exact client_static0_init]. Qed.
End Handoff.
End CANSEC1.
