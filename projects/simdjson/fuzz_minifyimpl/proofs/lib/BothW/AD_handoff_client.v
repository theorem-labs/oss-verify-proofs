(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP Mem Cells Frame RunConst.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.AS Require Import MainExport MainFactsBoth MainEntryBoth.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Spec Require Import AsanProgDeps.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.LibA Require Import Shadow.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Common Require Import RunDraw.
(* [comment removed for export] *)
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.BothW Require Import BImg ABase AU_kit AU_iface AU_consts AHarnessU_iface RtCells AAtexit_iface F_module_dtor_pre
     AD_handoff_md AD_hokit AD_handoff_exit AD_handoff0 ADriver_iface.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section CANSEC1. Context {rc : runConstT} {XP : ExitParams}.
Section Handoff.
  Variables (V : nat -> Z) (m : word -> option byte).
  Hypothesis HM : Forall (mfact_ok bsegs V m) both_mem_facts.
  Ltac go := repeat match goal with |- _ /\ _ => split end; ho_cells V m HM.

  (* [comment removed for export] *)
  Definition mfill_covb (lo n cv : Z) (f : mfact) : bool :=
    match f with MFill a n' c' => match zlit_of a with Some a' => (a' <=? lo) && (lo + n <=? a' + n') && (c' =? cv) | None => false end | _ => false end.
  Lemma mfill_cover : forall (l : list mfact) lo n cv,
    Forall (mfact_ok bsegs V m) l -> existsb (mfill_covb lo n cv) l = true -> forall i, 0 <= i < n -> m (wa (lo + i)) = Some (Z_to_bv 8 cv).
  Proof.
    intros l lo n cv HF HE i Hi. apply existsb_exists in HE as (f & Hin & Hf).
    pose proof (proj1 (Forall_forall _ _) HF f Hin) as K.
    destruct f as [? ? ?|? ?|? ? ?|? ?|a k c'|? ?|? ?|? ?|? ?]; try discriminate; cbn [mfill_covb] in Hf.
    destruct (zlit_of a) as [a'|] eqn:E; try discriminate. apply (zlit_of_zv V) in E. cbn [mfact_ok] in K. rewrite E in K.
    apply andb_prop in Hf as [Hf H3]. apply andb_prop in Hf as [H1 H2]. apply Z.leb_le in H1. apply Z.leb_le in H2. apply Z.eqb_eq in H3. subst c'.
    replace (lo + i) with (a' + (lo + i - a')) by lia. apply K. lia.
  Qed.
  Lemma byte_of_c1' : forall s b, rw_cells bsegs m s [C1 b] -> AIMG_HI <= s -> m (wa s) = Some b.
  Proof.
    intros s b [[_ (A & B & H)] _] Hs. unfold AIMG_HI in Hs. cbn [cells_bytes cbytes app length] in B, H.
    specialize (H 0%nat ltac:(lia)). cbn in H. rewrite Z.add_0_r in H.
    rewrite <- (mrd_no_image bsegs m s (s + 1) s (no_image_asan s (s + 1) Hs)) by lia.
    rewrite H. cbn. reflexivity.
  Qed.
  Lemma client_x_init : client_x m.
  Proof.
    unfold client_x, AMSG_SH, AJT_SH, AJT, AREAL_STRLEN, ASTRLEN_FN. split; [| split; [| split]].
    - intros i Hi. unfold amsg_shb.
      destruct (Z.ltb_spec i 4).
      { apply (mfill_cover both_mem_facts 0x7fffc890 4 249 HM); [vm_compute; reflexivity| lia]. }
      destruct (Z.ltb_spec i 10).
      { replace (0x7fffc890 + i) with (0x7fffc894 + (i - 4)) by lia. apply (mzero_cover V m both_mem_facts 0x7fffc894 6 HM); [vm_compute; reflexivity| lia]. }
      destruct (Z.eqb_spec i 10).
      { subst i. assert (C7 : rw_cells bsegs m 0x7fffc89a [C1 (Z_to_bv 8 7)]) by (ho_cells V m HM).
        change (0x7fffc890 + 10) with 0x7fffc89a. apply (byte_of_c1' _ _ C7). unfold AIMG_HI. lia. }
      replace (0x7fffc890 + i) with (0x7fffc89b + (i - 11)) by lia. apply (mfill_cover both_mem_facts 0x7fffc89b 5 249 HM); [vm_compute; reflexivity| lia].
    - intros i Hi. apply (mzero_cover V m both_mem_facts 0x8002708c 96 HM); [vm_compute; reflexivity| lia].
    - unfold AJT_BYTES, ajt_meta. match goal with |- rw_cells _ _ _ [CB _ ?bs] => let v := eval vm_compute in bs in change bs with v end.
      apply (img_ok V m both_mem_facts _ _ HM); [cbn; repeat split; exact I| vm_compute; reflexivity].
    - ho_cells V m HM.   (* [comment removed for export] *)
  Qed.
  Lemma client_img_init : client_img m.
  Proof.
    unfold client_img, AGOT_SUAR, ASUAR, AVTAB_SRS, AVTAB_VU8, ASRS_FN, AVU8_FN, AVTAB_MIN, AMIN_FN, AGOT_ERRC, AERRC, AERRMSG.
    split; [ho_cells V m HM|]. split; [ho_cells V m HM|]. split; [ho_cells V m HM|]. split; [ho_cells V m HM|]. split; [ho_cells V m HM|].
    split; [change (0x16dd60 + 248) with 0x16de58; ho_cells V m HM| exact client_x_init].
  Qed.

  (* [comment removed for export] *)
  Ltac sh0 :=
    match goal with |- m (wa ?A) = _ =>
      let a := eval vm_compute in A in change A with a; replace a with (a + 0) by lia;
      first [ apply (mzero_cover V m both_mem_facts a 1 HM); [vm_compute; reflexivity | lia]
            | apply (zchunk_pointwise m a 1); [apply rw_C1_CB; ho_cells V m HM | lia | lia] ] end.
  Lemma client_sh_init : client_sh m.
  Proof.
    intros X HX. unfold client_sh_addrs in HX. cbn [In] in HX.
    repeat (destruct HX as [<-|HX]; [sh0|]). destruct HX.
  Qed.

  Lemma harness_invA_init : harness_invA m.
  Proof. split; [exact client_img_init | exact client_sh_init]. Qed.

  (* [comment removed for export] *)
  Lemma client_static0_init : client_static0 m.
  Proof.
    unfold client_static0.
    split. { unfold atexit_rt. split; [ho_cells V m HM|]. exists (Z_to_bv 8 1), (Z_to_bv 8 0), (Z_to_bv 8 0), (Z_to_bv 64 0). ho_cells V m HM. }
    split; [exact (atexit_main_init V m HM)|].
    unfold AVEC, AVEC_GUARD, AFALLBACK, guard0, w0.
    repeat match goal with |- rw_cells _ _ _ _ /\ _ => split; [ho_cells V m HM|] end.
    destruct (sh_chunk V m both_mem_facts (shad 0x6afb00, 8) HM ltac:(vm_compute; reflexivity)) as [j H].
    exact (proj2 H).
  Qed.

  Lemma harness_inv0_init : harness_inv0 m.
  Proof. split; [exact harness_invA_init | exact client_static0_init]. Qed.
End Handoff.
End CANSEC1.
