(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

(* [comment removed for export] *)
From Stdlib Require ZArith.
From Stdlib Require List.
From Stdlib Require Lia.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Ceil.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require AImg.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RT_defs.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require CJ_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require ICPT_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require AShadow.
Module CJ_band.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Ceil.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.AImg OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_defs OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.CJ_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.ICPT_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.AShadow.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache.
Unset Nia Cache.
Unset Nra Cache.

Section CeilWrap.
Context {ACEIL : Ceil}.

Lemma ablk_sclr_sub : forall lo hi a n, ablk lo hi -> lo <= a -> a + n <= hi -> sclr a n.
Proof. intros lo hi a n H A B. unfold ablk, sclr in *. lia. Qed.

Lemma sclr_sub : forall a n a' n', sclr a n -> a <= a' -> a' + n' <= a + n -> sclr a' n'.
Proof. intros a n a' n' H A B. unfold sclr in *. lia. Qed.

(* [comment removed for export] *)
Lemma sclr_stack : forall a n, alloc_ceiling <= a -> sclr a n.
Proof. intros a n H. pose proof alloc_ceiling_range as R. right. unfold sclr, KHIGHMEM_BEG, AIMG_HI, KLOWSHADOW_BEG. lia. Qed.

(* [comment removed for export] *)
Lemma sclr_image : forall a n, a + n <= AIMG_HI -> sclr a n.
Proof. intros a n H. left. unfold AIMG_HI, KLOWSHADOW_BEG in *. lia. Qed.

Lemma art_block_sclr : forall (AI : art_iface) sp0 SPB LB LF TRS B m mo g A n a k,
  ART AI sp0 SPB LB LF TRS B m mo g -> In (A, n) LB -> A <= a -> a + k <= A + Z.max n 1 -> sclr a k.
Proof.
  intros AI sp0 SPB LB LF TRS B m mo g A n a k HL IN H1 H2.
  exact (ablk_sclr_sub _ _ _ _ (art_block_band AI _ _ _ _ _ _ _ _ _ _ _ HL IN) H1 H2).
Qed.

Lemma art_frame_sclr : forall (AI : art_iface) sp0 SPB LB LF TRS B m mo g Fr k0 a k,
  ART AI sp0 SPB LB LF TRS B m mo g -> In (Fr, k0) LF -> Fr <= a -> a + k <= Fr + fsz k0 -> sclr a k.
Proof.
  intros AI sp0 SPB LB LF TRS B m mo g Fr k0 a k HL IN H1 H2.
  exact (ablk_sclr_sub _ _ _ _ (art_frame_band AI _ _ _ _ _ _ _ _ _ _ _ HL IN) H1 H2).
Qed.

(* [comment removed for export] *)
Lemma SH_in_band : forall a, 0 <= a -> a + 8 <= 2^47 -> KLOWSHADOW_BEG < SH a < KHIGHMEM_BEG.
Proof.
  intros a H0 H1. unfold sclr, SH, SHADOW_OFFSET, KHIGHMEM_BEG, AIMG_HI, KLOWSHADOW_BEG.
  assert (0 <= a / 8) by (apply Z.div_pos; lia).
  assert (a / 8 <= (2^47 - 8) / 8) by (apply Z.div_le_mono; lia).
  change ((2^47 - 8) / 8) with 17592186044415 in *. lia.
Qed.

(* [comment removed for export] *)
Lemma SH_ceiling_bounds : 0x10006fef8000 <= SH alloc_ceiling /\ SH alloc_ceiling < 0x10007fff8000 /\ SH alloc_ceiling < alloc_ceiling.
Proof. pose proof alloc_ceiling_range as R. unfold SH, SHADOW_OFFSET. Z.div_mod_to_equations. lia. Qed.

(* [comment removed for export] *)
Lemma sclr_clear_band : forall a n x, sclr a n -> KLOWSHADOW_BEG <= x < KHIGHMEM_BEG -> ~ (a <= x < a + n).
Proof. intros a n x H B. unfold sclr in H. lia. Qed.

(* [comment removed for export] *)
Lemma mod8_of_256 : forall x, x mod 256 = 0 -> x mod 8 = 0.
Proof. intros x H. Z.div_mod_to_equations. lia. Qed.
Lemma mod8_of_128 : forall x, x mod 128 = 0 -> x mod 8 = 0.
Proof. intros x H. Z.div_mod_to_equations. lia. Qed.
Lemma mod8_of_16 : forall x, x mod 16 = 0 -> x mod 8 = 0.
Proof. intros x H. Z.div_mod_to_equations. lia. Qed.
Lemma mod8_of_fsz : forall x k, k = 1 \/ k = 2 -> x mod fsz k = 0 -> x mod 8 = 0.
Proof. intros x k [-> | ->] H; [change (fsz 1) with 128 in H; exact (mod8_of_128 _ H)| change (fsz 2) with 256 in H; exact (mod8_of_256 _ H)]. Qed.

(* [comment removed for export] *)
Lemma frame_sh_in_band : forall Fr k a, k = 1 \/ k = 2 -> Fr mod fsz k = 0 -> 0 <= Fr -> Fr + fsz k <= alloc_ceiling ->
  SH Fr <= a < SH Fr + fsz k / 8 -> KLOWSHADOW_BEG <= a < KHIGHMEM_BEG.
Proof.
  intros Fr k a Hk AL H0 H1 Ha. pose proof alloc_ceiling_range as R.
  assert (F8 : Fr mod 8 = 0) by (exact (mod8_of_fsz _ _ Hk AL)).
  assert (Hfs : 0 < fsz k <= 256) by (destruct Hk as [-> | ->]; [change (fsz 1) with 128| change (fsz 2) with 256]; lia).
  pose proof (SH_in_band Fr H0 ltac:(lia)) as (S1 & S2).
  pose proof (SH_mono (Fr + fsz k) (2^47) ltac:(lia)) as M1. rewrite (SH_aligned_add Fr (fsz k) F8) in M1.
  assert (SHC : SH (2^47) = KHIGHMEM_BEG) by reflexivity. rewrite SHC in M1. lia.
Qed.
Lemma stack_sh_in_band : forall sp0 a, astack_shadow sp0 a -> KLOWSHADOW_BEG <= a < KHIGHMEM_BEG.
Proof.
  intros sp0 a H. unfold astack_shadow in H. pose proof SH_ceiling_bounds as (S1 & S2 & S3).
  assert (SHC : SH (2^47) = KHIGHMEM_BEG) by reflexivity. rewrite SHC in H. unfold KLOWSHADOW_BEG, KHIGHMEM_BEG in *. lia.
Qed.
(* [comment removed for export] *)
Lemma band_addr_not_block : forall (AI : art_iface) sp0 SPB LB LF TRS B m mo g A n a,
  ART AI sp0 SPB LB LF TRS B m mo g -> In (A, n) LB -> KLOWSHADOW_BEG <= a < KHIGHMEM_BEG -> a < A \/ A + Z.max n 1 <= a.
Proof.
  intros AI sp0 SPB LB LF TRS B m mo g A n a HL IN Ha.
  pose proof (ablk_clear_band _ _ a (art_block_band AI _ _ _ _ _ _ _ _ _ _ _ HL IN) Ha). lia.
Qed.
Lemma band_addr_not_frame : forall (AI : art_iface) sp0 SPB LB LF TRS B m mo g Fr k a,
  ART AI sp0 SPB LB LF TRS B m mo g -> In (Fr, k) LF -> KLOWSHADOW_BEG <= a < KHIGHMEM_BEG -> a < Fr \/ Fr + fsz k <= a.
Proof.
  intros AI sp0 SPB LB LF TRS B m mo g Fr k a HL IN Ha.
  pose proof (ablk_clear_band _ _ a (art_frame_band AI _ _ _ _ _ _ _ _ _ _ _ HL IN) Ha). lia.
Qed.

End CeilWrap.

(* [comment removed for export] *)
Ltac ablk_lits H := unfold ablk, AIMG_HI, KLOWSHADOW_BEG, KHIGHMEM_BEG in H.
Ltac sclr_lits H := unfold sclr, KHIGHMEM_BEG, AIMG_HI, KLOWSHADOW_BEG in H.

(* [comment removed for export] *)
Ltac app_rng AI :=
  first
  [ right; unfold highmem_range, KHIGHMEM_BEG, KHIGHMEM_END; lia
  | match goal with
    | HL : ART AI _ _ ?LB _ _ _ _ _ _, IN : In (?A, ?n) ?LB |- _ =>
        eapply (art_block_app_range AI _ _ _ _ _ _ _ _ _ A n); [exact HL| exact IN| lia| lia| lia]
    | HL : ART AI _ _ ((?A, ?n) :: _) _ _ _ _ _ _ |- _ =>
        eapply (art_block_app_range AI _ _ _ _ _ _ _ _ _ A n); [exact HL| left; reflexivity| lia| lia| lia]
    | HL : ART AI _ _ _ ?LF _ _ _ _ _, IN : In (?Fr, ?k) ?LF |- _ =>
        eapply (art_frame_app_range AI _ _ _ _ _ _ _ _ _ Fr k); [exact HL| exact IN| lia| lia| try (change (fsz 1) with 128); try (change (fsz 2) with 256); lia]
    | HL : ART AI _ _ _ ((?Fr, ?k) :: _) _ _ _ _ _ |- _ =>
        eapply (art_frame_app_range AI _ _ _ _ _ _ _ _ _ Fr k); [exact HL| left; reflexivity| lia| lia| try (change (fsz 1) with 128); try (change (fsz 2) with 256); lia]
    end ].
Ltac mod8 := first [ assumption | apply mod8_of_256; assumption | apply mod8_of_128; assumption | apply mod8_of_16; assumption
                   | eapply mod8_of_fsz; eassumption ].

(* [comment removed for export] *)
Ltac sclr_tac :=
  lazymatch goal with |- sclr _ _ => idtac end;
  first
  [ apply sclr_stack; lia
  | match goal with
    | HL : ART ?AI _ _ ?LB _ _ _ _ _ _, IN : In (?A, ?n) ?LB |- _ =>
        eapply (art_block_sclr AI _ _ _ _ _ _ _ _ _ A n); [exact HL| exact IN| lia| lia]
    | HL : ART ?AI _ _ ((?A, ?n) :: _) _ _ _ _ _ _ |- _ =>
        eapply (art_block_sclr AI _ _ _ _ _ _ _ _ _ A n); [exact HL| left; reflexivity| lia| lia]
    | HL : ART ?AI _ _ _ ?LF _ _ _ _ _, IN : In (?Fr, ?k) ?LF |- _ =>
        eapply (art_frame_sclr AI _ _ _ _ _ _ _ _ _ Fr k); [exact HL| exact IN| lia| try (change (fsz 1) with 128); try (change (fsz 2) with 256); lia]
    | HL : ART ?AI _ _ _ ((?Fr, ?k) :: _) _ _ _ _ _ |- _ =>
        eapply (art_frame_sclr AI _ _ _ _ _ _ _ _ _ Fr k); [exact HL| left; reflexivity| lia| try (change (fsz 1) with 128); try (change (fsz 2) with 256); lia]
    end ].
End CJ_band.

(* [comment removed for export] *)
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Frame.
From Stdlib Require Permutation.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require CJ_tree.
Module CJ_band2.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Ceil OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Frame.
Import Stdlib.Sorting.Permutation.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.AImg OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_defs OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.CJ_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.ICPT_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.AShadow OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.CJ_tree CJ_band.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache.
Unset Nia Cache.
Unset Nra Cache.

Section CeilWrap.
Context {ACEIL : Ceil}.

(* [comment removed for export] *)
Lemma frame_sh_band : forall Fr k, k = 1 \/ k = 2 -> Fr mod fsz k = 0 -> 0 <= Fr -> Fr + fsz k <= alloc_ceiling ->
  KLOWSHADOW_BEG <= SH Fr /\ SH Fr + fsz k / 8 <= KHIGHMEM_BEG.
Proof.
  intros Fr k Hk AL H0 H1.
  assert (Hfs : 0 < fsz k / 8) by (destruct Hk as [-> | ->]; [change (fsz 1 / 8) with 16| change (fsz 2 / 8) with 32]; lia).
  pose proof (frame_sh_in_band Fr k (SH Fr) Hk AL H0 H1 ltac:(lia)) as B1.
  pose proof (frame_sh_in_band Fr k (SH Fr + fsz k / 8 - 1) Hk AL H0 H1 ltac:(lia)) as B2. lia.
Qed.

(* [comment removed for export] *)
Lemma frame1_sh_band : forall Fr, Fr mod 128 = 0 -> 0 <= Fr -> Fr + 128 <= alloc_ceiling ->
  0x7fff7000 <= Z.shiftr Fr 3 + 2147450880 /\ Z.shiftr Fr 3 + 2147450880 + 16 <= 0x10007fff8000.
Proof.
  intros Fr AL H0 H1. pose proof (frame_sh_band Fr 1 ltac:(left; reflexivity) AL H0 H1) as (B1 & B2).
  rewrite SH_shiftr. change (fsz 1 / 8) with 16 in B2. unfold KLOWSHADOW_BEG, KHIGHMEM_BEG in *. lia.
Qed.
Lemma frame2_sh_band : forall Fr, Fr mod 256 = 0 -> 0 <= Fr -> Fr + 256 <= alloc_ceiling ->
  0x7fff7000 <= Z.shiftr Fr 3 + 2147450880 /\ Z.shiftr Fr 3 + 2147450880 + 32 <= 0x10007fff8000.
Proof.
  intros Fr AL H0 H1. pose proof (frame_sh_band Fr 2 ltac:(right; reflexivity) AL H0 H1) as (B1 & B2).
  rewrite SH_shiftr. change (fsz 2 / 8) with 32 in B2. unfold KLOWSHADOW_BEG, KHIGHMEM_BEG in *. lia.
Qed.

End CeilWrap.

(* [comment removed for export] *)
Ltac sclr_tac2 :=
  first [ sclr_tac
        | match goal with
          | HL : ART ?AI _ _ ?LB _ _ _ _ _ _, HP : Permutation ((?A, ?n) :: _) ?LB |- sclr _ _ =>
              eapply (art_block_sclr AI _ _ _ _ _ _ _ _ _ A n); [exact HL| exact (perm_in_head _ _ _ HP)| lia| lia]
          | HL : ART ?AI _ _ (_ :: ?LB) _ _ _ _ _ _, IN : In (?A, ?n) ?LB |- sclr _ _ =>
              eapply (art_block_sclr AI _ _ _ _ _ _ _ _ _ A n); [exact HL| right; exact IN| lia| lia]
          end
        | unfold sclr, KHIGHMEM_BEG, KLOWSHADOW_BEG; lia ].
Ltac pbuf_dj_at P :=
  let PB1 := fresh "PB1" in let PB2 := fresh "PB2" in let PM := fresh "PM" in
  pose proof (SH_in_band P ltac:(lia) ltac:(lia)) as (PB1 & _);
  pose proof (SH_in_band (P + 55) ltac:(lia) ltac:(lia)) as (_ & PB2);
  pose proof (SH_mono P (P + 55) ltac:(lia)) as PM;
  unfold KLOWSHADOW_BEG, KHIGHMEM_BEG in PB1, PB2;
  cbn [disjoint_from fst snd];
  repeat lazymatch goal with
  | |- True => exact I
  | |- _ /\ _ => split
  | |- _ + _ <= ?u \/ ?v <= _ =>
      first [ let SC := fresh "SC" in assert (SC : sclr u (v - u)) by sclr_tac2;
              unfold sclr, KHIGHMEM_BEG, KLOWSHADOW_BEG in SC; lia
            | unfold SH, SHADOW_OFFSET in *; Z.div_mod_to_equations; lia ]
  end.
Ltac pbuf_dj := lazymatch goal with |- Frame.disjoint_from _ (SH ?P) _ => pbuf_dj_at P end.

(* [comment removed for export] *)
Ltac app_rng0 :=
  first
  [ right; unfold highmem_range, KHIGHMEM_BEG, KHIGHMEM_END; lia
  | match goal with
    | HL : ART ?AI _ _ ?LB _ _ _ _ _ _, IN : In (?A, ?n) ?LB |- _ =>
        eapply (art_block_app_range AI _ _ _ _ _ _ _ _ _ A n); [exact HL| exact IN| lia| lia| lia]
    | HL : ART ?AI _ _ ((?A, ?n) :: _) _ _ _ _ _ _ |- _ =>
        eapply (art_block_app_range AI _ _ _ _ _ _ _ _ _ A n); [exact HL| left; reflexivity| lia| lia| lia]
    | HL : ART ?AI _ _ ?LB _ _ _ _ _ _, HP : Permutation ((?A, ?n) :: _) ?LB |- _ =>
        eapply (art_block_app_range AI _ _ _ _ _ _ _ _ _ A n); [exact HL| exact (perm_in_head _ _ _ HP)| lia| lia| lia]
    | HL : ART ?AI _ _ (_ :: ?LB) _ _ _ _ _ _, IN : In (?A, ?n) ?LB |- _ =>
        eapply (art_block_app_range AI _ _ _ _ _ _ _ _ _ A n); [exact HL| right; exact IN| lia| lia| lia]
    | HL : ART ?AI _ _ _ ?LF _ _ _ _ _, IN : In (?Fr, ?k) ?LF |- _ =>
        eapply (art_frame_app_range AI _ _ _ _ _ _ _ _ _ Fr k); [exact HL| exact IN| lia| lia| try (change (fsz 1) with 128); try (change (fsz 2) with 256); lia]
    | HL : ART ?AI _ _ _ ((?Fr, ?k) :: _) _ _ _ _ _ |- _ =>
        eapply (art_frame_app_range AI _ _ _ _ _ _ _ _ _ Fr k); [exact HL| left; reflexivity| lia| lia| try (change (fsz 1) with 128); try (change (fsz 2) with 256); lia]
    end ].

(* [comment removed for export] *)
Ltac pose_blk_band HL IN :=
  let R := fresh "BR" in let SC := fresh "BSC" in
  lazymatch type of HL with ART ?AI _ _ _ _ _ _ _ _ _ =>
  lazymatch type of IN with In (?A, ?n) _ =>
    pose proof (art_block_range AI _ _ _ _ _ _ _ _ _ _ _ HL IN) as R;
    pose proof (art_block_sclr AI _ _ _ _ _ _ _ _ _ A n A (Z.max n 1) HL IN (Z.le_refl _) (Z.le_refl _)) as SC;
    unfold sclr, ablock_range, KHIGHMEM_BEG, KLOWSHADOW_BEG, AIMG_HI in R, SC end end.
Ltac pose_frm_band HL IN :=
  let SC := fresh "FSC" in
  lazymatch type of HL with ART ?AI _ _ _ _ _ _ _ _ _ =>
  lazymatch type of IN with In (?Fr, ?k) _ =>
    pose proof (art_frame_sclr AI _ _ _ _ _ _ _ _ _ Fr k Fr (fsz k) HL IN (Z.le_refl _) (Z.le_refl _)) as SC;
    try (change (fsz 1) with 128 in SC); try (change (fsz 2) with 256 in SC);
    unfold sclr, KHIGHMEM_BEG, KLOWSHADOW_BEG in SC end end.
End CJ_band2.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib Require Import ShapeAlg.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Import Tac Bytes.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require LiaOn.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.LiaOn.SepM.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require Import CJ_bandM AImg RT_defs CJ_iface AShadow.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require CJ_phex4.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.CJ_phex4.CJ_pbuf.
Import CJ_band.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require CJ_pstrA.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.CJ_pstrA.CJ_shfast.
Local Ltac sh_resolve_if ::= sh_resolve_if_fast.
Local Ltac sh_join v Cv rdk ::= sh_join_fast v Cv rdk.
Local Ltac sh_transport_via MU H ::= sh_transport_via_fast MU H.
(* [comment removed for export] *)
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require StoreCache.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.StoreCache.StoreFast.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Import StoreCache.
Local Ltac mem_after_store ::= mem_after_store_cached.
Local Ltac addr_eq_tac ::= addr_eq_tac_cached.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_cached segs m m' MU WM.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require RegFold.
Local Ltac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Step.simp_regs ::= OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.RegFold.simp_regs_raw.
(* [comment removed for export] *)
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require StepFast.
#[local] Ltac2 Set OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.StepFast.SF.sf_mode := 0.
(* [comment removed for export] *)
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require JunkAbs.
Local Ltac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Step.split_for_access H segs m A cs kn n ::=
  OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.JunkAbs.split_for_access_raw H segs m A cs kn n.
Section CeilWrap.
Context {ACEIL : Ceil}.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Definition skipws_entry : Z := 0x838f8.
Definition SKIPWS_STACK : Z := 16.

(* [comment removed for export] *)
Lemma alloc_ceiling_eq : alloc_ceiling = alloc_ceiling.
Proof. reflexivity. Qed.

Definition skipws_post (ra sp gp tp t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (P content length depth : Z) (bs : list byte) (r : Z) (lo : Z)
    (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists (t0 t1 a0 a1 a2 a3 a4 a5 a6 a7 : word) (m' : word -> option byte),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch [(P + 16, P + 24); (lo, bv_unsigned sp)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo (bv_unsigned sp)
    /\ pbuf_at m' P content length r depth
    /\ bytes_at asegs m' content bs.

Section Proofs.
  Variables (ra sp gp tp t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m0 : word -> option byte)
            (P content len off0 depth lo : Z) (bs : list byte).
  Hypothesis LEN : Z.of_nat (length bs) = len.
  Hypothesis PNZ : P <> 0.
  Hypothesis CNZ : 0 < content.
  Hypothesis CHI : content + len <= alloc_ceiling.
  Hypothesis PLO : AIMG_HI <= P.
  Hypothesis PHI : P + 56 <= alloc_ceiling.
  Hypothesis PAL : P mod 8 = 0.
  Hypothesis SEP : content + len <= P \/ P + 56 <= content.
  (* [comment removed for export] *)
  Hypothesis SB : shbase_cells m0.
  Hypothesis PSH : pbuf_sh m0 P.
  Hypothesis TSH : text_sh m0 content len.
  Hypothesis LOC : alloc_ceiling <= lo.
  Hypothesis LOR : lo + SKIPWS_STACK <= bv_unsigned sp.
  (* [comment removed for export] *)
  Hypothesis PBND : sclr P 56.

  Notation SP := (bv_unsigned sp).
  Definition W : list (Z * Z) := [(P + 16, P + 24); (lo, SP)].
  Notation POST r := (skipws_post ra sp gp tp t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
                        F fc P content len depth bs r lo m0).

  (* [comment removed for export] *)
  Definition fin (i : Z) : Z :=
    let k := i + Z.of_nat (ws_count (skipn (Z.to_nat i) bs)) in if k =? len then len - 1 else k.

  Lemma fin_off0 : 0 <= off0 < len -> skipws_off bs off0 = fin off0.
  Proof.
    intros H. unfold skipws_off, fin. rewrite LEN.
    destruct (Z.leb_spec 0 off0); [|lia]. destruct (Z.ltb_spec off0 len); [|lia]. reflexivity.
  Qed.

  Lemma fin_stop : forall i b, 0 <= i < len -> nth_error bs (Z.to_nat i) = Some b -> 32 < bv_unsigned b -> fin i = i.
  Proof.
    intros i b Hi Hn Hb. unfold fin.
    replace (ws_count (skipn (Z.to_nat i) bs)) with O.
    2:{ destruct (skipn (Z.to_nat i) bs) as [|c rest] eqn:E; [reflexivity|]. cbn.
        assert (Hc : nth_error (skipn (Z.to_nat i) bs) 0 = Some c) by (rewrite E; reflexivity).
        rewrite nth_error_skipn, Nat.add_0_r, Hn in Hc. inversion Hc; subst.
        destruct (Z.leb_spec (bv_unsigned c) 32); [lia| reflexivity]. }
    cbn [Z.of_nat]. rewrite Z.add_0_r. destruct (Z.eqb_spec i len); lia.
  Qed.

  Lemma fin_ws : forall i b, 0 <= i < len -> nth_error bs (Z.to_nat i) = Some b -> bv_unsigned b <= 32 ->
    fin i = (if i + 1 =? len then len - 1 else fin (i + 1)).
  Proof.
    intros i b Hi Hn Hb. unfold fin.
    destruct (skipn (Z.to_nat i) bs) as [|c rest] eqn:E.
    { exfalso. assert (Hc : nth_error (skipn (Z.to_nat i) bs) 0 = None) by (rewrite E; reflexivity).
      rewrite nth_error_skipn, Nat.add_0_r, Hn in Hc. discriminate. }
    assert (Hc : nth_error (skipn (Z.to_nat i) bs) 0 = Some c) by (rewrite E; reflexivity).
    rewrite nth_error_skipn, Nat.add_0_r, Hn in Hc. inversion Hc; subst c.
    assert (Er : rest = skipn (Z.to_nat (i + 1)) bs).
    { replace (Z.to_nat (i + 1)) with (S (Z.to_nat i)) by lia. rewrite <- skipn_skipn with (x := 1%nat) (y := Z.to_nat i).
      hnf. rewrite E. reflexivity. }
    cbn [ws_count]. destruct (Z.leb_spec (bv_unsigned b) 32); [|lia]. rewrite <- Er.
    destruct (Z.eqb_spec (i + 1) len) as [E1|NE1].
    - pose proof (ws_count_le rest) as HL.
      assert (length rest = 0)%nat. { rewrite Er, length_skipn. lia. }
      replace (ws_count rest) with O by lia.
      lazymatch goal with |- (if ?x =? ?y then _ else _) = _ => replace x with y by lia end.
      rewrite Z.eqb_refl. reflexivity.
    - rewrite Nat2Z.inj_succ. replace (i + Z.succ (Z.of_nat (ws_count rest))) with (i + 1 + Z.of_nat (ws_count rest)) by lia.
      reflexivity.
  Qed.

  (* [comment removed for export] *)
  Ltac lits :=
    pose proof (bv_unsigned_in_range 64 sp) as SPR; change (bv_modulus 64) with (2^64) in SPR;
    pose proof CHI as CHI'; pose proof PHI as PHI'; pose proof PLO as PLO'; pose proof LOC as LOC'; pose proof LOR as LOR';
    try rewrite alloc_ceiling_eq in CHI', PHI', LOC'; unfold sclr, KHIGHMEM_BEG, AIMG_HI, KLOWSHADOW_BEG in PLO'; unfold SKIPWS_STACK in LOR';
    pose proof PBND as PBND'; sclr_lits PBND'.

  (* [comment removed for export] *)
  Definition LST (pc : Z) (x5 x6 x11 : word) (i : Z) (mm : word -> option byte) : machine_state :=
    MS (mkR ra (Z_to_bv 64 (SP + -16)) gp tp x5 x6 t2 s0 s1 (Z_to_bv 64 (P + 16)) x11 (Z_to_bv 64 len) (Z_to_bv 64 2147450880)
            (Z_to_bv 64 (Z.shiftr (P + 16) 3 + 2147450880)) (Z_to_bv 64 content) (Z_to_bv 64 i) (Z_to_bv 64 32)
            s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
       F (Z_to_bv 64 pc) fc None mm (seg_rom asegs).

  (* [comment removed for export] *)
  Definition lmem (o : Z) (mm : word -> option byte) (j8 : list byte) : Prop :=
    rw_cells asegs mm P (pbuf_cells content len o depth) /\ bytes_at asegs mm content bs
    /\ rw_cells asegs mm (SP + -16) [CB 8 j8; C8 ra]
    /\ munch W m0 mm /\ wmono asegs m0 mm /\ mem_inv asegs mm /\ stk asegs mm lo (SP + -16).

  (* [comment removed for export] *)
  Lemma exit_tail : forall o mm j8 x5 x6 x10 x11 x12 x13 x14 x15 x16 x17,
    lmem o mm j8 ->
    evt asegs (POST o)
        (MS (mkR ra (Z_to_bv 64 (SP + -16)) gp tp x5 x6 t2 s0 s1 x10 x11 x12 x13 x14 x15 x16 x17
                 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 0x839cc) fc None mm (seg_rom asegs)).
  Proof.
    intros until x17. intros (PB & BY & FR & MU & WM & MI & ST). lits. bandM.
    zstep. zstep.
    release_frame FR ST (bv_unsigned sp).
    zstep. apply evt_done. unfold skipws_post.
    do 10 eexists. exists mm. split; [reflexivity|].
    split. { unfold W in MU. exact MU. }
    repeat (split; [assumption|]). exact BY.
  Qed.

  (* [comment removed for export] *)
  Lemma skipws_loop : forall (k : nat) (i r : Z) (x5 x6 x11 : word) (mm : word -> option byte) (j8 : list byte),
    Z.to_nat (len - i) = k -> 0 <= i < len -> r = fin i ->
    lmem i mm j8 ->
    evt asegs (POST r) (LST 0x83974 x5 x6 x11 i mm).
  Proof.
    induction k as [|k IH]; intros i r x5 x6 x11 mm j8 Hk Hi Hr LM; [lia|].
    pose proof LM as (PB & BY & FR & MU & WM & MI & ST). lits. bandM. sepM. unfold W in MU. unfold LST.
    unfold pbuf_cells, wz in PB.
    destruct (nth_error bs (Z.to_nat i)) as [b|] eqn:Hn. 2:{ apply nth_error_None in Hn. lia. }
    pose proof (u8ro_read asegs mm content bs i b _ BY Hn ltac:(lia) eq_refl) as RD.
    pose proof (bv_unsigned_in_range 8 b) as Rb. change (bv_modulus 8) with 256 in Rb.
    zstep. zstep. zstep.                                      (* [comment removed for export] *)
    pose proof (TSH (content + i) ltac:(lia)) as CK. asan_chk CK.   (* [comment removed for export] *)
    zstep.                                                    (* [comment removed for export] *)
    zstep. if_cases K; zify_cond K.
    - (* [comment removed for export] *)
      rewrite (fin_stop i b) in Hr by first [lia | exact Hn]. subst r.
      zstep. if_cases K2; zify_cond K2; [| exfalso; lia].
      eapply exit_tail. split; [unfold pbuf_cells, wz; exact PB|]. split; [exact BY|]. split; [exact FR|].
      split; [exact MU|]. split; [exact WM|]. split; [exact MI| exact ST].
    - (* [comment removed for export] *)
      rewrite (fin_ws i b) in Hr by first [lia | exact Hn].
      pose proof (sh_zero_shb m0 P (P + 56) (P + 16) PSH ltac:(lia)) as Z16. asan_chk Z16. clear Z16.
      zstep. zstep.                                           (* [comment removed for export] *)
      zstep. if_cases K2; zify_cond K2.
      + (* [comment removed for export] *)
        destruct (Z.eqb_spec (i + 1) len); [exfalso; lia|].
        apply (IH (i + 1) r _ _ _ _ j8); try lia.
        split; [unfold pbuf_cells, wz; assumption|]. split; [exact BY|]. split; [assumption|].
        split; [exact MU|]. split; [exact WM|]. split; [exact MI| exact ST].
      + (* [comment removed for export] *)
        destruct (Z.eqb_spec (i + 1) len); [| exfalso; lia]. subst r.
        zstep.
        pose proof (sh_zero_shb m0 P (P + 56) (P + 16) PSH ltac:(lia)) as Z16. asan_chk Z16. clear Z16.
        zstep. zstep.
        replace (len + -1) with (len - 1) by lia.
        eapply exit_tail. split; [unfold pbuf_cells, wz|]. 2: split; [exact BY|]. 2: split; [eassumption|].
        2: split; [exact MU|]. 2: split; [exact WM|]. 2: split; [exact MI| exact ST].
        lazymatch goal with H : rw_cells asegs _ P _ |- _ => exact H end.
  Qed.

  Lemma skipws_body : forall (t0 t1 a1 a2 a3 a4 a5 a6 a7 : word),
    bytes_at asegs m0 content bs ->
    pbuf_at m0 P content len off0 depth ->
    0 <= off0 <= len ->
    mem_inv asegs m0 -> stk asegs m0 lo SP ->
    evt asegs (POST (skipws_off bs off0))
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 P) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 skipws_entry) fc None m0 (seg_rom asegs)).
  Proof.
    intros until a7. intros BY PB OFF MI ST. lits. bandM. sepM.
    pose proof (pbuf_at_bound _ _ _ _ _ _ PB) as PBB. unfold pbuf_at, pbuf_cells, wz in PB.
    pose proof (munch_refl W m0) as MU. pose proof (wmono_refl asegs m0) as WM. unfold W in MU.
    pose proof SB as SB0. shbase_split SB0.                   (* [comment removed for export] *)
    unfold skipws_entry.
    carve_frame 16%nat ST.
    zstep. zstep.                                             (* [comment removed for export] *)
    zstep. if_cases K0; zify_cond K0; [exfalso; lia|].        (* [comment removed for export] *)
    zstep. zstep. zstep. zstep.                               (* [comment removed for export] *)
    zstep. zstep.                                             (* [comment removed for export] *)
    pose proof (sh_zero_shb m0 P (P + 56) P PSH ltac:(lia)) as Z0. asan_chk Z0. clear Z0.   (* [comment removed for export] *)
    zstep.                                                    (* [comment removed for export] *)
    zstep. if_cases K1; zify_cond K1; [exfalso; lia|].
    zstep. zstep. zstep.                                      (* [comment removed for export] *)
    pose proof (sh_zero_shb m0 P (P + 56) (P + 16) PSH ltac:(lia)) as Z16. asan_chk Z16. clear Z16.
    zstep. zstep. zstep.                                      (* [comment removed for export] *)
    pose proof (sh_zero_shb m0 P (P + 56) (P + 8) PSH ltac:(lia)) as Z8. asan_chk Z8. clear Z8.
    zstep. zstep.                                             (* [comment removed for export] *)
    zstep. if_cases K2; zify_cond K2.
    - (* [comment removed for export] *)
      rewrite skipws_off_noop by lia.
      eapply exit_tail. split; [unfold pbuf_cells, wz; exact PB|]. split; [exact BY|]. split; [exact FR|].
      split; [exact MU|]. split; [exact WM|]. split; [exact MI| exact ST].
    - pose proof (sh_zero_shb m0 P (P + 56) (P + 16) PSH ltac:(lia)) as Z16. asan_chk Z16. clear Z16.
      zstep.                                                  (* [comment removed for export] *)
      zstep. if_cases K3; zify_cond K3; [exfalso; lia|].
      zstep.                                                  (* [comment removed for export] *)
      eapply skipws_loop with (i := off0) (k := Z.to_nat (len - off0)) (j8 := firstn 8 junk); try lia.
      + apply fin_off0. lia.
      + split; [unfold pbuf_cells, wz; exact PB|]. split; [exact BY|]. split; [exact FR|].
        split; [exact MU|]. split; [exact WM|]. split; [exact MI| exact ST].
  Qed.
End Proofs.

Lemma skipws_spec : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
    (P content len offset depth lo : Z) (bs : list byte),
  pbuf_at m P content len offset depth ->
  a0 = wz P -> P <> 0 -> 0 < content ->
  bytes_at asegs m content bs -> Z.of_nat (length bs) = len ->
  0 <= offset <= len ->
  content + len <= alloc_ceiling -> AIMG_HI <= P -> P + 56 <= alloc_ceiling -> P mod 8 = 0 ->
  (content + len <= P \/ P + 56 <= content) ->
  shbase_cells m -> pbuf_sh m P -> text_sh m content len ->
  mem_inv asegs m ->
  stk asegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo + SKIPWS_STACK <= bv_unsigned sp ->
  sclr P 56 ->                                  (* [comment removed for export] *)
  evt asegs (skipws_post ra sp gp tp t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
               F fc P content len depth bs (skipws_off bs offset) lo m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x838f8) fc None m (seg_rom asegs)).
Proof.
  intros until bs. intros PB A0 PNZ CNZ BY LEN OFF CHI PLO PHI PAL SEP SB PSH TSH MI ST LOC LOR PBND. unfold wz in A0. subst a0.
  eapply skipws_body; eauto.
Qed.


End CeilWrap.
