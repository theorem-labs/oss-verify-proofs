(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib Require Import PropExec MState Mem Cells Step Frame Arr InitMem.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.LibA Require Import ExecF Shadow.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Spec Require Import STree AsanCtrl AsanEmbed AsanHandoff.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.AS Require Import MainExport MainFactsAsan.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.AsanT Require Import BImg ABase ABytes ALayout ARep AHeapP ARepInit_kit ARepInit_A.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import RunDraw.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Ltac lit_divs := repeat match goal with |- context [?a / ?b] =>
  let v := eval vm_compute in (a / b) in lazymatch v with Zpos _ => change (a / b) with v | Z0 => change (a / b) with v end end.

Section CANSEC1. Context {rc : runConstT}.
Section E.
  Variables (lz : list (word * word)) (AL : word -> Prop) (V : nat -> Z) (w : bool) (U : list (list Z)).
  Hypothesis A0I : forall p : word, bv_unsigned p mod 4096 = 0 -> aallowed (allow_of 2147450880 V both_vis) p -> AL p.
  Hypothesis HP : Forall (pfact_ok V) both_pure_facts.
  Hypothesis HU : (length U <= Z.to_nat AUMAX)%nat.
  Hypothesis HAT : 32768 * V 0%nat + 4096 * V 10%nat + 16 * V 6%nat - 8388608 = ATOP.   (* [comment removed for export] *)
  Let L := mkALayout (LV V) w U.
  Let RNG := fp_ok lz AL.
  (* [comment removed for export] *)
  Hypothesis ASH0 : forall p : word, bv_unsigned p mod 4096 = 0 ->
    shad (al_space_beg L) <= bv_unsigned p < shad (al_space_beg L) + 17179869184 -> AL p.

  Lemma page_base_of_val : forall z, 0 <= z < 2^64 -> bv_unsigned (page_base_of z) = z / 4096 * 4096.
  Proof.
    intros z Hz. unfold page_base_of, page_size. rewrite Z_to_bv_unsigned, bv_wrap_small; [reflexivity|].
    unfold bv_modulus. change (2 ^ Z.of_N 64) with (2^64). Z.div_mod_to_equations. lia.
  Qed.

  Lemma vis_rng_gen : forall b n lo len,
    In (pagedown b, pageup (b + n)) (allow_of 2147450880 V both_vis) ->
    b <= lo -> lo + len <= b + n -> 0 <= lo -> lo + len <= 2^64 ->
    rng RNG lo len.
  Proof.
    intros b n lo len HIN H1 H2 H3 H4. apply rng_fp_ok_allowed; [lia| lia|].
    intros p (z & Hz & ->). pose proof (page_base_of_val z ltac:(lia)) as PV.
    apply A0I; [rewrite PV; Z.div_mod_to_equations; lia|].
    exists (pagedown b, pageup (b + n)). split; [exact HIN|]. cbn [fst snd]. rewrite PV. unfold pagedown, pageup.
    Z.div_mod_to_equations. nia.
  Qed.

  Lemma allow_in_app : forall k bn, nth_error both_vis k = Some bn ->      (* [comment removed for export] *)
    In (pagedown (zv V (fst bn)), pageup (zv V (fst bn) + zv V (snd bn))) (allow_of 2147450880 V both_vis)
    /\ In (pagedown (2147450880 + zv V (fst bn) / 8), pageup (2147450880 + (zv V (fst bn) + zv V (snd bn)) / 8)) (allow_of 2147450880 V both_vis).
  Proof.
    intros k bn Hk. unfold allow_of. split; apply in_flat_map; exists bn; split; try (eapply nth_error_In; exact Hk); cbn; tauto.
  Qed.

  Lemma vis_rng : forall k bn lo len, nth_error both_vis k = Some bn ->
    zv V (fst bn) <= lo -> lo + len <= zv V (fst bn) + zv V (snd bn) -> 0 <= lo -> lo + len <= 2^64 -> rng RNG lo len.
  Proof. intros k bn lo len Hk H1 H2 H3 H4. eapply vis_rng_gen; [exact (proj1 (allow_in_app k bn Hk))| lia| lia| lia| lia]. Qed.

  Lemma vis_rng_sh : forall k bn lo len, nth_error both_vis k = Some bn ->
    2147450880 + zv V (fst bn) / 8 <= lo -> lo + len <= 2147450880 + (zv V (fst bn) + zv V (snd bn)) / 8 -> 0 <= lo -> lo + len <= 2^64 ->
    rng RNG lo len.
  Proof.
    intros k bn lo len Hk H1 H2 H3 H4.
    eapply (vis_rng_gen (2147450880 + zv V (fst bn) / 8) ((zv V (fst bn) + zv V (snd bn)) / 8 - zv V (fst bn) / 8)); [| lia| lia| lia| lia].
    replace (2147450880 + zv V (fst bn) / 8 + ((zv V (fst bn) + zv V (snd bn)) / 8 - zv V (fst bn) / 8)) with (2147450880 + (zv V (fst bn) + zv V (snd bn)) / 8) by lia.
    exact (proj2 (allow_in_app k bn Hk)).
  Qed.

  Lemma rng_empty : forall b, 0 <= b <= 2^64 -> rng RNG b 0.
  Proof. intros b Hb. apply rng_fp_ok; [lia| lia|]. intros z Hz. lia. Qed.

  (* [comment removed for export] *)
  Lemma obj_rng : forall k a n, nth_error both_vis k = Some (ZMul (ZLit 4096) (ZV a), ZLit n) ->     (* [comment removed for export] *)
    4096 <= 4096 * V a -> 4096 * V a + n <= ATOP -> rng RNG (4096 * V a) n.
  Proof. intros k a n Hk H1 H2. atop_facts. eapply (vis_rng k); [exact Hk| cbn; lia| cbn; lia| lia| lia]. Qed.

  Theorem arng_init : arng L RNG (ST0 V).
  Proof.
    pose proof (alayout_ok_init V w U HP HU HAT) as ALO.
    pose proof (ao_t _ ALO) as (_ & T1 & T2 & _). pose proof (ao_ctx _ ALO) as (_ & C1 & C2 & _). pose proof (ao_nodes _ ALO) as (_ & N1 & N2 & _).
    pose proof (ao_store _ ALO) as (_ & S1 & S2 & _). pose proof (ao_fake _ ALO) as (_ & F1 & F2 & _). pose proof (ao_dtls _ ALO) as (_ & D1 & D2 & _).
    pose proof (alayout_space _ ALO) as (B1 & B2 & B3 & B4). pose proof (ao_ptr _ ALO) as (_ & P1 & P2 & _).
    revert T1 T2 C1 C2 N1 N2 S1 S2 F1 F2 D1 D2 B1 B2 B3 B4 P1 P2.
    unfold al_t, al_ctx, al_nodes, al_store, al_fake, al_dtls, al_ptr_array, K_SPACE_SIZE, K_SPACE_EXTRA. cbv [al_V LV Nat.eqb].   (* [comment removed for export] *)
    intros T1 T2 C1 C2 N1 N2 S1 S2 F1 F2 D1 D2 B1 B2 B3 B4 P1 P2.
    unfold L in *.
    assert (ESB : al_space_beg (mkALayout (LV V) w U) = 4096 * V 208%nat + -4096 * V 209%nat + 65536) by (rewrite LV_space_beg; lia).
    rewrite ?ESB in B1, B2, B3, B4.
    unfold arng, al_t, al_ctx, al_nodes, al_store, al_fake, al_dtls, al_ptr_array. cbn [al_V LV Nat.eqb]. rewrite ESB.
    split; [eapply (vis_rng 11); [reflexivity| cbn; lia| cbn; lia| lia| lia]|].
    split; [eapply (obj_rng 7); [reflexivity| lia| atop_facts; lia]|].
    split; [eapply (obj_rng 6); [reflexivity| lia| atop_facts; lia]|].
    split; [eapply (obj_rng 2); [reflexivity| lia| atop_facts; lia]|].
    split; [eapply (obj_rng 1); [reflexivity| lia| atop_facts; lia]|].
    split.
    { unfold K_SPACE_SIZE, K_SPACE_EXTRA. eapply (vis_rng 8); [reflexivity| | | lia| lia];
        cbn [fst snd zv nth_error both_vis both_vis_app app]; lia. }
    split; [eapply (obj_rng 3); [reflexivity| lia| atop_facts; lia]|].
    split.
    { rewrite shad_div. unfold shlen, AsanEmbed.ASHOFF. rewrite Z.shiftr_div_pow2 by lia. change (2^3) with 8.
      eapply (vis_rng_sh 3); [reflexivity| | | |]; cbn -[Z.div Z.mul]; Z.div_mod_to_equations; lia. }
    split; [eapply (obj_rng 4); [reflexivity| lia| atop_facts; lia]|].
    split.
    { intros c Hc. rewrite get_cls_ST0. cbn [c_mapped_user c_mapped_free_array aclass0]. change (shlen 0) with 0.
      unfold afreearr, aregion, K_REGION, K_FREEARR_OFF, K_NUM_CLASSES in *. change (2^32) with 4294967296.
      repeat split; apply rng_empty; rewrite ?shad_div; unfold AsanEmbed.ASHOFF; try (Z.div_mod_to_equations; lia); lia. }
    (* [comment removed for export] *)
    split.
    { cbn [a_nres ST0 ainit]. change (8 * 0) with 0. apply rng_empty. change (al_V L 239%nat) with (V 226%nat). atop_facts. lia. }
    split. { unfold RSEC, sec_chunks_of, achunks. cbn [a_live a_qloc a_qglob ST0 ainit app flat_map]. rewrite map_to_list_empty. constructor. }
    (* [comment removed for export] *)
    assert (SBA : shad (al_space_beg L) mod 4096 = 0 /\ 0 <= shad (al_space_beg L) /\ shad (al_space_beg L) + 17179869184 <= 2^64).
    { unfold L. rewrite shad_div, ESB. unfold AsanEmbed.ASHOFF in *. clear -B1 B2 B3. unfold K_ALIGN in B3. Z.div_mod_to_equations. lia. }
    unfold L in SBA.
    destruct SBA as (SBA & SB0 & SB1). rewrite <- ESB. replace (shlen K_SPACE_SIZE) with 17179869184 by reflexivity.
    apply rng_fp_ok_allowed; [exact SB0| exact SB1|].
    intros p (z & Hz & ->). pose proof (page_base_of_val z ltac:(lia)) as PV. apply ASH0; rewrite PV; [clear -Hz; Z.div_mod_to_equations; lia|].
    clear -Hz SBA. Z.div_mod_to_equations. lia.
  Qed.
End E.
End CANSEC1.
