(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (the main entry's recorded facts read as the main entry keeps them: APKN, imported from MainEntry; 10 recorded proofs replaced by written proofs (page_base_of_val, vis_rng_gen, allow_in_app and 7 more); ported by content from zstd_frame_info's file of the same role, with this binary's addresses and names). *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Lib Require Import PropExec MState Mem Cells Step Frame Arr InitMem.
From OSSVerify.Proofs.zstd.huf_decompress.lib.LibA Require Import ExecF Shadow.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Spec Require Import STree AsanCtrl AsanEmbed AsanHandoff.
From OSSVerify.Proofs.zstd.huf_decompress.lib.AS Require Import MainExport MainFactsAsan MainEntry.
From OSSVerify.Proofs.zstd.huf_decompress.lib.AsanW Require Import AImg ABase ABytes ALayout ARep AHeapP ARepInit_kit ARepInit_A.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Common Require Import RunDraw.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Ltac lit_divs := repeat match goal with |- context [?a / ?b] =>
  let v := eval vm_compute in (a / b) in lazymatch v with Zpos _ => change (a / b) with v | Z0 => change (a / b) with v end end.

Section CANSEC1. Context {rc : runConstT}.
Section E.
  Variables (lz : list (word * word)) (AL : word -> Prop) (V : nat -> Z) (w : bool) (U : list (list Z)).
  Hypothesis A0I : forall p : word, bv_unsigned p mod 4096 = 0 -> aallowed (allow_of 2147450880 V asan_vis) p -> AL p.
  Hypothesis HP : Forall (pfact_ok V) APKN.
  Hypothesis HU : (length U <= Z.to_nat AUMAX)%nat.
  Hypothesis HAT : 32768 * V 0%nat + 4096 * V 10%nat + 16 * V 6%nat - 8388608 = ATOP.   (* [comment removed for export] *)
  Let L := mkALayout (LV V) w U.
  Let RNG := fp_ok lz AL.
  (* [comment removed for export] *)
  Hypothesis ASH0 : forall (p : word) (c k : Z), bv_unsigned p mod 4096 = 0 -> 1 <= c < 32 ->
    (bv_unsigned p = shad (al_space_beg L) + 536870912 * c - 4096
     \/ (0 <= k <= 14336 /\ bv_unsigned p = shad (al_space_beg L) + 536870912 * c + 32768 * k)) -> AL p.

  Lemma page_base_of_val : forall z, 0 <= z < 2^64 -> bv_unsigned (page_base_of z) = z / 4096 * 4096.
  Proof.
    intros z Hz. unfold page_base_of, page_size. rewrite Z_to_bv_unsigned, bv_wrap_small; [reflexivity|].
    unfold bv_modulus. change (2 ^ Z.of_N 64) with (2^64).
(first [ (Z.div_mod_to_equations; lia) | (Z.to_euclidean_division_equations; nia) ]).
  Qed.

  Lemma vis_rng_gen : forall b n lo len,
    In (pagedown b, pageup (b + n)) (allow_of 2147450880 V asan_vis) ->
    b <= lo -> lo + len <= b + n -> 0 <= lo -> lo + len <= 2^64 ->
    rng RNG lo len.
  Proof.
    intros b n lo len HIN H1 H2 H3 H4.
apply rng_fp_ok_allowed; [lia| lia|].
    intros p (z & Hz & ->). pose proof (page_base_of_val z ltac:(lia)) as PV.
    apply A0I; [rewrite PV; (first [ (Z.div_mod_to_equations; lia) | (Z.to_euclidean_division_equations; nia) ])|].
    exists (pagedown b, pageup (b + n)). split; [exact HIN|]. cbn [fst snd]. rewrite PV. unfold pagedown, pageup.
    Z.div_mod_to_equations. nia.
  Qed.

  Lemma allow_in_app : forall k bn, nth_error asan_vis k = Some bn ->      (* [comment removed for export] *)
    In (pagedown (zv V (fst bn)), pageup (zv V (fst bn) + zv V (snd bn))) (allow_of 2147450880 V asan_vis)
    /\ In (pagedown (2147450880 + zv V (fst bn) / 8), pageup (2147450880 + (zv V (fst bn) + zv V (snd bn)) / 8)) (allow_of 2147450880 V asan_vis).
  Proof.
    intros k bn Hk. unfold allow_of. split; apply in_flat_map; exists bn; split; try (eapply nth_error_In; exact Hk); cbn; tauto.
  Qed.

  Lemma vis_rng : forall k bn lo len, nth_error asan_vis k = Some bn ->
    zv V (fst bn) <= lo -> lo + len <= zv V (fst bn) + zv V (snd bn) -> 0 <= lo -> lo + len <= 2^64 -> rng RNG lo len.
  Proof. intros k bn lo len Hk H1 H2 H3 H4. eapply vis_rng_gen; [exact (proj1 (allow_in_app k bn Hk))| lia| lia| lia| lia]. Qed.

  Lemma vis_rng_sh : forall k bn lo len, nth_error asan_vis k = Some bn ->
    2147450880 + zv V (fst bn) / 8 <= lo -> lo + len <= 2147450880 + (zv V (fst bn) + zv V (snd bn)) / 8 -> 0 <= lo -> lo + len <= 2^64 ->
    rng RNG lo len.
  Proof.
    intros k bn lo len Hk H1 H2 H3 H4.
eapply (vis_rng_gen (2147450880 + zv V (fst bn) / 8) ((zv V (fst bn) + zv V (snd bn)) / 8 - zv V (fst bn) / 8)); [| lia| lia| lia| lia].
    replace (2147450880 + zv V (fst bn) / 8 + ((zv V (fst bn) + zv V (snd bn)) / 8 - zv V (fst bn) / 8)) with (2147450880 + (zv V (fst bn) + zv V (snd bn)) / 8) by lia.
    exact (proj2 (allow_in_app k bn Hk)).
  Qed.

  Lemma rng_empty : forall b, 0 <= b <= 2^64 -> rng RNG b 0.
  Proof. intros b Hb.
apply rng_fp_ok; [lia| lia|]. intros z Hz. lia. Qed.

  (* [comment removed for export] *)
  Lemma obj_rng : forall k a n, nth_error asan_vis k = Some (ZMul (ZLit 4096) (ZV a), ZLit n) ->     (* [comment removed for export] *)
    4096 <= 4096 * V a -> 4096 * V a + n <= ATOP -> rng RNG (4096 * V a) n.
  Proof. intros k a n Hk H1 H2. atop_facts.
eapply (vis_rng k); [exact Hk| cbn; lia| cbn; lia| lia| lia]. Qed.

  (* [comment removed for export] *)
  Lemma shad_aregion : forall c, shad (aregion L c) = shad (al_space_beg L) + 536870912 * c
    /\ shad (al_space_beg L) mod 4096 = 0 /\ 4096 <= shad (al_space_beg L) /\ shad (al_space_beg L) + 17179869184 <= 2^64.
  Proof.
    intros c. pose proof (alayout_space _ (alayout_ok_init V w U HP HU HAT)) as (B1 & B2 & B3 & B4). unfold L in *.
    unfold aregion, K_REGION. rewrite !shad_div. unfold AsanEmbed.ASHOFF, K_ALIGN in *. change (2^32) with 4294967296.
    clear -B1 B3 B4.
(first [ (Z.div_mod_to_equations; lia) | (Z.to_euclidean_division_equations; nia) ]).
  Qed.

  Lemma lattice_rng : forall c, 1 <= c < K_NUM_CLASSES ->
       rng RNG (shad (aregion L c) - 4096) 8192
    /\ rng RNG (shad (aregion L c) - 4096) 4096
    /\ (forall k, 0 <= k <= 14336 -> rng RNG (shad (aregion L c) + 32768 * k) 4096).
  Proof.
    intros c Hc. unfold K_NUM_CLASSES in Hc. pose proof (shad_aregion c) as (E & AL8 & LO & HI). rewrite E.
    assert (P1 : forall k, 0 <= k <= 14336 -> rng RNG (shad (al_space_beg L) + 536870912 * c + 32768 * k) 4096).
    { intros k Hk.
apply rng_fp_ok_allowed; [clear -LO Hc Hk; lia| clear -HI Hc Hk; lia|].
      intros p (z & Hz & ->). pose proof (page_base_of_val z ltac:(clear -LO HI Hc Hk Hz; lia)) as PV.
      apply (ASH0 _ c k); [rewrite PV; clear; (first [ (Z.div_mod_to_equations; lia) | (Z.to_euclidean_division_equations; nia) ])| exact Hc|]. right. split; [exact Hk|]. rewrite PV. clear -AL8 Hz. (first [ (Z.div_mod_to_equations; lia) | (Z.to_euclidean_division_equations; nia) ]). }
    assert (P0 : rng RNG (shad (al_space_beg L) + 536870912 * c - 4096) 4096).
    { apply rng_fp_ok_allowed; [clear -LO Hc; lia| clear -HI Hc; lia|].
      intros p (z & Hz & ->). pose proof (page_base_of_val z ltac:(clear -LO HI Hc Hz; lia)) as PV.
      apply (ASH0 _ c 0); [rewrite PV; clear; (first [ (Z.div_mod_to_equations; lia) | (Z.to_euclidean_division_equations; nia) ])| exact Hc|]. left. rewrite PV. clear -AL8 Hz. (first [ (Z.div_mod_to_equations; lia) | (Z.to_euclidean_division_equations; nia) ]). }
    split; [| split; [exact P0| exact P1]].
    (* [comment removed for export] *)
    apply rng_fp_ok_allowed; [clear -LO Hc; lia| clear -HI Hc; lia|].
    intros p (z & Hz & ->). pose proof (page_base_of_val z ltac:(clear -LO HI Hc Hz; lia)) as PV.
    apply (ASH0 _ c 0); [rewrite PV; clear; (first [ (Z.div_mod_to_equations; lia) | (Z.to_euclidean_division_equations; nia) ])| exact Hc|].
    destruct (Z_lt_le_dec z (shad (al_space_beg L) + 536870912 * c)) as [LT|GE].
    - left. rewrite PV. clear -AL8 Hz LT. (first [ (Z.div_mod_to_equations; lia) | (Z.to_euclidean_division_equations; nia) ]).
    - right. split; [clear; lia|]. rewrite PV. clear -AL8 Hz GE. (first [ (Z.div_mod_to_equations; lia) | (Z.to_euclidean_division_equations; nia) ]).
  Qed.

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
        cbn [fst snd zv nth_error asan_vis asan_vis_app app]; lia. }
    split; [eapply (obj_rng 3); [reflexivity| lia| atop_facts; lia]|].
    split.
    { rewrite shad_div. unfold shlen, AsanEmbed.ASHOFF. rewrite Z.shiftr_div_pow2 by lia. change (2^3) with 8.
      eapply (vis_rng_sh 3); [reflexivity| | | |]; cbn -[Z.div Z.mul]; (first [ (Z.div_mod_to_equations; lia) | (Z.to_euclidean_division_equations; nia) ]). }
    split; [eapply (obj_rng 4); [reflexivity| lia| atop_facts; lia]|].
    split.
    { intros c Hc. pose proof (lattice_rng c Hc) as [HUL _].   (* [comment removed for export] *)
      rewrite get_cls_ST0. cbn [c_mapped_user c_mapped_free_array aclass0]. change (shlen 0) with 0.
      unfold afreearr, aregion, K_REGION, K_FREEARR_OFF, K_NUM_CLASSES in *. change (2^32) with 4294967296.
      split; [| split; [exact HUL|]]; repeat split; apply rng_empty; rewrite ?shad_div; unfold AsanEmbed.ASHOFF; try ((first [ (Z.div_mod_to_equations; lia) | (Z.to_euclidean_division_equations; nia) ])); lia. }
    (* [comment removed for export] *)
    split.
    { cbn [a_nres ST0 ainit]. change (8 * 0) with 0. apply rng_empty. change (al_V L 239%nat) with (V 226%nat). atop_facts. lia. }
    split. { unfold RSEC, sec_chunks_of, achunks. cbn [a_live a_qloc a_qglob ST0 ainit app flat_map]. rewrite map_to_list_empty. constructor. }
    (* [comment removed for export] *)
    intros c Hc. pose proof (lattice_rng c Hc) as (_ & LP0 & LP1). split; [exact LP0| exact LP1].
  Qed.
End E.
End CANSEC1.
