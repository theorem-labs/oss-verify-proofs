(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import PropExec ShapeAlg MmapSim.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import MState Mem Cells Frame Step Arr Bytes.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yc Require Import SpinAlg Ledger Hull Restrict.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Ym Require Import Asanljo Asan12c Asanqj4.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yf Require Import ImgA.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require Import ARt_u2d.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AIface AState ADepotM LayoutPA AInv ALogic1 ALogic2 ALogic3 ALogic AMalmys.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AQWf.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AQPart AFreeRP.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIface OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AState OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ADepotM OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.LayoutPA OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AInv OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ALogic1 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ALogic2 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ALogic3 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ALogic OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AMalmys OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AQWf.AQOps OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AQPart OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AFreeRP.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Ceiling.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Dest4xs.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require AndN.   (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
(* [comment removed for export] *)
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_noeuclid ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_post_hook.
(* [comment removed for export] *)
Open Scope bv_scope.
Local Open Scope Z_scope.

Notation wz z := (Z_to_bv 64 z) (only parsing).

Section RQ.
Context {Clg : Ceiling}.

  Lemma u64_of_rw : forall (v : mem) a z, 0 <= z < 2^64 -> rw_cells rsegs v a [C8 (wz z)] -> u64_at rsegs v a z.
  Proof. intros v a z Hz [[_ B] _]. cbn [cells_bytes cbytes] in B. rewrite app_nil_r in B. exact B. Qed.

  (* [comment removed for export] *)
  Lemma region_return_of_cells : forall (v v' : mem) sb (R : region) c (out : list Z) (w80 w88 : word),
    1 <= c <= 30 ->
    let ria := region_info_addr sb c in let fa := free_array_beg sb c in let nf := Z.of_nat (length (rg_free R)) in
    region_repr_ LPA sb R v c ->
    0 <= nf + Z.of_nat (length out) < 2^64 -> 0 <= rg_mapped_fa R < 2^64 ->
    (forall a, ria + 32 <= a < ria + 80 -> v' (wz a) = v (wz a)) ->
    (forall a, ria + 96 <= a < ria + 128 -> v' (wz a) = v (wz a)) ->
    (forall a, fa <= a < fa + 4 * nf -> v' (wz a) = v (wz a)) ->
    (forall a, fa <= a < fa + rg_mapped_fa R -> v (wz a) <> None -> v' (wz a) <> None) ->
    (forall a, region_beg sb c <= a < region_beg sb c + rg_mapped_user R -> v (wz a) <> None -> v' (wz a) <> None) ->
    rw_cells rsegs v' (ria + 16) [C8 (wz (nf + Z.of_nat (length out)))] ->
    rw_cells rsegs v' (ria + 24) [C8 (wz (rg_mapped_fa R))] ->
    rw_cells rsegs v' (ria + 80) [C8 w80; C8 w88] ->
    u32arr rsegs v' (fa + 4 * nf) (map (fun k => Z_to_bv 64 (k * class_size c / kCompactPtrScale)) out) ->
    region_repr_ LPA sb (reg_return R out (rg_mapped_fa R)) v' c.
  Proof.
    intros v v' sb R c out w80 w88 Hc. cbv zeta. intros RR NFR MFR AG1 AG2 AG3 NNf NNu C16 C24 C80 ARR.
    unfold region_repr_ in RR |- *. cbv zeta in RR |- *.
    (first [ dand13 RR as Hnf Hfa Hal Ham Hmu Hmm Hex J64 Jna Jrt ENT MFA MUS | destruct RR as (Hnf & Hfa & Hal & Ham & Hmu & Hmm & Hex & J64 & Jna & Jrt & ENT & MFA & MUS) ]).
    rewrite reg_return_free, reg_return_mapped_fa, reg_return_allocated, reg_return_mapped_user.
    unfold off_ri_num_freed, off_ri_mapped_free_array, off_ri_allocated_user, off_ri_allocated_meta, off_ri_mapped_user, off_ri_mapped_meta,
           off_ri_exhausted, off_ri_n_allocated, off_ri_rtoi in *.
    OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.and_splits.
    - rewrite length_app, Nat2Z.inj_add. apply u64_of_rw; [exact NFR| exact C16].
    - apply u64_of_rw; [exact MFR| exact C24].
    - eapply u64_at_agree; [exact Hal|]. intros i Hi. apply AG1. lia.
    - eapply u64_at_agree; [exact Ham|]. intros i Hi. apply AG1. lia.
    - eapply u64_at_agree; [exact Hmu|]. intros i Hi. apply AG1. lia.
    - eapply u64_at_agree; [exact Hmm|]. intros i Hi. apply AG1. lia.
    - eapply u8_at_agree; [exact Hex|]. apply AG1. lia.
    - eapply junk_at_agree; [exact J64|]. intros i Hi. apply AG1. lia.
    - (* [comment removed for export] *)
      (first [ dex1 Jna as bs; destruct Jna as [L B] | dand3 Jna as bs L B | destruct Jna as (bs & L & B) ]). destruct C80 as [[_ B80] _]. cbn [cells_bytes cbytes] in B80. rewrite app_nil_r in B80. apply bytes_at_app in B80 as [B80 _].
      exists (firstn 8 bs ++ le8 w80). split; [rewrite length_app, firstn_length_le, length_le8 by lia; lia|].
      apply bytes_at_app. split.
      + pose proof (bytes_at_mid v _ bs 0 8 B ltac:(lia)) as X. rewrite Z.add_0_r, skipn_O in X.
        eapply bytes_at_agree_gen; [exact X|]. intros i Hi. rewrite firstn_length_le in Hi by lia. apply AG1. lia.
      + rewrite firstn_length_le by lia. replace (region_info_addr sb c + 72 + Z.of_nat 8) with (region_info_addr sb c + 80) by lia. exact B80.
    - (* [comment removed for export] *)
      (first [ dex1 Jrt as bs; destruct Jrt as [L B] | dand3 Jrt as bs L B | destruct Jrt as (bs & L & B) ]). destruct C80 as [[_ B80] _]. cbn [cells_bytes cbytes] in B80. rewrite app_nil_r in B80. apply bytes_at_app in B80 as [_ B88]. rewrite length_le8 in B88.
      exists (le8 w88 ++ skipn 8 bs). split; [rewrite length_app, length_le8, length_skipn; lia|].
      apply bytes_at_app. split.
      + replace (region_info_addr sb c + 88) with (region_info_addr sb c + 80 + Z.of_nat 8) by lia. exact B88.
      + rewrite length_le8. pose proof (bytes_at_mid v _ bs 8 32 B ltac:(lia)) as X. rewrite firstn_all2 in X by (rewrite length_skipn; lia).
        eapply bytes_at_agree_gen; [exact X|]. intros i Hi. rewrite length_skipn in Hi. apply AG2. lia.
    - intros i k Hk. destruct (Nat.lt_ge_cases i (length (rg_free R))) as [LT|GE].
      + rewrite nth_error_app1 in Hk by exact LT. eapply u32_at_agree; [exact (ENT i k Hk)|]. intros j Hj. apply AG3. lia.
      + rewrite nth_error_app2 in Hk by exact GE. destruct ARR as [BA _].
        pose proof (nth_error_Some_lt _ _ _ Hk) as IL.
        pose proof (bytes_at_mid v' _ _ (4 * (i - length (rg_free R))) 4 BA ltac:(rewrite u32s_length, length_map; lia)) as X.
        rewrite (u32s_nth _ (i - length (rg_free R))%nat (Z_to_bv 64 (k * class_size c / kCompactPtrScale))) in X by (rewrite nth_error_map, Hk; reflexivity).
        unfold u32_at. replace (free_array_beg sb c + 4 * Z.of_nat i) with (free_array_beg sb c + 4 * Z.of_nat (length (rg_free R)) + Z.of_nat (4 * (i - length (rg_free R)))) by lia.
        exact X.
    - intros i Hi. apply NNf; [lia|]. apply MFA. lia.
    - intros i Hi. apply NNu; [lia|]. apply MUS. lia.
  Qed.
End RQ.
