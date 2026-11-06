(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.simdjson.fuzz_element.lib.Lib Require Import Tac Arr Bytes StoreFast.
From OSSVerify.Proofs.simdjson.fuzz_element.lib.Sj Require Import SjS1Out SjStage2 SjLeaves.
From OSSVerify.Proofs.simdjson.fuzz_element.lib.P Require Import Sj_stage2_defs.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac lia ::= s2lia.
Local Ltac tlia ::= s2tlia.

Section ArrBegin.
  Variable E : s2env.
  Hypothesis OK : env_ok E.
  Notation INV := (Inv (e_bs E) (e_idxs E)).

  Lemma seg_arr_begin : forall (Q : machine_state -> Prop) (s : st)
      xra xt0 xt1 xt2 xs1 xa0 xa1 xa2 xa3 xa4 xa7 xs2 xs3 xs5 xs6 xs7 xs8 xs9 xs10 xt3 xt4 xt5 xt6
      j0 j1 j2 j3 j4 j5 j6 j8 j9 (F : bvmap 5 word) (fc : bv 32) (m1 : mem),
    INV ArrBegin s ->
    MEMI E (e_nxt0 E) [CB 8 j0; CB 8 j1; CB 8 j2; CB 8 j3; CB 8 j4; CB 8 j5; CB 8 j6;
                       C8 (Z_to_bv 64 (e_TAPE E + 8 * W s)); CB 8 j8; CB 8 j9] (scopes s) fc m1 ->
    exit_k E Q ->
    ((depth s + 1 < MAXDEPTH)%Z -> lab_k E Q 0x476a8 (mkst (k s) (depth s + 1) (W s + 1) (sb s) ((true, W s) :: scopes s))) ->
    evt psegs Q (S2R E 0x42d74 xra xt0 xt1 xt2 (Z_to_bv 64 (e_THIS E)) xs1 xa0 xa1 xa2 xa3 xa4
                     (Z_to_bv 64 (depth s)) (Z_to_bv 64 (e_IDX E + 4 * k s)) xa7 xs2 xs3 (Z_to_bv 64 (e_BUF E)) xs5 xs6 xs7
                     xs8 xs9 xs10 (Z_to_bv 64 (e_SBUF E + sb s)) xt3 xt4 xt5 xt6 F fc m1).
  Proof using OK.
    intros Q s xra xt0 xt1 xt2 xs1 xa0 xa1 xa2 xa3 xa4 xa7 xs2 xs3 xs5 xs6 xs7 xs8 xs9 xs10 xt3 xt4 xt5 xt6
           j0 j1 j2 j3 j4 j5 j6 j8 j9 F fc m1 HI HM KX KV.
    pose proof (inv_k _ _ _ _ HI) as HK. pose proof (inv_W _ _ _ _ HI) as HW. pose proof (inv_depth _ _ _ _ HI) as [HD1 HD2].
    cbn [slackW] in HW. unfold MAXDEPTH in *.
    pose proof (n_bound E OK) as HN. pose proof (n_le_len _ _ (ok_s1 _ OK)) as HNL. s2_env OK.
    s2_open_mem HM.
    zstep. zstep. zstep. zstep. s2norm. zstep. zstep.
    if_cases K; zify_cond K.
    -
      zstep. zstep. s2_err_exit KX.
      eapply (MEMX_of_MEMI E (e_nxt0 E)); [s2_close_mem0 | reflexivity ..].
    - pose proof (u8arr_store_ok psegs m1 (e_IA E) ias (depth s + 1) (wa (e_IA E + (depth s + 1))) IAA ltac:(lia) eq_refl) as SOK1.
      zstep. zstep. zstep. zstep.
      change (le1 (Z_to_bv 64 1)) with [Z_to_bv 8 1].
      pose proof (u8arr_write psegs m1 (e_IA E) ias (depth s + 1) (Z_to_bv 8 1) IAA ltac:(lia)) as IAA'.
      store_done.
      s2_cur_mem ltac:(fun m =>
        pose proof (u32arr_store_ok psegs m (e_OC E) ocs (2 * (depth s + 1)) (wa (e_OC E + 8 * (depth s + 1))) OCA ltac:(lia)
                      ltac:(unfold wa; f_equal; lia)) as SOK2).
      zstep. zstep. zstep. zstep. s2norm. zstep. zstep. zstep. zstep. s2norm.
      zstep.
      s2_old_mem ltac:(fun m =>
        pose proof (u32arr_write psegs m (e_OC E) ocs (2 * (depth s + 1)) (Z_to_bv 64 (W s)) OCA ltac:(lia)) as OCA').
      replace (e_OC E + 4 * (2 * (depth s + 1)))%Z with (e_OC E + 8 * (depth s + 1))%Z in OCA' by lia.
      store_done.
      s2_cur_mem ltac:(fun m =>
        pose proof (u32arr_store_ok psegs m (e_OC E) _ (2 * (depth s + 1) + 1) (wa (e_OC E + 8 * (depth s + 1) + 4)) OCA' ltac:(rewrite upd_length; lia)
                      ltac:(unfold wa; f_equal; lia)) as SOK3).
      zstep.
      s2_old_mem ltac:(fun m =>
        pose proof (u32arr_write psegs m (e_OC E) _ (2 * (depth s + 1) + 1) (Z_to_bv 64 1) OCA' ltac:(rewrite upd_length; lia)) as OCA'').
      replace (e_OC E + 4 * (2 * (depth s + 1) + 1))%Z with (e_OC E + 8 * (depth s + 1) + 4)%Z in OCA'' by lia.
      store_done.
      zstep.
      replace (e_TAPE E + 8 * W s + 8)%Z with (e_TAPE E + 8 * (W s + 1))%Z by lia.
      eapply (KV K). cbn [scopes].
      eapply MEMJ_of_MEMI; [ s2_close_mem | reflexivity .. ].
      + rewrite !upd_length. exact OCL.
      + apply oc_rel_upd_other.
        * replace (Z.to_nat (2 * (depth s + 1))) with (2 * (length (scopes s) + 1))%nat by lia.
          apply oc_rel_push; [exact OCR | lia].
        * intros jj Hjj. lia.
      + rewrite upd_length. exact IAL.
      + replace (Z.to_nat (depth s + 1)) with (length (scopes s) + 1)%nat by lia.
        apply (ia_rel_push (scopes s) ias true (W s)); [exact IAR | lia].
  Qed.
End ArrBegin.
