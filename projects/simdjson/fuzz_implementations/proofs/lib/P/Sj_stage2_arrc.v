(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.simdjson.fuzz_implementations.lib.Lib Require Import Tac Arr Bytes StoreFast.
From OSSVerify.Proofs.simdjson.fuzz_implementations.lib.Sj Require Import SjS1Out SjStage2 SjLeaves.
From OSSVerify.Proofs.simdjson.fuzz_implementations.lib.P Require Import Sj_stage2_defs.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac lia ::= s2lia.
Local Ltac tlia ::= s2tlia.

Section ArrCont.
  Variable E : s2env.
  Hypothesis OK : env_ok E.
  Notation INV := (Inv (e_bs E) (e_idxs E)).

  Lemma seg_arr_cont : forall (Q : machine_state -> Prop) (s : st)
      xra xt0 xt1 xt2 xs1 xa0 xa1 xa2 xa3 xa4 xa7 xs2 xs3 xs5 xs6 xs7 xs9 xs10 xt3 xt4 xt5 xt6 (F : bvmap 5 word) (fc : bv 32) (m1 : mem),
    INV ArrCont s -> MEMJ E (scopes s) fc m1 ->
    exit_k E Q ->
    (e_tok E (k s) = c_comma -> lab_k E Q 0x4ac1c (mkst (k s + 1) (depth s) (W s) (sb s) (scopes s))) ->
    (e_tok E (k s) = c_rbrack -> endc_k E Q 91 (mkst (k s + 1) (depth s) (W s) (sb s) (scopes s))) ->
    evt psegs Q (S2ML E 0x4abe0 xra xt0 xt1 xt2 xs1 xa0 xa1 xa2 xa3 xa4 xa7 xs2 xs3 xs5 xs6 xs7 xs9 xs10 xt3 xt4 xt5 xt6
                      (depth s) (k s) (W s) (sb s) F fc m1).
  Proof using OK.
    intros Q s xra xt0 xt1 xt2 xs1 xa0 xa1 xa2 xa3 xa4 xa7 xs2 xs3 xs5 xs6 xs7 xs9 xs10 xt3 xt4 xt5 xt6 F fc m1 HI HM KX KV KE.
    pose proof (inv_k _ _ _ _ HI) as HK.
    pose proof (off_bound E OK (k s) HK) as HO. pose proof (tok_range E OK (k s)) as HT.
    pose proof (n_bound E OK) as HN. s2_env OK.
    s2_open_memj HM.
    pose proof (idx_read E OK m1 (k s) IDXA ltac:(lia)) as RD1.
    pose proof (tok_read E OK m1 (k s) BUFRO HK) as RD2.
    zstep. s2norm. zstep. zstep. s2norm. zstep. zstep. zstep.
    if_cases K; zify_cond K.
    -
      zstep. zstep.
      replace (e_IDX E + 4 * k s + 4)%Z with (e_IDX E + 4 * (k s + 1))%Z by lia.
      eapply (KE K).
      cbn [scopes]. s2_close_memj0.
    -
      zstep. zstep.
      if_cases K2; zify_cond K2.
      +
        zstep. zstep. s2_err_exit KX.
        eapply (MEMX_of_MEMI E (e_nxt0 E)); [s2_close_mem0 | reflexivity ..].
      +
        pose proof (inv_depth_range _ _ _ _ HI) as HD.
        zstep. zstep. zstep. zstep. s2norm.
        destruct (nth_error_ex ocs (Z.to_nat (2 * depth s + 1)) ltac:(lia)) as [cnt Hcnt].
        pose proof (u32arr_read psegs m1 (e_OC E) ocs (2 * depth s + 1) cnt (wa (e_OC E + 8 * depth s + 4)) OCA Hcnt ltac:(lia)
                      ltac:(unfold wa; f_equal; lia)) as RD3.
        pose proof (u32arr_store_ok psegs m1 (e_OC E) ocs (2 * depth s + 1) (wa (e_OC E + 8 * depth s + 4)) OCA ltac:(lia)
                      ltac:(unfold wa; f_equal; lia)) as SOK.
        zstep. zstep. zstep.
        pose proof (u32arr_write psegs m1 (e_OC E) ocs (2 * depth s + 1) (Z_to_bv 64 (bv_unsigned (sx32 cnt) + 1)) OCA ltac:(lia)) as OCA'.
        replace (e_OC E + 4 * (2 * depth s + 1))%Z with (e_OC E + 8 * depth s + 4)%Z in OCA' by lia.
        store_done.
        replace (e_IDX E + 4 * k s + 4)%Z with (e_IDX E + 4 * (k s + 1))%Z by lia.
        eapply (KV K2). cbn [scopes].
        s2_close_memj; [rewrite upd_length; exact OCL | | exact IAL | exact IAR].
        apply oc_rel_upd_other; [exact OCR|]. intros jj Hjj. lia.
  Qed.
End ArrCont.
