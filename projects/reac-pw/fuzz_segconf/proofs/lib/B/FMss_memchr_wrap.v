(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/A/PSstrlen.v, with its module paths changed; 142 of its 194 lines of code are new or changed and 691 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-10: copied from plugin-hostd/fuzz_reply (a working branch 86b50358d34) to libreac/fuzz_boxreg: module paths changed, no other change. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_boxreg/lib/A/RT_mem_bz.v, with its module paths and module names changed; 204 of its 281 lines of code are new or changed and 117 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_segconf/lib/B/Prog/asan_memcpy.v, with its module paths and module names changed; 46 of its 82 lines of code are new or changed and 245 lines of the source are left out. *)
(* B twin (fm.asan-ubsan, pin ca61e5c9eabc0050) of lib/A/FMss_memchr_wrap.v at cold/port-fm-int 5d8d8a15571, relocated A->B by asan-kit elfmap.py + remap.py over the unstripped twins; every image numeral re-derived by symbol / section (fmb-b4 reloc report). *)
(* lib/A/Prog/memchr_wrap.v (RtStr's port, unchanged from cold/c-asan-rt-fmio-n affce6489c8), re-run against the
   local-shadow statement FMss_memchr_wrap_c.v: the range check comes from chk_ok_of_loc (FMss_shv.v) and the post's
   shadow fact from shvis_kept; every other line is the original's. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Lib Require Import PropExec MState Mem Exec Frame Step Cells Arr Bytes.
From OSSVerify.Proofs.reac_pw.fuzz_segconf Require Import lib.MemNorm.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import Img0 AsanRT AsanRTFacts BzBridge FMss_shv.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Spec Require Import StrFun.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import memchr_wrap_c wrap_kit.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import FMss_memchr_wrap_c.
Require OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog.asan_region_is_poisoned.
Require OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Bz.A.I_memchrw.
Require OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Bz.A.I_tramp.
Require OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Bz.A.R_m2s.
Require OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Bz.A.R_isPoisoned.
Import ListNotations.
Open Scope Z_scope.

Module ARP := OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog.asan_region_is_poisoned.
Module BzT := OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Bz.A.I_tramp.
Module BzR := OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Bz.A.R_m2s.
Module BzP := OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Bz.A.R_isPoisoned.

(* The check length of the moved walk is the statement's. *)
Lemma memchr_len_n : forall s c n buf, BzMC.memchr_len s c n buf = memchr_n s c n buf.
Proof. reflexivity. Qed.

(* The memchr wrapper at 0x4134c: a jump to the interceptor at 0x43bd8 (moved walk imemchr_spec), which calls the plain
   routine through REAL_MEMCHR and checks [s, s + memchr_n) against the shadow. *)

Theorem memchr_wrap_holds_L : memchr_wrap_contract_L.
Proof.
  unfold memchr_wrap_contract_L.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m buf lo.
  cbv zeta. intros BUF OK HMI HN AD EA A7 SEP HST HK HLO HSP HC HSR HRM.
  unfold MEMCHR_WRAP_K in *.
  pose proof (ro_agree_of_mem_inv m HMI) as RO.
  pose proof AD as (S0 & N0 & SE & _).
  pose proof (bv_unsigned_in_range 64 a1) as R1. pose proof (bv_unsigned_in_range 64 a2) as R2.
  unfold bv_modulus in R1, R2. cbn in R1, R2.
  pose proof (memchr_len_n (bv_unsigned a0) (bv_unsigned a1 mod 256) (bv_unsigned a2) buf) as ELN.
  assert (SE' : bv_unsigned a0 + BzMC.memchr_len (bv_unsigned a0) (bv_unsigned a1 mod 256) (bv_unsigned a2) buf <= 2^47)
    by (rewrite ELN; unfold APPMEM_END in SE; lia).
  destruct (cut47_len (bv_unsigned a0) buf ltac:(unfold APPMEM_END in SE; lia)) as (LC & LC2).
  destruct (memchr_cut (bv_unsigned a0) (bv_unsigned a1 mod 256) (bv_unsigned a2) buf S0 ltac:(lia) SE' OK) as (OKc & ER).
  apply (evt_mono rsegs (fun st => exists st0,
            BzMC.imemchr_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc
              (BzSF.memchr_res (bv_unsigned a0) (bv_unsigned a1 mod 256) (bv_unsigned a2) (cut47 (bv_unsigned a0) buf)) lo
              (normalize_cj rsegs m) st0
            /\ ms_rel_cj rsegs st st0 /\ cj_same rsegs m (ms_mem st))).
  - apply (bz_run _ _ F _ fc m HMI).
    apply BzT.tramp_memchr.
    apply (BzMC.imemchr_spec BzP.rip_proof mch_proof ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8
             s9 s10 s11 t3 t4 t5 t6 F fc (normalize_cj rsegs m) (bv_unsigned a0) (bv_unsigned a1) (bv_unsigned a2)
             (cut47 (bv_unsigned a0) buf) lo).
    + symmetry. apply Z_to_bv_bv_unsigned.
    + symmetry. apply Z_to_bv_bv_unsigned.
    + symmetry. apply Z_to_bv_bv_unsigned.
    + exact (stk_normalize m lo (bv_unsigned sp) HMI HST ltac:(unfold TASK_SIZE, APPMEM_END in *; lia)).
    + lia.
    + unfold BzR.kHighShadowEnd, HIGHMEM_BEG in *. lia.
    + unfold APPMEM_END in *. lia.
    + unfold APPMEM_END in *. lia.
    + lia.
    + lia.
    + unfold BzMC.memchr_len. rewrite ER. exact SE'.
    + assert (HL : bv_unsigned a0 + Z.of_nat (length (cut47 (bv_unsigned a0) buf)) <= TASK_SIZE)
        by (unfold TASK_SIZE; lia).
      exact (bytes_normalize_low m _ _ RO HL (cut47_bytes m _ _ BUF)).
    + exact OKc.
    + lia.
    + unfold BzMC.memchr_len. rewrite ER.
      exact (chk_ok_of_loc m (bv_unsigned a0) _ HMI HSR AD EA A7 HN).
    + exact (ARP.m2s_cells_normalize m HMI HC).
    + exact (icells_mc_norm m HMI HC HRM).
    + exact (bz_mem_inv_normalize m).
  - intros st (st0 & HQ & REL & SAME).
    destruct HQ as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m0' &
                    E0 & MU & WM & MI & ST).
    rewrite ER in E0. subst st0.
    destruct REL as (E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8).
    destruct (stack_W_ok (bv_unsigned sp - 2208) (bv_unsigned sp) ltac:(lia) ltac:(lia) ltac:(lia)) as [AW DJ].
    destruct (wrap_post_L [(bv_unsigned sp - 2208, bv_unsigned sp)] m (ms_mem st) m0' lo (bv_unsigned sp)
                HMI HC E8 SAME MU WM ST AW DJ)
      as (MU' & WM' & MI' & ST' & HC' & MK').
    exists t0', t1', t2', a1', a2', a3', a4', a5', a6', a7', t3', t4', t5', t6', (ms_mem st).
    split; [|split; [exact MU'|split; [exact WM'|split; [exact MI'|split; [exact ST'|split; [exact HC'|split; [exact (shvis_kept _ _ _ _ HSR MK' (addressable_app _ _ _ AD))|]]]]]]].
    + destruct st. cbn in E1, E2, E3, E4, E5, E6, E7 |- *. subst. reflexivity.
    + apply (bytes_at_transport rsegs [(bv_unsigned sp - 2208, bv_unsigned sp)] m (ms_mem st)); [exact BUF | exact MU' |].
      cbn [disjoint_from]. split; [lia | exact I].
Qed.
