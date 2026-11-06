(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/A/PSbz_str.v, with its module paths and module names changed; 125 of its 195 lines of code are new or changed and 89 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-10: relocated from omx-clap-core/fuzz_manifest lib/A/FMgxa_bzcj.v (a working branch 3e35620c52e) to libreac/fuzz_boxreg.asan-ubsan: module paths changed; 0 address numerals relocated (port_addr_check 0767e70e074a predict mode, symbol + offset). *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_boxreg/lib/B/Rt/FMgxa_bzcj.v, with its module paths changed; 83 of its 219 lines of code are new or changed and 59 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_reply/lib/B/RT_gxa_calls.v, with its module paths and addresses changed; 13 of its 111 lines of code are new or changed and 121 lines of the source are left out. *)
(* Copied from proofs/omx-clap-core/fuzz_manifest/lib/A/RT_gxa_strnlen.v (cold/port-fm-rtprintf-param 0ddf65fd8cc); relocated to libreac/fuzz_disco.asan by g9/tool (reloc.py target disco-A): module paths changed; 3 address numerals moved (port_addr_check 0767e70e074a predict, fm.asan -> fuzz_disco.asan, symbol + offset; table g9/tool/tables/disco-A/RT_gxa_strnlen.table); GXA symbol keys kept (0x21920); names: record RT_IImgA -> A_img RecAsanVfA.N_img_asan_vf. *)
(* Modified by Theorem Labs, 2026-10: proofs/libreac/fuzz_disco/lib/A/RT_gxa_strnlen.v at 2d2ff01bb6f2 relocated to reac-pw/fuzz_rate's ASan image A: module paths changed; numerals by port_core 1e42da8952ec (ledger provenance/reloc/A-Snp.tsv). *)
(* GXA's interceptor call contract for strnlen (lib/CJ/RL/GXA/StrnlenCall.v:30 strnlen_stack_contract),
   discharged at the ASan instance A_img (RT_IImgA.v:102) on the pinned fuzz_manifest.asan.

   This file proves no new function.  It composes proofs that are already in the tree:
   - c-asan-rt's Bz interceptor walk of ___interceptor_strnlen 0x415f8 (lib/A/Bz/A/I_strnlen.v istrnlen_spec, relocated
     here from fuzz_state), which calls REAL(strnlen) = musl strnlen 0x92f68 (I_strnlenw.v:81 musl_strnlen_spec);
   - its two section hypotheses: rip_stmt (lib/A/Bz/A/R_isPoisoned.v rip_proof) and memchr_stmt
     (lib/A/FMmch.v mch_proof);
   - GXA's call-contract statement, which it takes as a Context in G_printf_core.v.
   What it adds is glue only:
   - the trampoline: GXA's call target `sym 0x21920` is __wrap_strnlen = __interceptor_trampoline_strnlen 0x412cc
     under A_img (RT_IImgA.v:69), and that is one instruction, `j 415f8 <___interceptor_strnlen>` (32c0006f);
   - the vocabulary: lib/A/FMgxa_bzcj.v's generic Bz <-> CJ bridge (bz_cj_evt, mem_inv_cj_bz / mem_inv_bz_cj,
     ms_cj_bz, mkR_cj_bz, seg_rom_cj_bz), shared with the memcpy and memset contracts.
   What a caller supplies: strn_ready (below) is exactly what istrnlen_spec asks beyond the contract's own
   premises; strn_ready_intro proves it from GXA's own ASan vocabulary (AsanFacts.v pf_rng / shadow_rw), the
   stack placement and ASan's runtime cells, the shadow half through FMgxa_bzcj.v's chk_ok_of_pf_rng.
   Numerals introduced here, each keyed on its fuzz_manifest.asan symbol + offset:
     0x412cc  __wrap_strnlen = __interceptor_trampoline_strnlen + 0  (the A_img row KV 0x21920 0x412cc)
     0x415f8  ___interceptor_strnlen + 0                             (the target of the j at 0x412cc; istrnlen_spec's entry pc) *)
(* Modified by Theorem Labs, 2026-10: relocated to omx-clap-core fuzz_manifest.asan; from origin/cold/port-reply-r4 5247aa4d0b9 proofs/plugin-hostd/fuzz_reply/lib/A/RT_gxa_calls.v, module path fuzz_reply -> fuzz_manifest, FRsl -> FMmch, renamed RT_gxa_calls.v -> RT_gxa_strnlen.v, its image-generic lemmas moved to lib/A/FMgxa_bzcj.v, and 2 fuzz_reply.asan address numerals re-imaged by symbol + offset: __interceptor_trampoline_strnlen 0x42190 -> 0x412cc, ___interceptor_strnlen 0x424c4 -> 0x415f8 (comments: musl memchr 0x963d0 -> 0x924a8, musl strnlen 0x96e48 -> 0x92f68). *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.A.Bz.Lib Require Import Tac ImageA SysStep.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.A.Bz.Spec Require Import StrFun.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.A.Bz.Lib Require Import StoreFast.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.A.Bz.P Require Import Str_tac Startup_glue.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.A.Bz.A Require Import Shadow R_small R_m2s R_thread I_consts I_qck X_atexit IcptSpec D_kit I_ikit I_musl I_memchrw I_strnlenw I_strnlen.
Require OSSVerify.Proofs.reac_pw.fuzz_rate.lib.A.Bz.Common.PropExec.
Require OSSVerify.Proofs.reac_pw.fuzz_rate.lib.A.Bz.Lib.MState.
Require OSSVerify.Proofs.reac_pw.fuzz_rate.lib.A.Bz.Lib.Exec.
Require OSSVerify.Proofs.reac_pw.fuzz_rate.lib.A.Bz.Lib.Mem.
Require OSSVerify.Proofs.reac_pw.fuzz_rate.lib.A.Bz.Lib.Frame.
Require OSSVerify.Proofs.reac_pw.fuzz_rate.lib.A.Bz.A.R_isPoisoned.
Require OSSVerify.Proofs.reac_pw.fuzz_rate.lib.A.FMmch.
Require OSSVerify.Proofs.reac_pw.fuzz_rate.lib.CJ.Lib.PropExec.
Require OSSVerify.Proofs.reac_pw.fuzz_rate.lib.CJ.Lib.MState.
Require OSSVerify.Proofs.reac_pw.fuzz_rate.lib.CJ.Lib.Exec.
Require OSSVerify.Proofs.reac_pw.fuzz_rate.lib.CJ.Lib.Mem.
Require OSSVerify.Proofs.reac_pw.fuzz_rate.lib.CJ.Lib.Frame.
Require OSSVerify.Proofs.reac_pw.fuzz_rate.lib.CJ.RL.Reloc.RStep.
Require OSSVerify.Proofs.reac_pw.fuzz_rate.lib.CJ.RL.GXA.StrnlenCall.
Require OSSVerify.Proofs.reac_pw.fuzz_rate.lib.CJ.RL.GXA.AsanFacts.
Require OSSVerify.Proofs.reac_pw.fuzz_rate.lib.CJ.RL.I.RecAsanVfA.
Require OSSVerify.Proofs.reac_pw.fuzz_rate.lib.A.RT_gxa_bridge_seam.
Import ListNotations.
Open Scope Z_scope.

Module BzP := OSSVerify.Proofs.reac_pw.fuzz_rate.lib.A.Bz.Common.PropExec.
Module BzS := OSSVerify.Proofs.reac_pw.fuzz_rate.lib.A.Bz.Lib.MState.
Module BzE := OSSVerify.Proofs.reac_pw.fuzz_rate.lib.A.Bz.Lib.Exec.
Module BzM := OSSVerify.Proofs.reac_pw.fuzz_rate.lib.A.Bz.Lib.Mem.
Module BzF := OSSVerify.Proofs.reac_pw.fuzz_rate.lib.A.Bz.Lib.Frame.
Module BzRIP := OSSVerify.Proofs.reac_pw.fuzz_rate.lib.A.Bz.A.R_isPoisoned.
Module FMM := OSSVerify.Proofs.reac_pw.fuzz_rate.lib.A.FMmch.
Module CJP := OSSVerify.Proofs.reac_pw.fuzz_rate.lib.CJ.Lib.PropExec.
Module CJS := OSSVerify.Proofs.reac_pw.fuzz_rate.lib.CJ.Lib.MState.
Module CJE := OSSVerify.Proofs.reac_pw.fuzz_rate.lib.CJ.Lib.Exec.
Module CJM := OSSVerify.Proofs.reac_pw.fuzz_rate.lib.CJ.Lib.Mem.
Module CJF := OSSVerify.Proofs.reac_pw.fuzz_rate.lib.CJ.Lib.Frame.
Module CJR := OSSVerify.Proofs.reac_pw.fuzz_rate.lib.CJ.RL.Reloc.RStep.
Module GXS := OSSVerify.Proofs.reac_pw.fuzz_rate.lib.CJ.RL.GXA.StrnlenCall.
Module GXF := OSSVerify.Proofs.reac_pw.fuzz_rate.lib.CJ.RL.GXA.AsanFacts.
Module RTA := OSSVerify.Proofs.reac_pw.fuzz_rate.lib.CJ.RL.I.RecAsanVfA.
Module BC := OSSVerify.Proofs.reac_pw.fuzz_rate.lib.A.RT_gxa_bridge_seam.

(* ---- the trampoline: one `j`, in the Bz tree's words ---- *)

(* __interceptor_trampoline_strnlen = __wrap_strnlen 0x412cc: `j 415f8 <___interceptor_strnlen>` (32c0006f) *)
Lemma strnlen_tramp_step : forall (Q : machine_state -> Prop)
    ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem),
  evt asegs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
      F (Z_to_bv 64 0x424b8) fc None m (seg_rom asegs)) ->
  evt asegs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
      F (Z_to_bv 64 0x42198) fc None m (seg_rom asegs)).
Proof. intros until m. intros H. lstep. exact H. Qed.

(* GXA's call target, under A_img: the strnlen trampoline __wrap_strnlen (RT_IImgA.v:69) *)
Lemma A_sym_strnlen : @CJR.sym RTA.N_img_asan_vf 0x21920 = 0x42198.
Proof. vm_compute. reflexivity. Qed.

(* ---- the contract ---- *)

(* What istrnlen_spec asks beyond what strnlen_stack_contract already gives, over the same memory m, with
   sp = bv_unsigned sp, s = bv_unsigned a0, n = bv_unsigned a1 and the walk's stack floor sp - STRN_DEPTH:
   - the stack window lies above ASan's high shadow and below 2^63;
   - the bytes the interceptor checks, [s, s + min (strnlen_res n buf + 1) n), end at or below 2^47;
   - those bytes pass the interceptor's range check (chk_ok: shadow says addressable, the quick check's two
     aligned shadow words are readable, the range is application memory of at most 2^40 bytes);
   - ASan's runtime cells: the mem-to-shadow cells (m2s_cells: the GOT words of
     __asan_shadow_memory_dynamic_address, kMidMemBeg, kMidMemEnd, kHighMemEnd and their values), the cells
     the strnlen interceptor reads (icells_sn: the GOT words of common_flags_dont_use and of the shadow
     address, the shadow offset 0x7fff8000, asan_inited = 1, the flag byte common_flags_dont_use+251 = 1), the
     cells the memchr interceptor reads under musl strnlen (icells_mc: REAL(memchr) = musl memchr 0x924a8
     among them), and REAL(strnlen) = musl strnlen 0x92f68 (icells_sns).
   The checked length is GXA's pc_guard bound (G_printf_core_common.v:157-158): the caller there holds
   `pf_rng m S L` and `Z.min (strnlen_res N buf + 1) N <= L`, which is what strn_ready_intro takes. *)
Definition strn_ready (m : word -> option byte) (sp s n : Z) (buf : list byte) : Prop :=
  kHighShadowEnd < sp - GXS.STRN_DEPTH /\ sp < 2 ^ 63
  /\ s + Z.min (strnlen_res n buf + 1) n <= 2 ^ 47
  /\ chk_ok m s (Z.min (strnlen_res n buf + 1) n)
  /\ m2s_cells m /\ icells_sn m /\ icells_mc m /\ icells_sns m.

Theorem strnlen_stack_contract_A : @GXS.strnlen_stack_contract RTA.N_img_asan_vf strn_ready.
Proof.
  unfold GXS.strnlen_stack_contract.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m buf
    S0 BUF OK MI SEPS ST (LOLO & SPH & SH & CS & M2S & IC & ICM & ICS).
  unfold GXS.STRN_DEPTH in *.
  rewrite A_sym_strnlen.
  apply BC.bz_cj_evt.
  pose proof (bv_unsigned_in_range 64 a1) as N0. change (bv_modulus 64) with (2 ^ 64) in N0.
  assert (LEN : 0 <= memchr_chk 0 (bv_unsigned a1) buf
                /\ memchr_chk 0 (bv_unsigned a1) buf = Z.min (strnlen_res (bv_unsigned a1) buf + 1) (bv_unsigned a1)).
  { unfold memchr_chk, strnlen_res. destruct (find_byte 0 (firstn (Z.to_nat (bv_unsigned a1)) buf)) as [i|] eqn:FB.
    - destruct (find_byte_Some _ _ _ FB) as (Hi & _). rewrite length_firstn in Hi. lia.
    - lia. }
  destruct LEN as (LEN0 & LENE).
  assert (BUFb : bytes_at asegs m (bv_unsigned a0) buf) by exact BUF.
  apply (BzE.evt_mono asegs (istrnlen_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc
            (strnlen_res (bv_unsigned a1) buf) (bv_unsigned sp - 4384) m)).
  - rewrite BC.ms_cj_bz, BC.mkR_cj_bz, BC.seg_rom_cj_bz.
    apply strnlen_tramp_step.
    assert (EA0 : a0 = Z_to_bv 64 (bv_unsigned a0)) by (symmetry; apply Z_to_bv_bv_unsigned).
    assert (EA1 : a1 = Z_to_bv 64 (bv_unsigned a1)) by (symmetry; apply Z_to_bv_bv_unsigned).
    assert (STb : stk asegs m (bv_unsigned sp - 4384) (bv_unsigned sp)) by exact ST.
    assert (OKb : strnlen_ok (bv_unsigned a0) (bv_unsigned a1) buf) by exact OK.
    assert (CSb : chk_ok m (bv_unsigned a0) (strnlen_chk (bv_unsigned a1) buf))
      by (unfold strnlen_chk; rewrite LENE; exact CS).
    exact (istrnlen_spec BzRIP.rip_proof FMM.mch_proof
             ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
             (bv_unsigned a0) (bv_unsigned a1) buf (bv_unsigned sp - 4384)
             EA0 EA1 STb ltac:(lia) LOLO SPH ltac:(lia) ltac:(lia) ltac:(unfold strnlen_chk; lia)
             BUFb OKb SEPS CSb M2S IC ICM ICS (BC.mem_inv_cj_bz m MI)).
  - intros ms' (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & E & MU & WM & MI' & ST').
    assert (BUF' : bytes_at asegs m' (bv_unsigned a0) buf).
    { apply (BzF.bytes_at_transport asegs [(bv_unsigned sp - 4384, bv_unsigned sp)] m m' (bv_unsigned a0) buf BUFb MU).
      cbn [BzF.disjoint_from]. split; [lia | exact I]. }
    unfold GXS.strnlen_stack_post.
    exists t0', t1', t2', a1', a2', a3', a4', a5', a6', a7', t3', t4', t5', t6', m'.
    split; [exact E|]. split; [exact MU|]. split; [exact WM|].
    split; [exact (BC.mem_inv_bz_cj m' MI')|]. split; [exact ST'| exact BUF'].
Qed.

(* ---- what a caller supplies: strn_ready from GXA's own ASan vocabulary ---- *)

(* strn_ready from what GXA's printf_core caller holds at a strnlen call (pc_guard, G_printf_core_common.v:157-158:
   the stack placement, `pf_rng m S L` with `Z.min (strnlen_res N buf + 1) N <= L`), a readable shadow and
   ASan's runtime cells.  pc_guard states pf_rng at the entry memory; GXA's pf_rng_kept and munch_meta
   (AsanFacts.v:128, 142) carry it to the call's memory. *)
Lemma strn_ready_intro : forall (m : word -> option byte) sp S N L buf,
  kHighShadowEnd < sp - GXS.STRN_DEPTH -> sp < 2 ^ 63 ->
  @GXF.pf_rng RTA.N_img_asan_vf m S L -> @GXF.shadow_rw RTA.N_img_asan_vf m -> Z.min (strnlen_res N buf + 1) N <= L ->
  m2s_cells m -> icells_sn m -> icells_mc m -> icells_sns m ->
  strn_ready m sp S N buf.
Proof.
  intros m sp S N L buf H1 H2 PR SRW HL C1 C2 C3 C4.
  split; [exact H1|]. split; [exact H2|]. split.
  - destruct PR as (_ & (_ & _ & Hpn & _) & _). unfold GXF.APPMEM_END in Hpn. lia.
  - split; [exact (BC.chk_ok_of_pf_rng m S L _ PR SRW HL)|].
    exact (conj C1 (conj C2 (conj C3 C4))).
Qed.
