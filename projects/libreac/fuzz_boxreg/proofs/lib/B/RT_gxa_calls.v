(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/jsoncons/fuzz_msgpack_encoder/lib/CJ/Ref/Mh_0118.v, with its module paths, module names and addresses changed; 1147 of its 1229 lines of code are new or changed and 2359 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_reply/lib/Prog/drain_b_seg.v, with its module paths, module names and numbers changed; 578 of its 664 lines of code are new or changed and 1143 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_reply/lib/U/Prog/relay_finish_seg.v, with its module paths and module names changed; 360 of its 432 lines of code are new or changed and 592 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/U/Prog/CF/RecKindB.v, with its module paths and module names changed; 186 of its 219 lines of code are new or changed and 399 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-10: relocated from plugin-hostd/fuzz_reply (a working branch 86b50358d34) to libreac/fuzz_boxreg.asan-ubsan by symbol + offset pairing (port_addr_check 5033540ba83b predict mode; boxreg's interceptor and runtime code is instruction-for-instruction fuzz_reply's modulo numerals): 4 address numeral(s) rewritten, module paths changed; GXA sym KEYS (the donor key space, `sym RTA.A_img 0x...`) kept unrelocated (this image's tree is lib/B). *)
(* GXA's interceptor call contract for strnlen (lib/CJ/RL/GXA/StrnlenCall.v:29-41 strnlen_stack_contract),
   discharged at the ASan instance A_img (RT_IImgA.v:96) on the pinned fuzz_reply.asan.

   This file proves no new function.  It composes three proofs that are already in the tree:
   - a Theorem Labs lane's Bz interceptor walk of ___interceptor_strnlen 0x424c4 (lib/A/Bz/A/I_strnlen.v:103 istrnlen_spec,
     relocated by a Theorem Labs lane), which calls REAL(strnlen) = musl strnlen 0x96e48 (I_strnlenw.v:81 musl_strnlen_spec);
   - its two section hypotheses: rip_stmt (lib/A/Bz/A/R_isPoisoned.v:298 rip_proof) and memchr_stmt
     (lib/A/FRsl.v:76 mch_proof);
   - GXA's call-contract statement, which it takes as a Context in G_printf_core.v:124-125.
   What it adds is glue only:
   - the trampoline: GXA's call target `sym 0x21920` is __interceptor_trampoline_strnlen 0x42190 under A_img
     (RT_IImgA.v:59), and that is one instruction, `j 424c4 <___interceptor_strnlen>` (fuzz_reply.objdump.txt:18281);
   - the vocabulary: the Bz tree (lib/A/Bz/Lib) and the CJ tree (lib/CJ/Lib) are two copies of the same machine
     library.  Every definition used here is the same term in both, so it converts by `exact`, except two:
     `msteps` (an Inductive in each tree; bz_cj_msteps) and `mem_inv` (CJ: every byte is outside read-only
     segments and inside a segment or below TASK_SIZE; Bz: every byte and every segment byte is below UTOP).
     TASK_SIZE = UTOP = 2^47, and every segment of fuzz_reply.asan ends below 2^47 (asegs_below).
   What a caller supplies: strn_ready (below) is exactly what istrnlen_spec asks beyond the contract's own
   premises; strn_ready_intro proves it from GXA's own ASan vocabulary (AsanFacts.v pf_rng / shadow_rw), the
   stack placement and ASan's runtime cells, the shadow half through FRbz_str.v's ro_C8_of_vis.
   Numerals introduced here (none is relocated from another image):
     0x42190  __interceptor_trampoline_strnlen  (fuzz_reply.nm.txt; the A_img row KV 0x21920 0x42190)
     0x424c4  ___interceptor_strnlen            (the target of the j at 0x42190; istrnlen_spec's entry pc)
   The memcpy and memset contracts (CopyCall.v:29, SetCall.v:28) are discharged in RT_gxa_calls_mem.v, over
   a Theorem Labs lane's interceptor walks relocated from 840c4afa7e2 (lib/A/Bz/A/I_memcpy.v, I_imemset.v). *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.B.Bz.Lib Require Import Tac ImageA SysStep.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.B.Bz.Spec Require Import StrFun.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.B.Bz.Lib Require Import StoreFast.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.B.Bz.P Require Import Str_tac Startup_glue.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.B.Bz.A Require Import Shadow R_small R_m2s R_thread I_consts I_qck X_atexit IcptSpec D_kit I_ikit I_musl I_memchrw I_strnlenw I_strnlen.
Require OSSVerify.Proofs.libreac.fuzz_boxreg.lib.B.Bz.Common.PropExec.
Require OSSVerify.Proofs.libreac.fuzz_boxreg.lib.B.Bz.Lib.MState.
Require OSSVerify.Proofs.libreac.fuzz_boxreg.lib.B.Bz.Lib.Exec.
Require OSSVerify.Proofs.libreac.fuzz_boxreg.lib.B.Bz.Lib.Mem.
Require OSSVerify.Proofs.libreac.fuzz_boxreg.lib.B.Bz.Lib.Frame.
Require OSSVerify.Proofs.libreac.fuzz_boxreg.lib.B.Bz.A.R_isPoisoned.
Require OSSVerify.Proofs.libreac.fuzz_boxreg.lib.B.FRsl.
Require OSSVerify.Proofs.libreac.fuzz_boxreg.lib.CJ.Lib.PropExec.
Require OSSVerify.Proofs.libreac.fuzz_boxreg.lib.CJ.Lib.MState.
Require OSSVerify.Proofs.libreac.fuzz_boxreg.lib.CJ.Lib.Exec.
Require OSSVerify.Proofs.libreac.fuzz_boxreg.lib.CJ.Lib.Mem.
Require OSSVerify.Proofs.libreac.fuzz_boxreg.lib.CJ.Lib.Frame.
Require OSSVerify.Proofs.libreac.fuzz_boxreg.lib.CJ.RL.Reloc.RStep.
Require OSSVerify.Proofs.libreac.fuzz_boxreg.lib.CJ.RL.GXA.StrnlenCall.
Require OSSVerify.Proofs.libreac.fuzz_boxreg.lib.CJ.RL.GXA.AsanFacts.
Require OSSVerify.Proofs.libreac.fuzz_boxreg.lib.B.RT_IImgA.
Require OSSVerify.Proofs.libreac.fuzz_boxreg.lib.B.FRbz_str.
Import ListNotations.
Open Scope Z_scope.

Module BzP := OSSVerify.Proofs.libreac.fuzz_boxreg.lib.B.Bz.Common.PropExec.
Module BzS := OSSVerify.Proofs.libreac.fuzz_boxreg.lib.B.Bz.Lib.MState.
Module BzE := OSSVerify.Proofs.libreac.fuzz_boxreg.lib.B.Bz.Lib.Exec.
Module BzM := OSSVerify.Proofs.libreac.fuzz_boxreg.lib.B.Bz.Lib.Mem.
Module BzF := OSSVerify.Proofs.libreac.fuzz_boxreg.lib.B.Bz.Lib.Frame.
Module BzRIP := OSSVerify.Proofs.libreac.fuzz_boxreg.lib.B.Bz.A.R_isPoisoned.
Module FRS := OSSVerify.Proofs.libreac.fuzz_boxreg.lib.B.FRsl.
Module CJP := OSSVerify.Proofs.libreac.fuzz_boxreg.lib.CJ.Lib.PropExec.
Module CJS := OSSVerify.Proofs.libreac.fuzz_boxreg.lib.CJ.Lib.MState.
Module CJE := OSSVerify.Proofs.libreac.fuzz_boxreg.lib.CJ.Lib.Exec.
Module CJM := OSSVerify.Proofs.libreac.fuzz_boxreg.lib.CJ.Lib.Mem.
Module CJF := OSSVerify.Proofs.libreac.fuzz_boxreg.lib.CJ.Lib.Frame.
Module CJR := OSSVerify.Proofs.libreac.fuzz_boxreg.lib.CJ.RL.Reloc.RStep.
Module GXS := OSSVerify.Proofs.libreac.fuzz_boxreg.lib.CJ.RL.GXA.StrnlenCall.
Module GXF := OSSVerify.Proofs.libreac.fuzz_boxreg.lib.CJ.RL.GXA.AsanFacts.
Module RTA := OSSVerify.Proofs.libreac.fuzz_boxreg.lib.B.RT_IImgA.
Module FBS := OSSVerify.Proofs.libreac.fuzz_boxreg.lib.B.FRbz_str.

(* ---- the trampoline: one `j`, in the Bz tree's words ---- *)

(* __interceptor_trampoline_strnlen 0x42190: `j 424c4 <___interceptor_strnlen>` (3340006f) *)
Lemma strnlen_tramp_step : forall (Q : machine_state -> Prop)
    ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem),
  evt asegs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
      F (Z_to_bv 64 0x41774) fc None m (seg_rom asegs)) ->
  evt asegs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
      F (Z_to_bv 64 0x41450) fc None m (seg_rom asegs)).
Proof. intros until m. intros H. lstep. exact H. Qed.

(* ---- the two trees' vocabularies ---- *)

Lemma ms_cj_bz : forall R F pc fc rv m ro, CJS.MS R F pc fc rv m ro = BzS.MS R F pc fc rv m ro.
Proof. reflexivity. Qed.

Lemma mkR_cj_bz : forall x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31,
  CJF.mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31
  = BzF.mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31.
Proof. reflexivity. Qed.

Lemma seg_rom_cj_bz : CJP.seg_rom (@CJR.img_segs RTA.A_img) = BzP.seg_rom asegs.
Proof. reflexivity. Qed.

Lemma bz_cj_msteps : forall s s', BzE.msteps asegs s s' -> CJE.msteps (@CJR.img_segs RTA.A_img) s s'.
Proof.
  intros s s' H. induction H as [s|s s1 s2 Hs _ IH].
  - apply CJE.msteps_refl.
  - eapply CJE.msteps_cons; [exact Hs | exact IH].
Qed.

Lemma bz_cj_evt : forall Q ms, BzE.evt asegs Q ms -> CJE.evt (@CJR.img_segs RTA.A_img) Q ms.
Proof. intros Q ms (ms' & H & HQ). exists ms'. split; [exact (bz_cj_msteps ms ms' H) | exact HQ]. Qed.

Local Lemma find_segment_rng : forall segs a n seg, find_segment segs a n = Some seg ->
  In seg segs /\ Z.of_N (seg_base seg) <= a /\ a + n <= Z.of_N (seg_base seg) + Z.of_N (seg_size seg).
Proof.
  induction segs as [|s segs IH]; intros a n seg H; cbn [find_segment] in H; [discriminate|].
  match type of H with context [if ?c then _ else _] => destruct c eqn:E end.
  - injection H as <-. apply andb_prop in E as [E1 E2]. apply Z.leb_le in E1. apply Z.leb_le in E2.
    split; [left; reflexivity|]. lia.
  - destruct (IH a n seg H) as (Hi & H1 & H2). split; [right; exact Hi|]. lia.
Qed.

(* every segment of fuzz_reply.asan ends below 2^47 *)
Lemma asegs_below : forall a : word, BzM.seg_addr asegs a = true -> bv_unsigned a < BzM.UTOP.
Proof.
  intros a H. unfold BzM.seg_addr in H.
  destruct (find_segment asegs (bv_unsigned a) 1) as [sg|] eqn:E; [|discriminate].
  destruct (find_segment_rng _ _ _ _ E) as (I & _ & R).
  assert (B : forallb (fun sg => Z.of_N (seg_base sg) + Z.of_N (seg_size sg) <=? 2 ^ 47) asegs = true)
    by (vm_compute; reflexivity).
  rewrite forallb_forall in B. specialize (B sg I). apply Z.leb_le in B. unfold BzM.UTOP. lia.
Qed.

Lemma mem_inv_cj_bz : forall m, CJM.mem_inv (@CJR.img_segs RTA.A_img) m -> BzM.mem_inv asegs m.
Proof.
  intros m H. apply BzM.mem_inv_intro; [exact asegs_below|].
  intros a b E. destruct (H a b E) as [[R S]|[R T]].
  - split; [exact R|]. apply asegs_below. unfold BzM.seg_addr.
    change (find_segment asegs (bv_unsigned a) 1 <> None) in S.
    destruct (find_segment asegs (bv_unsigned a) 1); [reflexivity | congruence].
  - split; [exact R|]. unfold BzM.UTOP. unfold TASK_SIZE in T. lia.
Qed.

Lemma mem_inv_bz_cj : forall m, BzM.mem_inv asegs m -> CJM.mem_inv (@CJR.img_segs RTA.A_img) m.
Proof.
  intros m H a b E. right. split.
  - exact (BzM.mem_inv_ro asegs m a b H E).
  - pose proof (BzM.mem_inv_ov_below asegs m a b H E) as B. unfold BzM.UTOP in B. unfold TASK_SIZE. lia.
Qed.

(* GXA's call target, under A_img: the strnlen trampoline (RT_IImgA.v:59) *)
Lemma A_sym_strnlen : @CJR.sym RTA.A_img 0x21920 = 0x41450.
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
     cells the memchr interceptor reads under musl strnlen (icells_mc: REAL(memchr) = musl memchr 0x963d0
     among them), and REAL(strnlen) = musl strnlen 0x96e48 (icells_sns).
   The checked length is GXA's pc_guard bound (G_printf_core_common.v:157-158): the caller there holds
   `pf_rng m S L` and `Z.min (strnlen_res N buf + 1) N <= L`, which is what strn_ready_intro takes. *)
Definition strn_ready (m : word -> option byte) (sp s n : Z) (buf : list byte) : Prop :=
  kHighShadowEnd < sp - GXS.STRN_DEPTH /\ sp < 2 ^ 63
  /\ s + Z.min (strnlen_res n buf + 1) n <= 2 ^ 47
  /\ chk_ok m s (Z.min (strnlen_res n buf + 1) n)
  /\ m2s_cells m /\ icells_sn m /\ icells_mc m /\ icells_sns m.

Theorem strnlen_stack_contract_A : @GXS.strnlen_stack_contract RTA.A_img strn_ready.
Proof.
  unfold GXS.strnlen_stack_contract.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m buf
    S0 BUF OK MI SEPS ST (LOLO & SPH & SH & CS & M2S & IC & ICM & ICS).
  unfold GXS.STRN_DEPTH in *.
  rewrite A_sym_strnlen.
  apply bz_cj_evt.
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
  - rewrite ms_cj_bz, mkR_cj_bz, seg_rom_cj_bz.
    apply strnlen_tramp_step.
    assert (EA0 : a0 = Z_to_bv 64 (bv_unsigned a0)) by (symmetry; apply Z_to_bv_bv_unsigned).
    assert (EA1 : a1 = Z_to_bv 64 (bv_unsigned a1)) by (symmetry; apply Z_to_bv_bv_unsigned).
    assert (STb : stk asegs m (bv_unsigned sp - 4384) (bv_unsigned sp)) by exact ST.
    assert (OKb : strnlen_ok (bv_unsigned a0) (bv_unsigned a1) buf) by exact OK.
    assert (CSb : chk_ok m (bv_unsigned a0) (strnlen_chk (bv_unsigned a1) buf))
      by (unfold strnlen_chk; rewrite LENE; exact CS).
    exact (istrnlen_spec BzRIP.rip_proof FRS.mch_proof
             ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
             (bv_unsigned a0) (bv_unsigned a1) buf (bv_unsigned sp - 4384)
             EA0 EA1 STb ltac:(lia) LOLO SPH ltac:(lia) ltac:(lia) ltac:(unfold strnlen_chk; lia)
             BUFb OKb SEPS CSb M2S IC ICM ICS (mem_inv_cj_bz m MI)).
  - intros ms' (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & E & MU & WM & MI' & ST').
    assert (BUF' : bytes_at asegs m' (bv_unsigned a0) buf).
    { apply (BzF.bytes_at_transport asegs [(bv_unsigned sp - 4384, bv_unsigned sp)] m m' (bv_unsigned a0) buf BUFb MU).
      cbn [BzF.disjoint_from]. split; [lia | exact I]. }
    unfold GXS.strnlen_stack_post.
    exists t0', t1', t2', a1', a2', a3', a4', a5', a6', a7', t3', t4', t5', t6', m'.
    split; [exact E|]. split; [exact MU|]. split; [exact WM|].
    split; [exact (mem_inv_bz_cj m' MI')|]. split; [exact ST'| exact BUF'].
Qed.

(* ---- what a caller supplies: strn_ready from GXA's own ASan vocabulary ---- *)

Local Lemma shad_eq : forall x, shad x = GXF.shadow_addr x.
Proof. intros x. unfold shad, SHB, GXF.shadow_addr, GXF.ASAN_K. lia. Qed.

(* a byte GXA's reader sees is a byte the walks can read *)
Local Lemma bytes_at1_of_mrd : forall (m : word -> option byte) a b,
  0 <= a < 2 ^ 64 -> CJM.mrd (@CJR.img_segs RTA.A_img) m (CJM.wa a) = Some b -> bytes_at asegs m a [b].
Proof.
  intros m a b Ha H. split; [lia|]. split; [cbn; lia|].
  intros i Hi. cbn [length] in Hi. assert (Hi0 : i = 0%nat) by lia. subst i.
  cbn [nth_error]. rewrite Z.add_0_r. exact H.
Qed.

(* GXA reads a shadow byte signed (AsanFacts.v:20), the walks unsigned (Shadow.v:16); on 0..7 they agree *)
Local Lemma sh_ok_of_shadow_ok : forall (b : byte) a, GXF.shadow_ok a (bv_signed b) -> sh_ok b a.
Proof.
  intros b a H. pose proof (bv_unsigned_in_range 8 b) as R.
  unfold GXF.shadow_ok, bv_signed, bv_swrap, bv_wrap in H. unfold sh_ok.
  change (bv_half_modulus 8) with 128 in H. change (bv_modulus 8) with 256 in H, R.
  Z.div_mod_to_equations. lia.
Qed.

(* the quick check's aligned shadow word of an application byte lies in ASan's shadow *)
Local Lemma al8_shad_in_shadow : forall x j, GXF.app_mem x -> 0 <= j < 8 -> GXF.in_shadow (al8 (shad x) + j).
Proof.
  intros x j H Hj.
  unfold GXF.app_mem, GXF.in_shadow, GXF.LOWMEM_END, GXF.LOWSHADOW_END, GXF.HIGHSHADOW_BEG, GXF.HIGHMEM_BEG,
    GXF.APPMEM_END, al8, shad, SHB in *.
  Z.div_mod_to_equations. lia.
Qed.

Local Lemma qc_word_of_shadow_rw : forall (m : word -> option byte) x,
  @GXF.shadow_rw RTA.A_img m -> GXF.app_mem x ->
  ro_cells asegs m (al8 (shad x)) [C8 (FBS.word_of_mem m (al8 (shad x)))].
Proof.
  intros m x SRW Hx.
  assert (B : 0 <= al8 (shad x) /\ al8 (shad x) + 8 <= 2 ^ 64).
  { unfold GXF.app_mem, GXF.LOWMEM_END, GXF.HIGHMEM_BEG, GXF.APPMEM_END, al8, shad, SHB in *.
    Z.div_mod_to_equations. lia. }
  apply FBS.ro_C8_of_vis; [lia | lia |].
  intros j Hj. pose proof (al8_shad_in_shadow x j Hx Hj) as HS.
  destruct (SRW _ HS) as (_ & b & Hb). exists b.
  apply bytes_at1_of_mrd; [| exact Hb].
  unfold GXF.in_shadow, GXF.LOWMEM_END, GXF.LOWSHADOW_END, GXF.HIGHSHADOW_BEG, GXF.HIGHMEM_BEG in HS. lia.
Qed.

(* the interceptor's range check on any prefix of a range GXA calls addressable, given a readable shadow *)
Lemma chk_ok_of_pf_rng : forall (m : word -> option byte) p n k,
  @GXF.pf_rng RTA.A_img m p n -> @GXF.shadow_rw RTA.A_img m -> k <= n -> chk_ok m p k.
Proof.
  intros m p n k (HN & (Hp & Hn & Hpn & AD) & _ & SEVEN) SRW Hk.
  unfold GXF.APPMEM_END in Hpn.
  split; [| split].
  - intros i Hi. destruct (AD i ltac:(lia)) as (APP & b & Hb & Hok).
    exists b. split.
    + rewrite shad_eq. apply bytes_at1_of_mrd; [| exact Hb].
      unfold GXF.shadow_addr, GXF.ASAN_K. Z.div_mod_to_equations. lia.
    + apply sh_ok_of_shadow_ok. exact Hok.
  - intros Hk1.
    destruct (AD 0 ltac:(lia)) as (A0 & _). rewrite Z.add_0_r in A0.
    destruct (AD (k - 1) ltac:(lia)) as (A1 & _). replace (p + (k - 1)) with (p + k - 1) in A1 by lia.
    exists (FBS.word_of_mem m (al8 (shad p))), (FBS.word_of_mem m (al8 (shad (p + k - 1)))).
    split; apply qc_word_of_shadow_rw; assumption.
  - intros Hk0. split; [| lia].
    destruct (AD 0 ltac:(lia)) as (A0 & _). rewrite Z.add_0_r in A0.
    pose proof (SEVEN (k - 1) ltac:(lia)) as A7.
    unfold region_in_mem, kLowMemEnd, kHighShadowEnd, kHighMemEnd.
    unfold GXF.app_mem, GXF.LOWMEM_END, GXF.HIGHMEM_BEG, GXF.APPMEM_END in A0, A7. lia.
Qed.

(* strn_ready from what GXA's printf_core caller holds at a strnlen call (pc_guard, G_printf_core_common.v:157-158:
   the stack placement, `pf_rng m S L` with `Z.min (strnlen_res N buf + 1) N <= L`), a readable shadow and
   ASan's runtime cells.  pc_guard states pf_rng at the entry memory; GXA's pf_rng_kept and munch_meta
   (AsanFacts.v:128, 142) carry it to the call's memory. *)
Lemma strn_ready_intro : forall (m : word -> option byte) sp S N L buf,
  kHighShadowEnd < sp - GXS.STRN_DEPTH -> sp < 2 ^ 63 ->
  @GXF.pf_rng RTA.A_img m S L -> @GXF.shadow_rw RTA.A_img m -> Z.min (strnlen_res N buf + 1) N <= L ->
  m2s_cells m -> icells_sn m -> icells_mc m -> icells_sns m ->
  strn_ready m sp S N buf.
Proof.
  intros m sp S N L buf H1 H2 PR SRW HL C1 C2 C3 C4.
  split; [exact H1|]. split; [exact H2|]. split.
  - destruct PR as (_ & (_ & _ & Hpn & _) & _). unfold GXF.APPMEM_END in Hpn. lia.
  - split; [exact (chk_ok_of_pf_rng m S L _ PR SRW HL)|].
    exact (conj C1 (conj C2 (conj C3 C4))).
Qed.
