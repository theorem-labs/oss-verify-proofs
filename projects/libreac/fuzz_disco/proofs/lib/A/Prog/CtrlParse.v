(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: the walk of reac_ctrl_stamp_headamp on fuzz_grant.asan, written for libreac/fuzz_grant with proof steps adapted from proofs/cgif/cgif_file_fuzzer/lib/A/AC8a.v, proofs/cgif/cgif_file_fuzzer/lib/A/ACam.v, proofs/cgif/cgif_file_fuzzer/lib/A/ACbf.v, proofs/cgif/cgif_file_fuzzer/lib/A/ACf6.v, proofs/cgif/cgif_file_fuzzer/lib/A/AChd.v. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_grant/lib/A/Prog/CtrlStampHeadamp.v, with its module paths, module names and numbers changed; 361 of its 413 lines of code are new or changed and 1226 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_disco/lib/A/Prog/ReacBoxNameSeg1.v, with its module names changed; 64 of its 94 lines of code are new or changed and 383 lines of the source are left out. *)
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YP09 YI04 YI09 YI08 YI00 YN3v YG0v.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YI16 YM05.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import
PaTable PaSym PaShadow PaRun PaStep PaJournal DiscoSyms DiscoList DiscoAddr DiscoPa DiscoPaLib DiscoBase.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require Import RcParse.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.
Section d. Context {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg disco_listing}.
#[local] Notation SEGS := (@pa_segs _ disco_listing PI).
#[local] Notation BASE := (@pa_val _ disco_listing PI A_TEXT).
Context {RO : ro_below_ofl SEGS pa_relro_lo pa_relro_hi}.
Section h.
Variable B : asyms.
Definition REAC_CTRL_PARSE_STK : Z := 144 + 2 * ESTACK.
Definition REAC_CTRL_PARSE_DEPTH : Z := 9.
Definition treac_ctrl_parse_post (fq : YK11.FPState) (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (S : astate)
  (W0 : world SEGS) (mem0 : word -> option byte) (md0 : Model) (own : list (Z * Z))
  (lyc : alayout) (Sc : astate) (W : world SEGS) (memc : word -> option byte) (k : Z)
  (regs : bvmap 5 word) (o n : Z) (fr : list byte) : world SEGS -> config -> Prop :=
  fun W2 c2 => exists (fx' : YK11.FPState) ly2 S2 regs2 mem2 md2,
    c2 = mkCfg (@mkst fx' regs2 (getr regs 1) mem2 (seg_rom SEGS)) md2 /\
    (forall k : bv 5, bv_unsigned k <> 10 -> Sem.reg_get (@YK11.fp_regs fx') k = Sem.reg_get (@YK11.fp_regs fq) k) /\
    (@YK11.fp_csr fx' = @YK11.fp_csr fq \/ Z.land (Z.shiftr (bv_unsigned (@YK11.fp_csr fx')) 5) 7 = 0) /\
    ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own ly2 S2 W2 mem2 md2 k /\
    aregs_preserved regs regs2 /\ frames S2 = frames Sc /\
    Permutation (ablocks B ly2 S2) (ablocks B lyc Sc) /\
    getr regs2 10 = w64 (fst (ctrlparse n fr)) /\
    garr8 SEGS (mrestrict (w_H W2) mem2) o (map (fun b : byte => bv_unsigned b) (snd (ctrlparse n fr))) /\
    (forall a, alloc_ceiling <= a < 2 ^ 64 -> ~ (spZ regs - REAC_CTRL_PARSE_STK <= a < spZ regs) ->
       ~ (o <= a < o + 36) -> aview SEGS (w_H W2) mem2 a = aview SEGS (w_H W) memc a) /\
    (forall b m i, In (b, m) (ablocks B lyc Sc) -> 0 <= i < req_size m -> ~ (o <= b + i < o + 36) ->
       aview SEGS (w_H W2) mem2 (b + i) = aview SEGS (w_H W) memc (b + i)) /\
    (forall a, in_img SEGS a -> ~ Exists (in_zr a) (as_owned_static B) -> ~ (as_errno B <= a < as_errno B + 4) ->
       aview SEGS (w_H W2) mem2 a = aview SEGS (w_H W) memc a) /\
    (forall cid pos a, In (cid, pos) (frames Sc) ->
       (in_zr a (frame_rng lyc (cid, pos)) \/ in_zr a (shadow_addr (frame_addr lyc cid pos), fs_frame_bytes cid / 8)) ->
       ~ (o <= a < o + 36) -> aview SEGS (w_H W2) mem2 a = aview SEGS (w_H W) memc a) /\
    (forall a, alloc_ceiling <= a < 2 ^ 64 -> ~ (spZ regs - REAC_CTRL_PARSE_STK <= a < spZ regs) ->
       apresent (w_H W) memc a -> apresent (w_H W2) mem2 a) /\
    (forall a, spZ regs - REAC_CTRL_PARSE_STK <= a < spZ regs -> apresent (w_H W2) mem2 a).
Definition treac_ctrl_parse_spec : Prop :=
  forall (fq : YK11.FPState) STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word) ch
    (f n o : Z) (fr : list byte),
  ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
  arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS (w_H W) memc) ->
  YK0s.ret_ok (getr regs 1) -> 4096 <= raZ regs ->
  getr regs 3 = w64 (as_gp B) -> getr regs 4 = w64 (as_tp B) ->
  getr regs 10 = w64 f -> getr regs 11 = w64 n -> getr regs 12 = w64 o ->
  achain lyc (aview SEGS (w_H W) memc) (spZ regs) (s0Z regs) ch ->
  spZ regs mod 16 = 0 -> sp0 - STK <= spZ regs - REAC_CTRL_PARSE_STK -> spZ regs <= sp0 ->
  spZ regs + 32 <= ly_top lyc ->
  Z.of_nat (length (frames Sc)) <= REAC_CTRL_PARSE_DEPTH ->
  0 <= n < 2 ^ 64 -> length fr = 50%nat ->
  (50 <= n -> 0 < f /\ f + 50 <= 2 ^ 47 /\ amem_range f 50 /\ off_img f 50 /\
     (f + 50 <= kLowShadowBeg \/ kHighMemBeg <= f) /\
     (spZ regs <= f \/ f + 50 <= spZ regs - REAC_CTRL_PARSE_STK) /\
     (forall a, f <= a < f + 50 -> apresent (w_H W) memc a) /\
     ((exists cid pos, In (cid, pos) (frames Sc) /\
         frame_addr lyc cid pos <= f /\ f + 50 <= frame_addr lyc cid pos + fs_frame_bytes cid) \/
      (exists b m, In (b, m) (ablocks B lyc Sc) /\ b <= f /\ f + 50 <= b + req_size m) \/
      (ly_stk_lo lyc <= f /\ f + 50 <= ly_stk_hi lyc)) /\
     range_addressable (aview SEGS (w_H W) memc) SHADOW_OFF f 50 /\
     shadow_hull_vis (aview SEGS (w_H W) memc) f 50 /\
     garr8 SEGS (mrestrict (w_H W) memc) f (map (fun b : byte => bv_unsigned b) fr) /\
     (o + 36 <= f \/ f + 50 <= o)) ->
  o mod 32 = 0 -> 4096 <= o -> o + 36 <= 2 ^ 47 -> amem_range o 36 -> off_img o 36 ->
  (o + 36 <= kLowShadowBeg \/ kHighMemBeg <= o) ->
  o + 36 <= alloc_ceiling ->
  range_addressable (aview SEGS (w_H W) memc) SHADOW_OFF o 36 ->
  shadow_hull_vis (aview SEGS (w_H W) memc) o 36 ->
  (forall a, o <= a < o + 36 ->
     awr_byte STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own a /\ apresent (w_H W) memc a) ->
  SRr SEGS W (cfg_at (fx := fq) SEGS (BASE + AF_reac_ctrl_parse) regs memc mdc)
    (treac_ctrl_parse_post fq STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs o n fr).
End h.
End f.
End d.
