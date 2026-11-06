(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* lib/B twin of lib/A/RT_pf_snp_pcom.v (sha256 11119c4e75de; internal record) for fuzz_reply.asan-ubsan: module paths lib.A -> lib.B, AB1v -> YB1v; image numerals GLOBALS_TOP 0x5fb000 -> 0x5fc000, GOT word of __stack_chk_guard 0x9e658 -> 0x9ebd8 (SNPSRRB-numerals.tsv sha256 b8c04c0261ed; internal record) *)
(* Theorem Labs, 2026-10: printf_common's start premise (RT_pf_bz.v pcom_pre) for fuzz_reply's one snprintf format
   "%s %d ", at a store m' reached from the per-call normalized store m0 = FMgxaSeamNorm.cjnormv ly R (w_H W) mem.

   No function is walked here.  snp_pcom is the PCOM obligation of RT_pf_snp_srr.v snp_xn (CHAIN_K's premise
   `forall m', munch .. m0 m' -> .. -> pcom_pre A (q - PF_SPILL) (q - PF_SNF_FRAME - PF_VSN_FRAME) m'`) and the
   pcom_pre conjunct of vf_ready_icpt (RT_pf_stmt.v, at q - 2608), stated at a general floor qpc and a general m'
   with the two store facts both sites give: m' agrees with m0 below GLOBALS_TOP = 0x5fc000 (every munch of the chain
   is on the stack window or the destination, both at or above it), and m' keeps m0's ASan shadow (meta_kept).

   The witnesses: body = "%s %d ", args = [PA_s s; PA_i 0] (printf_common's grammar walk and its checks read only the
   kind of each argument and the %s string's bytes: ck_arg of PA_i is True), slots = the five spilled words, no
   precomputed covers.  From the contract:
   - the format's bytes (HSTR) and the %s string's bytes (its astr_at) are the harness's view below 0x9ebd8, read the
     same in m0 (MN.ro_agree, and the zone test drops nothing below LOWMEM_END) and in m' (the agreement);
   - chk_ok of the format and chkr of the string: each range is carved in R, so its shadow hull is kept by cjnormv
     (FMgxaSeamNorm.hull_kept_carved), the contract's aread_ok gives the hull and the addressability in the harness's
     view, and m' keeps the shadow; chkr's per-byte aligned shadow words are the hull's words;
   - the slot of the %s argument from the va_list area;
   - pctx from m0's (printf_common's cells lie below 0x5fc000). *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn YP0b YP0a.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YCbqG FCiface.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import
W_syms W_listing W_place W_tbl W_kit W_img W_journal W_contract W_sites W_journal_x W_sites_x.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require printf_facts_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import YB1v.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require RT_IImgA.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import RT_pf_Tbl.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.CJ.Lib Require Mem Frame Cells Step Arr.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib Require MemNorm.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require RT_pf_bz FMgxaSeamBase FMgxaSeamNorm FMgxaSeamNormG
FMgxaSeamReadyX FRbz_str RT_gxa_calls.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B.Bz.Lib Require ImageA Mem Cells Step.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B.Bz.A Require R_m2s I_pcrr I_pchead I_pck I_qck I_pcxgram
I_pcxlist I_consts F_achk Shadow D_kit.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.CJ.RL.G Require G_pop_arg.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.CJ.RL.GXA Require AsanFacts.
Import ListNotations.
Local Unset Lia Cache. Local Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

Module PFC := OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog.printf_facts_c.
Module CJMm := OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.CJ.Lib.Mem.
Module CJArr := OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.CJ.Lib.Arr.
Module SBa := OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B.FMgxaSeamBase.
Module NM := OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B.FMgxaSeamNorm.
Module NG := OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B.FMgxaSeamNormG.
Module MN := OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.MemNorm.
Module SRy := OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B.FMgxaSeamReadyX.
Module GAF := OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.CJ.RL.GXA.AsanFacts.
Module GPOP := OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.CJ.RL.G.G_pop_arg.
Module PB := OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B.RT_pf_bz.
Module BzI := OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B.Bz.Lib.ImageA.
Module BzM := OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B.Bz.Lib.Mem.
Module BzCl := OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B.Bz.Lib.Cells.
Module BzSt := OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B.Bz.Lib.Step.
Module BzPH := OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B.Bz.A.I_pchead.
Module BzPK := OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B.Bz.A.I_pck.
Module BzQ := OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B.Bz.A.I_qck.
Module BzG := OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B.Bz.A.I_pcxgram.
Module BzL := OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B.Bz.A.I_pcxlist.
Module BzF := OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B.Bz.A.F_achk.
Module BzSh := OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B.Bz.A.Shadow.
Module BzR := OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B.Bz.A.R_m2s.
Module BzK := OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B.Bz.A.I_consts.
Module BzD := OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B.Bz.A.D_kit.
Module FRS := OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B.FRbz_str.
Module BC := OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B.RT_gxa_calls.

#[local] Existing Instance RT_IImgA.A_img.

Section pcom. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.

(* ---- bytes the harness sees below GLOBALS_TOP are bytes of m' (through m0 = cjnormv, then the agreement) ---- *)
Lemma pc_bytes_low : forall ly R (W : world tfibsegs) mem (m' : word -> option byte) a (l : list byte),
  MN.ro_agree tfibsegs (SBa.cjstore (w_H W) mem) ->
  (forall x : word, bv_unsigned x < 0x5fc000 -> m' x = NM.cjnormv ly R (w_H W) mem x) ->
  0 <= a -> a + Z.of_nat (length l) <= 0x5fc000 ->
  (forall i, (i < length l)%nat ->
     aview tfibsegs (w_H W) mem (a + Z.of_nat i) = Some (bv_unsigned (nth i l (Z_to_bv 8 0)))) ->
  BzM.bytes_at BzI.asegs m' a l.
Proof.
intros ly R W mem m' a l HRO AG H0 H1 HV.
split; [exact H0|]. split; [lia|]. intros i Hi.
assert (Hx : bv_unsigned (CJMm.wa (a + Z.of_nat i)) = a + Z.of_nat i)
  by (apply CJMm.wa_unsigned; lia).
change (CJMm.mrd tfibsegs m' (CJMm.wa (a + Z.of_nat i)) = nth_error l i).
assert (E : CJMm.mrd tfibsegs m' (CJMm.wa (a + Z.of_nat i)) =
            CJMm.mrd tfibsegs (NM.cjnormv ly R (w_H W) mem) (CJMm.wa (a + Z.of_nat i))).
{ unfold CJMm.mrd. rewrite (AG _ ltac:(rewrite Hx; lia)). reflexivity. }
rewrite E.
rewrite (NM.mrd_cjnormv ly R (w_H W) mem _ HRO ltac:(right; rewrite Hx; unfold TASK_SIZE; lia)
           ltac:(rewrite Hx; apply NM.dz_low; unfold GAF.LOWMEM_END; lia)).
rewrite (SBa.mrd_of_view (w_H W) mem _ _ (HV i Hi)), SBa.byte_roundtrip.
symmetry. apply nth_error_nth'. exact Hi.
Qed.

(* ---- an aread_ok range carved in R: addressable with its hull visible at every m' that keeps m0's shadow ---- *)
Lemma pc_rng0 : forall stk (W : world tfibsegs) regs mem p n,
  aread_ok stk W regs mem p n -> amem_range p (n + 8) -> GAF.pf_rng (SBa.cjstore (w_H W) mem) p n.
Proof.
intros stk W regs mem p n (H0 & H1 & H2 & _ & HAM & HRA & _) HAM8.
replace n with (Z.of_nat (Z.to_nat n)) in * by lia.
apply SRy.seam_dest_rng; [lia | lia | exact HAM | exact HAM8 | exact HRA].
Qed.

Lemma pc_kept : forall ly R (W : world tfibsegs) mem regs stk (m' : word -> option byte) p n,
  In (p, n) R -> aread_ok stk W regs mem p n -> 0 < n -> amem_range p (n + 8) ->
  GAF.meta_kept (NM.cjnormv ly R (w_H W) mem) m' ->
  GAF.pf_rng m' p n /\ shadow_hull_vis (SRy.sview m') p n.
Proof.
intros ly R W mem regs stk m' p n Hin HRD Hn HAM8 MK.
pose proof (pc_rng0 stk W regs mem p n HRD HAM8) as PF.
pose proof HRD as (H0 & _ & _ & _ & HAM & _ & HHV).
pose proof (NM.hull_kept_carved ly R (p, n) Hin H0 (NM.amem_app p n H0 HAM)) as K. cbn [fst snd] in K.
pose proof (NM.pf_rng_cjnormv ly R (w_H W) mem p n (NM.sh_kept_of_hull ly R p n K) PF) as PF0.
split; [exact (GAF.pf_rng_kept _ _ p n PF0 MK)|].
apply (SRy.hull_kept (NM.cjnormv ly R (w_H W) mem) m' p n MK Hn (SRy.pf_rng_app _ p n PF0)).
exact (NM.hull_cjnormv ly R (w_H W) mem p n K (HHV Hn)).
Qed.

(* ---- chkr (F_achk.v): chk_ok's shadow bytes and range, and each byte's aligned shadow word, which is a word of
   the hull ---- *)
Lemma pc_chkr : forall (m : word -> option byte) p n,
  BzQ.chk_ok m p n -> 0 <= p -> 0 < n -> p + n <= 2 ^ 63 ->
  shadow_hull_vis (SRy.sview m) p n -> BzF.chkr m p n.
Proof.
intros m p n (AC & _ & RO) Hp Hn Hpn HV. split; [exact AC|]. split; [|exact (RO Hn)].
intros i Hi.
pose proof (SRy.hull_sub _ p n (p + i) 1 HV ltac:(lia) ltac:(lia) ltac:(lia)) as HV1.
unfold shadow_hull_vis in HV1.
assert (E1 : p + i + 1 - 1 = p + i) by lia. rewrite E1 in HV1. clear E1.
exists (FRS.word_of_mem m (BzQ.al8 (BzSh.shad (p + i)))).
rewrite SRy.al8_shad_hull.
assert (B0 : 0 <= shadow_addr (p + i) / 8 * 8).
{ unfold shadow_addr, SHADOW_OFF. pose proof (Z.div_pos (p + i) 8 ltac:(lia) ltac:(lia)).
  apply Z.mul_nonneg_nonneg; [apply Z.div_pos|]; lia. }
assert (B1 : shadow_addr (p + i) / 8 * 8 + 8 <= 2 ^ 64).
{ pose proof (Z.mul_div_le (shadow_addr (p + i)) 8 ltac:(lia)).
  assert (shadow_addr (p + i) <= SHADOW_OFF + (p + i)).
  { unfold shadow_addr. apply Z.add_le_mono_l. apply Z.div_le_upper_bound; lia. }
  unfold SHADOW_OFF in *. lia. }
apply FRS.ro_C8_of_vis; [exact B0 | exact B1 |]. intros j Hj.
remember (shadow_addr (p + i) / 8 * 8) as S0 eqn:ES0.
assert (Hs : S0 <= S0 + j < S0 + 8) by lia.
pose proof (HV1 (S0 + j) Hs) as V. unfold SRy.sview in V.
destruct (CJMm.mrd tfibsegs m (CJMm.wa (S0 + j))) as [b|] eqn:E;
  [|exfalso; apply V; reflexivity].
exists b. apply BC.bytes_at1_of_mrd; [lia | exact E].
Qed.

(* ---- printf_common's cells lie below GLOBALS_TOP, so m' holds them as m0 does ---- *)
Lemma pc_pctx : forall (m m' : word -> option byte), BzPH.pctx m ->
  (forall x : word, bv_unsigned x < 0x5fc000 -> m' x = m x) -> BzPH.pctx m'.
Proof.
intros m m' ((X1 & X2 & X3) & (P1 & P2)) AG.
assert (AGP : BzD.agree_on BzPH.in_PCR m m').
{ intros a Ha. apply AG. unfold BzPH.in_PCR in Ha. lia. }
assert (RO : forall A cs, BzSt.ro_cells BzI.asegs m A cs ->
               (forall x, A <= x < A + Z.of_nat (BzCl.cells_size cs) -> BzPH.in_PCR x) ->
               BzSt.ro_cells BzI.asegs m' A cs).
{ intros A cs H HX. apply (BzD.ro_cells_agree _ m m' _ _ H). exact (BzD.agree_sub _ _ _ _ AGP HX). }
assert (RW : forall A cs, BzSt.rw_cells BzI.asegs m A cs ->
               (forall x, A <= x < A + Z.of_nat (BzCl.cells_size cs) -> BzPH.in_PCR x) ->
               BzSt.rw_cells BzI.asegs m' A cs).
{ intros A cs [Hc (H0 & H1 & Hw)] HX.
  split; [exact (BzD.cells_at_agree _ m m' A cs Hc (BzD.agree_sub _ _ _ _ AGP HX))|].
  split; [exact H0|]. split; [exact H1|]. intros i Hi.
  pose proof (HX (A + i) ltac:(lia)) as Hp. unfold BzPH.in_PCR in Hp.
  rewrite (BzD.wview_agree _ m m' (BzM.wa (A + i))); [exact (Hw i Hi)|].
  apply AG. rewrite BzM.wa_unsigned by lia. lia. }
split; [split; [| split] | split].
all: first [ apply RO; [assumption | cbn [BzCl.cells_size BzCl.csize]; intros x Hx; unfold BzPH.in_PCR; lia]
           | apply RW; [assumption | cbn [BzCl.cells_size BzCl.csize]; intros x Hx; unfold BzPH.in_PCR; lia] ].
Qed.

(* ---- the %s slot: the first word of the va_list area ---- *)
Lemma pc_slot0 : forall (m' : word -> option byte) VA (a3 a4 a5 a6 a7 : word),
  GPOP.va_area m' VA ([a3; a4; a5; a6; a7] ++ []) -> BzSt.ro_cells BzI.asegs m' VA [BzCl.C8 a3].
Proof.
intros m' VA a3 a4 a5 a6 a7 HVA. unfold GPOP.va_area in HVA. cbn [app CJArr.u64s] in HVA.
apply CJMm.bytes_at_app in HVA. destruct HVA as [HB _].
split; [cbn; tauto|]. cbn [BzCl.cells_bytes BzCl.cbytes]. rewrite app_nil_r. exact HB.
Qed.

Theorem snp_pcom : forall ly (R : list (Z * Z)) (W : world tfibsegs) mem (regs : bvmap 5 word) (stk f q qpc : Z)
    (s : list Z) (a3 a4 a5 a6 a7 : word) (m' : word -> option byte),
  MN.ro_agree tfibsegs (SBa.cjstore (w_H W) mem) ->
  BzPH.pctx (NM.cjnormv ly R (w_H W) mem) ->
  In (f, 7) R -> In (bv_unsigned a3, Z.of_nat (length s) + 1) R ->
  astr_at W mem f (PFC.pf_bytes [37; 115; 32; 37; 100; 32]) ->
  aread_ok stk W regs mem f 7 ->
  65536 <= f -> f + 7 <= 0x9ebd8 ->
  astr_at W mem (bv_unsigned a3) (PFC.pf_bytes s) ->
  aread_ok stk W regs mem (bv_unsigned a3) (Z.of_nat (length s) + 1) ->
  65536 <= bv_unsigned a3 -> bv_unsigned a3 + Z.of_nat (length s) + 1 + 8 <= 0x9ebd8 ->
  0x5fc000 + PF_PCOM_DEPTH <= qpc -> qpc <= q - PF_SPILL -> q <= 2 ^ 47 ->
  (forall x : word, bv_unsigned x < 0x5fc000 -> m' x = NM.cjnormv ly R (w_H W) mem x) ->
  GAF.meta_kept (NM.cjnormv ly R (w_H W) mem) m' ->
  GPOP.va_area m' (q - PF_SPILL) ([a3; a4; a5; a6; a7] ++ []) ->
  PB.pcom_pre f (q - PF_SPILL) qpc m'.
Proof.
intros ly R W mem regs stk f q qpc s a3 a4 a5 a6 a7 m' HRO HPCX HinF HinS HSTR HRD Hf1 Hf2 HsSTR HsRD Hs1 Hs2
  HQ1 HQ2 HQ3 AG MK HVA.
unfold PF_PCOM_DEPTH, PF_SPILL in *.
destruct (pc_kept ly R W mem regs stk m' f 7 HinF HRD ltac:(lia)
            ltac:(unfold amem_range, kLowMemEnd; left; lia) MK) as [PFf HVf].
destruct (pc_kept ly R W mem regs stk m' (bv_unsigned a3) (Z.of_nat (length s) + 1) HinS HsRD ltac:(lia)
            ltac:(unfold amem_range, kLowMemEnd; left; lia) MK) as [PFs HVs].
assert (Lps : length (PFC.pf_bytes s) = length s) by (unfold PFC.pf_bytes; apply length_map).
exists [37; 115; 32; 37; 100; 32], [BzG.PA_s s; BzG.PA_i 0], [], [a3; a4; a5; a6; a7].
split; [reflexivity|].
split; [repeat constructor; lia|].
split; [cbn; lia|].
split.
{ (* the format's bytes *)
  exact (pc_bytes_low ly R W mem m' f (PFC.pf_bytes [37; 115; 32; 37; 100; 32] ++ [Z_to_bv 8 0]) HRO AG
           ltac:(lia) ltac:(cbn; lia) (proj1 HSTR)). }
split; [cbn [length]; lia|].
split; [lia|].
split.
{ (* the %s slot, above printf_common's window *)
  intros i w a Hw Ha Hsa.
  destruct i as [|[|i]]; cbn [nth_error] in Hw, Ha.
  - injection Hw as <-. injection Ha as <-.
    replace (q - 40 + 8 * Z.of_nat 0) with (q - 40) by lia.
    split; [exact (pc_slot0 m' (q - 40) a3 a4 a5 a6 a7 HVA) | right; lia].
  - injection Ha as <-. destruct Hsa.
  - destruct i; discriminate Ha. }
split; [lia|].
split; [cbn [length]; lia|].
split.
{ (* the %s string: its bytes, its place below printf_common's window, chkr from its hull *)
  change (BzL.ck_args m' (qpc - 2320) qpc [a3; a4; a5; a6; a7] [BzG.PA_s s; BzG.PA_i 0] [None; None]).
  cbn [BzL.ck_args BzG.vhd_cov tl]. split; [|split; [exact I | exact I]].
  cbn [BzL.ck_arg]. exists (PFC.pf_bytes s). rewrite Lps.
  split.
  { split; [|exact (proj2 HsSTR)].
    exact (pc_bytes_low ly R W mem m' (bv_unsigned a3) (PFC.pf_bytes s ++ [Z_to_bv 8 0]) HRO AG ltac:(lia)
             ltac:(rewrite length_app, Lps; cbn [length]; lia) (proj1 HsSTR)). }
  split; [lia|]. split; [left; lia|]. split; [lia|].
  exact (pc_chkr m' (bv_unsigned a3) (Z.of_nat (length s) + 1)
           (SRy.chk_ok_of_pf_rng_hull_m m' (bv_unsigned a3) (Z.of_nat (length s) + 1) (Z.of_nat (length s) + 1)
              PFs HVs ltac:(lia)) ltac:(lia) ltac:(lia) ltac:(lia) HVs). }
split.
{ (* the format's check *)
  exact (SRy.chk_ok_of_pf_rng_hull_m m' f 7 7 PFf HVf ltac:(lia)). }
(* printf_common's cells *)
exact (pc_pctx _ m' HPCX AG).
Qed.

End pcom.
