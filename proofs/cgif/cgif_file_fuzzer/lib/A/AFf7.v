(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import Logic.FunctionalExtensionality.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s YO0d.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YP0j.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YN3v YI04.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YK04 YA0i YA0n YA0o YA0p YA0q.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YG00 YG0a YG01 YG04 YG02 YG06 YG07 YG03 YG0f YG0v YG0n YG0d YG0s YG0q YG0o.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AB1v AB1q AB1t AF0l AF0m AF0x AFl0 AFl1.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YO0a.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AB1w AFeq AFex AFfu.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YFfj.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AFew AFeu AFfm AFf3 AFf4 AFff AFgu AFf5 AFgw AFfb AFgx AFfd AFgv AFg8 AFfc AFf6 AFfe AB13.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Ltac ceil := try (let H := fresh "CR" in let H2 := fresh "CR" in pose proof (proj1 (@YG0f.ASAN_CEIL_range _)) as H; pose proof H as H2; unfold YG0f.ASAN_CEIL in H2).
Local Set Warnings "-abstract-large-number".
Local Set Warnings "-notation-for-abbreviation".
Open Scope Z_scope.
Local Open Scope am_scope.
Set Printing Depth 100. Set Printing Width 200.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Ltac numconst := ceil; unfold zone3, zone3cases, TFIB_IMG_LO, kLowShadowBeg, kHighMemBeg, kHighMemEnd, ASAN_CEIL, kThreadObjSize, kSpaceSize, kPrimResvSize, kPtrArrayResv, kNodesBlockSize, kStoreBlockSize, t_qc, t_cache, t_cache_stats, t_unwinding, t_stats, KSTACK, TFIB_IMG_END, kBatchBytes, SHADOW_OFF, TFIB_TP, TFIB_TSD, TFIB_INST, A_ALLOCATOR, o_space, o_rinfo, o_sec, o_sec_chunks, o_sec_reserved, o_sec_n, o_sec_sorted, o_sec_stats, o_sec_mutex, kRegionInfoOff, kLowMemEnd, EV_MAX, kChunkHeaderSize, MALLOC_MAX, kPage, AFgu.GFRAME, AFgx.GFRAME, GDEPTH in *.
Ltac splits := repeat match goal with |- _ /\ _ => split end.
Ltac inS := cbn [In]; repeat (first [left; reflexivity | right]).
Section c.
Variable B : asyms.
Hypothesis TB : TfibSyms B.
Variables (ly : alayout) (X : astate) (k : chunk) (cbp : Z) (W : world tfibsegs) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model).
Variables (r : nat) (o : Z) (sm : secmap) (i : nat).
Hypothesis PRE : rcc_pre B ly X k cbp W regs mem md.
Hypothesis Hb : ck_beg k = PSec r o.
Hypothesis Hsm : nth_error (st_secs X) r = Some sm.
Hypothesis Hi : nth_error (st_sec_arr X) i = Some r.
Hypothesis HTSD : ly_tsd ly = TFIB_TSD.
Let sp0 : Z := bv_unsigned (getr regs 2).
Local Notation H0 := (w_H W).
Local Notation rd0 := (aview tfibsegs (w_H W) mem).
Local Notation m0 := (mrestrict (w_H W) mem).
Local Notation T := (ly_T ly).
Local Notation SB := (ly_space ly).
Local Notation Q := (ly_Q ly).
Local Notation MAP := (AFg8.MAP ly r).
Local Notation LEN := (AFg8.LEN sm).
Local Notation nA := (AFg8.nA X).
Local Notation hdr := (AFfc.hdr B ly k).
Local Notation HWv := (AFfc.HWv B ly k W mem).
Local Notation j1 := (AFfc.j1 ly W mem).
Local Notation j2 := (AFfc.j2 ly W mem).
Local Notation v := (AFf6.v regs).
Local Notation vra := (AFf6.v regs 1%bv).
Local Notation vs0 := (AFf6.v regs 8%bv).
Local Notation vs1 := (AFf6.v regs 9%bv).
Local Notation vs2 := (AFf6.v regs 18%bv).
Local Notation vs3 := (AFf6.v regs 19%bv).
Local Notation vs4 := (AFf6.v regs 20%bv).
Local Notation WINA := (AFf6.WINA regs).
Lemma M : ARm B ly X rd0. Proof. exact (proj1 (proj1 PRE)). Qed.
Definition WIND (a : Z) : Prop := WINA a \/ (T + t_stats + 40 <= a < T + t_stats + 56).
Definition MEQD (mm : word -> option byte) : Prop := forall x : word, ~ WIND (bv_unsigned x) -> mm x = mem x.
Definition PRED (regsD : bvmap 5 word) (memD : word -> option byte) : Prop :=
(forall r' : bv 5, In r' AFgv.SREGS -> getr regsD r' = getr regs r') /\
getr regsD 2 = getr regs 2 /\ getr regsD 1 = w64 vra /\ getr regsD 8 = w64 vs0 /\ getr regsD 9 = w64 vs1 /\ getr regsD 18 = w64 vs2 /\
getr regsD 10 = w64 (A_ALLOCATOR + 64) /\ getr regsD 11 = w64 (A_ALLOCATOR + 688) /\ getr regsD 12 = w64 (MAP + 4096) /\
MEQD memD /\
(forall a, sp0 - 80 <= a < sp0 -> apresent H0 memD a) /\
(forall a, T + t_stats + 40 <= a < T + t_stats + 56 -> apresent H0 memD a) /\
val_mem tfibsegs (mrestrict H0 memD) (A_ALLOCATOR + 680) 4 0.
Definition ATD (W' : world tfibsegs) (c' : config) : Prop :=
W' = W /\ exists regsD memD matD, c' = mkCfg (mkst regsD (w64 0x33b38) memD (seg_rom tfibsegs)) (with_vm_backing (m_vm_lazy md) matD md) /\ PRED regsD memD.
Theorem to_LMD : forall mat, SRr tfibsegs W (mkCfg (mkst regs (w64 A_RChunk) mem (seg_rom tfibsegs)) (with_vm_backing (m_vm_lazy md) mat md)) ATD.
Proof.
intros mat.
pose proof (AFfc.HI B TB ly X k cbp W regs mem md PRE) as (hP1 & hP2 & hQ1 & hQ2 & hT1 & hT2 & hC1 & hC2 & hS1 & hS2 & hCE & _).
pose proof (AFfc.HSP B ly X k cbp W regs mem md PRE) as [S1 S2].
eapply SRr_bind; [exact (AFf6.to_XG B TB ly X k cbp W regs mem md r o sm i PRE Hb Hsm Hi mat)|].
intros W1 c1 _ HX. destruct HX as (-> & regsX & memX & matX & -> & SX).
pose proof (AFfe.XSEED B TB ly X k cbp W regs mem md r o sm i PRE Hb Hsm Hi HTSD regsX memX SX) as FHX.
destruct SX as (regsL & PX & SR & R13).
destruct PX as (SRL & L2 & L1r & L8 & L9 & L10 & L11 & L12 & L13 & L14 & L19 & L20 & MQA & PRS & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & VM).
assert (X2 : getr regsX 2 = w64 (sp0 - 80)) by (rewrite (SR 2%bv ltac:(inS)); exact L2).
assert (USX : bv_unsigned (getr regsX 2) = sp0 - 80) by (rewrite X2; unfold w64; apply unsigned_lit_small; pose proof (u64_range (getr regs 2)); clear - S1 S2 hS1 hS2 H; numconst; subst sp0; lia).
eapply SRr_mono; [exact (AFfd.segGX W ly regsX memX md hdr MAP LEN HWv (ck_n k) j1 j2 cbp vra vs0 vs1 vs2 vs3 vs4 matX FHX)|].
intros W2 c2 _ HD. destruct HD as (-> & regsD & memD & matD & -> & DSR & D2 & D1 & D8 & D9 & D18 & D19 & D20 & D10 & D11 & D12 & MQX & DPRS & DMUT & DJ1 & DJ2).
rewrite USX in D2, DPRS. unfold AFgx.MEQ, AFgx.WIN in MQX. rewrite USX in MQX.
split; [reflexivity|]. exists regsD, memD, matD. split; [reflexivity|].
unfold PRED. splits.
- intros r' Hr'. unfold AFgv.SREGS in Hr'. cbn [In] in Hr'.
assert (CASE : r' = 19%bv \/ r' = 20%bv \/ In r' AFgx.SREGS).
{ unfold AFgx.SREGS. cbn [In]. clear - Hr'. intuition (subst; auto 20). }
destruct CASE as [-> | [-> | C]].
+ rewrite D19. unfold AFf6.v, w64. apply Z_to_bv_bv_unsigned.
+ rewrite D20. unfold AFf6.v, w64. apply Z_to_bv_bv_unsigned.
+ rewrite (DSR r' C). assert (C2 : In r' AFgw.SREGS /\ In r' AFgu.SREGS).
{ unfold AFgx.SREGS in C. unfold AFgw.SREGS, AFgu.SREGS. cbn [In] in C |- *. clear - C. intuition (subst; auto 40). }
destruct C2 as [C2 C3]. rewrite (SR r' C2). exact (SRL r' C3).
- rewrite D2. replace (sp0 - 80 + AFgx.GFRAME) with sp0 by (numconst; lia). unfold sp0, w64. apply Z_to_bv_bv_unsigned.
- exact D1.
- exact D8.
- exact D9.
- exact D18.
- exact D10.
- exact D11.
- exact D12.
- intros x Hx. unfold WIND, AFf6.WINA in Hx. fold sp0 in Hx. rewrite MQX by (clear - Hx; numconst; lia). apply MQA. unfold AFf6.WINA. fold sp0. clear - Hx. lia.
- intros a Ha. destruct (Z_lt_le_dec a (sp0 - 48)) as [LOW|HI'].
+ apply DPRS. lia.
+ apply (apresent_same (w_H W) memX); [|apply PRS; lia]. apply MQX. rewrite unsigned_lit_small by (clear - Ha S1 S2 hS1 hS2; numconst; lia).
clear - Ha HI' S1 S2 hS1 hCE hT1 hT2. numconst. lia.
- intros a Ha. assert (Ha' : off_img a) by (apply (zone3_off_img _ _ _ hT1); clear - Ha; unfold t_stats, kThreadObjSize in *; lia).
destruct (Z_lt_le_dec a (T + t_stats + 48)) as [LOW|HI'].
+ pose proof (DJ1 (Z.to_nat (a - (T + t_stats + 40))) ltac:(lia)) as Hb'. rewrite Z2Nat.id in Hb' by lia. replace (T + t_stats + 40 + (a - (T + t_stats + 40))) with a in Hb' by lia.
exact (mbyte_off_apresent (w_H W) memD a _ Ha' Hb').
+ pose proof (DJ2 (Z.to_nat (a - (T + t_stats + 48))) ltac:(lia)) as Hb'. rewrite Z2Nat.id in Hb' by lia. replace (T + t_stats + 48 + (a - (T + t_stats + 48))) with a in Hb' by lia.
exact (mbyte_off_apresent (w_H W) memD a _ Ha' Hb').
-
intros kk Hkk. destruct kk as [|kk'].
+ pose proof (DMUT 0%nat ltac:(lia)) as E0. cbn [Z.of_nat] in E0 |- *. rewrite le_byte_zero in *. exact E0.
+ rewrite (mbyte_mrestrict_same (w_H W) memX memD).
* pose proof (VM (S kk') Hkk) as E1. rewrite E1. f_equal. f_equal. rewrite le_byte_zero.
unfold YO0f.le_byte. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ (8 * Z.of_nat 4)) with 4294967296. rewrite Z.mod_small by lia.
rewrite Z.div_small; [reflexivity|]. split; [lia|]. eapply Z.lt_le_trans with (2 ^ 8); [lia|]. apply Z.pow_le_mono_r; lia.
* apply MQX. unfold A_ALLOCATOR. rewrite unsigned_lit_small by lia. clear - Hkk S1 hS1 hT1. numconst. lia.
Qed.
End c.
End b.
