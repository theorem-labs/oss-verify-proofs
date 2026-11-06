(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: from proofs/cgif/cgif_file_fuzzer/lib/DMcdGWb.v (commit 67fc7ef5787c2195464dbe4d4f7905278328dc0c, CacheDealloc walk (H3 DMcd* + FG*N, a Theorem Labs lane's DMcdGWb / DMcdGW); file sha256 475b67822732) onto plugin-hostd/fuzz_reply's asan image (unstripped fuzz_reply.asan, sha256 d751b179ea49; pin 42c58610e125); module paths changed; its 1 image addresses moved by code-verified function pairs (1 port_addr_check e55e1b52a8a0 MAPS predictions, each code one re-derived by funcpair.py; 0 code pcs the tool read as sizes, by funcpair.py), and 7 pcs named in comments; 1 hand maps (each with its evidence: pinned image bytes, YImgTop, the unit AF twin); no other numeral changed. *)
(* Theorem Labs, 2026-10-30, a Theorem Labs lane (lane B1 slice H3, W2 of CacheDealloc's growth arm): the BRIDGE from
   EnsureFreeArraySpace's growth leaf (FGtN.efa_leafT_lk, back at ReturnToAllocator's 0x348d0) to the symbolic state
   [SS3] from which the released YFgz.segK2 tail (lib/YFgz.v:313-523: run to 0x348e8, YFep.cpyk_stretch, ...) is
   ported in DMcdGW.v.  [SS3] is W1's closed state DMcdK.K9 after the call (YI04.st_ok_after_call): the regions EFA's
   frame XG cannot touch kept (the caller frames sp0 - 240 .. sp0 and the image constants), the caller-saved registers
   havocked from atom 54 (= aHAVf), a0 = 1, and the cells inside XG that the tail touches re-added from the leaf: RG+0
   (the lock word 2^60), RG+16 (writable), RG+24 (the grown size mf + kFreeArrayMapSize), RG+80 / RG+88, the cache
   header Pr+0 / Pr+8, the stats word T+2784 and the frame below (sp0 - 320 .. sp0 - 240).  The destination's
   presence: the old part [DSTv, FAv + mf) from DMcdGk.fh_full, unchanged by EFA; the new part from the grant.
   rule 24: proves function SizeClassAllocator64LocalCache::Deallocate (growth-arm tail); reuse: port of YFgz.segK2's
   tail (released, no-growth arm); `proof-index ReturnToAllocator EnsureFreeArraySpace 0x348d0 0x3476c`
   2026-10-30T01:1xZ exit 4: no released growth-arm walk. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s YO0d.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YP0j.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0p YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0v YG0n YG0d YG0s YG06.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import AB1v AB1q AB1t AF0l AF0m AF0x AFl0 AFl1.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YO0a.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import AB1w AFeq AFew AFeu AFep AFeo AFgo AFh2 AFfo DMcdGk.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require DMcdK DMcdGI FGsN FGtN FGcN FGwN AFk5 AFkn.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Ltac ceil := try (let H := fresh "CR" in let H2 := fresh "CR" in pose proof (proj1 (@YG0f.ASAN_CEIL_range _)) as H; pose proof H as H2; unfold YG0f.ASAN_CEIL in H2).
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Set Printing Depth 100. Set Printing Width 200.
Local Ltac numconst := ceil; unfold zone3, zone3cases, TFIB_IMG_LO, kLowShadowBeg, kHighMemBeg, kHighMemEnd, ASAN_CEIL, kThreadObjSize, kSpaceSize, kPrimResvSize, kNodesBlockSize, kStoreBlockSize, t_qc, t_cache, t_cache_stats, t_unwinding, t_stats, ASTACK, QSTACK, RSTACK, DSTACK, KSTACK, TFIB_IMG_END, kBatchBytes, kBatchSlots, SHADOW_OFF, TFIB_TP, TFIB_TSD, A_QUAR, A_ALLOCATOR, o_quar, kRegionInfoOff, kFreeArrayOffset, kFreeArrayMax, kMaxSize, kUserMapSize, kFreeArrayMapSize, AFk5.SHBv in *.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* The symbolic state at 0x348d0 after the call (closed).                                                            *)
(* ---------------------------------------------------------------------------------------------------------------- *)
Definition A_RTA_RET : Z := 0x348d0.
(* the first atom the call's havoc writes (= YFeq.aHAVf; every atom of DMcdK.K9 is below 50) *)
Definition kE3 : nat := 54.
(* K9's regions EFA's frame cannot touch: index 3, the caller frames sp0 - 240 .. sp0 (saved registers), and the six
   image constants at indices 7 .. 12 *)
Definition RS3 : smem := Eval vm_compute in
  nth 3 (ss_mem DMcdK.K9) (YP09.mkRegion None 0 0 0 0 []) :: skipn 7 (ss_mem DMcdK.K9).
(* the cells re-added from the leaf (K9's regions 0 / 1 / 2 / 5 / 6 / 4, with the leaf's values) *)
Definition R_RGA3 : YP09.region := YP09.mkRegion (Some 41%nat) 0 8 0 8 [YP09.mkChunk 0 (CVal 8 (SLit FGsN.LOCKV))].
Definition R_RGB3 : YP09.region := YP09.mkRegion (Some 41%nat) 8 80 16 24 [YP09.mkChunk 24 (CVal 8 (SOff 43%nat kFreeArrayMapSize))].
Definition R_PC3 : YP09.region := YP09.mkRegion (Some 36%nat) 0 16 0 4
  [YP09.mkChunk 0 (CVal 4 (SAlu ALU_SUB (SOff 37%nat 0) (SAlu ALU_SRL (SOff 38%nat 0) (SLit 1)))); YP09.mkChunk 8 (CVal 8 (SOff 39%nat 0))].
Definition ADD3 : smem := [R_RGA3; R_RGB3; DMcdGk.R_RGC; R_PC3; DMcdGk.R_JST; DMcdGk.R_STK_LO].
Definition SS3 : sstate := Eval vm_compute in
  mkSS A_RTA_RET (sr_set (sr_sets (ss_regs DMcdK.K9) (junk_upd kE3 CLOB)) 10%bv (SLit 1)) (ADD3 ++ RS3) None (ss_facts DMcdK.K9).

(* A region whose bytes are equal in two memories is kept. *)
Lemma region_kept_eq : forall E (m m' : word -> option byte) r,
  (forall a, base_val E (YP09.r_base r) + YP09.r_lo r <= a < base_val E (YP09.r_base r) + YP09.r_hi r ->
     m' (Z_to_bv 64 a) = m (Z_to_bv 64 a)) ->
  (YP09.r_whi r <= YP09.r_wlo r \/ (YP09.r_lo r <= YP09.r_wlo r /\ YP09.r_whi r <= YP09.r_hi r)) ->
  region_kept tfibsegs E m m' r.
Proof.
  intros E m m' r H Hw. split; intros a Ha.
  - unfold mbyte. rewrite (H a Ha). reflexivity.
  - intros Hwr. destruct Hw as [Hw|[Hw1 Hw2]]; [lia|].
    unfold writable_at, wview in *. rewrite (H a ltac:(lia)). exact Hwr.
Qed.

(* Bytes of a value read off the image are present. *)
Lemma val_mem_apresent : forall (H : word -> bool) (m : word -> option byte) a (n : nat) v,
  val_mem tfibsegs (mrestrict H m) a n v -> (forall b, a <= b < a + Z.of_nat n -> off_img b) ->
  forall b, a <= b < a + Z.of_nat n -> apresent H m b.
Proof.
  intros H m a n v Hv Hoff b Hb.
  pose proof (Hv (Z.to_nat (b - a)) ltac:(lia)) as E. rewrite Z2Nat.id in E by lia.
  replace (a + (b - a)) with b in E by lia.
  unfold mbyte, mrestrict, apresent in *.
  destruct (H (Z_to_bv 64 b)) eqn:Hh.
  - rewrite (seg_rom_none_off b (Hoff b Hb)) in E. discriminate.
  - split; [reflexivity|]. destruct (m (Z_to_bv 64 b)) as [x|] eqn:Hm; [exists x; reflexivity|].
    rewrite (seg_rom_none_off b (Hoff b Hb)) in E. discriminate.
Qed.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Section WB.
Variables (W : world tfibsegs) (ly : alayout).
Variables (regs0 : bvmap 5 word) (mem0 : word -> option byte) (md0 : Model).
Variables (c off cnt old mf j80 j88 jst : Z) (X : astate).
Local Notation sp0 := (bv_unsigned (getr regs0 2)).
Local Notation T := (ly_T ly).
Local Notation SB := (ly_space ly).
Hypothesis FH : free_hyps W ly regs0 mem0 c off cnt old mf j80 j88 jst.
Local Notation Pv := (DMcdGk.Pv ly off).
Local Notation PCv := (DMcdGk.PCv ly c).
Local Notation MAXv := (DMcdGk.MAXv c).
Local Notation SZv := (DMcdGk.SZv c).
Local Notation Nv := (DMcdGk.Nv c).
Local Notation CNTPv := (DMcdGk.CNTPv c cnt).
Local Notation SLOTv := (DMcdGk.SLOTv ly c cnt).
Local Notation RIv := (DMcdGk.RIv ly).
Local Notation RGv := (DMcdGk.RGv ly c).
Local Notation RBv := (DMcdGk.RBv ly c).
Local Notation FAv := (DMcdGk.FAv ly c).
Local Notation DSTv := (DMcdGk.DSTv ly c old).
Local Notation SRCv := (DMcdGk.SRCv ly c cnt).
Local Notation E0 := (DMcdGk.E0 ly regs0 c off cnt old mf j80 j88 jst).
Local Notation E2 := (DMcdGk.E2 ly regs0 c off cnt old mf j80 j88 jst).
Local Notation EqT := (DMcdGk.EqT ly regs0 c off cnt old mf j80 j88 jst).
Local Notation EqC := (DMcdGk.EqC ly regs0 c off cnt old mf j80 j88 jst).
Local Notation EqPC := (DMcdGk.EqPC ly regs0 c off cnt old mf j80 j88 jst).
Local Notation EqCNT := (DMcdGk.EqCNT ly regs0 c off cnt old mf j80 j88 jst).
Local Notation EqMAX := (DMcdGk.EqMAX ly regs0 c off cnt old mf j80 j88 jst).
Local Notation EqSZ := (DMcdGk.EqSZ ly regs0 c off cnt old mf j80 j88 jst).
Local Notation EqRG := (DMcdGk.EqRG ly regs0 c off cnt old mf j80 j88 jst).
Local Notation EqMF := (DMcdGk.EqMF ly regs0 c off cnt old mf j80 j88 jst).
Local Notation EqJ80 := (DMcdGk.EqJ80 ly regs0 c off cnt old mf j80 j88 jst).
Local Notation EqJ88 := (DMcdGk.EqJ88 ly regs0 c off cnt old mf j80 j88 jst).
Local Notation EqJST := (DMcdGk.EqJST ly regs0 c off cnt old mf j80 j88 jst).
Local Notation LYB := (DMcdGk.LYB W ly regs0 mem0 c off cnt old mf j80 j88 jst FH).
Local Notation class_facts := (DMcdGk.class_facts W ly regs0 mem0 c off cnt old mf j80 j88 jst FH).
Local Notation derived_ranges := (DMcdGk.derived_ranges W ly regs0 mem0 c off cnt old mf j80 j88 jst FH).
Local Notation WINX := (DMcdGk.WINX ly regs0 c cnt).
Local Notation DST_notWINX := (DMcdGk.DST_notWINX W ly regs0 mem0 c off cnt old mf j80 j88 jst FH).
Local Notation SRC_notWINX := (DMcdGk.SRC_notWINX W ly regs0 mem0 c off cnt old mf j80 j88 jst FH).
Local Notation off_T := (DMcdGk.off_T W ly regs0 mem0 c off cnt old mf j80 j88 jst FH).
Local Ltac open_FH := pose proof FH as FH_; destruct FH_ as [LY IMG Htp Hra Hra4096 Hsp Hsp_al Hpres Hc Hcnt Hoff Hslot Hjunk Hfull SEED].
Local Ltac off_by tac :=
first [ apply off_img_high; tac | apply off_T; unfold kThreadObjSize, t_qc, t_cache, t_cache_stats; tac | unfold off_img; unfold TFIB_IMG_LO; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, TFIB_IMG_END; tac ].
Local Ltac reg_zevK HS r tac :=
let Q := fresh "Q" in
pose proof (st_ok_reg_denot _ _ _ _ r HS) as Q; cbn [ms_regs restrict mkst] in Q;
lazymatch type of Q with _ = sv_denot _ (sr_get ?sr ?rr) => let t := eval vm_compute in (sr_get sr rr) in change (sr_get sr rr) with t in Q end;
rewrite Q; clear Q;
apply denot_by_zev; [ reflexivity | tac
| cbn [zev zalu_raw zmd_raw]; unfold zalu_raw, zmd_raw; rewrite ?Z.add_0_r;
repeat match goal with R : rho_of _ ?k = _ |- context [rho_of _ ?k] => rewrite R end; land_lits;
repeat match goal with |- context [Z.land (zcanon ?k) 63] => let cc := eval vm_compute in (Z.land (zcanon k) 63) in change (Z.land (zcanon k) 63) with cc end;
rewrite ?Z.shiftl_mul_pow2, ?Z.shiftr_div_pow2 by zlia; tac ].

(* The pre of the ported segK2 stretch at 0x348d0: the closed state [SS3] under an environment that agrees with the
   seed's on the seed atoms, the destination and the source present in the grown world, and the source's bytes equal
   to the entry's (the copy's values). *)
Definition w2_pre (W3 : world tfibsegs) (regs3 : bvmap 5 word) (mem3 : word -> option byte) : Prop :=
  exists E3 : env,
    (forall k, (k < aHAVf)%nat -> ew E3 k = ew E0 k) /\
    st_ok tfibsegs E3 SS3 (restrict (w_H W3) (mkst regs3 (Z_to_bv 64 A_RTA_RET) mem3 (seg_rom tfibsegs))) /\
    (forall a, DSTv <= a < DSTv + 4 * Nv -> apresent (w_H W3) mem3 a) /\
    (forall a, SRCv <= a < SRCv + 4 * Nv -> apresent (w_H W3) mem3 a) /\
    (forall x : word, SRCv <= bv_unsigned x < SRCv + 4 * Nv -> mem3 x = mem0 x).

Lemma w2_bridge : cnt = MAXv -> rg_mapped_fa (reg X c) = mf -> mf < 4 * (old + Nv) ->
  forall c9, DMcdGI.at_EFA W ly regs0 mem0 md0 c off cnt old mf j80 j88 jst c9 ->
  forall regs9 mem9 md9, c9 = cfg_at tfibsegs FGsN.A_EFA regs9 mem9 md9 ->
  forall r W' c', FGtN.efa_leafT_lk ly X W regs9 mem9 md9 c (old + Nv) j80 j88 jst old (rg_alloc_user (reg X c)) (rg_mapped_user (reg X c)) r W' c' ->
  snd r = upd_reg c (FGcN.rgG (reg X c)) X /\
  exists regs3 mem3 mdx,
    c' = mkCfg (mkst regs3 (Z_to_bv 64 A_RTA_RET) mem3 (seg_rom tfibsegs)) mdx /\ w2_pre W' regs3 mem3.
Proof.
intros HFULL HX HGROW c9 HEFA regs9 mem9 md9 Hc9 r W' c' HLEAF.
open_FH. pose proof Hwx_tfa as Hwx. destruct Hsp as [Hlo Hhi]. pose proof LYB as LB.
pose proof derived_ranges as DR.
pose proof DR as (dT1 & dT2 & dS1 & dS2 & dSal & dK1 & dK2 & dP1 & dP2 & dPal & dC1 & dC2 & dCal & [dN1 dN2] & [dQ1 dQ2] & dL1 & dL2 & dI1 & dI2 & dG0 & dG1 & dG2 & dI3 & dB0 & dB1 & dB2 & dF0 & [dJ1 dJ2] & [dJ3 dJ4] & [dJ5 dJ6]).
pose proof class_facts as KF. pose proof KF as (K1 & K2 & K3 & K4 & K5 & K6 & K7 & K8 & K9).
assert (Usp : 0 <= sp0 < 2 ^ 64) by apply u64_range.
destruct (Hfull HFULL) as (F1 & F2 & F3 & F4 & Frg & Vmx & Vold & Vmf & V80 & V88 & Psrc & Pold).
(* W1's leaf *)
destruct HEFA as (ms9 & mat9 & E & Hc9e & HEa & HS9 & MQ9).
rewrite Hc9 in Hc9e. unfold cfg_at in Hc9e. injection Hc9e as Hms9 _. subst ms9.
assert (R2 : rho_of E 2%nat = sp0) by (unfold rho_of; rewrite (HEa 2%nat ltac:(cbv; lia)), E2; reflexivity).
assert (R32 : rho_of E 32%nat = T) by (unfold rho_of; rewrite (HEa 32%nat ltac:(cbv; lia)), EqT; unfold w64; apply unsigned_lit_small; clear - LB; numconst; zlia).
(* registers at EFA's entry *)
assert (RA9 : getr regs9 1 = Z_to_bv 64 A_RTA_RET).
{ let Q := fresh "Q" in pose proof (st_ok_reg_denot _ _ _ _ 1%bv HS9) as Q; cbn [ms_regs restrict mkst] in Q; rewrite Q; vm_compute; reflexivity. }
assert (SP9 : getr regs9 2 = Z_to_bv 64 (sp0 - 240)).
{ reg_zevK HS9 (2%bv : bv 5) ltac:(clear - Usp dK1 Hlo LB; numconst; zcanon_simp; unfold zcanon, M64; zlia). }
assert (USP9 : bv_unsigned (getr regs9 2) = sp0 - 240) by (rewrite SP9; apply unsigned_lit_small; clear - Usp dK1; numconst; zlia).
(* EFA's leaf: the growth disjunct *)
unfold FGtN.efa_leafT_lk in HLEAF. destruct HLEAF as (j68 & _ & HLEAF). unfold FGcN.efa_leaf in HLEAF.
destruct HLEAF as [_ [(Hng & _ & _) | (_ & Hsnd & matN & W3 & _ & _ & _ & Hhid & Hsame & _ & _ & _ & _ & _ & HRET)]].
{ exfalso. rewrite HX in Hng. clear - Hng HGROW. unfold DMcdGk.Nv, DMcdGk.MAXv in *. lia. }
split; [exact Hsnd|].
destruct HRET as (HW' & regs3 & mem3 & mat3 & Hc' & Ha0 & Hcs & Hfr & Hstk & HP).
subst W'.
destruct HP as [[[_ [Hgr Hshr]] _] [Hpmf (Lk0 & Lk80 & Lk88 & Lkp & Lks & Lkt & Lkpres & _)]].
rewrite RA9 in Hc'. exists regs3, mem3. eexists. split; [exact Hc'|].
rewrite HX in *.
unfold AFk5.RGv, AFk5.Pr, AFk5.FAv, AFk5.RBv in *.
rewrite USP9 in Hstk.
set (fadr := ly_space ly + c * 2 ^ 32 + kFreeArrayOffset + mf) in *.
assert (HFA : FAv = fadr - mf) by (unfold fadr, DMcdGk.FAv, DMcdGk.RBv; rewrite K8; lia).
(* the free-array map lies in the high space, its shadow in the high shadow *)
assert (FA1 : ly_space ly + 2 ^ 32 + kFreeArrayOffset <= fadr /\ fadr + kUserMapSize <= ly_space ly + 32 * 2 ^ 32).
{ unfold fadr. clear - Hc F1 F2 F3. unfold kFreeArrayOffset, kFreeArrayMax, kUserMapSize in *. lia. }
assert (SH1 : 0 <= fadr / 8) by (apply Z.div_pos; [clear - FA1 dS1; numconst; lia | lia]).
assert (SH2 : fadr / 8 < 0x0fffffff0000).
{ apply Z.div_lt_upper_bound; [lia|]. destruct LB as (_ & _ & _ & _ & LS & LP & _). clear - FA1 LS LP. numconst. lia. }
(* the memory at 0x348d0 and the entry's world outside EFA's frame and the new map *)
assert (NXG : forall a, 0 <= a < 2 ^ 64 ->
  ~ (sp0 - 240 - RSTACK <= a < sp0 - 240) -> ~ (T + t_cache + 80 * c <= a < T + t_cache + 80 * c + 16) ->
  ~ (RGv <= a < RGv + 128) -> ~ (T + 2768 <= a < T + 2800) -> ~ (T + 2872 <= a < T + 2888) ->
  ~ (fadr <= a < fadr + kUserMapSize) -> ~ (AFk5.SHBv + fadr / 8 <= a < AFk5.SHBv + fadr / 8 + 32768) ->
  mem3 (Z_to_bv 64 a) = mem9 (Z_to_bv 64 a)).
{ intros a Ha N1 N2 N3 N4 N5 N6 N7. apply Hfr.
  unfold FGcN.XG, AFk5.WINR0, AFkn.RANGE, AFk5.W_FSH, AFk5.Pr, AFk5.RGv. rewrite unsigned_lit_small by lia. rewrite USP9.
  intros HX'. destruct HX' as [[[HX'|[HX'|[HX'|[HX'|HX']]]]|HX']|HX'].
  - exact (N1 HX').
  - exact (N2 HX').
  - apply N3. unfold DMcdGk.RGv, DMcdGk.RIv. exact HX'.
  - exact (N4 HX').
  - exact (N5 HX').
  - exact (N6 HX').
  - apply N7. unfold kFreeArrayMapSize in HX'. change (262144 / 8) with 32768 in HX'. exact HX'. }
assert (OUT : forall a, 0 <= a < 2 ^ 64 ->
  ~ (sp0 - 240 - RSTACK <= a < sp0 - 240) -> ~ (T + t_cache + 80 * c <= a < T + t_cache + 80 * c + 16) ->
  ~ (RGv <= a < RGv + 128) -> ~ (T + 2768 <= a < T + 2800) -> ~ (T + 2872 <= a < T + 2888) ->
  ~ (fadr <= a < fadr + kUserMapSize) -> ~ (AFk5.SHBv + fadr / 8 <= a < AFk5.SHBv + fadr / 8 + 32768) ->
  mrestrict (w_H W3) mem3 (Z_to_bv 64 a) = mrestrict (w_H W) mem9 (Z_to_bv 64 a)).
{ intros a Ha N1 N2 N3 N4 N5 N6 N7. unfold mrestrict.
  rewrite Hsame by (unfold AFkn.RANGE, AFkn.SHR; rewrite unsigned_lit_small by lia; first [exact N6 | exact N7]).
  rewrite (NXG a Ha N1 N2 N3 N4 N5 N6 N7). reflexivity. }
cbn [ms_mem mkst] in MQ9.
assert (BV2E : bv_unsigned (ew E 2) = sp0) by exact R2.
(* the call: K9's kept regions, the callee-saved registers *)
assert (SUB : submem RS3 (ss_mem DMcdK.K9)).
{ unfold RS3. cbn [DMcdK.K9 ss_mem].
  apply submem_drop; apply submem_drop; apply submem_drop; apply submem_keep; [apply subregion_refl|].
  apply submem_drop; apply submem_drop; apply submem_drop; apply submem_refl. }
assert (HPRES : regs_preserved (ms_regs (restrict (w_H W) (mkst regs9 (w64 FGsN.A_EFA) mem9 (seg_rom tfibsegs)))) regs3).
{ cbn [ms_regs restrict mkst]. intros rz Hrz. unfold callee_saved in Hrz. apply Hcs.
  assert (Hz : rz = 2 \/ rz = 3 \/ rz = 4 \/ rz = 8 \/ rz = 9 \/ rz = 18 \/ rz = 19 \/ rz = 20 \/ rz = 21 \/ rz = 22 \/
    rz = 23 \/ rz = 24 \/ rz = 25 \/ rz = 26 \/ rz = 27) by lia.
  repeat (destruct Hz as [->|Hz]; [cbn [In]; repeat first [left; apply bv_eq; reflexivity | right]|]);
  subst rz; cbn [In]; repeat first [left; apply bv_eq; reflexivity | right]. }
assert (HKEPT : Forall (region_kept tfibsegs E (ms_mem (restrict (w_H W) (mkst regs9 (w64 FGsN.A_EFA) mem9 (seg_rom tfibsegs))))
  (mrestrict (w_H W3) mem3)) RS3).
{ cbn [ms_mem restrict mkst]. unfold RS3.
  repeat apply Forall_cons; try apply Forall_nil; apply region_kept_eq;
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val]; rewrite ?BV2E;
  first [ left; lia | right; split; lia
        | intros a Ha; apply OUT; clear - LB Hlo Hhi Hc FA1 SH1 SH2 Usp Ha; unfold DMcdGk.RGv, DMcdGk.RIv; numconst; lia ]. }
pose proof (st_ok_after_call tfibsegs kE3 E DMcdK.K9 _ regs3 (mrestrict (w_H W3) mem3) RS3 A_RTA_RET HS9
  ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
  ltac:(vm_compute; reflexivity) SUB ltac:(vm_compute; reflexivity) HPRES HKEPT) as HS.
clear HS9 SUB HPRES HKEPT.
change (mkst regs3 (Z_to_bv 64 A_RTA_RET) (mrestrict (w_H W3) mem3) (seg_rom tfibsegs))
  with (restrict (w_H W3) (mkst regs3 (Z_to_bv 64 A_RTA_RET) mem3 (seg_rom tfibsegs))) in HS.
set (E3 := havoc E kE3 (map (getr regs3) CLOB)) in HS.
assert (HE3 : forall k, (k < aHAVf)%nat -> ew E3 k = ew E0 k).
{ intros k Hk. unfold E3. rewrite ew_havoc_old by (unfold kE3, aHAVf in *; lia). apply HEa. exact Hk. }
lazymatch type of HS with st_ok _ _ ?ss _ => let ss' := eval vm_compute in ss in change ss with ss' in HS end.
assert (B2 : bv_unsigned (ew E3 2) = sp0) by (rewrite HE3 by (cbv; lia); rewrite E2; reflexivity).
assert (B32 : bv_unsigned (ew E3 32) = T) by (rewrite HE3 by (cbv; lia); rewrite EqT; unfold w64; apply unsigned_lit_small; clear - LB; numconst; zlia).
assert (B36 : bv_unsigned (ew E3 36) = PCv) by (rewrite HE3 by (cbv; lia); rewrite EqPC; unfold w64; apply unsigned_lit_small; clear - dT1 dT2 dS1 dS2 dP1 dP2 dC1 dC2 dL1 dL2 K1; numconst; zlia).
assert (B41 : bv_unsigned (ew E3 41) = RGv) by (rewrite HE3 by (cbv; lia); rewrite EqRG; unfold w64; apply unsigned_lit_small; clear - dG0 dG1 dG2 dI1 dI3; numconst; zlia).
assert (R37 : rho_of E3 37%nat = cnt) by (unfold rho_of; rewrite HE3 by (cbv; lia); rewrite EqCNT; unfold w64; apply unsigned_lit_small; clear - Hcnt K3; zlia).
assert (R38 : rho_of E3 38%nat = MAXv) by (unfold rho_of; rewrite HE3 by (cbv; lia); rewrite EqMAX; unfold w64; apply unsigned_lit_small; clear - K3; zlia).
(* re-add the cells the tail touches inside EFA's frame, from the leaf *)
apply (st_ok_add_region _ _ _ DMcdGk.R_STK_LO) in HS;
[ | reflexivity
| unfold DMcdGk.R_STK_LO, YP09.region_ok; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict mkst]; rewrite B2;
  split; [clear - Usp dK1; numconst; zlia|]; split; [clear - Usp; zlia|];
  split; [intros o Ho; apply apresent_writable_off; [off_by ltac:(clear - Usp dK1 Ho; numconst; zlia) | apply Hstk; clear - Ho; unfold RSTACK; lia] | apply Forall_nil]
| try unfold DMcdGk.R_STK_LO; try unfold DMcdGk.R_JST; try unfold R_PC3; try unfold DMcdGk.R_RGC; try unfold R_RGB3; try unfold R_RGA3;
  cbn [YP09.all_disjoint ss_mem]; unfold YP09.extent_disjoint; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]; rewrite ?B2;
  clear - Usp dK1 Hlo Hhi LB; numconst; repeat split; zlia ].
cbn [ss_pc ss_regs ss_mem ss_resv ss_facts] in HS.
apply (st_ok_add_region _ _ _ DMcdGk.R_JST) in HS;
[ | reflexivity
| unfold DMcdGk.R_JST, YP09.region_ok; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict mkst]; rewrite B32;
  split; [clear - dT1 dT2; numconst; zlia|]; split; [clear - dT1 dT2; numconst; zlia|];
  split; [intros o Ho; apply apresent_writable_off;
          [ off_by ltac:(clear - Ho dT1 dT2; numconst; zlia)
          | apply (val_mem_apresent _ _ (T + 2784) 8 jst Lkt); [intros b Hb; off_by ltac:(clear - Hb dT1 dT2; numconst; zlia) | clear - Ho; unfold t_cache in Ho; cbn; lia] ] |];
  apply Forall_cons; [eapply chunk_ok_val with (v := jst); [cbn [sv_denot]; rewrite HE3 by (cbv; lia); rewrite EqJST; unfold w64; rewrite Zbv_add_unsigned; f_equal; zlia | clear - Hjunk; cbn; zlia | cbn; zlia | exact Lkt] | apply Forall_nil]
| try unfold DMcdGk.R_STK_LO; try unfold DMcdGk.R_JST; try unfold R_PC3; try unfold DMcdGk.R_RGC; try unfold R_RGB3; try unfold R_RGA3;
  cbn [YP09.all_disjoint ss_mem]; unfold YP09.extent_disjoint; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]; rewrite ?B2, ?B32;
  clear - Usp dK1 Hlo Hhi LB dT1 dT2; numconst; repeat split; zlia ].
cbn [ss_pc ss_regs ss_mem ss_resv ss_facts] in HS.
apply (st_ok_add_region _ _ _ R_PC3) in HS;
[ | reflexivity
| unfold R_PC3, YP09.region_ok; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict mkst]; rewrite B36;
  split; [clear - dC1 dC2 dT1 dT2; numconst; zlia|]; split; [clear - dC1 dC2 dT1 dT2; numconst; zlia|];
  split; [intros o Ho; apply apresent_writable_off;
          [ off_by ltac:(clear - Ho dC1 dC2 dT1 dT2; numconst; zlia)
          | apply (val_mem_apresent _ _ (PCv + 0) 4 _ Lkp); [intros b Hb; off_by ltac:(clear - Hb dC1 dC2 dT1 dT2; numconst; zlia) | clear - Ho; cbn; lia] ] |];
  apply Forall_cons;
  [ eapply chunk_ok_val with (v := Nv);
    [ apply denot_by_zev; [ reflexivity | clear - K5; zlia
      | cbn [zev zalu_raw zmd_raw]; unfold zalu_raw, zmd_raw; rewrite ?Z.add_0_r; rewrite R37, R38, HFULL;
        unfold DMcdGk.Nv, DMcdGk.MAXv in *; clear - K3 K4 K5 K6;
        rewrite (zcanon_id (max_cached c)) by (unfold M64; lia); rewrite (zcanon_id 1) by (unfold M64; lia);
        change (Z.land 1 63) with 1; rewrite Z.shiftr_div_pow2 by lia; change (2 ^ 1) with 2;
        rewrite (zcanon_id (max_cached c / 2)) by (unfold M64; lia); rewrite zcanon_id by (unfold M64; lia); lia ]
    | clear - K5; cbn; zlia | cbn; zlia | exact Lkp ] |];
  apply Forall_cons; [eapply chunk_ok_val with (v := SZv); [cbn [sv_denot]; rewrite HE3 by (cbv; lia); rewrite EqSZ; unfold w64; rewrite Zbv_add_unsigned; f_equal; zlia | clear - K1; cbn; numconst; zlia | cbn; zlia | exact Lks] | apply Forall_nil]
| try unfold DMcdGk.R_STK_LO; try unfold DMcdGk.R_JST; try unfold R_PC3; try unfold DMcdGk.R_RGC; try unfold R_RGB3; try unfold R_RGA3;
  cbn [YP09.all_disjoint ss_mem]; unfold YP09.extent_disjoint; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]; rewrite ?B2, ?B32, ?B36;
  clear - Usp dK1 Hlo Hhi LB dT1 dT2 dC1 dC2; numconst; repeat split; zlia ].
cbn [ss_pc ss_regs ss_mem ss_resv ss_facts] in HS.
apply (st_ok_add_region _ _ _ DMcdGk.R_RGC) in HS;
[ | reflexivity
| unfold DMcdGk.R_RGC, YP09.region_ok; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict mkst]; rewrite B41;
  split; [clear - dG0 dG1 dG2 dI1 dI3; numconst; zlia|]; split; [clear - dG0 dG1 dG2 dI1 dI3; numconst; zlia|];
  split; [intros o Ho; apply apresent_writable_off; [off_by ltac:(clear - dG0 dG1 dG2 dI1 dI3 Ho; numconst; zlia) | apply Lkpres; unfold DMcdGk.RGv, DMcdGk.RIv; lia]|];
  apply Forall_cons; [eapply chunk_ok_val with (v := j80); [cbn [sv_denot]; rewrite HE3 by (cbv; lia); rewrite EqJ80; unfold w64; rewrite Zbv_add_unsigned; f_equal; zlia | clear - Hjunk; cbn; zlia | cbn; zlia | exact Lk80]|];
  apply Forall_cons; [eapply chunk_ok_val with (v := j88); [cbn [sv_denot]; rewrite HE3 by (cbv; lia); rewrite EqJ88; unfold w64; rewrite Zbv_add_unsigned; f_equal; zlia | clear - Hjunk; cbn; zlia | cbn; zlia | exact Lk88]|];
  apply Forall_nil
| try unfold DMcdGk.R_STK_LO; try unfold DMcdGk.R_JST; try unfold R_PC3; try unfold DMcdGk.R_RGC; try unfold R_RGB3; try unfold R_RGA3;
  cbn [YP09.all_disjoint ss_mem]; unfold YP09.extent_disjoint; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]; rewrite ?B2, ?B32, ?B36, ?B41;
  clear - Usp dK1 Hlo Hhi LB dT1 dT2 dS1 dS2 dC1 dC2 dL1 dL2 dI1 dI2 dG0 dG1 dG2 dI3; numconst; repeat split; zlia ].
cbn [ss_pc ss_regs ss_mem ss_resv ss_facts] in HS.
apply (st_ok_add_region _ _ _ R_RGB3) in HS;
[ | reflexivity
| unfold R_RGB3, YP09.region_ok; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict mkst]; rewrite B41;
  split; [clear - dG0 dG1 dG2 dI1 dI3; numconst; zlia|]; split; [clear - dG0 dG1 dG2 dI1 dI3; numconst; zlia|];
  split; [intros o Ho; apply apresent_writable_off; [off_by ltac:(clear - dG0 dG1 dG2 dI1 dI3 Ho; numconst; zlia) | apply Lkpres; unfold DMcdGk.RGv, DMcdGk.RIv; lia]|];
  apply Forall_cons; [eapply chunk_ok_val with (v := mf + kFreeArrayMapSize); [cbn [sv_denot]; rewrite HE3 by (cbv; lia); rewrite EqMF; unfold w64; rewrite Zbv_add_unsigned; reflexivity | clear - F1 F2 F3; cbn; numconst; zlia | cbn; zlia | exact Hpmf]|];
  apply Forall_nil
| try unfold DMcdGk.R_STK_LO; try unfold DMcdGk.R_JST; try unfold R_PC3; try unfold DMcdGk.R_RGC; try unfold R_RGB3; try unfold R_RGA3;
  cbn [YP09.all_disjoint ss_mem]; unfold YP09.extent_disjoint; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]; rewrite ?B2, ?B32, ?B36, ?B41;
  clear - Usp dK1 Hlo Hhi LB dT1 dT2 dS1 dS2 dC1 dC2 dL1 dL2 dI1 dI2 dG0 dG1 dG2 dI3; numconst; repeat split; zlia ].
cbn [ss_pc ss_regs ss_mem ss_resv ss_facts] in HS.
apply (st_ok_add_region _ _ _ R_RGA3) in HS;
[ | reflexivity
| unfold R_RGA3, YP09.region_ok; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict mkst]; rewrite B41;
  split; [clear - dG0 dG1 dG2 dI1 dI3; numconst; zlia|]; split; [clear - dG0 dG1 dG2 dI1 dI3; numconst; zlia|];
  split; [intros o Ho; apply apresent_writable_off; [off_by ltac:(clear - dG0 dG1 dG2 dI1 dI3 Ho; numconst; zlia) | apply Lkpres; unfold DMcdGk.RGv, DMcdGk.RIv; lia]|];
  apply Forall_cons; [eapply chunk_ok_val with (v := FGsN.LOCKV); [reflexivity | unfold FGsN.LOCKV; cbn; lia | cbn; lia | exact Lk0]|];
  apply Forall_nil
| try unfold DMcdGk.R_STK_LO; try unfold DMcdGk.R_JST; try unfold R_PC3; try unfold DMcdGk.R_RGC; try unfold R_RGB3; try unfold R_RGA3;
  cbn [YP09.all_disjoint ss_mem]; unfold YP09.extent_disjoint; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]; rewrite ?B2, ?B32, ?B36, ?B41;
  clear - Usp dK1 Hlo Hhi LB dT1 dT2 dS1 dS2 dC1 dC2 dL1 dL2 dI1 dI2 dG0 dG1 dG2 dI3; numconst; repeat split; zlia ].
cbn [ss_pc ss_regs ss_mem ss_resv ss_facts] in HS.
(* a0 = 1, EFA's answer *)
assert (H58 : ew E3 58%nat = Z_to_bv 64 1).
{ unfold E3, havoc, kE3. cbn [ew Nat.ltb Nat.leb Nat.sub nth map CLOB]. exact Ha0. }
apply (st_ok_pin_regU _ _ _ 10%bv (SLit 1)) in HS;
[ | intros Hx; discriminate
| lazymatch goal with |- U _ _ = U _ (sr_get ?sr ?r) => let t := eval vm_compute in (sr_get sr r) in change (sr_get sr r) with t end;
  unfold U; cbn [sv_denot]; rewrite H58; vm_compute; reflexivity ].
cbn [ss_pc ss_regs ss_mem ss_resv ss_facts sr_set] in HS.
lazymatch type of HS with st_ok _ _ ?ss _ => assert (EQ3 : ss = SS3) by (vm_compute; reflexivity); rewrite EQ3 in HS end.
exists E3. split; [exact HE3|]. split; [exact HS|].
split.
{ (* the destination: the old part from the entry, the new part from the grant *)
  intros a Ha. destruct (Z_lt_le_dec a fadr) as [Hlt|Hge].
  - assert (Ho : DSTv <= a < FAv + mf) by (rewrite HFA; lia).
    destruct (Pold a Ho) as [Hh [b Hb]]. split; [exact (Hhid _ Hh)|]. exists b.
    rewrite NXG; [ | clear - LB Hlo Hhi Hc FA1 SH1 SH2 Usp Ha Hlt HFA F1 F2 F3 K5; unfold DMcdGk.DSTv, DMcdGk.RGv, DMcdGk.RIv in *; numconst; lia .. ].
    rewrite MQ9; [exact Hb|]. rewrite unsigned_lit_small by (clear - LB Hc FA1 Ha Hlt HFA F1 F2; unfold DMcdGk.DSTv in *; numconst; lia).
    exact (DST_notWINX HFULL a Ha).
  - apply (proj1 (Hgr a ltac:(unfold AFkn.RANGE; clear - Ha Hge HFA F1 F2 K5 HGROW; unfold DMcdGk.DSTv, DMcdGk.Nv, DMcdGk.MAXv in *; unfold kUserMapSize; lia))). }
assert (SRCo : forall a, SRCv <= a < SRCv + 4 * Nv -> mem3 (Z_to_bv 64 a) = mem0 (Z_to_bv 64 a)).
{ intros a Ha.
  rewrite NXG; [ | clear - LB Hlo Hhi Hc FA1 SH1 SH2 Usp Ha dC1 dC2 dT1 dT2 HFULL K3 K5 K6; unfold DMcdGk.SRCv, DMcdGk.Nv, DMcdGk.MAXv, DMcdGk.RGv, DMcdGk.RIv, DMcdGk.PCv in *; numconst; lia .. ].
  apply MQ9. rewrite unsigned_lit_small by (clear - Ha dC1 dC2 dT1 dT2 HFULL K3 K5 K6; unfold DMcdGk.SRCv, DMcdGk.Nv, DMcdGk.MAXv in *; numconst; lia).
  exact (SRC_notWINX HFULL a Ha). }
split.
{ intros a Ha. destruct (Psrc a Ha) as [Hh [b Hb]]. split; [exact (Hhid _ Hh)|]. exists b. rewrite SRCo by exact Ha. exact Hb. }
intros x Hx. pose proof (SRCo (bv_unsigned x) Hx) as Q. rewrite Z_to_bv_bv_unsigned in Q. exact Q.
Qed.
End WB.
End d.
