(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: from proofs/plugin-hostd/fuzz_reply/lib/A/DMrcSecCf.v (commit 67deba317dfb, blob fba36ad880e3) onto omx-clap-core/fuzz_preset's asan image (unstripped fuzz_preset.asan, sha256 bff8519bbe3e; pin 1be0f53d96cb); module paths changed; 1 image numerals moved by port_addr_check 3d2eee813cce MAPS predictions and the twins' symbol + offset map (0 model labels and sizes kept); no other numeral changed; comments removed (the source file keeps them). *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s YO0d.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YP0j.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0p YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG0a YG01 YG04 YG02 YG06 YG07 YG03 YG0f YG0v YG0n YG0d YG0s YG0q YG0o.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import AB1v AB1q AB1t AF0l AF0m AF0x AFl0 AFl1.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import ImgBase.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import ImgBaseDG.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import AImgA.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import DMspec DMiface.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require AFg8.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YFfn YK0v YK0g.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require AFf3 AFeu DMrcSecGvA DMrcSecMunA DMrcSecF6A DMrcSecReadsA DMrcSecNfA.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfNames.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YG03cf YGcfXs.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YGcfInstDrainR.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require YGcfInstRcSec CfInstImgA.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YGcfRehidePost YGcfRehideAR.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Set Warnings "-notation-for-abbreviation".
Open Scope Z_scope.

From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YGcfImgRows.
Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : YGcfNames.CfImg} {cp : CfParams}.

Lemma im_syms_preset : forall B, TfibSyms B -> @im_syms AImg_A B.
Proof. intros B TB. exact TB. Qed.

Definition ARXsl_cf (B : asyms) (IOK : Z -> Prop) (Hp : list Z) (d : Z) :
  Z -> alayout -> astate -> world tfibsegs -> (word -> option byte) -> Model -> Prop :=
fun inst ly S W mem md => IOK inst /\ YGcfRehideAR.ARcfR_sl tfibsegs B ly S Hp W mem md d /\ YGcfXs.xs_mapped_cf ly S md.

Definition REC_LE : Prop :=
forall MAP LEN, 0 <= MAP -> kMaxSize + kPage <= LEN -> cf_rec_drop LEN <= YGcfRehidePost.rh_hi MAP LEN - YGcfRehidePost.rh_lo MAP.

Lemma munmap_wvb_maps : forall a n mat1 md,
m_vmmaps (YK0v.munmap_model a n (with_vm_backing (m_vm_lazy md) mat1 md)) = m_vmmaps (YK0v.munmap_model a n md).
Proof. intros a n mat1 md. destruct md as [fd0 [maps0 lz0 mt0] io0 fs0 proc0 lim0 tm0]. reflexivity. Qed.
Lemma munmap_wvb_lazy : forall a n mat1 md,
m_vm_lazy (YK0v.munmap_model a n (with_vm_backing (m_vm_lazy md) mat1 md)) = m_vm_lazy (YK0v.munmap_model a n md).
Proof. intros a n mat1 md. destruct md as [fd0 [maps0 lz0 mt0] io0 fs0 proc0 lim0 tm0]. reflexivity. Qed.

Section f.
Variable B : asyms.
Hypothesis TB : TfibSyms B.
Variable IOK : Z -> Prop.
Variable Hp : list Z.

Hypothesis EAP : YGcfImgRows.ERRB_QAPART.

Hypothesis RLE : REC_LE.
Variables (inst : Z) (ly : alayout) (X : astate) (k : chunk) (cbp : Z) (W : world tfibsegs) (regs : bvmap 5 word)
  (mem : word -> option byte) (md : Model) (r : nat) (o : Z) (sm : secmap) (i : nat) (regsD : bvmap 5 word)
  (memD : word -> option byte) (mat1 : list word) (regs' : bvmap 5 word) (mem' : word -> option byte) (mat : list word).
Local Notation ARXr := (@YGcfInstDrainR.ARXr_cf rc ci cp AImg_A B IOK Hp).
Local Notation MAP := (AFg8.MAP ly r).
Local Notation LEN := (AFg8.LEN sm).
Local Notation QI := (AFg8.qi ly i).
Local Notation LST := (AFg8.lst ly X r).
Local Notation mdM := (YK0v.munmap_model (w64 MAP) (w64 LEN) (with_vm_backing (m_vm_lazy md) mat1 md)).
Hypothesis PRE : @rcc_pre_sec AImg_A B ARXr inst ly X k cbp W regs mem md.
Hypothesis Hb : ck_beg k = PSec r o.
Hypothesis Hsm : nth_error (st_secs X) r = Some sm.
Hypothesis Hi : nth_error (st_sec_arr X) i = Some r.
Hypothesis Hk : In k (st_chunks X).
Hypothesis Hst : ck_state k = CQuarantined.
Hypothesis Hni : ~ In (ck_beg k) (map ck_beg (q_items X)).
Hypothesis LNK : DMrcSecMunA.LINKD ly W regs mem regsD memD.
Hypothesis HR : DMrcSecGvA.at_RET W ly regsD memD MAP LEN (AFg8.idx i) (AFg8.nA X) QI LST
  (DMrcSecF6A.v regs 1%bv) (DMrcSecF6A.v regs 8%bv) (DMrcSecF6A.v regs 9%bv) (DMrcSecF6A.v regs 18%bv) (AFg8.own X i) mdM
  W (mkCfg (mkst regs' (w64 (DMrcSecF6A.v regs 1%bv)) mem' (seg_rom tfibsegs)) (with_vm_backing (m_vm_lazy mdM) mat mdM)).
Hypothesis CONST' : Forall (cell_holds B ly (aview tfibsegs (w_H W) mem')) (as_const B ly).

Lemma AR : ARXr inst ly X W mem md. Proof. exact (proj1 PRE). Qed.
Lemma MR : @YGcfInstDrainR.ARcfR rc ci cp tfibsegs B ly X Hp W mem md. Proof. exact (proj1 (proj2 AR)). Qed.

Lemma LEN_eq : YGcfInstRcSec.LEN k = LEN.
Proof.
destruct (@YGcfInstRcSec.KFACTS rc ci cp AImg_A B ly X Hp k r o sm W mem md MR Hk Hb Hsm) as (_ & E & _).
unfold AFg8.LEN. symmetry. exact E.
Qed.
Lemma W2_eq : YGcfInstRcSec.W2 (IM := AImg_A) ly k r W = AFg8.W2 ly W r sm.
Proof. unfold YGcfInstRcSec.W2, AFg8.W2, AFg8.iv. rewrite LEN_eq. reflexivity. Qed.
Lemma X2_eq : YGcfInstRcSec.rsX2 X k r sm i = AFg8.X2v X k r sm i.
Proof.
unfold YGcfInstRcSec.rsX2, YGcfInstRcSec.arr', YGcfInstRcSec.arr, YGcfInstRcSec.lastr, AFg8.X2v, AFg8.X2, AFg8.X1, AFf3.X1.
first [reflexivity | destruct X; reflexivity].
Qed.
Lemma OL : YGcfInstRcSec.own X i = true -> LST = ly_sec ly r.
Proof.
intros Eo. pose proof (@YGcfInstRcSec.ARR rc ci cp AImg_A B ly X Hp r i W mem md MR Hi) as (_ & _ & _ & _ & _ & _ & _ & OWN).
pose proof (proj1 OWN Eo) as E0. unfold YGcfInstRcSec.lastr, YGcfInstRcSec.arr in E0. unfold AFg8.lst. rewrite E0. reflexivity.
Qed.
Lemma GEO : 8192 <= LEN /\ 4096 <= MAP /\ MAP + LEN <= ASAN_CEIL.
Proof.
pose proof (@YGcfInstRcSec.geom rc ci cp AImg_A B ly X Hp k r o sm W mem md MR Hk Hb Hsm) as (_ & G2 & _ & _ & G5 & G6).
rewrite LEN_eq in G2, G5. unfold YGcfInstRcSec.MAP in G5, G6. unfold AFg8.MAP. lia.
Qed.

Lemma LEN_M2 : kMaxSize + kPage <= LEN.
Proof.
exact (YGcfRehideAR.M2_of_pre X k r o sm
  (proj1 (Forall_forall _ _) (YG03cf.wfr_chunks _ _ _ _ _ (YGcfInstDrainR.amr_wfr _ _ _ _ _ (proj1 MR))) k Hk) Hb Hsm).
Qed.

Lemma win_rsD : forall a, DMrcSecMunA.WPRE ly regs a \/ DMrcSecGvA.WIN3 ly regs MAP LEN QI LST a ->
YGcfInstRcSec.rsD B ly X k r i (spZ regs) a.
Proof.
intros a Hw. pose proof GEO as (G1 & G2 & G3). pose proof LEN_eq as EL. pose proof (ts_inst _ TB) as EI.
unfold YGcfInstRcSec.rsD, YGcfInstRcSec.rsDS, YGcfInstRcSec.rsDI, YGcfInstRcSec.rsDJ, YGcfInstRcSec.rsDQ,
  YGcfInstRcSec.rsDL, YGcfInstRcSec.rsDH, YGcfInstRcSec.rsDM, shadow_addr, spZ.
rewrite EI, EL.
change (YGcfInstRcSec.MAP ly r) with MAP. change (YGcfInstRcSec.qi ly i) with QI. change (YGcfInstRcSec.lst ly X r) with LST.
unfold DMrcSecMunA.WPRE, DMrcSecGvA.WIN3, DMrcSecGvA.WIN, DMrcSecGvA.WINS, DMrcSecGvA.WINM, DMrcSecGvA.SHAv, DMrcSecGvA.CNTv in Hw.
cbv zeta in Hw.
unfold A_ALLOCATOR, TFIB_INST, DMrcSecGvA.GDEPTH, AFeu.KSTACK in Hw |- *.
destruct Hw as [[H|[H|H]]|[[H|[H|[H|[H|[H|[H|[H|H]]]]]]]|[H|H]]].
- left. lia.
- right; left. lia.
- do 2 right; left. lia.
- left. lia.
- right; left. lia.
- right; left. lia.
- right; left. lia.
- right; left. lia.
- do 3 right; left. exact H.
- do 2 right; left. lia.
- destruct (YGcfInstRcSec.own X i) eqn:Eo.
  + do 6 right. rewrite (OL Eo) in H. unfold AFg8.MAP in *. lia.
  + do 4 right; left. split; [reflexivity | exact H].
- do 5 right; left. lia.
- do 6 right. lia.
Qed.

Lemma LSP : getr regsD 2 = getr regs 2. Proof. exact (proj1 LNK). Qed.
Lemma W3E : forall a, DMrcSecGvA.WIN3 ly regsD MAP LEN QI LST a <-> DMrcSecGvA.WIN3 ly regs MAP LEN QI LST a.
Proof. intros a. unfold DMrcSecGvA.WIN3, DMrcSecGvA.WIN. cbv zeta. rewrite LSP. tauto. Qed.
Lemma RETF :
(forall x : word, ~ DMrcSecGvA.WIN3 ly regs MAP LEN QI LST (bv_unsigned x) -> mem' x = memD x) /\
(forall x : word, DMrcSecGvA.WINS MAP LEN (bv_unsigned x) -> mem' x = Some (Z_to_bv 8 0)) /\
(forall a, bv_unsigned (getr regs 2) - DMrcSecGvA.GDEPTH <= a < bv_unsigned (getr regs 2) -> apresent (w_H W) mem' a) /\
(forall a, (QI <= a < QI + 8) \/ (ly_T ly + t_stats + 88 <= a < ly_T ly + t_stats + 104) -> apresent (w_H W) mem' a) /\
val_mem tfibsegs (mrestrict (w_H W) mem') (A_ALLOCATOR + 680) 4 0 /\
val_mem tfibsegs (mrestrict (w_H W) mem') (A_ALLOCATOR + 120) 8 (AFg8.nA X - 1) /\
val_mem tfibsegs (mrestrict (w_H W) mem') (A_ALLOCATOR + 128) 1 0 /\
(exists v, val_mem tfibsegs (mrestrict (w_H W) mem') (A_ALLOCATOR + 144) 8 v) /\
(exists v, val_mem tfibsegs (mrestrict (w_H W) mem') (A_ALLOCATOR + 152) 8 v) /\
(exists v, val_mem tfibsegs (mrestrict (w_H W) mem') (A_ALLOCATOR + 704) 8 v) /\
(exists v, val_mem tfibsegs (mrestrict (w_H W) mem') (A_ALLOCATOR + 712) 8 v) /\
val_mem tfibsegs (mrestrict (w_H W) mem') QI 8 LST /\
(AFg8.own X i = false -> val_mem tfibsegs (mrestrict (w_H W) mem') (LST + 24) 8 (AFg8.idx i) /\
  forall a, LST + 24 <= a < LST + 32 -> apresent (w_H W) mem' a).
Proof.
pose proof HR as (_ & regs0 & mem0 & mat0 & Ec & _ & _ & _ & _ & _ & MEQ & SHD & PS & PQ & VALS).
injection Ec; intros; subst mem0.
unfold DMrcSecGvA.MEQP in MEQ. unfold DMrcSecGvA.SHD in SHD.
split. { intros x Nx. apply MEQ. rewrite W3E. exact Nx. }
split. { exact SHD. }
split. { intros a Ha. apply PS. rewrite LSP. exact Ha. }
split. { exact PQ. }
cbv zeta in VALS. exact VALS.
Qed.
Lemma KEEP : forall x : word, ~ DMrcSecMunA.WPRE ly regs (bv_unsigned x) ->
~ DMrcSecGvA.WIN3 ly regs MAP LEN QI LST (bv_unsigned x) -> mem' x = mem x.
Proof. intros x N1 N2. pose proof RETF as (M & _). rewrite (M x N2). exact (proj1 (proj2 (proj2 LNK)) x N1). Qed.

Lemma HSP : ly_stk_lo ly + AFeu.KSTACK <= spZ regs <= ly_stk_hi ly.
Proof. destruct PRE as (_ & _ & _ & _ & H1 & H2 & H3 & _). unfold AFeu.KSTACK, KSTACK_CF in *. lia. Qed.

Lemma AG : forall a, 0 <= a < 2 ^ 64 -> ~ YGcfInstRcSec.rsD B ly X k r i (spZ regs) a ->
aview tfibsegs (w_H W) mem' a = aview tfibsegs (w_H W) mem a.
Proof.
intros a Ha ND. apply aview_same.
apply KEEP; rewrite unsigned_lit_small by exact Ha; intros Hw; apply ND, win_rsD; first [left; exact Hw | right; exact Hw].
Qed.

Lemma EQb : forall a, in_band_rw a -> ~ YGcfInstRcSec.rsD B ly X k r i (spZ regs) a -> mem' (w64 a) = mem (w64 a).
Proof.
intros a Hb0 ND.
assert (Ha : 0 <= a < 2 ^ 64) by (unfold in_band_rw, kLowShadowBeg, kLowShadowEnd, kHighShadowBeg, kHighShadowEnd in Hb0; lia).
unfold w64. apply KEEP; rewrite unsigned_lit_small by exact Ha; intros Hw; apply ND, win_rsD; first [left; exact Hw | right; exact Hw].
Qed.

Lemma ZE : forall a, YGcfInstRcSec.rsDH ly k r a -> mem' (w64 a) = Some (Z_to_bv 8 0).
Proof.
intros a H. pose proof (@YGcfInstRcSec.DH_zone rc ci cp AImg_A B ly X Hp k r o sm W mem md MR Hk Hb Hsm a H) as Z0.
assert (Ha : 0 <= a < 2 ^ 64) by (unfold SHADOW_OFF, kHighMemBeg in Z0; lia).
pose proof RETF as (_ & SH & _). unfold w64. apply SH. rewrite unsigned_lit_small by exact Ha.
unfold YGcfInstRcSec.rsDH, shadow_addr in H. rewrite LEN_eq in H. unfold DMrcSecGvA.WINS, DMrcSecGvA.SHAv, DMrcSecGvA.CNTv. exact H.
Qed.

Lemma MUTv : forall j, 0 <= j < 4 -> aview tfibsegs (w_H W) mem' (as_inst B + 680 + j) = Some 0.
Proof.
intros j Hj. pose proof RETF as (_ & _ & _ & _ & V & _).
rewrite (ts_inst _ TB). replace (TFIB_INST + 680 + j) with (A_ALLOCATOR + 680 + Z.of_nat (Z.to_nat j)) by (unfold TFIB_INST, A_ALLOCATOR; lia).
rewrite (AFg8.val_mem_aview _ _ _ 4 0 (Z.to_nat j) V ltac:(lia)). f_equal.
unfold le_byte. rewrite Z.mod_0_l by (apply Z.pow_nonzero; lia). rewrite Z.shiftr_0_l. reflexivity.
Qed.

Lemma NSv : forall kk, (kk < 8)%nat ->
aview tfibsegs (w_H W) mem' (as_inst B + 120 + Z.of_nat kk) = Some (le_byte (YGcfInstRcSec.nA X - 1) 8 kk).
Proof.
intros kk Hkk. pose proof RETF as (_ & _ & _ & _ & _ & V & _).
rewrite (ts_inst _ TB). change TFIB_INST with A_ALLOCATOR. exact (AFg8.val_mem_aview _ _ _ 8 _ kk V Hkk).
Qed.

Lemma QIv : forall kk, (kk < 8)%nat ->
aview tfibsegs (w_H W) mem' (YGcfInstRcSec.qi ly i + Z.of_nat kk) = Some (le_byte (YGcfInstRcSec.lst ly X r) 8 kk).
Proof.
intros kk Hkk. pose proof RETF as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & V & _).
exact (AFg8.val_mem_aview _ _ _ 8 _ kk V Hkk).
Qed.

Lemma LSTv : YGcfInstRcSec.own X i = false -> forall kk, (kk < 8)%nat ->
aview tfibsegs (w_H W) mem' (YGcfInstRcSec.lst ly X r + 24 + Z.of_nat kk) = Some (le_byte (YGcfInstRcSec.idx i) 8 kk).
Proof.
intros Eo kk Hkk. pose proof RETF as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & VO).
exact (AFg8.val_mem_aview _ _ _ 8 _ kk (proj1 (VO Eo)) Hkk).
Qed.

Lemma VISv : forall a, 0 <= a < 2 ^ 64 -> aview tfibsegs (w_H W) mem a <> None -> ~ YGcfInstRcSec.rsDM ly k r a ->
aview tfibsegs (w_H W) mem' a <> None.
Proof.
intros a Ha HV NM.
pose proof RETF as (MD & SH & PS & PQ & V680 & V120 & V128 & [v1 V144] & [v2 V152] & [v3 V704] & [v4 V712] & VQI & VOWN).
assert (NM' : ~ (MAP <= a < MAP + LEN)) by (intros HM; apply NM; unfold YGcfInstRcSec.rsDM; rewrite LEN_eq; exact HM).
assert (PV : apresent (w_H W) mem' a -> aview tfibsegs (w_H W) mem' a <> None) by (apply AFg8.apresent_vis; exact Ha).
assert (D : DMrcSecGvA.WIN3 ly regs MAP LEN QI LST a \/ ~ DMrcSecGvA.WIN3 ly regs MAP LEN QI LST a)
  by (unfold DMrcSecGvA.WIN3, DMrcSecGvA.WIN, DMrcSecGvA.WINS, DMrcSecGvA.WINM; cbv zeta; lia).
destruct D as [Hw|Nw].
- unfold DMrcSecGvA.WIN3, DMrcSecGvA.WIN, DMrcSecGvA.WINS, DMrcSecGvA.WINM in Hw. cbv zeta in Hw.
  destruct Hw as [[H|[H|[H|[H|[H|[H|[H|H]]]]]]]|[H|H]].
  + apply PV. apply PS. exact H.
  + exact (AFg8.val_mem_vis _ _ _ 4 0 a V680 ltac:(cbn; lia)).
  + destruct (Z_lt_le_dec a (A_ALLOCATOR + 128)) as [L|L].
    * exact (AFg8.val_mem_vis _ _ _ 8 _ a V120 ltac:(cbn; lia)).
    * exact (AFg8.val_mem_vis _ _ _ 1 0 a V128 ltac:(cbn; lia)).
  + destruct (Z_lt_le_dec a (A_ALLOCATOR + 152)) as [L|L].
    * exact (AFg8.val_mem_vis _ _ _ 8 v1 a V144 ltac:(cbn; lia)).
    * exact (AFg8.val_mem_vis _ _ _ 8 v2 a V152 ltac:(cbn; lia)).
  + destruct (Z_lt_le_dec a (A_ALLOCATOR + 712)) as [L|L].
    * exact (AFg8.val_mem_vis _ _ _ 8 v3 a V704 ltac:(cbn; lia)).
    * exact (AFg8.val_mem_vis _ _ _ 8 v4 a V712 ltac:(cbn; lia)).
  + apply PV. apply PQ. left. exact H.
  + apply PV. apply PQ. right. exact H.
  + destruct (AFg8.own X i) eqn:Eo.
    * exfalso. pose proof GEO as (G1 & _). rewrite (OL Eo) in H. unfold AFg8.MAP in NM'. lia.
    * apply PV. exact (proj2 (VOWN eq_refl) a H).
  + destruct (w_H W (Z_to_bv 64 a)) eqn:Hh.
    * exfalso. exact (HV (AFg8.aview_hidden_none W mem a Hh)).
    * apply PV. split; [exact Hh|]. exists (Z_to_bv 8 0). apply SH. rewrite unsigned_lit_small by exact Ha. exact H.
  + exfalso. exact (NM' H).
- assert (E1 : mem' (Z_to_bv 64 a) = memD (Z_to_bv 64 a)) by (apply MD; rewrite unsigned_lit_small by exact Ha; exact Nw).
  assert (DP : DMrcSecMunA.WPRE ly regs a \/ ~ DMrcSecMunA.WPRE ly regs a) by (unfold DMrcSecMunA.WPRE; cbv zeta; lia).
  destruct DP as [HW0|NP].
  + unfold DMrcSecMunA.WPRE in HW0. cbv zeta in HW0. destruct HW0 as [H|[H|H]].
    * exfalso. apply Nw. unfold DMrcSecGvA.WIN3, DMrcSecGvA.WIN. cbv zeta. left. left. exact H.
    * exfalso. apply Nw. unfold DMrcSecGvA.WIN3, DMrcSecGvA.WIN. cbv zeta. left. right. left. exact H.
    * apply PV. destruct (proj2 (proj2 (proj2 LNK)) a H) as [Hh [b Hb1]]. split; [exact Hh|]. exists b. rewrite E1. exact Hb1.
  + rewrite (aview_same (w_H W) mem mem' a); [exact HV|]. rewrite E1. apply (proj1 (proj2 (proj2 LNK))).
    rewrite unsigned_lit_small by exact Ha. exact NP.
Qed.

Lemma Ev : m_vmmaps (with_vm_backing (m_vm_lazy mdM) mat mdM) =
m_vmmaps (YK0v.munmap_model (w64 (YGcfInstRcSec.MAP ly r)) (w64 (YGcfInstRcSec.LEN k)) md).
Proof. rewrite LEN_eq, YK0g.m_vmmaps_with_vm_backing. apply munmap_wvb_maps. Qed.
Lemma El : m_vm_lazy (with_vm_backing (m_vm_lazy mdM) mat mdM) =
m_vm_lazy (YK0v.munmap_model (w64 (YGcfInstRcSec.MAP ly r)) (w64 (YGcfInstRcSec.LEN k)) md).
Proof. rewrite LEN_eq, YK0g.m_vm_lazy_with_vm_backing. apply munmap_wvb_lazy. Qed.
Lemma Ee : eager_used (with_vm_backing (m_vm_lazy mdM) mat mdM) =
eager_used (YK0v.munmap_model (w64 (YGcfInstRcSec.MAP ly r)) (w64 (YGcfInstRcSec.LEN k)) md).
Proof. unfold eager_used. rewrite Ev, El. reflexivity. Qed.

Lemma step_sl_cf :
ARXsl_cf B IOK Hp (YGcfRehidePost.rh_hi MAP LEN - YGcfRehidePost.rh_lo MAP) inst ly (AFg8.X2v X k r sm i) (AFg8.W2 ly W r sm)
  mem' (with_vm_backing (m_vm_lazy mdM) mat mdM) /\
(forall a, 0 <= a < 2 ^ 64 -> DMrcSecMunA.WPRE ly regs a \/ DMrcSecGvA.WIN3 ly regs MAP LEN QI LST a ->
 aowned B ly X a \/ ascratch B KSTACK_CF regs a) /\
(forall a, aowned B ly (AFg8.X2v X k r sm i) a -> aowned B ly X a) /\
(forall a, YFeuC.puser ly X a -> YFeuC.puser ly (AFg8.X2v X k r sm i) a) /\
(forall a, YFeuC.puser ly X a -> ~ (ck_base B ly k <= a < ck_base B ly k + ck_extent k) ->
 ~ DMrcSecMunA.WPRE ly regs a /\ ~ DMrcSecGvA.WIN3 ly regs MAP LEN QI LST a).
Proof.
destruct (@YGcfInstRcSec.rc_sec_step_sl_cf rc ci cp AImg_A B IOK Hp EAP inst ly X k r o sm i (spZ regs) W mem md mem'
  (with_vm_backing (m_vm_lazy mdM) mat mdM) AR Hk Hst Hb Hni Hsm Hi HSP (im_syms_preset B TB) CfInstImgA.img_sapart_A
  CfInstImgA.img_junk_A AG VISv MUTv NSv QIv LSTv CONST' EQb ZE Ev El Ee) as (HI & SL & XS & WOWN & OWN2 & PUN).
split.
{ rewrite <- X2_eq, <- W2_eq. split; [exact HI|]. split; [|exact XS].

  refine (YGcfRehideAR.ARcfR_sl_mono _ B ly _ Hp _ mem' _ (cf_rec_drop (sm_len sm)) _ _ SL).
  pose proof GEO as (_ & G2 & _).
  exact (RLE MAP LEN ltac:(lia) LEN_M2). }
split.
{ intros a Ha Hw. destruct (WOWN a ltac:(lia) (win_rsD a Hw)) as [O|S]; [left; exact O | right].
  unfold ascratch. left. unfold YGcfInstRcSec.rsDS, AFeu.KSTACK in S. unfold KSTACK_CF. lia. }
split. { intros a Ha. apply OWN2. rewrite X2_eq. exact Ha. }
split. { intros a Ha. exact Ha. }
intros a Ha _. pose proof (PUN a Ha) as ND. split; intros Hw; apply ND, win_rsD; [left | right]; exact Hw.
Qed.
End f.

Theorem rc_sec_step_nf_sl_of_cf : forall (B : asyms), TfibSyms B -> forall IOK Hp,
  YGcfImgRows.ERRB_QAPART -> REC_LE ->
  DMrcSecNfA.rc_sec_step_nf_g B (@YGcfInstDrainR.ARXr_cf rc ci cp AImg_A B IOK Hp) (ARXsl_cf B IOK Hp) (aowned B).
Proof.
intros B TB IOK Hp EAP RLE. unfold DMrcSecNfA.rc_sec_step_nf_g.
intros inst ly X k cbp W regs mem md r o sm i regsD memD mat1 regs' mem' mat PRE Hb Hsm Hi Hk Hst Hni LNK.
cbv zeta. intros HR CONST'.
exact (step_sl_cf B TB IOK Hp EAP RLE inst ly X k cbp W regs mem md r o sm i regsD memD mat1 regs' mem' mat
  PRE Hb Hsm Hi Hk Hst Hni LNK HR CONST').
Qed.

Theorem rc_sec_step_sl_of_cf : forall (B : asyms), TfibSyms B -> forall IOK Hp,
  YGcfImgRows.ERRB_QAPART -> REC_LE ->
  DMrcSecReadsA.rc_sec_step_g B (@YGcfInstDrainR.ARXr_cf rc ci cp AImg_A B IOK Hp) (ARXsl_cf B IOK Hp) (aowned B).
Proof.
intros B TB IOK Hp EAP RLE. unfold DMrcSecReadsA.rc_sec_step_g.
intros inst ly X k cbp W regs mem md r o sm i regsD memD mat1 regs' mem' mat PRE Hb Hsm Hi Hk Hst Hni LNK.
cbv zeta. intros HR CONST'.
destruct (rc_sec_step_nf_sl_of_cf B TB IOK Hp EAP RLE inst ly X k cbp W regs mem md r o sm i regsD memD mat1 regs'
  mem' mat (rcc_pre_sec_of_x _ _ _ _ _ _ _ _ _ _ _ PRE) Hb Hsm Hi Hk Hst Hni LNK HR CONST') as (AR2 & WOWN & OWN2 & PUS & PUN).

exact (conj AR2 (conj WOWN (conj OWN2 (conj PUS (conj PUN (proj1 (proj2 PRE))))))).
Qed.
End d.
