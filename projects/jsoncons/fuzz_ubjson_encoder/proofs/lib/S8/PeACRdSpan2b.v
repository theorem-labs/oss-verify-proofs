(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.

From Stdlib Require Import ZArith List Lia Bool FunctionalExtensionality.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.jsoncons.fuzz_ubjson_encoder.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S8 Require Import PropExec CatExec CatSim StoreOk Hoare ShapeAlg SpinAlg AsanAcct HeapIface HeapIfaceA IcptIfaceA L5Defs L5Core L5CoreKit L5Kn L5KnA L5LazyA L5DefsA L5CoreAS8 L5StepARS8.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import PmLayout PmLayoutA.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S8 Require Import PmModel PmModelFacts PmStatics PmStaticsA HeapIfaceAEx PmSpecsA PmSpecsAX PeSpecsAa PnStatics.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import PeCLayoutA.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S8 Require Import PeCModelA PeCSpecsA PeCSpecsAa PmModelFactsA PeStepA PmStep PmTxtKit2 PeASrcKitJ PeACReset1 PeARsKit PmSpecs PeCSink PeCModel PeCSpecs PeCFrame PeCSrcD PeCTxtSpecsA PeARdSpanP PeACRdSpan1 PeACRdSpan2.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.Spec Require Import UbjRef.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S8.Spec Require Import UbjRefFactsS8.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.L5FastLia. Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.L5FastLiaT. Local Ltac lia := L5FastLia.plia. Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module PECRS2bA.
Ltac inl := apply L5K.In_of_mem; vm_compute; reflexivity.
Abbreviation reg i := (Z_to_bv 5 (Z.of_nat i)).
Abbreviation RSEGS := Asan.M.loaded_segments.
Lemma pst_eta (s : PM.pst) :
  PM.PST (PM.p_more s) (PM.p_done s) (PM.p_depth s) (PM.p_src s) (PM.p_tb s) (PM.p_tg s) (PM.p_b s) (PM.p_k s) (PM.p_stk s) = s.
Proof. destruct s; reflexivity. Qed.
Abbreviation AD := PeCLayoutA.CADDR_A.
Abbreviation pot := PECRS1A.pot.
Ltac pdestr PP := repeat match type of PP with _ /\ _ => let H := fresh "Q" in destruct PP as (H & PP) end.

Section WithHeap.
Context {SCFG_P : ScfgP}.
Variables (L : asan_layout) (ar : asan_run) (C : asan_statics_cells) (HI : asan_iface).
Hypothesis LY : PMA.layout L C.
Hypothesis HIok : HAJ.asan_iface_okR L ar C SCFG HI.
Variable IL : icpt_layout.
Hypothesis ICok : aicpt_ok L ar IL SCFG HI.
Hypothesis ILY : as0_icpt_layout IL.
Let LYa := PMA.ly_as0 L C LY.

Section Call.
Variables (R0 : bvmap 5 word) (M0 : word -> option byte) (model0 : Model) (K : TSet) (LBX : list (Z * Z)) (FF LK0 : list fframe) (Aw0 : list (Z * Z)) (cr0 : credit).
Variables (S r fb len : Z) (s0 : PM.pst) (str : PM.vstr) (sm0 : PM.strm).
Variable pl : list Z.
Hypothesis Rra0 : getr R0 (reg 1) = Z_to_bv 64 r.
Hypothesis RAok : L5.ra_ok r.
Hypothesis Rsp0 : getr R0 (reg 2) = Z_to_bv 64 S.
Hypothesis Rgp0 : getr R0 (reg 3) = Z_to_bv 64 (pa_gp AD).
Hypothesis Rtp0 : getr R0 (reg 4) = Z_to_bv 64 (hl_tp L).
Hypothesis K0 : K [].
Hypothesis FRM0 : PMSPA.ffroomA 6 FF LK0.
Hypothesis FRS : PMSPA.ffrsA FF S.
Hypothesis FOK : PECA.frame_ok5 FF fb.
Hypothesis SA32 : S mod 32 = 0.
Hypothesis Hlen : 0 <= len < 2 ^ 64.
Hypothesis INCS : incl (PM.vs_own str) LBX.
Hypothesis UN0 : PM.unread (PM.p_src s0) sm0 < 2 ^ 26.
Hypothesis STKSH0 : shadow_zero M0 (S - 24576) 3072.
Hypothesis POK : PECS.payload_ok pl.
Hypothesis FBS : PECSA.fill_buffer_spec L ar HI.
Hypothesis SRDS : @PECTXSA.csrd_read_spec SCFG_P RSEGS AD L ar HI.
Hypothesis KONT : forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) (LK' : list fframe) (Aw' : list (Z * Z)) (s' : PM.pst) (sm' : PM.strm) (cr' : credit) (ptr n : Z),
  regs_preserved R0 R' -> getr R' 10%bv = Z_to_bv 64 ptr -> getr R' 11%bv = Z_to_bv 64 n -> 0 <= n <= len -> n < 2 ^ 26 ->
  ((ptr = 0 /\ n = 0) \/ (exists B m, In (B, m) (PM.parser_own s') /\ B <= ptr /\ ptr + n <= B + m) \/ (PMSPA.o_tb AD fb + 1 <= ptr /\ ptr + n <= PMSPA.o_tb AD fb + 24)) ->
  L5.defined M' ptr n -> PMSPA.accA M' ptr n -> L5.bytes_at RSEGS M' ptr (UbjRef.slice pl (PEC.pos_of pl (PM.p_src s0) sm0) n) ->
  n = Z.min len (blen pl - PEC.pos_of pl (PM.p_src s0) sm0) ->
  PM.parser_at RSEGS AD PMSPA.accA PMSPA.annA M' (PMSPA.o_p AD fb) (PMSPA.o_is AD fb) s' -> PM.iss_at RSEGS AD PMSPA.accA M' (PMSPA.o_is AD fb) str sm' ->
  PM.tb_ok (PM.p_tb s') (PM.p_tg s') ->
  PEC.content_ok RSEGS AD M' fb pl (PM.p_src s') str sm' ->
  PM.p_more s' = PM.p_more s0 -> PM.p_done s' = PM.p_done s0 -> PM.p_depth s' = PM.p_depth s0 ->
  PM.p_b s' = PM.p_b s0 -> PM.p_k s' = PM.p_k s0 -> PM.p_stk s' = PM.p_stk s0 ->
  PMSPA.src_step (PM.p_src s0) (PM.p_src s') sm0 sm' -> PMSPA.consumed (PM.p_src s0) (PM.p_src s') sm0 sm' = n ->
  L5CA.ahpres L ar LBX FF S (PMSPA.pm_scr 6) (PMSPA.W_srcf AD fb ++ [(PMSPA.o_tb AD fb, 24)]) M0 M' ->
  PMSPA.credit_keep cr0 cr' (pot L ar s0) (pot L ar s') ->
  model_rt model0 model' -> incl LK' LK0 -> incl Aw0 Aw' -> L5CA.amodel_ok Aw' model' -> ri_inv HI (PM.parser_own s' ++ LBX) FF LK' cr' Aw' M' (vml_of model') ->
  srealizes RSEGS SCFG (@PMSPA.cfg RSEGS fx' R' r M' model') K.

#[local] Abbreviation op := (PECRS1A.op fb).
#[local] Abbreviation os := (PECRS1A.os fb).
#[local] Abbreviation ois := (PECRS1A.ois fb).
#[local] Abbreviation tb := (PECRS1A.tb fb).
#[local] Abbreviation W0 := (PECRS1A.W0 fb).
#[local] Abbreviation U := (PECRS1A.U R0).
#[local] Abbreviation saves9 := (PECRS1A.saves9 R0 S).
#[local] Abbreviation kept_rs := (PECRS1A.kept_rs R0).
#[local] Abbreviation memrel := (PECRS1A.memrel L ar M0 LBX FF S fb).
#[local] Abbreviation fields_eq := (PECRS1A.fields_eq s0).
#[local] Abbreviation st_ok := (PECRS1A.st_ok L ar HI R0 M0 model0 LBX FF LK0 Aw0 cr0 S fb s0 str pl).
#[local] Abbreviation bregs := (PECRS1A.bregs R0 S fb len).
#[local] Abbreviation finish_rs := (PECRS1A.finish_rs L ar C HI LY HIok IL ICok ILY R0 M0 model0 K LBX FF LK0 Aw0 cr0 S r fb len s0 str sm0 pl Rra0 RAok Rsp0 Rgp0 Rtp0 K0 FRM0 FRS FOK SA32 Hlen INCS UN0 STKSH0 POK FBS SRDS KONT).
#[local] Abbreviation call_srd := (PECRS1A.call_srd L ar C HI LY HIok IL ICok ILY R0 M0 model0 K LBX FF LK0 Aw0 cr0 S r fb len s0 str sm0 pl Rra0 RAok Rsp0 Rgp0 Rtp0 K0 FRM0 FRS FOK SA32 Hlen INCS UN0 STKSH0 POK FBS SRDS KONT).
#[local] Abbreviation vpack := (PECRS1A.vpack L ar C HI LY HIok IL ICok ILY R0 M0 model0 K LBX FF LK0 Aw0 cr0 S r fb len s0 str sm0 pl Rra0 RAok Rsp0 Rgp0 Rtp0 K0 FRM0 FRS FOK SA32 Hlen INCS UN0 STKSH0 POK FBS SRDS KONT).
#[local] Abbreviation content_agree := (PECRS1A.content_agree L ar C HI LY HIok IL ICok ILY R0 M0 model0 K LBX FF LK0 Aw0 cr0 S r fb len s0 str sm0 pl Rra0 RAok Rsp0 Rgp0 Rtp0 K0 FRM0 FRS FOK SA32 Hlen INCS UN0 STKSH0 POK FBS SRDS KONT).
#[local] Abbreviation content_step := (PECRS1A.content_step L ar C HI LY HIok IL ICok ILY R0 M0 model0 K LBX FF LK0 Aw0 cr0 S r fb len s0 str sm0 pl Rra0 RAok Rsp0 Rgp0 Rtp0 K0 FRM0 FRS FOK SA32 Hlen INCS UN0 STKSH0 POK FBS SRDS KONT).
#[local] Abbreviation outside_W0 := (PECRS1A.outside_W0 L ar C HI LY HIok IL ICok ILY R0 M0 model0 K LBX FF LK0 Aw0 cr0 S r fb len s0 str sm0 pl Rra0 RAok Rsp0 Rgp0 Rtp0 K0 FRM0 FRS FOK SA32 Hlen INCS UN0 STKSH0 POK FBS SRDS KONT).

#[local] Abbreviation at_srd := (PECRS2A.at_srd L ar C HI LY HIok IL ICok ILY R0 M0 model0 K LBX FF LK0 Aw0 cr0 S r fb len s0 str sm0 pl Rra0 RAok Rsp0 Rgp0 Rtp0 K0 FRM0 FRS FOK SA32 Hlen INCS UN0 STKSH0 POK FBS SRDS KONT).
Ltac bvr1 x := let H := fresh "BU" in pose proof (bv_unsigned_in_range 64 (getr R0 (reg x))) as H; change (bv_modulus 64) with (2 ^ 64) in H.
Ltac bvr := bvr1 1%nat; bvr1 8%nat; bvr1 9%nat; bvr1 18%nat; bvr1 19%nat; bvr1 20%nat; bvr1 21%nat; bvr1 22%nat; bvr1 23%nat.
Ltac vis64 AV := lazymatch goal with |- L5.u64_at ?sg (mrestrict ?H ?M) ?a ?v =>
  apply (proj2 (L5A.u64_at_vis H M a v ltac:(apply AV; lia) ltac:(lia) ltac:(lia))); assumption end.
Ltac vis8 AV := lazymatch goal with |- L5.u8_at ?sg (mrestrict ?H ?M) ?a ?v =>
  apply (proj2 (L5A.u8_at_vis H M a v ltac:(apply AV; lia) ltac:(lia) ltac:(lia))); assumption end.

Lemma own_with_tb (s : PM.pst) tb1 tg1 : PM.vs_own tb1 = PM.vs_own (PM.p_tb s) -> PM.parser_own (PMTK2.with_tb s tb1 tg1) = PM.parser_own s.
Proof using All. intros E. unfold PM.parser_own, PMTK2.with_tb. cbn [PM.p_src PM.p_b PM.p_k PM.p_tb]. rewrite E. reflexivity. Qed.

Lemma slow (fx : FPState) R M model s sm cr LK Aw :
  bregs R -> 1 <= len -> st_ok M model s sm cr LK Aw -> fields_eq s -> PMSPA.src_step (PM.p_src s0) (PM.p_src s) sm0 sm ->
  PM.unread (PM.p_src s) sm = PM.unread (PM.p_src s0) sm0 ->
  srealizes RSEGS SCFG (@PMSPA.cfg RSEGS fx R 0xb65dc M model) K.
Proof using All.
  intros BR0 Hl SO FE STEP U0. pose proof BR0 as (A2 & A8 & A9 & A18 & A19 & A21 & A22 & KP).
  pose proof (vpack M model s sm cr LK Aw SO) as (V0 & V1 & V2 & (SR1 & S16 & V3) & SVV & (O1 & O8 & OBIG) & OZ & OW & OAV & (T1 & T8 & TBIG) & TZ & TW & TAV & OSS & TBS & AO & AT).
  pose proof SO as ((EK & DK & STK) & SV & PA & IA & BASE & TBOK & HH & AM & MRT & ILK & IAW & CRL & CRK & ACC & CT).
  pose proof (PECRS1A.geo fb) as (Eop & Eos & Eois & Etb). pose proof (PECRS1A.fbb FF fb FOK) as (F1024 & rs & Hfb).
  pose proof (HAJ.aior_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as (WB & WF & FSAPP & FSCEIL & _ & _ & _ & _ & _ & _ & NDL & _).
  pose proof (PMASKJ.brb_of L ar C HI HIok _ _ _ _ _ _ _ HH) as BRB. pose proof (PMASKJ.frb_of L ar C HI HIok _ _ _ _ _ _ _ HH) as FRB.
  pose proof (PMASKJ.fs_above_img L ar C HI LY HIok _ _ _ _ _ _ _ HH) as FSI.
  destruct (WF _ Hfb) as (FF1 & FF2 & _). cbn [ff_addr ff_class fst snd] in FF1, FF2.
  pose proof PA as (_ & PD & _ & _ & _ & _ & _ & _ & _ & SRC & _ & _ & _ & VS & VEC & _).
  destruct SRC as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & DC & _ & _).
  replace (op + 336) with tb in VS by lia.
  pose proof VEC as (_ & _ & _ & Hk & _). pose proof (PM.pow2_pos (PM.p_k s) (proj1 Hk)) as P2.
  assert (VIN : In (PM.p_b s, 32 * 2 ^ PM.p_k s) (PM.parser_own s ++ LBX)) by (apply in_or_app; left; right; left; reflexivity).
  destruct (BRB _ VIN) as (VB0 & VB1). cbn [fst snd] in VB0, VB1.
  assert (QIN : In (PM.sr_qc (PM.p_src s), PM.CHUNK) (PM.parser_own s ++ LBX)) by (apply in_or_app; left; left; reflexivity).
  destruct (BRB _ QIN) as (QB0 & QB1). cbn [fst snd] in QB0, QB1.
  assert (BLKAP : forall q m, In (q, m) (PM.parser_own s ++ LBX) -> q + m <= fb \/ fb + 2048 <= q).
  { intros q m Hq. destruct (WB _ Hq) as (_ & _ & _ & _ & _ & FA & _). cbn [fst snd] in FA.
    destruct (FA (fb, 5, rs) (in_or_app _ _ _ (or_introl Hfb))) as [X|X]; cbn [ff_addr ff_class fst snd] in X; change (ff_bytes 5) with 2048 in X; [left|right]; lia. }
  assert (AOI : PMSPA.aobjA FF ois 272).
  { exists (fb, 5, rs). split; [exact Hfb|]. cbn [ff_addr ff_class fst snd]. change (ff_bytes 5) with 2048. lia. }
  pose proof SV as (Z8 & Z16 & Z24 & Z32 & Z40 & Z48 & Z56 & Z64 & Z72).
  set (MV := mrestrict (ahid Aw model) M) in *.
  assert (NOTSH : forall a n, 0 <= a -> a + n <= 2 ^ 47 -> forall x, a <= x < a + n -> 0 <= HeapIfaceA.S x < 2 ^ 64 /\ 2147446784 <= HeapIfaceA.S x < 17594333495296).
  { intros a n Ha Hn x Hx. unfold HeapIfaceA.S, HeapIfaceA.SB.
    assert (X8 : 0 <= x / 8 <= 17592186044416) by (split; [apply Z.div_pos; lia| apply Z.div_le_upper_bound; lia]). lia. }
  revert VS. destruct (PM.p_tb s) as [n0|c0 n0 q0] eqn:ETB; intros (VD & VC & VS).
  -
    destruct VS as (Hn0 & BY0). pose proof (PMF.even_byte n0) as EV.
    assert (TZ1 : L5KA.zeros_at MV ((tb + 1) / 8 + 2147450880) 1).
    { replace ((tb + 1) / 8) with (tb / 8) by (apply Z.div_unique with 1; [left; lia| pose proof (Z.div_mod tb 8 ltac:(lia)); lia]).
      intros i Hi. apply TZ. lia. }
    pose proof (PMARSPP.arpSS_conc fx R MV (fun j => match j with 2%nat => S | 36%nat => os | 37%nat => tb | 38%nat => len | 39%nat => 2 * n0 | _ => 0 end)) as PP.
    cbn beta iota in PP.
    L5SAR.feed PP ltac:(first [assumption | lazymatch goal with
        | |- L5.u8_at _ _ tb _ => unfold MV; vis8 TAV
        | |- PMARSPP.aligned _ _ => unfold PMARSPP.aligned; lia
        | |- _ => lia end]).
    destruct PP as (fx1 & R1 & M1v & MG1 & _ & FRZ1 & MS1 & KS1 & E1 & E10 & E11 & E12 & E19 & C0 & C1).
    set (P := fun a => tb + 0 <= a < tb + 0 + 2).
    unfold PMSPA.cfg.
    apply (L5SAR.apiece L ar C HI LYa HIok _ FF LK cr Aw M model fx fx1 R 0xb65dc R1 0xb763c M1v P K HH AM MS1 MG1).
    { intros a Ha N. apply FRZ1; [exact Ha| exact N]. }
    { intros a Ha Wa. unfold P in Wa. split.
      - unfold aclientw, aclient_g. right; right; right; left. exists (fb, 5, rs). split; [exact Hfb|]. cbn [ff_addr ff_class fst snd]. change (ff_bytes 5) with 2048. lia.
      - lia. }
    intros M1 model1 HH1 AM1 MRT1 HID1 VIS1 MGM1 FR1 VV1.
    assert (AG : forall a n, 0 <= a -> a + n <= 2 ^ 64 -> (a + n <= tb \/ tb + 2 <= a) -> L5C.agree_on M M1 a n).
    { intros a n Ha Hn X i Hi. apply FR1; [lia| unfold P; lia]. }
    assert (AGSH : forall a n, 0 <= a -> a + n <= 2 ^ 47 -> PMFA.agsh M M1 a n).
    { intros a n Ha Hn x Hx. destruct (NOTSH a n Ha Hn x Hx) as (X1 & X2). apply FR1; [lia| unfold P; destruct TBIG; lia]. }
    assert (AGB : forall q m, In (q, m) (PM.parser_own s ++ LBX) -> PMFA.agA M M1 q m).
    { intros q m Hq. destruct (BRB _ Hq) as (X0 & X1). cbn [fst snd] in X0, X1. destruct (BLKAP q m Hq) as [BF|BF]; (split; [apply AG; lia| apply AGSH; lia]). }
    set (s1 := PMTK2.with_tb s (PM.VShort 0) (PM.p_tg s)).
    assert (OW1 : PM.vs_own (PM.VShort 0) = PM.vs_own (PM.p_tb s)) by (rewrite ETB; reflexivity).
    assert (BK1 : forall a v, tb <= a -> a + 1 <= tb + 24 -> L5.u8_at RSEGS M1v a v -> L5.u8_at RSEGS M1 a v).
    { intros a v Ha Hb X. apply (proj1 (L5A.u8_at_vis (ahid Aw model) M1 a v ltac:(apply TAV; lia) ltac:(lia) ltac:(lia))). rewrite VIS1. exact X. }
    assert (PA1 : PM.parser_at RSEGS AD PMSPA.accA PMSPA.annA M1 op ois s1).
    { apply (PMARSK.parser_tb_setA M M1 op ois s (PM.VShort 0) (PM.p_tg s) PA); [lia| lia| | | | lia| cbv [PM.CHUNK] in *; lia| | lia| lia| | |].
      - split; [apply AG; lia| apply AGSH; lia].
      - split; [apply AG; lia| apply AGSH; lia].
      - apply AGSH; lia.
      - exact (AGB _ _ QIN).
      - exact (AGB _ _ VIN).
      - replace (op + 336) with tb by lia. split; [intros i Hi; apply MGM1; apply VD; exact Hi|].
        split; [apply (PMFA.accA_agree M M1 tb 24); [apply AGSH; lia| exact VC]|]. split; [lia|]. replace (2 * 0) with 0 by lia. apply BK1; [lia| lia| exact C0].
      - intros i Hi. apply MGM1. apply PD. exact Hi. }
    set (Wp := [(tb, 2)]).
    assert (EK1 : L5SAR.ek L ar (PM.parser_own s ++ LBX) FF S 24576 Wp M M1).
    { apply (L5SAR.ek_piece L ar _ FF S 24576 Wp M M1 P); [intros a Ha N; apply FR1; [exact Ha| exact N]|].
      intros a Ha CA OWx Pa. apply (OWx (tb, 2)); [left; reflexivity|]. unfold L5.in_rng, P in *; cbn [fst snd]. lia. }
    assert (WAPPp : PMKA.wapp Wp) by (apply PMKA.wapp_cons; [cbn [fst snd]; unfold BIGSHADOW_LO, BIGSHADOW_HI; destruct TBIG; [right| left]; lia| apply PMKA.wapp_nil]).
    assert (IA1 : PM.iss_at RSEGS AD PMSPA.accA M1 ois str sm).
    { apply (PMKA.iss_keepA RSEGS AD L ar _ FF S 24576 Wp M M1 EK1 WAPPp FRB BRB _ _ _ AOI); [intros x Hx; apply in_or_app; right; apply INCS; exact Hx| | |exact IA].
      - intros i Hi r0 Hr. unfold Wp in Hr. unfold L5.in_rng. destruct Hr as [<-|[]]; cbn [fst snd]; lia.
      - intros c n p E i Hi r0 Hr. assert (Ip : In (p, c) (PM.parser_own s ++ LBX)) by (apply in_or_app; right; apply INCS; rewrite E; left; reflexivity).
        destruct (BLKAP _ _ Ip) as [X|X]; unfold Wp in Hr; unfold L5.in_rng; destruct Hr as [<-|[]]; cbn [fst snd]; lia. }
    assert (EKn : L5SAR.ek L ar LBX FF S 24576 W0 M M1).
    { apply (L5SAR.ek_piece L ar LBX FF S 24576 W0 M M1 P); [intros a Ha N; apply FR1; [exact Ha| exact N]|].
      intros a Ha CA OWx Pa. apply (OWx (PMSPA.o_tb AD fb, 24)); [unfold PECRS1A.W0; apply in_or_app; right; left; reflexivity|].
      unfold L5.in_rng, P in *; cbn [fst snd] in *. change (PMSPA.o_tb AD fb) with tb. lia. }
    assert (SO1 : st_ok M1 model1 s1 sm cr LK Aw).
    { split; [split; [|split]|].
      - exact (L5SAR.ek_trans L ar LBX FF S 24576 W0 M0 M M1 EK EKn).
      - apply (L5SAR.dk_trans L ar LBX FF S 24576 M0 M M1 DK). apply L5SAR.dk_grows. exact MGM1.
      - exact (L5SAR.astk_grows ar M M1 S 24576 STK MGM1).
      - split; [repeat split; (apply (L5C.u64_at_agree RSEGS M M1); [apply AG; lia| lia| lia| assumption])|].
        split; [exact PA1|]. split; [exact IA1|].
        split; [apply (PMASKJ.base_keep L ar C LY LBX FF S 24576 W0 M M1 EKn); [intros a Ha; apply outside_W0; lia| exact BASE]|].
        split; [unfold s1; cbn [PMTK2.with_tb PM.p_tb PM.p_tg]; unfold PM.tb_ok in *; cbn [PM.vs_cap] in *; exact TBOK|].
        split; [unfold s1; rewrite (own_with_tb s _ _ OW1); exact HH1|]. split; [exact AM1|].
        split; [eapply L5LZ.model_rt_trans; [exact MRT| exact MRT1]|].
        split; [exact ILK|]. split; [exact IAW|].
        unfold s1; cbn [PMTK2.with_tb PM.p_tb PM.p_tg]. unfold PM.pot_text in *. try rewrite ETB in CRL. try rewrite ETB in CRK. cbn [PM.vs_cap] in *. split; [exact CRL|]. split; [exact CRK|].
        destruct (FRB _ Hfb) as (Fb0 & Fb1). cbn [ff_addr ff_class fst snd] in Fb0, Fb1. change (ff_bytes 5) with 2048 in Fb1.
        split; [apply (PMFA.accA_agree M M1 op PECA.RDR_BYTES); [apply AGSH; unfold PECA.RDR_BYTES; clear - Eop Fb0 Fb1; lia| exact ACC]|].

        cbn [PM.p_src].
        apply (content_agree M M1 s sm cr LK Aw (vml_of model) (proj1 (AGB _ _ QIN)) (fun B m Hin => proj1 (AGB B m ltac:(apply in_or_app; right; exact Hin))) ltac:(apply AG; clear - Eois Eos Etb Fb0 Fb1; lia) HH PA IA CT). }
    apply (at_srd fx1 R1 M1 model1 s1 sm cr LK Aw); try assumption.
    all: first [ rewrite (KS1 2%nat) by inl; exact A2 | rewrite (KS1 8%nat) by inl; exact A8 | rewrite (KS1 9%nat) by inl; exact A9
               | rewrite (KS1 18%nat) by inl; exact A18 | rewrite (KS1 21%nat) by inl; exact A21 | rewrite (KS1 22%nat) by inl; exact A22
               | (intros x Hx; rewrite (KS1 x) by (cbn in Hx; repeat (destruct Hx as [<-|Hx]; [inl|]); destruct Hx); apply KP; exact Hx)
               | (unfold s1; cbn [PMTK2.with_tb PM.p_tb PM.vs_size]; reflexivity)
               | (unfold s1; cbn [PMTK2.with_tb PM.p_src]; exact U0) ].
  -
    destruct VS as (W0' & W8 & W16 & Hn0 & Hc0 & Hce & DQ & CQ).
    pose proof (PMF.u8_of_u64 RSEGS M tb (c0 + 1) ltac:(lia) W0') as BY0. pose proof (PMF.odd_byte c0 Hce ltac:(lia)) as ODB.
    assert (H39 : 0 <= (c0 + 1) mod 256 <= 255) by (pose proof (Z.mod_pos_bound (c0 + 1) 256 ltac:(lia)); lia).
    assert (TIN : In (q0, c0) (PM.parser_own s ++ LBX)) by (apply in_or_app; left; unfold PM.parser_own; rewrite ETB; cbn; right; right; left; reflexivity).
    pose proof (PMARSK.tbd_vis L ar C HI LY HIok _ FF LK cr Aw M model q0 c0 HH TIN ltac:(lia) CQ) as ((D1 & D2 & D16 & DBIG) & DZ & DW & DAV & DCE).
    pose proof STK as (A16 & SLO & SHI & SPT & SDEF & SUP).
    pose proof (PMASKJ.blk_img L ar C HI LY HIok _ _ _ _ _ _ _ q0 c0 HH TIN) as QIMG.
    assert (TFA := BLKAP _ _ TIN).

    assert (KQT : q0 + 1 <= tb \/ tb + 24 <= q0) by (destruct TFA; [left|right]; lia).
    assert (KQO : q0 + 1 <= os \/ os + 296 <= q0) by (destruct TFA; [left|right]; lia).
    assert (KQS : 2147446784 + 17592186048512 <= q0 \/ q0 + 1 <= 2147446784) by (destruct DBIG; [left|right]; lia).
    assert (KQF : S - 80 + 80 <= q0 \/ q0 + 1 <= S - 80) by (right; lia).
    assert (QNI : ~ (65536 <= q0 < 6914048)) by (destruct QIMG; lia). clear QIMG.
    pose proof (PMARSPP.arpSL_conc fx R MV (fun j => match j with 2%nat => S | 36%nat => os | 37%nat => tb | 38%nat => len | 39%nat => (c0 + 1) mod 256
         | 40%nat => n0 | 41%nat => q0 | _ => 0 end)) as PP.
    cbn beta iota in PP.
    L5SAR.feed PP ltac:(first [assumption | lazymatch goal with
        | |- L5.u8_at _ _ tb _ => unfold MV; vis8 TAV
        | |- L5.u64_at _ _ (tb + _) _ => unfold MV; vis64 TAV
        | |- PMARSPP.aligned q0 8 => unfold PMARSPP.aligned; apply PMKA.mod16_8'; exact D16
        | |- PMARSPP.aligned _ _ => unfold PMARSPP.aligned; lia
        | |- _ => lia end]).
    destruct PP as (fx1 & R1 & M1v & MG1 & _ & FRZ1 & MS1 & KS1 & E1 & E10 & E11 & E12 & E19 & C0 & C1).
    set (P := fun a => (q0 + 0 <= a < q0 + 0 + 1) \/ (tb + 8 <= a < tb + 8 + 8)).
    unfold PMSPA.cfg.
    apply (L5SAR.apiece L ar C HI LYa HIok _ FF LK cr Aw M model fx fx1 R 0xb65dc R1 0xb763c M1v P K HH AM MS1 MG1).
    { intros a Ha N. apply FRZ1; [exact Ha| intros X; apply N; left; exact X| intros X; apply N; right; exact X]. }
    { intros a Ha Wa. unfold P in Wa. destruct Wa as [Wa|Wa].
      - split; [unfold aclientw, aclient_g; left; exists (q0, c0); split; [exact TIN| cbn [fst snd]; lia]| intros X; apply QNI; lia].
      - split; [|lia]. unfold aclientw, aclient_g. right; right; right; left. exists (fb, 5, rs). split; [exact Hfb|]. cbn [ff_addr ff_class fst snd]. change (ff_bytes 5) with 2048. lia. }
    intros M1 model1 HH1 AM1 MRT1 HID1 VIS1 MGM1 FR1 VV1.
    assert (AG : forall a n, 0 <= a -> a + n <= 2 ^ 64 -> (a + n <= q0 \/ q0 + 1 <= a) -> (a + n <= tb + 8 \/ tb + 16 <= a) -> L5C.agree_on M M1 a n).
    { intros a n Ha Hn X Y i Hi. apply FR1; [lia| unfold P; clear - X Y Hi; lia]. }
    assert (AGSH : forall a n, 0 <= a -> a + n <= 2 ^ 47 -> PMFA.agsh M M1 a n).
    { intros a n Ha Hn x Hx. destruct (NOTSH a n Ha Hn x Hx) as (X1 & X2). apply FR1; [lia| unfold P; clear - X2 TBIG KQS; destruct TBIG; destruct KQS; lia]. }
    assert (OTH : forall q m, In (q, m) (PM.parser_own s ++ LBX) -> q <> q0 -> PMFA.agA M M1 q m).
    { intros q m Hq NE. destruct (BRB _ Hq) as (X0 & X1). cbn [fst snd] in X0, X1.
      destruct (PMASKJ.blk_apart L ar C HI HIok _ FF LK cr Aw M _ q m q0 c0 HH Hq TIN NE) as [AP|AP]; destruct (BLKAP q m Hq) as [BF|BF];
      (split; [apply AG; lia| apply AGSH; lia]). }
    assert (NEQ : PM.sr_qc (PM.p_src s) <> q0).
    { intros E. apply (PMARS1.fst_neq_app [(PM.sr_qc (PM.p_src s), PM.CHUNK)] (PM.vec_own (PM.p_b s) (PM.p_k s) ++ PM.vs_own (PM.p_tb s) ++ LBX) (PM.sr_qc (PM.p_src s)) PM.CHUNK q0 c0).
      - exact NDL. - left. reflexivity. - rewrite ETB. right. left. reflexivity. - exact E. }
    assert (NEV : PM.p_b s <> q0).
    { intros E. apply (PMARS1.fst_neq_app ([(PM.sr_qc (PM.p_src s), PM.CHUNK)] ++ PM.vec_own (PM.p_b s) (PM.p_k s)) (PM.vs_own (PM.p_tb s) ++ LBX) (PM.p_b s) (32 * 2 ^ PM.p_k s) q0 c0).
      - rewrite <- app_assoc. exact NDL. - right. left. reflexivity. - rewrite ETB. left. reflexivity. - exact E. }
    set (s1 := PMTK2.with_tb s (PM.VLong c0 0 q0) (PM.p_tg s)).
    assert (OW1 : PM.vs_own (PM.VLong c0 0 q0) = PM.vs_own (PM.p_tb s)) by (rewrite ETB; reflexivity).
    assert (BK64 : forall a v, tb <= a -> a + 8 <= tb + 24 -> L5.u64_at RSEGS M1v a v -> L5.u64_at RSEGS M1 a v).
    { intros a v Ha Hb X. apply (proj1 (L5A.u64_at_vis (ahid Aw model) M1 a v ltac:(apply TAV; lia) ltac:(lia) ltac:(lia))). rewrite VIS1. exact X. }
    assert (PA1 : PM.parser_at RSEGS AD PMSPA.accA PMSPA.annA M1 op ois s1).
    { apply (PMARSK.parser_tb_setA M M1 op ois s (PM.VLong c0 0 q0) (PM.p_tg s) PA); [lia| lia| | | | lia| cbv [PM.CHUNK] in *; lia| | lia| lia| | |].
      - destruct TFA as [TF|TF]; (split; [apply AG; lia| apply AGSH; lia]).
      - destruct TFA as [TF|TF]; (split; [apply AG; lia| apply AGSH; lia]).
      - apply AGSH; lia.
      - exact (OTH _ _ QIN NEQ).
      - exact (OTH _ _ VIN NEV).
      - replace (op + 336) with tb by lia. split; [intros i Hi; apply MGM1; apply VD; exact Hi|].
        split; [apply (PMFA.accA_agree M M1 tb 24); [apply AGSH; lia| exact VC]|].
        split; [apply (L5C.u64_at_agree RSEGS M M1); [destruct TFA as [TF|TF]; apply AG; lia| lia| lia| exact W0']|].
        split; [apply BK64; [lia| lia| exact C0]|].
        split; [apply (L5C.u64_at_agree RSEGS M M1); [destruct TFA as [TF|TF]; apply AG; lia| lia| lia| exact W16]|].
        split; [lia|]. split; [lia|]. split; [exact Hce|]. split; [intros i Hi; apply MGM1; apply DQ; exact Hi|].
        apply (PMFA.accA_agree M M1 q0 c0); [apply AGSH; lia| exact CQ].
      - intros i Hi. apply MGM1. apply PD. exact Hi. }
    set (Wp := [(q0, 1); (tb + 8, 8)]).
    assert (EK1 : L5SAR.ek L ar (PM.parser_own s ++ LBX) FF S 24576 Wp M M1).
    { apply (L5SAR.ek_piece L ar _ FF S 24576 Wp M M1 P); [intros a Ha N; apply FR1; [exact Ha| exact N]|].
      intros a Ha CA OWx Pa. unfold P in Pa. destruct Pa as [X|X]; [apply (OWx (q0, 1))| apply (OWx (tb + 8, 8))]; try (unfold Wp; cbn; auto); unfold L5.in_rng; cbn [fst snd]; lia. }
    assert (WAPPp : PMKA.wapp Wp).
    { unfold Wp. apply PMKA.wapp_cons; [cbn [fst snd]; unfold BIGSHADOW_LO, BIGSHADOW_HI; destruct DBIG; [right| left]; lia|].
      apply PMKA.wapp_cons; [cbn [fst snd]; unfold BIGSHADOW_LO, BIGSHADOW_HI; destruct TBIG; [right| left]; lia| apply PMKA.wapp_nil]. }
    assert (IA1 : PM.iss_at RSEGS AD PMSPA.accA M1 ois str sm).
    { apply (PMKA.iss_keepA RSEGS AD L ar _ FF S 24576 Wp M M1 EK1 WAPPp FRB BRB _ _ _ AOI); [intros x Hx; apply in_or_app; right; apply INCS; exact Hx| | |exact IA].
      - intros i Hi r0 Hr. unfold Wp in Hr. unfold L5.in_rng. destruct TFA as [TF|TF]; destruct Hr as [<-|[<-|[]]]; cbn [fst snd]; lia.
      - intros c n p E i Hi r0 Hr. assert (Ip : In (p, c) (PM.parser_own s ++ LBX)) by (apply in_or_app; right; apply INCS; rewrite E; left; reflexivity).
        assert (NE : p <> q0).
        { intros Ep. subst p. apply (PMARS1.fst_neq_app (PM.parser_own s) LBX q0 c0 q0 c); [exact NDL| unfold PM.parser_own; rewrite ETB; cbn; right; right; left; reflexivity| apply INCS; rewrite E; left; reflexivity| reflexivity]. }
        destruct (BLKAP _ _ Ip) as [X|X]; destruct (PMASKJ.blk_apart L ar C HI HIok _ FF LK cr Aw M _ p c q0 c0 HH Ip TIN NE) as [Y|Y];
        unfold Wp in Hr; unfold L5.in_rng; destruct Hr as [<-|[<-|[]]]; cbn [fst snd]; lia. }
    assert (EKn : L5SAR.ek L ar LBX FF S 24576 W0 M M1).
    { apply (L5SAR.ek_piece L ar LBX FF S 24576 W0 M M1 P); [intros a Ha N; apply FR1; [exact Ha| exact N]|].
      intros a Ha CA OWx Pa. unfold P in Pa. destruct Pa as [X|X].
      - apply (PMARS1.own_not_aclient L ar C HI HIok (PM.parser_own s) LBX FF LK cr Aw M _ q0 c0 a S 24576 HH); [unfold PM.parser_own; rewrite ETB; cbn; right; right; left; reflexivity| lia| exact CA].
      - apply (OWx (PMSPA.o_tb AD fb, 24)); [unfold PECRS1A.W0; apply in_or_app; right; left; reflexivity|].
        unfold L5.in_rng; cbn [fst snd]. change (PMSPA.o_tb AD fb) with tb. lia. }
    assert (SO1 : st_ok M1 model1 s1 sm cr LK Aw).
    { split; [split; [|split]|].
      - exact (L5SAR.ek_trans L ar LBX FF S 24576 W0 M0 M M1 EK EKn).
      - apply (L5SAR.dk_trans L ar LBX FF S 24576 M0 M M1 DK). apply L5SAR.dk_grows. exact MGM1.
      - exact (L5SAR.astk_grows ar M M1 S 24576 STK MGM1).
      - split; [repeat split; (apply (L5C.u64_at_agree RSEGS M M1); [apply AG; lia| lia| lia| assumption])|].
        split; [exact PA1|]. split; [exact IA1|].
        split; [apply (PMASKJ.base_keep L ar C LY LBX FF S 24576 W0 M M1 EKn); [intros a Ha; apply outside_W0; lia| exact BASE]|].
        split; [unfold s1; cbn [PMTK2.with_tb PM.p_tb PM.p_tg]; unfold PM.tb_ok in *; cbn [PM.vs_cap] in *; exact TBOK|].
        split; [unfold s1; rewrite (own_with_tb s _ _ OW1); exact HH1|]. split; [exact AM1|].
        split; [eapply L5LZ.model_rt_trans; [exact MRT| exact MRT1]|].
        split; [exact ILK|]. split; [exact IAW|].
        unfold s1; cbn [PMTK2.with_tb PM.p_tb PM.p_tg]. unfold PM.pot_text in *. try rewrite ETB in CRL. try rewrite ETB in CRK. cbn [PM.vs_cap] in *. split; [exact CRL|]. split; [exact CRK|].
        destruct (FRB _ Hfb) as (Fb0 & Fb1). cbn [ff_addr ff_class fst snd] in Fb0, Fb1. change (ff_bytes 5) with 2048 in Fb1.
        split; [apply (PMFA.accA_agree M M1 op PECA.RDR_BYTES); [apply AGSH; unfold PECA.RDR_BYTES; clear - Eop Fb0 Fb1; lia| exact ACC]|].

        cbn [PM.p_src].
        apply (content_agree M M1 s sm cr LK Aw (vml_of model) (proj1 (OTH _ _ QIN NEQ)) (fun B m Hin => proj1 (OTH B m ltac:(apply in_or_app; right; exact Hin)
                    ltac:(intros EB; apply (PMASKJ.fst_neq_appA (PM.parser_own s) LBX q0 c0 B m (PMASKJ.lb_nodup L ar C HI HIok _ _ _ _ _ _ _ HH)); [unfold PM.parser_own; rewrite ETB; cbn; right; right; left; reflexivity| exact Hin| symmetry; exact EB]))) ltac:(apply AG; clear - Eois Eos Etb Fb0 Fb1 TFA Hn0 Hc0; lia) HH PA IA CT). }
    apply (at_srd fx1 R1 M1 model1 s1 sm cr LK Aw); try assumption.
    all: first [ rewrite (KS1 2%nat) by inl; exact A2 | rewrite (KS1 8%nat) by inl; exact A8 | rewrite (KS1 9%nat) by inl; exact A9
               | rewrite (KS1 18%nat) by inl; exact A18 | rewrite (KS1 21%nat) by inl; exact A21 | rewrite (KS1 22%nat) by inl; exact A22
               | (intros x Hx; rewrite (KS1 x) by (cbn in Hx; repeat (destruct Hx as [<-|Hx]; [inl|]); destruct Hx); apply KP; exact Hx)
               | (unfold s1; cbn [PMTK2.with_tb PM.p_tb PM.vs_size]; reflexivity)
               | (unfold s1; cbn [PMTK2.with_tb PM.p_src]; exact U0) ].
Qed.

End Call.
End WithHeap.
End PECRS2bA.
