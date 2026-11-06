(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.

From Stdlib Require Import ZArith List Lia Bool FunctionalExtensionality.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.jsoncons.fuzz_ubjson_encoder.images Require Import AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S9 Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare ShapeAlg SpinAlg AsanAcct HeapIface HeapIfaceA HeapIfaceAEx IcptIfaceAB0 LibIface AxSymExec3 AxSymExec3Sound SegRun BigLinkBase BigLinkGlue L5Defs L5Core L5CoreKit L5Kn L5KnA L5LazyA L5DefsAB0 L5CoreAB0S9 L5CoreSpecsAB0S9 L5StepARB0S9 L5CoreBRB0S9 L5ADetailHRB0S9.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import PmLayout PmLayoutA.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S9 Require Import PmModel PmModelFacts PmStatics PmStaticsA PmSpecs PmSpecsA PmSpecsAX PeSpecsAb PnStatics PmModelFactsA PmStep PeStepAB0 PmParStep PmParKit PeBSrcKit PeBParKit LibIfaceAB.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import PeCLayout PeCLayoutB.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S9 Require Import PeCSink PeCModel PeCSpecs PeCFrame PeCSinkA PeCModelA PeCStaticsA PeCSpecsA PeCSpecsAb PeCFrameA PeBCReset1 PmBUarK PmBUar PeBRtvP.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import Eb0_code_b7050_b7054 Eb0_code_b7150_b7154.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.Spec Require Import UbjRef.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S9.Spec Require Import UbjRefFactsS9.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.

Module PEBCRTV.
Ltac inl := apply L5K.In_of_mem; vm_compute; reflexivity.
Abbreviation reg i := (Z_to_bv 5 (Z.of_nat i)).
Abbreviation RSEGS := AsanUbsan.M.loaded_segments.
Abbreviation AD := PeCLayoutB.CADDR_B.
Abbreviation AAD := PeCLayoutB.CAADDR_B.
Abbreviation EE := PeCLayoutB.EADDR_B.

Lemma slice_pos_1 p pos : 0 <= pos < blen p -> UbjRef.slice p pos 1 = [bat p pos].
Proof.
  intros Hp. unfold UbjRef.slice, bat, blen in *. change (Z.to_nat 1) with 1%nat.
  remember (Z.to_nat pos) as n. assert (Hn : (n < length p)%nat) by lia. clear Heqn Hp.
  revert p Hn. induction n as [|n IH]; intros [|x p] Hn; cbn in Hn |- *; try lia; [reflexivity|]. apply IH. lia.
Qed.
Lemma bat_byte p pos : UbjRefFactsS9.bytes_ok p -> 0 <= pos < blen p -> 0 <= bat p pos < 256.
Proof.
  intros HB Hp. unfold bat, blen in *. apply (Forall_nth (fun b => 0 <= b < 256) p); [exact HB| lia].
Qed.
Lemma u8_at_inj M a b b' : L5.u8_at RSEGS M a b -> L5.u8_at RSEGS M a b' -> 0 <= b < 256 -> 0 <= b' < 256 -> b = b'.
Proof.
  intros U U' Hb Hb'. unfold L5.u8_at in U, U'. rewrite U in U'.
  apply (f_equal (fun o : option (list byte) => match o with Some (x :: _) => bv_unsigned x | _ => 0 end)) in U'. cbn beta iota in U'.
  rewrite !Z_to_bv_small in U' by (unfold bv_modulus; cbn; Lia.lia). exact U'.
Qed.

Definition own (E : Z) (R : bvmap 5 word) (M : word -> option byte) : Prop :=
  L5.u64_at RSEGS M (E - 8) (bv_unsigned (getr R (reg 1))) /\ L5.u64_at RSEGS M (E - 16) (bv_unsigned (getr R (reg 8)))
  /\ L5.u64_at RSEGS M (E - 24) (bv_unsigned (getr R (reg 9))) /\ L5.u64_at RSEGS M (E - 32) (bv_unsigned (getr R (reg 18)))
  /\ L5.u64_at RSEGS M (E - 40) (bv_unsigned (getr R (reg 19))) /\ L5.u64_at RSEGS M (E - 48) (bv_unsigned (getr R (reg 20)))
  /\ L5.u64_at RSEGS M (E - 56) (bv_unsigned (getr R (reg 21))) /\ L5.u64_at RSEGS M (E - 64) (bv_unsigned (getr R (reg 22)))
  /\ L5.u64_at RSEGS M (E - 72) (bv_unsigned (getr R (reg 23))) /\ L5.u64_at RSEGS M (E - 80) (bv_unsigned (getr R (reg 24)))
  /\ L5.u64_at RSEGS M (E - 88) (bv_unsigned (getr R (reg 25))).
Definition ocell (E : Z) (a : Z) : Prop := E - 88 <= a < E.
Lemma own_agree E R M1 M1' : 0 <= E - 88 -> E <= 2 ^ 64 ->
  own E R M1 -> (forall a, ocell E a -> M1' (Z_to_bv 64 a) = M1 (Z_to_bv 64 a)) -> own E R M1'.
Proof.
  intros H0 H1 (C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8 & C9 & C10 & C11) AG. unfold own, ocell in *.
  repeat split; (eapply L5C.u64_at_agree; [ | | | eassumption]; [intros j Hj; apply AG; lia | lia | lia]).
Qed.

Lemma reg12_other (R : bvmap 5 word) v k : In k [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%nat -> getr (regupd R (reg 12) v) (reg k) = getr R (reg k).
Proof.
  intros Hk. assert (Hk' : k <> 12%nat /\ (k < 32)%nat) by (repeat (destruct Hk as [<-|Hk]; [split; lia|]); destruct Hk).
  apply PMPX.regupd_other_idx; lia.
Qed.

Lemma frame_ok5_push FF fb f : PECA.frame_ok5 FF fb -> PECA.frame_ok5 (f :: FF) fb.
Proof. intros ((r0 & Hf) & Hm). split; [exists r0; right; exact Hf| exact Hm]. Qed.

Tactic Notation "wr_mem" integer(n) := unfold PEC.W_crun, PMSP.W_run, PMSP.W_srcf, PMSP.err_W; cbn [app]; do n right; left; reflexivity.
Ltac wr_rng := unfold L5.in_rng, PMSP.o_src, PMSP.o_p, PMSP.o_is, PMSP.o_tb, PMSP.o_vec, PMSP.o_ec, PMSP.o_v, PESK.o_sink;
  cbn [fst snd pa_off_p pa_off_is pa_off_ec pa_off_v pe_off_sink pa_errcat_guard pa_atexit AD EE PeCLayoutB.CADDR_B PeCLayoutB.EADDR_B].

Section WithHeap.
Context {SCFG_P : ScfgP}.
Variables (L : asan_layout) (ar : asan_run) (C : asan_statics_cells) (HI : asan_iface) (P : PESKA.sink_policyA).
Hypothesis LY : PMB.layout L C.
Hypothesis HIok : HAJ.asan_iface_okR L ar C SCFG HI.
Variable IL : icpt_layout.
Hypothesis ICok : aicpt_ok L ar IL SCFG HI.
Hypothesis ILY : as0_icpt_layout IL.
Let LYa := PMB.ly_as0 L C LY.

Lemma content_keepA' LB FF sp scr W M M' fb p s str sm op :
  L5SAR.ek L ar LB FF sp scr W M M' -> PMKB.wapp W ->
  (forall f, In f FF -> 0 <= ff_addr f /\ ff_addr f + ff_bytes (ff_class f) <= 2 ^ 47) ->
  (forall b, In b LB -> 0 <= fst b /\ fst b + snd b <= 2 ^ 47) ->
  PMSPA.aobjA FF (PMSPA.o_is AD fb) 272 -> (forall i, PMSPA.o_is AD fb + 80 <= i < PMSPA.o_is AD fb + 80 + 24 -> L5.outside W i) ->
  incl (PM.vs_own str) LB -> In (PM.sr_qc (PM.p_src s), PM.CHUNK) LB ->
  (forall q m, In (q, m) LB -> PMKB.blk_out W q m) ->
  PM.iss_at RSEGS AD PMSPA.accA M (PMSPA.o_is AD fb) str sm -> PM.parser_at RSEGS AD PMSPA.accA PMSPA.annA M op (PMSPA.o_is AD fb) s ->
  PEC.content_ok RSEGS AD M fb p (PM.p_src s) str sm -> PEC.content_ok RSEGS AD M' fb p (PM.p_src s) str sm.
Proof.
  intros EK WAPP FRB BRB AO OW INCS QIN OB IA PA.
  pose proof IA as (_ & _ & _ & _ & _ & _ & _ & _ & _ & VS & _). pose proof VS as (_ & _ & VSF).
  pose proof PA as (_ & _ & _ & _ & _ & _ & _ & _ & _ & SRC & _). pose proof SRC as (_ & _ & _ & _ & _ & _ & _ & G1 & G2 & G3 & _).
  apply (PECFA.content_keepA RSEGS AD L ar LB FF sp scr W M M' EK WAPP FRB BRB fb p s str sm AO OW INCS).
  - intros c n q ->. cbn in VSF. destruct VSF as (_ & _ & _ & Hn & Hc & _ & _ & _). split; [lia|]. apply OB. apply INCS. cbn. left. reflexivity.
  - intros n ->. cbn in VSF. lia.
  - exact QIN.
  - apply OB. exact QIN.
  - exact G1.
  - exact G2.
  - exact G3.
Qed.

Theorem rtv_ok : PECSB.src_read_spec L ar HI -> PECSB.make_ec_spec L ar HI -> PECSB.read_value_spec L ar HI P -> PECSB.rtv_spec L ar HI P.
Proof.
  intros SR MKE RV. unfold PECSB.rtv_spec, PECSPA.rtv_spec, PECSPA.crun_spec.
  intros PMODE [] fx R M model K LBX FF LK Aw cr sp r fb cat p X s str sm en k e HH AM K0 ENT FRM FRS FOK SP32 ARGS CPRE INCS POK MP NB HB CRED KONT.
  destruct ENT as (Rra & RAok & Rsp & Rgp & Rtp & ASTK & STKSH). change (PMSPA.pm_scr 9) with 30720 in *. change (30720 / 8) with 3840 in STKSH.
  pose proof AM as (Mh & MI). pose proof ASTK as (A16 & SLO & SHI & SPT & SDEF & SUP). pose proof RAok as (Hr1 & Hr2).
  destruct ARGS as (A10 & A11 & A12).
  rewrite L5K.rl1 in Rra. rewrite L5K.rl2 in Rsp. rewrite L5K.rl3 in Rgp. rewrite L5K.rl4 in Rtp. rewrite L5K.rl10 in A10. rewrite L5K.rl11 in A11. rewrite L5K.rl12 in A12.
  destruct CPRE as (PA & IA & EA & VREF & SKA & BASE & ERR & TBOK & CONT & CL & ECS & ECI & ACCR).
  destruct MP as (PRE & DONE & HALT & DEPB & ESTKB & STKB). pose proof PRE as (PRE0 & MORE). pose proof PRE0 as (BOK & PPOS & PLH & PBAD & PED & PEOK).
  pose proof FOK as ((rs & Hfb) & Fal).
  set (op := PMSPA.o_p AD fb) in *. set (ov := PMSPA.o_v AD fb) in *. set (oec := PMSPA.o_ec AD fb) in *. set (ois := PMSPA.o_is AD fb) in *.
  set (osk := PESK.o_sink EE fb) in *.
  assert (Eop : op = fb + 592) by reflexivity. assert (Eov : ov = fb + 496) by reflexivity. assert (Eoec : oec = fb + 1120) by reflexivity.
  assert (Eois : ois = fb + 96) by reflexivity. assert (Eosk : osk = fb + 432) by reflexivity.

  pose proof (HAJ.aior_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as (WB & WF & FSAPP & FSCEIL & FSIMG & FSSH & STSH & _ & _ & STOP & ND & _).
  pose proof (WF _ Hfb) as (F1 & F2 & F3 & F4 & F5 & F6). cbn [ff_addr ff_class fst snd] in F1, F2, F3, F4, F5, F6. change (ff_bytes 5) with 2048 in *.
  unfold app_mem, BIGSHADOW_LO, BIGSHADOW_HI in FSAPP. unfold FS_BYTES in *.
  assert (AOF : forall a n, fb + 32 <= a -> a + n <= fb + 2040 -> PMSPA.aobjA FF a n).
  { intros a n H1 H2. exists (fb, 5, rs). split; [exact Hfb|]. cbn [ff_addr ff_class fst snd]. change (ff_bytes 5) with 2048. lia. }
  assert (FB8 : forall j, (fb + 8 * j) mod 8 = 0).
  { intros j. pose proof (Z.div_mod fb 2048 ltac:(lia)) as E. rewrite Fal, Z.add_0_r in E. rewrite E.
    replace (2048 * (fb / 2048) + 8 * j) with ((256 * (fb / 2048) + j) * 8) by lia. apply Z_mod_mult. }
  assert (O8 : op mod 8 = 0) by (rewrite Eop; replace (fb + 592) with (fb + 8 * 74) by lia; apply FB8).
  assert (Q8 : ov mod 8 = 0) by (rewrite Eov; replace (fb + 496) with (fb + 8 * 62) by lia; apply FB8).
  assert (I8 : ois mod 8 = 0) by (rewrite Eois; replace (fb + 96) with (fb + 8 * 12) by lia; apply FB8).
  assert (C8m : oec mod 8 = 0) by (rewrite Eoec; replace (fb + 1120) with (fb + 8 * 140) by lia; apply FB8).
  pose proof (L5SAR.vis_pack L ar C HI LYa HIok _ FF LK cr Aw M model HH) as (HOFF & VIS & VIMG & VFS & VBLK & VBSH & VFSSH & VSTSH).
  set (H := ahid Aw model) in *. set (MV := mrestrict H M) in *.
  pose proof (L5SAR.aobj_facts L ar C HI LYa HIok _ FF LK cr Aw M model op 384 sp 30720 HH (PMKB.aobj_of_aobjA FF op 384 (AOF op 384 ltac:(lia) ltac:(lia)) O8) ltac:(lia) ltac:(reflexivity))
    as ((O1 & O2 & O3 & O4 & O5) & OBIG & ODEF & OVIS & OSHV & OCL & OSHCL).
  pose proof (L5SAR.aobj_facts L ar C HI LYa HIok _ FF LK cr Aw M model ois 272 sp 30720 HH (PMKB.aobj_of_aobjA FF ois 272 (AOF ois 272 ltac:(lia) ltac:(lia)) I8) ltac:(lia) ltac:(reflexivity))
    as ((I1 & I2 & I3 & I4 & I5) & IBIG & IDEF & IVIS & ISHV & ICL & ISHCL).
  pose proof (HAJ.aior_statics _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as ST. rewrite (L5A.aly_segs L C LYa) in ST.
  pose proof (L5A.statics_facts L C M LYa ST) as (GOT & CSB & CUAR & _).

  pose proof PA as (P0 & PD & PC0 & P8 & P9 & P12 & P16 & P20 & PNI & PSRC & P320 & P328 & PC320 & PTB & PVEC & PB1 & PB2 & PB3).
  pose proof PSRC as (PS240 & _ & _ & _ & _ & _ & _ & SG1 & SG2 & SG3 & _).
  destruct CL as (Lmore & Ldone & Ldepth & Lstk & Lpos & Lestk & Ledepth & Lz & Lbad).
  pose proof (Lpos MORE DONE) as POS.
  set (LB := PEC.owned s en k ++ LBX) in *.
  assert (EPO : LB = PM.parser_own s ++ (PEC.enc_own en ++ PESK.sink_own k ++ LBX)) by (unfold LB; rewrite PEC.owned_app; reflexivity).
  assert (Iq : In (PM.sr_qc (PM.p_src s), PM.CHUNK) LB) by (rewrite EPO; apply in_or_app; left; unfold PM.parser_own, PM.src_own; left; reflexivity).
  assert (Ib : In (PM.p_b s, 32 * 2 ^ PM.p_k s) LB) by (rewrite EPO; apply in_or_app; left; unfold PM.parser_own, PM.vec_own; right; left; reflexivity).
  pose proof (WB _ Ib) as ((Bb0 & Bb1 & Bb2 & Bb3 & Bb4 & Bb5) & _). cbn [fst snd] in Bb0, Bb1, Bb2, Bb3, Bb4, Bb5.
  pose proof (WB _ Iq) as ((Bq0 & Bq1 & Bq2 & Bq3 & Bq4 & Bq5) & _). cbn [fst snd] in Bq0, Bq1, Bq2, Bq3, Bq4, Bq5. unfold app_mem, BIGSHADOW_LO, BIGSHADOW_HI, PM.CHUNK in Bq5, Bq4.
  destruct Bq5 as (_ & Bq5 & _).
  pose proof (PMBSK.blk_img L ar C HI LY HIok _ _ _ _ _ _ _ _ _ HH Iq) as Bqi. unfold PM.CHUNK in Bqi.
  assert (BRB : forall x, In x LB -> 0 <= fst x /\ fst x + snd x <= 2 ^ 47) by exact (PMBSK.brb_of L ar C HI HIok _ _ _ _ _ _ _ HH).
  assert (FRB : forall f, In f FF -> 0 <= ff_addr f /\ ff_addr f + ff_bytes (ff_class f) <= 2 ^ 47) by exact (PMBSK.frb_of L ar C HI HIok _ _ _ _ _ _ _ HH).
  assert (PINC : incl (PM.parser_own s) LB) by (rewrite EPO; apply incl_appl; apply incl_refl).
  assert (INCX : incl LBX LB) by (unfold LB; apply incl_appr; apply incl_refl).
  assert (SINC : incl (PM.vs_own str) LB) by (unfold LB; apply incl_appr; exact INCS).
  assert (EINC : incl (PEC.enc_own en) LB).
  { unfold LB, PEC.owned. intros x Hx. apply in_or_app. left. apply in_or_app. right. apply in_or_app. left. exact Hx. }
  assert (KINC : incl (PESK.sink_own k) LB).
  { unfold LB, PEC.owned. intros x Hx. apply in_or_app. left. apply in_or_app. right. apply in_or_app. right. exact Hx. }
  assert (AOP : PMSPA.aobjA FF op 384) by (apply AOF; lia).
  assert (AOI : PMSPA.aobjA FF ois 272) by (apply AOF; lia).

  assert (CV : forall a m, op <= a -> a + m <= op + 384 -> L5A.avis H a m) by (intros a m X1 X2; eapply L5A.avis_sub; [exact OVIS| lia| lia]).
  assert (CVi : forall a m, ois <= a -> a + m <= ois + 272 -> L5A.avis H a m) by (intros a m X1 X2; eapply L5A.avis_sub; [exact IVIS| lia| lia]).
  assert (BASE' : PMSTA.base_okA RSEGS PMB.AD M) by exact BASE.
  pose proof (PMBSK.mach_vis L ar C HI LY HIok _ FF LK cr Aw M model HH BASE') as (IC0 & CSBv & CUARv). fold H in IC0, CSBv, CUARv. fold MV in IC0, CSBv, CUARv.
  pose proof (PMBSK.stk_vis L ar C HI LY HIok _ FF LK cr Aw M model sp 30720 96 HH ASTK ltac:(lia)) as (SL96 & SH96 & SWR).

  pose proof (PEBRTVP.artA_conc fx R MV (fun j => match j with 2%nat => sp | 36%nat => op | 37%nat => ov | 38%nat => oec | _ => 0 end)) as PP.
  cbn beta iota in PP.
  L5SAR.feed PP ltac:(first [assumption | unfold PEBRTVP.aligned; assumption | clear - SL96 SHI SPT; lia | clear - O1 O3; lia | clear - O1 O3 Eop Eov; lia | clear - O1 O3 Eop Eoec; lia]).
  destruct PP as (fx1 & R1 & M1v & MG1 & _ & FRZ1 & MS1 & KS1 & T1 & T2 & T8 & T9 & T10 & _ & _ & T19 & T20 & T21 & T25
                 & C88 & C80 & C72 & C64 & C56 & C48 & C40 & C32 & C24 & C16 & C8 & C96).
  unfold PMSPA.cfg. cbn [pa_rtv AD PeCLayoutB.CADDR_B].
  apply (L5SAR.apiece L ar C HI LYa HIok _ FF LK cr Aw M model fx fx1 R 0xb6f0c R1 0x5ec3c M1v (fun a => sp - 96 <= a < sp - 96 + 96) K HH AM MS1 MG1).
  { intros a Ha N. apply FRZ1; [exact Ha| exact N]. }
  { intros a Ha Wa. split; [|intros X'; clear - X' Wa SLO SPT; lia]. unfold aclientw, aclient_g. right; left. split; [clear - Wa SL96 SHI SPT; lia| intros X'; clear - X'; lia]. }
  intros M1 model1 HH1 AM1 MRT1 HID1 VIS1 MGM1 FR1 VV1. change (mrestrict H M1 = M1v) in VIS1.
  assert (NCS0 : forall a, sp - 96 <= a < sp -> ~ aclient L ar LB FF sp 30720 a).
  { intros a Xa Hc. destruct (L5SAR.aclient_cases L ar C HI LYa HIok _ FF LK cr Aw M _ sp 30720 a HH SPT Hc) as [Y|Y].
    - clear - Xa Y; lia.
    - clear - Xa Y SL96; lia. }
  assert (EK01f : L5SAR.ek L ar LB FF sp 30720 [] M M1).
  { apply (L5SAR.ek_piece L ar LB FF sp 30720 [] M M1 (fun a => sp - 96 <= a < sp - 96 + 96) FR1). intros a Ha Hc _ X'. apply (NCS0 a); [clear - X'; lia| exact Hc]. }
  assert (DK01f : L5SAR.dk L ar LB FF sp 30720 M M1) by (apply L5SAR.dk_grows; exact MGM1).
  pose proof (PMKB.ek_sublb L ar LB LBX FF sp 30720 [] M M1 INCX EK01f) as EK01.
  pose proof (PMKB.dk_sublb L ar LB LBX FF sp 30720 M M1 INCX DK01f) as DK01.

  assert (SV1 : forall a v, sp - 96 <= a -> a + 8 <= sp -> L5.u64_at RSEGS M1v a v -> L5.u64_at RSEGS M1 a v).
  { intros a v Ha1 Ha2 X'. apply (proj1 (L5A.u64_at_vis H M1 a v (VIS a 8 ltac:(clear - Ha1 SL96 SPT; lia) ltac:(clear - Ha2 SHI SPT; lia)) ltac:(clear - Ha1 SL96 SPT; lia) ltac:(clear - Ha2 SHI SPT; lia))).
    rewrite VIS1. exact X'. }
  assert (OWN1 : own sp R M1).
  { unfold own. split; [apply SV1; [clear; lia| clear; lia| exact C8]|]. split; [apply SV1; [clear; lia| clear; lia| exact C16]|].
    split; [apply SV1; [clear; lia| clear; lia| exact C24]|]. split; [apply SV1; [clear; lia| clear; lia| exact C32]|].
    split; [apply SV1; [clear; lia| clear; lia| exact C40]|]. split; [apply SV1; [clear; lia| clear; lia| exact C48]|].
    split; [apply SV1; [clear; lia| clear; lia| exact C56]|]. split; [apply SV1; [clear; lia| clear; lia| exact C64]|].
    split; [apply SV1; [clear; lia| clear; lia| exact C72]|]. split; [apply SV1; [clear; lia| clear; lia| exact C80]|].
    apply SV1; [clear; lia| clear; lia| exact C88]. }
  clear C88 C80 C72 C64 C56 C48 C40 C32 C24 C16 C8 C96 SV1.

  assert (FRk0 : ff_room 0 FF LK) by (pose proof (FRM 0 ltac:(left; reflexivity)) as X'; unfold ff_room; clear - X'; lia).
  change 0x5ec3c with (PMB.SM_PC 0).
  apply (PMBUAR.uar_sm L ar C HI LY HIok 0 LBX (PEC.owned s en k) FF LK cr Aw sp 30720 (sp - 96) (sp - 88) sp (ocell sp) (own sp R)
           fx1 R1 M M1 model model1 K 0xb6f7c ltac:(left; reflexivity) HH HH1 AM1 K0 ASTK MGM1 EK01 DK01).
  { rewrite L5K.rl2. exact T2. }
  { rewrite L5K.rl4. rewrite (KS1 4%nat) by inl. rewrite <- L5K.rl4. exact Rtp. }
  { rewrite L5K.rl1. exact T1. }
  { reflexivity. }
  { clear; lia. }
  { replace (sp - 96) with (sp + (-6) * 16) by (clear; lia). rewrite Z_mod_plus_full. exact A16. }
  { clear; lia. } { clear; lia. } { clear; lia. } { clear; lia. }
  { intros a Ha. exact Ha. }
  { intros Ma Mb OW AG. apply (own_agree sp R Ma Mb ltac:(clear - SL96 SPT; lia) ltac:(clear - SHI SPT; lia) OW AG). }
  { exact FRk0. }
  { intros f Hf. specialize (FRS f Hf). clear - FRS; lia. }
  intros R2 M2 model2 F fl LK2 G G10 RP2 AM2 MRT2 ASTK2 EK02 DK02 EK12f DK12f AGF FW FSHW FSHZ FLC FLW FDEF VF VSH VFL APART.
  change (ff_bytes 0) with 64 in *. change (64 / 8) with 8 in *. change (64 - 8) with 56 in *.
  pose proof G as G'. destruct G' as [_ _ _ _ _ _ _ GFS1 GFS2 GFCEIL GLKI2 GFLP GFLNC GHH2 GFLC GFR GF8 GFBIG GF32 GFLA GFLR GFLBIG GNCF GNCS].
  change (ff_bytes 0) with 64 in *.
  fold LB in EK12f, DK12f, GHH2, APART.

  pose proof (L5SAR.ek_trans L ar LB FF sp 30720 [] M M1 M2 EK01f EK12f) as EK02f.
  pose proof (L5SAR.dk_trans L ar LB FF sp 30720 M M1 M2 DK01f DK12f) as DK02f.
  assert (PA2 : PM.parser_at RSEGS AD PMSPA.accA PMSPA.annA M2 op ois s).
  { apply (PMKB.parser_keepA RSEGS AD L ar LB FF sp 30720 [] M M2 EK02f PMKB.wapp_nil FRB BRB _ _ _ AOP); [exact PINC| intros i _ r0 []| intros i _ r0 []| intros i _ r0 []| intros c0 n0 p0 _ i _ r0 []| exact PA]. }
  assert (IA2 : PM.iss_at RSEGS AD PMSPA.accA M2 ois str sm).
  { apply (PMKB.iss_keepA RSEGS AD L ar LB FF sp 30720 [] M M2 EK02f PMKB.wapp_nil FRB BRB ois str sm AOI); [exact SINC| intros i _ r0 []| intros c0 n0 p0 _ i _ r0 []| exact IA]. }
  assert (BASE2 : PMSTA.base_okA RSEGS AD M2).
  { change (PMSTA.base_okA RSEGS PMB.AD M2). apply (PMBSK.base_keep L ar C LY LB FF sp 30720 [] M M2 EK02f); [intros a _ r0 []| exact BASE]. }
  assert (ACC2 : PMSPA.accA M2 op PECA.RDR_BYTES) by exact (PMKB.acc_keepA' L ar LB FF sp 30720 [] M M2 EK02f PMKB.wapp_nil FRB op 392 (AOF op 392 ltac:(lia) ltac:(lia)) ACCR).
  assert (HH2 : ri_inv HI LB ((F, 0, sp - 96 + 32) :: FF) LK2 cr Aw M2 (vml_of model2)) by exact GHH2.
  set (FF' := (F, 0, sp - 96 + 32) :: FF) in *.
  assert (FOK' : PECA.frame_ok5 FF' fb) by exact (frame_ok5_push FF fb (F, 0, sp - 96 + 32) FOK).
  assert (AOF' : forall a n, fb + 32 <= a -> a + n <= fb + 2040 -> PMSPA.aobjA FF' a n) by (intros a n X1 X2; apply PMBUAR.aobjA_push; apply AOF; [exact X1| exact X2]).
  pose proof (PMBPAR.op_vis L ar C HI LY HIok _ _ LK2 cr Aw M2 model2 fb _ s HH2 FOK' PA2) as ((_ & _ & _) & Zop2 & Z322 & Z202 & OWR2 & _ & OVIS2 & _ & _).
  set (H2 := ahid Aw model2) in *. set (MV2 := mrestrict H2 M2) in *.
  assert (BASE2' : PMSTA.base_okA RSEGS PMB.AD M2) by exact BASE2.
  pose proof (PMBSK.mach_vis L ar C HI LY HIok _ _ LK2 cr Aw M2 model2 HH2 BASE2') as (W0 & W1 & W2). fold H2 in W0, W1, W2. fold MV2 in W0, W1, W2.
  pose proof (PMBSK.stk_vis L ar C HI LY HIok _ _ LK2 cr Aw M2 model2 sp 30720 96 HH2 ASTK2 ltac:(lia)) as (_ & _ & SWR2). fold H2 in SWR2. fold MV2 in SWR2.
  pose proof (L5SAR.aobj_facts L ar C HI LYa HIok _ FF' LK2 cr Aw M2 model2 ois 272 sp 30720 HH2 (PMKB.aobj_of_aobjA FF' ois 272 (AOF' ois 272 ltac:(lia) ltac:(lia)) I8) ltac:(lia) ltac:(reflexivity))
    as (_ & _ & IDEF2 & IVIS2 & _). fold H2 in IVIS2.
  assert (Zis2 : L5KA.zeros_at MV2 (ois / 8 + SB) 34).
  { assert (IACC : PMSPA.accA M2 ois 272).
    { destruct IA2 as (_ & _ & C0 & _ & _ & _ & _ & _ & _ & _ & _ & _ & IOS & _). destruct IOS as (_ & _ & _ & _ & _ & _ & _ & IC & _).
      intros a Ha. destruct (Z_lt_le_dec a (ois + 120)) as [X'|X']; [apply C0; lia| apply IC; lia]. }
    change 34 with (272 / 8). apply (PMKB.obj_shadow_vis L ar C HI LYa HIok _ FF' LK2 cr Aw M2 model2 ois 272 HH2 (AOF' ois 272 ltac:(lia) ltac:(lia)) I8); [lia| reflexivity| exact IACC]. }
  assert (IWR2 : L5.writable RSEGS MV2 ois 272).
  { apply (proj2 (L5A.writable_vis H2 M2 ois 272 IVIS2 ltac:(lia) ltac:(lia))). apply (L5C.writable_of_defined RSEGS); [exact IDEF2| lia| lia]. }
  pose proof (PMBSK.img_shz_vis L ar C HI LY IL ICok ILY _ _ LK2 cr Aw M2 model2 0x13b520 1 HH2 ltac:(lia) ltac:(lia) ltac:(reflexivity) ltac:(lia) ltac:(lia)) as ZOT2.
  fold H2 in ZOT2. fold MV2 in ZOT2.
  assert (U264 : L5.u64_at RSEGS MV2 (op + 264) ois).
  { pose proof PA2 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & PSRC2 & _). pose proof PSRC2 as (PS240b & _).
    replace (op + 264) with (op + 24 + 240) by (clear; lia).
    apply (proj2 (L5A.u64_at_vis H2 M2 _ ois (OVIS2 (op + 24 + 240) 8 ltac:(clear; lia) ltac:(clear; lia)) ltac:(clear - O1; lia) ltac:(clear - O1 O3; lia))). exact PS240b. }
  pose proof IA2 as (IS0 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & IOSB & _). pose proof IOSB as (_ & IST & _ & _ & _ & _ & _ & _ & STV).
  assert (UIS0 : L5.u64_at RSEGS MV2 ois 1291576).
  { apply (proj2 (L5A.u64_at_vis H2 M2 ois _ (L5A.avis_sub H2 ois 272 ois 8 IVIS2 ltac:(clear; lia) ltac:(clear; lia)) ltac:(clear - I1; lia) ltac:(clear - I1 I3; lia))). exact IS0. }
  assert (UIST : L5.u32_at RSEGS MV2 (ois + 152) (PM.sm_st sm)).
  { replace (ois + 152) with (ois + 120 + 32) by (clear; lia).
    apply (proj2 (L5A.u32_at_vis H2 M2 _ _ (L5A.avis_sub H2 ois 272 (ois + 120 + 32) 4 IVIS2 ltac:(clear; lia) ltac:(clear; lia)) ltac:(clear - I1; lia) ltac:(clear - I1 I3; lia))). exact IST. }

  assert (CLfb : forall a n, fb + 32 <= a -> a + n <= fb + 2040 -> 0 < n -> forall i, 0 <= i < n -> aclient L ar LB FF 0 0 (a + i)).
  { intros a n X1 X2 X3 i Hi. unfold aclient, aclient_g. do 3 right; left. exists (fb, 5, rs). split; [exact Hfb|]. cbn [ff_addr ff_class fst snd].
    change (ff_bytes 5) with 2048. split; [clear - X1 X2 Hi; lia| intros Y; clear - X1 X2 Hi Y; lia]. }
  destruct (APART op 384 0 0 (CLfb op 384 ltac:(clear - Eop; lia) ltac:(clear - Eop; lia) ltac:(clear; lia)) ltac:(clear; lia)) as (ApF & ApSF & ApFL).
  destruct (APART ois 272 0 0 (CLfb ois 272 ltac:(clear - Eois; lia) ltac:(clear - Eois; lia) ltac:(clear; lia)) ltac:(clear; lia)) as (AiF & AiSF & AiFL).
  destruct (APART ov 56 0 0 (CLfb ov 56 ltac:(clear - Eov; lia) ltac:(clear - Eov; lia) ltac:(clear; lia)) ltac:(clear; lia)) as (AvF & AvSF & AvFL).
  destruct (APART oec 16 0 0 (CLfb oec 16 ltac:(clear - Eoec; lia) ltac:(clear - Eoec; lia) ltac:(clear; lia)) ltac:(clear; lia)) as (AeF & AeSF & AeFL).
  assert (CLsh : forall a n, fb / 8 + SB <= a -> a + n <= fb / 8 + SB + 256 -> 0 < n -> forall i, 0 <= i < n -> aclient L ar LB FF 0 0 (a + i)).
  { intros a n X1 X2 X3 i Hi. unfold aclient, aclient_g. do 5 right; left. exists (fb, 5, rs). split; [exact Hfb|]. cbn [ff_addr ff_class fst snd].
    change (ff_bytes 5) with 2048. unfold in_shadow_of, S. unfold SB in *.
    assert (D1 : (fb + 2048 - 1) / 8 = fb / 8 + 255).
    { pose proof (Z.div_mod fb 2048 ltac:(lia)) as Dm. rewrite Fal, Z.add_0_r in Dm. rewrite Dm.
      replace (2048 * (fb / 2048) + 2048 - 1) with (7 + (256 * (fb / 2048) + 255) * 8) by (clear; lia). rewrite Z.div_add by lia.
      replace (2048 * (fb / 2048)) with ((256 * (fb / 2048)) * 8) by (clear; lia). rewrite Z.div_mul by lia. clear; lia. }
    rewrite D1. clear - X1 X2 Hi. lia. }
  assert (SHof : forall d, op = fb + 8 * d -> op / 8 + SB = fb / 8 + SB + d).
  { intros d Ed. rewrite Ed. pose proof (Z.div_mod fb 2048 ltac:(lia)) as Dm. rewrite Fal, Z.add_0_r in Dm. rewrite Dm.
    replace (2048 * (fb / 2048) + 8 * d) with ((256 * (fb / 2048) + d) * 8) by (clear; lia). rewrite Z.div_mul by lia.
    replace (2048 * (fb / 2048)) with ((256 * (fb / 2048)) * 8) by (clear; lia). rewrite Z.div_mul by lia. clear; lia. }
  assert (SHop : op / 8 + SB = fb / 8 + SB + 74) by (apply SHof; clear - Eop; lia).
  assert (SHis : ois / 8 + SB = fb / 8 + SB + 12).
  { rewrite Eois. pose proof (Z.div_mod fb 2048 ltac:(lia)) as Dm. rewrite Fal, Z.add_0_r in Dm. rewrite Dm.
    replace (2048 * (fb / 2048) + 96) with ((256 * (fb / 2048) + 12) * 8) by (clear; lia). rewrite Z.div_mul by lia.
    replace (2048 * (fb / 2048)) with ((256 * (fb / 2048)) * 8) by (clear; lia). rewrite Z.div_mul by lia. clear; lia. }
  clear SHof.
  destruct (APART (op / 8 + SB) 48 0 0 (CLsh (op / 8 + SB) 48 ltac:(clear - SHop; lia) ltac:(clear - SHop; lia) ltac:(clear; lia)) ltac:(clear; lia)) as (_ & AsopSF & _).
  destruct (APART (ois / 8 + SB) 34 0 0 (CLsh (ois / 8 + SB) 34 ltac:(clear - SHis; lia) ltac:(clear - SHis; lia) ltac:(clear; lia)) ltac:(clear; lia)) as (_ & AsisSF & _).

  assert (R2c : forall j, In j [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%nat -> getr R2 (reg j) = getr R1 (reg j)).
  { intros j Hj. apply (L5SAR.cs_of_preserved R1 R2 j RP2 Hj). }
  assert (B2R : getr R2 (reg 2) = Z_to_bv 64 (sp - 96)) by (rewrite (R2c 2%nat) by inl; exact T2).
  assert (B8R : getr R2 (reg 8) = Z_to_bv 64 sp) by (rewrite (R2c 8%nat) by inl; exact T8).
  assert (B9R : getr R2 (reg 9) = Z_to_bv 64 (sp - 96)) by (rewrite (R2c 9%nat) by inl; exact T9).
  assert (B19R : getr R2 (reg 19) = Z_to_bv 64 oec) by (rewrite (R2c 19%nat) by inl; exact T19).
  assert (B20R : getr R2 (reg 20) = Z_to_bv 64 op) by (rewrite (R2c 20%nat) by inl; exact T20).
  assert (B21R : getr R2 (reg 21) = Z_to_bv 64 ov) by (rewrite (R2c 21%nat) by inl; exact T21).
  assert (B25R : getr R2 (reg 25) = Z_to_bv 64 2147450880) by (rewrite (R2c 25%nat) by inl; exact T25).
  assert (B10R : getr R2 (reg 10) = Z_to_bv 64 F) by (rewrite <- L5K.rl10; exact G10).
  assert (FLCv : L5.u64_at RSEGS MV2 (F + 56) fl) by (replace (F + 56) with (F + 64 - 8) by (clear; lia); exact FLC).
  assert (Q0 : 0 <= sp < 2 ^ 64 /\ 0 <= op < 2 ^ 64 /\ 0 <= ov < 2 ^ 64 /\ 0 <= oec < 2 ^ 64 /\ 0 <= ois < 2 ^ 64 /\ 0 <= F < 2 ^ 64 /\ 0 <= fl < 2 ^ 64)
    by (clear - SL96 SHI SPT O1 O3 Eop Eov Eoec Eois GFR GFLR; lia).
  destruct Q0 as (Q0a & Q0b & Q0c & Q0d & Q0e & Q0f & Q0g).
  assert (Q1 : 140735332487264 <= sp <= 140737488355328) by (clear - SL96 SHI SPT; lia).
  assert (Q2 : (sp - 96) + 96 <= op \/ op + 384 <= (sp - 96)) by (clear - O2 SL96; lia).
  assert (Q3 : 6930432 <= F <= 140737488355264) by (clear - GFR; lia).
  assert (Q4 : (sp - 96) + 96 <= F \/ F + 64 <= (sp - 96)) by (clear - GFCEIL SL96; lia).
  assert (Q5 : (sp - 96) + 96 <= fl \/ fl + 1 <= (sp - 96)) by (clear - GFLR SL96; lia).
  assert (Q6 : (sp - 96) + 96 <= ois \/ ois + 272 <= (sp - 96)) by (clear - I2 SL96; lia).
  assert (Q7 : 4096 <= fl <= 140737488355327) by (clear - GFLR; lia).
  assert (Q8' : F + 64 <= 65536 \/ 65536 + 1204292 <= F) by (clear - GFR; lia).
  assert (Q9 : ((F / 8) + 2147450880) + 8 <= 2147612324 \/ 2147612324 + 1 <= ((F / 8) + 2147450880)).
  { clear - GFR GF8. unfold SB in *. assert (F / 8 >= 849920) by (apply Z.le_ge; apply Z.div_le_lower_bound; lia). lia. }
  assert (Q10 : op + 384 <= ois \/ ois + 272 <= op) by (clear - Eop Eois; lia).
  assert (Q11 : 6930432 <= op <= 140737488354944) by (clear - O1 O3; lia).
  assert (Q12 : 6930432 <= ois <= 140737488355056) by (clear - I1 I3; lia).
  unfold SB in AsopSF, AsisSF, ApSF, AiSF.
  assert (PB : exists (fx3 : FPState) R3 M3v, mem_grows MV2 M3v
            /\ (forall i, 0 <= i < 2 ^ 64 -> ~ (sp - 96 <= i < sp - 96 + 8) -> ~ (F <= i < F + 24) -> ~ (F / 8 + 2147450880 <= i < F / 8 + 2147450880 + 8) ->
                  M3v (Z_to_bv 64 i) = MV2 (Z_to_bv 64 i))
            /\ msteps RSEGS (L5A.st fx1 R2 0xb6f7c MV2) (L5A.st fx3 R3 0xb9148 M3v)
            /\ (forall x, In x [2; 3; 4; 8; 9; 19; 20; 21; 25; 26; 27]%nat -> getr R3 (reg x) = getr R2 (reg x))
            /\ getr R3 (reg 1) = Z_to_bv 64 749724 /\ getr R3 (reg 10) = Z_to_bv 64 (op + 24) /\ getr R3 (reg 11) = Z_to_bv 64 (F + 32)
            /\ getr R3 (reg 12) = Z_to_bv 64 1 /\ getr R3 (reg 18) = Z_to_bv 64 F /\ getr R3 (reg 22) = Z_to_bv 64 (F + 32)
            /\ getr R3 (reg 23) = Z_to_bv 64 F /\ getr R3 (reg 24) = Z_to_bv 64 ((F / 8) + 2147450880)
            /\ L5.u8_at RSEGS M3v ((F / 8) + 2147450884) 1 /\ L5.defined M3v (F + 24) 40).
  { destruct STV as [STE|STE]; rewrite STE in UIST.
    - pose proof (PEBRTVP.artB0_conc fx1 R2 MV2 (fun j => match j with 2%nat => sp | 36%nat => op | 37%nat => ov | 38%nat => oec | 45%nat => ois
                                                  | 47%nat => F | 48%nat => fl | _ => 0 end)) as PP. cbn beta iota in PP.
      L5SAR.feed PP ltac:(first [assumption | unfold PEBRTVP.aligned; assumption]).
      destruct PP as (fx3 & R3 & M3v & MG3 & _ & FRZ3 & MS3 & KS3 & Y1 & Y10 & Y11 & Y12 & _ & _ & Y18 & Y22 & Y23 & Y24 & Y4 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & YD).
      exists fx3, R3, M3v. split; [exact MG3|]. split; [intros i Hi N1 N2 N3; apply FRZ3; [exact Hi| intros X'; apply N1; clear - X'; lia| intros X'; apply N2; clear - X'; lia| intros X'; apply N3; clear - X'; lia]|].
      split; [exact MS3|]. split; [intros x Hx; apply KS3; revert x Hx; apply (L5K.incl_b [2; 3; 4; 8; 9; 19; 20; 21; 25; 26; 27]%nat); vm_compute; reflexivity|].
      repeat (split; [assumption|]). exact YD.
    - pose proof (PEBRTVP.artB2_conc fx1 R2 MV2 (fun j => match j with 2%nat => sp | 36%nat => op | 37%nat => ov | 38%nat => oec | 45%nat => ois
                                                  | 47%nat => F | 48%nat => fl | _ => 0 end)) as PP. cbn beta iota in PP.
      L5SAR.feed PP ltac:(first [assumption | unfold PEBRTVP.aligned; assumption]).
      destruct PP as (fx3 & R3 & M3v & MG3 & _ & FRZ3 & MS3 & KS3 & Y1 & Y10 & Y11 & Y12 & _ & _ & Y18 & Y22 & Y23 & Y24 & Y4 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & YD).
      exists fx3, R3, M3v. split; [exact MG3|]. split; [intros i Hi N1 N2 N3; apply FRZ3; [exact Hi| intros X'; apply N1; clear - X'; lia| intros X'; apply N2; clear - X'; lia| intros X'; apply N3; clear - X'; lia]|].
      split; [exact MS3|]. split; [intros x Hx; apply KS3; revert x Hx; apply (L5K.incl_b [2; 3; 4; 8; 9; 19; 20; 21; 25; 26; 27]%nat); vm_compute; reflexivity|].
      repeat (split; [assumption|]). exact YD. }
  destruct PB as (fx3 & R3 & M3v & MG3 & FRZ3 & MS3 & KS3 & Y1 & Y10 & Y11 & Y12 & Y18 & Y22 & Y23 & Y24 & Y4 & YD).
  set (W3 := fun a => (sp - 96 <= a < sp - 96 + 8) \/ (F <= a < F + 24) \/ (F / 8 + 2147450880 <= a < F / 8 + 2147450880 + 8)).
  apply (L5SAR.apiece L ar C HI LYa HIok LB FF' LK2 cr Aw M2 model2 fx1 fx3 R2 0xb6f7c R3 0xb9148 M3v W3 K HH2 AM2 MS3 MG3).
  { intros a Ha Hn. apply FRZ3; [exact Ha| intros X'; apply Hn; left; exact X'| intros X'; apply Hn; right; left; exact X'| intros X'; apply Hn; right; right; exact X']. }
  { intros a Ha Wa. split.
    - destruct Wa as [X'|[X'|X']].
      + unfold aclientw, aclient_g. right; left. split; [clear - X' SL96 SHI SPT; lia| intros Y; clear - Y; lia].
      + apply (L5SAR.fframe_client L ar LB FF' 0 0 F 0 (sp - 96 + 32)); [left; reflexivity| change (ff_bytes 0) with 64; clear - X'; lia].
      + apply (L5SAR.fframe_shadow_client L ar LB FF' 0 0 F 0 (sp - 96 + 32)); [left; reflexivity|]. change (ff_bytes 0) with 64.
        unfold in_shadow_of, S. rewrite (proj1 (proj2 GF8)). unfold SB. clear - X'; lia.
    - destruct Wa as [X'|[X'|X']]; clear - X' GFR SL96 SPT; lia. }
  intros M3 model3 HH3 AM3 MRT3 HID3 VIS3 MGM3 FR3 VV3. change (mrestrict H2 M3 = M3v) in VIS3.
  assert (Y4' : L5.u8_at RSEGS M3 ((F / 8) + 2147450884) 1).
  { apply (proj1 (L5A.u8_at_vis H2 M3 ((F / 8) + 2147450884) 1 (L5A.avis_sub H2 (F / 8 + SB) 8 ((F / 8) + 2147450884) 1 VSH ltac:(unfold SB; clear; lia) ltac:(unfold SB; clear; lia))
                  ltac:(clear - Q0f GFR; lia) ltac:(clear - GFR; lia))).
    rewrite VIS3. exact Y4. }
  assert (YD' : L5.defined M3 (F + 24) 40).
  { apply (proj1 (L5A.defined_vis H2 M3 (F + 24) 40 (L5A.avis_sub H2 F 64 (F + 24) 40 VF ltac:(clear; lia) ltac:(clear; lia)))). rewrite VIS3. exact YD. }
  assert (EK23f : L5SAR.ek L ar LB FF sp 30720 [] M2 M3).
  { apply (L5SAR.ek_piece L ar LB FF sp 30720 [] M2 M3 W3 FR3). intros a Ha Hc _ X'. destruct X' as [X'|[X'|X']].
    - apply (NCS0 a); [clear - X'; lia| exact Hc].
    - destruct (APART a 1 sp 30720 ltac:(intros i Hi; replace (a + i) with a by (clear - Hi; lia); exact Hc) ltac:(clear; lia)) as (Y & _). clear - X' Y; lia.
    - destruct (APART a 1 sp 30720 ltac:(intros i Hi; replace (a + i) with a by (clear - Hi; lia); exact Hc) ltac:(clear; lia)) as (_ & Y & _). unfold SB in Y. clear - X' Y; lia. }
  pose proof (L5SAR.ek_trans L ar LB FF sp 30720 [] M M2 M3 EK02f EK23f) as EK03f.
  assert (DK23f : L5SAR.dk L ar LB FF sp 30720 M2 M3) by (apply L5SAR.dk_grows; exact MGM3).
  pose proof (L5SAR.dk_trans L ar LB FF sp 30720 M M2 M3 DK02f DK23f) as DK03f.
  assert (OWN3 : own sp R M3).
  { apply (own_agree sp R M1 M3 ltac:(clear - SL96 SPT; lia) ltac:(clear - SHI SPT; lia) OWN1). intros a Ha. unfold ocell in Ha.
    rewrite FR3; [apply AGF; clear - Ha; lia| clear - Ha SL96 SHI SPT; lia| intros [X'|[X'|X']]; clear - X' Ha GFCEIL GFR SL96 SPT; unfold SB in *; lia]. }
  set (WR := PEC.W_crun AD EE fb) in *.
  assert (WRR : forall rr a, In rr WR -> L5.in_rng rr a ->
            (op + 8 <= a < op + 16) \/ (op + 280 <= a < op + 320) \/ (ois + 40 <= a < ois + 48) \/ (ois + 152 <= a < ois + 156) \/ (op + 336 <= a < op + 384)
            \/ (oec <= a < oec + 16) \/ (0x678780 <= a < 0x678782) \/ (0x69a1d0 <= a < 0x69a3f0) \/ (ov <= a < ov + 56) \/ (osk <= a < osk + 24)).
  { intros rr a Hin Hr. unfold WR, PEC.W_crun, PMSP.W_run, PMSP.W_srcf, PMSP.err_W, PMSP.o_src, PMSP.o_is, PMSP.o_tb, PMSP.o_vec, PMSP.o_ec, PMSP.o_p, PMSP.o_v, PESK.o_sink in Hin.
    cbn [app pa_off_p pa_off_is pa_off_ec pa_off_v pe_off_sink pa_errcat_guard pa_atexit AD EE PeCLayoutB.CADDR_B PeCLayoutB.EADDR_B] in Hin. unfold L5.in_rng in Hr.
    rewrite Eop, Eois, Eoec, Eov, Eosk.
    repeat (destruct Hin as [<-|Hin]; [cbn [fst snd] in Hr; clear - Hr; lia|]). destruct Hin. }
  assert (WAPPR : PMKB.wapp WR).
  { intros rr Hin. destruct rr as [ra' rn]. unfold BIGSHADOW_LO, BIGSHADOW_HI. cbn [fst snd].
    pose proof FSAPP as (FA0 & FA1 & FA2). unfold BIGSHADOW_LO, BIGSHADOW_HI in FA1.
    unfold WR, PEC.W_crun, PMSP.W_run, PMSP.W_srcf, PMSP.err_W, PMSP.o_src, PMSP.o_is, PMSP.o_tb, PMSP.o_vec, PMSP.o_ec, PMSP.o_p, PMSP.o_v, PESK.o_sink in Hin.
    cbn [app pa_off_p pa_off_is pa_off_ec pa_off_v pe_off_sink pa_errcat_guard pa_atexit AD EE PeCLayoutB.CADDR_B PeCLayoutB.EADDR_B] in Hin.
    repeat (destruct Hin as [Hin|Hin]; [injection Hin; intros <- <-; destruct FA1 as [FA1|FA1]; clear - FA0 FA1 FA2 F1 F2; lia|]). destruct Hin. }
  assert (BI3 : PMBUK.binv L ar HI M model LBX FF LK Aw sp 30720 (sp - 96) (own sp R) F 0 WR (PEC.owned s en k) M3 model3 LK2 cr Aw).
  { unfold PMBUK.binv. split; [exact HH3|]. split; [exact AM3|].
    split; [eapply L5LZ.model_rt_trans; [exact MRT1| eapply L5LZ.model_rt_trans; [exact MRT2| exact MRT3]]|].
    split; [apply incl_refl|]. split; [exact GLKI2|]. split; [exact (L5SAR.astk_grows ar M2 M3 sp 30720 ASTK2 MGM3)|].
    split; [apply (L5SAR.ek_W L ar LBX FF sp 30720 WR [] M M3 (PMKB.ek_sublb L ar LB LBX FF sp 30720 [] M M3 INCX EK03f)); intros a _ r0 []|].
    split; [exact (PMKB.dk_sublb L ar LB LBX FF sp 30720 M M3 INCX DK03f)|].
    split; [exact OWN3|].
    change (ff_bytes 0 / 8) with 8. apply (L5.defined_grows M2 M3 _ _ MGM3).
    apply (proj1 (L5A.defined_vis H2 M2 (F / 8 + SB) 8 VSH)). intros i Hi. pose proof (FSHZ i Hi) as Z0. unfold MV2 in Z0. rewrite Z0. discriminate. }

  assert (SZK : forall Mc lo g, L5SAR.ek L ar LBX FF sp 30720 WR M Mc -> sp - 30720 <= lo -> lo + 8 * g <= sp -> lo mod 8 = 0 -> 0 <= g -> shadow_zero Mc lo g).
  { intros Mc lo g EKc H1' H2' H3' H4'. apply (PMKB.stksh_keepA L ar LBX FF sp 30720 WR M Mc EKc WAPPR lo g); [clear - H1' SLO SPT; lia| clear - H1' SLO; lia| clear - H2' SHI SPT; lia| exact H3'| exact H4'|].
    apply (PMKB.shadow_zero_sub M (sp - 30720) 3840); [| exact H3'| exact H1'| clear - H2'; lia| exact H4'| exact STKSH].
    apply PMKB.mod16_8'. replace (sp - 30720) with (sp + (-1920) * 16) by (clear; lia). rewrite Z_mod_plus_full. exact A16. }
  assert (ASTK3 : L5CA.astk ar M3 sp 30720) by exact (L5SAR.astk_grows ar M2 M3 sp 30720 ASTK2 MGM3).
  pose proof (HAJ.aior_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH3) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & NDF3 & _).

  assert (CONT3 : PEC.content_ok RSEGS AD M3 fb p (PM.p_src s) str sm).
  { apply (content_keepA' LB FF sp 30720 [] M M3 fb p s str sm op EK03f PMKB.wapp_nil FRB BRB AOI); [intros i _ r0 []| exact SINC| exact Iq| intros q m _ i _ r0 []| exact IA| exact PA| exact CONT]. }
  assert (PA3 : PM.parser_at RSEGS AD PMSPA.accA PMSPA.annA M3 op ois s).
  { apply (PMKB.parser_keepA RSEGS AD L ar LB FF sp 30720 [] M M3 EK03f PMKB.wapp_nil FRB BRB _ _ _ AOP); [exact PINC| intros i _ r0 []| intros i _ r0 []| intros i _ r0 []| intros c0 n0 p0 _ i _ r0 []| exact PA]. }
  assert (IA3 : PM.iss_at RSEGS AD PMSPA.accA M3 ois str sm).
  { apply (PMKB.iss_keepA RSEGS AD L ar LB FF sp 30720 [] M M3 EK03f PMKB.wapp_nil FRB BRB ois str sm AOI); [exact SINC| intros i _ r0 []| intros c0 n0 p0 _ i _ r0 []| exact IA]. }
  assert (BASE3 : PMSTA.base_okA RSEGS AD M3).
  { change (PMSTA.base_okA RSEGS PMB.AD M3). apply (PMBSK.base_keep L ar C LY LB FF sp 30720 [] M M3 EK03f); [intros a _ r0 []| exact BASE]. }
  assert (ACC3 : PMSPA.accA M3 op PECA.RDR_BYTES) by exact (PMKB.acc_keepA' L ar LB FF sp 30720 [] M M3 EK03f PMKB.wapp_nil FRB op 392 (AOF op 392 ltac:(lia) ltac:(lia)) ACCR).
  unfold PECSB.src_read_spec, PECSPA.src_read_spec, PECSPA.csrc_spec in SR.
  apply (SR fx3 R3 M3 model3 K (PEC.enc_own en ++ PESK.sink_own k ++ LBX) FF' LK2 Aw cr (sp - 96) 0xb709c fb p s str sm [(F + 32, 1)] ltac:(rewrite PEC.owned_app; exact HH3) AM3 K0).
  { split; [rewrite L5K.rl1; exact Y1|]. split; [split; [clear; lia| reflexivity]|]. split; [rewrite L5K.rl2; rewrite (KS3 2%nat) by inl; exact B2R|].
    split; [rewrite L5K.rl3; rewrite (KS3 3%nat) by inl; rewrite (R2c 3%nat) by inl; rewrite (KS1 3%nat) by inl; rewrite <- L5K.rl3; exact Rgp|].
    split; [rewrite L5K.rl4; rewrite (KS3 4%nat) by inl; rewrite (R2c 4%nat) by inl; rewrite (KS1 4%nat) by inl; rewrite <- L5K.rl4; exact Rtp|].
    change (PMSPA.pm_scr 4) with 20480. change (20480 / 8) with 2560.
    split; [apply (L5SAR.astk_sub ar M3 M3 sp 30720 96 20480 ASTK3 (mem_grows_refl M3)); [clear; lia| clear; lia| clear; lia| replace (sp - 96) with (sp + (-6) * 16) by (clear; lia); rewrite Z_mod_plus_full; exact A16]|].
    apply SZK; [exact (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 BI3)))))))| clear; lia| clear; lia| | clear; lia].
    apply PMKB.mod16_8'. replace (sp - 96 - 20480) with (sp + (-1286) * 16) by (clear; lia). rewrite Z_mod_plus_full. exact A16. }
  { apply (PMBUAR.ffroomA_push 9 4 FF LK LK2 _ FRM GLKI2); [exact NDF3| clear; lia]. }
  { apply (PMBUAR.ffrsA_push FF sp (sp - 96) F 0 (sp - 96 + 32) FRS); clear; lia. }
  { exact FOK'. }
  { replace (sp - 96) with (sp + (-3) * 32) by (clear; lia). rewrite Z_mod_plus_full. exact SP32. }
  { unfold PMSPA.o_src. fold op. rewrite L5K.rl10. exact Y10. }
  { exists (F + 32), 1. split; [rewrite L5K.rl11; exact Y11|]. split; [rewrite L5K.rl12; exact Y12|]. split; [clear; lia|].
    split; [exists (F, 0, sp - 96 + 32); split; [left; reflexivity| cbn [ff_addr ff_class fst snd]; change (ff_bytes 0) with 64; clear; lia]|].
    split; [apply (L5.defined_sub M3 (F + 24) 40); [exact YD'| clear; lia| clear; lia]|].
    split; [|split; [fold ois; clear - AiF; change (ff_bytes 0) with 64 in AiF; lia | fold op; unfold PECA.RDR_BYTES; clear - ApF; change (ff_bytes 0) with 64 in ApF; lia]].
    intros a Ha. assert (Ea : a = F + 32) by (clear - Ha; lia). subst a. right. exists 1. split; [| split; [clear; lia|]].
    - unfold byte_at, S. replace ((F + 32) / 8 + SB) with (F / 8 + 2147450884) by (clear - GF8; unfold SB; lia).
      apply (L5ADHR.byte_of_u8 M3 _ 1 Y4'); [right| ]; clear - GFR; lia.
    - replace (F + 32) with (F + 4 * 8) by (clear; lia). rewrite Z_mod_plus_full. rewrite <- (proj1 GF8). rewrite Z_mod_mult. clear; lia. }
  { exists (F + 32), 1. split; [rewrite L5K.rl11; exact Y11|]. split; [rewrite L5K.rl12; exact Y12|]. split; [clear - Q0f GFR; lia|]. split; [clear; lia| reflexivity]. }
  { exact PA3. }
  { exact IA3. }
  { exact BASE3. }
  { exact ACC3. }
  { intros x Hx. apply in_or_app. right. apply in_or_app. right. exact (INCS x Hx). }
  { exact POK. }
  { exact CONT3. }
  intros fx4 R4 M4 model4 LK4 Aw4 src4 sm4 RP4 PA4 IA4 STEP4 RES4 HP4 MRT4 INCLK4 INCAw4 AM4 HH4.
  change (PMSPA.pm_scr 4) with 20480 in HP4. rewrite PEC.owned_app in HP4, HH4. fold LB in HP4, HH4.

  set (qc := PM.sr_qc (PM.p_src s)) in *.
  set (Wc := PMSPA.W_src AD fb (PM.p_src s) ++ [(F + 32, 1)]) in HP4.
  assert (WcR : forall rr a, In rr Wc -> L5.in_rng rr a ->
            (op + 280 <= a < op + 320) \/ (ois + 40 <= a < ois + 48) \/ (ois + 152 <= a < ois + 156) \/ (qc <= a < qc + 16384) \/ a = F + 32).
  { intros rr a Hin Hr. unfold Wc, PMSPA.W_src, PMSPA.W_srcf, PMSPA.o_src, PMSPA.o_is, PMSPA.o_p in Hin. cbn [app pa_off_p pa_off_is AD PeCLayoutB.CADDR_B] in Hin.
    unfold L5.in_rng in Hr. fold qc in Hin. destruct Hin as [<-|[<-|[<-|[<-|[<-|[]]]]]]; cbn [fst snd] in Hr; unfold PM.CHUNK in Hr; clear - Hr Eop Eois;
      [left|right;left|right;right;left|right;right;right;left|right;right;right;right]; lia. }
  assert (BI4 : PMBUK.binv L ar HI M model LBX FF LK Aw sp 30720 (sp - 96) (own sp R) F 0 WR (PEC.owned s en k) M4 model4 LK4 cr Aw4).
  { apply (PMBUK.binv_callee L ar C HI HIok M model LBX FF LK Aw sp 30720 (sp - 96) (sp - 88) sp (ocell sp) (own sp R) F fl 0 LK2 M2 model2 cr (PEC.owned s en k) G
             WR WR (PEC.owned s en k) (PEC.owned s en k) (PEC.owned s en k) M3 model3 LK2 cr Aw M4 model4 LK4 cr Aw4 20480 Wc BI3 HP4 HH4 AM4 MRT4 INCAw4 INCLK4);
      [clear; lia| clear; lia| | | intros a X'; exact X'].
    - intros rr a Hin Hr. change (ff_bytes 0 / 8) with 8. unfold ocell, SB.
      pose proof GFR as (GF1 & GF2 & _). assert (D1 : 0 <= F / 8) by (apply Z.div_pos; clear - GF1; lia).
      assert (D2 : F / 8 <= 17592186044408) by (apply Z.div_le_upper_bound; clear - GF2; lia).
      destruct (WcR rr a Hin Hr) as [X'|[X'|[X'|[X'|X']]]]; (split; [clear - X' O2 I2 Bq4 GFCEIL SL96 Eop Eois GF2; lia|]).
      + clear - X' OBIG D1 D2; lia.
      + clear - X' IBIG D1 D2; lia.
      + clear - X' IBIG D1 D2; lia.
      + destruct Bq5 as [Y|Y]; clear - X' Y D1 D2; lia.
      + subst a. destruct GFBIG as [Y|Y]; clear - Y D1 D2; lia.
    - intros a Hc Ho rr Hin Hr. destruct (WcR rr a Hin Hr) as [X'|[X'|[X'|[X'|X']]]].
      + apply (Ho (PMSP.o_src AD fb + 256, 40)); [unfold WR, PEC.W_crun, PMSP.W_run, PMSP.W_srcf; right; left; reflexivity| unfold L5.in_rng, PMSP.o_src; cbn [fst snd]; clear - X' Eop; unfold PMSP.o_p; cbn [pa_off_p AD PeCLayoutB.CADDR_B]; lia].
      + apply (Ho (PMSP.o_is AD fb + 40, 8)); [unfold WR, PEC.W_crun, PMSP.W_run, PMSP.W_srcf; right; right; left; reflexivity| unfold L5.in_rng, PMSP.o_is; cbn [fst snd pa_off_is AD PeCLayoutB.CADDR_B]; clear - X' Eois; lia].
      + apply (Ho (PMSP.o_is AD fb + 152, 4)); [unfold WR, PEC.W_crun, PMSP.W_run, PMSP.W_srcf; right; right; right; left; reflexivity| unfold L5.in_rng, PMSP.o_is; cbn [fst snd pa_off_is AD PeCLayoutB.CADDR_B]; clear - X' Eois; lia].
      + assert (Iq' : In (qc, 16384) (PEC.owned s en k)) by (unfold PEC.owned; apply in_or_app; left; unfold PM.parser_own, PM.src_own; left; reflexivity).
        exact (PMBRS1.own_not_aclient L ar C HI HIok (PEC.owned s en k) LBX FF LK cr Aw M _ qc 16384 a sp 30720 HH Iq' X' Hc).
      + subst a. apply (GNCF (F + 32)); [left; clear; lia| exact Hc]. }
  pose proof (L5SAR.ek_callee L ar LB [] FF [(F, 0, sp - 96 + 32)] sp 30720 (sp - 96) 20480 Wc Wc M3 M4 ltac:(rewrite app_nil_l; exact HP4) ltac:(clear; lia) ltac:(clear; lia) (fun a _ X' => X')) as EK34.
  pose proof (L5SAR.ek_trans L ar LB FF sp 30720 Wc M M3 M4 (L5SAR.ek_W L ar LB FF sp 30720 Wc [] M M3 EK03f (fun a _ r0 H0 => match H0 with end)) EK34) as EK04.
  assert (OUTc : forall a n, fb + 32 <= a -> a + n <= fb + 2040 -> (a + n <= op + 280 \/ op + 320 <= a) -> (a + n <= ois + 40 \/ ois + 48 <= a) ->
                 (a + n <= ois + 152 \/ ois + 156 <= a) -> forall i, a <= i < a + n -> L5.outside Wc i).
  { intros a n X1 X2 X3 X4 X5 i Hi rr Hin Hr. destruct (WcR rr i Hin Hr) as [Y|[Y|[Y|[Y|Y]]]]; [clear - Hi Y X3; lia| clear - Hi Y X4; lia| clear - Hi Y X5; lia| |].
    - destruct (PMBSK.blk_obj_apart L ar C HI HIok _ _ _ _ _ _ _ qc 16384 a n HH Iq (AOF a n X1 X2)) as [Z'|Z']; clear - Hi Y Z'; lia.
    - subst i. destruct (APART a n 0 0 (CLfb a n X1 X2 ltac:(clear - Hi; lia)) ltac:(clear - Hi; lia)) as (Z' & _). clear - Hi Z'; lia. }
  assert (WAPPc : PMKB.wapp Wc).
  { intros rr Hin. unfold Wc, PMSPA.W_src, PMSPA.W_srcf, PMSPA.o_src, PMSPA.o_is, PMSPA.o_p in Hin. cbn [app pa_off_p pa_off_is AD PeCLayoutB.CADDR_B] in Hin. fold qc in Hin.
    unfold BIGSHADOW_LO, BIGSHADOW_HI. destruct Hin as [<-|[<-|[<-|[<-|[<-|[]]]]]]; cbn [fst snd]; unfold PM.CHUNK.
    - clear - OBIG Eop; lia.
    - clear - IBIG Eois; lia.
    - clear - IBIG Eois; lia.
    - destruct Bq5 as [Y|Y]; clear - Y; lia.
    - destruct GFBIG as [Y|Y]; clear - Y; lia. }
  assert (OUTBc : forall q' m, In (q', m) LB -> q' <> qc -> forall i, q' <= i < q' + m -> L5.outside Wc i).
  { intros q' m Hq' NE i Hi rr Hin Hr. destruct (WcR rr i Hin Hr) as [Y|[Y|[Y|[Y|Y]]]].
    - destruct (PMBSK.blk_obj_apart L ar C HI HIok _ _ _ _ _ _ _ q' m op 384 HH Hq' AOP) as [Z'|Z']; clear - Hi Y Z'; lia.
    - destruct (PMBSK.blk_obj_apart L ar C HI HIok _ _ _ _ _ _ _ q' m ois 272 HH Hq' AOI) as [Z'|Z']; clear - Hi Y Z'; lia.
    - destruct (PMBSK.blk_obj_apart L ar C HI HIok _ _ _ _ _ _ _ q' m ois 272 HH Hq' AOI) as [Z'|Z']; clear - Hi Y Z'; lia.
    - pose proof (PMBSK.blk_apart L ar C HI HIok _ _ _ _ _ _ _ q' m qc 16384 HH Hq' Iq NE) as Z'. clear - Hi Y Z'; lia.
    - subst i. pose proof (WB _ Hq') as (_ & _ & _ & _ & _ & _ & FA). cbn [fst snd] in FA. unfold FS_BYTES in FA, GFS1, GFS2. clear - Hi FA GFS1 GFS2; lia. }

  assert (NDL : NoDup (map fst (PM.parser_own s ++ (PEC.enc_own en ++ PESK.sink_own k ++ LBX)))) by (rewrite <- EPO; exact ND).
  assert (NEQ : forall q' m, In (q', m) (PEC.enc_own en ++ PESK.sink_own k ++ LBX) -> q' <> qc).
  { intros q' m Hin. apply not_eq_sym. apply (PMPK.fst_neq_app (PM.parser_own s) (PEC.enc_own en ++ PESK.sink_own k ++ LBX) qc 16384 q' m NDL); [| exact Hin].
    unfold PM.parser_own, PM.src_own. left. reflexivity. }

  assert (EA4 : PECA.enc_atA RSEGS EE L ar M4 ov fb en).
  { apply (PECFA.enc_keepA RSEGS EE L ar LB FF sp 30720 Wc M M4 EK04 WAPPc FRB BRB ov fb en (AOF ov 56 ltac:(lia) ltac:(lia))); [| exact EINC| | exact EA].
    - apply OUTc; clear - Eop Eov Eois; lia.
    - intros Hp. assert (INe : In (PEC.en_b en, PEC.ESZ * PEC.ecap (PEC.en_k en)) (PEC.enc_own en)).
      { unfold PEC.enc_own. replace (PEC.en_k en =? 0) with false by (symmetry; apply Z.eqb_neq; lia). left. reflexivity. }
      refine (OUTBc _ _ (EINC _ INe) _). apply (NEQ _ (PEC.ESZ * PEC.ecap (PEC.en_k en))). apply in_or_app. left. exact INe. }
  assert (VREF4 : L5.u64_at RSEGS M4 (op + 384) ov).
  { apply (PMKB.u64_keepA RSEGS L ar LB FF sp 30720 Wc M M4 EK04 WAPPc FRB (op + 384) ov (AOF (op + 384) 8 ltac:(lia) ltac:(lia))); [| exact VREF].
    apply OUTc; clear - Eop Eois; lia. }
  assert (SKA4 : PESKA.sink_atA RSEGS L ar P M4 osk k).
  { apply (PECFA.sink_keepA RSEGS L ar LB FF sp 30720 Wc M M4 EK04 WAPPc FRB BRB P osk k (AOF osk 24 ltac:(lia) ltac:(lia))); [| exact KINC| | exact SKA].
    - apply OUTc; clear - Eop Eosk Eois; lia.
    - intros Hp. assert (INk : In (PESK.sk_b k, PESK.sk_c k) (PESK.sink_own k)).
      { unfold PESK.sink_own. replace (PESK.sk_c k =? 0) with false by (symmetry; apply Z.eqb_neq; lia). left. reflexivity. }
      refine (OUTBc _ _ (KINC _ INk) _). apply (NEQ _ (PESK.sk_c k)). apply in_or_app. right. apply in_or_app. left. exact INk. }
  assert (SDEP : forall W, (forall i, 0x678780 <= i < 0x69a4f4 -> L5.outside W i) ->
                 forall a, PMST.dep AD a -> hl_img_lo L <= a < hl_img_hi L /\ ~ hl_rt_static L a /\ L5.outside W a).
  { intros W OUT a D. change (PMST.dep PMB.AD a) in D. pose proof (PMBSK.dep_img a D) as DI. rewrite (L5A.aly_img_lo L C LYa), (L5A.aly_img_hi L C LYa).
    split; [clear - DI; lia|]. split; [exact (PMB.ly_static L C LY a (PnStatics.PNST.dep_of_j _ _ a D))|]. apply OUT; exact DI. }
  assert (OUTcI : forall i, 0x678780 <= i < 0x69a4f4 -> L5.outside Wc i).
  { intros i Hi rr Hin Hr. destruct (WcR rr i Hin Hr) as [Y|[Y|[Y|[Y|Y]]]]; [clear - Hi Y O1; lia| clear - Hi Y I1; lia| clear - Hi Y I1; lia| |].
    - destruct Bqi as [Z'|Z']; clear - Hi Y Z'; lia.
    - clear - Hi Y GFR; lia. }
  assert (ERR4 : PESTA.err_okA RSEGS AD AAD EE M4 e).
  { apply (PECFA.err_okA_keep RSEGS AD AAD EE L ar LB FF sp 30720 Wc M M4 EK04 e PECSB.addrs_wf_B); [| exact ERR]. exact (SDEP Wc OUTcI). }
  assert (BASE4 : PMSTA.base_okA RSEGS AD M4).
  { change (PMSTA.base_okA RSEGS PMB.AD M4). apply (PMBSK.base_keep L ar C LY LB FF sp 30720 Wc M M4 EK04); [| exact BASE].
    intros a Ha rr Hin Hr. destruct (WcR rr a Hin Hr) as [Y|[Y|[Y|[Y|Y]]]]; [clear - Ha Y O1; lia| clear - Ha Y I1; lia| clear - Ha Y I1; lia| destruct Bqi as [Z'|Z']; clear - Ha Y Z'; lia| clear - Ha Y GFR; lia]. }
  assert (ECS4 : PECA.ec_stateA RSEGS AD M4 fb (s_ec X) cat).
  { apply (PECFA.ec_state_keepA RSEGS AD L ar LB FF sp 30720 Wc M M4 EK04 WAPPc FRB fb (s_ec X) cat (AOF oec 16 ltac:(lia) ltac:(lia))); [| exact ECS].
    fold oec. apply OUTc; clear - Eop Eoec Eois; lia. }
  assert (ACC4 : PMSPA.accA M4 op PECA.RDR_BYTES).
  { pose proof PA4 as (_ & _ & C24 & _). pose proof BI4 as (_ & _ & _ & _ & _ & _ & EKb4 & _).
    exact (PMKB.acc_keepA' L ar LBX FF sp 30720 WR M M4 EKb4 WAPPR FRB op 392 (AOF op 392 ltac:(lia) ltac:(lia)) ACCR). }

  destruct RES4 as (CW4 & p' & k' & d & Yp & Yk & Hp1 & Hp2 & Hk' & Yd & Hd & CONS & SHORT & DEFd & BYT).
  assert (Ek : k' = 1).
  { rewrite L5K.rl12 in Yk. rewrite Y12 in Yk. apply (f_equal bv_unsigned) in Yk. unfold PM.CHUNK in Hk'. rewrite !L5.unsigned_lit in Yk by (clear - Hk'; lia). clear - Yk; lia. }
  subst k'.
  assert (Ep : p' = F + 32).
  { rewrite L5K.rl11 in Yp. rewrite Y11 in Yp. apply (f_equal bv_unsigned) in Yp. rewrite !L5.unsigned_lit in Yp by (clear - Hp1 Hp2 Q0f GFR; lia). clear - Yp; lia. }
  subst p'. rewrite L5K.rl10 in Yd.
  assert (R4c : forall j, In j [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%nat -> getr R4 (reg j) = getr R3 (reg j))
    by (intros j Hj; exact (L5SAR.cs_of_preserved R3 R4 j RP4 Hj)).
  assert (G2' : getr R4 (reg 2) = Z_to_bv 64 (sp - 96)) by (rewrite (R4c 2%nat) by inl; rewrite (KS3 2%nat) by inl; exact B2R).
  assert (G8' : getr R4 (reg 8) = Z_to_bv 64 sp) by (rewrite (R4c 8%nat) by inl; rewrite (KS3 8%nat) by inl; exact B8R).
  assert (G9' : getr R4 (reg 9) = Z_to_bv 64 (sp - 96)) by (rewrite (R4c 9%nat) by inl; rewrite (KS3 9%nat) by inl; exact B9R).
  assert (G18' : getr R4 (reg 18) = Z_to_bv 64 F) by (rewrite (R4c 18%nat) by inl; exact Y18).
  assert (G19' : getr R4 (reg 19) = Z_to_bv 64 oec) by (rewrite (R4c 19%nat) by inl; rewrite (KS3 19%nat) by inl; exact B19R).
  assert (G20' : getr R4 (reg 20) = Z_to_bv 64 op) by (rewrite (R4c 20%nat) by inl; rewrite (KS3 20%nat) by inl; exact B20R).
  assert (G21' : getr R4 (reg 21) = Z_to_bv 64 ov) by (rewrite (R4c 21%nat) by inl; rewrite (KS3 21%nat) by inl; exact B21R).
  assert (G22' : getr R4 (reg 22) = Z_to_bv 64 (F + 32)) by (rewrite (R4c 22%nat) by inl; exact Y22).
  assert (G23' : getr R4 (reg 23) = Z_to_bv 64 F) by (rewrite (R4c 23%nat) by inl; exact Y23).
  assert (G24' : getr R4 (reg 24) = Z_to_bv 64 ((F / 8) + 2147450880)) by (rewrite (R4c 24%nat) by inl; exact Y24).
  assert (G25' : getr R4 (reg 25) = Z_to_bv 64 2147450880) by (rewrite (R4c 25%nat) by inl; rewrite (KS3 25%nat) by inl; exact B25R).
  assert (G34' : forall j, In j [3; 4; 26; 27]%nat -> getr R4 (reg j) = getr R (reg j)).
  { intros j Hj. rewrite (R4c j) by (revert j Hj; apply (L5K.incl_b [3; 4; 26; 27]%nat); vm_compute; reflexivity).
    rewrite (KS3 j) by (revert j Hj; apply (L5K.incl_b [3; 4; 26; 27]%nat); vm_compute; reflexivity).
    rewrite (R2c j) by (revert j Hj; apply (L5K.incl_b [3; 4; 26; 27]%nat); vm_compute; reflexivity).
    apply KS1. revert j Hj. apply (L5K.incl_b [3; 4; 26; 27]%nat). vm_compute. reflexivity. }
  assert (QC4 : PM.sr_qc src4 = qc) by (destruct STEP4 as (X' & _); exact X').
  set (s4 := PMSPA.with_src s src4) in *.
  assert (EOWN : PM.parser_own s4 = PM.parser_own s) by (unfold s4, PMSPA.with_src, PM.parser_own, PM.src_own; cbn [PM.p_src PM.p_b PM.p_k PM.p_tb]; rewrite QC4; reflexivity).
  assert (EOWN4 : PEC.owned s4 en k = PEC.owned s en k) by (unfold PEC.owned; rewrite EOWN; reflexivity).

  assert (CONT4 : PEC.content_ok RSEGS AD M4 fb p src4 str sm4).
  { destruct CW4 as (CWP & CWB & CW5). pose proof IA3 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & VS3 & _). pose proof VS3 as (_ & _ & VSF3).
    apply (PECF.content_ok_step RSEGS AD M3 M4 fb p (PM.p_src s) str sm src4 sm4); [clear - I1 Eois; unfold PMSP.o_is; cbn [pa_off_is AD PeCLayoutB.CADDR_B]; lia| clear - I3 Eois; unfold PMSP.o_is; cbn [pa_off_is AD PeCLayoutB.CADDR_B]; lia| | | | clear - CWP; lia| exact CWB| exact CW5| exact CONT3].
    - unfold PMSP.o_is. cbn [pa_off_is AD PeCLayoutB.CADDR_B]. change (fb + 96) with ois.
      exact (proj1 (PMKB.agA_obj L ar LB FF sp 30720 Wc M3 M4 EK34 WAPPc FRB (ois + 80) 24 (AOF (ois + 80) 24 ltac:(lia) ltac:(lia)) (OUTc (ois + 80) 24 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)))).
    - intros c0 n0 q0 Es. cbn in VSF3. rewrite Es in VSF3. cbn in VSF3. destruct VSF3 as (_ & _ & _ & Hn0 & Hc0 & _).
      assert (IN0 : In (q0, c0) LB) by (apply SINC; unfold PM.vs_own; rewrite Es; left; reflexivity).
      destruct (BRB _ IN0) as (B0' & B1'). cbn [fst snd] in B0', B1'.
      split; [exact B0'|]. split; [clear - B1'; lia|]. split; [clear - Hn0; lia|].
      refine (proj1 (PMKB.agA_blk L ar LB FF sp 30720 Wc M3 M4 EK34 WAPPc BRB q0 c0 IN0 _)).
      refine (OUTBc q0 c0 IN0 _). apply (NEQ q0 c0). apply in_or_app. right. apply in_or_app. right. apply INCS. unfold PM.vs_own. rewrite Es. left. reflexivity.
    - intros n0 Es. cbn in VSF3. rewrite Es in VSF3. cbn in VSF3. clear - VSF3. lia. }

  assert (UNR : PM.unread (PM.p_src s) sm = blen p - s_pos X) by (unfold PEC.pos_of in POS; clear - POS; lia).
  unfold PMSPA.consumed in CONS.
  assert (ECD4 : L5.defined M4 oec 16 /\ PMSPA.accA M4 oec 16).
  { unfold PECA.ec_stateA in ECS4. fold oec in ECS4.
    destruct (s_ec X); [destruct ECS4 as (v0 & _ & (_ & _ & D' & A')); exact (conj D' A')| destruct ECS4 as (_ & _ & D' & A'); exact (conj D' A')]. }
  destruct (Z.eq_dec d 0) as [D0|D1'].
  -
    rewrite D0 in Yd, CONS, SHORT, DEFd, BYT. clear Hd. assert (SH0 : PM.unread src4 sm4 = 0) by (apply SHORT; clear; lia).
    assert (HEOF : blen p <= s_pos X) by (clear - UNR CONS SH0; lia).
    set (H4 := ahid Aw4 model4) in *. set (MV4 := mrestrict H4 M4) in *.
    pose proof (PEBRTVP.artE0_conc fx4 R4 MV4 (fun j => match j with 2%nat => sp | 36%nat => op | 37%nat => ov | 38%nat => oec | 47%nat => F | _ => 0 end)) as PP.
    cbn beta iota in PP. rewrite Yd in PP. L5SAR.feed PP ltac:(first [assumption | reflexivity]).
    destruct PP as (fx5 & R5 & M5v & MG5 & _ & FRZ5 & MS5 & KS5 & Z1 & Z10 & Z11).
    assert (E5 : M5v = MV4) by (apply L5SAR.mem_eq_of_agree; intros a Ha; apply FRZ5; exact Ha). subst M5v.
    apply (L5SAR.apiece_ro L ar C HI LYa HIok LB FF' LK4 cr Aw4 M4 model4 fx4 fx5 R4 0xb709c R5 0xafda8 MV4 K HH4 AM4 MS5 (fun x Hx => Hx) (fun a Ha => eq_refl)).
    intros M5 model5 HH5 AM5 MRT5 HID5 VIS5 MGM5 FR5.
    assert (E5 : M5 = M4) by (apply L5SAR.mem_eq_of_agree; exact FR5). subst M5.
    pose proof (PMBUK.binv_model L ar HI M model LBX FF LK Aw sp 30720 (sp - 96) (own sp R) F 0 WR (PEC.owned s en k) M4 model4 LK4 cr Aw4 model5 BI4 HH5 AM5 MRT5) as BI5.
    assert (R5c : forall j, In j [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%nat -> getr R5 (reg j) = getr R4 (reg j)).
    { intros j Hj. apply KS5. revert j Hj. apply (L5K.incl_b [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%nat). vm_compute. reflexivity. }

    unfold PECSB.make_ec_spec, PECSPA.make_ec_spec in MKE.
    apply (MKE fx5 R5 M4 model5 K LB FF' LK4 Aw4 cr oec 1 (sp - 96) 0xb70ec e HH5 AM5 K0).
    { split; [rewrite L5K.rl1; exact Z1|]. split; [split; [clear; lia| reflexivity]|]. split; [rewrite L5K.rl2; rewrite (R5c 2%nat) by inl; exact G2'|].
      split; [rewrite L5K.rl3; rewrite (R5c 3%nat) by inl; rewrite (G34' 3%nat) by inl; rewrite <- L5K.rl3; exact Rgp|].
      split; [rewrite L5K.rl4; rewrite (R5c 4%nat) by inl; rewrite (G34' 4%nat) by inl; rewrite <- L5K.rl4; exact Rtp|].
      change (PMSPA.pm_scr 1) with 14336. change (14336 / 8) with 1792.
      pose proof BI4 as (_ & _ & _ & _ & _ & ASTK4 & EKb4 & _).
      split; [apply (L5SAR.astk_sub ar M4 M4 sp 30720 96 14336 ASTK4 (mem_grows_refl M4)); [clear; lia| clear; lia| clear; lia| replace (sp - 96) with (sp + (-6) * 16) by (clear; lia); rewrite Z_mod_plus_full; exact A16]|].
      apply SZK; [exact EKb4| clear; lia| clear; lia| | clear; lia].
      apply PMKB.mod16_8'. replace (sp - 96 - 14336) with (sp + (-902) * 16) by (clear; lia). rewrite Z_mod_plus_full. exact A16. }
    { pose proof (HAJ.aior_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH5) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & NDF5 & _).
      apply (PMBUAR.ffroomA_push 9 1 FF LK LK4 _ FRM (fun x Hx => GLKI2 x (INCLK4 x Hx))); [exact NDF5| clear; lia]. }
    { apply (PMBUAR.ffrsA_push FF sp (sp - 96) F 0 (sp - 96 + 32) FRS); clear; lia. }
    { rewrite L5K.rl10. exact Z10. }
    { rewrite L5K.rl11. exact Z11. }
    { clear; lia. }
    { apply AOF'; clear - Eoec; lia. }
    { exact C8m. }
    { exact (proj1 ECD4). }
    { exact (proj2 ECD4). }
    { exact BASE4. }
    { exact ERR4. }
    intros fx6 R6 M6 model6 LK6 Aw6 RP6 EC6 ERR6 HP6 MRT6 INCLK6 INCAw6 AM6 HH6.
    change (PMSPA.pm_scr 1) with 14336 in HP6.
    set (Wc6 := (oec, 16) :: (if e then [] else PMSPA.err_W AD)) in HP6.
    assert (Wc6R : forall rr a, In rr Wc6 -> L5.in_rng rr a -> (oec <= a < oec + 16) \/ (0x678780 <= a < 0x69a4f4)).
    { intros rr a Hin Hr. unfold Wc6 in Hin. destruct Hin as [<-|Hin]; [left; exact Hr|]. right. destruct e; [destruct Hin|].
      unfold PMSPA.err_W in Hin. cbn [pa_errcat_guard pa_atexit AD PeCLayoutB.CADDR_B] in Hin. unfold L5.in_rng in Hr.
      destruct Hin as [<-|[<-|[]]]; cbn [fst snd] in Hr; clear - Hr; lia. }
    assert (BI6 : PMBUK.binv L ar HI M model LBX FF LK Aw sp 30720 (sp - 96) (own sp R) F 0 WR (PEC.owned s en k) M6 model6 LK6 cr Aw6).
    { apply (PMBUK.binv_callee L ar C HI HIok M model LBX FF LK Aw sp 30720 (sp - 96) (sp - 88) sp (ocell sp) (own sp R) F fl 0 LK2 M2 model2 cr (PEC.owned s en k) G
               WR WR (PEC.owned s en k) (PEC.owned s en k) (PEC.owned s en k) M4 model5 LK4 cr Aw4 M6 model6 LK6 cr Aw6 14336 Wc6 BI5 HP6 HH6 AM6 MRT6 INCAw6 INCLK6);
        [clear; lia| clear; lia| | | intros a X'; exact X'].
      - intros rr a Hin Hr. change (ff_bytes 0 / 8) with 8. unfold ocell, SB.
        pose proof GFR as (GF1 & GF2 & _). assert (DF1 : 0 <= F / 8) by (apply Z.div_pos; clear - GF1; lia).
        assert (DF2 : F / 8 <= 17592186044408) by (apply Z.div_le_upper_bound; clear - GF2; lia).
        pose proof FSAPP as (FA0 & FA1 & FA2).
        destruct (Wc6R rr a Hin Hr) as [X'|X']; (split; [clear - X' SL96 SPT Eop Eoec F2 FSCEIL; lia|]).
        + destruct FA1 as [Y|Y]; clear - X' Y DF1 DF2 F1 F2 Eoec; lia.
        + clear - X' DF1; lia.
      - intros a Hc Ho rr Hin Hr. destruct (Wc6R rr a Hin Hr) as [X'|X'].
        + apply (Ho (PMSP.o_ec AD fb, 16)); [unfold WR; wr_mem 6| wr_rng; clear - X' Eoec; lia].
        + unfold Wc6 in Hin. destruct Hin as [<-|Hin]; [unfold L5.in_rng in Hr; cbn [fst snd] in Hr; clear - Hr X' Eoec O1 Eop; lia|].
          destruct e; [destruct Hin|]. unfold PMSPA.err_W in Hin. cbn [pa_errcat_guard pa_atexit AD PeCLayoutB.CADDR_B] in Hin.
          destruct Hin as [<-|[<-|[]]].
          * apply (Ho (pa_errcat_guard AD, 2)); [unfold WR; wr_mem 7| exact Hr].
          * apply (Ho (pa_atexit AD, 544)); [unfold WR; wr_mem 8| exact Hr]. }
    pose proof (L5SAR.ek_callee L ar LB [] FF [(F, 0, sp - 96 + 32)] sp 30720 (sp - 96) 14336 Wc6 Wc6 M4 M6 ltac:(rewrite app_nil_l; exact HP6) ltac:(clear; lia) ltac:(clear; lia) (fun a _ X' => X')) as EK46.
    assert (WAPP6 : PMKB.wapp Wc6).
    { intros rr Hin. unfold Wc6 in Hin. unfold BIGSHADOW_LO, BIGSHADOW_HI. destruct Hin as [<-|Hin]; cbn [fst snd].
      - pose proof FSAPP as (FA0 & FA1 & FA2). destruct FA1 as [Y|Y]; clear - Y F1 F2 Eoec; lia.
      - destruct e; [destruct Hin|]. unfold PMSPA.err_W in Hin. cbn [pa_errcat_guard pa_atexit AD PeCLayoutB.CADDR_B] in Hin. destruct Hin as [<-|[<-|[]]]; cbn [fst snd]; clear; lia. }
    assert (OUT6 : forall a n, fb + 32 <= a -> a + n <= fb + 2040 -> (a + n <= oec \/ oec + 16 <= a) -> forall i, a <= i < a + n -> L5.outside Wc6 i).
    { intros a n X1 X2 X3 i Hi rr Hin Hr. destruct (Wc6R rr i Hin Hr) as [Y|Y]; [clear - Hi Y X3; lia| clear - Hi Y X1 Eop O1; lia]. }
    assert (OUTB6 : forall q' m, In (q', m) LB -> forall i, q' <= i < q' + m -> L5.outside Wc6 i).
    { intros q' m Hq i Hi rr Hin Hr. destruct (Wc6R rr i Hin Hr) as [Y|Y].
      - destruct (PMBSK.blk_obj_apart L ar C HI HIok _ _ _ _ _ _ _ q' m oec 16 HH Hq (AOF oec 16 ltac:(clear - Eoec; lia) ltac:(clear - Eoec; lia))) as [Z'|Z']; clear - Hi Y Z'; lia.
      - pose proof (PMBSK.blk_img L ar C HI LY HIok _ _ _ _ _ _ _ q' m HH Hq) as Z'. destruct Z' as [Z'|Z']; clear - Hi Y Z'; lia. }
    assert (OUT6I : forall i, 65536 <= i < 0x678780 -> L5.outside Wc6 i).
    { intros i Hi rr Hin Hr. destruct (Wc6R rr i Hin Hr) as [Y|Y]; [clear - Hi Y Eoec Eop O1; lia| clear - Hi Y; lia]. }
    assert (PA6 : PM.parser_at RSEGS AD PMSPA.accA PMSPA.annA M6 op ois s4).
    { apply (PMKB.parser_keepA RSEGS AD L ar LB FF sp 30720 Wc6 M4 M6 EK46 WAPP6 FRB BRB _ _ _ AOP); [| | | | | exact PA4].
      - rewrite EOWN. exact PINC.
      - apply OUT6; clear - Eop Eoec; lia.
      - unfold s4, PMSPA.with_src, PMKB.blk_out. cbn [PM.p_src]. rewrite QC4. apply (OUTB6 qc 16384). exact Iq.
      - unfold s4, PMSPA.with_src, PMKB.blk_out. cbn [PM.p_b PM.p_k]. apply (OUTB6 (PM.p_b s) (32 * 2 ^ PM.p_k s)). exact Ib.
      - unfold s4, PMSPA.with_src, PMKB.blk_out. cbn [PM.p_tb]. intros c0 n0 p0 E0. apply (OUTB6 p0 c0). apply PINC. unfold PM.parser_own, PM.vs_own. rewrite E0. right; right; left; reflexivity. }
    assert (IA6 : PM.iss_at RSEGS AD PMSPA.accA M6 ois str sm4).
    { apply (PMKB.iss_keepA RSEGS AD L ar LB FF sp 30720 Wc6 M4 M6 EK46 WAPP6 FRB BRB ois str sm4 AOI); [exact SINC| | | exact IA4].
      - apply OUT6; clear - Eois Eoec; lia.
      - intros c0 n0 p0 E0. unfold PMKB.blk_out. apply (OUTB6 p0 c0). apply SINC. unfold PM.vs_own. rewrite E0. left; reflexivity. }
    assert (EA6 : PECA.enc_atA RSEGS EE L ar M6 ov fb en).
    { apply (PECFA.enc_keepA RSEGS EE L ar LB FF sp 30720 Wc6 M4 M6 EK46 WAPP6 FRB BRB ov fb en (AOF ov 56 ltac:(lia) ltac:(lia))); [| exact EINC| | exact EA4].
      - apply OUT6; clear - Eov Eoec; lia.
      - intros Hp. refine (OUTB6 _ _ _). apply EINC. unfold PEC.enc_own. replace (PEC.en_k en =? 0) with false by (symmetry; apply Z.eqb_neq; lia). left. reflexivity. }
    assert (VREF6 : L5.u64_at RSEGS M6 (op + 384) ov).
    { apply (PMKB.u64_keepA RSEGS L ar LB FF sp 30720 Wc6 M4 M6 EK46 WAPP6 FRB (op + 384) ov (AOF (op + 384) 8 ltac:(lia) ltac:(lia))); [| exact VREF4]. apply OUT6; clear - Eop Eoec; lia. }
    assert (SKA6 : PESKA.sink_atA RSEGS L ar P M6 osk k).
    { apply (PECFA.sink_keepA RSEGS L ar LB FF sp 30720 Wc6 M4 M6 EK46 WAPP6 FRB BRB P osk k (AOF osk 24 ltac:(lia) ltac:(lia))); [| exact KINC| | exact SKA4].
      - apply OUT6; clear - Eosk Eoec; lia.
      - intros Hp. refine (OUTB6 _ _ _). apply KINC. unfold PESK.sink_own. replace (PESK.sk_c k =? 0) with false by (symmetry; apply Z.eqb_neq; lia). left. reflexivity. }
    assert (BASE6 : PMSTA.base_okA RSEGS AD M6).
    { apply (PMBPAR.base_keepW L ar C LY LB FF sp 30720 Wc6 M4 M6 EK46); [| | | | exact BASE4].
      - intros a Ha. apply OUT6I. clear - Ha; lia.
      - intros a Ha rr Hin Hr. unfold Wc6 in Hin. destruct Hin as [<-|Hin]; [unfold L5.in_rng in Hr; cbn [fst snd] in Hr; clear - Hr Ha Eoec Eop O1; lia|]. destruct e; [destruct Hin|].
        unfold PMSPA.err_W in Hin. cbn [pa_errcat_guard pa_atexit AD PeCLayoutB.CADDR_B] in Hin. unfold L5.in_rng in Hr.
        destruct Hin as [<-|[<-|[]]]; cbn [fst snd] in Hr; clear - Hr Ha; lia.
      - intros rr Hin Hr. unfold Wc6 in Hin. destruct Hin as [<-|Hin]; [unfold L5.in_rng in Hr; cbn [fst snd] in Hr; clear - Hr Eoec Eop O1; lia|]. destruct e; [destruct Hin|].
        unfold PMSPA.err_W in Hin. cbn [pa_errcat_guard pa_atexit AD PeCLayoutB.CADDR_B] in Hin. unfold L5.in_rng in Hr.
        destruct Hin as [<-|[<-|[]]]; cbn [fst snd] in Hr; clear - Hr; lia.
      - intros a Ha rr Hin Hr. unfold Wc6 in Hin. destruct Hin as [<-|Hin]; [unfold L5.in_rng in Hr; cbn [fst snd] in Hr; clear - Hr Ha Eoec Eop O1; lia|]. destruct e; [destruct Hin|].
        unfold PMSPA.err_W in Hin. cbn [pa_errcat_guard pa_atexit AD PeCLayoutB.CADDR_B] in Hin. unfold L5.in_rng in Hr.
        destruct Hin as [<-|[<-|[]]]; cbn [fst snd] in Hr; clear - Hr Ha; lia. }
    assert (CONT6 : PEC.content_ok RSEGS AD M6 fb p src4 str sm4).
    { change src4 with (PM.p_src s4).
      apply (content_keepA' LB FF sp 30720 Wc6 M4 M6 fb p s4 str sm4 op EK46 WAPP6 FRB BRB AOI); [| exact SINC| | intros q' m Hq'; exact (OUTB6 q' m Hq')| exact IA4| exact PA4| exact CONT4].
      - fold ois. apply OUT6; clear - Eois Eoec; lia.
      - unfold s4, PMSPA.with_src. cbn [PM.p_src]. rewrite QC4. exact Iq. }
    assert (ACC6 : PMSPA.accA M6 op PECA.RDR_BYTES).
    { pose proof BI6 as (_ & _ & _ & _ & _ & _ & EKb6 & _). exact (PMKB.acc_keepA' L ar LBX FF sp 30720 WR M M6 EKb6 WAPPR FRB op 392 (AOF op 392 ltac:(lia) ltac:(lia)) ACCR). }

    set (H6 := ahid Aw6 model6) in *. set (MV6 := mrestrict H6 M6) in *.
    destruct (PMBUK.vis_facts L ar C HI LYa HIok M model LBX FF LK Aw sp 30720 (sp - 96) (sp - 88) sp (ocell sp) (own sp R) F fl 0 LK2 M2 model2 cr (PEC.owned s en k) G
                WR (PEC.owned s en k) M6 model6 LK6 cr Aw6 BI6) as ((WS6 & IC6 & CSB6 & CUAR6 & _) & OWN6 & (FD6 & FW6 & FSW6 & FLC6 & FLW6) & (FLCc6 & FLV6 & VF6 & VS6 & VSH6)).
    change (ff_bytes 0) with 64 in *. change (64 / 8) with 8 in *. replace (sp - (sp - 96)) with 96 in WS6 by (clear; lia).
    replace (F + 64 - 8) with (F + 56) in FLC6 by (clear; lia).
    fold H6 in WS6, IC6, CSB6, CUAR6, OWN6, FD6, FW6, FSW6, FLC6, FLW6, FLV6, VF6, VS6, VSH6. fold MV6 in WS6, IC6, CSB6, CUAR6, OWN6, FD6, FW6, FSW6, FLC6, FLW6.
    pose proof (PMBPAR.op_vis L ar C HI LY HIok _ _ LK6 cr Aw6 M6 model6 fb _ s4 HH6 FOK' PA6) as ((_ & _ & _) & Zop6 & Z326 & Z206 & OWR6 & _ & OVIS6 & _ & _).
    fold H6 in Zop6, Z326, Z206, OWR6, OVIS6. fold MV6 in Zop6, Z326, Z206, OWR6.
    assert (R6c : forall j, In j [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%nat -> getr R6 (reg j) = getr R4 (reg j)).
    { intros j Hj. rewrite (L5SAR.cs_of_preserved R5 R6 j RP6 Hj). exact (R5c j Hj). }
    pose proof OWN6 as (S8 & S16 & S24 & S32 & S40 & S48 & S56 & S64 & S72 & S80 & S88).
    pose proof (bv_unsigned_in_range 64 (getr R (reg 1))) as B1. pose proof (bv_unsigned_in_range 64 (getr R (reg 8))) as B8.
    pose proof (bv_unsigned_in_range 64 (getr R (reg 9))) as B9. pose proof (bv_unsigned_in_range 64 (getr R (reg 18))) as B18.
    pose proof (bv_unsigned_in_range 64 (getr R (reg 19))) as B19. pose proof (bv_unsigned_in_range 64 (getr R (reg 20))) as B20.
    pose proof (bv_unsigned_in_range 64 (getr R (reg 21))) as B21. pose proof (bv_unsigned_in_range 64 (getr R (reg 22))) as B22.
    pose proof (bv_unsigned_in_range 64 (getr R (reg 23))) as B23. pose proof (bv_unsigned_in_range 64 (getr R (reg 24))) as B24.
    pose proof (bv_unsigned_in_range 64 (getr R (reg 25))) as B25. change (bv_modulus 64) with (2 ^ 64) in *.
    pose proof (PEBRTVP.artZ_conc fx6 R6 MV6 (fun j => match j with 2%nat => sp | 36%nat => op | 37%nat => ov | 38%nat => oec | 47%nat => F | 48%nat => fl
             | 64%nat => bv_unsigned (getr R (reg 1)) | 65%nat => bv_unsigned (getr R (reg 8)) | 66%nat => bv_unsigned (getr R (reg 9))
             | 67%nat => bv_unsigned (getr R (reg 18)) | 68%nat => bv_unsigned (getr R (reg 19)) | 69%nat => bv_unsigned (getr R (reg 20))
             | 70%nat => bv_unsigned (getr R (reg 21)) | 71%nat => bv_unsigned (getr R (reg 22)) | 72%nat => bv_unsigned (getr R (reg 23))
             | 73%nat => bv_unsigned (getr R (reg 24)) | 74%nat => bv_unsigned (getr R (reg 25)) | _ => 0 end)) as PP.
    cbn beta iota in PP.
    L5SAR.feed PP ltac:(first [assumption | (rewrite R6c by inl; assumption) | unfold PEBRTVP.aligned; assumption]).
    destruct PP as (fx7 & R7 & M7v & MG7 & _ & FRZ7 & MS7 & KS7 & E1 & E2 & E8 & E9 & _ & _ & E18 & E19 & E20 & E21 & E22 & E23 & E24 & E25 & FL0
                   & _ & _ & _ & _ & _ & _ & _ & _ & _ & MO0 & _).
    assert (R7ra : getr R7 (reg 1) = Z_to_bv 64 r) by (rewrite E1, Z_to_bv_bv_unsigned; exact Rra).
    pose proof (PMK.ret_to RSEGS fx7 R7 M7v 0xb71a0 W_b7150 r F_b7150 eq_refl D_b7150 R7ra Hr1 Hr2) as MSr.
    apply (PMBUK.retire_coreW L ar C HI LYa HIok M model LBX FF LK Aw sp 30720 (sp - 96) (sp - 88) sp (ocell sp) (own sp R) F fl 0 LK2 M2 model2 cr (PEC.owned s en k) G
             WR (PEC.owned s en k) M6 model6 LK6 cr Aw6 (fun a => op + 8 <= a < op + 9) fx6 fx7 R6 0xb70ec R7 r M7v K BI6).
    { intros a X'. split.
      - apply (L5SAR.fframe_client L ar (PEC.owned s en k ++ LBX) FF' 0 0 fb 5 rs); [right; exact Hfb| change (ff_bytes 5) with 2048; clear - X' Eop; lia].
      - intros O. apply (O (PMSP.o_p AD fb + 8, 8)); [unfold WR; wr_mem 0| wr_rng; clear - X' Eop; lia]. }
    { intros a. destruct (L5SAR.rng_dec a (op + 8) (op + 9)) as [X'|X']; [left; exact X'| right; exact X']. }
    { exact (msteps_trans _ _ _ _ MS7 MSr). }
    { exact MG7. }
    { intros a Ha Nw. unfold PMBUK.WretX, PMBUK.Wret in Nw. change (ff_bytes 0) with 64 in Nw.
      apply FRZ7; [exact Ha| intros X'; apply Nw; right; clear - X'; lia| intros X'; apply Nw; left; left; left; clear - X'; lia
                  | intros X'; apply Nw; left; left; right; unfold SB; clear - X'; lia| intros X'; apply Nw; left; right; clear - X'; lia]. }
    { exact FL0. }
    intros Mf modelf FZf MGf VISf AHf MRTf AMf HHf. change (mrestrict H6 Mf = M7v) in VISf.
    assert (EKf : L5SAR.ek L ar LB FF 0 0 [(op + 8, 1)] M6 Mf).
    { apply (PMBUAR.wret_ek L ar C HI LY HIok LBX FF LK Aw sp 30720 (sp - 96) (sp - 88) sp (ocell sp) (own sp R) F fl 0 LK2 M2 model2 cr (PEC.owned s en k)
               LB LK6 cr Aw6 M6 Mf _ [(op + 8, 1)] (fun a => op + 8 <= a < op + 9) G HH6).
      - intros a X' O. apply (O (op + 8, 1)); [left; reflexivity| unfold L5.in_rng; cbn [fst snd]; clear - X'; lia].
      - exact FZf. }
    pose proof (PMBSK.brb_of L ar C HI HIok _ _ _ _ _ _ _ HH6) as BRB6.
    assert (MO0f : L5.u8_at RSEGS Mf (op + 8) 0).
    { apply (proj1 (L5A.u8_at_vis H6 Mf (op + 8) 0 (OVIS6 (op + 8) 1 ltac:(clear; lia) ltac:(clear; lia)) ltac:(clear - O1; lia) ltac:(clear - O1 O3; lia))). rewrite VISf. exact MO0. }
    pose proof BI6 as (_ & _ & _ & INCA6 & INCL6 & _ & EKb6 & _).
    assert (WAPP8 : PMKB.wapp [(op + 8, 1)]).
    { apply PMKB.wapp_cons; [| apply PMKB.wapp_nil]. cbn [fst snd]. unfold BIGSHADOW_LO, BIGSHADOW_HI. clear - OBIG; lia. }
    assert (OUT8 : forall a n, (a + n <= op + 8 \/ op + 9 <= a) -> forall i, a <= i < a + n -> L5.outside [(op + 8, 1)] i).
    { intros a n X3 i Hi rr [<-|[]] Hr. unfold L5.in_rng in Hr. cbn [fst snd] in Hr. clear - Hi Hr X3. lia. }
    assert (OUTB8 : forall q' m, In (q', m) LB -> forall i, q' <= i < q' + m -> L5.outside [(op + 8, 1)] i).
    { intros q' m Hq i Hi rr [<-|[]] Hr. unfold L5.in_rng in Hr. cbn [fst snd] in Hr.
      destruct (PMBSK.blk_obj_apart L ar C HI HIok _ _ _ _ _ _ _ q' m op 384 HH6 Hq (AOF' op 384 ltac:(lia) ltac:(lia))) as [Z'|Z']; clear - Hi Hr Z'; lia. }
    assert (OUT8I : forall i, 0x678780 <= i < 0x69a4f4 -> L5.outside [(op + 8, 1)] i).
    { intros i Hi rr [<-|[]] Hr. unfold L5.in_rng in Hr. cbn [fst snd] in Hr. clear - Hi Hr O1; lia. }
    apply (KONT fx7 R7 Mf modelf LK6 Aw6 (PMPK.set_more s4 0) sm4 en k true cr).
    + apply L5SAR.preserved_by_index. intros j Hj. pose proof Hj as Hj'. unfold L5SAR.cs_all in Hj.
      repeat (destruct Hj as [<-|Hj]; [first [ rewrite E2; exact (eq_sym Rsp) | rewrite E8; apply Z_to_bv_bv_unsigned | rewrite E9; apply Z_to_bv_bv_unsigned
           | rewrite E18; apply Z_to_bv_bv_unsigned | rewrite E19; apply Z_to_bv_bv_unsigned | rewrite E20; apply Z_to_bv_bv_unsigned
           | rewrite E21; apply Z_to_bv_bv_unsigned | rewrite E22; apply Z_to_bv_bv_unsigned | rewrite E23; apply Z_to_bv_bv_unsigned
           | rewrite E24; apply Z_to_bv_bv_unsigned | rewrite E25; apply Z_to_bv_bv_unsigned
           | rewrite (KS7 _) by inl; rewrite (R6c _) by inl; apply G34'; inl ] |]).
      destruct Hj.
    + cbn beta. unfold r_tv. replace (blen p <=? s_pos X) with true by (symmetry; apply Z.leb_le; exact HEOF).
      destruct (BRB6 _ Iq) as (Xq1 & Xq2). destruct (BRB6 _ Ib) as (Xb1 & Xb2). cbn [fst snd] in Xq1, Xq2, Xb1, Xb2.
      split.
      { apply (PMBPAR.parser_more_updA M6 Mf op ois s4 0 PA6).
        * clear - O1; lia.
        * clear - O1 O3; lia.
        * apply (PMKB.agA_obj L ar _ FF 0 0 _ M6 Mf EKf WAPP8 FRB op 8 (AOF op 8 ltac:(clear - Eop; lia) ltac:(clear - Eop; lia))). apply OUT8. clear; lia.
        * apply (PMKB.agA_obj L ar _ FF 0 0 _ M6 Mf EKf WAPP8 FRB (op + 9) 375 (AOF (op + 9) 375 ltac:(clear - Eop; lia) ltac:(clear - Eop; lia))). apply OUT8. clear; lia.
        * exact (PMKB.agsh_obj L ar _ FF 0 0 _ M6 Mf EKf WAPP8 FRB op 384 AOP).
        * pose proof PA6 as (_ & PD6 & _). apply (L5.defined_grows M6 Mf _ _ MGf PD6).
        * exact MO0f.
        * left; reflexivity.
        * unfold s4, PMSPA.with_src. cbn [PM.p_src]. rewrite QC4. exact Xq1.
        * unfold s4, PMSPA.with_src. cbn [PM.p_src]. rewrite QC4. unfold PM.CHUNK in Xq2 |- *. clear - Xq2; lia.
        * unfold s4, PMSPA.with_src. cbn [PM.p_src]. rewrite QC4. apply (PMKB.agA_blk L ar _ FF 0 0 _ M6 Mf EKf WAPP8 BRB6 _ _ Iq). apply OUTB8. exact Iq.
        * unfold s4, PMSPA.with_src. cbn [PM.p_b]. exact Xb1.
        * unfold s4, PMSPA.with_src. cbn [PM.p_b PM.p_k]. clear - Xb2; lia.
        * unfold s4, PMSPA.with_src. cbn [PM.p_b PM.p_k]. apply (PMKB.agA_blk L ar _ FF 0 0 _ M6 Mf EKf WAPP8 BRB6 _ _ Ib). apply OUTB8. exact Ib.
        * unfold s4, PMSPA.with_src. cbn [PM.p_tb]. intros c0 n0 p0 E0.
          assert (Ip : In (p0, c0) LB) by (apply PINC; unfold PM.parser_own, PM.vs_own; rewrite E0; right; right; left; reflexivity).
          apply (PMKB.agA_blk L ar _ FF 0 0 _ M6 Mf EKf WAPP8 BRB6 _ _ Ip). apply OUTB8. exact Ip. }
      split.
      { apply (PMKB.iss_keepA RSEGS AD L ar _ FF 0 0 _ M6 Mf EKf WAPP8 FRB BRB6 ois str sm4 AOI); [exact SINC| | | exact IA6].
        * apply OUT8. clear - Eop Eois; lia.
        * intros c0 n0 p0 E0. unfold PMKB.blk_out. apply (OUTB8 p0 c0). apply SINC. unfold PM.vs_own. rewrite E0. left; reflexivity. }
      split.
      { apply (PECFA.enc_keepA RSEGS EE L ar _ FF 0 0 _ M6 Mf EKf WAPP8 FRB BRB6 ov fb en (AOF ov 56 ltac:(lia) ltac:(lia))); [| exact EINC| | exact EA6].
        * apply OUT8. clear - Eop Eov; lia.
        * intros Hp. refine (OUTB8 _ _ _). apply EINC. unfold PEC.enc_own. replace (PEC.en_k en =? 0) with false by (symmetry; apply Z.eqb_neq; lia). left. reflexivity. }
      split.
      { apply (PMKB.u64_keepA RSEGS L ar _ FF 0 0 _ M6 Mf EKf WAPP8 FRB (op + 384) _ (AOF (op + 384) 8 ltac:(lia) ltac:(lia))); [| exact VREF6]. apply OUT8. clear; lia. }
      split.
      { apply (PECFA.sink_keepA RSEGS L ar _ FF 0 0 _ M6 Mf EKf WAPP8 FRB BRB6 P osk k (AOF osk 24 ltac:(lia) ltac:(lia))); [| exact KINC| | exact SKA6].
        * apply OUT8. clear - Eop Eosk; lia.
        * intros Hp. refine (OUTB8 _ _ _). apply KINC. unfold PESK.sink_own. replace (PESK.sk_c k =? 0) with false by (symmetry; apply Z.eqb_neq; lia). left. reflexivity. }
      split.
      { change (PMSTA.base_okA RSEGS PMB.AD Mf). apply (PMBSK.base_keep L ar C LY _ FF 0 0 _ M6 Mf EKf); [| exact BASE6]. intros a Ha rr [<-|[]] Hr. unfold L5.in_rng in Hr. cbn [fst snd] in Hr. clear - Ha Hr O1; lia. }
      split.
      { apply (PECFA.err_okA_keep RSEGS AD AAD EE L ar _ FF 0 0 _ M6 Mf EKf true PECSB.addrs_wf_B); [| exact ERR6]. exact (SDEP _ OUT8I). }
      split; [unfold PMPK.set_more, s4, PMSPA.with_src; cbn [PM.p_tb PM.p_tg]; exact TBOK|].
      split.
      { unfold PMPK.set_more, s4, PMSPA.with_src. cbn [PM.p_src]. change src4 with (PM.p_src s4).
        apply (content_keepA' LB FF 0 0 [(op + 8, 1)] M6 Mf fb p s4 str sm4 op EKf WAPP8 FRB BRB6 AOI); [| exact SINC| | intros q' m Hq'; exact (OUTB8 q' m Hq')| exact IA6| exact PA6| exact CONT6].
        * fold ois. apply OUT8. clear - Eop Eois; lia.
        * unfold s4, PMSPA.with_src. cbn [PM.p_src]. rewrite QC4. exact Iq. }
      split.
      { unfold PEC.clink, r_fail, PMPK.set_more, s4, PMSPA.with_src. cbn [s_more s_done s_depth s_stk s_pos s_estk s_edepth s_lo s_hi s_bad s_ec w_more w_ec PM.p_more PM.p_done PM.p_depth PM.p_stk PM.p_src].
        split; [reflexivity|]. split; [exact Ldone|]. split; [exact Ldepth|]. split; [exact Lstk|].
        split; [intros X'; discriminate X'|]. split; [exact Lestk|]. split; [exact Ledepth|]. split; [exact Lz| exact Lbad]. }
      split.
      { unfold PECA.ec_stateA, r_fail. cbn [s_ec w_more w_ec]. fold oec. exists 1. split; [clear; lia|].
        pose proof EC6 as (EC6a & EC6b & EC6c & EC6d). split; [|split; [|split]].
        * apply (PMF.u32_at_agree RSEGS M6 Mf); [| clear - O1 Eop Eoec; lia| clear - O3 Eop Eoec; lia| exact EC6a].
          apply (proj1 (PMKB.agA_obj L ar _ FF 0 0 _ M6 Mf EKf WAPP8 FRB oec 4 (AOF oec 4 ltac:(lia) ltac:(lia)) ltac:(apply OUT8; clear - Eop Eoec; lia))).
        * apply (L5C.u64_at_agree RSEGS M6 Mf); [| clear - O1 Eop Eoec; lia| clear - O3 Eop Eoec; lia| exact EC6b].
          apply (proj1 (PMKB.agA_obj L ar _ FF 0 0 _ M6 Mf EKf WAPP8 FRB (oec + 8) 8 (AOF (oec + 8) 8 ltac:(lia) ltac:(lia)) ltac:(apply OUT8; clear - Eop Eoec; lia))).
        * apply (L5.defined_grows M6 Mf _ _ MGf EC6c).
        * exact (PMKB.acc_keepA' L ar _ FF 0 0 _ M6 Mf EKf WAPP8 FRB oec 16 (AOF oec 16 ltac:(lia) ltac:(lia)) EC6d). }
      split; [intros _; reflexivity|].
      exact (PMKB.acc_keepA' L ar _ FF 0 0 _ M6 Mf EKf WAPP8 FRB op 392 (AOF op 392 ltac:(lia) ltac:(lia)) ACC6).
    + unfold PMPK.set_more, s4, PMSPA.with_src. cbn [PM.p_src]. exact STEP4.
    + intros _; reflexivity.
    + exact AHf.
    + unfold PMSP.credit_keep, PMPK.set_more, s4, PMSPA.with_src, PECA.pot_allA, PEC.credit_add, PM.pot_parser. cbn [PM.p_k PM.p_tb PM.p_tg fst snd]. clear; lia.
    + exact MRTf.
    + exact INCL6.
    + exact INCA6.
    + exact AMf.
    + unfold PMPK.set_more. change (PEC.owned (PM.PST 0 (PM.p_done s4) (PM.p_depth s4) (PM.p_src s4) (PM.p_tb s4) (PM.p_tg s4) (PM.p_b s4) (PM.p_k s4) (PM.p_stk s4)) en k)
        with (PEC.owned s4 en k). rewrite EOWN4. exact HHf.
  -
    assert (D1 : d = 1) by (clear - Hd D1'; lia). rewrite D1 in Yd, CONS, SHORT, DEFd, BYT. clear Hd D1' SHORT.
    destruct CW4 as (CWP & CWB & CW5). unfold PEC.pos_of in CWP.
    assert (HPOS : s_pos X < blen p) by (clear - CONS UNR CWP; lia).
    assert (POS4 : PEC.pos_of p src4 sm4 = s_pos X + 1) by (unfold PEC.pos_of; clear - CONS UNR; lia).
    rewrite POS in BYT. rewrite (slice_pos_1 p (s_pos X)) in BYT by (clear - HPOS PPOS; lia).
    assert (U8 : L5.u8_at RSEGS M4 (F + 32) (bat p (s_pos X))) by (specialize (BYT 0%nat ltac:(cbn; clear; lia)); cbn [nth] in BYT; rewrite Z.add_0_r in BYT; exact BYT).
    pose proof (bat_byte p (s_pos X) BOK ltac:(clear - HPOS PPOS; lia)) as BB.
    set (t := bat p (s_pos X)) in *. set (X2 := w_pos (s_pos X + 1) X).
    set (H4 := ahid Aw4 model4) in *. set (MV4 := mrestrict H4 M4) in *.
    pose proof (L5SAR.vis_pack L ar C HI LYa HIok _ _ LK4 cr Aw4 M4 model4 HH4) as (_ & VIS4 & _ & VFS4 & _). fold H4 in VIS4, VFS4.
    pose proof (PEBRTVP.artC_conc fx4 R4 MV4 (fun j => match j with 2%nat => sp | 36%nat => op | 37%nat => ov | 38%nat => oec | 47%nat => F | _ => 0 end)) as PP.
    cbn beta iota in PP. rewrite Yd in PP. L5SAR.feed PP ltac:(first [assumption | reflexivity]).
    destruct PP as (fx5 & R5 & M5v & MG5 & _ & FRZ5 & MS5 & KS5).
    assert (E5 : M5v = MV4) by (apply L5SAR.mem_eq_of_agree; intros a Ha; apply FRZ5; exact Ha). subst M5v.
    assert (DV4 : L5.defined MV4 (F + 32) 1).
    { apply (proj2 (L5A.defined_vis H4 M4 (F + 32) 1 (VFS4 (F + 32) 1 ltac:(clear - GFS1; lia) ltac:(clear - GFS2; lia)))). exact DEFd. }
    assert (U8v : L5.u8_at RSEGS MV4 (F + 32) t).
    { apply (proj2 (L5A.u8_at_vis H4 M4 (F + 32) t (VFS4 (F + 32) 1 ltac:(clear - GFS1; lia) ltac:(clear - GFS2; lia)) ltac:(clear - GFR; lia) ltac:(clear - GFR; lia))). exact U8. }
    destruct (PMPX.lbu_run RSEGS fx5 R5 MV4 0xb70a0 W_b7050 12%bv 22%bv 0%bv (F + 32) F_b7050 eq_refl D_b7050) as (tb & Htb & U8t & MSt).
    { intros E0. apply (f_equal bv_unsigned) in E0. vm_compute in E0. discriminate E0. }
    { clear; lia. } { clear; lia. }
    { rewrite L5K.rl22. rewrite (KS5 22%nat) by inl. exact G22'. }
    { clear - Q0f GFR; lia. }
    { change (bv_signed (0%bv : bv 12)) with 0. clear - Q0f GFR; lia. }
    { change (bv_signed (0%bv : bv 12)) with 0. rewrite Z.add_0_r. exact DV4. }
    change (0xb70a0 + 4) with 0xb70a4 in MSt. rewrite L5K.rl12 in MSt. change (bv_signed (0%bv : bv 12)) with 0 in U8t. rewrite Z.add_0_r in U8t.
    assert (Etb : tb = t) by exact (u8_at_inj MV4 (F + 32) tb t U8t U8v Htb BB). subst tb.
    set (R5' := regupd R5 (reg 12) (Z_to_bv 64 t)) in MSt.
    assert (R5o : forall j, In j [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%nat -> getr R5' (reg j) = getr R4 (reg j)).
    { intros j Hj. unfold R5'. rewrite (reg12_other R5 _ j Hj). apply KS5. revert j Hj. apply (L5K.incl_b [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%nat). vm_compute. reflexivity. }
    assert (R512 : getr R5' (reg 12) = Z_to_bv 64 t) by (unfold R5'; apply PMPX.regupd_same_idx; lia).
    pose proof (PEBRTVP.artD_conc fx5 R5' MV4 (fun j => match j with 2%nat => sp | 36%nat => op | 37%nat => ov | 38%nat => oec | 47%nat => F | 49%nat => t | _ => 0 end)) as PP.
    cbn beta iota in PP.
    L5SAR.feed PP ltac:(first [assumption | (rewrite R5o by inl; assumption) | clear - BB; lia]).
    destruct PP as (fx6 & R6 & M6v & MG6 & _ & FRZ6 & MS6 & KS6 & Z1 & Z10 & Z11 & Z13).
    assert (E6 : M6v = MV4) by (apply L5SAR.mem_eq_of_agree; intros a Ha; apply FRZ6; exact Ha). subst M6v.
    apply (L5SAR.apiece_ro L ar C HI LYa HIok LB FF' LK4 cr Aw4 M4 model4 fx4 fx6 R4 0xb709c R6 0xb73bc MV4 K HH4 AM4).
    { eapply msteps_trans; [exact MS5| eapply msteps_trans; [exact MSt| exact MS6]]. }
    { intros x Hx. exact Hx. }
    { intros a Ha. reflexivity. }
    intros M5 model5 HH5 AM5 MRT5 HID5 VIS5 MGM5 FR5.
    assert (E5 : M5 = M4) by (apply L5SAR.mem_eq_of_agree; exact FR5). subst M5.
    pose proof (PMBUK.binv_model L ar HI M model LBX FF LK Aw sp 30720 (sp - 96) (own sp R) F 0 WR (PEC.owned s en k) M4 model4 LK4 cr Aw4 model5 BI4 HH5 AM5 MRT5) as BI5.
    assert (R6c : forall j, In j [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%nat -> getr R6 (reg j) = getr R4 (reg j)).
    { intros j Hj. rewrite (KS6 j) by (revert j Hj; apply (L5K.incl_b [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%nat); vm_compute; reflexivity).
      exact (R5o j Hj). }

    unfold PECSB.read_value_spec, PECSPA.read_value_spec, PECSPA.crun_spec in RV.
    apply (RV PMODE t fx6 R6 M4 model5 K LBX FF' LK4 Aw4 cr (sp - 96) 0xb70b4 fb cat p X2 s4 str sm4 en k e).
    { rewrite EOWN4. exact HH5. }
    { exact AM5. }
    { exact K0. }
    { split; [rewrite L5K.rl1; exact Z1|]. split; [split; [clear; lia| reflexivity]|]. split; [rewrite L5K.rl2; rewrite (R6c 2%nat) by inl; exact G2'|].
      split; [rewrite L5K.rl3; rewrite (R6c 3%nat) by inl; rewrite (G34' 3%nat) by inl; rewrite <- L5K.rl3; exact Rgp|].
      split; [rewrite L5K.rl4; rewrite (R6c 4%nat) by inl; rewrite (G34' 4%nat) by inl; rewrite <- L5K.rl4; exact Rtp|].
      change (PMSPA.pm_scr 8) with 28672. change (28672 / 8) with 3584.
      pose proof BI4 as (_ & _ & _ & _ & _ & ASTK4 & EKb4 & _).
      split; [apply (L5SAR.astk_sub ar M4 M4 sp 30720 96 28672 ASTK4 (mem_grows_refl M4)); [clear; lia| clear; lia| clear; lia| replace (sp - 96) with (sp + (-6) * 16) by (clear; lia); rewrite Z_mod_plus_full; exact A16]|].
      apply SZK; [exact EKb4| clear; lia| clear; lia| | clear; lia].
      apply PMKB.mod16_8'. replace (sp - 96 - 28672) with (sp + (-1798) * 16) by (clear; lia). rewrite Z_mod_plus_full. exact A16. }
    { pose proof (HAJ.aior_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH5) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & NDF5 & _).
      apply (PMBUAR.ffroomA_push 9 8 FF LK LK4 _ FRM (fun x Hx => GLKI2 x (INCLK4 x Hx))); [exact NDF5| clear; lia]. }
    { apply (PMBUAR.ffrsA_push FF sp (sp - 96) F 0 (sp - 96 + 32) FRS); clear; lia. }
    { exact FOK'. }
    { replace (sp - 96) with (sp + (-3) * 32) by (clear; lia). rewrite Z_mod_plus_full. exact SP32. }
    { split; [rewrite L5K.rl10; exact Z10|]. split; [rewrite L5K.rl11; exact Z11|]. split; [rewrite L5K.rl13; exact Z13|].
      split; [exact BB|]. rewrite L5K.rl12. rewrite (KS6 12%nat) by inl. exact R512. }
    { split; [exact PA4|]. split; [exact IA4|]. split; [exact EA4|]. split; [exact VREF4|]. split; [exact SKA4|].
      split; [exact BASE4|]. split; [exact ERR4|]. split; [unfold s4, PMSPA.with_src; cbn [PM.p_tb PM.p_tg]; exact TBOK|].
      split; [unfold s4, PMSPA.with_src; cbn [PM.p_src]; exact CONT4|].
      split.
      { unfold PEC.clink, X2, w_pos, s4, PMSPA.with_src. cbn [s_more s_done s_depth s_stk s_pos s_estk s_edepth s_lo s_hi s_bad s_ec PM.p_more PM.p_done PM.p_depth PM.p_stk PM.p_src].
        split; [exact Lmore|]. split; [exact Ldone|]. split; [exact Ldepth|]. split; [exact Lstk|].
        split; [intros _ _; exact POS4|]. split; [exact Lestk|]. split; [exact Ledepth|]. split; [exact Lz| exact Lbad]. }
      split; [unfold X2, w_pos; cbn [s_ec]; exact ECS4|]. split; [exact ECI| exact ACC4]. }
    { exact INCS. }
    { exact POK. }
    { unfold PECSPA.mp_rv, pre_run, pre, X2, w_pos. cbn [s_stk s_pos s_more s_done s_halt s_depth s_ec s_estk s_edepth s_lo s_hi s_bad].
      split; [split; [| exact MORE]| split; [exact DONE| split; [exact HALT| split; [exact DEPB| split; [exact ESTKB| exact STKB]]]]].
      split; [exact BOK|]. split; [clear - HPOS PPOS; lia|]. split; [exact PLH|]. split; [exact PBAD|]. split; [exact PED| exact PEOK]. }
    { unfold r_tv in NB. replace (blen p <=? s_pos X) with false in NB by (symmetry; apply Z.leb_gt; exact HPOS). exact NB. }
    { unfold r_tv in HB. replace (blen p <=? s_pos X) with false in HB by (symmetry; apply Z.leb_gt; exact HPOS). exact HB. }
    { unfold s4, PMSPA.with_src. exact CRED. }
    intros fx7 R7 M7 model7 LK7 Aw7 s7 sm7 en7 k7 e7 cr7 RP7 CPRE7 STEP7 EE7 HP7 CK7 MRT7 INCLK7 INCAw7 AM7 HH7.
    change (PMSPA.pm_scr 8) with 28672 in HP7.
    assert (WRR' : forall rr a, In rr WR -> L5.in_rng rr a -> (fb + 32 <= a < fb + 2040) \/ (0x678780 <= a < 0x69a4f4)).
    { intros rr a Hin Hr. destruct (WRR rr a Hin Hr) as [Y|[Y|[Y|[Y|[Y|[Y|[Y|[Y|[Y|Y]]]]]]]]];
        first [left; clear - Y Eop Eois Eoec Eov Eosk; lia | right; clear - Y; lia]. }
    set (LB7 := PEC.owned s7 en7 k7 ++ LBX) in *.
    assert (BI7 : PMBUK.binv L ar HI M model LBX FF LK Aw sp 30720 (sp - 96) (own sp R) F 0 WR (PEC.owned s7 en7 k7) M7 model7 LK7 cr7 Aw7).
    { apply (PMBUK.binv_callee L ar C HI HIok M model LBX FF LK Aw sp 30720 (sp - 96) (sp - 88) sp (ocell sp) (own sp R) F fl 0 LK2 M2 model2 cr (PEC.owned s en k) G
               WR WR (PEC.owned s en k) [] (PEC.owned s7 en7 k7) M4 model5 LK4 cr Aw4 M7 model7 LK7 cr7 Aw7 28672 WR BI5 HP7 HH7 AM7 MRT7 INCAw7 INCLK7);
        [clear; lia| clear; lia| | intros a _ X'; exact X'| intros a X'; exact X'].
      intros rr a Hin Hr. change (ff_bytes 0 / 8) with 8. unfold ocell, SB.
      pose proof GFR as (GF1 & GF2 & _). assert (DF1 : 0 <= F / 8) by (apply Z.div_pos; clear - GF1; lia).
      assert (DF2 : F / 8 <= 17592186044408) by (apply Z.div_le_upper_bound; clear - GF2; lia).
      pose proof FSAPP as (FA0 & FA1 & FA2).
      destruct (WRR' rr a Hin Hr) as [X'|X']; (split; [clear - X' SL96 SPT F2 FSCEIL; lia|]).
      - destruct FA1 as [Y|Y]; clear - X' Y DF1 DF2 F1 F2; lia.
      - clear - X' DF1; lia. }
    set (H7 := ahid Aw7 model7) in *. set (MV7 := mrestrict H7 M7) in *.
    destruct (PMBUK.vis_facts L ar C HI LYa HIok M model LBX FF LK Aw sp 30720 (sp - 96) (sp - 88) sp (ocell sp) (own sp R) F fl 0 LK2 M2 model2 cr (PEC.owned s en k) G
                WR (PEC.owned s7 en7 k7) M7 model7 LK7 cr7 Aw7 BI7) as ((WS7 & _ & CSB7 & CUAR7 & _) & OWN7 & (FD7 & FW7 & FSW7 & FLC7 & FLW7) & (FLCc7 & FLV7 & VF7 & VS7 & VSH7)).
    change (ff_bytes 0) with 64 in *. change (64 / 8) with 8 in *. replace (sp - (sp - 96)) with 96 in WS7 by (clear; lia).
    replace (F + 64 - 8) with (F + 56) in FLC7 by (clear; lia).
    fold H7 in WS7, CSB7, CUAR7, OWN7, FD7, FW7, FSW7, FLC7, FLW7, FLV7, VF7, VS7, VSH7. fold MV7 in WS7, CSB7, CUAR7, OWN7, FD7, FW7, FSW7, FLC7, FLW7.
    assert (R7c : forall j, In j [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%nat -> getr R7 (reg j) = getr R4 (reg j)).
    { intros j Hj. rewrite (L5SAR.cs_of_preserved R6 R7 j RP7 Hj). exact (R6c j Hj). }
    pose proof OWN7 as (S8 & S16 & S24 & S32 & S40 & S48 & S56 & S64 & S72 & S80 & S88).
    pose proof (bv_unsigned_in_range 64 (getr R (reg 1))) as B1. pose proof (bv_unsigned_in_range 64 (getr R (reg 8))) as B8.
    pose proof (bv_unsigned_in_range 64 (getr R (reg 9))) as B9. pose proof (bv_unsigned_in_range 64 (getr R (reg 18))) as B18.
    pose proof (bv_unsigned_in_range 64 (getr R (reg 19))) as B19. pose proof (bv_unsigned_in_range 64 (getr R (reg 20))) as B20.
    pose proof (bv_unsigned_in_range 64 (getr R (reg 21))) as B21. pose proof (bv_unsigned_in_range 64 (getr R (reg 22))) as B22.
    pose proof (bv_unsigned_in_range 64 (getr R (reg 23))) as B23. pose proof (bv_unsigned_in_range 64 (getr R (reg 24))) as B24.
    pose proof (bv_unsigned_in_range 64 (getr R (reg 25))) as B25. change (bv_modulus 64) with (2 ^ 64) in *.
    pose proof (PEBRTVP.artE_conc fx7 R7 MV7 (fun j => match j with 2%nat => sp | 36%nat => op | 37%nat => ov | 38%nat => oec | 47%nat => F | 48%nat => fl
             | 64%nat => bv_unsigned (getr R (reg 1)) | 65%nat => bv_unsigned (getr R (reg 8)) | 66%nat => bv_unsigned (getr R (reg 9))
             | 67%nat => bv_unsigned (getr R (reg 18)) | 68%nat => bv_unsigned (getr R (reg 19)) | 69%nat => bv_unsigned (getr R (reg 20))
             | 70%nat => bv_unsigned (getr R (reg 21)) | 71%nat => bv_unsigned (getr R (reg 22)) | 72%nat => bv_unsigned (getr R (reg 23))
             | 73%nat => bv_unsigned (getr R (reg 24)) | 74%nat => bv_unsigned (getr R (reg 25)) | _ => 0 end)) as PP.
    cbn beta iota in PP.
    L5SAR.feed PP ltac:(first [assumption | (rewrite R7c by inl; assumption) | unfold PEBRTVP.aligned; assumption]).
    destruct PP as (fx8 & R8 & M8v & MG8 & _ & FRZ8 & MS8 & KS8 & E1 & E2 & E8 & E9 & _ & E18 & E19 & E20 & E21 & E22 & E23 & E24 & E25 & FL0 & _).
    assert (R8ra : getr R8 (reg 1) = Z_to_bv 64 r) by (rewrite E1, Z_to_bv_bv_unsigned; exact Rra).
    pose proof (PMK.ret_to RSEGS fx8 R8 M8v 0xb71a0 W_b7150 r F_b7150 eq_refl D_b7150 R8ra Hr1 Hr2) as MSr.
    apply (PMBUK.retire_core L ar C HI LYa HIok M model LBX FF LK Aw sp 30720 (sp - 96) (sp - 88) sp (ocell sp) (own sp R) F fl 0 LK2 M2 model2 cr (PEC.owned s en k) G
             WR (PEC.owned s7 en7 k7) M7 model7 LK7 cr7 Aw7 fx7 fx8 R7 0xb70b4 R8 r M8v K BI7 (msteps_trans _ _ _ _ MS8 MSr) MG8).
    { intros a Ha Nw. unfold PMBUK.Wret in Nw. change (ff_bytes 0) with 64 in Nw. apply FRZ8; [exact Ha| intros X'; apply Nw; left; left; clear - X'; lia
         | intros X'; apply Nw; left; right; unfold SB; clear - X'; lia| intros X'; apply Nw; right; clear - X'; lia]. }
    { exact FL0. }
    intros Mf modelf FZf AHf MRTf AMf HHf.
    assert (EKf : L5SAR.ek L ar LB7 FF 0 0 [] M7 Mf).
    { apply (PMBUAR.wret_ek L ar C HI LY HIok LBX FF LK Aw sp 30720 (sp - 96) (sp - 88) sp (ocell sp) (own sp R) F fl 0 LK2 M2 model2 cr (PEC.owned s en k)
               LB7 LK7 cr7 Aw7 M7 Mf _ [] (fun _ => False) G HH7 (fun a X' => match X' with end)).
      intros a Ha N. apply FZf; [exact Ha| intros X'; apply N; left; exact X']. }
    pose proof (PMBSK.brb_of L ar C HI HIok _ _ _ _ _ _ _ HH7) as BRB7.
    destruct CPRE7 as (PA7 & IA7 & EA7 & VREF7 & SKA7 & BASE7 & ERR7 & TBOK7 & CONT7 & CL7 & ECS7 & ECI7 & ACC7).
    pose proof BI7 as (_ & _ & _ & INCA7 & INCL7 & _).
    assert (PINC7 : incl (PM.parser_own s7) LB7) by (unfold LB7, PEC.owned; intros x Hx; apply in_or_app; left; apply in_or_app; left; exact Hx).
    assert (SINC7 : incl (PM.vs_own str) LB7) by (unfold LB7; apply incl_appr; exact INCS).
    assert (EINC7 : incl (PEC.enc_own en7) LB7).
    { unfold LB7, PEC.owned. intros x Hx. apply in_or_app. left. apply in_or_app. right. apply in_or_app. left. exact Hx. }
    assert (KINC7 : incl (PESK.sink_own k7) LB7).
    { unfold LB7, PEC.owned. intros x Hx. apply in_or_app. left. apply in_or_app. right. apply in_or_app. right. exact Hx. }
    assert (Iq7 : In (PM.sr_qc (PM.p_src s7), PM.CHUNK) LB7) by (apply PINC7; unfold PM.parser_own, PM.src_own; left; reflexivity).
    apply (KONT fx8 R8 Mf modelf LK7 Aw7 s7 sm7 en7 k7 e7 cr7).
    + apply L5SAR.preserved_by_index. intros j Hj. pose proof Hj as Hj'. unfold L5SAR.cs_all in Hj.
      repeat (destruct Hj as [<-|Hj]; [first [ rewrite E2; exact (eq_sym Rsp) | rewrite E8; apply Z_to_bv_bv_unsigned | rewrite E9; apply Z_to_bv_bv_unsigned
           | rewrite E18; apply Z_to_bv_bv_unsigned | rewrite E19; apply Z_to_bv_bv_unsigned | rewrite E20; apply Z_to_bv_bv_unsigned
           | rewrite E21; apply Z_to_bv_bv_unsigned | rewrite E22; apply Z_to_bv_bv_unsigned | rewrite E23; apply Z_to_bv_bv_unsigned
           | rewrite E24; apply Z_to_bv_bv_unsigned | rewrite E25; apply Z_to_bv_bv_unsigned
           | rewrite (KS8 _) by inl; rewrite (R7c _) by inl; apply G34'; inl ] |]).
      destruct Hj.
    + cbn beta. unfold r_tv. replace (blen p <=? s_pos X) with false by (symmetry; apply Z.leb_gt; exact HPOS). fold t. fold X2.
      split.
      { apply (PMKB.parser_keepA RSEGS AD L ar LB7 FF 0 0 [] M7 Mf EKf PMKB.wapp_nil FRB BRB7 _ _ _ AOP); [exact PINC7| intros i _ r0 []| intros i _ r0 []| intros i _ r0 []| intros c0 n0 p0 _ i _ r0 []| exact PA7]. }
      split.
      { apply (PMKB.iss_keepA RSEGS AD L ar LB7 FF 0 0 [] M7 Mf EKf PMKB.wapp_nil FRB BRB7 ois str sm7 AOI); [exact SINC7| intros i _ r0 []| intros c0 n0 p0 _ i _ r0 []| exact IA7]. }
      split.
      { apply (PECFA.enc_keepA RSEGS EE L ar LB7 FF 0 0 [] M7 Mf EKf PMKB.wapp_nil FRB BRB7 ov fb en7 (AOF ov 56 ltac:(lia) ltac:(lia))); [intros i _ r0 []| exact EINC7| intros _ i _ r0 []| exact EA7]. }
      split.
      { apply (PMKB.u64_keepA RSEGS L ar LB7 FF 0 0 [] M7 Mf EKf PMKB.wapp_nil FRB (op + 384) ov (AOF (op + 384) 8 ltac:(lia) ltac:(lia))); [intros i _ r0 []| exact VREF7]. }
      split.
      { apply (PECFA.sink_keepA RSEGS L ar LB7 FF 0 0 [] M7 Mf EKf PMKB.wapp_nil FRB BRB7 P osk k7 (AOF osk 24 ltac:(lia) ltac:(lia))); [intros i _ r0 []| exact KINC7| intros _ i _ r0 []| exact SKA7]. }
      split.
      { change (PMSTA.base_okA RSEGS PMB.AD Mf). apply (PMBSK.base_keep L ar C LY LB7 FF 0 0 [] M7 Mf EKf); [intros a _ r0 []| exact BASE7]. }
      split.
      { apply (PECFA.err_okA_keep RSEGS AD AAD EE L ar LB7 FF 0 0 [] M7 Mf EKf e7 PECSB.addrs_wf_B); [| exact ERR7]. refine (SDEP [] _). intros i _ r0 []. }
      split; [exact TBOK7|].
      split.
      { apply (content_keepA' LB7 FF 0 0 [] M7 Mf fb p s7 str sm7 op EKf PMKB.wapp_nil FRB BRB7 AOI); [intros i _ r0 []| exact SINC7| exact Iq7| intros q' m _ i _ r0 []| exact IA7| exact PA7| exact CONT7]. }
      split; [exact CL7|].
      split.
      { apply (PECFA.ec_state_keepA RSEGS AD L ar LB7 FF 0 0 [] M7 Mf EKf PMKB.wapp_nil FRB fb _ cat (AOF oec 16 ltac:(lia) ltac:(lia))); [intros i _ r0 []| exact ECS7]. }
      split; [exact ECI7|].
      exact (PMKB.acc_keepA' L ar LB7 FF 0 0 [] M7 Mf EKf PMKB.wapp_nil FRB op 392 (AOF op 392 ltac:(lia) ltac:(lia)) ACC7).
    + apply (PMBPAR.src_step_transA (PM.p_src s) src4 (PM.p_src s7) sm sm4 sm7 STEP4). unfold s4, PMSPA.with_src in STEP7. cbn [PM.p_src] in STEP7. exact STEP7.
    + exact EE7.
    + exact AHf.
    + unfold s4, PMSPA.with_src in CK7. exact CK7.
    + exact MRTf.
    + exact INCL7.
    + exact INCA7.
    + exact AMf.
    + exact HHf.
Qed.

End WithHeap.
End PEBCRTV.
