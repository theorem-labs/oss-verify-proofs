(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.

From Stdlib Require Import ZArith List Lia Bool FunctionalExtensionality.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.jsoncons.fuzz_ubjson_encoder.images Require Import AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S9 Require Import PropExec CatExec CatSim StoreOk Hoare ShapeAlg SpinAlg AsanAcct HeapIface HeapIfaceA L5Defs L5Core L5CoreKit L5Kn L5KnA L5LazyA L5DefsAB0 L5CoreAB0S9 L5StepARB0S9.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import PmLayout PmLayoutA.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S9 Require Import PmModel PmModelFacts PmStatics PmStaticsA HeapIfaceAEx PmSpecs PmSpecsA PmSpecsAX PeSpecsAb PnStatics.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import PeCLayout PeCLayoutB.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S9 Require Import PeCSink PeCModel PeCSpecs PeCFrame PeCSinkA PeCModelA PeCStaticsA PeCSpecsA PeCSpecsAb PeCFrameA PeSpecsBXJ PmModelFactsA PeStepAB0 PeBSrcKitJ PeCRdReadSpecZ PeBRdReadP.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.Spec Require Import UbjRef.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S9.Spec Require Import UbjRefFactsS9.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Module PEBCRR.
Ltac inl := apply L5K.In_of_mem; vm_compute; reflexivity.
Abbreviation reg i := (Z_to_bv 5 (Z.of_nat i)).
Abbreviation RSEGS := AsanUbsan.M.loaded_segments.

Lemma own_reset s : PM.parser_own (PMSPA.pst_reset s) = PM.parser_own s.
Proof. destruct s as [m d dp src tb tg b k stk]. unfold PM.parser_own, PMSPA.pst_reset. cbn. destruct tb; reflexivity. Qed.
Lemma tb_ok_reset s : PM.tb_ok (PM.p_tb s) (PM.p_tg s) -> PM.tb_ok (PM.p_tb (PMSPA.pst_reset s)) (PM.p_tg (PMSPA.pst_reset s)).
Proof. destruct s as [m d dp src tb tg b k stk]. cbn. destruct tb; intros H; exact H. Qed.
Lemma inv_reset s : PM.tb_ok (PM.p_tb s) (PM.p_tg s) -> PM.inv (PMSPA.pst_reset s).
Proof.
  intros TB. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [|apply tb_ok_reset; exact TB].
  unfold PM.stack_shape. cbn [PMSPA.pst_reset PM.p_stk length nth]. split; [lia|]. split; [unfold PM.MAX_DEPTH; lia|]. split; [left; reflexivity|].
  split; [intros i Hi; lia|]. intros i Hi. assert (i = 0%nat) by lia. subst i. cbn [nth]. unfold PM.pstate_ok, PM.ps_root. cbn. split; [lia|]. right. right. split; [left; reflexivity| split; reflexivity].
Qed.
Lemma src_reset s : PM.p_src (PMSPA.pst_reset s) = PM.p_src s.
Proof. destruct s; reflexivity. Qed.

Lemma ek_drop (L : asan_layout) (ar : asan_run) BX LB FF sp scr W M M' : L5SAR.ek L ar (BX ++ LB) FF sp scr W M M' -> L5SAR.ek L ar LB FF sp scr W M M'.
Proof. induction BX as [|b BX IH]; intros E; [exact E| apply IH; exact (L5SAR.ek_tl L ar _ b FF sp scr W M M' E)]. Qed.

Lemma ffroomA_sub h h' FF LK LK2 : PMSPA.ffroomA h FF LK -> incl LK2 LK -> NoDup (map ff_addr (FF ++ LK2)) -> h' <= h -> PMSPA.ffroomA h' FF LK2.
Proof.
  intros FR INC ND Hh k Hk. specialize (FR k Hk). rewrite L5SAR.ff_count_app in FR. rewrite L5SAR.ff_count_app.
  pose proof (L5SAR.ff_count_incl k LK2 LK INC (L5SAR.nodup_of_map_app_r FF LK2 ND)) as C2. lia.
Qed.

Section SCFG_1.
Context {SCFG_P : ScfgP}.
Section WithHeap.
Variables (L : asan_layout) (ar : asan_run) (C : asan_statics_cells) (HI : asan_iface).
Variable P : PESKA.sink_policyA.
Hypothesis LY : PMB.layout L C.
Hypothesis HIok : HAJ.asan_iface_okR L ar C SCFG HI.
Let LYa := PMB.ly_as0 L C LY.

Theorem reader_read_ok : PECSB.reset_spec L ar HI -> PECSB.parse_spec L ar HI P -> PECRRZ.reader_read_specZ RSEGS PeCLayoutB.CADDR_B PeCLayoutB.CAADDR_B PeCLayoutB.EADDR_B L ar HI P.
Proof.
  intros RST PARSE. unfold PECRRZ.reader_read_specZ.
  intros PMODE fx R M model K LBX FF LK Aw cr sp r fb cat p s str sm en k e HH AM K0 ENT FRM FRS FOK SP32 A10 A11 RPRE LEN POS0 REM0 EN0 ED0 KZ0 INCS POK HB CRED KONT.
  destruct ENT as (Rra & RAok & Rsp & Rgp & Rtp & ASTK & STKSH). change (PMSPA.pm_scr 11) with 34816 in *. change (34816 / 8) with 4352 in STKSH.
  pose proof AM as (Mh & MI). pose proof ASTK as (A16 & SLO & SHI & SPT & SDEF & SUP). pose proof RAok as (Hr1 & Hr2).
  rewrite L5K.rl1 in Rra. rewrite L5K.rl2 in Rsp. rewrite L5K.rl3 in Rgp. rewrite L5K.rl4 in Rtp. rewrite L5K.rl10 in A10. rewrite L5K.rl11 in A11.
  pose proof RPRE as (PA & IA & EA & VREF & SKA & BASE & ERR & TBOK & CONT & EC & ACC).
  set (LBr := PEC.enc_own en ++ PESK.sink_own k ++ LBX).
  set (LB := PM.parser_own s ++ LBr).
  assert (ELB : PEC.owned s en k ++ LBX = LB) by (unfold LB, LBr, PEC.owned; rewrite <- !app_assoc; reflexivity). rewrite ELB in HH.
  set (op := PMSPA.o_p PeCLayoutB.CADDR_B fb) in *. set (oec := PMSPA.o_ec PeCLayoutB.CADDR_B fb) in *. set (ois := PMSPA.o_is PeCLayoutB.CADDR_B fb) in *. set (ov := PMSPA.o_v PeCLayoutB.CADDR_B fb) in *. set (osk := PESK.o_sink PeCLayoutB.EADDR_B fb) in *.
  pose proof FOK as ((rs & Hfb) & Fal).
  assert (AOF : forall a n, fb + 32 <= a -> a + n <= fb + 2040 -> PMSPA.aobjA FF a n).
  { intros a n Xa1 Xa2. exists (fb, 5, rs). split; [exact Hfb|]. cbn [ff_addr ff_class fst snd]. change (ff_bytes 5) with 2048. clear - Xa1 Xa2; lia. }
  assert (Eoec : oec = fb + 1120) by reflexivity. assert (Eop : op = fb + 592) by reflexivity.
  assert (Eois : ois = fb + 96) by reflexivity. assert (Eov : ov = fb + 496) by reflexivity. assert (Eosk : osk = fb + 432) by reflexivity.
  assert (INCSr : incl (PM.vs_own str) LBr) by (unfold LBr; intros x Hx; apply in_or_app; right; apply in_or_app; right; apply INCS; exact Hx).
  assert (INE : incl (PEC.enc_own en) LBr) by (unfold LBr; intros x Hx; apply in_or_app; left; exact Hx).
  assert (INK : incl (PESK.sink_own k) LBr) by (unfold LBr; intros x Hx; apply in_or_app; right; apply in_or_app; left; exact Hx).
  pose proof (HAJ.aior_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as (WB & WF & FSAPP & FSCEIL & _ & _ & _ & _ & _ & TOP & _).
  pose proof (WF _ Hfb) as (F1 & F2 & _). cbn [ff_addr ff_class fst snd] in F1, F2. change (ff_bytes 5) with 2048 in *. unfold app_mem, FS_BYTES in FSAPP, FSCEIL, F1, F2.
  pose proof (PMBSKJ.fs_above_img L ar C HI LY HIok _ _ _ _ _ _ _ HH) as FSI.
  pose proof (L5SAR.vis_pack L ar C HI LYa HIok LB FF LK cr Aw M model HH) as (HOFF & VISs & VIMG & VFS & VBLK & VBSH & VFSSH & VSTSH).
  set (H := ahid Aw model) in *. set (MV := mrestrict H M) in *.
  pose proof (PMBSKJ.mach_vis L ar C HI LY HIok LB FF LK cr Aw M model HH BASE) as (V0 & V1 & V2).
  pose proof (PMBSKJ.stk_vis L ar C HI LY HIok LB FF LK cr Aw M model sp 34816 32 HH ASTK ltac:(lia)) as (SL32 & SH32 & V3).
  pose proof (bv_unsigned_in_range 64 (getr R (reg 1))) as Hs1. pose proof (bv_unsigned_in_range 64 (getr R (reg 8))) as Hs8.
  pose proof (bv_unsigned_in_range 64 (getr R (reg 9))) as Hs9. pose proof (bv_unsigned_in_range 64 (getr R (reg 18))) as Hs18.
  change (bv_modulus 64) with (2 ^ 64) in *.

  assert (V0' : L5.img_clear MV 1273856 1306624) by (intros i Hi; apply V0; lia).
  pose proof (PMBRRP.brrA_conc fx R MV (fun j => match j with 2%nat => sp | _ => 0 end)) as PC. cbn beta iota in PC.
  L5SAR.feed PC ltac:(first [assumption | unfold PMBRRP.aligned; lia | lia]).
  destruct PC as (fx1 & R1 & M1v & MG1 & _ & FRZ1 & MS1 & KS1 & A1 & A2 & A8 & A9 & A11' & A18 & C32 & C24 & C16 & C8).
  unfold PMSPA.cfg. cbn [pa_reader_read PMB.AD PeLayoutA.ADDR_B PeCLayoutB.CADDR_B].
  apply (L5SAR.apiece L ar C HI LYa HIok LB FF LK cr Aw M model fx fx1 R 0xaa0ac R1 0xb5bd0 M1v (fun a => sp - 32 <= a < sp - 32 + 32) K HH AM MS1 MG1 FRZ1).
  { intros a Ha Wa. split; [|intros X; lia]. unfold aclientw, aclient_g. right; left. split; [lia| intros X; lia]. }
  intros M1 model1 HH1 AM1 MRT1 HID1 VIS1 MGM1 FR1 VV1.
  assert (EK01 : L5SAR.ek L ar LB FF sp 34816 [] M M1).
  { apply (PMKB.ek_own_frame L ar C HI LYa HIok LB FF LK cr Aw M M1 _ sp 34816 [] (sp - 32) (sp - 32 + 32) HH SPT); [lia|lia|lia|].
    intros a Ha Hn. apply FR1; [exact Ha| exact Hn]. }
  assert (ASTK1 : L5CA.astk ar M1 sp 34816) by (apply (L5SAR.astk_grows ar M M1 sp 34816 ASTK MGM1)).
  assert (SV1 : forall kq v, 1 <= kq <= 4 -> L5.u64_at RSEGS M1v (sp - 8 * kq) v -> L5.u64_at RSEGS M1 (sp - 8 * kq) v).
  { intros kq v Hk X. rewrite <- VIS1 in X. exact (proj1 (L5A.u64_at_vis H M1 (sp - 8 * kq) v (VISs (sp - 8 * kq) 8 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia)) X). }
  pose proof (PMBSKJ.frb_of L ar C HI HIok _ _ _ _ _ _ _ HH) as FRB. pose proof (PMBSKJ.brb_of L ar C HI HIok _ _ _ _ _ _ _ HH) as BRB.
  assert (AOP : PMSPA.aobjA FF op 384) by (apply AOF; clear - Eop; lia).
  assert (PA1 : PM.parser_at RSEGS PeCLayoutB.CADDR_B PMSPA.accA PMSPA.annA M1 op ois s).
  { apply (PMKB.parser_keepA RSEGS PeCLayoutB.CADDR_B L ar LB FF sp 34816 [] M M1 EK01 PMKB.wapp_nil FRB BRB _ _ _ AOP); [| intros i _ r0 []| intros i _ r0 []| intros i _ r0 []| intros c0 n0 p0 _ i _ r0 []| exact PA].
    unfold LB. apply incl_appl, incl_refl. }

  unfold PECSB.reset_spec, PMSPA.reset_spec in RST. cbn [pa_reset PMB.AD PeLayoutA.ADDR_B PeCLayoutB.CADDR_B] in RST.
  apply (RST fx1 R1 M1 model1 K LBr FF LK Aw cr (sp - 32) 0xaa0d8 fb s HH1 AM1 K0).
  { split; [rewrite L5K.rl1; exact A1|]. split; [split; [lia| reflexivity]|]. split; [rewrite L5K.rl2; exact A2|].
    split; [rewrite L5K.rl3; rewrite (KS1 3%nat) by inl; exact Rgp|]. split; [rewrite L5K.rl4; rewrite (KS1 4%nat) by inl; exact Rtp|].
    change (PMSPA.pm_scr 1) with 14336. change (14336 / 8) with 1792.
    split; [apply (L5SAR.astk_sub ar M1 M1 sp 34816 32 14336 ASTK1 (fun _ X => X)); [lia|lia|lia|]; replace (sp - 32) with (sp + (-2) * 16) by lia; rewrite Z.mod_add by lia; exact A16|].
    apply (PMKB.stksh_keepA L ar LB FF sp 34816 [] M M1 EK01 PMKB.wapp_nil (sp - 32 - 14336) 1792); [lia|lia|lia| | lia|].
    - apply PMKB.mod16_8'. replace (sp - 32 - 14336) with (sp + (-898) * 16) by lia. rewrite Z_mod_plus_full. exact A16.
    - apply (PMKB.shadow_zero_sub M (sp - 34816) 4352); [| | lia| lia| lia| exact STKSH].
      + apply PMKB.mod16_8'. replace (sp - 34816) with (sp + (-2176) * 16) by lia. rewrite Z_mod_plus_full. exact A16.
      + apply PMKB.mod16_8'. replace (sp - 32 - 14336) with (sp + (-898) * 16) by lia. rewrite Z_mod_plus_full. exact A16. }
  { intros kq Hk. specialize (FRM kq Hk). lia. }
  { intros f Hf. specialize (FRS f Hf). lia. }
  { exact FOK. }
  { rewrite L5K.rl10. rewrite (KS1 10%nat) by inl. exact A10. }
  { exact PA1. }
  { exact LEN. }
  intros fx2 R2 M2 model2 LK2 Aw2 RP2 PA2 HP2 MRT2 INCLK2 INCA2 AM2 HH2.
  change (PMSPA.pm_scr 1) with 14336 in HP2. unfold PMSPA.o_tb, PMSPA.o_vec in HP2. fold op in HP2.
  set (W4 := [(op + 8, 8); (op + 336, 24); (op + 360, 24)]) in *.
  assert (WC4 : forall rr a, In rr W4 -> L5.in_rng rr a -> op + 8 <= a < op + 384).
  { intros rr a Hin Hr. unfold W4 in Hin. unfold L5.in_rng in Hr. destruct Hin as [<-|[<-|[<-|[]]]]; cbn [fst snd] in Hr; lia. }
  assert (EK12 : L5SAR.ek L ar LBr FF sp 34816 W4 M1 M2).
  { apply (L5SAR.ek_callee L ar LBr [] FF [] sp 34816 (sp - 32) 14336 W4 W4 M1 M2 HP2); [lia|lia|]. intros a _ O. exact O. }
  assert (DK12 : L5SAR.dk L ar LBr FF sp 34816 M1 M2) by (apply (L5SAR.dk_callee L ar LBr [] FF [] sp 34816 (sp - 32) 14336 W4 M1 M2 HP2); lia).
  assert (EK01x : L5SAR.ek L ar LBr FF sp 34816 W4 M M1).
  { apply (L5SAR.ek_W L ar LBr FF sp 34816 W4 [] M M1); [| intros a _ r0 []]. exact (ek_drop L ar (PM.parser_own s) LBr FF sp 34816 [] M M1 EK01). }
  assert (EK02 : L5SAR.ek L ar LBr FF sp 34816 W4 M M2) by exact (L5SAR.ek_trans L ar LBr FF sp 34816 W4 M M1 M2 EK01x EK12).
  assert (WAPP4 : PMKB.wapp W4).
  { unfold W4. pose proof FSAPP as (FA0 & FA1 & FA2). unfold BIGSHADOW_LO, BIGSHADOW_HI in *.
    repeat apply PMKB.wapp_cons; [..| apply PMKB.wapp_nil]; cbn [fst snd]; unfold BIGSHADOW_LO, BIGSHADOW_HI; destruct FA1 as [Y|Y]; clear - Y F1 F2 Eop; lia. }
  pose proof FRB as FRBx.
  assert (BRBx : forall b, In b LBr -> 0 <= fst b /\ fst b + snd b <= 2 ^ 47) by (intros b Hb; apply BRB; unfold LB; apply in_or_app; right; exact Hb).
  assert (OB4 : forall q m, In (q, m) LBr -> PMKB.blk_out W4 q m).
  { intros q m Hq. unfold PMKB.blk_out. intros i Hi rr Hin Hr. pose proof (WC4 rr i Hin Hr) as Y.
    destruct (PMBSKJ.blk_obj_apart L ar C HI HIok LB FF LK cr Aw M _ q m op 384 HH (in_or_app _ _ _ (or_intror Hq)) AOP) as [Z|Z]; clear - Hi Y Z; lia. }
  assert (OUT4 : forall a n, fb + 32 <= a -> a + n <= fb + 2040 -> (a + n <= op + 8 \/ op + 384 <= a) -> forall i, a <= i < a + n -> L5.outside W4 i).
  { intros a n X1 X2 X3 i Hi rr Hin Hr. pose proof (WC4 rr i Hin Hr) as Y. clear - X3 Hi Y. lia. }
  assert (ASTK2 : L5CA.astk ar M2 sp 34816) by (apply (PMKB.astk_after_ahpres L ar LBr FF M1 M2 sp 34816 (sp - 32) 14336 W4 ASTK1 HP2); lia).
  assert (IA2 : PM.iss_at RSEGS PeCLayoutB.CADDR_B PMSPA.accA M2 ois str sm).
  { apply (PMKB.iss_keepA RSEGS PeCLayoutB.CADDR_B L ar LBr FF sp 34816 W4 M M2 EK02 WAPP4 FRBx BRBx _ _ _
             (AOF ois 272 ltac:(clear - Eois; lia) ltac:(clear - Eois; lia))); [exact INCSr| apply OUT4; clear - Eois Eop; lia| | exact IA].
    intros c0 n0 p0 E0. apply OB4. apply INCSr. rewrite E0. cbn. left. reflexivity. }
  assert (EA2 : PECA.enc_atA RSEGS PeCLayoutB.EADDR_B L ar M2 ov fb en).
  { apply (PECFA.enc_keepA RSEGS PeCLayoutB.EADDR_B L ar LBr FF sp 34816 W4 M M2 EK02 WAPP4 FRBx BRBx ov fb en (AOF ov 56 ltac:(clear - Eov; lia) ltac:(clear - Eov; lia)));
      [apply OUT4; clear - Eov Eop; lia| exact INE| | exact EA].
    intros Hp. apply OB4. apply INE. unfold PEC.enc_own. replace (PEC.en_k en =? 0) with false by (symmetry; apply Z.eqb_neq; clear - Hp; lia). left. reflexivity. }
  assert (SKA2 : PESKA.sink_atA RSEGS L ar P M2 osk k).
  { apply (PECFA.sink_keepA RSEGS L ar LBr FF sp 34816 W4 M M2 EK02 WAPP4 FRBx BRBx P osk k (AOF osk 24 ltac:(clear - Eosk; lia) ltac:(clear - Eosk; lia)));
      [apply OUT4; clear - Eosk Eop; lia| exact INK| | exact SKA].
    intros Hp. apply OB4. apply INK. unfold PESK.sink_own. replace (PESK.sk_c k =? 0) with false by (symmetry; apply Z.eqb_neq; clear - Hp; lia). left. reflexivity. }
  assert (ACC2 : PMSPA.accA M2 op 392) by exact (PMKB.acc_keepA' L ar LBr FF sp 34816 W4 M M2 EK02 WAPP4 FRBx op 392 (AOF op 392 ltac:(clear - Eop; lia) ltac:(clear - Eop; lia)) ACC).
  assert (CONT2 : PEC.content_ok RSEGS PeCLayoutB.CADDR_B M2 fb p (PM.p_src s) str sm).
  {
    destruct CONT as (SZ & BS & PS0' & _ & ST2). pose proof IA as (_ & _ & _ & _ & _ & _ & _ & _ & _ & VS & _).
    split; [exact SZ|]. split; [| split; [exact PS0'| split; [| exact ST2]]].
    2:{ rewrite REM0. unfold UbjRef.slice. intros i Hi. exfalso. rewrite length_firstn, Z2Nat.inj_0 in Hi. clear - Hi. Lia.lia. }
    unfold PMSP.o_is in BS |- *. cbn [pa_off_is PeCLayoutB.CADDR_B] in BS |- *. rewrite Eois in VS.
    assert (LENp : Z.of_nat (length p) = PM.vs_size str) by (rewrite SZ; unfold blen; reflexivity).
    destruct str as [ns|cs ns qs]; cbn [PM.vs_data PM.vs_size] in BS, VS, LENp |- *.
    - destruct VS as (_ & _ & Hn & _).
      apply (L5C.bytes_at_agree RSEGS M M2); [| lia| lia| exact BS].
      eapply L5C.agree_on_sub; [exact (proj1 (PMKB.agA_obj L ar LBr FF sp 34816 W4 M M2 EK02 WAPP4 FRBx (fb + 96 + 80) 24 (AOF (fb + 96 + 80) 24 ltac:(clear; lia) ltac:(clear; lia))
                                                 ltac:(apply OUT4; clear - Eop; lia)))| lia| lia].
    - destruct VS as (_ & _ & _ & _ & _ & Hnc & Hc & _).
      assert (HinX : In (qs, cs) LBr) by (apply INCSr; cbn; left; reflexivity). destruct (BRBx _ HinX) as (Q0 & Q1). cbn [fst snd] in Q0, Q1.
      apply (L5C.bytes_at_agree RSEGS M M2); [| lia| lia| exact BS].
      eapply L5C.agree_on_sub; [exact (proj1 (PMKB.agA_blk L ar LBr FF sp 34816 W4 M M2 EK02 WAPP4 BRBx qs cs HinX (OB4 qs cs HinX)))| lia| lia]. }
  assert (VREF2 : L5.u64_at RSEGS M2 (op + 384) ov).
  { apply (PMKB.u64_keepA RSEGS L ar LBr FF sp 34816 W4 M M2 EK02 WAPP4 FRBx (op + 384) _ (AOF (op + 384) 8 ltac:(clear - Eop; lia) ltac:(clear - Eop; lia))); [| exact VREF].
    apply OUT4; clear - Eop; lia. }
  assert (EC2 : PMSPA.ec_at RSEGS M2 oec 0 cat).
  { apply (PMKB.ec_keepA RSEGS L ar LBr FF sp 34816 W4 M M2 EK02 WAPP4 FRBx _ 0 cat (AOF oec 16 ltac:(clear - Eoec; lia) ltac:(clear - Eoec; lia))); [| exact EC].
    apply OUT4; clear - Eoec Eop; lia. }
  assert (FB0 : 6930432 <= fb) by (clear - FSI F1; lia).
  assert (BASE2 : PMSTA.base_okA RSEGS PeCLayoutB.CADDR_B M2).
  { apply (PMBSKJ.base_keep L ar C LY LBr FF sp 34816 W4 M M2 EK02); [| exact BASE].
    intros a Ha rr Hin Hr. pose proof (WC4 rr a Hin Hr) as Y. clear - Ha Y FB0 Eop; lia. }
  assert (ERR2 : PESTA.err_okA RSEGS PeCLayoutB.CADDR_B PeCLayoutB.CAADDR_B PeCLayoutB.EADDR_B M2 e).
  { apply (PECFA.err_okA_keep RSEGS PeCLayoutB.CADDR_B PeCLayoutB.CAADDR_B PeCLayoutB.EADDR_B L ar LBr FF sp 34816 W4 M M2 EK02 e PECSB.addrs_wf_B); [| exact ERR].
    intros a D. pose proof (PMBSKJ.dep_img a D) as DI. rewrite (L5A.aly_img_lo L C LYa), (L5A.aly_img_hi L C LYa). split; [clear - DI; lia|].
    split; [exact (PMB.ly_static L C LY a (PnStatics.PNST.dep_of_j _ _ a D))|]. intros rr Hin Hr. pose proof (WC4 rr a Hin Hr) as Y. clear - DI Y FB0 Eop; lia. }

  assert (FRAME12 : forall a, sp - 32 <= a < sp -> M2 (Z_to_bv 64 a) = M1 (Z_to_bv 64 a)).
  { intros a Ha. destruct HP2 as (P2 & _ & _). apply P2. split; [lia|]. split.
    - unfold aclient, aclient_g. right; left. split; [lia| intros X; lia].
    - intros rr Hin Hr. pose proof (WC4 rr a Hin Hr) as Y. clear - Ha Y F2 FSCEIL SLO Eop; lia. }
  pose proof (L5SAR.vis_pack L ar C HI LYa HIok _ FF LK2 cr Aw2 M2 model2 HH2) as (_ & VIS2s & _).
  set (H2 := ahid Aw2 model2) in *. set (MV2 := mrestrict H2 M2) in *.
  assert (SV2 : forall kq v, 1 <= kq <= 4 -> L5.u64_at RSEGS M1v (sp - 8 * kq) v -> L5.u64_at RSEGS MV2 (sp - 8 * kq) v).
  { intros kq v Hk X. apply (proj2 (L5A.u64_at_vis H2 M2 (sp - 8 * kq) v (VIS2s (sp - 8 * kq) 8 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))).
    apply (L5C.u64_at_agree RSEGS M1 M2); [intros i Hi; apply FRAME12; lia| lia| lia| exact (SV1 kq v Hk X)]. }
  pose proof (PMBSKJ.stk_vis L ar C HI LY HIok _ FF LK2 cr Aw2 M2 model2 sp 34816 32 HH2 ASTK2 ltac:(lia)) as (_ & _ & W3).
  pose proof (L5SAR.aobj_facts L ar C HI LYa HIok _ FF LK2 cr Aw2 M2 model2 op 392 sp 34816 HH2 (PMKB.aobj_of_aobjA FF op 392 (AOF op 392 ltac:(clear - Eop; lia) ltac:(clear - Eop; lia)) ltac:(clear - Eop Fal; lia)) ltac:(lia) ltac:(reflexivity))
    as ((O1 & O2 & O3 & O4 & O5) & OBIG & ODEF & OVIS & OSHV & OCL & OSHCL).
  change (392 / 8) with 49 in OSHV. unfold SB in OSHV.
  assert (VR2v : L5.u64_at RSEGS MV2 (op + 384) ov).
  { apply (proj2 (L5A.u64_at_vis H2 M2 (op + 384) ov ltac:(eapply L5A.avis_sub; [exact OVIS|lia|lia]) ltac:(lia) ltac:(lia))). exact VREF2. }
  assert (Z384 : L5KA.zeros_at MV2 ((op / 8) + 2147450928) 1).
  { assert (ACC2' : PMSPA.accA M2 (op + 384) 8) by (intros x Hx; apply ACC2; clear - Hx; lia).
    assert (SX : HeapIfaceA.S (op + 391) = op / 8 + 2147450928).
    { unfold HeapIfaceA.S, HeapIfaceA.SB. rewrite <- O5 at 1. replace (op / 8 * 8 + 391) with (7 + (op / 8 + 48) * 8) by lia. rewrite Z.div_add by lia. change (7 / 8) with 0. lia. }
    assert (M7 : (op + 391) mod 8 = 7).
    { rewrite <- O5 at 1. replace (op / 8 * 8 + 391) with (7 + (op / 8 + 48) * 8) by lia. rewrite Z_mod_plus_full. reflexivity. }
    apply (proj2 (L5A.zeros_at_vis H2 M2 (op / 8 + 2147450928) 1 ltac:(eapply L5A.avis_sub; [exact OSHV| lia| lia]))).
    intros i Hi. assert (i = 0) by lia. subst i. rewrite Z.add_0_r.
    destruct (ACC2' (op + 391) ltac:(lia)) as [B|(v & B & Bv1 & Bv2)]; rewrite SX in B; [exact B|]. exfalso. clear - M7 Bv1 Bv2. lia. }
  pose proof (PMBRRP.brrB_conc fx2 R2 MV2 (fun j => match j with 2%nat => sp | 36%nat => bv_unsigned (getr R (reg 18)) | 37%nat => r
                | 38%nat => bv_unsigned (getr R (reg 9)) | 39%nat => bv_unsigned (getr R (reg 8)) | 40%nat => op | 41%nat => oec | 43%nat => ov | _ => 0 end)) as PC.
  cbn beta iota in PC.
  assert (R22 : getr R2 (reg 2) = Z_to_bv 64 (sp - 32)) by (rewrite (L5SAR.cs_of_preserved R1 R2 2 RP2) by inl; exact A2).
  assert (R28 : getr R2 (reg 8) = Z_to_bv 64 oec) by (rewrite (L5SAR.cs_of_preserved R1 R2 8 RP2) by inl; rewrite A8; exact A11).
  assert (R29 : getr R2 (reg 9) = Z_to_bv 64 op) by (rewrite (L5SAR.cs_of_preserved R1 R2 9 RP2) by inl; rewrite A9; exact A10).
  assert (R218 : getr R2 (reg 18) = Z_to_bv 64 2147450880) by (rewrite (L5SAR.cs_of_preserved R1 R2 18 RP2) by inl; exact A18).
  rewrite Rra, L5.unsigned_lit in C8 by lia.
  assert (D8 : L5.u64_at RSEGS MV2 (sp - 8) r) by (replace (sp - 8) with (sp - 8 * 1) by lia; apply SV2; [lia| exact C8]).
  assert (D16 : L5.u64_at RSEGS MV2 (sp - 16) (bv_unsigned (getr R (reg 8)))) by (replace (sp - 16) with (sp - 8 * 2) by lia; apply SV2; [lia| exact C16]).
  assert (D24 : L5.u64_at RSEGS MV2 (sp - 24) (bv_unsigned (getr R (reg 9)))) by (replace (sp - 24) with (sp - 8 * 3) by lia; apply SV2; [lia| exact C24]).
  assert (D32 : L5.u64_at RSEGS MV2 (sp - 32) (bv_unsigned (getr R (reg 18)))) by (replace (sp - 32) with (sp - 8 * 4) by lia; apply SV2; [lia| exact C32]).
  assert (OV8 : ov mod 8 = 0) by (rewrite Eov; replace (fb + 496) with (fb + 8 * 62) by (clear; lia); clear - Hfb Fal; unfold PECA.frame_ok5 in *; lia).
  L5SAR.feed PC ltac:(first [assumption | unfold PMBRRP.aligned; lia | lia]).
  destruct PC as (fx3 & R3 & M3v & MG3 & FRW3 & _ & MS3 & KS3 & B1 & B2 & B8 & B9 & B10 & B11 & B12 & B18).
  assert (E3 : M3v = MV2) by (apply functional_extensionality; exact FRW3). subst M3v.
  apply (L5SAR.apiece_ro L ar C HI LYa HIok _ FF LK2 cr Aw2 M2 model2 fx2 fx3 R2 0xaa0d8 R3 0xb5e2c MV2 K HH2 AM2 MS3 MG3 (fun a Ha => eq_refl)).
  intros M3 model3 HH3 AM3 MRT3 HID3 VIS3 MGM3 FR3.
  assert (E3 : M3 = M2) by (apply L5SAR.mem_eq_of_agree; exact FR3). subst M3.

  assert (CH : forall kq, In kq PMBRRP.KS_brrA -> In kq PMBRRP.KS_brrB -> In kq L5SAR.cs_all -> getr R3 (reg kq) = getr R (reg kq)).
  { intros kq K1 K2 K3. rewrite (KS3 kq K2). rewrite (L5SAR.cs_of_preserved R1 R2 kq RP2 K3). apply KS1. exact K1. }
  unfold PECSB.parse_spec, PECSPA.parse_spec in PARSE. cbn [pa_parse PeCLayoutB.CADDR_B] in PARSE.
  assert (OWNr : PEC.owned (PMSPA.pst_reset s) en k ++ LBX = PM.parser_own s ++ LBr) by (unfold LBr, PEC.owned; rewrite own_reset, <- !app_assoc; reflexivity).
  apply (PARSE PMODE fx3 R3 M2 model3 K LBX FF LK2 Aw2 cr sp r fb cat p (PMSPA.pst_reset s) str sm en k e ltac:(rewrite OWNr; exact HH3) AM3 K0).
  - split; [rewrite L5K.rl1; exact B1|]. split; [exact RAok|]. split; [rewrite L5K.rl2; exact B2|].
    split; [rewrite L5K.rl3; rewrite (CH 3%nat) by inl; exact Rgp|]. split; [rewrite L5K.rl4; rewrite (CH 4%nat) by inl; exact Rtp|].
    change (PMSPA.pm_scr 10) with 32768. change (32768 / 8) with 4096.
    split; [pose proof (L5SAR.astk_sub ar M2 M2 sp 34816 0 32768 ASTK2 (fun _ X => X) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(replace (sp - 0) with sp by lia; exact A16)) as X;
            replace (sp - 0) with sp in X by lia; exact X|].
    replace (sp - 32768) with (sp - 0 - 32768) by lia.
    apply (PMKB.stksh_keepA L ar LBr FF sp 34816 W4 M M2 EK02 WAPP4 (sp - 0 - 32768) 4096); [lia|lia|lia| | lia|].
    + apply PMKB.mod16_8'. replace (sp - 0 - 32768) with (sp + (-2048) * 16) by lia. rewrite Z_mod_plus_full. exact A16.
    + apply (PMKB.shadow_zero_sub M (sp - 34816) 4352); [| | lia| lia| lia| exact STKSH].
      * apply PMKB.mod16_8'. replace (sp - 34816) with (sp + (-2176) * 16) by lia. rewrite Z_mod_plus_full. exact A16.
      * apply PMKB.mod16_8'. replace (sp - 0 - 32768) with (sp + (-2048) * 16) by lia. rewrite Z_mod_plus_full. exact A16.
  - pose proof (HAJ.aior_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH3) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & NDF3 & _).
    exact (ffroomA_sub 11 10 FF LK LK2 FRM INCLK2 NDF3 ltac:(lia)).
  - exact FRS.
  - exact FOK.
  - exact SP32.
  - unfold PECSPA.args3. rewrite L5K.rl10, L5K.rl11, L5K.rl12. split; [exact B10|]. split; [exact B11| exact B12].
  -
    split; [exact PA2|]. split; [exact IA2|]. split; [exact EA2|]. split; [exact VREF2|]. split; [exact SKA2|]. split; [exact BASE2|]. split; [exact ERR2|].
    split; [apply tb_ok_reset; exact TBOK|]. split; [rewrite src_reset; exact CONT2|].
    split.
    { unfold PEC.clink. cbn [s_more s_done s_depth s_stk s_pos s_estk s_edepth s_lo s_hi s_bad UbjRef.init PEC.b2z PEC.stk_conv rev map app PEC.ps_conv ps_mode ps_len ps_type ps_idx PEC.mode_code].
      clear - POS0 EN0 ED0 KZ0. destruct s as [mo dn dp srcx tb tg vb vk stk]; cbn [PMSPA.pst_reset PM.p_more PM.p_done PM.p_depth PM.p_stk PM.p_src PM.ps_root] in *.
      split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [intros _ _; exact POS0|].
      split; [rewrite EN0; reflexivity|]. split; [exact ED0|]. split; [rewrite KZ0; clear; lia| reflexivity]. }
    split; [exact EC2|]. split; [intros X; discriminate|]. exact ACC2.
  - exact INCS.
  - exact POK.
  - exact HB.
  - exact CRED.
  - intros fx4 R4 M4 model4 LK4 Aw4 nn s' sm' en' k' e' cr' RP4 HALT PPOST STEP EE4 HP4 CK4 MRT4 INCLK4 INCA4 AM4 HH4.
    change (PMSPA.pm_scr 10) with 32768 in HP4. rewrite src_reset in STEP.
    apply (KONT fx4 R4 M4 model4 LK4 Aw4 nn s' sm' en' k' e' cr'); [| exact HALT| exact PPOST| exact STEP| exact EE4| | exact CK4| | | | exact AM4| exact HH4].
    + apply (L5SAR.regs_preserved_trans R R3 R4); [|exact RP4]. apply L5SAR.preserved_by_index. intros kq Hk. unfold L5SAR.cs_all in Hk.
      destruct Hk as [<-|Hk]; [rewrite B2, Rsp; reflexivity|].
      repeat (destruct Hk as [<-|Hk];
        [ first [ (rewrite B8; apply Z_to_bv_bv_unsigned) | (rewrite B9; apply Z_to_bv_bv_unsigned) | (rewrite B18; apply Z_to_bv_bv_unsigned)
                | (apply CH; [inl| inl| unfold L5SAR.cs_all; cbn; tauto]) ] |]).
      destruct Hk.
    + set (WR4 := PEC.W_crun PeCLayoutB.CADDR_B PeCLayoutB.EADDR_B fb) in *.
      assert (SUB : forall a, L5.outside WR4 a -> L5.outside W4 a).
      { intros a O rr Hin. apply O. unfold WR4, PEC.W_crun, PMSP.W_run, PMSP.W_srcf, PMSP.o_tb, PMSP.o_vec, PMSP.o_p. change (pa_off_p PeCLayoutB.CADDR_B) with 592. fold op. cbn [app]. unfold W4 in Hin.
        destruct Hin as [<-|[<-|[<-|[]]]]; [left; reflexivity| do 4 right; left; reflexivity| do 5 right; left; reflexivity]. }
      assert (HP2x : L5CA.ahpres L ar ((PEC.enc_own en ++ PESK.sink_own k) ++ LBX) FF (sp - 32) 14336 W4 M1 M2) by (rewrite <- app_assoc; exact HP2).
      assert (EK02X : L5SAR.ek L ar LBX FF sp 34816 W4 M M2).
      { apply (L5SAR.ek_trans L ar LBX FF sp 34816 W4 M M1 M2).
        - apply (L5SAR.ek_W L ar LBX FF sp 34816 W4 [] M M1); [| intros a _ r0 []].
          exact (ek_drop L ar (PESK.sink_own k) LBX FF sp 34816 [] M M1 (ek_drop L ar (PEC.enc_own en) _ FF sp 34816 [] M M1 (ek_drop L ar (PM.parser_own s) LBr FF sp 34816 [] M M1 EK01))).
        - apply (L5SAR.ek_callee L ar LBX (PEC.enc_own en ++ PESK.sink_own k) FF [] sp 34816 (sp - 32) 14336 W4 W4 M1 M2 HP2x); [lia|lia|]. intros a _ O. exact O. }
      assert (EK24 : L5SAR.ek L ar LBX FF sp 34816 WR4 M2 M4).
      { apply (L5SAR.ek_callee L ar LBX [] FF [] sp 34816 sp 32768 WR4 WR4 M2 M4 HP4); [lia|lia|]. intros a _ O. exact O. }
      apply (L5SAR.ahpres_of L ar LBX FF sp 34816 WR4 M M4).
      * apply (L5SAR.ek_trans L ar LBX FF sp 34816 WR4 M M2 M4); [apply (L5SAR.ek_W L ar LBX FF sp 34816 WR4 W4 M M2 EK02X SUB)| exact EK24].
      * pose proof (PMKB.astk_after_ahpres L ar LBX FF M2 M4 sp 34816 sp 32768 WR4 ASTK2 HP4 ltac:(lia) ltac:(lia) ltac:(lia) TOP) as (_ & _ & _ & _ & D4 & _). exact D4.
      * apply (L5SAR.dk_trans L ar LBX FF sp 34816 M M1 M4); [apply L5SAR.dk_grows; exact MGM1|].
        apply (L5SAR.dk_trans L ar LBX FF sp 34816 M1 M2 M4); [exact (L5SAR.dk_callee L ar LBX (PEC.enc_own en ++ PESK.sink_own k) FF [] sp 34816 (sp - 32) 14336 W4 M1 M2 HP2x ltac:(lia) ltac:(lia))|].
        apply (L5SAR.dk_callee L ar LBX [] FF [] sp 34816 sp 32768 WR4 M2 M4 HP4); lia.
    + eapply L5LZ.model_rt_trans; [exact MRT1|]. eapply L5LZ.model_rt_trans; [exact MRT2|]. eapply L5LZ.model_rt_trans; [exact MRT3| exact MRT4].
    + intros x Hx. apply INCLK2. apply INCLK4. exact Hx.
    + intros x Hx. apply INCA4. apply INCA2. exact Hx.
Qed.

End WithHeap.
End SCFG_1.
End PEBCRR.
