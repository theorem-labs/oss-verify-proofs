(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.jsoncons.fuzz_json_encoder.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare ShapeAlg SpinAlg
  AxSymExec3 AxSymExec3B AxSymExec3Sound AxSymRun3 AsanPlanCore AsanPlan AsanPlanSound AsanPlanSoundSums LibSym SegRun SegPlan SegPlanAuto
  HeapIface L5Defs L5Core. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5 Require Import Pm6PlanKit_u5 PmLibDefs_u5 PmLibSpecs_u5 PmLayout_u5 PmEncSpecs_u5 PmEncSpecs2_u5.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.CutCert Require Import CutCert CutOps CutHeap CutAuto CutLib. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.CutCert Require Import Pm6CutKit_u5. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.CutCert Require Import CutHeap2 CutL5 CutAutoX CutHeap2V.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.PmGrow Require Import GrowKit_u5.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.PmParse Require Import ParseBridges_u5 ParseBridges2_u5.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.PmEnc Require Import EncSums_u5. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.PmEnc Require Import EncSums2. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.PmEnc Require Import EncAppendK_u5 EncKit_u5 EncKit2_u5 EncKit3_u5 EncTail2_u5.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.PmFloatX Require Import VbmKitX_u5 VbhKitX_u5 VbhObjAposX_u5 VbhObjAzeroX_u5 VbhObjBsegX_u5 VbhObjCsegX_u5.

Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Module VBH_OAU.
Import PML. Import PMES.

Ltac csv := vm_compute; repeat first [left; reflexivity | right].
Ltac inw := cbn [In]; repeat first [left; reflexivity | right].

Section Head.
Context {SCFG_P : ScfgP}.
Variable L : heap_layout.
Variable HI : heap_iface.
Hypothesis HIok : heap_iface_ok L SCFG HI.
Hypothesis LAY : PmLayout.pm0_layout L.
Hypothesis FPM : forall (fx fx' : FPState) R pc M R' pc' M',
  msteps GK.RSEGS (@mkst fx R (Z_to_bv 64 pc) M (seg_rom GK.RSEGS)) (@mkst fx' R' (Z_to_bv 64 pc') M' (seg_rom GK.RSEGS)) -> PML.fp_ok fx -> PML.fp_ok fx'.
Hypothesis APPENDX : str_append_x_specU L HI.
Hypothesis NEWLINE2 : new_line2_specU L HI.

Lemma hpres_wdrop : forall LB sp scr W W' (M M' : mem),
  (forall bb, In bb LB -> fst bb + snd bb <= hl_ceil L) -> hl_img_hi L <= hl_ceil L -> hl_ceil L <= sp - scr ->
  (forall a, L5.outside W' a -> ~ (sp - scr <= a < sp) -> L5.outside W a) ->
  L5C.hpres L LB sp scr W M M' -> L5C.hpres L LB sp scr W' M M'.
Proof.
  intros LB sp scr W W' M M' HB HIM HC HW (HP1 & HP2 & HP3).
  split; [|split; [exact HP2 | exact HP3]].
  intros a (K1 & K2 & K3 & K4). apply HP1. split; [exact K1|]. split; [exact K2|]. split; [exact K3|].
  apply HW; [exact K4|]. intros Hin.
  destruct K2 as [(bb & Hbb & Hr)|[[C1 C2]|[C1 C2]]]; [pose proof (HB bb Hbb); lia | lia | lia].
Qed.

Lemma agree_stk : forall LB sp' scr W (M0 M M' : mem) a n,
  L5C.hpres L LB sp' scr W M M' -> L5C.stk (hl_sptop L) M0 sp' scr -> 0 <= scr -> sp' <= a -> a + n <= 2 ^ 64 ->
  (forall x, a <= x < a + n -> L5.outside W x) -> L5C.agree_on M M' a n.
Proof.
  intros LB sp' scr W M0 M M' a n HP HS H0 Ha Hn HW i Hi. pose proof (PmLayout.ly_errno L LAY) as LER.
  apply (L5C.hpres_kept _ _ _ _ _ _ _ i HP). apply (L5C.kept_stack_stk L LB M0 sp' scr W i HS H0); [lia | rewrite LER; lia | apply HW; exact Hi].
Qed.

Lemma agree_blk : forall LB sp' scr W (M M' : mem) A n,
  L5C.hpres L LB sp' scr W M M' -> In (A, n) LB -> block_range L A n -> hl_sptop L <= 2 ^ 47 ->
  (forall x, A <= x < A + n -> L5.outside W x) -> L5C.agree_on M M' A n.
Proof.
  intros LB sp' scr W M M' A n HP Hin (B1 & B2 & B3 & B4 & B5) HT HW i Hi.
  pose proof (PmLayout.ly_errno L LAY) as LER. pose proof (PmLayout.ly_img_lo L LAY) as ILO. pose proof (PmLayout.ly_img_hi L LAY) as IHI.
  apply (L5C.hpres_kept _ _ _ _ _ _ _ i HP). apply (L5C.kept_block L LB sp' scr W A n i Hin Hi); [lia | lia | | apply HW; exact Hi].
  rewrite LER. rewrite ILO, IHI in B2. lia.
Qed.

Lemma defined_hp : forall LB sp' scr W (M M' : mem) a n,
  L5C.hpres L LB sp' scr W M M' -> 0 <= a -> a + n <= 2 ^ 64 -> hl_ceil L <= a -> sp' <= a -> hl_errno L + 4 <= hl_ceil L ->
  L5.defined M a n -> L5.defined M' a n.
Proof.
  intros LB sp' scr W M M' a n HP H0 H1 Hc Hs He HD i Hi.
  apply (L5C.hpres_cdef _ _ _ _ _ _ _ (a + i) HP); [lia | right; left; lia | unfold in_errno; lia | apply HD; exact Hi].
Qed.

Lemma stk_in : forall (M0 M : mem) sp S k scr, L5C.stk (hl_sptop L) M0 sp S -> PMES2.HEAD_SCR <= S ->
  L5.defined M (sp - PMES2.HEAD_SCR) PMES2.HEAD_SCR -> 0 <= k -> k mod 16 = 0 -> k + scr <= PMES2.HEAD_SCR -> 0 <= scr ->
  L5C.stk (hl_sptop L) M (sp - k) scr.
Proof.
  intros M0 M sp S k scr (A1 & A2 & A3 & A4 & A5) HS HD Hk Hk16 Hks Hs.
  split; [rewrite Zminus_mod, A1, Hk16; reflexivity|]. split; [lia|]. split; [lia|]. split; [exact A4|].
  intros i Hi. replace (sp - k - scr + i) with (sp - PMES2.HEAD_SCR + (PMES2.HEAD_SCR - k - scr + i)) by lia. apply HD. lia.
Qed.

Lemma frame_agree : forall arr (M M' : mem) spf r s0 s1 s2 s3,
  L5C.agree_on M M' (spf + PMES2.LOC arr) (64 - PMES2.LOC arr) -> 0 <= spf -> spf + 64 <= 2 ^ 64 ->
  PMES2.frame_at arr M spf r s0 s1 s2 s3 -> PMES2.frame_at arr M' spf r s0 s1 s2 s3.
Proof.
  intros arr M M' spf r s0 s1 s2 s3 AG H0 H1 (F1 & F2 & F3 & F4 & F5).
  assert (LB : 24 <= PMES2.LOC arr <= 32) by (unfold PMES2.LOC; destruct arr; lia).
  unfold PMES2.frame_at. split; [|split; [|split; [|split]]];
    [ .. | intros HA; assert (LA : PMES2.LOC arr = 24) by (unfold PMES2.LOC; rewrite HA; reflexivity); specialize (F5 HA) ];
    (apply (EK.u64_agree M M'); [apply (EK.agree_sub M M' _ _ _ _ AG); lia | lia | lia | assumption]).
Qed.

Lemma kept_cs : forall arr (x : bv 5), In (bv_unsigned x) (PMES2.KEPT arr) -> In (bv_unsigned x) callee_saved_idx.
Proof. intros arr x Hx. unfold PMES2.KEPT, callee_saved_idx in *. destruct arr; cbn [In] in *; tauto. Qed.

Lemma nl_reads_of : forall (M : mem) V S2 dI dD, PMES2.enc_objx M V S2 dI dD -> 0 <= dI <= MAX_DEPTH -> nl_reads M V S2 dI.
Proof.
  intros M V S2 dI dD H Hd.
  destruct H as (_ & H2 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & N1 & N2 & N3 & N4 & _ & _ & _ & IC & _ & _ & _ & IN & CO & _).
  exact (conj H2 (conj N1 (conj N2 (conj N3 (conj N4 (conj IC (conj IN (conj Hd CO)))))))).
Qed.

Lemma enc_objx_agree_all : forall (M M' : mem) V S2 dI dD, 0 <= V -> V + ENC_SIZE <= 2 ^ 64 ->
  L5C.agree_on M M' V ENC_SIZE -> PMES2.enc_objx M V S2 dI dD -> PMES2.enc_objx M' V S2 dI dD.
Proof.
  intros M M' V S2 dI dD H0 H1 AG H.
  assert (DC : L5.defined M' (V + O_COLUMN) 8).
  { apply (L5C.defined_agree M M'); [apply (EK.agree_sub M M' V ENC_SIZE); [exact AG | unfold O_COLUMN; lia | unfold O_COLUMN, ENC_SIZE; lia] |].
    destruct H as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & C25 & _). exact C25. }
  apply (EK3.enc_objx_agree M M' V S2 dI dD H0 H1);
    [apply (EK.agree_sub M M' V ENC_SIZE); [exact AG | lia | unfold O_STACK, ENC_SIZE; lia]
    | apply (EK.agree_sub M M' V ENC_SIZE); [exact AG | unfold O_INDENT; lia | unfold O_INDENT, ENC_SIZE; lia]
    | apply (EK.agree_sub M M' V ENC_SIZE); [exact AG | unfold O_COLON; lia | unfold O_COLON, ENC_SIZE; lia]
    | exact DC | exact H].
Qed.

Lemma lits_hp : forall LBk sp scr W (M M' : mem), L5C.hpres L LBk sp scr W M M' ->
  (forall w a, In w W -> L5.in_rng w a -> ~ (LIT_LO <= a < LIT_HI)) -> lits_ok M -> lits_ok M'.
Proof.
  intros LBk sp scr W M M' HP HW HL. apply (lits_ok_agree M M'); [|exact HL]. intros a Ha.
  apply (L5C.hpres_kept _ _ _ _ _ _ _ a HP).
  pose proof (PmLayout.ly_img_lo L LAY) as ILO. pose proof (PmLayout.ly_img_hi L LAY) as IHI. pose proof (PmLayout.ly_errno L LAY) as LE. unfold LIT_LO, LIT_HI in *.
  apply L5C.kept_static; [rewrite ILO, IHI; lia | intros X; pose proof (PmLayout.ly_static L LAY a X); lia | rewrite ILO; lia | rewrite IHI; lia | rewrite LE; lia|].
  intros w Hw Hin. exact (HW w a Hw Hin Ha).
Qed.

Lemma grown_facts : forall LBo st cr (M' : mem) o rep s' LB' cr' LBk rep',
  List.NoDup (map fst (LBo ++ srep_blocks rep ++ st)) ->
  x_grownU L (LBo ++ srep_blocks rep ++ st) cr M' o rep s' LB' cr' LBk rep' ->
  sink_at M' o rep' /\ srep_chars rep' = s' /\ Permutation LB' (LBo ++ srep_blocks rep' ++ st) /\ LBk = LBo ++ st.
Proof.
  intros LBo st cr M' o rep s' LB' cr' LBk rep' ND [(F & -> & HS & -> & _ & ->)|(NF & p' & G)].
  - rewrite (VBHK.lb_drop_mid LBo rep st ND). split; [exact HS|].
    split; [destruct rep; reflexivity|]. split; [destruct rep; cbn [same_rep srep_blocks]; apply Permutation_refl | reflexivity].
  - cbv zeta in G. destruct G as (-> & HS & _ & -> & _ & ->). rewrite (VBHK.lb_drop_mid LBo rep st ND).
    split; [exact HS|]. split; [reflexivity|]. split; [cbn [srep_blocks app]; apply EK.perm_lbv_in | reflexivity].
Qed.

Lemma kept_oc : forall (x : bv 5), In (bv_unsigned x) (PMES2.KEPT false) -> In (bv_unsigned x) [1; 2; 3; 4; 8; 9; 10; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27].
Proof. intros x Hx. unfold PMES2.KEPT in Hx. cbn [In] in *. tauto. Qed.

Theorem head_ok : PMES2.head_obj_inarr_spec L HI.
Proof.
  unfold PMES2.head_obj_inarr_spec, PMES2.head_spec.
  intros LBo cr sp r V S2 kx bx g. destruct g as [es len0 rep b capb]. unfold PMES2.cps_seg.
  intros fx R M model KK HH Hmo HK Hfp (Hent & Ha0 & HGX & Hinv & Hdep & Himg & Hlits & Hroom & Hcred & Hobjs) Hcont.
  cbn [g_es g_len g_rep g_sb g_scap] in HGX, Hdep, Hcont.
  destruct es as [|c0 r0]; [exfalso; exact HGX|].
  assert (HARR : ec_arr c0 = true) by exact HGX.
  pose proof Hent as (Hra & Hraok & Hsp & Htp & Hstk).
  pose proof Hstk as (SK1 & SK2 & SK3 & SK4 & SK5).
  assert (VSC : PMES2.HEAD_SCR <= VIS_SCR WD_SCR_X) by (apply Z.leb_le; vm_compute; reflexivity).
  assert (EHS : PMES2.HEAD_SCR = 8672) by reflexivity.
  assert (EST : STRX_SCR = 8496) by reflexivity.
  assert (ENL : NEWLINE_SCR = 8576) by reflexivity.
  pose proof (PmLayout.ly_errno L LAY) as LER. pose proof (PmLayout.ly_img_lo L LAY) as ILO. pose proof (PmLayout.ly_img_hi L LAY) as IHI.
  pose proof (PmLayout.ly_kpm L LAY) as KPM. pose proof (PmLayout.ly_bov L LAY) as BOV.
  pose proof Hobjs as (OV & OS & OAP). pose proof OV as (OV1 & OV2 & OV3). pose proof OS as (OS1 & OS2 & OS3).
  unfold ENC_SIZE, apart in OV2, OAP.
  pose proof Hinv as (HOBJ0 & HSTK0 & HSINK0 & HLEN0 & HDEP0). cbn [g_es g_len g_rep g_sb g_scap] in HOBJ0, HSTK0, HSINK0, HLEN0, HDEP0.
  pose proof Hcred as (KX0 & _ & BX0 & _).
  pose proof (EK.scredit_of_ecreditU L KPM BOV cr _ kx bx Hcred) as HSC. cbn [g_rep g_scap] in HSC.
  assert (D1 : 1 <= depth (c0 :: r0)) by (unfold depth; cbn [length]; lia).
  assert (CB : 32 <= capb) by (destruct HSTK0 as (_ & _ & _ & T & _); lia).
  assert (SBK : stack_blocks b capb = [(b, capb)]) by (unfold stack_blocks; destruct (Z.eqb_spec capb 0); [lia | reflexivity]).
  destruct (hio_wf L SCFG HI HIok _ _ _ _ HH) as (Hwf & _ & _ & _).
  assert (BLO : forall bb, In bb LBo -> fst bb + snd bb <= hl_ceil L).
  { intros bb Hbb. destruct (Hwf bb ltac:(apply in_or_app; left; exact Hbb)) as ((B1 & B2 & B3 & B4 & B5) & _). exact B5. }
  assert (BB : block_range L b capb).
  { assert (HIN : In (b, capb) (LBo ++ g_lbv (EG (c0 :: r0) len0 rep b capb))).
    { apply in_or_app. right. unfold g_lbv. cbn [g_rep g_sb g_scap]. rewrite SBK. apply in_or_app. right. left. reflexivity. }
    destruct (Hwf _ HIN) as (BR & _). exact BR. }
  pose proof BB as (BB1 & BB2 & BB3 & BB4 & BB5).
  assert (ROOM0 : len0 + comma c0 + (1 + 4 * depth (c0 :: r0)) + 1 <= CLU).
  { clear - Hroom HARR. unfold eroomU, kmax, ev_ind, pay_hi in Hroom. cbn [g_len g_es] in Hroom. rewrite HARR in Hroom. unfold nl in Hroom. cbv beta iota in Hroom. lia. }
  assert (OBJ64 : objs_enc L (sp - 64) V S2).
  { split; [|split; [|exact OAP]]; unfold obj_on_stack, ENC_SIZE; lia. }
  assert (SD : 32 * depth (c0 :: r0) <= capb) by (destruct HSTK0 as (_ & _ & _ & T & _); exact T).
  assert (TAIL : forall fx3 R3 M3 mo3 cr3 rep3,
    fp_ok fx3 -> getr R3 1%bv = Z_to_bv 64 247044 -> getr R3 2%bv = Z_to_bv 64 (sp - 64) -> getr R3 4%bv = Z_to_bv 64 TP ->
    getr R3 8%bv = Z_to_bv 64 V -> getr R3 9%bv = Z_to_bv 64 (V + O_STACK) -> a0 R3 V -> PMES2.regs_kept false R R3 ->
    PMES2.frame_at false M3 (sp - 64) r (bv_unsigned (getr R 8%bv)) (bv_unsigned (getr R 9%bv)) (bv_unsigned (getr R 18%bv)) (bv_unsigned (getr R 19%bv)) ->
    L5.defined M3 (sp - 64) 64 -> u8 M3 (sp - 64 + 31) 0 ->
    PMES2.enc_objx M3 V S2 (depth (c0 :: r0)) (depth (c0 :: r0) + 1) -> stack_at M3 V (set_nla c0 :: r0) b capb -> sink_at M3 S2 rep3 ->
    len (srep_chars rep3) = len0 + comma c0 ->
    L5C.hpres L LBo sp PMES2.HEAD_SCR (PMES2.W_head V S2) M M3 -> model_but_vm model mo3 ->
    hi_heap HI (LBo ++ srep_blocks rep3 ++ stack_blocks b capb) cr3 M3 (m_vmmaps mo3) ->
    screditU L cr3 rep3 (kx + kv_st capb * hl_k_per_malloc L) (bx + bpot_st L capb) ->
    srealizes RSEGS SCFG (@cfg fx3 R3 PC_NEW_LINE M3 mo3) KK).
  { intros fx3 R3 M3 mo3 cr3 rep3 Hfp3 T1 T2 T4 T8 T9 TA0 TK TFR TDEF TU8 TOBJ TSTK TSINK TLEN HP3 Hbv3 HH3 TCR.
    assert (STK4 : L5C.stk (hl_sptop L) M3 (sp - 64) NEWLINE_SCR).
    { apply (stk_in M M3 sp (VIS_SCR WD_SCR_X) 64 NEWLINE_SCR Hstk VSC (L5C.hpres_defined _ _ _ _ _ _ _ HP3)); [lia | reflexivity | lia | lia]. }
    assert (HH3' : hi_heap HI ((LBo ++ stack_blocks b capb) ++ srep_blocks rep3) cr3 M3 (m_vmmaps mo3)).
    { apply (CH2V.hi_heap_perm L HI HIok _ _ _ _ _ HH3). rewrite <- app_assoc. apply Permutation_app_head. apply Permutation_app_comm. }
    apply (NEWLINE2 (LBo ++ stack_blocks b capb) cr3 (sp - 64) 247044 V S2 (kx + kv_st capb * hl_k_per_malloc L) (bx + bpot_st L capb)
             (depth (c0 :: r0)) rep3 fx3 R3 M3 mo3 KK HH3' (VBHK.model_ok_but_vm _ _ Hmo Hbv3) HK Hfp3).
    { split; [split; [exact T1|]; split; [unfold L5.ra_ok; split; [lia | reflexivity]|]; split; [exact T2|]; split; [exact T4 | exact STK4]|].
      split; [exact TA0|]. split; [apply (nl_reads_of M3 V S2 _ _ TOBJ); lia|].
      split; [exact TSINK|]. split; [exact TCR|]. split; [rewrite TLEN; lia | exact OBJ64]. }
    intros fx4 R4 M4 mo4 LB4 cr4 LBk4 W4 Hfp4 (rep4 & NSINK & NLEN & NCOL & -> & -> & -> & NCR) HRP4 HP4 Hbv4 HH4.
    assert (HPF : L5C.hpres L LBo sp PMES2.HEAD_SCR (PMES2.W_head V S2) M M4).
    { apply (ETL2.hpres_comp L LBo sp PMES2.HEAD_SCR (64 + NEWLINE_SCR) (PMES2.W_head V S2) M M3 M4); [lia | lia | lia | lia | lia | exact HP3 |].
      apply (VBHK.hpres_rebase L LBo sp 64 NEWLINE_SCR (PMES2.W_head V S2) M3 M4); [lia | lia | exact TDEF | lia | lia | lia | lia |].
      apply (VBHK.hpres_mono L (LBo ++ stack_blocks b capb) LBo (sp - 64) NEWLINE_SCR (W_h V S2) (PMES2.W_head V S2) M3 M4);
        [intros bb Hbb; apply in_or_app; left; exact Hbb | | exact HP4].
      intros a HO w Hw. unfold W_h in Hw. destruct Hw as [<-|[<-|[]]]; apply HO; unfold PMES2.W_head; inw. }
    assert (AG4 : forall a n, sp - 64 <= a -> a + n <= 2 ^ 64 -> (a + n <= V + O_COLUMN \/ V + O_COLUMN + 8 <= a) -> (a + n <= S2 \/ S2 + 24 <= a) ->
                  L5C.agree_on M3 M4 a n).
    { intros a n Ha Hn HC HS. apply (agree_stk _ _ _ _ M3 M3 M4 a n HP4 STK4); [lia | exact Ha | exact Hn |].
      intros x Hx w Hw. unfold W_h in Hw. destruct Hw as [<-|[<-|[]]]; unfold L5.in_rng; cbn [fst snd]; lia. }
    assert (AGF4 : L5C.agree_on M3 M4 (sp - 64) 64) by (apply AG4; unfold O_COLUMN; lia).
    assert (DEF4 : L5.defined M4 (sp - 64) 64) by exact (L5C.defined_agree M3 M4 _ _ AGF4 TDEF).
    assert (U84 : u8 M4 (sp - 64 + 31) 0) by (apply (EK.u8_agree M3 M4); [apply (EK.agree_sub M3 M4 _ _ _ _ AGF4); lia | lia | lia | exact TU8]).
    assert (FR4 : PMES2.frame_at false M4 (sp - 64) r (bv_unsigned (getr R 8%bv)) (bv_unsigned (getr R 9%bv)) (bv_unsigned (getr R 18%bv)) (bv_unsigned (getr R 19%bv))).
    { apply (frame_agree false M3 M4); [apply (EK.agree_sub M3 M4 _ _ _ _ AGF4); change (PMES2.LOC false) with 32; lia | lia | lia | exact TFR]. }
    assert (OBJ4 : PMES2.enc_objx M4 V S2 (depth (c0 :: r0)) (depth (c0 :: r0) + 1)).
    { apply (EK3.enc_objx_agree M3 M4 V S2 _ _); [lia | unfold ENC_SIZE; lia | apply AG4; unfold O_STACK, O_COLUMN in *; lia
          | apply AG4; unfold O_INDENT, O_COLUMN in *; lia | apply AG4; unfold O_COLON, O_COLUMN, ENC_SIZE in *; lia | exact NCOL | exact TOBJ]. }
    assert (STK4M : stack_at M4 V (set_nla c0 :: r0) b capb).
    { apply (EK.stack_at_agree M3 M4 V _ b capb); [lia | unfold ENC_SIZE; lia | apply AG4; unfold O_STACK, O_COLUMN in *; lia | intros _; split; [lia | split; [lia |]] | exact TSTK].
      apply (agree_blk _ _ _ _ M3 M4 b capb HP4); [rewrite SBK; apply in_or_app; right; left; reflexivity | exact BB | lia |].
      intros x Hx w Hw. unfold W_h in Hw. destruct Hw as [<-|[<-|[]]]; unfold L5.in_rng; cbn [fst snd]; unfold O_COLUMN; lia. }
    assert (HH4' : hi_heap HI (LBo ++ srep_blocks rep4 ++ stack_blocks b capb) cr4 M4 (m_vmmaps mo4)).
    { apply (CH2V.hi_heap_perm L HI HIok _ _ _ _ _ HH4). rewrite <- app_assoc. apply Permutation_app_head. apply Permutation_app_comm. }
    assert (STK5 : L5C.stk (hl_sptop L) M4 (sp - 64) 0).
    { apply (stk_in M M4 sp (VIS_SCR WD_SCR_X) 64 0 Hstk VSC (L5C.hpres_defined _ _ _ _ _ _ _ HPF)); [lia | reflexivity | lia | lia]. }
    pose proof STK4M as (U1 & U2 & _).
    apply (VBH_OC.seg_ok L HI HIok LAY FPM (LBo ++ srep_blocks rep4 ++ stack_blocks b capb) cr4 (sp - 64) V b (depth (c0 :: r0)) fx4 R4 M4 mo4 KK HH4'
             (VBHK.model_ok_but_vm _ _ (VBHK.model_ok_but_vm _ _ Hmo Hbv3) Hbv4) HK Hfp4).
    { split; [rewrite (HRP4 2%bv ltac:(csv)); exact T2|]. split; [rewrite (HRP4 4%bv ltac:(csv)); exact T4|]. split; [exact STK5|].
      split; [rewrite Zminus_mod, SK1; reflexivity|]. split; [rewrite (HRP4 8%bv ltac:(csv)); exact T8|].
      split; [exact U1|]. split; [exact U2|]. split; [lia|]. split; [unfold MAX_DEPTH in Hdep; lia|]. split; [lia|].
      replace (sp - 64 + 64) with sp by lia. exact OV. }
    intros fx5 R5 M5 mo5 LB5 cr5 LBk5 W5 Hfp5 (OR & -> & -> & -> & -> & OM) HP5 Hbv5 HH5.
    assert (AG5 : forall a n, sp - 64 <= a -> a + n <= 2 ^ 64 -> L5C.agree_on M4 M5 a n).
    { intros a n Ha Hn i Hi. apply OM. lia. }
    assert (HPG : L5C.hpres L LBo sp PMES2.HEAD_SCR (PMES2.W_head V S2) M M5).
    { apply (ETL2.hpres_comp L LBo sp PMES2.HEAD_SCR (64 + 0) (PMES2.W_head V S2) M M4 M5); [lia | lia | lia | lia | lia | exact HPF |].
      apply (VBHK.hpres_rebase L LBo sp 64 0 (PMES2.W_head V S2) M4 M5); [lia | lia | exact DEF4 | lia | lia | lia | lia |].
      apply (VBHK.hpres_mono L (LBo ++ srep_blocks rep4 ++ stack_blocks b capb) LBo (sp - 64) 0 [] (PMES2.W_head V S2) M4 M5);
        [intros bb Hbb; apply in_or_app; left; exact Hbb | intros a _ w [] | exact HP5]. }
    apply (Hcont fx5 R5 M5 mo5 (LBo ++ srep_blocks rep4 ++ stack_blocks b capb) cr4 LBo (PMES2.W_head V S2) Hfp5);
      [| exact HPG | exact (L5C.model_but_vm_trans _ _ _ (L5C.model_but_vm_trans _ _ _ Hbv3 Hbv4) Hbv5) | exact HH5].
    exists rep4. change PMES2.FRAME with 64.
    split; [rewrite (OR 2%bv ltac:(csv)), (HRP4 2%bv ltac:(csv)); exact T2|].
    split; [rewrite (OR 4%bv ltac:(csv)), (HRP4 4%bv ltac:(csv)); exact T4|].
    split; [rewrite (OR 8%bv ltac:(csv)), (HRP4 8%bv ltac:(csv)); exact T8|].
    split; [rewrite (OR 9%bv ltac:(csv)), (HRP4 9%bv ltac:(csv)); exact T9|].
    split; [unfold PMES2.RX_OBJ_NESTED; apply (EK.u8_agree M4 M5); [apply AG5; lia | lia | lia | exact U84]|].
    split; [intros x Hx; rewrite (OR x (kept_oc x Hx)), (HRP4 x (kept_cs false x Hx)); exact (TK x Hx)|].
    split; [apply (frame_agree false M4 M5); [apply AG5; change (PMES2.LOC false) with 32; lia | lia | lia | exact FR4]|].
    split; [exact (L5C.defined_agree M4 M5 _ _ (AG5 (sp - 64) 64 ltac:(lia) ltac:(lia)) DEF4)|].
    split.
    { unfold PMES2.head_post. cbv beta iota. rewrite HARR. cbv beta iota.
      split; [|split; [|split]].
      - apply (enc_objx_agree_all M4 M5); [lia | unfold ENC_SIZE; lia | apply AG5; unfold ENC_SIZE; lia | exact OBJ4].
      - apply (EK.stack_at_agree M4 M5 V _ b capb); [lia | unfold ENC_SIZE; lia | apply AG5; unfold O_STACK; lia | intros _; split; [lia | split; [lia |]] | exact STK4M].
        apply (agree_blk _ _ _ _ M4 M5 b capb HP5); [rewrite SBK; apply in_or_app; right; apply in_or_app; right; left; reflexivity | exact BB | lia | intros x _ w []].
      - destruct (hio_wf L SCFG HI HIok _ _ _ _ HH4') as (Hwf4 & _).
        apply (EK.sink_at_agree M4 M5 S2 rep4); [lia | lia | apply AG5; lia | | exact NSINK].
        destruct rep4 as [s|cap p s]; [exact I|].
        destruct (Hwf4 (p, cap) ltac:(apply in_or_app; right; apply in_or_app; left; left; reflexivity)) as (BR & _). cbn [fst snd] in BR.
        pose proof BR as (R1' & R2' & R3' & R4' & R5').
        split; [lia|]. split; [lia|].
        apply (agree_blk _ _ _ _ M4 M5 p cap HP5); [apply in_or_app; right; apply in_or_app; left; left; reflexivity | exact BR | lia | intros x _ w []].
      - rewrite NLEN, TLEN. unfold nl. lia. }
    split.
    { apply (lits_hp _ _ _ _ M M5 HPG); [|exact Hlits]. intros w a Hw Hin. unfold PMES2.W_head in Hw.
      destruct Hw as [<-|[<-|[<-|[]]]]; unfold L5.in_rng in Hin; cbn [fst snd] in Hin; unfold LIT_LO, LIT_HI, O_COLUMN, O_DEPTH in *; lia. }
    split.
    { apply (EK.img_ro_hpres L LBo sp PMES2.HEAD_SCR (PMES2.W_head V S2) M M5 LAY HPG); [|exact Himg]. intros w a Hw Hin. unfold PMES2.W_head in Hw.
      destruct Hw as [<-|[<-|[<-|[]]]]; unfold L5.in_rng in Hin; cbn [fst snd] in Hin; unfold IMG_RO_HI, O_COLUMN, O_DEPTH in *; lia. }
    split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. exact NCR. }
  destruct (Z.eq_dec (ec_count c0) 0) as [HC0|HC0].
  - apply (VBH_OAZ.seg_ok L HI HIok LAY FPM LBo cr sp r V S2 len0 b capb rep c0 r0 HARR HC0 fx R M model KK HH Hmo HK Hfp).
    { split; [exact Hent|]. split; [exact Ha0|]. split; [exact Hinv|]. split; [exact Hdep|]. split; [exact Himg|]. split; [exact Hlits | exact Hobjs]. }
    intros fx1 R1 M1 mo1 LB1 cr1 LBk1 W1 Hfp1 (Z1 & Z2 & Z4 & Z8 & Z9 & ZA0 & Z18 & ZK & ZFR & ZDEF & ZU8 & ZOBJ & ZSTK & ZSINK & ZLITS & ZIMG & -> & -> & -> & ->) HP1 Hbv1 HH1.
    apply (TAIL fx1 R1 M1 mo1 cr rep Hfp1 Z1 Z2 Z4 Z8 Z9 ZA0 ZK ZFR ZDEF ZU8 ZOBJ ZSTK ZSINK); [| | exact Hbv1 | exact HH1 | exact HSC].
    + rewrite HLEN0. unfold comma. rewrite HC0. cbn. lia.
    + apply (VBHK.hpres_mono L (LBo ++ srep_blocks rep) LBo sp PMES2.HEAD_SCR [(V + O_DEPTH, 4)] (PMES2.W_head V S2) M M1); [intros bb Hbb; apply in_or_app; left; exact Hbb | | exact HP1].
      intros a HO w Hw. destruct Hw as [<-|[]]. apply HO. unfold PMES2.W_head. inw.
  - assert (HPOS : 0 < ec_count c0).
    { pose proof (EK3.stack_head M V c0 r0 b capb HSTK0) as (_ & _ & _ & _ & CN & _). lia. }
    assert (COMMA2 : comma c0 = 2) by (unfold comma; rewrite (proj2 (Z.ltb_lt 0 (ec_count c0)) HPOS); reflexivity).
    apply (VBH_OAP.seg_ok L HI HIok LAY FPM LBo cr sp r V S2 len0 b capb rep c0 r0 HARR HPOS fx R M model KK HH Hmo HK Hfp).
    { split; [exact Hent|]. split; [exact Ha0|]. split; [exact Hinv|]. split; [exact Hdep|]. split; [exact Himg|]. split; [exact Hlits | exact Hobjs]. }
    intros fx1 R1 M1 mo1 LB1 cr1 LBk1 W1 Hfp1 (Q1 & Q2 & Q4 & Q8 & QA0 & QA1 & QA2 & QK & QFR & QDEF & QOBJ & QSTK & QSINK & QLITS & QIMG & -> & -> & -> & ->) HP1 Hbv1 HH1.
    pose proof (VBHK.model_ok_but_vm _ _ Hmo Hbv1) as Hmo1.
    assert (HPa : L5C.hpres L LBo sp PMES2.HEAD_SCR (PMES2.W_head V S2) M M1).
    { apply (VBHK.hpres_mono L (LBo ++ srep_blocks rep ++ stack_blocks b capb) LBo sp PMES2.HEAD_SCR [(V + O_DEPTH, 4)] (PMES2.W_head V S2) M M1); [intros bb Hbb; apply in_or_app; left; exact Hbb | | exact HP1].
      intros a HO w Hw. destruct Hw as [<-|[]]. apply HO. unfold PMES2.W_head. inw. }
    assert (STK2 : L5C.stk (hl_sptop L) M1 (sp - 64) STRX_SCR).
    { apply (stk_in M M1 sp (VIS_SCR WD_SCR_X) 64 STRX_SCR Hstk VSC (L5C.hpres_defined _ _ _ _ _ _ _ HPa)); [lia | reflexivity | lia | lia]. }
    assert (ND1 : List.NoDup (map fst (LBo ++ srep_blocks rep ++ stack_blocks b capb))).
    { destruct (hio_wf L SCFG HI HIok _ _ _ _ HH1) as (_ & N & _). first [apply base.NoDup_ListNoDup in N; exact N | exact N]. }
    assert (L2 : len [44; 32] = 2) by reflexivity.
    eapply (APPENDX (LBo ++ srep_blocks rep ++ stack_blocks b capb) cr S2 TXT_COMMA (sp - 64) _ rep [44; 32] fx1 R1 M1 mo1 KK HH1 Hmo1 HK Hfp1).
    { split; [split; [exact Q1|]; split; [unfold L5.ra_ok; split; [lia | reflexivity]|]; split; [exact Q2|]; split; [exact Q4 | exact STK2]|].
      split; [exact QA0|]. split; [exact QA1|]. split; [exact QA2|]. split; [exact QSINK|].
      split; [exact (EK.rep_live_lbv LBo (EG (c0 :: r0) len0 rep b capb))|].
      split; [unfold obj_on_stack; split; [lia | split; [lia | exact OS3]]|].
      split; [eapply EK.lit_bytes; [exact QIMG | apply Z.leb_le; vm_compute; reflexivity | apply Z.leb_le; vm_compute; reflexivity | exact EK.txt_comma]|].
      split; [right; left; split; [apply Z.leb_le; vm_compute; reflexivity | split; [apply Z.leb_le; vm_compute; reflexivity | exact QIMG]]|].
      split; [rewrite L2, HLEN0; unfold CLU in ROOM0; lia|].
      intros Hnf. apply (EK.grow_okU L KPM BOV cr rep _ _ _ HSC (EK.rep8_of_sink _ _ _ QSINK)); [unfold len; lia | rewrite L2, HLEN0; lia | exact Hnf]. }
    intros fx2 R2 M2 mo2 LB2 cr2 LBk2 W2 Hfp2 (rep2 & s2 & HLS & HXG & ->) HRP2 HP2 Hbv2 HH2.
    pose proof (VBHK.model_ok_but_vm _ _ Hmo1 Hbv2) as Hmo2.
    pose proof (EK.grown_screditU L KPM BOV _ _ _ _ _ _ _ _ _ _ _ _ HXG (EK.rep8_of_sink _ _ _ QSINK) ltac:(rewrite HLS, L2, HLEN0; lia) HSC) as HSC2.
    destruct (grown_facts _ _ _ _ _ _ _ _ _ _ _ ND1 HXG) as (GSINK & GCH & GPERM & ->).
    pose proof (CH2V.hi_heap_perm L HI HIok _ _ _ _ _ HH2 GPERM) as HH2'.
    assert (HPb : L5C.hpres L LBo sp PMES2.HEAD_SCR (PMES2.W_head V S2) M M2).
    { apply (ETL2.hpres_comp L LBo sp PMES2.HEAD_SCR (64 + STRX_SCR) (PMES2.W_head V S2) M M1 M2); [lia | lia | lia | lia | lia | exact HPa |].
      apply (VBHK.hpres_rebase L LBo sp 64 STRX_SCR (PMES2.W_head V S2) M1 M2); [lia | lia | exact QDEF | lia | lia | lia | lia |].
      apply (VBHK.hpres_mono L (LBo ++ stack_blocks b capb) LBo (sp - 64) STRX_SCR [(S2, 24)] (PMES2.W_head V S2) M1 M2);
        [intros bb Hbb; apply in_or_app; left; exact Hbb | | exact HP2].
      intros a HO w Hw. destruct Hw as [<-|[]]. apply HO. unfold PMES2.W_head. inw. }
    assert (AG2 : forall a n, sp - 64 <= a -> a + n <= 2 ^ 64 -> (a + n <= S2 \/ S2 + 24 <= a) -> L5C.agree_on M1 M2 a n).
    { intros a n Ha Hn HS. apply (agree_stk _ _ _ _ M1 M1 M2 a n HP2 STK2); [lia | exact Ha | exact Hn |].
      intros x Hx w Hw. destruct Hw as [<-|[]]. unfold L5.in_rng. cbn [fst snd]. lia. }
    assert (AGF2 : L5C.agree_on M1 M2 (sp - 64) 64) by (apply AG2; lia).
    assert (DEF2 : L5.defined M2 (sp - 64) 64) by exact (L5C.defined_agree M1 M2 _ _ AGF2 QDEF).
    assert (OBJ2 : PMES2.enc_objx M2 V S2 (depth (c0 :: r0)) (depth (c0 :: r0) + 1)).
    { apply (enc_objx_agree_all M1 M2); [lia | unfold ENC_SIZE; lia | apply AG2; unfold ENC_SIZE; lia | exact QOBJ]. }
    assert (AGB2 : L5C.agree_on M1 M2 b capb).
    { apply (agree_blk _ _ _ _ M1 M2 b capb HP2); [rewrite SBK; apply in_or_app; right; left; reflexivity | exact BB | lia |].
      intros x Hx w Hw. destruct Hw as [<-|[]]. unfold L5.in_rng. cbn [fst snd]. lia. }
    assert (STKM2 : stack_at M2 V (c0 :: r0) b capb).
    { apply (EK.stack_at_agree M1 M2 V (c0 :: r0) b capb); [lia | unfold ENC_SIZE; lia | apply AG2; unfold O_STACK; lia | intros _; split; [lia | split; [lia | exact AGB2]] | exact QSTK]. }
    assert (STK3 : L5C.stk (hl_sptop L) M2 (sp - 64) 0).
    { apply (stk_in M M2 sp (VIS_SCR WD_SCR_X) 64 0 Hstk VSC (L5C.hpres_defined _ _ _ _ _ _ _ HPb)); [lia | reflexivity | lia | lia]. }
    apply (VBH_OB.seg_ok L HI HIok LAY FPM LBo cr2 (sp - 64) V S2 b capb (depth (c0 :: r0)) (depth (c0 :: r0) + 1) rep2 c0 r0 HARR fx2 R2 M2 mo2 KK HH2' Hmo2 HK Hfp2).
    { split; [rewrite (HRP2 2%bv ltac:(csv)); exact Q2|]. split; [rewrite (HRP2 4%bv ltac:(csv)); exact Q4|]. split; [exact STK3|].
      split; [rewrite Zminus_mod, SK1; reflexivity|]. split; [rewrite (HRP2 8%bv ltac:(csv)); exact Q8|].
      split; [exact OBJ2|]. split; [exact STKM2|]. split; [exact Hdep|]. split; [replace (sp - 64 + 64) with sp by lia; exact OV|].
      intros i Hi. apply DEF2. lia. }
    intros fx3 R3 M3 mo3 LB3 cr3 LBk3 W3 Hfp3 (B1 & B2 & B4 & B8 & B9 & BA0 & B18 & BK & BU8 & BOBJ & BSTK & -> & -> & -> & ->) HP3 Hbv3 HH3.
    assert (DEF3 : L5.defined M3 (sp - 64) 64).
    { apply (defined_hp _ _ _ _ M2 M3 (sp - 64) 64 HP3); [lia | lia | lia | lia | lia | exact DEF2]. }
    assert (AG3 : forall a n, sp - 32 <= a -> a + n <= 2 ^ 64 -> (a + n <= V + O_COLUMN \/ V + O_COLUMN + 8 <= a) -> L5C.agree_on M2 M3 a n).
    { intros a n Ha Hn HC. apply (agree_stk _ _ _ _ M2 M2 M3 a n HP3 STK3); [lia | lia | exact Hn |].
      intros x Hx w Hw. destruct Hw as [<-|[<-|[]]]; unfold L5.in_rng; cbn [fst snd]; lia. }
    assert (FR3 : PMES2.frame_at false M3 (sp - 64) r (bv_unsigned (getr R 8%bv)) (bv_unsigned (getr R 9%bv)) (bv_unsigned (getr R 18%bv)) (bv_unsigned (getr R 19%bv))).
    { apply (frame_agree false M2 M3); [apply AG3; change (PMES2.LOC false) with 32; unfold O_COLUMN; lia | lia | lia |].
      apply (frame_agree false M1 M2); [apply AG2; change (PMES2.LOC false) with 32; lia | lia | lia | exact QFR]. }
    assert (SINK3 : sink_at M3 S2 rep2).
    { destruct (hio_wf L SCFG HI HIok _ _ _ _ HH2') as (Hwf2 & _).
      apply (EK.sink_at_agree M2 M3 S2 rep2); [lia | lia | apply AG3; unfold O_COLUMN; lia | | exact GSINK].
      destruct rep2 as [s|cap p s]; [exact I|].
      destruct (Hwf2 (p, cap) ltac:(apply in_or_app; right; apply in_or_app; left; left; reflexivity)) as (BR & _). cbn [fst snd] in BR.
      pose proof BR as (R1' & R2' & R3' & R4' & R5').
      split; [lia|]. split; [lia|].
      apply (agree_blk _ _ _ _ M2 M3 p cap HP3); [apply in_or_app; right; left; reflexivity | exact BR | lia |].
      intros x Hx w Hw. destruct Hw as [<-|[<-|[]]]; unfold L5.in_rng; cbn [fst snd]; unfold O_COLUMN; lia. }
    assert (HPc : L5C.hpres L LBo sp PMES2.HEAD_SCR (PMES2.W_head V S2) M M3).
    { apply (ETL2.hpres_comp L LBo sp PMES2.HEAD_SCR (64 + 0) (PMES2.W_head V S2) M M2 M3); [lia | lia | lia | lia | lia | exact HPb |].
      apply (hpres_wdrop LBo sp (64 + 0) [(V + O_COLUMN, 8); (sp - 64, 32)] (PMES2.W_head V S2) M2 M3 BLO); [lia | lia | |].
      - intros a HO HN w Hw. destruct Hw as [<-|[<-|[]]].
        + apply HO. unfold PMES2.W_head. inw.
        + unfold L5.in_rng. cbn [fst snd]. lia.
      - apply (VBHK.hpres_rebase L LBo sp 64 0 [(V + O_COLUMN, 8); (sp - 64, 32)] M2 M3); [lia | lia | exact DEF2 | lia | lia | lia | lia |].
        apply (VBHK.hpres_mono L (LBo ++ srep_blocks rep2) LBo (sp - 64) 0 [(V + O_COLUMN, 8); (sp - 64, 32)] [(V + O_COLUMN, 8); (sp - 64, 32)] M2 M3); [intros bb Hbb; apply in_or_app; left; exact Hbb | intros a H; exact H | exact HP3]. }
    apply (TAIL fx3 R3 M3 mo3 cr2 rep2 Hfp3 B1 B2 B4 B8 B9 BA0);
      [| exact FR3 | exact DEF3 | exact BU8 | exact BOBJ | exact BSTK | exact SINK3 | rewrite GCH, HLS, L2, HLEN0, COMMA2; reflexivity | exact HPc
       | exact (L5C.model_but_vm_trans _ _ _ (L5C.model_but_vm_trans _ _ _ Hbv1 Hbv2) Hbv3) | exact HH3 | exact HSC2].
    intros x Hx. rewrite (BK x Hx), (HRP2 x (kept_cs false x Hx)), (QK x Hx). reflexivity.
Qed.
End Head.
End VBH_OAU.
