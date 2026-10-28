(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OssFuzzTheorems.jsoncons.fuzz_json_encoder.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare ShapeAlg SpinAlg HeapIface L5Defs L5Core. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5 Require Import PmLibDefs_u5 PmLibSpecs_u5 PmLayout_u5 PmEncSpecs_u5 PmEncSpecs2_u5.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.CutCert Require Import CutHeap2.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.PmParse Require Import ParseBridges_u5.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.PmEnc Require Import EncKit_u5 EncKit2_u5 EncKit3_u5.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Module EVBFU.
Import PML PMES.
Abbreviation mem := (word -> option byte).

(* [comment removed for export] *)
Definition hd_upd (es : estate) : estate := match es with [] => [] | c :: r => if ec_arr c then set_nla c :: r else es end.
Lemma depth_hd_upd : forall es, depth (hd_upd es) = depth es.
Proof. intros [|c r]; [reflexivity|]. unfold hd_upd. destruct (ec_arr c); reflexivity. Qed.
Lemma hd_upd_nil : forall es, hd_upd es = [] <-> es = [].
Proof. intros [|c r]; [split; reflexivity|]. unfold hd_upd. destruct (ec_arr c); split; intros H; discriminate H. Qed.

(* [comment removed for export] *)
Lemma scr_vals : VIS_SCR WD_SCR_X = 10624 /\ PMES2.HEAD_SCR = 8672 /\ PMES2.MID_SCR = 8384 /\ PMES2.TAIL_SCR = 8496.
Proof. repeat split; reflexivity. Qed.

(* [comment removed for export] *)
Lemma defined_fwd : forall (M M' : mem) a n, L5.defined M a n -> (forall i, a <= i < a + n -> M (Z_to_bv 64 i) <> None -> M' (Z_to_bv 64 i) <> None) -> L5.defined M' a n.
Proof. intros M M' a n HD HF i Hi. apply HF; [lia|]. apply HD. exact Hi. Qed.
Lemma defined_of_agree : forall (M M' : mem) a n, L5C.agree_on M M' a n -> L5.defined M a n -> L5.defined M' a n.
Proof. intros M M' a n AG HD i Hi. rewrite (AG (a + i)) by lia. apply HD. exact Hi. Qed.
Lemma defined_u64 : forall (M : mem) a v, u64 M a v -> 0xfe000 <= a -> a + 8 <= 2 ^ 64 -> L5.defined M a 8.
Proof. intros M a v Hu Ha H8. intros i Hi. exact (PB.defined_of_u64 M a v Hu Ha H8 i Hi). Qed.

(* [comment removed for export] *)
Lemma kv_pow : forall k, 0 <= k <= 10 -> Z.log2 (32768 / (32 * 2 ^ k)) = 10 - k.
Proof.
  intros k Hk. replace 32768 with (2 ^ (10 - k) * (32 * 2 ^ k)).
  - rewrite Z.div_mul by (pose proof (Z.pow_pos_nonneg 2 k); lia). apply Z.log2_pow2. lia.
  - rewrite (Z.mul_comm 32 (2 ^ k)), Z.mul_assoc, <- Z.pow_add_r by lia. replace (10 - k + k) with 10 by lia. reflexivity.
Qed.

Section S.
Context {SCFG_P : ScfgP}.
Variable L : heap_layout.
Variable HI : heap_iface.
Hypothesis HIok : heap_iface_ok L SCFG HI.
Hypothesis LAY : PmLayout.pm0_layout L.

(* [comment removed for export] *)
Lemma lits_hpres : forall LBk sp scr W (M M' : mem), L5C.hpres L LBk sp scr W M M' ->
  (forall w a, In w W -> L5.in_rng w a -> ~ (LIT_LO <= a < LIT_HI)) -> lits_ok M -> lits_ok M'.
Proof.
  intros LBk sp scr W M M' HP HW HL. apply (lits_ok_agree M M'); [|exact HL]. intros a Ha.
  apply (L5C.hpres_kept _ _ _ _ _ _ _ a HP).
  pose proof (PmLayout.ly_img_lo L LAY) as ILO. pose proof (PmLayout.ly_img_hi L LAY) as IHI. pose proof (PmLayout.ly_errno L LAY) as LE. unfold LIT_LO, LIT_HI in *.
  apply L5C.kept_static; [rewrite ILO, IHI; lia | intros X; pose proof (PmLayout.ly_static L LAY a X); lia | rewrite ILO; lia | rewrite IHI; lia | rewrite LE; lia|].
  intros w Hw Hin. exact (HW w a Hw Hin Ha).
Qed.

Section Compose.
Variable K : PMES2.bkind.
Variables (pc pcm : Z) (GXh GXm : estate -> Prop) (RX : bvmap 5 word -> mem -> Z -> Z -> Z -> Prop).
Hypothesis HEAD : PMES2.head_spec L HI (PMES2.bk_arr K) pc pcm GXh RX.
Hypothesis MID : PMES2.mid_spec L HI K pcm GXm RX.
Hypothesis TAIL : PMES2.tail_spec L HI K.
Hypothesis GXhm : forall es, GXh es -> GXm (hd_upd es).

Lemma compose_ok : forall (LBo : list (Z * Z)) (cr : credit) (sp r V S2 kx bx : Z) (g : eghost), GXh (g_es g) ->
  cps_heap L HI pc r sp (VIS_SCR WD_SCR_X) (LBo ++ g_lbv g) cr
    (fun R M => entry L R M sp r (VIS_SCR WD_SCR_X) /\ a0 R V /\ True /\ enc_inv M V S2 g /\ ev_guard (g_es g) (EvBegin (PMES2.bk_arr K)) /\ eroomU g (EvBegin (PMES2.bk_arr K)) /\ img_ro M /\ lits_ok M /\
                ecreditU L cr g kx bx /\ objs_enc L sp V S2)
    (fun R M R' M' LB' cr' LBk W => exists (g' : eghost) (pay : Z),
        a0 R' 1 /\ enc_inv M' V S2 g' /\ g_es g' = estep (g_es g) (EvBegin (PMES2.bk_arr K)) /\ pay_ok (EvBegin (PMES2.bk_arr K)) pay /\
        g_len g' = g_len g + ev_ind (g_es g) (EvBegin (PMES2.bk_arr K)) + pay /\
        lits_ok M' /\ LB' = LBo ++ g_lbv g' /\ LBk = LBo /\ W = W_enc V S2 /\ ecreditU L cr' g' kx bx).
Proof.
  intros LBo cr sp r V S2 kx bx g HGX fx R M model KK HH Hmo HK Hfp (Hent & Ha0 & _ & Hinv & Hgd & Hroom & Himg & Hlits & Hcred & Hobjs) Hcont.
  pose proof scr_vals as (EVS & EHS & EMS & ETS).
  pose proof Hent as (Hra & Hraok & Hsp & Htp & Hstk). pose proof Hstk as (S1 & S2f & S3 & S4 & S5). rewrite EVS in S2f, S5.
  unfold ev_guard in Hgd. pose proof Hcred as (KX0 & _ & BX0 & _).
  pose proof (PmLayout.ly_errno L LAY) as LER. pose proof (PmLayout.ly_kpm L LAY) as KPM. pose proof (PmLayout.ly_bov L LAY) as BOV.
  assert (LOCB : 24 <= PMES2.LOC (PMES2.bk_arr K) <= 32) by (unfold PMES2.LOC; destruct (PMES2.bk_arr K); lia).
  pose proof Hobjs as (OV & OS & OAP). pose proof OV as (OV1 & OV2 & OV3). pose proof OS as (OS1 & OS2 & OS3). unfold ENC_SIZE, apart in OV2, OAP.
  set (es := g_es g) in *. set (d := depth es) in *. set (b := g_sb g) in *. set (capb := g_scap g) in *.
  assert (D0 : 0 <= d) by (unfold d, depth; lia).
  destruct (hio_wf L SCFG HI HIok _ _ _ _ HH) as (Hwf & _ & CR0 & _).
  assert (BLO : forall bb, In bb LBo -> block_range L (fst bb) (snd bb)) by (intros bb Hbb; apply Hwf; apply in_or_app; left; exact Hbb).
  (* [comment removed for export] *)
  apply (HEAD LBo cr sp r V S2 kx bx g fx R M model KK HH Hmo HK Hfp).
  { split; [exact Hent|]. split; [exact Ha0|]. split; [exact HGX|]. split; [exact Hinv|]. split; [exact Hgd|]. split; [exact Himg|]. split; [exact Hlits|].
    split; [exact Hroom|]. split; [exact Hcred | exact Hobjs]. }
  intros fx1 R1 M1 mo1 LB1 cr1 LBk1 W1 Hfp1 (rep1 & Q2 & Q4 & Q8 & Q9 & QRX & QK1 & QFR & QDEF & (QOBJ & QSTK & QSINK & QLEN) & QLITS & QIMG & -> & -> & -> & QCR) HP1 Hbv1 HH1.
  change PMES2.FRAME with 64 in *.
  fold es in QRX, QOBJ, QSTK, QLEN, QCR, HH1. fold d in QRX, QOBJ, QSTK, QLEN, QCR, HH1. fold b in QRX, QOBJ, QSTK, QLEN, QCR, HH1. fold capb in QRX, QOBJ, QSTK, QLEN, QCR, HH1.
  pose proof (CH2.model_ok_but_vm _ _ Hbv1 Hmo) as Hmo1.
  pose proof HP1 as (HK1 & HD1 & HC1). rewrite EHS in HD1, HK1, HC1.
  (* [comment removed for export] *)
  destruct (hio_wf L SCFG HI HIok _ _ _ _ HH1) as (Hwf1 & _ & CR1 & _).
  (* [comment removed for export] *)
  replace (LBo ++ srep_blocks rep1 ++ stack_blocks b capb) with ((LBo ++ srep_blocks rep1) ++ stack_blocks b capb) in HH1 by (symmetry; apply app_assoc || (rewrite app_assoc; reflexivity)).
  apply (MID (LBo ++ srep_blocks rep1) cr1 (sp - 64) V S2 b capb d (d + 1) (hd_upd es) fx1 R1 M1 mo1 KK HH1 Hmo1 HK Hfp1).
  change PMES2.FRAME with 64.
  { split; [exact Q2|]. split; [exact Q4|]. split.
    { split; [clear - S1; apply Z.mod_divide in S1; [|lia]; apply Z.mod_divide; [lia|]; destruct S1 as [q Hq]; exists (q - 4); lia|].
      rewrite EMS. split; [lia|]. split; [lia|]. split; [lia|]. intros i Hi. replace (sp - 64 - 8384 + i) with (sp - 8672 + (i + 224)) by lia. apply HD1. lia. }
    split; [clear - S1; apply Z.mod_divide in S1; [|lia]; apply Z.mod_divide; [lia|]; destruct S1 as [q Hq]; exists (q - 4); lia|].
    split; [exact Q8|]. split; [exact Q9|]. split; [apply GXhm; exact HGX|]. split; [rewrite depth_hd_upd; exact QRX|].
    split; [exact QOBJ|]. split; [exact QSTK|]. split; [rewrite depth_hd_upd; exact Hgd|].
    split; [replace (sp - 64 + 64) with sp by lia; exact OV|]. split; [exact QDEF|].
    intros Hfull. rewrite depth_hd_upd in Hfull.
    pose proof (EK.ecredit_of_screditU L KPM BOV cr1 g kx bx rep1 (EG (hd_upd es) (g_len g) rep1 b capb) eq_refl eq_refl QCR KX0 BX0) as HE1.
    destruct (EK.ecredit_stack_growU L KPM BOV cr1 (EG (hd_upd es) (g_len g) rep1 b capb) kx bx HE1 (EK.stack_shape_of_at _ _ _ _ _ QSTK))
      as [HG _]; [cbn [g_es g_scap]; rewrite depth_hd_upd; exact Hfull | cbn [g_es]; rewrite depth_hd_upd; exact Hgd | exact HG]. }
  intros fx2 R2 M2 mo2 LB2 cr2 LBk2 W2 Hfp2 (b' & capb' & P2 & P4 & P8 & P18 & PK2 & POBJ & PSTM & -> & -> & -> & PCASE) HP2 Hbv2 HH2.
  rewrite depth_hd_upd in P18, PCASE. unfold PMES2.W_mid in HP2. cbn [PMES2.bk_arr] in HP2.
  pose proof (CH2.model_ok_but_vm _ _ Hbv2 Hmo1) as Hmo2.
  pose proof HP2 as (HK2 & HD2 & HCL2). rewrite EMS in HD2, HK2, HCL2.
  destruct (hio_wf L SCFG HI HIok _ _ _ _ HH2) as (Hwf2 & _ & CR2 & _).
  assert (CB' : 32 <= capb') by (destruct PSTM as (_ & _ & _ & (k & Hk & ->) & _); assert (1 <= 2 ^ k) by (apply Z.pow_le_mono_r with (a := 2) (b := 0) (c := k) || idtac; pose proof (Z.pow_pos_nonneg 2 k); lia); nia).
  (* [comment removed for export] *)
  assert (KM : forall a, 0 <= a < 2 ^ 64 -> (sp - 64 <= a \/ (hl_ceil L <= a < sp - 64 - 8384) \/ (hl_img_lo L <= a < hl_img_hi L /\ ~ hl_alloc_static L a) \/ in_block (LBo ++ srep_blocks rep1) a) ->
                 ~ in_errno L a -> ~ (V + O_STACK <= a < V + O_STACK + 24) -> ~ (sp - 64 <= a < sp - 64 + PMES2.LOC (PMES2.bk_arr K)) -> M2 (Z_to_bv 64 a) = M1 (Z_to_bv 64 a)).
  { intros a Ha Hc He Hw1 Hw2. apply HK2. split; [exact Ha|]. split.
    - destruct Hc as [X|[X|[X|X]]]; [right; left; unfold hl_ceil in *; lia | right; left; lia | right; right; exact X | left; exact X].
    - split; [exact He|]. intros w [<-|[<-|[]]]; unfold L5.in_rng; cbn [fst snd]; lia. }
  assert (FR2 : PMES2.frame_at (PMES2.bk_arr K) M2 (sp - 64) r (bv_unsigned (getr R 8%bv)) (bv_unsigned (getr R 9%bv)) (bv_unsigned (getr R 18%bv)) (bv_unsigned (getr R 19%bv))).
  { destruct QFR as (F1 & F2 & F3 & F4 & F5). unfold PMES2.frame_at.
    assert (AGF : L5C.agree_on M1 M2 (sp - 64 + PMES2.LOC (PMES2.bk_arr K)) (64 - PMES2.LOC (PMES2.bk_arr K))).
    { intros i Hi. apply KM; [unfold hl_ceil in *; lia | left; lia | unfold in_errno; rewrite LER; unfold hl_ceil in *; lia | unfold O_STACK, obj_on_stack in *; lia | lia]. }
    split; [|split; [|split; [|split]]];
      [ .. | intros HA; assert (LA : PMES2.LOC (PMES2.bk_arr K) = 24) by (unfold PMES2.LOC; rewrite HA; reflexivity); specialize (F5 HA) ];
      (apply (EK.u64_agree M1 M2); [apply (EK.agree_sub M1 M2 _ _ _ _ AGF); lia | unfold hl_ceil in *; lia | unfold hl_ceil in *; lia | assumption]). }
  assert (DEF2 : L5.defined M2 (sp - 64) 64).
  { apply (defined_fwd M1 M2 _ _ QDEF). intros i Hi Hd. apply HCL2; [unfold hl_ceil in *; lia | right; left; unfold hl_ceil in *; lia | unfold in_errno; rewrite LER; unfold hl_ceil in *; lia | exact Hd]. }
  assert (D272 : L5.defined M2 (V + O_STACK + 8) 8).
  { destruct QSTK as (_ & T2 & _). apply (defined_fwd M1 M2 _ _ (defined_u64 M1 _ _ T2 ltac:(unfold O_STACK, obj_on_stack, hl_ceil in *; lia) ltac:(unfold O_STACK, obj_on_stack, hl_ceil in *; lia))).
    intros i Hi Hd. apply HCL2; [unfold O_STACK, obj_on_stack, hl_ceil in *; lia | right; left; unfold O_STACK, obj_on_stack, hl_ceil in *; lia | unfold in_errno; rewrite LER; unfold O_STACK, obj_on_stack, hl_ceil in *; lia | exact Hd]. }
  assert (SINK2 : sink_at M2 S2 rep1).
  { apply (EK.sink_at_agree M1 M2 S2 rep1); [unfold obj_on_stack, hl_ceil in *; lia | unfold obj_on_stack, hl_ceil in *; lia | | | exact QSINK].
    - intros i Hi. apply KM; [unfold obj_on_stack, hl_ceil in *; lia | left; unfold obj_on_stack in *; lia | unfold in_errno; rewrite LER; unfold obj_on_stack, hl_ceil in *; lia | unfold O_STACK in *; lia | unfold obj_on_stack in *; lia].
    - destruct rep1 as [s|cap p s]; [exact I|]. cbn [srep_blocks] in *.
      destruct (Hwf1 (p, cap) ltac:(apply in_or_app; right; apply in_or_app; left; left; reflexivity)) as ((R1' & R2' & R3' & R4' & R5') & _). cbn [fst snd] in *.
      split; [lia|]. split; [unfold hl_ceil in *; lia|]. intros i Hi. apply KM; [unfold hl_ceil in *; lia | right; right; right; exists (p, cap); split; [apply in_or_app; right; left; reflexivity | cbn [fst snd]; lia] | | unfold O_STACK, obj_on_stack, hl_ceil in *; lia | unfold hl_ceil in *; lia].
      unfold in_errno. rewrite LER. pose proof (PmLayout.ly_img_lo L LAY). pose proof (PmLayout.ly_img_hi L LAY). lia. }
  assert (LITS2 : lits_ok M2).
  { apply (lits_hpres _ _ _ _ M1 M2 HP2); [|exact QLITS]. intros w a [<-|[<-|[]]]; unfold L5.in_rng, LIT_LO, LIT_HI, O_STACK, obj_on_stack, hl_ceil in *; cbn [fst snd]; lia. }
  assert (IMG2 : img_ro M2).
  { apply (EK.img_ro_hpres L _ _ _ _ M1 M2 LAY HP2); [|exact QIMG]. intros w a [<-|[<-|[]]]; unfold L5.in_rng, IMG_RO_HI, O_STACK, obj_on_stack, hl_ceil in *; cbn [fst snd]; lia. }
  (* [comment removed for export] *)
  assert (SCR2 : screditU L cr2 rep1 (kx + kv_st capb' * hl_k_per_malloc L) (bx + bpot_st L capb')).
  { destruct PCASE as [(PC1 & PCb & PCc & PC4)|(PC1 & PC2 & PC3)]; [rewrite PCc, PC4; exact QCR|].
    pose proof (EK.ecredit_of_screditU L KPM BOV cr1 g kx bx rep1 (EG (hd_upd es) (g_len g) rep1 b capb) eq_refl eq_refl QCR KX0 BX0) as HE1.
    destruct (EK.ecredit_stack_growU L KPM BOV cr1 (EG (hd_upd es) (g_len g) rep1 b capb) kx bx HE1 (EK.stack_shape_of_at _ _ _ _ _ QSTK))
      as [_ HG]; [cbn [g_es g_scap]; rewrite depth_hd_upd; exact PC1 | cbn [g_es]; rewrite depth_hd_upd; exact Hgd |].
    pose proof (HG (EG (hd_upd es) (g_len g) rep1 b' capb') eq_refl PC2) as HE2. cbn [g_scap g_rep] in HE2. rewrite <- PC3 in HE2.
    exact (EK.scredit_of_ecreditU L KPM BOV cr2 (EG (hd_upd es) (g_len g) rep1 b' capb') kx bx HE2). }
  assert (ROOMT : len (srep_chars rep1) + 1 <= CLU).
  { clear - Hroom QLEN. unfold eroomU, kmax, pay_hi, ev_ind in Hroom. rewrite QLEN. unfold es.
    destruct (g_es g) as [|c rr]; [lia | destruct (ec_arr c); lia]. }
  (* [comment removed for export] *)
  apply (TAIL LBo cr2 (sp - 64) V S2 b' capb' (kx + kv_st capb' * hl_k_per_malloc L) (bx + bpot_st L capb') r (bv_unsigned (getr R 8%bv)) (bv_unsigned (getr R 9%bv)) (bv_unsigned (getr R 18%bv)) (bv_unsigned (getr R 19%bv))
               (hd_upd es) rep1 fx2 R2 M2 mo2 KK ltac:(replace (LBo ++ srep_blocks rep1 ++ [(b', capb')]) with ((LBo ++ srep_blocks rep1) ++ [(b', capb')]) by (symmetry; apply app_assoc || (rewrite app_assoc; reflexivity)); exact HH2) Hmo2 HK Hfp2).
  { split; [exact P2|]. split; [exact P4|]. split.
    { split; [clear - S1; apply Z.mod_divide in S1; [|lia]; apply Z.mod_divide; [lia|]; destruct S1 as [q Hq]; exists (q - 4); lia|].
      rewrite ETS. split; [lia|]. split; [lia|]. split; [lia|].
      intros i Hi. destruct (Z_lt_dec (sp - 64 - 8496 + i) (sp - 64 - 8384)).
      - apply HCL2; [unfold hl_ceil in *; lia | right; left; unfold hl_ceil in *; lia | unfold in_errno; rewrite LER; unfold hl_ceil in *; lia |].
        replace (sp - 64 - 8496 + i) with (sp - 8672 + (112 + i)) by lia. apply HD1. lia.
      - replace (sp - 64 - 8496 + i) with (sp - 64 - 8384 + (i - 112)) by lia. apply HD2. lia. }
    split; [clear - S1; apply Z.mod_divide in S1; [|lia]; apply Z.mod_divide; [lia|]; destruct S1 as [q Hq]; exists (q - 4); lia|].
    split; [exact P8|]. split; [rewrite depth_hd_upd; exact P18|]. split; [exact FR2|]. split; [exact Hraok|]. split; [exact DEF2|]. split; [exact D272|].
    split; [rewrite depth_hd_upd; exact POBJ|]. split; [exact PSTM|]. split; [rewrite depth_hd_upd; exact Hgd|]. split; [exact SINK2|]. split; [exact SCR2|]. split; [exact ROOMT|].
    split; [exact IMG2|]. change PMES2.FRAME with 64. replace (sp - 64 + 64) with sp by lia. exact Hobjs. }
  intros fx3 R3 M3 mo3 LB3 cr3 LBk3 W3 Hfp3 (rep3 & T2 & T4 & TA0 & TK3 & T8 & T9 & T18 & T19 & TINV & -> & -> & -> & TCR) HP3 Hbv3 HH3.
  change PMES2.FRAME with 64 in *.
  pose proof HP3 as (HK3 & HD3 & HCL3). rewrite ETS in HD3, HK3, HCL3.
  set (g' := EG (ECtx (PMES2.bk_arr K) 0 false :: hd_upd es) (len (srep_chars rep1) + 1) rep3 b' capb').
  apply (Hcont fx3 R3 M3 mo3 (LBo ++ g_lbv g') cr3 LBo (W_enc V S2) Hfp3).
  - (* [comment removed for export] *)
    exists g', 0. split; [exact TA0|]. split; [exact TINV|]. split; [reflexivity|]. split; [reflexivity|].
    split; [unfold g'; cbn [g_len]; rewrite QLEN; unfold ev_ind, es; destruct (g_es g) as [|c rr]; [lia | destruct (ec_arr c); lia]|].
    split.
    { apply (lits_hpres _ _ _ _ M2 M3 HP3); [|exact LITS2]. intros w a [<-|[<-|[]]]; unfold L5.in_rng, LIT_LO, LIT_HI, O_STACK, obj_on_stack, hl_ceil in *; cbn [fst snd]; lia. }
    split; [unfold g', g_lbv, stack_blocks; cbn [g_rep g_sb g_scap]; destruct (Z.eqb_spec capb' 0); [lia | reflexivity]|].
    split; [reflexivity|]. split; [reflexivity|].
    exact (EK.ecredit_of_screditU L KPM BOV cr3 g' kx bx rep3 g' eq_refl eq_refl TCR KX0 BX0).
  - (* [comment removed for export] *)
    intros x Hx. unfold callee_saved_idx in Hx. cbn [In] in Hx.
    assert (KEPT : In (bv_unsigned x) (PMES2.KEPT (PMES2.bk_arr K)) -> getr R3 x = getr R x).
    { intros Hin. rewrite (TK3 x Hin), (PK2 x Hin), (QK1 x Hin). reflexivity. }
    assert (BX : forall y : bv 5, bv_unsigned x = bv_unsigned y -> x = y) by (intros y Hy; apply bv_eq; exact Hy).
    destruct Hx as [Hx|[Hx|[Hx|[Hx|[Hx|[Hx|[Hx|[Hx|Hx]]]]]]]]; try (symmetry in Hx).
    + rewrite (BX 2%bv Hx). rewrite T2, Hsp. f_equal. lia.
    + apply KEPT. rewrite Hx. unfold PMES2.KEPT. destruct (PMES2.bk_arr K); cbn; tauto.
    + rewrite (BX 4%bv Hx). rewrite T4, Htp. reflexivity.
    + rewrite (BX 8%bv Hx). rewrite T8. apply Z_to_bv_bv_unsigned.
    + rewrite (BX 9%bv Hx). rewrite T9. apply Z_to_bv_bv_unsigned.
    + rewrite (BX 18%bv Hx). rewrite T18. apply Z_to_bv_bv_unsigned.
    + destruct (PMES2.bk_arr K) eqn:HA.
      * rewrite (BX 19%bv Hx). first [rewrite (T19 eq_refl) | rewrite (T19 HA)]. apply Z_to_bv_bv_unsigned.
      * apply KEPT. try rewrite HA. rewrite Hx. cbn. tauto.
    + apply KEPT. rewrite Hx. unfold PMES2.KEPT. destruct (PMES2.bk_arr K); cbn; tauto.
    + apply KEPT. unfold PMES2.KEPT. destruct (PMES2.bk_arr K); cbn [In] in Hx |- *; tauto.
  - (* [comment removed for export] *)
    rewrite EVS. split; [|split].
    + intros a (Ha & CA & NE & OW).
      assert (OW' : ~ (V + O_STACK <= a < V + O_STACK + 40) /\ ~ (V + O_DEPTH <= a < V + O_DEPTH + 4) /\ ~ (S2 <= a < S2 + 24)).
      { split; [|split]; intros X; [apply (OW (V + O_STACK, 40)); [left; reflexivity|] | apply (OW (V + O_DEPTH, 4)); [right; left; reflexivity|] | apply (OW (S2, 24)); [right; right; left; reflexivity|]];
          unfold L5.in_rng; cbn [fst snd]; lia. }
      destruct OW' as (OW1 & OW2 & OW3).
      assert (CA' : sp <= a \/ hl_ceil L <= a < sp - 10624 \/ (hl_img_lo L <= a < hl_img_hi L /\ ~ hl_alloc_static L a) \/ in_block LBo a).
      { destruct CA as [X|[[X1 X2]|X]]; [right; right; right; exact X | | right; right; left; exact X]. destruct (Z_lt_dec a sp); [right; left; lia | left; lia]. }
      assert (BLK : in_block LBo a -> a < hl_ceil L) by (intros (bb & Hbb & Hr); destruct (BLO bb Hbb) as (_ & _ & _ & _ & B5); lia).
      transitivity (M2 (Z_to_bv 64 a)); [|transitivity (M1 (Z_to_bv 64 a))].
      * apply HK3. split; [exact Ha|]. split; [destruct CA' as [X|[X|[X|X]]]; [right; left; unfold hl_ceil in *; lia | right; left; lia | right; right; exact X | left; exact X]|].
        split; [exact NE|]. intros w [<-|[<-|[]]]; unfold L5.in_rng, O_STACK in *; cbn [fst snd]; lia.
      * apply KM; [exact Ha | | exact NE | unfold O_STACK in *; lia | destruct CA' as [X|[X|[X|X]]]; [lia | lia | pose proof (PmLayout.ly_img_hi L LAY); unfold hl_ceil in *; lia | pose proof (BLK X); unfold hl_ceil in *; lia]].
        destruct CA' as [X|[X|[X|X]]]; [left; lia | right; left; lia | right; right; left; exact X | right; right; right; destruct X as (bb & Hbb & Hr); exists bb; split; [apply in_or_app; left; exact Hbb | exact Hr]].
      * apply HK1. split; [exact Ha|]. split; [destruct CA' as [X|[X|[X|X]]]; [right; left; unfold hl_ceil in *; lia | right; left; lia | right; right; exact X | left; exact X]|].
        split; [exact NE|]. intros w [<-|[<-|[<-|[]]]]; unfold L5.in_rng, O_STACK, O_COLUMN, O_DEPTH in *; cbn [fst snd]; lia.
    + intros i Hi. destruct (Z_lt_dec (sp - 10624 + i) (sp - 64 - 8496)); [|destruct (Z_lt_dec (sp - 10624 + i) (sp - 64))].
      * apply HCL3; [unfold hl_ceil in *; lia | right; left; unfold hl_ceil in *; lia | unfold in_errno; rewrite LER; unfold hl_ceil in *; lia |].
        apply HCL2; [unfold hl_ceil in *; lia | right; left; unfold hl_ceil in *; lia | unfold in_errno; rewrite LER; unfold hl_ceil in *; lia |].
        destruct (Z_lt_dec (sp - 10624 + i) (sp - 8672)).
        -- apply HC1; [unfold hl_ceil in *; lia | right; left; unfold hl_ceil in *; lia | unfold in_errno; rewrite LER; unfold hl_ceil in *; lia |]. apply S5. lia.
        -- replace (sp - 10624 + i) with (sp - 8672 + (i - 1952)) by lia. apply HD1. lia.
      * replace (sp - 10624 + i) with (sp - 64 - 8496 + (i - 2064)) by lia. apply HD3. lia.
      * apply HCL3; [unfold hl_ceil in *; lia | right; left; unfold hl_ceil in *; lia | unfold in_errno; rewrite LER; unfold hl_ceil in *; lia |].
        replace (sp - 10624 + i) with (sp - 64 + (i - 10560)) by lia. apply DEF2. lia.
    + intros a Ha CA NE Hd.
      assert (CA' : forall LB' spx scrx, (forall bb, In bb LBo -> In bb LB') -> spx - scrx >= sp - 10624 -> spx <= sp -> client_addr L LB' spx scrx a).
      { intros LB' spx scrx HLB H1 H2. destruct CA as [(bb & Hbb & Hr)|[[X1 X2]|X]]; [left; exists bb; split; [apply HLB; exact Hbb | exact Hr] | right; left; lia | right; right; exact X]. }
      apply HCL3; [exact Ha | apply CA'; [intros bb Hbb; exact Hbb | lia | lia] | exact NE |].
      apply HCL2; [exact Ha | apply CA'; [intros bb Hbb; apply in_or_app; left; exact Hbb | lia | lia] | exact NE |].
      apply HC1; [exact Ha | apply CA'; [intros bb Hbb; exact Hbb | lia | lia] | exact NE | exact Hd].
  - exact (L5C.model_but_vm_trans _ _ _ Hbv1 (L5C.model_but_vm_trans _ _ _ Hbv2 Hbv3)).
  - unfold g', g_lbv, stack_blocks. cbn [g_rep g_sb g_scap]. destruct (Z.eqb_spec capb' 0); [lia|]. exact HH3.
Qed.
End Compose.

Hypothesis HEAD_OR : PMES2.head_obj_root_spec L HI.
Hypothesis HEAD_OO : PMES2.head_obj_inobj_spec L HI.
Hypothesis HEAD_OA : PMES2.head_obj_inarr_spec L HI.
Hypothesis HEAD_AR : PMES2.head_arr_root_spec L HI.
Hypothesis HEAD_AO : PMES2.head_arr_inobj_spec L HI.
Hypothesis HEAD_AA : PMES2.head_arr_inarr_spec L HI.
Hypothesis MID_OR : PMES2.mid_obj_root_spec L HI.
Hypothesis MID_ON : PMES2.mid_obj_nested_spec L HI.
Hypothesis MID_AR : PMES2.mid_arr_root_spec L HI.
Hypothesis MID_AO : PMES2.mid_arr_inobj_spec L HI.
Hypothesis MID_AA : PMES2.mid_arr_inarr_spec L HI.
Hypothesis TAIL_O : PMES2.tail_obj_spec L HI.
Hypothesis TAIL_A : PMES2.tail_arr_spec L HI.

Lemma par_cases : forall (es : estate), PMES2.par_root es \/ PMES2.par_obj es \/ PMES2.par_arr es.
Proof. intros [|c r]; [left; reflexivity | right; unfold PMES2.par_obj, PMES2.par_arr; destruct (ec_arr c); [right | left]; reflexivity]. Qed.
Lemma root_hm : forall es, PMES2.par_root es -> PMES2.is_root (hd_upd es).
Proof. intros es H. unfold PMES2.par_root, PMES2.is_root in *. subst es. reflexivity. Qed.
Lemma obj_hm : forall es, PMES2.par_obj es -> PMES2.is_nested (hd_upd es).
Proof. intros [|c r] H; [destruct H|]. unfold PMES2.is_nested. intros X. apply (proj1 (hd_upd_nil (c :: r))) in X. discriminate X. Qed.
Lemma arr_hm : forall es, PMES2.par_arr es -> PMES2.is_nested (hd_upd es).
Proof. intros [|c r] H; [destruct H|]. unfold PMES2.is_nested. intros X. apply (proj1 (hd_upd_nil (c :: r))) in X. discriminate X. Qed.

Theorem visit_begin_object_ok : visit_begin_object_specU L HI WD_SCR_X.
Proof.
  unfold visit_begin_object_specU, vtransU, vtrans_genU. intros LBo cr sp r V S2 kx bx g.
  destruct (par_cases (g_es g)) as [H|[H|H]].
  - exact (compose_ok PMES2.BK_OBJECT _ _ _ _ _ HEAD_OR MID_OR TAIL_O root_hm LBo cr sp r V S2 kx bx g H).
  - exact (compose_ok PMES2.BK_OBJECT _ _ _ _ _ HEAD_OO MID_ON TAIL_O obj_hm LBo cr sp r V S2 kx bx g H).
  - exact (compose_ok PMES2.BK_OBJECT _ _ _ _ _ HEAD_OA MID_ON TAIL_O arr_hm LBo cr sp r V S2 kx bx g H).
Qed.
Theorem visit_begin_array_ok : visit_begin_array_specU L HI WD_SCR_X.
Proof.
  unfold visit_begin_array_specU, vtransU, vtrans_genU. intros LBo cr sp r V S2 kx bx g.
  destruct (par_cases (g_es g)) as [H|[H|H]].
  - exact (compose_ok PMES2.BK_ARRAY _ _ _ _ _ HEAD_AR MID_AR TAIL_A root_hm LBo cr sp r V S2 kx bx g H).
  - exact (compose_ok PMES2.BK_ARRAY _ _ _ _ _ HEAD_AO MID_AO TAIL_A obj_hm LBo cr sp r V S2 kx bx g H).
  - exact (compose_ok PMES2.BK_ARRAY _ _ _ _ _ HEAD_AA MID_AA TAIL_A arr_hm LBo cr sp r V S2 kx bx g H).
Qed.
Print Assumptions visit_begin_array_ok.
End S.
End EVBFU.
