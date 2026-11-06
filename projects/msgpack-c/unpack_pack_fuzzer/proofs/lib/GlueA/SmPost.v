(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import PrimInt63 Uint63.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib Require Import PropExec MState Cells Frame ITree Nodes.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib Require ALib.Mem ALib.Step.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA Require Import AcctCore ExecF ITreeA NodesA.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec Require Import STree AsanCtrl AsanEmbed.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require Import AImg AProto ABase AMalloc_iface.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require Import AMalloc_iface2.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common Require Import RunDraw ShapeAlg.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX Require Import W64 Val IMap Instr State Step Plan PlanSound.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX Require Import Mem.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Heap Require Import Op.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Ctr Require Import Lib DefsA.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Bridge Require Import Ledger Op Adeq.
Import ListNotations.
Import W64 Val OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Mem.Mem FI St OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Step.Step Plan PlanS CtrLib HeapOp.
Open Scope Z_scope.
Unset Lia Cache.

From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Bridge Require Import Actr.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX Require Import W64Proofs ValProofs MemProofs StepSoundBase.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Br Require Import CtrFX.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Br Require HeapCtr HeapCtrB.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Bridge Require CallA CtrPre GlueA CtrPost CtrFrame.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Unp Require GLib.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.GlueA Require SmLib.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.GlueA Require Import ActrB SmShape SmWorld.
Unset Nia Cache. Unset Nra Cache.
Import ValP MemP CtrFX.
Import ActrA.
Module AP := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.PropExec.
Module AM := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Mem.
Module AS := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Step.

Section Post.
Context {rc : runConstT}.
Variable AI : AMallocIface2.
Variable IMGX : list iv.
Hypothesis IMGX_aci : imgx_ok AI IMGX.
Hypothesis IMGSH_aci : forall v a, In v Op.SHLIT -> fst v <= a < snd v -> exists a', in_ranges (aci AI) a' /\ a = shad a'.
Variable ACCT : word -> alayout -> footprint -> astate -> list ablock -> Model -> Prop.
Variable UNIV : list (list Z).
Variable Cw : client_world.
Variable OPS : optable.
Hypothesis AI_fake : AI_fake_law AI.
Hypothesis OPS_holds1 : forall args m mo, op_holds OPS HEAP_ID args m mo <-> heap_holdsX AI ACCT UNIV Cw args m mo.
Hypothesis OPS_fp1 : forall args, op_fp OPS HEAP_ID args = heap_fp IMGX args.
Hypothesis OPS_cov1 : forall args z, op_cov1 OPS HEAP_ID args z <-> Op.cov1 HEAP_ID args z.
Hypothesis OPS_frame_other : forall id args m m' mo, id <> HEAP_ID -> op_holds OPS id args m mo ->
  (forall a, 0 <= a < two64 -> Exists (fun iv => fst iv <= a < snd iv) (op_fp OPS id args) -> m (Z_to_bv 64 a) = m' (Z_to_bv 64 a)) ->
  (forall a, 0 <= a < two64 -> (in_ranges (aci AI) a \/ (exists a', in_ranges (aci AI) a' /\ a = shad a') \/ (exists a', ATOP <= a' < 2 ^ 47 /\ a = shad a')) -> wb asegs m a = true -> wb asegs m' a = true) ->
  op_holds OPS id args m' mo.
Hypothesis OPS_fp_other : forall id args a, id <> HEAP_ID -> Exists (fun iv => fst iv <= a < snd iv) (op_fp OPS id args) ->
  in_ranges (aci AI) a \/ (exists a', in_ranges (aci AI) a' /\ a = shad a') \/ (exists a', ATOP <= a' < 2 ^ 47 /\ a = shad a').
Variable OTHER : Model -> Model -> Prop.
Hypothesis OPS_mo_other : forall id args m mo mo', id <> HEAP_ID -> OTHER mo mo' -> op_holds OPS id args m mo -> op_holds OPS id args m mo'.
Hypothesis OPS_cov0_img : forall a, (exists seg, find_segment asegs a 1 = Some seg) -> op_cov0 OPS a.

Hypothesis Cw_ghost_grow_f : forall kd md ca LB ws m b n, kd = K_FRAMEz \/ kd = K_FTWINz -> cw_holds Cw md ca LB ws m ->
  (forall a, in_iv (b, n) a -> ~ in_user LB a) -> cw_holds Cw md ca ((b, n) :: LB) (ws ++ [Win b n kd]) m.

Definition live_stmt (E : env) (st : sstate) (ms : machine_state) (L : alayout) (RNG : footprint) (sta : astate) (LBa LBk : list ablock) : Prop :=
  forall (W : wit) nn rest wnl aw LB mo, wit_of W L RNG sta LBa -> aw_realW AI ACCT UNIV aw LB (ms_mem ms) mo W -> ties W (wins_of E nn rest) ->
    (exists md A nw, find_op HEAP_ID (s_ops st) = Some (VL md :: A :: VL nw :: rest) /\ wt nw = false /\ nn = Z.to_nat (to_Z (wl nw)) /\ (3 * nn <= length rest)%nat) ->
    CtrA.nonstack_windows nn rest = Some wnl ->
    forall b, vis W b -> In b LBk.

Lemma sm_post_ok : forall st E ms mo cls r hargs wnl st1 h1 h2 (L : alayout) (RNG : footprint) (sta : astate) (LBa : list ablock) (aw : word)
    (F : Z) (R' : bvmap 5 word) (m' : amem) (mo' : Model) (LBk : list ablock),
  st_ok asegs OPS E st ms mo -> call_pre st = Some r -> ActrA.forget_stack_below_sp_g st = Some st1 ->
  CtrPre.acallG AI ACCT UNIV Cw E st ms mo r hargs wnl L RNG sta LBa aw ->
  PrimInt63.leb cls 2%uint63 = true ->
  heap_add_window hargs (VP (s_next (clobber st1)) wzero) (VL (wlit (sm_usz cls))) (VL ActrB.K_FRAME) = Some h1 ->
  heap_add_window h1 (VP (PrimInt63.add (s_next (clobber st1)) 1%uint63) wzero) (VL (wlit (sm_tlen cls))) (VL ActrB.K_FTWIN) = Some h2 ->
  let R := ms_regs ms in let sp := bv_unsigned (AP.getr R 2) in let c := to_Z cls in let n := fsize c in let fb := mkABlock (ABFake c) F n in

  (forall rg, In rg CtrFrame.kept_regsA -> AP.getr R' rg = AP.getr R rg) -> AP.getr R' 10%bv = Z_to_bv 64 F ->
  AM.mem_inv asegs m' -> stk asegs m' (CtrPre.sp_lo E st) sp ->
  aheap_pres (aci AI) LBk sp (ms_mem ms) m' ->
  twins_pres LBa (ms_mem ms) m' ->
  AHEAP AI L RNG sta (fb :: LBk) m' -> ACCT aw L RNG sta (fb :: LBk) mo' ->
  (forall b, In b LBk -> In b LBa) -> live_stmt E st ms L RNG sta LBa LBk ->
  F mod 64 = 0 ->
  AS.rw_cells asegs m' (F + 24) [C8 (AP.getr R 2)] ->
  (forall g, 0 <= g < n / 8 -> m' (AM.wa (shad F + g)) = Some (Z_to_bv 8 0)) ->
  (exists flg, AM.bytes_at asegs m' (F + n - 8) (AM.le8 (Z_to_bv 64 flg)) /\ flag_law AI L fb flg) ->
  op_minv OPS mo' -> OTHER mo mo' ->
  exists E1, env_ext (s_next st) E E1 /\ st_ok asegs OPS E1 (sm_post st st1 r cls h2) (CtrFrame.ms' ms r R' m') mo'.
Proof.
  intros st E ms mo cls r hargs wnl st1 h1 h2 L RNG sta LBa aw F R' m' mo' LBk HS CP FS CF C2 H1 H2 R sp c n fb
         KEPT A0' MINV' STK' PRES TWP AH' AC' KEEP1 LIVE F64 RSW ZSH FLW MINVo OTH.
  destruct CF as (LB & ks & offs & rss & ksp & nn & md & A & nw & rest & SPR & Hksp & SPE & K16 & LOSP & FLOOR & Hf & Hc & Eh & Tnw & Nn & Ln & N255
                  & NW & AN & AJ & TS & WF & HC & AWden & (W & WOF & ARW & TI)).
  destruct (HeapCtr.call_pre_inv st r CP) as (FOK & _).
  destruct (cls_lits cls C2) as (SZ & USZ & TLEN & NCASES). fold c in SZ, USZ, TLEN, NCASES. fold n in SZ, USZ, TLEN, NCASES.
  pose proof atop_range as ATR.
  pose proof WOF as WOF0. destruct WOF as (E1 & E2 & E3 & E4). pose proof ARW as [HWW EMW].
  assert (FF : is_fake fb) by (exists c; reflexivity).

  destruct (AI_fake L RNG sta (fb :: LBk) m' fb AH' ltac:(left; reflexivity) FF) as (BKF & HIF & A8F & N8F & NPF & WRF & WRS).
  cbn [ab_addr ab_size fb] in BKF, HIF, A8F, N8F, NPF, WRF, WRS.
  assert (BKL : (AIMG_HI <= F /\ F + n <= KLS) \/ (0x10007fff8000 <= F /\ F + n <= ATOP)) by (unfold ablk in BKF; lia).

  assert (KEEP2 : forall b, vis W b -> In b LBk).
  { apply (LIVE W nn rest wnl aw LB mo WOF0 ARW TI); [| exact NW]. exists md, A, nw. rewrite <- Eh. auto. }

  destruct (aw_real_frame_in AI ACCT UNIV AI_fake aw aw LB (ms_mem ms) mo W RNG sta c F n LBk m' mo' sp ARW
              ltac:(rewrite E1; exact AH') ltac:(rewrite E1; exact AC') PRES ltac:(unfold FRAME_MAX; lia)
              ltac:(intros b Hb; rewrite E4; exact (KEEP1 b Hb)) KEEP2 ltac:(rewrite E1; exact FLW) ltac:(rewrite E4; exact TWP)) as (AR1 & VF1 & DJ1 & DJ2).
  set (W1 := mkWit (w_L W) RNG sta (fb :: LBk) (w_T W) (List.filter (fun b => if in_dec ablock_eq_dec b LBk then true else false) (w_FA W)) m' (w_zc W)) in *.
  set (LB1 := (F, n - 8) :: (shad F, shlen n) :: LB) in *.
  assert (NINF : ~ In fb LBk).
  { pose proof (AI_blocks_nodup AI _ _ _ _ _ AH') as ND'. apply NoDup_cons_iff in ND' as [NIN _]. exact NIN. }

  assert (STB : forall a, 0 <= a < 2 ^ 64 -> CtrFrame.stableA AI ms LB a -> m' (AM.wa a) = ms_mem ms (AM.wa a)).
  { intros a Ha ST. pose proof HWW as (_ & HT & _).
    destruct (LB_classify AI ACCT UNIV AI_fake W aw LB (ms_mem ms) mo HWW) as (KU & KT).
    apply (aw_real_stable AI ACCT UNIV AI_fake aw LB (ms_mem ms) mo W RNG sta (fb :: LBk) m' LBk LB sp LBa TWP ltac:(intros b Hb _ _; rewrite <- E4; exact Hb) ARW).
    - rewrite E1. exact AH'.
    - exact PRES.
    - intros v Hv UB P. destruct (KU v Hv UB P) as (b & Vb & ->). exists b. split; [exact (KEEP2 b Vb)| reflexivity].
    - intros v Hv NUB. destruct (KT v Hv NUB) as [(b & Hb & ->)|(b & Vb & ->)].
      + left. exists b. destruct (HT b Hb) as [HbL HH]. destruct (twin_T_facts AI ACCT UNIV W aw LB (ms_mem ms) mo b HWW Hb) as (_ & VB & _).
        split; [exact HbL|]. split; [right; exact (KEEP2 b VB)|]. split; [exact HH| reflexivity].
      + right. exists b. split; [exact (proj1 (proj1 Vb))|]. split; [exact (KEEP2 b (proj1 Vb))|]. split; [exact (proj2 Vb)| reflexivity].
    - exact Ha.
    - exact ST. }
  set (Fv := CtrPost.cfvA R' (Z_to_bv 64 F) (Z_to_bv 64 (shad F))).
  set (Gv := fun (_ : Z) (o : Z) => match m' (AM.wa (F + o)) with Some b => b | None => Z_to_bv 8 0 end).
  set (E' := CtrFrame.E' E st Fv Gv).
  exists E'. split; [apply CtrFrame.EXT|].

  set (kf := addn (s_next st) 15). set (shf := addn (s_next st) 16).
  destruct (CtrFrame.NX st FOK) as (_ & NXP & NXB). pose proof (int_range (s_next st)) as RNX. rewrite two63_eq in RNX.
  assert (KFZ : to_Z kf = to_Z (s_next st) + 15) by (unfold kf; rewrite addn_Z; [lia| rewrite wB_two63, two63_eq; lia]).
  assert (SHZ : to_Z shf = to_Z (s_next st) + 16) by (unfold shf; rewrite addn_Z; [lia| rewrite wB_two63, two63_eq; lia]).
  assert (KFE : s_next (clobber st1) = kf).
  { destruct (clobber_fields st1) as (_ & _ & _ & _ & _ & _ & _ & NXc). destruct (CtrFrame.st1_fields st st1 FS) as (_ & _ & _ & _ & _ & _ & _ & NX1).
    rewrite NXc, NX1. symmetry. apply addn_lit; [reflexivity| rewrite wB_two63, two63_eq; lia]. }
  assert (SHE : PrimInt63.add kf 1%uint63 = shf).
  { apply Uint63.to_Z_inj. rewrite add_Z by (rewrite KFZ; change (to_Z 1%uint63) with 1; rewrite wB_two63, two63_eq; lia).
    rewrite KFZ, SHZ. change (to_Z 1%uint63) with 1. lia. }
  assert (KFNZ : PrimInt63.eqb kf 0%uint63 = false) by (apply Uint63.eqb_false_spec; intros X; rewrite X in KFZ; change (to_Z 0%uint63) with 0 in KFZ; lia).
  assert (SHNZ : PrimInt63.eqb shf 0%uint63 = false) by (apply Uint63.eqb_false_spec; intros X; rewrite X in SHZ; change (to_Z 0%uint63) with 0 in SHZ; lia).
  unfold AIMG_HI, KLS in BKL. assert (FR64 : 0x62f000 <= F /\ F + n < 2 ^ 47) by lia.
  destruct (fsh_band F n BKF HIF A8F N8F ltac:(lia)) as (FS1 & FS2 & FS3 & FS4 & FS5).
  assert (EVF : bv_unsigned (ev E' kf) = F).
  { unfold E', kf. rewrite (CtrFrame.ev_E'_fresh E st FOK Fv Gv 15 ltac:(lia)). change (Fv (Z.of_nat 15)) with (Z_to_bv 64 F).
    apply Z_to_bv_small. unfold bv_modulus, two64. lia. }
  assert (EVS : bv_unsigned (ev E' shf) = shad F).
  { unfold E', shf. rewrite (CtrFrame.ev_E'_fresh E st FOK Fv Gv 16 ltac:(lia)). change (Fv (Z.of_nat 16)) with (Z_to_bv 64 (shad F)).
    apply Z_to_bv_small. unfold bv_modulus, two64. lia. }
  pose proof (CtrFrame.HS' OPS E st ms mo HS FOK Fv Gv) as HSp. fold E' in HSp.
  set (spv := getr st X2).
  assert (DSP : den E' spv = AP.getr R 2%bv).
  { unfold E'. rewrite (CtrFrame.den_E' E st Fv Gv spv (CtrFrame.reg_below st FOK X2)). unfold spv, R.
    rewrite <- (GlueA.getr_RA asegs OPS E st ms mo HS X2). reflexivity. }

  assert (RAWS : forall a, 0x62f000 <= a < 2 ^ 64 -> wb asegs m' a = true -> exists b, m' (Z_to_bv 64 a) = Some b).
  { intros a Ha Wb. unfold wb, wview in Wb. destruct (m' (Z_to_bv 64 a)) as [b|]; [eauto|]. exfalso.
    rewrite Z_to_bv_unsigned, bv_wrap_small in Wb by (unfold bv_modulus; lia). rewrite (SmLib.no_seg_above a (proj1 Ha)) in Wb. discriminate Wb. }
  assert (VALF : forall a, F <= a < F + n -> (exists b, m' (Z_to_bv 64 a) = Some b) /\ wb asegs m' a = true /\ find_segment asegs a 1 = None).
  { intros a Ha. destruct WRF as (_ & _ & WV).
    assert (WBI : wb asegs m' a = true) by (apply (GlueA.wb_wviewA asegs); replace a with (F + (a - F)) by lia; apply WV; lia).
    split; [apply RAWS; [lia| exact WBI]|]. split; [exact WBI| apply SmLib.no_seg_above; lia]. }
  assert (SHN : shlen n = n / 8) by (unfold shlen; rewrite Z.shiftr_div_pow2 by lia; reflexivity).
  assert (VALS : forall a, shad F <= a < shad F + n / 8 -> wb asegs m' a = true /\ find_segment asegs a 1 = None).
  { intros a Ha. destruct WRS as (_ & _ & WV). rewrite SHN in WV.
    split; [apply (GlueA.wb_wviewA asegs); replace a with (shad F + (a - shad F)) by lia; apply WV; lia| apply SmLib.no_seg_above; lia]. }
  set (fr0 := Region 0%uint63 (VL (wlit (sm_usz cls))) true BGUnk IMap.empty).
  assert (EHF : hiZ E' fr0 = n - 8).
  { unfold hiZ, fr0. cbn [rg_hi den]. rewrite W64Proofs.wbv_unsigned, W64Proofs.wlit_ok. exact USZ. }
  assert (RO0 : region_ok asegs (s_priv st) E' m' kf fr0).
  { assert (EL : loZ fr0 = 0) by reflexivity.
    constructor; rewrite ?EVF, ?EHF, ?EL.
    - apply IMap.bst_empty.
    - intros _. unfold two64. lia.
    - intros _ a Ha. destruct (VALF a ltac:(lia)) as ((b & Hb) & WBI & SEG).
      split; [unfold rb; rewrite Hb; discriminate|]. split; [intros _; exact WBI| exact SEG].
    - intros g gr Hg. cbn [fr0 rg_cells] in Hg. rewrite IMap.find_empty in Hg. discriminate Hg.
    - intros g gr c0 i Hg. cbn [fr0 rg_cells] in Hg. rewrite IMap.find_empty in Hg. discriminate Hg.
    - intros o Ho1 _ _. specialize (Ho1 KFNZ). unfold bg_byte. cbn [fr0 rg_bg]. unfold E', CtrFrame.E'. rewrite eg_above by (rewrite KFZ; lia).
      rewrite KFZ. replace (to_Z (s_next st) + 15 - to_Z (s_next st)) with 15 by lia.
      destruct (VALF (F + o) ltac:(lia)) as ((b & Hb) & _). unfold rb, Gv, AM.wa. rewrite Hb. reflexivity. }
  assert (CWR : can_write asegs (s_facts st) (s_priv st) kf fr0 24%uint63 8%uint63 = true).
  { unfold can_write, can_read. rewrite KFNZ. unfold fr0. cbn [rg_w rg_lo rg_hi]. destruct (cls_cases cls C2) as [->|[->| ->]]; vm_compute; reflexivity. }
  destruct (MemP.region_store_sound asegs (s_priv st) E' m' (s_facts st) kf fr0 24%uint63 8%uint63 spv
              (so_facts _ _ _ _ _ _ HSp) (so_zero _ _ _ _ _ _ HSp) RO0 ltac:(right; right; right; reflexivity) CWR) as (_ & RO1 & ELo & EHi & EW & EBg & _).
  assert (ROF : region_ok asegs (s_priv st) E' m' kf (sm_fr cls spv)).
  { apply (MemP.region_ok_frame asegs (s_priv st) E' _ m' kf _ (so_zero _ _ _ _ _ _ HSp) RO1). intros a Ha _ _.
    unfold addrZ. rewrite EVF, DSP. change (keyZ 24%uint63) with 24. symmetry.
    replace (F + 24) with (F + 24 + Z.of_nat 0) by lia.
    apply (SmLib.ghost_c8 m' (F + 24) [C8 (AP.getr R 2%bv)] 0 (AP.getr R 2%bv) RSW eq_refl ltac:(lia)). }
  assert (EHT : hiZ E' (sm_tw cls) = n / 8).
  { unfold hiZ, sm_tw. cbn [rg_hi den]. rewrite W64Proofs.wbv_unsigned, W64Proofs.wlit_ok. exact TLEN. }
  assert (ROT : region_ok asegs (s_priv st) E' m' shf (sm_tw cls)).
  { assert (EL : loZ (sm_tw cls) = 0) by reflexivity.
    constructor; rewrite ?EVS, ?EHT, ?EL.
    - apply IMap.bst_empty.
    - intros _. unfold two64. lia.
    - intros _ a Ha. destruct (VALS a ltac:(lia)) as (WBI & SEG).
      split; [unfold rb; replace a with (shad F + (a - shad F)) by lia; unfold AM.wa in ZSH; rewrite (ZSH (a - shad F) ltac:(lia)); discriminate|].
      split; [intros _; exact WBI| exact SEG].
    - intros g gr Hg. cbn [sm_tw rg_cells] in Hg. rewrite IMap.find_empty in Hg. discriminate Hg.
    - intros g gr c0 i Hg. cbn [sm_tw rg_cells] in Hg. rewrite IMap.find_empty in Hg. discriminate Hg.
    - intros o Ho1 _ _. specialize (Ho1 SHNZ). unfold bg_byte. cbn [sm_tw rg_bg]. unfold rb. unfold AM.wa in ZSH. rewrite (ZSH o ltac:(lia)). reflexivity. }

  set (WFr := Win F (n - 8) K_FRAMEz). set (WTw := Win (shad F) (shlen n) K_FTWINz).
  set (ws' := (wins_of E nn rest ++ [WFr]) ++ [WTw]).
  assert (NS : to_Z (wl nw) + 2 < two63).
  { pose proof (Uint63.to_Z_bounded (wl nw)) as B. unfold two63. rewrite Nn in N255. lia. }
  rewrite KFE in H1. rewrite KFE, SHE in H2.
  destruct (CtrPost.add_window_facts E' md A nw rest nn (VP kf wzero) (VL (wlit (sm_usz cls))) (VL ActrB.K_FRAME) Tnw Nn Ln ltac:(lia))
    as (AW1 & T1 & N1 & L1 & WS1 & SK1).
  set (rest1 := firstn (3 * nn) rest ++ [VP kf wzero; VL (wlit (sm_usz cls)); VL ActrB.K_FRAME] ++ skipn (3 * nn) rest) in *.
  set (nw1 := wadd nw wone) in *.
  destruct (CtrPost.add_window_facts E' md A nw1 rest1 (S nn) (VP shf wzero) (VL (wlit (sm_tlen cls))) (VL ActrB.K_FTWIN) T1 N1 L1
              ltac:(destruct (wadd_one_small nw Tnw ltac:(lia)) as [_ X]; fold nw1 in X; lia)) as (AW2 & T2 & N2 & L2 & WS2 & SK2).
  set (rest2 := firstn (3 * S nn) rest1 ++ [VP shf wzero; VL (wlit (sm_tlen cls)); VL ActrB.K_FTWIN] ++ skipn (3 * S nn) rest1) in *.
  set (nw2 := wadd nw1 wone) in *.
  rewrite Eh in H1. rewrite AW1 in H1. injection H1 as <-. rewrite AW2 in H2. injection H2 as <-.
  pose proof (CtrFrame.rest_below st FOK rest hargs md A nw Hf Eh) as RBL.
  assert (ABL : sv_vars_below (s_next st) A = true).
  { pose proof (CtrFrame.hargs_below st FOK hargs Hf) as X. rewrite Eh in X. cbn [forallb] in X. apply andb_prop in X as [_ X]. apply andb_prop in X as [X _]. exact X. }
  assert (DECN : decode (map (den E') (VL md :: A :: VL nw2 :: rest2)) = Some (w2Z md, aw, ws', map (den E) (skipn (3 * nn) rest))).
  { rewrite (decode_hargs E' md A nw2 rest2 (S (S nn)) T2 N2 L2). rewrite WS2, WS1, SK2, SK1.
    unfold E'. rewrite (CtrFrame.wins_of_E' E st Fv Gv nn rest RBL), (CtrFrame.map_den_E' E st Fv Gv _ (CtrPost.forallb_skipn _ (3 * nn) rest RBL)).
    rewrite (CtrFrame.den_E' E st Fv Gv A ABL), <- AWden. fold E'.
    assert (C2' : Win (bv_unsigned (den E' (VP kf wzero))) (bv_unsigned (den E' (VL (wlit (sm_usz cls))))) (bv_unsigned (den E' (VL ActrB.K_FRAME))) = WFr).
    { unfold WFr. rewrite HeapCtr.den_VPz, EVF. cbn [den]. rewrite W64Proofs.wbv_unsigned, W64Proofs.wlit_ok, USZ. reflexivity. }
    assert (C3' : Win (bv_unsigned (den E' (VP shf wzero))) (bv_unsigned (den E' (VL (wlit (sm_tlen cls))))) (bv_unsigned (den E' (VL ActrB.K_FTWIN))) = WTw).
    { unfold WTw. rewrite HeapCtr.den_VPz, EVS. cbn [den]. rewrite W64Proofs.wbv_unsigned, W64Proofs.wlit_ok, TLEN, SHN. reflexivity. }
    rewrite C2', C3'. reflexivity. }

  set (LB2 := (shad F, shlen n) :: (F, n - 8) :: LB).
  assert (HW2 : aw_holds_w AI ACCT UNIV W1 aw LB2 m' mo').
  { destruct AR1 as [(AHx & HTx & NDx & HFAx & NDFx & HLBx & RESTx) _].
    split; [exact AHx|]. split; [exact HTx|]. split; [exact NDx|]. split; [exact HFAx|]. split; [exact NDFx|]. split; [| exact RESTx].
    assert (PERM : forall v, In v LB2 <-> In v LB1) by (intros v; unfold LB1, LB2; cbn [In]; tauto).
    intros v. split; [intros Hv; apply (proj1 (HLBx v)); apply PERM; exact Hv| intros X; apply PERM; exact (proj2 (HLBx v) X)]. }
  assert (HOLDN : op_holds OPS HEAP_ID (map (den E') (VL md :: A :: VL nw2 :: rest2)) m' mo').
  { rewrite OPS_holds1. exists (w2Z md), aw, ws', (map (den E) (skipn (3 * nn) rest)), LB2, W1.
    split; [exact DECN|]. split; [exact HW2|]. split; [| split].
    -
      apply Forall_app. split; [apply Forall_app; split|].
      + apply (CtrPost.windows_wf_mono _ LB LB2 _ WF). intros b Hb. right; right. exact Hb.
      + constructor; [|constructor]. unfold window_wf, WFr, w_iv. cbn [w_lo w_len w_kind]. split; [lia|]. split; [lia|]. split; [unfold two64; lia|].
        right; right. split; [unfold K_SUB, K_FRAMEz; lia|]. exists (F, n - 8). split; [right; left; reflexivity|]. intros a Ha. exact Ha.
      + constructor; [|constructor]. unfold window_wf, WTw, w_iv. cbn [w_lo w_len w_kind]. split; [lia|]. split; [lia|]. split; [unfold two64; lia|].
        right; right. split; [unfold K_SUB, K_FTWINz; lia|]. exists (shad F, shlen n). split; [left; reflexivity|]. intros a Ha. exact Ha.
    -
      assert (HC1 : cw_holds Cw (w2Z md) (map (den E) (skipn (3 * nn) rest)) LB (wins_of E nn rest) m').
      { apply (cw_frame Cw _ _ _ _ (ms_mem ms) m' HC). intros a Ha U _.
        pose proof (STB a ltac:(unfold two64 in Ha; lia) ltac:(right; right; exact U)) as E0. unfold AM.wa in E0. symmetry. exact E0. }
      pose proof (Cw_ghost_grow_f K_FRAMEz _ _ _ _ m' F (n - 8) ltac:(left; reflexivity) HC1 DJ1) as HC2.
      apply (Cw_ghost_grow_f K_FTWINz _ _ _ _ m' (shad F) (shlen n) ltac:(right; reflexivity) HC2).
      intros a Ha U. apply in_ivs_cons in U as [U|U]; [| exact (DJ2 a Ha U)].
      unfold in_iv in Ha, U. cbn [fst snd] in Ha, U. lia.
    -
      apply (ties_frame_in W W1 (wins_of E nn rest) ws' fb TI eq_refl eq_refl FF).
      + exact (frame_in_visf AI ACCT UNIV aw LB (ms_mem ms) mo W RNG sta c F n LBk m' ARW ltac:(rewrite E1; exact AH')
                 ltac:(intros b Hb; rewrite E4; exact (KEEP1 b Hb)) KEEP2).
      + intros w. unfold ws'. cbn [ab_addr ab_size fb]. fold WFr WTw. split.
        * intros H. apply in_app_or in H as [H|[<-|[]]]; [apply in_app_or in H as [H|[<-|[]]]; [left; exact H| right; left; reflexivity]| right; right; reflexivity].
        * intros [H|[->| ->]]; [apply in_or_app; left; apply in_or_app; left; exact H| apply in_or_app; left; apply in_or_app; right; left; reflexivity| apply in_or_app; right; left; reflexivity].
      +
        intros b HB [Hb NF]. unfold W1 in Hb, NF. cbn [w_LBa w_FA] in Hb, NF. destruct Hb as [<-|Hb].
        * exfalso. destruct HB as [p HP]. cbn [fb ab_kind] in HP. discriminate HP.
        * split; [rewrite E4; exact (KEEP1 b Hb)|]. intros X. apply NF. apply filter_In. split; [exact X|].
          destruct (in_dec ablock_eq_dec b LBk); [reflexivity| contradiction].
      +
        destruct TI as (_ & _ & _ & _ & _ & _ & _ & _ & _ & GA & _).
        apply (ghost_apart_new_ghosts (wins_of E nn rest) ws' LB _ WF GA). intros w Hw. unfold ws' in Hw.
        apply in_app_or in Hw as [Hw|[<-|[]]]; [apply in_app_or in Hw as [Hw|[<-|[]]]; [left; exact Hw|]|].
        -- right. split; [unfold WFr; cbn [w_kind]; unfold K_FRAMEz, K_BLOCK; lia|]. intros _ a Ha. unfold WFr, w_iv in Ha. cbn [w_lo w_len] in Ha. exact (DJ1 a Ha).
        -- right. split; [unfold WTw; cbn [w_kind]; unfold K_FTWINz, K_BLOCK; lia|]. intros _ a Ha. unfold WTw, w_iv in Ha. cbn [w_lo w_len] in Ha. exact (DJ2 a Ha).
      +
        intros P. unfold W1. cbn [w_st]. rewrite <- E3. exact P. }

  pose proof (aw_real_holds AI ACCT UNIV _ _ _ _ _ ARW) as AWH.
  assert (SBV : forall a, 0 <= a < 2 ^ 64 -> CtrFrame.stableA AI ms LB a ->
            rb asegs m' a = rb asegs (ms_mem ms) a /\ (wb asegs (ms_mem ms) a = true -> wb asegs m' a = true)).
  { intros a Ha ST. pose proof (STB a Ha ST) as EQ. split.
    - unfold rb. unfold AM.wa in EQ. rewrite EQ. reflexivity.
    - intros Wb. apply (GlueA.wb_wviewA asegs). apply (GlueA.wb_wviewA asegs) in Wb. rewrite (wview_ext1 m' (ms_mem ms) _ EQ). exact Wb. }
  assert (SBO : forall o a, In o (s_ops st) -> not_id HEAP_ID o -> 0 <= a < two64 ->
            Exists (fun iv => fst iv <= a < snd iv) (op_fp OPS (op_id o) (map (den E') (op_args o))) -> m' (Z_to_bv 64 a) = ms_mem ms (Z_to_bv 64 a)).
  { intros o a Ho NI Ha FP. unfold not_id in NI. apply Uint63.eqb_false_spec in NI.
    destruct (OPS_fp_other _ _ a NI FP) as [RR|[(a' & RR & ->)|(a' & STK & ->)]].
    - pose proof (STB a ltac:(unfold two64 in Ha; lia) ltac:(right; left; exact RR)) as E0. unfold AM.wa in E0. exact E0.
    - pose proof (proj1 (PRES (shad a') ltac:(unfold two64 in Ha; lia) ltac:(right; right; right; exists a'; split; [right; left; exact RR| reflexivity]))) as E0.
      unfold AM.wa in E0. exact E0.
    -
      pose proof (proj1 (PRES (shad a') ltac:(unfold two64 in Ha; lia) ltac:(right; right; right; exists a'; split; [left; exact STK| reflexivity]))) as E0.
      unfold AM.wa in E0. exact E0. }
  assert (WBM : forall a, 0 <= a < two64 -> (in_ranges (aci AI) a \/ (exists a', in_ranges (aci AI) a' /\ a = shad a') \/ (exists a', ATOP <= a' < 2 ^ 47 /\ a = shad a')) ->
            wb asegs (ms_mem ms) a = true -> wb asegs m' a = true).
  { intros a Ha CC Wb. apply (GlueA.wb_wviewA asegs). apply (GlueA.wb_wviewA asegs) in Wb.
    refine (proj2 (PRES a ltac:(unfold two64 in Ha; lia) _) Wb).
    destruct CC as [CC|[(a' & CC & ->)|(a' & CC & ->)]]; [right; left; exact CC| |]; right; right; right; exists a'; (split; [| reflexivity]); [right; left; exact CC| left; exact CC]. }
  assert (WINKW : forall k0 len kd, True -> CtrA.win_lookup wnl k0 = Some (len, kd) ->
            forall a, bv_unsigned (ev E k0) <= a < bv_unsigned (ev E k0) + bv_unsigned (den E len) -> in_user LB a).
  { intros k0 len kd _ WL a Ha.
    destruct (HeapCtrB.nonstack_windows_In E nn rest wnl k0 len kd NW (HeapCtrB.win_lookup_In _ _ _ _ WL)) as (_ & _ & KD & INW).
    pose proof (proj1 (Forall_forall _ _) WF _ INW) as (W1' & W2' & W3' & [[KS0 _]|[[KB B]|[KS2 (b & Hb & SUB)]]]); unfold w_iv in *; cbn [w_kind w_lo w_len] in *.
    - exfalso. exact (KD KS0).
    - apply in_ivs_In. eexists. split; [exact B|]. unfold in_iv. cbn [fst snd]. lia.
    - apply in_ivs_In. exists b. split; [exact Hb|]. apply SUB. unfold in_iv. cbn [fst snd]. lia. }

  assert (SBT : forall a, 0 <= a < 2 ^ 64 -> sh_cov a -> in_based E (s_regs st) a ->
            rb asegs m' a = rb asegs (ms_mem ms) a /\ (wb asegs (ms_mem ms) a = true -> wb asegs m' a = true)).
  { intros a Ha SC _.
    assert (CA : aclient_addr (aci AI) LBk sp a).
    { destruct SC as [(a' & RR & ->)|(v & Hv & RR)].
      - right; right; right. exists a'. split; [left; exact RR| reflexivity].
      - destruct (IMGSH_aci v a Hv RR) as (a' & INA & ->). right; right; right. exists a'. split; [right; left; exact INA| reflexivity]. }
    destruct (PRES a Ha CA) as [EQ WV]. split.
    - unfold rb. unfold AM.wa in EQ. rewrite EQ. reflexivity.
    - intros Wb. apply (GlueA.wb_wviewA asegs). apply (GlueA.wb_wviewA asegs) in Wb. exact (WV Wb). }

  pose proof STK' as STK2.
  set (newR := [(kf, sm_fr cls spv); (shf, sm_tw cls)]).
  set (NEWSET := fun a : Z => in_iv (F, n - 8) a \/ in_iv (shad F, shlen n) a).
  assert (HIFR : hiZ E' (sm_fr cls spv) = n - 8 /\ loZ (sm_fr cls spv) = 0 /\ rg_w (sm_fr cls spv) = true).
  { unfold sm_fr. fold fr0. unfold hiZ, loZ. rewrite EHi, ELo, EW. split; [exact EHF| split; reflexivity]. }
  destruct HIFR as (HIFR & LOFR & WFR).
  assert (NEWRANGE : forall k rg a, In (k, rg) newR -> bv_unsigned (ev E' k) + loZ rg <= a < bv_unsigned (ev E' k) + hiZ E' rg -> NEWSET a).
  { intros k rg a [X|[X|[]]] Ha; injection X as <- <-.
    - left. rewrite EVF, LOFR, HIFR in Ha. unfold in_iv. cbn [fst snd]. lia.
    - right. rewrite EVS, EHT in Ha. change (loZ (sm_tw cls)) with 0 in Ha. unfold in_iv. cbn [fst snd]. lia. }
  assert (NEWLOW : forall a, NEWSET a -> AIMG_HI <= a < ATOP + 4096 /\ ~ in_user LB a).
  { intros a [X|X]; (split; [unfold in_iv in X; cbn [fst snd] in X; unfold AIMG_HI; lia|]); [exact (DJ1 a X)| exact (DJ2 a X)]. }
  assert (NEWNOSH : forall a, NEWSET a -> ~ (0x7fff8000 <= a < 0x800bde00)).
  { intros a [X|X] Y; unfold in_iv in X; cbn [fst snd] in X; [lia|].
    assert (0x800bde00 <= shad F) by (unfold shad, ASHOFF; rewrite Z.shiftr_div_pow2 by lia; change (2 ^ 3) with 8; Z.div_mod_to_equations; lia). lia. }
  assert (NEWNOSTK : forall a, NEWSET a -> ~ (exists a', ATOP <= a' < 2 ^ 47 /\ a = shad a')).
  { intros a X (a' & RR & ->).
    assert (SHB : shad ATOP <= shad a' < 0x10007fff8000) by (unfold shad, ASHOFF; rewrite !Z.shiftr_div_pow2 by lia; change (2 ^ 3) with 8; Z.div_mod_to_equations; lia).
    assert (SHT : shad F + shlen n <= shad ATOP).
    { rewrite SHN. unfold shad, ASHOFF. rewrite !Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8. clear - HIF A8F N8F NCASES FR64. Z.div_mod_to_equations. lia. }
    assert (KLSB : 0x7fff7000 < shad ATOP) by (unfold shad, ASHOFF; rewrite Z.shiftr_div_pow2 by lia; change (2 ^ 3) with 8; clear - ATR; Z.div_mod_to_equations; lia).
    destruct X as [X|X]; unfold in_iv in X; cbn [fst snd] in X; lia. }
  assert (NEWDISJ : forall k1 r1 k2 r2 a, In (k1, r1) newR -> In (k2, r2) newR -> k1 <> k2 -> (rg_w r1 = true \/ rg_w r2 = true) ->
            ~ (bv_unsigned (ev E' k1) + loZ r1 <= a < bv_unsigned (ev E' k1) + hiZ E' r1 /\ bv_unsigned (ev E' k2) + loZ r2 <= a < bv_unsigned (ev E' k2) + hiZ E' r2)).
  { intros k1 r1 k2 r2 a [X1|[X1|[]]] [X2|[X2|[]]] NE _ [A1 A2]; injection X1 as <- <-; injection X2 as <- <-; try (apply NE; reflexivity);
      rewrite ?EVF, ?EVS, ?LOFR, ?HIFR, ?EHT in A1, A2; change (loZ (sm_tw cls)) with 0 in *; lia. }
  assert (NEWND : List.NoDup (map fst newR)).
  { cbn [map fst newR]. constructor; [intros [X|[]]; rewrite X in SHZ; lia| constructor; [intros []| constructor]]. }
  assert (NEWFRESH : forall k rg, In (k, rg) newR -> PrimInt63.eqb k 0%uint63 = false).
  { intros k rg [X|[X|[]]]; injection X as <- <-; apply (CtrFrame.fresh_nz st ms FOK r); lia. }
  assert (NEWOK : forall k rg, In (k, rg) newR -> region_ok asegs (s_priv st) E' m' k rg).
  { intros k rg [X|[X|[]]]; injection X as <- <-; [exact ROF| exact ROT]. }

  assert (INWS : forall ws0 a, in_ws (heap_ws (wins_of E nn rest)) a \/ in_iv (w_iv WFr) a \/ in_iv (w_iv WTw) a -> ws0 = ws' -> in_ws (heap_ws ws0) a).
  { intros ws0 a X ->. unfold in_ws, heap_ws in *. apply in_ivs_In.
    destruct X as [X|[X|X]].
    - apply in_ivs_In in X as (v & Hv & Hin). exists v. split; [| exact Hin]. apply in_map_iff in Hv as (w & <- & Hw). apply in_map.
      apply filter_In in Hw as [Hw K]. apply filter_In. split; [| exact K]. apply in_or_app. left. apply in_or_app. left. exact Hw.
    - exists (w_iv WFr). split; [| exact X]. apply in_map. apply filter_In. split; [apply in_or_app; left; apply in_or_app; right; left; reflexivity| reflexivity].
    - exists (w_iv WTw). split; [| exact X]. apply in_map. apply filter_In. split; [apply in_or_app; right; left; reflexivity| reflexivity]. }
  assert (W1p : forall a, NEWSET a -> in_ws (heap_ws ws') a).
  { intros a [X|X]; apply (INWS ws' a); try reflexivity; [right; left; exact X| right; right; exact X]. }
  assert (W3p : forall a, 0 <= a < two64 -> ~ in_ivs IMGX a -> ~ in_ws ws' a ->
            ~ in_ws (wins_of E nn rest) a \/ (find_segment asegs a 1 = None /\ ~ in_based E' (CtrFrame.RgPg st ks rss ksp newR []) a)).
  { intros a _ _ NWS. left. intros X. apply NWS. unfold in_ws, ws' in *. rewrite !map_app. apply in_ivs_app. left. apply in_ivs_app. left. exact X. }
  assert (W4p : forall a, in_based E' (CtrFrame.RgPg st ks rss ksp newR []) a -> in_ws (heap_ws (wins_of E nn rest)) a -> in_ws (heap_ws ws') a).
  { intros a _ X. apply (INWS ws' a); [left; exact X| reflexivity]. }

  set (facts' := ActrB.link_fact shf kf :: FAlign kf 6%uint63 :: FRange kf ActrB.BLK_LO ActrB.BLK_HI :: s_facts st).
  assert (FACTS : facts_hold E' facts').
  { constructor; [| constructor; [| constructor; [| exact (so_facts _ _ _ _ _ _ HSp)]]].
    - unfold ActrB.link_fact. cbn [fact_holds]. rewrite HeapCtr.den_VPz.
      change (den E' (VAlu ALU_ADD (VAlu ALU_SRL (VP kf wzero) (VL (wlit 3%uint63))) (VL ActrB.SBw)))
        with (alu64 ALU_ADD (alu64 ALU_SRL (den E' (VP kf wzero)) (wbv (wlit 3%uint63))) (wbv ActrB.SBw)).
      rewrite HeapCtr.den_VPz. apply bv_eq. unfold alu64, alu. rewrite bv_add_unsigned, bv_shiftr_unsigned, bv_and_unsigned, EVS, EVF.
      replace (bv_unsigned (wbv (wlit 3%uint63))) with 3 by (vm_compute; reflexivity).
      replace (bv_unsigned (Z_to_bv 64 63)) with 63 by (vm_compute; reflexivity).
      change (Z.land 3 63) with 3.
      replace (bv_unsigned (wbv ActrB.SBw)) with 0x7fff8000 by (vm_compute; reflexivity).
      unfold shad, ASHOFF, bv_wrap, bv_modulus. rewrite Z.mod_small; [apply Z.add_comm|]. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8.
      change (2 ^ Z.of_N 64) with (2 ^ 64). clear - FR64 NCASES. Z.div_mod_to_equations. lia.
    - cbn [fact_holds]. rewrite EVF. change (2 ^ to_Z 6%uint63) with 64. exact F64.
    - cbn [fact_holds]. rewrite EVF. replace (w2Z ActrB.BLK_LO) with 0x62f000 by (vm_compute; reflexivity).
      replace (w2Z ActrB.BLK_HI) with (2 ^ 47 - 1) by (vm_compute; reflexivity). lia. }
  assert (DV : den E' (VP kf wzero) = AP.getr R' 10%bv).
  { rewrite HeapCtr.den_VPz, A0'. unfold E', kf. rewrite (CtrFrame.ev_E'_fresh E st FOK Fv Gv 15 ltac:(lia)). reflexivity. }

  assert (SHP : sm_post st st1 r cls (VL md :: A :: VL nw2 :: rest2)
              = SS r (rf_set (s_rf (clobber st1)) X10 (VP kf wzero)) (s_ff st) (s_resv st) (CtrFrame.RgPg st ks rss ksp newR []) facts'
                   (CtrFrame.opsg st (VL md :: A :: VL nw2 :: rest2)) (s_priv st) (PrimInt63.add shf 1%uint63)).
  { unfold sm_post. cbv zeta. rewrite KFE, SHE.
    destruct (clobber_fields st1) as (_ & FF1 & RV1 & RG1 & FS1' & OP1 & PV1 & _).
    destruct (CtrFrame.st1_fields st st1 FS) as (_ & _ & FF0 & RV0 & FS0 & OP0 & PV0 & _).
    rewrite FF1, RV1, RG1, FS1', OP1, PV1, FF0, RV0, FS0, OP0, PV0.
    rewrite (CtrFrame.st1_regs st st1 FS ks offs rss ksp SPR Hksp). reflexivity. }
  rewrite SHP.
  exact (CtrFrame.frame_st_ok AI IMGX IMGX_aci ACCT UNIV OPS AI_fake OPS_fp1 OPS_cov1 OPS_frame_other OPS_fp_other OTHER OPS_mo_other OPS_cov0_img
           E st ms mo HS FOK Fv Gv r st1 CP FS R' m' mo' KEPT (fun x i Hx => CtrPost.cfvA_clob R' _ _ x i Hx) aw LB LB AWH MINV' SBV SBO WBM SBT
           ks offs rss ksp SPR SPE wnl nn rest AJ WF (fun _ => True) WINKW ltac:(intros; exact I) ltac:(intros; exact I) K16 LOSP STK2 FLOOR hargs md A nw Hf Hc Eh Tnw Nn Ln OTH
           newR [] NEWND NEWFRESH (fun _ _ => I) NEWSET NEWOK NEWRANGE NEWLOW NEWNOSH NEWNOSTK NEWDISJ
           (VL md :: A :: VL nw2 :: rest2) (w2Z md) aw ws' (map (den E) (skipn (3 * nn) rest)) DECN HOLDN W1p W3p W4p
           facts' (VP kf wzero) (PrimInt63.add shf 1%uint63) FACTS DV MINVo).
Qed.
End Post.

From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.BothW Require Import BImg.
Module TwinB.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.PropExec OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.MState OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Cells OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Frame OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.ITree OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Nodes.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA.AcctCore OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA.ExecF OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA.ITreeA OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA.NodesA.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.STree OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.AsanCtrl OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.AsanEmbed.
Import AProto.TwinB ABase.TwinB AMalloc_iface.TwinB.
Import AMalloc_iface2.TwinB.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common.RunDraw OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common.ShapeAlg.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.W64 OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Val OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.IMap OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Instr OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.State OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Step OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Plan OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.PlanSound.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Mem.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Heap.Op.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Ctr.Lib OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Ctr.DefsA.
Import Ledger.TwinB Op.TwinB Adeq.TwinB.

Import ListNotations.
Import W64 Val OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Mem.Mem FI St OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Step.Step Plan PlanS CtrLib HeapOp.
Open Scope Z_scope.
Unset Lia Cache.

Import Actr.TwinB.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.W64Proofs OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.ValProofs OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.MemProofs OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.StepSoundBase.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Br.CtrFX.

Import ActrB.TwinB SmShape.TwinB SmWorld.TwinB.
Unset Nia Cache. Unset Nra Cache.
Import ValP MemP CtrFX.
Import ActrA.
Module AP := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.PropExec.
Module AM := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Mem.
Module AS := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Step.

Section Post.
Context {rc : runConstT}.
Variable AI : AMallocIface2.
Variable IMGX : list iv.
Hypothesis IMGX_aci : imgx_ok AI IMGX.
Hypothesis IMGSH_aci : forall v a, In v Op.TwinB.SHLIT -> fst v <= a < snd v -> exists a', in_ranges (aci AI) a' /\ a = shad a'.
Variable ACCT : word -> alayout -> footprint -> astate -> list ablock -> Model -> Prop.
Variable UNIV : list (list Z).
Variable Cw : client_world.
Variable OPS : optable.
Hypothesis AI_fake : AI_fake_law AI.
Hypothesis OPS_holds1 : forall args m mo, op_holds OPS HEAP_ID args m mo <-> heap_holdsX AI ACCT UNIV Cw args m mo.
Hypothesis OPS_fp1 : forall args, op_fp OPS HEAP_ID args = heap_fp IMGX args.
Hypothesis OPS_cov1 : forall args z, op_cov1 OPS HEAP_ID args z <-> Op.TwinB.cov1 HEAP_ID args z.
Hypothesis OPS_frame_other : forall id args m m' mo, id <> HEAP_ID -> op_holds OPS id args m mo ->
  (forall a, 0 <= a < two64 -> Exists (fun iv => fst iv <= a < snd iv) (op_fp OPS id args) -> m (Z_to_bv 64 a) = m' (Z_to_bv 64 a)) ->
  (forall a, 0 <= a < two64 -> (in_ranges (aci AI) a \/ (exists a', in_ranges (aci AI) a' /\ a = shad a') \/ (exists a', ATOP <= a' < 2 ^ 47 /\ a = shad a')) -> wb bsegs m a = true -> wb bsegs m' a = true) ->
  op_holds OPS id args m' mo.
Hypothesis OPS_fp_other : forall id args a, id <> HEAP_ID -> Exists (fun iv => fst iv <= a < snd iv) (op_fp OPS id args) ->
  in_ranges (aci AI) a \/ (exists a', in_ranges (aci AI) a' /\ a = shad a') \/ (exists a', ATOP <= a' < 2 ^ 47 /\ a = shad a').
Variable OTHER : Model -> Model -> Prop.
Hypothesis OPS_mo_other : forall id args m mo mo', id <> HEAP_ID -> OTHER mo mo' -> op_holds OPS id args m mo -> op_holds OPS id args m mo'.
Hypothesis OPS_cov0_img : forall a, (exists seg, find_segment bsegs a 1 = Some seg) -> op_cov0 OPS a.

Hypothesis Cw_ghost_grow_f : forall kd md ca LB ws m b n, kd = K_FRAMEz \/ kd = K_FTWINz -> cw_holds Cw md ca LB ws m ->
  (forall a, in_iv (b, n) a -> ~ in_user LB a) -> cw_holds Cw md ca ((b, n) :: LB) (ws ++ [Win b n kd]) m.

Definition live_stmt (E : env) (st : sstate) (ms : machine_state) (L : alayout) (RNG : footprint) (sta : astate) (LBa LBk : list ablock) : Prop :=
  forall (W : wit) nn rest wnl aw LB mo, wit_of W L RNG sta LBa -> aw_realW AI ACCT UNIV aw LB (ms_mem ms) mo W -> ties W (wins_of E nn rest) ->
    (exists md A nw, find_op HEAP_ID (s_ops st) = Some (VL md :: A :: VL nw :: rest) /\ wt nw = false /\ nn = Z.to_nat (to_Z (wl nw)) /\ (3 * nn <= length rest)%nat) ->
    CtrA.nonstack_windows nn rest = Some wnl ->
    forall b, vis W b -> In b LBk.

Lemma sm_post_ok : forall st E ms mo cls r hargs wnl st1 h1 h2 (L : alayout) (RNG : footprint) (sta : astate) (LBa : list ablock) (aw : word)
    (F : Z) (R' : bvmap 5 word) (m' : amem) (mo' : Model) (LBk : list ablock),
  st_ok bsegs OPS E st ms mo -> call_pre st = Some r -> ActrA.forget_stack_below_sp_g st = Some st1 ->
  CtrPre.TwinB.acallG AI ACCT UNIV Cw E st ms mo r hargs wnl L RNG sta LBa aw ->
  PrimInt63.leb cls 2%uint63 = true ->
  heap_add_window hargs (VP (s_next (clobber st1)) wzero) (VL (wlit (sm_usz cls))) (VL ActrB.TwinB.ActrB.K_FRAME) = Some h1 ->
  heap_add_window h1 (VP (PrimInt63.add (s_next (clobber st1)) 1%uint63) wzero) (VL (wlit (sm_tlen cls))) (VL ActrB.TwinB.ActrB.K_FTWIN) = Some h2 ->
  let R := ms_regs ms in let sp := bv_unsigned (AP.getr R 2) in let c := to_Z cls in let n := fsize c in let fb := mkABlock (ABFake c) F n in

  (forall rg, In rg CtrFrame.TwinB.kept_regsA -> AP.getr R' rg = AP.getr R rg) -> AP.getr R' 10%bv = Z_to_bv 64 F ->
  AM.mem_inv bsegs m' -> stk bsegs m' (CtrPre.TwinB.sp_lo E st) sp ->
  aheap_pres (aci AI) LBk sp (ms_mem ms) m' ->
  twins_pres LBa (ms_mem ms) m' ->
  AHEAP AI L RNG sta (fb :: LBk) m' -> ACCT aw L RNG sta (fb :: LBk) mo' ->
  (forall b, In b LBk -> In b LBa) -> live_stmt E st ms L RNG sta LBa LBk ->
  F mod 64 = 0 ->
  AS.rw_cells bsegs m' (F + 24) [C8 (AP.getr R 2)] ->
  (forall g, 0 <= g < n / 8 -> m' (AM.wa (shad F + g)) = Some (Z_to_bv 8 0)) ->
  (exists flg, AM.bytes_at bsegs m' (F + n - 8) (AM.le8 (Z_to_bv 64 flg)) /\ flag_law AI L fb flg) ->
  op_minv OPS mo' -> OTHER mo mo' ->
  exists E1, env_ext (s_next st) E E1 /\ st_ok bsegs OPS E1 (sm_post st st1 r cls h2) (CtrFrame.TwinB.ms' ms r R' m') mo'.
Proof.
  intros st E ms mo cls r hargs wnl st1 h1 h2 L RNG sta LBa aw F R' m' mo' LBk HS CP FS CF C2 H1 H2 R sp c n fb
         KEPT A0' MINV' STK' PRES TWP AH' AC' KEEP1 LIVE F64 RSW ZSH FLW MINVo OTH.
  destruct CF as (LB & ks & offs & rss & ksp & nn & md & A & nw & rest & SPR & Hksp & SPE & K16 & LOSP & FLOOR & Hf & Hc & Eh & Tnw & Nn & Ln & N255
                  & NW & AN & AJ & TS & WF & HC & AWden & (W & WOF & ARW & TI)).
  destruct (HeapCtr.TwinB.call_pre_inv st r CP) as (FOK & _).
  destruct (cls_lits cls C2) as (SZ & USZ & TLEN & NCASES). fold c in SZ, USZ, TLEN, NCASES. fold n in SZ, USZ, TLEN, NCASES.
  pose proof atop_range as ATR.
  pose proof WOF as WOF0. destruct WOF as (E1 & E2 & E3 & E4). pose proof ARW as [HWW EMW].
  assert (FF : is_fake fb) by (exists c; reflexivity).

  destruct (AI_fake L RNG sta (fb :: LBk) m' fb AH' ltac:(left; reflexivity) FF) as (BKF & HIF & A8F & N8F & NPF & WRF & WRS).
  cbn [ab_addr ab_size fb] in BKF, HIF, A8F, N8F, NPF, WRF, WRS.
  assert (BKL : (AIMG_HI <= F /\ F + n <= KLS) \/ (0x10007fff8000 <= F /\ F + n <= ATOP)) by (unfold ablk in BKF; lia).

  assert (KEEP2 : forall b, vis W b -> In b LBk).
  { apply (LIVE W nn rest wnl aw LB mo WOF0 ARW TI); [| exact NW]. exists md, A, nw. rewrite <- Eh. auto. }

  destruct (aw_real_frame_in AI ACCT UNIV AI_fake aw aw LB (ms_mem ms) mo W RNG sta c F n LBk m' mo' sp ARW
              ltac:(rewrite E1; exact AH') ltac:(rewrite E1; exact AC') PRES ltac:(unfold FRAME_MAX; lia)
              ltac:(intros b Hb; rewrite E4; exact (KEEP1 b Hb)) KEEP2 ltac:(rewrite E1; exact FLW) ltac:(rewrite E4; exact TWP)) as (AR1 & VF1 & DJ1 & DJ2).
  set (W1 := mkWit (w_L W) RNG sta (fb :: LBk) (w_T W) (List.filter (fun b => if in_dec ablock_eq_dec b LBk then true else false) (w_FA W)) m' (w_zc W)) in *.
  set (LB1 := (F, n - 8) :: (shad F, shlen n) :: LB) in *.
  assert (NINF : ~ In fb LBk).
  { pose proof (AI_blocks_nodup AI _ _ _ _ _ AH') as ND'. apply NoDup_cons_iff in ND' as [NIN _]. exact NIN. }

  assert (STB : forall a, 0 <= a < 2 ^ 64 -> CtrFrame.TwinB.stableA AI ms LB a -> m' (AM.wa a) = ms_mem ms (AM.wa a)).
  { intros a Ha ST. pose proof HWW as (_ & HT & _).
    destruct (LB_classify AI ACCT UNIV AI_fake W aw LB (ms_mem ms) mo HWW) as (KU & KT).
    apply (aw_real_stable AI ACCT UNIV AI_fake aw LB (ms_mem ms) mo W RNG sta (fb :: LBk) m' LBk LB sp LBa TWP ltac:(intros b Hb _ _; rewrite <- E4; exact Hb) ARW).
    - rewrite E1. exact AH'.
    - exact PRES.
    - intros v Hv UB P. destruct (KU v Hv UB P) as (b & Vb & ->). exists b. split; [exact (KEEP2 b Vb)| reflexivity].
    - intros v Hv NUB. destruct (KT v Hv NUB) as [(b & Hb & ->)|(b & Vb & ->)].
      + left. exists b. destruct (HT b Hb) as [HbL HH]. destruct (twin_T_facts AI ACCT UNIV W aw LB (ms_mem ms) mo b HWW Hb) as (_ & VB & _).
        split; [exact HbL|]. split; [right; exact (KEEP2 b VB)|]. split; [exact HH| reflexivity].
      + right. exists b. split; [exact (proj1 (proj1 Vb))|]. split; [exact (KEEP2 b (proj1 Vb))|]. split; [exact (proj2 Vb)| reflexivity].
    - exact Ha.
    - exact ST. }
  set (Fv := CtrPost.TwinB.cfvA R' (Z_to_bv 64 F) (Z_to_bv 64 (shad F))).
  set (Gv := fun (_ : Z) (o : Z) => match m' (AM.wa (F + o)) with Some b => b | None => Z_to_bv 8 0 end).
  set (E' := CtrFrame.TwinB.E' E st Fv Gv).
  exists E'. split; [apply CtrFrame.TwinB.EXT|].

  set (kf := addn (s_next st) 15). set (shf := addn (s_next st) 16).
  destruct (CtrFrame.TwinB.NX st FOK) as (_ & NXP & NXB). pose proof (int_range (s_next st)) as RNX. rewrite two63_eq in RNX.
  assert (KFZ : to_Z kf = to_Z (s_next st) + 15) by (unfold kf; rewrite addn_Z; [lia| rewrite wB_two63, two63_eq; lia]).
  assert (SHZ : to_Z shf = to_Z (s_next st) + 16) by (unfold shf; rewrite addn_Z; [lia| rewrite wB_two63, two63_eq; lia]).
  assert (KFE : s_next (clobber st1) = kf).
  { destruct (clobber_fields st1) as (_ & _ & _ & _ & _ & _ & _ & NXc). destruct (CtrFrame.TwinB.st1_fields st st1 FS) as (_ & _ & _ & _ & _ & _ & _ & NX1).
    rewrite NXc, NX1. symmetry. apply addn_lit; [reflexivity| rewrite wB_two63, two63_eq; lia]. }
  assert (SHE : PrimInt63.add kf 1%uint63 = shf).
  { apply Uint63.to_Z_inj. rewrite add_Z by (rewrite KFZ; change (to_Z 1%uint63) with 1; rewrite wB_two63, two63_eq; lia).
    rewrite KFZ, SHZ. change (to_Z 1%uint63) with 1. lia. }
  assert (KFNZ : PrimInt63.eqb kf 0%uint63 = false) by (apply Uint63.eqb_false_spec; intros X; rewrite X in KFZ; change (to_Z 0%uint63) with 0 in KFZ; lia).
  assert (SHNZ : PrimInt63.eqb shf 0%uint63 = false) by (apply Uint63.eqb_false_spec; intros X; rewrite X in SHZ; change (to_Z 0%uint63) with 0 in SHZ; lia).
  unfold AIMG_HI, KLS in BKL. assert (FR64 : 0x631000 <= F /\ F + n < 2 ^ 47) by lia.
  destruct (fsh_band F n BKF HIF A8F N8F ltac:(lia)) as (FS1 & FS2 & FS3 & FS4 & FS5).
  assert (EVF : bv_unsigned (ev E' kf) = F).
  { unfold E', kf. rewrite (CtrFrame.TwinB.ev_E'_fresh E st FOK Fv Gv 15 ltac:(lia)). change (Fv (Z.of_nat 15)) with (Z_to_bv 64 F).
    apply Z_to_bv_small. unfold bv_modulus, two64. lia. }
  assert (EVS : bv_unsigned (ev E' shf) = shad F).
  { unfold E', shf. rewrite (CtrFrame.TwinB.ev_E'_fresh E st FOK Fv Gv 16 ltac:(lia)). change (Fv (Z.of_nat 16)) with (Z_to_bv 64 (shad F)).
    apply Z_to_bv_small. unfold bv_modulus, two64. lia. }
  pose proof (CtrFrame.TwinB.HS' OPS E st ms mo HS FOK Fv Gv) as HSp. fold E' in HSp.
  set (spv := getr st X2).
  assert (DSP : den E' spv = AP.getr R 2%bv).
  { unfold E'. rewrite (CtrFrame.TwinB.den_E' E st Fv Gv spv (CtrFrame.TwinB.reg_below st FOK X2)). unfold spv, R.
    rewrite <- (GlueA.TwinB.getr_RA bsegs OPS E st ms mo HS X2). reflexivity. }

  assert (RAWS : forall a, 0x631000 <= a < 2 ^ 64 -> wb bsegs m' a = true -> exists b, m' (Z_to_bv 64 a) = Some b).
  { intros a Ha Wb. unfold wb, wview in Wb. destruct (m' (Z_to_bv 64 a)) as [b|]; [eauto|]. exfalso.
    rewrite Z_to_bv_unsigned, bv_wrap_small in Wb by (unfold bv_modulus; lia). rewrite (SmLib.TwinB.no_seg_above a (proj1 Ha)) in Wb. discriminate Wb. }
  assert (VALF : forall a, F <= a < F + n -> (exists b, m' (Z_to_bv 64 a) = Some b) /\ wb bsegs m' a = true /\ find_segment bsegs a 1 = None).
  { intros a Ha. destruct WRF as (_ & _ & WV).
    assert (WBI : wb bsegs m' a = true) by (apply (GlueA.TwinB.wb_wviewA bsegs); replace a with (F + (a - F)) by lia; apply WV; lia).
    split; [apply RAWS; [lia| exact WBI]|]. split; [exact WBI| apply SmLib.TwinB.no_seg_above; lia]. }
  assert (SHN : shlen n = n / 8) by (unfold shlen; rewrite Z.shiftr_div_pow2 by lia; reflexivity).
  assert (VALS : forall a, shad F <= a < shad F + n / 8 -> wb bsegs m' a = true /\ find_segment bsegs a 1 = None).
  { intros a Ha. destruct WRS as (_ & _ & WV). rewrite SHN in WV.
    split; [apply (GlueA.TwinB.wb_wviewA bsegs); replace a with (shad F + (a - shad F)) by lia; apply WV; lia| apply SmLib.TwinB.no_seg_above; lia]. }
  set (fr0 := Region 0%uint63 (VL (wlit (sm_usz cls))) true BGUnk IMap.empty).
  assert (EHF : hiZ E' fr0 = n - 8).
  { unfold hiZ, fr0. cbn [rg_hi den]. rewrite W64Proofs.wbv_unsigned, W64Proofs.wlit_ok. exact USZ. }
  assert (RO0 : region_ok bsegs (s_priv st) E' m' kf fr0).
  { assert (EL : loZ fr0 = 0) by reflexivity.
    constructor; rewrite ?EVF, ?EHF, ?EL.
    - apply IMap.bst_empty.
    - intros _. unfold two64. lia.
    - intros _ a Ha. destruct (VALF a ltac:(lia)) as ((b & Hb) & WBI & SEG).
      split; [unfold rb; rewrite Hb; discriminate|]. split; [intros _; exact WBI| exact SEG].
    - intros g gr Hg. cbn [fr0 rg_cells] in Hg. rewrite IMap.find_empty in Hg. discriminate Hg.
    - intros g gr c0 i Hg. cbn [fr0 rg_cells] in Hg. rewrite IMap.find_empty in Hg. discriminate Hg.
    - intros o Ho1 _ _. specialize (Ho1 KFNZ). unfold bg_byte. cbn [fr0 rg_bg]. unfold E', CtrFrame.TwinB.E'. rewrite eg_above by (rewrite KFZ; lia).
      rewrite KFZ. replace (to_Z (s_next st) + 15 - to_Z (s_next st)) with 15 by lia.
      destruct (VALF (F + o) ltac:(lia)) as ((b & Hb) & _). unfold rb, Gv, AM.wa. rewrite Hb. reflexivity. }
  assert (CWR : can_write bsegs (s_facts st) (s_priv st) kf fr0 24%uint63 8%uint63 = true).
  { unfold can_write, can_read. rewrite KFNZ. unfold fr0. cbn [rg_w rg_lo rg_hi]. destruct (cls_cases cls C2) as [->|[->| ->]]; vm_compute; reflexivity. }
  destruct (MemP.region_store_sound bsegs (s_priv st) E' m' (s_facts st) kf fr0 24%uint63 8%uint63 spv
              (so_facts _ _ _ _ _ _ HSp) (so_zero _ _ _ _ _ _ HSp) RO0 ltac:(right; right; right; reflexivity) CWR) as (_ & RO1 & ELo & EHi & EW & EBg & _).
  assert (ROF : region_ok bsegs (s_priv st) E' m' kf (sm_fr cls spv)).
  { apply (MemP.region_ok_frame bsegs (s_priv st) E' _ m' kf _ (so_zero _ _ _ _ _ _ HSp) RO1). intros a Ha _ _.
    unfold addrZ. rewrite EVF, DSP. change (keyZ 24%uint63) with 24. symmetry.
    replace (F + 24) with (F + 24 + Z.of_nat 0) by lia.
    apply (SmLib.TwinB.ghost_c8 m' (F + 24) [C8 (AP.getr R 2%bv)] 0 (AP.getr R 2%bv) RSW eq_refl ltac:(lia)). }
  assert (EHT : hiZ E' (sm_tw cls) = n / 8).
  { unfold hiZ, sm_tw. cbn [rg_hi den]. rewrite W64Proofs.wbv_unsigned, W64Proofs.wlit_ok. exact TLEN. }
  assert (ROT : region_ok bsegs (s_priv st) E' m' shf (sm_tw cls)).
  { assert (EL : loZ (sm_tw cls) = 0) by reflexivity.
    constructor; rewrite ?EVS, ?EHT, ?EL.
    - apply IMap.bst_empty.
    - intros _. unfold two64. lia.
    - intros _ a Ha. destruct (VALS a ltac:(lia)) as (WBI & SEG).
      split; [unfold rb; replace a with (shad F + (a - shad F)) by lia; unfold AM.wa in ZSH; rewrite (ZSH (a - shad F) ltac:(lia)); discriminate|].
      split; [intros _; exact WBI| exact SEG].
    - intros g gr Hg. cbn [sm_tw rg_cells] in Hg. rewrite IMap.find_empty in Hg. discriminate Hg.
    - intros g gr c0 i Hg. cbn [sm_tw rg_cells] in Hg. rewrite IMap.find_empty in Hg. discriminate Hg.
    - intros o Ho1 _ _. specialize (Ho1 SHNZ). unfold bg_byte. cbn [sm_tw rg_bg]. unfold rb. unfold AM.wa in ZSH. rewrite (ZSH o ltac:(lia)). reflexivity. }

  set (WFr := Win F (n - 8) K_FRAMEz). set (WTw := Win (shad F) (shlen n) K_FTWINz).
  set (ws' := (wins_of E nn rest ++ [WFr]) ++ [WTw]).
  assert (NS : to_Z (wl nw) + 2 < two63).
  { pose proof (Uint63.to_Z_bounded (wl nw)) as B. unfold two63. rewrite Nn in N255. lia. }
  rewrite KFE in H1. rewrite KFE, SHE in H2.
  destruct (CtrPost.TwinB.add_window_facts E' md A nw rest nn (VP kf wzero) (VL (wlit (sm_usz cls))) (VL ActrB.TwinB.ActrB.K_FRAME) Tnw Nn Ln ltac:(lia))
    as (AW1 & T1 & N1 & L1 & WS1 & SK1).
  set (rest1 := firstn (3 * nn) rest ++ [VP kf wzero; VL (wlit (sm_usz cls)); VL ActrB.TwinB.ActrB.K_FRAME] ++ skipn (3 * nn) rest) in *.
  set (nw1 := wadd nw wone) in *.
  destruct (CtrPost.TwinB.add_window_facts E' md A nw1 rest1 (S nn) (VP shf wzero) (VL (wlit (sm_tlen cls))) (VL ActrB.TwinB.ActrB.K_FTWIN) T1 N1 L1
              ltac:(destruct (wadd_one_small nw Tnw ltac:(lia)) as [_ X]; fold nw1 in X; lia)) as (AW2 & T2 & N2 & L2 & WS2 & SK2).
  set (rest2 := firstn (3 * S nn) rest1 ++ [VP shf wzero; VL (wlit (sm_tlen cls)); VL ActrB.TwinB.ActrB.K_FTWIN] ++ skipn (3 * S nn) rest1) in *.
  set (nw2 := wadd nw1 wone) in *.
  rewrite Eh in H1. rewrite AW1 in H1. injection H1 as <-. rewrite AW2 in H2. injection H2 as <-.
  pose proof (CtrFrame.TwinB.rest_below st FOK rest hargs md A nw Hf Eh) as RBL.
  assert (ABL : sv_vars_below (s_next st) A = true).
  { pose proof (CtrFrame.TwinB.hargs_below st FOK hargs Hf) as X. rewrite Eh in X. cbn [forallb] in X. apply andb_prop in X as [_ X]. apply andb_prop in X as [X _]. exact X. }
  assert (DECN : decode (map (den E') (VL md :: A :: VL nw2 :: rest2)) = Some (w2Z md, aw, ws', map (den E) (skipn (3 * nn) rest))).
  { rewrite (decode_hargs E' md A nw2 rest2 (S (S nn)) T2 N2 L2). rewrite WS2, WS1, SK2, SK1.
    unfold E'. rewrite (CtrFrame.TwinB.wins_of_E' E st Fv Gv nn rest RBL), (CtrFrame.TwinB.map_den_E' E st Fv Gv _ (CtrPost.TwinB.forallb_skipn _ (3 * nn) rest RBL)).
    rewrite (CtrFrame.TwinB.den_E' E st Fv Gv A ABL), <- AWden. fold E'.
    assert (C2' : Win (bv_unsigned (den E' (VP kf wzero))) (bv_unsigned (den E' (VL (wlit (sm_usz cls))))) (bv_unsigned (den E' (VL ActrB.TwinB.ActrB.K_FRAME))) = WFr).
    { unfold WFr. rewrite HeapCtr.TwinB.den_VPz, EVF. cbn [den]. rewrite W64Proofs.wbv_unsigned, W64Proofs.wlit_ok, USZ. reflexivity. }
    assert (C3' : Win (bv_unsigned (den E' (VP shf wzero))) (bv_unsigned (den E' (VL (wlit (sm_tlen cls))))) (bv_unsigned (den E' (VL ActrB.TwinB.ActrB.K_FTWIN))) = WTw).
    { unfold WTw. rewrite HeapCtr.TwinB.den_VPz, EVS. cbn [den]. rewrite W64Proofs.wbv_unsigned, W64Proofs.wlit_ok, TLEN, SHN. reflexivity. }
    rewrite C2', C3'. reflexivity. }

  set (LB2 := (shad F, shlen n) :: (F, n - 8) :: LB).
  assert (HW2 : aw_holds_w AI ACCT UNIV W1 aw LB2 m' mo').
  { destruct AR1 as [(AHx & HTx & NDx & HFAx & NDFx & HLBx & RESTx) _].
    split; [exact AHx|]. split; [exact HTx|]. split; [exact NDx|]. split; [exact HFAx|]. split; [exact NDFx|]. split; [| exact RESTx].
    assert (PERM : forall v, In v LB2 <-> In v LB1) by (intros v; unfold LB1, LB2; cbn [In]; tauto).
    intros v. split; [intros Hv; apply (proj1 (HLBx v)); apply PERM; exact Hv| intros X; apply PERM; exact (proj2 (HLBx v) X)]. }
  assert (HOLDN : op_holds OPS HEAP_ID (map (den E') (VL md :: A :: VL nw2 :: rest2)) m' mo').
  { rewrite OPS_holds1. exists (w2Z md), aw, ws', (map (den E) (skipn (3 * nn) rest)), LB2, W1.
    split; [exact DECN|]. split; [exact HW2|]. split; [| split].
    -
      apply Forall_app. split; [apply Forall_app; split|].
      + apply (CtrPost.TwinB.windows_wf_mono _ LB LB2 _ WF). intros b Hb. right; right. exact Hb.
      + constructor; [|constructor]. unfold window_wf, WFr, w_iv. cbn [w_lo w_len w_kind]. split; [lia|]. split; [lia|]. split; [unfold two64; lia|].
        right; right. split; [unfold K_SUB, K_FRAMEz; lia|]. exists (F, n - 8). split; [right; left; reflexivity|]. intros a Ha. exact Ha.
      + constructor; [|constructor]. unfold window_wf, WTw, w_iv. cbn [w_lo w_len w_kind]. split; [lia|]. split; [lia|]. split; [unfold two64; lia|].
        right; right. split; [unfold K_SUB, K_FTWINz; lia|]. exists (shad F, shlen n). split; [left; reflexivity|]. intros a Ha. exact Ha.
    -
      assert (HC1 : cw_holds Cw (w2Z md) (map (den E) (skipn (3 * nn) rest)) LB (wins_of E nn rest) m').
      { apply (cw_frame Cw _ _ _ _ (ms_mem ms) m' HC). intros a Ha U _.
        pose proof (STB a ltac:(unfold two64 in Ha; lia) ltac:(right; right; exact U)) as E0. unfold AM.wa in E0. symmetry. exact E0. }
      pose proof (Cw_ghost_grow_f K_FRAMEz _ _ _ _ m' F (n - 8) ltac:(left; reflexivity) HC1 DJ1) as HC2.
      apply (Cw_ghost_grow_f K_FTWINz _ _ _ _ m' (shad F) (shlen n) ltac:(right; reflexivity) HC2).
      intros a Ha U. apply in_ivs_cons in U as [U|U]; [| exact (DJ2 a Ha U)].
      unfold in_iv in Ha, U. cbn [fst snd] in Ha, U. lia.
    -
      apply (ties_frame_in W W1 (wins_of E nn rest) ws' fb TI eq_refl eq_refl FF).
      + exact (frame_in_visf AI ACCT UNIV aw LB (ms_mem ms) mo W RNG sta c F n LBk m' ARW ltac:(rewrite E1; exact AH')
                 ltac:(intros b Hb; rewrite E4; exact (KEEP1 b Hb)) KEEP2).
      + intros w. unfold ws'. cbn [ab_addr ab_size fb]. fold WFr WTw. split.
        * intros H. apply in_app_or in H as [H|[<-|[]]]; [apply in_app_or in H as [H|[<-|[]]]; [left; exact H| right; left; reflexivity]| right; right; reflexivity].
        * intros [H|[->| ->]]; [apply in_or_app; left; apply in_or_app; left; exact H| apply in_or_app; left; apply in_or_app; right; left; reflexivity| apply in_or_app; right; left; reflexivity].
      +
        intros b HB [Hb NF]. unfold W1 in Hb, NF. cbn [w_LBa w_FA] in Hb, NF. destruct Hb as [<-|Hb].
        * exfalso. destruct HB as [p HP]. cbn [fb ab_kind] in HP. discriminate HP.
        * split; [rewrite E4; exact (KEEP1 b Hb)|]. intros X. apply NF. apply filter_In. split; [exact X|].
          destruct (in_dec ablock_eq_dec b LBk); [reflexivity| contradiction].
      +
        destruct TI as (_ & _ & _ & _ & _ & _ & _ & _ & _ & GA & _).
        apply (ghost_apart_new_ghosts (wins_of E nn rest) ws' LB _ WF GA). intros w Hw. unfold ws' in Hw.
        apply in_app_or in Hw as [Hw|[<-|[]]]; [apply in_app_or in Hw as [Hw|[<-|[]]]; [left; exact Hw|]|].
        -- right. split; [unfold WFr; cbn [w_kind]; unfold K_FRAMEz, K_BLOCK; lia|]. intros _ a Ha. unfold WFr, w_iv in Ha. cbn [w_lo w_len] in Ha. exact (DJ1 a Ha).
        -- right. split; [unfold WTw; cbn [w_kind]; unfold K_FTWINz, K_BLOCK; lia|]. intros _ a Ha. unfold WTw, w_iv in Ha. cbn [w_lo w_len] in Ha. exact (DJ2 a Ha).
      +
        intros P. unfold W1. cbn [w_st]. rewrite <- E3. exact P. }

  pose proof (aw_real_holds AI ACCT UNIV _ _ _ _ _ ARW) as AWH.
  assert (SBV : forall a, 0 <= a < 2 ^ 64 -> CtrFrame.TwinB.stableA AI ms LB a ->
            rb bsegs m' a = rb bsegs (ms_mem ms) a /\ (wb bsegs (ms_mem ms) a = true -> wb bsegs m' a = true)).
  { intros a Ha ST. pose proof (STB a Ha ST) as EQ. split.
    - unfold rb. unfold AM.wa in EQ. rewrite EQ. reflexivity.
    - intros Wb. apply (GlueA.TwinB.wb_wviewA bsegs). apply (GlueA.TwinB.wb_wviewA bsegs) in Wb. rewrite (wview_ext1 m' (ms_mem ms) _ EQ). exact Wb. }
  assert (SBO : forall o a, In o (s_ops st) -> not_id HEAP_ID o -> 0 <= a < two64 ->
            Exists (fun iv => fst iv <= a < snd iv) (op_fp OPS (op_id o) (map (den E') (op_args o))) -> m' (Z_to_bv 64 a) = ms_mem ms (Z_to_bv 64 a)).
  { intros o a Ho NI Ha FP. unfold not_id in NI. apply Uint63.eqb_false_spec in NI.
    destruct (OPS_fp_other _ _ a NI FP) as [RR|[(a' & RR & ->)|(a' & STK & ->)]].
    - pose proof (STB a ltac:(unfold two64 in Ha; lia) ltac:(right; left; exact RR)) as E0. unfold AM.wa in E0. exact E0.
    - pose proof (proj1 (PRES (shad a') ltac:(unfold two64 in Ha; lia) ltac:(right; right; right; exists a'; split; [right; left; exact RR| reflexivity]))) as E0.
      unfold AM.wa in E0. exact E0.
    -
      pose proof (proj1 (PRES (shad a') ltac:(unfold two64 in Ha; lia) ltac:(right; right; right; exists a'; split; [left; exact STK| reflexivity]))) as E0.
      unfold AM.wa in E0. exact E0. }
  assert (WBM : forall a, 0 <= a < two64 -> (in_ranges (aci AI) a \/ (exists a', in_ranges (aci AI) a' /\ a = shad a') \/ (exists a', ATOP <= a' < 2 ^ 47 /\ a = shad a')) ->
            wb bsegs (ms_mem ms) a = true -> wb bsegs m' a = true).
  { intros a Ha CC Wb. apply (GlueA.TwinB.wb_wviewA bsegs). apply (GlueA.TwinB.wb_wviewA bsegs) in Wb.
    refine (proj2 (PRES a ltac:(unfold two64 in Ha; lia) _) Wb).
    destruct CC as [CC|[(a' & CC & ->)|(a' & CC & ->)]]; [right; left; exact CC| |]; right; right; right; exists a'; (split; [| reflexivity]); [right; left; exact CC| left; exact CC]. }
  assert (WINKW : forall k0 len kd, True -> CtrA.win_lookup wnl k0 = Some (len, kd) ->
            forall a, bv_unsigned (ev E k0) <= a < bv_unsigned (ev E k0) + bv_unsigned (den E len) -> in_user LB a).
  { intros k0 len kd _ WL a Ha.
    destruct (HeapCtrB.TwinB.nonstack_windows_In E nn rest wnl k0 len kd NW (HeapCtrB.TwinB.win_lookup_In _ _ _ _ WL)) as (_ & _ & KD & INW).
    pose proof (proj1 (Forall_forall _ _) WF _ INW) as (W1' & W2' & W3' & [[KS0 _]|[[KB B]|[KS2 (b & Hb & SUB)]]]); unfold w_iv in *; cbn [w_kind w_lo w_len] in *.
    - exfalso. exact (KD KS0).
    - apply in_ivs_In. eexists. split; [exact B|]. unfold in_iv. cbn [fst snd]. lia.
    - apply in_ivs_In. exists b. split; [exact Hb|]. apply SUB. unfold in_iv. cbn [fst snd]. lia. }

  assert (SBT : forall a, 0 <= a < 2 ^ 64 -> sh_cov a -> in_based E (s_regs st) a ->
            rb bsegs m' a = rb bsegs (ms_mem ms) a /\ (wb bsegs (ms_mem ms) a = true -> wb bsegs m' a = true)).
  { intros a Ha SC _.
    assert (CA : aclient_addr (aci AI) LBk sp a).
    { destruct SC as [(a' & RR & ->)|(v & Hv & RR)].
      - right; right; right. exists a'. split; [left; exact RR| reflexivity].
      - destruct (IMGSH_aci v a Hv RR) as (a' & INA & ->). right; right; right. exists a'. split; [right; left; exact INA| reflexivity]. }
    destruct (PRES a Ha CA) as [EQ WV]. split.
    - unfold rb. unfold AM.wa in EQ. rewrite EQ. reflexivity.
    - intros Wb. apply (GlueA.TwinB.wb_wviewA bsegs). apply (GlueA.TwinB.wb_wviewA bsegs) in Wb. exact (WV Wb). }

  pose proof STK' as STK2.
  set (newR := [(kf, sm_fr cls spv); (shf, sm_tw cls)]).
  set (NEWSET := fun a : Z => in_iv (F, n - 8) a \/ in_iv (shad F, shlen n) a).
  assert (HIFR : hiZ E' (sm_fr cls spv) = n - 8 /\ loZ (sm_fr cls spv) = 0 /\ rg_w (sm_fr cls spv) = true).
  { unfold sm_fr. fold fr0. unfold hiZ, loZ. rewrite EHi, ELo, EW. split; [exact EHF| split; reflexivity]. }
  destruct HIFR as (HIFR & LOFR & WFR).
  assert (NEWRANGE : forall k rg a, In (k, rg) newR -> bv_unsigned (ev E' k) + loZ rg <= a < bv_unsigned (ev E' k) + hiZ E' rg -> NEWSET a).
  { intros k rg a [X|[X|[]]] Ha; injection X as <- <-.
    - left. rewrite EVF, LOFR, HIFR in Ha. unfold in_iv. cbn [fst snd]. lia.
    - right. rewrite EVS, EHT in Ha. change (loZ (sm_tw cls)) with 0 in Ha. unfold in_iv. cbn [fst snd]. lia. }
  assert (NEWLOW : forall a, NEWSET a -> AIMG_HI <= a < ATOP + 4096 /\ ~ in_user LB a).
  { intros a [X|X]; (split; [unfold in_iv in X; cbn [fst snd] in X; unfold AIMG_HI; lia|]); [exact (DJ1 a X)| exact (DJ2 a X)]. }
  assert (NEWNOSH : forall a, NEWSET a -> ~ (0x7fff8000 <= a < 0x800be200)).
  { intros a [X|X] Y; unfold in_iv in X; cbn [fst snd] in X; [lia|].
    assert (0x800be200 <= shad F) by (unfold shad, ASHOFF; rewrite Z.shiftr_div_pow2 by lia; change (2 ^ 3) with 8; Z.div_mod_to_equations; lia). lia. }
  assert (NEWNOSTK : forall a, NEWSET a -> ~ (exists a', ATOP <= a' < 2 ^ 47 /\ a = shad a')).
  { intros a X (a' & RR & ->).
    assert (SHB : shad ATOP <= shad a' < 0x10007fff8000) by (unfold shad, ASHOFF; rewrite !Z.shiftr_div_pow2 by lia; change (2 ^ 3) with 8; Z.div_mod_to_equations; lia).
    assert (SHT : shad F + shlen n <= shad ATOP).
    { rewrite SHN. unfold shad, ASHOFF. rewrite !Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8. clear - HIF A8F N8F NCASES FR64. Z.div_mod_to_equations. lia. }
    assert (KLSB : 0x7fff7000 < shad ATOP) by (unfold shad, ASHOFF; rewrite Z.shiftr_div_pow2 by lia; change (2 ^ 3) with 8; clear - ATR; Z.div_mod_to_equations; lia).
    destruct X as [X|X]; unfold in_iv in X; cbn [fst snd] in X; lia. }
  assert (NEWDISJ : forall k1 r1 k2 r2 a, In (k1, r1) newR -> In (k2, r2) newR -> k1 <> k2 -> (rg_w r1 = true \/ rg_w r2 = true) ->
            ~ (bv_unsigned (ev E' k1) + loZ r1 <= a < bv_unsigned (ev E' k1) + hiZ E' r1 /\ bv_unsigned (ev E' k2) + loZ r2 <= a < bv_unsigned (ev E' k2) + hiZ E' r2)).
  { intros k1 r1 k2 r2 a [X1|[X1|[]]] [X2|[X2|[]]] NE _ [A1 A2]; injection X1 as <- <-; injection X2 as <- <-; try (apply NE; reflexivity);
      rewrite ?EVF, ?EVS, ?LOFR, ?HIFR, ?EHT in A1, A2; change (loZ (sm_tw cls)) with 0 in *; lia. }
  assert (NEWND : List.NoDup (map fst newR)).
  { cbn [map fst newR]. constructor; [intros [X|[]]; rewrite X in SHZ; lia| constructor; [intros []| constructor]]. }
  assert (NEWFRESH : forall k rg, In (k, rg) newR -> PrimInt63.eqb k 0%uint63 = false).
  { intros k rg [X|[X|[]]]; injection X as <- <-; apply (CtrFrame.TwinB.fresh_nz st ms FOK r); lia. }
  assert (NEWOK : forall k rg, In (k, rg) newR -> region_ok bsegs (s_priv st) E' m' k rg).
  { intros k rg [X|[X|[]]]; injection X as <- <-; [exact ROF| exact ROT]. }

  assert (INWS : forall ws0 a, in_ws (heap_ws (wins_of E nn rest)) a \/ in_iv (w_iv WFr) a \/ in_iv (w_iv WTw) a -> ws0 = ws' -> in_ws (heap_ws ws0) a).
  { intros ws0 a X ->. unfold in_ws, heap_ws in *. apply in_ivs_In.
    destruct X as [X|[X|X]].
    - apply in_ivs_In in X as (v & Hv & Hin). exists v. split; [| exact Hin]. apply in_map_iff in Hv as (w & <- & Hw). apply in_map.
      apply filter_In in Hw as [Hw K]. apply filter_In. split; [| exact K]. apply in_or_app. left. apply in_or_app. left. exact Hw.
    - exists (w_iv WFr). split; [| exact X]. apply in_map. apply filter_In. split; [apply in_or_app; left; apply in_or_app; right; left; reflexivity| reflexivity].
    - exists (w_iv WTw). split; [| exact X]. apply in_map. apply filter_In. split; [apply in_or_app; right; left; reflexivity| reflexivity]. }
  assert (W1p : forall a, NEWSET a -> in_ws (heap_ws ws') a).
  { intros a [X|X]; apply (INWS ws' a); try reflexivity; [right; left; exact X| right; right; exact X]. }
  assert (W3p : forall a, 0 <= a < two64 -> ~ in_ivs IMGX a -> ~ in_ws ws' a ->
            ~ in_ws (wins_of E nn rest) a \/ (find_segment bsegs a 1 = None /\ ~ in_based E' (CtrFrame.TwinB.RgPg st ks rss ksp newR []) a)).
  { intros a _ _ NWS. left. intros X. apply NWS. unfold in_ws, ws' in *. rewrite !map_app. apply in_ivs_app. left. apply in_ivs_app. left. exact X. }
  assert (W4p : forall a, in_based E' (CtrFrame.TwinB.RgPg st ks rss ksp newR []) a -> in_ws (heap_ws (wins_of E nn rest)) a -> in_ws (heap_ws ws') a).
  { intros a _ X. apply (INWS ws' a); [left; exact X| reflexivity]. }

  set (facts' := ActrB.TwinB.ActrB.link_fact shf kf :: FAlign kf 6%uint63 :: FRange kf ActrB.TwinB.ActrB.BLK_LO ActrB.TwinB.ActrB.BLK_HI :: s_facts st).
  assert (FACTS : facts_hold E' facts').
  { constructor; [| constructor; [| constructor; [| exact (so_facts _ _ _ _ _ _ HSp)]]].
    - unfold ActrB.TwinB.ActrB.link_fact. cbn [fact_holds]. rewrite HeapCtr.TwinB.den_VPz.
      change (den E' (VAlu ALU_ADD (VAlu ALU_SRL (VP kf wzero) (VL (wlit 3%uint63))) (VL ActrB.TwinB.ActrB.SBw)))
        with (alu64 ALU_ADD (alu64 ALU_SRL (den E' (VP kf wzero)) (wbv (wlit 3%uint63))) (wbv ActrB.TwinB.ActrB.SBw)).
      rewrite HeapCtr.TwinB.den_VPz. apply bv_eq. unfold alu64, alu. rewrite bv_add_unsigned, bv_shiftr_unsigned, bv_and_unsigned, EVS, EVF.
      replace (bv_unsigned (wbv (wlit 3%uint63))) with 3 by (vm_compute; reflexivity).
      replace (bv_unsigned (Z_to_bv 64 63)) with 63 by (vm_compute; reflexivity).
      change (Z.land 3 63) with 3.
      replace (bv_unsigned (wbv ActrB.TwinB.ActrB.SBw)) with 0x7fff8000 by (vm_compute; reflexivity).
      unfold shad, ASHOFF, bv_wrap, bv_modulus. rewrite Z.mod_small; [apply Z.add_comm|]. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8.
      change (2 ^ Z.of_N 64) with (2 ^ 64). clear - FR64 NCASES. Z.div_mod_to_equations. lia.
    - cbn [fact_holds]. rewrite EVF. change (2 ^ to_Z 6%uint63) with 64. exact F64.
    - cbn [fact_holds]. rewrite EVF. replace (w2Z ActrB.TwinB.ActrB.BLK_LO) with 0x631000 by (vm_compute; reflexivity).
      replace (w2Z ActrB.TwinB.ActrB.BLK_HI) with (2 ^ 47 - 1) by (vm_compute; reflexivity). lia. }
  assert (DV : den E' (VP kf wzero) = AP.getr R' 10%bv).
  { rewrite HeapCtr.TwinB.den_VPz, A0'. unfold E', kf. rewrite (CtrFrame.TwinB.ev_E'_fresh E st FOK Fv Gv 15 ltac:(lia)). reflexivity. }

  assert (SHP : sm_post st st1 r cls (VL md :: A :: VL nw2 :: rest2)
              = SS r (rf_set (s_rf (clobber st1)) X10 (VP kf wzero)) (s_ff st) (s_resv st) (CtrFrame.TwinB.RgPg st ks rss ksp newR []) facts'
                   (CtrFrame.TwinB.opsg st (VL md :: A :: VL nw2 :: rest2)) (s_priv st) (PrimInt63.add shf 1%uint63)).
  { unfold sm_post. cbv zeta. rewrite KFE, SHE.
    destruct (clobber_fields st1) as (_ & FF1 & RV1 & RG1 & FS1' & OP1 & PV1 & _).
    destruct (CtrFrame.TwinB.st1_fields st st1 FS) as (_ & _ & FF0 & RV0 & FS0 & OP0 & PV0 & _).
    rewrite FF1, RV1, RG1, FS1', OP1, PV1, FF0, RV0, FS0, OP0, PV0.
    rewrite (CtrFrame.TwinB.st1_regs st st1 FS ks offs rss ksp SPR Hksp). reflexivity. }
  rewrite SHP.
  exact (CtrFrame.TwinB.frame_st_ok AI IMGX IMGX_aci ACCT UNIV OPS AI_fake OPS_fp1 OPS_cov1 OPS_frame_other OPS_fp_other OTHER OPS_mo_other OPS_cov0_img
           E st ms mo HS FOK Fv Gv r st1 CP FS R' m' mo' KEPT (fun x i Hx => CtrPost.TwinB.cfvA_clob R' _ _ x i Hx) aw LB LB AWH MINV' SBV SBO WBM SBT
           ks offs rss ksp SPR SPE wnl nn rest AJ WF (fun _ => True) WINKW ltac:(intros; exact I) ltac:(intros; exact I) K16 LOSP STK2 FLOOR hargs md A nw Hf Hc Eh Tnw Nn Ln OTH
           newR [] NEWND NEWFRESH (fun _ _ => I) NEWSET NEWOK NEWRANGE NEWLOW NEWNOSH NEWNOSTK NEWDISJ
           (VL md :: A :: VL nw2 :: rest2) (w2Z md) aw ws' (map (den E) (skipn (3 * nn) rest)) DECN HOLDN W1p W3p W4p
           facts' (VP kf wzero) (PrimInt63.add shf 1%uint63) FACTS DV MINVo).
Qed.
End Post.
End TwinB.
