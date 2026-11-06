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
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require I_asan_memcpy.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common Require Import RunDraw ShapeAlg.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX Require Import W64 Val IMap Instr State Step Plan PlanSound.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX Require Import Mem.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Heap Require Import Op.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Ctr Require Import Lib Defs DefsA DefsB.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Bridge Require Import Ledger Op Adeq.
Import ListNotations.
Import W64 Val OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Mem.Mem FI St OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Step.Step Plan PlanS CtrLib HeapOp.
Open Scope Z_scope.
Unset Lia Cache.

From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Bridge Require Import Actr.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX Require Import W64Proofs ValProofs MemProofs StepSoundBase.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Br Require Import CtrFX.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Br Require HeapCtr HeapCtrB MemFX RstageCtr.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Bridge Require CallA CallV GlueA CtrPre CtrFrame CtrNoDelta CtrFree.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.GlueA Require UnreggGeo UnreggPre.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.GlueA Require Import ReadC ReadPre MemOps RstageC MemsetFX RangePre MemsetPre MemsetPost RegRepl RstageSound.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.GlueA Require ReadPost.
Unset Nia Cache. Unset Nra Cache.
Import ValP MemP StepB CtrFX ActrA RstageC.
Module IMC := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.I_asan_memcpy.I_memcpy.

Section Leaf.
Context {rc : runConstT}.
Variable AI : AMallocIface2.
Variable IMGX : list iv.
Hypothesis IMGX_aci : imgx_ok AI IMGX.
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
Hypothesis Cw_sub_ghost : forall md ca LB ws m w g a, cw_holds Cw md ca LB ws m -> In w ws -> In g ws ->
  K_SUB <= w_kind w < K_GHOST -> K_GHOST <= w_kind g -> in_iv (w_iv w) a -> in_iv (w_iv g) a -> False.
Variable MP : Model -> Prop.
Variable PB : (int -> list byte) -> Prop.
Variable file : list byte.

Definition uband (a : Z) : Prop := (AIMG_HI <= a < KLS) \/ (0x10007fff8000 <= a < ATOP).
Lemma shad_not_uband : forall a', 0 <= a' < 2 ^ 47 -> ~ uband (shad a').
Proof.
  intros a' H U. pose proof atop_range as ATR. unfold uband, AIMG_HI, KLS in U.
  assert (0x7fff8000 <= shad a' < 0x10007fff8000) by (unfold shad, ASHOFF; rewrite Z.shiftr_div_pow2 by lia; change (2 ^ 3) with 8; Z.div_mod_to_equations; lia). lia.
Qed.

Section Zone.
Variables (E : env) (st : sstate) (ms : machine_state) (mo : Model).
Hypothesis HS : st_ok asegs OPS E st ms mo.
Variables (r : int) (hargs : list sv) (wnl : list (int * sv * w64)) (L : alayout) (RNG : footprint) (sta : astate) (LBa : list ablock) (aw : word).
Hypothesis CF : CtrPre.acallG AI ACCT UNIV Cw E st ms mo r hargs wnl L RNG sta LBa aw.
Hypothesis AH : AHEAP AI L RNG sta LBa (ms_mem ms).
Variables (kb : int) (wlen : sv).
Hypothesis WL : CtrA.win_lookup wnl kb = Some (wlen, CtrLib.K_BLOCK).
Hypothesis OT : others_twins wnl kb = true.
Let Db := bv_unsigned (ev E kb).
Let wlenZ := bv_unsigned (den E wlen).

Lemma zone_regions : forall a, Db <= a < Db + wlenZ -> uband a ->
  forall k2 r2, IMap.find k2 (s_regs st) = Some r2 -> k2 <> kb -> PrimInt63.eqb k2 0%uint63 = false ->
  ~ (bv_unsigned (ev E k2) + loZ r2 <= a < bv_unsigned (ev E k2) + hiZ E r2).
Proof.
  intros a INB UB k2 r2 Hk2 NK K20 RG. pose proof atop_range as ATR.
  destruct CF as (LB & ks & offs & rss & ksp & nn & md & A & nw & rest & SPR & Hksp & SPE & K16 & LOSP & FLOOR & Hf & Hc & Eh & Tnw & Nn & Ln & N255
                  & NW & AN & AJ & TS & WF & HC & AWden & (W & WOF & ARW & TI)).
  assert (KN0 : k2 <> 0%uint63) by (intros ->; discriminate K20).
  pose proof ARW as [HWW _].

  assert (TWINWIN : forall k len kd, CtrA.win_lookup wnl k = Some (len, kd) -> k <> kb ->
            forall x, bv_unsigned (ev E k) <= x < bv_unsigned (ev E k) + bv_unsigned (den E len) -> ~ uband x).
  { intros k len kd WLk NKb x Hx U. pose proof (HeapCtrB.win_lookup_In _ _ _ _ WLk) as Ik.
    pose proof (proj1 (forallb_forall _ _) OT _ Ik) as Q. cbv beta iota in Q.
    replace (PrimInt63.eqb k kb) with false in Q by (symmetry; apply Uint63.eqb_false_spec; exact NKb). cbn [orb] in Q. apply weqb_eq in Q. subst kd.
    destruct (HeapCtrB.nonstack_windows_In E nn rest wnl k len K_TWIN NW Ik) as (_ & _ & _ & INW).
    destruct TI as (_ & T2 & _). destruct (T2 _ INW eq_refl) as (b & HbT & EIV). unfold w_iv, twin_iv in EIV. cbn [w_lo w_len] in EIV. injection EIV as E1 E2.
    destruct (LB_twin_facts AI ACCT UNIV W _ LB (ms_mem ms) mo b HWW HbT) as (T1 & T2' & _).
    unfold uband, AIMG_HI, KLS in U. rewrite E1, E2 in Hx. lia. }
  destruct (CallA.aregion_just_sound asegs OPS E st ms mo wnl ks offs rss k2 r2 HS SPR AJ Hk2 KN0) as [[EQ TOPk]|[NE [(len0 & kd0 & WLS & LZ & HZ)|[[J1 J2]|VJ]]]].
  -
    subst k2. destruct (CallA.sp_region_inv st ks offs rss SPR) as (_ & Hrs & _). rewrite Hrs in Hk2. injection Hk2 as <-.
    unfold uband, AIMG_HI, KLS in UB. lia.
  - apply (TWINWIN k2 len0 kd0 WLS NK a); [rewrite LZ in RG; lia| exact UB].
  - rewrite (CtrFrame.SP_den OPS E st ms mo HS) in J1. unfold uband, AIMG_HI, KLS in UB.
    assert (SPF : ATOP + 4096 <= bv_unsigned (AP.getr (ms_regs ms) 2%bv)) by (rewrite SPE; lia). lia.
  -
    destruct VJ as [VJ|SL]; [| exfalso; pose proof (CtrPre.sliver_low OPS E st ms mo ks offs rss k2 r2 hargs nn md A nw rest LB a HS SPR Hk2 KN0 NE SL Hf Eh Tnw Nn Ln WF RG) as SLO; unfold uband, AIMG_HI, KLS in UB; lia].
    pose proof (CallV.view_just_sound asegs OPS E st ms mo wnl ks offs rss k2 r2 HS SPR Hk2 KN0 VJ) as VS. unfold CallV.view_sem in VS. cbv zeta in VS.
    destruct VS as [(_ & blo & bhi & SHZ & BH & BL)|[(hs & n0 & sh & len1 & ZV & BT & _ & WLs & V1 & V2)|[(VI & v & Hv & V1 & V2)|(shD & kbD & nD & lenD & WLD & BTD & WLkD & STD & TND & ROD & LOD & HID)]]].
    + destruct (SHZ a RG) as (a' & Ha' & ->).
      assert (A0 : 0 <= a').
      { destruct BL as [(wlo & _ & ->)|[(rs & Frs & ->)|BL]].
        - pose proof (bv_unsigned_in_range 64 (den E (VP STACK_ID wlo))). lia.
        - destruct (CallA.sp_region_inv st ks offs rss SPR) as (_ & Hrs & _). rewrite Hrs in Frs. injection Frs as <-. lia.
        - pose proof (bv_unsigned_in_range 64 (den E (getr st X2))). lia. }
      assert (SZ : CallV.shz a' = shad a') by (unfold CallV.shz, shad, ASHOFF; rewrite Z.shiftr_div_pow2 by lia; change (2 ^ 3) with 8; lia).
      rewrite SZ in UB. exact (shad_not_uband a' ltac:(lia) UB).
    + assert (NKS : sh <> kb) by (intros ->; rewrite WL in WLs; assert (Q : CtrLib.K_BLOCK = K_TWIN) by congruence; vm_compute in Q; discriminate Q).
      apply (TWINWIN sh len1 K_TWIN WLs NKS a); [lia| exact UB].
    + unfold ActrA.IMGSH in Hv. cbn [In] in Hv. destruct Hv as [<-|[]]. cbn [fst snd] in V1, V2. unfold uband, AIMG_HI, KLS in UB. lia.
    +
      assert (NKSD : shD <> kb) by (intros ->; rewrite WL in WLD; assert (Q : CtrLib.K_BLOCK = K_TWIN) by congruence; vm_compute in Q; discriminate Q).
      apply (TWINWIN shD lenD K_TWIN WLD NKSD a); [lia| exact UB].
Qed.

Lemma zone_ops : forall a, 0 <= a < two64 -> Db <= a < Db + wlenZ -> uband a ->
  forall o, In o (s_ops st) -> ~ Exists (fun iv => fst iv <= a < snd iv) (op_fp OPS (op_id o) (map (den E) (op_args o))).
Proof.
  intros a Ha INB UB o Ho FP. pose proof atop_range as ATR.
  destruct CF as (LB & ks & offs & rss & ksp & nn & md & A & nw & rest & SPR & Hksp & SPE & K16 & LOSP & FLOOR & Hf & Hc & Eh & Tnw & Nn & Ln & N255
                  & NW & AN & AJ & TS & WF & HC & AWden & (W & WOF & ARW & TI)).
  destruct (PrimInt63.eqb (op_id o) HEAP_ID) eqn:QH.
  - apply Uint63.eqb_correct in QH. pose proof (ReadPost.count_one_args HEAP_ID (s_ops st) o hargs Ho QH Hc Hf) as EA.
    rewrite QH, EA, OPS_fp1, Eh in FP.
    apply (proj1 (fp_spec IMGX _ _ _ _ _ a (decode_hargs E md A nw rest nn Tnw Nn Ln))) in FP as (_ & _ & NWS).
    apply NWS. destruct (HeapCtrB.nonstack_windows_In E nn rest wnl kb wlen CtrLib.K_BLOCK NW (HeapCtrB.win_lookup_In _ _ _ _ WL)) as (_ & _ & _ & INW).
    unfold in_ws. apply in_ivs_In. eexists. split; [apply in_map; exact INW|]. unfold in_iv, w_iv. cbn [w_lo w_len fst snd]. fold Db wlenZ. lia.
  - apply Uint63.eqb_false_spec in QH. destruct (OPS_fp_other _ _ a QH FP) as [(iv0 & Hi & RRa)|[(a' & (iv0 & Hi & RRa) & ->)|(a' & STK & ->)]].
    + pose proof (AI_aci_img AI iv0 Hi) as HIa. unfold uband, AIMG_HI, KLS in *. lia.
    + pose proof (AI_aci_img AI iv0 Hi) as HIa. pose proof (AI_aci_lo AI iv0 Hi) as LOa. unfold AIMG_HI in HIa.
      exact (shad_not_uband a' ltac:(lia) UB).
    +
      exact (shad_not_uband a' ltac:(lia) UB).
Qed.
End Zone.

Hypothesis OPS_holds_rstage' : forall args m mo, ReadPost.rstage_holds_v file args m -> op_holds OPS ReadC.RSTV_ID args m mo.
Hypothesis OPS_fp_rstage : forall args args', op_fp OPS ReadC.RSTV_ID args = op_fp OPS ReadC.RSTV_ID args'.
Hypothesis OPS_cov1_heap : forall id args z, op_cov1 OPS id args z -> id = HEAP_ID.
Hypothesis PB_file : forall b, PB b -> b 4%uint63 = file.

Lemma setr_X10 : forall S v, setr S X10 v = SS (s_pc S) (rf_set (s_rf S) X10 v) (s_ff S) (s_resv S) (s_regs S) (s_facts S) (s_ops S) (s_priv S) (s_next S).
Proof. reflexivity. Qed.

Lemma rs_post_shape : forall st st1 r kb X off, rs_post st st1 r kb X off =
  let C := clobber st1 in
  SS r (rf_set (s_rf C) X10 (getr st X10)) (s_ff C) (s_resv C)
     (IMap.add kb (Region 0%uint63 (CtrB.new_hi (s_facts st) X (getr st X12)) true (BGBlob 4%uint63 0%uint63) IMap.empty) (s_regs C))
     (s_facts C) (set_op ReadC.RSTV_ID [sv_alu ALU_ADD off (getr st X12); VL wzero] (s_ops C)) (s_priv C) (s_next C).
Proof. intros st st1 r kb X off. unfold rs_post. cbv zeta. generalize (clobber st1). intros C. destruct C. reflexivity. Qed.

Lemma arstage_leaf_ok : RstageSound.arstage_leaf AI ACCT UNIV Cw OPS file OTHER MP PB.
Proof.
  unfold RstageSound.arstage_leaf.
  intros st K E ms mo r hargs wnl st1 kb X off n' wlen rgb L RNG sta LBa aw HS HPB HK PRE SO F3 CNT WL OT FB CB PFX LO0 RW EQoff EQn CP FS CF AH MI
         BOT LO SPT NB SUM LOWD HID FLEN EA0 EA1 EA2 ms' mo' HQ HMP' HMI' OTH ACP.
  set (R := ms_regs ms) in *. set (Db := bv_unsigned (ev E kb)) in *. set (Xz := bv_unsigned (den E X)) in *.
  set (nsv := getr st X12) in *. set (nZ := bv_unsigned (den E nsv)) in *. set (wlenZ := bv_unsigned (den E wlen)) in *.
  set (D := Db + Xz) in *. set (m := ms_mem ms) in *.
  destruct HQ as (t0 & t1 & t2 & a1' & a2' & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & m' & EMS & MU & WM & MINV' & STK' & DSTP & SRCP).
  rewrite EA0, EA2 in MU, DSTP. rewrite EA1 in SRCP.
  pose proof atop_range as ATR. pose proof (so_facts _ _ _ _ _ _ HS) as Hfs.
  match type of EMS with ms' = MS ?RR _ _ _ _ _ _ => set (R' := RR) in * end.
  set (Fv := CtrFree.cfvF R'). set (Gv := fun (_ _ : Z) => Z_to_bv 8 0). set (E' := CtrFrame.E' E st Fv Gv).
  destruct (HeapCtr.call_pre_inv st r CP) as (FOK & ra0 & Hra0 & WT0 & LT0 & ER).
  assert (RAEQ : AP.getr R 1%bv = Z_to_bv 64 (to_Z r)).
  { unfold R. rewrite <- HeapCtr.reg_of_X1, (GlueA.getr_RA asegs OPS E st ms mo HS X1), Hra0, ER.
    assert (ERA : ra0 = wlit (wl ra0)) by (destruct ra0 as [t l]; cbn in WT0 |- *; subst t; reflexivity). rewrite ERA at 1. apply HeapCtr.den_wlit. }
  assert (EMS' : ms' = CtrFrame.ms' ms r R' m').
  { rewrite EMS. unfold CtrFrame.ms'. f_equal. rewrite RAEQ. apply ret_pc_even.
    - pose proof (int_range r) as RR. rewrite two63_eq in RR. lia.
    - pose proof (HeapCtr.call_pre_even st r CP) as EV.
      pose proof (land_mk r 1%uint63 ltac:(change (to_Z 1%uint63) with 1; lia)) as LM.
      change (PrimInt63.sub (PrimInt63.lsl 1 1) 1)%uint63 with 1%uint63 in LM. rewrite EV in LM. change (to_Z 0%uint63) with 0 in LM.
      change (2 ^ to_Z 1%uint63) with 2 in LM. lia. }
  destruct (clobber_fields st1) as (_ & FF & RV & RG & FS0 & OP & PV & NXc).
  destruct (CtrFrame.st1_fields st st1 FS) as (_ & _ & FF1 & RV1 & FS1 & OP1 & PV1 & NX1).
  assert (RVN : s_resv st = RNone) by (unfold call_pre in CP; destruct (s_resv st); try discriminate CP; reflexivity).
  pose proof (HeapCtr.fresh_ok_inv st FOK) as (SVB & _).
  destruct (CtrFrame.SVB_parts st FOK) as (RFB & _ & _ & _ & _ & OPB).
  assert (VB10 : sv_vars_below (s_next st) (getr st X10) = true) by exact (PlanS.rf_allb_get _ _ _ RFB X10).
  assert (DVP : den E' (getr st X10) = AP.getr R' 10%bv).
  { unfold E'. rewrite (CtrFrame.den_E' E st Fv Gv _ VB10). symmetry. exact (GlueA.getr_RA asegs OPS E st ms mo HS X10). }

  pose proof (phaseA_ms AI IMGX IMGX_aci ACCT UNIV Cw OPS AI_fake OPS_holds1 OPS_fp1 OPS_cov1 OPS_frame_other OPS_fp_other OTHER OPS_mo_other OPS_cov0_img
                st E ms mo r hargs wnl st1 L RNG sta LBa aw m' R' mo' D nZ 2240 (getr st X10) (s_next (clobber st1)) HS CP FS CF AH BOT LO SPT
                ltac:(unfold AIMG_HI in *; lia) (or_introl HID) ltac:(lia) MU WM MI MINV' STK'
                ltac:(intros rg Hrg; unfold CtrFrame.kept_regsA in Hrg; cbn [In] in Hrg; repeat (destruct Hrg as [<-|Hrg]; [reflexivity|]); destruct Hrg)
                DVP OTH HMI' ACP) as HSA.
  fold Fv Gv E' in HSA. fold m in HSA.
  set (mj := mjoinR D (D + nZ) m m') in *.
  idtac "RP-A".

  pose proof CF as CF0.
  destruct CF0 as (LB & ks & offs & rss & ksp & nn & md & A & nw & rest & SPR & Hksp & SPE & K16 & LOSP & FLOOR & Hf & Hc & Eh & Tnw & Nn & Ln & N255
                   & NW & AN & AJ & TS & WF & HC & AWden & (W & WOF & ARW & TI)).
  destruct (HeapCtrB.nonstack_windows_In E nn rest wnl kb wlen CtrLib.K_BLOCK NW (HeapCtrB.win_lookup_In _ _ _ _ WL)) as (Kb0 & _ & _ & INWb).
  assert (Kb0' : PrimInt63.eqb kb 0%uint63 = false) by (apply Uint63.eqb_false_spec; exact Kb0).
  pose proof (bv_unsigned_in_range 64 (den E X)) as XR. change (bv_modulus 64) with (2 ^ 64) in XR. fold Xz in XR.
  assert (KZ0 : keyZ 0%uint63 = 0) by reflexivity.
  destruct (CallA.sp_region_inv st ks offs rss SPR) as (_ & Hrs & _).
  assert (NKS : kb <> ks).
  { intros Q. rewrite Q, Hrs in FB. injection FB as Q2. rewrite Q2 in FLOOR. unfold loZ in FLOOR. rewrite LO0, KZ0 in FLOOR.
    rewrite <- Q in FLOOR. fold Db in FLOOR. unfold D in HID. lia. }
  assert (FB1 : IMap.find kb (s_regs st1) = Some rgb).
  { rewrite (CtrFrame.st1_regs st st1 FS ks offs rss ksp SPR Hksp).
    rewrite IMap.find_add_other; [exact FB| exact (so_bst _ _ _ _ _ _ HS)| intros Q; apply NKS; symmetry; exact Q]. }

  assert (KT : W64.weqb CtrLib.K_BLOCK ActrA.K_TWIN = false) by reflexivity.
  destruct (window_block_k AI ACCT UNIV Cw AI_fake Cw_sub_ghost E st ms mo r hargs wnl L RNG sta LBa aw kb wlen CtrLib.K_BLOCK 0 wlenZ CF WL KT
              ltac:(vm_compute; congruence) ltac:(vm_compute; congruence) ltac:(vm_compute; split; [discriminate| reflexivity]) ltac:(lia) ltac:(lia) ltac:(unfold wlenZ; lia)) as (p & Ab & nb & HINB & BA1 & BA2).
  fold Db in BA1, BA2.
  assert (UBW : forall a, Db <= a < Db + wlenZ -> uband a).
  { intros a Ha. exact (Op.blk_band AI AI_fake L RNG sta LBa m (HB p Ab nb) a AH HINB ltac:(cbn [ab_addr ab_size]; lia)). }
  idtac "RP-B0".

  set (hi' := CtrB.new_hi (s_facts st) X nsv). set (rb' := Region 0%uint63 hi' true (BGBlob 4%uint63 0%uint63) IMap.empty).
  destruct (CtrFrame.reg_E' OPS E st ms mo HS FOK Fv Gv kb rgb FB) as (EKb & EHb & _ & _). fold E' in EKb, EHb.
  assert (VX : sv_vars_below (s_next st) X = true) by exact (RstageCtr.sym_offset_vars_below _ _ _ _ _ VB10 SO).
  assert (Vn : sv_vars_below (s_next st) nsv = true) by exact (PlanS.rf_allb_get _ _ _ RFB X12).
  pose proof (bv_unsigned_in_range 64 (den E wlen)) as WLR. change (bv_modulus 64) with (2 ^ 64) in WLR. fold wlenZ in WLR.
  assert (DEF : bv_unsigned (den E (sv_alu ALU_ADD X nsv)) = Xz + nZ).
  { rewrite den_sv_alu. cbn [alu64 alu]. rewrite bv_add_unsigned. fold Xz nZ. apply bv_wrap_small. change (bv_modulus 64) with (2 ^ 64). lia. }
  assert (HI' : sv_vars_below (s_next st) hi' = true /\ bv_unsigned (den E hi') = Xz + nZ).
  { unfold hi', CtrB.new_hi.
    assert (DFL : sv_vars_below (s_next st) (sv_alu ALU_ADD X nsv) = true /\ bv_unsigned (den E (sv_alu ALU_ADD X nsv)) = Xz + nZ).
    { split; [apply MemFX.MemFX.sv_vars_below_alu; [left; reflexivity| exact VX| exact Vn]| exact DEF]. }
    revert Vn DEF DFL SUM. unfold nZ. generalize nsv. intros n0 Vn DEF DFL SUM0.
    destruct n0 as [| |[] sz X'| | | | | | | |]; try exact DFL.
    destruct (known_eq (s_facts st) X' X) eqn:KQ; [| exact DFL].
    apply (HeapCtr.known_eq_sound E _ _ _ Hfs) in KQ.
    cbn [sv_vars_below] in Vn. apply andb_prop in Vn as [Vsz _]. split; [exact Vsz|].
    cbn [den alu64 alu] in SUM0 |- *. rewrite KQ, bv_sub_unsigned in SUM0 |- *. fold Xz in SUM0 |- *.
    pose proof (bv_unsigned_in_range 64 (den E sz)) as SR. change (bv_modulus 64) with (2 ^ 64) in SR.
    unfold bv_wrap in *. change (bv_modulus 64) with (2 ^ 64) in *.
    destruct (Z_lt_le_dec (bv_unsigned (den E sz)) Xz) as [LT|GE].
    - exfalso. replace ((bv_unsigned (den E sz) - Xz) mod 2 ^ 64) with (bv_unsigned (den E sz) - Xz + 2 ^ 64) in SUM0
        by (apply (Z.mod_unique_pos _ _ (-1)); lia). lia.
    - rewrite Z.mod_small by lia. lia. }
  destruct HI' as [Vhi EHI0].
  assert (EHI : hiZ E' rb' = Xz + nZ).
  { unfold hiZ, rb'. cbn [rg_hi]. unfold E'. rewrite (CtrFrame.den_E' E st Fv Gv _ Vhi). exact EHI0. }
  assert (EL : loZ rb' = 0) by reflexivity.

  destruct (block_range_cells AI L RNG sta LBa m p Ab nb Db (Xz + nZ) AH HINB ltac:(lia) ltac:(lia) ltac:(lia)) as (junkP & DSTALL).
  assert (MAPPED : forall a, Db <= a < Db + (Xz + nZ) -> m' (Z_to_bv 64 a) <> None).
  { intros a Ha. destruct DSTALL as [_ (_ & _ & WV)]. cbn [cells_size csize Nat.add] in WV. rewrite Nat.add_0_r, Z2Nat.id in WV by lia.
    pose proof (WM _ (WV (a - Db) ltac:(lia))) as WV'. replace (Db + (a - Db)) with a in WV' by lia.
    rewrite (AImg.ref_wview_overlay m' (AM.wa a)) in WV'; [exact WV'|].
    pose proof (bv_unsigned_in_range 64 (ev E kb)) as RDb. change (bv_modulus 64) with (2 ^ 64) in RDb. fold Db in RDb.
    assert (AR : 0 <= a < 2 ^ 64) by (unfold D in HID; lia).
    right. rewrite (ReadPost.wa_u a AR). pose proof (UBW a ltac:(lia)) as U. unfold uband, AIMG_HI, KLS in U. lia. }
  idtac "RP-B1a".
  pose proof (bv_unsigned_in_range 64 (ev E kb)) as RDb. change (bv_modulus 64) with (2 ^ 64) in RDb. fold Db in RDb.
  assert (A64 : forall a, Db <= a < Db + wlenZ -> 0 <= a < 2 ^ 64 /\ 0x62f000 <= a).
  { intros a Ha. pose proof (UBW a Ha) as U. unfold uband, AIMG_HI, KLS in U. lia. }

  assert (FINAL : forall a, D <= a < D + nZ -> mj (AM.wa a) = m (AM.wa a)) by (intros a Ha; unfold mj, mjoinR; rewrite (ReadPost.wa_u a (proj1 (A64 a ltac:(unfold D in *; lia)))); unfold in_rng; replace ((D <=? a) && (a <? D + nZ)) with true by lia; reflexivity).
  assert (OUTSIDE : forall a, 0 <= a < 2 ^ 64 -> ~ (D <= a < D + nZ) -> mj (AM.wa a) = m' (AM.wa a)).
  { intros a Ha N. unfold mj, mjoinR. rewrite (ReadPost.wa_u a Ha). unfold in_rng. replace ((D <=? a) && (a <? D + nZ)) with false by lia. reflexivity. }
  assert (EBF : eb E' 4%uint63 = file) by exact (PB_file _ HPB).
  assert (RO' : region_ok asegs (s_priv st) E' m' kb rb').
  { destruct DSTP as [[_ BY] _]. cbn [cells_bytes cbytes] in BY. rewrite app_nil_r in BY. destruct BY as (_ & _ & BY). rewrite stage_src_len in BY.
    constructor; rewrite ?EHI, ?EL, ?EKb; fold Db.
    - cbn. exact I.
    - intros _. unfold two64. unfold D in HID. lia.
    - intros _ a Ha. pose proof (MAPPED a ltac:(lia)) as MP1. destruct (A64 a ltac:(lia)) as [AR A6].
      split; [| split].
      + unfold rb. destruct (m' (Z_to_bv 64 a)); [discriminate| exfalso; exact (MP1 eq_refl)].
      + intros _. apply (GlueA.wb_wviewA asegs). rewrite (AImg.ref_wview_overlay m' (AM.wa a)); [exact MP1|]. right. rewrite (ReadPost.wa_u a AR). lia.
      + exact (UnreggPre.no_seg_above a A6).
    - intros g gr Hg. cbn in Hg. discriminate Hg.
    - intros g gr c ii Hg. cbn in Hg. discriminate Hg.
    - intros o H1 _ _. specialize (H1 Kb0'). unfold bg_byte. cbn [rb' rg_bg]. change (to_Z 0%uint63) with 0. rewrite Z.sub_0_r, EBF.
      destruct (A64 (Db + o) ltac:(lia)) as [AR A6].
      destruct (Z_lt_le_dec o Xz) as [LT|GE].
      +
        unfold prefix_ok in PFX. apply orb_prop in PFX. destruct PFX as [PFX|X0].
        2:{ apply (HeapCtr.known_eq_sound E _ _ _ Hfs) in X0. exfalso. unfold Xz in LT. rewrite X0 in LT. cbn [den] in LT. rewrite wbv_unsigned, wzero_ok in LT. lia. }
        apply andb_prop in PFX as [BGP HIP]. destruct (rg_bg rgb) as [| | | |j sh] eqn:BGB; try discriminate BGP.
        apply andb_prop in BGP as [J4 SH0]. apply Uint63.eqb_correct in J4. apply Uint63.eqb_correct in SH0. subst j sh.
        apply (HeapCtr.known_eq_sound E _ _ _ Hfs) in HIP.
        pose proof (ro_bg _ _ _ _ _ _ (so_reg _ _ _ _ _ _ HSA kb rgb FB1) o
                      ltac:(intros _; unfold loZ; rewrite LO0, KZ0, EHb; unfold hiZ; rewrite HIP; fold Xz; lia)
                      ltac:(intros X1; rewrite Kb0' in X1; discriminate X1) ltac:(intros g gr _ F; rewrite CB in F; cbn in F; discriminate F)) as G.
        unfold bg_byte in G. rewrite BGB in G. change (to_Z 0%uint63) with 0 in G. rewrite Z.sub_0_r, EBF, EKb in G. fold Db in G.
        cbn [ms_mem CtrFrame.ms'] in G. rewrite <- G. apply ReadPost.rb_ext. symmetry. apply (OUTSIDE (Db + o) AR). unfold D. lia.
      +
        rewrite (GlueA.rb_mrdA asegs). replace (Db + o) with (D + Z.of_nat (Z.to_nat (o - Xz))) by (unfold D; lia). rewrite BY by lia.
        unfold stage_src. rewrite nth_error_map, nth_error_seq. destruct (Nat.ltb_spec (Z.to_nat (o - Xz)) (Z.to_nat nZ)); [|lia]. cbn [option_map].
        f_equal. f_equal. lia. }
  idtac "RP-B1b".

  assert (REGT : forall k2 r2, IMap.find k2 (s_regs st1) = Some r2 ->
            exists r2', IMap.find k2 (s_regs st) = Some r2' /\ loZ r2 = loZ r2' /\ hiZ E' r2 = hiZ E r2' /\ ev E' k2 = ev E k2).
  { intros k2 r2 H. rewrite (CtrFrame.st1_regs st st1 FS ks offs rss ksp SPR Hksp) in H. destruct (Uint63.eqb ks k2) eqn:Q.
    - apply Uint63.eqb_correct in Q. subst k2. rewrite IMap.find_add_same in H by exact (so_bst _ _ _ _ _ _ HS). injection H as <-.
      destruct (CtrFrame.reg_E' OPS E st ms mo HS FOK Fv Gv ks rss Hrs) as (EK & EH & _). exists rss. split; [exact Hrs|]. split; [reflexivity|]. split; [exact EH| exact EK].
    - apply Uint63.eqb_false_spec in Q. rewrite IMap.find_add_other in H by (exact (so_bst _ _ _ _ _ _ HS) || exact Q).
      destruct (CtrFrame.reg_E' OPS E st ms mo HS FOK Fv Gv k2 r2 H) as (EK & EH & _). exists r2. split; [exact H|]. split; [reflexivity|]. split; [exact EH| exact EK]. }
  assert (ARGT : forall o, In o (s_ops st) -> map (den E') (op_args o) = map (den E) (op_args o)).
  { intros o Ho. apply (CtrFrame.map_den_E' E st Fv Gv). exact (proj1 (forallb_forall _ _) OPB o Ho). }
  assert (HS1 : st_ok asegs OPS E'
            (SS r (rf_set (s_rf (clobber st1)) X10 (getr st X10)) (s_ff st) (s_resv st) (IMap.add kb rb' (s_regs st1)) (s_facts st) (s_ops st) (s_priv st) (s_next (clobber st1)))
            (MS R' (ms_fregs ms) (Z_to_bv 64 (to_Z r)) (ms_fcsr ms) None m' (seg_rom asegs)) mo').
  { apply (st_ok_based_replace_g asegs OPS E' _ R' (ms_fregs ms) (Z_to_bv 64 (to_Z r)) (ms_fcsr ms) None mj m' (seg_rom asegs) mo' kb rgb rb' HSA FB1 Kb0').
    -
      intros a Ha NC. unfold two64 in Ha. cbn [s_regs s_ops] in *.
      assert (INB : Db <= a < Db + wlenZ).
      { destruct NC as [RGa|CH]; [rewrite EHI, EL, EKb in RGa; fold Db in RGa; lia|].
        destruct (Z_lt_le_dec a D) as [L1|G1]; [exfalso; apply CH; symmetry; apply (OUTSIDE a ltac:(lia)); lia|].
        destruct (Z_lt_le_dec a (D + nZ)) as [L2|G2]; [unfold D in *; lia| exfalso; apply CH; symmetry; apply (OUTSIDE a ltac:(lia)); lia]. }
      pose proof (UBW a INB) as UB. split; [| split].
      + intros k2 r2 H2 NK2 K20 RG2. destruct (REGT k2 r2 H2) as (r2' & F2 & L2 & H2' & EK2). rewrite L2, H2', EK2 in RG2.
        exact (zone_regions E st ms mo HS r hargs wnl L RNG sta LBa aw CF kb wlen WL OT a INB UB k2 r2' F2 NK2 K20 RG2).
      + exact (UnreggPre.no_seg_above a (proj2 (A64 a INB))).
      + intros o Ho FP. rewrite (ARGT o Ho) in FP.
        exact (zone_ops E st ms mo r hargs wnl L RNG sta LBa aw CF kb wlen WL a ltac:(unfold two64; lia) INB UB o Ho FP).
    -
      intros x H. unfold mj, mjoinR in H. destruct (in_rng D (D + nZ) (bv_unsigned x)) eqn:IS; [| exact H].
      unfold in_rng in IS. rewrite <- (Z_to_bv_bv_unsigned x). apply MAPPED. unfold D in IS. lia.
    - intros x b Hx seg Hs. pose proof (MINV' x b Hx) as RO. unfold AM.ro_addr in RO. rewrite Hs in RO. apply negb_false_iff in RO. exact RO.
    - exact RO'.
    -
      intros a RGa. rewrite EHI, EL, EKb in RGa. fold Db in RGa. right. apply Exists_exists. exists (HEAP_ID, map (den E') hargs). split.
      + unfold insts. apply in_map_iff. exists (OpI HEAP_ID hargs). split; [reflexivity|]. cbn [s_ops]. exact (UnreggPre.find_op_In _ _ _ Hf).
      + cbn [fst snd]. apply OPS_cov1. split; [reflexivity|]. eexists _, _, _, _.
        split; [exact (CtrFrame.DEC' E st FOK Fv Gv nn rest hargs md A nw Hf Eh Tnw Nn Ln)| left].
        unfold in_ws, heap_ws. apply in_ivs_In. eexists. split; [apply in_map; apply filter_In; split; [exact INWb| reflexivity]|].
        unfold in_iv, w_iv. cbn [w_lo w_len fst snd]. fold Db wlenZ. lia. }
  idtac "RP-B1".

  set (os' := set_op ReadC.RSTV_ID [sv_alu ALU_ADD off nsv; VL wzero] (s_ops st)).
  pose proof (HeapCtr.known_eq_sound E _ _ _ Hfs EQoff) as Eoff.
  assert (Voff : sv_vars_below (s_next st) off = true).
  { pose proof (proj1 (forallb_forall _ _) OPB _ (UnreggPre.find_op_In _ _ _ F3)) as V3. cbn [op_args forallb] in V3. apply andb_prop in V3 as [V3 _]. exact V3. }
  assert (RSVN : ReadPost.rstage_holds_v file (map (den E') [sv_alu ALU_ADD off nsv; VL wzero]) m').
  { cbn [map ReadPost.rstage_holds_v].
    assert (Vsum : sv_vars_below (s_next st) (sv_alu ALU_ADD off nsv) = true) by (apply MemFX.MemFX.sv_vars_below_alu; [left; reflexivity| exact Voff| exact Vn]).
    unfold E'. rewrite (CtrFrame.den_E' E st Fv Gv _ Vsum). cbn [den]. rewrite wbv_unsigned, wzero_ok.
    rewrite den_sv_alu. cbn [alu64 alu]. rewrite bv_add_unsigned, Eoff. fold Xz nZ. rewrite bv_wrap_small by (change (bv_modulus 64) with (2 ^ 64); lia).
    split; [lia|]. split; [lia|]. intros i Hi. lia. }
  idtac "RP-B2a".
  pose proof (st_ok_memops asegs OPS E' _ _ mo' mo' [] os' (s_next (clobber st1)) m' HS1 (Forall_nil _) HMI') as B2.
  idtac "RP-B2b".
  cbn [s_pc s_rf s_ff s_resv s_regs s_facts s_ops s_priv app] in B2.
  idtac "RP-B2c".
  assert (HS2 : st_ok asegs OPS E'
            (SS r (rf_set (s_rf (clobber st1)) X10 (getr st X10)) (s_ff st) (s_resv st) (IMap.add kb rb' (s_regs st1)) (s_facts st) os' (s_priv st) (s_next (clobber st1)))
            (MS R' (ms_fregs ms) (Z_to_bv 64 (to_Z r)) (ms_fcsr ms) None m' (seg_rom asegs)) mo').
  { apply B2.
    - apply (CtrFX.ops_hold_set_op1 OPS E' (s_ops st) ReadC.RSTV_ID [off; n'] _ m' mo' F3 (so_ops _ _ _ _ _ _ HS1)).
      apply OPS_holds_rstage'. exact RSVN.
    - apply (CtrFX.ops_apart_set_op1 asegs OPS E' (s_ops st) ReadC.RSTV_ID [off; n'] _ _ _ F3 (so_apart _ _ _ _ _ _ HS1)). apply OPS_fp_rstage.
    - intros a Ha. apply (OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Glue.Nodes.FXN.cov_keep OPS E' (s_ops st)); [| exact (so_cover _ _ _ _ _ _ HS1 a Ha)].
      intros o Ho [z Hz]. pose proof (OPS_cov1_heap _ _ _ Hz) as HID0. apply ReadPost.CS.set_op_keep; [exact Ho| rewrite HID0; reflexivity].
    - intros a _ _. reflexivity.
    - intros a b Hb Hnone. change (m' a = None) in Hnone. rewrite Hnone in Hb. discriminate Hb. }
  idtac "RP-B2d".

  apply (HK _ (or_introl eq_refl) E' ms' mo' (CtrFrame.EXT E st Fv Gv) HMP').
  rewrite EMS'. unfold CtrFrame.ms'.
  rewrite (rs_post_shape st st1 r kb X off). cbv zeta. rewrite FF, RV, RG, FS0, OP, PV, FF1, RV1, FS1, OP1, PV1.
  exact HS2.
Qed.
End Leaf.

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
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Ctr.Lib OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Ctr.Defs OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Ctr.DefsA OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Ctr.DefsB.
Import Ledger.TwinB Op.TwinB Adeq.TwinB.

Import ListNotations.
Import W64 Val OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Mem.Mem FI St OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Step.Step Plan PlanS CtrLib HeapOp.
Open Scope Z_scope.
Unset Lia Cache.

Import Actr.TwinB.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.W64Proofs OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.ValProofs OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.MemProofs OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.StepSoundBase.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Br.CtrFX.

Import ReadC.TwinB ReadPre.TwinB MemOps.TwinB RstageC.TwinB MemsetFX.TwinB RangePre.TwinB MemsetPre.TwinB MemsetPost.TwinB RegRepl.TwinB RstageSound.TwinB.

Unset Nia Cache. Unset Nra Cache.
Import ValP MemP StepB CtrFX ActrA RstageC.TwinB.RstageC.
Module IMC := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.I_asan_memcpy.TwinB.I_memcpy.

Section Leaf.
Context {rc : runConstT}.
Variable AI : AMallocIface2.
Variable IMGX : list iv.
Hypothesis IMGX_aci : imgx_ok AI IMGX.
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
Hypothesis Cw_sub_ghost : forall md ca LB ws m w g a, cw_holds Cw md ca LB ws m -> In w ws -> In g ws ->
  K_SUB <= w_kind w < K_GHOST -> K_GHOST <= w_kind g -> in_iv (w_iv w) a -> in_iv (w_iv g) a -> False.
Variable MP : Model -> Prop.
Variable PB : (int -> list byte) -> Prop.
Variable file : list byte.

Definition uband (a : Z) : Prop := (AIMG_HI <= a < KLS) \/ (0x10007fff8000 <= a < ATOP).
Lemma shad_not_uband : forall a', 0 <= a' < 2 ^ 47 -> ~ uband (shad a').
Proof.
  intros a' H U. pose proof atop_range as ATR. unfold uband, AIMG_HI, KLS in U.
  assert (0x7fff8000 <= shad a' < 0x10007fff8000) by (unfold shad, ASHOFF; rewrite Z.shiftr_div_pow2 by lia; change (2 ^ 3) with 8; Z.div_mod_to_equations; lia). lia.
Qed.

Section Zone.
Variables (E : env) (st : sstate) (ms : machine_state) (mo : Model).
Hypothesis HS : st_ok bsegs OPS E st ms mo.
Variables (r : int) (hargs : list sv) (wnl : list (int * sv * w64)) (L : alayout) (RNG : footprint) (sta : astate) (LBa : list ablock) (aw : word).
Hypothesis CF : CtrPre.TwinB.acallG AI ACCT UNIV Cw E st ms mo r hargs wnl L RNG sta LBa aw.
Hypothesis AH : AHEAP AI L RNG sta LBa (ms_mem ms).
Variables (kb : int) (wlen : sv).
Hypothesis WL : CtrA.win_lookup wnl kb = Some (wlen, CtrLib.K_BLOCK).
Hypothesis OT : others_twins wnl kb = true.
Let Db := bv_unsigned (ev E kb).
Let wlenZ := bv_unsigned (den E wlen).

Lemma zone_regions : forall a, Db <= a < Db + wlenZ -> uband a ->
  forall k2 r2, IMap.find k2 (s_regs st) = Some r2 -> k2 <> kb -> PrimInt63.eqb k2 0%uint63 = false ->
  ~ (bv_unsigned (ev E k2) + loZ r2 <= a < bv_unsigned (ev E k2) + hiZ E r2).
Proof.
  intros a INB UB k2 r2 Hk2 NK K20 RG. pose proof atop_range as ATR.
  destruct CF as (LB & ks & offs & rss & ksp & nn & md & A & nw & rest & SPR & Hksp & SPE & K16 & LOSP & FLOOR & Hf & Hc & Eh & Tnw & Nn & Ln & N255
                  & NW & AN & AJ & TS & WF & HC & AWden & (W & WOF & ARW & TI)).
  assert (KN0 : k2 <> 0%uint63) by (intros ->; discriminate K20).
  pose proof ARW as [HWW _].

  assert (TWINWIN : forall k len kd, CtrA.win_lookup wnl k = Some (len, kd) -> k <> kb ->
            forall x, bv_unsigned (ev E k) <= x < bv_unsigned (ev E k) + bv_unsigned (den E len) -> ~ uband x).
  { intros k len kd WLk NKb x Hx U. pose proof (HeapCtrB.TwinB.win_lookup_In _ _ _ _ WLk) as Ik.
    pose proof (proj1 (forallb_forall _ _) OT _ Ik) as Q. cbv beta iota in Q.
    replace (PrimInt63.eqb k kb) with false in Q by (symmetry; apply Uint63.eqb_false_spec; exact NKb). cbn [orb] in Q. apply weqb_eq in Q. subst kd.
    destruct (HeapCtrB.TwinB.nonstack_windows_In E nn rest wnl k len K_TWIN NW Ik) as (_ & _ & _ & INW).
    destruct TI as (_ & T2 & _). destruct (T2 _ INW eq_refl) as (b & HbT & EIV). unfold w_iv, twin_iv in EIV. cbn [w_lo w_len] in EIV. injection EIV as E1 E2.
    destruct (LB_twin_facts AI ACCT UNIV W _ LB (ms_mem ms) mo b HWW HbT) as (T1 & T2' & _).
    unfold uband, AIMG_HI, KLS in U. rewrite E1, E2 in Hx. lia. }
  destruct (CallA.TwinB.aregion_just_sound bsegs OPS E st ms mo wnl ks offs rss k2 r2 HS SPR AJ Hk2 KN0) as [[EQ TOPk]|[NE [(len0 & kd0 & WLS & LZ & HZ)|[[J1 J2]|VJ]]]].
  -
    subst k2. destruct (CallA.TwinB.sp_region_inv st ks offs rss SPR) as (_ & Hrs & _). rewrite Hrs in Hk2. injection Hk2 as <-.
    unfold uband, AIMG_HI, KLS in UB. lia.
  - apply (TWINWIN k2 len0 kd0 WLS NK a); [rewrite LZ in RG; lia| exact UB].
  - rewrite (CtrFrame.TwinB.SP_den OPS E st ms mo HS) in J1. unfold uband, AIMG_HI, KLS in UB.
    assert (SPF : ATOP + 4096 <= bv_unsigned (AP.getr (ms_regs ms) 2%bv)) by (rewrite SPE; lia). lia.
  -
    destruct VJ as [VJ|SL]; [| exfalso; pose proof (CtrPre.TwinB.sliver_low OPS E st ms mo ks offs rss k2 r2 hargs nn md A nw rest LB a HS SPR Hk2 KN0 NE SL Hf Eh Tnw Nn Ln WF RG) as SLO; unfold uband, AIMG_HI, KLS in UB; lia].
    pose proof (CallV.TwinB.view_just_sound bsegs OPS E st ms mo wnl ks offs rss k2 r2 HS SPR Hk2 KN0 VJ) as VS. unfold CallV.TwinB.view_sem in VS. cbv zeta in VS.
    destruct VS as [(_ & blo & bhi & SHZ & BH & BL)|[(hs & n0 & sh & len1 & ZV & BT & _ & WLs & V1 & V2)|[(VI & v & Hv & V1 & V2)|(shD & kbD & nD & lenD & WLD & BTD & WLkD & STD & TND & ROD & LOD & HID)]]].
    + destruct (SHZ a RG) as (a' & Ha' & ->).
      assert (A0 : 0 <= a').
      { destruct BL as [(wlo & _ & ->)|[(rs & Frs & ->)|BL]].
        - pose proof (bv_unsigned_in_range 64 (den E (VP STACK_ID wlo))). lia.
        - destruct (CallA.TwinB.sp_region_inv st ks offs rss SPR) as (_ & Hrs & _). rewrite Hrs in Frs. injection Frs as <-. lia.
        - pose proof (bv_unsigned_in_range 64 (den E (getr st X2))). lia. }
      assert (SZ : CallV.TwinB.shz a' = shad a') by (unfold CallV.TwinB.shz, shad, ASHOFF; rewrite Z.shiftr_div_pow2 by lia; change (2 ^ 3) with 8; lia).
      rewrite SZ in UB. exact (shad_not_uband a' ltac:(lia) UB).
    + assert (NKS : sh <> kb) by (intros ->; rewrite WL in WLs; assert (Q : CtrLib.K_BLOCK = K_TWIN) by congruence; vm_compute in Q; discriminate Q).
      apply (TWINWIN sh len1 K_TWIN WLs NKS a); [lia| exact UB].
    + unfold ActrA.IMGSH in Hv. cbn [In] in Hv. destruct Hv as [<-|[]]. cbn [fst snd] in V1, V2. unfold uband, AIMG_HI, KLS in UB. lia.
    +
      assert (NKSD : shD <> kb) by (intros ->; rewrite WL in WLD; assert (Q : CtrLib.K_BLOCK = K_TWIN) by congruence; vm_compute in Q; discriminate Q).
      apply (TWINWIN shD lenD K_TWIN WLD NKSD a); [lia| exact UB].
Qed.

Lemma zone_ops : forall a, 0 <= a < two64 -> Db <= a < Db + wlenZ -> uband a ->
  forall o, In o (s_ops st) -> ~ Exists (fun iv => fst iv <= a < snd iv) (op_fp OPS (op_id o) (map (den E) (op_args o))).
Proof.
  intros a Ha INB UB o Ho FP. pose proof atop_range as ATR.
  destruct CF as (LB & ks & offs & rss & ksp & nn & md & A & nw & rest & SPR & Hksp & SPE & K16 & LOSP & FLOOR & Hf & Hc & Eh & Tnw & Nn & Ln & N255
                  & NW & AN & AJ & TS & WF & HC & AWden & (W & WOF & ARW & TI)).
  destruct (PrimInt63.eqb (op_id o) HEAP_ID) eqn:QH.
  - apply Uint63.eqb_correct in QH. pose proof (ReadPost.TwinB.count_one_args HEAP_ID (s_ops st) o hargs Ho QH Hc Hf) as EA.
    rewrite QH, EA, OPS_fp1, Eh in FP.
    apply (proj1 (fp_spec IMGX _ _ _ _ _ a (decode_hargs E md A nw rest nn Tnw Nn Ln))) in FP as (_ & _ & NWS).
    apply NWS. destruct (HeapCtrB.TwinB.nonstack_windows_In E nn rest wnl kb wlen CtrLib.K_BLOCK NW (HeapCtrB.TwinB.win_lookup_In _ _ _ _ WL)) as (_ & _ & _ & INW).
    unfold in_ws. apply in_ivs_In. eexists. split; [apply in_map; exact INW|]. unfold in_iv, w_iv. cbn [w_lo w_len fst snd]. fold Db wlenZ. lia.
  - apply Uint63.eqb_false_spec in QH. destruct (OPS_fp_other _ _ a QH FP) as [(iv0 & Hi & RRa)|[(a' & (iv0 & Hi & RRa) & ->)|(a' & STK & ->)]].
    + pose proof (AI_aci_img AI iv0 Hi) as HIa. unfold uband, AIMG_HI, KLS in *. lia.
    + pose proof (AI_aci_img AI iv0 Hi) as HIa. pose proof (AI_aci_lo AI iv0 Hi) as LOa. unfold AIMG_HI in HIa.
      exact (shad_not_uband a' ltac:(lia) UB).
    +
      exact (shad_not_uband a' ltac:(lia) UB).
Qed.
End Zone.

Hypothesis OPS_holds_rstage' : forall args m mo, ReadPost.TwinB.rstage_holds_v file args m -> op_holds OPS ReadC.TwinB.ReadC.RSTV_ID args m mo.
Hypothesis OPS_fp_rstage : forall args args', op_fp OPS ReadC.TwinB.ReadC.RSTV_ID args = op_fp OPS ReadC.TwinB.ReadC.RSTV_ID args'.
Hypothesis OPS_cov1_heap : forall id args z, op_cov1 OPS id args z -> id = HEAP_ID.
Hypothesis PB_file : forall b, PB b -> b 4%uint63 = file.

Lemma setr_X10 : forall S v, setr S X10 v = SS (s_pc S) (rf_set (s_rf S) X10 v) (s_ff S) (s_resv S) (s_regs S) (s_facts S) (s_ops S) (s_priv S) (s_next S).
Proof. reflexivity. Qed.

Lemma rs_post_shape : forall st st1 r kb X off, rs_post st st1 r kb X off =
  let C := clobber st1 in
  SS r (rf_set (s_rf C) X10 (getr st X10)) (s_ff C) (s_resv C)
     (IMap.add kb (Region 0%uint63 (CtrB.new_hi (s_facts st) X (getr st X12)) true (BGBlob 4%uint63 0%uint63) IMap.empty) (s_regs C))
     (s_facts C) (set_op ReadC.TwinB.ReadC.RSTV_ID [sv_alu ALU_ADD off (getr st X12); VL wzero] (s_ops C)) (s_priv C) (s_next C).
Proof. intros st st1 r kb X off. unfold rs_post. cbv zeta. generalize (clobber st1). intros C. destruct C. reflexivity. Qed.

Lemma arstage_leaf_ok : RstageSound.TwinB.arstage_leaf AI ACCT UNIV Cw OPS file OTHER MP PB.
Proof.
  unfold RstageSound.TwinB.arstage_leaf.
  intros st K E ms mo r hargs wnl st1 kb X off n' wlen rgb L RNG sta LBa aw HS HPB HK PRE SO F3 CNT WL OT FB CB PFX LO0 RW EQoff EQn CP FS CF AH MI
         BOT LO SPT NB SUM LOWD HID FLEN EA0 EA1 EA2 ms' mo' HQ HMP' HMI' OTH ACP.
  set (R := ms_regs ms) in *. set (Db := bv_unsigned (ev E kb)) in *. set (Xz := bv_unsigned (den E X)) in *.
  set (nsv := getr st X12) in *. set (nZ := bv_unsigned (den E nsv)) in *. set (wlenZ := bv_unsigned (den E wlen)) in *.
  set (D := Db + Xz) in *. set (m := ms_mem ms) in *.
  destruct HQ as (t0 & t1 & t2 & a1' & a2' & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & m' & EMS & MU & WM & MINV' & STK' & DSTP & SRCP).
  rewrite EA0, EA2 in MU, DSTP. rewrite EA1 in SRCP.
  pose proof atop_range as ATR. pose proof (so_facts _ _ _ _ _ _ HS) as Hfs.
  match type of EMS with ms' = MS ?RR _ _ _ _ _ _ => set (R' := RR) in * end.
  set (Fv := CtrFree.TwinB.cfvF R'). set (Gv := fun (_ _ : Z) => Z_to_bv 8 0). set (E' := CtrFrame.TwinB.E' E st Fv Gv).
  destruct (HeapCtr.TwinB.call_pre_inv st r CP) as (FOK & ra0 & Hra0 & WT0 & LT0 & ER).
  assert (RAEQ : AP.getr R 1%bv = Z_to_bv 64 (to_Z r)).
  { unfold R. rewrite <- HeapCtr.TwinB.reg_of_X1, (GlueA.TwinB.getr_RA bsegs OPS E st ms mo HS X1), Hra0, ER.
    assert (ERA : ra0 = wlit (wl ra0)) by (destruct ra0 as [t l]; cbn in WT0 |- *; subst t; reflexivity). rewrite ERA at 1. apply HeapCtr.TwinB.den_wlit. }
  assert (EMS' : ms' = CtrFrame.TwinB.ms' ms r R' m').
  { rewrite EMS. unfold CtrFrame.TwinB.ms'. f_equal. rewrite RAEQ. apply ret_pc_even.
    - pose proof (int_range r) as RR. rewrite two63_eq in RR. lia.
    - pose proof (HeapCtr.TwinB.call_pre_even st r CP) as EV.
      pose proof (land_mk r 1%uint63 ltac:(change (to_Z 1%uint63) with 1; lia)) as LM.
      change (PrimInt63.sub (PrimInt63.lsl 1 1) 1)%uint63 with 1%uint63 in LM. rewrite EV in LM. change (to_Z 0%uint63) with 0 in LM.
      change (2 ^ to_Z 1%uint63) with 2 in LM. lia. }
  destruct (clobber_fields st1) as (_ & FF & RV & RG & FS0 & OP & PV & NXc).
  destruct (CtrFrame.TwinB.st1_fields st st1 FS) as (_ & _ & FF1 & RV1 & FS1 & OP1 & PV1 & NX1).
  assert (RVN : s_resv st = RNone) by (unfold call_pre in CP; destruct (s_resv st); try discriminate CP; reflexivity).
  pose proof (HeapCtr.TwinB.fresh_ok_inv st FOK) as (SVB & _).
  destruct (CtrFrame.TwinB.SVB_parts st FOK) as (RFB & _ & _ & _ & _ & OPB).
  assert (VB10 : sv_vars_below (s_next st) (getr st X10) = true) by exact (PlanS.rf_allb_get _ _ _ RFB X10).
  assert (DVP : den E' (getr st X10) = AP.getr R' 10%bv).
  { unfold E'. rewrite (CtrFrame.TwinB.den_E' E st Fv Gv _ VB10). symmetry. exact (GlueA.TwinB.getr_RA bsegs OPS E st ms mo HS X10). }

  pose proof (phaseA_ms AI IMGX IMGX_aci ACCT UNIV Cw OPS AI_fake OPS_holds1 OPS_fp1 OPS_cov1 OPS_frame_other OPS_fp_other OTHER OPS_mo_other OPS_cov0_img
                st E ms mo r hargs wnl st1 L RNG sta LBa aw m' R' mo' D nZ 2240 (getr st X10) (s_next (clobber st1)) HS CP FS CF AH BOT LO SPT
                ltac:(unfold AIMG_HI in *; lia) (or_introl HID) ltac:(lia) MU WM MI MINV' STK'
                ltac:(intros rg Hrg; unfold CtrFrame.TwinB.kept_regsA in Hrg; cbn [In] in Hrg; repeat (destruct Hrg as [<-|Hrg]; [reflexivity|]); destruct Hrg)
                DVP OTH HMI' ACP) as HSA.
  fold Fv Gv E' in HSA. fold m in HSA.
  set (mj := mjoinR D (D + nZ) m m') in *.
  idtac "RP-A".

  pose proof CF as CF0.
  destruct CF0 as (LB & ks & offs & rss & ksp & nn & md & A & nw & rest & SPR & Hksp & SPE & K16 & LOSP & FLOOR & Hf & Hc & Eh & Tnw & Nn & Ln & N255
                   & NW & AN & AJ & TS & WF & HC & AWden & (W & WOF & ARW & TI)).
  destruct (HeapCtrB.TwinB.nonstack_windows_In E nn rest wnl kb wlen CtrLib.K_BLOCK NW (HeapCtrB.TwinB.win_lookup_In _ _ _ _ WL)) as (Kb0 & _ & _ & INWb).
  assert (Kb0' : PrimInt63.eqb kb 0%uint63 = false) by (apply Uint63.eqb_false_spec; exact Kb0).
  pose proof (bv_unsigned_in_range 64 (den E X)) as XR. change (bv_modulus 64) with (2 ^ 64) in XR. fold Xz in XR.
  assert (KZ0 : keyZ 0%uint63 = 0) by reflexivity.
  destruct (CallA.TwinB.sp_region_inv st ks offs rss SPR) as (_ & Hrs & _).
  assert (NKS : kb <> ks).
  { intros Q. rewrite Q, Hrs in FB. injection FB as Q2. rewrite Q2 in FLOOR. unfold loZ in FLOOR. rewrite LO0, KZ0 in FLOOR.
    rewrite <- Q in FLOOR. fold Db in FLOOR. unfold D in HID. lia. }
  assert (FB1 : IMap.find kb (s_regs st1) = Some rgb).
  { rewrite (CtrFrame.TwinB.st1_regs st st1 FS ks offs rss ksp SPR Hksp).
    rewrite IMap.find_add_other; [exact FB| exact (so_bst _ _ _ _ _ _ HS)| intros Q; apply NKS; symmetry; exact Q]. }

  assert (KT : W64.weqb CtrLib.K_BLOCK ActrA.K_TWIN = false) by reflexivity.
  destruct (window_block_k AI ACCT UNIV Cw AI_fake Cw_sub_ghost E st ms mo r hargs wnl L RNG sta LBa aw kb wlen CtrLib.K_BLOCK 0 wlenZ CF WL KT
              ltac:(vm_compute; congruence) ltac:(vm_compute; congruence) ltac:(vm_compute; split; [discriminate| reflexivity]) ltac:(lia) ltac:(lia) ltac:(unfold wlenZ; lia)) as (p & Ab & nb & HINB & BA1 & BA2).
  fold Db in BA1, BA2.
  assert (UBW : forall a, Db <= a < Db + wlenZ -> uband a).
  { intros a Ha. exact (Op.TwinB.blk_band AI AI_fake L RNG sta LBa m (HB p Ab nb) a AH HINB ltac:(cbn [ab_addr ab_size]; lia)). }
  idtac "RP-B0".

  set (hi' := CtrB.new_hi (s_facts st) X nsv). set (rb' := Region 0%uint63 hi' true (BGBlob 4%uint63 0%uint63) IMap.empty).
  destruct (CtrFrame.TwinB.reg_E' OPS E st ms mo HS FOK Fv Gv kb rgb FB) as (EKb & EHb & _ & _). fold E' in EKb, EHb.
  assert (VX : sv_vars_below (s_next st) X = true) by exact (RstageCtr.TwinB.sym_offset_vars_below _ _ _ _ _ VB10 SO).
  assert (Vn : sv_vars_below (s_next st) nsv = true) by exact (PlanS.rf_allb_get _ _ _ RFB X12).
  pose proof (bv_unsigned_in_range 64 (den E wlen)) as WLR. change (bv_modulus 64) with (2 ^ 64) in WLR. fold wlenZ in WLR.
  assert (DEF : bv_unsigned (den E (sv_alu ALU_ADD X nsv)) = Xz + nZ).
  { rewrite den_sv_alu. cbn [alu64 alu]. rewrite bv_add_unsigned. fold Xz nZ. apply bv_wrap_small. change (bv_modulus 64) with (2 ^ 64). lia. }
  assert (HI' : sv_vars_below (s_next st) hi' = true /\ bv_unsigned (den E hi') = Xz + nZ).
  { unfold hi', CtrB.new_hi.
    assert (DFL : sv_vars_below (s_next st) (sv_alu ALU_ADD X nsv) = true /\ bv_unsigned (den E (sv_alu ALU_ADD X nsv)) = Xz + nZ).
    { split; [apply MemFX.MemFX.sv_vars_below_alu; [left; reflexivity| exact VX| exact Vn]| exact DEF]. }
    revert Vn DEF DFL SUM. unfold nZ. generalize nsv. intros n0 Vn DEF DFL SUM0.
    destruct n0 as [| |[] sz X'| | | | | | | |]; try exact DFL.
    destruct (known_eq (s_facts st) X' X) eqn:KQ; [| exact DFL].
    apply (HeapCtr.TwinB.known_eq_sound E _ _ _ Hfs) in KQ.
    cbn [sv_vars_below] in Vn. apply andb_prop in Vn as [Vsz _]. split; [exact Vsz|].
    cbn [den alu64 alu] in SUM0 |- *. rewrite KQ, bv_sub_unsigned in SUM0 |- *. fold Xz in SUM0 |- *.
    pose proof (bv_unsigned_in_range 64 (den E sz)) as SR. change (bv_modulus 64) with (2 ^ 64) in SR.
    unfold bv_wrap in *. change (bv_modulus 64) with (2 ^ 64) in *.
    destruct (Z_lt_le_dec (bv_unsigned (den E sz)) Xz) as [LT|GE].
    - exfalso. replace ((bv_unsigned (den E sz) - Xz) mod 2 ^ 64) with (bv_unsigned (den E sz) - Xz + 2 ^ 64) in SUM0
        by (apply (Z.mod_unique_pos _ _ (-1)); lia). lia.
    - rewrite Z.mod_small by lia. lia. }
  destruct HI' as [Vhi EHI0].
  assert (EHI : hiZ E' rb' = Xz + nZ).
  { unfold hiZ, rb'. cbn [rg_hi]. unfold E'. rewrite (CtrFrame.TwinB.den_E' E st Fv Gv _ Vhi). exact EHI0. }
  assert (EL : loZ rb' = 0) by reflexivity.

  destruct (block_range_cells AI L RNG sta LBa m p Ab nb Db (Xz + nZ) AH HINB ltac:(lia) ltac:(lia) ltac:(lia)) as (junkP & DSTALL).
  assert (MAPPED : forall a, Db <= a < Db + (Xz + nZ) -> m' (Z_to_bv 64 a) <> None).
  { intros a Ha. destruct DSTALL as [_ (_ & _ & WV)]. cbn [cells_size csize Nat.add] in WV. rewrite Nat.add_0_r, Z2Nat.id in WV by lia.
    pose proof (WM _ (WV (a - Db) ltac:(lia))) as WV'. replace (Db + (a - Db)) with a in WV' by lia.
    rewrite (BImg.ref_wview_overlay m' (AM.wa a)) in WV'; [exact WV'|].
    pose proof (bv_unsigned_in_range 64 (ev E kb)) as RDb. change (bv_modulus 64) with (2 ^ 64) in RDb. fold Db in RDb.
    assert (AR : 0 <= a < 2 ^ 64) by (unfold D in HID; lia).
    right. rewrite (ReadPost.TwinB.wa_u a AR). pose proof (UBW a ltac:(lia)) as U. unfold uband, AIMG_HI, KLS in U. lia. }
  idtac "RP-B1a".
  pose proof (bv_unsigned_in_range 64 (ev E kb)) as RDb. change (bv_modulus 64) with (2 ^ 64) in RDb. fold Db in RDb.
  assert (A64 : forall a, Db <= a < Db + wlenZ -> 0 <= a < 2 ^ 64 /\ 0x631000 <= a).
  { intros a Ha. pose proof (UBW a Ha) as U. unfold uband, AIMG_HI, KLS in U. lia. }

  assert (FINAL : forall a, D <= a < D + nZ -> mj (AM.wa a) = m (AM.wa a)) by (intros a Ha; unfold mj, mjoinR; rewrite (ReadPost.TwinB.wa_u a (proj1 (A64 a ltac:(unfold D in *; lia)))); unfold in_rng; replace ((D <=? a) && (a <? D + nZ)) with true by lia; reflexivity).
  assert (OUTSIDE : forall a, 0 <= a < 2 ^ 64 -> ~ (D <= a < D + nZ) -> mj (AM.wa a) = m' (AM.wa a)).
  { intros a Ha N. unfold mj, mjoinR. rewrite (ReadPost.TwinB.wa_u a Ha). unfold in_rng. replace ((D <=? a) && (a <? D + nZ)) with false by lia. reflexivity. }
  assert (EBF : eb E' 4%uint63 = file) by exact (PB_file _ HPB).
  assert (RO' : region_ok bsegs (s_priv st) E' m' kb rb').
  { destruct DSTP as [[_ BY] _]. cbn [cells_bytes cbytes] in BY. rewrite app_nil_r in BY. destruct BY as (_ & _ & BY). rewrite stage_src_len in BY.
    constructor; rewrite ?EHI, ?EL, ?EKb; fold Db.
    - cbn. exact I.
    - intros _. unfold two64. unfold D in HID. lia.
    - intros _ a Ha. pose proof (MAPPED a ltac:(lia)) as MP1. destruct (A64 a ltac:(lia)) as [AR A6].
      split; [| split].
      + unfold rb. destruct (m' (Z_to_bv 64 a)); [discriminate| exfalso; exact (MP1 eq_refl)].
      + intros _. apply (GlueA.TwinB.wb_wviewA bsegs). rewrite (BImg.ref_wview_overlay m' (AM.wa a)); [exact MP1|]. right. rewrite (ReadPost.TwinB.wa_u a AR). lia.
      + exact (UnreggPre.TwinB.no_seg_above a A6).
    - intros g gr Hg. cbn in Hg. discriminate Hg.
    - intros g gr c ii Hg. cbn in Hg. discriminate Hg.
    - intros o H1 _ _. specialize (H1 Kb0'). unfold bg_byte. cbn [rb' rg_bg]. change (to_Z 0%uint63) with 0. rewrite Z.sub_0_r, EBF.
      destruct (A64 (Db + o) ltac:(lia)) as [AR A6].
      destruct (Z_lt_le_dec o Xz) as [LT|GE].
      +
        unfold prefix_ok in PFX. apply orb_prop in PFX. destruct PFX as [PFX|X0].
        2:{ apply (HeapCtr.TwinB.known_eq_sound E _ _ _ Hfs) in X0. exfalso. unfold Xz in LT. rewrite X0 in LT. cbn [den] in LT. rewrite wbv_unsigned, wzero_ok in LT. lia. }
        apply andb_prop in PFX as [BGP HIP]. destruct (rg_bg rgb) as [| | | |j sh] eqn:BGB; try discriminate BGP.
        apply andb_prop in BGP as [J4 SH0]. apply Uint63.eqb_correct in J4. apply Uint63.eqb_correct in SH0. subst j sh.
        apply (HeapCtr.TwinB.known_eq_sound E _ _ _ Hfs) in HIP.
        pose proof (ro_bg _ _ _ _ _ _ (so_reg _ _ _ _ _ _ HSA kb rgb FB1) o
                      ltac:(intros _; unfold loZ; rewrite LO0, KZ0, EHb; unfold hiZ; rewrite HIP; fold Xz; lia)
                      ltac:(intros X1; rewrite Kb0' in X1; discriminate X1) ltac:(intros g gr _ F; rewrite CB in F; cbn in F; discriminate F)) as G.
        unfold bg_byte in G. rewrite BGB in G. change (to_Z 0%uint63) with 0 in G. rewrite Z.sub_0_r, EBF, EKb in G. fold Db in G.
        cbn [ms_mem CtrFrame.TwinB.ms'] in G. rewrite <- G. apply ReadPost.TwinB.rb_ext. symmetry. apply (OUTSIDE (Db + o) AR). unfold D. lia.
      +
        rewrite (GlueA.TwinB.rb_mrdA bsegs). replace (Db + o) with (D + Z.of_nat (Z.to_nat (o - Xz))) by (unfold D; lia). rewrite BY by lia.
        unfold stage_src. rewrite nth_error_map, nth_error_seq. destruct (Nat.ltb_spec (Z.to_nat (o - Xz)) (Z.to_nat nZ)); [|lia]. cbn [option_map].
        f_equal. f_equal. lia. }
  idtac "RP-B1b".

  assert (REGT : forall k2 r2, IMap.find k2 (s_regs st1) = Some r2 ->
            exists r2', IMap.find k2 (s_regs st) = Some r2' /\ loZ r2 = loZ r2' /\ hiZ E' r2 = hiZ E r2' /\ ev E' k2 = ev E k2).
  { intros k2 r2 H. rewrite (CtrFrame.TwinB.st1_regs st st1 FS ks offs rss ksp SPR Hksp) in H. destruct (Uint63.eqb ks k2) eqn:Q.
    - apply Uint63.eqb_correct in Q. subst k2. rewrite IMap.find_add_same in H by exact (so_bst _ _ _ _ _ _ HS). injection H as <-.
      destruct (CtrFrame.TwinB.reg_E' OPS E st ms mo HS FOK Fv Gv ks rss Hrs) as (EK & EH & _). exists rss. split; [exact Hrs|]. split; [reflexivity|]. split; [exact EH| exact EK].
    - apply Uint63.eqb_false_spec in Q. rewrite IMap.find_add_other in H by (exact (so_bst _ _ _ _ _ _ HS) || exact Q).
      destruct (CtrFrame.TwinB.reg_E' OPS E st ms mo HS FOK Fv Gv k2 r2 H) as (EK & EH & _). exists r2. split; [exact H|]. split; [reflexivity|]. split; [exact EH| exact EK]. }
  assert (ARGT : forall o, In o (s_ops st) -> map (den E') (op_args o) = map (den E) (op_args o)).
  { intros o Ho. apply (CtrFrame.TwinB.map_den_E' E st Fv Gv). exact (proj1 (forallb_forall _ _) OPB o Ho). }
  assert (HS1 : st_ok bsegs OPS E'
            (SS r (rf_set (s_rf (clobber st1)) X10 (getr st X10)) (s_ff st) (s_resv st) (IMap.add kb rb' (s_regs st1)) (s_facts st) (s_ops st) (s_priv st) (s_next (clobber st1)))
            (MS R' (ms_fregs ms) (Z_to_bv 64 (to_Z r)) (ms_fcsr ms) None m' (seg_rom bsegs)) mo').
  { apply (st_ok_based_replace_g bsegs OPS E' _ R' (ms_fregs ms) (Z_to_bv 64 (to_Z r)) (ms_fcsr ms) None mj m' (seg_rom bsegs) mo' kb rgb rb' HSA FB1 Kb0').
    -
      intros a Ha NC. unfold two64 in Ha. cbn [s_regs s_ops] in *.
      assert (INB : Db <= a < Db + wlenZ).
      { destruct NC as [RGa|CH]; [rewrite EHI, EL, EKb in RGa; fold Db in RGa; lia|].
        destruct (Z_lt_le_dec a D) as [L1|G1]; [exfalso; apply CH; symmetry; apply (OUTSIDE a ltac:(lia)); lia|].
        destruct (Z_lt_le_dec a (D + nZ)) as [L2|G2]; [unfold D in *; lia| exfalso; apply CH; symmetry; apply (OUTSIDE a ltac:(lia)); lia]. }
      pose proof (UBW a INB) as UB. split; [| split].
      + intros k2 r2 H2 NK2 K20 RG2. destruct (REGT k2 r2 H2) as (r2' & F2 & L2 & H2' & EK2). rewrite L2, H2', EK2 in RG2.
        exact (zone_regions E st ms mo HS r hargs wnl L RNG sta LBa aw CF kb wlen WL OT a INB UB k2 r2' F2 NK2 K20 RG2).
      + exact (UnreggPre.TwinB.no_seg_above a (proj2 (A64 a INB))).
      + intros o Ho FP. rewrite (ARGT o Ho) in FP.
        exact (zone_ops E st ms mo r hargs wnl L RNG sta LBa aw CF kb wlen WL a ltac:(unfold two64; lia) INB UB o Ho FP).
    -
      intros x H. unfold mj, mjoinR in H. destruct (in_rng D (D + nZ) (bv_unsigned x)) eqn:IS; [| exact H].
      unfold in_rng in IS. rewrite <- (Z_to_bv_bv_unsigned x). apply MAPPED. unfold D in IS. lia.
    - intros x b Hx seg Hs. pose proof (MINV' x b Hx) as RO. unfold AM.ro_addr in RO. rewrite Hs in RO. apply negb_false_iff in RO. exact RO.
    - exact RO'.
    -
      intros a RGa. rewrite EHI, EL, EKb in RGa. fold Db in RGa. right. apply Exists_exists. exists (HEAP_ID, map (den E') hargs). split.
      + unfold insts. apply in_map_iff. exists (OpI HEAP_ID hargs). split; [reflexivity|]. cbn [s_ops]. exact (UnreggPre.TwinB.find_op_In _ _ _ Hf).
      + cbn [fst snd]. apply OPS_cov1. split; [reflexivity|]. eexists _, _, _, _.
        split; [exact (CtrFrame.TwinB.DEC' E st FOK Fv Gv nn rest hargs md A nw Hf Eh Tnw Nn Ln)| left].
        unfold in_ws, heap_ws. apply in_ivs_In. eexists. split; [apply in_map; apply filter_In; split; [exact INWb| reflexivity]|].
        unfold in_iv, w_iv. cbn [w_lo w_len fst snd]. fold Db wlenZ. lia. }
  idtac "RP-B1".

  set (os' := set_op ReadC.TwinB.ReadC.RSTV_ID [sv_alu ALU_ADD off nsv; VL wzero] (s_ops st)).
  pose proof (HeapCtr.TwinB.known_eq_sound E _ _ _ Hfs EQoff) as Eoff.
  assert (Voff : sv_vars_below (s_next st) off = true).
  { pose proof (proj1 (forallb_forall _ _) OPB _ (UnreggPre.TwinB.find_op_In _ _ _ F3)) as V3. cbn [op_args forallb] in V3. apply andb_prop in V3 as [V3 _]. exact V3. }
  assert (RSVN : ReadPost.TwinB.rstage_holds_v file (map (den E') [sv_alu ALU_ADD off nsv; VL wzero]) m').
  { cbn [map ReadPost.TwinB.rstage_holds_v].
    assert (Vsum : sv_vars_below (s_next st) (sv_alu ALU_ADD off nsv) = true) by (apply MemFX.MemFX.sv_vars_below_alu; [left; reflexivity| exact Voff| exact Vn]).
    unfold E'. rewrite (CtrFrame.TwinB.den_E' E st Fv Gv _ Vsum). cbn [den]. rewrite wbv_unsigned, wzero_ok.
    rewrite den_sv_alu. cbn [alu64 alu]. rewrite bv_add_unsigned, Eoff. fold Xz nZ. rewrite bv_wrap_small by (change (bv_modulus 64) with (2 ^ 64); lia).
    split; [lia|]. split; [lia|]. intros i Hi. lia. }
  idtac "RP-B2a".
  pose proof (st_ok_memops bsegs OPS E' _ _ mo' mo' [] os' (s_next (clobber st1)) m' HS1 (Forall_nil _) HMI') as B2.
  idtac "RP-B2b".
  cbn [s_pc s_rf s_ff s_resv s_regs s_facts s_ops s_priv app] in B2.
  idtac "RP-B2c".
  assert (HS2 : st_ok bsegs OPS E'
            (SS r (rf_set (s_rf (clobber st1)) X10 (getr st X10)) (s_ff st) (s_resv st) (IMap.add kb rb' (s_regs st1)) (s_facts st) os' (s_priv st) (s_next (clobber st1)))
            (MS R' (ms_fregs ms) (Z_to_bv 64 (to_Z r)) (ms_fcsr ms) None m' (seg_rom bsegs)) mo').
  { apply B2.
    - apply (CtrFX.ops_hold_set_op1 OPS E' (s_ops st) ReadC.TwinB.ReadC.RSTV_ID [off; n'] _ m' mo' F3 (so_ops _ _ _ _ _ _ HS1)).
      apply OPS_holds_rstage'. exact RSVN.
    - apply (CtrFX.ops_apart_set_op1 bsegs OPS E' (s_ops st) ReadC.TwinB.ReadC.RSTV_ID [off; n'] _ _ _ F3 (so_apart _ _ _ _ _ _ HS1)). apply OPS_fp_rstage.
    - intros a Ha. apply (OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Glue.Nodes.FXN.cov_keep OPS E' (s_ops st)); [| exact (so_cover _ _ _ _ _ _ HS1 a Ha)].
      intros o Ho [z Hz]. pose proof (OPS_cov1_heap _ _ _ Hz) as HID0. apply ReadPost.TwinB.CS.set_op_keep; [exact Ho| rewrite HID0; reflexivity].
    - intros a _ _. reflexivity.
    - intros a b Hb Hnone. change (m' a = None) in Hnone. rewrite Hnone in Hb. discriminate Hb. }
  idtac "RP-B2d".

  apply (HK _ (or_introl eq_refl) E' ms' mo' (CtrFrame.TwinB.EXT E st Fv Gv) HMP').
  rewrite EMS'. unfold CtrFrame.TwinB.ms'.
  rewrite (rs_post_shape st st1 r kb X off). cbv zeta. rewrite FF, RV, RG, FS0, OP, PV, FF1, RV1, FS1, OP1, PV1.
  exact HS2.
Qed.
End Leaf.
End TwinB.
