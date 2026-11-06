(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import PrimInt63 Uint63.
From Stdlib Require Import Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib Require Import PropExec MState Cells Frame ITree Nodes.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib Require ALib.Mem ALib.Step.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA Require Import AcctCore ExecF ITreeA NodesA.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA Require Shadow.
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
Import W64 Val OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Mem.Mem FI St Step Plan PlanS CtrLib HeapOp.
Open Scope Z_scope.
Unset Lia Cache.

From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Bridge Require Import Actr.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX Require Import W64Proofs ValProofs MemProofs StepSoundBase.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Br Require Import CtrFX.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Br Require HeapCtr HeapCtrB.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Bridge Require CallA CallV GlueA CtrPre CtrFrame CtrNoDelta.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.GlueA Require Import UnreggC UnreggPre.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.GlueA Require UnreggAsan.
Import ValP MemP CtrFX ActrA UnreggC.
Module AP := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.PropExec.
Module AM := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Mem.
Module AS := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Step.
Module UA := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.GlueA.UnreggAsan.

Definition MTX : Z := 0xd7370.

Section MemSide.
Context {rc : runConstT}.
Variables (m m' : amem) (sp lo : Z).
Notation W := [(sp - 1024, sp); (MTX, MTX + 8); (SH_LO, SH_HI); (ASH_LO, ASH_HI)]%Z.
Hypothesis MU : munch W m m'.
Hypothesis WM : wmono asegs m m'.
Hypothesis LO : ATOP + 4096 <= lo /\ lo <= sp - 1024 /\ sp < 2 ^ 47.
Hypothesis MTX0 : AS.rw_cells asegs m MTX [C8 (Z_to_bv 64 0)].
Hypothesis MTX1 : AS.rw_cells asegs m' MTX [C8 (Z_to_bv 64 0)].

Lemma raw_out : forall a, 0 <= a < 2 ^ 64 ->
  ~ (sp - 1024 <= a < sp) -> ~ (MTX <= a < MTX + 8) -> ~ (SH_LO <= a < SH_HI) -> ~ (ASH_LO <= a < ASH_HI) ->
  m' (AM.wa a) = m (AM.wa a).
Proof.
  intros a Ha N1 N2 N3 N4. apply MU. unfold AM.wa. rewrite Z_to_bv_unsigned, bv_wrap_small by (unfold bv_modulus; lia).
  cbn [outside]. tauto.
Qed.

Lemma wbm_all : forall a, wb asegs m a = true -> wb asegs m' a = true.
Proof. intros a H. apply (GlueA.wb_wviewA asegs). apply (GlueA.wb_wviewA asegs) in H. exact (WM _ H). Qed.

Lemma mtx_view : forall a, MTX <= a < MTX + 8 -> rb asegs m' a = rb asegs m a.
Proof.
  intros a Ha. destruct MTX0 as [[_ (_ & _ & B0)] _]. destruct MTX1 as [[_ (_ & _ & B1)] _].
  rewrite !(GlueA.rb_mrdA asegs). replace a with (MTX + Z.of_nat (Z.to_nat (a - MTX))) by lia.
  rewrite (B0 (Z.to_nat (a - MTX))), (B1 (Z.to_nat (a - MTX))); [reflexivity | |]; cbn; lia.
Qed.
End MemSide.

From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.GlueA Require Export UnreggGeo.

From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Bridge Require CtrFree.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.GlueA Require UnreggSound.
Unset Nia Cache. Unset Nra Cache.

Lemma zero_chunk_rb {rc : runConstT} : forall (m' : amem) A n, AS.rw_cells asegs m' A [CB n (repeat (Z_to_bv 8 0) n)] ->
  forall i, 0 <= i < Z.of_nat n -> rb asegs m' (A + i) = Some (Z_to_bv 8 0).
Proof.
  intros m' A n [[_ BY] _] i Hi. cbn [cells_bytes cbytes] in BY. rewrite app_nil_r in BY. destruct BY as (_ & _ & BY).
  specialize (BY (Z.to_nat i) ltac:(rewrite repeat_length; lia)). rewrite Z2Nat.id in BY by lia. rewrite nth_error_repeat in BY by lia. exact BY.
Qed.

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
Variable MP : Model -> Prop.
Variable PB : (int -> list byte) -> Prop.

Hypothesis ACI_mtx : In (0xd7370, 0xd7378) (aci AI).
Hypothesis ACI_glob : In (0x22c60, 0x23360) (aci AI).
Hypothesis ACI_desc : In (0xd5e90, 0xd6408) (aci AI).
Hypothesis OPS_fp_mtx : forall id args a, id <> HEAP_ID -> Exists (fun iv => fst iv <= a < snd iv) (op_fp OPS id args) ->
  ~ (0xd7370 <= a < 0xd7378).

Hypothesis OPS_fp_shw : forall id args a, id <> HEAP_ID -> id <> GSH_ID -> Exists (fun iv => fst iv <= a < snd iv) (op_fp OPS id args) ->
  ~ (SH_LO <= a < SH_HI) /\ ~ (ASH_LO <= a < ASH_HI).

Lemma aci_low' : forall a, in_ranges (aci AI) a -> a < AIMG_HI.
Proof. intros a (iv0 & Hi & RR). pose proof (AI_aci_img AI iv0 Hi). lia. Qed.

Lemma unregg_leaf_ok : UnreggSound.unregg_leaf AI ACCT UNIV Cw OPS OTHER MP PB.
Proof.
  unfold UnreggSound.unregg_leaf.
  intros st sts K E ms mo r hargs wnl st1 L RNG sta LBa aw HS HPB HK PRE PREB HVO ESTS CP FS CF AH UPRE BOT LO SPT ms' mo' HQ HMP' HMI' OTH ACP.
  set (R := ms_regs ms) in *.

  unfold hull_views_ok in HVO. apply andb_prop in HVO as [HVO NOG].
  assert (NOGSH : forall o, In o (s_ops st) -> op_id o <> GSH_ID).
  { destruct (find_op GSH_ID (s_ops st)) eqn:FG; [discriminate NOG|]. clear - FG. induction (s_ops st) as [|o0 os IH]; intros o Ho; [destruct Ho|].
    cbn [find_op] in FG. destruct (PrimInt63.eqb (op_id o0) GSH_ID) eqn:Q; [discriminate FG|].
    destruct Ho as [<-|Ho]; [apply Uint63.eqb_false_spec; exact Q| exact (IH FG o Ho)]. }
  destruct HQ as (t0 & t1 & t2 & a0 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & m' & EMS & MU & WM & MINV' & STK' & MTXZ & ZS).

  assert (ZCH : forall c, In c (u_zch CFG_ASAN) -> forall i, 0 <= i < snd c -> rb asegs m' (fst c + i) = Some (Z_to_bv 8 0)).
  { decompose [and] ZS. clear ZS. intros c Hc. cbn [u_zch CFG_ASAN In] in Hc.
    repeat (destruct Hc as [<-|Hc]; [cbn [fst snd]; intros i Hi;
      match goal with HH : AS.rw_cells asegs m' ?AA [CB ?nn _] |- rb asegs m' (?AA + _) = _ => apply (zero_chunk_rb m' AA nn HH); lia end|]).
    destruct Hc. }
  clear ZS.
  pose proof atop_range as ATR.

  assert (MTX0 : AS.rw_cells asegs (ms_mem ms) MTX [C8 (Z_to_bv 64 0)]).
  { unfold UA.unregg_pre in UPRE. exact (proj1 (proj2 UPRE)). }

  set (R' := mkR (AP.getr R 1) (AP.getr R 2) (AP.getr R 3) (AP.getr R 4) t0 t1 t2 (AP.getr R 8) (AP.getr R 9) a0 a1 a2 a3 a4 a5 a6 a7
               (AP.getr R 18) (AP.getr R 19) (AP.getr R 20) (AP.getr R 21) (AP.getr R 22) (AP.getr R 23) (AP.getr R 24) (AP.getr R 25)
               (AP.getr R 26) (AP.getr R 27) t3 t4 t5 t6) in *.
  set (Fv := CtrFree.cfvF R'). set (Gv := fun (_ _ : Z) => Z_to_bv 8 0).
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
  set (sp := bv_unsigned (AP.getr R 2)) in *.
  assert (LO3 : ATOP + 4096 <= CtrPre.sp_lo E st /\ CtrPre.sp_lo E st <= sp - 1024 /\ sp < 2 ^ 47) by lia.

  pose proof CF as CF0.
  destruct CF0 as (LB & ks & offs & rss & ksp & nn & md & A & nw & rest & SPR & Hksp & SPE & K16 & LOSP & FLOOR & Hf & Hc & Eh & Tnw & Nn & Ln & N255
                  & NW & AN & AJ & TS & WF & HC & AWden & (Wt & WOF & ARW & TI)).
  destruct (clobber_fields st1) as (_ & FF & RV & RG & FS0 & OP & PV & NXc).
  assert (F1 : s_ff st1 = s_ff st /\ s_resv st1 = s_resv st /\ s_facts st1 = s_facts st
               /\ s_ops st1 = s_ops st /\ s_priv st1 = s_priv st /\ s_next st1 = s_next st).
  { unfold forget_stack_below_sp_g in FS. rewrite SPR, Hksp in FS. injection FS as <-. repeat split; reflexivity. }
  destruct F1 as (FF1 & RV1 & FS1 & OP1 & PV1 & NX1).
  assert (XE : s_next (clobber st1) = addn (s_next st) 15).
  { rewrite NXc, NX1. symmetry. destruct (HeapCtr.fresh_ok_inv st FOK) as (_ & _ & B). pose proof (int_range (s_next st)) as RR. rewrite two63_eq in RR.
    apply addn_lit; [reflexivity| rewrite wB_two63, two63_eq; lia]. }
  assert (SHAPE : sts = [SS r (rf_set (s_rf (clobber st1)) X10 (VP (addn (s_next st) 15) wzero)) (s_ff st) (s_resv st) (s_regs st1) (s_facts st)
                            (s_ops st) (s_priv st) (PrimInt63.add (addn (s_next st) 15) 1%uint63)]).
  { rewrite ESTS. unfold fresh. cbn [fst snd]. rewrite XE. f_equal.
    assert (G : forall (S : sstate) nx1 v, setpc (setr (set_next S nx1) X10 v) r
                = SS r (rf_set (s_rf S) X10 v) (s_ff S) (s_resv S) (s_regs S) (s_facts S) (s_ops S) (s_priv S) nx1) by (intros [] ? ?; reflexivity).
    rewrite G, FF, RV, RG, FS0, OP, PV, FF1, RV1, FS1, OP1, PV1. reflexivity. }
  apply (HK _ ltac:(rewrite SHAPE; left; reflexivity) (CtrFrame.E' E st Fv Gv) ms' mo' (CtrFrame.EXT E st Fv Gv) HMP').
  rewrite EMS'.
  assert (MUw : munch [(sp - 1024, sp); (MTX, MTX + 8); (SH_LO, SH_HI); (ASH_LO, ASH_HI)]%Z (ms_mem ms) m')
    by (eapply munch_weaken; [| exact MU]; unfold sub_fp; cbn [outside]; intros q Hq; unfold MTX, SH_LO, SH_HI, ASH_LO, ASH_HI in *; lia).
  assert (RAW := raw_out (ms_mem ms) m' sp (CtrPre.sp_lo E st) MUw LO3).
  assert (IUOUT : forall LB0, aw_real AI ACCT UNIV aw LB0 (ms_mem ms) mo L RNG sta LBa -> forall a, 0 <= a < 2 ^ 64 -> in_user LB0 a ->
            m' (AM.wa a) = ms_mem ms (AM.wa a)).
  { intros LB0 AR0 a Ha IU. pose proof (user_out AI ACCT UNIV AI_fake aw LB0 (ms_mem ms) mo L RNG sta LBa a AR0 IU) as G.
    apply RAW; [exact Ha| | | |]; unfold MTX, SH_LO, SH_HI, ASH_LO, ASH_HI, AIMG_HI, KLS in *; lia. }
  apply (CtrNoDelta.nodelta_st_ok AI IMGX IMGX_aci ACCT UNIV Cw OPS AI_fake OPS_holds1 OPS_fp1 OPS_cov1 OPS_frame_other OPS_fp_other OTHER OPS_mo_other
           OPS_cov0_img E st ms mo r hargs wnl L RNG sta LBa aw st1 Fv Gv R' m' mo' RNG sta _ _ HS CP FS CF).
  -
    intros rg Hrg. unfold CtrFrame.kept_regsA in Hrg. cbn [In] in Hrg. repeat (destruct Hrg as [<-|Hrg]; [reflexivity|]). destruct Hrg.
  - intros x i Hx. exact (CtrFree.cfvF_clob R' x i Hx).
  - rewrite HeapCtr.den_VPz. rewrite (CtrFrame.ev_E'_fresh E st FOK Fv Gv 15 ltac:(lia)). reflexivity.
  - exact MINV'.
  - exact STK'.
  -
    intros LB0 AR0 a Ha STB. destruct STB as [S1|[S2|S3]].
    + apply (FrameV.frame_v_of_raw asegs). apply RAW; [exact Ha| | | |]; unfold MTX, SH_LO, SH_HI, ASH_LO, ASH_HI, sp, R in *; lia.
    + destruct (Z_lt_le_dec a MTX) as [Q|Q]; [| destruct (Z_lt_le_dec a (MTX + 8)) as [Q'|Q']].
      * apply (FrameV.frame_v_of_raw asegs). pose proof (aci_low' a S2) as AL.
        apply RAW; [exact Ha| | | |]; unfold MTX, SH_LO, SH_HI, ASH_LO, ASH_HI, AIMG_HI in *; lia.
      * split; [exact (mtx_view (ms_mem ms) m' MTX0 MTXZ a ltac:(lia)) | exact (wbm_all (ms_mem ms) m' WM a)].
      * apply (FrameV.frame_v_of_raw asegs). pose proof (aci_low' a S2) as AL.
        apply RAW; [exact Ha| | | |]; unfold MTX, SH_LO, SH_HI, ASH_LO, ASH_HI, AIMG_HI in *; lia.
    + apply (FrameV.frame_v_of_raw asegs). exact (IUOUT LB0 AR0 a Ha S3).
  -   exact IUOUT.
  -
    intros o a Ho NI Ha FP. unfold not_id in NI. apply Uint63.eqb_false_spec in NI.
    pose proof (OPS_fp_mtx _ _ a NI FP) as NM. destruct (OPS_fp_shw _ _ a NI (NOGSH o Ho) FP) as [NS1 NS2].
    destruct (OPS_fp_other _ _ a NI FP) as [INA|[(a' & INA & ->)|(a' & STK & ->)]].
    + pose proof (aci_low' a INA) as AL.
      apply (RAW a); [unfold two64 in Ha; lia| | | |]; unfold MTX, SH_LO, SH_HI, ASH_LO, ASH_HI, AIMG_HI in *; lia.
    + pose proof (aci_low' a' INA) as AL. destruct INA as (iv0 & I0 & I1). pose proof (AI_aci_lo AI iv0 I0) as A0.
      pose proof (CtrPre.shad_img_band a' ltac:(lia)) as BND.
      apply (RAW (shad a')); [unfold two64 in Ha; lia| | exact NM | exact NS1 | exact NS2]. lia.
    +
      assert (ZN : 0x10006fef8000 <= shad a' < 0x10007fff8000) by (unfold shad, ASHOFF; rewrite Z.shiftr_div_pow2 by lia; change (2 ^ 3) with 8; clear - STK ATR; Z.div_mod_to_equations; lia).
      apply (RAW (shad a')); [unfold two64 in Ha; lia| | exact NM | exact NS1 | exact NS2]. lia.
  -   intros a Ha _. exact (wbm_all (ms_mem ms) m' WM a).
  -
    intros a Ha SC IB.
    assert (ZN : (0x7fffa000 <= a < 0x7fffc66c) \/ (0x800b7820 <= a < 0x800bdca8) \/ (0x10006fef8000 <= a < 0x10007fff8000)).
    { destruct SC as [(a' & RR & ->)|(vv & Hv & RR)].
      - right; right. unfold shad, ASHOFF. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8. clear - RR ATR. Z.div_mod_to_equations. lia.
      -
        destruct (Op.SHLIT_cases vv Hv) as [->|(_ & P1 & P2 & P3)]; [left; cbn [fst snd] in RR; lia| right; left; lia]. }
    destruct (Z_lt_le_dec a SH_LO) as [QL|QL].
    { apply (FrameV.frame_v_of_raw asegs). apply RAW; [exact Ha| | | |]; unfold MTX, SH_LO, SH_HI, ASH_LO, ASH_HI, sp, R in *; lia. }
    destruct (Z_lt_le_dec a SH_HI) as [QH|QH].
    2:{ apply (FrameV.frame_v_of_raw asegs). apply RAW; [exact Ha| | | |]; unfold MTX, SH_LO, SH_HI, ASH_LO, ASH_HI, sp, R in *; lia. }
    split; [| exact (wbm_all (ms_mem ms) m' WM a)].
    unfold SH_LO, SH_HI in QL, QH.
    destruct IB as (k & rr & Hk & KZ & RNGa).
    assert (KN0 : k <> 0%uint63) by (intros ->; discriminate KZ).
    assert (ARc : aw_real AI ACCT UNIV aw LB (ms_mem ms) mo L RNG sta LBa) by (exists Wt; split; [exact WOF| exact ARW]).
    assert (INWIN : forall k0 len kd, CtrA.win_lookup wnl k0 = Some (len, kd) ->
              bv_unsigned (ev E k0) <= a < bv_unsigned (ev E k0) + bv_unsigned (den E len) -> False).
    { intros k0 len kd WL Hin.
      destruct (HeapCtrB.nonstack_windows_In E nn rest wnl k0 len kd NW (HeapCtrB.win_lookup_In _ _ _ _ WL)) as (_ & _ & KD & INW).
      assert (IU : in_user LB a).
      { pose proof (proj1 (Forall_forall _ _) WF _ INW) as (W1' & W2' & W3' & [[KS0 _]|[[KB B]|[KS2 (b & Hb & SUB)]]]); unfold w_iv in *; cbn [w_kind w_lo w_len] in *.
        - exfalso. exact (KD KS0).
        - apply in_ivs_In. eexists. split; [exact B|]. unfold in_iv. cbn [fst snd]. lia.
        - apply in_ivs_In. exists b. split; [exact Hb|]. apply SUB. unfold in_iv. cbn [fst snd]. lia. }
      pose proof (user_out AI ACCT UNIV AI_fake aw LB (ms_mem ms) mo L RNG sta LBa a ARc IU) as G. unfold AIMG_HI, KLS in G. lia. }
    pose proof (CallA.aregion_just_sound asegs OPS E st ms mo wnl ks offs rss k rr HS SPR AJ Hk KN0) as JU.
    destruct (CallA.sp_region_inv st ks offs rss SPR) as (_ & Hrs & _).
    destruct JU as [[EQ TOPk]|[NE [(len0 & kd0 & WLS & LZ & HZ)|[[J1 J2]|VJ]]]].
    + exfalso. subst k. rewrite Hrs in Hk. injection Hk as <-. lia.
    + exfalso. apply (INWIN k len0 kd0 WLS). rewrite LZ in RNGa. lia.
    + exfalso. rewrite (CtrFrame.SP_den OPS E st ms mo HS) in J1. fold R in J1. fold sp in J1. lia.
    +
      destruct VJ as [VJ|SL]; [| exfalso; pose proof (CtrPre.sliver_low OPS E st ms mo ks offs rss k rr hargs nn md A nw rest LB a HS SPR Hk KN0 NE SL Hf Eh Tnw Nn Ln WF RNGa) as SLO; lia].
      pose proof (CallV.view_just_sound asegs OPS E st ms mo wnl ks offs rss k rr HS SPR Hk KN0 VJ) as VS. unfold CallV.view_sem in VS. cbv zeta in VS.
      destruct VS as [((hs & ZV) & blo & bhi & SHZ & BHI & BLO)|[(hs & n0 & sh & len1 & ZV & _ & _ & WL1 & LO1 & HI1)|[(VI & v & Hv & V1 & V2)|(shD & kbD & nD & lenD & WLD & BTD & WLkD & STD & TND & ROD & LOD & HID)]]].
      * exfalso. destruct (SHZ a RNGa) as (a' & Ha' & EA).
        assert (BL : ATOP + 4096 <= blo).
        { destruct BLO as [(wlo & SW & ->)|[(rs0 & Frs & ->)|GE]].
          - exact (CallV.wlo_floor E st hargs nn md A nw rest LB (ATOP + 4096) wlo Hf Eh Tnw Nn Ln WF SW).
          - rewrite Hrs in Frs. injection Frs as <-. exact FLOOR.
          - rewrite (CtrFrame.SP_den OPS E st ms mo HS) in GE. fold R in GE. fold sp in GE. lia. }
        unfold CallV.shz in EA. clear - EA Ha' BL ATR QH. Z.div_mod_to_equations. lia.
      * exfalso. apply (INWIN sh len1 ActrA.K_TWIN WL1). lia.
      * pose proof (proj1 (IMap.forallb_spec _ _ (so_bst _ _ _ _ _ _ HS)) HVO k rr Hk) as CK. unfold hull_view_ok in CK. rewrite VI in CK. cbn [negb orb] in CK.
        destruct (ActrA.zero_view rr) as [hs|] eqn:ZV; [|discriminate CK]. destruct (ActrA.find_pin (s_facts st) k) as [pa|] eqn:FP; [|discriminate CK].
        pose proof (CallV.find_pin_sound E _ k pa (so_facts _ _ _ _ _ _ HS) FP) as EVK. pose proof (CallV.zero_view_hi E rr hs ZV) as HIK.
        rewrite EVK, HIK in RNGa. unfold loZ in RNGa. cbn [u_hull CFG_ASAN fst snd] in CK.
        apply orb_prop in CK as [CK|CK]; [apply orb_prop in CK as [CK|CK]|].
        -- exfalso. apply Z.leb_le in CK. lia.
        -- exfalso. apply Z.leb_le in CK. lia.
        -- apply existsb_exists in CK as (c & HcZ & CC). apply andb_prop in CC as [C1 C2]. apply Z.leb_le in C1, C2.
           replace a with (fst c + (a - fst c)) at 1 by lia. rewrite (ZCH c HcZ (a - fst c) ltac:(lia)).

           pose proof (so_reg _ _ _ _ _ _ HS k rr Hk) as RO.
           assert (ZVI : rg_bg rr = BGZero /\ rg_cells rr = IMap.Leaf).
           { unfold ActrA.zero_view in ZV. destruct (rg_hi rr); try discriminate ZV. destruct (rg_bg rr); try discriminate ZV.
             destruct (rg_cells rr); try discriminate ZV. auto. }
           destruct ZVI as [BGZ RCL].
           pose proof (ro_bg _ _ _ _ _ _ RO (a - bv_unsigned (ev E k)) ltac:(intros _; unfold loZ; rewrite HIK, EVK; lia) ltac:(intros KK; rewrite KK in KZ; discriminate KZ)) as BG.
           assert (UNC : uncovered rr (a - bv_unsigned (ev E k))) by (intros g gr _ FF0; rewrite RCL in FF0; discriminate FF0).
           specialize (BG UNC). unfold bg_byte in BG. rewrite BGZ in BG. replace (bv_unsigned (ev E k) + (a - bv_unsigned (ev E k))) with a in BG by lia.
           symmetry. exact BG.
      *   exfalso. apply (INWIN shD lenD ActrA.K_TWIN WLD). lia.
  -
    apply (AI_frame AI L RNG sta LBa (ms_mem ms) m' _ AH MU WM).
    repeat (apply Forall_cons; [cbn [fst snd]|]); [| | | | apply Forall_nil].
    + left. left. fold sp. lia.
    + left. right. left. exists (0xd7370, 0xd7378). split; [exact ACI_mtx| cbn [fst snd]; lia].
    + right. right. right. left. exists (0x22c60, 0x23360). split; [exact ACI_glob| cbn [fst snd]; unfold ASHOFF; lia].
    + right. right. right. left. exists (0xd5e90, 0xd6408). split; [exact ACI_desc| cbn [fst snd]; unfold ASHOFF; lia].
  - exact ACP.
  -
    intros b x Hb FK Hx. pose proof (Op.blk_band AI AI_fake L RNG sta LBa (ms_mem ms) b x AH Hb) as BB.
    destruct (AI_fake L RNG sta LBa (ms_mem ms) b AH Hb FK) as (_ & _ & _ & _ & SZ64 & _).
    specialize (BB ltac:(lia)). unfold MTX, SH_LO, SH_HI, ASH_LO, ASH_HI, AIMG_HI, KLS in *.
    apply RAW; lia.
  -
    apply (Op.twins_pres_band AI L RNG sta LBa (ms_mem ms) m' AH). intros a Ha.
    assert (SA : shad ATOP = ASHOFF + ATOP / 8) by (unfold shad; rewrite Z.shiftr_div_pow2 by lia; reflexivity).
    rewrite SA in Ha. unfold ASHOFF in Ha.
    apply RAW; unfold MTX, SH_LO, SH_HI, ASH_LO, ASH_HI in *; [| | | |]; try (clear - Ha ATR LO3; Z.div_mod_to_equations; lia).
  - exact OTH.
  - exact HMI'.
  - exact (fun P => P).
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
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Ctr.Lib OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Ctr.DefsA.
Import Ledger.TwinB Op.TwinB Adeq.TwinB.

Import ListNotations.
Import W64 Val OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Mem.Mem FI St Step Plan PlanS CtrLib HeapOp.
Open Scope Z_scope.
Unset Lia Cache.

Import Actr.TwinB.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.W64Proofs OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.ValProofs OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.MemProofs OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.StepSoundBase.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Br.CtrFX.

Import UnreggC.TwinB UnreggPre.TwinB.

Import ValP MemP CtrFX ActrA UnreggC.TwinB.UnreggC.
Module AP := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.PropExec.
Module AM := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Mem.
Module AS := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Step.
Module UA := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.GlueA.UnreggAsan.TwinB.

Definition MTX : Z := 0xd9530.

Section MemSide.
Context {rc : runConstT}.
Variables (m m' : amem) (sp lo : Z).
Notation W := [(sp - 1024, sp); (MTX, MTX + 8); (SH_LO, SH_HI); (ASH_LO, ASH_HI)]%Z.
Hypothesis MU : munch W m m'.
Hypothesis WM : wmono bsegs m m'.
Hypothesis LO : ATOP + 4096 <= lo /\ lo <= sp - 1024 /\ sp < 2 ^ 47.
Hypothesis MTX0 : AS.rw_cells bsegs m MTX [C8 (Z_to_bv 64 0)].
Hypothesis MTX1 : AS.rw_cells bsegs m' MTX [C8 (Z_to_bv 64 0)].

Lemma raw_out : forall a, 0 <= a < 2 ^ 64 ->
  ~ (sp - 1024 <= a < sp) -> ~ (MTX <= a < MTX + 8) -> ~ (SH_LO <= a < SH_HI) -> ~ (ASH_LO <= a < ASH_HI) ->
  m' (AM.wa a) = m (AM.wa a).
Proof.
  intros a Ha N1 N2 N3 N4. apply MU. unfold AM.wa. rewrite Z_to_bv_unsigned, bv_wrap_small by (unfold bv_modulus; lia).
  cbn [outside]. tauto.
Qed.

Lemma wbm_all : forall a, wb bsegs m a = true -> wb bsegs m' a = true.
Proof. intros a H. apply (GlueA.TwinB.wb_wviewA bsegs). apply (GlueA.TwinB.wb_wviewA bsegs) in H. exact (WM _ H). Qed.

Lemma mtx_view : forall a, MTX <= a < MTX + 8 -> rb bsegs m' a = rb bsegs m a.
Proof.
  intros a Ha. destruct MTX0 as [[_ (_ & _ & B0)] _]. destruct MTX1 as [[_ (_ & _ & B1)] _].
  rewrite !(GlueA.TwinB.rb_mrdA bsegs). replace a with (MTX + Z.of_nat (Z.to_nat (a - MTX))) by lia.
  rewrite (B0 (Z.to_nat (a - MTX))), (B1 (Z.to_nat (a - MTX))); [reflexivity | |]; cbn; lia.
Qed.
End MemSide.

Export UnreggGeo.TwinB.

Unset Nia Cache. Unset Nra Cache.

Lemma zero_chunk_rb {rc : runConstT} : forall (m' : amem) A n, AS.rw_cells bsegs m' A [CB n (repeat (Z_to_bv 8 0) n)] ->
  forall i, 0 <= i < Z.of_nat n -> rb bsegs m' (A + i) = Some (Z_to_bv 8 0).
Proof.
  intros m' A n [[_ BY] _] i Hi. cbn [cells_bytes cbytes] in BY. rewrite app_nil_r in BY. destruct BY as (_ & _ & BY).
  specialize (BY (Z.to_nat i) ltac:(rewrite repeat_length; lia)). rewrite Z2Nat.id in BY by lia. rewrite nth_error_repeat in BY by lia. exact BY.
Qed.

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
Variable MP : Model -> Prop.
Variable PB : (int -> list byte) -> Prop.

Hypothesis ACI_mtx : In (0xd9530, 0xd9538) (aci AI).
Hypothesis ACI_glob : In (0x22d00, 0x23500) (aci AI).
Hypothesis ACI_desc : In (0xd7fb0, 0xd85c8) (aci AI).
Hypothesis OPS_fp_mtx : forall id args a, id <> HEAP_ID -> Exists (fun iv => fst iv <= a < snd iv) (op_fp OPS id args) ->
  ~ (0xd9530 <= a < 0xd9538).

Hypothesis OPS_fp_shw : forall id args a, id <> HEAP_ID -> id <> GSH_ID -> Exists (fun iv => fst iv <= a < snd iv) (op_fp OPS id args) ->
  ~ (SH_LO <= a < SH_HI) /\ ~ (ASH_LO <= a < ASH_HI).

Lemma aci_low' : forall a, in_ranges (aci AI) a -> a < AIMG_HI.
Proof. intros a (iv0 & Hi & RR). pose proof (AI_aci_img AI iv0 Hi). lia. Qed.

Lemma unregg_leaf_ok : UnreggSound.TwinB.unregg_leaf AI ACCT UNIV Cw OPS OTHER MP PB.
Proof.
  unfold UnreggSound.TwinB.unregg_leaf.
  intros st sts K E ms mo r hargs wnl st1 L RNG sta LBa aw HS HPB HK PRE PREB HVO ESTS CP FS CF AH UPRE BOT LO SPT ms' mo' HQ HMP' HMI' OTH ACP.
  set (R := ms_regs ms) in *.

  unfold hull_views_ok in HVO. apply andb_prop in HVO as [HVO NOG].
  assert (NOGSH : forall o, In o (s_ops st) -> op_id o <> GSH_ID).
  { destruct (find_op GSH_ID (s_ops st)) eqn:FG; [discriminate NOG|]. clear - FG. induction (s_ops st) as [|o0 os IH]; intros o Ho; [destruct Ho|].
    cbn [find_op] in FG. destruct (PrimInt63.eqb (op_id o0) GSH_ID) eqn:Q; [discriminate FG|].
    destruct Ho as [<-|Ho]; [apply Uint63.eqb_false_spec; exact Q| exact (IH FG o Ho)]. }
  destruct HQ as (t0 & t1 & t2 & a0 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & m' & EMS & MU & WM & MINV' & STK' & MTXZ & ZS).

  assert (ZCH : forall c, In c (u_zch CFG_ASAN) -> forall i, 0 <= i < snd c -> rb bsegs m' (fst c + i) = Some (Z_to_bv 8 0)).
  { decompose [and] ZS. clear ZS. intros c Hc. cbn [u_zch CFG_ASAN In] in Hc.
    repeat (destruct Hc as [<-|Hc]; [cbn [fst snd]; intros i Hi;
      match goal with HH : AS.rw_cells bsegs m' ?AA [CB ?nn _] |- rb bsegs m' (?AA + _) = _ => apply (zero_chunk_rb m' AA nn HH); lia end|]).
    destruct Hc. }
  clear ZS.
  pose proof atop_range as ATR.

  assert (MTX0 : AS.rw_cells bsegs (ms_mem ms) MTX [C8 (Z_to_bv 64 0)]).
  { unfold UA.unregg_pre in UPRE. exact (proj1 (proj2 UPRE)). }

  set (R' := mkR (AP.getr R 1) (AP.getr R 2) (AP.getr R 3) (AP.getr R 4) t0 t1 t2 (AP.getr R 8) (AP.getr R 9) a0 a1 a2 a3 a4 a5 a6 a7
               (AP.getr R 18) (AP.getr R 19) (AP.getr R 20) (AP.getr R 21) (AP.getr R 22) (AP.getr R 23) (AP.getr R 24) (AP.getr R 25)
               (AP.getr R 26) (AP.getr R 27) t3 t4 t5 t6) in *.
  set (Fv := CtrFree.TwinB.cfvF R'). set (Gv := fun (_ _ : Z) => Z_to_bv 8 0).
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
  set (sp := bv_unsigned (AP.getr R 2)) in *.
  assert (LO3 : ATOP + 4096 <= CtrPre.TwinB.sp_lo E st /\ CtrPre.TwinB.sp_lo E st <= sp - 1024 /\ sp < 2 ^ 47) by lia.

  pose proof CF as CF0.
  destruct CF0 as (LB & ks & offs & rss & ksp & nn & md & A & nw & rest & SPR & Hksp & SPE & K16 & LOSP & FLOOR & Hf & Hc & Eh & Tnw & Nn & Ln & N255
                  & NW & AN & AJ & TS & WF & HC & AWden & (Wt & WOF & ARW & TI)).
  destruct (clobber_fields st1) as (_ & FF & RV & RG & FS0 & OP & PV & NXc).
  assert (F1 : s_ff st1 = s_ff st /\ s_resv st1 = s_resv st /\ s_facts st1 = s_facts st
               /\ s_ops st1 = s_ops st /\ s_priv st1 = s_priv st /\ s_next st1 = s_next st).
  { unfold forget_stack_below_sp_g in FS. rewrite SPR, Hksp in FS. injection FS as <-. repeat split; reflexivity. }
  destruct F1 as (FF1 & RV1 & FS1 & OP1 & PV1 & NX1).
  assert (XE : s_next (clobber st1) = addn (s_next st) 15).
  { rewrite NXc, NX1. symmetry. destruct (HeapCtr.TwinB.fresh_ok_inv st FOK) as (_ & _ & B). pose proof (int_range (s_next st)) as RR. rewrite two63_eq in RR.
    apply addn_lit; [reflexivity| rewrite wB_two63, two63_eq; lia]. }
  assert (SHAPE : sts = [SS r (rf_set (s_rf (clobber st1)) X10 (VP (addn (s_next st) 15) wzero)) (s_ff st) (s_resv st) (s_regs st1) (s_facts st)
                            (s_ops st) (s_priv st) (PrimInt63.add (addn (s_next st) 15) 1%uint63)]).
  { rewrite ESTS. unfold fresh. cbn [fst snd]. rewrite XE. f_equal.
    assert (G : forall (S : sstate) nx1 v, setpc (setr (set_next S nx1) X10 v) r
                = SS r (rf_set (s_rf S) X10 v) (s_ff S) (s_resv S) (s_regs S) (s_facts S) (s_ops S) (s_priv S) nx1) by (intros [] ? ?; reflexivity).
    rewrite G, FF, RV, RG, FS0, OP, PV, FF1, RV1, FS1, OP1, PV1. reflexivity. }
  apply (HK _ ltac:(rewrite SHAPE; left; reflexivity) (CtrFrame.TwinB.E' E st Fv Gv) ms' mo' (CtrFrame.TwinB.EXT E st Fv Gv) HMP').
  rewrite EMS'.
  assert (MUw : munch [(sp - 1024, sp); (MTX, MTX + 8); (SH_LO, SH_HI); (ASH_LO, ASH_HI)]%Z (ms_mem ms) m') by exact MU.
  assert (RAW := raw_out (ms_mem ms) m' sp (CtrPre.TwinB.sp_lo E st) MUw LO3).
  assert (IUOUT : forall LB0, aw_real AI ACCT UNIV aw LB0 (ms_mem ms) mo L RNG sta LBa -> forall a, 0 <= a < 2 ^ 64 -> in_user LB0 a ->
            m' (AM.wa a) = ms_mem ms (AM.wa a)).
  { intros LB0 AR0 a Ha IU. pose proof (user_out AI ACCT UNIV AI_fake aw LB0 (ms_mem ms) mo L RNG sta LBa a AR0 IU) as G.
    apply RAW; [exact Ha| | | |]; unfold MTX, SH_LO, SH_HI, ASH_LO, ASH_HI, AIMG_HI, KLS in *; lia. }
  apply (CtrNoDelta.TwinB.nodelta_st_ok AI IMGX IMGX_aci ACCT UNIV Cw OPS AI_fake OPS_holds1 OPS_fp1 OPS_cov1 OPS_frame_other OPS_fp_other OTHER OPS_mo_other
           OPS_cov0_img E st ms mo r hargs wnl L RNG sta LBa aw st1 Fv Gv R' m' mo' RNG sta _ _ HS CP FS CF).
  -
    intros rg Hrg. unfold CtrFrame.TwinB.kept_regsA in Hrg. cbn [In] in Hrg. repeat (destruct Hrg as [<-|Hrg]; [reflexivity|]). destruct Hrg.
  - intros x i Hx. exact (CtrFree.TwinB.cfvF_clob R' x i Hx).
  - rewrite HeapCtr.TwinB.den_VPz. rewrite (CtrFrame.TwinB.ev_E'_fresh E st FOK Fv Gv 15 ltac:(lia)). reflexivity.
  - exact MINV'.
  - exact STK'.
  -
    intros LB0 AR0 a Ha STB. destruct STB as [S1|[S2|S3]].
    + apply (FrameV.TwinB.frame_v_of_raw bsegs). apply RAW; [exact Ha| | | |]; unfold MTX, SH_LO, SH_HI, ASH_LO, ASH_HI, sp, R in *; lia.
    + destruct (Z_lt_le_dec a MTX) as [Q|Q]; [| destruct (Z_lt_le_dec a (MTX + 8)) as [Q'|Q']].
      * apply (FrameV.TwinB.frame_v_of_raw bsegs). pose proof (aci_low' a S2) as AL.
        apply RAW; [exact Ha| | | |]; unfold MTX, SH_LO, SH_HI, ASH_LO, ASH_HI, AIMG_HI in *; lia.
      * split; [exact (mtx_view (ms_mem ms) m' MTX0 MTXZ a ltac:(lia)) | exact (wbm_all (ms_mem ms) m' WM a)].
      * apply (FrameV.TwinB.frame_v_of_raw bsegs). pose proof (aci_low' a S2) as AL.
        apply RAW; [exact Ha| | | |]; unfold MTX, SH_LO, SH_HI, ASH_LO, ASH_HI, AIMG_HI in *; lia.
    + apply (FrameV.TwinB.frame_v_of_raw bsegs). exact (IUOUT LB0 AR0 a Ha S3).
  -   exact IUOUT.
  -
    intros o a Ho NI Ha FP. unfold not_id in NI. apply Uint63.eqb_false_spec in NI.
    pose proof (OPS_fp_mtx _ _ a NI FP) as NM. destruct (OPS_fp_shw _ _ a NI (NOGSH o Ho) FP) as [NS1 NS2].
    destruct (OPS_fp_other _ _ a NI FP) as [INA|[(a' & INA & ->)|(a' & STK & ->)]].
    + pose proof (aci_low' a INA) as AL.
      apply (RAW a); [unfold two64 in Ha; lia| | | |]; unfold MTX, SH_LO, SH_HI, ASH_LO, ASH_HI, AIMG_HI in *; lia.
    + pose proof (aci_low' a' INA) as AL. destruct INA as (iv0 & I0 & I1). pose proof (AI_aci_lo AI iv0 I0) as A0.
      pose proof (CtrPre.TwinB.shad_img_band a' ltac:(lia)) as BND.
      apply (RAW (shad a')); [unfold two64 in Ha; lia| | exact NM | exact NS1 | exact NS2]. lia.
    +
      assert (ZN : 0x10006fef8000 <= shad a' < 0x10007fff8000) by (unfold shad, ASHOFF; rewrite Z.shiftr_div_pow2 by lia; change (2 ^ 3) with 8; clear - STK ATR; Z.div_mod_to_equations; lia).
      apply (RAW (shad a')); [unfold two64 in Ha; lia| | exact NM | exact NS1 | exact NS2]. lia.
  -   intros a Ha _. exact (wbm_all (ms_mem ms) m' WM a).
  -
    intros a Ha SC IB.
    assert (ZN : (0x7fffa000 <= a < 0x7fffc6a0) \/ (0x800b7c58 <= a < 0x800be0e0) \/ (0x10006fef8000 <= a < 0x10007fff8000)).
    { destruct SC as [(a' & RR & ->)|(vv & Hv & RR)].
      - right; right. unfold shad, ASHOFF. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8. clear - RR ATR. Z.div_mod_to_equations. lia.
      -
        destruct (Op.TwinB.SHLIT_cases vv Hv) as [->|(_ & P1 & P2 & P3)]; [left; cbn [fst snd] in RR; lia| right; left; lia]. }
    destruct (Z_lt_le_dec a SH_LO) as [QL|QL].
    { apply (FrameV.TwinB.frame_v_of_raw bsegs). apply RAW; [exact Ha| | | |]; unfold MTX, SH_LO, SH_HI, ASH_LO, ASH_HI, sp, R in *; lia. }
    destruct (Z_lt_le_dec a SH_HI) as [QH|QH].
    2:{ apply (FrameV.TwinB.frame_v_of_raw bsegs). apply RAW; [exact Ha| | | |]; unfold MTX, SH_LO, SH_HI, ASH_LO, ASH_HI, sp, R in *; lia. }
    split; [| exact (wbm_all (ms_mem ms) m' WM a)].
    unfold SH_LO, SH_HI in QL, QH.
    destruct IB as (k & rr & Hk & KZ & RNGa).
    assert (KN0 : k <> 0%uint63) by (intros ->; discriminate KZ).
    assert (ARc : aw_real AI ACCT UNIV aw LB (ms_mem ms) mo L RNG sta LBa) by (exists Wt; split; [exact WOF| exact ARW]).
    assert (INWIN : forall k0 len kd, CtrA.win_lookup wnl k0 = Some (len, kd) ->
              bv_unsigned (ev E k0) <= a < bv_unsigned (ev E k0) + bv_unsigned (den E len) -> False).
    { intros k0 len kd WL Hin.
      destruct (HeapCtrB.TwinB.nonstack_windows_In E nn rest wnl k0 len kd NW (HeapCtrB.TwinB.win_lookup_In _ _ _ _ WL)) as (_ & _ & KD & INW).
      assert (IU : in_user LB a).
      { pose proof (proj1 (Forall_forall _ _) WF _ INW) as (W1' & W2' & W3' & [[KS0 _]|[[KB B]|[KS2 (b & Hb & SUB)]]]); unfold w_iv in *; cbn [w_kind w_lo w_len] in *.
        - exfalso. exact (KD KS0).
        - apply in_ivs_In. eexists. split; [exact B|]. unfold in_iv. cbn [fst snd]. lia.
        - apply in_ivs_In. exists b. split; [exact Hb|]. apply SUB. unfold in_iv. cbn [fst snd]. lia. }
      pose proof (user_out AI ACCT UNIV AI_fake aw LB (ms_mem ms) mo L RNG sta LBa a ARc IU) as G. unfold AIMG_HI, KLS in G. lia. }
    pose proof (CallA.TwinB.aregion_just_sound bsegs OPS E st ms mo wnl ks offs rss k rr HS SPR AJ Hk KN0) as JU.
    destruct (CallA.TwinB.sp_region_inv st ks offs rss SPR) as (_ & Hrs & _).
    destruct JU as [[EQ TOPk]|[NE [(len0 & kd0 & WLS & LZ & HZ)|[[J1 J2]|VJ]]]].
    + exfalso. subst k. rewrite Hrs in Hk. injection Hk as <-. lia.
    + exfalso. apply (INWIN k len0 kd0 WLS). rewrite LZ in RNGa. lia.
    + exfalso. rewrite (CtrFrame.TwinB.SP_den OPS E st ms mo HS) in J1. fold R in J1. fold sp in J1. lia.
    +
      destruct VJ as [VJ|SL]; [| exfalso; pose proof (CtrPre.TwinB.sliver_low OPS E st ms mo ks offs rss k rr hargs nn md A nw rest LB a HS SPR Hk KN0 NE SL Hf Eh Tnw Nn Ln WF RNGa) as SLO; lia].
      pose proof (CallV.TwinB.view_just_sound bsegs OPS E st ms mo wnl ks offs rss k rr HS SPR Hk KN0 VJ) as VS. unfold CallV.TwinB.view_sem in VS. cbv zeta in VS.
      destruct VS as [((hs & ZV) & blo & bhi & SHZ & BHI & BLO)|[(hs & n0 & sh & len1 & ZV & _ & _ & WL1 & LO1 & HI1)|[(VI & v & Hv & V1 & V2)|(shD & kbD & nD & lenD & WLD & BTD & WLkD & STD & TND & ROD & LOD & HID)]]].
      * exfalso. destruct (SHZ a RNGa) as (a' & Ha' & EA).
        assert (BL : ATOP + 4096 <= blo).
        { destruct BLO as [(wlo & SW & ->)|[(rs0 & Frs & ->)|GE]].
          - exact (CallV.TwinB.wlo_floor E st hargs nn md A nw rest LB (ATOP + 4096) wlo Hf Eh Tnw Nn Ln WF SW).
          - rewrite Hrs in Frs. injection Frs as <-. exact FLOOR.
          - rewrite (CtrFrame.TwinB.SP_den OPS E st ms mo HS) in GE. fold R in GE. fold sp in GE. lia. }
        unfold CallV.TwinB.shz in EA. clear - EA Ha' BL ATR QH. Z.div_mod_to_equations. lia.
      * exfalso. apply (INWIN sh len1 ActrA.K_TWIN WL1). lia.
      * pose proof (proj1 (IMap.forallb_spec _ _ (so_bst _ _ _ _ _ _ HS)) HVO k rr Hk) as CK. unfold hull_view_ok in CK. rewrite VI in CK. cbn [negb orb] in CK.
        destruct (ActrA.zero_view rr) as [hs|] eqn:ZV; [|discriminate CK]. destruct (ActrA.find_pin (s_facts st) k) as [pa|] eqn:FP; [|discriminate CK].
        pose proof (CallV.TwinB.find_pin_sound E _ k pa (so_facts _ _ _ _ _ _ HS) FP) as EVK. pose proof (CallV.TwinB.zero_view_hi E rr hs ZV) as HIK.
        rewrite EVK, HIK in RNGa. unfold loZ in RNGa. cbn [u_hull CFG_ASAN fst snd] in CK.
        apply orb_prop in CK as [CK|CK]; [apply orb_prop in CK as [CK|CK]|].
        -- exfalso. apply Z.leb_le in CK. lia.
        -- exfalso. apply Z.leb_le in CK. lia.
        -- apply existsb_exists in CK as (c & HcZ & CC). apply andb_prop in CC as [C1 C2]. apply Z.leb_le in C1, C2.
           replace a with (fst c + (a - fst c)) at 1 by lia. rewrite (ZCH c HcZ (a - fst c) ltac:(lia)).

           pose proof (so_reg _ _ _ _ _ _ HS k rr Hk) as RO.
           assert (ZVI : rg_bg rr = BGZero /\ rg_cells rr = IMap.Leaf).
           { unfold ActrA.zero_view in ZV. destruct (rg_hi rr); try discriminate ZV. destruct (rg_bg rr); try discriminate ZV.
             destruct (rg_cells rr); try discriminate ZV. auto. }
           destruct ZVI as [BGZ RCL].
           pose proof (ro_bg _ _ _ _ _ _ RO (a - bv_unsigned (ev E k)) ltac:(intros _; unfold loZ; rewrite HIK, EVK; lia) ltac:(intros KK; rewrite KK in KZ; discriminate KZ)) as BG.
           assert (UNC : uncovered rr (a - bv_unsigned (ev E k))) by (intros g gr _ FF0; rewrite RCL in FF0; discriminate FF0).
           specialize (BG UNC). unfold bg_byte in BG. rewrite BGZ in BG. replace (bv_unsigned (ev E k) + (a - bv_unsigned (ev E k))) with a in BG by lia.
           symmetry. exact BG.
      *   exfalso. apply (INWIN shD lenD ActrA.K_TWIN WLD). lia.
  -
    apply (AI_frame AI L RNG sta LBa (ms_mem ms) m' _ AH MU WM).
    repeat (apply Forall_cons; [cbn [fst snd]|]); [| | | | apply Forall_nil].
    + left. left. fold sp. lia.
    + left. right. left. exists (0xd9530, 0xd9538). split; [exact ACI_mtx| cbn [fst snd]; lia].
    + right. right. right. left. exists (0x22d00, 0x23500). split; [exact ACI_glob| cbn [fst snd]; unfold ASHOFF; lia].
    + right. right. right. left. exists (0xd7fb0, 0xd85c8). split; [exact ACI_desc| cbn [fst snd]; unfold ASHOFF; lia].
  - exact ACP.
  -
    intros b x Hb FK Hx. pose proof (Op.TwinB.blk_band AI AI_fake L RNG sta LBa (ms_mem ms) b x AH Hb) as BB.
    destruct (AI_fake L RNG sta LBa (ms_mem ms) b AH Hb FK) as (_ & _ & _ & _ & SZ64 & _).
    specialize (BB ltac:(lia)). unfold MTX, SH_LO, SH_HI, ASH_LO, ASH_HI, AIMG_HI, KLS in *.
    apply RAW; lia.
  -
    apply (Op.TwinB.twins_pres_band AI L RNG sta LBa (ms_mem ms) m' AH). intros a Ha.
    assert (SA : shad ATOP = ASHOFF + ATOP / 8) by (unfold shad; rewrite Z.shiftr_div_pow2 by lia; reflexivity).
    rewrite SA in Ha. unfold ASHOFF in Ha.
    apply RAW; unfold MTX, SH_LO, SH_HI, ASH_LO, ASH_HI in *; [| | | |]; try (clear - Ha ATR LO3; Z.div_mod_to_equations; lia).
  - exact OTH.
  - exact HMI'.
  - exact (fun P => P).
Qed.
End Leaf.
End TwinB.
