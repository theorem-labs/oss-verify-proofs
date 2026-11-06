(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import PrimInt63 Uint63.
From Stdlib Require Import Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib Require Import PropExec MState Cells Frame ITree Nodes Decode.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib Require ALib.Mem ALib.Step.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA Require Import AcctCore ExecF ITreeA NodesA.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA Require Shadow.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec Require Import STree AsanCtrl AsanEmbed.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require Import AImg AProto ABase AMalloc_iface.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require Import AMalloc_iface2.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require I_asan_memcpy0.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common Require Import RunDraw ShapeAlg.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX Require Import W64 Val IMap Instr State Step Plan PlanSound.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX Require Import Mem.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Heap Require Import Op.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Ctr Require Import Lib Defs DefsA.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Glue Require Ops.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Glue Require Nodes CtrSys OblsLib.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Bridge Require Import Ledger Op Adeq.
Import ListNotations.
Import W64 Val OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Mem.Mem FI St Step Plan PlanS CtrLib HeapOp.
Open Scope Z_scope.
Unset Lia Cache.

From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Bridge Require Import Actr.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX Require Import W64Proofs ValProofs MemProofs StepSoundBase.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Br Require Import CtrFX.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Br Require HeapCtr HeapCtrB MemFX.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Bridge Require CallA GlueA CtrPre CtrFrame CtrNoDelta CtrFree.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.GlueA Require UnreggGeo.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.GlueA Require Import ReadC ReadPre MemOps ReadSound.
Unset Nia Cache. Unset Nra Cache.
Import ValP MemP CtrFX ActrA ReadC.
Module AM := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Mem.
Module CS := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Glue.CtrSys.CtrSys.
Module OLB := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Glue.OblsLib.OL.

Definition in_stage (a : Z) : bool := (STAGE <=? a) && (a <? STAGE + 65536).

Definition mjoin (m m' : amem) : amem := fun x => if in_stage (bv_unsigned x) then m x else m' x.

Section MemSide.
Context {rc : runConstT}.
Variables (m m' : amem) (sp lo n : Z) (errv : word).
Notation W := [(sp - 2208, sp); (STAGE, STAGE + n); (ERRNO, ERRNO + 4)]%Z.
Hypothesis MU : munch W m m'.
Hypothesis WM : wmono asegs m m'.
Hypothesis LO : ATOP + 4096 <= lo /\ lo <= sp - 4096 /\ sp < 2 ^ 47.
Hypothesis Hn : 0 < n <= 65536.
Hypothesis ERR0 : AS.rw_cells asegs m ERRNO [C4 errv].
Hypothesis ERR1 : AS.rw_cells asegs m' ERRNO [C4 errv].
Notation mj := (mjoin m m').

Lemma wa_u : forall a, 0 <= a < 2 ^ 64 -> bv_unsigned (AM.wa a) = a.
Proof. intros a Ha. unfold AM.wa. rewrite Z_to_bv_unsigned. apply bv_wrap_small. unfold bv_modulus. lia. Qed.

Lemma raw_out : forall a, 0 <= a < 2 ^ 64 ->
  ~ (sp - 2208 <= a < sp) -> ~ (STAGE <= a < STAGE + n) -> ~ (ERRNO <= a < ERRNO + 4) -> m' (AM.wa a) = m (AM.wa a).
Proof. intros a Ha N1 N2 N3. apply MU. rewrite (wa_u a Ha). cbn [outside]. tauto. Qed.

Lemma mj_out : forall a, 0 <= a < 2 ^ 64 -> ~ (sp - 2208 <= a < sp) -> ~ (ERRNO <= a < ERRNO + 4) -> mj (AM.wa a) = m (AM.wa a).
Proof.
  intros a Ha N1 N3. unfold mjoin. rewrite (wa_u a Ha). destruct (in_stage a) eqn:IS; [reflexivity|].
  apply raw_out; [exact Ha | exact N1 | | exact N3]. unfold in_stage in IS. lia.
Qed.
Lemma mj_stage : forall a, 0 <= a < 2 ^ 64 -> STAGE <= a < STAGE + 65536 -> mj (AM.wa a) = m (AM.wa a).
Proof. intros a Ha S. unfold mjoin. rewrite (wa_u a Ha). unfold in_stage. replace ((STAGE <=? a) && (a <? STAGE + 65536)) with true by lia. reflexivity. Qed.
Lemma mj_final : forall a, 0 <= a < 2 ^ 64 -> ~ (STAGE <= a < STAGE + 65536) -> mj (AM.wa a) = m' (AM.wa a).
Proof. intros a Ha S. unfold mjoin. rewrite (wa_u a Ha). unfold in_stage. replace ((STAGE <=? a) && (a <? STAGE + 65536)) with false by lia. reflexivity. Qed.

Lemma wbm_all : forall a, wb asegs m a = true -> wb asegs m' a = true.
Proof. intros a H. apply (GlueA.wb_wviewA asegs). apply (GlueA.wb_wviewA asegs) in H. exact (WM _ H). Qed.

Lemma errno_view : forall a, ERRNO <= a < ERRNO + 4 -> rb asegs m' a = rb asegs m a.
Proof.
  intros a Ha. destruct ERR0 as [[_ (_ & _ & B0)] _]. destruct ERR1 as [[_ (_ & _ & B1)] _].
  rewrite !(GlueA.rb_mrdA asegs). replace a with (ERRNO + Z.of_nat (Z.to_nat (a - ERRNO))) by lia.
  rewrite (B0 (Z.to_nat (a - ERRNO))), (B1 (Z.to_nat (a - ERRNO))); [reflexivity | |]; cbn; lia.
Qed.

Lemma wview_ext : forall (m1 m2 : amem) x, m2 x = m1 x -> wview asegs m2 x = wview asegs m1 x.
Proof. intros m1 m2 x H. unfold wview. rewrite H. reflexivity. Qed.
Lemma mrd_ext : forall (m1 m2 : amem) x, m2 x = m1 x -> AM.mrd asegs m2 x = AM.mrd asegs m1 x.
Proof. intros m1 m2 x H. unfold AM.mrd. rewrite H. reflexivity. Qed.
Lemma rb_ext : forall (m1 m2 : amem) a, m2 (Z_to_bv 64 a) = m1 (Z_to_bv 64 a) -> rb asegs m2 a = rb asegs m1 a.
Proof. intros m1 m2 a H. unfold rb. rewrite H. reflexivity. Qed.
Lemma wb_ext : forall (m1 m2 : amem) a, m2 (Z_to_bv 64 a) = m1 (Z_to_bv 64 a) -> wb asegs m2 a = wb asegs m1 a.
Proof. intros m1 m2 a H. unfold wb. rewrite (wview_ext m1 m2 _ H). reflexivity. Qed.

Lemma mj_cases : forall x, mj x = m x \/ mj x = m' x.
Proof. intros x. unfold mjoin. destruct (in_stage (bv_unsigned x)); auto. Qed.

Lemma stage_wb_any : forall (mm : amem) a, STAGE <= a < STAGE + 65536 -> wb asegs mm a = true.
Proof.
  intros mm a Ha.
  destruct (MemP.abs_writable_sound asegs STAGE 65536 ltac:(unfold STAGE; lia) ltac:(lia) ltac:(vm_compute; reflexivity)) as [_ WB].
  replace a with (STAGE + (a - STAGE)) by lia. apply (proj1 (WB (a - STAGE) ltac:(lia))).
Qed.

Lemma mj_wmono : wmono asegs m mj.
Proof.
  intros x H. destruct (in_stage (bv_unsigned x)) eqn:IS.
  - rewrite (wview_ext m mj x); [exact H|]. unfold mjoin. rewrite IS. reflexivity.
  - rewrite (wview_ext m' mj x); [exact (WM x H)|]. unfold mjoin. rewrite IS. reflexivity.
Qed.
Lemma mj_munch : munch [(sp - 2208, sp); (ERRNO, ERRNO + 4)]%Z m mj.
Proof.
  intros x OUT. cbn [outside] in OUT. pose proof (bv_unsigned_in_range _ x) as RX. unfold bv_modulus in RX.
  assert (EX : AM.wa (bv_unsigned x) = x) by (unfold AM.wa; apply Z_to_bv_bv_unsigned).
  rewrite <- EX. apply (mj_out (bv_unsigned x)); [lia | tauto | tauto].
Qed.
Lemma mj_mem_inv : AM.mem_inv asegs m -> AM.mem_inv asegs m' -> AM.mem_inv asegs mj.
Proof. intros I1 I2 a b H. destruct (mj_cases a) as [Q|Q]; rewrite Q in H; [exact (I1 a b H)| exact (I2 a b H)]. Qed.
Lemma mj_stk : stk asegs m' lo sp -> stk asegs mj lo sp.
Proof.
  intros (H1 & H2 & H). split; [exact H1|]. split; [exact H2|]. intros a Ha.
  assert (E : mj (AM.wa a) = m' (AM.wa a)) by (apply mj_final; [lia| unfold STAGE; pose proof atop_range; lia]).
  rewrite (wview_ext m' mj _ E), (mrd_ext m' mj _ E). exact (H a Ha).
Qed.
End MemSide.

Definition rstage_holds_v (file : list byte) (args : list word) (m : word -> option byte) : Prop :=
  match args with
  | [off; n] => bv_unsigned off + bv_unsigned n <= Z.of_nat (length file) /\ bv_unsigned n <= 65536 /\
               forall i, 0 <= i < bv_unsigned n -> rb asegs m (STAGE + i) = Some (nth (Z.to_nat (bv_unsigned off + i)) file (Z_to_bv 8 0))
  | _ => False
  end.

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

Hypothesis ACI_errno : exists iv0, In iv0 (aci AI) /\ fst iv0 <= ERRNO /\ ERRNO + 4 <= snd iv0.
Hypothesis OPS_fp_errno : forall id args a, id <> HEAP_ID -> Exists (fun iv => fst iv <= a < snd iv) (op_fp OPS id args) ->
  ~ (ERRNO <= a < ERRNO + 4).

Lemma aci_low' : forall a, in_ranges (aci AI) a -> a < AIMG_HI.
Proof. intros a (iv0 & Hi & RR). pose proof (AI_aci_img AI iv0 Hi). lia. Qed.

Lemma phaseA : forall st E ms mo r hargs wnl st1 (L : alayout) (RNG : footprint) (sta : astate) (LBa : list ablock) (aw : word)
    (m' : amem) (R' : bvmap 5 word) (mo_j : Model) (errv : word) (n : Z) (v : sv) (nx' : int),
  st_ok asegs OPS E st ms mo -> call_pre st = Some r -> forget_stack_below_sp_g st = Some st1 ->
  CtrPre.acallG AI ACCT UNIV Cw E st ms mo r hargs wnl L RNG sta LBa aw -> AHEAP AI L RNG sta LBa (ms_mem ms) ->
  let R := ms_regs ms in let sp := bv_unsigned (AP.getr R 2) in
  ATOP + 4096 <= CtrPre.sp_lo E st -> CtrPre.sp_lo E st <= sp - 4096 -> sp < 2 ^ 47 -> 0 < n <= 65536 ->
  munch [(sp - 2208, sp); (STAGE, STAGE + n); (ERRNO, ERRNO + 4)]%Z (ms_mem ms) m' -> wmono asegs (ms_mem ms) m' ->
  AM.mem_inv asegs (ms_mem ms) -> AM.mem_inv asegs m' -> stk asegs m' (CtrPre.sp_lo E st) sp ->
  AS.rw_cells asegs (ms_mem ms) ERRNO [C4 errv] -> AS.rw_cells asegs m' ERRNO [C4 errv] ->
  (forall rg, In rg CtrFrame.kept_regsA -> AP.getr R' rg = AP.getr R rg) ->
  let Fv := CtrFree.cfvF R' in let Gv := fun (_ _ : Z) => Z_to_bv 8 0 in
  den (CtrFrame.E' E st Fv Gv) v = AP.getr R' 10%bv ->
  OTHER mo mo_j -> op_minv OPS mo_j -> ACCT aw L RNG sta LBa mo_j ->
  st_ok asegs OPS (CtrFrame.E' E st Fv Gv)
    (SS r (rf_set (s_rf (clobber st1)) X10 v) (s_ff st) (s_resv st) (s_regs st1) (s_facts st) (s_ops st) (s_priv st) nx')
    (CtrFrame.ms' ms r R' (mjoin (ms_mem ms) m')) mo_j.
Proof.
  intros st E ms mo r hargs wnl st1 L RNG sta LBa aw m' R' mo_j errv n v nx' HS CP FS CF AH R sp BOT LO SPT Hn MU WM MI MI' STK' ERR0 ERR1 KEPT Fv Gv DV OTH MIj ACj.
  pose proof atop_range as ATR.
  assert (LO3 : ATOP + 4096 <= CtrPre.sp_lo E st /\ CtrPre.sp_lo E st <= sp - 4096 /\ sp < 2 ^ 47) by lia.
  set (m := ms_mem ms) in *.
  assert (IUOUT : forall LB0, aw_real AI ACCT UNIV aw LB0 m mo L RNG sta LBa -> forall a, 0 <= a < 2 ^ 64 -> in_user LB0 a ->
            mjoin m m' (AM.wa a) = m (AM.wa a)).
  { intros LB0 AR0 a Ha IU. pose proof (UnreggGeo.user_out AI ACCT UNIV AI_fake aw LB0 m mo L RNG sta LBa a AR0 IU) as G.
    apply (mj_out m m' sp (CtrPre.sp_lo E st) n MU LO3 Hn a Ha); unfold ERRNO, AIMG_HI, KLS in *; lia. }
  apply (CtrNoDelta.nodelta_st_ok AI IMGX IMGX_aci ACCT UNIV Cw OPS AI_fake OPS_holds1 OPS_fp1 OPS_cov1 OPS_frame_other OPS_fp_other OTHER OPS_mo_other
           OPS_cov0_img E st ms mo r hargs wnl L RNG sta LBa aw st1 Fv Gv R' (mjoin m m') mo_j RNG sta _ _ HS CP FS CF).
  - exact KEPT.
  - intros x i Hx. exact (CtrFree.cfvF_clob R' x i Hx).
  - exact DV.
  - exact (mj_mem_inv m m' MI MI').
  - exact (mj_stk m m' sp (CtrPre.sp_lo E st) LO3 STK').
  -
    intros LB0 AR0 a Ha STB. destruct STB as [S1|[S2|S3]].
    + apply (FrameV.frame_v_of_raw asegs). apply (mj_out m m' sp (CtrPre.sp_lo E st) n MU LO3 Hn a Ha); unfold ERRNO, sp, R in *; lia.
    + destruct (Z_lt_le_dec a ERRNO) as [Q|Q]; [| destruct (Z_lt_le_dec a (ERRNO + 4)) as [Q'|Q']].
      * apply (FrameV.frame_v_of_raw asegs). pose proof (aci_low' a S2) as AL. apply (mj_out m m' sp (CtrPre.sp_lo E st) n MU LO3 Hn a Ha); unfold ERRNO, AIMG_HI in *; lia.
      * assert (EJ : mjoin m m' (Z_to_bv 64 a) = m' (Z_to_bv 64 a)) by (apply (mj_final m m' a Ha); unfold ERRNO, STAGE in *; lia).
        split; [rewrite (rb_ext m' (mjoin m m') a EJ); exact (errno_view m m' errv ERR0 ERR1 a ltac:(lia))
               | intros Wb; rewrite (wb_ext m' (mjoin m m') a EJ); exact (wbm_all m m' WM a Wb)].
      * apply (FrameV.frame_v_of_raw asegs). pose proof (aci_low' a S2) as AL. apply (mj_out m m' sp (CtrPre.sp_lo E st) n MU LO3 Hn a Ha); unfold ERRNO, AIMG_HI in *; lia.
    + apply (FrameV.frame_v_of_raw asegs). exact (IUOUT LB0 AR0 a Ha S3).
  -   exact IUOUT.
  -
    intros o a Ho NI Ha FP. unfold not_id in NI. apply Uint63.eqb_false_spec in NI.
    pose proof (OPS_fp_errno _ _ a NI FP) as NE. destruct (OPS_fp_other _ _ a NI FP) as [INA|[(a' & INA & ->)|(a' & STK & ->)]].
    + pose proof (aci_low' a INA) as AL.
      apply (mj_out m m' sp (CtrPre.sp_lo E st) n MU LO3 Hn a); [unfold two64 in Ha; lia| unfold AIMG_HI in *; lia | exact NE].
    + pose proof (aci_low' a' INA) as AL. destruct INA as (iv0 & I0 & I1). pose proof (AI_aci_lo AI iv0 I0) as A0.
      pose proof (CtrPre.shad_img_band a' ltac:(lia)) as BND.
      apply (mj_out m m' sp (CtrPre.sp_lo E st) n MU LO3 Hn (shad a')); [unfold two64 in Ha; lia| lia | exact NE].
    +
      assert (ZN : 0x7fffa000 <= shad a' < 0x10007fff8000) by (unfold shad, ASHOFF; rewrite Z.shiftr_div_pow2 by lia; change (2 ^ 3) with 8; clear - STK ATR; Z.div_mod_to_equations; lia).
      apply (mj_out m m' sp (CtrPre.sp_lo E st) n MU LO3 Hn (shad a')); [unfold two64 in Ha; lia| lia | exact NE].
  -   intros a Ha _ Wb. apply (GlueA.wb_wviewA asegs). apply (GlueA.wb_wviewA asegs) in Wb. exact (mj_wmono m m' WM _ Wb).
  -
    intros a Ha SC _. apply (FrameV.frame_v_of_raw asegs).
    assert (ZN : 0x7fffa000 <= a < 0x10007fff8000).
    { destruct SC as [(a' & RR & ->)|(vv & Hv & RR)].
      - unfold shad, ASHOFF. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8. clear - RR ATR. Z.div_mod_to_equations. lia.
      - destruct (Op.SHLIT_cases vv Hv) as [->|(_ & P1 & P2 & P3)]; [cbn [fst snd] in RR|]; lia. }
    apply (mj_out m m' sp (CtrPre.sp_lo E st) n MU LO3 Hn a Ha); unfold ERRNO, STAGE, sp, R in *; lia.
  -
    apply (AI_frame AI L RNG sta LBa m (mjoin m m') _ AH (mj_munch m m' sp (CtrPre.sp_lo E st) n MU LO3 Hn) (mj_wmono m m' WM)).
    repeat (apply Forall_cons; [cbn [fst snd]|]); [| | apply Forall_nil].
    + left. left. fold sp. lia.
    + left. right. left. destruct ACI_errno as (iv0 & I0 & I1 & I2). exists iv0. split; [exact I0| lia].
  - exact ACj.
  -
    intros b x Hb FK Hx. pose proof (Op.blk_band AI AI_fake L RNG sta LBa m b x AH Hb) as BB.
    destruct (AI_fake L RNG sta LBa m b AH Hb FK) as (_ & _ & _ & _ & SZ64 & _). specialize (BB ltac:(lia)).
    apply (mj_out m m' sp (CtrPre.sp_lo E st) n MU LO3 Hn x); unfold ERRNO, AIMG_HI, KLS in *; lia.
  -
    apply (Op.twins_pres_band AI L RNG sta LBa m (mjoin m m') AH). intros a Ha.
    assert (SA : shad ATOP = ASHOFF + ATOP / 8) by (unfold shad; rewrite Z.shiftr_div_pow2 by lia; reflexivity).
    rewrite SA in Ha. unfold ASHOFF in Ha.
    apply (mj_out m m' sp (CtrPre.sp_lo E st) n MU LO3 Hn a); unfold ERRNO in *; clear - Ha ATR LO3; Z.div_mod_to_equations; lia.
  - exact OTH.
  - exact MIj.
  - exact (fun P => P).
Qed.

Variables (p1 file : list byte).
Hypothesis OPS_holds_fd3' : forall args m mo, Ops.Ops.fd3_holds p1 file args mo -> op_holds OPS CtrS.FD3_ID args m mo.
Hypothesis OPS_holds_rstage' : forall args m mo, rstage_holds_v file args m -> op_holds OPS ReadC.RSTV_ID args m mo.
Hypothesis OPS_fp_fd3 : forall args, op_fp OPS CtrS.FD3_ID args = [].
Hypothesis OPS_fp_rstage : forall args args', op_fp OPS ReadC.RSTV_ID args = op_fp OPS ReadC.RSTV_ID args'.
Hypothesis OPS_fp_nostage : forall id args a, id <> ReadC.RSTV_ID -> Exists (fun iv => fst iv <= a < snd iv) (op_fp OPS id args) ->
  ~ (STAGE <= a < STAGE + 65536).
Hypothesis OPS_fds_other : forall id args m mo f, id <> HEAP_ID -> CtrS.is_fd_op (OpI id []) = false ->
  op_holds OPS id args m mo -> op_holds OPS id args m (with_fds f mo).
Hypothesis OPS_cov1_heap : forall id args z, op_cov1 OPS id args z -> id = HEAP_ID.
Hypothesis minv_fds : forall mo f, op_minv OPS mo -> op_minv OPS (with_fds f mo).
Hypothesis ACCT_fds : forall aw L RNG st LBa mo f, ACCT aw L RNG st LBa mo -> ACCT aw L RNG st LBa (with_fds f mo).
Hypothesis ACI_stage : exists iv0, In iv0 (aci AI) /\ fst iv0 <= STAGE /\ STAGE + 65536 <= snd iv0.

Lemma count_one_args : forall id os o args, In o os -> op_id o = id -> CtrA.count_op id os = 1%nat -> find_op id os = Some args -> op_args o = args.
Proof.
  intros id os. induction os as [|o0 os IH]; intros o args Hin Hid Hc Hf; [destruct Hin|].
  cbn [CtrA.count_op find_op] in Hc, Hf. destruct (PrimInt63.eqb (op_id o0) id) eqn:Q.
  - injection Hf as <-. destruct Hin as [->|Hin]; [reflexivity|]. exfalso. injection Hc as Hc.
    clear IH Q. induction os as [|o1 os IH2]; [destruct Hin|]. cbn [CtrA.count_op] in Hc. destruct (PrimInt63.eqb (op_id o1) id) eqn:Q1; [discriminate Hc|].
    destruct Hin as [->|Hin]; [rewrite Hid, Uint63.eqb_refl in Q1; discriminate Q1| exact (IH2 Hin Hc)].
  - destruct Hin as [->|Hin]; [rewrite Hid, Uint63.eqb_refl in Q; discriminate Q|]. exact (IH o args Hin Hid Hc Hf).
Qed.

Lemma phaseB : forall st E ms mo r hargs wnl st1 (L : alayout) (RNG : footprint) (sta : astate) (LBa : list ablock) (aw : word)
    (m' : amem) (R' : bvmap 5 word) (mo_j mo' : Model) (n : Z) (v : sv) (nx' : int) (off newoff nsv : sv) (fs' : list fact) (os' : list opinst),
  st_ok asegs OPS E st ms mo -> call_pre st = Some r -> forget_stack_below_sp_g st = Some st1 ->
  CtrPre.acallG AI ACCT UNIV Cw E st ms mo r hargs wnl L RNG sta LBa aw -> AHEAP AI L RNG sta LBa (ms_mem ms) ->
  let R := ms_regs ms in let sp := bv_unsigned (AP.getr R 2) in
  ATOP + 4096 <= CtrPre.sp_lo E st -> CtrPre.sp_lo E st <= sp - 4096 -> sp < 2 ^ 47 -> 0 < n <= 65536 ->
  munch [(sp - 2208, sp); (STAGE, STAGE + n); (ERRNO, ERRNO + 4)]%Z (ms_mem ms) m' -> wmono asegs (ms_mem ms) m' ->
  let Fv := CtrFree.cfvF R' in let Gv := fun (_ _ : Z) => Z_to_bv 8 0 in
  let E' := CtrFrame.E' E st Fv Gv in
  st_ok asegs OPS E'
    (SS r (rf_set (s_rf (clobber st1)) X10 v) (s_ff st) (s_resv st) (s_regs st1) (s_facts st) (s_ops st) (s_priv st) nx')
    (CtrFrame.ms' ms r R' (mjoin (ms_mem ms) m')) mo_j ->
  CtrS.priv_has st 6275344%uint63 CtrS.STAGE_LEN = true ->
  (exists r1 r2, In (OpI ReadC.RSTV_ID [r1; r2]) (s_ops st)) ->
  mo' = with_fds (m_fds mo') mo_j -> ACCT aw L RNG sta LBa mo_j -> op_minv OPS mo_j ->
  Ops.Ops.fd3_holds p1 file [den E' newoff] mo' ->
  rstage_holds_v file [den E' off; den E' nsv] m' ->
  Forall (fact_holds E') fs' ->
  (forall o, In o os' -> o = OpI CtrS.FD3_ID [newoff] \/ o = OpI ReadC.RSTV_ID [off; nsv] \/
                         (In o (s_ops st) /\ CtrS.is_fd_op o = false /\ PrimInt63.eqb (op_id o) ReadC.RSTV_ID = false)) ->
  (forall o, In o (s_ops st) -> op_id o = HEAP_ID -> In o os') ->
  st_ok asegs OPS E'
    (SS r (rf_set (s_rf (clobber st1)) X10 v) (s_ff st) (s_resv st) (s_regs st1) (fs' ++ s_facts st) os' (s_priv st) nx')
    (CtrFrame.ms' ms r R' m') mo'.
Proof.
  intros st E ms mo r hargs wnl st1 L RNG sta LBa aw m' R' mo_j mo' n v nx' off newoff nsv fs' os' HS CP FS CF AH R sp BOT LO SPT Hn MU WM Fv Gv E'
         HSj PRIV HRS EMO ACj MIj HFD3 HRST HFS HOS HKEEP.
  pose proof atop_range as ATR.
  assert (LO3 : ATOP + 4096 <= CtrPre.sp_lo E st /\ CtrPre.sp_lo E st <= sp - 4096 /\ sp < 2 ^ 47) by lia.
  set (m := ms_mem ms) in *.
  change (CtrFrame.ms' ms r R' m') with (ms_with_mem (CtrFrame.ms' ms r R' (mjoin m m')) m').
  change (SS r (rf_set (s_rf (clobber st1)) X10 v) (s_ff st) (s_resv st) (s_regs st1) (fs' ++ s_facts st) os' (s_priv st) nx')
    with (let T := SS r (rf_set (s_rf (clobber st1)) X10 v) (s_ff st) (s_resv st) (s_regs st1) (s_facts st) (s_ops st) (s_priv st) nx' in
          SS (s_pc T) (s_rf T) (s_ff T) (s_resv T) (s_regs T) (fs' ++ s_facts T) os' (s_priv T) nx').
  cbv zeta.
  apply (st_ok_memops asegs OPS E' _ _ mo_j mo' fs' os' nx' m' HSj HFS).
  - rewrite EMO. apply minv_fds. exact MIj.
  -   unfold ops_hold. apply Forall_forall. intros o Ho.
    destruct (HOS o Ho) as [-> | [-> | (Hin & Hnf & Hnr)]]; cbn [op_id op_args map].
    + apply OPS_holds_fd3'. exact HFD3.
    + apply OPS_holds_rstage'. exact HRST.
    + destruct (PrimInt63.eqb (op_id o) HEAP_ID) eqn:QH.
      *
        apply Uint63.eqb_correct in QH.
        destruct CF as (LB & ks & offs & rss & ksp & nn & md & A & nw & rest & SPR & Hksp & SPE & K16 & LOSP & FLOOR & Hf & Hc & Eh & Tnw & Nn & Ln & N255
                        & NW & AN & AJ & TS & WF & HC & AWden & (W & WOF & ARW & TI)).
        destruct (HeapCtr.call_pre_inv st r CP) as (FOK & _).
        pose proof (count_one_args HEAP_ID (s_ops st) o hargs Hin QH Hc Hf) as EA. rewrite QH, EA.
        assert (AR : aw_real AI ACCT UNIV aw LB m mo L RNG sta LBa) by (exists W; split; [exact WOF| exact ARW]).
        assert (SBU : forall a, 0 <= a < 2 ^ 64 -> in_user LB a -> m' (AM.wa a) = m (AM.wa a)).
        { intros a Ha IU. pose proof (UnreggGeo.user_out AI ACCT UNIV AI_fake aw LB m mo L RNG sta LBa a AR IU) as G.
          apply (raw_out m m' sp (CtrPre.sp_lo E st) n MU LO3 Hn a Ha); unfold STAGE, ERRNO, AIMG_HI, KLS in *; lia. }

        set (W' := mkWit (w_L W) RNG sta (w_LBa W) (w_T W) (w_FA W) m' (w_zc W)).
        assert (AR' : aw_realW AI ACCT UNIV aw LB m' mo' W').
        { destruct WOF as (E1 & E2 & E3 & E4).
          apply (aw_real_nodelta AI ACCT UNIV AI_fake aw aw LB m mo W RNG sta m' mo' ARW).
          - rewrite E1, E4. apply (AI_frame AI L RNG sta LBa m m' _ AH MU WM).
            repeat (apply Forall_cons; [cbn [fst snd]|]); [| | | apply Forall_nil].
            + left. left. fold sp. lia.
            + left. right. left. destruct ACI_stage as (iv0 & I0 & I1 & I2). exists iv0. split; [exact I0| lia].
            + left. right. left. destruct ACI_errno as (iv0 & I0 & I1 & I2). exists iv0. split; [exact I0| lia].
          - rewrite E1, E4. rewrite EMO. apply ACCT_fds. exact ACj.
          -
            intros b x Hb FK Hx. rewrite E4 in Hb. pose proof (Op.blk_band AI AI_fake L RNG sta LBa m b x AH Hb Hx) as BB.
            apply (raw_out m m' sp (CtrPre.sp_lo E st) n MU LO3 Hn x); unfold STAGE, ERRNO, AIMG_HI, KLS in *; lia.
          -
            rewrite E4. apply (Op.twins_pres_band AI L RNG sta LBa m m' AH). intros a Ha.
            assert (SA : shad ATOP = ASHOFF + ATOP / 8) by (unfold shad; rewrite Z.shiftr_div_pow2 by lia; reflexivity).
            rewrite SA in Ha. unfold ASHOFF in Ha.
            apply (raw_out m m' sp (CtrPre.sp_lo E st) n MU LO3 Hn a); unfold STAGE, ERRNO in *; clear - Ha ATR LO3 Hn; Z.div_mod_to_equations; lia. }
        assert (TI' : ties W' (wins_of E nn rest)) by (apply (ties_ext W W'); [reflexivity| intros b; reflexivity| reflexivity| exact TI| intros b _ V; exact V| intros P; unfold W'; cbn [w_st]; rewrite <- (proj1 (proj2 (proj2 WOF))); exact P]).
        assert (DECN : decode (map (den E') hargs) = Some (w2Z md, den E A, wins_of E nn rest, map (den E) (skipn (3 * nn) rest)))
          by exact (CtrFrame.DEC' E st FOK Fv Gv nn rest hargs md A nw Hf Eh Tnw Nn Ln).
        rewrite OPS_holds1. exists (w2Z md), aw, (wins_of E nn rest), (map (den E) (skipn (3 * nn) rest)), LB, W'.
        split; [rewrite AWden; exact DECN|]. split; [exact (proj1 AR')|]. split; [exact WF|]. split; [| exact TI'].
        apply (cw_frame Cw _ _ _ _ m m' HC). intros a Ha U _. symmetry. unfold AM.wa in SBU.
        apply (SBU a ltac:(unfold two64 in Ha; lia)). exact U.
      *
        apply Uint63.eqb_false_spec in QH.
        pose proof (proj1 (Forall_forall _ _) (so_ops _ _ _ _ _ _ HSj) o Hin) as HO. cbn [s_ops] in HO.
        rewrite EMO. apply OPS_fds_other; [exact QH | destruct o as [oi oa]; cbn [op_id] in *; unfold CtrS.is_fd_op in *; cbn [op_id] in *; exact Hnf |].
        apply (OPS_frame_other _ _ (mjoin m m') m' mo_j QH HO).
        -- intros a Ha FP. apply Uint63.eqb_false_spec in Hnr. pose proof (OPS_fp_nostage _ _ a Hnr FP) as NS.
           apply (mj_final m m' a ltac:(unfold two64 in Ha; lia) NS).
        -- intros a Ha _ Wb. destruct (in_stage a) eqn:IS.
           ++ apply stage_wb_any. unfold in_stage in IS. lia.
           ++ rewrite <- (wb_ext m' (mjoin m m') a); [exact Wb|]. apply (mj_final m m' a ltac:(unfold two64 in Ha; lia)). unfold in_stage in IS. lia.
  -   unfold ops_apart. apply Forall_forall. intros o Ho a Ha.
    destruct (HOS o Ho) as [-> | [-> | (Hin & _ & _)]].
    + exfalso. cbn [op_id op_args map] in Ha. rewrite OPS_fp_fd3 in Ha. inversion Ha.
    + destruct HRS as (r1 & r2 & HinR).
      pose proof (proj1 (Forall_forall _ _) (so_apart _ _ _ _ _ _ HSj) _ HinR a) as X. cbn [op_id op_args map s_regs s_priv] in X, Ha |- *.
      rewrite (OPS_fp_rstage _ (map (den E') [r1; r2])) in Ha. exact (X Ha).
    + exact (proj1 (Forall_forall _ _) (so_apart _ _ _ _ _ _ HSj) o Hin a Ha).
  -
    intros a Ha. apply (OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Glue.Nodes.FXN.cov_keep OPS E' (s_ops st)); [| exact (so_cover _ _ _ _ _ _ HSj a Ha)].
    intros o Ho [z Hz]. exact (HKEEP o Ho (OPS_cov1_heap _ _ _ Hz)).
  -
    intros a Ha Hout. cbn [ms_mem CtrFrame.ms']. destruct (in_stage a) eqn:IS.
    + exfalso. unfold in_stage in IS. assert (SA : STAGE <= a < STAGE + 65536) by lia.
      destruct (MemP.abs_writable_sound asegs STAGE 65536 ltac:(unfold STAGE; lia) ltac:(lia) ltac:(vm_compute; reflexivity)) as [_ WB].
      destruct (WB (a - STAGE) ltac:(lia)) as [_ (seg & Hseg & _)]. replace (STAGE + (a - STAGE)) with a in Hseg by lia.
      destruct Hout as [Hn0 | Hnp]; [congruence|]. apply Hnp.
      unfold CtrS.priv_has in PRIV. apply existsb_exists in PRIV as ([plo phi] & Hinp & Heq).
      apply andb_prop in Heq as [E1 E2]. cbn [fst snd] in E1, E2. apply Uint63.eqb_correct in E1. apply Uint63.eqb_correct in E2. subst plo phi.
      unfold in_priv. apply Exists_exists. exists (6275344%uint63, PrimInt63.add 6275344%uint63 CtrS.STAGE_LEN). split; [exact Hinp|]. cbn [fst snd].
      change (to_Z 6275344%uint63) with STAGE. change (to_Z (PrimInt63.add 6275344%uint63 CtrS.STAGE_LEN)) with (STAGE + 65536). lia.
    + symmetry. apply (mj_final m m' a ltac:(unfold two64 in Ha; lia)). unfold in_stage in IS. lia.
  -
    intros a b Hb Hnone seg Hseg. change (mjoin m m' a = None) in Hnone.
    pose proof (bv_unsigned_in_range _ a) as RA. unfold bv_modulus in RA.
    destruct (in_stage (bv_unsigned a)) eqn:IS.
    + unfold in_stage in IS.
      destruct (MemP.abs_writable_sound asegs STAGE 65536 ltac:(unfold STAGE; lia) ltac:(lia) ltac:(vm_compute; reflexivity)) as [_ WB].
      destruct (WB (bv_unsigned a - STAGE) ltac:(lia)) as [_ (seg' & Hseg' & WS)].
      replace (STAGE + (bv_unsigned a - STAGE)) with (bv_unsigned a) in Hseg' by lia. rewrite Hseg in Hseg'. injection Hseg' as <-. exact WS.
    + exfalso. unfold mjoin in Hnone. rewrite IS in Hnone. congruence.
Qed.

Hypothesis MP_fds : forall mo f, MP mo -> MP (with_fds f mo).
Hypothesis PB_size : forall b, PB b -> b 11%uint63 = Z_to_le_bytes 8 (Ops.Ops.fsize file).

Lemma known_leu_sound_g : forall E st ms model a b, st_ok asegs OPS E st ms model ->
  known_leu (s_facts st) a b = true -> bv_unsigned (den E a) <= bv_unsigned (den E b).
Proof.
  intros E st ms model a b HS H. unfold known_leu, dec_false in H.
  destruct (decide_ltu (s_facts st) b a) as [[|]|] eqn:Hd; try discriminate H.
  pose proof (ValP.decide_ltu_sound E (s_facts st) (so_facts _ _ _ _ _ _ HS) b a false Hd) as X.
  apply (proj1 (ValP.ltu_iff _ _ false)) in X. exact X.
Qed.
Lemma decide_ltu_holds_g : forall E st ms model a b r0, st_ok asegs OPS E st ms model ->
  decide_ltu (s_facts st) a b = Some r0 -> (if r0 then bv_unsigned (den E a) < bv_unsigned (den E b) else bv_unsigned (den E b) <= bv_unsigned (den E a)).
Proof.
  intros E st ms model a b r0 HS Hd.
  pose proof (ValP.decide_ltu_sound E (s_facts st) (so_facts _ _ _ _ _ _ HS) a b r0 Hd) as X.
  apply (proj1 (ValP.ltu_iff _ _ r0)) in X. exact X.
Qed.
Lemma ops_args_below : forall n st o a, st_vars_below n st = true -> In o (s_ops st) -> In a (op_args o) -> sv_vars_below n a = true.
Proof.
  intros n st o a H Ho Ha. unfold st_vars_below in H. apply andb_prop in H as [_ H].
  exact (proj1 (forallb_forall _ _) (proj1 (forallb_forall _ _) H o Ho) a Ha).
Qed.

Lemma aread_leaf_ok : ReadSound.aread_leaf AI ACCT UNIV Cw OPS p1 file OTHER MP PB.
Proof.
  unfold ReadSound.aread_leaf.
  intros st sts K E ms mo r hargs wnl st1 off cnt L RNG sta LBa aw junk errv HS HMP HPB HK Happ PRE RPRE ECNT WR CP FS CF AH BOT LO SPT TP MI STG ERR ZSH
         FDS OFFLE ms' mo' HQ FDS' MPj MIj OTj ACj.
  set (R := ms_regs ms) in *. set (bs := file_read file (den E off) (Z_to_bv 64 cnt)) in *. set (mo_j := with_fds (m_fds mo) mo') in *.
  destruct HQ as (_ & t0 & t1 & t2 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & m' & EMS & MU & WM & MINV' & STK' & STGP & ERRP & LENB).
  pose proof atop_range as ATR.
  assert (ETP : bv_unsigned (AP.getr R 4) + -164 = ERRNO) by (rewrite TP; vm_compute; reflexivity).
  rewrite ETP in MU, ERRP. rewrite Z2Nat.id in MU by lia.
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
  assert (F1 : s_ff st1 = s_ff st /\ s_resv st1 = s_resv st /\ s_facts st1 = s_facts st
               /\ s_ops st1 = s_ops st /\ s_priv st1 = s_priv st /\ s_next st1 = s_next st).
  { destruct (CtrFrame.st1_fields st st1 FS) as (_ & _ & Q1 & Q2 & Q3 & Q4 & Q5 & Q6). repeat split; assumption. }
  destruct F1 as (FF1 & RV1 & FS1 & OP1 & PV1 & NX1).
  idtac "LEAF-2".
  destruct (aread_pre_inv st off RPRE) as (_ & _ & PRIV & (r1 & r2 & FRS) & CNTR & ONEFD & _ & F3).
  pose proof (HeapCtr.fresh_ok_inv st FOK) as (SVB & _).
  assert (VBoff : sv_vars_below (s_next st) off = true).
  { apply (ops_args_below (s_next st) st (OpI CtrS.FD3_ID [off]) off SVB (UnreggPre.find_op_In _ _ _ F3)). left. reflexivity. }
  assert (DOFF : den E' off = den E off) by (apply CtrFrame.den_E'; exact VBoff).
  set (OFF := bv_unsigned (den E off)) in *. set (S := Ops.Ops.fsize file) in *.
  pose proof (u64_range (den E off)) as Hur. fold OFF in Hur.
  assert (HSr : 0 <= S <= Z.of_nat (length file) /\ S <= 2 ^ 62) by (unfold S, Ops.Ops.fsize; lia).
  assert (EMO : mo' = with_fds (m_fds mo') mo_j) by (unfold mo_j; rewrite with_fds_idem, with_fds_self; reflexivity).
  assert (HMP' : MP mo') by (rewrite EMO; apply MP_fds; exact MPj).

  assert (TAIL : forall (st' : sstate) (newoff nsv : sv) (fs' : list fact) (os' : list opinst),
    In st' sts ->
    st' = SS r (rf_set (s_rf (clobber st1)) X10 nsv) (s_ff st) (s_resv st) (s_regs st1) (fs' ++ s_facts st) os' (s_priv st) (s_next (clobber st1)) ->
    den E' newoff = (den E off + len_word bs)%bv ->
    OFF + Z.of_nat (length bs) <= S ->
    den E' nsv = len_word bs ->
    (forall i, (i < length bs)%nat -> nth i bs (Z_to_bv 8 0) = nth (Z.to_nat OFF + i) file (Z_to_bv 8 0)) ->
    Forall (fact_holds E') fs' ->
    (forall o, In o os' -> o = OpI CtrS.FD3_ID [newoff] \/ o = OpI ReadC.RSTV_ID [off; nsv] \/
                           (In o (s_ops st) /\ CtrS.is_fd_op o = false /\ PrimInt63.eqb (op_id o) ReadC.RSTV_ID = false)) ->
    (forall o, In o (s_ops st) -> op_id o = HEAP_ID -> In o os') ->
    realizes asegs (mkCfg ms' mo') K).
  { intros st' newoff nsv fs' os' Hin Hst' Hnew Hle Hn Hbytes Hfs Hos Hkeep.
    apply (HK st' Hin E' ms' mo' (CtrFrame.EXT E st Fv Gv) HMP').
    rewrite Hst', EMS'.
    assert (Hlen : Z.of_nat (length bs) <= 65536) by lia.
    assert (Hlenw : bv_unsigned (len_word bs) = Z.of_nat (length bs)) by (apply (CS.len_word_u file); exact Hlen).
    apply (phaseB st E ms mo r hargs wnl st1 L RNG sta LBa aw m' R' mo_j mo' cnt nsv (s_next (clobber st1)) off newoff nsv fs' os' HS CP FS CF AH BOT LO SPT WR MU WM).
    - apply (phaseA st E ms mo r hargs wnl st1 L RNG sta LBa aw m' R' mo_j errv cnt nsv (s_next (clobber st1)) HS CP FS CF AH BOT LO SPT WR MU WM).
      + exact MI.
      + exact MINV'.
      + exact STK'.
      + exact ERR.
      + exact ERRP.
      + intros rg Hrg. unfold CtrFrame.kept_regsA in Hrg. cbn [In] in Hrg. repeat (destruct Hrg as [<-|Hrg]; [reflexivity|]). destruct Hrg.
      + fold Fv Gv E'. rewrite Hn. reflexivity.
      + exact OTj.
      + exact MIj.
      + exact ACj.
    - exact PRIV.
    - exists r1, r2. exact (UnreggPre.find_op_In _ _ _ FRS).
    - exact EMO.
    - exact ACj.
    - exact MIj.
    -
      fold Fv Gv E'. cbn [Ops.Ops.fd3_holds]. split.
      + rewrite FDS', FDS, Hnew. reflexivity.
      + rewrite Hnew, bv_add_unsigned, Hlenw. fold OFF. rewrite bv_wrap_small; [fold S; lia|]. unfold bv_modulus. lia.
    -
      fold Fv Gv E'. rewrite DOFF, Hn. cbn [rstage_holds_v]. rewrite Hlenw. fold OFF. split; [lia|]. split; [lia|].
      intros i Hi. destruct STGP as [[_ (_ & _ & BY)] _]. rewrite (GlueA.rb_mrdA asegs).
      replace (STAGE + i) with (STAGE + Z.of_nat (Z.to_nat i)) by lia.
      rewrite (BY (Z.to_nat i)).
      * cbn [cells_bytes cbytes]. rewrite nth_error_app1 by lia. rewrite (nth_error_nth' bs (Z_to_bv 8 0)) by lia.
        f_equal. rewrite (Hbytes (Z.to_nat i)) by lia. f_equal. lia.
      * cbn [cells_bytes cbytes]. rewrite !length_app. lia.
    - exact Hfs.
    - exact Hos.
    - exact Hkeep. }
  idtac "LEAF-3".

  unfold aread_apply in Happ. rewrite PRE, RPRE in Happ. cbv zeta in Happ.
  assert (DS11 : den E CtrS.SIZE11 = Z_to_bv 64 S).
  { unfold CtrS.SIZE11. apply (OLB.den_param8 E 11%uint63 S (PB_size _ HPB)). lia. }
  assert (HS11 : bv_unsigned (den E CtrS.SIZE11) = S) by (rewrite DS11; apply OLB.Z_to_bv64_unsigned; lia).
  assert (H40 : bv_unsigned (den E CtrS.OFF_MAX) = 2 ^ 40) by (cbn [den CtrS.OFF_MAX]; rewrite wbv_unsigned, wlit_ok; reflexivity).
  assert (Hadd0 : forall x : word, (x + len_word (@nil byte))%bv = x).
  { intros x. apply bv_eq. rewrite bv_add_unsigned. change (bv_unsigned (len_word (@nil byte))) with 0. rewrite Z.add_0_r.
    apply bv_wrap_small. apply u64_range. }
  assert (VB11 : sv_vars_below (s_next st) CtrS.SIZE11 = true) by reflexivity.
  assert (SHAPE : forall os' v0 fs0, fold_left addfact fs0 (ret_state st1 r os' v0)
            = SS r (rf_set (s_rf (clobber st1)) X10 v0) (s_ff st) (s_resv st) (s_regs st1) (rev fs0 ++ s_facts st) os' (s_priv st) (s_next (clobber st1))).
  { intros os' v0 fs0. assert (G0 : ret_state st1 r os' v0
        = SS r (rf_set (s_rf (clobber st1)) X10 v0) (s_ff st) (s_resv st) (s_regs st1) (s_facts st) os' (s_priv st) (s_next (clobber st1))).
    { unfold ret_state. rewrite <- FF1, <- RV1, <- FS1, <- PV1, <- FF, <- RV, <- RG, <- FS0, <- PV. destruct (clobber st1); reflexivity. }
    rewrite G0. clear G0. generalize (s_facts st). induction fs0 as [|f fs0 IH]; intros l0; [reflexivity|].
    cbn [fold_left rev]. unfold addfact at 2. cbn [s_pc s_rf s_ff s_resv s_regs s_facts s_ops s_priv s_next]. rewrite IH, <- app_assoc. reflexivity. }
  assert (Hbsu : bs = firstn (Z.to_nat cnt) (skipn (Z.to_nat OFF) file)).
  { unfold bs. rewrite file_read_unguarded. unfold word_to_nat. rewrite OLB.Z_to_bv64_unsigned by lia. reflexivity. }
  assert (Hlenbs : length bs = Nat.min (Z.to_nat cnt) (length file - Z.to_nat OFF)) by (rewrite Hbsu, length_firstn, length_skipn; reflexivity).
  assert (Hbytes : forall i, (i < length bs)%nat -> nth i bs (Z_to_bv 8 0) = nth (Z.to_nat OFF + i) file (Z_to_bv 8 0)).
  { intros i Hi. rewrite Hbsu in Hi |- *. apply (CS.nth_window file). exact Hi. }
  idtac "LEAF-4".
  assert (ONE : Nat.eqb (CtrS.count_fd_ops (s_ops st)) 1%nat = true) by exact ONEFD.
  assert (EOFCASE : known_leu (s_facts st) CtrS.SIZE11 off = true -> known_leu (s_facts st) off CtrS.OFF_MAX = true ->
            sts = [ret_state st1 r (set_op ReadC.RSTV_ID [off; VL wzero] (s_ops st)) (VL wzero)] -> realizes asegs (mkCfg ms' mo') K).
  { intros Heof Hom ESTS. rewrite ESTS in TAIL.
    pose proof (known_leu_sound_g E st ms mo _ _ HS Heof) as H1. rewrite HS11 in H1. fold OFF in H1.
    pose proof (known_leu_sound_g E st ms mo _ _ HS Hom) as H2. rewrite H40 in H2. fold OFF in H2.
    assert (HOS0 : OFF = S /\ S = Z.of_nat (length file)) by (unfold S, Ops.Ops.fsize in *; lia).
    assert (Hb0 : bs = []) by (rewrite Hbsu, skipn_all2 by lia; apply firstn_nil).
    apply (TAIL _ off (VL wzero) [] (set_op ReadC.RSTV_ID [off; VL wzero] (s_ops st)) (or_introl eq_refl) (SHAPE _ _ [])).
    + rewrite DOFF, Hb0. symmetry. apply Hadd0.
    + rewrite Hb0. cbn [length Z.of_nat]. lia.
    + rewrite Hb0. cbn [den]. rewrite wbv_wzero. reflexivity.
    + intros i Hi. rewrite Hb0 in Hi. cbn in Hi. lia.
    + constructor.
    + intros o Ho. destruct (CS.set_op_others file _ _ _ o CNTR Ho) as [->|[Hin Hne]]; [right; left; reflexivity|].
      destruct (PrimInt63.eqb (op_id o) CtrS.FD3_ID) eqn:E2.
      * left. apply (CS.fd_op_is file (s_ops st) [off] o ONE F3 Hin). unfold CtrS.is_fd_op. rewrite E2, orb_true_r. reflexivity.
      * right; right. split; [exact Hin|]. split; [exact (CS.set_fd_others file (s_ops st) off o ONE F3 Hin E2) | exact Hne].
    + intros o Ho Hid1. apply CS.set_op_keep; [exact Ho| rewrite Hid1; reflexivity]. }
  destruct (CtrS.want_ok (Step.getr st X12)) as [w|] eqn:HW.
  2:{
      match type of Happ with (if ?cnd then _ else _) = _ => destruct cnd eqn:CND; [|discriminate Happ] end.
      repeat match type of CND with (_ && _)%bool = true => let Q := fresh "Q" in apply andb_prop in CND as [CND Q] end.
      injection Happ as <-. exact (EOFCASE Q0 Q eq_refl). }
  destruct (want_ok_inv _ _ HW) as [X12E WRw].
  assert (ECW : cnt = w2Z w) by (rewrite <- ECNT, X12E; cbn [den]; apply wbv_unsigned).
  destruct (known_leu (s_facts st) CtrS.SIZE11 off) eqn:Heof.
  -
    destruct (known_leu (s_facts st) off CtrS.OFF_MAX) eqn:Hom; [|discriminate Happ]. injection Happ as <-.
    exact (EOFCASE eq_refl eq_refl eq_refl).
  -
    set (e := sv_alu ALU_ADD off (VL w)) in *. set (nB := sv_alu ALU_SUB CtrS.SIZE11 off) in *.
    destruct (known_leu (s_facts st) e CtrS.OFF_MAX) eqn:Hem; [|discriminate Happ]. cbn [negb] in Happ.
    pose proof (known_leu_sound_g E st ms mo _ _ HS Hem) as H2. rewrite H40 in H2.
    assert (He : den E e = (den E off + wbv w)%bv) by (subst e; rewrite den_sv_alu; reflexivity).
    assert (Heu : bv_unsigned (den E e) = OFF + cnt).
    { rewrite He, bv_add_unsigned, wbv_unsigned, <- ECW. apply bv_wrap_small. unfold bv_modulus. subst OFF. lia. }
    rewrite Heu in H2.
    assert (VBe : sv_vars_below (s_next st) e = true) by (apply MemFX.MemFX.sv_vars_below_alu; [left; reflexivity| exact VBoff| reflexivity]).
    assert (VBn : sv_vars_below (s_next st) nB = true) by (apply MemFX.MemFX.sv_vars_below_alu; [right; reflexivity| exact VB11| exact VBoff]).
    assert (De : den E' e = den E e) by (apply CtrFrame.den_E'; exact VBe).
    assert (DnB : den E' nB = den E nB) by (apply CtrFrame.den_E'; exact VBn).
    assert (D11 : den E' CtrS.SIZE11 = den E CtrS.SIZE11) by (apply CtrFrame.den_E'; exact VB11).
    assert (Hc2 : forall x : sv, Nat.eqb (CtrS.count_ops CtrS.FD3_ID (set_op ReadC.RSTV_ID [off; x] (s_ops st))) 1%nat = true).
    { intros x. rewrite (CS.count_ops_set_op_ne CtrS.FD3_ID ReadC.RSTV_ID) by reflexivity. exact (CS.count_FD3_one file _ off ONE F3). }
    assert (HOSx : forall (newoff nsv : sv) o,
      In o (set_op CtrS.FD3_ID [newoff] (set_op ReadC.RSTV_ID [off; nsv] (s_ops st))) ->
      o = OpI CtrS.FD3_ID [newoff] \/ o = OpI ReadC.RSTV_ID [off; nsv] \/
      (In o (s_ops st) /\ CtrS.is_fd_op o = false /\ PrimInt63.eqb (op_id o) ReadC.RSTV_ID = false)).
    { intros newoff nsv o Ho. destruct (CS.set_op_others file _ _ _ o (Hc2 nsv) Ho) as [->|[Ho1 Hne2]]; [left; reflexivity|right].
      destruct (CS.set_op_others file _ _ _ o CNTR Ho1) as [->|[Hin Hne3]]; [left; reflexivity|right].
      split; [exact Hin|]. split; [exact (CS.set_fd_others file (s_ops st) off o ONE F3 Hin Hne2) | exact Hne3]. }
    assert (KEEPx : forall (newoff nsv : sv) o, In o (s_ops st) -> op_id o = HEAP_ID ->
      In o (set_op CtrS.FD3_ID [newoff] (set_op ReadC.RSTV_ID [off; nsv] (s_ops st)))).
    { intros newoff nsv o Ho Hid1. apply CS.set_op_keep; [apply CS.set_op_keep; [exact Ho| rewrite Hid1; reflexivity]| rewrite Hid1; reflexivity]. }
    assert (CASE_A : OFF + cnt <= S ->
      In (addfact (ret_state st1 r (set_op CtrS.FD3_ID [e] (set_op ReadC.RSTV_ID [off; VL w] (s_ops st))) (VL w)) (FULe e CtrS.SIZE11)) sts ->
      realizes asegs (mkCfg ms' mo') K).
    { intros HA Hin.
      assert (Hlw : length bs = Z.to_nat cnt) by (rewrite Hlenbs; unfold S, Ops.Ops.fsize in *; lia).
      assert (Hlword : len_word bs = wbv w). { unfold len_word. rewrite Hlw, CS.wbv_Z. f_equal. rewrite <- ECW. lia. }
      apply (TAIL _ e (VL w) [FULe e CtrS.SIZE11] _ Hin (SHAPE _ _ [FULe e CtrS.SIZE11])).
      + rewrite De, Hlword. exact He.
      + rewrite Hlw. lia.
      + rewrite Hlword. reflexivity.
      + exact Hbytes.
      + constructor; [|constructor]. cbn [fact_holds]. rewrite De, D11, Heu, HS11. exact HA.
      + apply HOSx.
      + apply KEEPx. }
    assert (CASE_B : S < OFF + cnt ->
      In (addfact (ret_state st1 r (set_op CtrS.FD3_ID [CtrS.SIZE11] (set_op ReadC.RSTV_ID [off; nB] (s_ops st))) nB) (FULt CtrS.SIZE11 e)) sts ->
      realizes asegs (mkCfg ms' mo') K).
    { intros HB Hin.
      assert (HSl : S = Z.of_nat (length file)) by (unfold S, Ops.Ops.fsize in *; lia).
      assert (Hlw : Z.of_nat (length bs) = S - OFF) by (rewrite Hlenbs; lia).
      assert (Hlword : len_word bs = Z_to_bv 64 (S - OFF)) by (unfold len_word; rewrite Hlw; reflexivity).
      assert (HnB : den E nB = Z_to_bv 64 (S - OFF)).
      { subst nB. rewrite den_sv_alu. cbn [alu64 alu]. apply bv_eq. rewrite bv_sub_unsigned, HS11, OLB.Z_to_bv64_unsigned by lia.
        fold OFF. apply bv_wrap_small. unfold bv_modulus. lia. }
      apply (TAIL _ CtrS.SIZE11 nB [FULt CtrS.SIZE11 e] _ Hin (SHAPE _ _ [FULt CtrS.SIZE11 e])).
      + rewrite D11, Hlword, DS11. apply bv_eq. rewrite bv_add_unsigned, !OLB.Z_to_bv64_unsigned by lia.
        fold OFF. replace (OFF + (S - OFF)) with S by lia. symmetry. apply bv_wrap_small. unfold bv_modulus. lia.
      + lia.
      + rewrite DnB, Hlword. exact HnB.
      + exact Hbytes.
      + constructor; [|constructor]. cbn [fact_holds]. rewrite De, D11, Heu, HS11. exact HB.
      + apply HOSx.
      + apply KEEPx. }
    destruct (decide_ltu (s_facts st) CtrS.SIZE11 e) as [[|]|] eqn:Hd; injection Happ as <-.
    + apply CASE_B; [|left; reflexivity]. pose proof (decide_ltu_holds_g E st ms mo _ _ _ HS Hd) as X. cbn [negb] in X. rewrite HS11, Heu in X. exact X.
    + apply CASE_A; [|left; reflexivity]. pose proof (decide_ltu_holds_g E st ms mo _ _ _ HS Hd) as X. cbn [negb] in X. rewrite HS11, Heu in X. exact X.
    + destruct (Z_lt_le_dec S (OFF + cnt)) as [HB|HA].
      * apply CASE_B; [exact HB | right; left; reflexivity].
      * apply CASE_A; [lia | left; reflexivity].
Qed.
End Leaf.

From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.BothW Require Import BImg.
Module TwinB.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.PropExec OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.MState OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Cells OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Frame OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.ITree OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Nodes OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Decode.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA.AcctCore OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA.ExecF OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA.ITreeA OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA.NodesA.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.STree OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.AsanCtrl OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.AsanEmbed.
Import AProto.TwinB ABase.TwinB AMalloc_iface.TwinB.
Import AMalloc_iface2.TwinB.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common.RunDraw OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common.ShapeAlg.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.W64 OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Val OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.IMap OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Instr OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.State OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Step OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Plan OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.PlanSound.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Mem.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Heap.Op.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Ctr.Lib OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Ctr.Defs OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Ctr.DefsA.
Import Ledger.TwinB Op.TwinB Adeq.TwinB.

Import ListNotations.
Import W64 Val OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Mem.Mem FI St Step Plan PlanS CtrLib HeapOp.
Open Scope Z_scope.
Unset Lia Cache.

Import Actr.TwinB.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.W64Proofs OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.ValProofs OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.MemProofs OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.StepSoundBase.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Br.CtrFX.

Import ReadC.TwinB ReadPre.TwinB MemOps.TwinB ReadSound.TwinB.
Unset Nia Cache. Unset Nra Cache.
Import ValP MemP CtrFX ActrA ReadC.TwinB.ReadC.
Module AM := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Mem.
Module CS := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Glue.CtrSys.CtrSys.
Module OLB := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Glue.OblsLib.OL.

Definition in_stage (a : Z) : bool := (STAGE <=? a) && (a <? STAGE + 65536).

Definition mjoin (m m' : amem) : amem := fun x => if in_stage (bv_unsigned x) then m x else m' x.

Section MemSide.
Context {rc : runConstT}.
Variables (m m' : amem) (sp lo n : Z) (errv : word).
Notation W := [(sp - 2208, sp); (STAGE, STAGE + n); (ERRNO, ERRNO + 4)]%Z.
Hypothesis MU : munch W m m'.
Hypothesis WM : wmono bsegs m m'.
Hypothesis LO : ATOP + 4096 <= lo /\ lo <= sp - 4096 /\ sp < 2 ^ 47.
Hypothesis Hn : 0 < n <= 65536.
Hypothesis ERR0 : AS.rw_cells bsegs m ERRNO [C4 errv].
Hypothesis ERR1 : AS.rw_cells bsegs m' ERRNO [C4 errv].
Notation mj := (mjoin m m').

Lemma wa_u : forall a, 0 <= a < 2 ^ 64 -> bv_unsigned (AM.wa a) = a.
Proof. intros a Ha. unfold AM.wa. rewrite Z_to_bv_unsigned. apply bv_wrap_small. unfold bv_modulus. lia. Qed.

Lemma raw_out : forall a, 0 <= a < 2 ^ 64 ->
  ~ (sp - 2208 <= a < sp) -> ~ (STAGE <= a < STAGE + n) -> ~ (ERRNO <= a < ERRNO + 4) -> m' (AM.wa a) = m (AM.wa a).
Proof. intros a Ha N1 N2 N3. apply MU. rewrite (wa_u a Ha). cbn [outside]. tauto. Qed.

Lemma mj_out : forall a, 0 <= a < 2 ^ 64 -> ~ (sp - 2208 <= a < sp) -> ~ (ERRNO <= a < ERRNO + 4) -> mj (AM.wa a) = m (AM.wa a).
Proof.
  intros a Ha N1 N3. unfold mjoin. rewrite (wa_u a Ha). destruct (in_stage a) eqn:IS; [reflexivity|].
  apply raw_out; [exact Ha | exact N1 | | exact N3]. unfold in_stage in IS. lia.
Qed.
Lemma mj_stage : forall a, 0 <= a < 2 ^ 64 -> STAGE <= a < STAGE + 65536 -> mj (AM.wa a) = m (AM.wa a).
Proof. intros a Ha S. unfold mjoin. rewrite (wa_u a Ha). unfold in_stage. replace ((STAGE <=? a) && (a <? STAGE + 65536)) with true by lia. reflexivity. Qed.
Lemma mj_final : forall a, 0 <= a < 2 ^ 64 -> ~ (STAGE <= a < STAGE + 65536) -> mj (AM.wa a) = m' (AM.wa a).
Proof. intros a Ha S. unfold mjoin. rewrite (wa_u a Ha). unfold in_stage. replace ((STAGE <=? a) && (a <? STAGE + 65536)) with false by lia. reflexivity. Qed.

Lemma wbm_all : forall a, wb bsegs m a = true -> wb bsegs m' a = true.
Proof. intros a H. apply (GlueA.TwinB.wb_wviewA bsegs). apply (GlueA.TwinB.wb_wviewA bsegs) in H. exact (WM _ H). Qed.

Lemma errno_view : forall a, ERRNO <= a < ERRNO + 4 -> rb bsegs m' a = rb bsegs m a.
Proof.
  intros a Ha. destruct ERR0 as [[_ (_ & _ & B0)] _]. destruct ERR1 as [[_ (_ & _ & B1)] _].
  rewrite !(GlueA.TwinB.rb_mrdA bsegs). replace a with (ERRNO + Z.of_nat (Z.to_nat (a - ERRNO))) by lia.
  rewrite (B0 (Z.to_nat (a - ERRNO))), (B1 (Z.to_nat (a - ERRNO))); [reflexivity | |]; cbn; lia.
Qed.

Lemma wview_ext : forall (m1 m2 : amem) x, m2 x = m1 x -> wview bsegs m2 x = wview bsegs m1 x.
Proof. intros m1 m2 x H. unfold wview. rewrite H. reflexivity. Qed.
Lemma mrd_ext : forall (m1 m2 : amem) x, m2 x = m1 x -> AM.mrd bsegs m2 x = AM.mrd bsegs m1 x.
Proof. intros m1 m2 x H. unfold AM.mrd. rewrite H. reflexivity. Qed.
Lemma rb_ext : forall (m1 m2 : amem) a, m2 (Z_to_bv 64 a) = m1 (Z_to_bv 64 a) -> rb bsegs m2 a = rb bsegs m1 a.
Proof. intros m1 m2 a H. unfold rb. rewrite H. reflexivity. Qed.
Lemma wb_ext : forall (m1 m2 : amem) a, m2 (Z_to_bv 64 a) = m1 (Z_to_bv 64 a) -> wb bsegs m2 a = wb bsegs m1 a.
Proof. intros m1 m2 a H. unfold wb. rewrite (wview_ext m1 m2 _ H). reflexivity. Qed.

Lemma mj_cases : forall x, mj x = m x \/ mj x = m' x.
Proof. intros x. unfold mjoin. destruct (in_stage (bv_unsigned x)); auto. Qed.

Lemma stage_wb_any : forall (mm : amem) a, STAGE <= a < STAGE + 65536 -> wb bsegs mm a = true.
Proof.
  intros mm a Ha.
  destruct (MemP.abs_writable_sound bsegs STAGE 65536 ltac:(unfold STAGE; lia) ltac:(lia) ltac:(vm_compute; reflexivity)) as [_ WB].
  replace a with (STAGE + (a - STAGE)) by lia. apply (proj1 (WB (a - STAGE) ltac:(lia))).
Qed.

Lemma mj_wmono : wmono bsegs m mj.
Proof.
  intros x H. destruct (in_stage (bv_unsigned x)) eqn:IS.
  - rewrite (wview_ext m mj x); [exact H|]. unfold mjoin. rewrite IS. reflexivity.
  - rewrite (wview_ext m' mj x); [exact (WM x H)|]. unfold mjoin. rewrite IS. reflexivity.
Qed.
Lemma mj_munch : munch [(sp - 2208, sp); (ERRNO, ERRNO + 4)]%Z m mj.
Proof.
  intros x OUT. cbn [outside] in OUT. pose proof (bv_unsigned_in_range _ x) as RX. unfold bv_modulus in RX.
  assert (EX : AM.wa (bv_unsigned x) = x) by (unfold AM.wa; apply Z_to_bv_bv_unsigned).
  rewrite <- EX. apply (mj_out (bv_unsigned x)); [lia | tauto | tauto].
Qed.
Lemma mj_mem_inv : AM.mem_inv bsegs m -> AM.mem_inv bsegs m' -> AM.mem_inv bsegs mj.
Proof. intros I1 I2 a b H. destruct (mj_cases a) as [Q|Q]; rewrite Q in H; [exact (I1 a b H)| exact (I2 a b H)]. Qed.
Lemma mj_stk : stk bsegs m' lo sp -> stk bsegs mj lo sp.
Proof.
  intros (H1 & H2 & H). split; [exact H1|]. split; [exact H2|]. intros a Ha.
  assert (E : mj (AM.wa a) = m' (AM.wa a)) by (apply mj_final; [lia| unfold STAGE; pose proof atop_range; lia]).
  rewrite (wview_ext m' mj _ E), (mrd_ext m' mj _ E). exact (H a Ha).
Qed.
End MemSide.

Definition rstage_holds_v (file : list byte) (args : list word) (m : word -> option byte) : Prop :=
  match args with
  | [off; n] => bv_unsigned off + bv_unsigned n <= Z.of_nat (length file) /\ bv_unsigned n <= 65536 /\
               forall i, 0 <= i < bv_unsigned n -> rb bsegs m (STAGE + i) = Some (nth (Z.to_nat (bv_unsigned off + i)) file (Z_to_bv 8 0))
  | _ => False
  end.

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

Hypothesis ACI_errno : exists iv0, In iv0 (aci AI) /\ fst iv0 <= ERRNO /\ ERRNO + 4 <= snd iv0.
Hypothesis OPS_fp_errno : forall id args a, id <> HEAP_ID -> Exists (fun iv => fst iv <= a < snd iv) (op_fp OPS id args) ->
  ~ (ERRNO <= a < ERRNO + 4).

Lemma aci_low' : forall a, in_ranges (aci AI) a -> a < AIMG_HI.
Proof. intros a (iv0 & Hi & RR). pose proof (AI_aci_img AI iv0 Hi). lia. Qed.

Lemma phaseA : forall st E ms mo r hargs wnl st1 (L : alayout) (RNG : footprint) (sta : astate) (LBa : list ablock) (aw : word)
    (m' : amem) (R' : bvmap 5 word) (mo_j : Model) (errv : word) (n : Z) (v : sv) (nx' : int),
  st_ok bsegs OPS E st ms mo -> call_pre st = Some r -> forget_stack_below_sp_g st = Some st1 ->
  CtrPre.TwinB.acallG AI ACCT UNIV Cw E st ms mo r hargs wnl L RNG sta LBa aw -> AHEAP AI L RNG sta LBa (ms_mem ms) ->
  let R := ms_regs ms in let sp := bv_unsigned (AP.getr R 2) in
  ATOP + 4096 <= CtrPre.TwinB.sp_lo E st -> CtrPre.TwinB.sp_lo E st <= sp - 4096 -> sp < 2 ^ 47 -> 0 < n <= 65536 ->
  munch [(sp - 2208, sp); (STAGE, STAGE + n); (ERRNO, ERRNO + 4)]%Z (ms_mem ms) m' -> wmono bsegs (ms_mem ms) m' ->
  AM.mem_inv bsegs (ms_mem ms) -> AM.mem_inv bsegs m' -> stk bsegs m' (CtrPre.TwinB.sp_lo E st) sp ->
  AS.rw_cells bsegs (ms_mem ms) ERRNO [C4 errv] -> AS.rw_cells bsegs m' ERRNO [C4 errv] ->
  (forall rg, In rg CtrFrame.TwinB.kept_regsA -> AP.getr R' rg = AP.getr R rg) ->
  let Fv := CtrFree.TwinB.cfvF R' in let Gv := fun (_ _ : Z) => Z_to_bv 8 0 in
  den (CtrFrame.TwinB.E' E st Fv Gv) v = AP.getr R' 10%bv ->
  OTHER mo mo_j -> op_minv OPS mo_j -> ACCT aw L RNG sta LBa mo_j ->
  st_ok bsegs OPS (CtrFrame.TwinB.E' E st Fv Gv)
    (SS r (rf_set (s_rf (clobber st1)) X10 v) (s_ff st) (s_resv st) (s_regs st1) (s_facts st) (s_ops st) (s_priv st) nx')
    (CtrFrame.TwinB.ms' ms r R' (mjoin (ms_mem ms) m')) mo_j.
Proof.
  intros st E ms mo r hargs wnl st1 L RNG sta LBa aw m' R' mo_j errv n v nx' HS CP FS CF AH R sp BOT LO SPT Hn MU WM MI MI' STK' ERR0 ERR1 KEPT Fv Gv DV OTH MIj ACj.
  pose proof atop_range as ATR.
  assert (LO3 : ATOP + 4096 <= CtrPre.TwinB.sp_lo E st /\ CtrPre.TwinB.sp_lo E st <= sp - 4096 /\ sp < 2 ^ 47) by lia.
  set (m := ms_mem ms) in *.
  assert (IUOUT : forall LB0, aw_real AI ACCT UNIV aw LB0 m mo L RNG sta LBa -> forall a, 0 <= a < 2 ^ 64 -> in_user LB0 a ->
            mjoin m m' (AM.wa a) = m (AM.wa a)).
  { intros LB0 AR0 a Ha IU. pose proof (UnreggGeo.TwinB.user_out AI ACCT UNIV AI_fake aw LB0 m mo L RNG sta LBa a AR0 IU) as G.
    apply (mj_out m m' sp (CtrPre.TwinB.sp_lo E st) n MU LO3 Hn a Ha); unfold ERRNO, AIMG_HI, KLS in *; lia. }
  apply (CtrNoDelta.TwinB.nodelta_st_ok AI IMGX IMGX_aci ACCT UNIV Cw OPS AI_fake OPS_holds1 OPS_fp1 OPS_cov1 OPS_frame_other OPS_fp_other OTHER OPS_mo_other
           OPS_cov0_img E st ms mo r hargs wnl L RNG sta LBa aw st1 Fv Gv R' (mjoin m m') mo_j RNG sta _ _ HS CP FS CF).
  - exact KEPT.
  - intros x i Hx. exact (CtrFree.TwinB.cfvF_clob R' x i Hx).
  - exact DV.
  - exact (mj_mem_inv m m' MI MI').
  - exact (mj_stk m m' sp (CtrPre.TwinB.sp_lo E st) LO3 STK').
  -
    intros LB0 AR0 a Ha STB. destruct STB as [S1|[S2|S3]].
    + apply (FrameV.TwinB.frame_v_of_raw bsegs). apply (mj_out m m' sp (CtrPre.TwinB.sp_lo E st) n MU LO3 Hn a Ha); unfold ERRNO, sp, R in *; lia.
    + destruct (Z_lt_le_dec a ERRNO) as [Q|Q]; [| destruct (Z_lt_le_dec a (ERRNO + 4)) as [Q'|Q']].
      * apply (FrameV.TwinB.frame_v_of_raw bsegs). pose proof (aci_low' a S2) as AL. apply (mj_out m m' sp (CtrPre.TwinB.sp_lo E st) n MU LO3 Hn a Ha); unfold ERRNO, AIMG_HI in *; lia.
      * assert (EJ : mjoin m m' (Z_to_bv 64 a) = m' (Z_to_bv 64 a)) by (apply (mj_final m m' a Ha); unfold ERRNO, STAGE in *; lia).
        split; [rewrite (rb_ext m' (mjoin m m') a EJ); exact (errno_view m m' errv ERR0 ERR1 a ltac:(lia))
               | intros Wb; rewrite (wb_ext m' (mjoin m m') a EJ); exact (wbm_all m m' WM a Wb)].
      * apply (FrameV.TwinB.frame_v_of_raw bsegs). pose proof (aci_low' a S2) as AL. apply (mj_out m m' sp (CtrPre.TwinB.sp_lo E st) n MU LO3 Hn a Ha); unfold ERRNO, AIMG_HI in *; lia.
    + apply (FrameV.TwinB.frame_v_of_raw bsegs). exact (IUOUT LB0 AR0 a Ha S3).
  -   exact IUOUT.
  -
    intros o a Ho NI Ha FP. unfold not_id in NI. apply Uint63.eqb_false_spec in NI.
    pose proof (OPS_fp_errno _ _ a NI FP) as NE. destruct (OPS_fp_other _ _ a NI FP) as [INA|[(a' & INA & ->)|(a' & STK & ->)]].
    + pose proof (aci_low' a INA) as AL.
      apply (mj_out m m' sp (CtrPre.TwinB.sp_lo E st) n MU LO3 Hn a); [unfold two64 in Ha; lia| unfold AIMG_HI in *; lia | exact NE].
    + pose proof (aci_low' a' INA) as AL. destruct INA as (iv0 & I0 & I1). pose proof (AI_aci_lo AI iv0 I0) as A0.
      pose proof (CtrPre.TwinB.shad_img_band a' ltac:(lia)) as BND.
      apply (mj_out m m' sp (CtrPre.TwinB.sp_lo E st) n MU LO3 Hn (shad a')); [unfold two64 in Ha; lia| lia | exact NE].
    +
      assert (ZN : 0x7fffa000 <= shad a' < 0x10007fff8000) by (unfold shad, ASHOFF; rewrite Z.shiftr_div_pow2 by lia; change (2 ^ 3) with 8; clear - STK ATR; Z.div_mod_to_equations; lia).
      apply (mj_out m m' sp (CtrPre.TwinB.sp_lo E st) n MU LO3 Hn (shad a')); [unfold two64 in Ha; lia| lia | exact NE].
  -   intros a Ha _ Wb. apply (GlueA.TwinB.wb_wviewA bsegs). apply (GlueA.TwinB.wb_wviewA bsegs) in Wb. exact (mj_wmono m m' WM _ Wb).
  -
    intros a Ha SC _. apply (FrameV.TwinB.frame_v_of_raw bsegs).
    assert (ZN : 0x7fffa000 <= a < 0x10007fff8000).
    { destruct SC as [(a' & RR & ->)|(vv & Hv & RR)].
      - unfold shad, ASHOFF. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8. clear - RR ATR. Z.div_mod_to_equations. lia.
      - destruct (Op.TwinB.SHLIT_cases vv Hv) as [->|(_ & P1 & P2 & P3)]; [cbn [fst snd] in RR|]; lia. }
    apply (mj_out m m' sp (CtrPre.TwinB.sp_lo E st) n MU LO3 Hn a Ha); unfold ERRNO, STAGE, sp, R in *; lia.
  -
    apply (AI_frame AI L RNG sta LBa m (mjoin m m') _ AH (mj_munch m m' sp (CtrPre.TwinB.sp_lo E st) n MU LO3 Hn) (mj_wmono m m' WM)).
    repeat (apply Forall_cons; [cbn [fst snd]|]); [| | apply Forall_nil].
    + left. left. fold sp. lia.
    + left. right. left. destruct ACI_errno as (iv0 & I0 & I1 & I2). exists iv0. split; [exact I0| lia].
  - exact ACj.
  -
    intros b x Hb FK Hx. pose proof (Op.TwinB.blk_band AI AI_fake L RNG sta LBa m b x AH Hb) as BB.
    destruct (AI_fake L RNG sta LBa m b AH Hb FK) as (_ & _ & _ & _ & SZ64 & _). specialize (BB ltac:(lia)).
    apply (mj_out m m' sp (CtrPre.TwinB.sp_lo E st) n MU LO3 Hn x); unfold ERRNO, AIMG_HI, KLS in *; lia.
  -
    apply (Op.TwinB.twins_pres_band AI L RNG sta LBa m (mjoin m m') AH). intros a Ha.
    assert (SA : shad ATOP = ASHOFF + ATOP / 8) by (unfold shad; rewrite Z.shiftr_div_pow2 by lia; reflexivity).
    rewrite SA in Ha. unfold ASHOFF in Ha.
    apply (mj_out m m' sp (CtrPre.TwinB.sp_lo E st) n MU LO3 Hn a); unfold ERRNO in *; clear - Ha ATR LO3; Z.div_mod_to_equations; lia.
  - exact OTH.
  - exact MIj.
  - exact (fun P => P).
Qed.

Variables (p1 file : list byte).
Hypothesis OPS_holds_fd3' : forall args m mo, Ops.Ops.fd3_holds p1 file args mo -> op_holds OPS CtrS.FD3_ID args m mo.
Hypothesis OPS_holds_rstage' : forall args m mo, rstage_holds_v file args m -> op_holds OPS ReadC.TwinB.ReadC.RSTV_ID args m mo.
Hypothesis OPS_fp_fd3 : forall args, op_fp OPS CtrS.FD3_ID args = [].
Hypothesis OPS_fp_rstage : forall args args', op_fp OPS ReadC.TwinB.ReadC.RSTV_ID args = op_fp OPS ReadC.TwinB.ReadC.RSTV_ID args'.
Hypothesis OPS_fp_nostage : forall id args a, id <> ReadC.TwinB.ReadC.RSTV_ID -> Exists (fun iv => fst iv <= a < snd iv) (op_fp OPS id args) ->
  ~ (STAGE <= a < STAGE + 65536).
Hypothesis OPS_fds_other : forall id args m mo f, id <> HEAP_ID -> CtrS.is_fd_op (OpI id []) = false ->
  op_holds OPS id args m mo -> op_holds OPS id args m (with_fds f mo).
Hypothesis OPS_cov1_heap : forall id args z, op_cov1 OPS id args z -> id = HEAP_ID.
Hypothesis minv_fds : forall mo f, op_minv OPS mo -> op_minv OPS (with_fds f mo).
Hypothesis ACCT_fds : forall aw L RNG st LBa mo f, ACCT aw L RNG st LBa mo -> ACCT aw L RNG st LBa (with_fds f mo).
Hypothesis ACI_stage : exists iv0, In iv0 (aci AI) /\ fst iv0 <= STAGE /\ STAGE + 65536 <= snd iv0.

Lemma count_one_args : forall id os o args, In o os -> op_id o = id -> CtrA.count_op id os = 1%nat -> find_op id os = Some args -> op_args o = args.
Proof.
  intros id os. induction os as [|o0 os IH]; intros o args Hin Hid Hc Hf; [destruct Hin|].
  cbn [CtrA.count_op find_op] in Hc, Hf. destruct (PrimInt63.eqb (op_id o0) id) eqn:Q.
  - injection Hf as <-. destruct Hin as [->|Hin]; [reflexivity|]. exfalso. injection Hc as Hc.
    clear IH Q. induction os as [|o1 os IH2]; [destruct Hin|]. cbn [CtrA.count_op] in Hc. destruct (PrimInt63.eqb (op_id o1) id) eqn:Q1; [discriminate Hc|].
    destruct Hin as [->|Hin]; [rewrite Hid, Uint63.eqb_refl in Q1; discriminate Q1| exact (IH2 Hin Hc)].
  - destruct Hin as [->|Hin]; [rewrite Hid, Uint63.eqb_refl in Q; discriminate Q|]. exact (IH o args Hin Hid Hc Hf).
Qed.

Lemma phaseB : forall st E ms mo r hargs wnl st1 (L : alayout) (RNG : footprint) (sta : astate) (LBa : list ablock) (aw : word)
    (m' : amem) (R' : bvmap 5 word) (mo_j mo' : Model) (n : Z) (v : sv) (nx' : int) (off newoff nsv : sv) (fs' : list fact) (os' : list opinst),
  st_ok bsegs OPS E st ms mo -> call_pre st = Some r -> forget_stack_below_sp_g st = Some st1 ->
  CtrPre.TwinB.acallG AI ACCT UNIV Cw E st ms mo r hargs wnl L RNG sta LBa aw -> AHEAP AI L RNG sta LBa (ms_mem ms) ->
  let R := ms_regs ms in let sp := bv_unsigned (AP.getr R 2) in
  ATOP + 4096 <= CtrPre.TwinB.sp_lo E st -> CtrPre.TwinB.sp_lo E st <= sp - 4096 -> sp < 2 ^ 47 -> 0 < n <= 65536 ->
  munch [(sp - 2208, sp); (STAGE, STAGE + n); (ERRNO, ERRNO + 4)]%Z (ms_mem ms) m' -> wmono bsegs (ms_mem ms) m' ->
  let Fv := CtrFree.TwinB.cfvF R' in let Gv := fun (_ _ : Z) => Z_to_bv 8 0 in
  let E' := CtrFrame.TwinB.E' E st Fv Gv in
  st_ok bsegs OPS E'
    (SS r (rf_set (s_rf (clobber st1)) X10 v) (s_ff st) (s_resv st) (s_regs st1) (s_facts st) (s_ops st) (s_priv st) nx')
    (CtrFrame.TwinB.ms' ms r R' (mjoin (ms_mem ms) m')) mo_j ->
  CtrS.priv_has st 6283984%uint63 CtrS.STAGE_LEN = true ->
  (exists r1 r2, In (OpI ReadC.TwinB.ReadC.RSTV_ID [r1; r2]) (s_ops st)) ->
  mo' = with_fds (m_fds mo') mo_j -> ACCT aw L RNG sta LBa mo_j -> op_minv OPS mo_j ->
  Ops.Ops.fd3_holds p1 file [den E' newoff] mo' ->
  rstage_holds_v file [den E' off; den E' nsv] m' ->
  Forall (fact_holds E') fs' ->
  (forall o, In o os' -> o = OpI CtrS.FD3_ID [newoff] \/ o = OpI ReadC.TwinB.ReadC.RSTV_ID [off; nsv] \/
                         (In o (s_ops st) /\ CtrS.is_fd_op o = false /\ PrimInt63.eqb (op_id o) ReadC.TwinB.ReadC.RSTV_ID = false)) ->
  (forall o, In o (s_ops st) -> op_id o = HEAP_ID -> In o os') ->
  st_ok bsegs OPS E'
    (SS r (rf_set (s_rf (clobber st1)) X10 v) (s_ff st) (s_resv st) (s_regs st1) (fs' ++ s_facts st) os' (s_priv st) nx')
    (CtrFrame.TwinB.ms' ms r R' m') mo'.
Proof.
  intros st E ms mo r hargs wnl st1 L RNG sta LBa aw m' R' mo_j mo' n v nx' off newoff nsv fs' os' HS CP FS CF AH R sp BOT LO SPT Hn MU WM Fv Gv E'
         HSj PRIV HRS EMO ACj MIj HFD3 HRST HFS HOS HKEEP.
  pose proof atop_range as ATR.
  assert (LO3 : ATOP + 4096 <= CtrPre.TwinB.sp_lo E st /\ CtrPre.TwinB.sp_lo E st <= sp - 4096 /\ sp < 2 ^ 47) by lia.
  set (m := ms_mem ms) in *.
  change (CtrFrame.TwinB.ms' ms r R' m') with (ms_with_mem (CtrFrame.TwinB.ms' ms r R' (mjoin m m')) m').
  change (SS r (rf_set (s_rf (clobber st1)) X10 v) (s_ff st) (s_resv st) (s_regs st1) (fs' ++ s_facts st) os' (s_priv st) nx')
    with (let T := SS r (rf_set (s_rf (clobber st1)) X10 v) (s_ff st) (s_resv st) (s_regs st1) (s_facts st) (s_ops st) (s_priv st) nx' in
          SS (s_pc T) (s_rf T) (s_ff T) (s_resv T) (s_regs T) (fs' ++ s_facts T) os' (s_priv T) nx').
  cbv zeta.
  apply (st_ok_memops bsegs OPS E' _ _ mo_j mo' fs' os' nx' m' HSj HFS).
  - rewrite EMO. apply minv_fds. exact MIj.
  -   unfold ops_hold. apply Forall_forall. intros o Ho.
    destruct (HOS o Ho) as [-> | [-> | (Hin & Hnf & Hnr)]]; cbn [op_id op_args map].
    + apply OPS_holds_fd3'. exact HFD3.
    + apply OPS_holds_rstage'. exact HRST.
    + destruct (PrimInt63.eqb (op_id o) HEAP_ID) eqn:QH.
      *
        apply Uint63.eqb_correct in QH.
        destruct CF as (LB & ks & offs & rss & ksp & nn & md & A & nw & rest & SPR & Hksp & SPE & K16 & LOSP & FLOOR & Hf & Hc & Eh & Tnw & Nn & Ln & N255
                        & NW & AN & AJ & TS & WF & HC & AWden & (W & WOF & ARW & TI)).
        destruct (HeapCtr.TwinB.call_pre_inv st r CP) as (FOK & _).
        pose proof (count_one_args HEAP_ID (s_ops st) o hargs Hin QH Hc Hf) as EA. rewrite QH, EA.
        assert (AR : aw_real AI ACCT UNIV aw LB m mo L RNG sta LBa) by (exists W; split; [exact WOF| exact ARW]).
        assert (SBU : forall a, 0 <= a < 2 ^ 64 -> in_user LB a -> m' (AM.wa a) = m (AM.wa a)).
        { intros a Ha IU. pose proof (UnreggGeo.TwinB.user_out AI ACCT UNIV AI_fake aw LB m mo L RNG sta LBa a AR IU) as G.
          apply (raw_out m m' sp (CtrPre.TwinB.sp_lo E st) n MU LO3 Hn a Ha); unfold STAGE, ERRNO, AIMG_HI, KLS in *; lia. }

        set (W' := mkWit (w_L W) RNG sta (w_LBa W) (w_T W) (w_FA W) m' (w_zc W)).
        assert (AR' : aw_realW AI ACCT UNIV aw LB m' mo' W').
        { destruct WOF as (E1 & E2 & E3 & E4).
          apply (aw_real_nodelta AI ACCT UNIV AI_fake aw aw LB m mo W RNG sta m' mo' ARW).
          - rewrite E1, E4. apply (AI_frame AI L RNG sta LBa m m' _ AH MU WM).
            repeat (apply Forall_cons; [cbn [fst snd]|]); [| | | apply Forall_nil].
            + left. left. fold sp. lia.
            + left. right. left. destruct ACI_stage as (iv0 & I0 & I1 & I2). exists iv0. split; [exact I0| lia].
            + left. right. left. destruct ACI_errno as (iv0 & I0 & I1 & I2). exists iv0. split; [exact I0| lia].
          - rewrite E1, E4. rewrite EMO. apply ACCT_fds. exact ACj.
          -
            intros b x Hb FK Hx. rewrite E4 in Hb. pose proof (Op.TwinB.blk_band AI AI_fake L RNG sta LBa m b x AH Hb Hx) as BB.
            apply (raw_out m m' sp (CtrPre.TwinB.sp_lo E st) n MU LO3 Hn x); unfold STAGE, ERRNO, AIMG_HI, KLS in *; lia.
          -
            rewrite E4. apply (Op.TwinB.twins_pres_band AI L RNG sta LBa m m' AH). intros a Ha.
            assert (SA : shad ATOP = ASHOFF + ATOP / 8) by (unfold shad; rewrite Z.shiftr_div_pow2 by lia; reflexivity).
            rewrite SA in Ha. unfold ASHOFF in Ha.
            apply (raw_out m m' sp (CtrPre.TwinB.sp_lo E st) n MU LO3 Hn a); unfold STAGE, ERRNO in *; clear - Ha ATR LO3 Hn; Z.div_mod_to_equations; lia. }
        assert (TI' : ties W' (wins_of E nn rest)) by (apply (ties_ext W W'); [reflexivity| intros b; reflexivity| reflexivity| exact TI| intros b _ V; exact V| intros P; unfold W'; cbn [w_st]; rewrite <- (proj1 (proj2 (proj2 WOF))); exact P]).
        assert (DECN : decode (map (den E') hargs) = Some (w2Z md, den E A, wins_of E nn rest, map (den E) (skipn (3 * nn) rest)))
          by exact (CtrFrame.TwinB.DEC' E st FOK Fv Gv nn rest hargs md A nw Hf Eh Tnw Nn Ln).
        rewrite OPS_holds1. exists (w2Z md), aw, (wins_of E nn rest), (map (den E) (skipn (3 * nn) rest)), LB, W'.
        split; [rewrite AWden; exact DECN|]. split; [exact (proj1 AR')|]. split; [exact WF|]. split; [| exact TI'].
        apply (cw_frame Cw _ _ _ _ m m' HC). intros a Ha U _. symmetry. unfold AM.wa in SBU.
        apply (SBU a ltac:(unfold two64 in Ha; lia)). exact U.
      *
        apply Uint63.eqb_false_spec in QH.
        pose proof (proj1 (Forall_forall _ _) (so_ops _ _ _ _ _ _ HSj) o Hin) as HO. cbn [s_ops] in HO.
        rewrite EMO. apply OPS_fds_other; [exact QH | destruct o as [oi oa]; cbn [op_id] in *; unfold CtrS.is_fd_op in *; cbn [op_id] in *; exact Hnf |].
        apply (OPS_frame_other _ _ (mjoin m m') m' mo_j QH HO).
        -- intros a Ha FP. apply Uint63.eqb_false_spec in Hnr. pose proof (OPS_fp_nostage _ _ a Hnr FP) as NS.
           apply (mj_final m m' a ltac:(unfold two64 in Ha; lia) NS).
        -- intros a Ha _ Wb. destruct (in_stage a) eqn:IS.
           ++ apply stage_wb_any. unfold in_stage in IS. lia.
           ++ rewrite <- (wb_ext m' (mjoin m m') a); [exact Wb|]. apply (mj_final m m' a ltac:(unfold two64 in Ha; lia)). unfold in_stage in IS. lia.
  -   unfold ops_apart. apply Forall_forall. intros o Ho a Ha.
    destruct (HOS o Ho) as [-> | [-> | (Hin & _ & _)]].
    + exfalso. cbn [op_id op_args map] in Ha. rewrite OPS_fp_fd3 in Ha. inversion Ha.
    + destruct HRS as (r1 & r2 & HinR).
      pose proof (proj1 (Forall_forall _ _) (so_apart _ _ _ _ _ _ HSj) _ HinR a) as X. cbn [op_id op_args map s_regs s_priv] in X, Ha |- *.
      rewrite (OPS_fp_rstage _ (map (den E') [r1; r2])) in Ha. exact (X Ha).
    + exact (proj1 (Forall_forall _ _) (so_apart _ _ _ _ _ _ HSj) o Hin a Ha).
  -
    intros a Ha. apply (OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Glue.Nodes.FXN.cov_keep OPS E' (s_ops st)); [| exact (so_cover _ _ _ _ _ _ HSj a Ha)].
    intros o Ho [z Hz]. exact (HKEEP o Ho (OPS_cov1_heap _ _ _ Hz)).
  -
    intros a Ha Hout. cbn [ms_mem CtrFrame.TwinB.ms']. destruct (in_stage a) eqn:IS.
    + exfalso. unfold in_stage in IS. assert (SA : STAGE <= a < STAGE + 65536) by lia.
      destruct (MemP.abs_writable_sound bsegs STAGE 65536 ltac:(unfold STAGE; lia) ltac:(lia) ltac:(vm_compute; reflexivity)) as [_ WB].
      destruct (WB (a - STAGE) ltac:(lia)) as [_ (seg & Hseg & _)]. replace (STAGE + (a - STAGE)) with a in Hseg by lia.
      destruct Hout as [Hn0 | Hnp]; [congruence|]. apply Hnp.
      unfold CtrS.priv_has in PRIV. apply existsb_exists in PRIV as ([plo phi] & Hinp & Heq).
      apply andb_prop in Heq as [E1 E2]. cbn [fst snd] in E1, E2. apply Uint63.eqb_correct in E1. apply Uint63.eqb_correct in E2. subst plo phi.
      unfold in_priv. apply Exists_exists. exists (6283984%uint63, PrimInt63.add 6283984%uint63 CtrS.STAGE_LEN). split; [exact Hinp|]. cbn [fst snd].
      change (to_Z 6283984%uint63) with STAGE. change (to_Z (PrimInt63.add 6283984%uint63 CtrS.STAGE_LEN)) with (STAGE + 65536). lia.
    + symmetry. apply (mj_final m m' a ltac:(unfold two64 in Ha; lia)). unfold in_stage in IS. lia.
  -
    intros a b Hb Hnone seg Hseg. change (mjoin m m' a = None) in Hnone.
    pose proof (bv_unsigned_in_range _ a) as RA. unfold bv_modulus in RA.
    destruct (in_stage (bv_unsigned a)) eqn:IS.
    + unfold in_stage in IS.
      destruct (MemP.abs_writable_sound bsegs STAGE 65536 ltac:(unfold STAGE; lia) ltac:(lia) ltac:(vm_compute; reflexivity)) as [_ WB].
      destruct (WB (bv_unsigned a - STAGE) ltac:(lia)) as [_ (seg' & Hseg' & WS)].
      replace (STAGE + (bv_unsigned a - STAGE)) with (bv_unsigned a) in Hseg' by lia. rewrite Hseg in Hseg'. injection Hseg' as <-. exact WS.
    + exfalso. unfold mjoin in Hnone. rewrite IS in Hnone. congruence.
Qed.

Hypothesis MP_fds : forall mo f, MP mo -> MP (with_fds f mo).
Hypothesis PB_size : forall b, PB b -> b 11%uint63 = Z_to_le_bytes 8 (Ops.Ops.fsize file).

Lemma known_leu_sound_g : forall E st ms model a b, st_ok bsegs OPS E st ms model ->
  known_leu (s_facts st) a b = true -> bv_unsigned (den E a) <= bv_unsigned (den E b).
Proof.
  intros E st ms model a b HS H. unfold known_leu, dec_false in H.
  destruct (decide_ltu (s_facts st) b a) as [[|]|] eqn:Hd; try discriminate H.
  pose proof (ValP.decide_ltu_sound E (s_facts st) (so_facts _ _ _ _ _ _ HS) b a false Hd) as X.
  apply (proj1 (ValP.ltu_iff _ _ false)) in X. exact X.
Qed.
Lemma decide_ltu_holds_g : forall E st ms model a b r0, st_ok bsegs OPS E st ms model ->
  decide_ltu (s_facts st) a b = Some r0 -> (if r0 then bv_unsigned (den E a) < bv_unsigned (den E b) else bv_unsigned (den E b) <= bv_unsigned (den E a)).
Proof.
  intros E st ms model a b r0 HS Hd.
  pose proof (ValP.decide_ltu_sound E (s_facts st) (so_facts _ _ _ _ _ _ HS) a b r0 Hd) as X.
  apply (proj1 (ValP.ltu_iff _ _ r0)) in X. exact X.
Qed.
Lemma ops_args_below : forall n st o a, st_vars_below n st = true -> In o (s_ops st) -> In a (op_args o) -> sv_vars_below n a = true.
Proof.
  intros n st o a H Ho Ha. unfold st_vars_below in H. apply andb_prop in H as [_ H].
  exact (proj1 (forallb_forall _ _) (proj1 (forallb_forall _ _) H o Ho) a Ha).
Qed.

Lemma aread_leaf_ok : ReadSound.TwinB.aread_leaf AI ACCT UNIV Cw OPS p1 file OTHER MP PB.
Proof.
  unfold ReadSound.TwinB.aread_leaf.
  intros st sts K E ms mo r hargs wnl st1 off cnt L RNG sta LBa aw junk errv HS HMP HPB HK Happ PRE RPRE ECNT WR CP FS CF AH BOT LO SPT TP MI STG ERR ZSH
         FDS OFFLE ms' mo' HQ FDS' MPj MIj OTj ACj.
  set (R := ms_regs ms) in *. set (bs := file_read file (den E off) (Z_to_bv 64 cnt)) in *. set (mo_j := with_fds (m_fds mo) mo') in *.
  destruct HQ as (_ & t0 & t1 & t2 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & m' & EMS & MU & WM & MINV' & STK' & STGP & ERRP & LENB).
  pose proof atop_range as ATR.
  assert (ETP : bv_unsigned (AP.getr R 4) + -164 = ERRNO) by (rewrite TP; vm_compute; reflexivity).
  rewrite ETP in MU, ERRP. rewrite Z2Nat.id in MU by lia.
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
  assert (F1 : s_ff st1 = s_ff st /\ s_resv st1 = s_resv st /\ s_facts st1 = s_facts st
               /\ s_ops st1 = s_ops st /\ s_priv st1 = s_priv st /\ s_next st1 = s_next st).
  { destruct (CtrFrame.TwinB.st1_fields st st1 FS) as (_ & _ & Q1 & Q2 & Q3 & Q4 & Q5 & Q6). repeat split; assumption. }
  destruct F1 as (FF1 & RV1 & FS1 & OP1 & PV1 & NX1).
  idtac "LEAF-2".
  destruct (aread_pre_inv st off RPRE) as (_ & _ & PRIV & (r1 & r2 & FRS) & CNTR & ONEFD & _ & F3).
  pose proof (HeapCtr.TwinB.fresh_ok_inv st FOK) as (SVB & _).
  assert (VBoff : sv_vars_below (s_next st) off = true).
  { apply (ops_args_below (s_next st) st (OpI CtrS.FD3_ID [off]) off SVB (UnreggPre.TwinB.find_op_In _ _ _ F3)). left. reflexivity. }
  assert (DOFF : den E' off = den E off) by (apply CtrFrame.TwinB.den_E'; exact VBoff).
  set (OFF := bv_unsigned (den E off)) in *. set (S := Ops.Ops.fsize file) in *.
  pose proof (u64_range (den E off)) as Hur. fold OFF in Hur.
  assert (HSr : 0 <= S <= Z.of_nat (length file) /\ S <= 2 ^ 62) by (unfold S, Ops.Ops.fsize; lia).
  assert (EMO : mo' = with_fds (m_fds mo') mo_j) by (unfold mo_j; rewrite with_fds_idem, with_fds_self; reflexivity).
  assert (HMP' : MP mo') by (rewrite EMO; apply MP_fds; exact MPj).

  assert (TAIL : forall (st' : sstate) (newoff nsv : sv) (fs' : list fact) (os' : list opinst),
    In st' sts ->
    st' = SS r (rf_set (s_rf (clobber st1)) X10 nsv) (s_ff st) (s_resv st) (s_regs st1) (fs' ++ s_facts st) os' (s_priv st) (s_next (clobber st1)) ->
    den E' newoff = (den E off + len_word bs)%bv ->
    OFF + Z.of_nat (length bs) <= S ->
    den E' nsv = len_word bs ->
    (forall i, (i < length bs)%nat -> nth i bs (Z_to_bv 8 0) = nth (Z.to_nat OFF + i) file (Z_to_bv 8 0)) ->
    Forall (fact_holds E') fs' ->
    (forall o, In o os' -> o = OpI CtrS.FD3_ID [newoff] \/ o = OpI ReadC.TwinB.ReadC.RSTV_ID [off; nsv] \/
                           (In o (s_ops st) /\ CtrS.is_fd_op o = false /\ PrimInt63.eqb (op_id o) ReadC.TwinB.ReadC.RSTV_ID = false)) ->
    (forall o, In o (s_ops st) -> op_id o = HEAP_ID -> In o os') ->
    realizes bsegs (mkCfg ms' mo') K).
  { intros st' newoff nsv fs' os' Hin Hst' Hnew Hle Hn Hbytes Hfs Hos Hkeep.
    apply (HK st' Hin E' ms' mo' (CtrFrame.TwinB.EXT E st Fv Gv) HMP').
    rewrite Hst', EMS'.
    assert (Hlen : Z.of_nat (length bs) <= 65536) by lia.
    assert (Hlenw : bv_unsigned (len_word bs) = Z.of_nat (length bs)) by (apply (CS.len_word_u file); exact Hlen).
    apply (phaseB st E ms mo r hargs wnl st1 L RNG sta LBa aw m' R' mo_j mo' cnt nsv (s_next (clobber st1)) off newoff nsv fs' os' HS CP FS CF AH BOT LO SPT WR MU WM).
    - apply (phaseA st E ms mo r hargs wnl st1 L RNG sta LBa aw m' R' mo_j errv cnt nsv (s_next (clobber st1)) HS CP FS CF AH BOT LO SPT WR MU WM).
      + exact MI.
      + exact MINV'.
      + exact STK'.
      + exact ERR.
      + exact ERRP.
      + intros rg Hrg. unfold CtrFrame.TwinB.kept_regsA in Hrg. cbn [In] in Hrg. repeat (destruct Hrg as [<-|Hrg]; [reflexivity|]). destruct Hrg.
      + fold Fv Gv E'. rewrite Hn. reflexivity.
      + exact OTj.
      + exact MIj.
      + exact ACj.
    - exact PRIV.
    - exists r1, r2. exact (UnreggPre.TwinB.find_op_In _ _ _ FRS).
    - exact EMO.
    - exact ACj.
    - exact MIj.
    -
      fold Fv Gv E'. cbn [Ops.Ops.fd3_holds]. split.
      + rewrite FDS', FDS, Hnew. reflexivity.
      + rewrite Hnew, bv_add_unsigned, Hlenw. fold OFF. rewrite bv_wrap_small; [fold S; lia|]. unfold bv_modulus. lia.
    -
      fold Fv Gv E'. rewrite DOFF, Hn. cbn [rstage_holds_v]. rewrite Hlenw. fold OFF. split; [lia|]. split; [lia|].
      intros i Hi. destruct STGP as [[_ (_ & _ & BY)] _]. rewrite (GlueA.TwinB.rb_mrdA bsegs).
      replace (STAGE + i) with (STAGE + Z.of_nat (Z.to_nat i)) by lia.
      rewrite (BY (Z.to_nat i)).
      * cbn [cells_bytes cbytes]. rewrite nth_error_app1 by lia. rewrite (nth_error_nth' bs (Z_to_bv 8 0)) by lia.
        f_equal. rewrite (Hbytes (Z.to_nat i)) by lia. f_equal. lia.
      * cbn [cells_bytes cbytes]. rewrite !length_app. lia.
    - exact Hfs.
    - exact Hos.
    - exact Hkeep. }
  idtac "LEAF-3".

  unfold aread_apply in Happ. rewrite PRE, RPRE in Happ. cbv zeta in Happ.
  assert (DS11 : den E CtrS.SIZE11 = Z_to_bv 64 S).
  { unfold CtrS.SIZE11. apply (OLB.den_param8 E 11%uint63 S (PB_size _ HPB)). lia. }
  assert (HS11 : bv_unsigned (den E CtrS.SIZE11) = S) by (rewrite DS11; apply OLB.Z_to_bv64_unsigned; lia).
  assert (H40 : bv_unsigned (den E CtrS.OFF_MAX) = 2 ^ 40) by (cbn [den CtrS.OFF_MAX]; rewrite wbv_unsigned, wlit_ok; reflexivity).
  assert (Hadd0 : forall x : word, (x + len_word (@nil byte))%bv = x).
  { intros x. apply bv_eq. rewrite bv_add_unsigned. change (bv_unsigned (len_word (@nil byte))) with 0. rewrite Z.add_0_r.
    apply bv_wrap_small. apply u64_range. }
  assert (VB11 : sv_vars_below (s_next st) CtrS.SIZE11 = true) by reflexivity.
  assert (SHAPE : forall os' v0 fs0, fold_left addfact fs0 (ret_state st1 r os' v0)
            = SS r (rf_set (s_rf (clobber st1)) X10 v0) (s_ff st) (s_resv st) (s_regs st1) (rev fs0 ++ s_facts st) os' (s_priv st) (s_next (clobber st1))).
  { intros os' v0 fs0. assert (G0 : ret_state st1 r os' v0
        = SS r (rf_set (s_rf (clobber st1)) X10 v0) (s_ff st) (s_resv st) (s_regs st1) (s_facts st) os' (s_priv st) (s_next (clobber st1))).
    { unfold ret_state. rewrite <- FF1, <- RV1, <- FS1, <- PV1, <- FF, <- RV, <- RG, <- FS0, <- PV. destruct (clobber st1); reflexivity. }
    rewrite G0. clear G0. generalize (s_facts st). induction fs0 as [|f fs0 IH]; intros l0; [reflexivity|].
    cbn [fold_left rev]. unfold addfact at 2. cbn [s_pc s_rf s_ff s_resv s_regs s_facts s_ops s_priv s_next]. rewrite IH, <- app_assoc. reflexivity. }
  assert (Hbsu : bs = firstn (Z.to_nat cnt) (skipn (Z.to_nat OFF) file)).
  { unfold bs. rewrite file_read_unguarded. unfold word_to_nat. rewrite OLB.Z_to_bv64_unsigned by lia. reflexivity. }
  assert (Hlenbs : length bs = Nat.min (Z.to_nat cnt) (length file - Z.to_nat OFF)) by (rewrite Hbsu, length_firstn, length_skipn; reflexivity).
  assert (Hbytes : forall i, (i < length bs)%nat -> nth i bs (Z_to_bv 8 0) = nth (Z.to_nat OFF + i) file (Z_to_bv 8 0)).
  { intros i Hi. rewrite Hbsu in Hi |- *. apply (CS.nth_window file). exact Hi. }
  idtac "LEAF-4".
  assert (ONE : Nat.eqb (CtrS.count_fd_ops (s_ops st)) 1%nat = true) by exact ONEFD.
  assert (EOFCASE : known_leu (s_facts st) CtrS.SIZE11 off = true -> known_leu (s_facts st) off CtrS.OFF_MAX = true ->
            sts = [ret_state st1 r (set_op ReadC.TwinB.ReadC.RSTV_ID [off; VL wzero] (s_ops st)) (VL wzero)] -> realizes bsegs (mkCfg ms' mo') K).
  { intros Heof Hom ESTS. rewrite ESTS in TAIL.
    pose proof (known_leu_sound_g E st ms mo _ _ HS Heof) as H1. rewrite HS11 in H1. fold OFF in H1.
    pose proof (known_leu_sound_g E st ms mo _ _ HS Hom) as H2. rewrite H40 in H2. fold OFF in H2.
    assert (HOS0 : OFF = S /\ S = Z.of_nat (length file)) by (unfold S, Ops.Ops.fsize in *; lia).
    assert (Hb0 : bs = []) by (rewrite Hbsu, skipn_all2 by lia; apply firstn_nil).
    apply (TAIL _ off (VL wzero) [] (set_op ReadC.TwinB.ReadC.RSTV_ID [off; VL wzero] (s_ops st)) (or_introl eq_refl) (SHAPE _ _ [])).
    + rewrite DOFF, Hb0. symmetry. apply Hadd0.
    + rewrite Hb0. cbn [length Z.of_nat]. lia.
    + rewrite Hb0. cbn [den]. rewrite wbv_wzero. reflexivity.
    + intros i Hi. rewrite Hb0 in Hi. cbn in Hi. lia.
    + constructor.
    + intros o Ho. destruct (CS.set_op_others file _ _ _ o CNTR Ho) as [->|[Hin Hne]]; [right; left; reflexivity|].
      destruct (PrimInt63.eqb (op_id o) CtrS.FD3_ID) eqn:E2.
      * left. apply (CS.fd_op_is file (s_ops st) [off] o ONE F3 Hin). unfold CtrS.is_fd_op. rewrite E2, orb_true_r. reflexivity.
      * right; right. split; [exact Hin|]. split; [exact (CS.set_fd_others file (s_ops st) off o ONE F3 Hin E2) | exact Hne].
    + intros o Ho Hid1. apply CS.set_op_keep; [exact Ho| rewrite Hid1; reflexivity]. }
  destruct (CtrS.want_ok (Step.getr st X12)) as [w|] eqn:HW.
  2:{
      match type of Happ with (if ?cnd then _ else _) = _ => destruct cnd eqn:CND; [|discriminate Happ] end.
      repeat match type of CND with (_ && _)%bool = true => let Q := fresh "Q" in apply andb_prop in CND as [CND Q] end.
      injection Happ as <-. exact (EOFCASE Q0 Q eq_refl). }
  destruct (want_ok_inv _ _ HW) as [X12E WRw].
  assert (ECW : cnt = w2Z w) by (rewrite <- ECNT, X12E; cbn [den]; apply wbv_unsigned).
  destruct (known_leu (s_facts st) CtrS.SIZE11 off) eqn:Heof.
  -
    destruct (known_leu (s_facts st) off CtrS.OFF_MAX) eqn:Hom; [|discriminate Happ]. injection Happ as <-.
    exact (EOFCASE eq_refl eq_refl eq_refl).
  -
    set (e := sv_alu ALU_ADD off (VL w)) in *. set (nB := sv_alu ALU_SUB CtrS.SIZE11 off) in *.
    destruct (known_leu (s_facts st) e CtrS.OFF_MAX) eqn:Hem; [|discriminate Happ]. cbn [negb] in Happ.
    pose proof (known_leu_sound_g E st ms mo _ _ HS Hem) as H2. rewrite H40 in H2.
    assert (He : den E e = (den E off + wbv w)%bv) by (subst e; rewrite den_sv_alu; reflexivity).
    assert (Heu : bv_unsigned (den E e) = OFF + cnt).
    { rewrite He, bv_add_unsigned, wbv_unsigned, <- ECW. apply bv_wrap_small. unfold bv_modulus. subst OFF. lia. }
    rewrite Heu in H2.
    assert (VBe : sv_vars_below (s_next st) e = true) by (apply MemFX.MemFX.sv_vars_below_alu; [left; reflexivity| exact VBoff| reflexivity]).
    assert (VBn : sv_vars_below (s_next st) nB = true) by (apply MemFX.MemFX.sv_vars_below_alu; [right; reflexivity| exact VB11| exact VBoff]).
    assert (De : den E' e = den E e) by (apply CtrFrame.TwinB.den_E'; exact VBe).
    assert (DnB : den E' nB = den E nB) by (apply CtrFrame.TwinB.den_E'; exact VBn).
    assert (D11 : den E' CtrS.SIZE11 = den E CtrS.SIZE11) by (apply CtrFrame.TwinB.den_E'; exact VB11).
    assert (Hc2 : forall x : sv, Nat.eqb (CtrS.count_ops CtrS.FD3_ID (set_op ReadC.TwinB.ReadC.RSTV_ID [off; x] (s_ops st))) 1%nat = true).
    { intros x. rewrite (CS.count_ops_set_op_ne CtrS.FD3_ID ReadC.TwinB.ReadC.RSTV_ID) by reflexivity. exact (CS.count_FD3_one file _ off ONE F3). }
    assert (HOSx : forall (newoff nsv : sv) o,
      In o (set_op CtrS.FD3_ID [newoff] (set_op ReadC.TwinB.ReadC.RSTV_ID [off; nsv] (s_ops st))) ->
      o = OpI CtrS.FD3_ID [newoff] \/ o = OpI ReadC.TwinB.ReadC.RSTV_ID [off; nsv] \/
      (In o (s_ops st) /\ CtrS.is_fd_op o = false /\ PrimInt63.eqb (op_id o) ReadC.TwinB.ReadC.RSTV_ID = false)).
    { intros newoff nsv o Ho. destruct (CS.set_op_others file _ _ _ o (Hc2 nsv) Ho) as [->|[Ho1 Hne2]]; [left; reflexivity|right].
      destruct (CS.set_op_others file _ _ _ o CNTR Ho1) as [->|[Hin Hne3]]; [left; reflexivity|right].
      split; [exact Hin|]. split; [exact (CS.set_fd_others file (s_ops st) off o ONE F3 Hin Hne2) | exact Hne3]. }
    assert (KEEPx : forall (newoff nsv : sv) o, In o (s_ops st) -> op_id o = HEAP_ID ->
      In o (set_op CtrS.FD3_ID [newoff] (set_op ReadC.TwinB.ReadC.RSTV_ID [off; nsv] (s_ops st)))).
    { intros newoff nsv o Ho Hid1. apply CS.set_op_keep; [apply CS.set_op_keep; [exact Ho| rewrite Hid1; reflexivity]| rewrite Hid1; reflexivity]. }
    assert (CASE_A : OFF + cnt <= S ->
      In (addfact (ret_state st1 r (set_op CtrS.FD3_ID [e] (set_op ReadC.TwinB.ReadC.RSTV_ID [off; VL w] (s_ops st))) (VL w)) (FULe e CtrS.SIZE11)) sts ->
      realizes bsegs (mkCfg ms' mo') K).
    { intros HA Hin.
      assert (Hlw : length bs = Z.to_nat cnt) by (rewrite Hlenbs; unfold S, Ops.Ops.fsize in *; lia).
      assert (Hlword : len_word bs = wbv w). { unfold len_word. rewrite Hlw, CS.wbv_Z. f_equal. rewrite <- ECW. lia. }
      apply (TAIL _ e (VL w) [FULe e CtrS.SIZE11] _ Hin (SHAPE _ _ [FULe e CtrS.SIZE11])).
      + rewrite De, Hlword. exact He.
      + rewrite Hlw. lia.
      + rewrite Hlword. reflexivity.
      + exact Hbytes.
      + constructor; [|constructor]. cbn [fact_holds]. rewrite De, D11, Heu, HS11. exact HA.
      + apply HOSx.
      + apply KEEPx. }
    assert (CASE_B : S < OFF + cnt ->
      In (addfact (ret_state st1 r (set_op CtrS.FD3_ID [CtrS.SIZE11] (set_op ReadC.TwinB.ReadC.RSTV_ID [off; nB] (s_ops st))) nB) (FULt CtrS.SIZE11 e)) sts ->
      realizes bsegs (mkCfg ms' mo') K).
    { intros HB Hin.
      assert (HSl : S = Z.of_nat (length file)) by (unfold S, Ops.Ops.fsize in *; lia).
      assert (Hlw : Z.of_nat (length bs) = S - OFF) by (rewrite Hlenbs; lia).
      assert (Hlword : len_word bs = Z_to_bv 64 (S - OFF)) by (unfold len_word; rewrite Hlw; reflexivity).
      assert (HnB : den E nB = Z_to_bv 64 (S - OFF)).
      { subst nB. rewrite den_sv_alu. cbn [alu64 alu]. apply bv_eq. rewrite bv_sub_unsigned, HS11, OLB.Z_to_bv64_unsigned by lia.
        fold OFF. apply bv_wrap_small. unfold bv_modulus. lia. }
      apply (TAIL _ CtrS.SIZE11 nB [FULt CtrS.SIZE11 e] _ Hin (SHAPE _ _ [FULt CtrS.SIZE11 e])).
      + rewrite D11, Hlword, DS11. apply bv_eq. rewrite bv_add_unsigned, !OLB.Z_to_bv64_unsigned by lia.
        fold OFF. replace (OFF + (S - OFF)) with S by lia. symmetry. apply bv_wrap_small. unfold bv_modulus. lia.
      + lia.
      + rewrite DnB, Hlword. exact HnB.
      + exact Hbytes.
      + constructor; [|constructor]. cbn [fact_holds]. rewrite De, D11, Heu, HS11. exact HB.
      + apply HOSx.
      + apply KEEPx. }
    destruct (decide_ltu (s_facts st) CtrS.SIZE11 e) as [[|]|] eqn:Hd; injection Happ as <-.
    + apply CASE_B; [|left; reflexivity]. pose proof (decide_ltu_holds_g E st ms mo _ _ _ HS Hd) as X. cbn [negb] in X. rewrite HS11, Heu in X. exact X.
    + apply CASE_A; [|left; reflexivity]. pose proof (decide_ltu_holds_g E st ms mo _ _ _ HS Hd) as X. cbn [negb] in X. rewrite HS11, Heu in X. exact X.
    + destruct (Z_lt_le_dec S (OFF + cnt)) as [HB|HA].
      * apply CASE_B; [exact HB | right; left; reflexivity].
      * apply CASE_A; [lia | left; reflexivity].
Qed.
End Leaf.
End TwinB.
