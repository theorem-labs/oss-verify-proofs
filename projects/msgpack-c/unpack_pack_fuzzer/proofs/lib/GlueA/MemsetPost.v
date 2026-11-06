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
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Ctr Require Import Lib DefsA.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Bridge Require Import Ledger Op Adeq.
Import ListNotations.
Import W64 Val OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Mem.Mem FI St OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Step.Step Plan PlanS CtrLib HeapOp.
Open Scope Z_scope.
Unset Lia Cache.

From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Bridge Require Import Actr.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX Require Import W64Proofs ValProofs MemProofs StepSoundBase.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Br Require Import CtrFX.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Br Require HeapCtr HeapCtrB MemFX.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Bridge Require CallA GlueA CtrPre CtrFrame CtrNoDelta CtrFree.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.GlueA Require UnreggGeo UnreggPre.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.GlueA Require Import MemsetC MemOps MemsetFX RangePre MemsetSound.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.GlueA Require ReadPost.
Unset Nia Cache. Unset Nra Cache.
Import ValP MemP StepB CtrFX ActrA MemsetC.
Module AM := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Mem.
Module AS := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Step.

Definition in_rng (lo hi a : Z) : bool := (lo <=? a) && (a <? hi).
Definition mjoinR (lo hi : Z) (m m' : amem) : amem := fun x => if in_rng lo hi (bv_unsigned x) then m x else m' x.

Section MemSide.
Context {rc : runConstT}.
Variables (m m' : amem) (sp lo A0 len FRM : Z).
Hypothesis MU : munch [(sp - FRM, sp); (A0, A0 + len)]%Z m m'.
Hypothesis WM : wmono asegs m m'.
Hypothesis LO : ATOP + 4096 <= lo /\ lo <= sp - 4096 /\ sp < 2 ^ 47.
Hypothesis DR : 0 <= A0 /\ (A0 + len <= ATOP \/ sp <= A0).
Notation mj := (mjoinR A0 (A0 + len) m m').

Lemma mjr_out : forall a, 0 <= a < 2 ^ 64 -> ~ (sp - FRM <= a < sp) -> mj (AM.wa a) = m (AM.wa a).
Proof.
  intros a Ha N1. unfold mjoinR. rewrite (ReadPost.wa_u a Ha). destruct (in_rng A0 (A0 + len) a) eqn:IS; [reflexivity|].
  apply MU. rewrite (ReadPost.wa_u a Ha). cbn [outside]. unfold in_rng in IS. lia.
Qed.
Lemma mjr_final : forall a, 0 <= a < 2 ^ 64 -> ~ (A0 <= a < A0 + len) -> mj (AM.wa a) = m' (AM.wa a).
Proof. intros a Ha S. unfold mjoinR. rewrite (ReadPost.wa_u a Ha). unfold in_rng. replace ((A0 <=? a) && (a <? A0 + len)) with false by lia. reflexivity. Qed.
Lemma mjr_wmono : wmono asegs m mj.
Proof.
  intros x H. destruct (in_rng A0 (A0 + len) (bv_unsigned x)) eqn:IS.
  - rewrite (ReadPost.wview_ext m mj x); [exact H|]. unfold mjoinR. rewrite IS. reflexivity.
  - rewrite (ReadPost.wview_ext m' mj x); [exact (WM x H)|]. unfold mjoinR. rewrite IS. reflexivity.
Qed.
Lemma mjr_munch : munch [(sp - FRM, sp)]%Z m mj.
Proof.
  intros x OUT. cbn [outside] in OUT. pose proof (bv_unsigned_in_range _ x) as RX. unfold bv_modulus in RX.
  assert (EX : AM.wa (bv_unsigned x) = x) by (unfold AM.wa; apply Z_to_bv_bv_unsigned).
  rewrite <- EX. apply (mjr_out (bv_unsigned x)); [lia | tauto].
Qed.
Lemma mjr_mem_inv : AM.mem_inv asegs m -> AM.mem_inv asegs m' -> AM.mem_inv asegs mj.
Proof. intros I1 I2 a b H. unfold mjoinR in H. destruct (in_rng A0 (A0 + len) (bv_unsigned a)); [exact (I1 a b H)| exact (I2 a b H)]. Qed.
Lemma mjr_stk : stk asegs m' lo sp -> stk asegs mj lo sp.
Proof.
  intros (H1 & H2 & H). split; [exact H1|]. split; [exact H2|]. intros a Ha.
  assert (E : mj (AM.wa a) = m' (AM.wa a)) by (apply mjr_final; lia).
  rewrite (ReadPost.wview_ext m' mj _ E), (ReadPost.mrd_ext m' mj _ E). exact (H a Ha).
Qed.
End MemSide.

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

Lemma aci_low' : forall a, in_ranges (aci AI) a -> a < AIMG_HI.
Proof. intros a (iv0 & Hi & RR). pose proof (AI_aci_img AI iv0 Hi). lia. Qed.

Lemma phaseA_ms_g : forall st E ms mo r hargs wnl st1 (L : alayout) (RNG : footprint) (sta : astate) (LBa : list ablock) (aw : word)
    (m' : amem) (R' : bvmap 5 word) (mo' : Model) (A0 len FRM : Z) (v : sv) (nx' : int),
  st_ok asegs OPS E st ms mo -> call_pre st = Some r -> forget_stack_below_sp_g st = Some st1 ->
  CtrPre.acallG AI ACCT UNIV Cw E st ms mo r hargs wnl L RNG sta LBa aw -> AHEAP AI L RNG sta LBa (ms_mem ms) ->
  let R := ms_regs ms in let sp := bv_unsigned (AP.getr R 2) in
  ATOP + 4096 <= CtrPre.sp_lo E st -> CtrPre.sp_lo E st <= sp - 4096 -> sp < 2 ^ 47 -> 0 <= A0 -> (A0 + len <= ATOP \/ sp <= A0) ->
  0 < FRM /\ CtrPre.sp_lo E st <= sp - FRM ->
  munch [(sp - FRM, sp); (A0, A0 + len)]%Z (ms_mem ms) m' -> wmono asegs (ms_mem ms) m' ->
  AM.mem_inv asegs (ms_mem ms) -> AM.mem_inv asegs m' -> stk asegs m' (CtrPre.sp_lo E st) sp ->
  (forall rg, In rg CtrFrame.kept_regsA -> AP.getr R' rg = AP.getr R rg) ->
  let Fv := CtrFree.cfvF R' in let Gv := fun (_ _ : Z) => Z_to_bv 8 0 in
  den (CtrFrame.E' E st Fv Gv) v = AP.getr R' 10%bv ->
  OTHER mo mo' -> op_minv OPS mo' -> ACCT aw L RNG sta LBa mo' ->
  st_ok asegs OPS (CtrFrame.E' E st Fv Gv)
    (SS r (rf_set (s_rf (clobber st1)) X10 v) (s_ff st) (s_resv st) (s_regs st1) (s_facts st) (s_ops st) (s_priv st) nx')
    (CtrFrame.ms' ms r R' (mjoinR A0 (A0 + len) (ms_mem ms) m')) mo'.
Proof.
  intros st E ms mo r hargs wnl st1 L RNG sta LBa aw m' R' mo' A0 len FRM v nx' HS CP FS CF AH R sp BOT LO SPT A00 AHI FRMok MU WM MI MI' STK' KEPT Fv Gv DV OTH MIj ACj.
  pose proof atop_range as ATR.
  assert (LO3 : ATOP + 4096 <= CtrPre.sp_lo E st /\ CtrPre.sp_lo E st <= sp - 4096 /\ sp < 2 ^ 47) by lia.
  assert (DR : 0 <= A0 /\ (A0 + len <= ATOP \/ sp <= A0)) by (split; assumption).
  set (m := ms_mem ms) in *.
  assert (IUOUT : forall LB0, aw_real AI ACCT UNIV aw LB0 m mo L RNG sta LBa -> forall a, 0 <= a < 2 ^ 64 -> in_user LB0 a ->
            mjoinR A0 (A0 + len) m m' (AM.wa a) = m (AM.wa a)).
  { intros LB0 AR0 a Ha IU. pose proof (UnreggGeo.user_out AI ACCT UNIV AI_fake aw LB0 m mo L RNG sta LBa a AR0 IU) as G.
    apply (mjr_out m m' sp A0 len FRM MU a Ha). unfold AIMG_HI, KLS in *. lia. }
  apply (CtrNoDelta.nodelta_st_ok AI IMGX IMGX_aci ACCT UNIV Cw OPS AI_fake OPS_holds1 OPS_fp1 OPS_cov1 OPS_frame_other OPS_fp_other OTHER OPS_mo_other
           OPS_cov0_img E st ms mo r hargs wnl L RNG sta LBa aw st1 Fv Gv R' (mjoinR A0 (A0 + len) m m') mo' RNG sta _ _ HS CP FS CF).
  - exact KEPT.
  - intros x i Hx. exact (CtrFree.cfvF_clob R' x i Hx).
  - exact DV.
  - exact (mjr_mem_inv m m' A0 len MI MI').
  - exact (mjr_stk m m' sp (CtrPre.sp_lo E st) A0 len LO3 DR STK').
  -
    intros LB0 AR0 a Ha STB. apply (FrameV.frame_v_of_raw asegs). destruct STB as [S1|[S2|S3]].
    + apply (mjr_out m m' sp A0 len FRM MU a Ha). unfold sp, R in *. lia.
    + pose proof (aci_low' a S2) as AL. apply (mjr_out m m' sp A0 len FRM MU a Ha). unfold AIMG_HI in *. lia.
    + exact (IUOUT LB0 AR0 a Ha S3).
  -   exact IUOUT.
  -
    intros o a Ho NI Ha FP. unfold not_id in NI. apply Uint63.eqb_false_spec in NI.
    destruct (OPS_fp_other _ _ a NI FP) as [INA|[(a' & INA & ->)|(a' & STK & ->)]].
    + pose proof (aci_low' a INA) as AL. apply (mjr_out m m' sp A0 len FRM MU a); [unfold two64 in Ha; lia| unfold AIMG_HI in *; lia].
    + pose proof (aci_low' a' INA) as AL. destruct INA as (iv0 & I0 & I1). pose proof (AI_aci_lo AI iv0 I0) as AA0.
      pose proof (CtrPre.shad_img_band a' ltac:(lia)) as BND. apply (mjr_out m m' sp A0 len FRM MU (shad a')); [unfold two64 in Ha; lia| lia].
    +
      assert (ZN : 0x7fffa000 <= shad a' < 0x10007fff8000) by (unfold shad, ASHOFF; rewrite Z.shiftr_div_pow2 by lia; change (2 ^ 3) with 8; clear - STK ATR; Z.div_mod_to_equations; lia).
      apply (mjr_out m m' sp A0 len FRM MU (shad a')); [unfold two64 in Ha; lia| unfold sp, R in *; lia].
  -   intros a Ha _ Wb. apply (GlueA.wb_wviewA asegs). apply (GlueA.wb_wviewA asegs) in Wb. exact (mjr_wmono m m' A0 len WM _ Wb).
  -
    intros a Ha SC _. apply (FrameV.frame_v_of_raw asegs).
    assert (ZN : 0x7fffa000 <= a < 0x10007fff8000).
    { destruct SC as [(a' & RR & ->)|(vv & Hv & RR)].
      - unfold shad, ASHOFF. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8. clear - RR ATR. Z.div_mod_to_equations. lia.
      - destruct (Op.SHLIT_cases vv Hv) as [->|(_ & P1 & P2 & P3)]; [cbn [fst snd] in RR|]; lia. }
    apply (mjr_out m m' sp A0 len FRM MU a Ha). unfold sp, R in *. lia.
  -
    apply (AI_frame AI L RNG sta LBa m (mjoinR A0 (A0 + len) m m') _ AH (mjr_munch m m' sp (CtrPre.sp_lo E st) A0 len FRM MU LO3 DR) (mjr_wmono m m' A0 len WM)).
    repeat (apply Forall_cons; [cbn [fst snd]|]); [| apply Forall_nil]. left. left. fold sp. lia.
  - exact ACj.
  -
    intros b x Hb FK Hx. pose proof (Op.blk_band AI AI_fake L RNG sta LBa m b x AH Hb) as BB.
    destruct (AI_fake L RNG sta LBa m b AH Hb FK) as (_ & _ & _ & _ & SZ64 & _). specialize (BB ltac:(lia)).
    apply (mjr_out m m' sp A0 len FRM MU x); unfold AIMG_HI, KLS in *; lia.
  -
    apply (Op.twins_pres_band AI L RNG sta LBa m (mjoinR A0 (A0 + len) m m') AH). intros a Ha.
    assert (SA : shad ATOP = ASHOFF + ATOP / 8) by (unfold shad; rewrite Z.shiftr_div_pow2 by lia; reflexivity).
    rewrite SA in Ha. unfold ASHOFF in Ha.
    apply (mjr_out m m' sp A0 len FRM MU a); [clear - Ha ATR; Z.div_mod_to_equations; lia| unfold sp, R in *; clear - Ha ATR LO3 FRMok; Z.div_mod_to_equations; lia].
  - exact OTH.
  - exact MIj.
  - exact (fun P => P).
Qed.

Lemma phaseA_ms : forall st E ms mo r hargs wnl st1 (L : alayout) (RNG : footprint) (sta : astate) (LBa : list ablock) (aw : word)
    (m' : amem) (R' : bvmap 5 word) (mo' : Model) (A0 len FRM : Z) (v : sv) (nx' : int),
  st_ok asegs OPS E st ms mo -> call_pre st = Some r -> forget_stack_below_sp_g st = Some st1 ->
  CtrPre.acallG AI ACCT UNIV Cw E st ms mo r hargs wnl L RNG sta LBa aw -> AHEAP AI L RNG sta LBa (ms_mem ms) ->
  let R := ms_regs ms in let sp := bv_unsigned (AP.getr R 2) in
  ATOP + 4096 <= CtrPre.sp_lo E st -> CtrPre.sp_lo E st <= sp - 4096 -> sp < 2 ^ 47 -> 0 <= A0 -> (A0 + len <= ATOP \/ sp <= A0) ->
  0 < FRM <= 4096 ->
  munch [(sp - FRM, sp); (A0, A0 + len)]%Z (ms_mem ms) m' -> wmono asegs (ms_mem ms) m' ->
  AM.mem_inv asegs (ms_mem ms) -> AM.mem_inv asegs m' -> stk asegs m' (CtrPre.sp_lo E st) sp ->
  (forall rg, In rg CtrFrame.kept_regsA -> AP.getr R' rg = AP.getr R rg) ->
  let Fv := CtrFree.cfvF R' in let Gv := fun (_ _ : Z) => Z_to_bv 8 0 in
  den (CtrFrame.E' E st Fv Gv) v = AP.getr R' 10%bv ->
  OTHER mo mo' -> op_minv OPS mo' -> ACCT aw L RNG sta LBa mo' ->
  st_ok asegs OPS (CtrFrame.E' E st Fv Gv)
    (SS r (rf_set (s_rf (clobber st1)) X10 v) (s_ff st) (s_resv st) (s_regs st1) (s_facts st) (s_ops st) (s_priv st) nx')
    (CtrFrame.ms' ms r R' (mjoinR A0 (A0 + len) (ms_mem ms) m')) mo'.
Proof.
  intros st E ms mo r hargs wnl st1 L RNG sta LBa aw m' R' mo' A0 len FRM v nx' HS CP FS CF AH R sp BOT LO SPT A00 AHI FRMok.
  apply (phaseA_ms_g st E ms mo r hargs wnl st1 L RNG sta LBa aw m' R' mo' A0 len FRM v nx' HS CP FS CF AH BOT LO SPT A00 AHI). fold R sp. lia.
Qed.

Lemma st_ok_mem_ext_g : forall E st ms mo (m' : amem),
  (forall x, m' x = ms_mem ms x) -> st_ok asegs OPS E st ms mo -> st_ok asegs OPS E st (ms_with_mem ms m') mo.
Proof.
  intros E st ms mo m' EQ HS.
  pose proof HS as [Ppc Px0 Pregs Pfregs Psvc Presv Pfcsr Prom Pz Pbst Preg Pdisj Ppub Pfacts Pops Papart Pmf Pcov Pminv].
  assert (RB : forall a, 0 <= a < two64 -> rb asegs m' a = rb asegs (ms_mem ms) a) by (intros a _; unfold rb; rewrite EQ; reflexivity).
  assert (WB : forall a, 0 <= a < two64 -> wb asegs (ms_mem ms) a = true -> wb asegs m' a = true).
  { intros a _. unfold wb, wview. rewrite EQ. exact (fun H => H). }
  split; cbn [ms_with_mem ms_upd ms_regs ms_fregs ms_pc_val ms_svc_pending ms_resv ms_fcsr ms_mem ms_rom core_of c_regs c_fregs c_pc c_fcsr c_resv] in *;
    try assumption; try reflexivity.
  - intros k r0 Hk. exact (MemFX.MemFX.region_ok_view_frame asegs _ _ (ms_mem ms) m' k r0 (Preg k r0 Hk) RB WB).
  - apply Forall_forall. intros o Ho. pose proof (proj1 (Forall_forall _ _) Pops o Ho) as OH.
    apply (St.op_frame OPS _ _ (ms_mem ms) m' mo); [intros a _ _; symmetry; apply EQ| intros a _ H; rewrite EQ; exact H| exact OH].
  - intros a b Hab. rewrite EQ in Hab. exact (Pminv a b Hab).
Qed.

Lemma byte_eq : forall c, Z_to_bv 8 (bv_unsigned (wbv c) mod 256) = Z_to_bv 8 (to_Z (PrimInt63.land (wl c) 255%uint63)).
Proof.
  intros c. f_equal. rewrite wbv_unsigned. pose proof (ValP.land_mk (wl c) 8%uint63 ltac:(change (to_Z 8%uint63) with 8; lia)) as LM.
  change (PrimInt63.sub (PrimInt63.lsl 1 8) 1)%uint63 with 255%uint63 in LM. rewrite LM. change (2 ^ to_Z 8%uint63) with 256.
  unfold w2Z. destruct (wt c); [| reflexivity]. unfold two63. rewrite <- (Z.add_mod_idemp_l 9223372036854775808) by lia.
  change (9223372036854775808 mod 256) with 0. reflexivity.
Qed.

Lemma amemset_leaf_ok : MemsetSound.amemset_leaf AI ACCT UNIV Cw OPS OTHER MP PB.
Proof.
  unfold MemsetSound.amemset_leaf.
  intros st sts K E ms mo r hargs wnl st1 kd od c n L RNG sta LBa aw HS HPB HK PRE G10 G11 G12 WTN NR SB CP FS CF AH MI BOT LO SPT
         LOWA HI47 POS EA0 EA2 EA1 ms' mo' HQ HMP' HMI' OTH ACP.
  set (R := ms_regs ms) in *. set (len := to_Z (wl n)) in *. set (A0 := bv_unsigned (ev E kd) + w2Zs od) in *.
  destruct HQ as (t0 & t1 & t2 & a1' & a2' & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & m' & EMS & MU & WM & MINV' & STK' & DSTP).
  rewrite EA0, EA2 in MU, DSTP.
  pose proof atop_range as ATR.
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
  idtac "ML-1".
  pose proof (HeapCtr.fresh_ok_inv st FOK) as (SVB & _).
  assert (VBd : sv_vars_below (s_next st) (VP kd od) = true).
  { unfold st_vars_below in SVB. do 5 (apply andb_prop in SVB as [SVB _]). rewrite <- G10. exact (PlanS.rf_allb_get _ _ _ SVB X10). }
  assert (DVP : den E' (VP kd od) = AP.getr R' 10%bv).
  { unfold E'. rewrite (CtrFrame.den_E' E st Fv Gv _ VBd), <- G10. symmetry. exact (GlueA.getr_RA asegs OPS E st ms mo HS X10). }
  assert (DA0 : bv_unsigned (den E' (VP kd od)) = A0) by (rewrite DVP; exact EA0).

  pose proof (phaseA_ms st E ms mo r hargs wnl st1 L RNG sta LBa aw m' R' mo' A0 len 2224 (VP kd od) (s_next (clobber st1)) HS CP FS CF AH BOT LO SPT
                ltac:(unfold AIMG_HI in *; lia) POS ltac:(lia) MU WM MI MINV' STK'
                ltac:(intros rg Hrg; unfold CtrFrame.kept_regsA in Hrg; cbn [In] in Hrg; repeat (destruct Hrg as [<-|Hrg]; [reflexivity|]); destruct Hrg)
                DVP OTH HMI' ACP) as HSA.
  fold Fv Gv E' in HSA.

  assert (SH2 : setpc (setr (clobber st1) X10 (VP kd od)) r
              = SS r (rf_set (s_rf (clobber st1)) X10 (VP kd od)) (s_ff st) (s_resv st) (s_regs st1) (s_facts st) (s_ops st) (s_priv st) (s_next (clobber st1))).
  { rewrite <- FF1, <- RV1, <- FS1, <- OP1, <- PV1, <- FF, <- RV, <- RG, <- FS0, <- OP, <- PV. destruct (clobber st1); reflexivity. }
  unfold set_bytes_post in SB. rewrite SH2 in SB.
  match type of SB with match ?sbx with _ => _ end = _ => destruct sbx as [stn|] eqn:SBY; [|discriminate SB] end. injection SB as <-.
  set (b := PrimInt63.land (wl c) 255%uint63) in *.
  assert (Hb : 0 <= to_Z b < 256).
  { unfold b. pose proof (ValP.land_mk (wl c) 8%uint63 ltac:(change (to_Z 8%uint63) with 8; lia)) as LM.
    change (PrimInt63.sub (PrimInt63.lsl 1 8) 1)%uint63 with 255%uint63 in LM. rewrite LM. change (2 ^ to_Z 8%uint63) with 256. apply Z.mod_pos_bound. lia. }
  destruct (MemsetFX.set_bytes_sound asegs OPS _ 0%uint63 (VP kd od) (wl od) b (wl n) _ stn E' _ mo' HSA RVN eq_refl SBY Hb
              ltac:(change (to_Z 0%uint63) with 0; fold len; lia) ltac:(rewrite DA0; fold len; unfold two64; lia))
    as (mc & HSc & FRc & INc & MONOc & _).
  rewrite DA0 in FRc, INc. fold len in FRc, INc. change (to_Z 0%uint63) with 0 in FRc, INc. cbn [ms_mem CtrFrame.ms'] in FRc.
  idtac "ML-2".

  assert (DSTB : forall j, 0 <= j < len -> m' (Z_to_bv 64 (A0 + j)) = Some (Z_to_bv 8 (to_Z b))).
  { intros j Hj. apply raw_of_view; [unfold AIMG_HI, ATOP in *; lia|].
    destruct DSTP as [[_ (_ & _ & BY)] _]. rewrite (GlueA.rb_mrdA asegs).
    replace (A0 + j) with (A0 + Z.of_nat (Z.to_nat j)) by lia.
    rewrite (BY (Z.to_nat j)).
    - cbn [cells_bytes cbytes]. rewrite app_nil_r. rewrite nth_error_repeat by lia. f_equal. rewrite EA1. unfold b. apply byte_eq.
    - cbn [cells_bytes cbytes]. rewrite app_nil_r, repeat_length. lia. }
  idtac "ML-3".

  assert (PW : forall x, m' x = mc x).
  { intros x. pose proof (bv_unsigned_in_range _ x) as RX. unfold bv_modulus in RX.
    assert (EX : Z_to_bv 64 (bv_unsigned x) = x) by apply Z_to_bv_bv_unsigned.
    destruct (in_rng A0 (A0 + len) (bv_unsigned x)) eqn:IS.
    - unfold in_rng in IS. rewrite <- EX. replace (bv_unsigned x) with (A0 + (bv_unsigned x - A0)) by lia.
      rewrite (DSTB (bv_unsigned x - A0)) by lia. symmetry. apply INc. lia.
    - unfold in_rng in IS. rewrite <- EX. rewrite (FRc (bv_unsigned x)); [| unfold two64; lia | lia].
      symmetry. apply (mjr_final (ms_mem ms) m' A0 len (bv_unsigned x)); lia. }
  idtac "ML-4".
  pose proof (st_ok_mem_ext_g E' stn (ms_with_mem (CtrFrame.ms' ms r R' (mjoinR A0 (A0 + len) (ms_mem ms) m')) mc) mo' m' PW HSc) as HSF.
  apply (HK stn ltac:(left; reflexivity) E' ms' mo' (CtrFrame.EXT E st Fv Gv) HMP').
  rewrite EMS'. exact HSF.
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
Import W64 Val OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Mem.Mem FI St OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Step.Step Plan PlanS CtrLib HeapOp.
Open Scope Z_scope.
Unset Lia Cache.

Import Actr.TwinB.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.W64Proofs OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.ValProofs OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.MemProofs OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.StepSoundBase.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Br.CtrFX.

Import MemsetC.TwinB MemOps.TwinB MemsetFX.TwinB RangePre.TwinB MemsetSound.TwinB.

Unset Nia Cache. Unset Nra Cache.
Import ValP MemP StepB CtrFX ActrA MemsetC.TwinB.MemsetC.
Module AM := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Mem.
Module AS := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Step.

Definition in_rng (lo hi a : Z) : bool := (lo <=? a) && (a <? hi).
Definition mjoinR (lo hi : Z) (m m' : amem) : amem := fun x => if in_rng lo hi (bv_unsigned x) then m x else m' x.

Section MemSide.
Context {rc : runConstT}.
Variables (m m' : amem) (sp lo A0 len FRM : Z).
Hypothesis MU : munch [(sp - FRM, sp); (A0, A0 + len)]%Z m m'.
Hypothesis WM : wmono bsegs m m'.
Hypothesis LO : ATOP + 4096 <= lo /\ lo <= sp - 4096 /\ sp < 2 ^ 47.
Hypothesis DR : 0 <= A0 /\ (A0 + len <= ATOP \/ sp <= A0).
Notation mj := (mjoinR A0 (A0 + len) m m').

Lemma mjr_out : forall a, 0 <= a < 2 ^ 64 -> ~ (sp - FRM <= a < sp) -> mj (AM.wa a) = m (AM.wa a).
Proof.
  intros a Ha N1. unfold mjoinR. rewrite (ReadPost.TwinB.wa_u a Ha). destruct (in_rng A0 (A0 + len) a) eqn:IS; [reflexivity|].
  apply MU. rewrite (ReadPost.TwinB.wa_u a Ha). cbn [outside]. unfold in_rng in IS. lia.
Qed.
Lemma mjr_final : forall a, 0 <= a < 2 ^ 64 -> ~ (A0 <= a < A0 + len) -> mj (AM.wa a) = m' (AM.wa a).
Proof. intros a Ha S. unfold mjoinR. rewrite (ReadPost.TwinB.wa_u a Ha). unfold in_rng. replace ((A0 <=? a) && (a <? A0 + len)) with false by lia. reflexivity. Qed.
Lemma mjr_wmono : wmono bsegs m mj.
Proof.
  intros x H. destruct (in_rng A0 (A0 + len) (bv_unsigned x)) eqn:IS.
  - rewrite (ReadPost.TwinB.wview_ext m mj x); [exact H|]. unfold mjoinR. rewrite IS. reflexivity.
  - rewrite (ReadPost.TwinB.wview_ext m' mj x); [exact (WM x H)|]. unfold mjoinR. rewrite IS. reflexivity.
Qed.
Lemma mjr_munch : munch [(sp - FRM, sp)]%Z m mj.
Proof.
  intros x OUT. cbn [outside] in OUT. pose proof (bv_unsigned_in_range _ x) as RX. unfold bv_modulus in RX.
  assert (EX : AM.wa (bv_unsigned x) = x) by (unfold AM.wa; apply Z_to_bv_bv_unsigned).
  rewrite <- EX. apply (mjr_out (bv_unsigned x)); [lia | tauto].
Qed.
Lemma mjr_mem_inv : AM.mem_inv bsegs m -> AM.mem_inv bsegs m' -> AM.mem_inv bsegs mj.
Proof. intros I1 I2 a b H. unfold mjoinR in H. destruct (in_rng A0 (A0 + len) (bv_unsigned a)); [exact (I1 a b H)| exact (I2 a b H)]. Qed.
Lemma mjr_stk : stk bsegs m' lo sp -> stk bsegs mj lo sp.
Proof.
  intros (H1 & H2 & H). split; [exact H1|]. split; [exact H2|]. intros a Ha.
  assert (E : mj (AM.wa a) = m' (AM.wa a)) by (apply mjr_final; lia).
  rewrite (ReadPost.TwinB.wview_ext m' mj _ E), (ReadPost.TwinB.mrd_ext m' mj _ E). exact (H a Ha).
Qed.
End MemSide.

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

Lemma aci_low' : forall a, in_ranges (aci AI) a -> a < AIMG_HI.
Proof. intros a (iv0 & Hi & RR). pose proof (AI_aci_img AI iv0 Hi). lia. Qed.

Lemma phaseA_ms_g : forall st E ms mo r hargs wnl st1 (L : alayout) (RNG : footprint) (sta : astate) (LBa : list ablock) (aw : word)
    (m' : amem) (R' : bvmap 5 word) (mo' : Model) (A0 len FRM : Z) (v : sv) (nx' : int),
  st_ok bsegs OPS E st ms mo -> call_pre st = Some r -> forget_stack_below_sp_g st = Some st1 ->
  CtrPre.TwinB.acallG AI ACCT UNIV Cw E st ms mo r hargs wnl L RNG sta LBa aw -> AHEAP AI L RNG sta LBa (ms_mem ms) ->
  let R := ms_regs ms in let sp := bv_unsigned (AP.getr R 2) in
  ATOP + 4096 <= CtrPre.TwinB.sp_lo E st -> CtrPre.TwinB.sp_lo E st <= sp - 4096 -> sp < 2 ^ 47 -> 0 <= A0 -> (A0 + len <= ATOP \/ sp <= A0) ->
  0 < FRM /\ CtrPre.TwinB.sp_lo E st <= sp - FRM ->
  munch [(sp - FRM, sp); (A0, A0 + len)]%Z (ms_mem ms) m' -> wmono bsegs (ms_mem ms) m' ->
  AM.mem_inv bsegs (ms_mem ms) -> AM.mem_inv bsegs m' -> stk bsegs m' (CtrPre.TwinB.sp_lo E st) sp ->
  (forall rg, In rg CtrFrame.TwinB.kept_regsA -> AP.getr R' rg = AP.getr R rg) ->
  let Fv := CtrFree.TwinB.cfvF R' in let Gv := fun (_ _ : Z) => Z_to_bv 8 0 in
  den (CtrFrame.TwinB.E' E st Fv Gv) v = AP.getr R' 10%bv ->
  OTHER mo mo' -> op_minv OPS mo' -> ACCT aw L RNG sta LBa mo' ->
  st_ok bsegs OPS (CtrFrame.TwinB.E' E st Fv Gv)
    (SS r (rf_set (s_rf (clobber st1)) X10 v) (s_ff st) (s_resv st) (s_regs st1) (s_facts st) (s_ops st) (s_priv st) nx')
    (CtrFrame.TwinB.ms' ms r R' (mjoinR A0 (A0 + len) (ms_mem ms) m')) mo'.
Proof.
  intros st E ms mo r hargs wnl st1 L RNG sta LBa aw m' R' mo' A0 len FRM v nx' HS CP FS CF AH R sp BOT LO SPT A00 AHI FRMok MU WM MI MI' STK' KEPT Fv Gv DV OTH MIj ACj.
  pose proof atop_range as ATR.
  assert (LO3 : ATOP + 4096 <= CtrPre.TwinB.sp_lo E st /\ CtrPre.TwinB.sp_lo E st <= sp - 4096 /\ sp < 2 ^ 47) by lia.
  assert (DR : 0 <= A0 /\ (A0 + len <= ATOP \/ sp <= A0)) by (split; assumption).
  set (m := ms_mem ms) in *.
  assert (IUOUT : forall LB0, aw_real AI ACCT UNIV aw LB0 m mo L RNG sta LBa -> forall a, 0 <= a < 2 ^ 64 -> in_user LB0 a ->
            mjoinR A0 (A0 + len) m m' (AM.wa a) = m (AM.wa a)).
  { intros LB0 AR0 a Ha IU. pose proof (UnreggGeo.TwinB.user_out AI ACCT UNIV AI_fake aw LB0 m mo L RNG sta LBa a AR0 IU) as G.
    apply (mjr_out m m' sp A0 len FRM MU a Ha). unfold AIMG_HI, KLS in *. lia. }
  apply (CtrNoDelta.TwinB.nodelta_st_ok AI IMGX IMGX_aci ACCT UNIV Cw OPS AI_fake OPS_holds1 OPS_fp1 OPS_cov1 OPS_frame_other OPS_fp_other OTHER OPS_mo_other
           OPS_cov0_img E st ms mo r hargs wnl L RNG sta LBa aw st1 Fv Gv R' (mjoinR A0 (A0 + len) m m') mo' RNG sta _ _ HS CP FS CF).
  - exact KEPT.
  - intros x i Hx. exact (CtrFree.TwinB.cfvF_clob R' x i Hx).
  - exact DV.
  - exact (mjr_mem_inv m m' A0 len MI MI').
  - exact (mjr_stk m m' sp (CtrPre.TwinB.sp_lo E st) A0 len LO3 DR STK').
  -
    intros LB0 AR0 a Ha STB. apply (FrameV.TwinB.frame_v_of_raw bsegs). destruct STB as [S1|[S2|S3]].
    + apply (mjr_out m m' sp A0 len FRM MU a Ha). unfold sp, R in *. lia.
    + pose proof (aci_low' a S2) as AL. apply (mjr_out m m' sp A0 len FRM MU a Ha). unfold AIMG_HI in *. lia.
    + exact (IUOUT LB0 AR0 a Ha S3).
  -   exact IUOUT.
  -
    intros o a Ho NI Ha FP. unfold not_id in NI. apply Uint63.eqb_false_spec in NI.
    destruct (OPS_fp_other _ _ a NI FP) as [INA|[(a' & INA & ->)|(a' & STK & ->)]].
    + pose proof (aci_low' a INA) as AL. apply (mjr_out m m' sp A0 len FRM MU a); [unfold two64 in Ha; lia| unfold AIMG_HI in *; lia].
    + pose proof (aci_low' a' INA) as AL. destruct INA as (iv0 & I0 & I1). pose proof (AI_aci_lo AI iv0 I0) as AA0.
      pose proof (CtrPre.TwinB.shad_img_band a' ltac:(lia)) as BND. apply (mjr_out m m' sp A0 len FRM MU (shad a')); [unfold two64 in Ha; lia| lia].
    +
      assert (ZN : 0x7fffa000 <= shad a' < 0x10007fff8000) by (unfold shad, ASHOFF; rewrite Z.shiftr_div_pow2 by lia; change (2 ^ 3) with 8; clear - STK ATR; Z.div_mod_to_equations; lia).
      apply (mjr_out m m' sp A0 len FRM MU (shad a')); [unfold two64 in Ha; lia| unfold sp, R in *; lia].
  -   intros a Ha _ Wb. apply (GlueA.TwinB.wb_wviewA bsegs). apply (GlueA.TwinB.wb_wviewA bsegs) in Wb. exact (mjr_wmono m m' A0 len WM _ Wb).
  -
    intros a Ha SC _. apply (FrameV.TwinB.frame_v_of_raw bsegs).
    assert (ZN : 0x7fffa000 <= a < 0x10007fff8000).
    { destruct SC as [(a' & RR & ->)|(vv & Hv & RR)].
      - unfold shad, ASHOFF. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8. clear - RR ATR. Z.div_mod_to_equations. lia.
      - destruct (Op.TwinB.SHLIT_cases vv Hv) as [->|(_ & P1 & P2 & P3)]; [cbn [fst snd] in RR|]; lia. }
    apply (mjr_out m m' sp A0 len FRM MU a Ha). unfold sp, R in *. lia.
  -
    apply (AI_frame AI L RNG sta LBa m (mjoinR A0 (A0 + len) m m') _ AH (mjr_munch m m' sp (CtrPre.TwinB.sp_lo E st) A0 len FRM MU LO3 DR) (mjr_wmono m m' A0 len WM)).
    repeat (apply Forall_cons; [cbn [fst snd]|]); [| apply Forall_nil]. left. left. fold sp. lia.
  - exact ACj.
  -
    intros b x Hb FK Hx. pose proof (Op.TwinB.blk_band AI AI_fake L RNG sta LBa m b x AH Hb) as BB.
    destruct (AI_fake L RNG sta LBa m b AH Hb FK) as (_ & _ & _ & _ & SZ64 & _). specialize (BB ltac:(lia)).
    apply (mjr_out m m' sp A0 len FRM MU x); unfold AIMG_HI, KLS in *; lia.
  -
    apply (Op.TwinB.twins_pres_band AI L RNG sta LBa m (mjoinR A0 (A0 + len) m m') AH). intros a Ha.
    assert (SA : shad ATOP = ASHOFF + ATOP / 8) by (unfold shad; rewrite Z.shiftr_div_pow2 by lia; reflexivity).
    rewrite SA in Ha. unfold ASHOFF in Ha.
    apply (mjr_out m m' sp A0 len FRM MU a); [clear - Ha ATR; Z.div_mod_to_equations; lia| unfold sp, R in *; clear - Ha ATR LO3 FRMok; Z.div_mod_to_equations; lia].
  - exact OTH.
  - exact MIj.
  - exact (fun P => P).
Qed.

Lemma phaseA_ms : forall st E ms mo r hargs wnl st1 (L : alayout) (RNG : footprint) (sta : astate) (LBa : list ablock) (aw : word)
    (m' : amem) (R' : bvmap 5 word) (mo' : Model) (A0 len FRM : Z) (v : sv) (nx' : int),
  st_ok bsegs OPS E st ms mo -> call_pre st = Some r -> forget_stack_below_sp_g st = Some st1 ->
  CtrPre.TwinB.acallG AI ACCT UNIV Cw E st ms mo r hargs wnl L RNG sta LBa aw -> AHEAP AI L RNG sta LBa (ms_mem ms) ->
  let R := ms_regs ms in let sp := bv_unsigned (AP.getr R 2) in
  ATOP + 4096 <= CtrPre.TwinB.sp_lo E st -> CtrPre.TwinB.sp_lo E st <= sp - 4096 -> sp < 2 ^ 47 -> 0 <= A0 -> (A0 + len <= ATOP \/ sp <= A0) ->
  0 < FRM <= 4096 ->
  munch [(sp - FRM, sp); (A0, A0 + len)]%Z (ms_mem ms) m' -> wmono bsegs (ms_mem ms) m' ->
  AM.mem_inv bsegs (ms_mem ms) -> AM.mem_inv bsegs m' -> stk bsegs m' (CtrPre.TwinB.sp_lo E st) sp ->
  (forall rg, In rg CtrFrame.TwinB.kept_regsA -> AP.getr R' rg = AP.getr R rg) ->
  let Fv := CtrFree.TwinB.cfvF R' in let Gv := fun (_ _ : Z) => Z_to_bv 8 0 in
  den (CtrFrame.TwinB.E' E st Fv Gv) v = AP.getr R' 10%bv ->
  OTHER mo mo' -> op_minv OPS mo' -> ACCT aw L RNG sta LBa mo' ->
  st_ok bsegs OPS (CtrFrame.TwinB.E' E st Fv Gv)
    (SS r (rf_set (s_rf (clobber st1)) X10 v) (s_ff st) (s_resv st) (s_regs st1) (s_facts st) (s_ops st) (s_priv st) nx')
    (CtrFrame.TwinB.ms' ms r R' (mjoinR A0 (A0 + len) (ms_mem ms) m')) mo'.
Proof.
  intros st E ms mo r hargs wnl st1 L RNG sta LBa aw m' R' mo' A0 len FRM v nx' HS CP FS CF AH R sp BOT LO SPT A00 AHI FRMok.
  apply (phaseA_ms_g st E ms mo r hargs wnl st1 L RNG sta LBa aw m' R' mo' A0 len FRM v nx' HS CP FS CF AH BOT LO SPT A00 AHI). fold R sp. lia.
Qed.

Lemma st_ok_mem_ext_g : forall E st ms mo (m' : amem),
  (forall x, m' x = ms_mem ms x) -> st_ok bsegs OPS E st ms mo -> st_ok bsegs OPS E st (ms_with_mem ms m') mo.
Proof.
  intros E st ms mo m' EQ HS.
  pose proof HS as [Ppc Px0 Pregs Pfregs Psvc Presv Pfcsr Prom Pz Pbst Preg Pdisj Ppub Pfacts Pops Papart Pmf Pcov Pminv].
  assert (RB : forall a, 0 <= a < two64 -> rb bsegs m' a = rb bsegs (ms_mem ms) a) by (intros a _; unfold rb; rewrite EQ; reflexivity).
  assert (WB : forall a, 0 <= a < two64 -> wb bsegs (ms_mem ms) a = true -> wb bsegs m' a = true).
  { intros a _. unfold wb, wview. rewrite EQ. exact (fun H => H). }
  split; cbn [ms_with_mem ms_upd ms_regs ms_fregs ms_pc_val ms_svc_pending ms_resv ms_fcsr ms_mem ms_rom core_of c_regs c_fregs c_pc c_fcsr c_resv] in *;
    try assumption; try reflexivity.
  - intros k r0 Hk. exact (MemFX.MemFX.region_ok_view_frame bsegs _ _ (ms_mem ms) m' k r0 (Preg k r0 Hk) RB WB).
  - apply Forall_forall. intros o Ho. pose proof (proj1 (Forall_forall _ _) Pops o Ho) as OH.
    apply (St.op_frame OPS _ _ (ms_mem ms) m' mo); [intros a _ _; symmetry; apply EQ| intros a _ H; rewrite EQ; exact H| exact OH].
  - intros a b Hab. rewrite EQ in Hab. exact (Pminv a b Hab).
Qed.

Lemma byte_eq : forall c, Z_to_bv 8 (bv_unsigned (wbv c) mod 256) = Z_to_bv 8 (to_Z (PrimInt63.land (wl c) 255%uint63)).
Proof.
  intros c. f_equal. rewrite wbv_unsigned. pose proof (ValP.land_mk (wl c) 8%uint63 ltac:(change (to_Z 8%uint63) with 8; lia)) as LM.
  change (PrimInt63.sub (PrimInt63.lsl 1 8) 1)%uint63 with 255%uint63 in LM. rewrite LM. change (2 ^ to_Z 8%uint63) with 256.
  unfold w2Z. destruct (wt c); [| reflexivity]. unfold two63. rewrite <- (Z.add_mod_idemp_l 9223372036854775808) by lia.
  change (9223372036854775808 mod 256) with 0. reflexivity.
Qed.

Lemma amemset_leaf_ok : MemsetSound.TwinB.amemset_leaf AI ACCT UNIV Cw OPS OTHER MP PB.
Proof.
  unfold MemsetSound.TwinB.amemset_leaf.
  intros st sts K E ms mo r hargs wnl st1 kd od c n L RNG sta LBa aw HS HPB HK PRE G10 G11 G12 WTN NR SB CP FS CF AH MI BOT LO SPT
         LOWA HI47 POS EA0 EA2 EA1 ms' mo' HQ HMP' HMI' OTH ACP.
  set (R := ms_regs ms) in *. set (len := to_Z (wl n)) in *. set (A0 := bv_unsigned (ev E kd) + w2Zs od) in *.
  destruct HQ as (t0 & t1 & t2 & a1' & a2' & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & m' & EMS & MU & WM & MINV' & STK' & DSTP).
  rewrite EA0, EA2 in MU, DSTP.
  pose proof atop_range as ATR.
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
  idtac "ML-1".
  pose proof (HeapCtr.TwinB.fresh_ok_inv st FOK) as (SVB & _).
  assert (VBd : sv_vars_below (s_next st) (VP kd od) = true).
  { unfold st_vars_below in SVB. do 5 (apply andb_prop in SVB as [SVB _]). rewrite <- G10. exact (PlanS.rf_allb_get _ _ _ SVB X10). }
  assert (DVP : den E' (VP kd od) = AP.getr R' 10%bv).
  { unfold E'. rewrite (CtrFrame.TwinB.den_E' E st Fv Gv _ VBd), <- G10. symmetry. exact (GlueA.TwinB.getr_RA bsegs OPS E st ms mo HS X10). }
  assert (DA0 : bv_unsigned (den E' (VP kd od)) = A0) by (rewrite DVP; exact EA0).

  pose proof (phaseA_ms st E ms mo r hargs wnl st1 L RNG sta LBa aw m' R' mo' A0 len 2224 (VP kd od) (s_next (clobber st1)) HS CP FS CF AH BOT LO SPT
                ltac:(unfold AIMG_HI in *; lia) POS ltac:(lia) MU WM MI MINV' STK'
                ltac:(intros rg Hrg; unfold CtrFrame.TwinB.kept_regsA in Hrg; cbn [In] in Hrg; repeat (destruct Hrg as [<-|Hrg]; [reflexivity|]); destruct Hrg)
                DVP OTH HMI' ACP) as HSA.
  fold Fv Gv E' in HSA.

  assert (SH2 : setpc (setr (clobber st1) X10 (VP kd od)) r
              = SS r (rf_set (s_rf (clobber st1)) X10 (VP kd od)) (s_ff st) (s_resv st) (s_regs st1) (s_facts st) (s_ops st) (s_priv st) (s_next (clobber st1))).
  { rewrite <- FF1, <- RV1, <- FS1, <- OP1, <- PV1, <- FF, <- RV, <- RG, <- FS0, <- OP, <- PV. destruct (clobber st1); reflexivity. }
  unfold set_bytes_post in SB. rewrite SH2 in SB.
  match type of SB with match ?sbx with _ => _ end = _ => destruct sbx as [stn|] eqn:SBY; [|discriminate SB] end. injection SB as <-.
  set (b := PrimInt63.land (wl c) 255%uint63) in *.
  assert (Hb : 0 <= to_Z b < 256).
  { unfold b. pose proof (ValP.land_mk (wl c) 8%uint63 ltac:(change (to_Z 8%uint63) with 8; lia)) as LM.
    change (PrimInt63.sub (PrimInt63.lsl 1 8) 1)%uint63 with 255%uint63 in LM. rewrite LM. change (2 ^ to_Z 8%uint63) with 256. apply Z.mod_pos_bound. lia. }
  destruct (MemsetFX.TwinB.MemsetFX.set_bytes_sound bsegs OPS _ 0%uint63 (VP kd od) (wl od) b (wl n) _ stn E' _ mo' HSA RVN eq_refl SBY Hb
              ltac:(change (to_Z 0%uint63) with 0; fold len; lia) ltac:(rewrite DA0; fold len; unfold two64; lia))
    as (mc & HSc & FRc & INc & MONOc & _).
  rewrite DA0 in FRc, INc. fold len in FRc, INc. change (to_Z 0%uint63) with 0 in FRc, INc. cbn [ms_mem CtrFrame.TwinB.ms'] in FRc.
  idtac "ML-2".

  assert (DSTB : forall j, 0 <= j < len -> m' (Z_to_bv 64 (A0 + j)) = Some (Z_to_bv 8 (to_Z b))).
  { intros j Hj. apply raw_of_view; [unfold AIMG_HI, ATOP in *; lia|].
    destruct DSTP as [[_ (_ & _ & BY)] _]. rewrite (GlueA.TwinB.rb_mrdA bsegs).
    replace (A0 + j) with (A0 + Z.of_nat (Z.to_nat j)) by lia.
    rewrite (BY (Z.to_nat j)).
    - cbn [cells_bytes cbytes]. rewrite app_nil_r. rewrite nth_error_repeat by lia. f_equal. rewrite EA1. unfold b. apply byte_eq.
    - cbn [cells_bytes cbytes]. rewrite app_nil_r, repeat_length. lia. }
  idtac "ML-3".

  assert (PW : forall x, m' x = mc x).
  { intros x. pose proof (bv_unsigned_in_range _ x) as RX. unfold bv_modulus in RX.
    assert (EX : Z_to_bv 64 (bv_unsigned x) = x) by apply Z_to_bv_bv_unsigned.
    destruct (in_rng A0 (A0 + len) (bv_unsigned x)) eqn:IS.
    - unfold in_rng in IS. rewrite <- EX. replace (bv_unsigned x) with (A0 + (bv_unsigned x - A0)) by lia.
      rewrite (DSTB (bv_unsigned x - A0)) by lia. symmetry. apply INc. lia.
    - unfold in_rng in IS. rewrite <- EX. rewrite (FRc (bv_unsigned x)); [| unfold two64; lia | lia].
      symmetry. apply (mjr_final (ms_mem ms) m' A0 len (bv_unsigned x)); lia. }
  idtac "ML-4".
  pose proof (st_ok_mem_ext_g E' stn (ms_with_mem (CtrFrame.TwinB.ms' ms r R' (mjoinR A0 (A0 + len) (ms_mem ms) m')) mc) mo' m' PW HSc) as HSF.
  apply (HK stn ltac:(left; reflexivity) E' ms' mo' (CtrFrame.TwinB.EXT E st Fv Gv) HMP').
  rewrite EMS'. exact HSF.
Qed.
End Leaf.
End TwinB.
