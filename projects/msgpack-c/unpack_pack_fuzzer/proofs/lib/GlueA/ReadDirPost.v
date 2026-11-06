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
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require I_asan_memcpy0. From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require F_syscalls.
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
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Bridge Require Import Actr.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX Require Import W64Proofs ValProofs MemProofs StepSoundBase.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Br Require Import CtrFX.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Br Require HeapCtr HeapCtrB MemFX.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Bridge Require CallA GlueA CtrPre CtrFrame CtrNoDelta CtrNull CtrFree.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.GlueA Require UnreggGeo UnreggPre.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.GlueA Require Import ReadC ReadDirC ReadPre MemOps ReadSound ReadPost ReadDirSound.
Import ValP MemP CtrFX ActrA ReadC ReadDirC.
Module AM := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Mem.
Module CS := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Glue.CtrSys.CtrSys.

Lemma set_op_same : forall id os args, find_op id os = Some args -> set_op id args os = os.
Proof.
  intros id os. induction os as [|o os IH]; intros args H; cbn [find_op set_op] in *; [discriminate H|].
  destruct (PrimInt63.eqb (op_id o) id) eqn:Q.
  - injection H as <-. apply Uint63.eqb_correct in Q. destruct o as [oi oa]; cbn [op_id op_args] in *. subst oi. reflexivity.
  - f_equal. exact (IH args H).
Qed.
Lemma set_ops_self : forall st, set_ops st (s_ops st) = st.
Proof. intros [pc x ff rv R fs os pv nx]. reflexivity. Qed.
Lemma setpc_set_ops : forall st os pc, setpc (set_ops st os) pc = set_ops (setpc st pc) os.
Proof. intros [p x ff rv R fs os0 pv nx] os pc. reflexivity. Qed.

Lemma errno_havoc_keeps : forall st2 stE, errno_havoc st2 = Some stE ->
  s_facts stE = s_facts st2 /\ s_ops stE = s_ops st2 /\ s_priv stE = s_priv st2 /\ s_ff stE = s_ff st2 /\ s_rf stE = s_rf st2.
Proof.
  intros st2 stE H. destruct (CtrNull.errno_havoc_inv _ _ H) as (r0 & _ & _ & ->). cbn [s_facts s_ops s_priv s_ff s_rf]. repeat split; reflexivity.
Qed.

Lemma s_ops_setr : forall s rd v, s_ops (setr s rd v) = s_ops s.      Proof. intros s rd v. destruct rd; reflexivity. Qed.
Lemma s_facts_setr : forall s rd v, s_facts (setr s rd v) = s_facts s.  Proof. intros s rd v. destruct rd; reflexivity. Qed.
Lemma s_priv_setr : forall s rd v, s_priv (setr s rd v) = s_priv s.    Proof. intros s rd v. destruct rd; reflexivity. Qed.

Lemma AERRNO_eq : AERRNO = ERRNO.
Proof. vm_compute. reflexivity. Qed.

Section Leaf.
Context {rc : runConstT}.

Lemma rawv : forall (m m' : amem) a, m' (AM.wa a) = m (AM.wa a) ->
  rb asegs m' a = rb asegs m a /\ (wb asegs m a = true -> wb asegs m' a = true).
Proof.
  intros m m' a EQ. unfold AM.wa in EQ. split; [exact (ReadPost.rb_ext m m' a EQ)|]. intros Wb. rewrite (ReadPost.wb_ext m m' a EQ). exact Wb.
Qed.

Lemma mj_errno_cells : forall (m m' : amem) (e : word),
  AS.rw_cells asegs m' ERRNO [C4 e] -> AS.rw_cells asegs (mjoin m m') ERRNO [C4 e].
Proof.
  intros m m' e H.
  apply (rw_cells_transport asegs [(STAGE, STAGE + 65536)]%Z m' (mjoin m m') ERRNO [C4 e] H).
  - intros x Hout. unfold mjoin. destruct (in_stage (bv_unsigned x)) eqn:IS; [| reflexivity].
    exfalso. unfold in_stage in IS. cbn [outside] in Hout. lia.
  - intros x Hx. destruct (in_stage (bv_unsigned x)) eqn:IS.
    + rewrite <- (Z_to_bv_bv_unsigned x). apply (proj1 (GlueA.wb_wviewA asegs (mjoin m m') (bv_unsigned x))). apply stage_wb_any. unfold in_stage in IS. lia.
    + assert (E0 : mjoin m m' x = m' x) by (unfold mjoin; rewrite IS; reflexivity). rewrite (ReadPost.wview_ext m' (mjoin m m') x E0). exact Hx.
  - cbn [cells_size csize Nat.add disjoint_from]. split; [unfold ERRNO, STAGE; lia| exact I].
Qed.

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

Hypothesis AERRNO_aci : forall LB SP, aclient_range (aci AI) LB SP AERRNO 4.
Hypothesis ACI_errno : exists iv0, In iv0 (aci AI) /\ fst iv0 <= ERRNO /\ ERRNO + 4 <= snd iv0.
Hypothesis ACI_stage : exists iv0, In iv0 (aci AI) /\ fst iv0 <= STAGE /\ STAGE + 65536 <= snd iv0.

Variable file : list byte.
Hypothesis OPS_holds_rstage : forall args m mo, op_holds OPS ReadC.RSTV_ID args m mo -> rstage_holds_v file args m.
Hypothesis OPS_holds_rstage' : forall args m mo, rstage_holds_v file args m -> op_holds OPS ReadC.RSTV_ID args m mo.
Hypothesis OPS_fp_nostage : forall id args a, id <> ReadC.RSTV_ID -> Exists (fun iv => fst iv <= a < snd iv) (op_fp OPS id args) ->
  ~ (STAGE <= a < STAGE + 65536).
Hypothesis OPS_cov1_heap : forall id args z, op_cov1 OPS id args z -> id = HEAP_ID.

Lemma aci_low'' : forall a, in_ranges (aci AI) a -> a < AIMG_HI.
Proof. intros a (iv0 & Hi & RR). pose proof (AI_aci_img AI iv0 Hi). lia. Qed.

Lemma phaseA_dir : forall st E ms mo r hargs wnl st1 (L : alayout) (RNG : footprint) (sta : astate) (LBa : list ablock) (aw : word)
    (m' : amem) (R' : bvmap 5 word) (mo' : Model) (errv e' : word) (n : Z) (v : sv) (stE : sstate),
  st_ok asegs OPS E st ms mo -> call_pre st = Some r -> forget_stack_below_sp_g st = Some st1 ->
  CtrPre.acallG AI ACCT UNIV Cw E st ms mo r hargs wnl L RNG sta LBa aw -> AHEAP AI L RNG sta LBa (ms_mem ms) ->
  let R := ms_regs ms in let sp := bv_unsigned (AP.getr R 2) in
  ATOP + 4096 <= CtrPre.sp_lo E st -> CtrPre.sp_lo E st <= sp - 4096 -> sp < 2 ^ 47 -> 0 < n <= 65536 ->
  munch [(sp - 2208, sp); (STAGE, STAGE + n); (ERRNO, ERRNO + 4)]%Z (ms_mem ms) m' -> wmono asegs (ms_mem ms) m' ->
  AM.mem_inv asegs (ms_mem ms) -> AM.mem_inv asegs m' -> stk asegs m' (CtrPre.sp_lo E st) sp ->
  AS.rw_cells asegs (ms_mem ms) ERRNO [C4 errv] -> AS.rw_cells asegs m' ERRNO [C4 e'] ->
  (forall rg, In rg CtrFrame.kept_regsA -> AP.getr R' rg = AP.getr R rg) ->
  let Fv := CtrNull.cfvE R' e' in let Gv := fun (_ _ : Z) => Z_to_bv 8 0 in
  den (CtrFrame.E' E st Fv Gv) v = AP.getr R' 10%bv ->
  errno_havoc (setr (clobber st1) X10 v) = Some stE ->
  OTHER mo mo' -> op_minv OPS mo' -> ACCT aw L RNG sta LBa mo' ->
  st_ok asegs OPS (CtrFrame.E' E st Fv Gv) (setpc stE r) (CtrFrame.ms' ms r R' (mjoin (ms_mem ms) m')) mo'.
Proof.
  intros st E ms mo r hargs wnl st1 L RNG sta LBa aw m' R' mo' errv e' n v stE HS CP FS CF AH R sp BOT LO SPT Hn MU WM MI MI' STK' ERR0 ERR1 KEPT Fv Gv DV HAV OTH MIj ACj.
  pose proof atop_range as ATR.
  assert (LO3 : ATOP + 4096 <= CtrPre.sp_lo E st /\ CtrPre.sp_lo E st <= sp - 4096 /\ sp < 2 ^ 47) by lia.
  set (m := ms_mem ms) in *.
  pose proof CF as CF0.
  destruct CF0 as (LB_ & ks & offs & rss & ksp & nn & md & A & nw & rest & SPR & Hksp & SPE & K16 & LOSP & FLOOR & Hf & Hc & Eh & Tnw & Nn & Ln & N255
                   & NW & AN & AJ & TS & WF & HC & AWden & WIT).
  destruct (HeapCtr.call_pre_inv st r CP) as (FOK & _).
  assert (IUOUT : forall LB0, aw_real AI ACCT UNIV aw LB0 m mo L RNG sta LBa -> forall a, 0 <= a < 2 ^ 64 -> in_user LB0 a ->
            mjoin m m' (AM.wa a) = m (AM.wa a)).
  { intros LB0 AR0 a Ha IU. pose proof (UnreggGeo.user_out AI ACCT UNIV AI_fake aw LB0 m mo L RNG sta LBa a AR0 IU) as G.
    apply (mj_out m m' sp (CtrPre.sp_lo E st) n MU LO3 Hn a Ha); unfold ERRNO, AIMG_HI, KLS in *; lia. }
  assert (HSA : heap_set_A hargs A = Some hargs) by (rewrite Eh; reflexivity).
  assert (DCN : den (CtrFrame.E' E st Fv Gv) A = aw).
  { rewrite (CtrFrame.den_E' E st Fv Gv A (CtrFrame.A_below st FOK rest hargs md A nw Hf Eh)). symmetry. exact AWden. }
  assert (OPSE : s_ops stE = s_ops st).
  { destruct (errno_havoc_keeps _ _ HAV) as (_ & O & _). rewrite O, s_ops_setr.
    destruct (clobber_fields st1) as (_ & _ & _ & _ & _ & OP & _). rewrite OP.
    destruct (CtrFrame.st1_fields st st1 FS) as (_ & _ & _ & _ & _ & OP1 & _). exact OP1. }
  assert (GOALEQ : setpc (set_ops stE (set_op HEAP_ID hargs (s_ops stE))) r = setpc stE r).
  { rewrite OPSE, (set_op_same HEAP_ID (s_ops st) hargs Hf), <- OPSE, set_ops_self. reflexivity. }
  rewrite <- GOALEQ.
  apply (CtrNull.nodelta_errno_st_ok AI IMGX IMGX_aci ACCT UNIV Cw OPS AI_fake OPS_holds1 OPS_fp1 OPS_cov1 OPS_frame_other OPS_fp_other OTHER OPS_mo_other
           OPS_cov0_img AERRNO_aci E st ms mo r hargs wnl L RNG sta LBa aw st1 Fv Gv R' (mjoin m m') mo' RNG sta v A hargs aw errv e' stE
           HS CP FS (CtrNull.acallN_of_G AI ACCT UNIV Cw E st ms mo r hargs wnl L RNG sta LBa aw CF) HSA DCN HAV KEPT).
  - intros x i Hx. exact (CtrNull.cfvE_clob R' e' x i Hx).
  - exact DV.
  - reflexivity.
  - rewrite AERRNO_eq. exact ERR0.
  - rewrite AERRNO_eq. exact (mj_errno_cells m m' e' ERR1).
  - exact (mj_mem_inv m m' MI MI').
  - exact (mj_stk m m' sp (CtrPre.sp_lo E st) LO3 STK').
  - exact BOT.
  -
    intros LB0 AR0 a Ha STB NE. apply rawv. destruct STB as [S1|[S2|S3]].
    + apply (mj_out m m' sp (CtrPre.sp_lo E st) n MU LO3 Hn a Ha); unfold ERRNO, sp, R in *; lia.
    + pose proof (aci_low'' a S2) as AL. unfold CtrNull.in_errno in NE. rewrite AERRNO_eq in NE.
      apply (mj_out m m' sp (CtrPre.sp_lo E st) n MU LO3 Hn a Ha); unfold ERRNO, AIMG_HI in *; lia.
    + exact (IUOUT LB0 AR0 a Ha S3).
  -   exact IUOUT.
  -
    intros o a Ho NI Ha NE FP. unfold not_id in NI. apply Uint63.eqb_false_spec in NI. unfold CtrNull.in_errno in NE. rewrite AERRNO_eq in NE.
    destruct (OPS_fp_other _ _ a NI FP) as [INA|[(a' & INA & ->)|(a' & STK & ->)]].
    + pose proof (aci_low'' a INA) as AL.
      apply (mj_out m m' sp (CtrPre.sp_lo E st) n MU LO3 Hn a); [unfold two64 in Ha; lia| unfold AIMG_HI in *; lia | exact NE].
    + pose proof (aci_low'' a' INA) as AL. destruct INA as (iv0 & I0 & I1). pose proof (AI_aci_lo AI iv0 I0) as A0.
      pose proof (CtrPre.shad_img_band a' ltac:(lia)) as BND.
      apply (mj_out m m' sp (CtrPre.sp_lo E st) n MU LO3 Hn (shad a')); [unfold two64 in Ha; lia| lia | exact NE].
    + assert (ZN : 0x7fffa000 <= shad a' < 0x10007fff8000) by (unfold shad, ASHOFF; rewrite Z.shiftr_div_pow2 by lia; change (2 ^ 3) with 8; clear - STK ATR; Z.div_mod_to_equations; lia).
      apply (mj_out m m' sp (CtrPre.sp_lo E st) n MU LO3 Hn (shad a')); [unfold two64 in Ha; lia| lia | exact NE].
  -   intros a Ha _ Wb. apply (GlueA.wb_wviewA asegs). apply (GlueA.wb_wviewA asegs) in Wb. exact (mj_wmono m m' WM _ Wb).
  -
    intros a Ha SC _. apply rawv.
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
  - exact (fun _ P => P).
Qed.

Lemma phaseB_dir : forall st E ms mo r hargs wnl st1 (L : alayout) (RNG : footprint) (sta : astate) (LBa : list ablock) (aw : word)
    (m' : amem) (R' : bvmap 5 word) (mo' : Model) (n : Z) (junk : list byte) (stE : sstate) (E' : env),
  st_ok asegs OPS E st ms mo -> call_pre st = Some r -> forget_stack_below_sp_g st = Some st1 ->
  CtrPre.acallG AI ACCT UNIV Cw E st ms mo r hargs wnl L RNG sta LBa aw -> AHEAP AI L RNG sta LBa (ms_mem ms) ->
  let R := ms_regs ms in let sp := bv_unsigned (AP.getr R 2) in
  ATOP + 4096 <= CtrPre.sp_lo E st -> CtrPre.sp_lo E st <= sp - 4096 -> sp < 2 ^ 47 -> 0 < n <= 65536 ->
  munch [(sp - 2208, sp); (STAGE, STAGE + n); (ERRNO, ERRNO + 4)]%Z (ms_mem ms) m' -> wmono asegs (ms_mem ms) m' ->
  AS.rw_cells asegs (ms_mem ms) STAGE [CB (Z.to_nat n) junk] -> AS.rw_cells asegs m' STAGE [CB (Z.to_nat n) junk] ->
  (forall a, sv_vars_below (s_next st) a = true -> den E' a = den E a) ->
  errno_havoc (setr (clobber st1) X10 MINUS1) = Some stE ->
  st_ok asegs OPS E' (setpc stE r) (CtrFrame.ms' ms r R' (mjoin (ms_mem ms) m')) mo' ->
  CtrS.priv_has st 6275344%uint63 CtrS.STAGE_LEN = true ->
  ACCT aw L RNG sta LBa mo' ->
  st_ok asegs OPS E' (setpc stE r) (CtrFrame.ms' ms r R' m') mo'.
Proof.
  intros st E ms mo r hargs wnl st1 L RNG sta LBa aw m' R' mo' n junk stE E' HS CP FS CF AH R sp BOT LO SPT Hn MU WM STG STGP DENE HAV HSj PRIV ACj.
  pose proof atop_range as ATR.
  assert (LO3 : ATOP + 4096 <= CtrPre.sp_lo E st /\ CtrPre.sp_lo E st <= sp - 4096 /\ sp < 2 ^ 47) by lia.
  set (m := ms_mem ms) in *.

  destruct (errno_havoc_keeps _ _ HAV) as (KF & KO & KP & _).
  destruct (clobber_fields st1) as (_ & FF & RV & RG & FS0 & OP & PV & NXc).
  destruct (CtrFrame.st1_fields st st1 FS) as (_ & _ & FF1 & RV1 & FS1 & OP1 & PV1 & NX1).
  assert (PCF : forall s pc, s_facts (setpc s pc) = s_facts s /\ s_ops (setpc s pc) = s_ops s /\ s_priv (setpc s pc) = s_priv s) by (intros [? ? ? ? ? ? ? ? ?] pc; repeat split; reflexivity).
  destruct (PCF stE r) as (PF & PO & PP).
  assert (HF : s_facts (setpc stE r) = s_facts st) by (rewrite PF, KF, s_facts_setr; rewrite FS0; exact FS1).
  assert (HO : s_ops (setpc stE r) = s_ops st) by (rewrite PO, KO, s_ops_setr; rewrite OP; exact OP1).
  assert (HP : s_priv (setpc stE r) = s_priv st) by (rewrite PP, KP, s_priv_setr; rewrite PV; exact PV1).
  change (CtrFrame.ms' ms r R' m') with (ms_with_mem (CtrFrame.ms' ms r R' (mjoin m m')) m').
  set (T := setpc stE r) in *.
  replace T with (SS (s_pc T) (s_rf T) (s_ff T) (s_resv T) (s_regs T) ([] ++ s_facts T) (s_ops T) (s_priv T) (s_next T)) by (destruct T; reflexivity).
  apply (st_ok_memops asegs OPS E' T _ mo' mo' [] (s_ops T) (s_next T) m' HSj (Forall_nil _) (so_mf _ _ _ _ _ _ HSj)).
  -   unfold ops_hold. apply Forall_forall. intros o Ho. rewrite HO in Ho.
    destruct (PrimInt63.eqb (op_id o) HEAP_ID) eqn:QH.
    +
      apply Uint63.eqb_correct in QH.
      destruct CF as (LB & ks & offs & rss & ksp & nn & md & A & nw & rest & SPR & Hksp & SPE & K16 & LOSP & FLOOR & Hf & Hc & Eh & Tnw & Nn & Ln & N255
                      & NW & AN & AJ & TS & WF & HC & AWden & (W & WOF & ARW & TI)).
      destruct (HeapCtr.call_pre_inv st r CP) as (FOK & _).
      pose proof (count_one_args HEAP_ID (s_ops st) o hargs Ho QH Hc Hf) as EA.
      replace (op_id o) with HEAP_ID. rewrite EA.
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
        - rewrite E1, E4. exact ACj.
        - intros b x Hb FK Hx. rewrite E4 in Hb. pose proof (Op.blk_band AI AI_fake L RNG sta LBa m b x AH Hb Hx) as BB.
          apply (raw_out m m' sp (CtrPre.sp_lo E st) n MU LO3 Hn x); unfold STAGE, ERRNO, AIMG_HI, KLS in *; lia.
        - rewrite E4. apply (Op.twins_pres_band AI L RNG sta LBa m m' AH). intros a Ha.
          assert (SA : shad ATOP = ASHOFF + ATOP / 8) by (unfold shad; rewrite Z.shiftr_div_pow2 by lia; reflexivity).
          rewrite SA in Ha. unfold ASHOFF in Ha.
          apply (raw_out m m' sp (CtrPre.sp_lo E st) n MU LO3 Hn a); unfold STAGE, ERRNO in *; clear - Ha ATR LO3 Hn; Z.div_mod_to_equations; lia. }
      assert (TI' : ties W' (wins_of E nn rest)) by (apply (ties_ext W W'); [reflexivity| intros b; reflexivity| reflexivity| exact TI| intros b _ V; exact V| intros P; unfold W'; cbn [w_st]; rewrite <- (proj1 (proj2 (proj2 WOF))); exact P]).
      assert (DECN0 : decode (map (den E) hargs) = Some (w2Z md, den E A, wins_of E nn rest, map (den E) (skipn (3 * nn) rest))).
      { rewrite Eh. exact (decode_hargs E md A nw rest nn Tnw Nn Ln). }
      assert (MAPE : map (den E') hargs = map (den E) hargs).
      { apply map_ext_in. intros a Ha. apply DENE.
        pose proof (HeapCtr.fresh_ok_inv st FOK) as (SVB & _).
        exact (ops_args_below (s_next st) st o a SVB Ho ltac:(rewrite EA; exact Ha)). }
      rewrite OPS_holds1, MAPE. exists (w2Z md), aw, (wins_of E nn rest), (map (den E) (skipn (3 * nn) rest)), LB, W'.
      split; [rewrite AWden; exact DECN0|]. split; [exact (proj1 AR')|]. split; [exact WF|]. split; [| exact TI'].
      apply (cw_frame Cw _ _ _ _ m m' HC). intros a Ha U _. symmetry. unfold AM.wa in SBU.
      apply (SBU a ltac:(unfold two64 in Ha; lia)). exact U.
    + apply Uint63.eqb_false_spec in QH.
      pose proof (proj1 (Forall_forall _ _) (so_ops _ _ _ _ _ _ HSj) o ltac:(rewrite HO; exact Ho)) as HOj. cbv beta in HOj. cbn [ms_mem CtrFrame.ms'] in HOj.
      destruct (PrimInt63.eqb (op_id o) ReadC.RSTV_ID) eqn:QR.
      *
        apply Uint63.eqb_correct in QR. rewrite QR in HOj |- *.
        apply OPS_holds_rstage'. pose proof (OPS_holds_rstage _ _ _ HOj) as RH.
        change (ms_mem (CtrFrame.ms' ms r R' (mjoin m m'))) with (mjoin m m') in RH.
        destruct (map (den E') (op_args o)) as [|off [|nv [|? ?]]]; cbn [rstage_holds_v] in RH |- *; try exact RH.
        destruct RH as (B1 & B2 & BY). split; [exact B1|]. split; [exact B2|]. intros i Hi. rewrite <- (BY i Hi).
        destruct (Z_lt_le_dec i n) as [IN|OUT].
        --
           destruct STG as [[WFm (_ & _ & BYm)] _]. destruct STGP as [[_ (_ & _ & BYm')] _].
           assert (LJ : length junk = Z.to_nat n) by (cbn [cells_wf cell_wf] in WFm; exact (proj1 WFm)).
           assert (LCB : length (cells_bytes [CB (Z.to_nat n) junk]) = Z.to_nat n) by (cbn [cells_bytes cbytes]; rewrite app_nil_r; exact LJ).
           assert (EJ : mjoin m m' (Z_to_bv 64 (STAGE + i)) = m (Z_to_bv 64 (STAGE + i))).
           { unfold mjoin. rewrite Z_to_bv_unsigned, bv_wrap_small by (rewrite bv_modulus_64; unfold W64.two64, STAGE; lia).
             replace (in_stage (STAGE + i)) with true by (unfold in_stage; symmetry; apply andb_true_intro; split; [apply Z.leb_le| apply Z.ltb_lt]; lia). reflexivity. }
           rewrite (ReadPost.rb_ext m (mjoin m m') (STAGE + i) EJ). rewrite !(GlueA.rb_mrdA asegs).
           replace (STAGE + i) with (STAGE + Z.of_nat (Z.to_nat i)) by lia.
           rewrite (BYm (Z.to_nat i)) by (rewrite LCB; lia). rewrite (BYm' (Z.to_nat i)) by (rewrite LCB; lia). reflexivity.
        --
           assert (EJ : mjoin m m' (Z_to_bv 64 (STAGE + i)) = m' (Z_to_bv 64 (STAGE + i))).
           { unfold mjoin. rewrite Z_to_bv_unsigned, bv_wrap_small by (rewrite bv_modulus_64; unfold W64.two64, STAGE; lia).
             destruct (in_stage (STAGE + i)); [| reflexivity]. symmetry.
             apply (raw_out m m' sp (CtrPre.sp_lo E st) n MU LO3 Hn (STAGE + i)); unfold STAGE, ERRNO in *; lia. }
           symmetry. exact (ReadPost.rb_ext m' (mjoin m m') (STAGE + i) EJ).
      *
        apply Uint63.eqb_false_spec in QR.
        apply (OPS_frame_other _ _ (mjoin m m') m' mo' QH HOj).
        -- intros a Ha FP. pose proof (OPS_fp_nostage _ _ a QR FP) as NS.
           apply (mj_final m m' a ltac:(unfold two64 in Ha; lia) NS).
        -- intros a Ha _ Wb. destruct (in_stage a) eqn:IS.
           ++ apply stage_wb_any. unfold in_stage in IS. lia.
           ++ rewrite <- (ReadPost.wb_ext m' (mjoin m m') a); [exact Wb|]. apply (mj_final m m' a ltac:(unfold two64 in Ha; lia)). unfold in_stage in IS. lia.
  -   exact (so_apart _ _ _ _ _ _ HSj).
  -   exact (so_cover _ _ _ _ _ _ HSj).
  -
    intros a Ha Hout. cbn [ms_mem CtrFrame.ms']. destruct (in_stage a) eqn:IS.
    + exfalso. unfold in_stage in IS. assert (SA : STAGE <= a < STAGE + 65536) by lia.
      destruct (MemP.abs_writable_sound asegs STAGE 65536 ltac:(unfold STAGE; lia) ltac:(lia) ltac:(vm_compute; reflexivity)) as [_ WB].
      destruct (WB (a - STAGE) ltac:(lia)) as [_ (seg & Hseg & _)]. replace (STAGE + (a - STAGE)) with a in Hseg by lia.
      destruct Hout as [Hn0 | Hnp]; [congruence|]. apply Hnp. rewrite HP.
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

Lemma aread_dir_leaf_ok : ReadDirSound.aread_dir_leaf AI ACCT UNIV Cw OPS OTHER MP PB.
Proof.
  unfold ReadDirSound.aread_dir_leaf.
  intros st K E ms mo r hargs wnl st1 stE cnt L RNG sta LBa aw junk errv HS HMP HPB HK PRE RPRE HAV ECNT WR CP FS CF AH BOT LO SPT TP MI STG ERR ZSH
         ms' mo' HQ MP' MI' OT' AC'.
  set (R := ms_regs ms) in *.
  destruct HQ as (_ & t0 & t1 & t2 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & m' & EMS & MU & WM & MINV' & STK' & STGP & ERRP & _).
  pose proof atop_range as ATR.
  assert (ETP : bv_unsigned (AP.getr R 4) + -164 = ERRNO) by (rewrite TP; vm_compute; reflexivity).
  rewrite ETP in MU, ERRP. rewrite Z2Nat.id in MU by lia.
  match type of EMS with ms' = MS ?RR _ _ _ _ _ _ => set (R' := RR) in * end.
  set (e' := Z_to_bv 64 EISDIR : word) in *.
  set (Fv := CtrNull.cfvE R' e'). set (Gv := fun (_ _ : Z) => Z_to_bv 8 0). set (E' := CtrFrame.E' E st Fv Gv).
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
  destruct (aread_dir_pre_inv st RPRE) as (_ & _ & PRIV & _ & _ & _ & _).
  apply (HK E' ms' mo' (CtrFrame.EXT E st Fv Gv) MP'). rewrite EMS'.
  apply (phaseB_dir st E ms mo r hargs wnl st1 L RNG sta LBa aw m' R' mo' cnt junk stE E' HS CP FS CF AH BOT LO SPT WR MU WM STG STGP).
  - intros a Ha. apply CtrFrame.den_E'. exact Ha.
  - exact HAV.
  - apply (phaseA_dir st E ms mo r hargs wnl st1 L RNG sta LBa aw m' R' mo' errv e' cnt MINUS1 stE HS CP FS CF AH BOT LO SPT WR MU WM MI MINV' STK' ERR ERRP).
    + intros rg Hrg. unfold CtrFrame.kept_regsA in Hrg. cbn [In] in Hrg. repeat (destruct Hrg as [<-|Hrg]; [reflexivity|]). destruct Hrg.
    +   cbn [den MINUS1 CtrS.errv]. subst R'. cbn [AP.getr]. unfold F_syscalls.read_ret. apply bv_eq. vm_compute. reflexivity.
    + exact HAV.
    + exact OT'.
    + exact MI'.
    + exact AC'.
  - exact PRIV.
  - exact AC'.
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
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import Actr.TwinB.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.W64Proofs OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.ValProofs OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.MemProofs OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.StepSoundBase.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Br.CtrFX.

Import ReadC.TwinB ReadDirC.TwinB ReadPre.TwinB MemOps.TwinB ReadSound.TwinB ReadPost.TwinB ReadDirSound.TwinB.
Import ValP MemP CtrFX ActrA ReadC.TwinB.ReadC ReadDirC.TwinB.ReadDirC.
Module AM := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Mem.
Module CS := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Glue.CtrSys.CtrSys.

Lemma set_op_same : forall id os args, find_op id os = Some args -> set_op id args os = os.
Proof.
  intros id os. induction os as [|o os IH]; intros args H; cbn [find_op set_op] in *; [discriminate H|].
  destruct (PrimInt63.eqb (op_id o) id) eqn:Q.
  - injection H as <-. apply Uint63.eqb_correct in Q. destruct o as [oi oa]; cbn [op_id op_args] in *. subst oi. reflexivity.
  - f_equal. exact (IH args H).
Qed.
Lemma set_ops_self : forall st, set_ops st (s_ops st) = st.
Proof. intros [pc x ff rv R fs os pv nx]. reflexivity. Qed.
Lemma setpc_set_ops : forall st os pc, setpc (set_ops st os) pc = set_ops (setpc st pc) os.
Proof. intros [p x ff rv R fs os0 pv nx] os pc. reflexivity. Qed.

Lemma errno_havoc_keeps : forall st2 stE, errno_havoc st2 = Some stE ->
  s_facts stE = s_facts st2 /\ s_ops stE = s_ops st2 /\ s_priv stE = s_priv st2 /\ s_ff stE = s_ff st2 /\ s_rf stE = s_rf st2.
Proof.
  intros st2 stE H. destruct (CtrNull.TwinB.errno_havoc_inv _ _ H) as (r0 & _ & _ & ->). cbn [s_facts s_ops s_priv s_ff s_rf]. repeat split; reflexivity.
Qed.

Lemma s_ops_setr : forall s rd v, s_ops (setr s rd v) = s_ops s.      Proof. intros s rd v. destruct rd; reflexivity. Qed.
Lemma s_facts_setr : forall s rd v, s_facts (setr s rd v) = s_facts s.  Proof. intros s rd v. destruct rd; reflexivity. Qed.
Lemma s_priv_setr : forall s rd v, s_priv (setr s rd v) = s_priv s.    Proof. intros s rd v. destruct rd; reflexivity. Qed.

Lemma AERRNO_eq : AERRNO = ERRNO.
Proof. vm_compute. reflexivity. Qed.

Section Leaf.
Context {rc : runConstT}.

Lemma rawv : forall (m m' : amem) a, m' (AM.wa a) = m (AM.wa a) ->
  rb bsegs m' a = rb bsegs m a /\ (wb bsegs m a = true -> wb bsegs m' a = true).
Proof.
  intros m m' a EQ. unfold AM.wa in EQ. split; [exact (ReadPost.TwinB.rb_ext m m' a EQ)|]. intros Wb. rewrite (ReadPost.TwinB.wb_ext m m' a EQ). exact Wb.
Qed.

Lemma mj_errno_cells : forall (m m' : amem) (e : word),
  AS.rw_cells bsegs m' ERRNO [C4 e] -> AS.rw_cells bsegs (mjoin m m') ERRNO [C4 e].
Proof.
  intros m m' e H.
  apply (rw_cells_transport bsegs [(STAGE, STAGE + 65536)]%Z m' (mjoin m m') ERRNO [C4 e] H).
  - intros x Hout. unfold mjoin. destruct (in_stage (bv_unsigned x)) eqn:IS; [| reflexivity].
    exfalso. unfold in_stage in IS. cbn [outside] in Hout. lia.
  - intros x Hx. destruct (in_stage (bv_unsigned x)) eqn:IS.
    + rewrite <- (Z_to_bv_bv_unsigned x). apply (proj1 (GlueA.TwinB.wb_wviewA bsegs (mjoin m m') (bv_unsigned x))). apply stage_wb_any. unfold in_stage in IS. lia.
    + assert (E0 : mjoin m m' x = m' x) by (unfold mjoin; rewrite IS; reflexivity). rewrite (ReadPost.TwinB.wview_ext m' (mjoin m m') x E0). exact Hx.
  - cbn [cells_size csize Nat.add disjoint_from]. split; [unfold ERRNO, STAGE; lia| exact I].
Qed.

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

Hypothesis AERRNO_aci : forall LB SP, aclient_range (aci AI) LB SP AERRNO 4.
Hypothesis ACI_errno : exists iv0, In iv0 (aci AI) /\ fst iv0 <= ERRNO /\ ERRNO + 4 <= snd iv0.
Hypothesis ACI_stage : exists iv0, In iv0 (aci AI) /\ fst iv0 <= STAGE /\ STAGE + 65536 <= snd iv0.

Variable file : list byte.
Hypothesis OPS_holds_rstage : forall args m mo, op_holds OPS ReadC.TwinB.ReadC.RSTV_ID args m mo -> rstage_holds_v file args m.
Hypothesis OPS_holds_rstage' : forall args m mo, rstage_holds_v file args m -> op_holds OPS ReadC.TwinB.ReadC.RSTV_ID args m mo.
Hypothesis OPS_fp_nostage : forall id args a, id <> ReadC.TwinB.ReadC.RSTV_ID -> Exists (fun iv => fst iv <= a < snd iv) (op_fp OPS id args) ->
  ~ (STAGE <= a < STAGE + 65536).
Hypothesis OPS_cov1_heap : forall id args z, op_cov1 OPS id args z -> id = HEAP_ID.

Lemma aci_low'' : forall a, in_ranges (aci AI) a -> a < AIMG_HI.
Proof. intros a (iv0 & Hi & RR). pose proof (AI_aci_img AI iv0 Hi). lia. Qed.

Lemma phaseA_dir : forall st E ms mo r hargs wnl st1 (L : alayout) (RNG : footprint) (sta : astate) (LBa : list ablock) (aw : word)
    (m' : amem) (R' : bvmap 5 word) (mo' : Model) (errv e' : word) (n : Z) (v : sv) (stE : sstate),
  st_ok bsegs OPS E st ms mo -> call_pre st = Some r -> forget_stack_below_sp_g st = Some st1 ->
  CtrPre.TwinB.acallG AI ACCT UNIV Cw E st ms mo r hargs wnl L RNG sta LBa aw -> AHEAP AI L RNG sta LBa (ms_mem ms) ->
  let R := ms_regs ms in let sp := bv_unsigned (AP.getr R 2) in
  ATOP + 4096 <= CtrPre.TwinB.sp_lo E st -> CtrPre.TwinB.sp_lo E st <= sp - 4096 -> sp < 2 ^ 47 -> 0 < n <= 65536 ->
  munch [(sp - 2208, sp); (STAGE, STAGE + n); (ERRNO, ERRNO + 4)]%Z (ms_mem ms) m' -> wmono bsegs (ms_mem ms) m' ->
  AM.mem_inv bsegs (ms_mem ms) -> AM.mem_inv bsegs m' -> stk bsegs m' (CtrPre.TwinB.sp_lo E st) sp ->
  AS.rw_cells bsegs (ms_mem ms) ERRNO [C4 errv] -> AS.rw_cells bsegs m' ERRNO [C4 e'] ->
  (forall rg, In rg CtrFrame.TwinB.kept_regsA -> AP.getr R' rg = AP.getr R rg) ->
  let Fv := CtrNull.TwinB.cfvE R' e' in let Gv := fun (_ _ : Z) => Z_to_bv 8 0 in
  den (CtrFrame.TwinB.E' E st Fv Gv) v = AP.getr R' 10%bv ->
  errno_havoc (setr (clobber st1) X10 v) = Some stE ->
  OTHER mo mo' -> op_minv OPS mo' -> ACCT aw L RNG sta LBa mo' ->
  st_ok bsegs OPS (CtrFrame.TwinB.E' E st Fv Gv) (setpc stE r) (CtrFrame.TwinB.ms' ms r R' (mjoin (ms_mem ms) m')) mo'.
Proof.
  intros st E ms mo r hargs wnl st1 L RNG sta LBa aw m' R' mo' errv e' n v stE HS CP FS CF AH R sp BOT LO SPT Hn MU WM MI MI' STK' ERR0 ERR1 KEPT Fv Gv DV HAV OTH MIj ACj.
  pose proof atop_range as ATR.
  assert (LO3 : ATOP + 4096 <= CtrPre.TwinB.sp_lo E st /\ CtrPre.TwinB.sp_lo E st <= sp - 4096 /\ sp < 2 ^ 47) by lia.
  set (m := ms_mem ms) in *.
  pose proof CF as CF0.
  destruct CF0 as (LB_ & ks & offs & rss & ksp & nn & md & A & nw & rest & SPR & Hksp & SPE & K16 & LOSP & FLOOR & Hf & Hc & Eh & Tnw & Nn & Ln & N255
                   & NW & AN & AJ & TS & WF & HC & AWden & WIT).
  destruct (HeapCtr.TwinB.call_pre_inv st r CP) as (FOK & _).
  assert (IUOUT : forall LB0, aw_real AI ACCT UNIV aw LB0 m mo L RNG sta LBa -> forall a, 0 <= a < 2 ^ 64 -> in_user LB0 a ->
            mjoin m m' (AM.wa a) = m (AM.wa a)).
  { intros LB0 AR0 a Ha IU. pose proof (UnreggGeo.TwinB.user_out AI ACCT UNIV AI_fake aw LB0 m mo L RNG sta LBa a AR0 IU) as G.
    apply (mj_out m m' sp (CtrPre.TwinB.sp_lo E st) n MU LO3 Hn a Ha); unfold ERRNO, AIMG_HI, KLS in *; lia. }
  assert (HSA : heap_set_A hargs A = Some hargs) by (rewrite Eh; reflexivity).
  assert (DCN : den (CtrFrame.TwinB.E' E st Fv Gv) A = aw).
  { rewrite (CtrFrame.TwinB.den_E' E st Fv Gv A (CtrFrame.TwinB.A_below st FOK rest hargs md A nw Hf Eh)). symmetry. exact AWden. }
  assert (OPSE : s_ops stE = s_ops st).
  { destruct (errno_havoc_keeps _ _ HAV) as (_ & O & _). rewrite O, s_ops_setr.
    destruct (clobber_fields st1) as (_ & _ & _ & _ & _ & OP & _). rewrite OP.
    destruct (CtrFrame.TwinB.st1_fields st st1 FS) as (_ & _ & _ & _ & _ & OP1 & _). exact OP1. }
  assert (GOALEQ : setpc (set_ops stE (set_op HEAP_ID hargs (s_ops stE))) r = setpc stE r).
  { rewrite OPSE, (set_op_same HEAP_ID (s_ops st) hargs Hf), <- OPSE, set_ops_self. reflexivity. }
  rewrite <- GOALEQ.
  apply (CtrNull.TwinB.nodelta_errno_st_ok AI IMGX IMGX_aci ACCT UNIV Cw OPS AI_fake OPS_holds1 OPS_fp1 OPS_cov1 OPS_frame_other OPS_fp_other OTHER OPS_mo_other
           OPS_cov0_img AERRNO_aci E st ms mo r hargs wnl L RNG sta LBa aw st1 Fv Gv R' (mjoin m m') mo' RNG sta v A hargs aw errv e' stE
           HS CP FS (CtrNull.TwinB.acallN_of_G AI ACCT UNIV Cw E st ms mo r hargs wnl L RNG sta LBa aw CF) HSA DCN HAV KEPT).
  - intros x i Hx. exact (CtrNull.TwinB.cfvE_clob R' e' x i Hx).
  - exact DV.
  - reflexivity.
  - rewrite AERRNO_eq. exact ERR0.
  - rewrite AERRNO_eq. exact (mj_errno_cells m m' e' ERR1).
  - exact (mj_mem_inv m m' MI MI').
  - exact (mj_stk m m' sp (CtrPre.TwinB.sp_lo E st) LO3 STK').
  - exact BOT.
  -
    intros LB0 AR0 a Ha STB NE. apply rawv. destruct STB as [S1|[S2|S3]].
    + apply (mj_out m m' sp (CtrPre.TwinB.sp_lo E st) n MU LO3 Hn a Ha); unfold ERRNO, sp, R in *; lia.
    + pose proof (aci_low'' a S2) as AL. unfold CtrNull.TwinB.in_errno in NE. rewrite AERRNO_eq in NE.
      apply (mj_out m m' sp (CtrPre.TwinB.sp_lo E st) n MU LO3 Hn a Ha); unfold ERRNO, AIMG_HI in *; lia.
    + exact (IUOUT LB0 AR0 a Ha S3).
  -   exact IUOUT.
  -
    intros o a Ho NI Ha NE FP. unfold not_id in NI. apply Uint63.eqb_false_spec in NI. unfold CtrNull.TwinB.in_errno in NE. rewrite AERRNO_eq in NE.
    destruct (OPS_fp_other _ _ a NI FP) as [INA|[(a' & INA & ->)|(a' & STK & ->)]].
    + pose proof (aci_low'' a INA) as AL.
      apply (mj_out m m' sp (CtrPre.TwinB.sp_lo E st) n MU LO3 Hn a); [unfold two64 in Ha; lia| unfold AIMG_HI in *; lia | exact NE].
    + pose proof (aci_low'' a' INA) as AL. destruct INA as (iv0 & I0 & I1). pose proof (AI_aci_lo AI iv0 I0) as A0.
      pose proof (CtrPre.TwinB.shad_img_band a' ltac:(lia)) as BND.
      apply (mj_out m m' sp (CtrPre.TwinB.sp_lo E st) n MU LO3 Hn (shad a')); [unfold two64 in Ha; lia| lia | exact NE].
    + assert (ZN : 0x7fffa000 <= shad a' < 0x10007fff8000) by (unfold shad, ASHOFF; rewrite Z.shiftr_div_pow2 by lia; change (2 ^ 3) with 8; clear - STK ATR; Z.div_mod_to_equations; lia).
      apply (mj_out m m' sp (CtrPre.TwinB.sp_lo E st) n MU LO3 Hn (shad a')); [unfold two64 in Ha; lia| lia | exact NE].
  -   intros a Ha _ Wb. apply (GlueA.TwinB.wb_wviewA bsegs). apply (GlueA.TwinB.wb_wviewA bsegs) in Wb. exact (mj_wmono m m' WM _ Wb).
  -
    intros a Ha SC _. apply rawv.
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
  - exact (fun _ P => P).
Qed.

Lemma phaseB_dir : forall st E ms mo r hargs wnl st1 (L : alayout) (RNG : footprint) (sta : astate) (LBa : list ablock) (aw : word)
    (m' : amem) (R' : bvmap 5 word) (mo' : Model) (n : Z) (junk : list byte) (stE : sstate) (E' : env),
  st_ok bsegs OPS E st ms mo -> call_pre st = Some r -> forget_stack_below_sp_g st = Some st1 ->
  CtrPre.TwinB.acallG AI ACCT UNIV Cw E st ms mo r hargs wnl L RNG sta LBa aw -> AHEAP AI L RNG sta LBa (ms_mem ms) ->
  let R := ms_regs ms in let sp := bv_unsigned (AP.getr R 2) in
  ATOP + 4096 <= CtrPre.TwinB.sp_lo E st -> CtrPre.TwinB.sp_lo E st <= sp - 4096 -> sp < 2 ^ 47 -> 0 < n <= 65536 ->
  munch [(sp - 2208, sp); (STAGE, STAGE + n); (ERRNO, ERRNO + 4)]%Z (ms_mem ms) m' -> wmono bsegs (ms_mem ms) m' ->
  AS.rw_cells bsegs (ms_mem ms) STAGE [CB (Z.to_nat n) junk] -> AS.rw_cells bsegs m' STAGE [CB (Z.to_nat n) junk] ->
  (forall a, sv_vars_below (s_next st) a = true -> den E' a = den E a) ->
  errno_havoc (setr (clobber st1) X10 MINUS1) = Some stE ->
  st_ok bsegs OPS E' (setpc stE r) (CtrFrame.TwinB.ms' ms r R' (mjoin (ms_mem ms) m')) mo' ->
  CtrS.priv_has st 6283984%uint63 CtrS.STAGE_LEN = true ->
  ACCT aw L RNG sta LBa mo' ->
  st_ok bsegs OPS E' (setpc stE r) (CtrFrame.TwinB.ms' ms r R' m') mo'.
Proof.
  intros st E ms mo r hargs wnl st1 L RNG sta LBa aw m' R' mo' n junk stE E' HS CP FS CF AH R sp BOT LO SPT Hn MU WM STG STGP DENE HAV HSj PRIV ACj.
  pose proof atop_range as ATR.
  assert (LO3 : ATOP + 4096 <= CtrPre.TwinB.sp_lo E st /\ CtrPre.TwinB.sp_lo E st <= sp - 4096 /\ sp < 2 ^ 47) by lia.
  set (m := ms_mem ms) in *.

  destruct (errno_havoc_keeps _ _ HAV) as (KF & KO & KP & _).
  destruct (clobber_fields st1) as (_ & FF & RV & RG & FS0 & OP & PV & NXc).
  destruct (CtrFrame.TwinB.st1_fields st st1 FS) as (_ & _ & FF1 & RV1 & FS1 & OP1 & PV1 & NX1).
  assert (PCF : forall s pc, s_facts (setpc s pc) = s_facts s /\ s_ops (setpc s pc) = s_ops s /\ s_priv (setpc s pc) = s_priv s) by (intros [? ? ? ? ? ? ? ? ?] pc; repeat split; reflexivity).
  destruct (PCF stE r) as (PF & PO & PP).
  assert (HF : s_facts (setpc stE r) = s_facts st) by (rewrite PF, KF, s_facts_setr; rewrite FS0; exact FS1).
  assert (HO : s_ops (setpc stE r) = s_ops st) by (rewrite PO, KO, s_ops_setr; rewrite OP; exact OP1).
  assert (HP : s_priv (setpc stE r) = s_priv st) by (rewrite PP, KP, s_priv_setr; rewrite PV; exact PV1).
  change (CtrFrame.TwinB.ms' ms r R' m') with (ms_with_mem (CtrFrame.TwinB.ms' ms r R' (mjoin m m')) m').
  set (T := setpc stE r) in *.
  replace T with (SS (s_pc T) (s_rf T) (s_ff T) (s_resv T) (s_regs T) ([] ++ s_facts T) (s_ops T) (s_priv T) (s_next T)) by (destruct T; reflexivity).
  apply (st_ok_memops bsegs OPS E' T _ mo' mo' [] (s_ops T) (s_next T) m' HSj (Forall_nil _) (so_mf _ _ _ _ _ _ HSj)).
  -   unfold ops_hold. apply Forall_forall. intros o Ho. rewrite HO in Ho.
    destruct (PrimInt63.eqb (op_id o) HEAP_ID) eqn:QH.
    +
      apply Uint63.eqb_correct in QH.
      destruct CF as (LB & ks & offs & rss & ksp & nn & md & A & nw & rest & SPR & Hksp & SPE & K16 & LOSP & FLOOR & Hf & Hc & Eh & Tnw & Nn & Ln & N255
                      & NW & AN & AJ & TS & WF & HC & AWden & (W & WOF & ARW & TI)).
      destruct (HeapCtr.TwinB.call_pre_inv st r CP) as (FOK & _).
      pose proof (count_one_args HEAP_ID (s_ops st) o hargs Ho QH Hc Hf) as EA.
      replace (op_id o) with HEAP_ID. rewrite EA.
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
        - rewrite E1, E4. exact ACj.
        - intros b x Hb FK Hx. rewrite E4 in Hb. pose proof (Op.TwinB.blk_band AI AI_fake L RNG sta LBa m b x AH Hb Hx) as BB.
          apply (raw_out m m' sp (CtrPre.TwinB.sp_lo E st) n MU LO3 Hn x); unfold STAGE, ERRNO, AIMG_HI, KLS in *; lia.
        - rewrite E4. apply (Op.TwinB.twins_pres_band AI L RNG sta LBa m m' AH). intros a Ha.
          assert (SA : shad ATOP = ASHOFF + ATOP / 8) by (unfold shad; rewrite Z.shiftr_div_pow2 by lia; reflexivity).
          rewrite SA in Ha. unfold ASHOFF in Ha.
          apply (raw_out m m' sp (CtrPre.TwinB.sp_lo E st) n MU LO3 Hn a); unfold STAGE, ERRNO in *; clear - Ha ATR LO3 Hn; Z.div_mod_to_equations; lia. }
      assert (TI' : ties W' (wins_of E nn rest)) by (apply (ties_ext W W'); [reflexivity| intros b; reflexivity| reflexivity| exact TI| intros b _ V; exact V| intros P; unfold W'; cbn [w_st]; rewrite <- (proj1 (proj2 (proj2 WOF))); exact P]).
      assert (DECN0 : decode (map (den E) hargs) = Some (w2Z md, den E A, wins_of E nn rest, map (den E) (skipn (3 * nn) rest))).
      { rewrite Eh. exact (decode_hargs E md A nw rest nn Tnw Nn Ln). }
      assert (MAPE : map (den E') hargs = map (den E) hargs).
      { apply map_ext_in. intros a Ha. apply DENE.
        pose proof (HeapCtr.TwinB.fresh_ok_inv st FOK) as (SVB & _).
        exact (ops_args_below (s_next st) st o a SVB Ho ltac:(rewrite EA; exact Ha)). }
      rewrite OPS_holds1, MAPE. exists (w2Z md), aw, (wins_of E nn rest), (map (den E) (skipn (3 * nn) rest)), LB, W'.
      split; [rewrite AWden; exact DECN0|]. split; [exact (proj1 AR')|]. split; [exact WF|]. split; [| exact TI'].
      apply (cw_frame Cw _ _ _ _ m m' HC). intros a Ha U _. symmetry. unfold AM.wa in SBU.
      apply (SBU a ltac:(unfold two64 in Ha; lia)). exact U.
    + apply Uint63.eqb_false_spec in QH.
      pose proof (proj1 (Forall_forall _ _) (so_ops _ _ _ _ _ _ HSj) o ltac:(rewrite HO; exact Ho)) as HOj. cbv beta in HOj. cbn [ms_mem CtrFrame.TwinB.ms'] in HOj.
      destruct (PrimInt63.eqb (op_id o) ReadC.TwinB.ReadC.RSTV_ID) eqn:QR.
      *
        apply Uint63.eqb_correct in QR. rewrite QR in HOj |- *.
        apply OPS_holds_rstage'. pose proof (OPS_holds_rstage _ _ _ HOj) as RH.
        change (ms_mem (CtrFrame.TwinB.ms' ms r R' (mjoin m m'))) with (mjoin m m') in RH.
        destruct (map (den E') (op_args o)) as [|off [|nv [|? ?]]]; cbn [rstage_holds_v] in RH |- *; try exact RH.
        destruct RH as (B1 & B2 & BY). split; [exact B1|]. split; [exact B2|]. intros i Hi. rewrite <- (BY i Hi).
        destruct (Z_lt_le_dec i n) as [IN|OUT].
        --
           destruct STG as [[WFm (_ & _ & BYm)] _]. destruct STGP as [[_ (_ & _ & BYm')] _].
           assert (LJ : length junk = Z.to_nat n) by (cbn [cells_wf cell_wf] in WFm; exact (proj1 WFm)).
           assert (LCB : length (cells_bytes [CB (Z.to_nat n) junk]) = Z.to_nat n) by (cbn [cells_bytes cbytes]; rewrite app_nil_r; exact LJ).
           assert (EJ : mjoin m m' (Z_to_bv 64 (STAGE + i)) = m (Z_to_bv 64 (STAGE + i))).
           { unfold mjoin. rewrite Z_to_bv_unsigned, bv_wrap_small by (rewrite bv_modulus_64; unfold W64.two64, STAGE; lia).
             replace (in_stage (STAGE + i)) with true by (unfold in_stage; symmetry; apply andb_true_intro; split; [apply Z.leb_le| apply Z.ltb_lt]; lia). reflexivity. }
           rewrite (ReadPost.TwinB.rb_ext m (mjoin m m') (STAGE + i) EJ). rewrite !(GlueA.TwinB.rb_mrdA bsegs).
           replace (STAGE + i) with (STAGE + Z.of_nat (Z.to_nat i)) by lia.
           rewrite (BYm (Z.to_nat i)) by (rewrite LCB; lia). rewrite (BYm' (Z.to_nat i)) by (rewrite LCB; lia). reflexivity.
        --
           assert (EJ : mjoin m m' (Z_to_bv 64 (STAGE + i)) = m' (Z_to_bv 64 (STAGE + i))).
           { unfold mjoin. rewrite Z_to_bv_unsigned, bv_wrap_small by (rewrite bv_modulus_64; unfold W64.two64, STAGE; lia).
             destruct (in_stage (STAGE + i)); [| reflexivity]. symmetry.
             apply (raw_out m m' sp (CtrPre.TwinB.sp_lo E st) n MU LO3 Hn (STAGE + i)); unfold STAGE, ERRNO in *; lia. }
           symmetry. exact (ReadPost.TwinB.rb_ext m' (mjoin m m') (STAGE + i) EJ).
      *
        apply Uint63.eqb_false_spec in QR.
        apply (OPS_frame_other _ _ (mjoin m m') m' mo' QH HOj).
        -- intros a Ha FP. pose proof (OPS_fp_nostage _ _ a QR FP) as NS.
           apply (mj_final m m' a ltac:(unfold two64 in Ha; lia) NS).
        -- intros a Ha _ Wb. destruct (in_stage a) eqn:IS.
           ++ apply stage_wb_any. unfold in_stage in IS. lia.
           ++ rewrite <- (ReadPost.TwinB.wb_ext m' (mjoin m m') a); [exact Wb|]. apply (mj_final m m' a ltac:(unfold two64 in Ha; lia)). unfold in_stage in IS. lia.
  -   exact (so_apart _ _ _ _ _ _ HSj).
  -   exact (so_cover _ _ _ _ _ _ HSj).
  -
    intros a Ha Hout. cbn [ms_mem CtrFrame.TwinB.ms']. destruct (in_stage a) eqn:IS.
    + exfalso. unfold in_stage in IS. assert (SA : STAGE <= a < STAGE + 65536) by lia.
      destruct (MemP.abs_writable_sound bsegs STAGE 65536 ltac:(unfold STAGE; lia) ltac:(lia) ltac:(vm_compute; reflexivity)) as [_ WB].
      destruct (WB (a - STAGE) ltac:(lia)) as [_ (seg & Hseg & _)]. replace (STAGE + (a - STAGE)) with a in Hseg by lia.
      destruct Hout as [Hn0 | Hnp]; [congruence|]. apply Hnp. rewrite HP.
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

Lemma aread_dir_leaf_ok : ReadDirSound.TwinB.aread_dir_leaf AI ACCT UNIV Cw OPS OTHER MP PB.
Proof.
  unfold ReadDirSound.TwinB.aread_dir_leaf.
  intros st K E ms mo r hargs wnl st1 stE cnt L RNG sta LBa aw junk errv HS HMP HPB HK PRE RPRE HAV ECNT WR CP FS CF AH BOT LO SPT TP MI STG ERR ZSH
         ms' mo' HQ MP' MI' OT' AC'.
  set (R := ms_regs ms) in *.
  destruct HQ as (_ & t0 & t1 & t2 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & m' & EMS & MU & WM & MINV' & STK' & STGP & ERRP & _).
  pose proof atop_range as ATR.
  assert (ETP : bv_unsigned (AP.getr R 4) + -164 = ERRNO) by (rewrite TP; vm_compute; reflexivity).
  rewrite ETP in MU, ERRP. rewrite Z2Nat.id in MU by lia.
  match type of EMS with ms' = MS ?RR _ _ _ _ _ _ => set (R' := RR) in * end.
  set (e' := Z_to_bv 64 EISDIR : word) in *.
  set (Fv := CtrNull.TwinB.cfvE R' e'). set (Gv := fun (_ _ : Z) => Z_to_bv 8 0). set (E' := CtrFrame.TwinB.E' E st Fv Gv).
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
  destruct (aread_dir_pre_inv st RPRE) as (_ & _ & PRIV & _ & _ & _ & _).
  apply (HK E' ms' mo' (CtrFrame.TwinB.EXT E st Fv Gv) MP'). rewrite EMS'.
  apply (phaseB_dir st E ms mo r hargs wnl st1 L RNG sta LBa aw m' R' mo' cnt junk stE E' HS CP FS CF AH BOT LO SPT WR MU WM STG STGP).
  - intros a Ha. apply CtrFrame.TwinB.den_E'. exact Ha.
  - exact HAV.
  - apply (phaseA_dir st E ms mo r hargs wnl st1 L RNG sta LBa aw m' R' mo' errv e' cnt MINUS1 stE HS CP FS CF AH BOT LO SPT WR MU WM MI MINV' STK' ERR ERRP).
    + intros rg Hrg. unfold CtrFrame.TwinB.kept_regsA in Hrg. cbn [In] in Hrg. repeat (destruct Hrg as [<-|Hrg]; [reflexivity|]). destruct Hrg.
    +   cbn [den MINUS1 CtrS.errv]. subst R'. cbn [AP.getr]. unfold F_syscalls.TwinB.read_ret. apply bv_eq. vm_compute. reflexivity.
    + exact HAV.
    + exact OT'.
    + exact MI'.
    + exact AC'.
  - exact PRIV.
  - exact AC'.
Qed.
End Leaf.
End TwinB.
