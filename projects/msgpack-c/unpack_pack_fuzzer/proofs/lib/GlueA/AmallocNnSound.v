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
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX Require Import W64Proofs ValProofs MemProofs.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Br Require Import CtrFX.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Br Require HeapCtr HeapCtrB.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Bridge Require CallA CallV GlueA CtrPre CtrPost C24 CtrNull Ctr.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.GlueA Require Import AmallocNnC NnDel.
Unset Nia Cache. Unset Nra Cache.
Import ValP MemP CtrFX ActrA AmallocNnC.
Module AP := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.PropExec.

Lemma has_prist_In : forall E0 md A nw rest n, wt nw = false -> n = Z.to_nat (to_Z (wl nw)) -> (3 * n <= length rest)%nat ->
  has_prist (VL md :: A :: VL nw :: rest) = true -> In prist_win (wins_of E0 n rest).
Proof.
  intros E0 md A nw rest n T N L H. unfold has_prist in H.
  destruct (heap_del_prist (VL md :: A :: VL nw :: rest)) as [h'|] eqn:HD; [|discriminate H].
  destruct (heap_del_prist_facts E0 _ h' HD) as (md1 & A1 & nw1 & rest1 & n1 & ws' & l1 & l2 & EH & T1 & N1 & L1 & _ & W1 & _).
  injection EH as -> -> -> ->. subst n1. rewrite <- N in W1. rewrite W1. apply in_app_iff. right. left. reflexivity.
Qed.

Section Sound.
Context {rc : runConstT}.
Variable AI : AMallocIface2.
Variable IMGX : list iv.
Hypothesis IMGX_aci : imgx_ok AI IMGX.
Hypothesis IMGSH_aci : forall v a, In v SHLIT -> fst v <= a < snd v -> exists a', in_ranges (aci AI) a' /\ a = shad a'.
Variable ACCT : word -> alayout -> footprint -> astate -> list ablock -> Model -> Prop.
Variable UNIV : list (list Z).
Variable Cw : client_world.
Variable OPS : optable.
Hypothesis AI_fake : AI_fake_law AI.
Hypothesis OPS_holds1 : forall args m mo, op_holds OPS HEAP_ID args m mo <-> heap_holdsX AI ACCT UNIV Cw args m mo.
Hypothesis Cw_ghost_grow : forall md ca LB ws m b0 n0 n, cw_holds Cw md ca LB ws m ->
  In (Win b0 n0 K_BLOCK) ws -> 0 < n0 -> b0 mod 8 = 0 ->
  (forall a, in_iv (shad b0, n) a -> ~ in_user LB a) -> cw_holds Cw md ca ((shad b0, n) :: LB) (ws ++ [Win (shad b0) n K_TWINz]) m.
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
Hypothesis ACCT_rng : forall aw L RNG st LBa mo, ACCT aw L RNG st LBa mo -> rng RNG (ATOP + 4096) (2^47 - (ATOP + 4096)).

Variable NMAXt : nat.
Notation twfS := (twfA node nstepA nexitA (nsafeA NMAXt) fstepS NMAXt).
Definition acct_leaf_some (mo0 : Model) (aw : word) (L : alayout) (st : astate) (LBa : list ablock) (n chg : Z)
    (r : astate * option aptr) (RNG' : footprint) (A' : alw) (moc' : Model) : Prop :=
  forall mo' Aaddr, mrel A' moc' mo' ->
    MP mo' /\ op_minv OPS mo' /\ OTHER mo0 mo' /\
    (exists p, snd r = Some p /\ ACCT (Z_to_bv 64 (bv_unsigned aw - chg)) L RNG' (fst r) (HB p Aaddr n :: LBa) mo')
    /\ (64512 < n -> aprist st -> aprist (fst r)).
Definition CRED0 : Z := 3 * 2 ^ 34.
Hypothesis ACCT_malloc_some_sec : forall aw L RNG st LBa mo n,
  ACCT aw L RNG st LBa mo -> MP mo -> op_minv OPS mo -> 64512 < n <= 2 ^ 28 -> n <= bv_unsigned aw -> CRED0 - 2 ^ 30 <= bv_unsigned aw ->
  C24.c24count LBa <= 255 ->
  exists RESV A moc, aresv_ok L RESV /\ Ctr.c6ok RESV RNG st /\ mrel A moc mo /\ minvA moc /\ m_halted moc = None /\
    twfS RNG A (aembed ATOP (amalloc ATOP RESV st n)) moc (acct_leaf_some mo aw L st LBa n n).
Hypothesis ACCT_malloc_some_prim : forall aw L RNG st LBa mo n,
  ACCT aw L RNG st LBa mo -> MP mo -> op_minv OPS mo -> 1 <= n <= 64512 -> 1048576 <= bv_unsigned aw -> C24.c24count LBa <= 255 -> aprist st ->
  exists RESV A moc, aresv_ok L RESV /\ Ctr.c6ok RESV RNG st /\ mrel A moc mo /\ minvA moc /\ m_halted moc = None /\
    twfS RNG A (aembed ATOP (amalloc ATOP RESV st n)) moc (acct_leaf_some mo aw L st LBa n 0).

Hypothesis AI_prist : OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.APristLaw.prist_det_law (AHEAP AI).
Let aprist_heap := Op.aprist_heap AI ACCT UNIV AI_prist.

Hypothesis Cw_k0_del : forall md ca LB ws ws' m w0, cw_holds Cw md ca LB ws m -> w_kind w0 = K_STACK ->
  (forall w, In w ws' <-> In w ws /\ w <> w0) -> cw_holds Cw md ca LB ws' m.

Notation sp_lo := CtrPre.sp_lo.

Lemma nn_tail : forall s stN posts K E ms mo,
  st_ok asegs OPS E s ms mo -> MP mo -> to_Z (s_pc s) = AMALLOC_SYM -> amalloc_apply UNIV AMALLOC_PC s = Some (stN :: posts) ->
  (forall L RNG sta LBa aw n,
     AHEAP AI L RNG sta LBa (ms_mem ms) -> ACCT aw L RNG sta LBa mo -> 1 <= n <= AREQMAX -> 1048576 <= bv_unsigned aw -> C24.c24count LBa <= 255 ->
     bv_unsigned (den E (getr s X10)) = n -> CtrPre.acall_facts AI ACCT UNIV Cw X10 E s ms mo L RNG sta LBa aw n -> (64512 < n \/ ~ CtrPre.prist_in E s) ->
     exists RESV A moc, aresv_ok L RESV /\ Ctr.c6ok RESV RNG sta /\ mrel A moc mo /\ minvA moc /\ m_halted moc = None /\
       twfS RNG A (aembed ATOP (amalloc ATOP RESV sta n)) moc
            (acct_leaf_some mo aw L sta LBa n (if prim_decided (s_facts s) (getr s X10) then 0 else n))) ->
  (forall st', In st' posts -> forall E' ms' mo', env_ext (s_next s) E E' -> MP mo' -> st_ok asegs OPS E' st' ms' mo' -> realizes asegs (mkCfg ms' mo') K) ->
  realizes asegs (mkCfg ms mo) K.
Proof.
  intros s stN posts K E ms mo HS HMP HPC HA TJF HK.
  destruct (CtrPre.amalloc_pre_facts AI ACCT UNIV Cw OPS AI_fake OPS_holds1 ACCT_rng s (stN :: posts) E ms mo HS HPC HA)
    as (L & RNG & sta & LBa & aw & n & Ems & AH & AC & HU & MI & ST & BOT & LO & TP & Ha0 & NR & NC & AUNW & S0NE & RA4 & RANE & SP16 & RSTK & CF & PRISTF).
  destruct AUNW as [utr AUNW]. destruct NC as [NCX NC].
  destruct (CtrPre.acall_facts_c24 AI ACCT UNIV Cw X10 E s ms mo L RNG sta LBa aw n CF) as [C24B NDEN].
  set (chg := if prim_decided (s_facts s) (getr s X10) then 0 else n).
  destruct (TJF L RNG sta LBa aw n AH AC NR NCX C24B NDEN CF PRISTF) as (RESV & A & moc & ROK & [C6M CAPB] & MR & MINV & HH & TW).
  set (R := ms_regs ms) in *.
  pose proof (AI_malloc AI L RNG (AP.getr R 1) (AP.getr R 2) (AP.getr R 3) (AP.getr R 4) (AP.getr R 5) (AP.getr R 6) (AP.getr R 7) (AP.getr R 8)
                (AP.getr R 9) (AP.getr R 10) (AP.getr R 11) (AP.getr R 12) (AP.getr R 13) (AP.getr R 14) (AP.getr R 15) (AP.getr R 16)
                (AP.getr R 17) (AP.getr R 18) (AP.getr R 19) (AP.getr R 20) (AP.getr R 21) (AP.getr R 22) (AP.getr R 23) (AP.getr R 24)
                (AP.getr R 25) (AP.getr R 26) (AP.getr R 27) (AP.getr R 28) (AP.getr R 29) (AP.getr R 30) (AP.getr R 31)
                (ms_fregs ms) (ms_fcsr ms) (ms_mem ms) sta LBa n (sp_lo E s) utr RESV AH MI ST BOT LO TP Ha0 NR AUNW S0NE RA4 RANE SP16 RSTK ROK
                (so_fcsr _ _ _ _ _ _ HS) C6M CAPB (CtrNull.errno_cells (ms_mem ms))) as IMPL.
  rewrite Ems. apply (GlueA.realizes_to_mkRA asegs).
  eapply (implS_twfS_realizes_silent asegs NMAXt _ RNG A _ _ _ moc mo K IMPL TW HH MINV MR).
  intros r RNG' A' ms' moc' mo' HQ HP ACC' HH' MINV' MR'.
  assert (LEAF : forall Aaddr, MP mo' /\ op_minv OPS mo' /\ OTHER mo mo' /\
            (exists p, snd r = Some p /\ ACCT (Z_to_bv 64 (bv_unsigned aw - chg)) L RNG' (fst r) (HB p Aaddr n :: LBa) mo')
            /\ (64512 < n -> aprist sta -> aprist (fst r))) by (intros Aaddr; exact (HP mo' Aaddr MR')).
  destruct (LEAF 0) as (HMP' & HMI' & OTH & (p0 & SR0 & _) & PKEEP).

  destruct r as [sta' [p|]]; cbn [fst snd] in SR0, PKEEP, LEAF; [| discriminate SR0].
  unfold amalloc_post2x in HQ; cbn [fst snd] in HQ.
  assert (ACP : forall Aaddr, ACCT (Z_to_bv 64 (bv_unsigned aw - chg)) L RNG' sta' (HB p Aaddr n :: LBa) mo').
  { intros Aaddr. destruct (LEAF Aaddr) as (_ & _ & _ & (p1 & SR & AC') & _). injection SR as <-. exact AC'. }
  assert (PRSX : CtrPre.prist_in E s -> aprist sta').
  { intros PI. destruct PRISTF as [SEC|NP]; [| exfalso; exact (NP PI)].
    exact (PKEEP SEC (CtrPre.prist_in_aprist AI ACCT UNIV Cw X10 E s ms mo L RNG sta LBa aw n CF PI)). }
  destruct (CtrPost.amalloc_post_okA AI IMGX IMGX_aci IMGSH_aci ACCT UNIV Cw OPS AI_fake OPS_holds1 OPS_fp1 OPS_cov1 Cw_ghost_grow OPS_frame_other OPS_fp_other
              OTHER OPS_mo_other OPS_cov0_img s (stN :: posts) E ms mo L RNG sta LBa aw n (sta', Some p) RNG' ms' mo' HS HA CF HQ ACP PRSX HMI' OTH) as (stB & E' & INB & EXT & HS').
  cbn [tl] in INB. exact (HK stB INB E' ms' mo' EXT HMP' HS').
Qed.

Theorem amalloc_nn_sound : forall pc, to_Z pc = AMALLOC_SYM -> contract_sound asegs OPS MP PB (amalloc_nn_c UNIV AMALLOC_PC pc).
Proof.
  intros pc Hpc st sts Hspc Happ K E ms mo HS HMP HPB HK. cbn [c_apply c_pc amalloc_nn_c] in Happ, Hspc.
  assert (HPC : to_Z (s_pc st) = AMALLOC_SYM) by (rewrite Hspc; exact Hpc).
  unfold amalloc_nn_apply in Happ.
  destruct (find_op HEAP_ID (s_ops st)) as [hargs0|] eqn:Hf0; [|discriminate Happ].
  destruct (heap_A hargs0) as [cred|] eqn:HAc; [|discriminate Happ]. cbv zeta in Happ.
  pose proof (so_facts _ _ _ _ _ _ HS) as HF.
  destruct (arm_sec (s_facts st) (getr st X10) cred) eqn:SEC.
  -
    destruct (amalloc_apply UNIV AMALLOC_PC st) as [[|stN posts]|] eqn:HA; try discriminate Happ. injection Happ as <-.
    apply (nn_tail st stN posts K E ms mo HS HMP HPC HA); [| exact HK].
    intros L RNG sta LBa aw n AH AC NR NCX C24B NDEN CF _.
    pose proof CF as CF'.
    destruct CF' as (LB & r & hargs & st1 & ks & offs & rss & ksp & wnl & nn & md & A & nw & rest
                    & CP & FS & SPR & Hksp & SPE & K16 & LOSP & FLOOR & Hf & Hc & Eh & Tnw & Nn & Ln & N255 & NW & AJ & WF & HC & AWden & _ & _ & _).
    rewrite Hf in Hf0. injection Hf0 as <-. rewrite Eh, heap_A_eq in HAc. injection HAc as <-.
    unfold arm_sec in SEC. apply andb_prop in SEC as [SEC S3]. apply andb_prop in SEC as [S1 S2].
    pose proof (HeapCtr.known_ltu_sound E _ _ _ HF S1) as B1. pose proof (HeapCtr.known_leu_sound E _ _ _ HF S2) as B2.
    pose proof (HeapCtr.known_leu_sound E _ _ _ HF S3) as B3. rewrite NDEN in B1, B2. rewrite <- AWden in B3.
    replace (bv_unsigned (den E (VL SEC_MINw))) with 64512 in B1 by (vm_compute; reflexivity).
    replace (bv_unsigned (den E (VL SEC_MAXw))) with (2 ^ 28) in B2 by (vm_compute; reflexivity).
    replace (bv_unsigned (den E (VL CRED_LOWw))) with (CRED0 - 2 ^ 30) in B3 by (vm_compute; reflexivity).
    assert (PD : prim_decided (s_facts st) (getr st X10) = false).
    { destruct (prim_decided (s_facts st) (getr st X10)) eqn:PD; [| reflexivity]. pose proof (CallA.prim_decided_sound E _ _ HF PD) as X. rewrite NDEN in X. lia. }
    rewrite PD.
    apply (ACCT_malloc_some_sec aw L RNG sta LBa mo n AC HMP (so_mf _ _ _ _ _ _ HS)); [lia| | exact B3| exact C24B].
    unfold CRED0 in B3. lia.
  -
    destruct (arm_prim (s_facts st) (getr st X10) hargs0) eqn:PRIM; [|discriminate Happ].
    destruct (amalloc_apply UNIV AMALLOC_PC (del_prist st)) as [[|stN posts]|] eqn:HA; try discriminate Happ. injection Happ as <-.
    unfold arm_prim in PRIM. apply andb_prop in PRIM as [PD HP].

    assert (PRW : exists W aw0 LB0, aw_holds_w AI ACCT UNIV W aw0 LB0 (ms_mem ms) mo /\ aprist (w_st W)).
    { pose proof (ops_hold_find OPS E (s_ops st) (ms_mem ms) mo HEAP_ID _ (so_ops _ _ _ _ _ _ HS) Hf0) as HH.
      rewrite OPS_holds1 in HH. destruct HH as (md' & aw0 & ws & ca & LB0 & W & D & HWw & _ & _ & TI).
      exists W, aw0, LB0. split; [exact HWw|]. apply (ties_prist W ws TI).
      unfold has_prist in HP. destruct (heap_del_prist hargs0) as [h'|] eqn:HD; [|discriminate HP].
      destruct (heap_del_prist_facts E hargs0 h' HD) as (md1 & A1 & nw1 & rest1 & n1 & ws1 & l1 & l2 & EH & _ & _ & _ & _ & _ & DEC & _).
      rewrite DEC in D. injection D as _ _ <- _. apply in_app_iff. right. left. reflexivity. }
    destruct PRW as (W & aw0 & LB0 & HWw & APR).
    pose proof (del_prist_ok AI IMGX ACCT UNIV Cw OPS OPS_holds1 OPS_fp1 OPS_cov1 Cw_k0_del E st ms mo HS) as HSd.
    apply (nn_tail (del_prist st) stN posts K E ms mo HSd HMP ltac:(rewrite del_prist_pc; exact HPC) HA).
    + intros L RNG sta LBa aw n AH AC NR NCX C24B NDEN CF _.
      rewrite del_prist_facts, del_prist_getr in *. rewrite PD.
      pose proof (CallA.prim_decided_sound E _ _ HF PD) as X. rewrite NDEN in X.
      apply (ACCT_malloc_some_prim aw L RNG sta LBa mo n AC HMP (so_mf _ _ _ _ _ _ HS)); [lia| exact NCX| exact C24B|].
      exact (aprist_heap W aw0 LB0 (ms_mem ms) mo L RNG sta LBa HWw AH APR).
    + intros st' Hin E' ms' mo' EXT. rewrite del_prist_next in EXT. exact (HK st' Hin E' ms' mo' EXT).
Qed.
End Sound.

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
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.W64Proofs OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.ValProofs OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.MemProofs.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Br.CtrFX.

Import AmallocNnC.TwinB NnDel.TwinB.
Unset Nia Cache. Unset Nra Cache.
Import ValP MemP CtrFX ActrA AmallocNnC.TwinB.AmallocNnC.
Module AP := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.PropExec.

Lemma has_prist_In : forall E0 md A nw rest n, wt nw = false -> n = Z.to_nat (to_Z (wl nw)) -> (3 * n <= length rest)%nat ->
  has_prist (VL md :: A :: VL nw :: rest) = true -> In prist_win (wins_of E0 n rest).
Proof.
  intros E0 md A nw rest n T N L H. unfold has_prist in H.
  destruct (heap_del_prist (VL md :: A :: VL nw :: rest)) as [h'|] eqn:HD; [|discriminate H].
  destruct (heap_del_prist_facts E0 _ h' HD) as (md1 & A1 & nw1 & rest1 & n1 & ws' & l1 & l2 & EH & T1 & N1 & L1 & _ & W1 & _).
  injection EH as -> -> -> ->. subst n1. rewrite <- N in W1. rewrite W1. apply in_app_iff. right. left. reflexivity.
Qed.

Section Sound.
Context {rc : runConstT}.
Variable AI : AMallocIface2.
Variable IMGX : list iv.
Hypothesis IMGX_aci : imgx_ok AI IMGX.
Hypothesis IMGSH_aci : forall v a, In v SHLIT -> fst v <= a < snd v -> exists a', in_ranges (aci AI) a' /\ a = shad a'.
Variable ACCT : word -> alayout -> footprint -> astate -> list ablock -> Model -> Prop.
Variable UNIV : list (list Z).
Variable Cw : client_world.
Variable OPS : optable.
Hypothesis AI_fake : AI_fake_law AI.
Hypothesis OPS_holds1 : forall args m mo, op_holds OPS HEAP_ID args m mo <-> heap_holdsX AI ACCT UNIV Cw args m mo.
Hypothesis Cw_ghost_grow : forall md ca LB ws m b0 n0 n, cw_holds Cw md ca LB ws m ->
  In (Win b0 n0 K_BLOCK) ws -> 0 < n0 -> b0 mod 8 = 0 ->
  (forall a, in_iv (shad b0, n) a -> ~ in_user LB a) -> cw_holds Cw md ca ((shad b0, n) :: LB) (ws ++ [Win (shad b0) n K_TWINz]) m.
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
Hypothesis ACCT_rng : forall aw L RNG st LBa mo, ACCT aw L RNG st LBa mo -> rng RNG (ATOP + 4096) (2^47 - (ATOP + 4096)).

Variable NMAXt : nat.
Notation twfS := (twfA node nstepA nexitA (nsafeA NMAXt) fstepS NMAXt).
Definition acct_leaf_some (mo0 : Model) (aw : word) (L : alayout) (st : astate) (LBa : list ablock) (n chg : Z)
    (r : astate * option aptr) (RNG' : footprint) (A' : alw) (moc' : Model) : Prop :=
  forall mo' Aaddr, mrel A' moc' mo' ->
    MP mo' /\ op_minv OPS mo' /\ OTHER mo0 mo' /\
    (exists p, snd r = Some p /\ ACCT (Z_to_bv 64 (bv_unsigned aw - chg)) L RNG' (fst r) (HB p Aaddr n :: LBa) mo')
    /\ (64512 < n -> aprist st -> aprist (fst r)).
Definition CRED0 : Z := 3 * 2 ^ 34.
Hypothesis ACCT_malloc_some_sec : forall aw L RNG st LBa mo n,
  ACCT aw L RNG st LBa mo -> MP mo -> op_minv OPS mo -> 64512 < n <= 2 ^ 28 -> n <= bv_unsigned aw -> CRED0 - 2 ^ 30 <= bv_unsigned aw ->
  C24.TwinB.c24count LBa <= 255 ->
  exists RESV A moc, aresv_ok L RESV /\ Ctr.TwinB.c6ok RESV RNG st /\ mrel A moc mo /\ minvA moc /\ m_halted moc = None /\
    twfS RNG A (aembed ATOP (amalloc ATOP RESV st n)) moc (acct_leaf_some mo aw L st LBa n n).
Hypothesis ACCT_malloc_some_prim : forall aw L RNG st LBa mo n,
  ACCT aw L RNG st LBa mo -> MP mo -> op_minv OPS mo -> 1 <= n <= 64512 -> 1048576 <= bv_unsigned aw -> C24.TwinB.c24count LBa <= 255 -> aprist st ->
  exists RESV A moc, aresv_ok L RESV /\ Ctr.TwinB.c6ok RESV RNG st /\ mrel A moc mo /\ minvA moc /\ m_halted moc = None /\
    twfS RNG A (aembed ATOP (amalloc ATOP RESV st n)) moc (acct_leaf_some mo aw L st LBa n 0).

Hypothesis AI_prist : OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.APristLaw.TwinB.prist_det_law (AHEAP AI).
Let aprist_heap := Op.TwinB.aprist_heap AI ACCT UNIV AI_prist.

Hypothesis Cw_k0_del : forall md ca LB ws ws' m w0, cw_holds Cw md ca LB ws m -> w_kind w0 = K_STACK ->
  (forall w, In w ws' <-> In w ws /\ w <> w0) -> cw_holds Cw md ca LB ws' m.

Notation sp_lo := CtrPre.TwinB.sp_lo.

Lemma nn_tail : forall s stN posts K E ms mo,
  st_ok bsegs OPS E s ms mo -> MP mo -> to_Z (s_pc s) = AMALLOC_SYM -> amalloc_apply UNIV AMALLOC_PC s = Some (stN :: posts) ->
  (forall L RNG sta LBa aw n,
     AHEAP AI L RNG sta LBa (ms_mem ms) -> ACCT aw L RNG sta LBa mo -> 1 <= n <= AREQMAX -> 1048576 <= bv_unsigned aw -> C24.TwinB.c24count LBa <= 255 ->
     bv_unsigned (den E (getr s X10)) = n -> CtrPre.TwinB.acall_facts AI ACCT UNIV Cw X10 E s ms mo L RNG sta LBa aw n -> (64512 < n \/ ~ CtrPre.TwinB.prist_in E s) ->
     exists RESV A moc, aresv_ok L RESV /\ Ctr.TwinB.c6ok RESV RNG sta /\ mrel A moc mo /\ minvA moc /\ m_halted moc = None /\
       twfS RNG A (aembed ATOP (amalloc ATOP RESV sta n)) moc
            (acct_leaf_some mo aw L sta LBa n (if prim_decided (s_facts s) (getr s X10) then 0 else n))) ->
  (forall st', In st' posts -> forall E' ms' mo', env_ext (s_next s) E E' -> MP mo' -> st_ok bsegs OPS E' st' ms' mo' -> realizes bsegs (mkCfg ms' mo') K) ->
  realizes bsegs (mkCfg ms mo) K.
Proof.
  intros s stN posts K E ms mo HS HMP HPC HA TJF HK.
  destruct (CtrPre.TwinB.amalloc_pre_facts AI ACCT UNIV Cw OPS AI_fake OPS_holds1 ACCT_rng s (stN :: posts) E ms mo HS HPC HA)
    as (L & RNG & sta & LBa & aw & n & Ems & AH & AC & HU & MI & ST & BOT & LO & TP & Ha0 & NR & NC & AUNW & S0NE & RA4 & RANE & SP16 & RSTK & CF & PRISTF).
  destruct AUNW as [utr AUNW]. destruct NC as [NCX NC].
  destruct (CtrPre.TwinB.acall_facts_c24 AI ACCT UNIV Cw X10 E s ms mo L RNG sta LBa aw n CF) as [C24B NDEN].
  set (chg := if prim_decided (s_facts s) (getr s X10) then 0 else n).
  destruct (TJF L RNG sta LBa aw n AH AC NR NCX C24B NDEN CF PRISTF) as (RESV & A & moc & ROK & [C6M CAPB] & MR & MINV & HH & TW).
  set (R := ms_regs ms) in *.
  pose proof (AI_malloc AI L RNG (AP.getr R 1) (AP.getr R 2) (AP.getr R 3) (AP.getr R 4) (AP.getr R 5) (AP.getr R 6) (AP.getr R 7) (AP.getr R 8)
                (AP.getr R 9) (AP.getr R 10) (AP.getr R 11) (AP.getr R 12) (AP.getr R 13) (AP.getr R 14) (AP.getr R 15) (AP.getr R 16)
                (AP.getr R 17) (AP.getr R 18) (AP.getr R 19) (AP.getr R 20) (AP.getr R 21) (AP.getr R 22) (AP.getr R 23) (AP.getr R 24)
                (AP.getr R 25) (AP.getr R 26) (AP.getr R 27) (AP.getr R 28) (AP.getr R 29) (AP.getr R 30) (AP.getr R 31)
                (ms_fregs ms) (ms_fcsr ms) (ms_mem ms) sta LBa n (sp_lo E s) utr RESV AH MI ST BOT LO TP Ha0 NR AUNW S0NE RA4 RANE SP16 RSTK ROK
                (so_fcsr _ _ _ _ _ _ HS) C6M CAPB (CtrNull.TwinB.errno_cells (ms_mem ms))) as IMPL.
  rewrite Ems. apply (GlueA.TwinB.realizes_to_mkRA bsegs).
  eapply (implS_twfS_realizes_silent bsegs NMAXt _ RNG A _ _ _ moc mo K IMPL TW HH MINV MR).
  intros r RNG' A' ms' moc' mo' HQ HP ACC' HH' MINV' MR'.
  assert (LEAF : forall Aaddr, MP mo' /\ op_minv OPS mo' /\ OTHER mo mo' /\
            (exists p, snd r = Some p /\ ACCT (Z_to_bv 64 (bv_unsigned aw - chg)) L RNG' (fst r) (HB p Aaddr n :: LBa) mo')
            /\ (64512 < n -> aprist sta -> aprist (fst r))) by (intros Aaddr; exact (HP mo' Aaddr MR')).
  destruct (LEAF 0) as (HMP' & HMI' & OTH & (p0 & SR0 & _) & PKEEP).

  destruct r as [sta' [p|]]; cbn [fst snd] in SR0, PKEEP, LEAF; [| discriminate SR0].
  unfold amalloc_post2x in HQ; cbn [fst snd] in HQ.
  assert (ACP : forall Aaddr, ACCT (Z_to_bv 64 (bv_unsigned aw - chg)) L RNG' sta' (HB p Aaddr n :: LBa) mo').
  { intros Aaddr. destruct (LEAF Aaddr) as (_ & _ & _ & (p1 & SR & AC') & _). injection SR as <-. exact AC'. }
  assert (PRSX : CtrPre.TwinB.prist_in E s -> aprist sta').
  { intros PI. destruct PRISTF as [SEC|NP]; [| exfalso; exact (NP PI)].
    exact (PKEEP SEC (CtrPre.TwinB.prist_in_aprist AI ACCT UNIV Cw X10 E s ms mo L RNG sta LBa aw n CF PI)). }
  destruct (CtrPost.TwinB.amalloc_post_okA AI IMGX IMGX_aci IMGSH_aci ACCT UNIV Cw OPS AI_fake OPS_holds1 OPS_fp1 OPS_cov1 Cw_ghost_grow OPS_frame_other OPS_fp_other
              OTHER OPS_mo_other OPS_cov0_img s (stN :: posts) E ms mo L RNG sta LBa aw n (sta', Some p) RNG' ms' mo' HS HA CF HQ ACP PRSX HMI' OTH) as (stB & E' & INB & EXT & HS').
  cbn [tl] in INB. exact (HK stB INB E' ms' mo' EXT HMP' HS').
Qed.

Theorem amalloc_nn_sound : forall pc, to_Z pc = AMALLOC_SYM -> contract_sound bsegs OPS MP PB (amalloc_nn_c UNIV AMALLOC_PC pc).
Proof.
  intros pc Hpc st sts Hspc Happ K E ms mo HS HMP HPB HK. cbn [c_apply c_pc amalloc_nn_c] in Happ, Hspc.
  assert (HPC : to_Z (s_pc st) = AMALLOC_SYM) by (rewrite Hspc; exact Hpc).
  unfold amalloc_nn_apply in Happ.
  destruct (find_op HEAP_ID (s_ops st)) as [hargs0|] eqn:Hf0; [|discriminate Happ].
  destruct (heap_A hargs0) as [cred|] eqn:HAc; [|discriminate Happ]. cbv zeta in Happ.
  pose proof (so_facts _ _ _ _ _ _ HS) as HF.
  destruct (arm_sec (s_facts st) (getr st X10) cred) eqn:SEC.
  -
    destruct (amalloc_apply UNIV AMALLOC_PC st) as [[|stN posts]|] eqn:HA; try discriminate Happ. injection Happ as <-.
    apply (nn_tail st stN posts K E ms mo HS HMP HPC HA); [| exact HK].
    intros L RNG sta LBa aw n AH AC NR NCX C24B NDEN CF _.
    pose proof CF as CF'.
    destruct CF' as (LB & r & hargs & st1 & ks & offs & rss & ksp & wnl & nn & md & A & nw & rest
                    & CP & FS & SPR & Hksp & SPE & K16 & LOSP & FLOOR & Hf & Hc & Eh & Tnw & Nn & Ln & N255 & NW & AJ & WF & HC & AWden & _ & _ & _).
    rewrite Hf in Hf0. injection Hf0 as <-. rewrite Eh, heap_A_eq in HAc. injection HAc as <-.
    unfold arm_sec in SEC. apply andb_prop in SEC as [SEC S3]. apply andb_prop in SEC as [S1 S2].
    pose proof (HeapCtr.TwinB.known_ltu_sound E _ _ _ HF S1) as B1. pose proof (HeapCtr.TwinB.known_leu_sound E _ _ _ HF S2) as B2.
    pose proof (HeapCtr.TwinB.known_leu_sound E _ _ _ HF S3) as B3. rewrite NDEN in B1, B2. rewrite <- AWden in B3.
    replace (bv_unsigned (den E (VL SEC_MINw))) with 64512 in B1 by (vm_compute; reflexivity).
    replace (bv_unsigned (den E (VL SEC_MAXw))) with (2 ^ 28) in B2 by (vm_compute; reflexivity).
    replace (bv_unsigned (den E (VL CRED_LOWw))) with (CRED0 - 2 ^ 30) in B3 by (vm_compute; reflexivity).
    assert (PD : prim_decided (s_facts st) (getr st X10) = false).
    { destruct (prim_decided (s_facts st) (getr st X10)) eqn:PD; [| reflexivity]. pose proof (CallA.TwinB.prim_decided_sound E _ _ HF PD) as X. rewrite NDEN in X. lia. }
    rewrite PD.
    apply (ACCT_malloc_some_sec aw L RNG sta LBa mo n AC HMP (so_mf _ _ _ _ _ _ HS)); [lia| | exact B3| exact C24B].
    unfold CRED0 in B3. lia.
  -
    destruct (arm_prim (s_facts st) (getr st X10) hargs0) eqn:PRIM; [|discriminate Happ].
    destruct (amalloc_apply UNIV AMALLOC_PC (del_prist st)) as [[|stN posts]|] eqn:HA; try discriminate Happ. injection Happ as <-.
    unfold arm_prim in PRIM. apply andb_prop in PRIM as [PD HP].

    assert (PRW : exists W aw0 LB0, aw_holds_w AI ACCT UNIV W aw0 LB0 (ms_mem ms) mo /\ aprist (w_st W)).
    { pose proof (ops_hold_find OPS E (s_ops st) (ms_mem ms) mo HEAP_ID _ (so_ops _ _ _ _ _ _ HS) Hf0) as HH.
      rewrite OPS_holds1 in HH. destruct HH as (md' & aw0 & ws & ca & LB0 & W & D & HWw & _ & _ & TI).
      exists W, aw0, LB0. split; [exact HWw|]. apply (ties_prist W ws TI).
      unfold has_prist in HP. destruct (heap_del_prist hargs0) as [h'|] eqn:HD; [|discriminate HP].
      destruct (heap_del_prist_facts E hargs0 h' HD) as (md1 & A1 & nw1 & rest1 & n1 & ws1 & l1 & l2 & EH & _ & _ & _ & _ & _ & DEC & _).
      rewrite DEC in D. injection D as _ _ <- _. apply in_app_iff. right. left. reflexivity. }
    destruct PRW as (W & aw0 & LB0 & HWw & APR).
    pose proof (del_prist_ok AI IMGX ACCT UNIV Cw OPS OPS_holds1 OPS_fp1 OPS_cov1 Cw_k0_del E st ms mo HS) as HSd.
    apply (nn_tail (del_prist st) stN posts K E ms mo HSd HMP ltac:(rewrite del_prist_pc; exact HPC) HA).
    + intros L RNG sta LBa aw n AH AC NR NCX C24B NDEN CF _.
      rewrite del_prist_facts, del_prist_getr in *. rewrite PD.
      pose proof (CallA.TwinB.prim_decided_sound E _ _ HF PD) as X. rewrite NDEN in X.
      apply (ACCT_malloc_some_prim aw L RNG sta LBa mo n AC HMP (so_mf _ _ _ _ _ _ HS)); [lia| exact NCX| exact C24B|].
      exact (aprist_heap W aw0 LB0 (ms_mem ms) mo L RNG sta LBa HWw AH APR).
    + intros st' Hin E' ms' mo' EXT. rewrite del_prist_next in EXT. exact (HK st' Hin E' ms' mo' EXT).
Qed.
End Sound.
End TwinB.
