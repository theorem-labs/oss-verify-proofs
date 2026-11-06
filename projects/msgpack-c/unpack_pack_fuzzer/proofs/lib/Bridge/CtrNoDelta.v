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
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib Require ALib.Mem.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA Require Import AcctCore ExecF ITreeA NodesA.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec Require Import STree AsanCtrl AsanEmbed.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require Import AImg AProto AMalloc_iface AMalloc_iface2.
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
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Bridge Require CallA CtrPre GlueA CtrFrame.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Unp Require GLib.
Unset Nia Cache. Unset Nra Cache.
Import ValP MemP CtrFX.
Import ActrA.
Module AP := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.PropExec.

Lemma set_op_same : forall id args os, find_op id os = Some args -> set_op id args os = os.
Proof.
  induction os as [|o os IH]; intros H; cbn [find_op set_op] in *; [reflexivity|].
  destruct (PrimInt63.eqb (op_id o) id) eqn:Q.
  - injection H as <-. apply Uint63.eqb_correct in Q. destruct o; cbn in *. subst. reflexivity.
  - f_equal. exact (IH H).
Qed.

Section NoDelta.
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

Theorem nodelta_st_ok : forall E st ms mo r hargs wnl L RNG sta LBa aw st1 Fv Gv R' m' mo' RNG' sta' (v : sv) (nx' : int),
  st_ok asegs OPS E st ms mo -> call_pre st = Some r -> forget_stack_below_sp_g st = Some st1 ->
  CtrPre.acallG AI ACCT UNIV Cw E st ms mo r hargs wnl L RNG sta LBa aw ->

  (forall rg, In rg CtrFrame.kept_regsA -> AP.getr R' rg = AP.getr (ms_regs ms) rg) ->
  (forall x i, clob_pos x = Some i -> Fv (Z.of_nat i) = AP.getr R' (reg_of_r5 x)) ->
  den (CtrFrame.E' E st Fv Gv) v = AP.getr R' 10%bv ->

  ALib.Mem.mem_inv asegs m' ->
  stk asegs m' (CtrPre.sp_lo E st) (bv_unsigned (AP.getr (ms_regs ms) 2%bv)) ->

  (forall LB, aw_real AI ACCT UNIV aw LB (ms_mem ms) mo L RNG sta LBa -> forall a, 0 <= a < 2 ^ 64 -> CtrFrame.stableA AI ms LB a ->
     rb asegs m' a = rb asegs (ms_mem ms) a /\ (wb asegs (ms_mem ms) a = true -> wb asegs m' a = true)) ->
  (forall LB, aw_real AI ACCT UNIV aw LB (ms_mem ms) mo L RNG sta LBa -> forall a, 0 <= a < 2 ^ 64 -> in_user LB a ->
     m' (ALib.Mem.wa a) = ms_mem ms (ALib.Mem.wa a)) ->
  (forall o a, In o (s_ops st) -> not_id HEAP_ID o -> 0 <= a < two64 ->
     Exists (fun iv => fst iv <= a < snd iv) (op_fp OPS (op_id o) (map (den (CtrFrame.E' E st Fv Gv)) (op_args o))) ->
     m' (Z_to_bv 64 a) = ms_mem ms (Z_to_bv 64 a)) ->
  (forall a, 0 <= a < two64 -> (in_ranges (aci AI) a \/ (exists a', in_ranges (aci AI) a' /\ a = shad a') \/ (exists a', ATOP <= a' < 2 ^ 47 /\ a = shad a')) ->
     wb asegs (ms_mem ms) a = true -> wb asegs m' a = true) ->

  (forall a, 0 <= a < 2 ^ 64 -> sh_cov a -> in_based E (s_regs st) a ->
     rb asegs m' a = rb asegs (ms_mem ms) a /\ (wb asegs (ms_mem ms) a = true -> wb asegs m' a = true)) ->

  AHEAP AI L RNG' sta' LBa m' -> ACCT aw L RNG' sta' LBa mo' ->
  (forall b x, In b LBa -> is_fake b -> ab_addr b <= x < ab_addr b + ab_size b -> m' (ALib.Mem.wa x) = ms_mem ms (ALib.Mem.wa x)) ->
  twins_pres LBa (ms_mem ms) m' ->
  OTHER mo mo' -> op_minv OPS mo' ->
  (aprist sta -> aprist sta') ->
  st_ok asegs OPS (CtrFrame.E' E st Fv Gv)
    (SS r (rf_set (s_rf (clobber st1)) X10 v) (s_ff st) (s_resv st) (s_regs st1) (s_facts st) (s_ops st) (s_priv st) nx')
    (CtrFrame.ms' ms r R' m') mo'.
Proof.
  intros E st ms mo r hargs wnl L RNG sta LBa aw st1 Fv Gv R' m' mo' RNG' sta' v nx' HS CP FS CF KEPT HF DV MINV' STK' SBVall SBUall SBO WBM SBT AH' AC' KEEPW TWP OTH MINVo PSN.
  destruct CF as (LB & ks & offs & rss & ksp & nn & md & A & nw & rest & SPR & Hksp & SPE & K16 & LOSP & FLOOR & Hf & Hc & Eh & Tnw & Nn & Ln & N255
                  & NW & AN & AJ & TS & WF & HC & AWden & (W & WOF & ARW & TI)).
  destruct (HeapCtr.call_pre_inv st r CP) as (FOK & _).
  pose proof (aw_real_holds AI ACCT UNIV _ _ _ _ _ ARW) as AWH.
  assert (AR : aw_real AI ACCT UNIV aw LB (ms_mem ms) mo L RNG sta LBa) by (exists W; split; [exact WOF| exact ARW]).
  pose proof (SBVall LB AR) as SBV. pose proof (SBUall LB AR) as SBU.
  set (W' := mkWit (w_L W) RNG' sta' (w_LBa W) (w_T W) (w_FA W) m' (w_zc W)).
  assert (AR' : aw_realW AI ACCT UNIV aw LB m' mo' W').
  { destruct WOF as (E1 & E2 & E3 & E4). pose proof ARW as [(_ & _ & _ & HFA & _) _].
    apply (aw_real_nodelta AI ACCT UNIV AI_fake aw aw LB (ms_mem ms) mo W RNG' sta' m' mo' ARW); [rewrite E1, E4; exact AH'| rewrite E1, E4; exact AC'| | rewrite E4; exact TWP].
    intros b x Hb FK Hx. apply (KEEPW b x); [rewrite <- E4; exact Hb| exact FK| exact Hx]. }
  assert (TI' : ties W' (wins_of E nn rest)) by (apply (ties_ext W W'); [reflexivity| intros b; reflexivity| reflexivity| exact TI| intros b _ V; exact V| destruct WOF as (_ & _ & E3 & _); rewrite E3; exact PSN]).
  pose proof STK' as STK2.

  assert (WINK : forall k0 len kd, True -> CtrA.win_lookup wnl k0 = Some (len, kd) ->
            forall a, bv_unsigned (ev E k0) <= a < bv_unsigned (ev E k0) + bv_unsigned (den E len) -> in_user LB a).
  { intros k0 len kd _ WL a Ha.
    destruct (HeapCtrB.nonstack_windows_In E nn rest wnl k0 len kd NW (HeapCtrB.win_lookup_In _ _ _ _ WL)) as (_ & _ & KD & INW).
    pose proof (proj1 (Forall_forall _ _) WF _ INW) as (W1 & W2 & W3 & [[KS0 _]|[[KB B]|[KS2 (b & Hb & SUB)]]]); unfold w_iv in *; cbn [w_kind w_lo w_len] in *.
    - exfalso. exact (KD KS0).
    - apply in_ivs_In. eexists. split; [exact B|]. unfold in_iv. cbn [fst snd]. lia.
    - apply in_ivs_In. exists b. split; [exact Hb|]. apply SUB. unfold in_iv. cbn [fst snd]. lia. }

  assert (DECN : decode (map (den (CtrFrame.E' E st Fv Gv)) hargs) = Some (w2Z md, den E A, wins_of E nn rest, map (den E) (skipn (3 * nn) rest)))
    by exact (CtrFrame.DEC' E st FOK Fv Gv nn rest hargs md A nw Hf Eh Tnw Nn Ln).
  assert (HOLDN : op_holds OPS HEAP_ID (map (den (CtrFrame.E' E st Fv Gv)) hargs) m' mo').
  { rewrite OPS_holds1. exists (w2Z md), aw, (wins_of E nn rest), (map (den E) (skipn (3 * nn) rest)), LB, W'.
    split; [rewrite AWden; exact DECN|]. split; [exact (proj1 AR')|]. split; [exact WF|]. split; [| exact TI'].
    apply (cw_frame Cw _ _ _ _ (ms_mem ms) m' HC). intros a Ha U _. symmetry. unfold ALib.Mem.wa in SBU.
    apply (SBU a ltac:(unfold two64 in Ha; lia)). exact U. }
  rewrite <- (set_op_same HEAP_ID hargs (s_ops st) Hf).
  replace (s_regs st1) with (CtrFrame.RgPg st ks rss ksp [] []).
  2:{ unfold forget_stack_below_sp_g in FS. rewrite SPR, Hksp in FS. injection FS as <-. reflexivity. }
  apply (CtrFrame.frame_st_ok AI IMGX IMGX_aci ACCT UNIV OPS AI_fake OPS_fp1 OPS_cov1 OPS_frame_other OPS_fp_other OTHER OPS_mo_other OPS_cov0_img
           E st ms mo HS FOK Fv Gv r st1 CP FS R' m' mo' KEPT HF aw LB LB AWH MINV' SBV SBO WBM SBT ks offs rss ksp SPR SPE wnl nn rest AJ WF (fun _ => True) WINK ltac:(intros; exact I) ltac:(intros; exact I)
           K16 LOSP STK2 FLOOR hargs md A nw Hf Hc Eh Tnw Nn Ln OTH [] [] (NoDup_nil _)
           ltac:(intros k1 r1 X; destruct X) ltac:(intros k0 _; exact I) (fun _ => False) ltac:(intros k1 r1 X; destruct X) ltac:(intros k1 r1 a1 X; destruct X)
           ltac:(intros a1 X; destruct X) ltac:(intros a1 X; destruct X) ltac:(intros a1 X; destruct X) ltac:(intros k1 r1 k2 r2 a1 X; destruct X)
           hargs (w2Z md) (den E A) (wins_of E nn rest) (map (den E) (skipn (3 * nn) rest)) DECN HOLDN).
  - intros a X. destruct X.
  - intros a Ha NIX NWS. left. exact NWS.
  - intros a _ X. exact X.
  - exact (so_facts _ _ _ _ _ _ (CtrFrame.HS' OPS E st ms mo HS FOK Fv Gv)).
  - exact DV.
  - exact MINVo.
Qed.

End NoDelta.

From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.BothW Require Import BImg.
Module TwinB.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.PropExec OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.MState OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Cells OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Frame OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.ITree OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Nodes.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA.AcctCore OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA.ExecF OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA.ITreeA OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA.NodesA.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.STree OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.AsanCtrl OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.AsanEmbed.
Import AProto.TwinB AMalloc_iface.TwinB AMalloc_iface2.TwinB.
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

Unset Nia Cache. Unset Nra Cache.
Import ValP MemP CtrFX.
Import ActrA.
Module AP := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.PropExec.

Lemma set_op_same : forall id args os, find_op id os = Some args -> set_op id args os = os.
Proof.
  induction os as [|o os IH]; intros H; cbn [find_op set_op] in *; [reflexivity|].
  destruct (PrimInt63.eqb (op_id o) id) eqn:Q.
  - injection H as <-. apply Uint63.eqb_correct in Q. destruct o; cbn in *. subst. reflexivity.
  - f_equal. exact (IH H).
Qed.

Section NoDelta.
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

Theorem nodelta_st_ok : forall E st ms mo r hargs wnl L RNG sta LBa aw st1 Fv Gv R' m' mo' RNG' sta' (v : sv) (nx' : int),
  st_ok bsegs OPS E st ms mo -> call_pre st = Some r -> forget_stack_below_sp_g st = Some st1 ->
  CtrPre.TwinB.acallG AI ACCT UNIV Cw E st ms mo r hargs wnl L RNG sta LBa aw ->

  (forall rg, In rg CtrFrame.TwinB.kept_regsA -> AP.getr R' rg = AP.getr (ms_regs ms) rg) ->
  (forall x i, clob_pos x = Some i -> Fv (Z.of_nat i) = AP.getr R' (reg_of_r5 x)) ->
  den (CtrFrame.TwinB.E' E st Fv Gv) v = AP.getr R' 10%bv ->

  ALib.Mem.mem_inv bsegs m' ->
  stk bsegs m' (CtrPre.TwinB.sp_lo E st) (bv_unsigned (AP.getr (ms_regs ms) 2%bv)) ->

  (forall LB, aw_real AI ACCT UNIV aw LB (ms_mem ms) mo L RNG sta LBa -> forall a, 0 <= a < 2 ^ 64 -> CtrFrame.TwinB.stableA AI ms LB a ->
     rb bsegs m' a = rb bsegs (ms_mem ms) a /\ (wb bsegs (ms_mem ms) a = true -> wb bsegs m' a = true)) ->
  (forall LB, aw_real AI ACCT UNIV aw LB (ms_mem ms) mo L RNG sta LBa -> forall a, 0 <= a < 2 ^ 64 -> in_user LB a ->
     m' (ALib.Mem.wa a) = ms_mem ms (ALib.Mem.wa a)) ->
  (forall o a, In o (s_ops st) -> not_id HEAP_ID o -> 0 <= a < two64 ->
     Exists (fun iv => fst iv <= a < snd iv) (op_fp OPS (op_id o) (map (den (CtrFrame.TwinB.E' E st Fv Gv)) (op_args o))) ->
     m' (Z_to_bv 64 a) = ms_mem ms (Z_to_bv 64 a)) ->
  (forall a, 0 <= a < two64 -> (in_ranges (aci AI) a \/ (exists a', in_ranges (aci AI) a' /\ a = shad a') \/ (exists a', ATOP <= a' < 2 ^ 47 /\ a = shad a')) ->
     wb bsegs (ms_mem ms) a = true -> wb bsegs m' a = true) ->

  (forall a, 0 <= a < 2 ^ 64 -> sh_cov a -> in_based E (s_regs st) a ->
     rb bsegs m' a = rb bsegs (ms_mem ms) a /\ (wb bsegs (ms_mem ms) a = true -> wb bsegs m' a = true)) ->

  AHEAP AI L RNG' sta' LBa m' -> ACCT aw L RNG' sta' LBa mo' ->
  (forall b x, In b LBa -> is_fake b -> ab_addr b <= x < ab_addr b + ab_size b -> m' (ALib.Mem.wa x) = ms_mem ms (ALib.Mem.wa x)) ->
  twins_pres LBa (ms_mem ms) m' ->
  OTHER mo mo' -> op_minv OPS mo' ->
  (aprist sta -> aprist sta') ->
  st_ok bsegs OPS (CtrFrame.TwinB.E' E st Fv Gv)
    (SS r (rf_set (s_rf (clobber st1)) X10 v) (s_ff st) (s_resv st) (s_regs st1) (s_facts st) (s_ops st) (s_priv st) nx')
    (CtrFrame.TwinB.ms' ms r R' m') mo'.
Proof.
  intros E st ms mo r hargs wnl L RNG sta LBa aw st1 Fv Gv R' m' mo' RNG' sta' v nx' HS CP FS CF KEPT HF DV MINV' STK' SBVall SBUall SBO WBM SBT AH' AC' KEEPW TWP OTH MINVo PSN.
  destruct CF as (LB & ks & offs & rss & ksp & nn & md & A & nw & rest & SPR & Hksp & SPE & K16 & LOSP & FLOOR & Hf & Hc & Eh & Tnw & Nn & Ln & N255
                  & NW & AN & AJ & TS & WF & HC & AWden & (W & WOF & ARW & TI)).
  destruct (HeapCtr.TwinB.call_pre_inv st r CP) as (FOK & _).
  pose proof (aw_real_holds AI ACCT UNIV _ _ _ _ _ ARW) as AWH.
  assert (AR : aw_real AI ACCT UNIV aw LB (ms_mem ms) mo L RNG sta LBa) by (exists W; split; [exact WOF| exact ARW]).
  pose proof (SBVall LB AR) as SBV. pose proof (SBUall LB AR) as SBU.
  set (W' := mkWit (w_L W) RNG' sta' (w_LBa W) (w_T W) (w_FA W) m' (w_zc W)).
  assert (AR' : aw_realW AI ACCT UNIV aw LB m' mo' W').
  { destruct WOF as (E1 & E2 & E3 & E4). pose proof ARW as [(_ & _ & _ & HFA & _) _].
    apply (aw_real_nodelta AI ACCT UNIV AI_fake aw aw LB (ms_mem ms) mo W RNG' sta' m' mo' ARW); [rewrite E1, E4; exact AH'| rewrite E1, E4; exact AC'| | rewrite E4; exact TWP].
    intros b x Hb FK Hx. apply (KEEPW b x); [rewrite <- E4; exact Hb| exact FK| exact Hx]. }
  assert (TI' : ties W' (wins_of E nn rest)) by (apply (ties_ext W W'); [reflexivity| intros b; reflexivity| reflexivity| exact TI| intros b _ V; exact V| destruct WOF as (_ & _ & E3 & _); rewrite E3; exact PSN]).
  pose proof STK' as STK2.

  assert (WINK : forall k0 len kd, True -> CtrA.win_lookup wnl k0 = Some (len, kd) ->
            forall a, bv_unsigned (ev E k0) <= a < bv_unsigned (ev E k0) + bv_unsigned (den E len) -> in_user LB a).
  { intros k0 len kd _ WL a Ha.
    destruct (HeapCtrB.TwinB.nonstack_windows_In E nn rest wnl k0 len kd NW (HeapCtrB.TwinB.win_lookup_In _ _ _ _ WL)) as (_ & _ & KD & INW).
    pose proof (proj1 (Forall_forall _ _) WF _ INW) as (W1 & W2 & W3 & [[KS0 _]|[[KB B]|[KS2 (b & Hb & SUB)]]]); unfold w_iv in *; cbn [w_kind w_lo w_len] in *.
    - exfalso. exact (KD KS0).
    - apply in_ivs_In. eexists. split; [exact B|]. unfold in_iv. cbn [fst snd]. lia.
    - apply in_ivs_In. exists b. split; [exact Hb|]. apply SUB. unfold in_iv. cbn [fst snd]. lia. }

  assert (DECN : decode (map (den (CtrFrame.TwinB.E' E st Fv Gv)) hargs) = Some (w2Z md, den E A, wins_of E nn rest, map (den E) (skipn (3 * nn) rest)))
    by exact (CtrFrame.TwinB.DEC' E st FOK Fv Gv nn rest hargs md A nw Hf Eh Tnw Nn Ln).
  assert (HOLDN : op_holds OPS HEAP_ID (map (den (CtrFrame.TwinB.E' E st Fv Gv)) hargs) m' mo').
  { rewrite OPS_holds1. exists (w2Z md), aw, (wins_of E nn rest), (map (den E) (skipn (3 * nn) rest)), LB, W'.
    split; [rewrite AWden; exact DECN|]. split; [exact (proj1 AR')|]. split; [exact WF|]. split; [| exact TI'].
    apply (cw_frame Cw _ _ _ _ (ms_mem ms) m' HC). intros a Ha U _. symmetry. unfold ALib.Mem.wa in SBU.
    apply (SBU a ltac:(unfold two64 in Ha; lia)). exact U. }
  rewrite <- (set_op_same HEAP_ID hargs (s_ops st) Hf).
  replace (s_regs st1) with (CtrFrame.TwinB.RgPg st ks rss ksp [] []).
  2:{ unfold forget_stack_below_sp_g in FS. rewrite SPR, Hksp in FS. injection FS as <-. reflexivity. }
  apply (CtrFrame.TwinB.frame_st_ok AI IMGX IMGX_aci ACCT UNIV OPS AI_fake OPS_fp1 OPS_cov1 OPS_frame_other OPS_fp_other OTHER OPS_mo_other OPS_cov0_img
           E st ms mo HS FOK Fv Gv r st1 CP FS R' m' mo' KEPT HF aw LB LB AWH MINV' SBV SBO WBM SBT ks offs rss ksp SPR SPE wnl nn rest AJ WF (fun _ => True) WINK ltac:(intros; exact I) ltac:(intros; exact I)
           K16 LOSP STK2 FLOOR hargs md A nw Hf Hc Eh Tnw Nn Ln OTH [] [] (NoDup_nil _)
           ltac:(intros k1 r1 X; destruct X) ltac:(intros k0 _; exact I) (fun _ => False) ltac:(intros k1 r1 X; destruct X) ltac:(intros k1 r1 a1 X; destruct X)
           ltac:(intros a1 X; destruct X) ltac:(intros a1 X; destruct X) ltac:(intros a1 X; destruct X) ltac:(intros k1 r1 k2 r2 a1 X; destruct X)
           hargs (w2Z md) (den E A) (wins_of E nn rest) (map (den E) (skipn (3 * nn) rest)) DECN HOLDN).
  - intros a X. destruct X.
  - intros a Ha NIX NWS. left. exact NWS.
  - intros a _ X. exact X.
  - exact (so_facts _ _ _ _ _ _ (CtrFrame.TwinB.HS' OPS E st ms mo HS FOK Fv Gv)).
  - exact DV.
  - exact MINVo.
Qed.

End NoDelta.
End TwinB.
