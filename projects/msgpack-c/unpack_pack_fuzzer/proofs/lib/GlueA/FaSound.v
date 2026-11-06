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
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Bridge Require CallA CallV GlueA CtrPre FrameV CtrDelta CtrFree.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.GlueA Require Import ActrB FfShape FaC FaShape.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.GlueA Require FaPost FaBurn.
Unset Nia Cache. Unset Nra Cache.
Import ValP MemP CtrFX ActrA.
Module AP := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.PropExec.
Module AM := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Mem.
Module AS := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Step.

Lemma abandon_one_shape : forall segs st st', FaC.abandon_one segs st = Some st' ->
  exists kf shf hargs wnl i0 len rsh h1 h2 h3,
    s_resv st = RNone /\ ActrA.aheap_windows st = Some (hargs, wnl)
    /\ ActrB.find_twin (s_facts st) kf = Some shf
    /\ heap_find_window hargs (VP kf wzero) = Some (i0, len, VL ActrB.K_FRAME)
    /\ IMap.find shf (s_regs st) = Some rsh /\ fresh_ok st = true
    /\ ActrA.afree_ok_k ActrB.K_FRAME ActrB.K_FTWIN st wnl kf shf = true
    /\ ActrA.stack_room_g st 0%uint63 = true /\ ActrA.sp_floor_ok st hargs = true
    /\ rg_lo rsh = 0%uint63 /\ (exists lent kdt, CtrA.win_lookup wnl shf = Some (lent, kdt) /\ known_eq (s_facts st) (rg_hi rsh) lent = true)
    /\ ActrB.heap_del_window_k hargs (VP kf wzero) ActrB.K_FRAME = Some h1
    /\ ActrB.heap_del_window_k h1 (VP shf wzero) ActrB.K_FTWIN = Some h2
    /\ FaC.heap_pay (s_facts st) h2 1%uint63 = Some h3
    /\ st' = set_ops (setregs st (IMap.remove shf (IMap.remove kf (s_regs st)))) (set_op HEAP_ID h3 (s_ops st)).
Proof.
  intros segs st st' H. unfold FaC.abandon_one in H.
  destruct (s_resv st) eqn:RV; try discriminate H.
  destruct (ActrA.aheap_windows st) as [[hargs wnl]|] eqn:AW; [|discriminate H].
  destruct (heap_nwin hargs) as [n|] eqn:HN; [|discriminate H].
  destruct hargs as [|[md| | | | | | | | | |] [|a [|[nw| | | | | | | | | |] rest]]]; try discriminate H.
  destruct (FaC.first_dead segs n (firstn (3 * n) rest) st) as [kf|] eqn:FD; [|discriminate H].
  destruct (ActrB.find_twin (s_facts st) kf) as [shf|] eqn:FT; [|discriminate H].
  destruct (heap_find_window (VL md :: a :: VL nw :: rest) (VP kf wzero)) as [[[i0 len] kd]|] eqn:FW; [|discriminate H].
  destruct (IMap.find shf (s_regs st)) as [rsh|] eqn:FR; [|discriminate H].
  match type of H with (if ?c then _ else _) = _ => destruct c eqn:CK; [|discriminate H] end.
  repeat match type of CK with (_ && _)%bool = true => let X := fresh "Q" in apply andb_prop in CK as [CK X] end.
  destruct (ActrB.heap_del_window_k (VL md :: a :: VL nw :: rest) (VP kf wzero) ActrB.K_FRAME) as [h1|] eqn:H1; [|discriminate H].
  destruct (ActrB.heap_del_window_k h1 (VP shf wzero) ActrB.K_FTWIN) as [h2|] eqn:H2; [|discriminate H].
  destruct (FaC.heap_pay (s_facts st) h2 1%uint63) as [h3|] eqn:H3; [|discriminate H].
  injection H as <-.
  apply sv_eqb_eq in Q4. subst kd. apply Uint63.eqb_correct in Q0.
  destruct (CtrA.win_lookup wnl shf) as [[lent kdt]|] eqn:WLT; [|discriminate Q].
  exists kf, shf, (VL md :: a :: VL nw :: rest), wnl, i0, len, rsh, h1, h2, h3.
  repeat (split; [reflexivity || assumption|]).
  split; [exists lent, kdt; split; [exact WLT| exact Q]|]. repeat (split; [reflexivity || assumption|]). reflexivity.
Qed.

Lemma burn_shape : forall c st st', FaC.burn c st = Some st' ->
  exists hargs wnl h', s_resv st = RNone /\ ActrA.aheap_windows st = Some (hargs, wnl) /\ fresh_ok st = true
    /\ ActrA.stack_room_g st 0%uint63 = true /\ ActrA.sp_floor_ok st hargs = true
    /\ FaC.heap_pay (s_facts st) hargs c = Some h' /\ st' = set_ops st (set_op HEAP_ID h' (s_ops st)).
Proof.
  intros c st st' H. unfold FaC.burn in H.
  destruct (s_resv st) eqn:RV; try discriminate H.
  destruct (ActrA.aheap_windows st) as [[hargs wnl]|] eqn:AW; [|discriminate H].
  match type of H with (if ?cnd then _ else _) = _ => destruct cnd eqn:CK; [|discriminate H] end.
  apply andb_prop in CK as [CK Q0]. apply andb_prop in CK as [CK Q1].
  destruct (FaC.heap_pay (s_facts st) hargs c) as [h'|] eqn:HP; [|discriminate H]. injection H as <-.
  exists hargs, wnl, h'. repeat (split; [reflexivity || assumption|]). reflexivity.
Qed.

Section Sound.
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
Hypothesis Cw_ghost_free_f : forall kd md ca LB ws m b n ws', kd = K_FRAMEz \/ kd = K_FTWINz -> cw_holds Cw md ca LB ws m -> In (Win b n kd) ws ->
  (forall w, In w ws' <-> In w ws /\ w <> Win b n kd) -> cw_holds Cw md ca (remove iv_eq_dec (b, n) LB) ws' m.
Hypothesis Cw_zc : forall md ca LB ws ws' m zc zc', cw_holds Cw md ca LB ws m -> ZC_BASE + zc' < ZC_BAND ->
  (forall w, In w ws' <-> (In w ws /\ w <> zc_win zc) \/ w = zc_win zc') -> cw_holds Cw md ca LB ws' m.
Hypothesis OPS_frame_other : forall id args m m' mo, id <> HEAP_ID -> op_holds OPS id args m mo ->
  (forall a, 0 <= a < two64 -> Exists (fun iv => fst iv <= a < snd iv) (op_fp OPS id args) -> m (Z_to_bv 64 a) = m' (Z_to_bv 64 a)) ->
  (forall a, 0 <= a < two64 -> (in_ranges (aci AI) a \/ (exists a', in_ranges (aci AI) a' /\ a = shad a') \/ (exists a', ATOP <= a' < 2 ^ 47 /\ a = shad a')) -> wb asegs m a = true -> wb asegs m' a = true) ->
  op_holds OPS id args m' mo.
Hypothesis OPS_fp_other : forall id args a, id <> HEAP_ID -> Exists (fun iv => fst iv <= a < snd iv) (op_fp OPS id args) ->
  in_ranges (aci AI) a \/ (exists a', in_ranges (aci AI) a' /\ a = shad a') \/ (exists a', ATOP <= a' < 2 ^ 47 /\ a = shad a').
Variable OTHER : Model -> Model -> Prop.
Hypothesis OTHER_refl : forall mo, OTHER mo mo.
Hypothesis OPS_mo_other : forall id args m mo mo', id <> HEAP_ID -> OTHER mo mo' -> op_holds OPS id args m mo -> op_holds OPS id args m mo'.
Hypothesis OPS_cov0_img : forall a, (exists seg, find_segment asegs a 1 = Some seg) -> op_cov0 OPS a.
Variable MP : Model -> Prop.
Variable PB : (int -> list byte) -> Prop.

Lemma ghost_regs : forall E st ms mo (HS : st_ok asegs OPS E st ms mo) (FOK : fresh_ok st = true) Fv Gv pc',
  forall x, rget (Core (ms_regs ms) (ms_fregs ms) (Z_to_bv 64 (to_Z pc')) (ms_fcsr ms) None) (reg_of_r5 x) = den (CtrDelta.E' E st Fv Gv) (rf_get (s_rf st) x).
Proof.
  intros E st ms mo HS FOK Fv Gv pc' x.
  pose proof (so_regs _ _ _ _ _ _ (CtrDelta.HS' OPS E st ms mo HS FOK Fv Gv) x) as R0. unfold rget in R0 |- *. cbn [c_regs] in R0 |- *. exact R0.
Qed.

Lemma mem_inv_of : forall E st ms mo, st_ok asegs OPS E st ms mo -> AM.mem_inv asegs (ms_mem ms).
Proof.
  intros E st ms mo HS a b Hm. unfold AM.ro_addr. destruct (find_segment asegs (bv_unsigned a) 1) as [seg|] eqn:Fs; [|reflexivity].
  rewrite (so_minv _ _ _ _ _ _ HS a b Hm seg Fs). reflexivity.
Qed.

Lemma abandon_one_ok : forall E st ms mo st', st_ok asegs OPS E st ms mo -> FaC.abandon_one asegs st = Some st' ->
  exists E1, env_ext (s_next st) E E1 /\ st_ok asegs OPS E1 st' ms mo /\ s_next st' = s_next st /\ s_pc st' = s_pc st.
Proof.
  intros E st ms mo st' HS H.
  destruct (abandon_one_shape asegs st st' H)
    as (kf & shf & hargs & wnl & i0 & len0 & rsh & h1 & h2 & h3 & RVN & AW & FT & FW & FRS & FOK & FOKk & SRG & SFO & LO0s & (lent0 & kdt & WLT0 & KEQ) & H1 & H2 & H3 & ->).
  destruct (CtrPre.aheap_call_facts AI ACCT UNIV Cw OPS AI_fake OPS_holds1 E st ms mo hargs wnl HS AW)
    as (r1 & n & md & A & nw & rest & LB & Hr1 & Hf & Hc & Hn & Eh & T & N & Ln & N255 & SW & NW & AN & JU & HA & WF & HC & W & ARW & TI).
  destruct (CallA.stack_sound_g asegs OPS E st ms mo 0%uint63 HS ltac:(change (to_Z 0%uint63) with 0; lia) SRG)
    as (ks & offs & rss & ksp & HX2 & Hrs & K0 & Hksp & K16 & A16 & Esp & LOX & HI64 & STK & SPR & LOR & LOZ0).
  destruct (CallA.sp_floor_sound asegs OPS E st ms mo hargs n md A nw rest ks offs rss HS SFO Hn Eh SPR LOZ0) as (wlo & len & INw & FLOOR0).
  pose proof (proj1 (Forall_forall _ _) WF _ INw) as (_ & _ & _ & KDs). cbn [w_kind w_lo] in KDs.
  assert (CE : ATOP + 4096 <= bv_unsigned (den E (VP STACK_ID wlo))).
  { destruct KDs as [[_ C]|[[K1 _]|[K1 _]]]; [exact C| unfold K_BLOCK, K_STACK in K1; lia| unfold K_SUB, K_STACK in K1; lia]. }
  change (to_Z 0%uint63) with 0 in LOR.
  set (R := ms_regs ms) in *. set (m := ms_mem ms) in *.
  assert (SP2 : bv_unsigned (AP.getr R 2%bv) = bv_unsigned (ev E ks) + keyZ ksp).
  { unfold R. rewrite <- HeapCtr.reg_of_X2, (GlueA.getr_RA asegs OPS E st ms mo HS X2). exact Esp. }
  destruct (CtrFree.afree_ok_k_inv OPS ActrB.K_FRAME ActrB.K_FTWIN E st ms mo wnl kf shf HS FOKk)
    as (rf & lenf & lent & Frf & WLf & WLt & BTs & LO0 & POSf & LEf & OTHERS).
  rewrite WLt in WLT0. injection WLT0 as <- <-.
  assert (FULLs : hiZ E rsh = bv_unsigned (den E lent)).
  { unfold hiZ. rewrite (HeapCtr.known_eq_sound E _ _ _ (so_facts _ _ _ _ _ _ HS) KEQ). reflexivity. }
  destruct (FaPost.owner_f AI ACCT UNIV OPS AI_fake E st ms mo HS wnl n rest LB (den E A) NW WF W ARW TI kf shf lenf lent WLf WLt BTs)
    as (fb & VF & EAf & ENf & ESH & ELT & INU & INS & UIV & SIV).
  set (Fv := fun _ : Z => Z_to_bv 64 0). set (Gv := fun (_ _ : Z) => Z_to_bv 8 0).
  exists (CtrDelta.E' E st Fv Gv). split; [exact (CtrDelta.EXT E st Fv Gv)|]. split; [| split; reflexivity].
  pose proof (FaPost.fa_post_ok AI IMGX IMGX_aci ACCT UNIV Cw OPS AI_fake OPS_holds1 OPS_fp1 OPS_cov1 Cw_ghost_free_f Cw_zc OPS_frame_other OPS_fp_other OTHER OPS_mo_other OPS_cov0_img
             E st ms mo HS wnl n rest LB (den E A) NW AN WF W ARW TI kf shf rf rsh lenf lent Frf FRS WLf WLt LO0 POSf LO0s FULLs OTHERS
             fb VF EAf ENf ESH ELT INU INS UIV SIV hargs md A nw Hf Eh T N Ln FOK Fv Gv h1 h2 H1 H2 h3 H3 eq_refl HC
             R (mem_inv_of E st ms mo HS) ks offs rss ksp SPR SP2 JU ltac:(lia) ltac:(lia) Hc (OTHER_refl mo) (so_mf _ _ _ _ _ _ HS)
             (s_pc st) (s_rf st) (s_next st) RVN (so_x0 _ _ _ _ _ _ HS) (ghost_regs E st ms mo HS FOK Fv Gv (s_pc st))) as HSF.
  rewrite (GlueA.ms_formA asegs OPS E st ms mo HS RVN) at 1. fold R m.
  unfold set_ops, setregs. cbn [s_pc s_rf s_ff s_resv s_regs s_facts s_ops s_priv s_next]. rewrite RVN. exact HSF.
Qed.

Lemma burn_ok : forall c E st ms mo st', st_ok asegs OPS E st ms mo -> FaC.burn c st = Some st' ->
  exists E1, env_ext (s_next st) E E1 /\ st_ok asegs OPS E1 st' ms mo.
Proof.
  intros c E st ms mo st' HS H.
  destruct (burn_shape c st st' H) as (hargs & wnl & h' & RVN & AW & FOK & SRG & SFO & HP & ->).
  destruct (CtrPre.aheap_call_facts AI ACCT UNIV Cw OPS AI_fake OPS_holds1 E st ms mo hargs wnl HS AW)
    as (r1 & n & md & A & nw & rest & LB & Hr1 & Hf & Hc & Hn & Eh & T & N & Ln & N255 & SW & NW & AN & JU & HA & WF & HC & W & ARW & TI).
  destruct (CallA.stack_sound_g asegs OPS E st ms mo 0%uint63 HS ltac:(change (to_Z 0%uint63) with 0; lia) SRG)
    as (ks & offs & rss & ksp & HX2 & Hrs & K0 & Hksp & K16 & A16 & Esp & LOX & HI64 & STK & SPR & LOR & LOZ0).
  destruct (CallA.sp_floor_sound asegs OPS E st ms mo hargs n md A nw rest ks offs rss HS SFO Hn Eh SPR LOZ0) as (wlo & len & INw & FLOOR0).
  pose proof (proj1 (Forall_forall _ _) WF _ INw) as (_ & _ & _ & KDs). cbn [w_kind w_lo] in KDs.
  assert (CE : ATOP + 4096 <= bv_unsigned (den E (VP STACK_ID wlo))).
  { destruct KDs as [[_ C]|[[K1 _]|[K1 _]]]; [exact C| unfold K_BLOCK, K_STACK in K1; lia| unfold K_SUB, K_STACK in K1; lia]. }
  change (to_Z 0%uint63) with 0 in LOR.
  set (R := ms_regs ms) in *. set (m := ms_mem ms) in *.
  assert (SP2 : bv_unsigned (AP.getr R 2%bv) = bv_unsigned (ev E ks) + keyZ ksp).
  { unfold R. rewrite <- HeapCtr.reg_of_X2, (GlueA.getr_RA asegs OPS E st ms mo HS X2). exact Esp. }
  set (Fv := fun _ : Z => Z_to_bv 64 0). set (Gv := fun (_ _ : Z) => Z_to_bv 8 0).
  exists (CtrDelta.E' E st Fv Gv). split; [exact (CtrDelta.EXT E st Fv Gv)|].
  pose proof (FaBurn.fa_burn_ok AI IMGX IMGX_aci ACCT UNIV Cw OPS AI_fake OPS_holds1 OPS_fp1 OPS_cov1 Cw_zc OPS_frame_other OPS_fp_other OTHER OPS_mo_other OPS_cov0_img
             E st ms mo HS wnl n rest LB (den E A) NW WF W ARW TI hargs md A nw Hf Eh T N Ln FOK Fv Gv c h' HP eq_refl HC
             R (mem_inv_of E st ms mo HS) ks offs rss ksp SPR SP2 JU ltac:(lia) ltac:(lia) Hc (OTHER_refl mo) (so_mf _ _ _ _ _ _ HS)
             (s_pc st) (s_rf st) (s_next st) RVN (so_x0 _ _ _ _ _ _ HS) (ghost_regs E st ms mo HS FOK Fv Gv (s_pc st))) as HSF.
  rewrite (GlueA.ms_formA asegs OPS E st ms mo HS RVN) at 1. fold R m.
  unfold set_ops. cbn [s_pc s_rf s_ff s_resv s_regs s_facts s_ops s_priv s_next]. rewrite RVN. exact HSF.
Qed.

Lemma abandon_loop_ok : forall fuel E st ms mo cnt st' cnt', st_ok asegs OPS E st ms mo -> FaC.abandon_loop asegs fuel st cnt = (st', cnt') ->
  exists E1, env_ext (s_next st) E E1 /\ st_ok asegs OPS E1 st' ms mo /\ s_next st' = s_next st.
Proof.
  induction fuel as [|f IH]; intros E st ms mo cnt st' cnt' HS H; cbn [FaC.abandon_loop] in H.
  - injection H as <- <-. exists E. split; [apply env_ext_refl|]. split; [exact HS| reflexivity].
  - destruct (FaC.abandon_one asegs st) as [st1|] eqn:A1.
    + destruct (abandon_one_ok E st ms mo st1 HS A1) as (E1 & X1 & HS1 & NX1 & _).
      destruct (IH E1 st1 ms mo (S cnt) st' cnt' HS1 H) as (E2 & X2 & HS2 & NX2).
      exists E2. split; [| split; [exact HS2| rewrite NX2; exact NX1]].
      rewrite NX1 in X2. exact (env_ext_trans (s_next st) (s_next st) E E1 E2 (Z.le_refl _) X1 X2).
    + injection H as <- <-. exists E. split; [apply env_ext_refl|]. split; [exact HS| reflexivity].
Qed.

Theorem frame_abandon_sound : forall pc, contract_sound asegs OPS MP PB (FaC.frame_abandon_c asegs pc).
Proof.
  intros pc st sts Hspc Happ K E ms mo HS HMP HPB HK. cbn [c_apply FaC.frame_abandon_c] in Happ. unfold FaC.frame_abandon_apply in Happ.
  destruct (FaC.abandon_loop asegs 16 st 0) as [st1 cnt] eqn:LP.
  destruct (abandon_loop_ok 16 E st ms mo 0%nat st1 cnt HS LP) as (E1 & X1 & HS1 & NX1).
  destruct (Nat.eqb cnt 0); [discriminate Happ|].
  destruct (Nat.eqb cnt 16).
  - injection Happ as <-. exact (HK st1 (or_introl eq_refl) E1 ms mo X1 HMP HS1).
  - destruct (FaC.burn (of_Z (Z.of_nat (16 - cnt))) st1) as [st2|] eqn:B; [|discriminate Happ]. injection Happ as <-.
    destruct (burn_ok _ E1 st1 ms mo st2 HS1 B) as (E2 & X2 & HS2).
    rewrite NX1 in X2.
    exact (HK st2 (or_introl eq_refl) E2 ms mo (env_ext_trans (s_next st) (s_next st) E E1 E2 (Z.le_refl _) X1 X2) HMP HS2).
Qed.

Theorem settle_sound : forall pc, contract_sound asegs OPS MP PB (FaC.settle_c asegs pc).
Proof.
  intros pc st sts Hspc Happ K E ms mo HS HMP HPB HK. cbn [c_apply FaC.settle_c] in Happ. unfold FaC.settle_apply in Happ.
  destruct (FaC.abandon_loop asegs 16 st 0) as [st1 cnt] eqn:LP.
  destruct (abandon_loop_ok 16 E st ms mo 0%nat st1 cnt HS LP) as (E1 & X1 & HS1 & NX1).
  destruct (Nat.eqb cnt 16).
  - injection Happ as <-. exact (HK st1 (or_introl eq_refl) E1 ms mo X1 HMP HS1).
  - destruct (FaC.burn (of_Z (Z.of_nat (16 - cnt))) st1) as [st2|] eqn:B; [|discriminate Happ]. injection Happ as <-.
    destruct (burn_ok _ E1 st1 ms mo st2 HS1 B) as (E2 & X2 & HS2).
    rewrite NX1 in X2.
    exact (HK st2 (or_introl eq_refl) E2 ms mo (env_ext_trans (s_next st) (s_next st) E E1 E2 (Z.le_refl _) X1 X2) HMP HS2).
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
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.W64Proofs OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.ValProofs OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.MemProofs OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.StepSoundBase.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Br.CtrFX.

Import ActrB.TwinB FfShape.TwinB FaC.TwinB FaShape.TwinB.

Unset Nia Cache. Unset Nra Cache.
Import ValP MemP CtrFX ActrA.
Module AP := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.PropExec.
Module AM := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Mem.
Module AS := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Step.

Lemma abandon_one_shape : forall segs st st', FaC.TwinB.FaC.abandon_one segs st = Some st' ->
  exists kf shf hargs wnl i0 len rsh h1 h2 h3,
    s_resv st = RNone /\ ActrA.aheap_windows st = Some (hargs, wnl)
    /\ ActrB.TwinB.ActrB.find_twin (s_facts st) kf = Some shf
    /\ heap_find_window hargs (VP kf wzero) = Some (i0, len, VL ActrB.TwinB.ActrB.K_FRAME)
    /\ IMap.find shf (s_regs st) = Some rsh /\ fresh_ok st = true
    /\ ActrA.afree_ok_k ActrB.TwinB.ActrB.K_FRAME ActrB.TwinB.ActrB.K_FTWIN st wnl kf shf = true
    /\ ActrA.stack_room_g st 0%uint63 = true /\ ActrA.sp_floor_ok st hargs = true
    /\ rg_lo rsh = 0%uint63 /\ (exists lent kdt, CtrA.win_lookup wnl shf = Some (lent, kdt) /\ known_eq (s_facts st) (rg_hi rsh) lent = true)
    /\ ActrB.TwinB.ActrB.heap_del_window_k hargs (VP kf wzero) ActrB.TwinB.ActrB.K_FRAME = Some h1
    /\ ActrB.TwinB.ActrB.heap_del_window_k h1 (VP shf wzero) ActrB.TwinB.ActrB.K_FTWIN = Some h2
    /\ FaC.TwinB.FaC.heap_pay (s_facts st) h2 1%uint63 = Some h3
    /\ st' = set_ops (setregs st (IMap.remove shf (IMap.remove kf (s_regs st)))) (set_op HEAP_ID h3 (s_ops st)).
Proof.
  intros segs st st' H. unfold FaC.TwinB.FaC.abandon_one in H.
  destruct (s_resv st) eqn:RV; try discriminate H.
  destruct (ActrA.aheap_windows st) as [[hargs wnl]|] eqn:AW; [|discriminate H].
  destruct (heap_nwin hargs) as [n|] eqn:HN; [|discriminate H].
  destruct hargs as [|[md| | | | | | | | | |] [|a [|[nw| | | | | | | | | |] rest]]]; try discriminate H.
  destruct (FaC.TwinB.FaC.first_dead segs n (firstn (3 * n) rest) st) as [kf|] eqn:FD; [|discriminate H].
  destruct (ActrB.TwinB.ActrB.find_twin (s_facts st) kf) as [shf|] eqn:FT; [|discriminate H].
  destruct (heap_find_window (VL md :: a :: VL nw :: rest) (VP kf wzero)) as [[[i0 len] kd]|] eqn:FW; [|discriminate H].
  destruct (IMap.find shf (s_regs st)) as [rsh|] eqn:FR; [|discriminate H].
  match type of H with (if ?c then _ else _) = _ => destruct c eqn:CK; [|discriminate H] end.
  repeat match type of CK with (_ && _)%bool = true => let X := fresh "Q" in apply andb_prop in CK as [CK X] end.
  destruct (ActrB.TwinB.ActrB.heap_del_window_k (VL md :: a :: VL nw :: rest) (VP kf wzero) ActrB.TwinB.ActrB.K_FRAME) as [h1|] eqn:H1; [|discriminate H].
  destruct (ActrB.TwinB.ActrB.heap_del_window_k h1 (VP shf wzero) ActrB.TwinB.ActrB.K_FTWIN) as [h2|] eqn:H2; [|discriminate H].
  destruct (FaC.TwinB.FaC.heap_pay (s_facts st) h2 1%uint63) as [h3|] eqn:H3; [|discriminate H].
  injection H as <-.
  apply sv_eqb_eq in Q4. subst kd. apply Uint63.eqb_correct in Q0.
  destruct (CtrA.win_lookup wnl shf) as [[lent kdt]|] eqn:WLT; [|discriminate Q].
  exists kf, shf, (VL md :: a :: VL nw :: rest), wnl, i0, len, rsh, h1, h2, h3.
  repeat (split; [reflexivity || assumption|]).
  split; [exists lent, kdt; split; [exact WLT| exact Q]|]. repeat (split; [reflexivity || assumption|]). reflexivity.
Qed.

Lemma burn_shape : forall c st st', FaC.TwinB.FaC.burn c st = Some st' ->
  exists hargs wnl h', s_resv st = RNone /\ ActrA.aheap_windows st = Some (hargs, wnl) /\ fresh_ok st = true
    /\ ActrA.stack_room_g st 0%uint63 = true /\ ActrA.sp_floor_ok st hargs = true
    /\ FaC.TwinB.FaC.heap_pay (s_facts st) hargs c = Some h' /\ st' = set_ops st (set_op HEAP_ID h' (s_ops st)).
Proof.
  intros c st st' H. unfold FaC.TwinB.FaC.burn in H.
  destruct (s_resv st) eqn:RV; try discriminate H.
  destruct (ActrA.aheap_windows st) as [[hargs wnl]|] eqn:AW; [|discriminate H].
  match type of H with (if ?cnd then _ else _) = _ => destruct cnd eqn:CK; [|discriminate H] end.
  apply andb_prop in CK as [CK Q0]. apply andb_prop in CK as [CK Q1].
  destruct (FaC.TwinB.FaC.heap_pay (s_facts st) hargs c) as [h'|] eqn:HP; [|discriminate H]. injection H as <-.
  exists hargs, wnl, h'. repeat (split; [reflexivity || assumption|]). reflexivity.
Qed.

Section Sound.
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
Hypothesis Cw_ghost_free_f : forall kd md ca LB ws m b n ws', kd = K_FRAMEz \/ kd = K_FTWINz -> cw_holds Cw md ca LB ws m -> In (Win b n kd) ws ->
  (forall w, In w ws' <-> In w ws /\ w <> Win b n kd) -> cw_holds Cw md ca (remove iv_eq_dec (b, n) LB) ws' m.
Hypothesis Cw_zc : forall md ca LB ws ws' m zc zc', cw_holds Cw md ca LB ws m -> ZC_BASE + zc' < ZC_BAND ->
  (forall w, In w ws' <-> (In w ws /\ w <> zc_win zc) \/ w = zc_win zc') -> cw_holds Cw md ca LB ws' m.
Hypothesis OPS_frame_other : forall id args m m' mo, id <> HEAP_ID -> op_holds OPS id args m mo ->
  (forall a, 0 <= a < two64 -> Exists (fun iv => fst iv <= a < snd iv) (op_fp OPS id args) -> m (Z_to_bv 64 a) = m' (Z_to_bv 64 a)) ->
  (forall a, 0 <= a < two64 -> (in_ranges (aci AI) a \/ (exists a', in_ranges (aci AI) a' /\ a = shad a') \/ (exists a', ATOP <= a' < 2 ^ 47 /\ a = shad a')) -> wb bsegs m a = true -> wb bsegs m' a = true) ->
  op_holds OPS id args m' mo.
Hypothesis OPS_fp_other : forall id args a, id <> HEAP_ID -> Exists (fun iv => fst iv <= a < snd iv) (op_fp OPS id args) ->
  in_ranges (aci AI) a \/ (exists a', in_ranges (aci AI) a' /\ a = shad a') \/ (exists a', ATOP <= a' < 2 ^ 47 /\ a = shad a').
Variable OTHER : Model -> Model -> Prop.
Hypothesis OTHER_refl : forall mo, OTHER mo mo.
Hypothesis OPS_mo_other : forall id args m mo mo', id <> HEAP_ID -> OTHER mo mo' -> op_holds OPS id args m mo -> op_holds OPS id args m mo'.
Hypothesis OPS_cov0_img : forall a, (exists seg, find_segment bsegs a 1 = Some seg) -> op_cov0 OPS a.
Variable MP : Model -> Prop.
Variable PB : (int -> list byte) -> Prop.

Lemma ghost_regs : forall E st ms mo (HS : st_ok bsegs OPS E st ms mo) (FOK : fresh_ok st = true) Fv Gv pc',
  forall x, rget (Core (ms_regs ms) (ms_fregs ms) (Z_to_bv 64 (to_Z pc')) (ms_fcsr ms) None) (reg_of_r5 x) = den (CtrDelta.TwinB.E' E st Fv Gv) (rf_get (s_rf st) x).
Proof.
  intros E st ms mo HS FOK Fv Gv pc' x.
  pose proof (so_regs _ _ _ _ _ _ (CtrDelta.TwinB.HS' OPS E st ms mo HS FOK Fv Gv) x) as R0. unfold rget in R0 |- *. cbn [c_regs] in R0 |- *. exact R0.
Qed.

Lemma mem_inv_of : forall E st ms mo, st_ok bsegs OPS E st ms mo -> AM.mem_inv bsegs (ms_mem ms).
Proof.
  intros E st ms mo HS a b Hm. unfold AM.ro_addr. destruct (find_segment bsegs (bv_unsigned a) 1) as [seg|] eqn:Fs; [|reflexivity].
  rewrite (so_minv _ _ _ _ _ _ HS a b Hm seg Fs). reflexivity.
Qed.

Lemma abandon_one_ok : forall E st ms mo st', st_ok bsegs OPS E st ms mo -> FaC.TwinB.FaC.abandon_one bsegs st = Some st' ->
  exists E1, env_ext (s_next st) E E1 /\ st_ok bsegs OPS E1 st' ms mo /\ s_next st' = s_next st /\ s_pc st' = s_pc st.
Proof.
  intros E st ms mo st' HS H.
  destruct (abandon_one_shape bsegs st st' H)
    as (kf & shf & hargs & wnl & i0 & len0 & rsh & h1 & h2 & h3 & RVN & AW & FT & FW & FRS & FOK & FOKk & SRG & SFO & LO0s & (lent0 & kdt & WLT0 & KEQ) & H1 & H2 & H3 & ->).
  destruct (CtrPre.TwinB.aheap_call_facts AI ACCT UNIV Cw OPS AI_fake OPS_holds1 E st ms mo hargs wnl HS AW)
    as (r1 & n & md & A & nw & rest & LB & Hr1 & Hf & Hc & Hn & Eh & T & N & Ln & N255 & SW & NW & AN & JU & HA & WF & HC & W & ARW & TI).
  destruct (CallA.TwinB.stack_sound_g bsegs OPS E st ms mo 0%uint63 HS ltac:(change (to_Z 0%uint63) with 0; lia) SRG)
    as (ks & offs & rss & ksp & HX2 & Hrs & K0 & Hksp & K16 & A16 & Esp & LOX & HI64 & STK & SPR & LOR & LOZ0).
  destruct (CallA.TwinB.sp_floor_sound bsegs OPS E st ms mo hargs n md A nw rest ks offs rss HS SFO Hn Eh SPR LOZ0) as (wlo & len & INw & FLOOR0).
  pose proof (proj1 (Forall_forall _ _) WF _ INw) as (_ & _ & _ & KDs). cbn [w_kind w_lo] in KDs.
  assert (CE : ATOP + 4096 <= bv_unsigned (den E (VP STACK_ID wlo))).
  { destruct KDs as [[_ C]|[[K1 _]|[K1 _]]]; [exact C| unfold K_BLOCK, K_STACK in K1; lia| unfold K_SUB, K_STACK in K1; lia]. }
  change (to_Z 0%uint63) with 0 in LOR.
  set (R := ms_regs ms) in *. set (m := ms_mem ms) in *.
  assert (SP2 : bv_unsigned (AP.getr R 2%bv) = bv_unsigned (ev E ks) + keyZ ksp).
  { unfold R. rewrite <- HeapCtr.TwinB.reg_of_X2, (GlueA.TwinB.getr_RA bsegs OPS E st ms mo HS X2). exact Esp. }
  destruct (CtrFree.TwinB.afree_ok_k_inv OPS ActrB.TwinB.ActrB.K_FRAME ActrB.TwinB.ActrB.K_FTWIN E st ms mo wnl kf shf HS FOKk)
    as (rf & lenf & lent & Frf & WLf & WLt & BTs & LO0 & POSf & LEf & OTHERS).
  rewrite WLt in WLT0. injection WLT0 as <- <-.
  assert (FULLs : hiZ E rsh = bv_unsigned (den E lent)).
  { unfold hiZ. rewrite (HeapCtr.TwinB.known_eq_sound E _ _ _ (so_facts _ _ _ _ _ _ HS) KEQ). reflexivity. }
  destruct (FaPost.TwinB.owner_f AI ACCT UNIV OPS AI_fake E st ms mo HS wnl n rest LB (den E A) NW WF W ARW TI kf shf lenf lent WLf WLt BTs)
    as (fb & VF & EAf & ENf & ESH & ELT & INU & INS & UIV & SIV).
  set (Fv := fun _ : Z => Z_to_bv 64 0). set (Gv := fun (_ _ : Z) => Z_to_bv 8 0).
  exists (CtrDelta.TwinB.E' E st Fv Gv). split; [exact (CtrDelta.TwinB.EXT E st Fv Gv)|]. split; [| split; reflexivity].
  pose proof (FaPost.TwinB.fa_post_ok AI IMGX IMGX_aci ACCT UNIV Cw OPS AI_fake OPS_holds1 OPS_fp1 OPS_cov1 Cw_ghost_free_f Cw_zc OPS_frame_other OPS_fp_other OTHER OPS_mo_other OPS_cov0_img
             E st ms mo HS wnl n rest LB (den E A) NW AN WF W ARW TI kf shf rf rsh lenf lent Frf FRS WLf WLt LO0 POSf LO0s FULLs OTHERS
             fb VF EAf ENf ESH ELT INU INS UIV SIV hargs md A nw Hf Eh T N Ln FOK Fv Gv h1 h2 H1 H2 h3 H3 eq_refl HC
             R (mem_inv_of E st ms mo HS) ks offs rss ksp SPR SP2 JU ltac:(lia) ltac:(lia) Hc (OTHER_refl mo) (so_mf _ _ _ _ _ _ HS)
             (s_pc st) (s_rf st) (s_next st) RVN (so_x0 _ _ _ _ _ _ HS) (ghost_regs E st ms mo HS FOK Fv Gv (s_pc st))) as HSF.
  rewrite (GlueA.TwinB.ms_formA bsegs OPS E st ms mo HS RVN) at 1. fold R m.
  unfold set_ops, setregs. cbn [s_pc s_rf s_ff s_resv s_regs s_facts s_ops s_priv s_next]. rewrite RVN. exact HSF.
Qed.

Lemma burn_ok : forall c E st ms mo st', st_ok bsegs OPS E st ms mo -> FaC.TwinB.FaC.burn c st = Some st' ->
  exists E1, env_ext (s_next st) E E1 /\ st_ok bsegs OPS E1 st' ms mo.
Proof.
  intros c E st ms mo st' HS H.
  destruct (burn_shape c st st' H) as (hargs & wnl & h' & RVN & AW & FOK & SRG & SFO & HP & ->).
  destruct (CtrPre.TwinB.aheap_call_facts AI ACCT UNIV Cw OPS AI_fake OPS_holds1 E st ms mo hargs wnl HS AW)
    as (r1 & n & md & A & nw & rest & LB & Hr1 & Hf & Hc & Hn & Eh & T & N & Ln & N255 & SW & NW & AN & JU & HA & WF & HC & W & ARW & TI).
  destruct (CallA.TwinB.stack_sound_g bsegs OPS E st ms mo 0%uint63 HS ltac:(change (to_Z 0%uint63) with 0; lia) SRG)
    as (ks & offs & rss & ksp & HX2 & Hrs & K0 & Hksp & K16 & A16 & Esp & LOX & HI64 & STK & SPR & LOR & LOZ0).
  destruct (CallA.TwinB.sp_floor_sound bsegs OPS E st ms mo hargs n md A nw rest ks offs rss HS SFO Hn Eh SPR LOZ0) as (wlo & len & INw & FLOOR0).
  pose proof (proj1 (Forall_forall _ _) WF _ INw) as (_ & _ & _ & KDs). cbn [w_kind w_lo] in KDs.
  assert (CE : ATOP + 4096 <= bv_unsigned (den E (VP STACK_ID wlo))).
  { destruct KDs as [[_ C]|[[K1 _]|[K1 _]]]; [exact C| unfold K_BLOCK, K_STACK in K1; lia| unfold K_SUB, K_STACK in K1; lia]. }
  change (to_Z 0%uint63) with 0 in LOR.
  set (R := ms_regs ms) in *. set (m := ms_mem ms) in *.
  assert (SP2 : bv_unsigned (AP.getr R 2%bv) = bv_unsigned (ev E ks) + keyZ ksp).
  { unfold R. rewrite <- HeapCtr.TwinB.reg_of_X2, (GlueA.TwinB.getr_RA bsegs OPS E st ms mo HS X2). exact Esp. }
  set (Fv := fun _ : Z => Z_to_bv 64 0). set (Gv := fun (_ _ : Z) => Z_to_bv 8 0).
  exists (CtrDelta.TwinB.E' E st Fv Gv). split; [exact (CtrDelta.TwinB.EXT E st Fv Gv)|].
  pose proof (FaBurn.TwinB.fa_burn_ok AI IMGX IMGX_aci ACCT UNIV Cw OPS AI_fake OPS_holds1 OPS_fp1 OPS_cov1 Cw_zc OPS_frame_other OPS_fp_other OTHER OPS_mo_other OPS_cov0_img
             E st ms mo HS wnl n rest LB (den E A) NW WF W ARW TI hargs md A nw Hf Eh T N Ln FOK Fv Gv c h' HP eq_refl HC
             R (mem_inv_of E st ms mo HS) ks offs rss ksp SPR SP2 JU ltac:(lia) ltac:(lia) Hc (OTHER_refl mo) (so_mf _ _ _ _ _ _ HS)
             (s_pc st) (s_rf st) (s_next st) RVN (so_x0 _ _ _ _ _ _ HS) (ghost_regs E st ms mo HS FOK Fv Gv (s_pc st))) as HSF.
  rewrite (GlueA.TwinB.ms_formA bsegs OPS E st ms mo HS RVN) at 1. fold R m.
  unfold set_ops. cbn [s_pc s_rf s_ff s_resv s_regs s_facts s_ops s_priv s_next]. rewrite RVN. exact HSF.
Qed.

Lemma abandon_loop_ok : forall fuel E st ms mo cnt st' cnt', st_ok bsegs OPS E st ms mo -> FaC.TwinB.FaC.abandon_loop bsegs fuel st cnt = (st', cnt') ->
  exists E1, env_ext (s_next st) E E1 /\ st_ok bsegs OPS E1 st' ms mo /\ s_next st' = s_next st.
Proof.
  induction fuel as [|f IH]; intros E st ms mo cnt st' cnt' HS H; cbn [FaC.TwinB.FaC.abandon_loop] in H.
  - injection H as <- <-. exists E. split; [apply env_ext_refl|]. split; [exact HS| reflexivity].
  - destruct (FaC.TwinB.FaC.abandon_one bsegs st) as [st1|] eqn:A1.
    + destruct (abandon_one_ok E st ms mo st1 HS A1) as (E1 & X1 & HS1 & NX1 & _).
      destruct (IH E1 st1 ms mo (S cnt) st' cnt' HS1 H) as (E2 & X2 & HS2 & NX2).
      exists E2. split; [| split; [exact HS2| rewrite NX2; exact NX1]].
      rewrite NX1 in X2. exact (env_ext_trans (s_next st) (s_next st) E E1 E2 (Z.le_refl _) X1 X2).
    + injection H as <- <-. exists E. split; [apply env_ext_refl|]. split; [exact HS| reflexivity].
Qed.

Theorem frame_abandon_sound : forall pc, contract_sound bsegs OPS MP PB (FaC.TwinB.FaC.frame_abandon_c bsegs pc).
Proof.
  intros pc st sts Hspc Happ K E ms mo HS HMP HPB HK. cbn [c_apply FaC.TwinB.FaC.frame_abandon_c] in Happ. unfold FaC.TwinB.FaC.frame_abandon_apply in Happ.
  destruct (FaC.TwinB.FaC.abandon_loop bsegs 16 st 0) as [st1 cnt] eqn:LP.
  destruct (abandon_loop_ok 16 E st ms mo 0%nat st1 cnt HS LP) as (E1 & X1 & HS1 & NX1).
  destruct (Nat.eqb cnt 0); [discriminate Happ|].
  destruct (Nat.eqb cnt 16).
  - injection Happ as <-. exact (HK st1 (or_introl eq_refl) E1 ms mo X1 HMP HS1).
  - destruct (FaC.TwinB.FaC.burn (of_Z (Z.of_nat (16 - cnt))) st1) as [st2|] eqn:B; [|discriminate Happ]. injection Happ as <-.
    destruct (burn_ok _ E1 st1 ms mo st2 HS1 B) as (E2 & X2 & HS2).
    rewrite NX1 in X2.
    exact (HK st2 (or_introl eq_refl) E2 ms mo (env_ext_trans (s_next st) (s_next st) E E1 E2 (Z.le_refl _) X1 X2) HMP HS2).
Qed.

Theorem settle_sound : forall pc, contract_sound bsegs OPS MP PB (FaC.TwinB.FaC.settle_c bsegs pc).
Proof.
  intros pc st sts Hspc Happ K E ms mo HS HMP HPB HK. cbn [c_apply FaC.TwinB.FaC.settle_c] in Happ. unfold FaC.TwinB.FaC.settle_apply in Happ.
  destruct (FaC.TwinB.FaC.abandon_loop bsegs 16 st 0) as [st1 cnt] eqn:LP.
  destruct (abandon_loop_ok 16 E st ms mo 0%nat st1 cnt HS LP) as (E1 & X1 & HS1 & NX1).
  destruct (Nat.eqb cnt 16).
  - injection Happ as <-. exact (HK st1 (or_introl eq_refl) E1 ms mo X1 HMP HS1).
  - destruct (FaC.TwinB.FaC.burn (of_Z (Z.of_nat (16 - cnt))) st1) as [st2|] eqn:B; [|discriminate Happ]. injection Happ as <-.
    destruct (burn_ok _ E1 st1 ms mo st2 HS1 B) as (E2 & X2 & HS2).
    rewrite NX1 in X2.
    exact (HK st2 (or_introl eq_refl) E2 ms mo (env_ext_trans (s_next st) (s_next st) E E1 E2 (Z.le_refl _) X1 X2) HMP HS2).
Qed.
End Sound.

End TwinB.
