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
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require Import AImg AProto ABase AMalloc_iface AMalloc_iface2.
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
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Bridge Require CallA CallV CtrPre GlueA FrameV CtrDelta CtrFree CtrPost.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Unp Require GLib.
Import ValP MemP CtrFX.
Import ActrA.
Module AP := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.PropExec.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX Require KnownT.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Bridge Require KnownA.
Unset Nia Cache. Unset Nra Cache.

Ltac split_ands H :=
  match type of H with
  | (if ?a then ?b else false) = true =>
      let X := fresh "Q" in let Y := fresh "Q" in
      assert (X : a = true) by (destruct a; [reflexivity| discriminate H]);
      assert (Y : b = true) by (rewrite X in H; exact H); clear H; split_ands X; split_ands Y
  | _ => idtac
  end.

Lemma twin_out_apply_shape : forall sel st sts, twin_out_apply sel st = Some sts ->
  sts = [st] \/
  exists hargs wnl kf n rf h1,
    aheap_windows st = Some (hargs, wnl) /\ s_resv st = RNone /\ fresh_ok st = true
    /\ stack_room_g st 0%uint63 = true /\ sp_floor_ok st hargs = true
    /\ CtrA.win_lookup wnl kf = Some (n, CtrLib.K_BLOCK) /\ IMap.find kf (s_regs st) = Some rf
    /\ rg_w rf = true /\ rg_lo rf = 0%uint63 /\ KnownT.KnownT.known_ltu_t (s_facts st) (VL wzero) (rg_hi rf) = true
    /\ size_shape_ok (s_facts st) n = true
    /\ forallb (tw_other_ok (s_facts st) (s_regs st) wnl (carg_vecs st) kf (KnownT.KnownT.known_eq_t (s_facts st) (rg_hi rf) n)) wnl = true
    /\ heap_add_window hargs (VP (s_next st) wzero) (twin_len n) (VL K_TWIN) = Some h1
    /\ sts = [addfact (set_ops (setregs (set_next st (PrimInt63.add (s_next st) 1%uint63)) (IMap.add (s_next st) (twin_region n) (s_regs st)))
                               (set_op HEAP_ID h1 (s_ops st))) (link_fact (s_next st) kf)].
Proof.
  intros sel st sts H. unfold twin_out_apply in H.
  destruct (aheap_windows st) as [[hargs wnl]|] eqn:AW; [|discriminate H].
  destruct (twsel_blk sel st wnl) as [kf|] eqn:SEL; [| left; injection H as <-; reflexivity].
  destruct (tw_out (s_facts st) wnl kf) as [p0|] eqn:TO; [left; injection H as <-; reflexivity|].
  destruct (CtrA.win_lookup wnl kf) as [[n kd]|] eqn:WL; [|discriminate H].
  destruct (IMap.find kf (s_regs st)) as [rf|] eqn:Frf; [|discriminate H].
  right.
  match type of H with (if ?c then _ else _) = _ => destruct c eqn:CK; [|discriminate H] end.
  split_ands CK.
  cbn [fresh fst snd] in H.
  destruct (heap_add_window hargs (VP (s_next st) wzero) (twin_len n) (VL K_TWIN)) as [h1|] eqn:H1; [|discriminate H]. injection H as <-.
  match goal with X : weqb kd CtrLib.K_BLOCK = true |- _ => apply weqb_eq in X; subst kd end.
  assert (RV : s_resv st = RNone) by (destruct (s_resv st); try reflexivity; discriminate).
  match goal with X : PrimInt63.eqb (rg_lo rf) 0%uint63 = true |- _ => apply Uint63.eqb_correct in X end.
  exists hargs, wnl, kf, n, rf, h1. repeat (split; [reflexivity || assumption|]). reflexivity.
Qed.

Lemma w2Z_twin : forall kd, w2Z kd = 9 -> kd = K_TWIN.
Proof.
  intros [t l] H. unfold w2Z in H. cbn [wt wl] in H. pose proof (Uint63.to_Z_bounded l) as B. destruct t.
  - exfalso. unfold two63 in H. lia.
  - assert (L : l = 9%uint63) by (apply Uint63.to_Z_inj; change (to_Z 9%uint63) with 9; lia). subst l. reflexivity.
Qed.

Lemma nonstack_len_In : forall m ws l k len kd, CtrA.nonstack_windows m ws = Some l -> In (k, len, kd) l -> In len ws.
Proof.
  induction m as [|m IH]; intros ws l k len kd H Hin; [cbn in H; injection H as <-; destruct Hin|].
  destruct ws as [|wlo [|ln [|kdv ws']]]; try (cbn in H; discriminate).
  cbn [CtrA.nonstack_windows] in H. destruct kdv as [kw| | | | | | | | | |]; try discriminate.
  destruct (CtrA.nonstack_windows m ws') as [l0|] eqn:NW0; [|discriminate].
  destruct (weqb kw wzero).
  - injection H as <-. right; right; right. exact (IH _ _ _ _ _ NW0 Hin).
  - destruct wlo as [|k0 o| | | | | | | | |]; try discriminate. cbv beta iota in H.
    match type of H with (if ?c then _ else _) = _ => destruct c; [|discriminate H] end. injection H as <-.
    destruct Hin as [X|X]; [right; left; congruence| right; right; right; exact (IH _ _ _ _ _ NW0 X)].
Qed.

Section TwinOut.
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

Hypothesis Cw_ghost_grow : forall md ca LB ws m b0 n0 n, cw_holds Cw md ca LB ws m ->
  In (Win b0 n0 K_BLOCK) ws -> 0 < n0 -> b0 mod 8 = 0 ->
  (forall a, in_iv (shad b0, n) a -> ~ in_user LB a) -> cw_holds Cw md ca ((shad b0, n) :: LB) (ws ++ [Win (shad b0) n K_TWINz]) m.

Hypothesis Cw_vec_unowned : forall md ca LB ws m i a, cw_holds Cw md ca LB ws m -> In i (VECS md) -> nth_error ca i = Some a -> bv_unsigned a <> 0 ->
  forall w, In w ws -> w_kind w = K_BLOCK -> 0 < w_len w -> w_lo w <> bv_unsigned a.
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

Section ADDED.
Variables (E : env) (st : sstate) (ms : machine_state) (mo : Model).
Hypothesis HS : st_ok asegs OPS E st ms mo.
Variables (wnl : list (int * sv * w64)) (nn : nat) (rest : list sv) (LB : blocks) (aw : word).
Hypothesis NW : CtrA.nonstack_windows nn rest = Some wnl.
Hypothesis AN : CtrA.windows_anchored (s_regs st) wnl = true.
Hypothesis WF : windows_wf (wins_of E nn rest) LB (ATOP + 4096).
Variable WW : wit.
Hypothesis AR : aw_realW AI ACCT UNIV aw LB (ms_mem ms) mo WW.
Hypothesis TI : ties WW (wins_of E nn rest).
Hypothesis CVU : forall kb, In kb (carg_vecs st) -> bv_unsigned (ev E kb) <> 0 -> forall w, In w (wins_of E nn rest) -> w_kind w = K_BLOCK -> 0 < w_len w -> w_lo w <> bv_unsigned (ev E kb).
Variables (kf : int) (rf : region) (lenf : sv).
Hypothesis Frf : IMap.find kf (s_regs st) = Some rf.
Hypothesis WLf : CtrA.win_lookup wnl kf = Some (lenf, CtrLib.K_BLOCK).
Hypothesis WRf : rg_w rf = true.
Hypothesis LO0 : rg_lo rf = 0%uint63.
Hypothesis POSf : 0 < hiZ E rf.
Hypothesis SHAPE : size_shape_ok (s_facts st) lenf = true.
Hypothesis OTH : forall k len kd, In (k, len, kd) wnl -> weqb kd K_TWIN = true ->
  exists kb, block_of_twin (s_facts st) k = Some kb /\ kb <> kf
    /\ ((exists n2 r2, CtrA.win_lookup wnl kb = Some (n2, CtrLib.K_BLOCK) /\ IMap.find kb (s_regs st) = Some r2 /\ rg_w r2 = true
                       /\ rg_lo r2 = 0%uint63 /\ 0 < hiZ E r2)
        \/ (hiZ E rf = bv_unsigned (den E lenf) /\ twin_arm_evx (s_facts st) (s_regs st) wnl (carg_vecs st) k len kf = true)).

Let Af : Z := bv_unsigned (ev E kf).
Let nf : Z := bv_unsigned (den E lenf).
Let m : amem := ms_mem ms.

Lemma AWHf : aw_holds_asan AI ACCT UNIV aw LB m mo.
Proof. exact (aw_real_holds AI ACCT UNIV _ _ _ _ _ AR). Qed.
Lemma HWf : aw_holds_w AI ACCT UNIV WW aw LB m mo.
Proof. exact (proj1 AR). Qed.
Lemma GAf : ghost_apart (wins_of E nn rest).
Proof. destruct TI as (_ & _ & _ & _ & _ & _ & _ & _ & _ & X & _). exact X. Qed.

Lemma entry_w : forall k len kd, In (k, len, kd) wnl ->
  k <> 0%uint63 /\ In (Win (bv_unsigned (ev E k)) (bv_unsigned (den E len)) (w2Z kd)) (wins_of E nn rest)
  /\ exists b, In b LB /\ (forall a, in_iv (bv_unsigned (ev E k), bv_unsigned (den E len)) a -> in_iv b a)
       /\ (kd = CtrLib.K_BLOCK -> b = (bv_unsigned (ev E k), bv_unsigned (den E len))).
Proof.
  intros k len kd Hin. destruct (HeapCtrB.nonstack_windows_In E nn rest wnl k len kd NW Hin) as (K0 & _ & KD & INW).
  split; [exact K0|]. split; [exact INW|].
  pose proof (proj1 (Forall_forall _ _) WF _ INW) as (W1 & W2 & W3 & [[KS0 _]|[[KB B]|[KS2 (b & Hb & SUB)]]]); unfold w_iv in *; cbn [w_kind w_lo w_len] in *.
  - exfalso. exact (KD KS0).
  - eexists. split; [exact B|]. split; [intros a Ha; exact Ha| reflexivity].
  - exists b. split; [exact Hb|]. split; [exact SUB|]. intros ->. change (w2Z CtrLib.K_BLOCK) with 1 in KS2. unfold K_SUB in KS2. lia.
Qed.

Lemma kblock_heap : forall k len, In (k, len, CtrLib.K_BLOCK) wnl ->
  exists b, vis WW b /\ is_heap b /\ ab_addr b = bv_unsigned (ev E k) /\ ab_size b = bv_unsigned (den E len).
Proof.
  intros k len Hin. destruct (entry_w k len _ Hin) as (_ & INW & b0 & Hb0 & _ & EQ). rewrite (EQ eq_refl) in Hb0.
  change (w2Z CtrLib.K_BLOCK) with K_BLOCK in INW.
  set (A := bv_unsigned (ev E k)) in *. set (N := bv_unsigned (den E len)) in *.
  pose proof HWf as HW0. pose proof HW0 as (AH & HT & _).
  destruct TI as (T1 & _ & T3 & _).
  assert (GHOST : forall g, In g (wins_of E nn rest) -> K_GHOST <= w_kind g -> w_iv g = (A, N) -> 0 < N -> False).
  { intros g Hg KG EG PN. apply (GAf g (Win A N K_BLOCK) Hg INW KG eq_refl A); [rewrite EG|]; unfold in_iv, w_iv; cbn [fst snd w_lo w_len]; lia. }
  destruct (LB_cases AI ACCT UNIV WW aw LB m mo (A, N) HW0 Hb0) as [(b & Vb & EQb)|[(b & HbT & EQb)|(b & Vb & EQb)]].
  - destruct (kind_cases b) as [HH|HF].
    + exists b. unfold user_iv in EQb. rewrite (usz_heap b HH) in EQb. injection EQb as E1 E2. auto.
    + exfalso. destruct (T3 b (conj Vb HF)) as [X _].
      destruct (AI_fake _ _ _ _ _ b AH (proj1 Vb) HF) as (_ & _ & _ & _ & NP & _).
      unfold user_iv in EQb. rewrite (usz_fake b HF) in EQb. injection EQb as E1 E2.
      apply (GHOST _ X); [cbn [w_kind]; unfold K_FRAMEz, K_GHOST; lia| unfold w_iv; cbn [w_lo w_len]; rewrite E1, E2; reflexivity| lia].
  - exfalso. destruct (LB_twin_facts AI ACCT UNIV WW aw LB m mo b HW0 HbT) as (_ & _ & P).
    unfold twin_iv in EQb. injection EQb as E1 E2.
    apply (GHOST _ (T1 b HbT)); [cbn [w_kind]; unfold K_TWINz, K_GHOST; lia| unfold w_iv; cbn [w_lo w_len]; rewrite E1, E2; reflexivity| lia].
  - exfalso. destruct (T3 b Vb) as [_ Y]. destruct Vb as [Vb HF].
    destruct (AI_fake _ _ _ _ _ b AH (proj1 Vb) HF) as (_ & _ & _ & _ & NP & _).
    unfold fsh_iv in EQb. injection EQb as E1 E2.
    apply (GHOST _ Y); [cbn [w_kind]; unfold K_FTWINz, K_GHOST; lia| unfold w_iv; cbn [w_lo w_len]; rewrite E1, E2; reflexivity|].
    rewrite E2. unfold shlen. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8. clear - NP. Z.div_mod_to_equations. lia.
Qed.

Lemma INf : In (kf, lenf, CtrLib.K_BLOCK) wnl.
Proof. exact (HeapCtrB.win_lookup_In _ _ _ _ WLf). Qed.
Lemma WINf : In (Win Af nf K_BLOCK) (wins_of E nn rest).
Proof. destruct (entry_w kf lenf _ INf) as (_ & X & _). exact X. Qed.
Lemma blockLB : In (Af, nf) LB.
Proof. destruct (entry_w kf lenf _ INf) as (_ & _ & b & Hb & _ & EQ). rewrite (EQ eq_refl) in Hb. exact Hb. Qed.

Lemma heap_facts : forall b, vis WW b -> is_heap b ->
  1 <= ab_size b <= AREQMAX /\ ablk (ab_addr b) (ab_addr b + ab_size b) /\ ab_addr b + ab_size b <= ATOP /\ ab_addr b mod 16 = 0.
Proof.
  intros b Vb HH. pose proof HWf as (AH & _).
  destruct (heap_block_facts AI _ _ _ _ _ b AH (proj1 Vb) HH) as (N & (BK & _ & HI & AL) & _). auto.
Qed.

Lemma not_out : forall b, vis WW b -> is_heap b -> ab_addr b = Af -> ab_size b = nf -> ~ In b (w_T WW).
Proof.
  intros b Vb HH EA EN HbT. destruct (heap_facts b Vb HH) as (NR & BK & HI & AL). rewrite EA, EN in *.
  pose proof atop_range as ATR. unfold ablk, AIMG_HI, KLS in BK.
  pose proof (so_facts _ _ _ _ _ _ HS) as HF.
  destruct TI as (T1 & _). pose proof (T1 b HbT) as INT. rewrite EA, EN in INT.
  destruct (HeapCtrB.wins_cover E nn rest wnl _ NW INT) as [KS|(k & len & kd & Ik & EW)]; [cbn [w_kind] in KS; unfold K_TWINz, K_STACK in KS; lia|].
  injection EW as E1 E2 E3. unfold K_TWINz in E3. symmetry in E3. apply w2Z_twin in E3. subst kd.
  destruct (OTH k len K_TWIN Ik eq_refl) as (kb & BT & NKB & CASE).
  pose proof (CallA.block_of_twin_sound E _ k kb HF BT) as LK.
  pose proof (bv_unsigned_in_range 64 (ev E kb)) as RKB. change (bv_modulus 64) with (2 ^ 64) in RKB.
  rewrite Z.mod_small in LK by (clear - RKB; Z.div_mod_to_equations; lia).
  assert (SHE : bv_unsigned (ev E kb) / 8 = Af / 8).
  { rewrite <- E1 in LK. unfold shad, ASHOFF in LK. rewrite Z.shiftr_div_pow2 in LK by lia. change (2 ^ 3) with 8 in LK. lia. }
  destruct (entry_w kf lenf _ INf) as (Kf0 & _).
  assert (ZF : PrimInt63.eqb kf 0%uint63 = false) by (apply Uint63.eqb_false_spec; exact Kf0).
  assert (KZ0 : keyZ 0%uint63 = 0) by reflexivity.
  assert (RF : forall x, Af <= x < Af + hiZ E rf -> bv_unsigned (ev E kf) + loZ rf <= x < bv_unsigned (ev E kf) + hiZ E rf).
  { intros x Hx. unfold loZ. rewrite LO0, KZ0. fold Af. lia. }
  destruct CASE as [(n2 & r2 & WL2 & Fr2 & W2 & L2 & P2)|(FULL & EVA)].
  -
    pose proof (HeapCtrB.win_lookup_In _ _ _ _ WL2) as IN2.
    destruct (kblock_heap kb n2 IN2) as (b2 & Vb2 & HH2 & EA2 & EN2).
    destruct (heap_facts b2 Vb2 HH2) as (_ & _ & _ & AL2). rewrite EA2 in AL2.
    assert (EKB : bv_unsigned (ev E kb) = Af) by (clear - SHE AL AL2; Z.div_mod_to_equations; lia).
    destruct (entry_w kb n2 _ IN2) as (Kb0 & _).
    assert (ZB : PrimInt63.eqb kb 0%uint63 = false) by (apply Uint63.eqb_false_spec; exact Kb0).
    apply (so_disj _ _ _ _ _ _ HS kb r2 kf rf Fr2 Frf NKB ZB ZF (or_introl W2) Af). split.
    + unfold loZ. rewrite L2, KZ0, EKB. lia.
    + apply RF. lia.
  -
    destruct (CallV.twin_ev_cases E _ _ _ _ _ _ _ HF EVA) as (kb2 & BT2 & LW & ALk & EVD).
    rewrite BT in BT2. injection BT2 as <-.
    pose proof (GTwinSub.GTwinSub.mod8_of_align E _ kb HF ALk) as K8.
    assert (EKB : bv_unsigned (ev E kb) = Af) by (clear - SHE AL K8; Z.div_mod_to_equations; lia).
    destruct EVD as [CVk|(ks & lens & kds & rsub & Hins & NXs & NKBs & NKTs & Frsub & RWs & L0s & HPOS & XLO & XHI)].
    + apply (CVU kb CVk ltac:(rewrite EKB; lia) _ WINf); [reflexivity| cbn [w_len]; lia| cbn [w_lo]; symmetry; exact EKB].
    + idtac.
      assert (XIN : Af <= bv_unsigned (ev E ks) < Af + nf).
      { rewrite <- E2, EKB in XHI. rewrite EKB in XLO. unfold shlen in XHI. rewrite Z.shiftr_div_pow2 in XHI by lia. change (2 ^ 3) with 8 in XHI.
        clear - XLO XHI NR. Z.div_mod_to_equations. lia. }
      destruct (entry_w ks lens kds Hins) as (Ks0 & _).
      assert (ZKs : PrimInt63.eqb ks 0%uint63 = false) by (apply Uint63.eqb_false_spec; exact Ks0).
      apply (so_disj _ _ _ _ _ _ HS ks rsub kf rf Frsub Frf NXs ZKs ZF (or_introl RWs) (bv_unsigned (ev E ks))). split.
      * unfold loZ. rewrite L0s, KZ0. lia.
      * apply RF. fold nf in FULL. rewrite FULL. exact XIN.
Qed.

Variable b : ablock.
Hypothesis Vb : vis WW b.
Hypothesis HHb : is_heap b.
Hypothesis EAb : ab_addr b = Af.
Hypothesis ENb : ab_size b = nf.

Definition W1 : wit := set_T WW (b :: w_T WW).
Definition LB1 : blocks := (shad Af, shlen (nf + 7)) :: LB.
Definition WTo : window := Win (shad Af) (shlen (nf + 7)) K_TWINz.

Lemma OUTW : aw_holds_w AI ACCT UNIV W1 aw LB1 m mo /\ ~ In (shad Af, shlen (nf + 7)) LB
  /\ (forall g, 0 <= g -> 8 * g < nf -> m (ALib.Mem.wa (shad Af + g)) = Some (Z_to_bv 8 (if 8 * g + 8 <=? nf then 0 else nf - 8 * g))).
Proof.
  pose proof (twin_out_w AI ACCT UNIV AI_fake WW aw LB m mo b HWf Vb HHb (not_out b Vb HHb EAb ENb)) as X.
  unfold twin_iv in X. rewrite EAb, ENb in X. exact X.
Qed.
Lemma HW1 : aw_holds_w AI ACCT UNIV W1 aw LB1 m mo. Proof. exact (proj1 OUTW). Qed.
Lemma AWH1 : aw_holds_asan AI ACCT UNIV aw LB1 m mo. Proof. exists W1. exact HW1. Qed.
Lemma bT1 : In b (w_T W1). Proof. left. reflexivity. Qed.

Lemma twin_facts : 0x800bde00 <= shad Af /\ shad Af + shlen (nf + 7) <= shad ATOP /\ 1 <= shlen (nf + 7) /\ 1 <= nf <= AREQMAX /\ Af mod 16 = 0
  /\ AIMG_HI <= Af /\ Af + nf <= ATOP.
Proof.
  destruct (heap_facts b Vb HHb) as (NR & BK & HI & AL). rewrite EAb, ENb in *.
  destruct (shadow_tight Af nf BK HI ltac:(lia)) as [S1 S2].
  destruct (LB_twin_facts AI ACCT UNIV W1 aw LB1 m mo b HW1 bT1) as (_ & _ & T3). rewrite ?EAb, ?ENb in T3.
  pose proof (ablk_lin _ _ BK) as (X1 & _). auto 10.
Qed.

Lemma TWFRESH : forall a, in_iv (shad Af, shlen (nf + 7)) a -> ~ in_user LB a.
Proof.
  intros a Ha U. apply in_ivs_In in U as (v & Hv & Hin). destruct v as [A' n'].
  apply (aw_blocks_disj_asan AI ACCT UNIV AI_fake aw LB1 m mo (A', n') (shad Af, shlen (nf + 7)) a AWH1 (or_intror Hv) (or_introl eq_refl)); [| exact Hin| exact Ha].
  cbn [fst]. intros ->. apply (proj1 (proj2 OUTW)).
  rewrite <- (LB_same_addr AI ACCT UNIV AI_fake W1 aw LB1 m mo (shad Af) n' (shlen (nf + 7)) HW1 (or_intror Hv) (or_introl eq_refl)). exact Hv.
Qed.

Lemma windows_wf_mono1 : forall ws L1 L2 c, windows_wf ws L1 c -> (forall v, In v L1 -> In v L2) -> windows_wf ws L2 c.
Proof.
  intros ws L1 L2 c WF0 SUB. apply Forall_forall. intros w Hw.
  pose proof (proj1 (Forall_forall _ _) WF0 w Hw) as (X1 & X2 & X3 & [[K S]|[[K B]|[K (b0 & Hb0 & SB)]]]).
  - split; [exact X1|]. split; [exact X2|]. split; [exact X3|]. left; auto.
  - split; [exact X1|]. split; [exact X2|]. split; [exact X3|]. right; left; auto.
  - split; [exact X1|]. split; [exact X2|]. split; [exact X3|]. right; right. split; [exact K|]. exists b0. auto.
Qed.

Variables (hargs : list sv) (md : w64) (A : sv) (nw : w64).
Hypothesis Hf : find_op HEAP_ID (s_ops st) = Some hargs.
Hypothesis Eh : hargs = VL md :: A :: VL nw :: rest.
Hypothesis Tnw : wt nw = false.
Hypothesis Nn : nn = Z.to_nat (to_Z (wl nw)).
Hypothesis Ln : (3 * nn <= length rest)%nat.
Hypothesis N255 : (nn <= 255)%nat.
Hypothesis FOK : fresh_ok st = true.
Variables (Fv : Z -> word) (Gv : Z -> Z -> byte).
Hypothesis FV0 : Fv 0 = Z_to_bv 64 (shad Af).
Notation E' := (CtrDelta.E' E st Fv Gv).
Let sh : int := s_next st.
Variable h1 : list sv.
Hypothesis H1 : heap_add_window hargs (VP sh wzero) (twin_len lenf) (VL K_TWIN) = Some h1.

Lemma ev_sh : bv_unsigned (ev E' sh) = shad Af.
Proof.
  pose proof (CtrDelta.ev_E'_fresh E st FOK Fv Gv 0%nat ltac:(lia)) as X. cbn [addn] in X. fold sh in X. rewrite X. change (Z.of_nat 0) with 0. rewrite FV0.
  destruct twin_facts as (S1 & S2 & S3 & _). pose proof atop_range as ATR.
  apply Z_to_bv_small. unfold bv_modulus. change (2 ^ Z.of_N 64) with (2 ^ 64).
  assert (SA : shad ATOP <= 2 ^ 47).
  { unfold shad, ASHOFF. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8. clear - ATR. Z.div_mod_to_equations. lia. }
  unfold two64. lia.
Qed.
Lemma lenf_below : sv_vars_below (s_next st) lenf = true.
Proof.
  pose proof (CtrDelta.rest_below st FOK rest hargs md A nw Hf Eh) as RB.
  exact (proj1 (forallb_forall _ _) RB lenf (nonstack_len_In _ _ _ _ _ _ NW INf)).
Qed.

Lemma den_lenf' : bv_unsigned (den E' lenf) = nf.
Proof. rewrite (CtrDelta.den_E' E st Fv Gv lenf lenf_below). reflexivity. Qed.

Lemma DEC1 : decode (map (den E') h1) = Some (w2Z md, den E A, wins_of E nn rest ++ [WTo], map (den E) (skipn (3 * nn) rest)).
Proof.
  destruct twin_facts as (_ & _ & _ & NR & _). unfold AREQMAX in NR.
  assert (NS : to_Z (wl nw) + 1 < two63).
  { pose proof (Uint63.to_Z_bounded (wl nw)) as B. unfold two63. rewrite Nn in N255. lia. }
  destruct (CtrPost.add_window_facts E' md A nw rest nn (VP sh wzero) (twin_len lenf) (VL K_TWIN) Tnw Nn Ln NS) as (A1 & T1 & N1 & L1 & W1' & S1).
  set (rest1 := firstn (3 * nn) rest ++ [VP sh wzero; twin_len lenf; VL K_TWIN] ++ skipn (3 * nn) rest) in *.
  set (nw1 := wadd nw wone) in *.
  assert (EH1 : h1 = VL md :: A :: VL nw1 :: rest1) by (pose proof H1 as H1'; rewrite Eh in H1'; rewrite A1 in H1'; injection H1' as X; symmetry; exact X).
  rewrite EH1.
  rewrite (decode_hargs E' md A nw1 rest1 (S nn) T1 N1 L1). rewrite W1', S1.
  pose proof (CtrDelta.rest_below st FOK rest hargs md A nw Hf Eh) as RB.
  rewrite (CtrDelta.den_E' E st Fv Gv A (CtrDelta.A_below st FOK rest hargs md A nw Hf Eh)).
  rewrite (CtrDelta.wins_of_E' E st Fv Gv _ _ RB).
  rewrite (CtrDelta.map_den_E' E st Fv Gv _ (CtrFree.forallb_skipn _ (3 * nn) rest RB)).
  assert (C3 : Win (bv_unsigned (den E' (VP sh wzero))) (bv_unsigned (den E' (twin_len lenf))) (bv_unsigned (den E' (VL K_TWIN))) = WTo).
  { unfold WTo. rewrite HeapCtr.den_VPz, ev_sh. rewrite (CallA.twin_len_den E' lenf) by (rewrite den_lenf'; lia).
    rewrite den_lenf'. unfold shlen. rewrite Z.shiftr_div_pow2 by lia. reflexivity. }
  rewrite C3. reflexivity.
Qed.

Hypothesis AWden : aw = den E A.
Hypothesis HC : cw_holds Cw (w2Z md) (map (den E) (skipn (3 * nn) rest)) LB (wins_of E nn rest) m.

Lemma HOLDN1 : op_holds OPS HEAP_ID (map (den E') h1) m mo.
Proof.
  rewrite OPS_holds1. destruct twin_facts as (S1 & S2 & S3 & NR & AL & LOA & HIA). pose proof atop_range as ATR.
  assert (SA : shad ATOP <= 2 ^ 47).
  { unfold shad, ASHOFF. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8. clear - ATR. Z.div_mod_to_equations. lia. }
  exists (w2Z md), aw, (wins_of E nn rest ++ [WTo]), (map (den E) (skipn (3 * nn) rest)), LB1, W1.
  split; [rewrite AWden; exact DEC1|]. split; [exact HW1|]. split; [| split].
  - apply Forall_app. split.
    + apply (windows_wf_mono1 _ LB LB1 _ WF). intros v Hv. right. exact Hv.
    + constructor; [|constructor]. unfold window_wf, WTo, w_iv. cbn [w_lo w_len w_kind]. split; [lia|]. split; [lia|]. split; [unfold two64; lia|].
      right; right. split; [unfold K_SUB, K_TWINz; lia|]. exists (shad Af, shlen (nf + 7)). split; [left; reflexivity|]. intros a Ha. exact Ha.
  - apply (Cw_ghost_grow _ _ _ _ m Af nf (shlen (nf + 7)) HC WINf); [lia| clear - AL; Z.div_mod_to_equations; lia| exact TWFRESH].
  - pose proof (ties_twin_out WW (wins_of E nn rest) b TI) as X. rewrite EAb, ENb in X. apply X.
    apply (ghost_apart_new_ghosts (wins_of E nn rest) _ LB (ATOP + 4096) WF GAf).
    intros w Hw. apply in_app_or in Hw as [Hw|[<-|[]]]; [left; exact Hw| right]. split; [cbn [w_kind]; unfold K_TWINz, K_BLOCK; lia|].
    intros _ a Ha. unfold w_iv in Ha. cbn [w_lo w_len] in Ha. exact (TWFRESH a Ha).
Qed.

Lemma sh_nz : PrimInt63.eqb sh 0%uint63 = false.
Proof.
  pose proof FOK as F0. unfold fresh_ok in F0. apply andb_prop in F0 as [F0 _]. apply andb_prop in F0 as [_ F0]. apply Uint63.ltb_spec in F0.
  apply Uint63.eqb_false_spec. unfold sh. intros E0. rewrite E0 in F0. change (to_Z 0%uint63) with 0 in F0. lia.
Qed.

Lemma NEW_region_ok : region_ok asegs (s_priv st) E' m sh (twin_region lenf).
Proof.
  destruct twin_facts as (S1 & S2 & S3 & NR & AL & LOA & HIA). unfold AREQMAX in NR. pose proof atop_range as ATR.
  destruct OUTW as (_ & _ & PAT).
  apply (CallA.twin_region_ok asegs (s_priv st) E' m sh lenf sh_nz); rewrite ?den_lenf', ?ev_sh.
  - lia.
  - lia.
  - exact (CallA.size_shape_sound E _ lenf (so_facts _ _ _ _ _ _ HS) SHAPE).
  - assert (SA : shad ATOP <= 2 ^ 47).
    { unfold shad, ASHOFF. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8. clear - ATR. Z.div_mod_to_equations. lia. }
    unfold shlen in S2. rewrite Z.shiftr_div_pow2 in S2 by lia. change (2 ^ 3) with 8 in S2. unfold two64. lia.
  - intros g G0 G1. split.
    + pose proof (PAT g G0 G1) as P1. unfold rb. unfold ALib.Mem.wa in P1. rewrite P1. reflexivity.
    + apply (proj2 (aw_user_ok_asan AI ACCT UNIV AI_fake aw LB1 m mo _ (shad Af + g) AWH1 (or_introl eq_refl)
                     ltac:(unfold in_iv; cbn [fst snd]; unfold shlen; rewrite Z.shiftr_div_pow2 by lia; change (2 ^ 3) with 8; clear - G0 G1; Z.div_mod_to_equations; lia))).
Qed.

Hypothesis MINV' : ALib.Mem.mem_inv asegs m.
Variables (ks : int) (offs : w64) (rss : region) (ksp : int).
Let sp : Z := bv_unsigned (AP.getr (ms_regs ms) 2%bv).
Hypothesis SPR : sp_region st = Some (ks, offs, rss).
Hypothesis SPE : sp = bv_unsigned (ev E ks) + keyZ ksp.
Hypothesis AJ : aregions_justified st wnl = true.
Hypothesis LOSP : loZ rss <= keyZ ksp.
Hypothesis FLOOR : ATOP + 4096 <= bv_unsigned (ev E ks) + loZ rss.
Hypothesis Hc : CtrA.count_op HEAP_ID (s_ops st) = 1%nat.
Hypothesis MINVo : op_minv OPS mo.

Definition RgO : IMap.t region := CtrDelta.RgPg (s_regs st) [(sh, twin_region lenf)] [].
Definition NEWSETo (a : Z) : Prop := in_iv (shad Af, shlen (nf + 7)) a.
Definition KEEPo (_ : int) : Prop := True.

Lemma WINKo : forall k0 len kd, KEEPo k0 -> CtrA.win_lookup wnl k0 = Some (len, kd) ->
  forall a, bv_unsigned (ev E k0) <= a < bv_unsigned (ev E k0) + bv_unsigned (den E len) -> in_user LB a.
Proof.
  intros k0 len kd _ WL a Ha. destruct (entry_w k0 len kd (HeapCtrB.win_lookup_In _ _ _ _ WL)) as (_ & _ & b0 & Hb0 & SUB & _).
  apply in_ivs_In. exists b0. split; [exact Hb0|]. apply SUB. unfold in_iv. cbn [fst snd]. lia.
Qed.

Lemma NEW_rng : forall a, bv_unsigned (ev E' sh) + loZ (twin_region lenf) <= a < bv_unsigned (ev E' sh) + hiZ E' (twin_region lenf) -> NEWSETo a.
Proof.
  intros a Ha. destruct twin_facts as (_ & _ & _ & NR & _). unfold AREQMAX in NR.
  destruct (CallA.twin_region_fields lenf) as (LO & _ & _).
  assert (KZ0 : keyZ 0%uint63 = 0) by reflexivity.
  unfold loZ, hiZ in Ha. rewrite LO, KZ0, CallA.twin_region_hi, (CallA.twin_len_den E' lenf), den_lenf', ev_sh in Ha by (rewrite den_lenf'; lia).
  unfold NEWSETo, in_iv, shlen. cbn [fst snd]. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8. lia.
Qed.

Theorem twin_out_post : forall (nx' : int),
  s_resv st = RNone ->
  st_ok asegs OPS E' (SS (s_pc st) (s_rf st) (s_ff st) RNone RgO (link_fact sh kf :: s_facts st) (set_op HEAP_ID h1 (s_ops st)) (s_priv st) nx')
        (MS (ms_regs ms) (ms_fregs ms) (Z_to_bv 64 (to_Z (s_pc st))) (ms_fcsr ms) None m (seg_rom asegs)) mo.
Proof.
  intros nx' RVN. destruct twin_facts as (S1 & S2 & S3 & NR & AL & LOA & HIA). pose proof atop_range as ATR. unfold AIMG_HI in LOA.
  assert (SAT : shad ATOP + 4096 <= ATOP).
  { unfold shad, ASHOFF. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8. clear - ATR. Z.div_mod_to_equations. lia. }
  assert (RSNOK : region_ok asegs (s_priv st) E' m ks rss).
  { apply (CtrDelta.sp_region_same_ok OPS E st ms mo HS FOK Fv Gv m ks offs rss SPR). intros a0 Ha RA0. split; [reflexivity| exact (fun H => H)]. }
  apply (CtrDelta.delta_st_ok AI IMGX IMGX_aci ACCT UNIV OPS AI_fake OPS_fp1 OPS_cov1 OPS_frame_other OPS_fp_other OTHER OPS_mo_other OPS_cov0_img
           E st ms mo HS FOK Fv Gv (ms_regs ms) m mo aw LB LB AWHf MINV'
           ltac:(intros a0 Ha S; split; [reflexivity| exact (fun H => H)]) ltac:(intros; reflexivity) ltac:(intros a0 Ha CC H; exact H)
           ltac:(intros a0 Ha SC IB; split; [reflexivity| exact (fun H => H)])
           ltac:(intros a0 Ha; split; [reflexivity| exact (fun H => H)])
           ks offs rss ksp SPR SPE wnl nn rest AJ WF KEEPo WINKo ltac:(intros; exact I) ltac:(intros; exact I)
           LOSP FLOOR (s_regs st) rss (so_bst _ _ _ _ _ _ HS) (CtrDelta.inline_RB_find st ks offs rss SPR) eq_refl (fun _ => eq_refl) eq_refl RSNOK
           hargs md A nw Hf Hc Eh Tnw Nn Ln (OTHER_refl mo) [(sh, twin_region lenf)] []
           ltac:(constructor; [intros []| constructor])
           ltac:(intros k1 r1 [X|[]]; injection X as <- _; exact sh_nz)
           ltac:(intros; exact I) NEWSETo
           ltac:(intros k1 r1 [X|[]]; injection X as <- <-; exact NEW_region_ok)
           ltac:(intros k1 r1 a1 [X|[]]; injection X as <- <-; exact (NEW_rng a1))
           ltac:(intros a1 X; unfold NEWSETo, in_iv in X; cbn [fst snd] in X; split; [unfold AIMG_HI; lia| exact (TWFRESH a1 X)])
           ltac:(intros a1 X; unfold NEWSETo, in_iv in X; cbn [fst snd] in X; lia)
           ltac:(intros a1 X (a' & Ra & EQa); unfold NEWSETo, in_iv in X; cbn [fst snd] in X; subst a1;
                 assert (shad ATOP <= shad a') by (unfold shad, ASHOFF; rewrite !Z.shiftr_div_pow2 by lia; change (2 ^ 3) with 8; clear - Ra; Z.div_mod_to_equations; lia); lia)
           ltac:(intros k1 r1 k2 r2 a1 [X|[]] [Y|[]]; injection X as <- _; injection Y as <- _; intros NE; exfalso; exact (NE eq_refl))
           h1 (w2Z md) (den E A) (wins_of E nn rest ++ [WTo]) (map (den E) (skipn (3 * nn) rest)) DEC1 HOLDN1).
  -
    intros a X. unfold in_ws, heap_ws. apply in_ivs_In. exists (w_iv WTo). split; [| exact X].
    apply in_map. apply filter_In. split; [apply in_or_app; right; left; reflexivity| reflexivity].
  -   intros a Ha NIX NWS. left. intros X. apply NWS. unfold in_ws in *. apply in_ivs_In in X as (v & Hv & Hin). apply in_ivs_In. exists v. split; [| exact Hin].
    apply in_map_iff in Hv as (w & <- & Hw). apply in_map. apply in_or_app. left. exact Hw.
  -   intros a IB X. unfold in_ws, heap_ws in X |- *. apply in_ivs_In in X as (v & Hv & Hin). apply in_map_iff in Hv as (w & <- & Hw). apply filter_In in Hw as [Hw KW].
    apply in_ivs_In. exists (w_iv w). split; [| exact Hin]. apply in_map. apply filter_In. split; [apply in_or_app; left; exact Hw| exact KW].
  - exact (so_x0 _ _ _ _ _ _ HS).
  - intros x. pose proof (so_regs _ _ _ _ _ _ (CtrDelta.HS' OPS E st ms mo HS FOK Fv Gv) x) as R0. unfold rget in R0 |- *. cbn [c_regs] in R0 |- *. exact R0.
  - reflexivity.
  -
    constructor; [| exact (so_facts _ _ _ _ _ _ (CtrDelta.HS' OPS E st ms mo HS FOK Fv Gv))].
    cbn [fact_holds link_fact]. rewrite HeapCtr.den_VPz.
    change (den E' (VAlu ALU_ADD (VAlu ALU_SRL (VP kf wzero) (VL (wlit 3%uint63))) (VL SBw)))
      with (alu64 ALU_ADD (alu64 ALU_SRL (den E' (VP kf wzero)) (wbv (wlit 3%uint63))) (wbv SBw)).
    rewrite HeapCtr.den_VPz. apply bv_eq. unfold alu64, alu. rewrite bv_add_unsigned, bv_shiftr_unsigned, bv_and_unsigned, ev_sh.
    destruct (entry_w kf lenf _ INf) as (Kf0 & _).
    destruct (CtrDelta.reg_E' OPS E st ms mo HS FOK Fv Gv kf rf Frf) as (EKF & _). rewrite EKF. fold Af.
    replace (bv_unsigned (wbv (wlit 3%uint63))) with 3 by (vm_compute; reflexivity).
    replace (bv_unsigned (Z_to_bv 64 63)) with 63 by (vm_compute; reflexivity).
    change (Z.land 3 63) with 3.
    replace (bv_unsigned (wbv SBw)) with 0x7fff8000 by (vm_compute; reflexivity).
    unfold shad, ASHOFF, bv_wrap, bv_modulus. rewrite Z.mod_small; [lia|]. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8.
    change (2 ^ Z.of_N 64) with (2 ^ 64). clear - LOA HIA ATR NR. Z.div_mod_to_equations. lia.
  - exact MINVo.
Qed.
End ADDED.

Variable MP : Model -> Prop.
Variable PB : (int -> list byte) -> Prop.

Lemma mem_inv_of : forall E st ms mo, st_ok asegs OPS E st ms mo -> ALib.Mem.mem_inv asegs (ms_mem ms).
Proof.
  intros E st ms mo HS a b Hm. unfold ALib.Mem.ro_addr. destruct (find_segment asegs (bv_unsigned a) 1) as [seg|] eqn:Fs; [|reflexivity].
  rewrite (so_minv _ _ _ _ _ _ HS a b Hm seg Fs). reflexivity.
Qed.

Lemma scan_inv : forall E fs R wnl cv kf rf lenf, facts_hold E fs ->
  forallb (tw_other_ok fs R wnl cv kf (KnownT.KnownT.known_eq_t fs (rg_hi rf) lenf)) wnl = true ->
  forall k len kd, In (k, len, kd) wnl -> weqb kd K_TWIN = true ->
  exists kb, block_of_twin fs k = Some kb /\ kb <> kf
    /\ ((exists n2 r2, CtrA.win_lookup wnl kb = Some (n2, CtrLib.K_BLOCK) /\ IMap.find kb R = Some r2 /\ rg_w r2 = true
                       /\ rg_lo r2 = 0%uint63 /\ 0 < hiZ E r2)
        \/ (hiZ E rf = bv_unsigned (den E lenf) /\ twin_arm_evx fs R wnl cv k len kf = true)).
Proof.
  intros E fs R wnl cv kf rf lenf HF SCAN k len kd Hin KT.
  pose proof (proj1 (forallb_forall _ _) SCAN _ Hin) as C. unfold tw_other_ok in C. rewrite KT in C.
  destruct (block_of_twin fs k) as [kb|] eqn:BT; [|discriminate C]. exists kb. split; [reflexivity|].
  destruct (negb (PrimInt63.eqb kb kf)) eqn:NE; [|discriminate C]. apply negb_true_iff in NE. apply Uint63.eqb_false_spec in NE. split; [exact NE|].
  match type of C with (if ?a then true else ?b) = true => destruct a eqn:OLD; [left| right] end.
  - destruct (CtrA.win_lookup wnl kb) as [[n2 kdb]|] eqn:WL2; [|discriminate OLD].
    destruct (weqb kdb CtrLib.K_BLOCK) eqn:KB; [|discriminate OLD]. apply weqb_eq in KB. subst kdb.
    unfold blk_reg_ok in OLD. destruct (IMap.find kb R) as [r2|] eqn:Fr2; [|discriminate OLD].
    destruct (rg_w r2) eqn:W2; [|discriminate OLD]. destruct (PrimInt63.eqb (rg_lo r2) 0%uint63) eqn:L2; [|discriminate OLD].
    apply Uint63.eqb_correct in L2.
    pose proof (KnownA.KnownA.known_ltu_sound E _ _ _ HF OLD) as LT. cbn [den] in LT. rewrite wbv_unsigned, wzero_ok in LT.
    exists n2, r2. repeat (split; [reflexivity || assumption|]). exact LT.
  - destruct (KnownT.KnownT.known_eq_t fs (rg_hi rf) lenf) eqn:FULL; [|discriminate C].
    pose proof (KnownA.KnownA.known_eq_sound E _ _ _ HF FULL) as EQ. split; [unfold hiZ; rewrite EQ; reflexivity| exact C].
Qed.

Theorem twin_out_sound : forall pc sel, contract_sound asegs OPS MP PB (twin_out_c pc sel).
Proof.
  intros pc sel st sts Hspc Happ K E ms mo HS HMP HPB HK. cbn [c_apply twin_out_c] in Happ.
  destruct (twin_out_apply_shape sel st sts Happ)
    as [->|(hargs & wnl & kf & lenf & rf & h1 & AW & RVN & FOK & SRG & SFO & WLf & Frf & WRf & LO0 & POSK & SHAPE & SCAN & H1 & ->)].
  {   exact (HK st (or_introl eq_refl) E ms mo (env_ext_refl _ _) HMP HS). }
  destruct (CtrPre.aheap_call_facts AI ACCT UNIV Cw OPS AI_fake OPS_holds1 E st ms mo hargs wnl HS AW)
    as (r1 & n & md & A & nw & rest & LB & Hr1 & Hf & Hc & Hn & Eh & T & N & Ln & N255 & SW & NW & AN & JU & HA & WF & HC & W & ARW & TI).
  destruct (CallA.stack_sound_g asegs OPS E st ms mo 0%uint63 HS ltac:(change (to_Z 0%uint63) with 0; lia) SRG)
    as (ks & offs & rss & ksp & HX2 & Hrs & K0 & Hksp & K16 & A16 & Esp & LOX & HI64 & STK & SPR & LOR & LOZ0).
  destruct (CallA.sp_floor_sound asegs OPS E st ms mo hargs n md A nw rest ks offs rss HS SFO Hn Eh SPR LOZ0) as (wlo & len & INw & FLOOR0).
  pose proof (proj1 (Forall_forall _ _) WF _ INw) as (_ & _ & _ & KDs). cbn [w_kind w_lo] in KDs.
  assert (CE : ATOP + 4096 <= bv_unsigned (den E (VP STACK_ID wlo))).
  { destruct KDs as [[_ C]|[[K1 _]|[K1 _]]]; [exact C| unfold K_BLOCK, K_STACK in K1; lia| unfold K_SUB, K_STACK in K1; lia]. }
  change (to_Z 0%uint63) with 0 in LOR.
  assert (SP2 : bv_unsigned (AP.getr (ms_regs ms) 2%bv) = bv_unsigned (ev E ks) + keyZ ksp).
  { rewrite <- HeapCtr.reg_of_X2, (GlueA.getr_RA asegs OPS E st ms mo HS X2). exact Esp. }
  pose proof (so_facts _ _ _ _ _ _ HS) as HF.
  assert (POSf : 0 < hiZ E rf).
  { pose proof (KnownA.KnownA.known_ltu_sound E _ _ _ HF POSK) as LT. cbn [den] in LT. rewrite wbv_unsigned, wzero_ok in LT. exact LT. }
  pose proof (scan_inv E _ _ _ _ kf rf lenf HF SCAN) as OTH.
  pose proof (CtrFree.cvu_of Cw Cw_vec_unowned E st (ms_mem ms) LB n md A nw rest ltac:(rewrite <- Eh; exact Hf) N HC) as CVU.
  assert (KB : exists b, vis W b /\ is_heap b /\ ab_addr b = bv_unsigned (ev E kf) /\ ab_size b = bv_unsigned (den E lenf)).
  { eapply kblock_heap; try eassumption. exact (HeapCtrB.win_lookup_In _ _ _ _ WLf). }
  destruct KB as (b & Vb & HHb & EAb & ENb).
  set (Fv := fun _ : Z => Z_to_bv 64 (shad (bv_unsigned (ev E kf)))). set (Gv := fun (_ _ : Z) => Z_to_bv 8 0).
  assert (HSF : st_ok asegs OPS (CtrDelta.E' E st Fv Gv)
            (SS (s_pc st) (s_rf st) (s_ff st) RNone (RgO st lenf) (link_fact (s_next st) kf :: s_facts st) (set_op HEAP_ID h1 (s_ops st)) (s_priv st)
                (PrimInt63.add (s_next st) 1%uint63))
            (MS (ms_regs ms) (ms_fregs ms) (Z_to_bv 64 (to_Z (s_pc st))) (ms_fcsr ms) None (ms_mem ms) (seg_rom asegs)) mo).
  { eapply (twin_out_post E st ms mo HS wnl n rest LB (den E A) NW) with (b := b) (WW := W) (rf := rf) (ks := ks) (offs := offs) (rss := rss) (ksp := ksp)
           (hargs := hargs) (md := md) (A := A) (nw := nw); try eassumption; try reflexivity; try lia.
    all: try exact (mem_inv_of E st ms mo HS). all: try exact (so_mf _ _ _ _ _ _ HS). }
  apply (HK _ (or_introl eq_refl) (CtrDelta.E' E st Fv Gv) ms mo (CtrDelta.EXT E st Fv Gv) HMP).
  rewrite (GlueA.ms_formA asegs OPS E st ms mo HS RVN) at 1.
  unfold addfact, set_ops, setregs, set_next. cbn [s_pc s_rf s_ff s_resv s_regs s_facts s_ops s_priv s_next]. rewrite RVN. exact HSF.
Qed.
End TwinOut.

From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.BothW Require Import BImg.
Module TwinB.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.PropExec OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.MState OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Cells OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Frame OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.ITree OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Nodes.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA.AcctCore OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA.ExecF OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA.ITreeA OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA.NodesA.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.STree OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.AsanCtrl OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.AsanEmbed.
Import AProto.TwinB ABase.TwinB AMalloc_iface.TwinB AMalloc_iface2.TwinB.
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

Import ValP MemP CtrFX.
Import ActrA.
Module AP := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.PropExec.

Unset Nia Cache. Unset Nra Cache.

Ltac split_ands H :=
  match type of H with
  | (if ?a then ?b else false) = true =>
      let X := fresh "Q" in let Y := fresh "Q" in
      assert (X : a = true) by (destruct a; [reflexivity| discriminate H]);
      assert (Y : b = true) by (rewrite X in H; exact H); clear H; split_ands X; split_ands Y
  | _ => idtac
  end.

Lemma twin_out_apply_shape : forall sel st sts, twin_out_apply sel st = Some sts ->
  sts = [st] \/
  exists hargs wnl kf n rf h1,
    aheap_windows st = Some (hargs, wnl) /\ s_resv st = RNone /\ fresh_ok st = true
    /\ stack_room_g st 0%uint63 = true /\ sp_floor_ok st hargs = true
    /\ CtrA.win_lookup wnl kf = Some (n, CtrLib.K_BLOCK) /\ IMap.find kf (s_regs st) = Some rf
    /\ rg_w rf = true /\ rg_lo rf = 0%uint63 /\ KnownT.KnownT.known_ltu_t (s_facts st) (VL wzero) (rg_hi rf) = true
    /\ size_shape_ok (s_facts st) n = true
    /\ forallb (tw_other_ok (s_facts st) (s_regs st) wnl (carg_vecs st) kf (KnownT.KnownT.known_eq_t (s_facts st) (rg_hi rf) n)) wnl = true
    /\ heap_add_window hargs (VP (s_next st) wzero) (twin_len n) (VL K_TWIN) = Some h1
    /\ sts = [addfact (set_ops (setregs (set_next st (PrimInt63.add (s_next st) 1%uint63)) (IMap.add (s_next st) (twin_region n) (s_regs st)))
                               (set_op HEAP_ID h1 (s_ops st))) (link_fact (s_next st) kf)].
Proof.
  intros sel st sts H. unfold twin_out_apply in H.
  destruct (aheap_windows st) as [[hargs wnl]|] eqn:AW; [|discriminate H].
  destruct (twsel_blk sel st wnl) as [kf|] eqn:SEL; [| left; injection H as <-; reflexivity].
  destruct (tw_out (s_facts st) wnl kf) as [p0|] eqn:TO; [left; injection H as <-; reflexivity|].
  destruct (CtrA.win_lookup wnl kf) as [[n kd]|] eqn:WL; [|discriminate H].
  destruct (IMap.find kf (s_regs st)) as [rf|] eqn:Frf; [|discriminate H].
  right.
  match type of H with (if ?c then _ else _) = _ => destruct c eqn:CK; [|discriminate H] end.
  split_ands CK.
  cbn [fresh fst snd] in H.
  destruct (heap_add_window hargs (VP (s_next st) wzero) (twin_len n) (VL K_TWIN)) as [h1|] eqn:H1; [|discriminate H]. injection H as <-.
  match goal with X : weqb kd CtrLib.K_BLOCK = true |- _ => apply weqb_eq in X; subst kd end.
  assert (RV : s_resv st = RNone) by (destruct (s_resv st); try reflexivity; discriminate).
  match goal with X : PrimInt63.eqb (rg_lo rf) 0%uint63 = true |- _ => apply Uint63.eqb_correct in X end.
  exists hargs, wnl, kf, n, rf, h1. repeat (split; [reflexivity || assumption|]). reflexivity.
Qed.

Lemma w2Z_twin : forall kd, w2Z kd = 9 -> kd = K_TWIN.
Proof.
  intros [t l] H. unfold w2Z in H. cbn [wt wl] in H. pose proof (Uint63.to_Z_bounded l) as B. destruct t.
  - exfalso. unfold two63 in H. lia.
  - assert (L : l = 9%uint63) by (apply Uint63.to_Z_inj; change (to_Z 9%uint63) with 9; lia). subst l. reflexivity.
Qed.

Lemma nonstack_len_In : forall m ws l k len kd, CtrA.nonstack_windows m ws = Some l -> In (k, len, kd) l -> In len ws.
Proof.
  induction m as [|m IH]; intros ws l k len kd H Hin; [cbn in H; injection H as <-; destruct Hin|].
  destruct ws as [|wlo [|ln [|kdv ws']]]; try (cbn in H; discriminate).
  cbn [CtrA.nonstack_windows] in H. destruct kdv as [kw| | | | | | | | | |]; try discriminate.
  destruct (CtrA.nonstack_windows m ws') as [l0|] eqn:NW0; [|discriminate].
  destruct (weqb kw wzero).
  - injection H as <-. right; right; right. exact (IH _ _ _ _ _ NW0 Hin).
  - destruct wlo as [|k0 o| | | | | | | | |]; try discriminate. cbv beta iota in H.
    match type of H with (if ?c then _ else _) = _ => destruct c; [|discriminate H] end. injection H as <-.
    destruct Hin as [X|X]; [right; left; congruence| right; right; right; exact (IH _ _ _ _ _ NW0 X)].
Qed.

Section TwinOut.
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

Hypothesis Cw_ghost_grow : forall md ca LB ws m b0 n0 n, cw_holds Cw md ca LB ws m ->
  In (Win b0 n0 K_BLOCK) ws -> 0 < n0 -> b0 mod 8 = 0 ->
  (forall a, in_iv (shad b0, n) a -> ~ in_user LB a) -> cw_holds Cw md ca ((shad b0, n) :: LB) (ws ++ [Win (shad b0) n K_TWINz]) m.

Hypothesis Cw_vec_unowned : forall md ca LB ws m i a, cw_holds Cw md ca LB ws m -> In i (VECS md) -> nth_error ca i = Some a -> bv_unsigned a <> 0 ->
  forall w, In w ws -> w_kind w = K_BLOCK -> 0 < w_len w -> w_lo w <> bv_unsigned a.
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

Section ADDED.
Variables (E : env) (st : sstate) (ms : machine_state) (mo : Model).
Hypothesis HS : st_ok bsegs OPS E st ms mo.
Variables (wnl : list (int * sv * w64)) (nn : nat) (rest : list sv) (LB : blocks) (aw : word).
Hypothesis NW : CtrA.nonstack_windows nn rest = Some wnl.
Hypothesis AN : CtrA.windows_anchored (s_regs st) wnl = true.
Hypothesis WF : windows_wf (wins_of E nn rest) LB (ATOP + 4096).
Variable WW : wit.
Hypothesis AR : aw_realW AI ACCT UNIV aw LB (ms_mem ms) mo WW.
Hypothesis TI : ties WW (wins_of E nn rest).
Hypothesis CVU : forall kb, In kb (carg_vecs st) -> bv_unsigned (ev E kb) <> 0 -> forall w, In w (wins_of E nn rest) -> w_kind w = K_BLOCK -> 0 < w_len w -> w_lo w <> bv_unsigned (ev E kb).
Variables (kf : int) (rf : region) (lenf : sv).
Hypothesis Frf : IMap.find kf (s_regs st) = Some rf.
Hypothesis WLf : CtrA.win_lookup wnl kf = Some (lenf, CtrLib.K_BLOCK).
Hypothesis WRf : rg_w rf = true.
Hypothesis LO0 : rg_lo rf = 0%uint63.
Hypothesis POSf : 0 < hiZ E rf.
Hypothesis SHAPE : size_shape_ok (s_facts st) lenf = true.
Hypothesis OTH : forall k len kd, In (k, len, kd) wnl -> weqb kd K_TWIN = true ->
  exists kb, block_of_twin (s_facts st) k = Some kb /\ kb <> kf
    /\ ((exists n2 r2, CtrA.win_lookup wnl kb = Some (n2, CtrLib.K_BLOCK) /\ IMap.find kb (s_regs st) = Some r2 /\ rg_w r2 = true
                       /\ rg_lo r2 = 0%uint63 /\ 0 < hiZ E r2)
        \/ (hiZ E rf = bv_unsigned (den E lenf) /\ twin_arm_evx (s_facts st) (s_regs st) wnl (carg_vecs st) k len kf = true)).

Let Af : Z := bv_unsigned (ev E kf).
Let nf : Z := bv_unsigned (den E lenf).
Let m : amem := ms_mem ms.

Lemma AWHf : aw_holds_asan AI ACCT UNIV aw LB m mo.
Proof. exact (aw_real_holds AI ACCT UNIV _ _ _ _ _ AR). Qed.
Lemma HWf : aw_holds_w AI ACCT UNIV WW aw LB m mo.
Proof. exact (proj1 AR). Qed.
Lemma GAf : ghost_apart (wins_of E nn rest).
Proof. destruct TI as (_ & _ & _ & _ & _ & _ & _ & _ & _ & X & _). exact X. Qed.

Lemma entry_w : forall k len kd, In (k, len, kd) wnl ->
  k <> 0%uint63 /\ In (Win (bv_unsigned (ev E k)) (bv_unsigned (den E len)) (w2Z kd)) (wins_of E nn rest)
  /\ exists b, In b LB /\ (forall a, in_iv (bv_unsigned (ev E k), bv_unsigned (den E len)) a -> in_iv b a)
       /\ (kd = CtrLib.K_BLOCK -> b = (bv_unsigned (ev E k), bv_unsigned (den E len))).
Proof.
  intros k len kd Hin. destruct (HeapCtrB.TwinB.nonstack_windows_In E nn rest wnl k len kd NW Hin) as (K0 & _ & KD & INW).
  split; [exact K0|]. split; [exact INW|].
  pose proof (proj1 (Forall_forall _ _) WF _ INW) as (W1 & W2 & W3 & [[KS0 _]|[[KB B]|[KS2 (b & Hb & SUB)]]]); unfold w_iv in *; cbn [w_kind w_lo w_len] in *.
  - exfalso. exact (KD KS0).
  - eexists. split; [exact B|]. split; [intros a Ha; exact Ha| reflexivity].
  - exists b. split; [exact Hb|]. split; [exact SUB|]. intros ->. change (w2Z CtrLib.K_BLOCK) with 1 in KS2. unfold K_SUB in KS2. lia.
Qed.

Lemma kblock_heap : forall k len, In (k, len, CtrLib.K_BLOCK) wnl ->
  exists b, vis WW b /\ is_heap b /\ ab_addr b = bv_unsigned (ev E k) /\ ab_size b = bv_unsigned (den E len).
Proof.
  intros k len Hin. destruct (entry_w k len _ Hin) as (_ & INW & b0 & Hb0 & _ & EQ). rewrite (EQ eq_refl) in Hb0.
  change (w2Z CtrLib.K_BLOCK) with K_BLOCK in INW.
  set (A := bv_unsigned (ev E k)) in *. set (N := bv_unsigned (den E len)) in *.
  pose proof HWf as HW0. pose proof HW0 as (AH & HT & _).
  destruct TI as (T1 & _ & T3 & _).
  assert (GHOST : forall g, In g (wins_of E nn rest) -> K_GHOST <= w_kind g -> w_iv g = (A, N) -> 0 < N -> False).
  { intros g Hg KG EG PN. apply (GAf g (Win A N K_BLOCK) Hg INW KG eq_refl A); [rewrite EG|]; unfold in_iv, w_iv; cbn [fst snd w_lo w_len]; lia. }
  destruct (LB_cases AI ACCT UNIV WW aw LB m mo (A, N) HW0 Hb0) as [(b & Vb & EQb)|[(b & HbT & EQb)|(b & Vb & EQb)]].
  - destruct (kind_cases b) as [HH|HF].
    + exists b. unfold user_iv in EQb. rewrite (usz_heap b HH) in EQb. injection EQb as E1 E2. auto.
    + exfalso. destruct (T3 b (conj Vb HF)) as [X _].
      destruct (AI_fake _ _ _ _ _ b AH (proj1 Vb) HF) as (_ & _ & _ & _ & NP & _).
      unfold user_iv in EQb. rewrite (usz_fake b HF) in EQb. injection EQb as E1 E2.
      apply (GHOST _ X); [cbn [w_kind]; unfold K_FRAMEz, K_GHOST; lia| unfold w_iv; cbn [w_lo w_len]; rewrite E1, E2; reflexivity| lia].
  - exfalso. destruct (LB_twin_facts AI ACCT UNIV WW aw LB m mo b HW0 HbT) as (_ & _ & P).
    unfold twin_iv in EQb. injection EQb as E1 E2.
    apply (GHOST _ (T1 b HbT)); [cbn [w_kind]; unfold K_TWINz, K_GHOST; lia| unfold w_iv; cbn [w_lo w_len]; rewrite E1, E2; reflexivity| lia].
  - exfalso. destruct (T3 b Vb) as [_ Y]. destruct Vb as [Vb HF].
    destruct (AI_fake _ _ _ _ _ b AH (proj1 Vb) HF) as (_ & _ & _ & _ & NP & _).
    unfold fsh_iv in EQb. injection EQb as E1 E2.
    apply (GHOST _ Y); [cbn [w_kind]; unfold K_FTWINz, K_GHOST; lia| unfold w_iv; cbn [w_lo w_len]; rewrite E1, E2; reflexivity|].
    rewrite E2. unfold shlen. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8. clear - NP. Z.div_mod_to_equations. lia.
Qed.

Lemma INf : In (kf, lenf, CtrLib.K_BLOCK) wnl.
Proof. exact (HeapCtrB.TwinB.win_lookup_In _ _ _ _ WLf). Qed.
Lemma WINf : In (Win Af nf K_BLOCK) (wins_of E nn rest).
Proof. destruct (entry_w kf lenf _ INf) as (_ & X & _). exact X. Qed.
Lemma blockLB : In (Af, nf) LB.
Proof. destruct (entry_w kf lenf _ INf) as (_ & _ & b & Hb & _ & EQ). rewrite (EQ eq_refl) in Hb. exact Hb. Qed.

Lemma heap_facts : forall b, vis WW b -> is_heap b ->
  1 <= ab_size b <= AREQMAX /\ ablk (ab_addr b) (ab_addr b + ab_size b) /\ ab_addr b + ab_size b <= ATOP /\ ab_addr b mod 16 = 0.
Proof.
  intros b Vb HH. pose proof HWf as (AH & _).
  destruct (heap_block_facts AI _ _ _ _ _ b AH (proj1 Vb) HH) as (N & (BK & _ & HI & AL) & _). auto.
Qed.

Lemma not_out : forall b, vis WW b -> is_heap b -> ab_addr b = Af -> ab_size b = nf -> ~ In b (w_T WW).
Proof.
  intros b Vb HH EA EN HbT. destruct (heap_facts b Vb HH) as (NR & BK & HI & AL). rewrite EA, EN in *.
  pose proof atop_range as ATR. unfold ablk, AIMG_HI, KLS in BK.
  pose proof (so_facts _ _ _ _ _ _ HS) as HF.
  destruct TI as (T1 & _). pose proof (T1 b HbT) as INT. rewrite EA, EN in INT.
  destruct (HeapCtrB.TwinB.wins_cover E nn rest wnl _ NW INT) as [KS|(k & len & kd & Ik & EW)]; [cbn [w_kind] in KS; unfold K_TWINz, K_STACK in KS; lia|].
  injection EW as E1 E2 E3. unfold K_TWINz in E3. symmetry in E3. apply w2Z_twin in E3. subst kd.
  destruct (OTH k len K_TWIN Ik eq_refl) as (kb & BT & NKB & CASE).
  pose proof (CallA.TwinB.block_of_twin_sound E _ k kb HF BT) as LK.
  pose proof (bv_unsigned_in_range 64 (ev E kb)) as RKB. change (bv_modulus 64) with (2 ^ 64) in RKB.
  rewrite Z.mod_small in LK by (clear - RKB; Z.div_mod_to_equations; lia).
  assert (SHE : bv_unsigned (ev E kb) / 8 = Af / 8).
  { rewrite <- E1 in LK. unfold shad, ASHOFF in LK. rewrite Z.shiftr_div_pow2 in LK by lia. change (2 ^ 3) with 8 in LK. lia. }
  destruct (entry_w kf lenf _ INf) as (Kf0 & _).
  assert (ZF : PrimInt63.eqb kf 0%uint63 = false) by (apply Uint63.eqb_false_spec; exact Kf0).
  assert (KZ0 : keyZ 0%uint63 = 0) by reflexivity.
  assert (RF : forall x, Af <= x < Af + hiZ E rf -> bv_unsigned (ev E kf) + loZ rf <= x < bv_unsigned (ev E kf) + hiZ E rf).
  { intros x Hx. unfold loZ. rewrite LO0, KZ0. fold Af. lia. }
  destruct CASE as [(n2 & r2 & WL2 & Fr2 & W2 & L2 & P2)|(FULL & EVA)].
  -
    pose proof (HeapCtrB.TwinB.win_lookup_In _ _ _ _ WL2) as IN2.
    destruct (kblock_heap kb n2 IN2) as (b2 & Vb2 & HH2 & EA2 & EN2).
    destruct (heap_facts b2 Vb2 HH2) as (_ & _ & _ & AL2). rewrite EA2 in AL2.
    assert (EKB : bv_unsigned (ev E kb) = Af) by (clear - SHE AL AL2; Z.div_mod_to_equations; lia).
    destruct (entry_w kb n2 _ IN2) as (Kb0 & _).
    assert (ZB : PrimInt63.eqb kb 0%uint63 = false) by (apply Uint63.eqb_false_spec; exact Kb0).
    apply (so_disj _ _ _ _ _ _ HS kb r2 kf rf Fr2 Frf NKB ZB ZF (or_introl W2) Af). split.
    + unfold loZ. rewrite L2, KZ0, EKB. lia.
    + apply RF. lia.
  -
    destruct (CallV.TwinB.twin_ev_cases E _ _ _ _ _ _ _ HF EVA) as (kb2 & BT2 & LW & ALk & EVD).
    rewrite BT in BT2. injection BT2 as <-.
    pose proof (GTwinSub.GTwinSub.mod8_of_align E _ kb HF ALk) as K8.
    assert (EKB : bv_unsigned (ev E kb) = Af) by (clear - SHE AL K8; Z.div_mod_to_equations; lia).
    destruct EVD as [CVk|(ks & lens & kds & rsub & Hins & NXs & NKBs & NKTs & Frsub & RWs & L0s & HPOS & XLO & XHI)].
    + apply (CVU kb CVk ltac:(rewrite EKB; lia) _ WINf); [reflexivity| cbn [w_len]; lia| cbn [w_lo]; symmetry; exact EKB].
    + idtac.
      assert (XIN : Af <= bv_unsigned (ev E ks) < Af + nf).
      { rewrite <- E2, EKB in XHI. rewrite EKB in XLO. unfold shlen in XHI. rewrite Z.shiftr_div_pow2 in XHI by lia. change (2 ^ 3) with 8 in XHI.
        clear - XLO XHI NR. Z.div_mod_to_equations. lia. }
      destruct (entry_w ks lens kds Hins) as (Ks0 & _).
      assert (ZKs : PrimInt63.eqb ks 0%uint63 = false) by (apply Uint63.eqb_false_spec; exact Ks0).
      apply (so_disj _ _ _ _ _ _ HS ks rsub kf rf Frsub Frf NXs ZKs ZF (or_introl RWs) (bv_unsigned (ev E ks))). split.
      * unfold loZ. rewrite L0s, KZ0. lia.
      * apply RF. fold nf in FULL. rewrite FULL. exact XIN.
Qed.

Variable b : ablock.
Hypothesis Vb : vis WW b.
Hypothesis HHb : is_heap b.
Hypothesis EAb : ab_addr b = Af.
Hypothesis ENb : ab_size b = nf.

Definition W1 : wit := set_T WW (b :: w_T WW).
Definition LB1 : blocks := (shad Af, shlen (nf + 7)) :: LB.
Definition WTo : window := Win (shad Af) (shlen (nf + 7)) K_TWINz.

Lemma OUTW : aw_holds_w AI ACCT UNIV W1 aw LB1 m mo /\ ~ In (shad Af, shlen (nf + 7)) LB
  /\ (forall g, 0 <= g -> 8 * g < nf -> m (ALib.Mem.wa (shad Af + g)) = Some (Z_to_bv 8 (if 8 * g + 8 <=? nf then 0 else nf - 8 * g))).
Proof.
  pose proof (twin_out_w AI ACCT UNIV AI_fake WW aw LB m mo b HWf Vb HHb (not_out b Vb HHb EAb ENb)) as X.
  unfold twin_iv in X. rewrite EAb, ENb in X. exact X.
Qed.
Lemma HW1 : aw_holds_w AI ACCT UNIV W1 aw LB1 m mo. Proof. exact (proj1 OUTW). Qed.
Lemma AWH1 : aw_holds_asan AI ACCT UNIV aw LB1 m mo. Proof. exists W1. exact HW1. Qed.
Lemma bT1 : In b (w_T W1). Proof. left. reflexivity. Qed.

Lemma twin_facts : 0x800be200 <= shad Af /\ shad Af + shlen (nf + 7) <= shad ATOP /\ 1 <= shlen (nf + 7) /\ 1 <= nf <= AREQMAX /\ Af mod 16 = 0
  /\ AIMG_HI <= Af /\ Af + nf <= ATOP.
Proof.
  destruct (heap_facts b Vb HHb) as (NR & BK & HI & AL). rewrite EAb, ENb in *.
  destruct (shadow_tight Af nf BK HI ltac:(lia)) as [S1 S2].
  destruct (LB_twin_facts AI ACCT UNIV W1 aw LB1 m mo b HW1 bT1) as (_ & _ & T3). rewrite ?EAb, ?ENb in T3.
  pose proof (ablk_lin _ _ BK) as (X1 & _). auto 10.
Qed.

Lemma TWFRESH : forall a, in_iv (shad Af, shlen (nf + 7)) a -> ~ in_user LB a.
Proof.
  intros a Ha U. apply in_ivs_In in U as (v & Hv & Hin). destruct v as [A' n'].
  apply (aw_blocks_disj_asan AI ACCT UNIV AI_fake aw LB1 m mo (A', n') (shad Af, shlen (nf + 7)) a AWH1 (or_intror Hv) (or_introl eq_refl)); [| exact Hin| exact Ha].
  cbn [fst]. intros ->. apply (proj1 (proj2 OUTW)).
  rewrite <- (LB_same_addr AI ACCT UNIV AI_fake W1 aw LB1 m mo (shad Af) n' (shlen (nf + 7)) HW1 (or_intror Hv) (or_introl eq_refl)). exact Hv.
Qed.

Lemma windows_wf_mono1 : forall ws L1 L2 c, windows_wf ws L1 c -> (forall v, In v L1 -> In v L2) -> windows_wf ws L2 c.
Proof.
  intros ws L1 L2 c WF0 SUB. apply Forall_forall. intros w Hw.
  pose proof (proj1 (Forall_forall _ _) WF0 w Hw) as (X1 & X2 & X3 & [[K S]|[[K B]|[K (b0 & Hb0 & SB)]]]).
  - split; [exact X1|]. split; [exact X2|]. split; [exact X3|]. left; auto.
  - split; [exact X1|]. split; [exact X2|]. split; [exact X3|]. right; left; auto.
  - split; [exact X1|]. split; [exact X2|]. split; [exact X3|]. right; right. split; [exact K|]. exists b0. auto.
Qed.

Variables (hargs : list sv) (md : w64) (A : sv) (nw : w64).
Hypothesis Hf : find_op HEAP_ID (s_ops st) = Some hargs.
Hypothesis Eh : hargs = VL md :: A :: VL nw :: rest.
Hypothesis Tnw : wt nw = false.
Hypothesis Nn : nn = Z.to_nat (to_Z (wl nw)).
Hypothesis Ln : (3 * nn <= length rest)%nat.
Hypothesis N255 : (nn <= 255)%nat.
Hypothesis FOK : fresh_ok st = true.
Variables (Fv : Z -> word) (Gv : Z -> Z -> byte).
Hypothesis FV0 : Fv 0 = Z_to_bv 64 (shad Af).
Notation E' := (CtrDelta.TwinB.E' E st Fv Gv).
Let sh : int := s_next st.
Variable h1 : list sv.
Hypothesis H1 : heap_add_window hargs (VP sh wzero) (twin_len lenf) (VL K_TWIN) = Some h1.

Lemma ev_sh : bv_unsigned (ev E' sh) = shad Af.
Proof.
  pose proof (CtrDelta.TwinB.ev_E'_fresh E st FOK Fv Gv 0%nat ltac:(lia)) as X. cbn [addn] in X. fold sh in X. rewrite X. change (Z.of_nat 0) with 0. rewrite FV0.
  destruct twin_facts as (S1 & S2 & S3 & _). pose proof atop_range as ATR.
  apply Z_to_bv_small. unfold bv_modulus. change (2 ^ Z.of_N 64) with (2 ^ 64).
  assert (SA : shad ATOP <= 2 ^ 47).
  { unfold shad, ASHOFF. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8. clear - ATR. Z.div_mod_to_equations. lia. }
  unfold two64. lia.
Qed.
Lemma lenf_below : sv_vars_below (s_next st) lenf = true.
Proof.
  pose proof (CtrDelta.TwinB.rest_below st FOK rest hargs md A nw Hf Eh) as RB.
  exact (proj1 (forallb_forall _ _) RB lenf (nonstack_len_In _ _ _ _ _ _ NW INf)).
Qed.

Lemma den_lenf' : bv_unsigned (den E' lenf) = nf.
Proof. rewrite (CtrDelta.TwinB.den_E' E st Fv Gv lenf lenf_below). reflexivity. Qed.

Lemma DEC1 : decode (map (den E') h1) = Some (w2Z md, den E A, wins_of E nn rest ++ [WTo], map (den E) (skipn (3 * nn) rest)).
Proof.
  destruct twin_facts as (_ & _ & _ & NR & _). unfold AREQMAX in NR.
  assert (NS : to_Z (wl nw) + 1 < two63).
  { pose proof (Uint63.to_Z_bounded (wl nw)) as B. unfold two63. rewrite Nn in N255. lia. }
  destruct (CtrPost.TwinB.add_window_facts E' md A nw rest nn (VP sh wzero) (twin_len lenf) (VL K_TWIN) Tnw Nn Ln NS) as (A1 & T1 & N1 & L1 & W1' & S1).
  set (rest1 := firstn (3 * nn) rest ++ [VP sh wzero; twin_len lenf; VL K_TWIN] ++ skipn (3 * nn) rest) in *.
  set (nw1 := wadd nw wone) in *.
  assert (EH1 : h1 = VL md :: A :: VL nw1 :: rest1) by (pose proof H1 as H1'; rewrite Eh in H1'; rewrite A1 in H1'; injection H1' as X; symmetry; exact X).
  rewrite EH1.
  rewrite (decode_hargs E' md A nw1 rest1 (S nn) T1 N1 L1). rewrite W1', S1.
  pose proof (CtrDelta.TwinB.rest_below st FOK rest hargs md A nw Hf Eh) as RB.
  rewrite (CtrDelta.TwinB.den_E' E st Fv Gv A (CtrDelta.TwinB.A_below st FOK rest hargs md A nw Hf Eh)).
  rewrite (CtrDelta.TwinB.wins_of_E' E st Fv Gv _ _ RB).
  rewrite (CtrDelta.TwinB.map_den_E' E st Fv Gv _ (CtrFree.TwinB.forallb_skipn _ (3 * nn) rest RB)).
  assert (C3 : Win (bv_unsigned (den E' (VP sh wzero))) (bv_unsigned (den E' (twin_len lenf))) (bv_unsigned (den E' (VL K_TWIN))) = WTo).
  { unfold WTo. rewrite HeapCtr.TwinB.den_VPz, ev_sh. rewrite (CallA.TwinB.twin_len_den E' lenf) by (rewrite den_lenf'; lia).
    rewrite den_lenf'. unfold shlen. rewrite Z.shiftr_div_pow2 by lia. reflexivity. }
  rewrite C3. reflexivity.
Qed.

Hypothesis AWden : aw = den E A.
Hypothesis HC : cw_holds Cw (w2Z md) (map (den E) (skipn (3 * nn) rest)) LB (wins_of E nn rest) m.

Lemma HOLDN1 : op_holds OPS HEAP_ID (map (den E') h1) m mo.
Proof.
  rewrite OPS_holds1. destruct twin_facts as (S1 & S2 & S3 & NR & AL & LOA & HIA). pose proof atop_range as ATR.
  assert (SA : shad ATOP <= 2 ^ 47).
  { unfold shad, ASHOFF. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8. clear - ATR. Z.div_mod_to_equations. lia. }
  exists (w2Z md), aw, (wins_of E nn rest ++ [WTo]), (map (den E) (skipn (3 * nn) rest)), LB1, W1.
  split; [rewrite AWden; exact DEC1|]. split; [exact HW1|]. split; [| split].
  - apply Forall_app. split.
    + apply (windows_wf_mono1 _ LB LB1 _ WF). intros v Hv. right. exact Hv.
    + constructor; [|constructor]. unfold window_wf, WTo, w_iv. cbn [w_lo w_len w_kind]. split; [lia|]. split; [lia|]. split; [unfold two64; lia|].
      right; right. split; [unfold K_SUB, K_TWINz; lia|]. exists (shad Af, shlen (nf + 7)). split; [left; reflexivity|]. intros a Ha. exact Ha.
  - apply (Cw_ghost_grow _ _ _ _ m Af nf (shlen (nf + 7)) HC WINf); [lia| clear - AL; Z.div_mod_to_equations; lia| exact TWFRESH].
  - pose proof (ties_twin_out WW (wins_of E nn rest) b TI) as X. rewrite EAb, ENb in X. apply X.
    apply (ghost_apart_new_ghosts (wins_of E nn rest) _ LB (ATOP + 4096) WF GAf).
    intros w Hw. apply in_app_or in Hw as [Hw|[<-|[]]]; [left; exact Hw| right]. split; [cbn [w_kind]; unfold K_TWINz, K_BLOCK; lia|].
    intros _ a Ha. unfold w_iv in Ha. cbn [w_lo w_len] in Ha. exact (TWFRESH a Ha).
Qed.

Lemma sh_nz : PrimInt63.eqb sh 0%uint63 = false.
Proof.
  pose proof FOK as F0. unfold fresh_ok in F0. apply andb_prop in F0 as [F0 _]. apply andb_prop in F0 as [_ F0]. apply Uint63.ltb_spec in F0.
  apply Uint63.eqb_false_spec. unfold sh. intros E0. rewrite E0 in F0. change (to_Z 0%uint63) with 0 in F0. lia.
Qed.

Lemma NEW_region_ok : region_ok bsegs (s_priv st) E' m sh (twin_region lenf).
Proof.
  destruct twin_facts as (S1 & S2 & S3 & NR & AL & LOA & HIA). unfold AREQMAX in NR. pose proof atop_range as ATR.
  destruct OUTW as (_ & _ & PAT).
  apply (CallA.TwinB.twin_region_ok bsegs (s_priv st) E' m sh lenf sh_nz); rewrite ?den_lenf', ?ev_sh.
  - lia.
  - lia.
  - exact (CallA.TwinB.size_shape_sound E _ lenf (so_facts _ _ _ _ _ _ HS) SHAPE).
  - assert (SA : shad ATOP <= 2 ^ 47).
    { unfold shad, ASHOFF. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8. clear - ATR. Z.div_mod_to_equations. lia. }
    unfold shlen in S2. rewrite Z.shiftr_div_pow2 in S2 by lia. change (2 ^ 3) with 8 in S2. unfold two64. lia.
  - intros g G0 G1. split.
    + pose proof (PAT g G0 G1) as P1. unfold rb. unfold ALib.Mem.wa in P1. rewrite P1. reflexivity.
    + apply (proj2 (aw_user_ok_asan AI ACCT UNIV AI_fake aw LB1 m mo _ (shad Af + g) AWH1 (or_introl eq_refl)
                     ltac:(unfold in_iv; cbn [fst snd]; unfold shlen; rewrite Z.shiftr_div_pow2 by lia; change (2 ^ 3) with 8; clear - G0 G1; Z.div_mod_to_equations; lia))).
Qed.

Hypothesis MINV' : ALib.Mem.mem_inv bsegs m.
Variables (ks : int) (offs : w64) (rss : region) (ksp : int).
Let sp : Z := bv_unsigned (AP.getr (ms_regs ms) 2%bv).
Hypothesis SPR : sp_region st = Some (ks, offs, rss).
Hypothesis SPE : sp = bv_unsigned (ev E ks) + keyZ ksp.
Hypothesis AJ : aregions_justified st wnl = true.
Hypothesis LOSP : loZ rss <= keyZ ksp.
Hypothesis FLOOR : ATOP + 4096 <= bv_unsigned (ev E ks) + loZ rss.
Hypothesis Hc : CtrA.count_op HEAP_ID (s_ops st) = 1%nat.
Hypothesis MINVo : op_minv OPS mo.

Definition RgO : IMap.t region := CtrDelta.TwinB.RgPg (s_regs st) [(sh, twin_region lenf)] [].
Definition NEWSETo (a : Z) : Prop := in_iv (shad Af, shlen (nf + 7)) a.
Definition KEEPo (_ : int) : Prop := True.

Lemma WINKo : forall k0 len kd, KEEPo k0 -> CtrA.win_lookup wnl k0 = Some (len, kd) ->
  forall a, bv_unsigned (ev E k0) <= a < bv_unsigned (ev E k0) + bv_unsigned (den E len) -> in_user LB a.
Proof.
  intros k0 len kd _ WL a Ha. destruct (entry_w k0 len kd (HeapCtrB.TwinB.win_lookup_In _ _ _ _ WL)) as (_ & _ & b0 & Hb0 & SUB & _).
  apply in_ivs_In. exists b0. split; [exact Hb0|]. apply SUB. unfold in_iv. cbn [fst snd]. lia.
Qed.

Lemma NEW_rng : forall a, bv_unsigned (ev E' sh) + loZ (twin_region lenf) <= a < bv_unsigned (ev E' sh) + hiZ E' (twin_region lenf) -> NEWSETo a.
Proof.
  intros a Ha. destruct twin_facts as (_ & _ & _ & NR & _). unfold AREQMAX in NR.
  destruct (CallA.TwinB.twin_region_fields lenf) as (LO & _ & _).
  assert (KZ0 : keyZ 0%uint63 = 0) by reflexivity.
  unfold loZ, hiZ in Ha. rewrite LO, KZ0, CallA.TwinB.twin_region_hi, (CallA.TwinB.twin_len_den E' lenf), den_lenf', ev_sh in Ha by (rewrite den_lenf'; lia).
  unfold NEWSETo, in_iv, shlen. cbn [fst snd]. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8. lia.
Qed.

Theorem twin_out_post : forall (nx' : int),
  s_resv st = RNone ->
  st_ok bsegs OPS E' (SS (s_pc st) (s_rf st) (s_ff st) RNone RgO (link_fact sh kf :: s_facts st) (set_op HEAP_ID h1 (s_ops st)) (s_priv st) nx')
        (MS (ms_regs ms) (ms_fregs ms) (Z_to_bv 64 (to_Z (s_pc st))) (ms_fcsr ms) None m (seg_rom bsegs)) mo.
Proof.
  intros nx' RVN. destruct twin_facts as (S1 & S2 & S3 & NR & AL & LOA & HIA). pose proof atop_range as ATR. unfold AIMG_HI in LOA.
  assert (SAT : shad ATOP + 4096 <= ATOP).
  { unfold shad, ASHOFF. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8. clear - ATR. Z.div_mod_to_equations. lia. }
  assert (RSNOK : region_ok bsegs (s_priv st) E' m ks rss).
  { apply (CtrDelta.TwinB.sp_region_same_ok OPS E st ms mo HS FOK Fv Gv m ks offs rss SPR). intros a0 Ha RA0. split; [reflexivity| exact (fun H => H)]. }
  apply (CtrDelta.TwinB.delta_st_ok AI IMGX IMGX_aci ACCT UNIV OPS AI_fake OPS_fp1 OPS_cov1 OPS_frame_other OPS_fp_other OTHER OPS_mo_other OPS_cov0_img
           E st ms mo HS FOK Fv Gv (ms_regs ms) m mo aw LB LB AWHf MINV'
           ltac:(intros a0 Ha S; split; [reflexivity| exact (fun H => H)]) ltac:(intros; reflexivity) ltac:(intros a0 Ha CC H; exact H)
           ltac:(intros a0 Ha SC IB; split; [reflexivity| exact (fun H => H)])
           ltac:(intros a0 Ha; split; [reflexivity| exact (fun H => H)])
           ks offs rss ksp SPR SPE wnl nn rest AJ WF KEEPo WINKo ltac:(intros; exact I) ltac:(intros; exact I)
           LOSP FLOOR (s_regs st) rss (so_bst _ _ _ _ _ _ HS) (CtrDelta.TwinB.inline_RB_find st ks offs rss SPR) eq_refl (fun _ => eq_refl) eq_refl RSNOK
           hargs md A nw Hf Hc Eh Tnw Nn Ln (OTHER_refl mo) [(sh, twin_region lenf)] []
           ltac:(constructor; [intros []| constructor])
           ltac:(intros k1 r1 [X|[]]; injection X as <- _; exact sh_nz)
           ltac:(intros; exact I) NEWSETo
           ltac:(intros k1 r1 [X|[]]; injection X as <- <-; exact NEW_region_ok)
           ltac:(intros k1 r1 a1 [X|[]]; injection X as <- <-; exact (NEW_rng a1))
           ltac:(intros a1 X; unfold NEWSETo, in_iv in X; cbn [fst snd] in X; split; [unfold AIMG_HI; lia| exact (TWFRESH a1 X)])
           ltac:(intros a1 X; unfold NEWSETo, in_iv in X; cbn [fst snd] in X; lia)
           ltac:(intros a1 X (a' & Ra & EQa); unfold NEWSETo, in_iv in X; cbn [fst snd] in X; subst a1;
                 assert (shad ATOP <= shad a') by (unfold shad, ASHOFF; rewrite !Z.shiftr_div_pow2 by lia; change (2 ^ 3) with 8; clear - Ra; Z.div_mod_to_equations; lia); lia)
           ltac:(intros k1 r1 k2 r2 a1 [X|[]] [Y|[]]; injection X as <- _; injection Y as <- _; intros NE; exfalso; exact (NE eq_refl))
           h1 (w2Z md) (den E A) (wins_of E nn rest ++ [WTo]) (map (den E) (skipn (3 * nn) rest)) DEC1 HOLDN1).
  -
    intros a X. unfold in_ws, heap_ws. apply in_ivs_In. exists (w_iv WTo). split; [| exact X].
    apply in_map. apply filter_In. split; [apply in_or_app; right; left; reflexivity| reflexivity].
  -   intros a Ha NIX NWS. left. intros X. apply NWS. unfold in_ws in *. apply in_ivs_In in X as (v & Hv & Hin). apply in_ivs_In. exists v. split; [| exact Hin].
    apply in_map_iff in Hv as (w & <- & Hw). apply in_map. apply in_or_app. left. exact Hw.
  -   intros a IB X. unfold in_ws, heap_ws in X |- *. apply in_ivs_In in X as (v & Hv & Hin). apply in_map_iff in Hv as (w & <- & Hw). apply filter_In in Hw as [Hw KW].
    apply in_ivs_In. exists (w_iv w). split; [| exact Hin]. apply in_map. apply filter_In. split; [apply in_or_app; left; exact Hw| exact KW].
  - exact (so_x0 _ _ _ _ _ _ HS).
  - intros x. pose proof (so_regs _ _ _ _ _ _ (CtrDelta.TwinB.HS' OPS E st ms mo HS FOK Fv Gv) x) as R0. unfold rget in R0 |- *. cbn [c_regs] in R0 |- *. exact R0.
  - reflexivity.
  -
    constructor; [| exact (so_facts _ _ _ _ _ _ (CtrDelta.TwinB.HS' OPS E st ms mo HS FOK Fv Gv))].
    cbn [fact_holds link_fact]. rewrite HeapCtr.TwinB.den_VPz.
    change (den E' (VAlu ALU_ADD (VAlu ALU_SRL (VP kf wzero) (VL (wlit 3%uint63))) (VL SBw)))
      with (alu64 ALU_ADD (alu64 ALU_SRL (den E' (VP kf wzero)) (wbv (wlit 3%uint63))) (wbv SBw)).
    rewrite HeapCtr.TwinB.den_VPz. apply bv_eq. unfold alu64, alu. rewrite bv_add_unsigned, bv_shiftr_unsigned, bv_and_unsigned, ev_sh.
    destruct (entry_w kf lenf _ INf) as (Kf0 & _).
    destruct (CtrDelta.TwinB.reg_E' OPS E st ms mo HS FOK Fv Gv kf rf Frf) as (EKF & _). rewrite EKF. fold Af.
    replace (bv_unsigned (wbv (wlit 3%uint63))) with 3 by (vm_compute; reflexivity).
    replace (bv_unsigned (Z_to_bv 64 63)) with 63 by (vm_compute; reflexivity).
    change (Z.land 3 63) with 3.
    replace (bv_unsigned (wbv SBw)) with 0x7fff8000 by (vm_compute; reflexivity).
    unfold shad, ASHOFF, bv_wrap, bv_modulus. rewrite Z.mod_small; [lia|]. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8.
    change (2 ^ Z.of_N 64) with (2 ^ 64). clear - LOA HIA ATR NR. Z.div_mod_to_equations. lia.
  - exact MINVo.
Qed.
End ADDED.

Variable MP : Model -> Prop.
Variable PB : (int -> list byte) -> Prop.

Lemma mem_inv_of : forall E st ms mo, st_ok bsegs OPS E st ms mo -> ALib.Mem.mem_inv bsegs (ms_mem ms).
Proof.
  intros E st ms mo HS a b Hm. unfold ALib.Mem.ro_addr. destruct (find_segment bsegs (bv_unsigned a) 1) as [seg|] eqn:Fs; [|reflexivity].
  rewrite (so_minv _ _ _ _ _ _ HS a b Hm seg Fs). reflexivity.
Qed.

Lemma scan_inv : forall E fs R wnl cv kf rf lenf, facts_hold E fs ->
  forallb (tw_other_ok fs R wnl cv kf (KnownT.KnownT.known_eq_t fs (rg_hi rf) lenf)) wnl = true ->
  forall k len kd, In (k, len, kd) wnl -> weqb kd K_TWIN = true ->
  exists kb, block_of_twin fs k = Some kb /\ kb <> kf
    /\ ((exists n2 r2, CtrA.win_lookup wnl kb = Some (n2, CtrLib.K_BLOCK) /\ IMap.find kb R = Some r2 /\ rg_w r2 = true
                       /\ rg_lo r2 = 0%uint63 /\ 0 < hiZ E r2)
        \/ (hiZ E rf = bv_unsigned (den E lenf) /\ twin_arm_evx fs R wnl cv k len kf = true)).
Proof.
  intros E fs R wnl cv kf rf lenf HF SCAN k len kd Hin KT.
  pose proof (proj1 (forallb_forall _ _) SCAN _ Hin) as C. unfold tw_other_ok in C. rewrite KT in C.
  destruct (block_of_twin fs k) as [kb|] eqn:BT; [|discriminate C]. exists kb. split; [reflexivity|].
  destruct (negb (PrimInt63.eqb kb kf)) eqn:NE; [|discriminate C]. apply negb_true_iff in NE. apply Uint63.eqb_false_spec in NE. split; [exact NE|].
  match type of C with (if ?a then true else ?b) = true => destruct a eqn:OLD; [left| right] end.
  - destruct (CtrA.win_lookup wnl kb) as [[n2 kdb]|] eqn:WL2; [|discriminate OLD].
    destruct (weqb kdb CtrLib.K_BLOCK) eqn:KB; [|discriminate OLD]. apply weqb_eq in KB. subst kdb.
    unfold blk_reg_ok in OLD. destruct (IMap.find kb R) as [r2|] eqn:Fr2; [|discriminate OLD].
    destruct (rg_w r2) eqn:W2; [|discriminate OLD]. destruct (PrimInt63.eqb (rg_lo r2) 0%uint63) eqn:L2; [|discriminate OLD].
    apply Uint63.eqb_correct in L2.
    pose proof (KnownA.TwinB.KnownA.known_ltu_sound E _ _ _ HF OLD) as LT. cbn [den] in LT. rewrite wbv_unsigned, wzero_ok in LT.
    exists n2, r2. repeat (split; [reflexivity || assumption|]). exact LT.
  - destruct (KnownT.KnownT.known_eq_t fs (rg_hi rf) lenf) eqn:FULL; [|discriminate C].
    pose proof (KnownA.TwinB.KnownA.known_eq_sound E _ _ _ HF FULL) as EQ. split; [unfold hiZ; rewrite EQ; reflexivity| exact C].
Qed.

Theorem twin_out_sound : forall pc sel, contract_sound bsegs OPS MP PB (twin_out_c pc sel).
Proof.
  intros pc sel st sts Hspc Happ K E ms mo HS HMP HPB HK. cbn [c_apply twin_out_c] in Happ.
  destruct (twin_out_apply_shape sel st sts Happ)
    as [->|(hargs & wnl & kf & lenf & rf & h1 & AW & RVN & FOK & SRG & SFO & WLf & Frf & WRf & LO0 & POSK & SHAPE & SCAN & H1 & ->)].
  {   exact (HK st (or_introl eq_refl) E ms mo (env_ext_refl _ _) HMP HS). }
  destruct (CtrPre.TwinB.aheap_call_facts AI ACCT UNIV Cw OPS AI_fake OPS_holds1 E st ms mo hargs wnl HS AW)
    as (r1 & n & md & A & nw & rest & LB & Hr1 & Hf & Hc & Hn & Eh & T & N & Ln & N255 & SW & NW & AN & JU & HA & WF & HC & W & ARW & TI).
  destruct (CallA.TwinB.stack_sound_g bsegs OPS E st ms mo 0%uint63 HS ltac:(change (to_Z 0%uint63) with 0; lia) SRG)
    as (ks & offs & rss & ksp & HX2 & Hrs & K0 & Hksp & K16 & A16 & Esp & LOX & HI64 & STK & SPR & LOR & LOZ0).
  destruct (CallA.TwinB.sp_floor_sound bsegs OPS E st ms mo hargs n md A nw rest ks offs rss HS SFO Hn Eh SPR LOZ0) as (wlo & len & INw & FLOOR0).
  pose proof (proj1 (Forall_forall _ _) WF _ INw) as (_ & _ & _ & KDs). cbn [w_kind w_lo] in KDs.
  assert (CE : ATOP + 4096 <= bv_unsigned (den E (VP STACK_ID wlo))).
  { destruct KDs as [[_ C]|[[K1 _]|[K1 _]]]; [exact C| unfold K_BLOCK, K_STACK in K1; lia| unfold K_SUB, K_STACK in K1; lia]. }
  change (to_Z 0%uint63) with 0 in LOR.
  assert (SP2 : bv_unsigned (AP.getr (ms_regs ms) 2%bv) = bv_unsigned (ev E ks) + keyZ ksp).
  { rewrite <- HeapCtr.TwinB.reg_of_X2, (GlueA.TwinB.getr_RA bsegs OPS E st ms mo HS X2). exact Esp. }
  pose proof (so_facts _ _ _ _ _ _ HS) as HF.
  assert (POSf : 0 < hiZ E rf).
  { pose proof (KnownA.TwinB.KnownA.known_ltu_sound E _ _ _ HF POSK) as LT. cbn [den] in LT. rewrite wbv_unsigned, wzero_ok in LT. exact LT. }
  pose proof (scan_inv E _ _ _ _ kf rf lenf HF SCAN) as OTH.
  pose proof (CtrFree.TwinB.cvu_of Cw Cw_vec_unowned E st (ms_mem ms) LB n md A nw rest ltac:(rewrite <- Eh; exact Hf) N HC) as CVU.
  assert (KB : exists b, vis W b /\ is_heap b /\ ab_addr b = bv_unsigned (ev E kf) /\ ab_size b = bv_unsigned (den E lenf)).
  { eapply kblock_heap; try eassumption. exact (HeapCtrB.TwinB.win_lookup_In _ _ _ _ WLf). }
  destruct KB as (b & Vb & HHb & EAb & ENb).
  set (Fv := fun _ : Z => Z_to_bv 64 (shad (bv_unsigned (ev E kf)))). set (Gv := fun (_ _ : Z) => Z_to_bv 8 0).
  assert (HSF : st_ok bsegs OPS (CtrDelta.TwinB.E' E st Fv Gv)
            (SS (s_pc st) (s_rf st) (s_ff st) RNone (RgO st lenf) (link_fact (s_next st) kf :: s_facts st) (set_op HEAP_ID h1 (s_ops st)) (s_priv st)
                (PrimInt63.add (s_next st) 1%uint63))
            (MS (ms_regs ms) (ms_fregs ms) (Z_to_bv 64 (to_Z (s_pc st))) (ms_fcsr ms) None (ms_mem ms) (seg_rom bsegs)) mo).
  { eapply (twin_out_post E st ms mo HS wnl n rest LB (den E A) NW) with (b := b) (WW := W) (rf := rf) (ks := ks) (offs := offs) (rss := rss) (ksp := ksp)
           (hargs := hargs) (md := md) (A := A) (nw := nw); try eassumption; try reflexivity; try lia.
    all: try exact (mem_inv_of E st ms mo HS). all: try exact (so_mf _ _ _ _ _ _ HS). }
  apply (HK _ (or_introl eq_refl) (CtrDelta.TwinB.E' E st Fv Gv) ms mo (CtrDelta.TwinB.EXT E st Fv Gv) HMP).
  rewrite (GlueA.TwinB.ms_formA bsegs OPS E st ms mo HS RVN) at 1.
  unfold addfact, set_ops, setregs, set_next. cbn [s_pc s_rf s_ff s_resv s_regs s_facts s_ops s_priv s_next]. rewrite RVN. exact HSF.
Qed.
End TwinOut.
End TwinB.
