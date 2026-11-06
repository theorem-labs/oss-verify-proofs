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
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Bridge Require CallA CtrPre GlueA FrameV CtrDelta CtrFree.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Unp Require GLib.
Unset Nia Cache. Unset Nra Cache.
Import ValP MemP CtrFX.
Import ActrA.
Module AP := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.PropExec.

Lemma twin_in_apply_shape : forall sel st sts, twin_in_apply sel st = Some sts ->
  sts = [st] \/
  exists hargs wnl kf sh h1,
    aheap_windows st = Some (hargs, wnl) /\ s_resv st = RNone /\ fresh_ok st = true
    /\ stack_room_g st 0%uint63 = true /\ sp_floor_ok st hargs = true
    /\ find_twin (s_facts st) kf = Some sh
    /\ afree_ok st wnl kf sh = true /\ twin_canon st wnl kf sh = true /\ no_views_on (s_facts st) (s_regs st) kf sh = true
    /\ heap_del_window_k hargs (VP sh wzero) K_TWIN = Some h1
    /\ sts = [set_facts (set_ops (setregs st (IMap.remove sh (s_regs st))) (set_op HEAP_ID h1 (s_ops st))) (drop_anchor_facts sh (s_facts st))].
Proof.
  intros sel st sts H. unfold twin_in_apply in H.
  destruct (aheap_windows st) as [[hargs wnl]|] eqn:AW; [|discriminate H].
  destruct (twsel_pair sel st wnl) as [[kf sh]|] eqn:SEL; [| left; injection H as <-; reflexivity].
  right.
  assert (OUT : forall wl0 k p, tw_out (s_facts st) wl0 k = Some p -> find_twin (s_facts st) (fst p) = Some (snd p)).
  { intros wl0 k p X. unfold tw_out in X. destruct (find_twin (s_facts st) k) as [sh0|] eqn:F0; [|discriminate X]. destruct (CtrA.win_lookup wl0 sh0); [|discriminate X].
    injection X as <-. exact F0. }
  assert (GO : forall wl0 n l p, twlen_go (s_facts st) wl0 n l = Some p -> find_twin (s_facts st) (fst p) = Some (snd p)).
  { intros wl0 n l p. induction l as [|[[k len] kd] l IH]; intros X; [discriminate X|]. cbn [twlen_go] in X.
    destruct len as [lw| | | | | | | | | |]; try (exact (IH X)).
    destruct (weqb kd CtrLib.K_BLOCK && weqb lw n); [| exact (IH X)].
    destruct (tw_out (s_facts st) wl0 k) as [p0|] eqn:O0; [| exact (IH X)]. injection X as <-. exact (OUT wl0 k p0 O0). }
  assert (FT : find_twin (s_facts st) kf = Some sh).
  { unfold twsel_pair in SEL. destruct sel as [rs off|n]; [| exact (GO wnl n wnl (kf, sh) SEL)].
    destruct (getr st rs) as [|k o| | | | | | | | |]; try discriminate SEL. destruct (weqb o off); [|discriminate SEL]. exact (OUT wnl k (kf, sh) SEL). }
  match type of H with (if ?c then _ else _) = _ => destruct c eqn:CK; [|discriminate H] end.
  repeat match type of CK with (_ && _)%bool = true => let X := fresh "Q" in apply andb_prop in CK as [CK X] end.
  destruct (heap_del_window_k hargs (VP sh wzero) K_TWIN) as [h1|] eqn:H1; [|discriminate H]. injection H as <-.
  destruct (s_resv st) eqn:RV; try discriminate CK.
  exists hargs, wnl, kf, sh, h1. repeat (split; [reflexivity || assumption|]). reflexivity.
Qed.

Section TwinIn.
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

Hypothesis Cw_ghost_free : forall md ca LB ws m b n ws', cw_holds Cw md ca LB ws m -> In (Win b n K_TWINz) ws ->
  (forall w, In w ws' <-> In w ws /\ w <> Win b n K_TWINz) -> cw_holds Cw md ca (remove iv_eq_dec (b, n) LB) ws' m.

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

Section RELEASED.
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
Variables (kf sh : int).
Hypothesis NV : no_views_on (s_facts st) (s_regs st) kf sh = true.
Hypothesis TCAN : twin_canon st wnl kf sh = true.
Variables (rf : region) (lenf lent : sv).
Hypothesis Frf : IMap.find kf (s_regs st) = Some rf.
Hypothesis WLf : CtrA.win_lookup wnl kf = Some (lenf, CtrLib.K_BLOCK).
Hypothesis WLt : CtrA.win_lookup wnl sh = Some (lent, K_TWIN).
Hypothesis BTs : block_of_twin (s_facts st) sh = Some kf.
Hypothesis LO0 : rg_lo rf = 0%uint63.
Hypothesis POSf : 0 < hiZ E rf.
Hypothesis LEf : hiZ E rf <= bv_unsigned (den E lenf).
Hypothesis OTHERS : forall k len kd, In (k, len, kd) wnl -> k <> kf -> k <> sh ->
  (weqb kd K_TWIN = true /\ exists kb, block_of_twin (s_facts st) k = Some kb /\ kb <> kf)
  \/ (weqb kd K_TWIN = false /\ exists r0, IMap.find k (s_regs st) = Some r0 /\ rg_lo r0 = 0%uint63 /\ hiZ E r0 <= bv_unsigned (den E len)
        /\ 0 < hiZ E r0 /\ rg_w r0 = true /\ (kd = CtrLib.K_BLOCK \/ hiZ E rf = bv_unsigned (den E lenf))).

Let Af : Z := bv_unsigned (ev E kf).
Let nf : Z := bv_unsigned (den E lenf).
Let m : amem := ms_mem ms.
Let WOF : wit_of WW (w_L WW) (w_RNG WW) (w_st WW) (w_LBa WW) := wit_of_refl WW.

Lemma AWHf : aw_holds_asan AI ACCT UNIV aw LB m mo.
Proof. exact (aw_real_holds AI ACCT UNIV _ _ _ _ _ AR). Qed.
Lemma HWf : aw_holds_w AI ACCT UNIV WW aw LB m mo.
Proof. exact (proj1 AR). Qed.

Lemma twin_data : exists rs p,
  IMap.find sh (s_regs st) = Some rs /\ bv_unsigned (ev E sh) = shad Af /\ bv_unsigned (den E lent) = shlen (nf + 7)
  /\ In (Af, nf) LB /\ In (shad Af, shlen (nf + 7)) LB /\ In (HB p Af nf) (w_T WW) /\ user_band Af /\ 1 <= nf
  /\ ablock_shadow m Af nf.
Proof.
  destruct (CtrFree.twin_sh AI IMGX IMGX_aci ACCT UNIV OPS AI_fake E st ms mo HS wnl nn rest LB aw NW WF WW AR kf sh None (CtrFree.twin_consume_canon _ _ _ _ TCAN) rf lenf lent WLf WLt BTs POSf LEf)
    as (rs & Frs & _ & _ & ESH & ELT).
  destruct (CtrFree.owner AI IMGX IMGX_aci ACCT UNIV OPS AI_fake E st ms mo HS wnl nn rest LB aw _ _ _ _ NW WF WW WOF AR TI kf sh None (CtrFree.twin_consume_canon _ _ _ _ TCAN) rf lenf lent WLf WLt BTs POSf LEf)
    as (UBf & HTf & (p & _ & HPT) & NRf & _).
  exists rs, p. split; [exact Frs|]. split; [exact ESH|]. split; [exact ELT|].
  split. { destruct (CtrFree.entry_window E wnl nn rest LB NW WF kf lenf kf lenf CtrLib.K_BLOCK (HeapCtrB.win_lookup_In _ _ _ _ WLf)) as (_ & _ & b & Hb & _ & EQ). rewrite (EQ eq_refl) in Hb. exact Hb. }
  split; [exact HTf|]. split; [exact HPT|]. split; [exact UBf|]. split; [lia|].
  exact (CtrFree.freed_pattern AI IMGX IMGX_aci ACCT UNIV OPS AI_fake E st ms mo HS wnl nn rest LB aw _ _ _ _ NW WF WW WOF AR TI kf sh None (CtrFree.twin_consume_canon _ _ _ _ TCAN) rf lenf lent WLf WLt BTs POSf LEf OTHERS).
Qed.

Variables (rs : region) (p : aptr).
Hypothesis Frs : IMap.find sh (s_regs st) = Some rs.
Hypothesis ESH : bv_unsigned (ev E sh) = shad Af.
Hypothesis ELT : bv_unsigned (den E lent) = shlen (nf + 7).
Hypothesis INB : In (Af, nf) LB.
Hypothesis INT : In (shad Af, shlen (nf + 7)) LB.
Hypothesis HPT : In (HB p Af nf) (w_T WW).
Hypothesis UBf : user_band Af.
Hypothesis NF1 : 1 <= nf.
Hypothesis PAT : ablock_shadow m Af nf.

Let bT : ablock := HB p Af nf.
Definition LBk : blocks := remove iv_eq_dec (twin_iv bT) LB.
Definition Wf : wit := wit_twin_in WW m bT.
Definition WTf : window := Win (shad Af) (shlen (nf + 7)) K_TWINz.

Lemma LBk_In : forall v, In v LBk <-> (In v LB /\ v <> (shad Af, shlen (nf + 7))).
Proof.
  intros v. unfold LBk, bT, twin_iv. cbn [ab_addr ab_size]. split.
  - intros H. apply in_remove in H. exact H.
  - intros [H N]. apply in_in_remove; assumption.
Qed.
Lemma LBk_sub : forall v, In v LBk -> In v LB.
Proof. intros v H. exact (proj1 (proj1 (LBk_In v) H)). Qed.

Lemma HW1 : aw_holds_w AI ACCT UNIV Wf aw LBk m mo.
Proof. exact (twin_in_w AI ACCT UNIV AI_fake WW aw LB m mo bT HWf HPT PAT). Qed.

Definition KEEPf (k0 : int) : Prop := k0 <> sh.
Lemma twin_not_user : (Af, nf) <> (shad Af, shlen (nf + 7)).
Proof.
  intros X. injection X as X1 _. destruct (LB_twin_facts AI ACCT UNIV WW aw LB m mo bT HWf HPT) as (T1 & T2 & T3). unfold bT in T1, T2, T3. cbn [ab_addr ab_size] in T1, T2, T3.
  unfold user_band in UBf. lia.
Qed.
Lemma kept_entry : forall k len kd b, In (k, len, kd) wnl -> k <> sh ->
  In b LB -> (forall a, in_iv (bv_unsigned (ev E k), bv_unsigned (den E len)) a -> in_iv b a) -> b <> (shad Af, shlen (nf + 7)).
Proof.
  intros k len kd b Hin NKs Hb SUB. destruct (Uint63.eqb k kf) eqn:Q.
  - apply Uint63.eqb_correct in Q. subst k.
    destruct (HeapCtrB.windows_anchored_nodup _ _ kf len kd lenf CtrLib.K_BLOCK AN Hin (HeapCtrB.win_lookup_In _ _ _ _ WLf)) as [-> ->].

    intros ->. fold Af nf in SUB. specialize (SUB Af ltac:(unfold in_iv; cbn [fst snd]; lia)).
    destruct (LB_twin_facts AI ACCT UNIV WW aw LB m mo bT HWf HPT) as (T1 & T2 & T3). unfold bT in T1, T2, T3. cbn [ab_addr ab_size] in T1, T2, T3.
    unfold in_iv in SUB. cbn [fst snd] in SUB. unfold user_band in UBf. lia.
  - apply Uint63.eqb_false_spec in Q.
    exact (proj2 (CtrFree.kept_block AI IMGX IMGX_aci ACCT UNIV OPS AI_fake E st ms mo HS wnl nn rest LB aw _ _ _ _ NW WF WW WOF AR TI CVU kf sh None (CtrFree.twin_consume_canon _ _ _ _ TCAN) rf lenf lent Frf WLf WLt BTs LO0 POSf LEf OTHERS
                    k len kd b Hin Q NKs Hb SUB)).
Qed.

Lemma WINKf : forall k0 len kd, KEEPf k0 -> CtrA.win_lookup wnl k0 = Some (len, kd) ->
  forall a, bv_unsigned (ev E k0) <= a < bv_unsigned (ev E k0) + bv_unsigned (den E len) -> in_user LBk a.
Proof.
  intros k0 len kd NKs WL a Ha. pose proof (HeapCtrB.win_lookup_In _ _ _ _ WL) as Hin.
  destruct (CtrFree.entry_window E wnl nn rest LB NW WF kf lenf k0 len kd Hin) as (_ & _ & b & Hb & SUB & _).
  apply in_ivs_In. exists b. split; [apply LBk_In; split; [exact Hb| exact (kept_entry k0 len kd b Hin NKs Hb SUB)]|]. apply SUB. unfold in_iv. cbn [fst snd]. lia.
Qed.
Lemma VKEEPf : forall k0 rg hs n sh' len, IMap.find k0 (s_regs st) = Some rg -> zero_view rg = Some hs -> KEEPf k0 ->
  block_of_twin (s_facts st) k0 = Some n -> CallV.view_parent (s_facts st) (s_regs st) n sh' ->
  CtrA.win_lookup wnl sh' = Some (len, K_TWIN) -> KEEPf sh'.
Proof.
  intros k0 rg hs n sh' len Fk ZV NKs BT VPAR WL. intros ->. unfold no_views_on in NV.
  pose proof (proj1 (IMap.forallb_spec _ _ (so_bst _ _ _ _ _ _ HS)) NV k0 rg Fk) as C. cbv beta in C.
  replace (PrimInt63.eqb k0 sh) with false in C by (symmetry; apply Uint63.eqb_false_spec; exact NKs).
  rewrite ZV, BT in C. destruct VPAR as [(kb & o1 & UB & TW)|(rshp & Frshp & HNp)];
      [rewrite UB, TW, Uint63.eqb_refl in C; cbn in C; discriminate C| rewrite Frshp, HNp in C; cbn [negb] in C; rewrite !Bool.andb_false_r in C; discriminate C].
Qed.

Lemma TKEEPf : forall k0 rg sh' kb n len, IMap.find k0 (s_regs st) = Some rg -> KEEPf k0 -> CtrA.win_lookup wnl sh' = Some (len, K_TWIN) ->
  block_of_twin (s_facts st) sh' = Some kb -> CtrA.win_lookup wnl kb = Some (n, CtrLib.K_BLOCK) ->
  size_tail_ok (s_facts st) n = true -> tail_named (tail_rhs sh' n) k0 (s_facts st) = true -> KEEPf sh'.
Proof.
  intros k0 rg sh' kb n len Fk NKs WL BT WLk ST TN. intros ->. rewrite BTs in BT. injection BT as <-. rewrite WLf in WLk. injection WLk as <-.
  destruct (CallA.twin_canon_inv st wnl kf sh TCAN) as (rs0 & n0 & kdn & lent0 & kdt & _ & WLn & _ & _ & _ & _ & _ & NTA). rewrite WLf in WLn. injection WLn as <- <-.
  exact (CallA.no_tail_at_sound _ _ _ _ k0 rg (so_bst _ _ _ _ _ _ HS) NTA Fk TN).
Qed.
Lemma KEEP_delf : forall k0, ~ In k0 [sh] -> KEEPf k0.
Proof. intros k0 H ->. apply H. left. reflexivity. Qed.

Variables (hargs : list sv) (md : w64) (A : sv) (nw : w64).
Hypothesis Hf : find_op HEAP_ID (s_ops st) = Some hargs.
Hypothesis Eh : hargs = VL md :: A :: VL nw :: rest.
Hypothesis Tnw : wt nw = false.
Hypothesis Nn : nn = Z.to_nat (to_Z (wl nw)).
Hypothesis Ln : (3 * nn <= length rest)%nat.
Hypothesis FOK : fresh_ok st = true.
Variables (Fv : Z -> word) (Gv : Z -> Z -> byte).
Notation E' := (CtrDelta.E' E st Fv Gv).
Variable h1 : list sv.
Hypothesis H1 : heap_del_window_k hargs (VP sh wzero) K_TWIN = Some h1.

Lemma DEL1 : exists m1 m2,
  decode (map (den E') h1) = Some (w2Z md, den E A, m1 ++ m2, map (den E) (skipn (3 * nn) rest))
  /\ wins_of E nn rest = m1 ++ WTf :: m2 /\ ~ In WTf (m1 ++ m2).
Proof.
  pose proof (HeapCtrB.windows_anchored_nodup_anchors _ _ AN) as NDA.
  rewrite Eh in H1.
  destruct (CtrFree.heap_del_window_k_facts E md A nw rest nn sh K_TWIN h1 wnl eq_refl Tnw Nn Ln NW H1)
    as (ws1 & m1 & len1 & m2 & wl1 & EH1 & I1 & W1 & W1' & T1 & N1 & L1 & SK1 & NW1 & S1 & S2 & S3 & M1 & PM1).
  destruct (HeapCtrB.windows_anchored_nodup _ _ sh len1 K_TWIN lent K_TWIN AN I1 (HeapCtrB.win_lookup_In _ _ _ _ WLt)) as [-> _].
  assert (ND1 : List.NoDup (sh :: HeapCtrB.anchors wl1)) by (exact (Permutation_NoDup (CtrFree.anchors_perm _ _ PM1) NDA)).
  apply List.NoDup_cons_iff in ND1 as [NSH1 _].
  exists m1, m2. split; [| split].
  - rewrite EH1. rewrite (decode_hargs E' md A _ _ (pred nn) T1 N1 L1).
    assert (RB : forallb (sv_vars_below (s_next st)) rest = true) by exact (CtrDelta.rest_below st FOK rest hargs md A nw Hf Eh).
    assert (RB1 : forallb (sv_vars_below (s_next st)) (ws1 ++ skipn (3 * nn) rest) = true) by (apply (CtrFree.forallb_sub _ rest); [exact S3| exact RB]).
    rewrite (CtrDelta.den_E' E st Fv Gv A (CtrDelta.A_below st FOK rest hargs md A nw Hf Eh)).
    rewrite (CtrDelta.wins_of_E' E st Fv Gv _ _ RB1), W1', SK1.
    rewrite (CtrDelta.map_den_E' E st Fv Gv _ (CtrFree.forallb_skipn _ (3 * nn) rest RB)). reflexivity.
  - rewrite W1. unfold WTf. rewrite ESH, ELT. reflexivity.
  - intros X. rewrite <- W1' in X.
    destruct (HeapCtrB.wins_cover E (pred nn) _ wl1 WTf NW1 X) as [KS|(k & len & kd & Ik & EW)]; [cbn in KS; unfold K_TWINz, K_STACK in KS; lia|].
    unfold WTf in EW. injection EW as E1 E2 E3.
    assert (NKs : k <> sh).
    { intros ->. apply NSH1. unfold HeapCtrB.anchors. apply in_map_iff. exists (sh, len, kd). split; [reflexivity| exact Ik]. }
    exact (kept_entry k len kd (shad Af, shlen (nf + 7)) (S1 _ Ik) NKs INT ltac:(rewrite <- E1, <- E2; intros a Ha; exact Ha) eq_refl).
Qed.

Hypothesis AWden : aw = den E A.
Hypothesis HC : cw_holds Cw (w2Z md) (map (den E) (skipn (3 * nn) rest)) LB (wins_of E nn rest) m.

Lemma HOLDN1 : forall m1 m2,
  decode (map (den E') h1) = Some (w2Z md, den E A, m1 ++ m2, map (den E) (skipn (3 * nn) rest)) ->
  wins_of E nn rest = m1 ++ WTf :: m2 -> ~ In WTf (m1 ++ m2) ->
  op_holds OPS HEAP_ID (map (den E') h1) m mo.
Proof.
  intros m1 m2 D W1 NT. rewrite OPS_holds1.
  assert (IN1 : forall w, In w (m1 ++ m2) <-> In w (wins_of E nn rest) /\ w <> WTf).
  { intros w. rewrite W1. split.
    - intros H. split; [apply in_app_or in H as [H|H]; apply in_or_app; [left; exact H| right; right; exact H]| intros ->; exact (NT H)].
    - intros [H NE]. apply in_app_or in H as [H|[H|H]]; apply in_or_app; [left; exact H| congruence| right; exact H]. }
  exists (w2Z md), aw, (m1 ++ m2), (map (den E) (skipn (3 * nn) rest)), LBk, Wf.
  split; [rewrite AWden; exact D|]. split; [exact HW1|]. split; [| split].
  - apply Forall_forall. intros w Hw. apply IN1 in Hw as [Hw NWT].
    pose proof (proj1 (Forall_forall _ _) WF w Hw) as (X1 & X2 & X3 & KD). split; [exact X1|]. split; [exact X2|]. split; [exact X3|].
    destruct (HeapCtrB.wins_cover E nn rest wnl w NW Hw) as [KS|(k & len & kd & Ik & EW)].
    { left. destruct KD as [[_ C]|[[K _]|[K _]]]; [split; [exact KS| exact C]| rewrite KS in K; unfold K_BLOCK, K_STACK in K; lia| rewrite KS in K; unfold K_SUB, K_STACK in K; lia]. }
    assert (NKs : k <> sh).
    { intros ->. destruct (HeapCtrB.windows_anchored_nodup _ _ sh len kd lent K_TWIN AN Ik (HeapCtrB.win_lookup_In _ _ _ _ WLt)) as [-> ->].
      apply NWT. rewrite EW. unfold WTf. rewrite ESH, ELT. reflexivity. }
    destruct KD as [[K C]|[[K B]|[K (b & Hb & SUB)]]].
    + left. auto.
    + right; left. split; [exact K|]. apply LBk_In. split; [exact B|].
      apply (kept_entry k len kd (w_iv w) Ik NKs B). rewrite EW. unfold w_iv. cbn [w_lo w_len]. intros a0 Ha. exact Ha.
    + right; right. split; [exact K|]. exists b. split; [| exact SUB]. apply LBk_In. split; [exact Hb|].
      apply (kept_entry k len kd b Ik NKs Hb). rewrite EW in SUB. unfold w_iv in SUB. cbn [w_lo w_len] in SUB. exact SUB.
  - assert (INW : In WTf (wins_of E nn rest)) by (rewrite W1; apply in_or_app; right; left; reflexivity).
    exact (Cw_ghost_free _ _ _ _ m (shad Af) (shlen (nf + 7)) (m1 ++ m2) HC INW IN1).
  - exact (ties_twin_in AI ACCT UNIV AI_fake WW aw LB m mo (wins_of E nn rest) (m1 ++ m2) bT m HWf TI HPT IN1).
Qed.

Lemma released_off_image : forall a, in_iv (shad Af, shlen (nf + 7)) a -> find_segment asegs a 1 = None.
Proof. intros a Ha. exact (proj2 (aw_user_ok_asan AI ACCT UNIV AI_fake aw LB m mo _ a AWHf INT Ha)). Qed.

Variable R' : bvmap 5 word.
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

Definition RgF : IMap.t region := CtrDelta.RgPg (s_regs st) [] [sh].
Definition NEWSETf (_ : Z) : Prop := False.

Lemma released_unbased : forall a, in_iv (shad Af, shlen (nf + 7)) a -> ~ in_based E' RgF a.
Proof.
  intros a Ha (k0 & rg & Fk & KZ & RA).
  assert (SPF : ATOP + 4096 <= sp) by (rewrite SPE; lia).
  destruct (LB_twin_facts AI ACCT UNIV WW aw LB m mo bT HWf HPT) as (T1 & T2 & T3). unfold bT in T1, T2, T3. cbn [ab_addr ab_size] in T1, T2, T3.
  pose proof atop_range as ATR. unfold in_iv in Ha. cbn [fst snd] in Ha.
  destruct (CtrDelta.RgPg_range OPS E st ms mo HS FOK Fv Gv LB LBk ks offs rss ksp SPR SPE wnl nn rest AJ WF KEEPf WINKf VKEEPf TKEEPf LOSP FLOOR
              (s_regs st) rss (so_bst _ _ _ _ _ _ HS) (CtrDelta.inline_RB_find st ks offs rss SPR) eq_refl (fun _ => eq_refl)
              hargs md A nw Hf Hc Eh Tnw Nn Ln [] [sh]
              (NoDup_nil _) KEEP_delf NEWSETf ltac:(intros k1 r1 a1 X; destruct X) k0 rg a Fk KZ RA) as [[X _]|[_ [[_ X]|[_ [X|[X|X]]]]]].
  - destruct X.
  - lia.
  - fold sp in X. lia.
  -
    apply in_ivs_In in X as (v & Hv & Hin). apply LBk_In in Hv as [Hv NE]. destruct v as [A' n'].
    apply (aw_blocks_disj_asan AI ACCT UNIV AI_fake aw LB m mo (A', n') (shad Af, shlen (nf + 7)) a AWHf Hv INT); [| exact Hin| unfold in_iv; cbn [fst snd]; exact Ha].
    cbn [fst]. intros ->. apply NE. f_equal. exact (LB_same_addr AI ACCT UNIV AI_fake WW aw LB m mo (shad Af) n' (shlen (nf + 7)) HWf Hv INT).
  -
    assert (HbL : In bT (w_LBa WW)) by (pose proof HWf as (_ & HT & _); exact (proj1 (HT bT HPT))).
    pose proof HWf as (AH & _).
    destruct (heap_block_facts AI _ _ _ _ _ bT AH HbL ltac:(exists p; reflexivity)) as (NP & (BK & _ & HI & _) & _). cbn [ab_addr ab_size bT] in NP, BK, HI.
    destruct (shadow_tight Af nf BK HI ltac:(lia)) as [S1 S2].
    destruct (sh_cov_band a X) as [C|C]; lia.
Qed.

Theorem twin_in_post : forall (nx' : int),
  s_resv st = RNone ->
  st_ok asegs OPS E' (SS (s_pc st) (s_rf st) (s_ff st) RNone RgF (drop_anchor_facts sh (s_facts st)) (set_op HEAP_ID h1 (s_ops st)) (s_priv st) nx')
        (MS (ms_regs ms) (ms_fregs ms) (Z_to_bv 64 (to_Z (s_pc st))) (ms_fcsr ms) None m (seg_rom asegs)) mo.
Proof.
  intros nx' RVN. destruct DEL1 as (m1 & m2 & D & W1 & NT).
  pose proof (HOLDN1 m1 m2 D W1 NT) as HOLDN.
  assert (INWS : forall a, in_ws (wins_of E nn rest) a -> in_ws (m1 ++ m2) a \/ in_iv (shad Af, shlen (nf + 7)) a).
  { intros a X. unfold in_ws in X. apply in_ivs_In in X as (v & Hv & Hin). apply in_map_iff in Hv as (w & <- & Hw).
    rewrite W1 in Hw. apply in_app_or in Hw as [Hw|[<-|Hw]]; [| right; exact Hin|];
      left; unfold in_ws; apply in_ivs_In; exists (w_iv w); (split; [apply in_map; apply in_or_app; auto| exact Hin]). }
  assert (RSNOK : region_ok asegs (s_priv st) E' m ks rss).
  { apply (CtrDelta.sp_region_same_ok OPS E st ms mo HS FOK Fv Gv m ks offs rss SPR). intros a0 Ha RA0. split; [reflexivity| exact (fun H => H)]. }
  apply (CtrDelta.delta_st_ok AI IMGX IMGX_aci ACCT UNIV OPS AI_fake OPS_fp1 OPS_cov1 OPS_frame_other OPS_fp_other OTHER OPS_mo_other OPS_cov0_img
           E st ms mo HS FOK Fv Gv (ms_regs ms) m mo aw LB LBk AWHf MINV'
           ltac:(intros a0 Ha S; split; [reflexivity| exact (fun H => H)]) ltac:(intros; reflexivity) ltac:(intros a0 Ha CC H; exact H)
           ltac:(intros a0 Ha SC IB; split; [reflexivity| exact (fun H => H)])
           ltac:(intros a0 Ha; split; [reflexivity| exact (fun H => H)])
           ks offs rss ksp SPR SPE wnl nn rest AJ WF KEEPf WINKf VKEEPf TKEEPf
           LOSP FLOOR (s_regs st) rss (so_bst _ _ _ _ _ _ HS) (CtrDelta.inline_RB_find st ks offs rss SPR) eq_refl (fun _ => eq_refl) eq_refl RSNOK
           hargs md A nw Hf Hc Eh Tnw Nn Ln (OTHER_refl mo) [] [sh] (NoDup_nil _)
           ltac:(intros k1 r1 X; destruct X) KEEP_delf NEWSETf ltac:(intros k1 r1 X; destruct X) ltac:(intros k1 r1 a1 X; destruct X)
           ltac:(intros a1 X; destruct X) ltac:(intros a1 X; destruct X) ltac:(intros a1 X; destruct X) ltac:(intros k1 r1 k2 r2 a1 X; destruct X)
           h1 (w2Z md) (den E A) (m1 ++ m2) (map (den E) (skipn (3 * nn) rest)) D HOLDN).
  - intros a X. destruct X.
  -   intros a Ha NIX NWS. destruct (GLib.UG.in_ws_dec (wins_of E nn rest) a) as [IW|NIW]; [| left; exact NIW].
    right. destruct (INWS a IW) as [X|FR]; [contradiction|]. split; [exact (released_off_image a FR)| exact (released_unbased a FR)].
  -   intros a IB X. pose proof (CtrDelta.in_heap_ws _ _ X) as IW. destruct (INWS a IW) as [Y|FR]; [| exfalso; exact (released_unbased a FR IB)].
    unfold in_ws, heap_ws in X |- *. apply in_ivs_In in X as (v & Hv & Hin). apply in_map_iff in Hv as (w & <- & Hw). apply filter_In in Hw as [Hw KW].
    apply in_ivs_In. exists (w_iv w). split; [| exact Hin]. apply in_map. apply filter_In. split; [| exact KW].
    rewrite W1 in Hw. apply in_app_or in Hw as [Hw|[<-|Hw]]; [apply in_or_app; auto| | apply in_or_app; auto].
    exfalso. exact (released_unbased a Hin IB).
  - exact (so_x0 _ _ _ _ _ _ HS).
  - intros x. pose proof (so_regs _ _ _ _ _ _ (CtrDelta.HS' OPS E st ms mo HS FOK Fv Gv) x) as R0. unfold rget in R0 |- *. cbn [c_regs] in R0 |- *. exact R0.
  - reflexivity.
  -
    pose proof (so_facts _ _ _ _ _ _ (CtrDelta.HS' OPS E st ms mo HS FOK Fv Gv)) as HF0. unfold facts_hold, drop_anchor_facts in *.
    apply Forall_forall. intros f Hf0. apply filter_In in Hf0 as [Hf0 _]. exact (proj1 (Forall_forall _ _) HF0 f Hf0).
  - exact MINVo.
Qed.
End RELEASED.

Variable MP : Model -> Prop.
Variable PB : (int -> list byte) -> Prop.

Lemma mem_inv_of : forall E st ms mo, st_ok asegs OPS E st ms mo -> ALib.Mem.mem_inv asegs (ms_mem ms).
Proof.
  intros E st ms mo HS a b Hm. unfold ALib.Mem.ro_addr. destruct (find_segment asegs (bv_unsigned a) 1) as [seg|] eqn:Fs; [|reflexivity].
  rewrite (so_minv _ _ _ _ _ _ HS a b Hm seg Fs). reflexivity.
Qed.

Theorem twin_in_sound : forall pc sel, contract_sound asegs OPS MP PB (twin_in_c pc sel).
Proof.
  intros pc sel st sts Hspc Happ K E ms mo HS HMP HPB HK. cbn [c_apply twin_in_c] in Happ.
  destruct (twin_in_apply_shape sel st sts Happ) as [->|(hargs & wnl & kf & sh & h1 & AW & RVN & FOK & SRG & SFO & FT & FOKk & TCAN & NV & H1 & ->)].
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
  destruct (CtrFree.afree_ok_k_inv OPS CtrLib.K_BLOCK K_TWIN E st ms mo wnl kf sh HS FOKk)
    as (rf & lenf & lent & Frf & WLf & WLt & BTs & LO0 & POSf & LEf & OTHERS).
  destruct (twin_data E st ms mo HS wnl n rest LB (den E A) NW WF W ARW TI kf sh TCAN rf lenf lent WLf WLt BTs POSf LEf OTHERS)
    as (rs & p & Frs & ESH & ELT & INB & INT & HPT & UBf & NF1 & PAT).
  set (Fv := fun _ : Z => Z_to_bv 64 0). set (Gv := fun (_ _ : Z) => Z_to_bv 8 0).
  pose proof (twin_in_post E st ms mo HS wnl n rest LB (den E A) NW AN WF W ARW TI
                (CtrFree.cvu_of Cw Cw_vec_unowned E st (ms_mem ms) LB n md A nw rest ltac:(rewrite <- Eh; exact Hf) N HC) kf sh NV TCAN rf lenf lent Frf WLf WLt BTs LO0 POSf LEf OTHERS
                p ESH ELT INT HPT UBf NF1 PAT hargs md A nw Hf Eh T N Ln FOK Fv Gv h1 H1 eq_refl HC
                (mem_inv_of E st ms mo HS) ks offs rss ksp SPR SP2 JU ltac:(lia) ltac:(lia) Hc (so_mf _ _ _ _ _ _ HS) (s_next st) RVN) as HSF.
  apply (HK _ (or_introl eq_refl) (CtrDelta.E' E st Fv Gv) ms mo (CtrDelta.EXT E st Fv Gv) HMP).
  rewrite (GlueA.ms_formA asegs OPS E st ms mo HS RVN) at 1.
  unfold set_facts, set_ops, setregs. cbn [s_pc s_rf s_ff s_resv s_regs s_facts s_ops s_priv s_next]. rewrite RVN. exact HSF.
Qed.
End TwinIn.

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

Unset Nia Cache. Unset Nra Cache.
Import ValP MemP CtrFX.
Import ActrA.
Module AP := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.PropExec.

Lemma twin_in_apply_shape : forall sel st sts, twin_in_apply sel st = Some sts ->
  sts = [st] \/
  exists hargs wnl kf sh h1,
    aheap_windows st = Some (hargs, wnl) /\ s_resv st = RNone /\ fresh_ok st = true
    /\ stack_room_g st 0%uint63 = true /\ sp_floor_ok st hargs = true
    /\ find_twin (s_facts st) kf = Some sh
    /\ afree_ok st wnl kf sh = true /\ twin_canon st wnl kf sh = true /\ no_views_on (s_facts st) (s_regs st) kf sh = true
    /\ heap_del_window_k hargs (VP sh wzero) K_TWIN = Some h1
    /\ sts = [set_facts (set_ops (setregs st (IMap.remove sh (s_regs st))) (set_op HEAP_ID h1 (s_ops st))) (drop_anchor_facts sh (s_facts st))].
Proof.
  intros sel st sts H. unfold twin_in_apply in H.
  destruct (aheap_windows st) as [[hargs wnl]|] eqn:AW; [|discriminate H].
  destruct (twsel_pair sel st wnl) as [[kf sh]|] eqn:SEL; [| left; injection H as <-; reflexivity].
  right.
  assert (OUT : forall wl0 k p, tw_out (s_facts st) wl0 k = Some p -> find_twin (s_facts st) (fst p) = Some (snd p)).
  { intros wl0 k p X. unfold tw_out in X. destruct (find_twin (s_facts st) k) as [sh0|] eqn:F0; [|discriminate X]. destruct (CtrA.win_lookup wl0 sh0); [|discriminate X].
    injection X as <-. exact F0. }
  assert (GO : forall wl0 n l p, twlen_go (s_facts st) wl0 n l = Some p -> find_twin (s_facts st) (fst p) = Some (snd p)).
  { intros wl0 n l p. induction l as [|[[k len] kd] l IH]; intros X; [discriminate X|]. cbn [twlen_go] in X.
    destruct len as [lw| | | | | | | | | |]; try (exact (IH X)).
    destruct (weqb kd CtrLib.K_BLOCK && weqb lw n); [| exact (IH X)].
    destruct (tw_out (s_facts st) wl0 k) as [p0|] eqn:O0; [| exact (IH X)]. injection X as <-. exact (OUT wl0 k p0 O0). }
  assert (FT : find_twin (s_facts st) kf = Some sh).
  { unfold twsel_pair in SEL. destruct sel as [rs off|n]; [| exact (GO wnl n wnl (kf, sh) SEL)].
    destruct (getr st rs) as [|k o| | | | | | | | |]; try discriminate SEL. destruct (weqb o off); [|discriminate SEL]. exact (OUT wnl k (kf, sh) SEL). }
  match type of H with (if ?c then _ else _) = _ => destruct c eqn:CK; [|discriminate H] end.
  repeat match type of CK with (_ && _)%bool = true => let X := fresh "Q" in apply andb_prop in CK as [CK X] end.
  destruct (heap_del_window_k hargs (VP sh wzero) K_TWIN) as [h1|] eqn:H1; [|discriminate H]. injection H as <-.
  destruct (s_resv st) eqn:RV; try discriminate CK.
  exists hargs, wnl, kf, sh, h1. repeat (split; [reflexivity || assumption|]). reflexivity.
Qed.

Section TwinIn.
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

Hypothesis Cw_ghost_free : forall md ca LB ws m b n ws', cw_holds Cw md ca LB ws m -> In (Win b n K_TWINz) ws ->
  (forall w, In w ws' <-> In w ws /\ w <> Win b n K_TWINz) -> cw_holds Cw md ca (remove iv_eq_dec (b, n) LB) ws' m.

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

Section RELEASED.
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
Variables (kf sh : int).
Hypothesis NV : no_views_on (s_facts st) (s_regs st) kf sh = true.
Hypothesis TCAN : twin_canon st wnl kf sh = true.
Variables (rf : region) (lenf lent : sv).
Hypothesis Frf : IMap.find kf (s_regs st) = Some rf.
Hypothesis WLf : CtrA.win_lookup wnl kf = Some (lenf, CtrLib.K_BLOCK).
Hypothesis WLt : CtrA.win_lookup wnl sh = Some (lent, K_TWIN).
Hypothesis BTs : block_of_twin (s_facts st) sh = Some kf.
Hypothesis LO0 : rg_lo rf = 0%uint63.
Hypothesis POSf : 0 < hiZ E rf.
Hypothesis LEf : hiZ E rf <= bv_unsigned (den E lenf).
Hypothesis OTHERS : forall k len kd, In (k, len, kd) wnl -> k <> kf -> k <> sh ->
  (weqb kd K_TWIN = true /\ exists kb, block_of_twin (s_facts st) k = Some kb /\ kb <> kf)
  \/ (weqb kd K_TWIN = false /\ exists r0, IMap.find k (s_regs st) = Some r0 /\ rg_lo r0 = 0%uint63 /\ hiZ E r0 <= bv_unsigned (den E len)
        /\ 0 < hiZ E r0 /\ rg_w r0 = true /\ (kd = CtrLib.K_BLOCK \/ hiZ E rf = bv_unsigned (den E lenf))).

Let Af : Z := bv_unsigned (ev E kf).
Let nf : Z := bv_unsigned (den E lenf).
Let m : amem := ms_mem ms.
Let WOF : wit_of WW (w_L WW) (w_RNG WW) (w_st WW) (w_LBa WW) := wit_of_refl WW.

Lemma AWHf : aw_holds_asan AI ACCT UNIV aw LB m mo.
Proof. exact (aw_real_holds AI ACCT UNIV _ _ _ _ _ AR). Qed.
Lemma HWf : aw_holds_w AI ACCT UNIV WW aw LB m mo.
Proof. exact (proj1 AR). Qed.

Lemma twin_data : exists rs p,
  IMap.find sh (s_regs st) = Some rs /\ bv_unsigned (ev E sh) = shad Af /\ bv_unsigned (den E lent) = shlen (nf + 7)
  /\ In (Af, nf) LB /\ In (shad Af, shlen (nf + 7)) LB /\ In (HB p Af nf) (w_T WW) /\ user_band Af /\ 1 <= nf
  /\ ablock_shadow m Af nf.
Proof.
  destruct (CtrFree.TwinB.twin_sh AI IMGX IMGX_aci ACCT UNIV OPS AI_fake E st ms mo HS wnl nn rest LB aw NW WF WW AR kf sh None (CtrFree.TwinB.twin_consume_canon _ _ _ _ TCAN) rf lenf lent WLf WLt BTs POSf LEf)
    as (rs & Frs & _ & _ & ESH & ELT).
  destruct (CtrFree.TwinB.owner AI IMGX IMGX_aci ACCT UNIV OPS AI_fake E st ms mo HS wnl nn rest LB aw _ _ _ _ NW WF WW WOF AR TI kf sh None (CtrFree.TwinB.twin_consume_canon _ _ _ _ TCAN) rf lenf lent WLf WLt BTs POSf LEf)
    as (UBf & HTf & (p & _ & HPT) & NRf & _).
  exists rs, p. split; [exact Frs|]. split; [exact ESH|]. split; [exact ELT|].
  split. { destruct (CtrFree.TwinB.entry_window E wnl nn rest LB NW WF kf lenf kf lenf CtrLib.K_BLOCK (HeapCtrB.TwinB.win_lookup_In _ _ _ _ WLf)) as (_ & _ & b & Hb & _ & EQ). rewrite (EQ eq_refl) in Hb. exact Hb. }
  split; [exact HTf|]. split; [exact HPT|]. split; [exact UBf|]. split; [lia|].
  exact (CtrFree.TwinB.freed_pattern AI IMGX IMGX_aci ACCT UNIV OPS AI_fake E st ms mo HS wnl nn rest LB aw _ _ _ _ NW WF WW WOF AR TI kf sh None (CtrFree.TwinB.twin_consume_canon _ _ _ _ TCAN) rf lenf lent WLf WLt BTs POSf LEf OTHERS).
Qed.

Variables (rs : region) (p : aptr).
Hypothesis Frs : IMap.find sh (s_regs st) = Some rs.
Hypothesis ESH : bv_unsigned (ev E sh) = shad Af.
Hypothesis ELT : bv_unsigned (den E lent) = shlen (nf + 7).
Hypothesis INB : In (Af, nf) LB.
Hypothesis INT : In (shad Af, shlen (nf + 7)) LB.
Hypothesis HPT : In (HB p Af nf) (w_T WW).
Hypothesis UBf : user_band Af.
Hypothesis NF1 : 1 <= nf.
Hypothesis PAT : ablock_shadow m Af nf.

Let bT : ablock := HB p Af nf.
Definition LBk : blocks := remove iv_eq_dec (twin_iv bT) LB.
Definition Wf : wit := wit_twin_in WW m bT.
Definition WTf : window := Win (shad Af) (shlen (nf + 7)) K_TWINz.

Lemma LBk_In : forall v, In v LBk <-> (In v LB /\ v <> (shad Af, shlen (nf + 7))).
Proof.
  intros v. unfold LBk, bT, twin_iv. cbn [ab_addr ab_size]. split.
  - intros H. apply in_remove in H. exact H.
  - intros [H N]. apply in_in_remove; assumption.
Qed.
Lemma LBk_sub : forall v, In v LBk -> In v LB.
Proof. intros v H. exact (proj1 (proj1 (LBk_In v) H)). Qed.

Lemma HW1 : aw_holds_w AI ACCT UNIV Wf aw LBk m mo.
Proof. exact (twin_in_w AI ACCT UNIV AI_fake WW aw LB m mo bT HWf HPT PAT). Qed.

Definition KEEPf (k0 : int) : Prop := k0 <> sh.
Lemma twin_not_user : (Af, nf) <> (shad Af, shlen (nf + 7)).
Proof.
  intros X. injection X as X1 _. destruct (LB_twin_facts AI ACCT UNIV WW aw LB m mo bT HWf HPT) as (T1 & T2 & T3). unfold bT in T1, T2, T3. cbn [ab_addr ab_size] in T1, T2, T3.
  unfold user_band in UBf. lia.
Qed.
Lemma kept_entry : forall k len kd b, In (k, len, kd) wnl -> k <> sh ->
  In b LB -> (forall a, in_iv (bv_unsigned (ev E k), bv_unsigned (den E len)) a -> in_iv b a) -> b <> (shad Af, shlen (nf + 7)).
Proof.
  intros k len kd b Hin NKs Hb SUB. destruct (Uint63.eqb k kf) eqn:Q.
  - apply Uint63.eqb_correct in Q. subst k.
    destruct (HeapCtrB.TwinB.windows_anchored_nodup _ _ kf len kd lenf CtrLib.K_BLOCK AN Hin (HeapCtrB.TwinB.win_lookup_In _ _ _ _ WLf)) as [-> ->].

    intros ->. fold Af nf in SUB. specialize (SUB Af ltac:(unfold in_iv; cbn [fst snd]; lia)).
    destruct (LB_twin_facts AI ACCT UNIV WW aw LB m mo bT HWf HPT) as (T1 & T2 & T3). unfold bT in T1, T2, T3. cbn [ab_addr ab_size] in T1, T2, T3.
    unfold in_iv in SUB. cbn [fst snd] in SUB. unfold user_band in UBf. lia.
  - apply Uint63.eqb_false_spec in Q.
    exact (proj2 (CtrFree.TwinB.kept_block AI IMGX IMGX_aci ACCT UNIV OPS AI_fake E st ms mo HS wnl nn rest LB aw _ _ _ _ NW WF WW WOF AR TI CVU kf sh None (CtrFree.TwinB.twin_consume_canon _ _ _ _ TCAN) rf lenf lent Frf WLf WLt BTs LO0 POSf LEf OTHERS
                    k len kd b Hin Q NKs Hb SUB)).
Qed.

Lemma WINKf : forall k0 len kd, KEEPf k0 -> CtrA.win_lookup wnl k0 = Some (len, kd) ->
  forall a, bv_unsigned (ev E k0) <= a < bv_unsigned (ev E k0) + bv_unsigned (den E len) -> in_user LBk a.
Proof.
  intros k0 len kd NKs WL a Ha. pose proof (HeapCtrB.TwinB.win_lookup_In _ _ _ _ WL) as Hin.
  destruct (CtrFree.TwinB.entry_window E wnl nn rest LB NW WF kf lenf k0 len kd Hin) as (_ & _ & b & Hb & SUB & _).
  apply in_ivs_In. exists b. split; [apply LBk_In; split; [exact Hb| exact (kept_entry k0 len kd b Hin NKs Hb SUB)]|]. apply SUB. unfold in_iv. cbn [fst snd]. lia.
Qed.
Lemma VKEEPf : forall k0 rg hs n sh' len, IMap.find k0 (s_regs st) = Some rg -> zero_view rg = Some hs -> KEEPf k0 ->
  block_of_twin (s_facts st) k0 = Some n -> CallV.TwinB.view_parent (s_facts st) (s_regs st) n sh' ->
  CtrA.win_lookup wnl sh' = Some (len, K_TWIN) -> KEEPf sh'.
Proof.
  intros k0 rg hs n sh' len Fk ZV NKs BT VPAR WL. intros ->. unfold no_views_on in NV.
  pose proof (proj1 (IMap.forallb_spec _ _ (so_bst _ _ _ _ _ _ HS)) NV k0 rg Fk) as C. cbv beta in C.
  replace (PrimInt63.eqb k0 sh) with false in C by (symmetry; apply Uint63.eqb_false_spec; exact NKs).
  rewrite ZV, BT in C. destruct VPAR as [(kb & o1 & UB & TW)|(rshp & Frshp & HNp)];
      [rewrite UB, TW, Uint63.eqb_refl in C; cbn in C; discriminate C| rewrite Frshp, HNp in C; cbn [negb] in C; rewrite !Bool.andb_false_r in C; discriminate C].
Qed.

Lemma TKEEPf : forall k0 rg sh' kb n len, IMap.find k0 (s_regs st) = Some rg -> KEEPf k0 -> CtrA.win_lookup wnl sh' = Some (len, K_TWIN) ->
  block_of_twin (s_facts st) sh' = Some kb -> CtrA.win_lookup wnl kb = Some (n, CtrLib.K_BLOCK) ->
  size_tail_ok (s_facts st) n = true -> tail_named (tail_rhs sh' n) k0 (s_facts st) = true -> KEEPf sh'.
Proof.
  intros k0 rg sh' kb n len Fk NKs WL BT WLk ST TN. intros ->. rewrite BTs in BT. injection BT as <-. rewrite WLf in WLk. injection WLk as <-.
  destruct (CallA.TwinB.twin_canon_inv st wnl kf sh TCAN) as (rs0 & n0 & kdn & lent0 & kdt & _ & WLn & _ & _ & _ & _ & _ & NTA). rewrite WLf in WLn. injection WLn as <- <-.
  exact (CallA.TwinB.no_tail_at_sound _ _ _ _ k0 rg (so_bst _ _ _ _ _ _ HS) NTA Fk TN).
Qed.
Lemma KEEP_delf : forall k0, ~ In k0 [sh] -> KEEPf k0.
Proof. intros k0 H ->. apply H. left. reflexivity. Qed.

Variables (hargs : list sv) (md : w64) (A : sv) (nw : w64).
Hypothesis Hf : find_op HEAP_ID (s_ops st) = Some hargs.
Hypothesis Eh : hargs = VL md :: A :: VL nw :: rest.
Hypothesis Tnw : wt nw = false.
Hypothesis Nn : nn = Z.to_nat (to_Z (wl nw)).
Hypothesis Ln : (3 * nn <= length rest)%nat.
Hypothesis FOK : fresh_ok st = true.
Variables (Fv : Z -> word) (Gv : Z -> Z -> byte).
Notation E' := (CtrDelta.TwinB.E' E st Fv Gv).
Variable h1 : list sv.
Hypothesis H1 : heap_del_window_k hargs (VP sh wzero) K_TWIN = Some h1.

Lemma DEL1 : exists m1 m2,
  decode (map (den E') h1) = Some (w2Z md, den E A, m1 ++ m2, map (den E) (skipn (3 * nn) rest))
  /\ wins_of E nn rest = m1 ++ WTf :: m2 /\ ~ In WTf (m1 ++ m2).
Proof.
  pose proof (HeapCtrB.TwinB.windows_anchored_nodup_anchors _ _ AN) as NDA.
  rewrite Eh in H1.
  destruct (CtrFree.TwinB.heap_del_window_k_facts E md A nw rest nn sh K_TWIN h1 wnl eq_refl Tnw Nn Ln NW H1)
    as (ws1 & m1 & len1 & m2 & wl1 & EH1 & I1 & W1 & W1' & T1 & N1 & L1 & SK1 & NW1 & S1 & S2 & S3 & M1 & PM1).
  destruct (HeapCtrB.TwinB.windows_anchored_nodup _ _ sh len1 K_TWIN lent K_TWIN AN I1 (HeapCtrB.TwinB.win_lookup_In _ _ _ _ WLt)) as [-> _].
  assert (ND1 : List.NoDup (sh :: HeapCtrB.TwinB.anchors wl1)) by (exact (Permutation_NoDup (CtrFree.TwinB.anchors_perm _ _ PM1) NDA)).
  apply List.NoDup_cons_iff in ND1 as [NSH1 _].
  exists m1, m2. split; [| split].
  - rewrite EH1. rewrite (decode_hargs E' md A _ _ (pred nn) T1 N1 L1).
    assert (RB : forallb (sv_vars_below (s_next st)) rest = true) by exact (CtrDelta.TwinB.rest_below st FOK rest hargs md A nw Hf Eh).
    assert (RB1 : forallb (sv_vars_below (s_next st)) (ws1 ++ skipn (3 * nn) rest) = true) by (apply (CtrFree.TwinB.forallb_sub _ rest); [exact S3| exact RB]).
    rewrite (CtrDelta.TwinB.den_E' E st Fv Gv A (CtrDelta.TwinB.A_below st FOK rest hargs md A nw Hf Eh)).
    rewrite (CtrDelta.TwinB.wins_of_E' E st Fv Gv _ _ RB1), W1', SK1.
    rewrite (CtrDelta.TwinB.map_den_E' E st Fv Gv _ (CtrFree.TwinB.forallb_skipn _ (3 * nn) rest RB)). reflexivity.
  - rewrite W1. unfold WTf. rewrite ESH, ELT. reflexivity.
  - intros X. rewrite <- W1' in X.
    destruct (HeapCtrB.TwinB.wins_cover E (pred nn) _ wl1 WTf NW1 X) as [KS|(k & len & kd & Ik & EW)]; [cbn in KS; unfold K_TWINz, K_STACK in KS; lia|].
    unfold WTf in EW. injection EW as E1 E2 E3.
    assert (NKs : k <> sh).
    { intros ->. apply NSH1. unfold HeapCtrB.TwinB.anchors. apply in_map_iff. exists (sh, len, kd). split; [reflexivity| exact Ik]. }
    exact (kept_entry k len kd (shad Af, shlen (nf + 7)) (S1 _ Ik) NKs INT ltac:(rewrite <- E1, <- E2; intros a Ha; exact Ha) eq_refl).
Qed.

Hypothesis AWden : aw = den E A.
Hypothesis HC : cw_holds Cw (w2Z md) (map (den E) (skipn (3 * nn) rest)) LB (wins_of E nn rest) m.

Lemma HOLDN1 : forall m1 m2,
  decode (map (den E') h1) = Some (w2Z md, den E A, m1 ++ m2, map (den E) (skipn (3 * nn) rest)) ->
  wins_of E nn rest = m1 ++ WTf :: m2 -> ~ In WTf (m1 ++ m2) ->
  op_holds OPS HEAP_ID (map (den E') h1) m mo.
Proof.
  intros m1 m2 D W1 NT. rewrite OPS_holds1.
  assert (IN1 : forall w, In w (m1 ++ m2) <-> In w (wins_of E nn rest) /\ w <> WTf).
  { intros w. rewrite W1. split.
    - intros H. split; [apply in_app_or in H as [H|H]; apply in_or_app; [left; exact H| right; right; exact H]| intros ->; exact (NT H)].
    - intros [H NE]. apply in_app_or in H as [H|[H|H]]; apply in_or_app; [left; exact H| congruence| right; exact H]. }
  exists (w2Z md), aw, (m1 ++ m2), (map (den E) (skipn (3 * nn) rest)), LBk, Wf.
  split; [rewrite AWden; exact D|]. split; [exact HW1|]. split; [| split].
  - apply Forall_forall. intros w Hw. apply IN1 in Hw as [Hw NWT].
    pose proof (proj1 (Forall_forall _ _) WF w Hw) as (X1 & X2 & X3 & KD). split; [exact X1|]. split; [exact X2|]. split; [exact X3|].
    destruct (HeapCtrB.TwinB.wins_cover E nn rest wnl w NW Hw) as [KS|(k & len & kd & Ik & EW)].
    { left. destruct KD as [[_ C]|[[K _]|[K _]]]; [split; [exact KS| exact C]| rewrite KS in K; unfold K_BLOCK, K_STACK in K; lia| rewrite KS in K; unfold K_SUB, K_STACK in K; lia]. }
    assert (NKs : k <> sh).
    { intros ->. destruct (HeapCtrB.TwinB.windows_anchored_nodup _ _ sh len kd lent K_TWIN AN Ik (HeapCtrB.TwinB.win_lookup_In _ _ _ _ WLt)) as [-> ->].
      apply NWT. rewrite EW. unfold WTf. rewrite ESH, ELT. reflexivity. }
    destruct KD as [[K C]|[[K B]|[K (b & Hb & SUB)]]].
    + left. auto.
    + right; left. split; [exact K|]. apply LBk_In. split; [exact B|].
      apply (kept_entry k len kd (w_iv w) Ik NKs B). rewrite EW. unfold w_iv. cbn [w_lo w_len]. intros a0 Ha. exact Ha.
    + right; right. split; [exact K|]. exists b. split; [| exact SUB]. apply LBk_In. split; [exact Hb|].
      apply (kept_entry k len kd b Ik NKs Hb). rewrite EW in SUB. unfold w_iv in SUB. cbn [w_lo w_len] in SUB. exact SUB.
  - assert (INW : In WTf (wins_of E nn rest)) by (rewrite W1; apply in_or_app; right; left; reflexivity).
    exact (Cw_ghost_free _ _ _ _ m (shad Af) (shlen (nf + 7)) (m1 ++ m2) HC INW IN1).
  - exact (ties_twin_in AI ACCT UNIV AI_fake WW aw LB m mo (wins_of E nn rest) (m1 ++ m2) bT m HWf TI HPT IN1).
Qed.

Lemma released_off_image : forall a, in_iv (shad Af, shlen (nf + 7)) a -> find_segment bsegs a 1 = None.
Proof. intros a Ha. exact (proj2 (aw_user_ok_asan AI ACCT UNIV AI_fake aw LB m mo _ a AWHf INT Ha)). Qed.

Variable R' : bvmap 5 word.
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

Definition RgF : IMap.t region := CtrDelta.TwinB.RgPg (s_regs st) [] [sh].
Definition NEWSETf (_ : Z) : Prop := False.

Lemma released_unbased : forall a, in_iv (shad Af, shlen (nf + 7)) a -> ~ in_based E' RgF a.
Proof.
  intros a Ha (k0 & rg & Fk & KZ & RA).
  assert (SPF : ATOP + 4096 <= sp) by (rewrite SPE; lia).
  destruct (LB_twin_facts AI ACCT UNIV WW aw LB m mo bT HWf HPT) as (T1 & T2 & T3). unfold bT in T1, T2, T3. cbn [ab_addr ab_size] in T1, T2, T3.
  pose proof atop_range as ATR. unfold in_iv in Ha. cbn [fst snd] in Ha.
  destruct (CtrDelta.TwinB.RgPg_range OPS E st ms mo HS FOK Fv Gv LB LBk ks offs rss ksp SPR SPE wnl nn rest AJ WF KEEPf WINKf VKEEPf TKEEPf LOSP FLOOR
              (s_regs st) rss (so_bst _ _ _ _ _ _ HS) (CtrDelta.TwinB.inline_RB_find st ks offs rss SPR) eq_refl (fun _ => eq_refl)
              hargs md A nw Hf Hc Eh Tnw Nn Ln [] [sh]
              (NoDup_nil _) KEEP_delf NEWSETf ltac:(intros k1 r1 a1 X; destruct X) k0 rg a Fk KZ RA) as [[X _]|[_ [[_ X]|[_ [X|[X|X]]]]]].
  - destruct X.
  - lia.
  - fold sp in X. lia.
  -
    apply in_ivs_In in X as (v & Hv & Hin). apply LBk_In in Hv as [Hv NE]. destruct v as [A' n'].
    apply (aw_blocks_disj_asan AI ACCT UNIV AI_fake aw LB m mo (A', n') (shad Af, shlen (nf + 7)) a AWHf Hv INT); [| exact Hin| unfold in_iv; cbn [fst snd]; exact Ha].
    cbn [fst]. intros ->. apply NE. f_equal. exact (LB_same_addr AI ACCT UNIV AI_fake WW aw LB m mo (shad Af) n' (shlen (nf + 7)) HWf Hv INT).
  -
    assert (HbL : In bT (w_LBa WW)) by (pose proof HWf as (_ & HT & _); exact (proj1 (HT bT HPT))).
    pose proof HWf as (AH & _).
    destruct (heap_block_facts AI _ _ _ _ _ bT AH HbL ltac:(exists p; reflexivity)) as (NP & (BK & _ & HI & _) & _). cbn [ab_addr ab_size bT] in NP, BK, HI.
    destruct (shadow_tight Af nf BK HI ltac:(lia)) as [S1 S2].
    destruct (sh_cov_band a X) as [C|C]; lia.
Qed.

Theorem twin_in_post : forall (nx' : int),
  s_resv st = RNone ->
  st_ok bsegs OPS E' (SS (s_pc st) (s_rf st) (s_ff st) RNone RgF (drop_anchor_facts sh (s_facts st)) (set_op HEAP_ID h1 (s_ops st)) (s_priv st) nx')
        (MS (ms_regs ms) (ms_fregs ms) (Z_to_bv 64 (to_Z (s_pc st))) (ms_fcsr ms) None m (seg_rom bsegs)) mo.
Proof.
  intros nx' RVN. destruct DEL1 as (m1 & m2 & D & W1 & NT).
  pose proof (HOLDN1 m1 m2 D W1 NT) as HOLDN.
  assert (INWS : forall a, in_ws (wins_of E nn rest) a -> in_ws (m1 ++ m2) a \/ in_iv (shad Af, shlen (nf + 7)) a).
  { intros a X. unfold in_ws in X. apply in_ivs_In in X as (v & Hv & Hin). apply in_map_iff in Hv as (w & <- & Hw).
    rewrite W1 in Hw. apply in_app_or in Hw as [Hw|[<-|Hw]]; [| right; exact Hin|];
      left; unfold in_ws; apply in_ivs_In; exists (w_iv w); (split; [apply in_map; apply in_or_app; auto| exact Hin]). }
  assert (RSNOK : region_ok bsegs (s_priv st) E' m ks rss).
  { apply (CtrDelta.TwinB.sp_region_same_ok OPS E st ms mo HS FOK Fv Gv m ks offs rss SPR). intros a0 Ha RA0. split; [reflexivity| exact (fun H => H)]. }
  apply (CtrDelta.TwinB.delta_st_ok AI IMGX IMGX_aci ACCT UNIV OPS AI_fake OPS_fp1 OPS_cov1 OPS_frame_other OPS_fp_other OTHER OPS_mo_other OPS_cov0_img
           E st ms mo HS FOK Fv Gv (ms_regs ms) m mo aw LB LBk AWHf MINV'
           ltac:(intros a0 Ha S; split; [reflexivity| exact (fun H => H)]) ltac:(intros; reflexivity) ltac:(intros a0 Ha CC H; exact H)
           ltac:(intros a0 Ha SC IB; split; [reflexivity| exact (fun H => H)])
           ltac:(intros a0 Ha; split; [reflexivity| exact (fun H => H)])
           ks offs rss ksp SPR SPE wnl nn rest AJ WF KEEPf WINKf VKEEPf TKEEPf
           LOSP FLOOR (s_regs st) rss (so_bst _ _ _ _ _ _ HS) (CtrDelta.TwinB.inline_RB_find st ks offs rss SPR) eq_refl (fun _ => eq_refl) eq_refl RSNOK
           hargs md A nw Hf Hc Eh Tnw Nn Ln (OTHER_refl mo) [] [sh] (NoDup_nil _)
           ltac:(intros k1 r1 X; destruct X) KEEP_delf NEWSETf ltac:(intros k1 r1 X; destruct X) ltac:(intros k1 r1 a1 X; destruct X)
           ltac:(intros a1 X; destruct X) ltac:(intros a1 X; destruct X) ltac:(intros a1 X; destruct X) ltac:(intros k1 r1 k2 r2 a1 X; destruct X)
           h1 (w2Z md) (den E A) (m1 ++ m2) (map (den E) (skipn (3 * nn) rest)) D HOLDN).
  - intros a X. destruct X.
  -   intros a Ha NIX NWS. destruct (GLib.UG.in_ws_dec (wins_of E nn rest) a) as [IW|NIW]; [| left; exact NIW].
    right. destruct (INWS a IW) as [X|FR]; [contradiction|]. split; [exact (released_off_image a FR)| exact (released_unbased a FR)].
  -   intros a IB X. pose proof (CtrDelta.TwinB.in_heap_ws _ _ X) as IW. destruct (INWS a IW) as [Y|FR]; [| exfalso; exact (released_unbased a FR IB)].
    unfold in_ws, heap_ws in X |- *. apply in_ivs_In in X as (v & Hv & Hin). apply in_map_iff in Hv as (w & <- & Hw). apply filter_In in Hw as [Hw KW].
    apply in_ivs_In. exists (w_iv w). split; [| exact Hin]. apply in_map. apply filter_In. split; [| exact KW].
    rewrite W1 in Hw. apply in_app_or in Hw as [Hw|[<-|Hw]]; [apply in_or_app; auto| | apply in_or_app; auto].
    exfalso. exact (released_unbased a Hin IB).
  - exact (so_x0 _ _ _ _ _ _ HS).
  - intros x. pose proof (so_regs _ _ _ _ _ _ (CtrDelta.TwinB.HS' OPS E st ms mo HS FOK Fv Gv) x) as R0. unfold rget in R0 |- *. cbn [c_regs] in R0 |- *. exact R0.
  - reflexivity.
  -
    pose proof (so_facts _ _ _ _ _ _ (CtrDelta.TwinB.HS' OPS E st ms mo HS FOK Fv Gv)) as HF0. unfold facts_hold, drop_anchor_facts in *.
    apply Forall_forall. intros f Hf0. apply filter_In in Hf0 as [Hf0 _]. exact (proj1 (Forall_forall _ _) HF0 f Hf0).
  - exact MINVo.
Qed.
End RELEASED.

Variable MP : Model -> Prop.
Variable PB : (int -> list byte) -> Prop.

Lemma mem_inv_of : forall E st ms mo, st_ok bsegs OPS E st ms mo -> ALib.Mem.mem_inv bsegs (ms_mem ms).
Proof.
  intros E st ms mo HS a b Hm. unfold ALib.Mem.ro_addr. destruct (find_segment bsegs (bv_unsigned a) 1) as [seg|] eqn:Fs; [|reflexivity].
  rewrite (so_minv _ _ _ _ _ _ HS a b Hm seg Fs). reflexivity.
Qed.

Theorem twin_in_sound : forall pc sel, contract_sound bsegs OPS MP PB (twin_in_c pc sel).
Proof.
  intros pc sel st sts Hspc Happ K E ms mo HS HMP HPB HK. cbn [c_apply twin_in_c] in Happ.
  destruct (twin_in_apply_shape sel st sts Happ) as [->|(hargs & wnl & kf & sh & h1 & AW & RVN & FOK & SRG & SFO & FT & FOKk & TCAN & NV & H1 & ->)].
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
  destruct (CtrFree.TwinB.afree_ok_k_inv OPS CtrLib.K_BLOCK K_TWIN E st ms mo wnl kf sh HS FOKk)
    as (rf & lenf & lent & Frf & WLf & WLt & BTs & LO0 & POSf & LEf & OTHERS).
  destruct (twin_data E st ms mo HS wnl n rest LB (den E A) NW WF W ARW TI kf sh TCAN rf lenf lent WLf WLt BTs POSf LEf OTHERS)
    as (rs & p & Frs & ESH & ELT & INB & INT & HPT & UBf & NF1 & PAT).
  set (Fv := fun _ : Z => Z_to_bv 64 0). set (Gv := fun (_ _ : Z) => Z_to_bv 8 0).
  pose proof (twin_in_post E st ms mo HS wnl n rest LB (den E A) NW AN WF W ARW TI
                (CtrFree.TwinB.cvu_of Cw Cw_vec_unowned E st (ms_mem ms) LB n md A nw rest ltac:(rewrite <- Eh; exact Hf) N HC) kf sh NV TCAN rf lenf lent Frf WLf WLt BTs LO0 POSf LEf OTHERS
                p ESH ELT INT HPT UBf NF1 PAT hargs md A nw Hf Eh T N Ln FOK Fv Gv h1 H1 eq_refl HC
                (mem_inv_of E st ms mo HS) ks offs rss ksp SPR SP2 JU ltac:(lia) ltac:(lia) Hc (so_mf _ _ _ _ _ _ HS) (s_next st) RVN) as HSF.
  apply (HK _ (or_introl eq_refl) (CtrDelta.TwinB.E' E st Fv Gv) ms mo (CtrDelta.TwinB.EXT E st Fv Gv) HMP).
  rewrite (GlueA.TwinB.ms_formA bsegs OPS E st ms mo HS RVN) at 1.
  unfold set_facts, set_ops, setregs. cbn [s_pc s_rf s_ff s_resv s_regs s_facts s_ops s_priv s_next]. rewrite RVN. exact HSF.
Qed.
End TwinIn.
End TwinB.
