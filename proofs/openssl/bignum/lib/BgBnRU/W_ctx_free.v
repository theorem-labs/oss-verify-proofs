(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgLib Require Import ImageBg.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP Frame.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.Malloc Require Import MallocBlocks Malloc_iface.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgMallocU Require Import RMallocRep RMallocTree RMalloc_iface.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.Spec Require Import Prelim STree Malloc Monad Prog LibProg ProgG.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.Spec Require Import BnBase BnWords BnModel BnTree BnInv BnBridge BgState BgInv BgLib BgTree.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgU Require Import Layout Lib_iface Lib_kit.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BnW Require Import BnArith BnMem BnTac BnTacX.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BnP Require Import BnKit BnKit2 BnArr.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgBnU Require Import BnHeap W_crypto.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgBnU Require BnRep.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgBnU2 Require W_alloc3 W_ctx3 W_ctxfree3 W_ctxfree3_bridge.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgRepU Require Import BgRepDefs BgRep BgLayer BgIface BgPlace.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgBnRU Require Import CtxFreeModel.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.Lib Require Import Ceiling.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.P Require Import Rnd.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

Local Ltac std_lia__ := lia.
Local Ltac lia := first [std_lia__ | try (pose proof alloc_ceiling_range as CEIL_RANGE__); std_lia__].

Local Notation ST := (bstate bptr).

Lemma val_ids_blocks : forall (vs : list (bignum bptr)), W_ctxfree3.val_ids vs = map fst (concat (map bn_blocks vs)).
Proof.
  induction vs as [|b vs IH]; [reflexivity|]. rewrite W_ctxfree3.val_ids_cons. cbn [map concat]. rewrite map_app, <- IH. f_equal.
  unfold bn_blocks. destruct (bn_d b); reflexivity.
Qed.

Lemma val_ids_app : forall (l1 l2 : list (bignum bptr)), W_ctxfree3.val_ids (l1 ++ l2) = W_ctxfree3.val_ids l1 ++ W_ctxfree3.val_ids l2.
Proof. intros l1 l2. unfold W_ctxfree3.val_ids. apply flat_map_app. Qed.

Lemma firstn_add_gen : forall {A} n m (l : list A), firstn (n + m) l = firstn n l ++ firstn m (skipn n l).
Proof.
  intros A n. induction n as [|n IH]; intros m l; [reflexivity|]. destruct l as [|x l]; cbn [Nat.add firstn skipn app].
  - rewrite firstn_nil. reflexivity.
  - f_equal. apply IH.
Qed.

Lemma item_ids_perm : forall items (vals : list (bignum bptr)),
  Permutation (W_ctxfree3.item_ids items vals) (W_ctxfree3.val_ids (firstn (16 * length items) vals) ++ items).
Proof.
  induction items as [|q items IH]; intros vals; [cbn; apply Permutation_refl|].
  rewrite W_ctxfree3.item_ids_cons. cbn [length].
  replace (16 * S (length items))%nat with (16 + 16 * length items)%nat by lia.
  rewrite firstn_add_gen, val_ids_app. rewrite <- app_assoc.
  apply Permutation_app_head. eapply Permutation_trans; [apply perm_skip; apply IH|]. apply Permutation_middle.
Qed.

Lemma ctx_free_ids_perm : forall (bs : ST) qc, length (st_bns bs) = (NFIX + 16 * length (gx_items (st_ctx bs)))%nat ->
  Permutation (W_ctxfree3.ctx_free_ids (gx_indexes (st_ctx bs)) (gx_items (st_ctx bs)) (skipn NFIX (st_bns bs)) qc) (ctx_part_ids bs qc).
Proof.
  intros bs qc EL. unfold W_ctxfree3.ctx_free_ids, ctx_part_ids.
  assert (E1 : W_ctxfree3.opt_ids (gx_indexes (st_ctx bs)) = map fst (opt_block (gx_indexes (st_ctx bs)) (4 * Z.of_nat BN_CTX_START_FRAMES)))
    by (destruct (gx_indexes (st_ctx bs)); reflexivity).
  rewrite E1. rewrite <- val_ids_blocks.
  assert (E2 : firstn (16 * length (gx_items (st_ctx bs))) (skipn NFIX (st_bns bs)) = skipn NFIX (st_bns bs)) by (apply firstn_all2; rewrite length_skipn; lia).
  pose proof (item_ids_perm (gx_items (st_ctx bs)) (skipn NFIX (st_bns bs))) as P. rewrite E2 in P.
  set (ix := map fst (opt_block (gx_indexes (st_ctx bs)) (4 * Z.of_nat BN_CTX_START_FRAMES))) in *.
  eapply Permutation_trans; [apply Permutation_app_head; apply Permutation_app_tail; exact P|].
  set (v := W_ctxfree3.val_ids (skipn NFIX (st_bns bs))). set (it := gx_items (st_ctx bs)). clearbody ix v it.

  eapply Permutation_trans; [apply Permutation_app_comm|].
  eapply Permutation_trans; [apply Permutation_app_tail; apply Permutation_app_comm|].
  cbn [app]. rewrite <- !app_assoc. apply Permutation_refl.
Qed.

Lemma lb_remove_list_app_l : forall ps OW LB, (forall p, In p ps -> ~ In p (map blk_id LB)) ->
  W_ctxfree3.lb_remove_list ps (OW ++ LB) = W_ctxfree3.lb_remove_list ps OW ++ LB.
Proof.
  induction ps as [|p ps IH]; intros OW LB H; [reflexivity|]. cbn [W_ctxfree3.lb_remove_list].
  rewrite lb_remove_app, (lb_remove_notin p LB (H p ltac:(left; reflexivity))). apply IH. intros p' Hp'. apply H. right. exact Hp'.
Qed.

Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.

Definition BN_CTX_FREE : Z := 0x100afc.
Definition BN_CTX_FREE_STACK : Z := W_ctxfree3.BN_CTX_FREE_STACK.

Definition ctxf_post (ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (s : PState) (st : ST) (OW LB : list block) (lo B : Z) (m : mem) (PL : placement) (EA : BnRep.err_addrs)
    (r : unit * ST) (s' : PState) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' OW' errv',
    ms' = MS (mkR ra sp gp (wz RATP) t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom bgusegs)
    /\ RHEAP s' (OW' ++ LB) m' /\ lib_state (snd r) m' OW' (pl_set_ctx PL None) EA /\ rauxv_ok m' B /\ stk bgusegs m' lo (bv_unsigned sp)
    /\ rw_cells bgusegs m' LX_ERRNO [C4 errv'] /\ mem_inv bgusegs m' /\ lx_pres LB (bv_unsigned sp) (XW PL) m m'
    /\ ps_fa s' = ps_fa s /\ ps_so s' = ps_so s /\ snd r = st_ctx_freed st.

Section Proofs.
  Hypothesis HM : rmalloc_stmt.
  Hypothesis HF : rfree_stmt.

  Lemma BN_CTX_free_walk : forall
      (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (s : PState) (bs : bstate bptr) (OW LB : list block) (PL : placement) (EA : BnRep.err_addrs)
      (lo B : Z) (errv : word) (ac : Z) (qc : bptr),
    bn_pre s bs m OW LB PL EA sp lo B errv BN_CTX_FREE_STACK -> tp = wz RATP ->
    pl_ctx PL = Some (ac, qc) -> a0 = wz ac ->
    implM bgusegs (interp (embed (BN_CTX_free_g (tree_ops bptr) qc bs))) s
      (ctxf_post ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s bs OW LB lo B m PL EA)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (wz BN_CTX_FREE) fc None m (seg_rom bgusegs)).
  Proof.
    intros until qc. intros (HEAP & LS & FROK & AUX & SPB & B63 & ST & CEIL & GLO & LO & ERR & MI) -> E ->.
    pose proof (RH_nodup_l _ _ _ _ HEAP) as ND. pose proof (LH_nodup _ _ _ HEAP) as NDL.
    pose proof (lib_state_h_parts _ _ _ _ _ _ LS) as PARTS; pose proof PARTS as (WFS & PWF & IDS & PLB & ERRB).
    pose proof WFS as (EL & OKS & _ & _). unfold BN_CTX_POOL_SIZE in EL.
    rewrite (BN_CTX_free_g_tree qc bs WFS).
    destruct (pool_fl0 bs) eqn:PF; [|cbn [interp]; apply implM_unr].

    pose proof LS as (_ & _ & _ & (_ & _ & _ & (_ & _ & M3 & _))). rewrite E in M3.
    destruct M3 as [Hinc (Hs & Ia & LHs & HCX & HIT)]. destruct (HCX eq_refl) as [CX SREP]. clear HCX.
    set (c := st_ctx bs) in *. set (items := gx_items c) in *. set (vals := skipn NFIX (st_bns bs)) in *.
    set (L := OW ++ LB) in *.
    assert (INCL : forall b0, In b0 OW -> In b0 L) by (intros b0 Hb0; apply in_or_app; left; exact Hb0).
    assert (LV : length vals = (16 * length items)%nat) by (unfold vals; rewrite length_skipn; clear - EL; lia).

    assert (PIT : W_ctxfree3.pitems m L items Hs vals 0).
    { eapply W_ctxfree3_bridge.items_gen_pitems.
      eapply (items_gen_impl_idx (holeR [] m OW PL) (W_ctxfree3_bridge.Rfree m L)).
      2:{ eapply (items_gen_transport (fun _ => True) (holeR [] m OW PL) (holeR [] m OW PL) false m m OW L); [exact HIT| apply agree_on_refl|].
          intros q0 H0 _ Hin0. split; [apply INCL; exact Hin0| intros _ x _; exact I]. }
      intros k q0 H0 j Ek EH Hj [[]|(D & SC & AR)]. rewrite pl_of_pool in SC, AR. cbn [Nat.add] in *.
      assert (KL : (k < length items)%nat) by (apply nth_error_Some; rewrite Ek; discriminate).
      assert (IDX : (16 * k + j < length vals)%nat) by (unfold BN_CTX_POOL_SIZE in *; lia).
      set (b0 := nth (BN_CTX_POOL_SIZE * k + j) vals (bn_nil 0)) in *.
      assert (EB : b0 = getbn (RPool (16 * k + j)) bs) by (unfold b0, getbn, RPool, vals, BN_CTX_POOL_SIZE; rewrite nth_skipn; reflexivity).
      split; [|split].
      - exists D. split; [exact SC|]. unfold bn_arr in *. destruct (bn_d b0) as [p0|]; [split; [apply INCL; exact (proj1 AR)| exact (proj2 AR)]| exact AR].
      - rewrite EB. apply OKS; [unfold RPool; rewrite EL; clear - KL Hj; unfold BN_CTX_POOL_SIZE in Hj; lia| unfold RPool, ROne, NFIX; lia].
      - unfold pool_fl0 in PF. rewrite forallb_forall in PF. apply Z.eqb_eq. apply PF. fold vals. unfold b0. apply nth_In. unfold BN_CTX_POOL_SIZE. exact IDX. }

    set (ids := W_ctxfree3.ctx_free_ids (gx_indexes c) items vals qc).
    pose proof (ctx_free_ids_perm bs qc EL) as PERM. fold c items vals ids in PERM.
    destruct (lib_state_unplace_ctx [] bs m OW PL EA ac qc LS ltac:(intros i []) E) as (LSU & DISJ).
    assert (NDI : List.NoDup ids).
    { eapply Permutation_NoDup; [apply Permutation_sym; exact PERM|].
      pose proof (Permutation_NoDup (all_ids_ctx_split bs PL EA ac qc E) IDS) as N. eapply nodup_app_l. exact N. }
    assert (IDOW : forall p, In p ids -> In p (map blk_id OW)).
    { intros p Hp. eapply (all_ids_owned bs m OW PL EA p LS ND).
      eapply Permutation_in; [apply Permutation_sym; apply (all_ids_ctx_split bs PL EA ac qc E)|]. apply in_or_app. left.
      eapply Permutation_in; [exact PERM| exact Hp]. }
    assert (IDLB : forall p, In p ids -> ~ In p (map blk_id LB)).
    { intros p Hp H. unfold L in NDL. rewrite map_app in NDL. exact (BnHeap.nodup_app_disj _ _ p NDL (IDOW p Hp) H). }
    assert (IDFRESH : forall p, In p ids -> ~ In p (all_ids (st_ctx_freed bs) (pl_set_ctx PL None) EA)).
    { intros p Hp. apply DISJ. eapply Permutation_in; [exact PERM| exact Hp]. }
    eapply (W_ctxfree3.BN_CTX_free_walk HF) with (B := B) (lo := lo) (errv := errv) (A := ac) (IX := Ia) (Hs := Hs) (prev := 0);
      [exact HEAP | apply INCL; exact Hinc | exact CX | | exact PIT | exact NDI | exact AUX | exact SPB | exact ST | exact CEIL | exact GLO | exact LO
      | exact ERR | exact MI | reflexivity | exact (proj1 LS) | reflexivity | ].
    { unfold stack_rep in SREP. destruct (gx_indexes c) as [qi|]; [apply INCL; exact (proj1 SREP)| exact (proj1 SREP)]. }
    intros s' ms' PO. unfold W_ctx3.gfree_post in PO.
    destruct PO as (y0 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & y8 & y9 & y10 & y11 & y12 & y13 & y14 & m' & -> & MI' & ST' & ERR' & AUX' & HP' & FA & SO & HEAP').
    cbn [interp]. apply implM_ret. apply evt_done.
    fold ids in HP', HEAP'. unfold L in HP', HEAP'. rewrite (lb_remove_list_app_l ids OW LB IDLB) in HP', HEAP'.
    set (OWF := W_ctxfree3.lb_remove_list ids OW) in *.
    unfold ctxf_post. exists y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, y14, m', OWF, errv. split; [reflexivity|]. cbn [fst snd].
    split; [exact HEAP'|].
    split. { eapply (lib_state_h_heap_pres _ _ _ _ _ _ _ _ _ (bv_unsigned sp) B); [| apply frames_ok_set_ctx; exact FROK| | exact HP'|]; [| lia| intros b0 Hb0; apply in_or_app; left; exact Hb0].
             eapply lib_state_h_ow; [exact LSU|]. intros q0 A0 n0 Hq0 Hin0. apply W_ctxfree3.lb_remove_list_In; [exact Hin0|].
             cbn [blk_id fst]. intros Hid. exact (IDFRESH q0 Hid Hq0). }
    split; [exact AUX'|]. split; [exact ST'|]. split; [exact ERR'|]. split; [exact MI'|].
    split. { apply lx_pres_of_heap_pres. eapply rheap_pres_weaken; [exact HP'| lia|]. intros b0 Hb0. apply in_or_app. right. exact Hb0. }
    split; [exact FA|]. split; [exact SO|]. reflexivity.
  Qed.

End Proofs.
End WithCeiling0.
