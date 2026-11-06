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
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Bridge Require CallA CallV CtrPre GlueA CtrFrame.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Unp Require GLib.
Import ValP MemP CtrFX.
Import ActrA.
Module AP := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.PropExec.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Bridge Require KnownA.
Unset Nia Cache. Unset Nra Cache.

Lemma del_window_k_split : forall E0 m ws k0 kd0 ws' wl,
  weqb kd0 wzero = false ->
  del_window_k m ws (VP k0 wzero) kd0 = Some ws' -> CtrA.nonstack_windows m ws = Some wl -> (3 * m <= length ws)%nat ->
  exists l1 len l2 wl', In (k0, len, kd0) wl
    /\ wins_of E0 m ws = l1 ++ Win (bv_unsigned (ev E0 k0)) (bv_unsigned (den E0 len)) (w2Z kd0) :: l2
    /\ wins_of E0 (pred m) ws' = l1 ++ l2 /\ length ws' = (length ws - 3)%nat /\ (1 <= m)%nat
    /\ CtrA.nonstack_windows (pred m) ws' = Some wl'
    /\ (forall x, In x wl' -> In x wl) /\ (forall x, In x wl -> x = (k0, len, kd0) \/ In x wl')
    /\ (forall x, In x ws' -> In x ws) /\ Permutation wl ((k0, len, kd0) :: wl').
Proof.
  intros E0 m. induction m as [|m IH]; intros ws k0 kd0 ws' wl KZ H N L; [cbn in H; destruct ws; discriminate|].
  destruct ws as [|wlo [|ln [|kdv ws0]]]; try (cbn in H; discriminate). cbn [del_window_k] in H. cbn [CtrA.nonstack_windows] in N. cbn [length] in L |- *.
  destruct kdv as [kw| | | | | | | | | |]; try discriminate.
  destruct (CtrA.nonstack_windows m ws0) as [l|] eqn:NW; [|discriminate].
  destruct (sv_eqb wlo (VP k0 wzero) && sv_eqb (VL kw) (VL kd0)) eqn:C.
  - injection H as <-. apply andb_prop in C as [C1 C2]. apply sv_eqb_eq in C1. apply sv_eqb_eq in C2. injection C2 as ->. subst wlo.
    rewrite KZ in N. rewrite weqb_refl in N. cbn [andb negb] in N.
    destruct (PrimInt63.eqb k0 0); [discriminate|]. destruct (PrimInt63.eqb k0 CtrA.STACK_ID); [discriminate|]. cbn [andb negb] in N. injection N as <-.
    exists [], ln, (wins_of E0 m ws0), l. split; [left; reflexivity|]. rewrite wins_of_cons, HeapCtr.den_VPz, unsigned_VL. cbn [app pred].
    split; [reflexivity|]. split; [reflexivity|]. split; [lia|]. split; [lia|]. split; [exact NW|].
    split; [intros x Hx; right; exact Hx|]. split; [intros x [<-|Hx]; [left; reflexivity| right; exact Hx]|]. split; [intros x Hx; do 3 right; exact Hx| apply Permutation_refl].
  - destruct (del_window_k m ws0 (VP k0 wzero) kd0) as [ws''|] eqn:D; [|discriminate]. injection H as <-.
    destruct (IH ws0 k0 kd0 ws'' l KZ D NW ltac:(lia)) as (l1 & len & l2 & wl'' & I & W1 & W2 & LEN & M1 & NW'' & S1 & S2 & S3 & PM).
    destruct m as [|m']; [lia|]. cbn [pred] in *.
    assert (SUBW : forall x, In x (wlo :: ln :: VL kw :: ws'') -> In x (wlo :: ln :: VL kw :: ws0)).
    { intros x [Hx|[Hx|[Hx|Hx]]]; [left| right; left| right; right; left| do 3 right; apply S3]; assumption. }
    destruct (weqb kw wzero) eqn:KW0.
    + injection N as <-.
      exists (Win (bv_unsigned (den E0 wlo)) (bv_unsigned (den E0 ln)) (bv_unsigned (den E0 (VL kw))) :: l1), len, l2, wl''.
      split; [exact I|]. rewrite wins_of_cons, W1. cbn [app]. split; [reflexivity|]. rewrite wins_of_cons, W2. split; [reflexivity|].
      cbn [length]. split; [lia|]. split; [lia|]. split; [cbn [CtrA.nonstack_windows]; rewrite NW'', KW0; reflexivity|].
      split; [exact S1|]. split; [exact S2|]. split; [exact SUBW| exact PM].
    + destruct wlo as [|kk oo| | | | | | | | |]; try discriminate.
      destruct (weqb oo wzero && negb (PrimInt63.eqb kk 0) && negb (PrimInt63.eqb kk CtrA.STACK_ID)) eqn:CC; [|discriminate]. injection N as <-.
      exists (Win (bv_unsigned (den E0 (VP kk oo))) (bv_unsigned (den E0 ln)) (bv_unsigned (den E0 (VL kw))) :: l1), len, l2, ((kk, ln, kw) :: wl'').
      split; [right; exact I|]. rewrite wins_of_cons, W1. cbn [app]. split; [reflexivity|]. rewrite wins_of_cons, W2. split; [reflexivity|].
      cbn [length]. split; [lia|]. split; [lia|]. split; [cbn [CtrA.nonstack_windows]; rewrite NW'', KW0, CC; reflexivity|].
      split; [intros x [<-|Hx]; [left; reflexivity| right; apply S1; exact Hx]|].
      split; [intros x [<-|Hx]; [right; left; reflexivity| destruct (S2 x Hx) as [X|X]; [left; exact X| right; right; exact X]]|]. split; [exact SUBW|].
      eapply Permutation_trans; [apply perm_skip; exact PM| apply perm_swap].
Qed.

Lemma heap_del_window_k_facts : forall E0 md A nw rest n k0 kd0 h' wnl,
  weqb kd0 wzero = false -> wt nw = false -> n = Z.to_nat (to_Z (wl nw)) -> (3 * n <= length rest)%nat ->
  CtrA.nonstack_windows n rest = Some wnl ->
  heap_del_window_k (VL md :: A :: VL nw :: rest) (VP k0 wzero) kd0 = Some h' ->
  exists ws' l1 len l2 wl',
    h' = VL md :: A :: VL (wsub nw wone) :: ws' ++ skipn (3 * n) rest
    /\ In (k0, len, kd0) wnl
    /\ wins_of E0 n rest = l1 ++ Win (bv_unsigned (ev E0 k0)) (bv_unsigned (den E0 len)) (w2Z kd0) :: l2
    /\ wins_of E0 (pred n) (ws' ++ skipn (3 * n) rest) = l1 ++ l2
    /\ wt (wsub nw wone) = false /\ pred n = Z.to_nat (to_Z (wl (wsub nw wone))) /\ (3 * pred n <= length (ws' ++ skipn (3 * n) rest))%nat
    /\ skipn (3 * pred n) (ws' ++ skipn (3 * n) rest) = skipn (3 * n) rest
    /\ CtrA.nonstack_windows (pred n) (ws' ++ skipn (3 * n) rest) = Some wl'
    /\ (forall x, In x wl' -> In x wnl) /\ (forall x, In x wnl -> x = (k0, len, kd0) \/ In x wl')
    /\ (forall x, In x (ws' ++ skipn (3 * n) rest) -> In x rest) /\ (1 <= n)%nat /\ Permutation wnl ((k0, len, kd0) :: wl').
Proof.
  intros E0 md A nw rest n k0 kd0 h' wnl KZ T N L NW H. unfold heap_del_window_k in H.
  assert (HN : heap_nwin (VL md :: A :: VL nw :: rest) = Some n).
  { unfold heap_nwin. rewrite T, <- N. destruct (Nat.leb_spec (3 * n) (length rest)); [reflexivity| lia]. }
  rewrite HN in H. destruct (del_window_k n (firstn (3 * n) rest) (VP k0 wzero) kd0) as [ws'|] eqn:D; [|discriminate]. injection H as <-.
  assert (NWf : CtrA.nonstack_windows n (firstn (3 * n) rest) = Some wnl) by (rewrite HeapCtrB.nonstack_windows_firstn; exact NW).
  destruct (del_window_k_split E0 n (firstn (3 * n) rest) k0 kd0 ws' wnl KZ D NWf ltac:(rewrite firstn_length_le by lia; lia))
    as (l1 & len & l2 & wl' & I & W1 & W2 & LEN & M1 & NW' & S1 & S2 & S3 & PM).
  rewrite firstn_length_le in LEN by lia.
  destruct (HeapCtrB.wsub_one_small nw T ltac:(pose proof (Uint63.to_Z_bounded (wl nw)); lia)) as [T' E'].
  exists ws', l1, len, l2, wl'. split; [reflexivity|]. split; [exact I|].
  split. { rewrite <- W1. rewrite <- (app_nil_r (firstn (3 * n) rest)) at 1. symmetry. apply (wins_of_firstn E0 n rest []). lia. }
  split; [rewrite (HeapCtrB.wins_of_prefix E0 (pred n) ws' _ ltac:(lia)); exact W2|].
  split; [exact T'|]. split; [rewrite E', N; lia|]. split; [rewrite app_length; lia|].
  split; [apply skipn_app_exact; lia|].
  split. { rewrite <- (HeapCtrB.nonstack_windows_firstn (pred n) (ws' ++ skipn (3 * n) rest)). rewrite firstn_app, firstn_all2 by lia.
           replace (3 * pred n - length ws')%nat with 0%nat by lia. cbn [firstn]. rewrite app_nil_r. exact NW'. }
  split; [exact S1|]. split; [exact S2|]. split; [| split; [exact M1| exact PM]].
  intros x Hx. rewrite <- (firstn_skipn (3 * n) rest). apply in_or_app. apply in_app_or in Hx as [Hx|Hx]; [left; apply S3; exact Hx| right; exact Hx].
Qed.

Definition afree_stF (tl : option int) (st1 : sstate) (r : int) (h2 : list sv) (kf sh : int) : sstate :=
  let st2 := clobber st1 in
  let x := s_next st2 in
  let st3 := set_next st2 (PrimInt63.add x 1%uint63) in
  let R' := remove_opt tl (IMap.remove sh (IMap.remove kf (s_regs st3))) in
  setpc (setr (set_ops (setregs st3 R') (set_op HEAP_ID h2 (s_ops st3))) X10 (VP x wzero)) r.

Lemma stF_shape_gen : forall (S : sstate) (nx1 : int) (R2 : IMap.t region -> IMap.t region) (h : list sv) (v : sv) (r : int),
  setpc (setr (set_ops (setregs (set_next S nx1) (R2 (s_regs (set_next S nx1)))) (set_op HEAP_ID h (s_ops (set_next S nx1)))) X10 v) r
  = SS r (rf_set (s_rf S) X10 v) (s_ff S) (s_resv S) (R2 (s_regs S)) (s_facts S) (set_op HEAP_ID h (s_ops S)) (s_priv S) nx1.
Proof. intros. destruct S. reflexivity. Qed.

Lemma afree_apply_shape : forall UNIV PCz st sts, afree_apply UNIV PCz st = Some sts ->
  exists r hargs wnl st1 kf sh h1 h2 tl,
    acall_pre ASTACK (Some (UNIV, PCz)) st = Some (r, hargs, wnl, st1) /\ getr st X10 = VP kf wzero
    /\ find_twin (s_facts st) kf = Some sh /\ afree_ok st wnl kf sh = true
    /\ heap_del_window_k hargs (VP kf wzero) CtrLib.K_BLOCK = Some h1 /\ heap_del_window_k h1 (VP sh wzero) K_TWIN = Some h2
    /\ sts = [afree_stF tl st1 r h2 kf sh] /\ no_views_on (s_facts st) (s_regs st) kf sh = true
    /\ twin_consume st wnl kf sh = Some tl.
Proof.
  intros UNIV PCz st sts H. unfold afree_apply in H.
  destruct (acall_pre ASTACK (Some (UNIV, PCz)) st) as [[[[r hargs] wnl] st1]|] eqn:PRE; [|discriminate].
  destruct (getr st X10) as [|kf off| | | | | | | | |] eqn:X10E; try discriminate.
  destruct (find_twin (s_facts st) kf) as [sh|] eqn:FT; [|discriminate].
  destruct (twin_consume st wnl kf sh) as [tl|] eqn:TC; [|discriminate].
  destruct (weqb off wzero && afree_ok st wnl kf sh && no_views_on (s_facts st) (s_regs st) kf sh) eqn:CK; [|discriminate].
  apply andb_prop in CK as [CK NV]. apply andb_prop in CK as [OFF FOK]. apply weqb_eq in OFF. subst off.
  destruct (heap_del_window_k hargs (VP kf wzero) CtrLib.K_BLOCK) as [h1|] eqn:H1; [|discriminate].
  destruct (heap_del_window_k h1 (VP sh wzero) K_TWIN) as [h2|] eqn:H2; [|discriminate].
  unfold fresh in H. cbv zeta in H. cbn [fst snd s_next set_next] in H. injection H as <-.
  exists r, hargs, wnl, st1, kf, sh, h1, h2, tl. repeat (split; [reflexivity || assumption|]). exact TC.
Qed.

Lemma twin_consume_canon : forall st wl kf sh, twin_canon st wl kf sh = true -> twin_consume st wl kf sh = Some None.
Proof. intros st wl kf sh H. unfold twin_consume. rewrite H. reflexivity. Qed.

Section Free.
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
Hypothesis OPS_mo_other : forall id args m mo mo', id <> HEAP_ID -> OTHER mo mo' -> op_holds OPS id args m mo -> op_holds OPS id args m mo'.
Hypothesis OPS_cov0_img : forall a, (exists seg, find_segment asegs a 1 = Some seg) -> op_cov0 OPS a.

Lemma afree_ok_k_inv : forall (kdB kdT : w64) E st ms mo wnl kf sh, st_ok asegs OPS E st ms mo -> afree_ok_k kdB kdT st wnl kf sh = true ->
  exists rf lenf lent,
  IMap.find kf (s_regs st) = Some rf /\ CtrA.win_lookup wnl kf = Some (lenf, kdB) /\ CtrA.win_lookup wnl sh = Some (lent, kdT)
  /\ block_of_twin (s_facts st) sh = Some kf /\ rg_lo rf = 0%uint63
  /\ 0 < hiZ E rf /\ hiZ E rf <= bv_unsigned (den E lenf)
  /\ forall k len kd, In (k, len, kd) wnl -> k <> kf -> k <> sh ->
       (weqb kd K_TWIN = true /\ exists kb, block_of_twin (s_facts st) k = Some kb /\ kb <> kf)
       \/ (weqb kd K_TWIN = false /\ exists r0, IMap.find k (s_regs st) = Some r0 /\ rg_lo r0 = 0%uint63 /\ hiZ E r0 <= bv_unsigned (den E len)
             /\ 0 < hiZ E r0 /\ rg_w r0 = true /\ (kd = kdB \/ hiZ E rf = bv_unsigned (den E lenf))).
Proof.
  intros kdB kdT E st ms mo wnl kf sh HS FOKk.
  pose proof (so_facts _ _ _ _ _ _ HS) as HF. unfold afree_ok_k in FOKk. cbv zeta in FOKk.
  destruct (IMap.find kf (s_regs st)) as [rf|] eqn:Frf; [|discriminate].
  destruct (CtrA.win_lookup wnl kf) as [[lenf kdf]|] eqn:WLf; [|discriminate].
  destruct (CtrA.win_lookup wnl sh) as [[lent kdt]|] eqn:WLt; [|discriminate].
  destruct (block_of_twin (s_facts st) sh) as [kb|] eqn:BT; [|discriminate].
  do 6 (apply andb_prop in FOKk as [FOKk ?]).
  rename H into ALL, H0 into LEQ, H1 into POS, H2 into LO0, H3 into KBE, H4 into KDT.
  apply weqb_eq in FOKk. subst kdf. apply weqb_eq in KDT. subst kdt. apply Uint63.eqb_correct in KBE. subst kb. apply Uint63.eqb_correct in LO0.
  pose proof (KnownA.KnownA.known_ltu_sound E _ _ _ HF POS) as POS'. cbn [den] in POS'. rewrite wbv_unsigned, wzero_ok in POS'.
  pose proof (KnownA.KnownA.known_leu_q_sound E _ _ _ HF LEQ) as LEQ'.
  exists rf, lenf, lent. repeat (split; [reflexivity || assumption|]).
  intros k len kd Hin NKf NKs. pose proof (proj1 (forallb_forall _ _) ALL _ Hin) as X. cbv beta iota in X.
  apply Uint63.eqb_false_spec in NKf, NKs. rewrite NKf, NKs in X. cbn [orb] in X.
  destruct (weqb kd K_TWIN) eqn:KT.
  - left. split; [reflexivity|]. destruct (block_of_twin (s_facts st) k) as [kb|]; [|discriminate]. exists kb. split; [reflexivity|].
    apply negb_true_iff in X. apply Uint63.eqb_false_spec in X. exact X.
  - right. split; [reflexivity|].
    destruct (IMap.find k (s_regs st)) as [r0|] eqn:Fr0; [|discriminate]. exists r0. split; [reflexivity|].
    apply andb_prop in X as [X KB]. apply andb_prop in X as [X W]. apply andb_prop in X as [X P0]. apply andb_prop in X as [L0 LE0]. apply Uint63.eqb_correct in L0.
    pose proof (KnownA.KnownA.known_ltu_sound E _ _ _ HF P0) as P0'. cbn [den] in P0'. rewrite wbv_unsigned, wzero_ok in P0'.
    split; [exact L0|]. split; [exact (KnownA.KnownA.known_leu_q_sound E _ _ _ HF LE0)|]. split; [exact P0'|]. split; [exact W|].
    apply orb_prop in KB as [KB|FULL]; [left; apply weqb_eq; exact KB| right].
    pose proof (KnownA.KnownA.known_eq_sound E _ _ _ HF FULL) as EQ. unfold hiZ. rewrite EQ. reflexivity.
Qed.

Lemma cvu_of : forall (E : env) (st : sstate) (m : amem) (LB : blocks) nn md A nw rest,
  find_op HEAP_ID (s_ops st) = Some (VL md :: A :: VL nw :: rest) -> nn = Z.to_nat (to_Z (wl nw)) ->
  cw_holds Cw (w2Z md) (map (den E) (skipn (3 * nn) rest)) LB (wins_of E nn rest) m ->
  forall kb, In kb (carg_vecs st) -> bv_unsigned (ev E kb) <> 0 -> forall w, In w (wins_of E nn rest) -> w_kind w = K_BLOCK -> 0 < w_len w -> w_lo w <> bv_unsigned (ev E kb).
Proof.
  intros E st m LB nn md A nw rest Hf Nn HC kb Hkb NZ w Hw KW PW.
  destruct (CallA.carg_vecs_spec st md A nw rest kb Hf Hkb) as (i & Hi & NE). rewrite <- Nn in NE.
  pose proof (Cw_vec_unowned _ _ _ _ _ i (den E (VP kb wzero)) HC Hi (map_nth_error (den E) _ _ NE)) as NEQ.
  rewrite HeapCtr.den_VPz in NEQ. exact (NEQ NZ w Hw KW PW).
Qed.

Section FREED.
Variables (E : env) (st : sstate) (ms : machine_state) (mo : Model).
Hypothesis HS : st_ok asegs OPS E st ms mo.
Variables (wnl : list (int * sv * w64)) (nn : nat) (rest : list sv) (LB : blocks) (aw : word)
          (L : alayout) (RNG : footprint) (sta : astate) (LBa : list ablock).
Hypothesis NW : CtrA.nonstack_windows nn rest = Some wnl.
Hypothesis AN : CtrA.windows_anchored (s_regs st) wnl = true.
Hypothesis WF : windows_wf (wins_of E nn rest) LB (ATOP + 4096).

Variable WW : wit.
Hypothesis WOF : wit_of WW L RNG sta LBa.
Hypothesis AR : aw_realW AI ACCT UNIV aw LB (ms_mem ms) mo WW.
Hypothesis TI : ties WW (wins_of E nn rest).

Hypothesis CVU : forall kb, In kb (carg_vecs st) -> bv_unsigned (ev E kb) <> 0 -> forall w, In w (wins_of E nn rest) -> w_kind w = K_BLOCK -> 0 < w_len w -> w_lo w <> bv_unsigned (ev E kb).
Variables (kf sh : int).
Hypothesis FT : find_twin (s_facts st) kf = Some sh.
Hypothesis FOKk : afree_ok st wnl kf sh = true.
Hypothesis NV : no_views_on (s_facts st) (s_regs st) kf sh = true.
Variable tl : option int.
Hypothesis TCONS : twin_consume st wnl kf sh = Some tl.

Lemma consume_cases :
  (tl = None /\ twin_canon st wnl kf sh = true)
  \/ (exists s2, tl = Some s2 /\ twin_canon_pair st wnl kf sh = Some s2).
Proof.
  unfold twin_consume in TCONS. destruct (twin_canon st wnl kf sh) eqn:TC.
  - injection TCONS as <-. left. auto.
  - destruct (twin_canon_pair st wnl kf sh) as [s2|] eqn:TP; [|discriminate TCONS]. injection TCONS as <-. right. exists s2. auto.
Qed.
Lemma canon_pair_inv : forall s2, twin_canon_pair st wnl kf sh = Some s2 ->
  exists r n kdn lent0 kdt, IMap.find sh (s_regs st) = Some r /\ CtrA.win_lookup wnl kf = Some (n, kdn) /\ CtrA.win_lookup wnl sh = Some (lent0, kdt)
    /\ is_twin_main r n = true /\ lent0 = twin_len n /\ twins_apart (s_facts st) (s_regs st) wnl (carg_vecs st) kf sh = true
    /\ tail_scan (s_facts st) (s_regs st) sh n = Some s2 /\ no_tails_on (s_facts st) (s_regs st) sh n s2 = true /\ s2 <> kf
    /\ CtrA.win_lookup wnl s2 = None.
Proof.
  intros s2 H. unfold twin_canon_pair in H. destruct (IMap.find sh (s_regs st)) as [r|]; [|discriminate H].
  destruct (CtrA.win_lookup wnl kf) as [[n kdn]|]; [|discriminate H]. destruct (CtrA.win_lookup wnl sh) as [[lent0 kdt]|]; [|discriminate H].
  match type of H with (if ?c then _ else _) = _ => destruct c eqn:Q; [|discriminate H] end.
  apply andb_prop in Q as [Q TAP]. apply andb_prop in Q as [TM LEN]. apply sv_eqb_eq in LEN.
  destruct (tail_scan (s_facts st) (s_regs st) sh n) as [s2'|] eqn:TS; [|discriminate H].
  destruct (no_tails_on (s_facts st) (s_regs st) sh n s2' && negb (PrimInt63.eqb s2' kf)
            && match CtrA.win_lookup wnl s2' with None => true | Some _ => false end) eqn:Q2; [|discriminate H].
  injection H as <-. apply andb_prop in Q2 as [Q2 NWIN]. apply andb_prop in Q2 as [NT NKF]. apply negb_true_iff in NKF. apply Uint63.eqb_false_spec in NKF.
  destruct (CtrA.win_lookup wnl s2') eqn:WL2; [discriminate NWIN|].
  exists r, n, kdn, lent0, kdt. repeat (split; [reflexivity || assumption|]). reflexivity.
Qed.

Lemma afree_ok_inv : exists rf lenf lent,
  IMap.find kf (s_regs st) = Some rf /\ CtrA.win_lookup wnl kf = Some (lenf, CtrLib.K_BLOCK) /\ CtrA.win_lookup wnl sh = Some (lent, K_TWIN)
  /\ block_of_twin (s_facts st) sh = Some kf /\ rg_lo rf = 0%uint63
  /\ 0 < hiZ E rf /\ hiZ E rf <= bv_unsigned (den E lenf)
  /\ forall k len kd, In (k, len, kd) wnl -> k <> kf -> k <> sh ->
       (weqb kd K_TWIN = true /\ exists kb, block_of_twin (s_facts st) k = Some kb /\ kb <> kf)
       \/ (weqb kd K_TWIN = false /\ exists r0, IMap.find k (s_regs st) = Some r0 /\ rg_lo r0 = 0%uint63 /\ hiZ E r0 <= bv_unsigned (den E len)
             /\ 0 < hiZ E r0 /\ rg_w r0 = true /\ (kd = CtrLib.K_BLOCK \/ hiZ E rf = bv_unsigned (den E lenf))).
Proof. exact (afree_ok_k_inv CtrLib.K_BLOCK K_TWIN E st ms mo wnl kf sh HS FOKk). Qed.

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

Lemma AWHf : aw_holds_asan AI ACCT UNIV aw LB (ms_mem ms) mo.
Proof. exact (aw_real_holds AI ACCT UNIV _ _ _ _ _ AR). Qed.

Lemma KB1 : w2Z CtrLib.K_BLOCK = 1. Proof. reflexivity. Qed.
Lemma KT9 : w2Z K_TWIN = 9. Proof. reflexivity. Qed.

Lemma entry_window : forall k len kd, In (k, len, kd) wnl ->
  k <> 0%uint63 /\ In (Win (bv_unsigned (ev E k)) (bv_unsigned (den E len)) (w2Z kd)) (wins_of E nn rest)
  /\ exists b, In b LB /\ (forall a, in_iv (bv_unsigned (ev E k), bv_unsigned (den E len)) a -> in_iv b a)
       /\ (kd = CtrLib.K_BLOCK -> b = (bv_unsigned (ev E k), bv_unsigned (den E len))).
Proof.
  intros k len kd Hin. destruct (HeapCtrB.nonstack_windows_In E nn rest wnl k len kd NW Hin) as (K0 & _ & KD & INW).
  split; [exact K0|]. split; [exact INW|].
  pose proof (proj1 (Forall_forall _ _) WF _ INW) as (W1 & W2 & W3 & [[KS0 _]|[[KB B]|[KS2 (b & Hb & SUB)]]]); unfold w_iv in *; cbn [w_kind w_lo w_len] in *.
  - exfalso. exact (KD KS0).
  - eexists. split; [exact B|]. split; [intros a Ha; exact Ha| reflexivity].
  - exists b. split; [exact Hb|]. split; [exact SUB|]. intros ->. rewrite KB1 in KS2. unfold K_SUB in KS2. lia.
Qed.

Lemma blockLB : In (Af, nf) LB.
Proof.
  destruct (entry_window kf lenf CtrLib.K_BLOCK (HeapCtrB.win_lookup_In _ _ _ _ WLf)) as (_ & _ & b & Hb & _ & EQ). rewrite (EQ eq_refl) in Hb. exact Hb.
Qed.

Lemma nf_small : 0 <= Af /\ 1 <= nf /\ Af + nf < 2 ^ 48.
Proof.
  destruct (aw_blocks_ok_asan AI IMGX IMGX_aci ACCT UNIV AI_fake aw LB (ms_mem ms) mo (Af, nf) AWHf blockLB) as (B1 & B2 & B3 & _). cbn [fst snd] in *.
  unfold aw_ceiling_asan in B3. pose proof atop_range. unfold hiZ in *. fold nf in LEf. lia.
Qed.

Lemma consume_common : exists rs, IMap.find sh (s_regs st) = Some rs /\ rg_w rs = false /\ rg_lo rs = 0%uint63
  /\ len_is_twin (s_facts st) lent lenf = true /\ twins_apart (s_facts st) (s_regs st) wnl (carg_vecs st) kf sh = true
  /\ ((tl = None /\ is_twin_region rs lenf = true /\ size_shape_ok (s_facts st) lenf = true /\ no_tail_at (s_facts st) (s_regs st) sh lenf = true)
      \/ (exists s2, tl = Some s2 /\ is_twin_main rs lenf = true /\ tail_scan (s_facts st) (s_regs st) sh lenf = Some s2
                     /\ no_tails_on (s_facts st) (s_regs st) sh lenf s2 = true /\ s2 <> kf /\ CtrA.win_lookup wnl s2 = None)).
Proof.
  destruct consume_cases as [[-> TCAN]|(s2 & -> & TP)].
  - destruct (CallA.twin_canon_inv st wnl kf sh TCAN) as (rs & n0 & kdn & lent0 & kdt & FR & WLn & WLt0 & TR & SS0 & LEN & TAP & NTA).
    rewrite WLf in WLn. injection WLn as <- <-. rewrite WLt in WLt0. injection WLt0 as <- <-.
    exists rs. split; [exact FR|].
    pose proof TR as TR'. unfold is_twin_region in TR'. cbv zeta in TR'. do 4 (apply andb_prop in TR' as [TR' ?]).
    apply Uint63.eqb_correct in TR'. match goal with X : negb (rg_w rs) = true |- _ => apply negb_true_iff in X; rename X into RO end.
    split; [exact RO|]. split; [exact TR'|]. split; [exact LEN|]. split; [exact TAP|]. left. auto.
  - destruct (canon_pair_inv s2 TP) as (rs & n0 & kdn & lent0 & kdt & FR & WLn & WLt0 & TM & LEN & TAP & TS & NT & NKF & NWIN).
    rewrite WLf in WLn. injection WLn as <- <-. rewrite WLt in WLt0. injection WLt0 as <- <-.
    exists rs. split; [exact FR|]. destruct (CallA.region_is_inv _ _ TM) as (LO & _ & WR & _). cbn [twin_main rg_lo rg_w] in LO, WR.
    split; [exact WR|]. split; [exact LO|]. split; [rewrite LEN; apply CallA.len_is_twin_refl|]. split; [exact TAP|]. right. exists s2. repeat (split; [reflexivity || assumption|]). exact NWIN.
Qed.

Lemma twin_sh : exists rs, IMap.find sh (s_regs st) = Some rs /\ rg_w rs = false /\ len_is_twin (s_facts st) lent lenf = true
  /\ bv_unsigned (ev E sh) = shad Af /\ bv_unsigned (den E lent) = shlen (nf + 7).
Proof.

  destruct consume_common as (rs & FR & TR & _ & LEN & _).
  exists rs. split; [exact FR|]. split; [exact TR|]. split; [exact LEN|].
  destruct nf_small as (A0 & N1 & SM).
  split.
  - rewrite (CallA.block_of_twin_sound E _ sh kf (so_facts _ _ _ _ _ _ HS) BTs). fold Af. unfold shad, ASHOFF. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8.
    rewrite Z.mod_small; [lia|]. clear - A0 SM N1. Z.div_mod_to_equations. lia.
  - rewrite (CallA.len_is_twin_sound E _ _ _ (so_facts _ _ _ _ _ _ HS) LEN) by (fold nf; lia). fold nf. unfold shlen. rewrite Z.shiftr_div_pow2 by lia. reflexivity.
Qed.

Lemma owner : user_band Af /\ In (shad Af, shlen (nf + 7)) LB /\ (exists p, In (HB p Af nf) LBa /\ In (HB p Af nf) (w_T WW))
  /\ 1 <= nf <= AREQMAX /\ Af mod 16 = 0.
Proof.
  destruct twin_sh as (rs & _ & _ & _ & ESH & ELT).
  destruct (entry_window sh lent K_TWIN (HeapCtrB.win_lookup_In _ _ _ _ WLt)) as (_ & INW & _). rewrite ESH, ELT, KT9 in INW.

  destruct TI as (_ & T2 & _). destruct (T2 _ INW eq_refl) as (b & HbT & EIV). unfold w_iv, twin_iv in EIV. cbn [w_lo w_len] in EIV. injection EIV as ESA ESL.
  destruct AR as [HWw EMw]. destruct WOF as (_ & _ & _ & ELB).
  destruct (twin_owner_w AI ACCT UNIV AI_fake WW aw LB (ms_mem ms) mo b Af nf HWw HbT blockLB ESA) as (EA & EN & NR).
  destruct (twin_T_facts AI ACCT UNIV WW aw LB (ms_mem ms) mo b HWw HbT) as (HbL & _ & _ & HTW & (p & EB) & _ & AL & UB & _).
  unfold twin_iv in HTW. rewrite <- EA, <- EN in HTW. rewrite <- EA in AL, UB. rewrite <- EN in NR. rewrite <- EA, <- EN in EB.
  split; [exact UB|]. split; [exact HTW|]. split; [| split; [exact NR| exact AL]].
  exists p. rewrite <- EB. split; [rewrite <- ELB; exact HbL| exact HbT].
Qed.

Lemma freed_pattern : ablock_shadow (ms_mem ms) Af nf.
Proof.
  destruct twin_sh as (rs & Frs & _ & _ & ESH & _). destruct owner as (UBf & HTf & (p0 & HPL & HPT) & NRf & ALf).
  destruct (entry_window sh lent K_TWIN (HeapCtrB.win_lookup_In _ _ _ _ WLt)) as (SH0 & _).
  assert (SHNZ : PrimInt63.eqb sh 0%uint63 = false) by (apply Uint63.eqb_false_spec; exact SH0).
  intros g G0 G1.
  assert (P1 : rb asegs (ms_mem ms) (shad Af + g) = Some (Z_to_bv 8 (if 8 * g + 8 <=? nf then 0 else nf - 8 * g))).
  { destruct consume_common as (rs' & Frs' & _ & _ & _ & _ & [(_ & TRs & SS & _)|(s2 & _ & TM & TS & _)]); rewrite Frs in Frs'; injection Frs' as <-.
    - pose proof (so_reg _ _ _ _ _ _ HS sh rs Frs) as RO.
      pose proof (CallA.size_shape_sound E _ lenf (so_facts _ _ _ _ _ _ HS) SS) as SHAPE.
      pose proof (CallA.is_twin_region_sound asegs (s_priv st) E (ms_mem ms) sh rs lenf RO SHNZ TRs) as PATR. fold nf in PATR. rewrite ESH in PATR.
      apply PATR; [unfold AREQMAX in NRf; lia| | exact G0| exact G1]. destruct lenf; try exact I; exact SHAPE.
    -
      pose proof (CallA.twin_pair_sound asegs (s_priv st) E (ms_mem ms) (s_facts st) (s_regs st) sh rs lenf s2 (so_facts _ _ _ _ _ _ HS)
                    (so_reg _ _ _ _ _ _ HS) Frs SHNZ TM TS) as PATP.
      fold nf in PATP. rewrite ESH in PATP. apply PATP; [clear - NRf; lia| | exact G0| exact G1].
      destruct nf_small as (A0 & N1 & SM). unfold shad, ASHOFF. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8. clear - A0 N1 SM. Z.div_mod_to_equations. lia. }

  destruct AR as [HWw _]. pose proof HWw as (_ & _ & _ & _ & _ & _ & _ & MAP & _).
  assert (MP : ms_mem ms (ALib.Mem.wa (shad Af + g)) <> None).
  { apply MAP. apply in_ivs_In. exists (twin_iv (HB p0 Af nf)). split; [apply in_map; exact HPT|].
    unfold in_iv, twin_iv. cbn [fst snd ab_addr ab_size]. unfold shlen. rewrite Z.shiftr_div_pow2 by lia. change (2^3) with 8. clear -G0 G1. Z.div_mod_to_equations. lia. }
  unfold rb in P1. unfold ALib.Mem.wa in *. destruct (ms_mem ms (Z_to_bv 64 (shad Af + g))) as [y|]; [exact P1| contradiction].
Qed.

Lemma twin_cover : forall a, in_iv (shad Af, shlen (nf + 7)) a ->
  exists kx rx, IMap.find kx (s_regs st) = Some rx /\ PrimInt63.eqb kx 0%uint63 = false /\ rg_w rx = false
    /\ bv_unsigned (ev E kx) + loZ rx <= a < bv_unsigned (ev E kx) + hiZ E rx.
Proof.
  intros a Ha. unfold in_iv, shlen in Ha. cbn [fst snd] in Ha. rewrite Z.shiftr_div_pow2 in Ha by lia. change (2 ^ 3) with 8 in Ha.
  destruct twin_sh as (rs & Frs & ROs & _ & ESH & _). destruct nf_small as (A0 & N1 & SM).
  destruct (entry_window sh lent K_TWIN (HeapCtrB.win_lookup_In _ _ _ _ WLt)) as (SH0 & _).
  assert (SHNZ : PrimInt63.eqb sh 0%uint63 = false) by (apply Uint63.eqb_false_spec; exact SH0).
  assert (KZ0 : keyZ 0%uint63 = 0) by reflexivity.
  destruct consume_common as (rs' & Frs' & _ & LOs & _ & _ & [(_ & TRs & _)|(s2 & _ & TM & TS & _)]); rewrite Frs in Frs'; injection Frs' as <-.
  - exists sh, rs. split; [exact Frs|]. split; [exact SHNZ|]. split; [exact ROs|].
    unfold is_twin_region in TRs. cbv zeta in TRs. do 4 (apply andb_prop in TRs as [TRs ?]).
    match goal with X : sv_eqb (rg_hi rs) _ = true |- _ => apply sv_eqb_eq in X; rewrite CallA.twin_region_hi in X; rename X into HIs end.
    unfold loZ, hiZ. rewrite LOs, HIs, (CallA.twin_len_den E lenf) by (fold nf; lia). fold nf. rewrite KZ0, ESH. lia.
  - destruct (CallA.region_is_inv _ _ TM) as (_ & HIm & _). cbn [twin_main rg_hi] in HIm.
    destruct (Z_lt_ge_dec a (shad Af + (nf - 1) / 8)) as [LT|GE].
    + exists sh, rs. split; [exact Frs|]. split; [exact SHNZ|]. split; [exact ROs|].
      unfold loZ, hiZ. rewrite LOs, HIm, CallA.sz_last_den by (fold nf; exact N1). fold nf. rewrite KZ0, ESH. lia.
    + destruct (CallA.tail_scan_inv _ _ _ _ _ TS) as (FTL & S0 & _ & r2 & F2 & TR2).
      destruct (CallA.region_is_inv _ _ TR2) as (LO2 & HI2 & WR2 & _). destruct (CallA.tail_region_fields lenf) as (TLO & THI & TWR & _).
      rewrite TLO in LO2. rewrite THI in HI2. rewrite TWR in WR2.
      assert (B : bv_unsigned (ev E sh) + (bv_unsigned (den E lenf) - 1) / 8 < 2 ^ 64).
      { fold nf. rewrite ESH. unfold shad, ASHOFF. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8. clear - A0 N1 SM. Z.div_mod_to_equations. lia. }
      pose proof (CallA.find_tail_sound E _ sh lenf s2 (so_facts _ _ _ _ _ _ HS) FTL) as EV. apply (f_equal bv_unsigned) in EV.
      rewrite (CallA.tail_rhs_den E sh lenf ltac:(fold nf; exact N1) B) in EV. fold nf in EV. rewrite ESH in EV.
      exists s2, r2. split; [exact F2|]. split; [apply Uint63.eqb_false_spec; exact S0|]. split; [exact WR2|].
      unfold loZ, hiZ. rewrite LO2, HI2, KZ0, EV. cbn [den]. rewrite wbv_unsigned. change (w2Z wone) with 1. clear - Ha GE N1. Z.div_mod_to_equations. lia.
Qed.

Lemma region_first_byte : forall k r0, IMap.find k (s_regs st) = Some r0 -> rg_lo r0 = 0%uint63 -> 0 < hiZ E r0 ->
  bv_unsigned (ev E k) + loZ r0 <= bv_unsigned (ev E k) < bv_unsigned (ev E k) + hiZ E r0.
Proof. intros k r0 _ L0 P. unfold loZ. rewrite L0. assert (KZ0 : keyZ 0%uint63 = 0) by reflexivity. rewrite KZ0. lia. Qed.

Lemma kept_block_w : forall k len kd r0 b, In (k, len, kd) wnl -> k <> kf -> k <> sh ->
  IMap.find k (s_regs st) = Some r0 -> rg_lo r0 = 0%uint63 -> hiZ E r0 <= bv_unsigned (den E len) -> 0 < hiZ E r0 -> rg_w r0 = true ->
  (kd = CtrLib.K_BLOCK \/ hiZ E rf = nf) ->
  In b LB -> (forall a, in_iv (bv_unsigned (ev E k), bv_unsigned (den E len)) a -> in_iv b a) ->
  b <> (Af, nf) /\ b <> (shad Af, shlen (nf + 7)).
Proof.
  intros k len kd r0 b Hin NKf NKs Fr0 L0 LE0 P0 W0 CASE Hb SUB.
  destruct (entry_window k len kd Hin) as (K0 & _ & b1 & Hb1 & SUB1 & EQ1).
  destruct (entry_window kf lenf CtrLib.K_BLOCK (HeapCtrB.win_lookup_In _ _ _ _ WLf)) as (Kf0 & _).
  destruct (entry_window sh lent K_TWIN (HeapCtrB.win_lookup_In _ _ _ _ WLt)) as (Ks0 & _).
  assert (ZK : PrimInt63.eqb k 0%uint63 = false) by (apply Uint63.eqb_false_spec; exact K0).
  assert (ZF : PrimInt63.eqb kf 0%uint63 = false) by (apply Uint63.eqb_false_spec; exact Kf0).
  assert (ZS : PrimInt63.eqb sh 0%uint63 = false) by (apply Uint63.eqb_false_spec; exact Ks0).
  assert (A0IN : in_iv (bv_unsigned (ev E k), bv_unsigned (den E len)) (bv_unsigned (ev E k))) by (unfold in_iv; cbn [fst snd]; lia).
  pose proof (SUB _ A0IN) as INB. pose proof (region_first_byte k r0 Fr0 L0 P0) as RK.
  split; intros ->.
  -
    unfold in_iv in INB. cbn [fst snd] in INB.
    assert (INF : bv_unsigned (ev E kf) + loZ rf <= bv_unsigned (ev E k) < bv_unsigned (ev E kf) + hiZ E rf).
    { unfold loZ. rewrite LO0. assert (KZ0 : keyZ 0%uint63 = 0) by reflexivity. rewrite KZ0. fold Af. destruct CASE as [->|FULL]; [| lia].

      pose proof (EQ1 eq_refl) as E1. subst b1.
      destruct (Z.eq_dec (bv_unsigned (ev E k)) Af) as [EA|NA]; [lia| exfalso].
      apply (aw_blocks_disj_asan AI ACCT UNIV AI_fake aw LB (ms_mem ms) mo _ (Af, nf) (bv_unsigned (ev E k)) AWHf Hb1 blockLB); [cbn [fst]; exact NA| exact A0IN|].
      unfold in_iv. cbn [fst snd]. lia. }
    exact (so_disj _ _ _ _ _ _ HS k r0 kf rf Fr0 Frf NKf ZK ZF (or_introl W0) _ (conj RK INF)).
  -
    destruct (twin_cover (bv_unsigned (ev E k)) INB) as (kx & rx & Fx & ZX & WX & INS).
    assert (NKx : k <> kx) by (intros ->; rewrite Fr0 in Fx; injection Fx as <-; rewrite W0 in WX; discriminate WX).
    exact (so_disj _ _ _ _ _ _ HS k r0 kx rx Fr0 Fx NKx ZK ZX (or_introl W0) _ (conj RK INS)).
Qed.

Lemma kept_block : forall k len kd b, In (k, len, kd) wnl -> k <> kf -> k <> sh ->
  In b LB -> (forall a, in_iv (bv_unsigned (ev E k), bv_unsigned (den E len)) a -> in_iv b a) ->
  b <> (Af, nf) /\ b <> (shad Af, shlen (nf + 7)).
Proof.
  intros k len kd b Hin NKf NKs Hb SUB.
  destruct (OTHERS k len kd Hin NKf NKs) as [[KT (kb & BTk & NKB)]|(KT & r0 & Fr0 & L0 & LE0 & P0 & W0 & CASE)].
  2:{ exact (kept_block_w k len kd r0 b Hin NKf NKs Fr0 L0 LE0 P0 W0 CASE Hb SUB). }

  destruct consume_common as (rsC & _ & _ & _ & _ & TAP & _).
  destruct (CallA.twins_apart_inv _ _ _ _ _ _ k len kd TAP Hin KT NKs) as [OLD|EVA].
  2:{ destruct (CallV.twin_ev_cases E _ _ _ _ _ _ _ (so_facts _ _ _ _ _ _ HS) EVA) as (kb2 & BT2 & LW & AL & EVD).
      rewrite BTk in BT2. injection BT2 as <-.
      pose proof (GTwinSub.GTwinSub.mod8_of_align E _ kb (so_facts _ _ _ _ _ _ HS) AL) as K8.

      destruct (entry_window k len kd Hin) as (_ & INWk & _). apply weqb_eq in KT. subst kd. rewrite KT9 in INWk.
      destruct TI as (_ & T2 & _). destruct (T2 _ INWk eq_refl) as (b2 & Hb2T & EIV). unfold w_iv in EIV. cbn [w_lo w_len] in EIV.
      pose proof AR as [HWw _].
      destruct (twin_T_facts AI ACCT UNIV WW aw LB (ms_mem ms) mo b2 HWw Hb2T) as (_ & _ & _ & _ & _ & NR2 & AL2 & UB2 & NUB2).
      assert (EB : b = twin_iv b2).
      { apply (twin_container AI ACCT UNIV AI_fake WW aw LB (ms_mem ms) mo b2 b HWw Hb2T Hb). rewrite <- EIV. exact SUB. }
      unfold twin_iv in EIV. injection EIV as ESA ESL.
      destruct owner as (UBf & HTf & _ & NRf & ALf).
      subst b. unfold twin_iv. split.
      - intros X. apply (f_equal fst) in X. cbn [fst] in X. apply NUB2. rewrite X. exact UBf.
      - intros X. injection X as XA XL.

        destruct nf_small as (A0 & N1 & SM).
        pose proof (CallA.block_of_twin_sound E _ k kb (so_facts _ _ _ _ _ _ HS) BTk) as LK.
        pose proof (bv_unsigned_in_range 64 (ev E kb)) as RKB. change (bv_modulus 64) with (2 ^ 64) in RKB.
        rewrite Z.mod_small in LK by (clear - RKB; Z.div_mod_to_equations; lia).
        assert (EKB : bv_unsigned (ev E kb) = Af).
        { rewrite ESA, XA in LK. unfold shad, ASHOFF in LK. rewrite Z.shiftr_div_pow2 in LK by lia. change (2 ^ 3) with 8 in LK.
          clear - LK K8 ALf. Z.div_mod_to_equations. lia. }
        destruct EVD as [CVk|(ks & lens & kds & rsub & Hins & NXs & NKBs & NKTs & Frsub & RWs & L0s & HPOS & XLO & XHI)].
        {
          destruct (HeapCtrB.nonstack_windows_In E nn rest wnl kf lenf CtrLib.K_BLOCK NW (HeapCtrB.win_lookup_In _ _ _ _ WLf)) as (_ & _ & _ & INk).
          assert (AFNZ : Af <> 0).
          { destruct owner as (_ & _ & (p0 & HP0 & _) & _). pose proof AR as [(AH0 & _) _]. destruct WOF as (_ & _ & _ & E4w). rewrite E4w in AH0.
            destruct (heap_block_facts AI _ _ _ _ _ (HB p0 Af nf) AH0 HP0 ltac:(exists p0; reflexivity)) as (_ & (BK0 & _) & _). unfold ablk, AIMG_HI, KLS in BK0. cbn [ab_addr ab_size] in BK0. lia. }
          apply (CVU kb CVk ltac:(rewrite EKB; exact AFNZ) _ INk); [reflexivity| cbn [w_len]; fold nf; lia| cbn [w_lo]; fold Af; symmetry; exact EKB]. }
        assert (XIN : Af <= bv_unsigned (ev E ks) < Af + nf).
        { rewrite ESL, XL in XHI. rewrite EKB in XLO, XHI. unfold shlen in XHI. rewrite Z.shiftr_div_pow2 in XHI by lia. change (2 ^ 3) with 8 in XHI.
          clear - XLO XHI N1. Z.div_mod_to_equations. lia. }
        destruct (entry_window ks lens kds Hins) as (Ks0 & _).
        destruct (entry_window kf lenf CtrLib.K_BLOCK (HeapCtrB.win_lookup_In _ _ _ _ WLf)) as (Kf0 & _).
        assert (ZKs : PrimInt63.eqb ks 0%uint63 = false) by (apply Uint63.eqb_false_spec; exact Ks0).
        assert (ZF : PrimInt63.eqb kf 0%uint63 = false) by (apply Uint63.eqb_false_spec; exact Kf0).
        assert (NSs : ks <> sh).
        { intros ->. destruct twin_sh as (rs & Frs & RO & _). rewrite Frsub in Frs. injection Frs as <-. rewrite RWs in RO. discriminate RO. }
        destruct (OTHERS ks lens kds Hins NXs NSs) as [[KTs _]|(_ & r0s & Fr0s & _ & _ & _ & _ & CASEs)]; [rewrite NKTs in KTs; discriminate KTs|].
        destruct CASEs as [KB|FULL]; [exact (NKBs KB)|].
        pose proof (region_first_byte ks rsub Frsub L0s HPOS) as RKs.
        assert (INF : bv_unsigned (ev E kf) + loZ rf <= bv_unsigned (ev E ks) < bv_unsigned (ev E kf) + hiZ E rf).
        { unfold loZ. rewrite LO0. assert (KZ0 : keyZ 0%uint63 = 0) by reflexivity. rewrite KZ0. fold Af. rewrite FULL. fold nf. lia. }
        exact (so_disj _ _ _ _ _ _ HS ks rsub kf rf Frsub Frf NXs ZKs ZF (or_introl RWs) _ (conj RKs INF)). }
  destruct (CallA.twin_arm_old_inv _ _ _ _ _ OLD) as (kb' & rk & n2 & BT2 & FRk & WL2 & LEN2 & _).
  rewrite BTk in BT2. injection BT2 as <-.
  pose proof (HeapCtrB.win_lookup_In _ _ _ _ WL2) as IN2.
  assert (NKBs : kb <> sh). { intros ->. rewrite WLt in WL2. apply (f_equal (fun o => match o with Some (_, kd0) => w2Z kd0 | None => 0 end)) in WL2. vm_compute in WL2. discriminate WL2. }
  destruct (entry_window kb n2 CtrLib.K_BLOCK IN2) as (Kb0 & _ & b2 & Hb2 & SUB2 & EQ2). pose proof (EQ2 eq_refl) as E2. subst b2.
  set (A2 := bv_unsigned (ev E kb)) in *. set (N2 := bv_unsigned (den E n2)) in *.

  destruct (OTHERS kb n2 CtrLib.K_BLOCK IN2 NKB NKBs) as [[X _]|(_ & r2 & Fr2 & L2 & LE2 & P2 & W2 & CASE2)]; [discriminate X|].
  destruct (kept_block_w kb n2 CtrLib.K_BLOCK r2 (A2, N2) IN2 NKB NKBs Fr2 L2 LE2 P2 W2 CASE2 Hb2 ltac:(intros a Ha; exact Ha)) as [NEB _].
  destruct (aw_blocks_ok_asan AI IMGX IMGX_aci ACCT UNIV AI_fake aw LB (ms_mem ms) mo (A2, N2) AWHf Hb2) as (B1 & B2 & B3 & _). cbn [fst snd] in B1, B2, B3.
  unfold aw_ceiling_asan in B3. pose proof atop_range as ATR.
  assert (N2pos : 1 <= N2) by (unfold hiZ in *; fold N2 in LE2; lia).
  assert (EK : bv_unsigned (ev E k) = shad A2).
  { rewrite (CallA.block_of_twin_sound E _ k kb (so_facts _ _ _ _ _ _ HS) BTk). fold A2. unfold shad, ASHOFF. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8.
    rewrite Z.mod_small; [lia|]. clear - B1 B3 N2pos ATR. Z.div_mod_to_equations. lia. }
  assert (EL : bv_unsigned (den E len) = shlen (N2 + 7)).
  { rewrite (CallA.len_is_twin_sound E _ _ _ (so_facts _ _ _ _ _ _ HS) LEN2) by (fold N2; lia). fold N2. unfold shlen. rewrite Z.shiftr_div_pow2 by lia. reflexivity. }
  rewrite EK, EL in SUB.

  destruct (entry_window k len kd Hin) as (_ & INWk & _). rewrite EK, EL in INWk. apply weqb_eq in KT. subst kd. rewrite KT9 in INWk.
  destruct TI as (_ & T2 & _). destruct (T2 _ INWk eq_refl) as (b2 & Hb2T & EIV). unfold w_iv, twin_iv in EIV. cbn [w_lo w_len] in EIV. injection EIV as ESA ESL.
  pose proof AR as [HWw _].
  destruct (twin_owner_w AI ACCT UNIV AI_fake WW aw LB (ms_mem ms) mo b2 A2 N2 HWw Hb2T Hb2 ESA) as (EA2 & EN2 & NR2).
  destruct (twin_T_facts AI ACCT UNIV WW aw LB (ms_mem ms) mo b2 HWw Hb2T) as (_ & _ & _ & _ & _ & _ & AL2 & UB2 & NUB2).
  rewrite <- EA2 in AL2, NUB2.

  assert (EB : b = (shad A2, shlen (N2 + 7))).
  { rewrite EA2, EN2. apply (twin_container AI ACCT UNIV AI_fake WW aw LB (ms_mem ms) mo b2 b HWw Hb2T Hb). unfold twin_iv. rewrite <- EA2, <- EN2. exact SUB. }
  destruct owner as (UBf & HTf & _ & NRf & ALf).
  subst b. split.
  - intros X. apply (f_equal fst) in X. cbn [fst] in X. apply NUB2. rewrite X. exact UBf.
  - intros X. apply (f_equal fst) in X. cbn [fst] in X. apply NEB.
    assert (EA : A2 = Af) by (unfold shad in X; rewrite !Z.shiftr_div_pow2 in X by lia; change (2 ^ 3) with 8 in X; clear - X AL2 ALf; Z.div_mod_to_equations; lia).
    rewrite EA in *. f_equal. exact (LB_same_addr AI ACCT UNIV AI_fake WW aw LB (ms_mem ms) mo Af N2 nf HWw Hb2 blockLB).
Qed.

Variables (p : aptr) (RNG' : footprint) (sta' : astate) (m' : amem) (mo' : Model).
Hypothesis HP : In (HB p Af nf) LBa.
Hypothesis AH' : AHEAP AI L RNG' sta' (lb_remove p LBa) m'.
Hypothesis AC' : ACCT aw L RNG' sta' (lb_remove p LBa) mo'.
Hypothesis PRSF : aprist sta -> aprist sta'.
Let sp : Z := bv_unsigned (AP.getr (ms_regs ms) 2%bv).
Hypothesis PRES : aheap_pres (aci AI) (lb_remove p LBa) sp (ms_mem ms) m'.
Hypothesis TWP : twins_pres (lb_remove p LBa) (ms_mem ms) m'.
Definition LBk : blocks := LB_free LB Af nf.

Definition Wf : wit := mkWit (w_L WW) RNG' sta' (lb_remove p (w_LBa WW))
                             (List.filter (fun x => if ablock_eq_dec x (HB p Af nf) then false else true) (w_T WW)) (w_FA WW) m' (w_zc WW).
Lemma AR'f : aw_realW AI ACCT UNIV aw LBk m' mo' Wf.
Proof.
  destruct WOF as (E1 & E2 & E3 & E4).
  apply (aw_real_free AI ACCT UNIV AI_fake aw aw LB (ms_mem ms) mo WW RNG' sta' p Af nf m' mo' sp AR); rewrite ?E1, ?E4; assumption.
Qed.

Lemma SBf : forall a, 0 <= a < 2 ^ 64 -> CtrFrame.stableA AI ms LBk a -> m' (ALib.Mem.wa a) = ms_mem ms (ALib.Mem.wa a).
Proof.
  intros a Ha ST. destruct WOF as (E1 & E2 & E3 & E4). pose proof AR'f as [HWf _]. pose proof AR as [HWw EMw]. pose proof HWw as (AH & _).
  assert (HPw : In (HB p Af nf) (w_LBa WW)) by (rewrite E4; exact HP).
  destruct (LB_classify AI ACCT UNIV AI_fake Wf aw LBk m' mo' HWf) as (KU & KT).
  apply (aw_real_stable AI ACCT UNIV AI_fake aw LB (ms_mem ms) mo WW RNG' sta' (lb_remove p LBa) m' (lb_remove p LBa) LBk sp (lb_remove p LBa) TWP ltac:(intros b _ Hb _; exact Hb) AR);
    [rewrite E1; exact AH'| exact PRES| | | exact Ha| exact ST].
  - intros v Hv UB P. destruct (KU v Hv UB P) as (b & Vb & ->). exists b. split; [| reflexivity].
    pose proof (proj1 Vb) as X. unfold Wf in X. cbn [w_LBa] in X. rewrite E4 in X. exact X.
  - intros v Hv NUB. destruct (KT v Hv NUB) as [(b & Hb & ->)|(b & Vb & ->)].
    + left. exists b. pose proof HWf as (_ & HTf & _). destruct (HTf b Hb) as [HbL' HH]. unfold Wf in HbL'. cbn [w_LBa] in HbL'.
      split; [exact (proj1 (proj1 (lb_remove_In AI _ _ _ _ _ p Af nf b AH HPw) HbL'))|]. split; [rewrite <- E4; exact HbL'|]. split; [exact HH| reflexivity].
    + right. exists b. destruct Vb as [[HbL' NF] HF]. unfold Wf in HbL'. cbn [w_LBa] in HbL'.
      split; [exact (proj1 (proj1 (lb_remove_In AI _ _ _ _ _ p Af nf b AH HPw) HbL'))|]. split; [rewrite <- E4; exact HbL'|]. split; [exact HF| reflexivity].
Qed.

Lemma SBVf : forall a, 0 <= a < 2 ^ 64 -> CtrFrame.stableA AI ms LBk a ->
  rb asegs m' a = rb asegs (ms_mem ms) a /\ (wb asegs (ms_mem ms) a = true -> wb asegs m' a = true).
Proof. exact (CtrFrame.SBV_of_raw (CtrFrame.stableA AI ms LBk) (ms_mem ms) m' SBf). Qed.
Lemma WBMf : forall a, 0 <= a < two64 -> (in_ranges (aci AI) a \/ (exists a', in_ranges (aci AI) a' /\ a = shad a') \/ (exists a', ATOP <= a' < 2 ^ 47 /\ a = shad a')) ->
  wb asegs (ms_mem ms) a = true -> wb asegs m' a = true.
Proof. exact (CtrFrame.WBM_of_pres AI _ _ _ _ PRES). Qed.

Definition KEEPf (k0 : int) : Prop := k0 <> kf /\ k0 <> sh /\ tl <> Some k0.

Lemma WINKf : forall k0 len kd, KEEPf k0 -> CtrA.win_lookup wnl k0 = Some (len, kd) ->
  forall a, bv_unsigned (ev E k0) <= a < bv_unsigned (ev E k0) + bv_unsigned (den E len) -> in_user LBk a.
Proof.
  intros k0 len kd (NKf & NKs & _) WL a Ha. pose proof (HeapCtrB.win_lookup_In _ _ _ _ WL) as Hin.
  destruct (entry_window k0 len kd Hin) as (_ & _ & b & Hb & SUB & _).
  destruct (kept_block k0 len kd b Hin NKf NKs Hb SUB) as [N1 N2].
  apply in_ivs_In. exists b. split; [apply LB_free_In; auto|]. apply SUB. unfold in_iv. cbn [fst snd]. lia.
Qed.

Lemma VKEEPf : forall k0 rg hs n sh' len, IMap.find k0 (s_regs st) = Some rg -> zero_view rg = Some hs -> KEEPf k0 ->
  block_of_twin (s_facts st) k0 = Some n -> CallV.view_parent (s_facts st) (s_regs st) n sh' ->
  CtrA.win_lookup wnl sh' = Some (len, K_TWIN) -> KEEPf sh'.
Proof.
  intros k0 rg hs n sh' len Fk ZV (NKf & NKs & _) BT VPAR WL. split; [| split].
  - intros ->. rewrite WLf in WL. assert (X : CtrLib.K_BLOCK = K_TWIN) by congruence. vm_compute in X. discriminate X.
  - intros ->. unfold no_views_on in NV.
    pose proof (proj1 (IMap.forallb_spec _ _ (so_bst _ _ _ _ _ _ HS)) NV k0 rg Fk) as C. cbv beta in C.
    replace (PrimInt63.eqb k0 sh) with false in C by (symmetry; apply Uint63.eqb_false_spec; exact NKs).
    rewrite ZV, BT in C. destruct VPAR as [(kb & o1 & UB & TW)|(rshp & Frshp & HNp)];
      [rewrite UB, TW, Uint63.eqb_refl in C; cbn in C; discriminate C| rewrite Frshp, HNp in C; cbn [negb] in C; rewrite !Bool.andb_false_r in C; discriminate C].
  -
    destruct consume_common as (rs & _ & _ & _ & _ & _ & [(-> & _)|(s2 & -> & _ & _ & _ & _ & NWIN)]); [discriminate|].
    intros X. injection X as ->. rewrite NWIN in WL. discriminate WL.
Qed.

Lemma TKEEPf : forall k0 rg sh' kb n len, IMap.find k0 (s_regs st) = Some rg -> KEEPf k0 -> CtrA.win_lookup wnl sh' = Some (len, K_TWIN) ->
  block_of_twin (s_facts st) sh' = Some kb -> CtrA.win_lookup wnl kb = Some (n, CtrLib.K_BLOCK) ->
  size_tail_ok (s_facts st) n = true -> tail_named (tail_rhs sh' n) k0 (s_facts st) = true -> KEEPf sh'.
Proof.
  intros k0 rg sh' kb n len Fk (NKf & NKs & NTL) WL BT WLk ST TN. split; [| split].
  - intros ->. rewrite WLf in WL. assert (X : CtrLib.K_BLOCK = K_TWIN) by congruence. vm_compute in X. discriminate X.
  - intros ->. rewrite BTs in BT. injection BT as <-. rewrite WLf in WLk. injection WLk as <-.
    destruct consume_common as (rs & _ & _ & _ & _ & _ & [(_ & _ & _ & NTA)|(s2 & ETL & _ & _ & NT & _)]).
    + exfalso. exact (CallA.no_tail_at_sound _ _ _ _ k0 rg (so_bst _ _ _ _ _ _ HS) NTA Fk TN).
    + unfold no_tails_on in NT. pose proof (proj1 (IMap.forallb_spec _ _ (so_bst _ _ _ _ _ _ HS)) NT k0 rg Fk) as C. cbv beta in C.
      rewrite TN in C. cbn [negb] in C. rewrite orb_false_r in C. apply Uint63.eqb_correct in C. subst k0. exact (NTL ETL).
  - destruct consume_common as (rs & _ & _ & _ & _ & _ & [(-> & _)|(s2 & -> & _ & _ & _ & _ & NWIN)]); [discriminate|].
    intros X. injection X as ->. rewrite NWIN in WL. discriminate WL.
Qed.
Lemma SBTf : forall a, 0 <= a < 2 ^ 64 -> sh_cov a -> in_based E (s_regs st) a ->
  rb asegs m' a = rb asegs (ms_mem ms) a /\ (wb asegs (ms_mem ms) a = true -> wb asegs m' a = true).
Proof.
  intros a Ha SC _. apply (FrameV.frame_v_of_raw asegs).
  destruct SC as [(a' & R & ->)|(v & Hv & R)].
  - exact (proj1 (PRES (shad a') Ha ltac:(right; right; right; exists a'; split; [left; exact R| reflexivity]))).
  - destruct (IMGSH_aci v a Hv R) as (a' & INA & ->).
    exact (proj1 (PRES (shad a') Ha ltac:(right; right; right; exists a'; split; [right; left; exact INA| reflexivity]))).
Qed.

Variables (hargs : list sv) (md : w64) (A : sv) (nw : w64).
Hypothesis Hf : find_op HEAP_ID (s_ops st) = Some hargs.
Hypothesis Eh : hargs = VL md :: A :: VL nw :: rest.
Hypothesis Tnw : wt nw = false.
Hypothesis Nn : nn = Z.to_nat (to_Z (wl nw)).
Hypothesis Ln : (3 * nn <= length rest)%nat.
Hypothesis FOK : fresh_ok st = true.
Variables (Fv : Z -> word) (Gv : Z -> Z -> byte).
Notation E' := (CtrFrame.E' E st Fv Gv).
Lemma SBOf : forall o a, In o (s_ops st) -> not_id HEAP_ID o -> 0 <= a < two64 ->
  Exists (fun iv => fst iv <= a < snd iv) (op_fp OPS (op_id o) (map (den E') (op_args o))) -> m' (Z_to_bv 64 a) = ms_mem ms (Z_to_bv 64 a).
Proof.
  intros o a Ho NI Ha FP. unfold not_id in NI. apply Uint63.eqb_false_spec in NI. destruct (OPS_fp_other _ _ a NI FP) as [R|[(a' & R & ->)|(a' & R & ->)]].
  - pose proof (SBf a ltac:(unfold two64 in Ha; lia) ltac:(right; left; exact R)) as E1. unfold ALib.Mem.wa in E1. exact E1.
  - pose proof (proj1 (PRES (shad a') ltac:(unfold two64 in Ha; lia) ltac:(right; right; right; exists a'; split; [right; left; exact R| reflexivity]))) as E1.
    unfold ALib.Mem.wa in E1. exact E1.
  - pose proof (proj1 (PRES (shad a') ltac:(unfold two64 in Ha; lia) ltac:(right; right; right; exists a'; split; [left; exact R| reflexivity]))) as E1.
    unfold ALib.Mem.wa in E1. exact E1.
Qed.
Variables (h1 h2 : list sv).
Hypothesis H1 : heap_del_window_k hargs (VP kf wzero) CtrLib.K_BLOCK = Some h1.
Hypothesis H2 : heap_del_window_k h1 (VP sh wzero) K_TWIN = Some h2.

Definition WBf : window := Win Af nf K_BLOCK.
Definition WTf : window := Win (shad Af) (shlen (nf + 7)) K_TWINz.

Lemma forallb_sub : forall {T} (f : T -> bool) l l', (forall x, In x l' -> In x l) -> forallb f l = true -> forallb f l' = true.
Proof. intros T f l l' SUB H. apply forallb_forall. intros x Hx. exact (proj1 (forallb_forall _ _) H x (SUB x Hx)). Qed.

Lemma forallb_skipn : forall {T} (f : T -> bool) j l, forallb f l = true -> forallb f (skipn j l) = true.
Proof.
  intros T f j. induction j as [|j IH]; intros l H; [exact H|]. destruct l as [|x l]; [reflexivity|]. cbn [skipn]. cbn [forallb] in H.
  apply andb_prop in H as [_ H]. exact (IH l H).
Qed.

Lemma anchors_perm : forall (l l' : list (int * sv * w64)), Permutation l l' -> Permutation (HeapCtrB.anchors l) (HeapCtrB.anchors l').
Proof. intros l l' P. unfold HeapCtrB.anchors. apply Permutation_map. exact P. Qed.

Lemma DEL2 : exists l1 l2 m1 m2,
  decode (map (den E') h2) = Some (w2Z md, den E A, m1 ++ m2, map (den E) (skipn (3 * nn) rest))
  /\ wins_of E nn rest = l1 ++ WBf :: l2 /\ l1 ++ l2 = m1 ++ WTf :: m2
  /\ ~ In WBf (l1 ++ l2) /\ ~ In WTf (m1 ++ m2).
Proof.
  pose proof (HeapCtrB.windows_anchored_nodup_anchors _ _ AN) as NDA.
  rewrite Eh in H1.
  destruct (heap_del_window_k_facts E md A nw rest nn kf CtrLib.K_BLOCK h1 wnl eq_refl Tnw Nn Ln NW H1)
    as (ws1 & l1 & len1 & l2 & wl1 & EH1 & I1 & W1 & W1' & T1 & N1 & L1 & SK1 & NW1 & S1 & S2 & S3 & M1 & PM1).
  destruct (HeapCtrB.windows_anchored_nodup _ _ kf len1 CtrLib.K_BLOCK lenf CtrLib.K_BLOCK AN I1 (HeapCtrB.win_lookup_In _ _ _ _ WLf)) as [-> _].
  rewrite EH1 in H2.
  destruct (heap_del_window_k_facts E md A (wsub nw wone) (ws1 ++ skipn (3 * nn) rest) (pred nn) sh K_TWIN h2 wl1 eq_refl T1 N1 L1 NW1 H2)
    as (ws2 & m1 & len2 & m2 & wl2 & EH2 & I2 & W2 & W2' & T2 & N2 & L2 & SK2 & NW2 & R1 & R2 & R3 & M2 & PM2).
  destruct (HeapCtrB.windows_anchored_nodup _ _ sh len2 K_TWIN lent K_TWIN AN (S1 _ I2) (HeapCtrB.win_lookup_In _ _ _ _ WLt)) as [-> _].
  destruct twin_sh as (rs & _ & _ & _ & ESH & ELT). destruct owner as (UBf & HTf & _ & NRf & ALf).

  assert (ND1 : List.NoDup (kf :: HeapCtrB.anchors wl1)) by (exact (Permutation_NoDup (anchors_perm _ _ PM1) NDA)).
  apply List.NoDup_cons_iff in ND1 as [NKF1 ND1'].
  assert (ND2 : List.NoDup (sh :: HeapCtrB.anchors wl2)) by (exact (Permutation_NoDup (anchors_perm _ _ PM2) ND1')).
  apply List.NoDup_cons_iff in ND2 as [NSH2 _].
  assert (ANCH : forall (l : list (int * sv * w64)) k len kd, In (k, len, kd) l -> In k (HeapCtrB.anchors l)).
  { intros l k len kd H. unfold HeapCtrB.anchors. apply in_map_iff. exists (k, len, kd). auto. }
  exists l1, l2, m1, m2.
  split.
  { rewrite EH2. rewrite (decode_hargs E' md A _ _ (pred (pred nn)) T2 N2 L2).
    assert (RB : forallb (sv_vars_below (s_next st)) rest = true) by exact (CtrFrame.rest_below st FOK rest hargs md A nw Hf Eh).
    assert (RB2 : forallb (sv_vars_below (s_next st)) (ws2 ++ skipn (3 * pred nn) (ws1 ++ skipn (3 * nn) rest)) = true).
    { apply (forallb_sub _ rest); [| exact RB]. intros x Hx. apply S3. apply R3. exact Hx. }
    rewrite (CtrFrame.den_E' E st Fv Gv A (CtrFrame.A_below st FOK rest hargs md A nw Hf Eh)).
    rewrite (CtrFrame.wins_of_E' E st Fv Gv _ _ RB2), W2', SK2, SK1.
    rewrite (CtrFrame.map_den_E' E st Fv Gv _ (forallb_skipn _ (3 * nn) rest RB)). reflexivity. }
  split. { rewrite W1. unfold WBf. fold Af nf. rewrite KB1. reflexivity. }
  split. { rewrite <- W1', W2. unfold WTf. rewrite ESH, ELT, KT9. reflexivity. }
  split.
  - intros X. rewrite <- W1' in X.
    destruct (HeapCtrB.wins_cover E (pred nn) _ wl1 WBf NW1 X) as [KS|(k & len & kd & Ik & EW)]; [cbn in KS; unfold K_BLOCK, K_STACK in KS; lia|].
    unfold WBf in EW. injection EW as E1 E2 E3.
    assert (NKf : k <> kf) by (intros ->; exact (NKF1 (ANCH _ _ _ _ Ik))).
    assert (NKs : k <> sh).
    { intros ->. destruct (HeapCtrB.windows_anchored_nodup _ _ sh len kd lent K_TWIN AN (S1 _ Ik) (HeapCtrB.win_lookup_In _ _ _ _ WLt)) as [_ ->]. rewrite KT9 in E3. unfold K_BLOCK in E3. lia. }
    destruct (kept_block k len kd (Af, nf) (S1 _ Ik) NKf NKs blockLB ltac:(rewrite <- E1, <- E2; intros a Ha; exact Ha)) as [NE _]. exact (NE eq_refl).
  - intros X. rewrite <- W2' in X.
    destruct (HeapCtrB.wins_cover E (pred (pred nn)) _ wl2 WTf NW2 X) as [KS|(k & len & kd & Ik & EW)]; [cbn in KS; unfold K_TWINz, K_STACK in KS; lia|].
    unfold WTf in EW. injection EW as E1 E2 E3.
    assert (NKs : k <> sh) by (intros ->; exact (NSH2 (ANCH _ _ _ _ Ik))).
    assert (NKf : k <> kf) by (intros ->; exact (NKF1 (ANCH _ _ _ _ (R1 _ Ik)))).
    destruct (kept_block k len kd _ (S1 _ (R1 _ Ik)) NKf NKs HTf ltac:(rewrite <- E1, <- E2; intros a Ha; exact Ha)) as [_ NE]. exact (NE eq_refl).
Qed.

Hypothesis AWden : aw = den E A.
Hypothesis HC : cw_holds Cw (w2Z md) (map (den E) (skipn (3 * nn) rest)) LB (wins_of E nn rest) (ms_mem ms).

Lemma freed_off_image : forall a, in_iv (Af, nf) a \/ in_iv (shad Af, shlen (nf + 7)) a -> find_segment asegs a 1 = None /\ a < ATOP.
Proof.
  intros a Ha. destruct owner as (UBf & HTf & _). pose proof atop_range as ATR. pose proof AR as [HWw _].
  assert (IU : in_user LB a).
  { unfold in_user. apply in_ivs_In. destruct Ha as [Ha|Ha]; [exists (Af, nf); split; [exact blockLB| exact Ha]| exists (shad Af, shlen (nf + 7)); split; [exact HTf| exact Ha]]. }
  split.
  - destruct Ha as [Ha|Ha]; [exact (proj2 (aw_user_ok_asan AI ACCT UNIV AI_fake aw LB (ms_mem ms) mo _ a AWHf blockLB Ha))
                            | exact (proj2 (aw_user_ok_asan AI ACCT UNIV AI_fake aw LB (ms_mem ms) mo _ a AWHf HTf Ha))].
  - destruct (LB_band AI ACCT UNIV AI_fake WW aw LB (ms_mem ms) mo a HWw IU) as [B|[B|B]]; unfold AIMG_HI, KLS in *; lia.
Qed.

Lemma HOLDNf : forall l1 l2 m1 m2,
  decode (map (den E') h2) = Some (w2Z md, den E A, m1 ++ m2, map (den E) (skipn (3 * nn) rest)) ->
  wins_of E nn rest = l1 ++ WBf :: l2 -> l1 ++ l2 = m1 ++ WTf :: m2 -> ~ In WBf (l1 ++ l2) -> ~ In WTf (m1 ++ m2) ->
  op_holds OPS HEAP_ID (map (den E') h2) m' mo'.
Proof.
  intros l1 l2 m1 m2 D W1 W2 NB NT. rewrite OPS_holds1. destruct owner as (UBf & HTf & _ & NRf & ALf).
  assert (IN1 : forall w, In w (l1 ++ l2) <-> In w (wins_of E nn rest) /\ w <> WBf).
  { intros w. rewrite W1. split.
    - intros H. split; [apply in_app_or in H as [H|H]; apply in_or_app; [left; exact H| right; right; exact H]| intros ->; exact (NB H)].
    - intros [H NE]. apply in_app_or in H as [H|[H|H]]; apply in_or_app; [left; exact H| congruence| right; exact H]. }
  assert (IN2 : forall w, In w (m1 ++ m2) <-> In w (l1 ++ l2) /\ w <> WTf).
  { intros w. rewrite W2. split.
    - intros H. split; [apply in_app_or in H as [H|H]; apply in_or_app; [left; exact H| right; right; exact H]| intros ->; exact (NT H)].
    - intros [H NE]. apply in_app_or in H as [H|[H|H]]; apply in_or_app; [left; exact H| congruence| right; exact H]. }
  exists (w2Z md), aw, (m1 ++ m2), (map (den E) (skipn (3 * nn) rest)), LBk, Wf.
  split; [rewrite AWden; exact D|]. split; [exact (proj1 AR'f)|]. split; [| split].
  -
    apply Forall_forall. intros w Hw. apply IN2 in Hw as [Hw NWT]. apply IN1 in Hw as [Hw NWB].
    pose proof (proj1 (Forall_forall _ _) WF w Hw) as (X1 & X2 & X3 & KD). split; [exact X1|]. split; [exact X2|]. split; [exact X3|].
    destruct (HeapCtrB.wins_cover E nn rest wnl w NW Hw) as [KS|(k & len & kd & Ik & EW)].
    { left. destruct KD as [[_ C]|[[K _]|[K _]]]; [split; [exact KS| exact C]| rewrite KS in K; unfold K_BLOCK, K_STACK in K; lia| rewrite KS in K; unfold K_SUB, K_STACK in K; lia]. }
    assert (NKf : k <> kf).
    { intros ->. destruct (HeapCtrB.windows_anchored_nodup _ _ kf len kd lenf CtrLib.K_BLOCK AN Ik (HeapCtrB.win_lookup_In _ _ _ _ WLf)) as [-> ->].
      apply NWB. rewrite EW. unfold WBf. rewrite KB1. reflexivity. }
    assert (NKs : k <> sh).
    { intros ->. destruct (HeapCtrB.windows_anchored_nodup _ _ sh len kd lent K_TWIN AN Ik (HeapCtrB.win_lookup_In _ _ _ _ WLt)) as [-> ->].
      destruct twin_sh as (rs & _ & _ & _ & ESH & ELT). apply NWT. rewrite EW. unfold WTf. rewrite ESH, ELT, KT9. reflexivity. }
    destruct KD as [[K C]|[[K B]|[K (b & Hb & SUB)]]].
    + left. auto.
    + right; left. split; [exact K|]. apply LB_free_In. split; [exact B|].
      apply (kept_block k len kd (w_iv w) Ik NKf NKs B). rewrite EW. unfold w_iv. cbn [w_lo w_len]. intros a Ha. exact Ha.
    + right; right. split; [exact K|]. exists b. split; [| exact SUB]. apply LB_free_In. split; [exact Hb|].
      apply (kept_block k len kd b Ik NKf NKs Hb). rewrite EW in SUB. unfold w_iv in SUB. cbn [w_lo w_len] in SUB. exact SUB.
  -
    assert (HC1 : cw_holds Cw (w2Z md) (map (den E) (skipn (3 * nn) rest)) LB (wins_of E nn rest) m').
    { apply (cw_frame Cw _ _ _ _ (ms_mem ms) m' HC). intros a Ha U NH.
      apply in_ivs_In in U as (b & Hb & Hin).
      assert (INWIN : forall w, In w (wins_of E nn rest) -> w_kind w <> K_STACK -> in_iv (w_iv w) a -> False).
      { intros w Hw NK Hwa. apply NH. unfold in_ws, heap_ws. apply in_ivs_In. exists (w_iv w). split; [| exact Hwa]. apply in_map. apply filter_In. split; [exact Hw|].
        destruct (Z.eqb_spec (w_kind w) K_STACK); [contradiction| reflexivity]. }
      destruct (iv_eq_dec b (Af, nf)) as [->|N1].
      { exfalso. apply (INWIN WBf); [rewrite W1; apply in_or_app; right; left; reflexivity| cbn; unfold K_BLOCK, K_STACK; lia| exact Hin]. }
      destruct (iv_eq_dec b (shad Af, shlen (nf + 7))) as [->|N2].
      { exfalso. apply (INWIN WTf); [| cbn; unfold K_TWINz, K_STACK; lia| exact Hin].
        assert (X : In WTf (l1 ++ l2)) by (rewrite W2; apply in_or_app; right; left; reflexivity). apply IN1 in X as [X _]. exact X. }
      symmetry. unfold ALib.Mem.wa in *. apply (SBf a ltac:(unfold two64 in Ha; lia)). right; right. apply in_ivs_In. exists b. split; [apply LB_free_In; auto| exact Hin]. }
    assert (INB : In WBf (wins_of E nn rest)) by (rewrite W1; apply in_or_app; right; left; reflexivity).
    pose proof (cw_free Cw _ _ _ _ m' Af nf (l1 ++ l2) HC1 INB IN1) as HC2.
    assert (INT : In WTf (l1 ++ l2)) by (rewrite W2; apply in_or_app; right; left; reflexivity).
    exact (Cw_ghost_free _ _ _ _ m' (shad Af) (shlen (nf + 7)) (m1 ++ m2) HC2 INT IN2).
  -
    pose proof AR as [HWw _]. pose proof HWw as (AHw & HTw & _). destruct WOF as (_ & _ & E3 & E4).
    destruct owner as (_ & _ & (p' & HP' & HPT) & _).
    assert (EP : HB p' Af nf = HB p Af nf).
    { apply (shadow_iv_inj AI AI_fake _ _ _ _ _ (HB p' Af nf) (HB p Af nf) AHw (proj1 (HTw _ HPT)) ltac:(rewrite E4; exact HP)). reflexivity. }
    rewrite EP in HPT.
    apply (ties_free AI ACCT UNIV AI_fake WW aw LB (ms_mem ms) mo (wins_of E nn rest) (l1 ++ l2) (m1 ++ m2) p Af nf RNG' sta' m' HWw TI HPT IN1 IN2).
    intros IP. apply PRSF. rewrite <- E3. exact (ties_prist WW _ TI IP).
Qed.

Variables (r : int) (st1 : sstate) (R' : bvmap 5 word).
Hypothesis CP : call_pre st = Some r.
Hypothesis FS : forget_stack_below_sp_g st = Some st1.
Hypothesis KEPT : forall rg, In rg CtrFrame.kept_regsA -> AP.getr R' rg = AP.getr (ms_regs ms) rg.
Hypothesis HF : forall x i, clob_pos x = Some i -> Fv (Z.of_nat i) = AP.getr R' (reg_of_r5 x).
Hypothesis F15 : Fv 15 = AP.getr R' 10%bv.
Hypothesis MINV' : ALib.Mem.mem_inv asegs m'.
Variables (ks : int) (offs : w64) (rss : region) (ksp : int).
Hypothesis SPR : sp_region st = Some (ks, offs, rss).
Hypothesis Hksp : okey offs = Some ksp.
Hypothesis SPE : sp = bv_unsigned (ev E ks) + keyZ ksp.
Hypothesis AJ : aregions_justified st wnl = true.
Hypothesis K16 : keyZ ksp mod 16 = 0.
Hypothesis LOSP : loZ rss <= keyZ ksp.
Hypothesis STK' : stk asegs m' (CtrPre.sp_lo E st) sp.
Hypothesis FLOOR : ATOP + 4096 <= bv_unsigned (ev E ks) + loZ rss.
Hypothesis Hc : CtrA.count_op HEAP_ID (s_ops st) = 1%nat.
Hypothesis OTH : OTHER mo mo'.
Hypothesis MINVo : op_minv OPS mo'.

Definition delKf : list int := kf :: sh :: match tl with Some s2 => [s2] | None => [] end.
Definition RgF : IMap.t region := CtrFrame.RgPg st ks rss ksp [] delKf.
Definition NEWSETf (_ : Z) : Prop := False.

Lemma KEEP_delf : forall k0, ~ In k0 delKf -> KEEPf k0.
Proof.
  intros k0 H. unfold delKf in H. split; [| split].
  - intros ->. apply H. left. reflexivity.
  - intros ->. apply H. right. left. reflexivity.
  - intros X. rewrite X in H. apply H. right. right. left. reflexivity.
Qed.

Lemma freed_band : forall a, in_iv (Af, nf) a \/ in_iv (shad Af, shlen (nf + 7)) a ->
  (a < 0x7fff7000 \/ 0x10007fff8000 <= a) \/ (0x800bde00 <= a < shad ATOP).
Proof.
  intros a Ha. pose proof AR as [(AH & _) EM]. destruct WOF as (E1 & E2 & E3 & E4). rewrite E4 in AH.
  destruct (heap_block_facts AI _ _ _ _ _ (HB p Af nf) AH HP ltac:(exists p; reflexivity)) as (NP & (BK & _ & HI & _) & _). cbn [ab_addr ab_size] in NP, BK, HI.
  destruct (shadow_tight Af nf BK HI ltac:(lia)) as [T1 T2]. unfold ablk, AIMG_HI, KLS in BK. unfold in_iv in Ha. cbn [fst snd] in Ha.
  destruct Ha as [Ha|Ha]; [left| right]; lia.
Qed.

Lemma freed_unbased : forall a, in_iv (Af, nf) a \/ in_iv (shad Af, shlen (nf + 7)) a -> ~ in_based E' RgF a.
Proof.
  intros a Ha (k0 & rg & Fk & KZ & RA). destruct (freed_off_image a Ha) as [_ LOW]. destruct owner as (_ & HTf & _).
  assert (SPF : ATOP + 4096 <= sp) by (rewrite SPE; lia).
  destruct (CtrFrame.RgPg_range OPS E st ms mo HS FOK Fv Gv LB LBk ks offs rss ksp SPR SPE wnl nn rest AJ WF KEEPf WINKf VKEEPf TKEEPf LOSP FLOOR hargs md A nw Hf Hc Eh Tnw Nn Ln [] delKf
              (NoDup_nil _) KEEP_delf NEWSETf ltac:(intros k1 r1 a1 X; destruct X) k0 rg a Fk KZ RA) as [[X _]|[_ [[_ X]|[_ [X|[X|X]]]]]].
  - destruct X.
  - lia.
  - fold sp in X. lia.
  - exact (freed_apart AI ACCT UNIV AI_fake aw LB (ms_mem ms) mo WW Af nf a AR blockLB HTf Ha X).
  -
    pose proof atop_range as ATR.
    assert (SHA : 0x7fff8000 <= shad ATOP) by (unfold shad, ASHOFF; rewrite Z.shiftr_div_pow2 by lia; change (2 ^ 3) with 8; Z.div_mod_to_equations; lia).
    destruct (sh_cov_band a X) as [C|C]; destruct (freed_band a Ha) as [B|B]; lia.
Qed.

Lemma stF_shape : afree_stF tl st1 r h2 kf sh
  = SS r (rf_set (s_rf (clobber st1)) X10 (VP (addn (s_next st) 15) wzero)) (s_ff st) (s_resv st) RgF (s_facts st)
       (set_op HEAP_ID h2 (s_ops st)) (s_priv st) (PrimInt63.add (addn (s_next st) 15) 1%uint63).
Proof.
  unfold afree_stF. cbv zeta.
  destruct (clobber_fields st1) as (_ & FF & RV & RG & FS0 & OP & PV & NXc).
  assert (F1 : s_pc st1 = s_pc st /\ s_rf st1 = s_rf st /\ s_ff st1 = s_ff st /\ s_resv st1 = s_resv st /\ s_facts st1 = s_facts st
               /\ s_ops st1 = s_ops st /\ s_priv st1 = s_priv st /\ s_next st1 = s_next st).
  { unfold forget_stack_below_sp_g in FS. rewrite SPR, Hksp in FS. injection FS as <-. repeat split; reflexivity. }
  destruct F1 as (_ & _ & FF1 & RV1 & FS1 & OP1 & PV1 & NX1).
  assert (R1 : s_regs st1 = IMap.add ks (region_forget_below rss ksp) (s_regs st)).
  { unfold forget_stack_below_sp_g in FS. rewrite SPR, Hksp in FS. injection FS as <-. reflexivity. }
  assert (XE : s_next (clobber st1) = addn (s_next st) 15).
  { rewrite NXc, NX1. symmetry. destruct (HeapCtr.fresh_ok_inv st FOK) as (_ & _ & B). pose proof (int_range (s_next st)) as RR. rewrite two63_eq in RR.
    apply addn_lit; [reflexivity| rewrite wB_two63, two63_eq; lia]. }
  rewrite XE. rewrite (stF_shape_gen (clobber st1) _ (fun R0 => remove_opt tl (IMap.remove sh (IMap.remove kf R0))) h2 _ r).
  rewrite FF, RV, RG, FS0, OP, PV, FF1, RV1, FS1, OP1, PV1, R1. unfold RgF, CtrFrame.RgPg, delKf. destruct tl; reflexivity.
Qed.

Theorem free_post : st_ok asegs OPS E' (afree_stF tl st1 r h2 kf sh) (CtrFrame.ms' ms r R' m') mo'.
Proof.
  rewrite stF_shape. destruct DEL2 as (l1 & l2 & m1 & m2 & D & W1 & W2 & NB & NT).
  pose proof (HOLDNf l1 l2 m1 m2 D W1 W2 NB NT) as HOLDN.
  assert (INWS : forall a, in_ws (wins_of E nn rest) a -> in_ws (m1 ++ m2) a \/ in_iv (Af, nf) a \/ in_iv (shad Af, shlen (nf + 7)) a).
  { intros a X. unfold in_ws in X. apply in_ivs_In in X as (v & Hv & Hin). apply in_map_iff in Hv as (w & <- & Hw).
    rewrite W1 in Hw. apply in_app_or in Hw as [Hw|[<-|Hw]]; [| right; left; exact Hin|].
    - assert (X : In w (l1 ++ l2)) by (apply in_or_app; left; exact Hw). rewrite W2 in X. apply in_app_or in X as [X|[<-|X]]; [| right; right; exact Hin|];
        left; unfold in_ws; apply in_ivs_In; exists (w_iv w); (split; [apply in_map; apply in_or_app; auto| exact Hin]).
    - assert (X : In w (l1 ++ l2)) by (apply in_or_app; right; exact Hw). rewrite W2 in X. apply in_app_or in X as [X|[<-|X]]; [| right; right; exact Hin|];
        left; unfold in_ws; apply in_ivs_In; exists (w_iv w); (split; [apply in_map; apply in_or_app; auto| exact Hin]). }
  apply (CtrFrame.frame_st_ok AI IMGX IMGX_aci ACCT UNIV OPS AI_fake OPS_fp1 OPS_cov1 OPS_frame_other OPS_fp_other OTHER OPS_mo_other OPS_cov0_img
           E st ms mo HS FOK Fv Gv r st1 CP FS R' m' mo' KEPT HF aw LB LBk AWHf MINV' SBVf SBOf WBMf SBTf ks offs rss ksp SPR SPE wnl nn rest AJ WF KEEPf WINKf VKEEPf TKEEPf
           K16 LOSP STK' FLOOR hargs md A nw Hf Hc Eh Tnw Nn Ln OTH [] delKf (NoDup_nil _)
           ltac:(intros k1 r1 X; destruct X) KEEP_delf NEWSETf ltac:(intros k1 r1 X; destruct X) ltac:(intros k1 r1 a1 X; destruct X)
           ltac:(intros a1 X; destruct X) ltac:(intros a1 X; destruct X) ltac:(intros a1 X; destruct X) ltac:(intros k1 r1 k2 r2 a1 X; destruct X)
           h2 (w2Z md) (den E A) (m1 ++ m2) (map (den E) (skipn (3 * nn) rest)) D HOLDN).
  - intros a X. destruct X.
  -   intros a Ha NIX NWS. destruct (GLib.UG.in_ws_dec (wins_of E nn rest) a) as [IW|NIW]; [| left; exact NIW].
    right. destruct (INWS a IW) as [X|FR]; [contradiction|]. split; [exact (proj1 (freed_off_image a FR))| exact (freed_unbased a FR)].
  -   intros a IB X. pose proof (CtrFrame.in_heap_ws _ _ X) as IW. destruct (INWS a IW) as [Y|FR]; [| exfalso; exact (freed_unbased a FR IB)].

    unfold in_ws, heap_ws in X |- *. apply in_ivs_In in X as (v & Hv & Hin). apply in_map_iff in Hv as (w & <- & Hw). apply filter_In in Hw as [Hw KW].
    apply in_ivs_In. exists (w_iv w). split; [| exact Hin]. apply in_map. apply filter_In. split; [| exact KW].
    rewrite W1 in Hw. assert (NFR : forall w0, w0 = WBf \/ w0 = WTf -> in_iv (w_iv w0) a -> False).
    { intros w0 [-> | ->] Hw0; [exact (freed_unbased a (or_introl Hw0) IB)| exact (freed_unbased a (or_intror Hw0) IB)]. }
    apply in_app_or in Hw as [Hw|[<-|Hw]]; [| exfalso; exact (NFR WBf (or_introl eq_refl) Hin)|].
    + assert (X : In w (l1 ++ l2)) by (apply in_or_app; left; exact Hw). rewrite W2 in X. apply in_app_or in X as [X|[<-|X]]; [apply in_or_app; auto| exfalso; exact (NFR WTf (or_intror eq_refl) Hin)| apply in_or_app; auto].
    + assert (X : In w (l1 ++ l2)) by (apply in_or_app; right; exact Hw). rewrite W2 in X. apply in_app_or in X as [X|[<-|X]]; [apply in_or_app; auto| exfalso; exact (NFR WTf (or_intror eq_refl) Hin)| apply in_or_app; auto].
  - exact (so_facts _ _ _ _ _ _ (CtrFrame.HS' OPS E st ms mo HS FOK Fv Gv)).
  - rewrite HeapCtr.den_VPz. rewrite (CtrFrame.ev_E'_fresh E st FOK Fv Gv 15 ltac:(lia)). exact F15.
  - exact MINVo.
Qed.

End FREED.

Lemma afree_block : forall E st ms mo r hargs wnl L RNG sta LBa aw kf sh tl,
  st_ok asegs OPS E st ms mo -> CtrPre.acallG AI ACCT UNIV Cw E st ms mo r hargs wnl L RNG sta LBa aw ->
  find_twin (s_facts st) kf = Some sh -> afree_ok st wnl kf sh = true -> twin_consume st wnl kf sh = Some tl -> getr st X10 = VP kf wzero ->
  exists p lenf, CtrA.win_lookup wnl kf = Some (lenf, CtrLib.K_BLOCK)
    /\ In (HB p (bv_unsigned (ev E kf)) (bv_unsigned (den E lenf))) LBa
    /\ AP.getr (ms_regs ms) 10%bv = Z_to_bv 64 (bv_unsigned (ev E kf))
    /\ ablock_shadow (ms_mem ms) (bv_unsigned (ev E kf)) (bv_unsigned (den E lenf)).
Proof.
  intros E st ms mo r hargs wnl L RNG sta LBa aw kf sh tl HS CF FT FOKk TCAN X10E.
  destruct CF as (LB & ks & offs & rss & ksp & nn & md & A & nw & rest & SPR & Hksp & SPE & K16 & LOSP & FLOOR & Hf & Hc & Eh & Tnw & Nn & Ln & N255
                  & NW & AN & AJ & TS & WF & HC & AWden & (W & WOF & AR & TI)).
  destruct (afree_ok_inv E st ms mo HS wnl kf sh FOKk) as (rf & lenf & lent & Frf & WLf & WLt & BTs & LO0 & POSf & LEf & OTHERS).
  destruct (owner E st ms mo HS wnl nn rest LB aw L RNG sta LBa NW WF W WOF AR TI kf sh tl TCAN rf lenf lent WLf WLt BTs POSf LEf) as (_ & _ & (p & HP & _) & _).
  exists p, lenf. split; [exact WLf|]. split; [exact HP|].
  split; [rewrite <- HeapCtr.reg_of_X10, (GlueA.getr_RA asegs OPS E st ms mo HS X10), X10E, HeapCtr.den_VPz; symmetry; apply Z_to_bv_bv_unsigned|].
  exact (freed_pattern E st ms mo HS wnl nn rest LB aw L RNG sta LBa NW WF W WOF AR TI kf sh tl TCAN rf lenf lent WLf WLt BTs POSf LEf OTHERS).
Qed.

Definition cfvF (R' : bvmap 5 word) (i : Z) : word :=
  nth (Z.to_nat i)
      [AP.getr R' 1%bv; AP.getr R' 5%bv; AP.getr R' 6%bv; AP.getr R' 7%bv;
       AP.getr R' 11%bv; AP.getr R' 12%bv; AP.getr R' 13%bv; AP.getr R' 14%bv;
       AP.getr R' 15%bv; AP.getr R' 16%bv; AP.getr R' 17%bv;
       AP.getr R' 28%bv; AP.getr R' 29%bv; AP.getr R' 30%bv; AP.getr R' 31%bv; AP.getr R' 10%bv] (Z_to_bv 64 0).
Lemma cfvF_clob : forall R' x i, clob_pos x = Some i -> cfvF R' (Z.of_nat i) = AP.getr R' (reg_of_r5 x).
Proof. intros R' x i H. destruct x; cbn in H; try discriminate; injection H as <-; cbn; f_equal; apply bv_eq; reflexivity. Qed.

Lemma afree_post_okA : forall st sts E ms mo r hargs wnl st1 kf sh tl h1 h2 (L : alayout) (RNG : footprint) (sta : astate) (LBa : list ablock)
    (aw : word) p lenf rr RNG' msP mo',
  st_ok asegs OPS E st ms mo ->
  call_pre st = Some r -> forget_stack_below_sp_g st = Some st1 ->
  CtrPre.acallG AI ACCT UNIV Cw E st ms mo r hargs wnl L RNG sta LBa aw ->
  find_twin (s_facts st) kf = Some sh -> afree_ok st wnl kf sh = true -> no_views_on (s_facts st) (s_regs st) kf sh = true ->
  twin_consume st wnl kf sh = Some tl ->
  heap_del_window_k hargs (VP kf wzero) CtrLib.K_BLOCK = Some h1 -> heap_del_window_k h1 (VP sh wzero) K_TWIN = Some h2 ->
  sts = [afree_stF tl st1 r h2 kf sh] ->
  CtrA.win_lookup wnl kf = Some (lenf, CtrLib.K_BLOCK) ->
  In (HB p (bv_unsigned (ev E kf)) (bv_unsigned (den E lenf))) LBa ->
  let R := ms_regs ms in
  afree_post2 (aci AI) (AHEAP AI) L RNG (AP.getr R 1) (AP.getr R 2) (AP.getr R 3) (AP.getr R 4) (AP.getr R 8) (AP.getr R 9)
     (AP.getr R 18) (AP.getr R 19) (AP.getr R 20) (AP.getr R 21) (AP.getr R 22) (AP.getr R 23) (AP.getr R 24) (AP.getr R 25)
     (AP.getr R 26) (AP.getr R 27) (ms_fregs ms) (ms_fcsr ms) sta LBa p (CtrPre.sp_lo E st) (ms_mem ms) rr RNG' msP ->
  ACCT aw L RNG' rr (lb_remove p LBa) mo' -> (aprist sta -> aprist rr) -> op_minv OPS mo' -> OTHER mo mo' ->
  exists stF E1, sts = [stF] /\ env_ext (s_next st) E E1 /\ st_ok asegs OPS E1 stF msP mo'.
Proof.
  intros st sts E ms mo r hargs wnl st1 kf sh tl h1 h2 L RNG sta LBa aw p lenf rr RNG' msP mo'
         HS CP FS CF FT FOKk NV TCAN H1 H2 -> WLf0 HP R HQ ACP PRSF MINVo OTH.
  destruct CF as (LB & ks & offs & rss & ksp & nn & md & A & nw & rest & SPR & Hksp & SPE & K16 & LOSP & FLOOR & Hf & Hc & Eh & Tnw & Nn & Ln & N255
                  & NW & AN & AJ & TS & WF & HC & AWden & (W & WOF & AR & TI)).
  destruct (afree_ok_inv E st ms mo HS wnl kf sh FOKk) as (rf & lenf' & lent & Frf & WLf & WLt & BTs & LO0 & POSf & LEf & OTHERS).
  rewrite WLf0 in WLf. injection WLf as <-. pose proof WLf0 as WLf.
  destruct (HeapCtr.call_pre_inv st r CP) as (FOK & ra0 & Hra0 & WT0 & LT0 & ER).
  destruct HQ as (FPLE & t0 & t1 & t2 & a0 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & m' & EMS & MINV' & STK' & PRES & TWP & AH').
  set (R' := mkR (AP.getr R 1) (AP.getr R 2) (AP.getr R 3) (AP.getr R 4) t0 t1 t2 (AP.getr R 8) (AP.getr R 9) a0 a1 a2 a3 a4 a5 a6 a7
               (AP.getr R 18) (AP.getr R 19) (AP.getr R 20) (AP.getr R 21) (AP.getr R 22) (AP.getr R 23) (AP.getr R 24) (AP.getr R 25)
               (AP.getr R 26) (AP.getr R 27) t3 t4 t5 t6) in *.
  set (Fv := cfvF R'). set (Gv := fun (_ _ : Z) => Z_to_bv 8 0).
  assert (RAEQ : AP.getr R 1%bv = Z_to_bv 64 (to_Z r)).
  { unfold R. rewrite <- HeapCtr.reg_of_X1, (GlueA.getr_RA asegs OPS E st ms mo HS X1), Hra0, ER.
    assert (ERA : ra0 = wlit (wl ra0)) by (destruct ra0 as [t l]; cbn in WT0 |- *; subst t; reflexivity). rewrite ERA at 1. apply HeapCtr.den_wlit. }
  assert (EMS' : msP = CtrFrame.ms' ms r R' m').
  { rewrite EMS. unfold CtrFrame.ms'. f_equal. rewrite RAEQ. apply ret_pc_even.
    - pose proof (int_range r) as RR. rewrite two63_eq in RR. lia.
    - pose proof (HeapCtr.call_pre_even st r CP) as EV.
      pose proof (land_mk r 1%uint63 ltac:(change (to_Z 1%uint63) with 1; lia)) as LM.
      change (PrimInt63.sub (PrimInt63.lsl 1 1) 1)%uint63 with 1%uint63 in LM. rewrite EV in LM. change (to_Z 0%uint63) with 0 in LM.
      change (2 ^ to_Z 1%uint63) with 2 in LM. lia. }
  eexists. exists (CtrFrame.E' E st Fv Gv). split; [reflexivity|]. split; [apply CtrFrame.EXT|]. rewrite EMS'.
  apply (free_post E st ms mo HS wnl nn rest LB aw L RNG sta LBa NW AN WF W WOF AR TI
           (cvu_of E st (ms_mem ms) LB nn md A nw rest ltac:(rewrite <- Eh; exact Hf) Nn HC) kf sh NV tl TCAN rf lenf lent Frf WLf WLt BTs LO0 POSf LEf OTHERS
           p RNG' rr m' mo' HP AH' ACP PRSF PRES TWP hargs md A nw Hf Eh Tnw Nn Ln FOK Fv Gv h1 h2 H1 H2 AWden HC r st1 R' CP FS) with (ks := ks) (offs := offs) (rss := rss) (ksp := ksp); try assumption.
  - intros rg Hrg. unfold CtrFrame.kept_regsA in Hrg. cbn [In] in Hrg. repeat (destruct Hrg as [<-|Hrg]; [reflexivity|]). destruct Hrg.
  - intros x i Hx. exact (cfvF_clob R' x i Hx).
  - reflexivity.
Qed.

End Free.

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

Import ValP MemP CtrFX.
Import ActrA.
Module AP := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.PropExec.

Unset Nia Cache. Unset Nra Cache.

Lemma del_window_k_split : forall E0 m ws k0 kd0 ws' wl,
  weqb kd0 wzero = false ->
  del_window_k m ws (VP k0 wzero) kd0 = Some ws' -> CtrA.nonstack_windows m ws = Some wl -> (3 * m <= length ws)%nat ->
  exists l1 len l2 wl', In (k0, len, kd0) wl
    /\ wins_of E0 m ws = l1 ++ Win (bv_unsigned (ev E0 k0)) (bv_unsigned (den E0 len)) (w2Z kd0) :: l2
    /\ wins_of E0 (pred m) ws' = l1 ++ l2 /\ length ws' = (length ws - 3)%nat /\ (1 <= m)%nat
    /\ CtrA.nonstack_windows (pred m) ws' = Some wl'
    /\ (forall x, In x wl' -> In x wl) /\ (forall x, In x wl -> x = (k0, len, kd0) \/ In x wl')
    /\ (forall x, In x ws' -> In x ws) /\ Permutation wl ((k0, len, kd0) :: wl').
Proof.
  intros E0 m. induction m as [|m IH]; intros ws k0 kd0 ws' wl KZ H N L; [cbn in H; destruct ws; discriminate|].
  destruct ws as [|wlo [|ln [|kdv ws0]]]; try (cbn in H; discriminate). cbn [del_window_k] in H. cbn [CtrA.nonstack_windows] in N. cbn [length] in L |- *.
  destruct kdv as [kw| | | | | | | | | |]; try discriminate.
  destruct (CtrA.nonstack_windows m ws0) as [l|] eqn:NW; [|discriminate].
  destruct (sv_eqb wlo (VP k0 wzero) && sv_eqb (VL kw) (VL kd0)) eqn:C.
  - injection H as <-. apply andb_prop in C as [C1 C2]. apply sv_eqb_eq in C1. apply sv_eqb_eq in C2. injection C2 as ->. subst wlo.
    rewrite KZ in N. rewrite weqb_refl in N. cbn [andb negb] in N.
    destruct (PrimInt63.eqb k0 0); [discriminate|]. destruct (PrimInt63.eqb k0 CtrA.STACK_ID); [discriminate|]. cbn [andb negb] in N. injection N as <-.
    exists [], ln, (wins_of E0 m ws0), l. split; [left; reflexivity|]. rewrite wins_of_cons, HeapCtr.TwinB.den_VPz, unsigned_VL. cbn [app pred].
    split; [reflexivity|]. split; [reflexivity|]. split; [lia|]. split; [lia|]. split; [exact NW|].
    split; [intros x Hx; right; exact Hx|]. split; [intros x [<-|Hx]; [left; reflexivity| right; exact Hx]|]. split; [intros x Hx; do 3 right; exact Hx| apply Permutation_refl].
  - destruct (del_window_k m ws0 (VP k0 wzero) kd0) as [ws''|] eqn:D; [|discriminate]. injection H as <-.
    destruct (IH ws0 k0 kd0 ws'' l KZ D NW ltac:(lia)) as (l1 & len & l2 & wl'' & I & W1 & W2 & LEN & M1 & NW'' & S1 & S2 & S3 & PM).
    destruct m as [|m']; [lia|]. cbn [pred] in *.
    assert (SUBW : forall x, In x (wlo :: ln :: VL kw :: ws'') -> In x (wlo :: ln :: VL kw :: ws0)).
    { intros x [Hx|[Hx|[Hx|Hx]]]; [left| right; left| right; right; left| do 3 right; apply S3]; assumption. }
    destruct (weqb kw wzero) eqn:KW0.
    + injection N as <-.
      exists (Win (bv_unsigned (den E0 wlo)) (bv_unsigned (den E0 ln)) (bv_unsigned (den E0 (VL kw))) :: l1), len, l2, wl''.
      split; [exact I|]. rewrite wins_of_cons, W1. cbn [app]. split; [reflexivity|]. rewrite wins_of_cons, W2. split; [reflexivity|].
      cbn [length]. split; [lia|]. split; [lia|]. split; [cbn [CtrA.nonstack_windows]; rewrite NW'', KW0; reflexivity|].
      split; [exact S1|]. split; [exact S2|]. split; [exact SUBW| exact PM].
    + destruct wlo as [|kk oo| | | | | | | | |]; try discriminate.
      destruct (weqb oo wzero && negb (PrimInt63.eqb kk 0) && negb (PrimInt63.eqb kk CtrA.STACK_ID)) eqn:CC; [|discriminate]. injection N as <-.
      exists (Win (bv_unsigned (den E0 (VP kk oo))) (bv_unsigned (den E0 ln)) (bv_unsigned (den E0 (VL kw))) :: l1), len, l2, ((kk, ln, kw) :: wl'').
      split; [right; exact I|]. rewrite wins_of_cons, W1. cbn [app]. split; [reflexivity|]. rewrite wins_of_cons, W2. split; [reflexivity|].
      cbn [length]. split; [lia|]. split; [lia|]. split; [cbn [CtrA.nonstack_windows]; rewrite NW'', KW0, CC; reflexivity|].
      split; [intros x [<-|Hx]; [left; reflexivity| right; apply S1; exact Hx]|].
      split; [intros x [<-|Hx]; [right; left; reflexivity| destruct (S2 x Hx) as [X|X]; [left; exact X| right; right; exact X]]|]. split; [exact SUBW|].
      eapply Permutation_trans; [apply perm_skip; exact PM| apply perm_swap].
Qed.

Lemma heap_del_window_k_facts : forall E0 md A nw rest n k0 kd0 h' wnl,
  weqb kd0 wzero = false -> wt nw = false -> n = Z.to_nat (to_Z (wl nw)) -> (3 * n <= length rest)%nat ->
  CtrA.nonstack_windows n rest = Some wnl ->
  heap_del_window_k (VL md :: A :: VL nw :: rest) (VP k0 wzero) kd0 = Some h' ->
  exists ws' l1 len l2 wl',
    h' = VL md :: A :: VL (wsub nw wone) :: ws' ++ skipn (3 * n) rest
    /\ In (k0, len, kd0) wnl
    /\ wins_of E0 n rest = l1 ++ Win (bv_unsigned (ev E0 k0)) (bv_unsigned (den E0 len)) (w2Z kd0) :: l2
    /\ wins_of E0 (pred n) (ws' ++ skipn (3 * n) rest) = l1 ++ l2
    /\ wt (wsub nw wone) = false /\ pred n = Z.to_nat (to_Z (wl (wsub nw wone))) /\ (3 * pred n <= length (ws' ++ skipn (3 * n) rest))%nat
    /\ skipn (3 * pred n) (ws' ++ skipn (3 * n) rest) = skipn (3 * n) rest
    /\ CtrA.nonstack_windows (pred n) (ws' ++ skipn (3 * n) rest) = Some wl'
    /\ (forall x, In x wl' -> In x wnl) /\ (forall x, In x wnl -> x = (k0, len, kd0) \/ In x wl')
    /\ (forall x, In x (ws' ++ skipn (3 * n) rest) -> In x rest) /\ (1 <= n)%nat /\ Permutation wnl ((k0, len, kd0) :: wl').
Proof.
  intros E0 md A nw rest n k0 kd0 h' wnl KZ T N L NW H. unfold heap_del_window_k in H.
  assert (HN : heap_nwin (VL md :: A :: VL nw :: rest) = Some n).
  { unfold heap_nwin. rewrite T, <- N. destruct (Nat.leb_spec (3 * n) (length rest)); [reflexivity| lia]. }
  rewrite HN in H. destruct (del_window_k n (firstn (3 * n) rest) (VP k0 wzero) kd0) as [ws'|] eqn:D; [|discriminate]. injection H as <-.
  assert (NWf : CtrA.nonstack_windows n (firstn (3 * n) rest) = Some wnl) by (rewrite HeapCtrB.TwinB.nonstack_windows_firstn; exact NW).
  destruct (del_window_k_split E0 n (firstn (3 * n) rest) k0 kd0 ws' wnl KZ D NWf ltac:(rewrite firstn_length_le by lia; lia))
    as (l1 & len & l2 & wl' & I & W1 & W2 & LEN & M1 & NW' & S1 & S2 & S3 & PM).
  rewrite firstn_length_le in LEN by lia.
  destruct (HeapCtrB.TwinB.wsub_one_small nw T ltac:(pose proof (Uint63.to_Z_bounded (wl nw)); lia)) as [T' E'].
  exists ws', l1, len, l2, wl'. split; [reflexivity|]. split; [exact I|].
  split. { rewrite <- W1. rewrite <- (app_nil_r (firstn (3 * n) rest)) at 1. symmetry. apply (wins_of_firstn E0 n rest []). lia. }
  split; [rewrite (HeapCtrB.TwinB.wins_of_prefix E0 (pred n) ws' _ ltac:(lia)); exact W2|].
  split; [exact T'|]. split; [rewrite E', N; lia|]. split; [rewrite app_length; lia|].
  split; [apply skipn_app_exact; lia|].
  split. { rewrite <- (HeapCtrB.TwinB.nonstack_windows_firstn (pred n) (ws' ++ skipn (3 * n) rest)). rewrite firstn_app, firstn_all2 by lia.
           replace (3 * pred n - length ws')%nat with 0%nat by lia. cbn [firstn]. rewrite app_nil_r. exact NW'. }
  split; [exact S1|]. split; [exact S2|]. split; [| split; [exact M1| exact PM]].
  intros x Hx. rewrite <- (firstn_skipn (3 * n) rest). apply in_or_app. apply in_app_or in Hx as [Hx|Hx]; [left; apply S3; exact Hx| right; exact Hx].
Qed.

Definition afree_stF (tl : option int) (st1 : sstate) (r : int) (h2 : list sv) (kf sh : int) : sstate :=
  let st2 := clobber st1 in
  let x := s_next st2 in
  let st3 := set_next st2 (PrimInt63.add x 1%uint63) in
  let R' := remove_opt tl (IMap.remove sh (IMap.remove kf (s_regs st3))) in
  setpc (setr (set_ops (setregs st3 R') (set_op HEAP_ID h2 (s_ops st3))) X10 (VP x wzero)) r.

Lemma stF_shape_gen : forall (S : sstate) (nx1 : int) (R2 : IMap.t region -> IMap.t region) (h : list sv) (v : sv) (r : int),
  setpc (setr (set_ops (setregs (set_next S nx1) (R2 (s_regs (set_next S nx1)))) (set_op HEAP_ID h (s_ops (set_next S nx1)))) X10 v) r
  = SS r (rf_set (s_rf S) X10 v) (s_ff S) (s_resv S) (R2 (s_regs S)) (s_facts S) (set_op HEAP_ID h (s_ops S)) (s_priv S) nx1.
Proof. intros. destruct S. reflexivity. Qed.

Lemma afree_apply_shape : forall UNIV PCz st sts, afree_apply UNIV PCz st = Some sts ->
  exists r hargs wnl st1 kf sh h1 h2 tl,
    acall_pre ASTACK (Some (UNIV, PCz)) st = Some (r, hargs, wnl, st1) /\ getr st X10 = VP kf wzero
    /\ find_twin (s_facts st) kf = Some sh /\ afree_ok st wnl kf sh = true
    /\ heap_del_window_k hargs (VP kf wzero) CtrLib.K_BLOCK = Some h1 /\ heap_del_window_k h1 (VP sh wzero) K_TWIN = Some h2
    /\ sts = [afree_stF tl st1 r h2 kf sh] /\ no_views_on (s_facts st) (s_regs st) kf sh = true
    /\ twin_consume st wnl kf sh = Some tl.
Proof.
  intros UNIV PCz st sts H. unfold afree_apply in H.
  destruct (acall_pre ASTACK (Some (UNIV, PCz)) st) as [[[[r hargs] wnl] st1]|] eqn:PRE; [|discriminate].
  destruct (getr st X10) as [|kf off| | | | | | | | |] eqn:X10E; try discriminate.
  destruct (find_twin (s_facts st) kf) as [sh|] eqn:FT; [|discriminate].
  destruct (twin_consume st wnl kf sh) as [tl|] eqn:TC; [|discriminate].
  destruct (weqb off wzero && afree_ok st wnl kf sh && no_views_on (s_facts st) (s_regs st) kf sh) eqn:CK; [|discriminate].
  apply andb_prop in CK as [CK NV]. apply andb_prop in CK as [OFF FOK]. apply weqb_eq in OFF. subst off.
  destruct (heap_del_window_k hargs (VP kf wzero) CtrLib.K_BLOCK) as [h1|] eqn:H1; [|discriminate].
  destruct (heap_del_window_k h1 (VP sh wzero) K_TWIN) as [h2|] eqn:H2; [|discriminate].
  unfold fresh in H. cbv zeta in H. cbn [fst snd s_next set_next] in H. injection H as <-.
  exists r, hargs, wnl, st1, kf, sh, h1, h2, tl. repeat (split; [reflexivity || assumption|]). exact TC.
Qed.

Lemma twin_consume_canon : forall st wl kf sh, twin_canon st wl kf sh = true -> twin_consume st wl kf sh = Some None.
Proof. intros st wl kf sh H. unfold twin_consume. rewrite H. reflexivity. Qed.

Section Free.
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
Hypothesis OPS_mo_other : forall id args m mo mo', id <> HEAP_ID -> OTHER mo mo' -> op_holds OPS id args m mo -> op_holds OPS id args m mo'.
Hypothesis OPS_cov0_img : forall a, (exists seg, find_segment bsegs a 1 = Some seg) -> op_cov0 OPS a.

Lemma afree_ok_k_inv : forall (kdB kdT : w64) E st ms mo wnl kf sh, st_ok bsegs OPS E st ms mo -> afree_ok_k kdB kdT st wnl kf sh = true ->
  exists rf lenf lent,
  IMap.find kf (s_regs st) = Some rf /\ CtrA.win_lookup wnl kf = Some (lenf, kdB) /\ CtrA.win_lookup wnl sh = Some (lent, kdT)
  /\ block_of_twin (s_facts st) sh = Some kf /\ rg_lo rf = 0%uint63
  /\ 0 < hiZ E rf /\ hiZ E rf <= bv_unsigned (den E lenf)
  /\ forall k len kd, In (k, len, kd) wnl -> k <> kf -> k <> sh ->
       (weqb kd K_TWIN = true /\ exists kb, block_of_twin (s_facts st) k = Some kb /\ kb <> kf)
       \/ (weqb kd K_TWIN = false /\ exists r0, IMap.find k (s_regs st) = Some r0 /\ rg_lo r0 = 0%uint63 /\ hiZ E r0 <= bv_unsigned (den E len)
             /\ 0 < hiZ E r0 /\ rg_w r0 = true /\ (kd = kdB \/ hiZ E rf = bv_unsigned (den E lenf))).
Proof.
  intros kdB kdT E st ms mo wnl kf sh HS FOKk.
  pose proof (so_facts _ _ _ _ _ _ HS) as HF. unfold afree_ok_k in FOKk. cbv zeta in FOKk.
  destruct (IMap.find kf (s_regs st)) as [rf|] eqn:Frf; [|discriminate].
  destruct (CtrA.win_lookup wnl kf) as [[lenf kdf]|] eqn:WLf; [|discriminate].
  destruct (CtrA.win_lookup wnl sh) as [[lent kdt]|] eqn:WLt; [|discriminate].
  destruct (block_of_twin (s_facts st) sh) as [kb|] eqn:BT; [|discriminate].
  do 6 (apply andb_prop in FOKk as [FOKk ?]).
  rename H into ALL, H0 into LEQ, H1 into POS, H2 into LO0, H3 into KBE, H4 into KDT.
  apply weqb_eq in FOKk. subst kdf. apply weqb_eq in KDT. subst kdt. apply Uint63.eqb_correct in KBE. subst kb. apply Uint63.eqb_correct in LO0.
  pose proof (KnownA.TwinB.KnownA.known_ltu_sound E _ _ _ HF POS) as POS'. cbn [den] in POS'. rewrite wbv_unsigned, wzero_ok in POS'.
  pose proof (KnownA.TwinB.KnownA.known_leu_q_sound E _ _ _ HF LEQ) as LEQ'.
  exists rf, lenf, lent. repeat (split; [reflexivity || assumption|]).
  intros k len kd Hin NKf NKs. pose proof (proj1 (forallb_forall _ _) ALL _ Hin) as X. cbv beta iota in X.
  apply Uint63.eqb_false_spec in NKf, NKs. rewrite NKf, NKs in X. cbn [orb] in X.
  destruct (weqb kd K_TWIN) eqn:KT.
  - left. split; [reflexivity|]. destruct (block_of_twin (s_facts st) k) as [kb|]; [|discriminate]. exists kb. split; [reflexivity|].
    apply negb_true_iff in X. apply Uint63.eqb_false_spec in X. exact X.
  - right. split; [reflexivity|].
    destruct (IMap.find k (s_regs st)) as [r0|] eqn:Fr0; [|discriminate]. exists r0. split; [reflexivity|].
    apply andb_prop in X as [X KB]. apply andb_prop in X as [X W]. apply andb_prop in X as [X P0]. apply andb_prop in X as [L0 LE0]. apply Uint63.eqb_correct in L0.
    pose proof (KnownA.TwinB.KnownA.known_ltu_sound E _ _ _ HF P0) as P0'. cbn [den] in P0'. rewrite wbv_unsigned, wzero_ok in P0'.
    split; [exact L0|]. split; [exact (KnownA.TwinB.KnownA.known_leu_q_sound E _ _ _ HF LE0)|]. split; [exact P0'|]. split; [exact W|].
    apply orb_prop in KB as [KB|FULL]; [left; apply weqb_eq; exact KB| right].
    pose proof (KnownA.TwinB.KnownA.known_eq_sound E _ _ _ HF FULL) as EQ. unfold hiZ. rewrite EQ. reflexivity.
Qed.

Lemma cvu_of : forall (E : env) (st : sstate) (m : amem) (LB : blocks) nn md A nw rest,
  find_op HEAP_ID (s_ops st) = Some (VL md :: A :: VL nw :: rest) -> nn = Z.to_nat (to_Z (wl nw)) ->
  cw_holds Cw (w2Z md) (map (den E) (skipn (3 * nn) rest)) LB (wins_of E nn rest) m ->
  forall kb, In kb (carg_vecs st) -> bv_unsigned (ev E kb) <> 0 -> forall w, In w (wins_of E nn rest) -> w_kind w = K_BLOCK -> 0 < w_len w -> w_lo w <> bv_unsigned (ev E kb).
Proof.
  intros E st m LB nn md A nw rest Hf Nn HC kb Hkb NZ w Hw KW PW.
  destruct (CallA.TwinB.carg_vecs_spec st md A nw rest kb Hf Hkb) as (i & Hi & NE). rewrite <- Nn in NE.
  pose proof (Cw_vec_unowned _ _ _ _ _ i (den E (VP kb wzero)) HC Hi (map_nth_error (den E) _ _ NE)) as NEQ.
  rewrite HeapCtr.TwinB.den_VPz in NEQ. exact (NEQ NZ w Hw KW PW).
Qed.

Section FREED.
Variables (E : env) (st : sstate) (ms : machine_state) (mo : Model).
Hypothesis HS : st_ok bsegs OPS E st ms mo.
Variables (wnl : list (int * sv * w64)) (nn : nat) (rest : list sv) (LB : blocks) (aw : word)
          (L : alayout) (RNG : footprint) (sta : astate) (LBa : list ablock).
Hypothesis NW : CtrA.nonstack_windows nn rest = Some wnl.
Hypothesis AN : CtrA.windows_anchored (s_regs st) wnl = true.
Hypothesis WF : windows_wf (wins_of E nn rest) LB (ATOP + 4096).

Variable WW : wit.
Hypothesis WOF : wit_of WW L RNG sta LBa.
Hypothesis AR : aw_realW AI ACCT UNIV aw LB (ms_mem ms) mo WW.
Hypothesis TI : ties WW (wins_of E nn rest).

Hypothesis CVU : forall kb, In kb (carg_vecs st) -> bv_unsigned (ev E kb) <> 0 -> forall w, In w (wins_of E nn rest) -> w_kind w = K_BLOCK -> 0 < w_len w -> w_lo w <> bv_unsigned (ev E kb).
Variables (kf sh : int).
Hypothesis FT : find_twin (s_facts st) kf = Some sh.
Hypothesis FOKk : afree_ok st wnl kf sh = true.
Hypothesis NV : no_views_on (s_facts st) (s_regs st) kf sh = true.
Variable tl : option int.
Hypothesis TCONS : twin_consume st wnl kf sh = Some tl.

Lemma consume_cases :
  (tl = None /\ twin_canon st wnl kf sh = true)
  \/ (exists s2, tl = Some s2 /\ twin_canon_pair st wnl kf sh = Some s2).
Proof.
  unfold twin_consume in TCONS. destruct (twin_canon st wnl kf sh) eqn:TC.
  - injection TCONS as <-. left. auto.
  - destruct (twin_canon_pair st wnl kf sh) as [s2|] eqn:TP; [|discriminate TCONS]. injection TCONS as <-. right. exists s2. auto.
Qed.
Lemma canon_pair_inv : forall s2, twin_canon_pair st wnl kf sh = Some s2 ->
  exists r n kdn lent0 kdt, IMap.find sh (s_regs st) = Some r /\ CtrA.win_lookup wnl kf = Some (n, kdn) /\ CtrA.win_lookup wnl sh = Some (lent0, kdt)
    /\ is_twin_main r n = true /\ lent0 = twin_len n /\ twins_apart (s_facts st) (s_regs st) wnl (carg_vecs st) kf sh = true
    /\ tail_scan (s_facts st) (s_regs st) sh n = Some s2 /\ no_tails_on (s_facts st) (s_regs st) sh n s2 = true /\ s2 <> kf
    /\ CtrA.win_lookup wnl s2 = None.
Proof.
  intros s2 H. unfold twin_canon_pair in H. destruct (IMap.find sh (s_regs st)) as [r|]; [|discriminate H].
  destruct (CtrA.win_lookup wnl kf) as [[n kdn]|]; [|discriminate H]. destruct (CtrA.win_lookup wnl sh) as [[lent0 kdt]|]; [|discriminate H].
  match type of H with (if ?c then _ else _) = _ => destruct c eqn:Q; [|discriminate H] end.
  apply andb_prop in Q as [Q TAP]. apply andb_prop in Q as [TM LEN]. apply sv_eqb_eq in LEN.
  destruct (tail_scan (s_facts st) (s_regs st) sh n) as [s2'|] eqn:TS; [|discriminate H].
  destruct (no_tails_on (s_facts st) (s_regs st) sh n s2' && negb (PrimInt63.eqb s2' kf)
            && match CtrA.win_lookup wnl s2' with None => true | Some _ => false end) eqn:Q2; [|discriminate H].
  injection H as <-. apply andb_prop in Q2 as [Q2 NWIN]. apply andb_prop in Q2 as [NT NKF]. apply negb_true_iff in NKF. apply Uint63.eqb_false_spec in NKF.
  destruct (CtrA.win_lookup wnl s2') eqn:WL2; [discriminate NWIN|].
  exists r, n, kdn, lent0, kdt. repeat (split; [reflexivity || assumption|]). reflexivity.
Qed.

Lemma afree_ok_inv : exists rf lenf lent,
  IMap.find kf (s_regs st) = Some rf /\ CtrA.win_lookup wnl kf = Some (lenf, CtrLib.K_BLOCK) /\ CtrA.win_lookup wnl sh = Some (lent, K_TWIN)
  /\ block_of_twin (s_facts st) sh = Some kf /\ rg_lo rf = 0%uint63
  /\ 0 < hiZ E rf /\ hiZ E rf <= bv_unsigned (den E lenf)
  /\ forall k len kd, In (k, len, kd) wnl -> k <> kf -> k <> sh ->
       (weqb kd K_TWIN = true /\ exists kb, block_of_twin (s_facts st) k = Some kb /\ kb <> kf)
       \/ (weqb kd K_TWIN = false /\ exists r0, IMap.find k (s_regs st) = Some r0 /\ rg_lo r0 = 0%uint63 /\ hiZ E r0 <= bv_unsigned (den E len)
             /\ 0 < hiZ E r0 /\ rg_w r0 = true /\ (kd = CtrLib.K_BLOCK \/ hiZ E rf = bv_unsigned (den E lenf))).
Proof. exact (afree_ok_k_inv CtrLib.K_BLOCK K_TWIN E st ms mo wnl kf sh HS FOKk). Qed.

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

Lemma AWHf : aw_holds_asan AI ACCT UNIV aw LB (ms_mem ms) mo.
Proof. exact (aw_real_holds AI ACCT UNIV _ _ _ _ _ AR). Qed.

Lemma KB1 : w2Z CtrLib.K_BLOCK = 1. Proof. reflexivity. Qed.
Lemma KT9 : w2Z K_TWIN = 9. Proof. reflexivity. Qed.

Lemma entry_window : forall k len kd, In (k, len, kd) wnl ->
  k <> 0%uint63 /\ In (Win (bv_unsigned (ev E k)) (bv_unsigned (den E len)) (w2Z kd)) (wins_of E nn rest)
  /\ exists b, In b LB /\ (forall a, in_iv (bv_unsigned (ev E k), bv_unsigned (den E len)) a -> in_iv b a)
       /\ (kd = CtrLib.K_BLOCK -> b = (bv_unsigned (ev E k), bv_unsigned (den E len))).
Proof.
  intros k len kd Hin. destruct (HeapCtrB.TwinB.nonstack_windows_In E nn rest wnl k len kd NW Hin) as (K0 & _ & KD & INW).
  split; [exact K0|]. split; [exact INW|].
  pose proof (proj1 (Forall_forall _ _) WF _ INW) as (W1 & W2 & W3 & [[KS0 _]|[[KB B]|[KS2 (b & Hb & SUB)]]]); unfold w_iv in *; cbn [w_kind w_lo w_len] in *.
  - exfalso. exact (KD KS0).
  - eexists. split; [exact B|]. split; [intros a Ha; exact Ha| reflexivity].
  - exists b. split; [exact Hb|]. split; [exact SUB|]. intros ->. rewrite KB1 in KS2. unfold K_SUB in KS2. lia.
Qed.

Lemma blockLB : In (Af, nf) LB.
Proof.
  destruct (entry_window kf lenf CtrLib.K_BLOCK (HeapCtrB.TwinB.win_lookup_In _ _ _ _ WLf)) as (_ & _ & b & Hb & _ & EQ). rewrite (EQ eq_refl) in Hb. exact Hb.
Qed.

Lemma nf_small : 0 <= Af /\ 1 <= nf /\ Af + nf < 2 ^ 48.
Proof.
  destruct (aw_blocks_ok_asan AI IMGX IMGX_aci ACCT UNIV AI_fake aw LB (ms_mem ms) mo (Af, nf) AWHf blockLB) as (B1 & B2 & B3 & _). cbn [fst snd] in *.
  unfold aw_ceiling_asan in B3. pose proof atop_range. unfold hiZ in *. fold nf in LEf. lia.
Qed.

Lemma consume_common : exists rs, IMap.find sh (s_regs st) = Some rs /\ rg_w rs = false /\ rg_lo rs = 0%uint63
  /\ len_is_twin (s_facts st) lent lenf = true /\ twins_apart (s_facts st) (s_regs st) wnl (carg_vecs st) kf sh = true
  /\ ((tl = None /\ is_twin_region rs lenf = true /\ size_shape_ok (s_facts st) lenf = true /\ no_tail_at (s_facts st) (s_regs st) sh lenf = true)
      \/ (exists s2, tl = Some s2 /\ is_twin_main rs lenf = true /\ tail_scan (s_facts st) (s_regs st) sh lenf = Some s2
                     /\ no_tails_on (s_facts st) (s_regs st) sh lenf s2 = true /\ s2 <> kf /\ CtrA.win_lookup wnl s2 = None)).
Proof.
  destruct consume_cases as [[-> TCAN]|(s2 & -> & TP)].
  - destruct (CallA.TwinB.twin_canon_inv st wnl kf sh TCAN) as (rs & n0 & kdn & lent0 & kdt & FR & WLn & WLt0 & TR & SS0 & LEN & TAP & NTA).
    rewrite WLf in WLn. injection WLn as <- <-. rewrite WLt in WLt0. injection WLt0 as <- <-.
    exists rs. split; [exact FR|].
    pose proof TR as TR'. unfold is_twin_region in TR'. cbv zeta in TR'. do 4 (apply andb_prop in TR' as [TR' ?]).
    apply Uint63.eqb_correct in TR'. match goal with X : negb (rg_w rs) = true |- _ => apply negb_true_iff in X; rename X into RO end.
    split; [exact RO|]. split; [exact TR'|]. split; [exact LEN|]. split; [exact TAP|]. left. auto.
  - destruct (canon_pair_inv s2 TP) as (rs & n0 & kdn & lent0 & kdt & FR & WLn & WLt0 & TM & LEN & TAP & TS & NT & NKF & NWIN).
    rewrite WLf in WLn. injection WLn as <- <-. rewrite WLt in WLt0. injection WLt0 as <- <-.
    exists rs. split; [exact FR|]. destruct (CallA.TwinB.region_is_inv _ _ TM) as (LO & _ & WR & _). cbn [twin_main rg_lo rg_w] in LO, WR.
    split; [exact WR|]. split; [exact LO|]. split; [rewrite LEN; apply CallA.TwinB.len_is_twin_refl|]. split; [exact TAP|]. right. exists s2. repeat (split; [reflexivity || assumption|]). exact NWIN.
Qed.

Lemma twin_sh : exists rs, IMap.find sh (s_regs st) = Some rs /\ rg_w rs = false /\ len_is_twin (s_facts st) lent lenf = true
  /\ bv_unsigned (ev E sh) = shad Af /\ bv_unsigned (den E lent) = shlen (nf + 7).
Proof.

  destruct consume_common as (rs & FR & TR & _ & LEN & _).
  exists rs. split; [exact FR|]. split; [exact TR|]. split; [exact LEN|].
  destruct nf_small as (A0 & N1 & SM).
  split.
  - rewrite (CallA.TwinB.block_of_twin_sound E _ sh kf (so_facts _ _ _ _ _ _ HS) BTs). fold Af. unfold shad, ASHOFF. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8.
    rewrite Z.mod_small; [lia|]. clear - A0 SM N1. Z.div_mod_to_equations. lia.
  - rewrite (CallA.TwinB.len_is_twin_sound E _ _ _ (so_facts _ _ _ _ _ _ HS) LEN) by (fold nf; lia). fold nf. unfold shlen. rewrite Z.shiftr_div_pow2 by lia. reflexivity.
Qed.

Lemma owner : user_band Af /\ In (shad Af, shlen (nf + 7)) LB /\ (exists p, In (HB p Af nf) LBa /\ In (HB p Af nf) (w_T WW))
  /\ 1 <= nf <= AREQMAX /\ Af mod 16 = 0.
Proof.
  destruct twin_sh as (rs & _ & _ & _ & ESH & ELT).
  destruct (entry_window sh lent K_TWIN (HeapCtrB.TwinB.win_lookup_In _ _ _ _ WLt)) as (_ & INW & _). rewrite ESH, ELT, KT9 in INW.

  destruct TI as (_ & T2 & _). destruct (T2 _ INW eq_refl) as (b & HbT & EIV). unfold w_iv, twin_iv in EIV. cbn [w_lo w_len] in EIV. injection EIV as ESA ESL.
  destruct AR as [HWw EMw]. destruct WOF as (_ & _ & _ & ELB).
  destruct (twin_owner_w AI ACCT UNIV AI_fake WW aw LB (ms_mem ms) mo b Af nf HWw HbT blockLB ESA) as (EA & EN & NR).
  destruct (twin_T_facts AI ACCT UNIV WW aw LB (ms_mem ms) mo b HWw HbT) as (HbL & _ & _ & HTW & (p & EB) & _ & AL & UB & _).
  unfold twin_iv in HTW. rewrite <- EA, <- EN in HTW. rewrite <- EA in AL, UB. rewrite <- EN in NR. rewrite <- EA, <- EN in EB.
  split; [exact UB|]. split; [exact HTW|]. split; [| split; [exact NR| exact AL]].
  exists p. rewrite <- EB. split; [rewrite <- ELB; exact HbL| exact HbT].
Qed.

Lemma freed_pattern : ablock_shadow (ms_mem ms) Af nf.
Proof.
  destruct twin_sh as (rs & Frs & _ & _ & ESH & _). destruct owner as (UBf & HTf & (p0 & HPL & HPT) & NRf & ALf).
  destruct (entry_window sh lent K_TWIN (HeapCtrB.TwinB.win_lookup_In _ _ _ _ WLt)) as (SH0 & _).
  assert (SHNZ : PrimInt63.eqb sh 0%uint63 = false) by (apply Uint63.eqb_false_spec; exact SH0).
  intros g G0 G1.
  assert (P1 : rb bsegs (ms_mem ms) (shad Af + g) = Some (Z_to_bv 8 (if 8 * g + 8 <=? nf then 0 else nf - 8 * g))).
  { destruct consume_common as (rs' & Frs' & _ & _ & _ & _ & [(_ & TRs & SS & _)|(s2 & _ & TM & TS & _)]); rewrite Frs in Frs'; injection Frs' as <-.
    - pose proof (so_reg _ _ _ _ _ _ HS sh rs Frs) as RO.
      pose proof (CallA.TwinB.size_shape_sound E _ lenf (so_facts _ _ _ _ _ _ HS) SS) as SHAPE.
      pose proof (CallA.TwinB.is_twin_region_sound bsegs (s_priv st) E (ms_mem ms) sh rs lenf RO SHNZ TRs) as PATR. fold nf in PATR. rewrite ESH in PATR.
      apply PATR; [unfold AREQMAX in NRf; lia| | exact G0| exact G1]. destruct lenf; try exact I; exact SHAPE.
    -
      pose proof (CallA.TwinB.twin_pair_sound bsegs (s_priv st) E (ms_mem ms) (s_facts st) (s_regs st) sh rs lenf s2 (so_facts _ _ _ _ _ _ HS)
                    (so_reg _ _ _ _ _ _ HS) Frs SHNZ TM TS) as PATP.
      fold nf in PATP. rewrite ESH in PATP. apply PATP; [clear - NRf; lia| | exact G0| exact G1].
      destruct nf_small as (A0 & N1 & SM). unfold shad, ASHOFF. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8. clear - A0 N1 SM. Z.div_mod_to_equations. lia. }

  destruct AR as [HWw _]. pose proof HWw as (_ & _ & _ & _ & _ & _ & _ & MAP & _).
  assert (MP : ms_mem ms (ALib.Mem.wa (shad Af + g)) <> None).
  { apply MAP. apply in_ivs_In. exists (twin_iv (HB p0 Af nf)). split; [apply in_map; exact HPT|].
    unfold in_iv, twin_iv. cbn [fst snd ab_addr ab_size]. unfold shlen. rewrite Z.shiftr_div_pow2 by lia. change (2^3) with 8. clear -G0 G1. Z.div_mod_to_equations. lia. }
  unfold rb in P1. unfold ALib.Mem.wa in *. destruct (ms_mem ms (Z_to_bv 64 (shad Af + g))) as [y|]; [exact P1| contradiction].
Qed.

Lemma twin_cover : forall a, in_iv (shad Af, shlen (nf + 7)) a ->
  exists kx rx, IMap.find kx (s_regs st) = Some rx /\ PrimInt63.eqb kx 0%uint63 = false /\ rg_w rx = false
    /\ bv_unsigned (ev E kx) + loZ rx <= a < bv_unsigned (ev E kx) + hiZ E rx.
Proof.
  intros a Ha. unfold in_iv, shlen in Ha. cbn [fst snd] in Ha. rewrite Z.shiftr_div_pow2 in Ha by lia. change (2 ^ 3) with 8 in Ha.
  destruct twin_sh as (rs & Frs & ROs & _ & ESH & _). destruct nf_small as (A0 & N1 & SM).
  destruct (entry_window sh lent K_TWIN (HeapCtrB.TwinB.win_lookup_In _ _ _ _ WLt)) as (SH0 & _).
  assert (SHNZ : PrimInt63.eqb sh 0%uint63 = false) by (apply Uint63.eqb_false_spec; exact SH0).
  assert (KZ0 : keyZ 0%uint63 = 0) by reflexivity.
  destruct consume_common as (rs' & Frs' & _ & LOs & _ & _ & [(_ & TRs & _)|(s2 & _ & TM & TS & _)]); rewrite Frs in Frs'; injection Frs' as <-.
  - exists sh, rs. split; [exact Frs|]. split; [exact SHNZ|]. split; [exact ROs|].
    unfold is_twin_region in TRs. cbv zeta in TRs. do 4 (apply andb_prop in TRs as [TRs ?]).
    match goal with X : sv_eqb (rg_hi rs) _ = true |- _ => apply sv_eqb_eq in X; rewrite CallA.TwinB.twin_region_hi in X; rename X into HIs end.
    unfold loZ, hiZ. rewrite LOs, HIs, (CallA.TwinB.twin_len_den E lenf) by (fold nf; lia). fold nf. rewrite KZ0, ESH. lia.
  - destruct (CallA.TwinB.region_is_inv _ _ TM) as (_ & HIm & _). cbn [twin_main rg_hi] in HIm.
    destruct (Z_lt_ge_dec a (shad Af + (nf - 1) / 8)) as [LT|GE].
    + exists sh, rs. split; [exact Frs|]. split; [exact SHNZ|]. split; [exact ROs|].
      unfold loZ, hiZ. rewrite LOs, HIm, CallA.TwinB.sz_last_den by (fold nf; exact N1). fold nf. rewrite KZ0, ESH. lia.
    + destruct (CallA.TwinB.tail_scan_inv _ _ _ _ _ TS) as (FTL & S0 & _ & r2 & F2 & TR2).
      destruct (CallA.TwinB.region_is_inv _ _ TR2) as (LO2 & HI2 & WR2 & _). destruct (CallA.TwinB.tail_region_fields lenf) as (TLO & THI & TWR & _).
      rewrite TLO in LO2. rewrite THI in HI2. rewrite TWR in WR2.
      assert (B : bv_unsigned (ev E sh) + (bv_unsigned (den E lenf) - 1) / 8 < 2 ^ 64).
      { fold nf. rewrite ESH. unfold shad, ASHOFF. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8. clear - A0 N1 SM. Z.div_mod_to_equations. lia. }
      pose proof (CallA.TwinB.find_tail_sound E _ sh lenf s2 (so_facts _ _ _ _ _ _ HS) FTL) as EV. apply (f_equal bv_unsigned) in EV.
      rewrite (CallA.TwinB.tail_rhs_den E sh lenf ltac:(fold nf; exact N1) B) in EV. fold nf in EV. rewrite ESH in EV.
      exists s2, r2. split; [exact F2|]. split; [apply Uint63.eqb_false_spec; exact S0|]. split; [exact WR2|].
      unfold loZ, hiZ. rewrite LO2, HI2, KZ0, EV. cbn [den]. rewrite wbv_unsigned. change (w2Z wone) with 1. clear - Ha GE N1. Z.div_mod_to_equations. lia.
Qed.

Lemma region_first_byte : forall k r0, IMap.find k (s_regs st) = Some r0 -> rg_lo r0 = 0%uint63 -> 0 < hiZ E r0 ->
  bv_unsigned (ev E k) + loZ r0 <= bv_unsigned (ev E k) < bv_unsigned (ev E k) + hiZ E r0.
Proof. intros k r0 _ L0 P. unfold loZ. rewrite L0. assert (KZ0 : keyZ 0%uint63 = 0) by reflexivity. rewrite KZ0. lia. Qed.

Lemma kept_block_w : forall k len kd r0 b, In (k, len, kd) wnl -> k <> kf -> k <> sh ->
  IMap.find k (s_regs st) = Some r0 -> rg_lo r0 = 0%uint63 -> hiZ E r0 <= bv_unsigned (den E len) -> 0 < hiZ E r0 -> rg_w r0 = true ->
  (kd = CtrLib.K_BLOCK \/ hiZ E rf = nf) ->
  In b LB -> (forall a, in_iv (bv_unsigned (ev E k), bv_unsigned (den E len)) a -> in_iv b a) ->
  b <> (Af, nf) /\ b <> (shad Af, shlen (nf + 7)).
Proof.
  intros k len kd r0 b Hin NKf NKs Fr0 L0 LE0 P0 W0 CASE Hb SUB.
  destruct (entry_window k len kd Hin) as (K0 & _ & b1 & Hb1 & SUB1 & EQ1).
  destruct (entry_window kf lenf CtrLib.K_BLOCK (HeapCtrB.TwinB.win_lookup_In _ _ _ _ WLf)) as (Kf0 & _).
  destruct (entry_window sh lent K_TWIN (HeapCtrB.TwinB.win_lookup_In _ _ _ _ WLt)) as (Ks0 & _).
  assert (ZK : PrimInt63.eqb k 0%uint63 = false) by (apply Uint63.eqb_false_spec; exact K0).
  assert (ZF : PrimInt63.eqb kf 0%uint63 = false) by (apply Uint63.eqb_false_spec; exact Kf0).
  assert (ZS : PrimInt63.eqb sh 0%uint63 = false) by (apply Uint63.eqb_false_spec; exact Ks0).
  assert (A0IN : in_iv (bv_unsigned (ev E k), bv_unsigned (den E len)) (bv_unsigned (ev E k))) by (unfold in_iv; cbn [fst snd]; lia).
  pose proof (SUB _ A0IN) as INB. pose proof (region_first_byte k r0 Fr0 L0 P0) as RK.
  split; intros ->.
  -
    unfold in_iv in INB. cbn [fst snd] in INB.
    assert (INF : bv_unsigned (ev E kf) + loZ rf <= bv_unsigned (ev E k) < bv_unsigned (ev E kf) + hiZ E rf).
    { unfold loZ. rewrite LO0. assert (KZ0 : keyZ 0%uint63 = 0) by reflexivity. rewrite KZ0. fold Af. destruct CASE as [->|FULL]; [| lia].

      pose proof (EQ1 eq_refl) as E1. subst b1.
      destruct (Z.eq_dec (bv_unsigned (ev E k)) Af) as [EA|NA]; [lia| exfalso].
      apply (aw_blocks_disj_asan AI ACCT UNIV AI_fake aw LB (ms_mem ms) mo _ (Af, nf) (bv_unsigned (ev E k)) AWHf Hb1 blockLB); [cbn [fst]; exact NA| exact A0IN|].
      unfold in_iv. cbn [fst snd]. lia. }
    exact (so_disj _ _ _ _ _ _ HS k r0 kf rf Fr0 Frf NKf ZK ZF (or_introl W0) _ (conj RK INF)).
  -
    destruct (twin_cover (bv_unsigned (ev E k)) INB) as (kx & rx & Fx & ZX & WX & INS).
    assert (NKx : k <> kx) by (intros ->; rewrite Fr0 in Fx; injection Fx as <-; rewrite W0 in WX; discriminate WX).
    exact (so_disj _ _ _ _ _ _ HS k r0 kx rx Fr0 Fx NKx ZK ZX (or_introl W0) _ (conj RK INS)).
Qed.

Lemma kept_block : forall k len kd b, In (k, len, kd) wnl -> k <> kf -> k <> sh ->
  In b LB -> (forall a, in_iv (bv_unsigned (ev E k), bv_unsigned (den E len)) a -> in_iv b a) ->
  b <> (Af, nf) /\ b <> (shad Af, shlen (nf + 7)).
Proof.
  intros k len kd b Hin NKf NKs Hb SUB.
  destruct (OTHERS k len kd Hin NKf NKs) as [[KT (kb & BTk & NKB)]|(KT & r0 & Fr0 & L0 & LE0 & P0 & W0 & CASE)].
  2:{ exact (kept_block_w k len kd r0 b Hin NKf NKs Fr0 L0 LE0 P0 W0 CASE Hb SUB). }

  destruct consume_common as (rsC & _ & _ & _ & _ & TAP & _).
  destruct (CallA.TwinB.twins_apart_inv _ _ _ _ _ _ k len kd TAP Hin KT NKs) as [OLD|EVA].
  2:{ destruct (CallV.TwinB.twin_ev_cases E _ _ _ _ _ _ _ (so_facts _ _ _ _ _ _ HS) EVA) as (kb2 & BT2 & LW & AL & EVD).
      rewrite BTk in BT2. injection BT2 as <-.
      pose proof (GTwinSub.GTwinSub.mod8_of_align E _ kb (so_facts _ _ _ _ _ _ HS) AL) as K8.

      destruct (entry_window k len kd Hin) as (_ & INWk & _). apply weqb_eq in KT. subst kd. rewrite KT9 in INWk.
      destruct TI as (_ & T2 & _). destruct (T2 _ INWk eq_refl) as (b2 & Hb2T & EIV). unfold w_iv in EIV. cbn [w_lo w_len] in EIV.
      pose proof AR as [HWw _].
      destruct (twin_T_facts AI ACCT UNIV WW aw LB (ms_mem ms) mo b2 HWw Hb2T) as (_ & _ & _ & _ & _ & NR2 & AL2 & UB2 & NUB2).
      assert (EB : b = twin_iv b2).
      { apply (twin_container AI ACCT UNIV AI_fake WW aw LB (ms_mem ms) mo b2 b HWw Hb2T Hb). rewrite <- EIV. exact SUB. }
      unfold twin_iv in EIV. injection EIV as ESA ESL.
      destruct owner as (UBf & HTf & _ & NRf & ALf).
      subst b. unfold twin_iv. split.
      - intros X. apply (f_equal fst) in X. cbn [fst] in X. apply NUB2. rewrite X. exact UBf.
      - intros X. injection X as XA XL.

        destruct nf_small as (A0 & N1 & SM).
        pose proof (CallA.TwinB.block_of_twin_sound E _ k kb (so_facts _ _ _ _ _ _ HS) BTk) as LK.
        pose proof (bv_unsigned_in_range 64 (ev E kb)) as RKB. change (bv_modulus 64) with (2 ^ 64) in RKB.
        rewrite Z.mod_small in LK by (clear - RKB; Z.div_mod_to_equations; lia).
        assert (EKB : bv_unsigned (ev E kb) = Af).
        { rewrite ESA, XA in LK. unfold shad, ASHOFF in LK. rewrite Z.shiftr_div_pow2 in LK by lia. change (2 ^ 3) with 8 in LK.
          clear - LK K8 ALf. Z.div_mod_to_equations. lia. }
        destruct EVD as [CVk|(ks & lens & kds & rsub & Hins & NXs & NKBs & NKTs & Frsub & RWs & L0s & HPOS & XLO & XHI)].
        {
          destruct (HeapCtrB.TwinB.nonstack_windows_In E nn rest wnl kf lenf CtrLib.K_BLOCK NW (HeapCtrB.TwinB.win_lookup_In _ _ _ _ WLf)) as (_ & _ & _ & INk).
          assert (AFNZ : Af <> 0).
          { destruct owner as (_ & _ & (p0 & HP0 & _) & _). pose proof AR as [(AH0 & _) _]. destruct WOF as (_ & _ & _ & E4w). rewrite E4w in AH0.
            destruct (heap_block_facts AI _ _ _ _ _ (HB p0 Af nf) AH0 HP0 ltac:(exists p0; reflexivity)) as (_ & (BK0 & _) & _). unfold ablk, AIMG_HI, KLS in BK0. cbn [ab_addr ab_size] in BK0. lia. }
          apply (CVU kb CVk ltac:(rewrite EKB; exact AFNZ) _ INk); [reflexivity| cbn [w_len]; fold nf; lia| cbn [w_lo]; fold Af; symmetry; exact EKB]. }
        assert (XIN : Af <= bv_unsigned (ev E ks) < Af + nf).
        { rewrite ESL, XL in XHI. rewrite EKB in XLO, XHI. unfold shlen in XHI. rewrite Z.shiftr_div_pow2 in XHI by lia. change (2 ^ 3) with 8 in XHI.
          clear - XLO XHI N1. Z.div_mod_to_equations. lia. }
        destruct (entry_window ks lens kds Hins) as (Ks0 & _).
        destruct (entry_window kf lenf CtrLib.K_BLOCK (HeapCtrB.TwinB.win_lookup_In _ _ _ _ WLf)) as (Kf0 & _).
        assert (ZKs : PrimInt63.eqb ks 0%uint63 = false) by (apply Uint63.eqb_false_spec; exact Ks0).
        assert (ZF : PrimInt63.eqb kf 0%uint63 = false) by (apply Uint63.eqb_false_spec; exact Kf0).
        assert (NSs : ks <> sh).
        { intros ->. destruct twin_sh as (rs & Frs & RO & _). rewrite Frsub in Frs. injection Frs as <-. rewrite RWs in RO. discriminate RO. }
        destruct (OTHERS ks lens kds Hins NXs NSs) as [[KTs _]|(_ & r0s & Fr0s & _ & _ & _ & _ & CASEs)]; [rewrite NKTs in KTs; discriminate KTs|].
        destruct CASEs as [KB|FULL]; [exact (NKBs KB)|].
        pose proof (region_first_byte ks rsub Frsub L0s HPOS) as RKs.
        assert (INF : bv_unsigned (ev E kf) + loZ rf <= bv_unsigned (ev E ks) < bv_unsigned (ev E kf) + hiZ E rf).
        { unfold loZ. rewrite LO0. assert (KZ0 : keyZ 0%uint63 = 0) by reflexivity. rewrite KZ0. fold Af. rewrite FULL. fold nf. lia. }
        exact (so_disj _ _ _ _ _ _ HS ks rsub kf rf Frsub Frf NXs ZKs ZF (or_introl RWs) _ (conj RKs INF)). }
  destruct (CallA.TwinB.twin_arm_old_inv _ _ _ _ _ OLD) as (kb' & rk & n2 & BT2 & FRk & WL2 & LEN2 & _).
  rewrite BTk in BT2. injection BT2 as <-.
  pose proof (HeapCtrB.TwinB.win_lookup_In _ _ _ _ WL2) as IN2.
  assert (NKBs : kb <> sh). { intros ->. rewrite WLt in WL2. apply (f_equal (fun o => match o with Some (_, kd0) => w2Z kd0 | None => 0 end)) in WL2. vm_compute in WL2. discriminate WL2. }
  destruct (entry_window kb n2 CtrLib.K_BLOCK IN2) as (Kb0 & _ & b2 & Hb2 & SUB2 & EQ2). pose proof (EQ2 eq_refl) as E2. subst b2.
  set (A2 := bv_unsigned (ev E kb)) in *. set (N2 := bv_unsigned (den E n2)) in *.

  destruct (OTHERS kb n2 CtrLib.K_BLOCK IN2 NKB NKBs) as [[X _]|(_ & r2 & Fr2 & L2 & LE2 & P2 & W2 & CASE2)]; [discriminate X|].
  destruct (kept_block_w kb n2 CtrLib.K_BLOCK r2 (A2, N2) IN2 NKB NKBs Fr2 L2 LE2 P2 W2 CASE2 Hb2 ltac:(intros a Ha; exact Ha)) as [NEB _].
  destruct (aw_blocks_ok_asan AI IMGX IMGX_aci ACCT UNIV AI_fake aw LB (ms_mem ms) mo (A2, N2) AWHf Hb2) as (B1 & B2 & B3 & _). cbn [fst snd] in B1, B2, B3.
  unfold aw_ceiling_asan in B3. pose proof atop_range as ATR.
  assert (N2pos : 1 <= N2) by (unfold hiZ in *; fold N2 in LE2; lia).
  assert (EK : bv_unsigned (ev E k) = shad A2).
  { rewrite (CallA.TwinB.block_of_twin_sound E _ k kb (so_facts _ _ _ _ _ _ HS) BTk). fold A2. unfold shad, ASHOFF. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8.
    rewrite Z.mod_small; [lia|]. clear - B1 B3 N2pos ATR. Z.div_mod_to_equations. lia. }
  assert (EL : bv_unsigned (den E len) = shlen (N2 + 7)).
  { rewrite (CallA.TwinB.len_is_twin_sound E _ _ _ (so_facts _ _ _ _ _ _ HS) LEN2) by (fold N2; lia). fold N2. unfold shlen. rewrite Z.shiftr_div_pow2 by lia. reflexivity. }
  rewrite EK, EL in SUB.

  destruct (entry_window k len kd Hin) as (_ & INWk & _). rewrite EK, EL in INWk. apply weqb_eq in KT. subst kd. rewrite KT9 in INWk.
  destruct TI as (_ & T2 & _). destruct (T2 _ INWk eq_refl) as (b2 & Hb2T & EIV). unfold w_iv, twin_iv in EIV. cbn [w_lo w_len] in EIV. injection EIV as ESA ESL.
  pose proof AR as [HWw _].
  destruct (twin_owner_w AI ACCT UNIV AI_fake WW aw LB (ms_mem ms) mo b2 A2 N2 HWw Hb2T Hb2 ESA) as (EA2 & EN2 & NR2).
  destruct (twin_T_facts AI ACCT UNIV WW aw LB (ms_mem ms) mo b2 HWw Hb2T) as (_ & _ & _ & _ & _ & _ & AL2 & UB2 & NUB2).
  rewrite <- EA2 in AL2, NUB2.

  assert (EB : b = (shad A2, shlen (N2 + 7))).
  { rewrite EA2, EN2. apply (twin_container AI ACCT UNIV AI_fake WW aw LB (ms_mem ms) mo b2 b HWw Hb2T Hb). unfold twin_iv. rewrite <- EA2, <- EN2. exact SUB. }
  destruct owner as (UBf & HTf & _ & NRf & ALf).
  subst b. split.
  - intros X. apply (f_equal fst) in X. cbn [fst] in X. apply NUB2. rewrite X. exact UBf.
  - intros X. apply (f_equal fst) in X. cbn [fst] in X. apply NEB.
    assert (EA : A2 = Af) by (unfold shad in X; rewrite !Z.shiftr_div_pow2 in X by lia; change (2 ^ 3) with 8 in X; clear - X AL2 ALf; Z.div_mod_to_equations; lia).
    rewrite EA in *. f_equal. exact (LB_same_addr AI ACCT UNIV AI_fake WW aw LB (ms_mem ms) mo Af N2 nf HWw Hb2 blockLB).
Qed.

Variables (p : aptr) (RNG' : footprint) (sta' : astate) (m' : amem) (mo' : Model).
Hypothesis HP : In (HB p Af nf) LBa.
Hypothesis AH' : AHEAP AI L RNG' sta' (lb_remove p LBa) m'.
Hypothesis AC' : ACCT aw L RNG' sta' (lb_remove p LBa) mo'.
Hypothesis PRSF : aprist sta -> aprist sta'.
Let sp : Z := bv_unsigned (AP.getr (ms_regs ms) 2%bv).
Hypothesis PRES : aheap_pres (aci AI) (lb_remove p LBa) sp (ms_mem ms) m'.
Hypothesis TWP : twins_pres (lb_remove p LBa) (ms_mem ms) m'.
Definition LBk : blocks := LB_free LB Af nf.

Definition Wf : wit := mkWit (w_L WW) RNG' sta' (lb_remove p (w_LBa WW))
                             (List.filter (fun x => if ablock_eq_dec x (HB p Af nf) then false else true) (w_T WW)) (w_FA WW) m' (w_zc WW).
Lemma AR'f : aw_realW AI ACCT UNIV aw LBk m' mo' Wf.
Proof.
  destruct WOF as (E1 & E2 & E3 & E4).
  apply (aw_real_free AI ACCT UNIV AI_fake aw aw LB (ms_mem ms) mo WW RNG' sta' p Af nf m' mo' sp AR); rewrite ?E1, ?E4; assumption.
Qed.

Lemma SBf : forall a, 0 <= a < 2 ^ 64 -> CtrFrame.TwinB.stableA AI ms LBk a -> m' (ALib.Mem.wa a) = ms_mem ms (ALib.Mem.wa a).
Proof.
  intros a Ha ST. destruct WOF as (E1 & E2 & E3 & E4). pose proof AR'f as [HWf _]. pose proof AR as [HWw EMw]. pose proof HWw as (AH & _).
  assert (HPw : In (HB p Af nf) (w_LBa WW)) by (rewrite E4; exact HP).
  destruct (LB_classify AI ACCT UNIV AI_fake Wf aw LBk m' mo' HWf) as (KU & KT).
  apply (aw_real_stable AI ACCT UNIV AI_fake aw LB (ms_mem ms) mo WW RNG' sta' (lb_remove p LBa) m' (lb_remove p LBa) LBk sp (lb_remove p LBa) TWP ltac:(intros b _ Hb _; exact Hb) AR);
    [rewrite E1; exact AH'| exact PRES| | | exact Ha| exact ST].
  - intros v Hv UB P. destruct (KU v Hv UB P) as (b & Vb & ->). exists b. split; [| reflexivity].
    pose proof (proj1 Vb) as X. unfold Wf in X. cbn [w_LBa] in X. rewrite E4 in X. exact X.
  - intros v Hv NUB. destruct (KT v Hv NUB) as [(b & Hb & ->)|(b & Vb & ->)].
    + left. exists b. pose proof HWf as (_ & HTf & _). destruct (HTf b Hb) as [HbL' HH]. unfold Wf in HbL'. cbn [w_LBa] in HbL'.
      split; [exact (proj1 (proj1 (lb_remove_In AI _ _ _ _ _ p Af nf b AH HPw) HbL'))|]. split; [rewrite <- E4; exact HbL'|]. split; [exact HH| reflexivity].
    + right. exists b. destruct Vb as [[HbL' NF] HF]. unfold Wf in HbL'. cbn [w_LBa] in HbL'.
      split; [exact (proj1 (proj1 (lb_remove_In AI _ _ _ _ _ p Af nf b AH HPw) HbL'))|]. split; [rewrite <- E4; exact HbL'|]. split; [exact HF| reflexivity].
Qed.

Lemma SBVf : forall a, 0 <= a < 2 ^ 64 -> CtrFrame.TwinB.stableA AI ms LBk a ->
  rb bsegs m' a = rb bsegs (ms_mem ms) a /\ (wb bsegs (ms_mem ms) a = true -> wb bsegs m' a = true).
Proof. exact (CtrFrame.TwinB.SBV_of_raw (CtrFrame.TwinB.stableA AI ms LBk) (ms_mem ms) m' SBf). Qed.
Lemma WBMf : forall a, 0 <= a < two64 -> (in_ranges (aci AI) a \/ (exists a', in_ranges (aci AI) a' /\ a = shad a') \/ (exists a', ATOP <= a' < 2 ^ 47 /\ a = shad a')) ->
  wb bsegs (ms_mem ms) a = true -> wb bsegs m' a = true.
Proof. exact (CtrFrame.TwinB.WBM_of_pres AI _ _ _ _ PRES). Qed.

Definition KEEPf (k0 : int) : Prop := k0 <> kf /\ k0 <> sh /\ tl <> Some k0.

Lemma WINKf : forall k0 len kd, KEEPf k0 -> CtrA.win_lookup wnl k0 = Some (len, kd) ->
  forall a, bv_unsigned (ev E k0) <= a < bv_unsigned (ev E k0) + bv_unsigned (den E len) -> in_user LBk a.
Proof.
  intros k0 len kd (NKf & NKs & _) WL a Ha. pose proof (HeapCtrB.TwinB.win_lookup_In _ _ _ _ WL) as Hin.
  destruct (entry_window k0 len kd Hin) as (_ & _ & b & Hb & SUB & _).
  destruct (kept_block k0 len kd b Hin NKf NKs Hb SUB) as [N1 N2].
  apply in_ivs_In. exists b. split; [apply LB_free_In; auto|]. apply SUB. unfold in_iv. cbn [fst snd]. lia.
Qed.

Lemma VKEEPf : forall k0 rg hs n sh' len, IMap.find k0 (s_regs st) = Some rg -> zero_view rg = Some hs -> KEEPf k0 ->
  block_of_twin (s_facts st) k0 = Some n -> CallV.TwinB.view_parent (s_facts st) (s_regs st) n sh' ->
  CtrA.win_lookup wnl sh' = Some (len, K_TWIN) -> KEEPf sh'.
Proof.
  intros k0 rg hs n sh' len Fk ZV (NKf & NKs & _) BT VPAR WL. split; [| split].
  - intros ->. rewrite WLf in WL. assert (X : CtrLib.K_BLOCK = K_TWIN) by congruence. vm_compute in X. discriminate X.
  - intros ->. unfold no_views_on in NV.
    pose proof (proj1 (IMap.forallb_spec _ _ (so_bst _ _ _ _ _ _ HS)) NV k0 rg Fk) as C. cbv beta in C.
    replace (PrimInt63.eqb k0 sh) with false in C by (symmetry; apply Uint63.eqb_false_spec; exact NKs).
    rewrite ZV, BT in C. destruct VPAR as [(kb & o1 & UB & TW)|(rshp & Frshp & HNp)];
      [rewrite UB, TW, Uint63.eqb_refl in C; cbn in C; discriminate C| rewrite Frshp, HNp in C; cbn [negb] in C; rewrite !Bool.andb_false_r in C; discriminate C].
  -
    destruct consume_common as (rs & _ & _ & _ & _ & _ & [(-> & _)|(s2 & -> & _ & _ & _ & _ & NWIN)]); [discriminate|].
    intros X. injection X as ->. rewrite NWIN in WL. discriminate WL.
Qed.

Lemma TKEEPf : forall k0 rg sh' kb n len, IMap.find k0 (s_regs st) = Some rg -> KEEPf k0 -> CtrA.win_lookup wnl sh' = Some (len, K_TWIN) ->
  block_of_twin (s_facts st) sh' = Some kb -> CtrA.win_lookup wnl kb = Some (n, CtrLib.K_BLOCK) ->
  size_tail_ok (s_facts st) n = true -> tail_named (tail_rhs sh' n) k0 (s_facts st) = true -> KEEPf sh'.
Proof.
  intros k0 rg sh' kb n len Fk (NKf & NKs & NTL) WL BT WLk ST TN. split; [| split].
  - intros ->. rewrite WLf in WL. assert (X : CtrLib.K_BLOCK = K_TWIN) by congruence. vm_compute in X. discriminate X.
  - intros ->. rewrite BTs in BT. injection BT as <-. rewrite WLf in WLk. injection WLk as <-.
    destruct consume_common as (rs & _ & _ & _ & _ & _ & [(_ & _ & _ & NTA)|(s2 & ETL & _ & _ & NT & _)]).
    + exfalso. exact (CallA.TwinB.no_tail_at_sound _ _ _ _ k0 rg (so_bst _ _ _ _ _ _ HS) NTA Fk TN).
    + unfold no_tails_on in NT. pose proof (proj1 (IMap.forallb_spec _ _ (so_bst _ _ _ _ _ _ HS)) NT k0 rg Fk) as C. cbv beta in C.
      rewrite TN in C. cbn [negb] in C. rewrite orb_false_r in C. apply Uint63.eqb_correct in C. subst k0. exact (NTL ETL).
  - destruct consume_common as (rs & _ & _ & _ & _ & _ & [(-> & _)|(s2 & -> & _ & _ & _ & _ & NWIN)]); [discriminate|].
    intros X. injection X as ->. rewrite NWIN in WL. discriminate WL.
Qed.
Lemma SBTf : forall a, 0 <= a < 2 ^ 64 -> sh_cov a -> in_based E (s_regs st) a ->
  rb bsegs m' a = rb bsegs (ms_mem ms) a /\ (wb bsegs (ms_mem ms) a = true -> wb bsegs m' a = true).
Proof.
  intros a Ha SC _. apply (FrameV.TwinB.frame_v_of_raw bsegs).
  destruct SC as [(a' & R & ->)|(v & Hv & R)].
  - exact (proj1 (PRES (shad a') Ha ltac:(right; right; right; exists a'; split; [left; exact R| reflexivity]))).
  - destruct (IMGSH_aci v a Hv R) as (a' & INA & ->).
    exact (proj1 (PRES (shad a') Ha ltac:(right; right; right; exists a'; split; [right; left; exact INA| reflexivity]))).
Qed.

Variables (hargs : list sv) (md : w64) (A : sv) (nw : w64).
Hypothesis Hf : find_op HEAP_ID (s_ops st) = Some hargs.
Hypothesis Eh : hargs = VL md :: A :: VL nw :: rest.
Hypothesis Tnw : wt nw = false.
Hypothesis Nn : nn = Z.to_nat (to_Z (wl nw)).
Hypothesis Ln : (3 * nn <= length rest)%nat.
Hypothesis FOK : fresh_ok st = true.
Variables (Fv : Z -> word) (Gv : Z -> Z -> byte).
Notation E' := (CtrFrame.TwinB.E' E st Fv Gv).
Lemma SBOf : forall o a, In o (s_ops st) -> not_id HEAP_ID o -> 0 <= a < two64 ->
  Exists (fun iv => fst iv <= a < snd iv) (op_fp OPS (op_id o) (map (den E') (op_args o))) -> m' (Z_to_bv 64 a) = ms_mem ms (Z_to_bv 64 a).
Proof.
  intros o a Ho NI Ha FP. unfold not_id in NI. apply Uint63.eqb_false_spec in NI. destruct (OPS_fp_other _ _ a NI FP) as [R|[(a' & R & ->)|(a' & R & ->)]].
  - pose proof (SBf a ltac:(unfold two64 in Ha; lia) ltac:(right; left; exact R)) as E1. unfold ALib.Mem.wa in E1. exact E1.
  - pose proof (proj1 (PRES (shad a') ltac:(unfold two64 in Ha; lia) ltac:(right; right; right; exists a'; split; [right; left; exact R| reflexivity]))) as E1.
    unfold ALib.Mem.wa in E1. exact E1.
  - pose proof (proj1 (PRES (shad a') ltac:(unfold two64 in Ha; lia) ltac:(right; right; right; exists a'; split; [left; exact R| reflexivity]))) as E1.
    unfold ALib.Mem.wa in E1. exact E1.
Qed.
Variables (h1 h2 : list sv).
Hypothesis H1 : heap_del_window_k hargs (VP kf wzero) CtrLib.K_BLOCK = Some h1.
Hypothesis H2 : heap_del_window_k h1 (VP sh wzero) K_TWIN = Some h2.

Definition WBf : window := Win Af nf K_BLOCK.
Definition WTf : window := Win (shad Af) (shlen (nf + 7)) K_TWINz.

Lemma forallb_sub : forall {T} (f : T -> bool) l l', (forall x, In x l' -> In x l) -> forallb f l = true -> forallb f l' = true.
Proof. intros T f l l' SUB H. apply forallb_forall. intros x Hx. exact (proj1 (forallb_forall _ _) H x (SUB x Hx)). Qed.

Lemma forallb_skipn : forall {T} (f : T -> bool) j l, forallb f l = true -> forallb f (skipn j l) = true.
Proof.
  intros T f j. induction j as [|j IH]; intros l H; [exact H|]. destruct l as [|x l]; [reflexivity|]. cbn [skipn]. cbn [forallb] in H.
  apply andb_prop in H as [_ H]. exact (IH l H).
Qed.

Lemma anchors_perm : forall (l l' : list (int * sv * w64)), Permutation l l' -> Permutation (HeapCtrB.TwinB.anchors l) (HeapCtrB.TwinB.anchors l').
Proof. intros l l' P. unfold HeapCtrB.TwinB.anchors. apply Permutation_map. exact P. Qed.

Lemma DEL2 : exists l1 l2 m1 m2,
  decode (map (den E') h2) = Some (w2Z md, den E A, m1 ++ m2, map (den E) (skipn (3 * nn) rest))
  /\ wins_of E nn rest = l1 ++ WBf :: l2 /\ l1 ++ l2 = m1 ++ WTf :: m2
  /\ ~ In WBf (l1 ++ l2) /\ ~ In WTf (m1 ++ m2).
Proof.
  pose proof (HeapCtrB.TwinB.windows_anchored_nodup_anchors _ _ AN) as NDA.
  rewrite Eh in H1.
  destruct (heap_del_window_k_facts E md A nw rest nn kf CtrLib.K_BLOCK h1 wnl eq_refl Tnw Nn Ln NW H1)
    as (ws1 & l1 & len1 & l2 & wl1 & EH1 & I1 & W1 & W1' & T1 & N1 & L1 & SK1 & NW1 & S1 & S2 & S3 & M1 & PM1).
  destruct (HeapCtrB.TwinB.windows_anchored_nodup _ _ kf len1 CtrLib.K_BLOCK lenf CtrLib.K_BLOCK AN I1 (HeapCtrB.TwinB.win_lookup_In _ _ _ _ WLf)) as [-> _].
  rewrite EH1 in H2.
  destruct (heap_del_window_k_facts E md A (wsub nw wone) (ws1 ++ skipn (3 * nn) rest) (pred nn) sh K_TWIN h2 wl1 eq_refl T1 N1 L1 NW1 H2)
    as (ws2 & m1 & len2 & m2 & wl2 & EH2 & I2 & W2 & W2' & T2 & N2 & L2 & SK2 & NW2 & R1 & R2 & R3 & M2 & PM2).
  destruct (HeapCtrB.TwinB.windows_anchored_nodup _ _ sh len2 K_TWIN lent K_TWIN AN (S1 _ I2) (HeapCtrB.TwinB.win_lookup_In _ _ _ _ WLt)) as [-> _].
  destruct twin_sh as (rs & _ & _ & _ & ESH & ELT). destruct owner as (UBf & HTf & _ & NRf & ALf).

  assert (ND1 : List.NoDup (kf :: HeapCtrB.TwinB.anchors wl1)) by (exact (Permutation_NoDup (anchors_perm _ _ PM1) NDA)).
  apply List.NoDup_cons_iff in ND1 as [NKF1 ND1'].
  assert (ND2 : List.NoDup (sh :: HeapCtrB.TwinB.anchors wl2)) by (exact (Permutation_NoDup (anchors_perm _ _ PM2) ND1')).
  apply List.NoDup_cons_iff in ND2 as [NSH2 _].
  assert (ANCH : forall (l : list (int * sv * w64)) k len kd, In (k, len, kd) l -> In k (HeapCtrB.TwinB.anchors l)).
  { intros l k len kd H. unfold HeapCtrB.TwinB.anchors. apply in_map_iff. exists (k, len, kd). auto. }
  exists l1, l2, m1, m2.
  split.
  { rewrite EH2. rewrite (decode_hargs E' md A _ _ (pred (pred nn)) T2 N2 L2).
    assert (RB : forallb (sv_vars_below (s_next st)) rest = true) by exact (CtrFrame.TwinB.rest_below st FOK rest hargs md A nw Hf Eh).
    assert (RB2 : forallb (sv_vars_below (s_next st)) (ws2 ++ skipn (3 * pred nn) (ws1 ++ skipn (3 * nn) rest)) = true).
    { apply (forallb_sub _ rest); [| exact RB]. intros x Hx. apply S3. apply R3. exact Hx. }
    rewrite (CtrFrame.TwinB.den_E' E st Fv Gv A (CtrFrame.TwinB.A_below st FOK rest hargs md A nw Hf Eh)).
    rewrite (CtrFrame.TwinB.wins_of_E' E st Fv Gv _ _ RB2), W2', SK2, SK1.
    rewrite (CtrFrame.TwinB.map_den_E' E st Fv Gv _ (forallb_skipn _ (3 * nn) rest RB)). reflexivity. }
  split. { rewrite W1. unfold WBf. fold Af nf. rewrite KB1. reflexivity. }
  split. { rewrite <- W1', W2. unfold WTf. rewrite ESH, ELT, KT9. reflexivity. }
  split.
  - intros X. rewrite <- W1' in X.
    destruct (HeapCtrB.TwinB.wins_cover E (pred nn) _ wl1 WBf NW1 X) as [KS|(k & len & kd & Ik & EW)]; [cbn in KS; unfold K_BLOCK, K_STACK in KS; lia|].
    unfold WBf in EW. injection EW as E1 E2 E3.
    assert (NKf : k <> kf) by (intros ->; exact (NKF1 (ANCH _ _ _ _ Ik))).
    assert (NKs : k <> sh).
    { intros ->. destruct (HeapCtrB.TwinB.windows_anchored_nodup _ _ sh len kd lent K_TWIN AN (S1 _ Ik) (HeapCtrB.TwinB.win_lookup_In _ _ _ _ WLt)) as [_ ->]. rewrite KT9 in E3. unfold K_BLOCK in E3. lia. }
    destruct (kept_block k len kd (Af, nf) (S1 _ Ik) NKf NKs blockLB ltac:(rewrite <- E1, <- E2; intros a Ha; exact Ha)) as [NE _]. exact (NE eq_refl).
  - intros X. rewrite <- W2' in X.
    destruct (HeapCtrB.TwinB.wins_cover E (pred (pred nn)) _ wl2 WTf NW2 X) as [KS|(k & len & kd & Ik & EW)]; [cbn in KS; unfold K_TWINz, K_STACK in KS; lia|].
    unfold WTf in EW. injection EW as E1 E2 E3.
    assert (NKs : k <> sh) by (intros ->; exact (NSH2 (ANCH _ _ _ _ Ik))).
    assert (NKf : k <> kf) by (intros ->; exact (NKF1 (ANCH _ _ _ _ (R1 _ Ik)))).
    destruct (kept_block k len kd _ (S1 _ (R1 _ Ik)) NKf NKs HTf ltac:(rewrite <- E1, <- E2; intros a Ha; exact Ha)) as [_ NE]. exact (NE eq_refl).
Qed.

Hypothesis AWden : aw = den E A.
Hypothesis HC : cw_holds Cw (w2Z md) (map (den E) (skipn (3 * nn) rest)) LB (wins_of E nn rest) (ms_mem ms).

Lemma freed_off_image : forall a, in_iv (Af, nf) a \/ in_iv (shad Af, shlen (nf + 7)) a -> find_segment bsegs a 1 = None /\ a < ATOP.
Proof.
  intros a Ha. destruct owner as (UBf & HTf & _). pose proof atop_range as ATR. pose proof AR as [HWw _].
  assert (IU : in_user LB a).
  { unfold in_user. apply in_ivs_In. destruct Ha as [Ha|Ha]; [exists (Af, nf); split; [exact blockLB| exact Ha]| exists (shad Af, shlen (nf + 7)); split; [exact HTf| exact Ha]]. }
  split.
  - destruct Ha as [Ha|Ha]; [exact (proj2 (aw_user_ok_asan AI ACCT UNIV AI_fake aw LB (ms_mem ms) mo _ a AWHf blockLB Ha))
                            | exact (proj2 (aw_user_ok_asan AI ACCT UNIV AI_fake aw LB (ms_mem ms) mo _ a AWHf HTf Ha))].
  - destruct (LB_band AI ACCT UNIV AI_fake WW aw LB (ms_mem ms) mo a HWw IU) as [B|[B|B]]; unfold AIMG_HI, KLS in *; lia.
Qed.

Lemma HOLDNf : forall l1 l2 m1 m2,
  decode (map (den E') h2) = Some (w2Z md, den E A, m1 ++ m2, map (den E) (skipn (3 * nn) rest)) ->
  wins_of E nn rest = l1 ++ WBf :: l2 -> l1 ++ l2 = m1 ++ WTf :: m2 -> ~ In WBf (l1 ++ l2) -> ~ In WTf (m1 ++ m2) ->
  op_holds OPS HEAP_ID (map (den E') h2) m' mo'.
Proof.
  intros l1 l2 m1 m2 D W1 W2 NB NT. rewrite OPS_holds1. destruct owner as (UBf & HTf & _ & NRf & ALf).
  assert (IN1 : forall w, In w (l1 ++ l2) <-> In w (wins_of E nn rest) /\ w <> WBf).
  { intros w. rewrite W1. split.
    - intros H. split; [apply in_app_or in H as [H|H]; apply in_or_app; [left; exact H| right; right; exact H]| intros ->; exact (NB H)].
    - intros [H NE]. apply in_app_or in H as [H|[H|H]]; apply in_or_app; [left; exact H| congruence| right; exact H]. }
  assert (IN2 : forall w, In w (m1 ++ m2) <-> In w (l1 ++ l2) /\ w <> WTf).
  { intros w. rewrite W2. split.
    - intros H. split; [apply in_app_or in H as [H|H]; apply in_or_app; [left; exact H| right; right; exact H]| intros ->; exact (NT H)].
    - intros [H NE]. apply in_app_or in H as [H|[H|H]]; apply in_or_app; [left; exact H| congruence| right; exact H]. }
  exists (w2Z md), aw, (m1 ++ m2), (map (den E) (skipn (3 * nn) rest)), LBk, Wf.
  split; [rewrite AWden; exact D|]. split; [exact (proj1 AR'f)|]. split; [| split].
  -
    apply Forall_forall. intros w Hw. apply IN2 in Hw as [Hw NWT]. apply IN1 in Hw as [Hw NWB].
    pose proof (proj1 (Forall_forall _ _) WF w Hw) as (X1 & X2 & X3 & KD). split; [exact X1|]. split; [exact X2|]. split; [exact X3|].
    destruct (HeapCtrB.TwinB.wins_cover E nn rest wnl w NW Hw) as [KS|(k & len & kd & Ik & EW)].
    { left. destruct KD as [[_ C]|[[K _]|[K _]]]; [split; [exact KS| exact C]| rewrite KS in K; unfold K_BLOCK, K_STACK in K; lia| rewrite KS in K; unfold K_SUB, K_STACK in K; lia]. }
    assert (NKf : k <> kf).
    { intros ->. destruct (HeapCtrB.TwinB.windows_anchored_nodup _ _ kf len kd lenf CtrLib.K_BLOCK AN Ik (HeapCtrB.TwinB.win_lookup_In _ _ _ _ WLf)) as [-> ->].
      apply NWB. rewrite EW. unfold WBf. rewrite KB1. reflexivity. }
    assert (NKs : k <> sh).
    { intros ->. destruct (HeapCtrB.TwinB.windows_anchored_nodup _ _ sh len kd lent K_TWIN AN Ik (HeapCtrB.TwinB.win_lookup_In _ _ _ _ WLt)) as [-> ->].
      destruct twin_sh as (rs & _ & _ & _ & ESH & ELT). apply NWT. rewrite EW. unfold WTf. rewrite ESH, ELT, KT9. reflexivity. }
    destruct KD as [[K C]|[[K B]|[K (b & Hb & SUB)]]].
    + left. auto.
    + right; left. split; [exact K|]. apply LB_free_In. split; [exact B|].
      apply (kept_block k len kd (w_iv w) Ik NKf NKs B). rewrite EW. unfold w_iv. cbn [w_lo w_len]. intros a Ha. exact Ha.
    + right; right. split; [exact K|]. exists b. split; [| exact SUB]. apply LB_free_In. split; [exact Hb|].
      apply (kept_block k len kd b Ik NKf NKs Hb). rewrite EW in SUB. unfold w_iv in SUB. cbn [w_lo w_len] in SUB. exact SUB.
  -
    assert (HC1 : cw_holds Cw (w2Z md) (map (den E) (skipn (3 * nn) rest)) LB (wins_of E nn rest) m').
    { apply (cw_frame Cw _ _ _ _ (ms_mem ms) m' HC). intros a Ha U NH.
      apply in_ivs_In in U as (b & Hb & Hin).
      assert (INWIN : forall w, In w (wins_of E nn rest) -> w_kind w <> K_STACK -> in_iv (w_iv w) a -> False).
      { intros w Hw NK Hwa. apply NH. unfold in_ws, heap_ws. apply in_ivs_In. exists (w_iv w). split; [| exact Hwa]. apply in_map. apply filter_In. split; [exact Hw|].
        destruct (Z.eqb_spec (w_kind w) K_STACK); [contradiction| reflexivity]. }
      destruct (iv_eq_dec b (Af, nf)) as [->|N1].
      { exfalso. apply (INWIN WBf); [rewrite W1; apply in_or_app; right; left; reflexivity| cbn; unfold K_BLOCK, K_STACK; lia| exact Hin]. }
      destruct (iv_eq_dec b (shad Af, shlen (nf + 7))) as [->|N2].
      { exfalso. apply (INWIN WTf); [| cbn; unfold K_TWINz, K_STACK; lia| exact Hin].
        assert (X : In WTf (l1 ++ l2)) by (rewrite W2; apply in_or_app; right; left; reflexivity). apply IN1 in X as [X _]. exact X. }
      symmetry. unfold ALib.Mem.wa in *. apply (SBf a ltac:(unfold two64 in Ha; lia)). right; right. apply in_ivs_In. exists b. split; [apply LB_free_In; auto| exact Hin]. }
    assert (INB : In WBf (wins_of E nn rest)) by (rewrite W1; apply in_or_app; right; left; reflexivity).
    pose proof (cw_free Cw _ _ _ _ m' Af nf (l1 ++ l2) HC1 INB IN1) as HC2.
    assert (INT : In WTf (l1 ++ l2)) by (rewrite W2; apply in_or_app; right; left; reflexivity).
    exact (Cw_ghost_free _ _ _ _ m' (shad Af) (shlen (nf + 7)) (m1 ++ m2) HC2 INT IN2).
  -
    pose proof AR as [HWw _]. pose proof HWw as (AHw & HTw & _). destruct WOF as (_ & _ & E3 & E4).
    destruct owner as (_ & _ & (p' & HP' & HPT) & _).
    assert (EP : HB p' Af nf = HB p Af nf).
    { apply (shadow_iv_inj AI AI_fake _ _ _ _ _ (HB p' Af nf) (HB p Af nf) AHw (proj1 (HTw _ HPT)) ltac:(rewrite E4; exact HP)). reflexivity. }
    rewrite EP in HPT.
    apply (ties_free AI ACCT UNIV AI_fake WW aw LB (ms_mem ms) mo (wins_of E nn rest) (l1 ++ l2) (m1 ++ m2) p Af nf RNG' sta' m' HWw TI HPT IN1 IN2).
    intros IP. apply PRSF. rewrite <- E3. exact (ties_prist WW _ TI IP).
Qed.

Variables (r : int) (st1 : sstate) (R' : bvmap 5 word).
Hypothesis CP : call_pre st = Some r.
Hypothesis FS : forget_stack_below_sp_g st = Some st1.
Hypothesis KEPT : forall rg, In rg CtrFrame.TwinB.kept_regsA -> AP.getr R' rg = AP.getr (ms_regs ms) rg.
Hypothesis HF : forall x i, clob_pos x = Some i -> Fv (Z.of_nat i) = AP.getr R' (reg_of_r5 x).
Hypothesis F15 : Fv 15 = AP.getr R' 10%bv.
Hypothesis MINV' : ALib.Mem.mem_inv bsegs m'.
Variables (ks : int) (offs : w64) (rss : region) (ksp : int).
Hypothesis SPR : sp_region st = Some (ks, offs, rss).
Hypothesis Hksp : okey offs = Some ksp.
Hypothesis SPE : sp = bv_unsigned (ev E ks) + keyZ ksp.
Hypothesis AJ : aregions_justified st wnl = true.
Hypothesis K16 : keyZ ksp mod 16 = 0.
Hypothesis LOSP : loZ rss <= keyZ ksp.
Hypothesis STK' : stk bsegs m' (CtrPre.TwinB.sp_lo E st) sp.
Hypothesis FLOOR : ATOP + 4096 <= bv_unsigned (ev E ks) + loZ rss.
Hypothesis Hc : CtrA.count_op HEAP_ID (s_ops st) = 1%nat.
Hypothesis OTH : OTHER mo mo'.
Hypothesis MINVo : op_minv OPS mo'.

Definition delKf : list int := kf :: sh :: match tl with Some s2 => [s2] | None => [] end.
Definition RgF : IMap.t region := CtrFrame.TwinB.RgPg st ks rss ksp [] delKf.
Definition NEWSETf (_ : Z) : Prop := False.

Lemma KEEP_delf : forall k0, ~ In k0 delKf -> KEEPf k0.
Proof.
  intros k0 H. unfold delKf in H. split; [| split].
  - intros ->. apply H. left. reflexivity.
  - intros ->. apply H. right. left. reflexivity.
  - intros X. rewrite X in H. apply H. right. right. left. reflexivity.
Qed.

Lemma freed_band : forall a, in_iv (Af, nf) a \/ in_iv (shad Af, shlen (nf + 7)) a ->
  (a < 0x7fff7000 \/ 0x10007fff8000 <= a) \/ (0x800be200 <= a < shad ATOP).
Proof.
  intros a Ha. pose proof AR as [(AH & _) EM]. destruct WOF as (E1 & E2 & E3 & E4). rewrite E4 in AH.
  destruct (heap_block_facts AI _ _ _ _ _ (HB p Af nf) AH HP ltac:(exists p; reflexivity)) as (NP & (BK & _ & HI & _) & _). cbn [ab_addr ab_size] in NP, BK, HI.
  destruct (shadow_tight Af nf BK HI ltac:(lia)) as [T1 T2]. unfold ablk, AIMG_HI, KLS in BK. unfold in_iv in Ha. cbn [fst snd] in Ha.
  destruct Ha as [Ha|Ha]; [left| right]; lia.
Qed.

Lemma freed_unbased : forall a, in_iv (Af, nf) a \/ in_iv (shad Af, shlen (nf + 7)) a -> ~ in_based E' RgF a.
Proof.
  intros a Ha (k0 & rg & Fk & KZ & RA). destruct (freed_off_image a Ha) as [_ LOW]. destruct owner as (_ & HTf & _).
  assert (SPF : ATOP + 4096 <= sp) by (rewrite SPE; lia).
  destruct (CtrFrame.TwinB.RgPg_range OPS E st ms mo HS FOK Fv Gv LB LBk ks offs rss ksp SPR SPE wnl nn rest AJ WF KEEPf WINKf VKEEPf TKEEPf LOSP FLOOR hargs md A nw Hf Hc Eh Tnw Nn Ln [] delKf
              (NoDup_nil _) KEEP_delf NEWSETf ltac:(intros k1 r1 a1 X; destruct X) k0 rg a Fk KZ RA) as [[X _]|[_ [[_ X]|[_ [X|[X|X]]]]]].
  - destruct X.
  - lia.
  - fold sp in X. lia.
  - exact (freed_apart AI ACCT UNIV AI_fake aw LB (ms_mem ms) mo WW Af nf a AR blockLB HTf Ha X).
  -
    pose proof atop_range as ATR.
    assert (SHA : 0x7fff8000 <= shad ATOP) by (unfold shad, ASHOFF; rewrite Z.shiftr_div_pow2 by lia; change (2 ^ 3) with 8; Z.div_mod_to_equations; lia).
    destruct (sh_cov_band a X) as [C|C]; destruct (freed_band a Ha) as [B|B]; lia.
Qed.

Lemma stF_shape : afree_stF tl st1 r h2 kf sh
  = SS r (rf_set (s_rf (clobber st1)) X10 (VP (addn (s_next st) 15) wzero)) (s_ff st) (s_resv st) RgF (s_facts st)
       (set_op HEAP_ID h2 (s_ops st)) (s_priv st) (PrimInt63.add (addn (s_next st) 15) 1%uint63).
Proof.
  unfold afree_stF. cbv zeta.
  destruct (clobber_fields st1) as (_ & FF & RV & RG & FS0 & OP & PV & NXc).
  assert (F1 : s_pc st1 = s_pc st /\ s_rf st1 = s_rf st /\ s_ff st1 = s_ff st /\ s_resv st1 = s_resv st /\ s_facts st1 = s_facts st
               /\ s_ops st1 = s_ops st /\ s_priv st1 = s_priv st /\ s_next st1 = s_next st).
  { unfold forget_stack_below_sp_g in FS. rewrite SPR, Hksp in FS. injection FS as <-. repeat split; reflexivity. }
  destruct F1 as (_ & _ & FF1 & RV1 & FS1 & OP1 & PV1 & NX1).
  assert (R1 : s_regs st1 = IMap.add ks (region_forget_below rss ksp) (s_regs st)).
  { unfold forget_stack_below_sp_g in FS. rewrite SPR, Hksp in FS. injection FS as <-. reflexivity. }
  assert (XE : s_next (clobber st1) = addn (s_next st) 15).
  { rewrite NXc, NX1. symmetry. destruct (HeapCtr.TwinB.fresh_ok_inv st FOK) as (_ & _ & B). pose proof (int_range (s_next st)) as RR. rewrite two63_eq in RR.
    apply addn_lit; [reflexivity| rewrite wB_two63, two63_eq; lia]. }
  rewrite XE. rewrite (stF_shape_gen (clobber st1) _ (fun R0 => remove_opt tl (IMap.remove sh (IMap.remove kf R0))) h2 _ r).
  rewrite FF, RV, RG, FS0, OP, PV, FF1, RV1, FS1, OP1, PV1, R1. unfold RgF, CtrFrame.TwinB.RgPg, delKf. destruct tl; reflexivity.
Qed.

Theorem free_post : st_ok bsegs OPS E' (afree_stF tl st1 r h2 kf sh) (CtrFrame.TwinB.ms' ms r R' m') mo'.
Proof.
  rewrite stF_shape. destruct DEL2 as (l1 & l2 & m1 & m2 & D & W1 & W2 & NB & NT).
  pose proof (HOLDNf l1 l2 m1 m2 D W1 W2 NB NT) as HOLDN.
  assert (INWS : forall a, in_ws (wins_of E nn rest) a -> in_ws (m1 ++ m2) a \/ in_iv (Af, nf) a \/ in_iv (shad Af, shlen (nf + 7)) a).
  { intros a X. unfold in_ws in X. apply in_ivs_In in X as (v & Hv & Hin). apply in_map_iff in Hv as (w & <- & Hw).
    rewrite W1 in Hw. apply in_app_or in Hw as [Hw|[<-|Hw]]; [| right; left; exact Hin|].
    - assert (X : In w (l1 ++ l2)) by (apply in_or_app; left; exact Hw). rewrite W2 in X. apply in_app_or in X as [X|[<-|X]]; [| right; right; exact Hin|];
        left; unfold in_ws; apply in_ivs_In; exists (w_iv w); (split; [apply in_map; apply in_or_app; auto| exact Hin]).
    - assert (X : In w (l1 ++ l2)) by (apply in_or_app; right; exact Hw). rewrite W2 in X. apply in_app_or in X as [X|[<-|X]]; [| right; right; exact Hin|];
        left; unfold in_ws; apply in_ivs_In; exists (w_iv w); (split; [apply in_map; apply in_or_app; auto| exact Hin]). }
  apply (CtrFrame.TwinB.frame_st_ok AI IMGX IMGX_aci ACCT UNIV OPS AI_fake OPS_fp1 OPS_cov1 OPS_frame_other OPS_fp_other OTHER OPS_mo_other OPS_cov0_img
           E st ms mo HS FOK Fv Gv r st1 CP FS R' m' mo' KEPT HF aw LB LBk AWHf MINV' SBVf SBOf WBMf SBTf ks offs rss ksp SPR SPE wnl nn rest AJ WF KEEPf WINKf VKEEPf TKEEPf
           K16 LOSP STK' FLOOR hargs md A nw Hf Hc Eh Tnw Nn Ln OTH [] delKf (NoDup_nil _)
           ltac:(intros k1 r1 X; destruct X) KEEP_delf NEWSETf ltac:(intros k1 r1 X; destruct X) ltac:(intros k1 r1 a1 X; destruct X)
           ltac:(intros a1 X; destruct X) ltac:(intros a1 X; destruct X) ltac:(intros a1 X; destruct X) ltac:(intros k1 r1 k2 r2 a1 X; destruct X)
           h2 (w2Z md) (den E A) (m1 ++ m2) (map (den E) (skipn (3 * nn) rest)) D HOLDN).
  - intros a X. destruct X.
  -   intros a Ha NIX NWS. destruct (GLib.UG.in_ws_dec (wins_of E nn rest) a) as [IW|NIW]; [| left; exact NIW].
    right. destruct (INWS a IW) as [X|FR]; [contradiction|]. split; [exact (proj1 (freed_off_image a FR))| exact (freed_unbased a FR)].
  -   intros a IB X. pose proof (CtrFrame.TwinB.in_heap_ws _ _ X) as IW. destruct (INWS a IW) as [Y|FR]; [| exfalso; exact (freed_unbased a FR IB)].

    unfold in_ws, heap_ws in X |- *. apply in_ivs_In in X as (v & Hv & Hin). apply in_map_iff in Hv as (w & <- & Hw). apply filter_In in Hw as [Hw KW].
    apply in_ivs_In. exists (w_iv w). split; [| exact Hin]. apply in_map. apply filter_In. split; [| exact KW].
    rewrite W1 in Hw. assert (NFR : forall w0, w0 = WBf \/ w0 = WTf -> in_iv (w_iv w0) a -> False).
    { intros w0 [-> | ->] Hw0; [exact (freed_unbased a (or_introl Hw0) IB)| exact (freed_unbased a (or_intror Hw0) IB)]. }
    apply in_app_or in Hw as [Hw|[<-|Hw]]; [| exfalso; exact (NFR WBf (or_introl eq_refl) Hin)|].
    + assert (X : In w (l1 ++ l2)) by (apply in_or_app; left; exact Hw). rewrite W2 in X. apply in_app_or in X as [X|[<-|X]]; [apply in_or_app; auto| exfalso; exact (NFR WTf (or_intror eq_refl) Hin)| apply in_or_app; auto].
    + assert (X : In w (l1 ++ l2)) by (apply in_or_app; right; exact Hw). rewrite W2 in X. apply in_app_or in X as [X|[<-|X]]; [apply in_or_app; auto| exfalso; exact (NFR WTf (or_intror eq_refl) Hin)| apply in_or_app; auto].
  - exact (so_facts _ _ _ _ _ _ (CtrFrame.TwinB.HS' OPS E st ms mo HS FOK Fv Gv)).
  - rewrite HeapCtr.TwinB.den_VPz. rewrite (CtrFrame.TwinB.ev_E'_fresh E st FOK Fv Gv 15 ltac:(lia)). exact F15.
  - exact MINVo.
Qed.

End FREED.

Lemma afree_block : forall E st ms mo r hargs wnl L RNG sta LBa aw kf sh tl,
  st_ok bsegs OPS E st ms mo -> CtrPre.TwinB.acallG AI ACCT UNIV Cw E st ms mo r hargs wnl L RNG sta LBa aw ->
  find_twin (s_facts st) kf = Some sh -> afree_ok st wnl kf sh = true -> twin_consume st wnl kf sh = Some tl -> getr st X10 = VP kf wzero ->
  exists p lenf, CtrA.win_lookup wnl kf = Some (lenf, CtrLib.K_BLOCK)
    /\ In (HB p (bv_unsigned (ev E kf)) (bv_unsigned (den E lenf))) LBa
    /\ AP.getr (ms_regs ms) 10%bv = Z_to_bv 64 (bv_unsigned (ev E kf))
    /\ ablock_shadow (ms_mem ms) (bv_unsigned (ev E kf)) (bv_unsigned (den E lenf)).
Proof.
  intros E st ms mo r hargs wnl L RNG sta LBa aw kf sh tl HS CF FT FOKk TCAN X10E.
  destruct CF as (LB & ks & offs & rss & ksp & nn & md & A & nw & rest & SPR & Hksp & SPE & K16 & LOSP & FLOOR & Hf & Hc & Eh & Tnw & Nn & Ln & N255
                  & NW & AN & AJ & TS & WF & HC & AWden & (W & WOF & AR & TI)).
  destruct (afree_ok_inv E st ms mo HS wnl kf sh FOKk) as (rf & lenf & lent & Frf & WLf & WLt & BTs & LO0 & POSf & LEf & OTHERS).
  destruct (owner E st ms mo HS wnl nn rest LB aw L RNG sta LBa NW WF W WOF AR TI kf sh tl TCAN rf lenf lent WLf WLt BTs POSf LEf) as (_ & _ & (p & HP & _) & _).
  exists p, lenf. split; [exact WLf|]. split; [exact HP|].
  split; [rewrite <- HeapCtr.TwinB.reg_of_X10, (GlueA.TwinB.getr_RA bsegs OPS E st ms mo HS X10), X10E, HeapCtr.TwinB.den_VPz; symmetry; apply Z_to_bv_bv_unsigned|].
  exact (freed_pattern E st ms mo HS wnl nn rest LB aw L RNG sta LBa NW WF W WOF AR TI kf sh tl TCAN rf lenf lent WLf WLt BTs POSf LEf OTHERS).
Qed.

Definition cfvF (R' : bvmap 5 word) (i : Z) : word :=
  nth (Z.to_nat i)
      [AP.getr R' 1%bv; AP.getr R' 5%bv; AP.getr R' 6%bv; AP.getr R' 7%bv;
       AP.getr R' 11%bv; AP.getr R' 12%bv; AP.getr R' 13%bv; AP.getr R' 14%bv;
       AP.getr R' 15%bv; AP.getr R' 16%bv; AP.getr R' 17%bv;
       AP.getr R' 28%bv; AP.getr R' 29%bv; AP.getr R' 30%bv; AP.getr R' 31%bv; AP.getr R' 10%bv] (Z_to_bv 64 0).
Lemma cfvF_clob : forall R' x i, clob_pos x = Some i -> cfvF R' (Z.of_nat i) = AP.getr R' (reg_of_r5 x).
Proof. intros R' x i H. destruct x; cbn in H; try discriminate; injection H as <-; cbn; f_equal; apply bv_eq; reflexivity. Qed.

Lemma afree_post_okA : forall st sts E ms mo r hargs wnl st1 kf sh tl h1 h2 (L : alayout) (RNG : footprint) (sta : astate) (LBa : list ablock)
    (aw : word) p lenf rr RNG' msP mo',
  st_ok bsegs OPS E st ms mo ->
  call_pre st = Some r -> forget_stack_below_sp_g st = Some st1 ->
  CtrPre.TwinB.acallG AI ACCT UNIV Cw E st ms mo r hargs wnl L RNG sta LBa aw ->
  find_twin (s_facts st) kf = Some sh -> afree_ok st wnl kf sh = true -> no_views_on (s_facts st) (s_regs st) kf sh = true ->
  twin_consume st wnl kf sh = Some tl ->
  heap_del_window_k hargs (VP kf wzero) CtrLib.K_BLOCK = Some h1 -> heap_del_window_k h1 (VP sh wzero) K_TWIN = Some h2 ->
  sts = [afree_stF tl st1 r h2 kf sh] ->
  CtrA.win_lookup wnl kf = Some (lenf, CtrLib.K_BLOCK) ->
  In (HB p (bv_unsigned (ev E kf)) (bv_unsigned (den E lenf))) LBa ->
  let R := ms_regs ms in
  afree_post2 (aci AI) (AHEAP AI) L RNG (AP.getr R 1) (AP.getr R 2) (AP.getr R 3) (AP.getr R 4) (AP.getr R 8) (AP.getr R 9)
     (AP.getr R 18) (AP.getr R 19) (AP.getr R 20) (AP.getr R 21) (AP.getr R 22) (AP.getr R 23) (AP.getr R 24) (AP.getr R 25)
     (AP.getr R 26) (AP.getr R 27) (ms_fregs ms) (ms_fcsr ms) sta LBa p (CtrPre.TwinB.sp_lo E st) (ms_mem ms) rr RNG' msP ->
  ACCT aw L RNG' rr (lb_remove p LBa) mo' -> (aprist sta -> aprist rr) -> op_minv OPS mo' -> OTHER mo mo' ->
  exists stF E1, sts = [stF] /\ env_ext (s_next st) E E1 /\ st_ok bsegs OPS E1 stF msP mo'.
Proof.
  intros st sts E ms mo r hargs wnl st1 kf sh tl h1 h2 L RNG sta LBa aw p lenf rr RNG' msP mo'
         HS CP FS CF FT FOKk NV TCAN H1 H2 -> WLf0 HP R HQ ACP PRSF MINVo OTH.
  destruct CF as (LB & ks & offs & rss & ksp & nn & md & A & nw & rest & SPR & Hksp & SPE & K16 & LOSP & FLOOR & Hf & Hc & Eh & Tnw & Nn & Ln & N255
                  & NW & AN & AJ & TS & WF & HC & AWden & (W & WOF & AR & TI)).
  destruct (afree_ok_inv E st ms mo HS wnl kf sh FOKk) as (rf & lenf' & lent & Frf & WLf & WLt & BTs & LO0 & POSf & LEf & OTHERS).
  rewrite WLf0 in WLf. injection WLf as <-. pose proof WLf0 as WLf.
  destruct (HeapCtr.TwinB.call_pre_inv st r CP) as (FOK & ra0 & Hra0 & WT0 & LT0 & ER).
  destruct HQ as (FPLE & t0 & t1 & t2 & a0 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & m' & EMS & MINV' & STK' & PRES & TWP & AH').
  set (R' := mkR (AP.getr R 1) (AP.getr R 2) (AP.getr R 3) (AP.getr R 4) t0 t1 t2 (AP.getr R 8) (AP.getr R 9) a0 a1 a2 a3 a4 a5 a6 a7
               (AP.getr R 18) (AP.getr R 19) (AP.getr R 20) (AP.getr R 21) (AP.getr R 22) (AP.getr R 23) (AP.getr R 24) (AP.getr R 25)
               (AP.getr R 26) (AP.getr R 27) t3 t4 t5 t6) in *.
  set (Fv := cfvF R'). set (Gv := fun (_ _ : Z) => Z_to_bv 8 0).
  assert (RAEQ : AP.getr R 1%bv = Z_to_bv 64 (to_Z r)).
  { unfold R. rewrite <- HeapCtr.TwinB.reg_of_X1, (GlueA.TwinB.getr_RA bsegs OPS E st ms mo HS X1), Hra0, ER.
    assert (ERA : ra0 = wlit (wl ra0)) by (destruct ra0 as [t l]; cbn in WT0 |- *; subst t; reflexivity). rewrite ERA at 1. apply HeapCtr.TwinB.den_wlit. }
  assert (EMS' : msP = CtrFrame.TwinB.ms' ms r R' m').
  { rewrite EMS. unfold CtrFrame.TwinB.ms'. f_equal. rewrite RAEQ. apply ret_pc_even.
    - pose proof (int_range r) as RR. rewrite two63_eq in RR. lia.
    - pose proof (HeapCtr.TwinB.call_pre_even st r CP) as EV.
      pose proof (land_mk r 1%uint63 ltac:(change (to_Z 1%uint63) with 1; lia)) as LM.
      change (PrimInt63.sub (PrimInt63.lsl 1 1) 1)%uint63 with 1%uint63 in LM. rewrite EV in LM. change (to_Z 0%uint63) with 0 in LM.
      change (2 ^ to_Z 1%uint63) with 2 in LM. lia. }
  eexists. exists (CtrFrame.TwinB.E' E st Fv Gv). split; [reflexivity|]. split; [apply CtrFrame.TwinB.EXT|]. rewrite EMS'.
  apply (free_post E st ms mo HS wnl nn rest LB aw L RNG sta LBa NW AN WF W WOF AR TI
           (cvu_of E st (ms_mem ms) LB nn md A nw rest ltac:(rewrite <- Eh; exact Hf) Nn HC) kf sh NV tl TCAN rf lenf lent Frf WLf WLt BTs LO0 POSf LEf OTHERS
           p RNG' rr m' mo' HP AH' ACP PRSF PRES TWP hargs md A nw Hf Eh Tnw Nn Ln FOK Fv Gv h1 h2 H1 H2 AWden HC r st1 R' CP FS) with (ks := ks) (offs := offs) (rss := rss) (ksp := ksp); try assumption.
  - intros rg Hrg. unfold CtrFrame.TwinB.kept_regsA in Hrg. cbn [In] in Hrg. repeat (destruct Hrg as [<-|Hrg]; [reflexivity|]). destruct Hrg.
  - intros x i Hx. exact (cfvF_clob R' x i Hx).
  - reflexivity.
Qed.

End Free.
End TwinB.
