(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Uint63 PrimString.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType RiscvSemantics State Run.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib Require Import HeapCeil.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import PropExec MState Mem Cells Step Frame Exec TacX.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.As Require Import ASegs AsShadow AsConst AsIface AsIfaceX AsCXXHeap.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.I2 Require Import FxSteps FxAcc.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.I2 Require Import
  W64 ITrie FxSpec FxInstr FxState FxMem FxExec FxRel FxKind FxMemSound FxValSound FxStepSound FxStepMain
  FxRun FxRn FxImage FxHandoff FxHandoff2 FxCellFrame FxRoFrame FxGeom FxGeomA I2Canon I2Mach I2Image I2Run I2RunA.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.I2A Require Import I2AInv I2ANodeLib I2ANodeMem I2AArgs.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Ltac slia := Zify.zify; xlia zchecker.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma ret_of_even : forall l, to_Z l mod 2 = 0 -> to_Z (ret_of l) = to_Z l.
Proof.
  intros l Hl. unfold ret_of. pose proof (i63_range l).
  rewrite Uint63.lsl_spec, Uint63.lsr_spec. change (2 ^ to_Z 1) with 2. change wB with (2 ^ 63).
  rewrite Z.mod_small; [|Z.div_mod_to_equations; slia]. Z.div_mod_to_equations. slia.
Qed.

Lemma ret_pc_of_link : forall l, to_Z l mod 2 = 0 -> ret_pc (Z_to_bv 64 (to_Z l)) = Z_to_bv 64 (to_Z (ret_of l)).
Proof.
  intros l Hl. rewrite (ret_of_even l Hl). pose proof (i63_range l). apply MState.ret_pc_even; slia.
Qed.

(* [comment removed for export] *)
Fixpoint index_of (k : int) (l : list int) : option nat :=
  match l with
  | [] => None
  | x :: r => if (x =? k)%uint63 then Some 0%nat else option_map S (index_of k r)
  end.
Lemma index_of_spec : forall k l i, index_of k l = Some i -> nth_error l i = Some k.
Proof.
  induction l as [|x r IH]; intros i H; cbn in H; [discriminate|].
  destruct (x =? k)%uint63 eqn:E.
  - injection H as <-. apply Uint63.eqb_spec in E. subst. reflexivity.
  - destruct (index_of k r) as [i'|] eqn:E'; [|discriminate]. injection H as <-. cbn. apply IH. reflexivity.
Qed.
Lemma index_of_none : forall k l, index_of k l = None -> ~ In k l.
Proof.
  induction l as [|x r IH]; intros H; cbn in H |- *; [tauto|].
  destruct (x =? k)%uint63 eqn:E; [discriminate|]. destruct (index_of k r); [discriminate|].
  intros [-> | Hin]; [rewrite Uint63.eqb_refl in E; discriminate | exact (IH eq_refl Hin)].
Qed.
Fixpoint nodupb (l : list int) : bool :=
  match l with [] => true | x :: r => negb (existsb (Uint63.eqb x) r) && nodupb r end.
Lemma nodupb_spec : forall l, nodupb l = true -> List.NoDup l.
Proof.
  induction l as [|x r IH]; intros H; [constructor|]. cbn in H. apply andb_true_iff in H as [H1 H2].
  constructor; [|exact (IH H2)]. intros Hin. apply negb_true_iff in H1.
  assert (existsb (Uint63.eqb x) r = true); [|congruence]. apply existsb_exists. exists x. split; [exact Hin | apply Uint63.eqb_refl].
Qed.

Lemma iget_clobber : forall rs t regs k,
  List.NoDup rs -> to_Z t + Z.of_nat (length rs) < 2 ^ 63 ->
  iget k (clobber rs t regs) = match index_of k rs with
                                | Some i => Some (FV (of_Z (to_Z t + Z.of_nat i)) w_zero)
                                | None => iget k regs
                                end.
Proof.
  intros rs t regs k Hnd Ht. destruct (index_of k rs) as [i|] eqn:E.
  - exact (iget_clobber_in rs t regs i k Hnd (index_of_spec _ _ _ E) Ht).
  - exact (iget_clobber_notin rs t regs k (index_of_none _ _ E)).
Qed.

Lemma bptr_eq_dec : forall p q : bptr, {p = q} + {p <> q}.
Proof. intros p q. apply Z.eq_dec. Qed.

Lemma nodup_ids_eq : forall (L : list block) b b', List.NoDup (map blk_id L) -> In b L -> In b' L -> blk_id b = blk_id b' -> b = b'.
Proof.
  induction L as [|x L IH]; intros b b' Hnd Hb Hb' E; [destruct Hb|].
  cbn [map] in Hnd. pose proof (proj1 (NoDup_cons_iff _ _) Hnd) as [Hn Hnd'].
  destruct Hb as [<-|Hb]; destruct Hb' as [<-|Hb']; [reflexivity | | | exact (IH b b' Hnd' Hb Hb' E)].
  - exfalso. apply Hn. rewrite E. apply in_map. exact Hb'.
  - exfalso. apply Hn. rewrite <- E. apply in_map. exact Hb.
Qed.

Lemma rget_regs' : forall F k, (k =? 0)%uint63 = false ->
  FxState.rget F k = match iget k (f_regs F) with Some v => v | None => fv0 end.
Proof. intros F k Hk. unfold FxState.rget. rewrite Hk. reflexivity. Qed.

Lemma regs_match_of_R : forall segs IM rho F L Fr pc fc rsv m rom,
  R segs IM rho F (MS (mkRl L) Fr pc fc rsv m rom) -> regs_match rho F L.
Proof.
  intros segs IM rho F L Fr pc fc rsv m rom HR k Hk.
  pose proof (R_regs _ _ _ _ _ HR (Z_to_bv 5 (Z.of_nat k))) as E.
  unfold Sem.rget in E. cbn [core_of c_regs MS ms_regs] in E.
  assert (Hx : is_x0 (Z_to_bv 5 (Z.of_nat k)) = false).
  { unfold is_x0. rewrite Z_to_bv_unsigned. apply Z.eqb_neq. unfold bv_wrap. change (bv_modulus 5) with 32. rewrite Z.mod_small; slia. }
  rewrite Hx, (reg_get_mkRl L _ Hx) in E. unfold ireg in E.
  rewrite Z_to_bv_unsigned in E. unfold bv_wrap in E. change (bv_modulus 5) with 32 in E. rewrite Z.mod_small in E by slia.
  replace (Z.to_nat (Z.of_nat k - 1)) with (k - 1)%nat in E by slia. exact E.
Qed.

Section Stk.
  Variable segs : list Segment.
  Lemma stk_pres : forall m m' lo hi,
    stk segs m lo hi ->
    (forall a, lo <= a < hi -> m' (wa a) = m (wa a) /\ (wview segs m (wa a) <> None -> wview segs m' (wa a) <> None)) ->
    stk segs m' lo hi.
  Proof.
    intros m m' lo hi (H0 & H1 & Hs) Hm. split; [exact H0|]. split; [exact H1|]. intros a Ha.
    destruct (Hs a Ha) as [Hw [b Hb]]. destruct (Hm a Ha) as [E W]. split; [exact (W Hw)|].
    exists b. unfold mrd in *. rewrite E. exact Hb.
  Qed.
End Stk.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition gremove (tb : int) (G : list gblk) : list gblk := List.filter (fun g => negb (g_tag g =? tb)%uint63) G.

Lemma In_gremove : forall tb G g, In g (gremove tb G) <-> In g G /\ g_tag g <> tb.
Proof.
  intros tb G g. unfold gremove. rewrite filter_In. split.
  - intros [Hin Hn]. split; [exact Hin|]. intros E. rewrite E, Uint63.eqb_refl in Hn. discriminate.
  - intros [Hin Hn]. split; [exact Hin|]. destruct (g_tag g =? tb)%uint63 eqn:E; [|reflexivity].
    apply Uint63.eqb_spec in E. congruence.
Qed.

Lemma bsize_of_map : forall tb G n,
  bsize_of tb (map (fun g => (g_tag g, g_size g)) G) = Some n -> exists gb, In gb G /\ g_tag gb = tb /\ g_size gb = n.
Proof.
  induction G as [|g G IH]; intros n H; cbn [map bsize_of] in H; [discriminate|].
  destruct (g_tag g =? tb)%uint63 eqn:E.
  - injection H as <-. apply Uint63.eqb_spec in E. exists g. split; [left; reflexivity | split; [exact E | reflexivity]].
  - destruct (IH n H) as (gb & Hin & Ht & Hs). exists gb. split; [right; exact Hin | split; assumption].
Qed.

Lemma gremove_notin : forall tb G, ~ In tb (map g_tag G) -> gremove tb G = G.
Proof.
  induction G as [|g G IH]; intros Hn; [reflexivity|]. cbn [gremove List.filter map] in *.
  destruct (g_tag g =? tb)%uint63 eqn:E.
  - apply Uint63.eqb_spec in E. exfalso. apply Hn. left. exact E.
  - cbn [negb]. unfold gremove in IH. rewrite IH by (intros Hin; apply Hn; right; exact Hin). reflexivity.
Qed.

Lemma bremove_map : forall tb G, List.NoDup (map g_tag G) ->
  bremove tb (map (fun g => (g_tag g, g_size g)) G) = map (fun g => (g_tag g, g_size g)) (gremove tb G).
Proof.
  induction G as [|g G IH]; intros Hnd; [reflexivity|]. cbn [map bremove]. cbn [map] in Hnd.
  pose proof (proj1 (NoDup_cons_iff _ _) Hnd) as [Hn Hnd'].
  unfold gremove. cbn [List.filter]. destruct (g_tag g =? tb)%uint63 eqn:E.
  - cbn [negb]. apply Uint63.eqb_spec in E. subst tb. fold (gremove (g_tag g) G). rewrite gremove_notin by exact Hn. reflexivity.
  - cbn [negb map]. f_equal. exact (IH Hnd').
Qed.

Lemma lb_bytes_app' : forall L1 L2 : list block, lb_bytes (L1 ++ L2) = lb_bytes L1 + lb_bytes L2.
Proof. induction L1 as [|b L1 IH]; intros L2; cbn [lb_bytes fold_right app]; [reflexivity|]. unfold lb_bytes in IH. rewrite IH. apply Z.add_assoc. Qed.

Section LB.
  Context {HCEIL : HeapCeil}.
  Variable H : asr.
  Hypothesis HL : lb_remove_laws H.

  Lemma lb_remove_split : forall LB p A n,
    List.NoDup (map blk_id LB) -> In (p, A, n) LB ->
    exists pre post, LB = pre ++ (p, A, n) :: post /\ as_lb_remove H p LB = pre ++ post.
  Proof.
    destruct HL as (L1 & L2 & L3).
    induction LB as [|b LB IH]; intros p A n Hnd Hin; [destruct Hin|].
    cbn [map] in Hnd. pose proof (proj1 (NoDup_cons_iff _ _) Hnd) as [Hn Hnd'].
    destruct Hin as [-> | Hin].
    - exists [], LB. split; [reflexivity|]. cbn [app]. apply L1. exact Hn.
    - assert (Hne : blk_id b <> p).
      { intros E. apply Hn. rewrite E. replace p with (blk_id (p, A, n)) by reflexivity. apply in_map. exact Hin. }
      destruct (IH p A n Hnd' Hin) as (pre & post & E1 & E2).
      exists (b :: pre), post. split; [rewrite E1; reflexivity|]. rewrite (L2 p b LB Hne), E2. reflexivity.
  Qed.

  Lemma lb_remove_facts : forall LB p A n,
    List.NoDup (map blk_id LB) -> In (p, A, n) LB ->
       lb_bytes (as_lb_remove H p LB) = lb_bytes LB - n
    /\ Z.of_nat (length (as_lb_remove H p LB)) = Z.of_nat (length LB) - 1
    /\ (forall b, In b LB -> blk_id b <> p -> In b (as_lb_remove H p LB))
    /\ (forall b, In b (as_lb_remove H p LB) -> In b LB)
    /\ ~ In p (map blk_id (as_lb_remove H p LB)).
  Proof.
    intros LB p A n Hnd Hin. destruct (lb_remove_split LB p A n Hnd Hin) as (pre & post & E1 & E2).
    rewrite E2. subst LB.
    rewrite !lb_bytes_app', !length_app. cbn [length]. rewrite lb_bytes_cons. cbn [blk_size snd].
    split; [slia|]. split; [slia|]. split.
    - intros b Hb Hne. apply in_app_iff in Hb. apply in_app_iff. destruct Hb as [Hb | [<- | Hb]]; [left; exact Hb | exfalso; apply Hne; reflexivity | right; exact Hb].
    - split.
      + intros b Hb. apply in_app_iff in Hb. apply in_app_iff. destruct Hb as [Hb|Hb]; [left; exact Hb | right; right; exact Hb].
      + rewrite map_app in Hnd |- *. cbn [map blk_id fst] in Hnd. intros Hin'.
        apply NoDup_remove_1 in Hnd as Hnd'. apply in_app_iff in Hin'.
        pose proof (NoDup_remove_2 _ _ _ Hnd) as Hn2. apply Hn2. apply in_app_iff. exact Hin'.
  Qed.
End LB.
