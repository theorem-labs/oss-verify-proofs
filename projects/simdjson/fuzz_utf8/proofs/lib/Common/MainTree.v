(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common Require Import PropExec. From OSSVerify.Proofs.simdjson.fuzz_utf8.lib Require Import FPSteps. From OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common Require Import ShapeAlg SpinAlg AgentLib. From OSSVerify.Proofs.simdjson.fuzz_utf8.lib Require Import Spec. From OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common Require Import AsanAcct AxSymExec3 AxSymExec3Sound AxSymRun3 AsanPlanCore AsanPlan AsanPlanSound AsanPlanSound2 AsanInit. From OSSVerify.Proofs.simdjson.fuzz_utf8.lib Require Import AsanNodesArg AsanNodesIO AsanMainLib AsanShape ImgParams MainDefs MallocNodes2 SlotProp MinifyGhost ParserGhost HooksLedger.   (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. (* [comment removed for export] *)
Import ListNotations.
Import AX2. Import AX2S. Import AP. Import APS.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section WithFP1.
Context {fx : FPState}.

(* [comment removed for export] *)
Fixpoint holes_declared (HT : htab) (s : shape) : bool :=
  match s with
  | SNil | SExit _ => true
  | SEmitP _ _ s' => holes_declared HT s'
  | SAlt2 a b => holes_declared HT a && holes_declared HT b
  | SCase _ _ a b => holes_declared HT a && holes_declared HT b
  | SHole h => match ht_of HT h with Some _ => true | None => false end
  | SNext => false
  end.
Definition hole_free (s : shape) : bool := holes_declared [] s.

(* [comment removed for export] *)
Fixpoint splice (HT : htab) (s : shape) : shape :=
  match s with
  | SEmitP fd ps s' => SEmitP fd ps (splice HT s')
  | SAlt2 a b => SAlt2 (splice HT a) (splice HT b)
  | SCase e mid a b => SCase e mid (splice HT a) (splice HT b)
  | SHole h => match sh_of HT h with Some sh => sh | None => SNil end
  | _ => s
  end.

(* [comment removed for export] *)
Definition htab_wf (HT : htab) : bool :=
  forallb (fun e : nat * (acs * shape) => hole_free (snd (snd e)) && shape_vars_lt NX0 (snd (snd e))) HT.

(* [comment removed for export] *)
Definition mcover {X : Type} (HT : htab) (PT : list (nat * X)) : bool :=
  forallb (fun e : nat * (acs * shape) => match lookupT PT (fst e) with Some _ => true | None => false end) HT.

(* [comment removed for export] *)
Definition Fv (C : class) (v : variant) : list kentry := vfacts v ++ facts_of_class C.

(* [comment removed for export] *)
Definition shape_fits (C : class) (X : option shape) (s : shape) : bool :=
  match X with
  | None => class_shape_ok C s
  | Some sh => forallb (fun v => negb (vconsistent C v) ||
                 match sresolve (Fv C v) s, sresolve (Fv C v) sh with
                 | Some a, Some b => shape_equiv a b
                 | _, _ => false
                 end)%bool variants
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Inductive mtree : Type :=
| MLeaf (fuel : nat) (p : plan)                                                (* [comment removed for export] *)
| MSeg (fuel : nat) (p : plan) (HT : htab) (PT : list (nat * mtree))
                                                                               (* [comment removed for export] *)
| MSplit (q : qty) (mid : Z) (le gt : mtree)                                   (* [comment removed for export] *)
| MCase (e : expr) (mid : Z) (le gt : mtree)                                   (* [comment removed for export] *)
| MClass (C' : class) (t : mtree)                                              (* [comment removed for export] *)
| MEmpty.                                                                      (* [comment removed for export] *)

(* [comment removed for export] *)
Section MTreeInd.
  Variable P : mtree -> Prop.
  Hypothesis Hleaf : forall fuel p, P (MLeaf fuel p).
  Hypothesis Hseg : forall fuel p HT PT, (forall j t, In (j, t) PT -> P t) -> P (MSeg fuel p HT PT).
  Hypothesis Hsplit : forall q mid le gt, P le -> P gt -> P (MSplit q mid le gt).
  Hypothesis Hcase : forall e mid le gt, P le -> P gt -> P (MCase e mid le gt).
  Hypothesis Hclass : forall C' t, P t -> P (MClass C' t).
  Hypothesis Hempty : P MEmpty.
  Fixpoint mtree_ind2 (t : mtree) : P t :=
    match t with
    | MLeaf fuel p => Hleaf fuel p
    | MEmpty => Hempty
    | MCase e mid le gt => Hcase e mid le gt (mtree_ind2 le) (mtree_ind2 gt)
    | MClass C' t' => Hclass C' t' (mtree_ind2 t')
    | MSeg fuel p HT PT =>
        Hseg fuel p HT PT
          ((fix go (PT : list (nat * mtree)) : forall j t, In (j, t) PT -> P t :=
              match PT return (forall j t, In (j, t) PT -> P t) with
              | [] => fun j t H => False_ind _ H
              | (j', t') :: PT' => fun j t H =>
                  match H with
                  | or_introl E => eq_ind (j', t') (fun jt => P (snd jt)) (mtree_ind2 t') (j, t) E
                  | or_intror H' => go PT' j t H'
                  end
              end) PT)
    | MSplit q mid le gt => Hsplit q mid le gt (mtree_ind2 le) (mtree_ind2 gt)
    end.
End MTreeInd.

(* [comment removed for export] *)
Definition all_qty : list qty := [QArgc; QL0; QL1; QLook; QFlen; QCfgLen; QCmod; QCnt; QRoom].
Definition qrange (q : qty) : Z * Z :=
  match q with
  | QArgc => (1, 1024) | QL0 => (0, 131071) | QL1 => (0, 131071) | QLook => (0, 4) | QFlen => (0, 2 ^ 26)
  | QCfgLen => (0, 32767) | QCmod => (0, 3) | QCnt => (0, 1) | QRoom => (- 32773, 2 ^ 26)
  end.
(* [comment removed for export] *)
Definition qbounds (C : class) (q : qty) : Z * Z := clamp (cbounds C q) (fst (qrange q)) (snd (qrange q)).
(* [comment removed for export] *)
Definition class_empty (C : class) : bool :=
  existsb (fun q => let a := qbounds C q in snd a <? fst a) all_qty
  || (let f := qbounds C QFlen in let g := qbounds C QCfgLen in let r := qbounds C QRoom in
      (snd r <? fst f - 6 - snd g) || (snd f - 6 - fst g <? fst r)).
(* [comment removed for export] *)
Definition class_le (C C' : class) : bool :=
  forallb (fun q => let a := qbounds C q in let b := cbounds C' q in
                    (snd a <? fst a) || ((fst b <=? fst a) && (snd a <=? snd b)))%bool all_qty.

Section Check.
  Variable ip : imgparams.
  Variable IT : itab.          (* [comment removed for export] *)
  Variable S : segtab.   (* [comment removed for export] *)
  #[local] Notation CHK fuel HS ch C p := (seg_checkV ip IT S fuel HS ch C p).

  Fixpoint mtree_okV (X : option shape) (ch : acs) (C : class) (t : mtree) : bool :=
    match t with
    | MLeaf fuel p =>
        match CHK fuel HS_none ch C p with COk s => shape_fits C X s | CErr _ _ _ => false | CNeed _ => false end
    | MSeg fuel p HT PT =>
        match CHK fuel (hs_of HT) ch C p with
        | COk s =>
            holes_declared HT s && htab_wf HT && mcover HT PT && shape_fits C X (splice HT s) &&
            (fix forest (PT : list (nat * mtree)) : bool :=
               match PT with
               | [] => true
               | (j, t') :: PT' =>
                   match ht_of HT j with Some e => mtree_okV (Some (snd e)) (fst e) C t' | None => true end && forest PT'
               end) PT
        | CErr _ _ _ => false | CNeed _ => false
        end
    | MSplit q mid le gt => mtree_okV X ch (C ++ [(q, QMIN, mid)]) le && mtree_okV X ch (C ++ [(q, mid + 1, QMAX)]) gt
    | MCase e mid le gt => mtree_okV X (mcase_lo ch e mid) C le && mtree_okV X (mcase_hi ch e mid) C gt
    | MClass C' t' => class_le C C' && mtree_okV X ch C' t'
    | MEmpty => class_empty C
    end.

  (* [comment removed for export] *)
  Fixpoint mforest_okV (HT : htab) (C : class) (PT : list (nat * mtree)) : bool :=
    match PT with
    | [] => true
    | (j, t') :: PT' => match ht_of HT j with Some e => mtree_okV (Some (snd e)) (fst e) C t' | None => true end && mforest_okV HT C PT'
    end.
  Lemma mtree_ok_MSeg : forall X ch C fuel p HT PT,
    mtree_okV X ch C (MSeg fuel p HT PT) =
    match CHK fuel (hs_of HT) ch C p with
    | COk s => holes_declared HT s && htab_wf HT && mcover HT PT && shape_fits C X (splice HT s) && mforest_okV HT C PT
    | CErr _ _ _ => false | CNeed _ => false
    end.
  Proof.
    intros. cbn [mtree_okV]. destruct (seg_checkV _ _ _ _ _ _ _ p) as [s| | ]; [|reflexivity|reflexivity].
    f_equal. induction PT as [|[j t'] PT IH]; [reflexivity|]. cbn [mforest_okV]. rewrite IH. reflexivity.
  Qed.

  (* [comment removed for export] *)
  Lemma mtree_ok_leaf : forall X ch C fuel p s,
    CHK fuel HS_none ch C p = COk s -> shape_fits C X s = true -> mtree_okV X ch C (MLeaf fuel p) = true.
  Proof. intros X ch C fuel p s H1 H2. cbn [mtree_okV]. rewrite H1. exact H2. Qed.

  Lemma mtree_ok_seg : forall X ch C fuel p HT PT s,
    CHK fuel (hs_of HT) ch C p = COk s ->
    (holes_declared HT s && htab_wf HT && mcover HT PT && shape_fits C X (splice HT s))%bool = true ->
    mforest_okV HT C PT = true ->
    mtree_okV X ch C (MSeg fuel p HT PT) = true.
  Proof. intros X ch C fuel p HT PT s H1 H2 H3. rewrite mtree_ok_MSeg, H1, H2, H3. reflexivity. Qed.

  Lemma mforest_ok_nil : forall HT C, mforest_okV HT C [] = true.
  Proof. reflexivity. Qed.
  Lemma mforest_ok_cons : forall HT C j t PT chj shj,
    ht_of HT j = Some (chj, shj) -> mtree_okV (Some shj) chj C t = true -> mforest_okV HT C PT = true ->
    mforest_okV HT C ((j, t) :: PT) = true.
  Proof. intros HT C j t PT chj shj H1 H2 H3. cbn [mforest_okV]. rewrite H1. cbn [fst snd]. rewrite H2. exact H3. Qed.
  Lemma mforest_ok_skip : forall HT C j t PT,
    ht_of HT j = None -> mforest_okV HT C PT = true -> mforest_okV HT C ((j, t) :: PT) = true.
  Proof. intros HT C j t PT H1 H2. cbn [mforest_okV]. rewrite H1. exact H2. Qed.

  Lemma mtree_ok_split : forall X ch C q mid le gt,
    mtree_okV X ch (C ++ [(q, QMIN, mid)]) le = true -> mtree_okV X ch (C ++ [(q, mid + 1, QMAX)]) gt = true ->
    mtree_okV X ch C (MSplit q mid le gt) = true.
  Proof. intros X ch C q mid le gt H1 H2. cbn [mtree_okV]. rewrite H1, H2. reflexivity. Qed.
  Lemma mtree_ok_case : forall X ch C e mid le gt,
    mtree_okV X (mcase_lo ch e mid) C le = true -> mtree_okV X (mcase_hi ch e mid) C gt = true ->
    mtree_okV X ch C (MCase e mid le gt) = true.
  Proof. intros X ch C e mid le gt H1 H2. cbn [mtree_okV]. rewrite H1, H2. reflexivity. Qed.
  Lemma mtree_ok_class : forall X ch C C' t,
    class_le C C' = true -> mtree_okV X ch C' t = true -> mtree_okV X ch C (MClass C' t) = true.
  Proof. intros X ch C C' t H0 H1. cbn [mtree_okV]. rewrite H0, H1. reflexivity. Qed.
  Lemma mtree_ok_empty : forall X ch C, class_empty C = true -> mtree_okV X ch C MEmpty = true.
  Proof. intros X ch C H. cbn [mtree_okV]. exact H. Qed.

  Lemma mforest_ok_sound : forall HT C PT j t e,
    mforest_okV HT C PT = true -> In (j, t) PT -> ht_of HT j = Some e -> mtree_okV (Some (snd e)) (fst e) C t = true.
  Proof.
    intros HT C PT j t e. induction PT as [|[j' t'] PT IH]; intros HF Hin He; [destruct Hin|].
    cbn [mforest_okV] in HF. apply andb_prop in HF as [H1 H2].
    destruct Hin as [Heq|Hin]; [|exact (IH H2 Hin He)].
    injection Heq as -> ->. rewrite He in H1. exact H1.
  Qed.
  Lemma mcover_sound {X} : forall HT (PT : list (nat * X)) j e, mcover HT PT = true -> ht_of HT j = Some e -> exists t, lookupT PT j = Some t.
  Proof.
    intros HT PT j e HC He. unfold mcover in HC. rewrite forallb_forall in HC.
    specialize (HC (j, e) (ht_of_In _ _ _ He)). cbn [fst] in HC. destruct (lookupT PT j) as [t|]; [exists t; reflexivity | discriminate].
  Qed.
End Check.
(* [comment removed for export] *)
Definition mtree_ok (ip : imgparams) (IT : itab) (SG : nat -> option segdef) := mtree_okV ip IT (ST SG []).
Definition mforest_ok (ip : imgparams) (IT : itab) (SG : nat -> option segdef) := mforest_okV ip IT (ST SG []).
Strategy expand [mtree_ok mforest_ok].

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma sd_splice : forall (HOLES : nat -> env -> Fs.Fs -> TSet) HT E fs s,
  holes_declared HT s = true ->
  (forall h ch sh, ht_of HT h = Some (ch, sh) -> HOLES h E fs = sd HOLES0 t_nil E fs sh) ->
  sd HOLES t_nil E fs s = sd HOLES0 t_nil E fs (splice HT s).
Proof.
  intros HOLES HT E fs s. induction s as [|c|fd ps s IH|a IHa b IHb|e mid a IHa b IHb|h|]; intros Hd HH; cbn [holes_declared] in Hd;
    cbn [splice sd]; try reflexivity; try discriminate.
  - rewrite IH by assumption. reflexivity.
  - apply andb_prop in Hd as [Ha Hb]. rewrite IHa, IHb by assumption. reflexivity.
  - apply andb_prop in Hd as [Ha Hb]. rewrite IHa, IHb by assumption. reflexivity.
  - unfold sh_of. destruct (ht_of HT h) as [[ch sh]|] eqn:He; [|discriminate]. cbn [snd]. apply (HH h ch sh He).
Qed.

Lemma htab_wf_sound : forall HT h ch sh, htab_wf HT = true -> ht_of HT h = Some (ch, sh) ->
  hole_free sh = true /\ shape_vars_lt NX0 sh = true.
Proof.
  intros HT h ch sh HW He. unfold htab_wf in HW. rewrite forallb_forall in HW.
  specialize (HW _ (ht_of_In _ _ _ He)). cbn [fst snd] in HW. apply andb_prop in HW. exact HW.
Qed.

(* [comment removed for export] *)
Lemma sd_hole_free : forall HOLES HOLES' D E fs s, hole_free s = true -> sd HOLES D E fs s = sd HOLES' D E fs s.
Proof.
  intros HOLES HOLES' D E fs s. unfold hole_free. induction s; cbn [holes_declared sd ht_of]; intros H; try reflexivity; try discriminate.
  - rewrite IHs by exact H. reflexivity.
  - apply andb_prop in H as [H1 H2]. rewrite IHs1, IHs2 by assumption. reflexivity.
  - apply andb_prop in H as [H1 H2]. rewrite IHs1, IHs2 by assumption. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma sd_nil0 : forall E fs s, sd HOLES0 t_nil E fs s [].
Proof. intros E fs s. apply sd_has_nil; [intros; reflexivity | reflexivity]. Qed.
End WithFP1.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section Sound.
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Variable ip : imgparams.
  Variable ph : PhdrInfo.
  #[local] Notation SEGS := (ip_segs ip).
  #[local] Notation A := (ip_A ip).
  #[local] Notation LIM := (ip_limit ip).
  Variable IT : itab.
  Hypothesis IT_ok : itab_sound SEGS IT.
  Variable S : segtab.          (* [comment removed for export] *)
  Hypothesis SG_ok : segs_okV ip IT S.
  Hypothesis GV_ok : gv_ok ip S.
  Hypothesis SEGS_wx : wx_segs_nowrap SEGS.
  Hypothesis SEGS_in_hull : forall a : word, in_hull A (bv_unsigned a) = false -> find_segment SEGS (bv_unsigned a) 1 = None.
  Hypothesis HULL_ok : hull_ok A.
  Hypothesis SHADOW_ok : shadow_ok A.
  (* [comment removed for export] *)
  Variable sp : word.
  Variable rdraw : EntryDraw.   (* [comment removed for export] *)
  Variable brk0 : word.
  Variable argv envp : list (list byte).
  Variable fs : Fs.Fs.
  Variable uid : word.
  Variable hw : word.   (* [comment removed for export] *)
  Hypothesis Hsp : valid_sp sp.
  Hypothesis Hva : valid_argv argv.
  Hypothesis Hve : valid_envp envp.
  Hypothesis Hfit : entry_stack_fits sp argv envp.

  #[local] Notation c := (content_of argv fs).
  #[local] Notation SINV := (SINVm ph sp rdraw brk0 argv envp uid hw (content_of argv fs)).
  #[local] Notation argH := (argH0 ph sp rdraw argv envp uid hw).

  (* [comment removed for export] *)
  Hypothesis Msys : forall (fy : FPState) y, sys_stmt (fx:=fy) SEGS A NX0 LIM SINV argH fs y.
  Hypothesis Mbrk2 : forall (fy : FPState), brk2d_stmt (fx:=fy) SEGS A NX0 LIM SINV argH fs (node_brk2 A LIM).   (* [comment removed for export] *)
  Hypothesis Mmmap : forall (fy : FPState), mmap_stmtW (fx:=fy) SEGS A NX0 LIM SINV argH fs.   (* [comment removed for export] *)
  Hypothesis Mmmapin : forall (fy : FPState), node1_stmt (fx:=fy) SEGS A NX0 LIM SINV argH fs (is_ecall_at SEGS) (node_mmapin A LIM).
  Hypothesis Mmprotect : forall (fy : FPState), node1_stmt (fx:=fy) SEGS A NX0 LIM SINV argH fs (is_ecall_at SEGS) (node_mprotect A LIM).
  Hypothesis Mexit : forall (fy : FPState), exit_stmt (fx:=fy) SEGS A LIM SINV argH fs.
  Hypothesis Mx : forall (fy : FPState) x, x_stmt (fx:=fy) SEGS A NX0 LIM SINV argH fs x.
  Hypothesis Mjoin : forall (fy : FPState), join_stmt (fx:=fy) SEGS A NX0 LIM SINV argH fs.
  (* [comment removed for export] *)
  Hypothesis Mxn : forall T, H_class_prop T argv fs SINV -> forall (fy : FPState) id, MN2.extG_m id = false ->
    ext_stmt_at (fx:=fy) SEGS A NX0 LIM (XNmV ip IT (st_vcs S) T) SINV argH fs id.
  Hypothesis MxnF : forall T, H_class_prop T argv fs SINV -> forall (fy : FPState) id, xnp_extF id = true ->
    ext_stmtF (fx:=fy) SEGS A NX0 LIM (XNmV ip IT (st_vcs S) T) SINV argH fs id.
  Hypothesis MxnG : forall T (fy : FPState) id, MN2.extG_m id = true ->
    ext_stmtG (fy:=fy) SEGS A NX0 LIM (XNmV ip IT (st_vcs S) T) SINV argH fs (PGA.GPall SEGS) id.
  (* [comment removed for export] *)
  Hypothesis MxnW : forall T, H_class_prop T argv fs SINV -> forall (fy : FPState) id args cs ws, xnp_ws id args cs = Some ws ->
    node1_stmtW_at (fx:=fy) SEGS A NX0 LIM SINV argH fs always (XNmV ip IT (st_vcs S) T id args) cs ws.
  Hypothesis MxnW0 : forall T, H_class_prop T argv fs SINV -> forall (fy : FPState) id args cs ws, xnp_ws id args cs = Some ws ->
    node1_stmtW_at (fx:=fy) SEGS A NX0 LIM SINV argH fs always (XNp ip IT T id args) cs ws.
  Hypothesis Mxe : forall (fy : FPState), emit_stmt (fx:=fy) SEGS A NX0 LIM (XEp ip) SINV argH fs.
  Hypothesis MxeW : forall (fy : FPState) id args cs ws, AN.xe_ws id args cs = Some ws ->
    emit_stmtW_at (fx:=fy) SEGS A NX0 LIM (XEp ip) SINV argH fs id args cs ws.
  Hypothesis MsysW : forall (fy : FPState) y cs ws, AP.sys_ws_std y cs = Some ws ->
    node1_stmtW_at (fx:=fy) SEGS A NX0 LIM SINV argH fs (is_ecall_at SEGS) (node_sys A NX0 y) cs ws.
  Hypothesis Mxb : forall T, H_class_prop T argv fs SINV -> forall (fy : FPState), ext2_stmt (fx:=fy) SEGS A NX0 LIM (XBp ip T) SINV argH fs.
  (* [comment removed for export] *)
  Hypothesis MxW : forall (fy : FPState) x args cs ws, AP.x_ws_std x args cs = Some ws ->
    node1_stmtW_at (fx:=fy) SEGS A NX0 LIM SINV argH fs always (node_x SEGS A NX0 x args) cs ws.
  Hypothesis Mxn0 : forall T, H_class_prop T argv fs SINV -> forall (fy : FPState), ext_stmt (fx:=fy) SEGS A NX0 LIM (XNp ip IT T) SINV argH fs.
  Hypothesis MxnF0 : forall T, H_class_prop T argv fs SINV -> forall (fy : FPState) id, xnp_extF id = true ->
    ext_stmtF (fx:=fy) SEGS A NX0 LIM (XNp ip IT T) SINV argH fs id.
  (* [comment removed for export] *)
  Hypothesis VF : forall E M, SINV E M -> know_ok SEGS E M (vfacts (variant_of c)).

  Lemma SINVm_frame' : forall E M M', (forall a, argH E a = true -> M' a = M a) -> SINV E M -> SINV E M'.
  Proof. intros. eapply SINVm_frame; eassumption. Qed.
  Lemma SINVm_agree' : forall E E' M, env_agree NX0 E E' -> SINV E M -> SINV E' M.
  Proof. intros. eapply SINVm_agree; eassumption. Qed.
  Lemma SINVm_blob : forall E M, SINV E M -> forall j, eb E (8 + j)%nat = chunk j (content_of argv fs).
  Proof. intros E M (_ & _ & _ & H) j. apply H. Qed.

  #[local] Notation AH := (argH0_high ph sp rdraw argv envp uid hw Hsp Hva).
  #[local] Notation AA := (argH0_agree ph sp rdraw argv envp uid hw).
  #[local] Notation CSOK := (cs_ok SEGS A LIM SINV argH fs).

  (* [comment removed for export] *)
  Lemma seg_check_sound : forall C HS HOLES,
    H_class_prop (iotab_of C) argv fs SINV ->
    (forall h E E' fs', env_agree NX0 E E' -> HOLES h E fs' = HOLES h E' fs') -> (forall h E fs', HOLES h E fs' []) ->
    (forall (fy : FPState), frm_zero (@fp_csr fy) -> holes_stmt (fx:=fy) SEGS A LIM HS SINV argH HOLES fs (PGA.GPall SEGS)) ->   (* [comment removed for export] *)
    forall fuel p cs s,
      check SEGS IT A NX0 LIM (XNmV ip IT (st_vcs S) (iotab_of C)) (XEp ip) (XBp ip (iotab_of C)) HS KCm (XPv S) BFUELm fuel None cs p = COk s ->
    forall (fy : FPState) E R FULL model, frm_zero (@fp_csr fy) -> CSOK E cs R FULL model ->
      props_ok (PGA.GPall SEGS) E (Mr A argH E cs model FULL) (a_props cs) ->
      srealizes SEGS (cfg_of (fx:=fy) SEGS R (pc cs) FULL model) (sd HOLES t_nil E (m_fs model) s).
  Proof.
    intros C HS HOLES HCL HOa HOn HOs fuel p cs s Hchk fy E R FULL model Hz HC HP.
    (* [comment removed for export] *)
    assert (HT0 : H_class_prop T0 argv fs SINV) by exact I.
    exact (check_sound_top SEGS IT IT_ok A NX0 APC_NX0_min LIM HS
                  (XNmV ip IT (st_vcs S) (iotab_of C)) (XEp ip) (XBp ip (iotab_of C))
                  SEGS_wx SEGS_in_hull HULL_ok SHADOW_ok SINV argH AH AA SINVm_frame' SINVm_agree'
                  HOLES HOa HOn fs KCm (XPv S) (PGA.GPall SEGS)
                  (fun Hhq : xp_hq (XPv S) = true => ltac:(discriminate Hhq))      (* [comment removed for export] *)
                  Msys Mbrk2 Mmmap Mmmapin Mmprotect Mexit Mx Mjoin
                  (Mxn _ HCL) Mxe (Mxb _ HCL) HOs
                  (MxnF _ HCL) MsysW (MxnW _ HCL) MxeW MxW
                  (PGA.GPall_frame SEGS (st_vcs S)) (PGA.Gparse_ok SEGS (st_vcs S) GV_ok) (MxnG _)
                  (segs_ok_sound SEGS IT IT_ok A NX0 APC_NX0_min LIM (XNp ip IT T0) (XEp ip) (XBp ip T0)
                     SEGS_wx SEGS_in_hull HULL_ok SHADOW_ok SINV argH AH AA SINVm_frame' SINVm_agree' fs KCm (XPv S)
                     Msys Mbrk2 Mmmap Mmmapin Mmprotect Mexit Mx Mjoin (Mxn0 _ HT0) Mxe (Mxb _ HT0)
                     (MxnF0 _ HT0) MsysW (MxnW0 _ HT0) MxeW MxW
                     (PGA.GPall SEGS) (PGA.GPall_frame SEGS (st_vcs S)) (PGA.Gparse_ok SEGS (st_vcs S) GV_ok)
                     HKL.sysws_std_reL HKL.xnp_ws_reL HKL.xe_ws_reL HKL.xws_std_reL
                     (HKL.XNp_reL ip IT T0) (HKL.XEp_reL ip) SG_ok)     (* [comment removed for export] *)
                  eq_refl fuel BFUELm p cs s Hchk fy E R FULL model t_nil Hz HC HP eq_refl).
  Qed.

  (* [comment removed for export] *)
  Lemma cs_ok_main_facts : forall E cs R FULL model,
    CSOK E cs R FULL model ->
    (forall n, (n < 8)%nat -> ev E n = ev (E0 ph sp rdraw brk0 argv envp uid hw) n)
    /\ eb E 1%nat = nth 0 argv [] /\ eb E 2%nat = nth 1 argv [] /\ m_fs model = fs
    /\ know_ok SEGS E FULL (vfacts (variant_of c)).
  Proof.
    intros E cs R FULL model HC.
    pose proof (co_sinv _ _ _ _ _ _ _ _ _ _ _ HC) as HS. pose proof HS as HS'.
    destruct HS as [[Hev _] [HB1 [HB2 _]]].
    refine (conj _ (conj HB1 (conj HB2 (conj (co_fs _ _ _ _ _ _ _ _ _ _ _ HC) (VF _ _ HS'))))).
    intros n Hn. apply Hev. unfold NX0. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma cs_ok_pay_start : forall C E cs R FULL model,
    in_class C argv fs = true -> CSOK E cs R FULL model -> CSOK E (pay_start cs C) R FULL model.
  Proof.
    intros C E cs R FULL model HC HCS. unfold pay_start. apply cs_ok_set_kn; [exact HCS|]. apply Forall_app. split.
    - eapply facts_of_class_sound; [eassumption.. | ]. apply (cs_ok_main_facts E cs R FULL model HCS).
    - exact (co_know _ _ _ _ _ _ _ _ _ _ _ HCS).
  Qed.

  Lemma pc_set_kn : forall cs k, pc (set_kn cs k) = pc cs.
  Proof. reflexivity. Qed.

  Lemma in_class_split : forall C q mid,
    in_class C argv fs = true ->
    if qval q argv fs <=? mid then in_class (C ++ [(q, QMIN, mid)]) argv fs = true
    else in_class (C ++ [(q, mid + 1, QMAX)]) argv fs = true.
  Proof.
    intros C q mid HC. pose proof (qval_bounds ph sp rdraw argv envp fs uid hw Hva Hfit q) as Hq.
    destruct (Z.leb_spec (qval q argv fs) mid); rewrite in_class_app, HC; cbn;
      (apply andb_true_intro; split; [|reflexivity]); apply andb_true_intro; split; apply Z.leb_le; lia.
  Qed.

  Lemma cbounds_entry : forall C q lo hi acc,
    In (q, lo, hi) C ->
    lo <= fst (fold_left (fun acc (t : qty * Z * Z) => let '(q', lo', hi') := t in
                           if qty_eqb q q' then (Z.max (fst acc) lo', Z.min (snd acc) hi') else acc) C acc)
    /\ snd (fold_left (fun acc (t : qty * Z * Z) => let '(q', lo', hi') := t in
                         if qty_eqb q q' then (Z.max (fst acc) lo', Z.min (snd acc) hi') else acc) C acc) <= hi.
  Proof.
    assert (MONO : forall C q acc,
      fst acc <= fst (fold_left (fun acc (t : qty * Z * Z) => let '(q', lo', hi') := t in
                                  if qty_eqb q q' then (Z.max (fst acc) lo', Z.min (snd acc) hi') else acc) C acc)
      /\ snd (fold_left (fun acc (t : qty * Z * Z) => let '(q', lo', hi') := t in
                           if qty_eqb q q' then (Z.max (fst acc) lo', Z.min (snd acc) hi') else acc) C acc) <= snd acc).
    { intros C q. induction C as [|[[q' lo'] hi'] C IH]; intros acc; cbn [fold_left]; [lia|].
      destruct (qty_eqb q q'); [|apply IH]. specialize (IH (Z.max (fst acc) lo', Z.min (snd acc) hi')). cbn [fst snd] in IH. lia. }
    intros C q lo hi. induction C as [|[[q' lo'] hi'] C IH]; intros acc Hin; [destruct Hin|].
    cbn [fold_left]. destruct Hin as [E|Hin]; [|apply IH; exact Hin].
    injection E as -> -> ->. replace (qty_eqb q q) with true by (symmetry; apply qty_eqb_eq; reflexivity).
    specialize (MONO C q (Z.max (fst acc) lo, Z.min (snd acc) hi)). cbn [fst snd] in MONO. lia.
  Qed.
  (* [comment removed for export] *)
  Lemma qval_qrange : forall q, fst (qrange q) <= qval q argv fs <= snd (qrange q).
  Proof.
    pose proof (argc_range argv Hva). pose proof (L0_range' argv Hva). pose proof (L1_range' ph sp rdraw argv envp uid hw Hva). pose proof (qlook_range sp argv envp fs Hva Hfit).
    pose proof (cfglen_range (content_of argv fs)). pose proof (flen_range (content_of argv fs)).
    pose proof (bz_range 2 (content_of argv fs)). pose proof (bz_range 1 (content_of argv fs)).
    pose proof (Z.mod_pos_bound (bz 2 (content_of argv fs)) 4 ltac:(lia)).
    assert (0 <= bz 1 (content_of argv fs) / 128 <= 1).
    { split; [apply Z.div_pos; lia |]. assert (bz 1 (content_of argv fs) / 128 < 2) by (apply Z.div_lt_upper_bound; lia). lia. }
    pose proof (room_eq (content_of argv fs)). pose proof (cmod_eq (content_of argv fs)).
    intros q; destruct q; cbn [qval qrange fst snd]; lia.
  Qed.
  Lemma qbounds_sound : forall C q, in_class C argv fs = true -> fst (qbounds C q) <= qval q argv fs <= snd (qbounds C q).
  Proof.
    intros C q HC. unfold qbounds, clamp. cbn [fst snd].
    pose proof (cbounds_sound C q argv fs HC (qval_bounds ph sp rdraw argv envp fs uid hw Hva Hfit q)). pose proof (qval_qrange q). lia.
  Qed.
  Lemma in_class_nonempty : forall C, in_class C argv fs = true -> class_empty C = false.
  Proof.
    intros C HC. apply Bool.not_true_is_false. unfold class_empty. rewrite Bool.orb_true_iff, existsb_exists. intros [(q & _ & H)|H].
    - apply Z.ltb_lt in H. pose proof (qbounds_sound C q HC). lia.
    - pose proof (qbounds_sound C QFlen HC) as BF. pose proof (qbounds_sound C QCfgLen HC) as BG. pose proof (qbounds_sound C QRoom HC) as BR.
      cbn [qval] in BF, BG, BR. rewrite room_eq in BR.
      apply Bool.orb_true_iff in H as [H|H]; apply Z.ltb_lt in H; lia.
  Qed.
  Lemma in_class_weaken : forall C C', class_le C C' = true -> in_class C argv fs = true -> in_class C' argv fs = true.
  Proof.
    intros C C' HLE HC. unfold in_class. apply forallb_forall. intros [[q lo] hi] Hin.
    pose proof (qbounds_sound C q HC) as B.
    unfold class_le in HLE. rewrite forallb_forall in HLE.
    assert (Hq : In q all_qty) by (destruct q; cbn; tauto).
    specialize (HLE q Hq). cbn beta in HLE. apply Bool.orb_prop in HLE as [H0|HLE]; [apply Z.ltb_lt in H0; lia|].
    apply andb_prop in HLE as [H1 H2]. apply Z.leb_le in H1. apply Z.leb_le in H2.
    pose proof (cbounds_entry C' q lo hi (QMIN, QMAX) Hin) as E. unfold cbounds in H1, H2.
    apply andb_true_intro; split; apply Z.leb_le; lia.
  Qed.

  (* [comment removed for export] *)
  Definition DEN (X : option shape) (E : env) (fs' : Fs.Fs) : TSet :=
    match X with None => spec argv fs' | Some sh => sd HOLES0 t_nil E fs' sh end.

  Lemma DEN_nil : forall X E fs', DEN X E fs' [].
  Proof. intros [sh|] E fs'; cbn [DEN]; [apply sd_nil0 | apply spec_nil]. Qed.

  (* [comment removed for export] *)
  Lemma shape_fits_sound : forall C X s E M,
    in_class C argv fs = true -> shape_fits C X s = true ->
    (forall n, (n < 8)%nat -> ev E n = ev (E0 ph sp rdraw brk0 argv envp uid hw) n) ->
    eb E 1%nat = nth 0 argv [] -> eb E 2%nat = nth 1 argv [] ->
    know_ok SEGS E M (vfacts (variant_of c)) ->
    t_eq (sd HOLES0 t_nil E fs s) (DEN X E fs).
  Proof.
    intros C X s E M HC HS Hev HB1 HB2 HV.
    destruct X as [sh|]; cbn [DEN shape_fits] in HS |- *.
    - rewrite forallb_forall in HS. specialize (HS (variant_of c) (variant_in argv fs)).
      rewrite (variant_consistent ph sp rdraw argv envp fs Hva uid hw Hfit C HC) in HS. cbn [negb orb] in HS.
      destruct (sresolve (Fv C (variant_of c)) s) as [a|] eqn:HRa; [|discriminate].
      destruct (sresolve (Fv C (variant_of c)) sh) as [b|] eqn:HRb; [|discriminate].
      assert (HF : know_ok SEGS E M (Fv C (variant_of c))).
      { unfold Fv. apply Forall_app. split; [exact HV | eapply facts_of_class_sound; eassumption]. }
      eapply t_eq_trans; [exact (sresolve_sound SEGS E M _ HF HOLES0 t_nil fs s a HRa)|].
      eapply t_eq_trans; [exact (shape_equiv_sound HOLES0 t_nil E fs a b (sresolve_nocase _ _ _ HRa) (sresolve_nocase _ _ _ HRb) HS)|].
      apply t_eq_sym. exact (sresolve_sound SEGS E M _ HF HOLES0 t_nil fs sh b HRb).
    - exact (class_shape_sound ph sp rdraw brk0 argv envp fs Hsp Hva Hve uid hw Hfit SEGS C s E M HOLES0 t_nil HC HS Hev HB1 HB2 HV).
  Qed.

  (* [comment removed for export] *)
  Theorem mtree_sound : forall t X ch C,
    mtree_okV ip IT S X ch C t = true -> in_class C argv fs = true ->
    match X with Some sh => shape_vars_lt NX0 sh = true | None => True end ->
    forall (fy : FPState) E R FULL model,
      frm_zero (@fp_csr fy) ->
      CSOK E ch R FULL model ->
      props_ok (PGA.GPall SEGS) E (Mr A argH E ch model FULL) (a_props ch) ->      (* [comment removed for export] *)
      srealizes SEGS (cfg_of (fx:=fy) SEGS R (pc ch) FULL model) (DEN X E fs).
  Proof.
    induction t as [fuel p | fuel p HT PT IH | q mid le gt IHle IHgt | e mid le gt IHle IHgt | C' t IHt | ] using mtree_ind2;
      intros X ch C HT0 HC HX fy E R FULL model Hz HCS HPS.
    - (* [comment removed for export] *)
      cbn [mtree_okV] in HT0.
      destruct (seg_checkV _ _ _ _ _ _ _ p) as [s| |] eqn:Hchk; [|discriminate|discriminate].
      pose proof (cs_ok_pay_start C E ch R FULL model HC HCS) as HC2.
      destruct (cs_ok_main_facts E _ R FULL model HC2) as (Hev & HB1 & HB2 & Hfs & HVF).
      pose proof (in_class_H_class ph sp rdraw argv envp fs uid hw Hva Hfit C SINV HC SINVm_blob) as HCL.
      assert (HOa : forall h E1 E2 fs', env_agree NX0 E1 E2 -> HOLES0 h E1 fs' = HOLES0 h E2 fs') by reflexivity.
      assert (HOn : forall h E1 fs', HOLES0 h E1 fs' []) by (intros; reflexivity).
      assert (HOs : forall (fy' : FPState), frm_zero (@fp_csr fy') -> holes_stmt (fx:=fy') SEGS A LIM HS_none SINV argH HOLES0 fs (PGA.GPall SEGS))
        by (intros fy' _ h chh Hh; discriminate Hh).
      unfold seg_check in Hchk.
      pose proof (seg_check_sound C HS_none HOLES0 HCL HOa HOn HOs fuel p _ s Hchk fy E R FULL model Hz HC2 HPS) as RZ.
      rewrite Hfs in RZ. unfold pay_start in RZ. rewrite pc_set_kn in RZ.
      eapply srz_conseq; [exact RZ|].
      exact (shape_fits_sound C X s E _ HC HT0 Hev HB1 HB2 HVF).
    - (* [comment removed for export] *)
      rewrite mtree_ok_MSeg in HT0.
      destruct (seg_checkV _ _ _ _ _ _ _ p) as [s| |] eqn:Hchk; [|discriminate|discriminate].
      apply andb_prop in HT0 as [HT0 HF]. apply andb_prop in HT0 as [HT0 Hfits]. apply andb_prop in HT0 as [HT0 Hcov].
      apply andb_prop in HT0 as [Hdecl Hwf].
      (* [comment removed for export] *)
      set (HOLESL := fun (h : nat) (E' : env) (fs' : Fs.Fs) =>
                       match sh_of HT h with Some sh => sd HOLES0 t_nil E' fs' sh | None => t_nil end).
      assert (HLa : forall h E1 E2 fs', env_agree NX0 E1 E2 -> HOLESL h E1 fs' = HOLESL h E2 fs').
      { intros h E1 E2 fs' Hag. unfold HOLESL, sh_of. destruct (ht_of HT h) as [[chh shh]|] eqn:He; [|reflexivity]. cbn [snd].
        apply (sd_agree NX0); [intros; reflexivity | exact Hag | exact (proj2 (htab_wf_sound HT h chh shh Hwf He))]. }
      assert (HLn : forall h E1 fs', HOLESL h E1 fs' []).
      { intros h E1 fs'. unfold HOLESL. destruct (sh_of HT h); [apply sd_nil0 | reflexivity]. }
      assert (HLs : forall (fy' : FPState), frm_zero (@fp_csr fy') -> holes_stmt (fx:=fy') SEGS A LIM (hs_of HT) SINV argH HOLESL fs (PGA.GPall SEGS)).
      { intros fy' Hz' j chj Hj E1 R1 FULL1 model1 HC1 HP1.
        unfold hs_of in Hj. destruct (ht_of HT j) as [[chj' shj]|] eqn:He; [|discriminate]. cbn [fst] in Hj. injection Hj as ->.
        destruct (mcover_sound HT PT j _ Hcov He) as (t' & Ht').
        pose proof (mforest_ok_sound ip IT S HT C PT j t' _ HF (lookupT_In _ _ _ Ht') He) as Hok. cbn [fst snd] in Hok.
        pose proof (IH j t' (lookupT_In _ _ _ Ht') (Some shj) chj C Hok HC (proj2 (htab_wf_sound HT j chj shj Hwf He))) as RZ.
        cbn [DEN] in RZ. unfold HOLESL, sh_of. rewrite He. cbn [snd]. rewrite (co_fs _ _ _ _ _ _ _ _ _ _ _ HC1). exact (RZ fy' E1 R1 FULL1 model1 Hz' HC1 HP1). }
      pose proof (cs_ok_pay_start C E ch R FULL model HC HCS) as HC2.
      destruct (cs_ok_main_facts E _ R FULL model HC2) as (Hev & HB1 & HB2 & Hfs & HVF).
      pose proof (in_class_H_class ph sp rdraw argv envp fs uid hw Hva Hfit C SINV HC SINVm_blob) as HCL.
      unfold seg_check in Hchk.
      pose proof (seg_check_sound C (hs_of HT) HOLESL HCL HLa HLn HLs fuel p _ s Hchk fy E R FULL model Hz HC2 HPS) as RZ.
      rewrite Hfs in RZ. unfold pay_start in RZ. rewrite pc_set_kn in RZ.
      eapply srz_conseq; [exact RZ|].
      rewrite (sd_splice HOLESL HT E fs s Hdecl).
      2: { intros h chh shh He. unfold HOLESL, sh_of. rewrite He. reflexivity. }
      exact (shape_fits_sound C X (splice HT s) E _ HC Hfits Hev HB1 HB2 HVF).
    - (* [comment removed for export] *)
      cbn [mtree_okV] in HT0. apply andb_prop in HT0 as [H1 H2].
      pose proof (in_class_split C q mid HC) as HC'.
      destruct (qval q argv fs <=? mid); [exact (IHle X ch _ H1 HC' HX fy E R FULL model Hz HCS HPS) | exact (IHgt X ch _ H2 HC' HX fy E R FULL model Hz HCS HPS)].
    - (* [comment removed for export] *)
      cbn [mtree_okV] in HT0. apply andb_prop in HT0 as [H1 H2].
      pose proof (u64_range (edenot E e)) as He. pose proof (co_know _ _ _ _ _ _ _ _ _ _ _ HCS) as HK.
      assert (HB : fst (ebounds (kn ch) e) <= uE E e <= snd (ebounds (kn ch) e)).
      { unfold ebounds. destruct (erange (kn ch) e) as [[blo bhi]|] eqn:Her; cbn [fst snd].
        - exact (erange_sound SEGS E _ (kn ch) e blo bhi HK Her).
        - unfold uE, two64. lia. }
      destruct (Z.leb_spec (uE E e) mid) as [Hm|Hm].
      + apply (IHle X _ C H1 HC HX fy E R FULL model Hz); [| exact HPS]. unfold mcase_lo. apply cs_ok_set_kn; [exact HCS|].
        constructor; [cbn [kentry_ok]; unfold uE in *; lia | exact HK].
      + apply (IHgt X _ C H2 HC HX fy E R FULL model Hz); [| exact HPS]. unfold mcase_hi. apply cs_ok_set_kn; [exact HCS|].
        constructor; [cbn [kentry_ok]; unfold uE, two64 in *; lia | exact HK].
    - (* [comment removed for export] *)
      cbn [mtree_okV] in HT0. apply andb_prop in HT0 as [HLE H1].
      exact (IHt X ch C' H1 (in_class_weaken C C' HLE HC) HX fy E R FULL model Hz HCS HPS).
    - (* [comment removed for export] *)
      cbn [mtree_okV] in HT0. rewrite (in_class_nonempty C HC) in HT0. discriminate HT0.
  Qed.
End Sound.
