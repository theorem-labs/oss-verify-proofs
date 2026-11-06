(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Uint63 PrimString.
From stdpp Require Import bitvector bitvector.tactics.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType RiscvSemantics State Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Mmap Mprotect.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Common.Cfg Require Import
  ShapeAlgBase ShapeCfg NodesCfg LedgerCfg AllocCfg LazyCfg LazyAccCfg AllocLazyCfg EagerCfg CountCfg.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Common.FX Require Import
  W64 ITrie FxSpec FxInstr FxState FxMem FxExec FxRel FxKind FxMemSound FxValSound FxStepSound FxStepMain FxRun FxRn
  FxLazy FxSys FxHandoff FxDrive FxCellFrame FxDrive3 FxDrive3N FxDrive3S FxDrive3C FxDrive3D FxDrive3H FxDrive3T FxDrive3O
  FxDrive3W FxDrive3K.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma jq_int_ok (a b : int) : (a =? b)%uint63 = true -> a = b.
Proof. exact (proj1 (Uint63.eqb_spec a b)). Qed.

Section JqList.
Context {T : Type} (eqb : T -> T -> bool) (eqb_ok : forall a b, eqb a b = true -> a = b).
Fixpoint jq_list (l m : list T) : bool :=
  match l, m with
  | [], [] => true
  | a :: l', b :: m' => if eqb a b then jq_list l' m' else false
  | _, _ => false
  end.
Lemma jq_list_ok : forall l m, jq_list l m = true -> l = m.
Proof.
  induction l as [|a l IH]; intros [|b m] H; cbn [jq_list] in H; try discriminate; [reflexivity|].
  destruct (eqb a b) eqn:E; [|discriminate]. apply eqb_ok in E. subst b. rewrite (IH m H). reflexivity.
Qed.
Fixpoint jq_itrie (s t : itrie T) : bool :=
  match s, t with
  | IEmpty, IEmpty => true
  | ILeaf k v, ILeaf k' v' => if (k =? k')%uint63 then eqb v v' else false
  | INode l r, INode l' r' => if jq_itrie l l' then jq_itrie r r' else false
  | _, _ => false
  end.
Lemma jq_itrie_ok : forall s t, jq_itrie s t = true -> s = t.
Proof.
  induction s as [|k v|l IHl r IHr]; intros [|k' v'|l' r'] H; cbn [jq_itrie] in H; try discriminate; [reflexivity| |].
  - destruct (k =? k')%uint63 eqn:E; [|discriminate]. apply jq_int_ok in E. apply eqb_ok in H. subst. reflexivity.
  - destruct (jq_itrie l l') eqn:E; [|discriminate]. rewrite (IHl _ E), (IHr _ H). reflexivity.
Qed.
Definition jq_option (a b : option T) : bool :=
  match a, b with Some x, Some y => eqb x y | None, None => true | _, _ => false end.
Lemma jq_option_ok a b : jq_option a b = true -> a = b.
Proof. destruct a, b; cbn; intros H; try discriminate; [rewrite (eqb_ok _ _ H)|]; reflexivity. Qed.
End JqList.

Definition jq_bool (a b : bool) : bool := if a then b else negb b.
Lemma jq_bool_ok a b : jq_bool a b = true -> a = b.
Proof. destruct a, b; cbn; intros H; try discriminate; reflexivity. Qed.
Definition jq_pkind (a b : pkind) : bool :=
  match a, b with PKZero, PKZero | PKImage, PKImage | PKUnk, PKUnk => true | _, _ => false end.
Lemma jq_pkind_ok a b : jq_pkind a b = true -> a = b.
Proof. destruct a, b; cbn; intros H; try discriminate; reflexivity. Qed.
Definition jq_rkind (a b : rkind) : bool :=
  match a, b with RK_plain, RK_plain => true | RK_shadow p, RK_shadow q => (p =? q)%uint63 | _, _ => false end.
Lemma jq_rkind_ok a b : jq_rkind a b = true -> a = b.
Proof. destruct a, b; cbn; intros H; try discriminate; [|apply jq_int_ok in H; subst]; reflexivity. Qed.
Definition jq_slot (a b : slot) : bool :=
  match a, b with
  | SK x, SK y => (x =? y)%uint63
  | SV v j, SV w k => if fval_eqb v w then (j =? k)%uint63 else false
  | SU, SU => true
  | _, _ => false
  end.
Lemma jq_slot_ok a b : jq_slot a b = true -> a = b.
Proof.
  destruct a as [x|v j|], b as [y|w k|]; cbn; intros H; try discriminate; [| |reflexivity].
  - apply jq_int_ok in H. subst. reflexivity.
  - destruct (fval_eqb v w) eqn:E; [|discriminate]. apply fval_eqb_eq in E. apply jq_int_ok in H. subst. reflexivity.
Qed.
Definition jq_slots (a b : slots) : bool :=
  if jq_slot (sl0 a) (sl0 b) then if jq_slot (sl1 a) (sl1 b) then if jq_slot (sl2 a) (sl2 b) then if jq_slot (sl3 a) (sl3 b) then
  if jq_slot (sl4 a) (sl4 b) then if jq_slot (sl5 a) (sl5 b) then if jq_slot (sl6 a) (sl6 b) then jq_slot (sl7 a) (sl7 b)
  else false else false else false else false else false else false else false.
Lemma jq_slots_ok a b : jq_slots a b = true -> a = b.
Proof.
  destruct a as [a0 a1 a2 a3 a4 a5 a6 a7], b as [b0 b1 b2 b3 b4 b5 b6 b7]. unfold jq_slots. cbn [sl0 sl1 sl2 sl3 sl4 sl5 sl6 sl7].
  intros H.
  destruct (jq_slot a0 b0) eqn:E0; [|discriminate]. destruct (jq_slot a1 b1) eqn:E1; [|discriminate].
  destruct (jq_slot a2 b2) eqn:E2; [|discriminate]. destruct (jq_slot a3 b3) eqn:E3; [|discriminate].
  destruct (jq_slot a4 b4) eqn:E4; [|discriminate]. destruct (jq_slot a5 b5) eqn:E5; [|discriminate].
  destruct (jq_slot a6 b6) eqn:E6; [|discriminate].
  apply jq_slot_ok in E0, E1, E2, E3, E4, E5, E6, H. subst. reflexivity.
Qed.
Definition jq_cell (a b : cell) : bool :=
  match a, b with CV v, CV w => fval_eqb v w | CU, CU => true | CB s, CB t => jq_slots s t | _, _ => false end.
Lemma jq_cell_ok a b : jq_cell a b = true -> a = b.
Proof.
  destruct a as [v| |s], b as [w| |t]; cbn; intros H; try discriminate; [|reflexivity|].
  - apply fval_eqb_eq in H. subst. reflexivity.
  - apply jq_slots_ok in H. subst. reflexivity.
Qed.
Definition jq_page (p q : page) : bool :=
  if jq_bool (pg_wr p) (pg_wr q) then if jq_pkind (pg_kind p) (pg_kind q) then jq_itrie jq_cell (pg_cells p) (pg_cells q)
  else false else false.
Lemma jq_page_ok p q : jq_page p q = true -> p = q.
Proof.
  destruct p as [w k c], q as [w' k' c']. unfold jq_page. cbn [pg_wr pg_kind pg_cells]. intros H.
  destruct (jq_bool w w') eqn:E1; [|discriminate]. destruct (jq_pkind k k') eqn:E2; [|discriminate].
  apply jq_bool_ok in E1. apply jq_pkind_ok in E2. apply (jq_itrie_ok jq_cell jq_cell_ok) in H. subst. reflexivity.
Qed.
Definition jq_region (r s : region) : bool :=
  if (rg_lo r =? rg_lo s)%uint63 then if (rg_len r =? rg_len s)%uint63 then if (rg_align r =? rg_align s)%uint63 then
  if jq_option jq_pkind (rg_dflt r) (rg_dflt s) then if (rg_clo r =? rg_clo s)%uint63 then if (rg_chi r =? rg_chi s)%uint63 then
  if jq_rkind (rg_kind r) (rg_kind s) then jq_itrie jq_page (rg_pages r) (rg_pages s)
  else false else false else false else false else false else false else false.
Lemma jq_region_ok r s : jq_region r s = true -> r = s.
Proof.
  destruct r as [a1 a2 a3 a4 a5 a6 a7 a8], s as [b1 b2 b3 b4 b5 b6 b7 b8]. unfold jq_region.
  cbn [rg_lo rg_len rg_align rg_dflt rg_pages rg_clo rg_chi rg_kind]. intros H.
  destruct (a1 =? b1)%uint63 eqn:E1; [|discriminate]. destruct (a2 =? b2)%uint63 eqn:E2; [|discriminate].
  destruct (a3 =? b3)%uint63 eqn:E3; [|discriminate]. destruct (jq_option jq_pkind a4 b4) eqn:E4; [|discriminate].
  destruct (a6 =? b6)%uint63 eqn:E6; [|discriminate]. destruct (a7 =? b7)%uint63 eqn:E7; [|discriminate].
  destruct (jq_rkind a8 b8) eqn:E8; [|discriminate].
  apply jq_int_ok in E1, E2, E3, E6, E7. apply (jq_option_ok jq_pkind jq_pkind_ok) in E4. apply jq_rkind_ok in E8.
  apply (jq_itrie_ok jq_page jq_page_ok) in H. subst. reflexivity.
Qed.
Definition jq_fstate (F G : fstate) : bool :=
  if (f_pc F =? f_pc G)%uint63 then if jq_option fval_eqb (f_resv F) (f_resv G) then
  if jq_itrie fval_eqb (f_regs F) (f_regs G) then jq_itrie jq_region (f_mem F) (f_mem G) else false else false else false.
Lemma jq_fstate_ok F G : jq_fstate F G = true -> F = G.
Proof.
  destruct F as [a1 a2 a3 a4], G as [b1 b2 b3 b4]. unfold jq_fstate. cbn [f_pc f_regs f_mem f_resv]. intros H.
  destruct (a1 =? b1)%uint63 eqn:E1; [|discriminate]. destruct (jq_option fval_eqb a4 b4) eqn:E4; [|discriminate].
  destruct (jq_itrie fval_eqb a2 b2) eqn:E2; [|discriminate].
  apply jq_int_ok in E1. apply (jq_option_ok fval_eqb fval_eqb_eq) in E4. apply (jq_itrie_ok fval_eqb fval_eqb_eq) in E2.
  apply (jq_itrie_ok jq_region jq_region_ok) in H. subst. reflexivity.
Qed.

(* [comment removed for export] *)
Definition jq_opk (a b : opk) : bool :=
  match a, b with OpCut, OpCut | OpLazy, OpLazy | OpGrant, OpGrant | OpShadow, OpShadow | OpCommit, OpCommit => true | _, _ => false end.
Lemma jq_opk_ok a b : jq_opk a b = true -> a = b.
Proof. destruct a, b; cbn; intros H; try discriminate; reflexivity. Qed.
Definition jq_vop (a b : vop) : bool := if jq_opk (fst a) (fst b) then fent_eqb (snd a) (snd b) else false.
Lemma jq_vop_ok a b : jq_vop a b = true -> a = b.
Proof.
  destruct a as [o e], b as [o' e']. unfold jq_vop. cbn [fst snd]. intros H. destruct (jq_opk o o') eqn:E; [|discriminate].
  apply jq_opk_ok in E. apply fent_eqb_eq in H. subst. reflexivity.
Qed.
Definition jq_iiz (a b : int * int * Z) : bool :=
  if (fst (fst a) =? fst (fst b))%uint63 then if (snd (fst a) =? snd (fst b))%uint63 then Z.eqb (snd a) (snd b) else false else false.
Lemma jq_iiz_ok a b : jq_iiz a b = true -> a = b.
Proof.
  destruct a as [[a1 a2] a3], b as [[b1 b2] b3]. unfold jq_iiz. cbn [fst snd]. intros H.
  destruct (a1 =? b1)%uint63 eqn:E1; [|discriminate]. destruct (a2 =? b2)%uint63 eqn:E2; [|discriminate].
  apply jq_int_ok in E1, E2. apply Z.eqb_eq in H. subst. reflexivity.
Qed.
Definition jq_izz (a b : int * Z * Z) : bool :=
  if (fst (fst a) =? fst (fst b))%uint63 then if Z.eqb (snd (fst a)) (snd (fst b)) then Z.eqb (snd a) (snd b) else false else false.
Lemma jq_izz_ok a b : jq_izz a b = true -> a = b.
Proof.
  destruct a as [[a1 a2] a3], b as [[b1 b2] b3]. unfold jq_izz. cbn [fst snd]. intros H.
  destruct (a1 =? b1)%uint63 eqn:E1; [|discriminate]. destruct (Z.eqb a2 b2) eqn:E2; [|discriminate].
  apply jq_int_ok in E1. apply Z.eqb_eq in E2, H. subst. reflexivity.
Qed.
Definition jq_fledger (a b : fledger) : bool :=
  if jq_list fent_eqb (fl_maps a) (fl_maps b) then if jq_list fent_eqb (fl_na a) (fl_na b) then
  if (fl_brk a =? fl_brk b)%uint63 then if Z.eqb (fl_c a) (fl_c b) then Z.eqb (fl_S a) (fl_S b) else false else false else false else false.
Lemma jq_fledger_ok a b : jq_fledger a b = true -> a = b.
Proof.
  destruct a as [a1 a2 a3 a4 a5], b as [b1 b2 b3 b4 b5]. unfold jq_fledger. cbn [fl_maps fl_na fl_brk fl_c fl_S]. intros H.
  destruct (jq_list fent_eqb a1 b1) eqn:E1; [|discriminate]. destruct (jq_list fent_eqb a2 b2) eqn:E2; [|discriminate].
  destruct (a3 =? b3)%uint63 eqn:E3; [|discriminate]. destruct (Z.eqb a4 b4) eqn:E4; [|discriminate].
  apply (jq_list_ok fent_eqb fent_eqb_eq) in E1, E2. apply jq_int_ok in E3. apply Z.eqb_eq in E4, H. subst. reflexivity.
Qed.

(* [comment removed for export] *)
Section JqSuffix.
Context {T : Type} (eqb : T -> T -> bool) (eqb_ok : forall a b, eqb a b = true -> a = b).
Fixpoint jq_suffix (lp lc : list T) : bool :=
  if jq_list eqb lp lc then true
  else match lc with [] => false | _ :: lc' => jq_suffix lp lc' end.
Lemma jq_suffix_ok : forall lc lp, jq_suffix lp lc = true -> exists pre, lc = pre ++ lp.
Proof.
  induction lc as [|a lc IH]; intros lp H; cbn [jq_suffix] in H.
  - destruct (jq_list eqb lp []) eqn:E; [|discriminate]. apply (jq_list_ok eqb eqb_ok) in E. subst lp. exists []. reflexivity.
  - destruct (jq_list eqb lp (a :: lc)) eqn:E.
    + apply (jq_list_ok eqb eqb_ok) in E. subst lp. exists []. reflexivity.
    + destruct (IH lp H) as [pre ->]. exists (a :: pre). reflexivity.
Qed.
End JqSuffix.

(* [comment removed for export] *)
Definition ledger_weaker (Lp Lc : fledger3) : bool :=
  if jq_fledger (fl3 Lp) (fl3 Lc) then if jq_list fent_eqb (fl_all Lp) (fl_all Lc) then if jq_list jq_vop (fl_ops Lp) (fl_ops Lc) then
  if jq_list fent_eqb (fl_lazy Lp) (fl_lazy Lc) then if jq_list fent_eqb (fl_allow Lp) (fl_allow Lc) then
  if Z.eqb (fl_Ab Lp) (fl_Ab Lc) then if Z.eqb (fl_E Lp) (fl_E Lc) then if jq_list fent_eqb (fl_ex Lp) (fl_ex Lc) then
  if jq_suffix jq_iiz (fl_ord Lp) (fl_ord Lc) then jq_suffix jq_izz (fl_res Lp) (fl_res Lc)
  else false else false else false else false else false else false else false else false else false.

Lemma ledger_weaker_ok Lp Lc : ledger_weaker Lp Lc = true ->
  exists oc rc, Lc = FL3 (fl3 Lp) (fl_all Lp) (fl_ops Lp) (fl_lazy Lp) (fl_allow Lp) (fl_Ab Lp) (fl_E Lp) (fl_ex Lp)
                         (oc ++ fl_ord Lp) (rc ++ fl_res Lp).
Proof.
  destruct Lp as [a1 a2 a3 a4 a5 a6 a7 a8 a9 a10], Lc as [b1 b2 b3 b4 b5 b6 b7 b8 b9 b10]. unfold ledger_weaker.
  cbn [fl3 fl_all fl_ops fl_lazy fl_allow fl_Ab fl_E fl_ex fl_ord fl_res]. intros H.
  destruct (jq_fledger a1 b1) eqn:E1; [|discriminate]. destruct (jq_list fent_eqb a2 b2) eqn:E2; [|discriminate].
  destruct (jq_list jq_vop a3 b3) eqn:E3; [|discriminate]. destruct (jq_list fent_eqb a4 b4) eqn:E4; [|discriminate].
  destruct (jq_list fent_eqb a5 b5) eqn:E5; [|discriminate]. destruct (Z.eqb a6 b6) eqn:E6; [|discriminate].
  destruct (Z.eqb a7 b7) eqn:E7; [|discriminate]. destruct (jq_list fent_eqb a8 b8) eqn:E8; [|discriminate].
  destruct (jq_suffix jq_iiz a9 b9) eqn:E9; [|discriminate].
  apply jq_fledger_ok in E1. apply (jq_list_ok fent_eqb fent_eqb_eq) in E2, E4, E5, E8. apply (jq_list_ok jq_vop jq_vop_ok) in E3.
  apply Z.eqb_eq in E6, E7. destruct (jq_suffix_ok jq_iiz jq_iiz_ok _ _ E9) as [oc ->].
  destruct (jq_suffix_ok jq_izz jq_izz_ok _ _ H) as [rc ->]. subst. exists oc, rc. reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section Drive3JDefs.
Local Open Scope uint63_scope.
Variable IM : fimage.
Variable code : itrie finstr.

(* [comment removed for export] *)
Definition xpc_ask (xask : fstate -> option (int * int)) (F : fstate) (L3 : fledger3) (n : int) : option dres3 :=
  match xask F with
  | Some (t, thr) =>
      match refine3 (fl3 L3) F n t thr with
      | Some (Fa, Fb) => Some (D3Two Fa L3 n Fb L3 n)
      | None => None
      end
  | None => None
  end.

(* [comment removed for export] *)
Variable x : fstate -> fledger3 -> int -> option dres3.
(* [comment removed for export] *)
Variable kw : nat.
Variable rounds : nat.

(* [comment removed for export] *)
Fixpoint run_to (jpc : int) (r : nat) (F : fstate) (L : fledger3) (n : int) : option (fstate * fledger3 * int) :=
  match r with
  | O => None
  | S r' =>
      match fx_run IM code jpc (Nat.min kw 61) F with
      | (F1, SBreak, _) => Some (F1, L, n)
      | (F1, SFuel, _) => run_to jpc r' F1 L n
      | (F1, SStuck _, _) =>
          match x F1 L n with
          | Some (D3One F2 L2 n2) => run_to jpc r' F2 L2 n2
          | _ => None
          end
      | (_, SEcall, _) => None
      end
  end.

(* [comment removed for export] *)
Fixpoint widen_bounds (Mp : itrie region) (ts : list int) (F : fstate) (n : int) : option fstate :=
  match ts with
  | [] => Some F
  | t :: ts' =>
      match iget t Mp, iget t (f_mem F) with
      | Some rp, Some rc =>
          if (t <? n) && (rg_clo rp <=? rg_clo rc) && (rg_chi rc <=? rg_chi rp)
          then widen_bounds Mp ts' (set_bounds F t rc (rg_clo rp) (rg_chi rp)) n
          else None
      | _, _ => None
      end
  end.

(* [comment removed for export] *)
Definition forget1 (F : fstate) (r n : int) : fstate :=
  FS (f_pc F) (iset r (FV n w_zero) (f_regs F)) (f_mem F) (f_resv F).
Fixpoint forget_regs (rs : list int) (F : fstate) (n : int) : option (fstate * int) :=
  match rs with
  | [] => Some (F, n)
  | r :: rs' =>
      if (0 <? r) && (r <? 32) && tag_ok F n then forget_regs rs' (forget1 F r n) (n + 1) else None
  end.

(* [comment removed for export] *)
Definition jplan : Type := (int * list int * list int)%type.

(* [comment removed for export] *)
Definition join_child (Fp : fstate) (Lp : fledger3) (plan : jplan) (c : fstate * fledger3 * int) : option (fstate * int) :=
  let '(jpc, _, ts) := plan in
  match run_to jpc rounds (fst (fst c)) (snd (fst c)) (snd c) with
  | Some (F1, L1, n1) =>
      if ledger_weaker Lp L1 then
        match widen_bounds (f_mem Fp) ts F1 n1 with
        | Some F2 => if tag_ok F2 n1 then Some (F2, n1) else None
        | None => None
        end
      else None
  | None => None
  end.

Definition join2 (Fp : fstate) (Lp : fledger3) (plan : jplan) (c1 c2 : fstate * fledger3 * int)
    : option (fstate * fledger3 * int) :=
  let '(_, rs, _) := plan in
  match join_child Fp Lp plan c1, join_child Fp Lp plan c2 with
  | Some (FA, nA), Some (FB, nB) =>
      let n0 := if nA <? nB then nB else nA in
      match forget_regs rs FA n0, forget_regs rs FB n0 with
      | Some (FA', nJ), Some (FB', _) =>
          if negb (f_pc FA' =? f_pc Fp) && jq_fstate FA' FB' then Some (FA', Lp, nJ) else None
      | _, _ => None
      end
  | _, _ => None
  end.

(* [comment removed for export] *)
Fixpoint join_first (Fp : fstate) (Lp : fledger3) (plans : list jplan) (c1 c2 : fstate * fledger3 * int)
    : option (fstate * fledger3 * int) :=
  match plans with
  | [] => None
  | plan :: rest =>
      match join2 Fp Lp plan c1 c2 with
      | Some J => Some J
      | None => join_first Fp Lp rest c1 c2
      end
  end.

(* [comment removed for export] *)
Variable planner : fstate -> fledger3 -> int -> fstate * fledger3 * int -> fstate * fledger3 * int -> list jplan.

Definition xpc_join (F : fstate) (L3 : fledger3) (n : int) : option dres3 :=
  match x F L3 n with
  | Some (D3Two F2 L2 n2 F3 L3' n3) =>
      match join_first F L3 (planner F L3 n (F2, L2, n2) (F3, L3', n3)) (F2, L2, n2) (F3, L3', n3) with
      | Some (FJ, LJ, nJ) => Some (D3One FJ LJ nJ)
      | None => Some (D3Two F2 L2 n2 F3 L3' n3)
      end
  | r => r
  end.
End Drive3JDefs.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section Drive3J.
Variable cfg : SpuriousCfg.
Variable segs : list Segment.
Variable IM : fimage.
Variable code : itrie finstr.
Hypothesis Hcode : code_ok segs code.
Hypothesis Halloc : sc_alloc cfg = false.
Variable R0 : list (word * word).
Variable Rb Rc Lim : Z.
Hypothesis HRb : live_bytes R0 <= Rb.
Hypothesis HRc : Z.of_nat (length R0) <= Rc.
Variable keep : list int.
Variable mem0 : word -> option byte.
Variable XI : (int -> word) -> Model -> Prop.
Variable xtags : list int.
Hypothesis XI_rho : forall rho rho' m, (forall t, In t xtags -> rho' t = rho t) -> XI rho m -> XI rho' m.
Hypothesis XI_vm : forall rho m m', same_but_vm m m' -> XI rho m -> XI rho m'.
Variable fr0 : bvmap 5 word.
Variable fc0 : bv 32.
Variable rom0 : word -> option byte.
Variable hi : word -> Prop.
Variable wb0 : word.
Variable na0 lz0 : list (word * word).
Variable brk0 : word.
Variable A0 : list (Z * Z).

Local Abbreviation D3 := (DInv3 cfg segs IM R0 Lim keep mem0 XI xtags fr0 fc0 rom0 hi wb0 na0 lz0 brk0 A0).
Local Abbreviation PX := (pext IM).
Local Abbreviation POK := (pc_ok3 cfg segs IM R0 Lim keep mem0 XI xtags fr0 fc0 rom0 hi wb0 na0 lz0 brk0 A0).
Local Abbreviation RCH := (reach cfg segs IM R0 Lim keep mem0 XI xtags fr0 fc0 rom0 hi wb0 na0 lz0 brk0 A0).
Local Abbreviation rbind := (reach_bind cfg segs IM R0 Lim keep mem0 XI xtags fr0 fc0 rom0 hi wb0 na0 lz0 brk0 A0).
Local Abbreviation rret := (reach_ret cfg segs IM R0 Lim keep mem0 XI xtags fr0 fc0 rom0 hi wb0 na0 lz0 brk0 A0).

(* [comment removed for export] *)
Lemma POK_reach n rho F L3 ms m res :
  POK n rho F L3 res ms m -> RCH n rho F L3 ms m (fun n' _ F' L' _ _ => dres3_in (F', L', n') res).
Proof.
  intros [H1 H2]. split.
  - intros T HT. apply H1. intros F' L' n' rho' ms' m' Hin HD HX. exact (HT n' rho' F' L' ms' m' Hin HD HX).
  - destruct H2 as (F' & L' & n' & rho' & ms' & m' & Hin & HD & HX & Hs). exists n', rho', F', L', ms', m'. auto.
Qed.

Lemma reach_mono n rho F L3 ms m (P Q : sprop) :
  RCH n rho F L3 ms m P -> (forall n' rho' F' L' ms' m', P n' rho' F' L' ms' m' -> Q n' rho' F' L' ms' m') ->
  RCH n rho F L3 ms m Q.
Proof.
  intros HP HPQ. apply (rbind n rho F L3 ms m P Q HP).
  intros n' rho' F' L' ms' m' Hp HD. apply rret; [exact HD | exact (HPQ _ _ _ _ _ _ Hp)].
Qed.

(* [comment removed for export] *)
Lemma reach_to n rho F L3 ms m n' rho' F' L' (P : sprop) :
  D3 n' rho' F' L' ms m -> PX n rho F L3 ms m n' rho' F' L' ms m -> P n' rho' F' L' ms m -> RCH n rho F L3 ms m P.
Proof.
  intros HD HX HP. split.
  - intros T HT. exact (HT n' rho' F' L' ms m HP HD HX).
  - exists n', rho', F', L', ms, m. split; [exact HP|]. split; [exact HD|]. split; [exact HX | apply star_cfg_refl].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Theorem xpc_ask_sound xask n rho F L3 ms m res :
  xpc_ask xask F L3 n = Some res -> D3 n rho F L3 ms m -> POK n rho F L3 res ms m.
Proof.
  intros Hx HD. unfold xpc_ask in Hx. destruct (xask F) as [[t thr]|]; [|discriminate].
  destruct (refine3 (fl3 L3) F n t thr) as [[Fa Fb]|] eqn:Href; [|discriminate]. injection Hx as <-.
  destruct (mfr_refine3 IM n rho F L3 ms (fl3 L3) t thr Fa Fb Href) as [Hma Hmb].
  assert (Hdx : dext n rho m n rho m) by exact (dext_refl R0 rom0 hi n rho m).
  apply (reach_POK cfg segs IM R0 Lim keep mem0 XI xtags fr0 fc0 rom0 hi wb0 na0 lz0 brk0 A0).
  destruct (DInv3_refine3 cfg segs IM R0 Lim keep mem0 XI xtags fr0 fc0 rom0 hi wb0 na0 lz0 brk0 A0 (fun _ => true)
              n rho F L3 ms m t thr Fa Fb HD Href) as [HDa|HDb].
  - apply (reach_to n rho F L3 ms m n rho Fa L3); [exact HDa | split; [exact Hdx | exact Hma] |].
    cbn [dres3_in]. left. reflexivity.
  - apply (reach_to n rho F L3 ms m n rho Fb L3); [exact HDb | split; [exact Hdx | exact Hmb] |].
    cbn [dres3_in]. right. reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma DInv3_weaken n rho F Lc Lp ms m :
  ledger_weaker Lp Lc = true -> D3 n rho F Lc ms m -> D3 n rho F Lp ms m.
Proof.
  intros Hw HD. destruct (ledger_weaker_ok Lp Lc Hw) as (oc & rc & ->).
  destruct HD as (HDI & HL & HS & HX). split; [exact HDI|]. split; [|split; [|exact HX]].
  - destruct HL. constructor; try assumption.
    + cbn [fl_ord] in lp_ord. apply Forall_app in lp_ord. exact (proj2 lp_ord).
    + cbn [fl_res] in lp_res. apply Forall_app in lp_res. exact (proj2 lp_res).
  - destruct HS. constructor; assumption.
Qed.

Lemma PX_weaken n rho F Lc Lp ms m :
  ledger_weaker Lp Lc = true -> PX n rho F Lc ms m n rho F Lp ms m.
Proof.
  intros Hw. destruct (ledger_weaker_ok Lp Lc Hw) as (oc & rc & ->).
  split; [exact (dext_refl R0 rom0 hi n rho m)|].
  exists []. split; [cbn [fl_ops]; symmetry; apply app_nil_r|]. split; [constructor|]. split; [|split].
  - intros; reflexivity.
  - intros y Hy. left. exact Hy.
  - intros y Hy. left. exact Hy.
Qed.
(* [comment removed for export] *)
(* [comment removed for export] *)
Section Join.
Variable x : fstate -> fledger3 -> int -> option dres3.
Hypothesis x_sound : forall n rho F L3 ms m res,
  x F L3 n = Some res -> D3 n rho F L3 ms m -> POK n rho F L3 res ms m.
Variable kw : nat.
Variable rounds : nat.

Lemma run_to_reach jpc : forall r n rho F L ms m F' L' n',
  run_to IM code x kw jpc r F L n = Some (F', L', n') -> D3 n rho F L ms m ->
  RCH n rho F L ms m (fun n'' _ F'' L'' _ _ => n'' = n' /\ F'' = F' /\ L'' = L').
Proof.
  induction r as [|r IH]; intros n rho F L ms m F' L' n' H HD; [discriminate H|].
  cbn [run_to] in H.
  destruct (fx_run IM code jpc (Nat.min kw 61) F) as [[F1 st] c] eqn:Erun.
  pose proof (reach_run cfg segs IM code Hcode R0 Lim keep mem0 XI xtags fr0 fc0 rom0 hi wb0 na0 lz0 brk0 A0
                n rho F L ms m jpc (Nat.min kw 61) F1 st c (Nat.le_min_r _ _) Erun HD) as Hr1.
  destruct st as [| | |sc].
  - apply (rbind _ _ _ _ _ _ _ _ Hr1). intros n1 rho1 F1' L1 ms1 m1 (-> & -> & -> & ->) HD1.
    exact (IH _ _ _ _ _ _ _ _ _ H HD1).
  - discriminate H.
  - injection H as <- <- <-. apply (reach_mono _ _ _ _ _ _ _ _ Hr1).
    intros n1 rho1 F1' L1 ms1 m1 (-> & _ & -> & ->). repeat split.
  - destruct (x F1 L n) as [[F2 L2 n2|]|] eqn:Ex; try discriminate H.
    apply (rbind _ _ _ _ _ _ _ _ Hr1). intros n1 rho1 F1' L1 ms1 m1 (-> & -> & -> & ->) HD1.
    pose proof (POK_reach _ _ _ _ _ _ _ (x_sound _ _ _ _ _ _ _ Ex HD1)) as Hr2.
    apply (rbind _ _ _ _ _ _ _ _ Hr2). intros n3 rho3 F3 L3' ms3 m3 Hin HD3.
    cbn [dres3_in] in Hin. injection Hin as -> -> ->.
    exact (IH _ _ _ _ _ _ _ _ _ H HD3).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma D3_bounds n rho F L ms m t rg :
  D3 n rho F L ms m -> iget t (f_mem F) = Some rg ->
  to_Z (rg_clo rg) <= bv_unsigned (rho t) <= to_Z (rg_chi rg).
Proof.
  intros (HDI & _) Hg. pose proof HDI as (HRn & H0 & _).
  pose proof (Rn_R segs IM n rho F ms HRn H0) as HR.
  destruct (proj1 (R_mem _ _ _ _ _ HR) t rg Hg) as [Hrok _].
  destruct Hrok as (_ & _ & _ & _ & _ & Hb & _). exact Hb.
Qed.

Lemma widen_reach Mp : forall ts n rho F L ms m F',
  widen_bounds Mp ts F n = Some F' -> D3 n rho F L ms m ->
  RCH n rho F L ms m (fun n'' _ F'' L'' _ _ => n'' = n /\ F'' = F' /\ L'' = L).
Proof.
  induction ts as [|t ts IH]; intros n rho F L ms m F' H HD.
  - injection H as <-. apply rret; [exact HD | repeat split].
  - cbn [widen_bounds] in H.
    destruct (iget t Mp) as [rp|]; [|discriminate H].
    destruct (iget t (f_mem F)) as [rc|] eqn:Hg; [|discriminate H].
    match type of H with (if ?c then _ else _) = _ => destruct c eqn:Hc end; [|discriminate H].
    apply andb_true_iff in Hc as [Hc Hchi]. apply andb_true_iff in Hc as [Ht Hclo].
    apply ltb_spec in Ht. apply leb_spec in Hclo, Hchi.
    pose proof (D3_bounds n rho F L ms m t rc HD Hg) as Hb.
    assert (HD1 : D3 n rho (set_bounds F t rc (rg_clo rp) (rg_chi rp)) L ms m).
    { apply (DInv3_rebound cfg segs IM R0 Lim keep mem0 XI xtags fr0 fc0 rom0 hi wb0 na0 lz0 brk0 A0
               n rho F L ms m t rc (rg_clo rp) (rg_chi rp) HD Hg Ht). lia. }
    apply (rbind n rho F L ms m (fun n'' rho'' F'' L'' ms'' m'' => n'' = n /\ rho'' = rho /\ F'' = set_bounds F t rc (rg_clo rp) (rg_chi rp) /\ L'' = L /\ ms'' = ms /\ m'' = m)).
    + apply (reach_to n rho F L ms m n rho (set_bounds F t rc (rg_clo rp) (rg_chi rp)) L); [exact HD1| |repeat split].
      split; [exact (dext_refl R0 rom0 hi n rho m) | exact (mfr_set_bounds IM n rho F L ms t rc _ _ Hg)].
    + intros n1 rho1 F1 L1 ms1 m1 (-> & -> & -> & -> & -> & ->) HD1'. exact (IH _ _ _ _ _ _ _ H HD1').
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma reg_of_int (r : int) : 0 < to_Z r < 32 -> exists rr : reg, ireg rr = r.
Proof.
  intros Hr. exists (Z_to_bv 5 (to_Z r)). unfold ireg. rewrite Z_to_bv_unsigned.
  rewrite bv_wrap_small by (unfold bv_modulus; change (2 ^ Z.of_N 5) with 32; lia). apply of_to_Z.
Qed.

Lemma forget1_reach n rho F L ms m r :
  D3 n rho F L ms m -> 0 < to_Z r < 32 -> tag_ok F n = true ->
  RCH n rho F L ms m (fun n'' _ F'' L'' _ _ => n'' = (n + 1)%uint63 /\ F'' = forget1 F r n /\ L'' = L).
Proof.
  intros HD Hr Htag.
  unfold tag_ok in Htag. apply andb_true_iff in Htag as [Htag Hlt]. apply andb_true_iff in Htag as [Hn0 Hn60].
  apply ltb_spec in Hn0, Hn60. rewrite to_Z_0 in Hn0. change (to_Z 1152921504606846976) with (2 ^ 60) in Hn60.
  pose proof (to_Z_succ61 R0 n Hn60) as Hn1.
  pose proof HD as (HDI & _). pose proof HDI as (HRn & H0 & _).
  set (xv := dv rho (FxState.rget F r)).
  set (rho' := rho_upd rho n xv).
  assert (Hrho : forall t, to_Z t < to_Z n -> rho' t = rho t).
  { intros t Ht. unfold rho'. apply rho_upd_other. apply (lt_neq R0). exact Ht. }
  refine (reach_abs cfg segs IM R0 Lim keep mem0 XI xtags XI_rho fr0 fc0 rom0 hi wb0 na0 lz0 brk0 A0
            n rho F L ms m (n + 1)%uint63 rho' (forget1 F r n) _ HD Hn0 _ Hrho Hlt eq_refl eq_refl eq_refl _ _);
    [lia| |split; [reflexivity | split; reflexivity]].
  intros rho2 Hag2 r0.
  destruct (agree_upd n rho xv rho2 ltac:(lia) Hag2) as [Hag Hn2].
  unfold FxState.rget, forget1. cbn [f_regs].
  destruct (r0 =? 0)%uint63 eqn:E0; [reflexivity|].
  rewrite iget_iset. destruct (r0 =? r)%uint63 eqn:Er; [|reflexivity].
  apply Uint63.eqb_spec in Er. subst r0.
  destruct (reg_of_int r Hr) as [rr Err].
  pose proof (R_regs _ _ _ _ _ (HRn rho2 Hag) rr) as H2.
  pose proof (R_regs _ _ _ _ _ (HRn rho (agree_refl n rho H0)) rr) as H1.
  rewrite Err in H1, H2.
  assert (Erg : FxState.rget F r = match iget r (f_regs F) with Some v => v | None => fv0 end)
    by (unfold FxState.rget; rewrite E0; reflexivity).
  rewrite <- Erg, <- H2, H1, (dv_opaque rho2 n Hn60), Hn2. reflexivity.
Qed.

Lemma forget_regs_reach : forall rs n rho F L ms m F' n',
  forget_regs rs F n = Some (F', n') -> D3 n rho F L ms m ->
  RCH n rho F L ms m (fun n'' _ F'' L'' _ _ => n'' = n' /\ F'' = F' /\ L'' = L).
Proof.
  induction rs as [|r rs IH]; intros n rho F L ms m F' n' H HD.
  - injection H as <- <-. apply rret; [exact HD | repeat split].
  - cbn [forget_regs] in H.
    match type of H with (if ?c then _ else _) = _ => destruct c eqn:Hc end; [|discriminate H].
    apply andb_true_iff in Hc as [Hc Htag]. apply andb_true_iff in Hc as [Hr0 Hr32].
    apply ltb_spec in Hr0, Hr32. rewrite to_Z_0 in Hr0. change (to_Z 32) with 32 in Hr32.
    apply (rbind _ _ _ _ _ _ _ _ (forget1_reach n rho F L ms m r HD (conj Hr0 Hr32) Htag)).
    intros n1 rho1 F1 L1 ms1 m1 (-> & -> & ->) HD1. exact (IH _ _ _ _ _ _ _ _ H HD1).
Qed.

(* [comment removed for export] *)
Lemma raise_reach n rho F L ms m n0 :
  D3 n rho F L ms m -> tag_ok F n = true -> to_Z n <= to_Z n0 ->
  RCH n rho F L ms m (fun n'' _ F'' L'' _ _ => n'' = n0 /\ F'' = F /\ L'' = L).
Proof.
  intros HD Htag Hle.
  unfold tag_ok in Htag. apply andb_true_iff in Htag as [Htag Hlt]. apply andb_true_iff in Htag as [Hn0 _].
  apply ltb_spec in Hn0. rewrite to_Z_0 in Hn0.
  refine (reach_abs cfg segs IM R0 Lim keep mem0 XI xtags XI_rho fr0 fc0 rom0 hi wb0 na0 lz0 brk0 A0
            n rho F L ms m n0 rho F _ HD Hn0 Hle (fun t _ => eq_refl) Hlt eq_refl eq_refl eq_refl (fun _ _ _ => eq_refl) _).
  split; [reflexivity | split; reflexivity].
Qed.
End Join.
Lemma forget_regs_n : forall rs F G n F' G' n' n'',
  forget_regs rs F n = Some (F', n') -> forget_regs rs G n = Some (G', n'') -> n' = n''.
Proof.
  induction rs as [|r rs IH]; intros F G n F' G' n' n'' H1 H2.
  - injection H1 as _ <-. injection H2 as _ <-. reflexivity.
  - cbn [forget_regs] in H1, H2.
    match type of H1 with (if ?c then _ else _) = _ => destruct c end; [|discriminate H1].
    match type of H2 with (if ?c then _ else _) = _ => destruct c end; [|discriminate H2].
    exact (IH _ _ _ _ _ _ _ H1 H2).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section Join2.
Variable x : fstate -> fledger3 -> int -> option dres3.
Hypothesis x_sound : forall n rho F L3 ms m res,
  x F L3 n = Some res -> D3 n rho F L3 ms m -> POK n rho F L3 res ms m.
Variable kw : nat.
Variable rounds : nat.

Lemma join_child_reach Fp Lp plan F1 L1 n1 F2 n2 :
  join_child IM code x kw rounds Fp Lp plan (F1, L1, n1) = Some (F2, n2) ->
  forall rho ms m, D3 n1 rho F1 L1 ms m ->
    RCH n1 rho F1 L1 ms m (fun n'' _ F'' L'' _ _ => n'' = n2 /\ F'' = F2 /\ L'' = Lp /\ tag_ok F2 n2 = true).
Proof.
  intros H rho ms m HD. unfold join_child in H. destruct plan as [[jpc rs] ts]. cbn [fst snd] in H.
  destruct (run_to IM code x kw jpc rounds F1 L1 n1) as [[[Fr Lr] nr]|] eqn:Erun; [|discriminate H].
  destruct (ledger_weaker Lp Lr) eqn:Ew; [|discriminate H].
  destruct (widen_bounds (f_mem Fp) ts Fr nr) as [Fw|] eqn:Ewd; [|discriminate H].
  destruct (tag_ok Fw nr) eqn:Etag; [|discriminate H]. injection H as <- <-.
  apply (rbind _ _ _ _ _ _ _ _ (run_to_reach x x_sound kw jpc rounds n1 rho F1 L1 ms m Fr Lr nr Erun HD)).
  intros n' rho' F' L' ms' m' (-> & -> & ->) HD'.
  apply (rbind nr rho' Fr Lr ms' m' (fun n'' rho'' F'' L'' ms'' m'' => n'' = nr /\ F'' = Fr /\ L'' = Lp)).
  - apply (reach_to nr rho' Fr Lr ms' m' nr rho' Fr Lp);
      [exact (DInv3_weaken _ _ _ _ _ _ _ Ew HD') | exact (PX_weaken _ _ _ _ _ _ _ Ew) | repeat split].
  - intros n3 rho3 F3 L3' ms3 m3 (-> & -> & ->) HD3.
    apply (reach_mono _ _ _ _ _ _ _ _ (widen_reach (f_mem Fp) ts nr rho3 Fr Lp ms3 m3 Fw Ewd HD3)).
    intros n4 rho4 F4 L4 ms4 m4 (-> & -> & ->). repeat split. exact Etag.
Qed.

(* [comment removed for export] *)
Lemma join2_reach Fp Lp plan F2 L2 n2 F3 L3' n3 FJ LJ nJ :
  join2 IM code x kw rounds Fp Lp plan (F2, L2, n2) (F3, L3', n3) = Some (FJ, LJ, nJ) ->
  forall F' L' n', (F', L', n') = (F2, L2, n2) \/ (F', L', n') = (F3, L3', n3) ->
  forall rho ms m, D3 n' rho F' L' ms m ->
    RCH n' rho F' L' ms m (fun n'' _ F'' L'' _ _ => (F'', L'', n'') = (FJ, LJ, nJ)).
Proof.
  intros Ej F' L' n' Hin rho' ms' m' HD'.
  unfold join2 in Ej. destruct plan as [[jpc rs] ts].
  destruct (join_child IM code x kw rounds Fp Lp (jpc, rs, ts) (F2, L2, n2)) as [[FA nA]|] eqn:EA; [|discriminate Ej].
  destruct (join_child IM code x kw rounds Fp Lp (jpc, rs, ts) (F3, L3', n3)) as [[FB nB]|] eqn:EB; [|discriminate Ej].
  cbv zeta in Ej.
  set (n0 := if (nA <? nB)%uint63 then nB else nA) in *.
  assert (Hn0 : to_Z nA <= to_Z n0 /\ to_Z nB <= to_Z n0).
  { unfold n0. destruct (nA <? nB)%uint63 eqn:E.
    - apply ltb_spec in E. lia.
    - assert (~ to_Z nA < to_Z nB) by (intros Hc; apply ltb_spec in Hc; rewrite Hc in E; discriminate E). lia. }
  destruct (forget_regs rs FA n0) as [[FA' nJA]|] eqn:EfA; [|discriminate Ej].
  destruct (forget_regs rs FB n0) as [[FB' nJB]|] eqn:EfB; [|discriminate Ej].
  match type of Ej with (if ?c then _ else _) = _ => destruct c eqn:Eq end; [|discriminate Ej].
  injection Ej as <- <- <-.
  apply andb_true_iff in Eq as [_ Eq]. apply jq_fstate_ok in Eq.
  pose proof (forget_regs_n rs FA FB n0 FA' FB' nJA nJB EfA EfB) as En.
  destruct Hin as [E|E]; injection E as -> -> ->.
  - apply (rbind _ _ _ _ _ _ _ _ (join_child_reach Fp Lp (jpc, rs, ts) F2 L2 n2 FA nA EA rho' ms' m' HD')).
    intros n1 rho1 F1 L1 ms1 m1 (-> & -> & -> & Htag) HD1.
    apply (rbind _ _ _ _ _ _ _ _ (raise_reach nA rho1 FA Lp ms1 m1 n0 HD1 Htag (proj1 Hn0))).
    intros n4 rho4 F4 L4 ms4 m4 (-> & -> & ->) HD4.
    apply (reach_mono _ _ _ _ _ _ _ _ (forget_regs_reach rs n0 rho4 FA Lp ms4 m4 FA' nJA EfA HD4)).
    intros n5 rho5 F5 L5 ms5 m5 (-> & -> & ->). reflexivity.
  - apply (rbind _ _ _ _ _ _ _ _ (join_child_reach Fp Lp (jpc, rs, ts) F3 L3' n3 FB nB EB rho' ms' m' HD')).
    intros n1 rho1 F1 L1 ms1 m1 (-> & -> & -> & Htag) HD1.
    apply (rbind _ _ _ _ _ _ _ _ (raise_reach nB rho1 FB Lp ms1 m1 n0 HD1 Htag (proj2 Hn0))).
    intros n4 rho4 F4 L4 ms4 m4 (-> & -> & ->) HD4.
    apply (reach_mono _ _ _ _ _ _ _ _ (forget_regs_reach rs n0 rho4 FB Lp ms4 m4 FB' nJB EfB HD4)).
    intros n5 rho5 F5 L5 ms5 m5 (-> & -> & ->). rewrite Eq, En. reflexivity.
Qed.

Lemma join_first_some Fp Lp c1 c2 J : forall plans,
  join_first IM code x kw rounds Fp Lp plans c1 c2 = Some J ->
  exists plan, join2 IM code x kw rounds Fp Lp plan c1 c2 = Some J.
Proof.
  induction plans as [|plan rest IH]; intros H; [discriminate H|]. cbn [join_first] in H.
  destruct (join2 IM code x kw rounds Fp Lp plan c1 c2) as [J'|] eqn:E.
  - injection H as <-. exists plan. exact E.
  - exact (IH H).
Qed.

Theorem xpc_join_sound planner n rho F L3 ms m res :
  xpc_join IM code x kw rounds planner F L3 n = Some res -> D3 n rho F L3 ms m -> POK n rho F L3 res ms m.
Proof.
  intros Hx HD. unfold xpc_join in Hx.
  destruct (x F L3 n) as [r0|] eqn:Ex; [|discriminate Hx].
  destruct r0 as [F1 L1 n1 | F2 L2 n2 F3 L3' n3].
  { injection Hx as <-. exact (x_sound _ _ _ _ _ _ _ Ex HD). }
  destruct (join_first IM code x kw rounds F L3 (planner F L3 n (F2, L2, n2) (F3, L3', n3)) (F2, L2, n2) (F3, L3', n3))
    as [[[FJ LJ] nJ]|] eqn:Ej; [|injection Hx as <-; exact (x_sound _ _ _ _ _ _ _ Ex HD)].
  injection Hx as <-. destruct (join_first_some _ _ _ _ _ _ Ej) as [plan Ej2].
  apply (reach_POK cfg segs IM R0 Lim keep mem0 XI xtags fr0 fc0 rom0 hi wb0 na0 lz0 brk0 A0).
  apply (rbind _ _ _ _ _ _ _ _ (POK_reach _ _ _ _ _ _ _ (x_sound _ _ _ _ _ _ _ Ex HD))).
  intros n' rho' F' L' ms' m' Hin HD'. cbn [dres3_in] in Hin.
  apply (reach_mono _ _ _ _ _ _ _ _ (join2_reach F L3 plan F2 L2 n2 F3 L3' n3 FJ LJ nJ Ej2 F' L' n' Hin rho' ms' m' HD')).
  intros n5 rho5 F5 L5 ms5 m5 E. cbn [dres3_in]. exact E.
Qed.
End Join2.
End Drive3J.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma xpc_ask_inv xask F L3 n res :
  cells_inv (f_mem F) -> xpc_ask xask F L3 n = Some res -> dres3_inv res.
Proof.
  intros HM H. unfold xpc_ask in H. destruct (xask F) as [[t thr]|]; [|discriminate H].
  destruct (refine3 (fl3 L3) F n t thr) as [[Fa Fb]|] eqn:Er; [|discriminate H]. injection H as <-.
  destruct (refine3_cells_inv _ _ _ _ _ _ _ HM Er) as [Ha Hb].
  intros F' L' n' Hin. cbn [dres3_in] in Hin. destruct Hin as [E|E]; injection E as -> _ _; assumption.
Qed.

Section JoinInv.
Variable IM : fimage.
Variable code : itrie finstr.
Variable x : fstate -> fledger3 -> int -> option dres3.
Hypothesis x_inv : forall F L3 n res, cells_inv (f_mem F) -> x F L3 n = Some res -> dres3_inv res.
Variable kw : nat.
Variable rounds : nat.

Lemma run_to_inv jpc : forall r F L n F' L' n',
  cells_inv (f_mem F) -> run_to IM code x kw jpc r F L n = Some (F', L', n') -> cells_inv (f_mem F').
Proof.
  induction r as [|r IH]; intros F L n F' L' n' HM H; [discriminate H|]. cbn [run_to] in H.
  destruct (fx_run IM code jpc (Nat.min kw 61) F) as [[F1 st] c] eqn:Erun.
  pose proof (fx_run_cells_inv IM code jpc (Nat.min kw 61) F F1 st c HM Erun) as HM1.
  destruct st as [| | |sc].
  - exact (IH _ _ _ _ _ _ HM1 H).
  - discriminate H.
  - injection H as <- _ _. exact HM1.
  - destruct (x F1 L n) as [[F2 L2 n2|]|] eqn:Ex; try discriminate H.
    exact (IH _ _ _ _ _ _ (x_inv F1 L n _ HM1 Ex F2 L2 n2 eq_refl) H).
Qed.

Lemma widen_bounds_inv Mp : forall ts F n F',
  cells_inv (f_mem F) -> widen_bounds Mp ts F n = Some F' -> cells_inv (f_mem F').
Proof.
  induction ts as [|t ts IH]; intros F n F' HM H.
  - injection H as <-. exact HM.
  - cbn [widen_bounds] in H. destruct (iget t Mp) as [rp|]; [|discriminate H].
    destruct (iget t (f_mem F)) as [rc|] eqn:Hg; [|discriminate H].
    match type of H with (if ?c then _ else _) = _ => destruct c end; [|discriminate H].
    exact (IH _ _ _ (set_bounds_cells_inv F t rc _ _ HM Hg) H).
Qed.

Lemma forget_regs_mem : forall rs F n F' n', forget_regs rs F n = Some (F', n') -> f_mem F' = f_mem F.
Proof.
  induction rs as [|r rs IH]; intros F n F' n' H.
  - injection H as <- _. reflexivity.
  - cbn [forget_regs] in H. match type of H with (if ?c then _ else _) = _ => destruct c end; [|discriminate H].
    rewrite (IH _ _ _ _ H). reflexivity.
Qed.

Lemma join2_inv Fp Lp plan F2 L2 n2 c2 FJ LJ nJ :
  cells_inv (f_mem F2) ->
  join2 IM code x kw rounds Fp Lp plan (F2, L2, n2) c2 = Some (FJ, LJ, nJ) -> cells_inv (f_mem FJ).
Proof.
  intros HM2 Ej. unfold join2 in Ej. destruct plan as [[jpc rs] ts].
  destruct (join_child IM code x kw rounds Fp Lp (jpc, rs, ts) (F2, L2, n2)) as [[FA nA]|] eqn:EA; [|discriminate Ej].
  destruct (join_child IM code x kw rounds Fp Lp (jpc, rs, ts) c2) as [[FB nB]|]; [|discriminate Ej].
  cbv zeta in Ej.
  destruct (forget_regs rs FA (if (nA <? nB)%uint63 then nB else nA)) as [[FA' nJA]|] eqn:EfA; [|discriminate Ej].
  destruct (forget_regs rs FB (if (nA <? nB)%uint63 then nB else nA)) as [[FB' nJB]|]; [|discriminate Ej].
  match type of Ej with (if ?c then _ else _) = _ => destruct c end; [|discriminate Ej].
  injection Ej as <- _ _. rewrite (forget_regs_mem _ _ _ _ _ EfA).
  unfold join_child in EA. cbn [fst snd] in EA.
  destruct (run_to IM code x kw jpc rounds F2 L2 n2) as [[[Fr Lr] nr]|] eqn:Erun; [|discriminate EA].
  destruct (ledger_weaker Lp Lr); [|discriminate EA].
  destruct (widen_bounds (f_mem Fp) ts Fr nr) as [Fw|] eqn:Ewd; [|discriminate EA].
  destruct (tag_ok Fw nr); [|discriminate EA]. injection EA as <- _.
  apply (widen_bounds_inv (f_mem Fp) ts Fr nr Fw); [|exact Ewd].
  exact (run_to_inv jpc rounds F2 L2 n2 Fr Lr nr HM2 Erun).
Qed.

Theorem xpc_join_inv planner F L3 n res :
  cells_inv (f_mem F) -> xpc_join IM code x kw rounds planner F L3 n = Some res -> dres3_inv res.
Proof.
  intros HM H. unfold xpc_join in H.
  destruct (x F L3 n) as [r0|] eqn:Ex; [|discriminate H].
  pose proof (x_inv F L3 n r0 HM Ex) as Hr0.
  destruct r0 as [F1 L1 n1 | F2 L2 n2 F3 L3' n3]; [injection H as <-; exact Hr0|].
  destruct (join_first IM code x kw rounds F L3 (planner F L3 n (F2, L2, n2) (F3, L3', n3)) (F2, L2, n2) (F3, L3', n3))
    as [[[FJ LJ] nJ]|] eqn:Ej; [|injection H as <-; exact Hr0].
  injection H as <-. apply dres3_inv_one.
  destruct (join_first_some IM code x kw rounds _ _ _ _ _ _ Ej) as [plan Ej2].
  exact (join2_inv F L3 plan F2 L2 n2 (F3, L3', n3) FJ LJ nJ (Hr0 F2 L2 n2 (or_introl eq_refl)) Ej2).
Qed.
End JoinInv.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section Planner.
Local Open Scope uint63_scope.
Variable IM : fimage.
Variable code : itrie finstr.
Variable x : fstate -> fledger3 -> int -> option dres3.
(* [comment removed for export] *)
Variable W : nat.

Definition jcfg : Type := (fstate * fledger3 * int)%type.
Definition jp_pc (c : jcfg) : int := f_pc (fst (fst c)).
Definition jp_step (c : jcfg) : option jcfg :=
  let '(F, L, n) := c in
  match fx_step IM code F with
  | FNext F' => Some (F', L, n)
  | FStuck _ => match x F L n with Some (D3One F2 L2 n2) => Some (F2, L2, n2) | _ => None end
  | FEcallAt => None
  end.
Fixpoint jp_trace (w : nat) (c : jcfg) : list jcfg :=
  match w with
  | O => [c]
  | S w' => match jp_step c with Some c' => c :: jp_trace w' c' | None => [c] end
  end.
Definition jp_seen0 (pc : int) (l : list jcfg) : bool := existsb (fun c => jp_pc c =? pc) l.
Fixpoint jp_index (pc : int) (l : list jcfg) (i : nat) : option nat :=
  match l with [] => None | c :: r => if jp_pc c =? pc then Some i else jp_index pc r (S i) end.
(* [comment removed for export] *)
Fixpoint jp_converge (la lb pa : list jcfg) (i : nat) (best : option (nat * nat)) : option (nat * nat) :=
  match la with
  | [] => best
  | a :: ra =>
      let best' :=
        if jp_seen0 (jp_pc a) pa then best else
        match jp_index (jp_pc a) lb 0 with
        | Some j =>
            match i, j with
            | O, O => best
            | _, _ => match best with
                      | Some (bi, bj) => if Nat.ltb (i + j) (bi + bj) then Some (i, j) else best
                      | None => Some (i, j)
                      end
            end
        | None => best
        end in
      jp_converge ra lb (a :: pa) (S i) best'
  end.
Definition jp_regs : list int :=
  [1;2;3;4;5;6;7;8;9;10;11;12;13;14;15;16;17;18;19;20;21;22;23;24;25;26;27;28;29;30;31].
Definition jp_diff (A B : fstate) : list int :=
  filter (fun r => negb (fval_eqb (FxState.rget A r) (FxState.rget B r))) jp_regs.
(* [comment removed for export] *)
Definition jp_csave (r : int) : bool :=
  ((5 <=? r) && (r <=? 7)) || ((10 <=? r) && (r <=? 17)) || ((28 <=? r) && (r <=? 31)).
Definition jp_seen (pc : int) (l : list jcfg) : bool := existsb (fun c => jp_pc c =? pc) l.
(* [comment removed for export] *)
Fixpoint jp_lockstep (fuel : nat) (la lb pa pb : list jcfg) : option int :=
  match fuel, la, lb with
  | S f, a :: ra, b :: rb =>
      if jp_pc a =? jp_pc b then
        if negb (jp_seen (jp_pc a) pa) && negb (jp_seen (jp_pc a) pb) then
          match jp_diff (fst (fst a)) (fst (fst b)) with
          | [] => Some (jp_pc a)
          | _ => jp_lockstep f ra rb (a :: pa) (b :: pb)
          end
        else jp_lockstep f ra rb (a :: pa) (b :: pb)
      else None
  | _, _, _ => None
  end.
(* [comment removed for export] *)
Definition jp_bounds (Mp : itrie region) (M : itrie region) : list int :=
  flat_map (fun kv => match iget (fst kv) Mp with
                      | Some rp => if ((rg_clo rp =? rg_clo (snd kv)) && (rg_chi rp =? rg_chi (snd kv))) then [] else [fst kv]
                      | None => []
                      end) (ielements M).

Definition jplan_default (F : fstate) (L3 : fledger3) (n : int) (c1 c2 : jcfg) : list jplan :=
  let ts := jp_bounds (f_mem F) (f_mem (fst (fst c1))) ++ jp_bounds (f_mem F) (f_mem (fst (fst c2))) in
  let la := jp_trace W c1 in
  let lb := jp_trace W c2 in
  match jp_converge la lb [] 0 None with
  | Some (i, j) =>
      let sa := skipn i la in
      let sb := skipn j lb in
      (match jp_lockstep W sa sb (firstn i la) (firstn j lb) with
       | Some jpc => [(jpc, [], ts)]
       | None => []
       end)
      ++ (match sa, sb with
          | a :: _, b :: _ =>
              let d := jp_diff (fst (fst a)) (fst (fst b)) in
              if forallb jp_csave d then [(jp_pc a, d, ts)] else []
          | _, _ => []
          end)
  | None => []
  end.
End Planner.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition xpc_fork7 (IM : fimage) (code : itrie finstr) (xask : fstate -> option (int * int))
    : fstate -> fledger3 -> int -> option dres3 :=
  xpc_or (xpc_builtin6 IM code) (xpc_ask xask).

Definition xpc_builtin7 (IM : fimage) (code : itrie finstr) (xask : fstate -> option (int * int)) (W kw rounds : nat)
    : fstate -> fledger3 -> int -> option dres3 :=
  xpc_join IM code (xpc_fork7 IM code xask) kw rounds (jplan_default IM code (xpc_fork7 IM code xask) W).

Lemma xpc_fork7_inv IM code xask F L3 n res :
  cells_inv (f_mem F) -> xpc_fork7 IM code xask F L3 n = Some res -> dres3_inv res.
Proof.
  intros HM H. unfold xpc_fork7, xpc_or in H. destruct (xpc_builtin6 IM code F L3 n) as [r|] eqn:E6.
  - injection H as <-. exact (keeps_mem_inv _ (xpc_builtin6_mem IM code) F L3 n r HM E6).
  - exact (xpc_ask_inv xask F L3 n res HM H).
Qed.

Theorem xpc_builtin7_inv IM code xask W kw rounds F L3 n res :
  cells_inv (f_mem F) -> xpc_builtin7 IM code xask W kw rounds F L3 n = Some res -> dres3_inv res.
Proof. exact (xpc_join_inv IM code _ (xpc_fork7_inv IM code xask) kw rounds _ F L3 n res). Qed.

(* [comment removed for export] *)
Theorem drive3_cells_inv7 IM code Rb Rc Lim keep shp xask xask' W kw rounds bp k fuel F L3 n :
  cells_inv (f_mem F) ->
  forall F' L' n' r,
    leaf_in3 (F', L', n', r)
      (drive3 IM code Rb Rc Lim keep shp (fun _ _ _ => None) xask' (xpc_builtin7 IM code xask W kw rounds) bp k fuel F L3 n) ->
    cells_inv (f_mem F').
Proof.
  apply drive3_cells_inv.
  - intros F0 L0 n0 res _ H. discriminate H.
  - exact (xpc_builtin7_inv IM code xask W kw rounds).
Qed.

Section Drive3J7.
Variable cfg : SpuriousCfg.
Variable segs : list Segment.
Variable IM : fimage.
Variable code : itrie finstr.
Hypothesis Hcode : code_ok segs code.
Variable R0 : list (word * word).
Variable Lim : Z.
Variable keep : list int.
Variable mem0 : word -> option byte.
Variable XI : (int -> word) -> Model -> Prop.
Variable xtags : list int.
Hypothesis XI_rho : forall rho rho' m, (forall t, In t xtags -> rho' t = rho t) -> XI rho m -> XI rho' m.
Variable fr0 : bvmap 5 word.
Variable fc0 : bv 32.
Variable rom0 : word -> option byte.
Variable hi : word -> Prop.
Variable wb0 : word.
Variable na0 lz0 : list (word * word).
Variable brk0 : word.
Variable A0 : list (Z * Z).

Local Abbreviation D3 := (DInv3 cfg segs IM R0 Lim keep mem0 XI xtags fr0 fc0 rom0 hi wb0 na0 lz0 brk0 A0).
Local Abbreviation POK := (pc_ok3 cfg segs IM R0 Lim keep mem0 XI xtags fr0 fc0 rom0 hi wb0 na0 lz0 brk0 A0).

Lemma xpc_fork7_sound xask n rho F L3 ms m res :
  xpc_fork7 IM code xask F L3 n = Some res -> D3 n rho F L3 ms m -> POK n rho F L3 res ms m.
Proof.
  apply (xpc_or_sound cfg segs IM R0 Lim keep mem0 XI xtags fr0 fc0 rom0 hi wb0 na0 lz0 brk0 A0).
  - exact (xpc_builtin6_sound cfg segs IM code Hcode R0 Lim keep mem0 XI xtags XI_rho fr0 fc0 rom0 hi wb0 na0 lz0 brk0 A0).
  - exact (xpc_ask_sound cfg segs IM R0 Lim keep mem0 XI xtags fr0 fc0 rom0 hi wb0 na0 lz0 brk0 A0 xask).
Qed.

(* [comment removed for export] *)
Theorem xpc_builtin7_sound xask W kw rounds n rho F L3 ms m res :
  xpc_builtin7 IM code xask W kw rounds F L3 n = Some res -> D3 n rho F L3 ms m -> POK n rho F L3 res ms m.
Proof.
  exact (xpc_join_sound cfg segs IM code Hcode R0 Lim keep mem0 XI xtags XI_rho fr0 fc0 rom0 hi wb0 na0 lz0 brk0 A0
           (xpc_fork7 IM code xask) (xpc_fork7_sound xask) kw rounds
           (jplan_default IM code (xpc_fork7 IM code xask) W) n rho F L3 ms m res).
Qed.
End Drive3J7.
