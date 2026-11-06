(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith.
From Stdlib Require Import FunctionalExtensionality.
From Stdlib Require Import NArith.
From Stdlib Require Import List.
From Stdlib Require Import Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase.
From LinuxProcessSemantics.LinuxProcessSem Require Import RiscvSemantics.
From LinuxProcessSemantics.LinuxProcessSem Require Import MemImageType.
From LinuxProcessSemantics.Riscv Require Import Instr.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import AxSymExec3 AxSymExec3B AsanPlanCore AsanPlan.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import AX2. Import AX2B. Import APC. Import AP. Import Instr.
Open Scope Z_scope.

(* [comment removed for export] *)
Notation "x &&& y" := (if x then y else false) (at level 40, left associativity, only parsing).

Module XRJ.
  (* [comment removed for export] *)
  Definition pow2_of (c : Z) : option Z :=
    if (Z.ltb 0 c && Z.eqb c (2 ^ Z.log2 c) && Z.ltb (Z.log2 c) 64)%bool then Some (Z.log2 c) else None.
  (* [comment removed for export] *)
  Definition negpow2 (c : Z) : option Z := pow2_of (2 ^ 64 - c mod 2 ^ 64).
  Fixpoint esimp (k : list kentry) (e : expr) : expr :=
    match e with
    | EAlu op a b =>
        let a' := esimp k a in let b' := esimp k b in
        match op, b with
        | ALU_AND, ELit c =>
            match negpow2 c with
            | Some s => mkMd M_MUL (ELit (2 ^ s)) (mkAluK k ALU_SRL a' (ELit s))
            | None => mkAluK k op a' b'
            end
        | _, _ => mkAluK k op a' b'
        end
    | EMd op a b => mkMd op (esimp k a) (esimp k b)
    | EExt sx lo n x =>
        (* [comment removed for export] *)
        if Nat.leb n 8 then extK0 k (mkExt sx lo n (esimp k x)) else e
    | _ => e
    end.
  Definition respellw_ok (k : list kentry) (a e : expr) : bool :=
    let a' := esimp k (extK0 k a) in let e' := esimp k e in
    (expr_eqb a' e' || respell_ok k a' e')%bool.

  (* [comment removed for export] *)
  Definition is_kwr (K : kentry) : bool := match K with KWr _ _ => true | _ => false end.
  Definition spell_cut (k : list kentry) (b : expr) (off n : Z) : list kentry :=
    let k1 := match b with ELit z => kimg_cut k (z + off) n | _ => k end in
    List.filter is_kwr k1 ++ List.filter (fun K => negb (is_kwr K)) (kn_cutoutM k1 b off (ELit n)).

  (* [comment removed for export] *)
  Fixpoint esimpB (bc : bctx) (e : expr) : expr :=
    match e with
    | EAlu op a b =>
        let a' := esimpB bc a in let b' := esimpB bc b in
        match op, b with
        | ALU_AND, ELit c =>
            match negpow2 c with
            | Some s => mkMd M_MUL (ELit (2 ^ s)) (mkAluKB bc ALU_SRL a' (ELit s))
            | None => mkAluKB bc op a' b'
            end
        | _, _ => mkAluKB bc op a' b'
        end
    | EMd op a b => mkMd op (esimpB bc a) (esimpB bc b)
    | EExt sx lo n x => if Nat.leb n 8 then extK0B bc (mkExt sx lo n (esimpB bc x)) else e
    | _ => e
    end.
  Lemma esimpB_eq : forall fk e, esimpB (mkbc fk) e = esimp fk e.
  Proof.
    intros fk e. induction e; cbn [esimpB esimp]; try reflexivity.
    - rewrite IHe1, IHe2, mkAluKB_eqf. reflexivity.
    - rewrite IHe1, IHe2. reflexivity.
    - rewrite IHe, extK0B_eqf. reflexivity.
  Qed.
  Definition respellw_okB (bc : bctx) (a e : expr) : bool :=
    let a' := esimpB bc (extK0B bc a) in let e' := esimpB bc e in
    if expr_eqb a' e' then true else respell_okB bc a' e'.
  Lemma respellw_okB_eqf : forall fk, respellw_okB (mkbc fk) = respellw_ok fk.
  Proof.
    intros fk. apply functional_extensionality; intros a. apply functional_extensionality; intros e.
    unfold respellw_okB, respellw_ok. cbv zeta. rewrite extK0B_eqf, !esimpB_eq, respell_okB_eqf. reflexivity.
  Qed.
  (* [comment removed for export] *)
  Definition spell_cutB (bc : bctx) (k : list kentry) (b : expr) (off n : Z) : list kentry :=
    match b with
    | ELit z => spell_cut k b off n
    | _ => List.filter is_kwr k ++ List.filter (fun K => negb (is_kwr K)) (kn_cutoutB bc b off (ELit n))
    end.
  Lemma spell_cutB_eq : forall k b off n, spell_cutB (mkbc k) k b off n = spell_cut k b off n.
  Proof. intros k b off n. unfold spell_cutB, spell_cut, kn_cutoutM. destruct b; reflexivity. Qed.

Section WithA.
  Variable segs : list Segment.
  Variable A : atable.
  Variable nx0 : nat.

  Definition node_spellw (cs : acs) (args : list expr) : option acs :=
    match args with
    | [addr; ELit n; e] =>
        let '(b, off) := split_lit addr in
        if (Z.leb 1 n && Z.leb n 8 && expr_vars_lt (nxt cs) e && flat_x (kn cs) b off (ELit n))%bool
        then match know_lookup segs (kn cs) b off (Z.to_nat n) false [] [] with
             | LHit v [] _ => if respellw_ok (kn cs) v e
                              then Some (set_kn cs (KWord (SA b off) (Z.to_nat n) e :: spell_cut (kn cs) b off n))
                              else None
             | _ => None
             end
        else None
    | _ => None
    end.

  Definition node_respellr (cs : acs) (args : list expr) : option acs :=
    match args with
    | [ELit r; e] =>
        if (Z.ltb 0 r && Z.ltb r 32 && expr_vars_lt (nxt cs) e && respellw_ok (kn cs) (reg cs (Z.to_nat r)) e)%bool
        then Some (set_reg cs (Z.to_nat r) e) else None
    | _ => None
    end.

  Definition node_freshw (cs : acs) (args : list expr) : option acs :=
    match args with
    | [addr; ELit n] =>
        let '(b, off) := split_lit addr in
        if (Z.leb 1 n && Z.leb n 8 && expr_vars_lt (nxt cs) b && kwritable A (kn cs) (kn cs) b off n && fresh_ok nx0 cs)%bool
        then Some (bump (set_kn cs (KWord (SA b off) (Z.to_nat n) (EVar (nxt cs)) :: kn_cutoutM (kn cs) b off (ELit n))) 1)
        else None
    | _ => None
    end.

  Definition node_freshwk (cs : acs) (args : list expr) : option acs :=
    match args with
    | [addr; ELit n] =>
        let '(b, off) := split_lit addr in
        if (Z.leb 1 n && Z.leb n 8 && expr_vars_lt (nxt cs) b && kwritable A (kn cs) (kn cs) b off n && fresh_ok nx0 cs)%bool
        then Some (bump (set_kn cs (KWord (SA b off) (Z.to_nat n) (EVar (nxt cs)) :: spell_cut (kn cs) b off n)) 1)
        else None
    | _ => None
    end.

  (* [comment removed for export] *)
  Definition xn_ref (id : nat) (args : list expr) (cs : acs) : option acs :=
    if Nat.eqb id 203 then node_spellw cs args
    else if Nat.eqb id 204 then node_freshw cs args
    else if Nat.eqb id 205 then node_respellr cs args
    else if Nat.eqb id 215 then node_freshwk cs args
    else None.

  (* [comment removed for export] *)
  Definition node_spellwM (cs : acs) (args : list expr) : option acs :=
    match args with
    | [addr; ELit n; e] =>
        let '(b, off) := split_lit addr in
        let bc := mkbc (kn cs) in
        if (Z.leb 1 n &&& Z.leb n 8 &&& expr_vars_lt (nxt cs) e &&& flat_xB bc b off (ELit n))
        then match know_lookupB segs bc b off (Z.to_nat n) false [] [] with
             | LHit v [] _ => if respellw_okB bc v e
                              then Some (set_kn cs (KWord (SA b off) (Z.to_nat n) e :: spell_cutB bc (kn cs) b off n))
                              else None
             | _ => None
             end
        else None
    | _ => None
    end.
  Definition node_respellrM (cs : acs) (args : list expr) : option acs :=
    match args with
    | [ELit r; e] =>
        if (Z.ltb 0 r &&& Z.ltb r 32 &&& expr_vars_lt (nxt cs) e &&& respellw_okB (mkbc (kn cs)) (reg cs (Z.to_nat r)) e)
        then Some (set_reg cs (Z.to_nat r) e) else None
    | _ => None
    end.
  Definition node_freshwM (cs : acs) (args : list expr) : option acs :=
    match args with
    | [addr; ELit n] =>
        let '(b, off) := split_lit addr in
        let bc := mkbc (kn cs) in
        if (Z.leb 1 n &&& Z.leb n 8 &&& expr_vars_lt (nxt cs) b &&& kwritableB A bc (kn cs) b off n &&& fresh_ok nx0 cs)
        then Some (bump (set_kn cs (KWord (SA b off) (Z.to_nat n) (EVar (nxt cs)) :: kn_cutoutB bc b off (ELit n))) 1)
        else None
    | _ => None
    end.
  Definition node_freshwkM (cs : acs) (args : list expr) : option acs :=
    match args with
    | [addr; ELit n] =>
        let '(b, off) := split_lit addr in
        let bc := mkbc (kn cs) in
        if (Z.leb 1 n &&& Z.leb n 8 &&& expr_vars_lt (nxt cs) b &&& kwritableB A bc (kn cs) b off n &&& fresh_ok nx0 cs)
        then Some (bump (set_kn cs (KWord (SA b off) (Z.to_nat n) (EVar (nxt cs)) :: spell_cutB bc (kn cs) b off n)) 1)
        else None
    | _ => None
    end.
  Lemma node_spellwM_eq : forall cs args, node_spellwM cs args = node_spellw cs args.
  Proof.
    intros cs args. unfold node_spellwM, node_spellw.
    destruct args as [|addr [|[n| | | | | | |] [|e [|]]]]; try reflexivity.
    destruct (split_lit addr) as [b off]. cbv zeta.
    rewrite flat_xB_eqf, know_lookupB_eqf, respellw_okB_eqf, spell_cutB_eq. reflexivity.
  Qed.
  Lemma node_respellrM_eq : forall cs args, node_respellrM cs args = node_respellr cs args.
  Proof.
    intros cs args. unfold node_respellrM, node_respellr.
    destruct args as [|[r| | | | | | |] [|e [|]]]; try reflexivity.
    rewrite respellw_okB_eqf. reflexivity.
  Qed.
  Lemma node_freshwM_eq : forall cs args, node_freshwM cs args = node_freshw cs args.
  Proof.
    intros cs args. unfold node_freshwM, node_freshw.
    destruct args as [|addr [|[n| | | | | | |] [|]]]; try reflexivity.
    destruct (split_lit addr) as [b off]. cbv zeta.
    rewrite kwritableB_eqf. unfold kn_cutoutM. reflexivity.
  Qed.
  Lemma node_freshwkM_eq : forall cs args, node_freshwkM cs args = node_freshwk cs args.
  Proof.
    intros cs args. unfold node_freshwkM, node_freshwk.
    destruct args as [|addr [|[n| | | | | | |] [|]]]; try reflexivity.
    destruct (split_lit addr) as [b off]. cbv zeta.
    rewrite kwritableB_eqf, spell_cutB_eq. reflexivity.
  Qed.
  Definition xn (id : nat) (args : list expr) (cs : acs) : option acs :=
    if Nat.eqb id 203 then node_spellwM cs args
    else if Nat.eqb id 204 then node_freshwM cs args
    else if Nat.eqb id 205 then node_respellrM cs args
    else if Nat.eqb id 215 then node_freshwkM cs args
    else None.
  Lemma xn_eq : forall id args cs, xn id args cs = xn_ref id args cs.
  Proof.
    intros id args cs. unfold xn, xn_ref.
    rewrite node_spellwM_eq, node_freshwM_eq, node_respellrM_eq, node_freshwkM_eq. reflexivity.
  Qed.
End WithA.
End XRJ.
