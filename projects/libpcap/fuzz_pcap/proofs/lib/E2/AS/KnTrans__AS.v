(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Lia.
(* [comment removed for export] *)
From Stdlib Require ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Sem.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require PropExec__Common.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require AxSymExec3 AxSymExec3Sound.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.AS Require MainExport.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require AsanPlanCore.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Module KnTrans.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require PropExec__Common. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require AxSymExec3 AxSymExec3Sound. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.PropExec__Common.PropExec OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AxSymExec3 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AxSymExec3Sound.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.AS Require Import MainExport.
Import ListNotations. Import AX2. Import AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition terms := list (Z * nat).            (* [comment removed for export] *)
Definition lin := (terms * Z)%type.            (* [comment removed for export] *)

Fixpoint tval (V : nat -> Z) (ts : terms) : Z :=
  match ts with [] => 0 | (c, n) :: r => c * V n + tval V r end.
Definition lval (V : nat -> Z) (l : lin) : Z := tval V (fst l) + snd l.

(* [comment removed for export] *)
Fixpoint tins (c : Z) (n : nat) (ts : terms) : terms :=
  match ts with
  | [] => if Z.eqb c 0 then [] else [(c, n)]
  | (c', n') :: r =>
      if Nat.ltb n n' then (if Z.eqb c 0 then ts else (c, n) :: ts)
      else if Nat.eqb n n' then (if Z.eqb (c + c') 0 then r else (c + c', n') :: r)
      else (c', n') :: tins c n r
  end.

Lemma tval_tins : forall V c n ts, tval V (tins c n ts) = c * V n + tval V ts.
Proof.
  intros V c n ts. induction ts as [|[c' n'] r IH]; cbn [tins tval].
  - destruct (Z.eqb_spec c 0); cbn [tval]; subst; lia.
  - destruct (Nat.ltb n n').
    + destruct (Z.eqb_spec c 0); cbn [tval]; subst; lia.
    + destruct (Nat.eqb_spec n n').
      * subst n'. destruct (Z.eqb_spec (c + c') 0); cbn [tval]; nia.
      * cbn [tval]. rewrite IH. lia.
Qed.

Fixpoint tadd (a b : terms) : terms :=
  match a with [] => b | (c, n) :: r => tins c n (tadd r b) end.

Lemma tval_tadd : forall V a b, tval V (tadd a b) = tval V a + tval V b.
Proof. intros V a b. induction a as [|[c n] r IH]; cbn [tadd tval]; [lia|]. rewrite tval_tins, IH. lia. Qed.

Definition tscale (k : Z) (ts : terms) : terms :=
  if Z.eqb k 0 then [] else List.map (fun t => (k * fst t, snd t)) ts.

Lemma tval_tscale : forall V k ts, tval V (tscale k ts) = k * tval V ts.
Proof.
  intros V k ts. unfold tscale. destruct (Z.eqb_spec k 0) as [K0|K0]; [subst; cbn; lia|].
  induction ts as [|[c v] r IH]; cbn [List.map tval fst snd]; [lia|]. rewrite IH. lia.
Qed.

Definition ladd (a b : lin) : lin := (tadd (fst a) (fst b), snd a + snd b).
Definition lscale (k : Z) (a : lin) : lin := (tscale k (fst a), k * snd a).

Lemma lval_ladd : forall V a b, lval V (ladd a b) = lval V a + lval V b.
Proof. intros. unfold lval, ladd. cbn [fst snd]. rewrite tval_tadd. lia. Qed.
Lemma lval_lscale : forall V k a, lval V (lscale k a) = k * lval V a.
Proof. intros. unfold lval, lscale. cbn [fst snd]. rewrite tval_tscale. lia. Qed.

(* [comment removed for export] *)
Definition tdiv8_ok (ts : terms) : bool := forallb (fun t => Z.eqb (fst t mod 8) 0) ts.
Definition tdiv8 (ts : terms) : terms := List.map (fun t => (fst t / 8, snd t)) ts.

Lemma tval_tdiv8 : forall V ts, tdiv8_ok ts = true -> tval V ts = 8 * tval V (tdiv8 ts).
Proof.
  intros V ts. induction ts as [|[c n] r IH]; cbn [tdiv8_ok forallb tdiv8 List.map tval fst snd]; intros H; [lia|].
  apply andb_prop in H as [H1 H2]. apply Z.eqb_eq in H1. rewrite (IH H2).
  pose proof (Z.div_mod c 8 ltac:(lia)) as DM. rewrite H1, Z.add_0_r in DM. rewrite DM at 1. unfold tdiv8. ring.
Qed.

(* [comment removed for export] *)
Fixpoint tbnd (VR : vranges) (ts : terms) : Z * Z :=
  match ts with
  | [] => (0, 0)
  | (c, n) :: r => let '(lo, hi) := vr_lookup VR n in let '(l1, h1) := itv_scale c lo hi in
                   let '(l2, h2) := tbnd VR r in (l1 + l2, h1 + h2)
  end.

Lemma tbnd_sound : forall V VR ts, vr_sound V VR -> fst (tbnd VR ts) <= tval V ts <= snd (tbnd VR ts).
Proof.
  intros V VR ts HV. induction ts as [|[c n] r IH]; cbn [tbnd tval]; [cbn; lia|].
  pose proof (vr_lookup_sound V VR n HV) as B. destruct (vr_lookup VR n) as [lo hi]. cbn [fst snd] in B.
  pose proof (itv_scale_sound c lo hi (V n) B) as S. destruct (itv_scale c lo hi) as [l1 h1]. cbn [fst snd] in S.
  destruct (tbnd VR r) as [l2 h2]. cbn [fst snd] in *. lia.
Qed.

(* [comment removed for export] *)
Definition lin_in (VR : vranges) (l : lin) (lo hi : Z) : bool :=
  let '(a, b) := tbnd VR (fst l) in (lo <=? a + snd l) && (b + snd l <=? hi).

Lemma lin_in_sound : forall V VR l lo hi, vr_sound V VR -> lin_in VR l lo hi = true -> lo <= lval V l <= hi.
Proof.
  intros V VR l lo hi HV H. unfold lin_in in H. pose proof (tbnd_sound V VR (fst l) HV) as B.
  destruct (tbnd VR (fst l)) as [a b]. cbn [fst snd] in B. apply andb_prop in H as [H1 H2].
  apply Z.leb_le in H1. apply Z.leb_le in H2. unfold lval. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition dict := list (nat * lin).
Fixpoint dlookup (D : dict) (i : nat) : option lin :=
  match D with [] => None | (k, l) :: r => if Nat.eqb k i then Some l else dlookup r i end.

Definition T64 : Z := 2 ^ 64.

Definition lit_of (e : expr) : option Z := match e with ELit z => Some z | _ => None end.
Lemma lit_of_eq : forall e z, lit_of e = Some z -> e = ELit z.
Proof. intros e z H. destruct e; try discriminate. injection H as <-. reflexivity. Qed.

Fixpoint lin_of (D : dict) (VR : vranges) (e : expr) : option lin :=
  match e with
  | ELit z => Some ([], z)
  | EVar i => dlookup D i
  | EAlu ALU_ADD a b => match lin_of D VR a, lin_of D VR b with Some x, Some y => Some (ladd x y) | _, _ => None end
  | EAlu ALU_SUB a b => match lin_of D VR a, lin_of D VR b with Some x, Some y => Some (ladd x (lscale (-1) y)) | _, _ => None end
  | EMd M_MUL a b =>
      match lit_of a with
      | Some k => match lin_of D VR b with Some y => Some (lscale k y) | None => None end
      | None => match lit_of b with
                | Some k => match lin_of D VR a with Some x => Some (lscale k x) | None => None end
                | None => None
                end
      end
  | EAlu ALU_SLL a (ELit s) =>
      if (0 <=? s) && (s <? 64) then match lin_of D VR a with Some x => Some (lscale (2 ^ s) x) | None => None end else None
  | EAlu ALU_SRL a (ELit 3) =>
      match lin_of D VR a with
      | Some x => if lin_in VR x 0 (T64 - 1) && tdiv8_ok (fst x) && Z.eqb (snd x mod 8) 0
                  then Some (tdiv8 (fst x), snd x / 8) else None
      | None => None
      end
  | _ => None
  end.

(* [comment removed for export] *)
Definition dict_ok (E : env) (V : nat -> Z) (D : dict) : Prop :=
  Forall (fun p => bv_unsigned (ev E (fst p)) = lval V (snd p) mod T64) D.

Lemma dlookup_ok : forall E V D i l, dict_ok E V D -> dlookup D i = Some l -> bv_unsigned (ev E i) = lval V l mod T64.
Proof.
  intros E V D i l HD. induction HD as [|[k l0] r Hk HD IH]; cbn [dlookup]; [discriminate|].
  destruct (Nat.eqb_spec k i); [|exact IH]. intros X. injection X as <-. subst k. exact Hk.
Qed.

Lemma lin_of_sound : forall E V D VR, dict_ok E V D -> vr_sound V VR ->
  forall e l, lin_of D VR e = Some l -> bv_unsigned (edenot E e) = lval V l mod T64.
Proof.
  intros E V D VR HD HV. unfold T64 in *.
  assert (MADD : forall a b x y, a = x mod 2 ^ 64 -> b = y mod 2 ^ 64 -> (a + b) mod 2 ^ 64 = (x + y) mod 2 ^ 64)
    by (intros a b x y -> ->; rewrite <- Zplus_mod; reflexivity).
  assert (MMUL : forall a b x y, a = x mod 2 ^ 64 -> b = y mod 2 ^ 64 -> (a * b) mod 2 ^ 64 = (x * y) mod 2 ^ 64)
    by (intros a b x y -> ->; rewrite <- Zmult_mod; reflexivity).
  assert (MSUB : forall a b x y, a = x mod 2 ^ 64 -> b = y mod 2 ^ 64 -> (a - b) mod 2 ^ 64 = (x + -1 * y) mod 2 ^ 64)
    by (intros a b x y -> ->; rewrite <- Zminus_mod; f_equal; lia).
  induction e; intros l Hl; cbn [lin_of] in Hl.
  - (* [comment removed for export] *) injection Hl as <-. cbn [edenot]. rewrite u_lit64, two64_eq. unfold lval. cbn [fst snd tval]. rewrite Z.add_0_l. reflexivity.
  - (* [comment removed for export] *) cbn [edenot]. exact (dlookup_ok E V D n l HD Hl).
  - (* [comment removed for export] *)
    destruct op; try discriminate.
    + (* [comment removed for export] *) destruct (lin_of D VR e1) as [x|] eqn:E1; [|discriminate]. destruct (lin_of D VR e2) as [y|] eqn:E2; [|discriminate].
      injection Hl as <-. cbn [edenot]. rewrite u_add64, lval_ladd. apply MADD; [apply IHe1 | apply IHe2]; reflexivity.
    + (* [comment removed for export] *) destruct (lin_of D VR e1) as [x|] eqn:E1; [|discriminate]. destruct (lin_of D VR e2) as [y|] eqn:E2; [|discriminate].
      injection Hl as <-. cbn [edenot]. rewrite u_sub64, lval_ladd, lval_lscale. apply MSUB; [apply IHe1 | apply IHe2]; reflexivity.
    + (* [comment removed for export] *) destruct e2; try discriminate.
      destruct ((0 <=? z) && (z <? 64)) eqn:Hs; [|discriminate]. apply andb_prop in Hs as [S1 S2]. apply Z.leb_le in S1. apply Z.ltb_lt in S2.
      destruct (lin_of D VR e1) as [x|] eqn:E1; [|discriminate]. injection Hl as <-.
      cbn [edenot]. rewrite u_sll64, u_lit64, two64_eq, (Z.mod_small z) by lia. rewrite (Z.mod_small z) by lia.
      rewrite lval_lscale, (IHe1 x eq_refl). rewrite Z.mul_mod_idemp_l by lia. f_equal. lia.
    + (* [comment removed for export] *) destruct e2; try discriminate. destruct z as [|p|p]; try discriminate. destruct p as [p|p|]; try discriminate. destruct p as [p|p|]; try discriminate.
      destruct (lin_of D VR e1) as [x|] eqn:E1; [|discriminate].
      unfold T64 in Hl. destruct (lin_in VR x 0 (2 ^ 64 - 1) && tdiv8_ok (fst x) && Z.eqb (snd x mod 8) 0) eqn:HC; [|discriminate].
      apply andb_prop in HC as [HC C3]. apply andb_prop in HC as [C1 C2]. apply Z.eqb_eq in C3.
      injection Hl as <-. pose proof (lin_in_sound V VR x 0 (2 ^ 64 - 1) HV C1) as R.
      cbn [edenot]. rewrite u_srl64, u_lit64, two64_eq. change (3 mod 2 ^ 64 mod 64) with 3. change (2 ^ 3) with 8.
      rewrite (IHe1 x eq_refl), (Z.mod_small (lval V x)) by lia.
      unfold lval in *. cbn [fst snd]. rewrite (tval_tdiv8 V (fst x) C2) in *.
      pose proof (Z.div_mod (snd x) 8 ltac:(lia)) as DM. rewrite C3 in DM.
      replace (8 * tval V (tdiv8 (fst x)) + snd x) with ((tval V (tdiv8 (fst x)) + snd x / 8) * 8) by lia.
      rewrite Z.div_mul by lia. rewrite Z.mod_small; [reflexivity|]. lia.
  - (* [comment removed for export] *) discriminate.
  - (* [comment removed for export] *)
    destruct op; try discriminate.
    destruct (lit_of e1) as [k|] eqn:L1.
    + apply lit_of_eq in L1. subst e1. destruct (lin_of D VR e2) as [y|] eqn:E2; [|discriminate]. injection Hl as <-.
      cbn [edenot]. rewrite u_mul64, u_lit64, two64_eq, lval_lscale. apply MMUL; [reflexivity | apply IHe2; reflexivity].
    + destruct (lit_of e2) as [k|] eqn:L2; [|discriminate]. apply lit_of_eq in L2. subst e2.
      destruct (lin_of D VR e1) as [x|] eqn:E1; [|discriminate]. injection Hl as <-.
      cbn [edenot]. rewrite u_mul64, u_lit64, two64_eq, lval_lscale, Z.mul_comm. apply MMUL; [reflexivity | apply IHe1; reflexivity].
  - discriminate.
  - discriminate.
  - discriminate.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition term_expr (t : Z * nat) : expr :=
  if Z.eqb (fst t) 1 then EVar (snd t) else EMd M_MUL (ELit (fst t)) (EVar (snd t)).

Fixpoint terms_expr (ts : terms) : expr :=
  match ts with
  | [] => ELit 0
  | t :: r => match r with [] => term_expr t | _ => EAlu ALU_ADD (term_expr t) (terms_expr r) end
  end.

Definition lin_expr (l : lin) : expr :=
  match fst l with
  | [] => ELit (snd l)
  | _ => if Z.eqb (snd l) 0 then terms_expr (fst l) else EAlu ALU_ADD (terms_expr (fst l)) (ELit (snd l))
  end.

Section Target.
Variable E' : env.
#[local] Abbreviation V' := (uev E').

#[using="Type"] Lemma uev_u : forall n, bv_unsigned (ev E' n) = V' n. Proof. reflexivity. Qed.

#[using="Type"] Lemma term_expr_val : forall t, bv_unsigned (edenot E' (term_expr t)) = (fst t * V' (snd t)) mod T64.
Proof.
  intros [c n]. unfold term_expr, T64. cbn [fst snd]. destruct (Z.eqb_spec c 1) as [->|NE]; cbn [edenot].
  - rewrite Z.mul_1_l. pose proof (u64_range (ev E' n)). unfold uev. symmetry. apply Z.mod_small. lia.
  - rewrite u_mul64, u_lit64, two64_eq. unfold uev. rewrite Z.mul_mod_idemp_l by lia. reflexivity.
Qed.

#[using="Type"] Lemma terms_expr_val : forall ts, bv_unsigned (edenot E' (terms_expr ts)) = tval V' ts mod T64.
Proof.
  induction ts as [|t r IH]; [reflexivity|]. cbn [terms_expr]. destruct r as [|t2 r2].
  - rewrite term_expr_val. destruct t as [c n]. cbn [tval fst snd]. f_equal. lia.
  - cbn [edenot]. rewrite u_add64, term_expr_val, IH. destruct t as [c n]. cbn [fst snd]. unfold T64.
    rewrite <- Zplus_mod. reflexivity.
Qed.

#[using="Type"] Lemma lin_expr_val : forall l, bv_unsigned (edenot E' (lin_expr l)) = lval V' l mod T64.
Proof.
  intros [ts k]. unfold lin_expr, lval, T64. cbn [fst snd]. destruct ts as [|t r].
  - cbn [edenot tval]. rewrite u_lit64, two64_eq. reflexivity.
  - destruct (Z.eqb_spec k 0) as [->|NE].
    + rewrite terms_expr_val, Z.add_0_r. reflexivity.
    + cbn [edenot]. rewrite u_add64, terms_expr_val, u_lit64, two64_eq. unfold T64. rewrite <- Zplus_mod. reflexivity.
Qed.

Variable E : env.
Variable D : dict.
Variable VR : vranges.
Hypothesis HD : dict_ok E V' D.
Hypothesis HV : vr_sound V' VR.
Hypothesis HB : eb E' = eb E.

Definition tr_expr (e : expr) : option expr := option_map lin_expr (lin_of D VR e).

#[using="HD HV"] Lemma tr_expr_sound : forall e e', tr_expr e = Some e' -> edenot E' e' = edenot E e.
Proof.
  intros e e' H. unfold tr_expr in H. destruct (lin_of D VR e) as [l|] eqn:HL; [|discriminate]. injection H as <-.
  apply bv_eq. rewrite lin_expr_val, (lin_of_sound E V' D VR HD HV e l HL). reflexivity.
Qed.

(* [comment removed for export] *)
Definition tr_saddr (a : saddr) : option saddr :=
  match lin_of D VR (a_base a) with
  | Some l => if lin_in VR (fst l, 0) 0 (T64 - 1) && lin_in VR l 0 (T64 - 1)
              then Some (SA (terms_expr (fst l)) (a_off a + snd l)) else None
  | None => None
  end.

#[using="HD HV"] Lemma tr_saddr_sound : forall a a', tr_saddr a = Some a' -> estart E' a' = estart E a.
Proof.
  intros a a' H. unfold tr_saddr in H. destruct (lin_of D VR (a_base a)) as [l|] eqn:HL; [|discriminate].
  destruct (lin_in VR (fst l, 0) 0 (T64 - 1) && lin_in VR l 0 (T64 - 1)) eqn:HC; [|discriminate].
  apply andb_prop in HC as [C1 C2]. injection H as <-.
  pose proof (lin_in_sound V' VR _ _ _ HV C1) as R1. pose proof (lin_in_sound V' VR _ _ _ HV C2) as R2.
  unfold lval in R1, R2. cbn [fst snd] in R1, R2. unfold T64 in *.
  unfold estart. cbn [a_base a_off]. rewrite terms_expr_val, (lin_of_sound E V' D VR HD HV _ l HL). unfold lval, T64.
  rewrite !Z.mod_small by lia. lia.
Qed.

#[using="HD HV"] Lemma tr_saddr_adenot : forall a a', tr_saddr a = Some a' -> adenot E' a' = adenot E a.
Proof.
  intros a a' H. pose proof (tr_saddr_sound a a' H) as ES. unfold estart in ES. unfold adenot, v_addi. f_equal. exact ES.
Qed.

#[using="HD HV"] Lemma tr_flat : forall a a' n, tr_saddr a = Some a' -> flat E a n -> flat E' a' n.
Proof. intros a a' n H F. unfold flat in *. rewrite (tr_saddr_sound a a' H). exact F. Qed.

#[using="HD HV"] Lemma tr_elenZ : forall n n', tr_expr n = Some n' -> elenZ E' n' = elenZ E n.
Proof. intros n n' H. unfold elenZ. rewrite (tr_expr_sound n n' H). reflexivity. Qed.

Definition tr_kentry (K : kentry) : option kentry :=
  match K with
  | KWord a w v => match tr_saddr a, tr_expr v with Some a', Some v' => Some (KWord a' w v') | _, _ => None end
  | KZero a n => match tr_saddr a, tr_expr n with Some a', Some n' => Some (KZero a' n') | _, _ => None end
  | KBlob a n k => match tr_saddr a, tr_expr n with Some a', Some n' => Some (KBlob a' n' k) | _, _ => None end
  | KImg lo hi => Some (KImg lo hi)
  | KAlign e m => match tr_expr e with Some e' => Some (KAlign e' m) | None => None end
  | KRange e lo hi => match tr_expr e with Some e' => Some (KRange e' lo hi) | None => None end
  | KWr a n => match tr_saddr a, tr_expr n with Some a', Some n' => Some (KWr a' n') | _, _ => None end
  | KDisj a1 n1 a2 n2 =>
      match tr_saddr a1, tr_expr n1, tr_saddr a2, tr_expr n2 with
      | Some a1', Some n1', Some a2', Some n2' => Some (KDisj a1' n1' a2' n2') | _, _, _, _ => None end
  | KFill a n c => match tr_saddr a, tr_expr n with Some a', Some n' => Some (KFill a' n' c) | _, _ => None end
  | KUnk a n => match tr_saddr a, tr_expr n with Some a', Some n' => Some (KUnk a' n') | _, _ => None end
  end.

#[using="HD HV HB"] Lemma tr_kentry_sound : forall segs M K K', tr_kentry K = Some K' -> kentry_ok segs E M K -> kentry_ok segs E' M K'.
Proof.
  intros segs M K K' H OK. destruct K; cbn [tr_kentry] in H;
    repeat match type of H with
           | match tr_saddr ?a with _ => _ end = _ => let A := fresh "A" in destruct (tr_saddr a) eqn:A; [|discriminate H]
           | match tr_expr ?e with _ => _ end = _ => let X := fresh "X" in destruct (tr_expr e) eqn:X; [|discriminate H]
           end; injection H as <-; cbn [kentry_ok] in OK |- *.
  - (* [comment removed for export] *) destruct OK as (Hw & Hfl & Hrd). split; [exact Hw|]. split; [exact (tr_flat _ _ _ A Hfl)|].
    rewrite (tr_saddr_adenot _ _ A), (tr_expr_sound _ _ X). exact Hrd.
  - (* [comment removed for export] *) destruct OK as (Hfl & Hz). rewrite (tr_elenZ _ _ X). split; [exact (tr_flat _ _ _ A Hfl)|].
    rewrite (tr_saddr_sound _ _ A). exact Hz.
  - (* [comment removed for export] *) destruct OK as (Hfl & Hlen & Hz). rewrite (tr_elenZ _ _ X), HB. split; [exact (tr_flat _ _ _ A Hfl)|].
    split; [exact Hlen|]. rewrite (tr_saddr_sound _ _ A). exact Hz.
  - (* [comment removed for export] *) exact OK.
  - (* [comment removed for export] *) rewrite (tr_expr_sound _ _ X). exact OK.
  - (* [comment removed for export] *) rewrite (tr_expr_sound _ _ X). exact OK.
  - (* [comment removed for export] *) destruct OK as (Hfl & Hz). rewrite (tr_elenZ _ _ X). split; [exact (tr_flat _ _ _ A Hfl)|].
    rewrite (tr_saddr_sound _ _ A). exact Hz.
  - (* [comment removed for export] *) rewrite (tr_elenZ _ _ X), (tr_elenZ _ _ X0), (tr_saddr_sound _ _ A), (tr_saddr_sound _ _ A0). exact OK.
  - (* [comment removed for export] *) destruct OK as (Hfl & Hz). rewrite (tr_elenZ _ _ X). split; [exact (tr_flat _ _ _ A Hfl)|].
    rewrite (tr_saddr_sound _ _ A). exact Hz.
  - (* [comment removed for export] *) destruct OK as (Hfl & Hz). rewrite (tr_elenZ _ _ X). split; [exact (tr_flat _ _ _ A Hfl)|].
    rewrite (tr_saddr_sound _ _ A). exact Hz.
Qed.

Fixpoint tr_kn (kn : list kentry) : list kentry :=
  match kn with
  | [] => []
  | K :: r => match tr_kentry K with Some K' => K' :: tr_kn r | None => tr_kn r end
  end.

(* [comment removed for export] *)
Fixpoint tr_dropped (kn : list kentry) : list kentry :=
  match kn with
  | [] => []
  | K :: r => match tr_kentry K with Some _ => tr_dropped r | None => K :: tr_dropped r end
  end.

#[using="HD HV HB"] Theorem tr_kn_sound : forall segs M kn, know_ok segs E M kn -> know_ok segs E' M (tr_kn kn).
Proof.
  intros segs M kn HK. unfold know_ok in *. induction HK as [|K r HK1 HKr IH]; cbn [tr_kn]; [constructor|].
  destruct (tr_kentry K) as [K'|] eqn:HT; [|exact IH]. constructor; [exact (tr_kentry_sound segs M K K' HT HK1) | exact IH].
Qed.

End Target.

(* [comment removed for export] *)
Definition vr_entries (VR : vranges) : list kentry :=
  List.map (fun t => KRange (EVar (fst (fst t))) (snd (fst t)) (snd t)) VR.

Lemma vr_entries_ok : forall segs E' M VR, vr_sound (uev E') VR -> know_ok segs E' M (vr_entries VR).
Proof.
  intros segs E' M VR [_ HF]. unfold know_ok, vr_entries. apply Forall_forall. intros K HK.
  apply in_map_iff in HK as ([[n lo] hi] & <- & Hin). cbn [fst snd kentry_ok edenot].
  exact (proj1 (Forall_forall _ _) HF _ Hin).
Qed.

(* [comment removed for export] *)

Module TwB.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Sem.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.PropExec__Common.PropExec OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AxSymExec3 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AxSymExec3Sound.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.AS.MainExport.TwB.
Import ListNotations. Import AX2. Import AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition terms := list (Z * nat).            (* [comment removed for export] *)
Definition lin := (terms * Z)%type.            (* [comment removed for export] *)

Fixpoint tval (V : nat -> Z) (ts : terms) : Z :=
  match ts with [] => 0 | (c, n) :: r => c * V n + tval V r end.
Definition lval (V : nat -> Z) (l : lin) : Z := tval V (fst l) + snd l.

(* [comment removed for export] *)
Fixpoint tins (c : Z) (n : nat) (ts : terms) : terms :=
  match ts with
  | [] => if Z.eqb c 0 then [] else [(c, n)]
  | (c', n') :: r =>
      if Nat.ltb n n' then (if Z.eqb c 0 then ts else (c, n) :: ts)
      else if Nat.eqb n n' then (if Z.eqb (c + c') 0 then r else (c + c', n') :: r)
      else (c', n') :: tins c n r
  end.

Lemma tval_tins : forall V c n ts, tval V (tins c n ts) = c * V n + tval V ts.
Proof.
  intros V c n ts. induction ts as [|[c' n'] r IH]; cbn [tins tval].
  - destruct (Z.eqb_spec c 0); cbn [tval]; subst; lia.
  - destruct (Nat.ltb n n').
    + destruct (Z.eqb_spec c 0); cbn [tval]; subst; lia.
    + destruct (Nat.eqb_spec n n').
      * subst n'. destruct (Z.eqb_spec (c + c') 0); cbn [tval]; nia.
      * cbn [tval]. rewrite IH. lia.
Qed.

Fixpoint tadd (a b : terms) : terms :=
  match a with [] => b | (c, n) :: r => tins c n (tadd r b) end.

Lemma tval_tadd : forall V a b, tval V (tadd a b) = tval V a + tval V b.
Proof. intros V a b. induction a as [|[c n] r IH]; cbn [tadd tval]; [lia|]. rewrite tval_tins, IH. lia. Qed.

Definition tscale (k : Z) (ts : terms) : terms :=
  if Z.eqb k 0 then [] else List.map (fun t => (k * fst t, snd t)) ts.

Lemma tval_tscale : forall V k ts, tval V (tscale k ts) = k * tval V ts.
Proof.
  intros V k ts. unfold tscale. destruct (Z.eqb_spec k 0) as [K0|K0]; [subst; cbn; lia|].
  induction ts as [|[c v] r IH]; cbn [List.map tval fst snd]; [lia|]. rewrite IH. lia.
Qed.

Definition ladd (a b : lin) : lin := (tadd (fst a) (fst b), snd a + snd b).
Definition lscale (k : Z) (a : lin) : lin := (tscale k (fst a), k * snd a).

Lemma lval_ladd : forall V a b, lval V (ladd a b) = lval V a + lval V b.
Proof. intros. unfold lval, ladd. cbn [fst snd]. rewrite tval_tadd. lia. Qed.
Lemma lval_lscale : forall V k a, lval V (lscale k a) = k * lval V a.
Proof. intros. unfold lval, lscale. cbn [fst snd]. rewrite tval_tscale. lia. Qed.

(* [comment removed for export] *)
Definition tdiv8_ok (ts : terms) : bool := forallb (fun t => Z.eqb (fst t mod 8) 0) ts.
Definition tdiv8 (ts : terms) : terms := List.map (fun t => (fst t / 8, snd t)) ts.

Lemma tval_tdiv8 : forall V ts, tdiv8_ok ts = true -> tval V ts = 8 * tval V (tdiv8 ts).
Proof.
  intros V ts. induction ts as [|[c n] r IH]; cbn [tdiv8_ok forallb tdiv8 List.map tval fst snd]; intros H; [lia|].
  apply andb_prop in H as [H1 H2]. apply Z.eqb_eq in H1. rewrite (IH H2).
  pose proof (Z.div_mod c 8 ltac:(lia)) as DM. rewrite H1, Z.add_0_r in DM. rewrite DM at 1. unfold tdiv8. ring.
Qed.

(* [comment removed for export] *)
Fixpoint tbnd (VR : vranges) (ts : terms) : Z * Z :=
  match ts with
  | [] => (0, 0)
  | (c, n) :: r => let '(lo, hi) := vr_lookup VR n in let '(l1, h1) := itv_scale c lo hi in
                   let '(l2, h2) := tbnd VR r in (l1 + l2, h1 + h2)
  end.

Lemma tbnd_sound : forall V VR ts, vr_sound V VR -> fst (tbnd VR ts) <= tval V ts <= snd (tbnd VR ts).
Proof.
  intros V VR ts HV. induction ts as [|[c n] r IH]; cbn [tbnd tval]; [cbn; lia|].
  pose proof (vr_lookup_sound V VR n HV) as B. destruct (vr_lookup VR n) as [lo hi]. cbn [fst snd] in B.
  pose proof (itv_scale_sound c lo hi (V n) B) as S. destruct (itv_scale c lo hi) as [l1 h1]. cbn [fst snd] in S.
  destruct (tbnd VR r) as [l2 h2]. cbn [fst snd] in *. lia.
Qed.

(* [comment removed for export] *)
Definition lin_in (VR : vranges) (l : lin) (lo hi : Z) : bool :=
  let '(a, b) := tbnd VR (fst l) in (lo <=? a + snd l) && (b + snd l <=? hi).

Lemma lin_in_sound : forall V VR l lo hi, vr_sound V VR -> lin_in VR l lo hi = true -> lo <= lval V l <= hi.
Proof.
  intros V VR l lo hi HV H. unfold lin_in in H. pose proof (tbnd_sound V VR (fst l) HV) as B.
  destruct (tbnd VR (fst l)) as [a b]. cbn [fst snd] in B. apply andb_prop in H as [H1 H2].
  apply Z.leb_le in H1. apply Z.leb_le in H2. unfold lval. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition dict := list (nat * lin).
Fixpoint dlookup (D : dict) (i : nat) : option lin :=
  match D with [] => None | (k, l) :: r => if Nat.eqb k i then Some l else dlookup r i end.

Definition T64 : Z := 2 ^ 64.

Definition lit_of (e : expr) : option Z := match e with ELit z => Some z | _ => None end.
Lemma lit_of_eq : forall e z, lit_of e = Some z -> e = ELit z.
Proof. intros e z H. destruct e; try discriminate. injection H as <-. reflexivity. Qed.

Fixpoint lin_of (D : dict) (VR : vranges) (e : expr) : option lin :=
  match e with
  | ELit z => Some ([], z)
  | EVar i => dlookup D i
  | EAlu ALU_ADD a b => match lin_of D VR a, lin_of D VR b with Some x, Some y => Some (ladd x y) | _, _ => None end
  | EAlu ALU_SUB a b => match lin_of D VR a, lin_of D VR b with Some x, Some y => Some (ladd x (lscale (-1) y)) | _, _ => None end
  | EMd M_MUL a b =>
      match lit_of a with
      | Some k => match lin_of D VR b with Some y => Some (lscale k y) | None => None end
      | None => match lit_of b with
                | Some k => match lin_of D VR a with Some x => Some (lscale k x) | None => None end
                | None => None
                end
      end
  | EAlu ALU_SLL a (ELit s) =>
      if (0 <=? s) && (s <? 64) then match lin_of D VR a with Some x => Some (lscale (2 ^ s) x) | None => None end else None
  | EAlu ALU_SRL a (ELit 3) =>
      match lin_of D VR a with
      | Some x => if lin_in VR x 0 (T64 - 1) && tdiv8_ok (fst x) && Z.eqb (snd x mod 8) 0
                  then Some (tdiv8 (fst x), snd x / 8) else None
      | None => None
      end
  | _ => None
  end.

(* [comment removed for export] *)
Definition dict_ok (E : env) (V : nat -> Z) (D : dict) : Prop :=
  Forall (fun p => bv_unsigned (ev E (fst p)) = lval V (snd p) mod T64) D.

Lemma dlookup_ok : forall E V D i l, dict_ok E V D -> dlookup D i = Some l -> bv_unsigned (ev E i) = lval V l mod T64.
Proof.
  intros E V D i l HD. induction HD as [|[k l0] r Hk HD IH]; cbn [dlookup]; [discriminate|].
  destruct (Nat.eqb_spec k i); [|exact IH]. intros X. injection X as <-. subst k. exact Hk.
Qed.

Lemma lin_of_sound : forall E V D VR, dict_ok E V D -> vr_sound V VR ->
  forall e l, lin_of D VR e = Some l -> bv_unsigned (edenot E e) = lval V l mod T64.
Proof.
  intros E V D VR HD HV. unfold T64 in *.
  assert (MADD : forall a b x y, a = x mod 2 ^ 64 -> b = y mod 2 ^ 64 -> (a + b) mod 2 ^ 64 = (x + y) mod 2 ^ 64)
    by (intros a b x y -> ->; rewrite <- Zplus_mod; reflexivity).
  assert (MMUL : forall a b x y, a = x mod 2 ^ 64 -> b = y mod 2 ^ 64 -> (a * b) mod 2 ^ 64 = (x * y) mod 2 ^ 64)
    by (intros a b x y -> ->; rewrite <- Zmult_mod; reflexivity).
  assert (MSUB : forall a b x y, a = x mod 2 ^ 64 -> b = y mod 2 ^ 64 -> (a - b) mod 2 ^ 64 = (x + -1 * y) mod 2 ^ 64)
    by (intros a b x y -> ->; rewrite <- Zminus_mod; f_equal; lia).
  induction e; intros l Hl; cbn [lin_of] in Hl.
  - (* [comment removed for export] *) injection Hl as <-. cbn [edenot]. rewrite u_lit64, two64_eq. unfold lval. cbn [fst snd tval]. rewrite Z.add_0_l. reflexivity.
  - (* [comment removed for export] *) cbn [edenot]. exact (dlookup_ok E V D n l HD Hl).
  - (* [comment removed for export] *)
    destruct op; try discriminate.
    + (* [comment removed for export] *) destruct (lin_of D VR e1) as [x|] eqn:E1; [|discriminate]. destruct (lin_of D VR e2) as [y|] eqn:E2; [|discriminate].
      injection Hl as <-. cbn [edenot]. rewrite u_add64, lval_ladd. apply MADD; [apply IHe1 | apply IHe2]; reflexivity.
    + (* [comment removed for export] *) destruct (lin_of D VR e1) as [x|] eqn:E1; [|discriminate]. destruct (lin_of D VR e2) as [y|] eqn:E2; [|discriminate].
      injection Hl as <-. cbn [edenot]. rewrite u_sub64, lval_ladd, lval_lscale. apply MSUB; [apply IHe1 | apply IHe2]; reflexivity.
    + (* [comment removed for export] *) destruct e2; try discriminate.
      destruct ((0 <=? z) && (z <? 64)) eqn:Hs; [|discriminate]. apply andb_prop in Hs as [S1 S2]. apply Z.leb_le in S1. apply Z.ltb_lt in S2.
      destruct (lin_of D VR e1) as [x|] eqn:E1; [|discriminate]. injection Hl as <-.
      cbn [edenot]. rewrite u_sll64, u_lit64, two64_eq, (Z.mod_small z) by lia. rewrite (Z.mod_small z) by lia.
      rewrite lval_lscale, (IHe1 x eq_refl). rewrite Z.mul_mod_idemp_l by lia. f_equal. lia.
    + (* [comment removed for export] *) destruct e2; try discriminate. destruct z as [|p|p]; try discriminate. destruct p as [p|p|]; try discriminate. destruct p as [p|p|]; try discriminate.
      destruct (lin_of D VR e1) as [x|] eqn:E1; [|discriminate].
      unfold T64 in Hl. destruct (lin_in VR x 0 (2 ^ 64 - 1) && tdiv8_ok (fst x) && Z.eqb (snd x mod 8) 0) eqn:HC; [|discriminate].
      apply andb_prop in HC as [HC C3]. apply andb_prop in HC as [C1 C2]. apply Z.eqb_eq in C3.
      injection Hl as <-. pose proof (lin_in_sound V VR x 0 (2 ^ 64 - 1) HV C1) as R.
      cbn [edenot]. rewrite u_srl64, u_lit64, two64_eq. change (3 mod 2 ^ 64 mod 64) with 3. change (2 ^ 3) with 8.
      rewrite (IHe1 x eq_refl), (Z.mod_small (lval V x)) by lia.
      unfold lval in *. cbn [fst snd]. rewrite (tval_tdiv8 V (fst x) C2) in *.
      pose proof (Z.div_mod (snd x) 8 ltac:(lia)) as DM. rewrite C3 in DM.
      replace (8 * tval V (tdiv8 (fst x)) + snd x) with ((tval V (tdiv8 (fst x)) + snd x / 8) * 8) by lia.
      rewrite Z.div_mul by lia. rewrite Z.mod_small; [reflexivity|]. lia.
  - (* [comment removed for export] *) discriminate.
  - (* [comment removed for export] *)
    destruct op; try discriminate.
    destruct (lit_of e1) as [k|] eqn:L1.
    + apply lit_of_eq in L1. subst e1. destruct (lin_of D VR e2) as [y|] eqn:E2; [|discriminate]. injection Hl as <-.
      cbn [edenot]. rewrite u_mul64, u_lit64, two64_eq, lval_lscale. apply MMUL; [reflexivity | apply IHe2; reflexivity].
    + destruct (lit_of e2) as [k|] eqn:L2; [|discriminate]. apply lit_of_eq in L2. subst e2.
      destruct (lin_of D VR e1) as [x|] eqn:E1; [|discriminate]. injection Hl as <-.
      cbn [edenot]. rewrite u_mul64, u_lit64, two64_eq, lval_lscale, Z.mul_comm. apply MMUL; [reflexivity | apply IHe1; reflexivity].
  - discriminate.
  - discriminate.
  - discriminate.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition term_expr (t : Z * nat) : expr :=
  if Z.eqb (fst t) 1 then EVar (snd t) else EMd M_MUL (ELit (fst t)) (EVar (snd t)).

Fixpoint terms_expr (ts : terms) : expr :=
  match ts with
  | [] => ELit 0
  | t :: r => match r with [] => term_expr t | _ => EAlu ALU_ADD (term_expr t) (terms_expr r) end
  end.

Definition lin_expr (l : lin) : expr :=
  match fst l with
  | [] => ELit (snd l)
  | _ => if Z.eqb (snd l) 0 then terms_expr (fst l) else EAlu ALU_ADD (terms_expr (fst l)) (ELit (snd l))
  end.

Section Target.
Variable E' : env.
#[local] Abbreviation V' := (uev E').

#[using="Type"] Lemma uev_u : forall n, bv_unsigned (ev E' n) = V' n. Proof. reflexivity. Qed.

#[using="Type"] Lemma term_expr_val : forall t, bv_unsigned (edenot E' (term_expr t)) = (fst t * V' (snd t)) mod T64.
Proof.
  intros [c n]. unfold term_expr, T64. cbn [fst snd]. destruct (Z.eqb_spec c 1) as [->|NE]; cbn [edenot].
  - rewrite Z.mul_1_l. pose proof (u64_range (ev E' n)). unfold uev. symmetry. apply Z.mod_small. lia.
  - rewrite u_mul64, u_lit64, two64_eq. unfold uev. rewrite Z.mul_mod_idemp_l by lia. reflexivity.
Qed.

#[using="Type"] Lemma terms_expr_val : forall ts, bv_unsigned (edenot E' (terms_expr ts)) = tval V' ts mod T64.
Proof.
  induction ts as [|t r IH]; [reflexivity|]. cbn [terms_expr]. destruct r as [|t2 r2].
  - rewrite term_expr_val. destruct t as [c n]. cbn [tval fst snd]. f_equal. lia.
  - cbn [edenot]. rewrite u_add64, term_expr_val, IH. destruct t as [c n]. cbn [fst snd]. unfold T64.
    rewrite <- Zplus_mod. reflexivity.
Qed.

#[using="Type"] Lemma lin_expr_val : forall l, bv_unsigned (edenot E' (lin_expr l)) = lval V' l mod T64.
Proof.
  intros [ts k]. unfold lin_expr, lval, T64. cbn [fst snd]. destruct ts as [|t r].
  - cbn [edenot tval]. rewrite u_lit64, two64_eq. reflexivity.
  - destruct (Z.eqb_spec k 0) as [->|NE].
    + rewrite terms_expr_val, Z.add_0_r. reflexivity.
    + cbn [edenot]. rewrite u_add64, terms_expr_val, u_lit64, two64_eq. unfold T64. rewrite <- Zplus_mod. reflexivity.
Qed.

Variable E : env.
Variable D : dict.
Variable VR : vranges.
Hypothesis HD : dict_ok E V' D.
Hypothesis HV : vr_sound V' VR.
Hypothesis HB : eb E' = eb E.

Definition tr_expr (e : expr) : option expr := option_map lin_expr (lin_of D VR e).

#[using="HD HV"] Lemma tr_expr_sound : forall e e', tr_expr e = Some e' -> edenot E' e' = edenot E e.
Proof.
  intros e e' H. unfold tr_expr in H. destruct (lin_of D VR e) as [l|] eqn:HL; [|discriminate]. injection H as <-.
  apply bv_eq. rewrite lin_expr_val, (lin_of_sound E V' D VR HD HV e l HL). reflexivity.
Qed.

(* [comment removed for export] *)
Definition tr_saddr (a : saddr) : option saddr :=
  match lin_of D VR (a_base a) with
  | Some l => if lin_in VR (fst l, 0) 0 (T64 - 1) && lin_in VR l 0 (T64 - 1)
              then Some (SA (terms_expr (fst l)) (a_off a + snd l)) else None
  | None => None
  end.

#[using="HD HV"] Lemma tr_saddr_sound : forall a a', tr_saddr a = Some a' -> estart E' a' = estart E a.
Proof.
  intros a a' H. unfold tr_saddr in H. destruct (lin_of D VR (a_base a)) as [l|] eqn:HL; [|discriminate].
  destruct (lin_in VR (fst l, 0) 0 (T64 - 1) && lin_in VR l 0 (T64 - 1)) eqn:HC; [|discriminate].
  apply andb_prop in HC as [C1 C2]. injection H as <-.
  pose proof (lin_in_sound V' VR _ _ _ HV C1) as R1. pose proof (lin_in_sound V' VR _ _ _ HV C2) as R2.
  unfold lval in R1, R2. cbn [fst snd] in R1, R2. unfold T64 in *.
  unfold estart. cbn [a_base a_off]. rewrite terms_expr_val, (lin_of_sound E V' D VR HD HV _ l HL). unfold lval, T64.
  rewrite !Z.mod_small by lia. lia.
Qed.

#[using="HD HV"] Lemma tr_saddr_adenot : forall a a', tr_saddr a = Some a' -> adenot E' a' = adenot E a.
Proof.
  intros a a' H. pose proof (tr_saddr_sound a a' H) as ES. unfold estart in ES. unfold adenot, v_addi. f_equal. exact ES.
Qed.

#[using="HD HV"] Lemma tr_flat : forall a a' n, tr_saddr a = Some a' -> flat E a n -> flat E' a' n.
Proof. intros a a' n H F. unfold flat in *. rewrite (tr_saddr_sound a a' H). exact F. Qed.

#[using="HD HV"] Lemma tr_elenZ : forall n n', tr_expr n = Some n' -> elenZ E' n' = elenZ E n.
Proof. intros n n' H. unfold elenZ. rewrite (tr_expr_sound n n' H). reflexivity. Qed.

Definition tr_kentry (K : kentry) : option kentry :=
  match K with
  | KWord a w v => match tr_saddr a, tr_expr v with Some a', Some v' => Some (KWord a' w v') | _, _ => None end
  | KZero a n => match tr_saddr a, tr_expr n with Some a', Some n' => Some (KZero a' n') | _, _ => None end
  | KBlob a n k => match tr_saddr a, tr_expr n with Some a', Some n' => Some (KBlob a' n' k) | _, _ => None end
  | KImg lo hi => Some (KImg lo hi)
  | KAlign e m => match tr_expr e with Some e' => Some (KAlign e' m) | None => None end
  | KRange e lo hi => match tr_expr e with Some e' => Some (KRange e' lo hi) | None => None end
  | KWr a n => match tr_saddr a, tr_expr n with Some a', Some n' => Some (KWr a' n') | _, _ => None end
  | KDisj a1 n1 a2 n2 =>
      match tr_saddr a1, tr_expr n1, tr_saddr a2, tr_expr n2 with
      | Some a1', Some n1', Some a2', Some n2' => Some (KDisj a1' n1' a2' n2') | _, _, _, _ => None end
  | KFill a n c => match tr_saddr a, tr_expr n with Some a', Some n' => Some (KFill a' n' c) | _, _ => None end
  | KUnk a n => match tr_saddr a, tr_expr n with Some a', Some n' => Some (KUnk a' n') | _, _ => None end
  end.

#[using="HD HV HB"] Lemma tr_kentry_sound : forall segs M K K', tr_kentry K = Some K' -> kentry_ok segs E M K -> kentry_ok segs E' M K'.
Proof.
  intros segs M K K' H OK. destruct K; cbn [tr_kentry] in H;
    repeat match type of H with
           | match tr_saddr ?a with _ => _ end = _ => let A := fresh "A" in destruct (tr_saddr a) eqn:A; [|discriminate H]
           | match tr_expr ?e with _ => _ end = _ => let X := fresh "X" in destruct (tr_expr e) eqn:X; [|discriminate H]
           end; injection H as <-; cbn [kentry_ok] in OK |- *.
  - (* [comment removed for export] *) destruct OK as (Hw & Hfl & Hrd). split; [exact Hw|]. split; [exact (tr_flat _ _ _ A Hfl)|].
    rewrite (tr_saddr_adenot _ _ A), (tr_expr_sound _ _ X). exact Hrd.
  - (* [comment removed for export] *) destruct OK as (Hfl & Hz). rewrite (tr_elenZ _ _ X). split; [exact (tr_flat _ _ _ A Hfl)|].
    rewrite (tr_saddr_sound _ _ A). exact Hz.
  - (* [comment removed for export] *) destruct OK as (Hfl & Hlen & Hz). rewrite (tr_elenZ _ _ X), HB. split; [exact (tr_flat _ _ _ A Hfl)|].
    split; [exact Hlen|]. rewrite (tr_saddr_sound _ _ A). exact Hz.
  - (* [comment removed for export] *) exact OK.
  - (* [comment removed for export] *) rewrite (tr_expr_sound _ _ X). exact OK.
  - (* [comment removed for export] *) rewrite (tr_expr_sound _ _ X). exact OK.
  - (* [comment removed for export] *) destruct OK as (Hfl & Hz). rewrite (tr_elenZ _ _ X). split; [exact (tr_flat _ _ _ A Hfl)|].
    rewrite (tr_saddr_sound _ _ A). exact Hz.
  - (* [comment removed for export] *) rewrite (tr_elenZ _ _ X), (tr_elenZ _ _ X0), (tr_saddr_sound _ _ A), (tr_saddr_sound _ _ A0). exact OK.
  - (* [comment removed for export] *) destruct OK as (Hfl & Hz). rewrite (tr_elenZ _ _ X). split; [exact (tr_flat _ _ _ A Hfl)|].
    rewrite (tr_saddr_sound _ _ A). exact Hz.
  - (* [comment removed for export] *) destruct OK as (Hfl & Hz). rewrite (tr_elenZ _ _ X). split; [exact (tr_flat _ _ _ A Hfl)|].
    rewrite (tr_saddr_sound _ _ A). exact Hz.
Qed.

Fixpoint tr_kn (kn : list kentry) : list kentry :=
  match kn with
  | [] => []
  | K :: r => match tr_kentry K with Some K' => K' :: tr_kn r | None => tr_kn r end
  end.

(* [comment removed for export] *)
Fixpoint tr_dropped (kn : list kentry) : list kentry :=
  match kn with
  | [] => []
  | K :: r => match tr_kentry K with Some _ => tr_dropped r | None => K :: tr_dropped r end
  end.

#[using="HD HV HB"] Theorem tr_kn_sound : forall segs M kn, know_ok segs E M kn -> know_ok segs E' M (tr_kn kn).
Proof.
  intros segs M kn HK. unfold know_ok in *. induction HK as [|K r HK1 HKr IH]; cbn [tr_kn]; [constructor|].
  destruct (tr_kentry K) as [K'|] eqn:HT; [|exact IH]. constructor; [exact (tr_kentry_sound segs M K K' HT HK1) | exact IH].
Qed.

End Target.

(* [comment removed for export] *)
Definition vr_entries (VR : vranges) : list kentry :=
  List.map (fun t => KRange (EVar (fst (fst t))) (snd (fst t)) (snd t)) VR.

Lemma vr_entries_ok : forall segs E' M VR, vr_sound (uev E') VR -> know_ok segs E' M (vr_entries VR).
Proof.
  intros segs E' M VR [_ HF]. unfold know_ok, vr_entries. apply Forall_forall. intros K HK.
  apply in_map_iff in HK as ([[n lo] hi] & <- & Hin). cbn [fst snd kentry_ok edenot].
  exact (proj1 (Forall_forall _ _) HF _ Hin).
Qed.
End TwB.
End KnTrans.

(* [comment removed for export] *)
Module A3Dict.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require PropExec__Common. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require AxSymExec3 AxSymExec3Sound. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.PropExec__Common.PropExec OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AxSymExec3 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AxSymExec3Sound.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.AS Require MainExport. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.AS.MainExport OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.AS.KnTrans__AS.KnTrans.
Import ListNotations. Import AX2. Import AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition PAGES4 : list (nat * nat * Z * Z) :=
  [(26%nat, 78%nat, 1, 34359736304);
   (27%nat, 207%nat, 1, 34359735410);
   (28%nat, 208%nat, 4295491576, 34326181871);
   (36%nat, 226%nat, 1, 34359734272);
   (37%nat, 227%nat, 1, 34359736319);
   (38%nat, 228%nat, 1, 34359736304);
   (46%nat, 245%nat, 1, 34359736319);
   (60%nat, 310%nat, 1, 34359736319);
   (83%nat, 393%nat, 1, 34359733495);
   (101%nat, 5%nat, 1507, 525795);
   (104%nat, 469%nat, 1, 34359736064);
   (105%nat, 470%nat, 1, 34359734272);
   (106%nat, 568%nat, 1, 34359736319);
   (107%nat, 487%nat, 1, 34359736319)].
Definition PAGES : list (nat * nat) := List.map (fun q => (fst (fst (fst q)), snd (fst (fst q)))) PAGES4.
(* [comment removed for export] *)
Definition RENAMES : list (nat * nat) := [(1, 1); (2, 2); (3, 3); (4, 4); (5, 8); (6, 9); (8, 44); (9, 45)]%nat.
(* [comment removed for export] *)
Definition SPECIAL : list nat := [0; 29; 62; 63]%nat.
Definition mapped (i : nat) : bool :=
  existsb (Nat.eqb i) SPECIAL || existsb (fun p => Nat.eqb i (fst p)) PAGES || existsb (fun p => Nat.eqb i (fst p)) RENAMES.
Definition OTHERS : list nat := Eval vm_compute in (List.filter (fun i => negb (mapped i)) (List.seq 0 108)).
Definition KEEP : nat := 1000.

Definition D_SPECIAL : dict :=
  [(0%nat, ([(32768, 0%nat); (16, 6%nat); (4096, 10%nat)], 0));
   (29%nat, ([(4096, 208%nat); (-4096, 209%nat)], 65536));
   (62%nat, ([(32768, 0%nat); (4096, 10%nat); (4096, 344%nat)], 0));
   (63%nat, ([(4096, 0%nat); (512, 10%nat); (512, 344%nat)], -1048576))].
Definition D_PAGES : dict := List.map (fun p => (fst p, ([(4096, snd p)], 0))) PAGES.
Definition D_RENAMES : dict := List.map (fun p => (fst p, ([(1, snd p)], 0))) RENAMES.
Definition D_OTHERS : dict := List.map (fun i => (i, ([(1, (KEEP + i)%nat)], 0))) OTHERS.
Definition D_A3 : dict := D_SPECIAL ++ D_PAGES ++ D_RENAMES ++ D_OTHERS.

Definition VR_SPECIAL : vranges := [(0%nat, 4294901760, 4294967295); (6%nat, 0, 255); (10%nat, 0, 7); (344%nat, 0, 1); (209%nat, 0, 15)].
Definition VR_PAGES : vranges := List.map (fun q => (snd (fst (fst q)), snd (fst q), snd q)) PAGES4.
(* [comment removed for export] *)
Definition VR_REN : list (nat * nat * Z * Z) :=
  [(1%nat, 1%nat, 1, 1024); (2%nat, 2%nat, 0, 256); (3%nat, 3%nat, 0, 131071); (4%nat, 4%nat, 0, 280000); (5%nat, 8%nat, 0, 4294967294); (8%nat, 44%nat, 1, 4194303)].
Definition VR_A3 : vranges := VR_SPECIAL ++ VR_PAGES ++ List.map (fun q => (snd (fst (fst q)), snd (fst q), snd q)) VR_REN.

Section Dict.
Variable E : env.
Let u (i : nat) : Z := bv_unsigned (ev E i).

(* [comment removed for export] *)
Definition page_src (k : nat) : option nat :=
  match List.find (fun p => Nat.eqb (snd p) k) PAGES with Some p => Some (fst p) | None => None end.
Definition ren_src (k : nat) : option nat :=
  match List.find (fun p => Nat.eqb (snd p) k) RENAMES with Some p => Some (fst p) | None => None end.

Definition tgt_val (k : nat) : Z :=
  if Nat.leb KEEP k then u (k - KEEP)%nat
  else if Nat.eqb k 0 then u 0%nat / 32768
  else if Nat.eqb k 6 then u 0%nat mod 4096 / 16
  else if Nat.eqb k 10 then u 0%nat mod 32768 / 4096
  else if Nat.eqb k 209 then u 28%nat mod 65536 / 4096
  else if Nat.eqb k 344 then (u 62%nat - u 0%nat / 4096 * 4096) / 4096
  else match page_src k with
       | Some i => u i / 4096
       | None => match ren_src k with Some i => u i | None => 0 end
       end.

Definition tgt_env : env := Env (fun k => Z_to_bv 64 (tgt_val k)) (eb E).
#[local] Notation V' := (uev tgt_env).

Hypothesis H16 : u 0%nat mod 16 = 0.
Hypothesis HSP : 0x7fff80000000 <= u 0%nat < 2 ^ 47.
Hypothesis HAL : Forall (fun q => u (fst (fst (fst q))) mod 4096 = 0 /\ 4096 * snd (fst q) <= u (fst (fst (fst q))) <= 4096 * snd q) PAGES4.
Hypothesis HREN : Forall (fun q => In (fst (fst (fst q)), snd (fst (fst q))) RENAMES /\ snd (fst q) <= u (fst (fst (fst q))) <= snd q) VR_REN.
Hypothesis HSB : u 29%nat = u 28%nat + 65536 - u 28%nat mod 65536.
Hypothesis HST : u 62%nat = (u 0%nat + 3935) / 4096 * 4096.
Hypothesis HXQ : u 63%nat = (u 62%nat - 8388608) / 8.

#[using="Type"] Lemma V'_small : forall k, 0 <= tgt_val k < 2 ^ 64 -> V' k = tgt_val k.
Proof. intros k H. unfold uev, tgt_env. cbn [ev]. apply u_small. exact H. Qed.

#[using="Type"] Lemma u_rng : forall i, 0 <= u i < 2 ^ 64. Proof. intros i. unfold u. exact (u64_range (ev E i)). Qed.

#[using="Type"] Lemma page_in4 : forall i k, In (i, k) PAGES -> exists lo hi, In (i, k, lo, hi) PAGES4.
Proof. intros i k Hin. unfold PAGES in Hin. apply in_map_iff in Hin as ([[[i0 k0] lo] hi] & X & Hin). cbn [fst snd] in X. injection X as <- <-. exists lo, hi. exact Hin. Qed.
#[using="HAL"] Lemma page_al : forall i k, In (i, k) PAGES -> u i mod 4096 = 0.
Proof. intros i k Hin. destruct (page_in4 i k Hin) as (lo & hi & H4). exact (proj1 (proj1 (Forall_forall _ _) HAL _ H4)). Qed.
#[using="HSP HAL"] Lemma page_rng : forall i k lo hi, In (i, k, lo, hi) PAGES4 -> lo <= u i / 4096 <= hi.
Proof.
  intros i k lo hi H4. destruct (proj1 (Forall_forall _ _) HAL _ H4) as [A B]. cbn [fst snd] in A, B.
  pose proof (Z.div_mod (u i) 4096 ltac:(lia)) as DM. rewrite A in DM. lia.
Qed.

#[using="HSP"] Lemma V'_keep : forall i, V' (KEEP + i)%nat = u i.
Proof.
  intros i. rewrite V'_small; unfold tgt_val; rewrite (proj2 (Nat.leb_le KEEP (KEEP + i)) ltac:(lia));
    replace (KEEP + i - KEEP)%nat with i by lia; [reflexivity | apply u_rng].
Qed.

#[using="HSP"] Lemma V'_0 : V' 0%nat = u 0%nat / 32768.
Proof. pose proof (u_rng 0%nat). rewrite V'_small; [reflexivity|]. change (tgt_val 0) with (u 0%nat / 32768).
  split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]. Qed.
#[using="Type"] Lemma V'_6 : V' 6%nat = u 0%nat mod 4096 / 16.
Proof. pose proof (Z.mod_pos_bound (u 0%nat) 4096 ltac:(lia)). rewrite V'_small; [reflexivity|]. change (tgt_val 6) with (u 0%nat mod 4096 / 16).
  split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]. Qed.
#[using="Type"] Lemma V'_10 : V' 10%nat = u 0%nat mod 32768 / 4096.
Proof. pose proof (Z.mod_pos_bound (u 0%nat) 32768 ltac:(lia)). rewrite V'_small; [reflexivity|]. change (tgt_val 10) with (u 0%nat mod 32768 / 4096).
  split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]. Qed.
#[using="Type"] Lemma V'_209 : V' 209%nat = u 28%nat mod 65536 / 4096.
Proof. pose proof (Z.mod_pos_bound (u 28%nat) 65536 ltac:(lia)). rewrite V'_small; [reflexivity|]. change (tgt_val 209) with (u 28%nat mod 65536 / 4096).
  split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]. Qed.

(* [comment removed for export] *)
#[using="HSP HST"] Lemma st_step : let s := (u 62%nat - u 0%nat / 4096 * 4096) / 4096 in (s = 0 \/ s = 1) /\ u 62%nat = u 0%nat / 4096 * 4096 + 4096 * s.
Proof.
  cbv zeta. rewrite HST. set (q := u 0%nat / 4096).
  pose proof (Z.div_mod (u 0%nat) 4096 ltac:(lia)) as DM. pose proof (Z.mod_pos_bound (u 0%nat) 4096 ltac:(lia)) as MB. fold q in DM.
  destruct (Z_le_gt_dec (u 0%nat mod 4096) 160) as [C|C].
  - assert (X : (u 0%nat + 3935) / 4096 = q) by (symmetry; apply Z.div_unique with (r := u 0%nat mod 4096 + 3935); lia).
    rewrite X. replace (q * 4096 - q * 4096) with 0 by lia. change (0 / 4096) with 0. split; [left; reflexivity | lia].
  - assert (X : (u 0%nat + 3935) / 4096 = q + 1) by (symmetry; apply Z.div_unique with (r := u 0%nat mod 4096 - 161); lia).
    rewrite X. replace ((q + 1) * 4096 - q * 4096) with (1 * 4096) by lia. rewrite Z.div_mul by lia. split; [right; reflexivity | lia].
Qed.
#[using="HSP HST"] Lemma V'_344 : V' 344%nat = (u 62%nat - u 0%nat / 4096 * 4096) / 4096.
Proof. destruct st_step as [S _]. rewrite V'_small; [reflexivity|]. change (tgt_val 344) with ((u 62%nat - u 0%nat / 4096 * 4096) / 4096). lia. Qed.

#[using="Type"] Lemma V'_page : forall i k, In (i, k) PAGES -> V' k = u i / 4096.
Proof.
  intros i k Hin. pose proof (u_rng i) as R.
  assert (TV : tgt_val k = u i / 4096).
  { unfold PAGES in Hin. cbn [In] in Hin. repeat (destruct Hin as [X|Hin]; [injection X as <- <-; reflexivity|]). destruct Hin. }
  rewrite V'_small; [exact TV|]. rewrite TV. split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia].
Qed.
#[using="Type"] Lemma V'_ren : forall i k, In (i, k) RENAMES -> V' k = u i.
Proof.
  intros i k Hin. pose proof (u_rng i) as R.
  assert (TV : tgt_val k = u i).
  { unfold RENAMES in Hin. cbn [In] in Hin. repeat (destruct Hin as [X|Hin]; [injection X as <- <-; reflexivity|]). destruct Hin. }
  rewrite V'_small; [exact TV|]. rewrite TV. exact R.
Qed.

(* [comment removed for export] *)
#[using="H16 HSP"] Lemma sp_digits : u 0%nat = 32768 * (u 0%nat / 32768) + 4096 * (u 0%nat mod 32768 / 4096) + 16 * (u 0%nat mod 4096 / 16)
  /\ u 0%nat / 4096 * 4096 = 32768 * (u 0%nat / 32768) + 4096 * (u 0%nat mod 32768 / 4096).
Proof.
  pose proof (Z.div_mod (u 0%nat) 32768 ltac:(lia)) as D1. pose proof (Z.mod_pos_bound (u 0%nat) 32768 ltac:(lia)) as M1.
  set (r := u 0%nat mod 32768) in *. set (q := u 0%nat / 32768) in *.
  pose proof (Z.div_mod r 4096 ltac:(lia)) as D2. pose proof (Z.mod_pos_bound r 4096 ltac:(lia)) as M2.
  assert (E1 : u 0%nat mod 4096 = r mod 4096).
  { rewrite D1. replace (32768 * q + r) with (r + (8 * q) * 4096) by lia. apply Z_mod_plus_full. }
  assert (E2 : u 0%nat / 4096 = 8 * q + r / 4096).
  { rewrite D1 at 1. replace (32768 * q + r) with (r + (8 * q) * 4096) by lia. rewrite Z_div_plus_full by lia. lia. }
  rewrite E1, E2.
  pose proof (Z.div_mod (r mod 4096) 16 ltac:(lia)) as D3.
  assert (E3 : (r mod 4096) mod 16 = 0).
  { rewrite <- E1. rewrite <- (Znumtheory.Zmod_div_mod 16 4096 (u 0%nat)) by (try lia; exists 256; reflexivity). exact H16. }
  rewrite E3 in D3. split; lia.
Qed.

#[using="H16 HSP HAL HSB HST HXQ"] Theorem dict_A3_ok : dict_ok E V' D_A3.
Proof.
  unfold dict_ok, D_A3, T64. destruct sp_digits as [SD1 SD2]. destruct st_step as [ST1 ST2]. cbv zeta in ST1, ST2.
  pose proof (u_rng 0%nat) as R0.
  apply Forall_app. split; [| apply Forall_app; split; [| apply Forall_app; split]].
  1: unfold D_SPECIAL; apply Forall_cons; [| apply Forall_cons; [| apply Forall_cons; [| apply Forall_cons; [| apply Forall_nil]]]].
  - (* [comment removed for export] *) unfold lval; cbn [fst snd tval]. fold (u 0%nat). rewrite V'_0, V'_6, V'_10. rewrite (Z.mod_small _ (2 ^ 64)); lia.
  - (* [comment removed for export] *) unfold lval; cbn [fst snd tval]. fold (u 29%nat). rewrite (V'_page 28%nat 208%nat), V'_209 by (unfold PAGES; cbn; tauto).
    pose proof (page_al 28%nat 208%nat ltac:(unfold PAGES; cbn; tauto)) as A28.
    pose proof (Z.div_mod (u 28%nat) 4096 ltac:(lia)) as D28. rewrite A28 in D28.
    pose proof (Z.mod_pos_bound (u 28%nat) 65536 ltac:(lia)) as M28.
    assert (A2 : (u 28%nat mod 65536) mod 4096 = 0).
    { rewrite <- (Znumtheory.Zmod_div_mod 4096 65536 (u 28%nat)) by (try lia; exists 16; reflexivity). exact A28. }
    pose proof (Z.div_mod (u 28%nat mod 65536) 4096 ltac:(lia)) as D2. rewrite A2 in D2.
    pose proof (u_rng 29%nat) as R29. rewrite HSB in *. rewrite (Z.mod_small _ (2 ^ 64)); lia.
  - (* [comment removed for export] *) unfold lval; cbn [fst snd tval]. fold (u 62%nat). rewrite V'_0, V'_10, V'_344. pose proof (u_rng 62%nat). rewrite (Z.mod_small _ (2 ^ 64)); lia.
  - (* [comment removed for export] *) unfold lval; cbn [fst snd tval]. fold (u 63%nat). rewrite V'_0, V'_10, V'_344. pose proof (u_rng 63%nat) as R63.
    set (a := u 0%nat / 32768) in *. set (b := u 0%nat mod 32768 / 4096) in *. set (s := (u 62%nat - u 0%nat / 4096 * 4096) / 4096) in *.
    assert (U62 : u 62%nat = 32768 * a + 4096 * b + 4096 * s) by lia.
    assert (X : (u 62%nat - 8388608) / 8 = 4096 * a + 512 * b + 512 * s - 1048576).
    { rewrite U62. replace (32768 * a + 4096 * b + 4096 * s - 8388608) with ((4096 * a + 512 * b + 512 * s - 1048576) * 8) by lia. apply Z.div_mul. lia. }
    rewrite HXQ, X in *. rewrite (Z.mod_small _ (2 ^ 64)); lia.
  - (* [comment removed for export] *) unfold D_PAGES. apply Forall_forall. intros [i l] Hin. apply in_map_iff in Hin as ([i0 k] & X & Hin). injection X as <- <-. unfold lval; cbn [fst snd tval]. fold (u i0).
    rewrite (V'_page i0 k Hin). pose proof (page_al i0 k Hin) as A.
    pose proof (Z.div_mod (u i0) 4096 ltac:(lia)) as DM. rewrite A in DM. pose proof (u_rng i0). rewrite (Z.mod_small _ (2 ^ 64)); lia.
  - (* [comment removed for export] *) unfold D_RENAMES. apply Forall_forall. intros [i l] Hin. apply in_map_iff in Hin as ([i0 k] & X & Hin). injection X as <- <-. unfold lval; cbn [fst snd tval]. fold (u i0).
    rewrite (V'_ren i0 k Hin). pose proof (u_rng i0). rewrite (Z.mod_small _ (2 ^ 64)); lia.
  - (* [comment removed for export] *) unfold D_OTHERS. apply Forall_forall. intros [i l] Hin. apply in_map_iff in Hin as (i0 & X & Hin). injection X as <- <-.
    change (u i0 = (1 * V' (KEEP + i0)%nat + 0 + 0) mod 2 ^ 64).
    rewrite V'_keep. pose proof (u_rng i0). rewrite (Z.mod_small _ (2 ^ 64)); lia.
Qed.

#[using="HSP HAL HREN HST"] Theorem vr_A3_sound : vr_sound V' VR_A3.
Proof.
  split; [intros n; apply uev_range|]. unfold VR_A3. destruct st_step as [ST1 _]. cbv zeta in ST1.
  apply Forall_app. split; [| apply Forall_app; split].
  1: unfold VR_SPECIAL; apply Forall_cons; [| apply Forall_cons; [| apply Forall_cons; [| apply Forall_cons; [| apply Forall_cons; [| apply Forall_nil]]]]].
  - rewrite V'_0. assert (u 0%nat / 32768 < 4294967296) by (apply Z.div_lt_upper_bound; lia). split; [apply Z.div_le_lower_bound; lia | lia].
  - rewrite V'_6. pose proof (Z.mod_pos_bound (u 0%nat) 4096 ltac:(lia)). assert (u 0%nat mod 4096 / 16 < 256) by (apply Z.div_lt_upper_bound; lia). split; [apply Z.div_pos; lia | lia].
  - rewrite V'_10. pose proof (Z.mod_pos_bound (u 0%nat) 32768 ltac:(lia)). assert (u 0%nat mod 32768 / 4096 < 8) by (apply Z.div_lt_upper_bound; lia). split; [apply Z.div_pos; lia | lia].
  - rewrite V'_344. lia.
  - rewrite V'_209. pose proof (Z.mod_pos_bound (u 28%nat) 65536 ltac:(lia)). assert (u 28%nat mod 65536 / 4096 < 16) by (apply Z.div_lt_upper_bound; lia). split; [apply Z.div_pos; lia | lia].
  - unfold VR_PAGES. apply Forall_forall. intros [[k lo] hi] Hin. apply in_map_iff in Hin as ([[[i0 k0] lo0] hi0] & X & Hin). cbn [fst snd] in X. injection X as <- <- <-.
    rewrite (V'_page i0 k0). 2:{ unfold PAGES. apply in_map_iff. exists (i0, k0, lo0, hi0). split; [reflexivity | exact Hin]. }
    exact (page_rng i0 k0 lo0 hi0 Hin).
  - apply Forall_forall. intros [[k lo] hi] Hin. apply in_map_iff in Hin as ([[[i0 k0] lo0] hi0] & X & Hin). cbn [fst snd] in X. injection X as <- <- <-.
    destruct (proj1 (Forall_forall _ _) HREN _ Hin) as [HR B]. cbn [fst snd] in HR, B. rewrite (V'_ren i0 k0 HR). exact B.
Qed.

#[using="Type"] Lemma tgt_blobs : eb tgt_env = eb E. Proof. reflexivity. Qed.

(* [comment removed for export] *)
#[using="H16 HSP HAL HREN HSB HST HXQ"] Theorem tr_A3_sound : forall segs M kn, know_ok segs E M kn -> know_ok segs tgt_env M (tr_kn D_A3 VR_A3 kn).
Proof. intros segs M kn HK. exact (tr_kn_sound tgt_env E D_A3 VR_A3 dict_A3_ok vr_A3_sound tgt_blobs segs M kn HK). Qed.

(* [comment removed for export] *)
#[using="H16 HSP HAL HREN HSB HST HXQ"] Theorem trx_A3_sound : forall segs M kn, know_ok segs E M kn -> know_ok segs tgt_env M (vr_entries VR_A3 ++ tr_kn D_A3 VR_A3 kn).
Proof.
  intros segs M kn HK. unfold know_ok. apply Forall_app. split; [exact (vr_entries_ok segs tgt_env M VR_A3 vr_A3_sound) | exact (tr_A3_sound segs M kn HK)].
Qed.

End Dict.

(* [comment removed for export] *)

Module TwB.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.PropExec__Common.PropExec OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AxSymExec3 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AxSymExec3Sound.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.AS.MainExport.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.AS.KnTrans__AS.KnTrans.TwB.
Import ListNotations. Import AX2. Import AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition PAGES4 : list (nat * nat * Z * Z) :=
  [(26%nat, 78%nat, 1, 34359736304);
   (27%nat, 207%nat, 1, 34359735410);
   (28%nat, 208%nat, 4295491576, 34326181871);
   (36%nat, 226%nat, 1, 34359734272);
   (37%nat, 227%nat, 1, 34359736319);
   (38%nat, 228%nat, 1, 34359736304);
   (46%nat, 245%nat, 1, 34359736319);
   (60%nat, 310%nat, 1, 34359736319);
   (83%nat, 393%nat, 1, 34359733495);
   (101%nat, 5%nat, 1508, 525796);   (* [comment removed for export] *)
   (104%nat, 469%nat, 1, 34359736064);
   (105%nat, 470%nat, 1, 34359734272);
   (106%nat, 568%nat, 1, 34359736319);
   (107%nat, 487%nat, 1, 34359736319)].
Definition PAGES : list (nat * nat) := List.map (fun q => (fst (fst (fst q)), snd (fst (fst q)))) PAGES4.
(* [comment removed for export] *)
Definition RENAMES : list (nat * nat) := [(1, 1); (2, 2); (3, 3); (4, 4); (5, 8); (6, 9); (8, 44); (9, 45)]%nat.
(* [comment removed for export] *)
Definition SPECIAL : list nat := [0; 29; 62; 63]%nat.
Definition mapped (i : nat) : bool :=
  existsb (Nat.eqb i) SPECIAL || existsb (fun p => Nat.eqb i (fst p)) PAGES || existsb (fun p => Nat.eqb i (fst p)) RENAMES.
Definition OTHERS : list nat := Eval vm_compute in (List.filter (fun i => negb (mapped i)) (List.seq 0 108)).
Definition KEEP : nat := 1000.

Definition D_SPECIAL : dict :=
  [(0%nat, ([(32768, 0%nat); (16, 6%nat); (4096, 10%nat)], 0));
   (29%nat, ([(4096, 208%nat); (-4096, 209%nat)], 65536));
   (62%nat, ([(32768, 0%nat); (4096, 10%nat); (4096, 344%nat)], 0));
   (63%nat, ([(4096, 0%nat); (512, 10%nat); (512, 344%nat)], -1048576))].
Definition D_PAGES : dict := List.map (fun p => (fst p, ([(4096, snd p)], 0))) PAGES.
Definition D_RENAMES : dict := List.map (fun p => (fst p, ([(1, snd p)], 0))) RENAMES.
Definition D_OTHERS : dict := List.map (fun i => (i, ([(1, (KEEP + i)%nat)], 0))) OTHERS.
Definition D_A3 : dict := D_SPECIAL ++ D_PAGES ++ D_RENAMES ++ D_OTHERS.

Definition VR_SPECIAL : vranges := [(0%nat, 4294901760, 4294967295); (6%nat, 0, 255); (10%nat, 0, 7); (344%nat, 0, 1); (209%nat, 0, 15)].
Definition VR_PAGES : vranges := List.map (fun q => (snd (fst (fst q)), snd (fst q), snd q)) PAGES4.
(* [comment removed for export] *)
Definition VR_REN : list (nat * nat * Z * Z) :=
  [(1%nat, 1%nat, 1, 1024); (2%nat, 2%nat, 0, 256); (3%nat, 3%nat, 0, 131071); (4%nat, 4%nat, 0, 280000); (5%nat, 8%nat, 0, 4294967294); (8%nat, 44%nat, 1, 4194303)].
Definition VR_A3 : vranges := VR_SPECIAL ++ VR_PAGES ++ List.map (fun q => (snd (fst (fst q)), snd (fst q), snd q)) VR_REN.

Section Dict.
Variable E : env.
Let u (i : nat) : Z := bv_unsigned (ev E i).

(* [comment removed for export] *)
Definition page_src (k : nat) : option nat :=
  match List.find (fun p => Nat.eqb (snd p) k) PAGES with Some p => Some (fst p) | None => None end.
Definition ren_src (k : nat) : option nat :=
  match List.find (fun p => Nat.eqb (snd p) k) RENAMES with Some p => Some (fst p) | None => None end.

Definition tgt_val (k : nat) : Z :=
  if Nat.leb KEEP k then u (k - KEEP)%nat
  else if Nat.eqb k 0 then u 0%nat / 32768
  else if Nat.eqb k 6 then u 0%nat mod 4096 / 16
  else if Nat.eqb k 10 then u 0%nat mod 32768 / 4096
  else if Nat.eqb k 209 then u 28%nat mod 65536 / 4096
  else if Nat.eqb k 344 then (u 62%nat - u 0%nat / 4096 * 4096) / 4096
  else match page_src k with
       | Some i => u i / 4096
       | None => match ren_src k with Some i => u i | None => 0 end
       end.

Definition tgt_env : env := Env (fun k => Z_to_bv 64 (tgt_val k)) (eb E).
#[local] Notation V' := (uev tgt_env).

Hypothesis H16 : u 0%nat mod 16 = 0.
Hypothesis HSP : 0x7fff80000000 <= u 0%nat < 2 ^ 47.
Hypothesis HAL : Forall (fun q => u (fst (fst (fst q))) mod 4096 = 0 /\ 4096 * snd (fst q) <= u (fst (fst (fst q))) <= 4096 * snd q) PAGES4.
Hypothesis HREN : Forall (fun q => In (fst (fst (fst q)), snd (fst (fst q))) RENAMES /\ snd (fst q) <= u (fst (fst (fst q))) <= snd q) VR_REN.
Hypothesis HSB : u 29%nat = u 28%nat + 65536 - u 28%nat mod 65536.
Hypothesis HST : u 62%nat = (u 0%nat + 3935) / 4096 * 4096.
Hypothesis HXQ : u 63%nat = (u 62%nat - 8388608) / 8.

#[using="Type"] Lemma V'_small : forall k, 0 <= tgt_val k < 2 ^ 64 -> V' k = tgt_val k.
Proof. intros k H. unfold uev, tgt_env. cbn [ev]. apply u_small. exact H. Qed.

#[using="Type"] Lemma u_rng : forall i, 0 <= u i < 2 ^ 64. Proof. intros i. unfold u. exact (u64_range (ev E i)). Qed.

#[using="Type"] Lemma page_in4 : forall i k, In (i, k) PAGES -> exists lo hi, In (i, k, lo, hi) PAGES4.
Proof. intros i k Hin. unfold PAGES in Hin. apply in_map_iff in Hin as ([[[i0 k0] lo] hi] & X & Hin). cbn [fst snd] in X. injection X as <- <-. exists lo, hi. exact Hin. Qed.
#[using="HAL"] Lemma page_al : forall i k, In (i, k) PAGES -> u i mod 4096 = 0.
Proof. intros i k Hin. destruct (page_in4 i k Hin) as (lo & hi & H4). exact (proj1 (proj1 (Forall_forall _ _) HAL _ H4)). Qed.
#[using="HSP HAL"] Lemma page_rng : forall i k lo hi, In (i, k, lo, hi) PAGES4 -> lo <= u i / 4096 <= hi.
Proof.
  intros i k lo hi H4. destruct (proj1 (Forall_forall _ _) HAL _ H4) as [A B]. cbn [fst snd] in A, B.
  pose proof (Z.div_mod (u i) 4096 ltac:(lia)) as DM. rewrite A in DM. lia.
Qed.

#[using="HSP"] Lemma V'_keep : forall i, V' (KEEP + i)%nat = u i.
Proof.
  intros i. rewrite V'_small; unfold tgt_val; rewrite (proj2 (Nat.leb_le KEEP (KEEP + i)) ltac:(lia));
    replace (KEEP + i - KEEP)%nat with i by lia; [reflexivity | apply u_rng].
Qed.

#[using="HSP"] Lemma V'_0 : V' 0%nat = u 0%nat / 32768.
Proof. pose proof (u_rng 0%nat). rewrite V'_small; [reflexivity|]. change (tgt_val 0) with (u 0%nat / 32768).
  split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]. Qed.
#[using="Type"] Lemma V'_6 : V' 6%nat = u 0%nat mod 4096 / 16.
Proof. pose proof (Z.mod_pos_bound (u 0%nat) 4096 ltac:(lia)). rewrite V'_small; [reflexivity|]. change (tgt_val 6) with (u 0%nat mod 4096 / 16).
  split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]. Qed.
#[using="Type"] Lemma V'_10 : V' 10%nat = u 0%nat mod 32768 / 4096.
Proof. pose proof (Z.mod_pos_bound (u 0%nat) 32768 ltac:(lia)). rewrite V'_small; [reflexivity|]. change (tgt_val 10) with (u 0%nat mod 32768 / 4096).
  split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]. Qed.
#[using="Type"] Lemma V'_209 : V' 209%nat = u 28%nat mod 65536 / 4096.
Proof. pose proof (Z.mod_pos_bound (u 28%nat) 65536 ltac:(lia)). rewrite V'_small; [reflexivity|]. change (tgt_val 209) with (u 28%nat mod 65536 / 4096).
  split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]. Qed.

(* [comment removed for export] *)
#[using="HSP HST"] Lemma st_step : let s := (u 62%nat - u 0%nat / 4096 * 4096) / 4096 in (s = 0 \/ s = 1) /\ u 62%nat = u 0%nat / 4096 * 4096 + 4096 * s.
Proof.
  cbv zeta. rewrite HST. set (q := u 0%nat / 4096).
  pose proof (Z.div_mod (u 0%nat) 4096 ltac:(lia)) as DM. pose proof (Z.mod_pos_bound (u 0%nat) 4096 ltac:(lia)) as MB. fold q in DM.
  destruct (Z_le_gt_dec (u 0%nat mod 4096) 160) as [C|C].
  - assert (X : (u 0%nat + 3935) / 4096 = q) by (symmetry; apply Z.div_unique with (r := u 0%nat mod 4096 + 3935); lia).
    rewrite X. replace (q * 4096 - q * 4096) with 0 by lia. change (0 / 4096) with 0. split; [left; reflexivity | lia].
  - assert (X : (u 0%nat + 3935) / 4096 = q + 1) by (symmetry; apply Z.div_unique with (r := u 0%nat mod 4096 - 161); lia).
    rewrite X. replace ((q + 1) * 4096 - q * 4096) with (1 * 4096) by lia. rewrite Z.div_mul by lia. split; [right; reflexivity | lia].
Qed.
#[using="HSP HST"] Lemma V'_344 : V' 344%nat = (u 62%nat - u 0%nat / 4096 * 4096) / 4096.
Proof. destruct st_step as [S _]. rewrite V'_small; [reflexivity|]. change (tgt_val 344) with ((u 62%nat - u 0%nat / 4096 * 4096) / 4096). lia. Qed.

#[using="Type"] Lemma V'_page : forall i k, In (i, k) PAGES -> V' k = u i / 4096.
Proof.
  intros i k Hin. pose proof (u_rng i) as R.
  assert (TV : tgt_val k = u i / 4096).
  { unfold PAGES in Hin. cbn [In] in Hin. repeat (destruct Hin as [X|Hin]; [injection X as <- <-; reflexivity|]). destruct Hin. }
  rewrite V'_small; [exact TV|]. rewrite TV. split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia].
Qed.
#[using="Type"] Lemma V'_ren : forall i k, In (i, k) RENAMES -> V' k = u i.
Proof.
  intros i k Hin. pose proof (u_rng i) as R.
  assert (TV : tgt_val k = u i).
  { unfold RENAMES in Hin. cbn [In] in Hin. repeat (destruct Hin as [X|Hin]; [injection X as <- <-; reflexivity|]). destruct Hin. }
  rewrite V'_small; [exact TV|]. rewrite TV. exact R.
Qed.

(* [comment removed for export] *)
#[using="H16 HSP"] Lemma sp_digits : u 0%nat = 32768 * (u 0%nat / 32768) + 4096 * (u 0%nat mod 32768 / 4096) + 16 * (u 0%nat mod 4096 / 16)
  /\ u 0%nat / 4096 * 4096 = 32768 * (u 0%nat / 32768) + 4096 * (u 0%nat mod 32768 / 4096).
Proof.
  pose proof (Z.div_mod (u 0%nat) 32768 ltac:(lia)) as D1. pose proof (Z.mod_pos_bound (u 0%nat) 32768 ltac:(lia)) as M1.
  set (r := u 0%nat mod 32768) in *. set (q := u 0%nat / 32768) in *.
  pose proof (Z.div_mod r 4096 ltac:(lia)) as D2. pose proof (Z.mod_pos_bound r 4096 ltac:(lia)) as M2.
  assert (E1 : u 0%nat mod 4096 = r mod 4096).
  { rewrite D1. replace (32768 * q + r) with (r + (8 * q) * 4096) by lia. apply Z_mod_plus_full. }
  assert (E2 : u 0%nat / 4096 = 8 * q + r / 4096).
  { rewrite D1 at 1. replace (32768 * q + r) with (r + (8 * q) * 4096) by lia. rewrite Z_div_plus_full by lia. lia. }
  rewrite E1, E2.
  pose proof (Z.div_mod (r mod 4096) 16 ltac:(lia)) as D3.
  assert (E3 : (r mod 4096) mod 16 = 0).
  { rewrite <- E1. rewrite <- (Znumtheory.Zmod_div_mod 16 4096 (u 0%nat)) by (try lia; exists 256; reflexivity). exact H16. }
  rewrite E3 in D3. split; lia.
Qed.

#[using="H16 HSP HAL HSB HST HXQ"] Theorem dict_A3_ok : dict_ok E V' D_A3.
Proof.
  unfold dict_ok, D_A3, T64. destruct sp_digits as [SD1 SD2]. destruct st_step as [ST1 ST2]. cbv zeta in ST1, ST2.
  pose proof (u_rng 0%nat) as R0.
  apply Forall_app. split; [| apply Forall_app; split; [| apply Forall_app; split]].
  1: unfold D_SPECIAL; apply Forall_cons; [| apply Forall_cons; [| apply Forall_cons; [| apply Forall_cons; [| apply Forall_nil]]]].
  - (* [comment removed for export] *) unfold lval; cbn [fst snd tval]. fold (u 0%nat). rewrite V'_0, V'_6, V'_10. rewrite (Z.mod_small _ (2 ^ 64)); lia.
  - (* [comment removed for export] *) unfold lval; cbn [fst snd tval]. fold (u 29%nat). rewrite (V'_page 28%nat 208%nat), V'_209 by (unfold PAGES; cbn; tauto).
    pose proof (page_al 28%nat 208%nat ltac:(unfold PAGES; cbn; tauto)) as A28.
    pose proof (Z.div_mod (u 28%nat) 4096 ltac:(lia)) as D28. rewrite A28 in D28.
    pose proof (Z.mod_pos_bound (u 28%nat) 65536 ltac:(lia)) as M28.
    assert (A2 : (u 28%nat mod 65536) mod 4096 = 0).
    { rewrite <- (Znumtheory.Zmod_div_mod 4096 65536 (u 28%nat)) by (try lia; exists 16; reflexivity). exact A28. }
    pose proof (Z.div_mod (u 28%nat mod 65536) 4096 ltac:(lia)) as D2. rewrite A2 in D2.
    pose proof (u_rng 29%nat) as R29. rewrite HSB in *. rewrite (Z.mod_small _ (2 ^ 64)); lia.
  - (* [comment removed for export] *) unfold lval; cbn [fst snd tval]. fold (u 62%nat). rewrite V'_0, V'_10, V'_344. pose proof (u_rng 62%nat). rewrite (Z.mod_small _ (2 ^ 64)); lia.
  - (* [comment removed for export] *) unfold lval; cbn [fst snd tval]. fold (u 63%nat). rewrite V'_0, V'_10, V'_344. pose proof (u_rng 63%nat) as R63.
    set (a := u 0%nat / 32768) in *. set (b := u 0%nat mod 32768 / 4096) in *. set (s := (u 62%nat - u 0%nat / 4096 * 4096) / 4096) in *.
    assert (U62 : u 62%nat = 32768 * a + 4096 * b + 4096 * s) by lia.
    assert (X : (u 62%nat - 8388608) / 8 = 4096 * a + 512 * b + 512 * s - 1048576).
    { rewrite U62. replace (32768 * a + 4096 * b + 4096 * s - 8388608) with ((4096 * a + 512 * b + 512 * s - 1048576) * 8) by lia. apply Z.div_mul. lia. }
    rewrite HXQ, X in *. rewrite (Z.mod_small _ (2 ^ 64)); lia.
  - (* [comment removed for export] *) unfold D_PAGES. apply Forall_forall. intros [i l] Hin. apply in_map_iff in Hin as ([i0 k] & X & Hin). injection X as <- <-. unfold lval; cbn [fst snd tval]. fold (u i0).
    rewrite (V'_page i0 k Hin). pose proof (page_al i0 k Hin) as A.
    pose proof (Z.div_mod (u i0) 4096 ltac:(lia)) as DM. rewrite A in DM. pose proof (u_rng i0). rewrite (Z.mod_small _ (2 ^ 64)); lia.
  - (* [comment removed for export] *) unfold D_RENAMES. apply Forall_forall. intros [i l] Hin. apply in_map_iff in Hin as ([i0 k] & X & Hin). injection X as <- <-. unfold lval; cbn [fst snd tval]. fold (u i0).
    rewrite (V'_ren i0 k Hin). pose proof (u_rng i0). rewrite (Z.mod_small _ (2 ^ 64)); lia.
  - (* [comment removed for export] *) unfold D_OTHERS. apply Forall_forall. intros [i l] Hin. apply in_map_iff in Hin as (i0 & X & Hin). injection X as <- <-.
    change (u i0 = (1 * V' (KEEP + i0)%nat + 0 + 0) mod 2 ^ 64).
    rewrite V'_keep. pose proof (u_rng i0). rewrite (Z.mod_small _ (2 ^ 64)); lia.
Qed.

#[using="HSP HAL HREN HST"] Theorem vr_A3_sound : vr_sound V' VR_A3.
Proof.
  split; [intros n; apply uev_range|]. unfold VR_A3. destruct st_step as [ST1 _]. cbv zeta in ST1.
  apply Forall_app. split; [| apply Forall_app; split].
  1: unfold VR_SPECIAL; apply Forall_cons; [| apply Forall_cons; [| apply Forall_cons; [| apply Forall_cons; [| apply Forall_cons; [| apply Forall_nil]]]]].
  - rewrite V'_0. assert (u 0%nat / 32768 < 4294967296) by (apply Z.div_lt_upper_bound; lia). split; [apply Z.div_le_lower_bound; lia | lia].
  - rewrite V'_6. pose proof (Z.mod_pos_bound (u 0%nat) 4096 ltac:(lia)). assert (u 0%nat mod 4096 / 16 < 256) by (apply Z.div_lt_upper_bound; lia). split; [apply Z.div_pos; lia | lia].
  - rewrite V'_10. pose proof (Z.mod_pos_bound (u 0%nat) 32768 ltac:(lia)). assert (u 0%nat mod 32768 / 4096 < 8) by (apply Z.div_lt_upper_bound; lia). split; [apply Z.div_pos; lia | lia].
  - rewrite V'_344. lia.
  - rewrite V'_209. pose proof (Z.mod_pos_bound (u 28%nat) 65536 ltac:(lia)). assert (u 28%nat mod 65536 / 4096 < 16) by (apply Z.div_lt_upper_bound; lia). split; [apply Z.div_pos; lia | lia].
  - unfold VR_PAGES. apply Forall_forall. intros [[k lo] hi] Hin. apply in_map_iff in Hin as ([[[i0 k0] lo0] hi0] & X & Hin). cbn [fst snd] in X. injection X as <- <- <-.
    rewrite (V'_page i0 k0). 2:{ unfold PAGES. apply in_map_iff. exists (i0, k0, lo0, hi0). split; [reflexivity | exact Hin]. }
    exact (page_rng i0 k0 lo0 hi0 Hin).
  - apply Forall_forall. intros [[k lo] hi] Hin. apply in_map_iff in Hin as ([[[i0 k0] lo0] hi0] & X & Hin). cbn [fst snd] in X. injection X as <- <- <-.
    destruct (proj1 (Forall_forall _ _) HREN _ Hin) as [HR B]. cbn [fst snd] in HR, B. rewrite (V'_ren i0 k0 HR). exact B.
Qed.

#[using="Type"] Lemma tgt_blobs : eb tgt_env = eb E. Proof. reflexivity. Qed.

(* [comment removed for export] *)
#[using="H16 HSP HAL HREN HSB HST HXQ"] Theorem tr_A3_sound : forall segs M kn, know_ok segs E M kn -> know_ok segs tgt_env M (tr_kn D_A3 VR_A3 kn).
Proof. intros segs M kn HK. exact (tr_kn_sound tgt_env E D_A3 VR_A3 dict_A3_ok vr_A3_sound tgt_blobs segs M kn HK). Qed.

(* [comment removed for export] *)
#[using="H16 HSP HAL HREN HSB HST HXQ"] Theorem trx_A3_sound : forall segs M kn, know_ok segs E M kn -> know_ok segs tgt_env M (vr_entries VR_A3 ++ tr_kn D_A3 VR_A3 kn).
Proof.
  intros segs M kn HK. unfold know_ok. apply Forall_app. split; [exact (vr_entries_ok segs tgt_env M VR_A3 vr_A3_sound) | exact (tr_A3_sound segs M kn HK)].
Qed.

End Dict.
End TwB.
End A3Dict.

(* [comment removed for export] *)
Module MainLedgerAsan.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require Import AsanPlanCore.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.AS Require Import MainExport.
Import ListNotations. Import APC.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Definition asan_vis_app : list (zexp * zexp) := [
  (ZMul (ZLit 4096) (ZV 568), ZLit 4096)        (* [comment removed for export] *)
  ; (ZMul (ZLit 4096) (ZV 487), ZLit 4096)      (* [comment removed for export] *)
  ; (ZMul (ZLit 4096) (ZV 470), ZLit 8388608)   (* [comment removed for export] *)
  ; (ZMul (ZLit 4096) (ZV 469), ZLit 1048576)   (* [comment removed for export] *)
  ; (ZMul (ZLit 4096) (ZV 393), ZLit 11571200)  (* [comment removed for export] *)
  ; (ZMul (ZLit 4096) (ZV 310), ZLit 4096)      (* [comment removed for export] *)
  ; (ZMul (ZLit 4096) (ZV 245), ZLit 4096)      (* [comment removed for export] *)
  ; (ZMul (ZLit 4096) (ZV 228), ZLit 65536)     (* [comment removed for export] *)
  ; (ZMul (ZLit 4096) (ZV 227), ZLit 4096)      (* [comment removed for export] *)
  ; (ZAdd (ZAdd (ZMul (ZLit 4096) (ZV 208)) (ZMul (ZLit (-4096)) (ZV 209))) (ZLit 137439019008), ZLit 4096)
                                                (* [comment removed for export] *)
  ; (ZMul (ZLit 4096) (ZV 207), ZLit 3727360)   (* [comment removed for export] *)
  ; (ZMul (ZLit 4096) (ZV 78), ZLit 65536)      (* [comment removed for export] *)
  ; (ZLit 65536, ZLit 6238208)                  (* [comment removed for export] *)
  ; (ZAdd (ZAdd (ZMul (ZLit 32768) (ZV 0)) (ZMul (ZLit 4096) (ZV 10))) (ZLit (-8388608)),
     ZAdd (ZAdd (ZMul (ZLit (-32768)) (ZV 0)) (ZMul (ZLit (-4096)) (ZV 10))) (ZLit 140737496743936))
                                                (* [comment removed for export] *)
  ; (ZV 1103, ZLit 4096)                        (* [comment removed for export] *)
  ; (ZV 1102, ZLit 8192)                        (* [comment removed for export] *)
].
Definition asan_ghost : list (zexp * zexp) := [ (ZLit 140737488355328, ZLit 32768) ].
Definition asan_vis : list (zexp * zexp) := asan_vis_app ++ asan_ghost.

Definition asan_ledger : list lentry := [
  LMap (ZMul (ZLit 4096) (ZV 487)) 4096 KRW
  ; LMap (ZMul (ZLit 4096) (ZV 568)) 4096 KRW
  ; LMap (ZMul (ZLit 4096) (ZV 470)) 8388608 KRWLAZY
  ; LMap (ZMul (ZLit 4096) (ZV 469)) 1048576 KRW
  ; LMap (ZV 1103) 4096 KRW
  ; LMap (ZV 1102) 8192 KRW
  ; LMap (ZMul (ZLit 4096) (ZV 393)) 11571200 KRW
  ; LMap (ZMul (ZLit 4096) (ZV 310)) 4096 KRW
  ; LMap (ZMul (ZLit 4096) (ZV 245)) 4096 KRW
  ; LMap (ZMul (ZLit 4096) (ZV 228)) 65536 KRW
  ; LMap (ZMul (ZLit 4096) (ZV 227)) 4096 KRW
  ; LMap (ZMul (ZLit 4096) (ZV 226)) 8388608 KNONELAZY      (* [comment removed for export] *)
  ; LMap (ZMul (ZLit 4096) (ZV 208)) 137439023104 KNONELAZY (* [comment removed for export] *)
  ; LMap (ZMul (ZLit 4096) (ZV 207)) 3727360 KRW
  ; LMap (ZMul (ZLit 4096) (ZV 78)) 65536 KRW
  ; LMap (ZLit 2201439137792) 15392894357504 KRWLAZY        (* [comment removed for export] *)
  ; LMap (ZLit 2415882240) 2199023255552 KNONELAZY          (* [comment removed for export] *)
  ; LMap (ZLit 2147446784) 268435456 KRWLAZY                (* [comment removed for export] *)
].

(* [comment removed for export] *)
Definition asan_totsz : Z := 17729664598016.  (* [comment removed for export] *)
Definition asan_eager : Z := 16519168.        (* [comment removed for export] *)
Definition asan_abytes : Z := 4294967296.     (* [comment removed for export] *)

(* [comment removed for export] *)

Module TwB.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AsanPlanCore.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.AS.MainExport.TwB.
Import ListNotations. Import APC.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Definition asan_vis_app : list (zexp * zexp) := [
  (ZMul (ZLit 4096) (ZV 568), ZLit 4096)        (* [comment removed for export] *)
  ; (ZMul (ZLit 4096) (ZV 487), ZLit 4096)      (* [comment removed for export] *)
  ; (ZMul (ZLit 4096) (ZV 470), ZLit 8388608)   (* [comment removed for export] *)
  ; (ZMul (ZLit 4096) (ZV 469), ZLit 1048576)   (* [comment removed for export] *)
  ; (ZMul (ZLit 4096) (ZV 393), ZLit 11571200)  (* [comment removed for export] *)
  ; (ZMul (ZLit 4096) (ZV 310), ZLit 4096)      (* [comment removed for export] *)
  ; (ZMul (ZLit 4096) (ZV 245), ZLit 4096)      (* [comment removed for export] *)
  ; (ZMul (ZLit 4096) (ZV 228), ZLit 65536)     (* [comment removed for export] *)
  ; (ZMul (ZLit 4096) (ZV 227), ZLit 4096)      (* [comment removed for export] *)
  ; (ZAdd (ZAdd (ZMul (ZLit 4096) (ZV 208)) (ZMul (ZLit (-4096)) (ZV 209))) (ZLit 137439019008), ZLit 4096)
                                                (* [comment removed for export] *)
  ; (ZMul (ZLit 4096) (ZV 207), ZLit 3727360)   (* [comment removed for export] *)
  ; (ZMul (ZLit 4096) (ZV 78), ZLit 65536)      (* [comment removed for export] *)
  ; (ZLit 65536, ZLit 6242304)                  (* [comment removed for export] *)
  ; (ZAdd (ZAdd (ZMul (ZLit 32768) (ZV 0)) (ZMul (ZLit 4096) (ZV 10))) (ZLit (-8388608)),
     ZAdd (ZAdd (ZMul (ZLit (-32768)) (ZV 0)) (ZMul (ZLit (-4096)) (ZV 10))) (ZLit 140737496743936))
                                                (* [comment removed for export] *)
  ; (ZV 1103, ZLit 4096)                        (* [comment removed for export] *)
  ; (ZV 1102, ZLit 8192)                        (* [comment removed for export] *)
].
Definition asan_ghost : list (zexp * zexp) := [ (ZLit 140737488355328, ZLit 32768) ].
Definition asan_vis : list (zexp * zexp) := asan_vis_app ++ asan_ghost.

Definition asan_ledger : list lentry := [
  LMap (ZMul (ZLit 4096) (ZV 487)) 4096 KRW
  ; LMap (ZMul (ZLit 4096) (ZV 568)) 4096 KRW
  ; LMap (ZMul (ZLit 4096) (ZV 470)) 8388608 KRWLAZY
  ; LMap (ZMul (ZLit 4096) (ZV 469)) 1048576 KRW
  ; LMap (ZV 1103) 4096 KRW
  ; LMap (ZV 1102) 8192 KRW
  ; LMap (ZMul (ZLit 4096) (ZV 393)) 11571200 KRW
  ; LMap (ZMul (ZLit 4096) (ZV 310)) 4096 KRW
  ; LMap (ZMul (ZLit 4096) (ZV 245)) 4096 KRW
  ; LMap (ZMul (ZLit 4096) (ZV 228)) 65536 KRW
  ; LMap (ZMul (ZLit 4096) (ZV 227)) 4096 KRW
  ; LMap (ZMul (ZLit 4096) (ZV 226)) 8388608 KNONELAZY      (* [comment removed for export] *)
  ; LMap (ZMul (ZLit 4096) (ZV 208)) 137439023104 KNONELAZY (* [comment removed for export] *)
  ; LMap (ZMul (ZLit 4096) (ZV 207)) 3727360 KRW
  ; LMap (ZMul (ZLit 4096) (ZV 78)) 65536 KRW
  ; LMap (ZLit 2201439137792) 15392894357504 KRWLAZY        (* [comment removed for export] *)
  ; LMap (ZLit 2415882240) 2199023255552 KNONELAZY          (* [comment removed for export] *)
  ; LMap (ZLit 2147446784) 268435456 KRWLAZY                (* [comment removed for export] *)
].

(* [comment removed for export] *)
Definition asan_totsz : Z := 17729664602112.  (* [comment removed for export] *)
Definition asan_eager : Z := 16519168.        (* [comment removed for export] *)
Definition asan_abytes : Z := 4294967296.     (* [comment removed for export] *)
End TwB.
End MainLedgerAsan.
