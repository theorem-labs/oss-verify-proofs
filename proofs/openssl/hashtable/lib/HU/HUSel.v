(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Instr.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import PropExec ShapeAlg AgentLib AxSymExec3 AxSymExec3Sound AxSymRun3 AsanPlanCore.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import CxRel CxPlan CxPlanSound CxGlue.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import CxBatch HUPlanImage HUAtable H0Sinv HUCheckG HUChain HUChain2 HUHop HUBatch HUFam HUDrv.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import AX2. Import AX2S. Import APC. Import CAP. Import CXS.
Open Scope Z_scope.

(* [comment removed for export] *)
Record tin : Type := TIN { t_n : Z; t_cl : Z; t_b2 : Z; t_cnt : bool }.
Definition t_calls (t : tin) : Z := if t_cl t =? 0 then 1 else 1 + t_b2 t mod 4.
Definition Llo (K : Z) : Z := if K =? 0 then 0 else 65536 * 2 ^ (K - 1).
Definition Lhi (K : Z) : Z := 65536 * 2 ^ K - 1.
Definition tin_ok (K : Z) (t : tin) : Prop :=
  0 <= t_n t /\ 0 <= t_cl t <= 32767 /\ 0 <= t_b2 t <= 255 /\ Llo K <= 6 + t_cl t + t_n t <= Lhi K.

(* [comment removed for export] *)
Record cell : Type := CELL { c_nlo : Z; c_nhi : Z; c_cllo : Z; c_clhi : Z; c_qlo : Z; c_qhi : Z; c_rlo : Z; c_rhi : Z }.
Definition in_cell (c : cell) (t : tin) : Prop :=
  c_nlo c <= t_n t <= c_nhi c /\ c_cllo c <= t_cl t <= c_clhi c
  /\ c_qlo c <= t_n t / 4096 <= c_qhi c /\ c_rlo c <= t_n t mod 4096 <= c_rhi c.

Section Sel.
  Variables (vk vs5 vq vr : nat).      (* [comment removed for export] *)
  Variable K : Z.                      (* [comment removed for export] *)
  Variable HASHF : kentry.             (* [comment removed for export] *)
  Hypothesis HK : 0 <= K <= 10.

  Definition eok (t : tin) (E : env) : Prop :=
    uE E (EVar 4) = t_n t /\ uE E (EVar 8) = t_cl t /\ uE E (EVar 9) = t_b2 t /\ uE E (EVar 1) = 1
    /\ uE E (EVar vk) = t_calls t /\ (uE E (EVar vs5) <= 9223372036854775807 <-> t_cnt t = false)
    /\ uE E (EVar vq) = t_n t / 4096 /\ uE E (EVar vr) = t_n t mod 4096
    /\ pure_holds E HASHF.

  Definition e_ncl : expr := eadd (EVar 4) (EVar 8).
  Definition e_nq : expr := eadd (escale 4096 (EVar vq)) (EVar vr).
  Definition e_nqcl : expr := eadd e_nq (EVar 8).
  Definition e_n1 : expr := eadd (EVar 4) (EVar 1).
  Definition e_r1 : expr := eadd (EVar vr) (EVar 1).
  Definition e_callsrel : expr := esub (eaddz (EAlu ALU_AND (EVar 9) (ELit 3)) 1) (EVar vk).

  Definition rng (lo hi a b : Z) : bool := (Z.leb lo a && Z.leb b hi)%bool.      (* [comment removed for export] *)
  Definition fact_ok (c : cell) (F : kentry) : bool :=
    match F with
    | KRange e lo hi =>
        if expr_eqb e (EVar 4) then rng lo hi (c_nlo c) (c_nhi c)
        else if expr_eqb e (EVar 8) then rng lo hi (c_cllo c) (c_clhi c)
        else if expr_eqb e (EVar 9) then rng lo hi 0 255
        else if expr_eqb e (EVar 1) then rng lo hi 1 1
        else if expr_eqb e (EVar vk) then rng lo hi 1 (if c_clhi c =? 0 then 1 else 4)
        else if expr_eqb e (EVar vq) then rng lo hi (c_qlo c) (c_qhi c)
        else if expr_eqb e (EVar vr) then rng lo hi (c_rlo c) (c_rhi c)
        else if (expr_eqb e e_ncl || expr_eqb e e_nqcl)%bool then rng lo hi (Z.max (c_nlo c + c_cllo c) (Llo K - 6)) (Z.min (c_nhi c + c_clhi c) (Lhi K - 6))
        else if expr_eqb e e_n1 then rng lo hi (c_nlo c + 1) (c_nhi c + 1)
        else if expr_eqb e e_r1 then rng lo hi (c_rlo c + 1) (c_rhi c + 1)
        else if expr_eqb e e_callsrel then (Z.leb 1 (c_cllo c) && rng lo hi 0 0)%bool
        else match e with ELit z => rng lo hi (z mod 2 ^ 64) (z mod 2 ^ 64) | _ => false end
    | _ => false
    end.

  Lemma rng_in : forall lo hi a b x, rng lo hi a b = true -> a <= x <= b -> lo <= x /\ x <= hi.
  Proof. intros lo hi a b x H Hx. unfold rng in H. apply andb_prop in H as [H1 H2]. apply Z.leb_le in H1, H2. lia. Qed.

  Lemma Lhi_bound : Lhi K < 2 ^ 27.
  Proof. unfold Lhi. assert (2 ^ K <= 2 ^ 10) by (apply Z.pow_le_mono_r; lia). lia. Qed.
  Lemma Llo_nonneg : 0 <= Llo K.
  Proof. unfold Llo. destruct (K =? 0) eqn:HK0; [lia|]. apply Z.eqb_neq in HK0. assert (0 < 2 ^ (K - 1)) by (apply Z.pow_pos_nonneg; lia). lia. Qed.

  Lemma uE_var : forall E x, uE E (EVar x) = bv_unsigned (ev E x).
  Proof. reflexivity. Qed.

  Lemma fact_ok_sound : forall c t E F, tin_ok K t -> in_cell c t -> eok t E -> fact_ok c F = true -> pure_holds E F.
  Proof.
    intros c t E F (Hn & Hcl & Hb2 & HL) (Cn & Ccl & Cq & Cr) (E4 & E8 & E9 & E1 & Ek & _ & Eq & Er & _) H.
    pose proof Lhi_bound as HLb. pose proof Llo_nonneg as HLn.
    destruct F as [ | | | | | e lo hi | | | | ]; try discriminate H. cbn [fact_ok] in H. cbn [pure_holds].
    change (bv_unsigned (edenot E e)) with (uE E e).
    destruct (expr_eqb e (EVar 4)) eqn:T1; [apply expr_eqb_eq in T1; subst e; rewrite E4; exact (rng_in _ _ _ _ _ H Cn)|].
    destruct (expr_eqb e (EVar 8)) eqn:T2; [apply expr_eqb_eq in T2; subst e; rewrite E8; exact (rng_in _ _ _ _ _ H Ccl)|].
    destruct (expr_eqb e (EVar 9)) eqn:T3; [apply expr_eqb_eq in T3; subst e; rewrite E9; exact (rng_in _ _ _ _ _ H Hb2)|].
    destruct (expr_eqb e (EVar 1)) eqn:T4; [apply expr_eqb_eq in T4; subst e; rewrite E1; apply (rng_in _ _ _ _ _ H); lia|].
    destruct (expr_eqb e (EVar vk)) eqn:T5.
    { apply expr_eqb_eq in T5; subst e. rewrite Ek. apply (rng_in _ _ _ _ _ H). unfold t_calls.
      destruct (c_clhi c =? 0) eqn:Hc0.
      - apply Z.eqb_eq in Hc0. assert (t_cl t = 0) by lia. replace (t_cl t =? 0) with true by (symmetry; apply Z.eqb_eq; assumption). lia.
      - destruct (t_cl t =? 0); [lia|]. pose proof (Z.mod_pos_bound (t_b2 t) 4 ltac:(lia)). lia. }
    destruct (expr_eqb e (EVar vq)) eqn:T6; [apply expr_eqb_eq in T6; subst e; rewrite Eq; exact (rng_in _ _ _ _ _ H Cq)|].
    destruct (expr_eqb e (EVar vr)) eqn:T7; [apply expr_eqb_eq in T7; subst e; rewrite Er; exact (rng_in _ _ _ _ _ H Cr)|].
    assert (Encl : uE E e_ncl = t_n t + t_cl t).
    { unfold uE, e_ncl, eadd. rewrite mkAlu_denot, u_add64. cbn [edenot]. rewrite uE_var in E4, E8. rewrite E4, E8. apply Z.mod_small. lia. }
    assert (Enq : uE E e_nq = t_n t).
    { unfold uE, e_nq, eadd, escale. rewrite mkAlu_denot, u_add64, mkMd_denot, u_mul64. cbn [edenot]. rewrite uE_var in Eq, Er. rewrite Eq, Er, u_lit64.
      change (4096 mod two64) with 4096. pose proof (Z.div_mod (t_n t) 4096 ltac:(lia)). pose proof (Z.mod_pos_bound (t_n t) 4096 ltac:(lia)).
      assert (0 <= t_n t / 4096) by (apply Z.div_pos; lia).
      rewrite (Z.mod_small (4096 * (t_n t / 4096))) by lia. rewrite (Z.mod_small (4096 * (t_n t / 4096) + t_n t mod 4096)) by lia. lia. }
    destruct (expr_eqb e e_ncl || expr_eqb e e_nqcl)%bool eqn:T8.
    { assert (Hv : uE E e = t_n t + t_cl t).
      { apply orb_prop in T8 as [T8|T8]; apply expr_eqb_eq in T8; subst e; [exact Encl|].
        unfold uE, e_nqcl, eadd. rewrite mkAlu_denot, u_add64. fold (eadd (escale 4096 (EVar vq)) (EVar vr)). fold e_nq. fold (uE E e_nq). rewrite Enq.
        cbn [edenot]. rewrite uE_var in E8. rewrite E8. apply Z.mod_small. lia. }
      rewrite Hv. apply (rng_in _ _ _ _ _ H). lia. }
    destruct (expr_eqb e e_n1) eqn:T9.
    { apply expr_eqb_eq in T9; subst e. unfold uE, e_n1, eadd. rewrite mkAlu_denot, u_add64. cbn [edenot]. rewrite uE_var in E4, E1. rewrite E4, E1.
      rewrite Z.mod_small by lia. apply (rng_in _ _ _ _ _ H). lia. }
    destruct (expr_eqb e e_r1) eqn:T10.
    { apply expr_eqb_eq in T10; subst e. unfold uE, e_r1, eadd. rewrite mkAlu_denot, u_add64. cbn [edenot]. rewrite uE_var in Er, E1. rewrite Er, E1.
      pose proof (Z.mod_pos_bound (t_n t) 4096 ltac:(lia)). rewrite Z.mod_small by lia. apply (rng_in _ _ _ _ _ H). lia. }
    destruct (expr_eqb e e_callsrel) eqn:T11.
    { apply expr_eqb_eq in T11; subst e. apply andb_prop in H as [Hc1 H]. apply Z.leb_le in Hc1.
      assert (Hv : uE E e_callsrel = 0).
      { unfold uE, e_callsrel, esub, eaddz. rewrite mkAlu_denot, u_sub64, mkAlu_denot, u_add64. cbn [edenot]. rewrite u_and64, !u_lit64.
        rewrite uE_var in E9, Ek. rewrite E9, Ek. unfold t_calls. replace (t_cl t =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
        change (3 mod two64) with (Z.ones 2). rewrite Z.land_ones by lia. change (2 ^ 2) with 4. change (1 mod two64) with 1.
        pose proof (Z.mod_pos_bound (t_b2 t) 4 ltac:(lia)). rewrite (Z.mod_small (t_b2 t mod 4 + 1)) by lia.
        replace (t_b2 t mod 4 + 1 - (1 + t_b2 t mod 4)) with 0 by lia. reflexivity. }
      rewrite Hv. apply (rng_in _ _ _ _ _ H). lia. }
    destruct e as [z| | | | | | |]; try discriminate H.
    unfold uE. cbn [edenot]. rewrite u_lit64. change two64 with (2 ^ 64). apply (rng_in _ _ _ _ _ H). lia.
  Qed.
End Sel.

(* [comment removed for export] *)
Definition B0a : expr := EExt false 0 1 (EBlob false 3 0 8).
Definition B0b : expr := EBlob false 3 0 1.

Lemma b0_val : forall E, exists w, 0 <= w < 256 /\ edenot E B0a = Z_to_bv 64 w /\ edenot E B0b = Z_to_bv 64 w.
Proof.
  intros E. unfold B0a, B0b. cbn [edenot]. unfold ext_val, blob_val, blob_bytes. cbn [Z.to_nat skipn].
  destruct (eb E 3%nat) as [|b r].
  - exists 0. split; [lia|]. cbn [firstn bytes_le_to_Z]. split; [|reflexivity].
    rewrite u_lit64. reflexivity.
  - exists (bv_unsigned b). pose proof (bv_unsigned_in_range 8 b) as Hb. change (bv_modulus 8) with 256 in Hb.
    split; [exact Hb|]. split.
    + cbn [firstn]. set (X := bytes_le_to_Z (b :: firstn 7 r)).
      assert (HX : 0 <= X < 2 ^ 64).
      { pose proof (bytes_le_to_Z_bound (b :: firstn 7 r)) as B. fold X in B. cbn [length] in B.
        pose proof (firstn_le_length 7 r) as L7.
        assert (2 ^ (8 * Z.of_nat (S (length (firstn 7 r)))) <= 2 ^ 64) by (apply Z.pow_le_mono_r; lia). lia. }
      rewrite u_lit64. change two64 with (2 ^ 64). rewrite (Z.mod_small X) by exact HX.
      f_equal. unfold ext_Z. cbn [Z.of_nat Z.mul]. change (2 ^ 0) with 1. rewrite Z.div_1_r.
      unfold X. cbn [bytes_le_to_Z]. change (8 * Z.of_nat 1) with 8. rewrite (lor_mod_pow2 _ _ 8) by lia.
      rewrite Z.shiftl_mul_pow2 by lia. rewrite Z.mod_mul by lia. rewrite Z.lor_0_r. apply Z.mod_small. exact Hb.
    + change (Z.to_nat 0) with O. cbn [skipn firstn bytes_le_to_Z]. rewrite Z.shiftl_0_l, Z.lor_0_r. reflexivity.
Qed.

Definition opfact_ok (HASHF : kentry) (w : Z) (F : kentry) : bool :=
  (kentry_eqb F HASHF ||
   match F with
   | KRange e lo hi =>
       match AX2.eval_closed (AX2.esubst B0b (ELit w) (AX2.esubst B0a (ELit w) e)) with
       | Some v => (Z.leb lo v && Z.leb v hi)%bool
       | None => false
       end
   | _ => false
   end)%bool.

Lemma opfact_ok_sound : forall HASHF E w F,
  edenot E B0a = Z_to_bv 64 w -> edenot E B0b = Z_to_bv 64 w -> pure_holds E HASHF ->
  opfact_ok HASHF w F = true -> pure_holds E F.
Proof.
  intros HASHF E w F Ha Hb HH H. unfold opfact_ok in H. apply orb_prop in H as [H|H].
  - apply kentry_eqb_eq in H. subst F. exact HH.
  - destruct F as [ | | | | | e lo hi | | | | ]; try discriminate H.
    destruct (AX2.eval_closed (AX2.esubst B0b (ELit w) (AX2.esubst B0a (ELit w) e))) as [v|] eqn:Hev; [|discriminate H].
    apply andb_prop in H as [H1 H2]. apply Z.leb_le in H1, H2.
    pose proof (AX2S.eval_closed_sound E _ _ Hev) as Hd. pose proof (AX2S.eval_closed_range _ _ Hev) as Hr.
    rewrite (AX2S.esubst_sound E B0b (ELit w)) in Hd by (cbn [edenot]; symmetry; exact Hb).
    rewrite (AX2S.esubst_sound E B0a (ELit w)) in Hd by (cbn [edenot]; symmetry; exact Ha).
    cbn [pure_holds]. rewrite Hd, u_lit64. change two64 with (2 ^ 64) in *. rewrite Z.mod_small by exact Hr. lia.
Qed.

(* [comment removed for export] *)
Inductive lnum : Type := LN (nlo nhi : Z) | LQ (qlo qhi rlo rhi : Z).
Definition ln_in (ln : lnum) (n : Z) : Prop :=
  match ln with
  | LN a b => a <= n <= b
  | LQ qa qb ra rb => qa <= n / 4096 <= qb /\ ra <= n mod 4096 <= rb
  end.
Definition cell_of (ln : lnum) (cl0 : bool) : cell :=
  let cllo := if cl0 then 0 else 1 in let clhi := if cl0 then 0 else 32767 in
  match ln with
  | LN a b => CELL a b cllo clhi 0 32767 0 4095
  | LQ qa qb ra rb => CELL (4096 * qa + ra) (4096 * qb + rb) cllo clhi qa qb ra rb
  end.

(* [comment removed for export] *)
Record gsel : Type := GS { gs_N0 : nat; gs_S0 : acs; gs_sub : sub; gs_a0s : list a0d; gs_lnums : list lnum; gs_leaves : list leafd; gs_ops : list opd;
                           gs_shapeB : shape; gs_sC2s : list shape; gs_short : bool }.
Definition gs_tab (g : gsel) : list (lnum * leafd) := combine (gs_lnums g) (gs_leaves g).
Definition gs_G (g : gsel) : grpd := GD (gs_N0 g) (gs_S0 g) (gs_sub g) (gs_a0s g) (gs_leaves g) (gs_ops g) (gs_shapeB g) (gs_sC2s g).

(* [comment removed for export] *)
Definition opsel (short : bool) (w : Z) : nat :=
  if short then 0%nat else
  let o := (Z.land w 63) mod 6 in
  if o =? 0 then (if Z.land w 64 =? 0 then 0%nat else 1%nat) else Z.to_nat (o + 1).

Section Family.
  Variables (vk vs5 vq vr : nat).
  Variable K : Z.
  Variable HASHF : kentry.
  Hypothesis HK : 0 <= K <= 10.
  Variable fam : list gsel.
  Variable cov : list (Z * Z * nat * nat).       (* [comment removed for export] *)
  Variable qcov : list (Z * Z * nat * nat).      (* [comment removed for export] *)
  Variable QMIN : Z.

  Definition NMIN : Z := Z.max 0 (Llo K - 6 - 32767).
  Definition NMAX : Z := Lhi K - 6.
  #[local] Notation FOK := (fact_ok vk vq vr K).

  Definition dflt_a0 : a0d := A0D [] PExit [] [].
  Definition dflt_op : opd := OD [] PExit [].
  Definition leaf_chk (g : gsel) (x : lnum * leafd) : bool :=
    forallb (fun cl0 : bool => let c := cell_of (fst x) cl0 in
                               (forallb (FOK c) (a0_F (nth (if cl0 then 0 else 1)%nat (gs_a0s g) dflt_a0)) && forallb (FOK c) (ld_F (snd x)))%bool) [true; false].
  Definition op_chk (g : gsel) (w : Z) : bool :=
    (Nat.ltb (opsel (gs_short g) w) (length (gs_ops g)) && forallb (opfact_ok HASHF w) (od_F (nth (opsel (gs_short g) w) (gs_ops g) dflt_op)))%bool.
  Definition sub_chk (s : sub) : bool :=
    match s with
    | [] => true
    | [(x, e)] => (Nat.eqb x 4 && expr_eqb e (e_nq vq vr))%bool
    | _ => false
    end.
  Definition grp_chk (g : gsel) : bool :=
    (Nat.eqb (length (gs_a0s g)) 2 && forallb (leaf_chk g) (gs_tab g) && forallb (op_chk g) (map Z.of_nat (seq 0 256)) && sub_chk (gs_sub g))%bool.

  Definition tab_at (gi li : nat) : option lnum :=
    match nth_error fam gi with
    | Some g => match nth_error (gs_tab g) li with Some x => Some (fst x) | None => None end
    | None => None
    end.
  Definition cov_entry_ok (x : Z * Z * nat * nat) : bool :=
    let '(lo, hi, gi, li) := x in
    match tab_at gi li with Some (LN a b) => (Z.leb a lo && Z.leb hi b)%bool | _ => false end.
  Definition qcov_entry_ok (x : Z * Z * nat * nat) : bool :=
    let '(rlo, rhi, gi, li) := x in
    match tab_at gi li with
    | Some (LQ qa qb ra rb) => (Z.leb ra rlo && Z.leb rhi rb && Z.ltb (4096 * (qa - 1) + rhi) (Z.max QMIN NMIN) && Z.ltb NMAX (4096 * (qb + 1) + rlo))%bool
    | _ => false
    end.
  Definition ivs (l : list (Z * Z * nat * nat)) : list (Z * Z) := map (fun x => (fst (fst (fst x)), snd (fst (fst x)))) l.
  (* [comment removed for export] *)
  Definition RLO : Z := if QMIN / 4096 =? NMAX / 4096 then QMIN mod 4096 else 0.      (* [comment removed for export] *)
  Definition RHI : Z := if QMIN / 4096 =? NMAX / 4096 then NMAX mod 4096 else 4095.
  Definition fam_chk : bool :=
    (forallb grp_chk fam
     && cover_ok (ivs cov) NMIN (Z.min NMAX (QMIN - 1)) && forallb cov_entry_ok cov
     && (Z.ltb NMAX QMIN || (cover_ok (ivs qcov) RLO RHI && forallb qcov_entry_ok qcov)))%bool.

  Hypothesis CHK : fam_chk = true.

  Lemma find_leaf : forall t, tin_ok K t -> exists g x, In g fam /\ In x (gs_tab g) /\ ln_in (fst x) (t_n t).
  Proof.
    intros t (Hn & Hcl & Hb2 & HL). unfold fam_chk in CHK.
    apply andb_prop in CHK as [C123 C4]. apply andb_prop in C123 as [C12 C3]. apply andb_prop in C12 as [_ C2].
    assert (Hrange : NMIN <= t_n t <= NMAX) by (unfold NMIN, NMAX; lia).
    assert (TA : forall gi li ln, tab_at gi li = Some ln -> exists g x, In g fam /\ In x (gs_tab g) /\ fst x = ln).
    { intros gi li ln H. unfold tab_at in H. destruct (nth_error fam gi) as [g|] eqn:Hg; [|discriminate].
      destruct (nth_error (gs_tab g) li) as [x|] eqn:Hx; [|discriminate]. injection H as <-.
      exists g, x. split; [exact (nth_error_In _ _ Hg)|]. split; [exact (nth_error_In _ _ Hx) | reflexivity]. }
    destruct (Z_lt_ge_dec (t_n t) QMIN) as [Hlt|Hge].
    - destruct (cover_ok_sound _ _ _ C2 (t_n t) ltac:(lia)) as [p [Hp Hr]].
      unfold ivs in Hp. apply in_map_iff in Hp as [[[[lo hi] gi] li] [<- Hin]]. cbn [fst snd] in Hr.
      pose proof (proj1 (forallb_forall _ _) C3 _ Hin) as Hc. cbn [cov_entry_ok] in Hc.
      destruct (tab_at gi li) as [[a b|]|] eqn:Ht; try discriminate Hc.
      apply andb_prop in Hc as [H1 H2]. apply Z.leb_le in H1, H2.
      destruct (TA _ _ _ Ht) as (g & x & Hg & Hx & Hfx). exists g, x. split; [exact Hg|]. split; [exact Hx|]. rewrite Hfx. cbn [ln_in]. lia.
    - apply orb_prop in C4 as [C4|C4]; [apply Z.ltb_lt in C4; lia|]. apply andb_prop in C4 as [C5 C6].
      pose proof (Z.mod_pos_bound (t_n t) 4096 ltac:(lia)) as Hr0. pose proof (Z.div_mod (t_n t) 4096 ltac:(lia)) as Hdm.
      assert (HR : RLO <= t_n t mod 4096 <= RHI).
      { unfold RLO, RHI. destruct (QMIN / 4096 =? NMAX / 4096) eqn:Hq; [|lia]. apply Z.eqb_eq in Hq.
        pose proof (Z.div_mod QMIN 4096 ltac:(lia)). pose proof (Z.div_mod NMAX 4096 ltac:(lia)).
        pose proof (Z.mod_pos_bound QMIN 4096 ltac:(lia)). pose proof (Z.mod_pos_bound NMAX 4096 ltac:(lia)).
        assert (QMIN / 4096 <= t_n t / 4096) by (apply Z.div_le_mono; lia). assert (t_n t / 4096 <= NMAX / 4096) by (apply Z.div_le_mono; lia). lia. }
      destruct (cover_ok_sound _ _ _ C5 (t_n t mod 4096) HR) as [p [Hp Hr]].
      unfold ivs in Hp. apply in_map_iff in Hp as [[[[rlo rhi] gi] li] [<- Hin]]. cbn [fst snd] in Hr.
      pose proof (proj1 (forallb_forall _ _) C6 _ Hin) as Hc. cbn [qcov_entry_ok] in Hc.
      destruct (tab_at gi li) as [[|qa qb ra rb]|] eqn:Ht; try discriminate Hc.
      apply andb_prop in Hc as [Hc H4]. apply andb_prop in Hc as [Hc H3]. apply andb_prop in Hc as [H1 H2].
      apply Z.leb_le in H1, H2. apply Z.ltb_lt in H3, H4.
      destruct (TA _ _ _ Ht) as (g & x & Hg & Hx & Hfx). exists g, x. split; [exact Hg|]. split; [exact Hx|]. rewrite Hfx. cbn [ln_in].
      split; [|lia]. split; nia.
  Qed.

  Lemma cell_of_in : forall ln t, tin_ok K t -> ln_in ln (t_n t) -> in_cell (cell_of ln (t_cl t =? 0)) t.
  Proof.
    intros ln t (Hn & Hcl & Hb2 & HL) Hin. pose proof (Lhi_bound K HK) as HLb.
    pose proof (Z.mod_pos_bound (t_n t) 4096 ltac:(lia)) as Hr0. pose proof (Z.div_mod (t_n t) 4096 ltac:(lia)) as Hdm.
    assert (0 <= t_n t / 4096) by (apply Z.div_pos; lia). assert (t_n t / 4096 < 32768) by (apply Z.div_lt_upper_bound; lia).
    unfold in_cell, cell_of. destruct ln as [a b|qa qb ra rb]; cbn [ln_in] in Hin; cbn [c_nlo c_nhi c_cllo c_clhi c_qlo c_qhi c_rlo c_rhi];
      destruct (t_cl t =? 0) eqn:Hc0; [apply Z.eqb_eq in Hc0 | apply Z.eqb_neq in Hc0 | apply Z.eqb_eq in Hc0 | apply Z.eqb_neq in Hc0]; repeat split; try lia; nia.
  Qed.

  Theorem select_x : forall t E, tin_ok K t -> eok vk vs5 vq vr HASHF t E ->
    exists g x v o, In g fam /\ In x (gs_tab g) /\ ln_in (fst x) (t_n t)
                    /\ In (gs_G g) (map gs_G fam) /\ In v (g_a0s (gs_G g)) /\ In (snd x) (g_leaves (gs_G g)) /\ In o (g_ops (gs_G g))
                    /\ sig_holds E (g_sub (gs_G g)) /\ Forall (pure_holds E) (g_facts v (snd x) o).
  Proof.
    intros t E Ht He. destruct (find_leaf t Ht) as (g & x & Hg & Hx & Hin).
    pose proof CHK as C. unfold fam_chk in C. apply andb_prop in C as [C _]. apply andb_prop in C as [C _]. apply andb_prop in C as [C _].
    pose proof (proj1 (forallb_forall _ _) C g Hg) as Cg. unfold grp_chk in Cg.
    apply andb_prop in Cg as [Cg Csub]. apply andb_prop in Cg as [Cg Cops]. apply andb_prop in Cg as [Clen Cleaves]. apply Nat.eqb_eq in Clen.
    pose proof (proj1 (forallb_forall _ _) Cleaves x Hx) as Cx. unfold leaf_chk in Cx.
    set (cl0 := t_cl t =? 0) in *.
    assert (Ccl : (forallb (FOK (cell_of (fst x) cl0)) (a0_F (nth (if cl0 then 0 else 1)%nat (gs_a0s g) dflt_a0))
                   && forallb (FOK (cell_of (fst x) cl0)) (ld_F (snd x)))%bool = true).
    { apply (proj1 (forallb_forall _ _) Cx cl0). destruct cl0; [left | right; left]; reflexivity. }
    apply andb_prop in Ccl as [Ca0 Cld].
    pose proof (cell_of_in (fst x) t Ht Hin) as Hcell. fold cl0 in Hcell.
    destruct (b0_val E) as (w & Hw & Hwa & Hwb).
    assert (Hwin : In w (map Z.of_nat (seq 0 256))).
    { apply in_map_iff. exists (Z.to_nat w). split; [lia|]. apply in_seq. lia. }
    pose proof (proj1 (forallb_forall _ _) Cops w Hwin) as Cw. unfold op_chk in Cw. apply andb_prop in Cw as [Cw1 Cw2]. apply Nat.ltb_lt in Cw1.
    set (v := nth (if cl0 then 0 else 1)%nat (gs_a0s g) dflt_a0) in *.
    set (o := nth (opsel (gs_short g) w) (gs_ops g) dflt_op) in *.
    exists g, x, v, o. split; [exact Hg|]. split; [exact Hx|]. split; [exact Hin|].
    split; [apply in_map; exact Hg|]. split; [cbn [gs_G g_a0s]; unfold v; apply nth_In; rewrite Clen; unfold cl0; destruct (t_cl t =? 0); lia|].
    split; [cbn [gs_G g_leaves]; destruct x as [xa xb]; exact (in_combine_r _ _ _ _ Hx)|]. split; [cbn [gs_G g_ops]; unfold o; apply nth_In; exact Cw1|].
    split.
    - cbn [gs_G g_sub]. unfold sub_chk in Csub. destruct (gs_sub g) as [|[y e] [|]]; [constructor | | discriminate Csub].
      apply andb_prop in Csub as [Hy Hee]. apply Nat.eqb_eq in Hy. apply expr_eqb_eq in Hee. subst y e.
      constructor; [|constructor]. cbn [fst snd].
      destruct He as (E4 & _ & _ & _ & _ & _ & Eq & Er & _). destruct Ht as (Hn & Hcl & _ & HL). pose proof (Lhi_bound K HK) as HLb.
      apply bv_eq. change (bv_unsigned (ev E 4%nat)) with (uE E (EVar 4)). rewrite E4.
      unfold e_nq, eadd, escale. rewrite mkAlu_denot, u_add64, mkMd_denot, u_mul64. cbn [edenot].
      change (bv_unsigned (ev E vq)) with (uE E (EVar vq)). change (bv_unsigned (ev E vr)) with (uE E (EVar vr)). rewrite Eq, Er, u_lit64.
      change (4096 mod two64) with 4096. pose proof (Z.div_mod (t_n t) 4096 ltac:(lia)). pose proof (Z.mod_pos_bound (t_n t) 4096 ltac:(lia)).
      assert (0 <= t_n t / 4096) by (apply Z.div_pos; lia).
      rewrite (Z.mod_small (4096 * (t_n t / 4096))) by lia. rewrite (Z.mod_small (4096 * (t_n t / 4096) + t_n t mod 4096)) by lia. lia.
    - unfold g_facts. apply Forall_app. split; [|apply Forall_app; split].
      + apply Forall_forall. intros F HF. exact (fact_ok_sound vk vs5 vq vr K HASHF HK _ t E F Ht Hcell He (proj1 (forallb_forall _ _) Ca0 F HF)).
      + apply Forall_forall. intros F HF. exact (fact_ok_sound vk vs5 vq vr K HASHF HK _ t E F Ht Hcell He (proj1 (forallb_forall _ _) Cld F HF)).
      + apply Forall_forall. intros F HF. destruct He as (_ & _ & _ & _ & _ & _ & _ & _ & HH).
        exact (opfact_ok_sound HASHF E w F Hwa Hwb HH (proj1 (forallb_forall _ _) Cw2 F HF)).
  Qed.

  (* [comment removed for export] *)
  Corollary select : forall t E, tin_ok K t -> eok vk vs5 vq vr HASHF t E -> exists G v l o, sel_ok (map gs_G fam) E G v l o.
  Proof.
    intros t E Ht He. destruct (select_x t E Ht He) as (g & x & v & o & _ & _ & _ & H1 & H2 & H3 & H4 & H5 & H6).
    exists (gs_G g), v, (snd x), o. repeat split; assumption.
  Qed.
End Family.

(* [comment removed for export] *)
Definition MAXS : Z := 9223372036854775807.
Definition line_of (neg : bool) : list Z * list Z := if neg then ([45; 49], [10]) else ([48], [10]).
Definition lineZ (neg : bool) : list Z := fst (line_of neg) ++ snd (line_of neg).
Fixpoint rep (l : list Z) (j : nat) : list Z := match j with O => [] | S j' => l ++ rep l j' end.
Definition shapeB_of (vk : nat) (neg : bool) : shape :=
  SEmitP 1 [SPLit (fst (line_of neg)); SPLit (snd (line_of neg))]
    (SCase (EVar vk) 1 (SHole 1) (SCase (EVar vk) 2 (SHole 2) (SCase (EVar vk) 3 (SHole 3) (SHole 4)))).
Definition sc2_of (neg : bool) (j : nat) (ex : Z) : shape :=
  match j with 1%nat => SExit ex | _ => SEmitP 1 [SPLit (rep (lineZ neg) (j - 1))] (SExit ex) end.
(* [comment removed for export] *)
Definition sC2s_of (vs5 : nat) (neg : bool) : list shape :=
  SNil :: map (fun j => SCase (EVar vs5) MAXS (sc2_of neg j 0) (sc2_of neg j 0)) [1; 2; 3; 4]%nat.

(* [comment removed for export] *)
Definition sC2s_flat_of (neg : bool) : list shape := SNil :: map (fun j => sc2_of neg j 0) [1; 2; 3; 4]%nat.
Definition sC2s_flat : list shape := sC2s_flat_of false.

Definition W1 (bs : list Z) : list event := map (WriteEv (Z_to_bv 64 1)) (map (Z_to_bv 8) bs).
(* [comment removed for export] *)
Definition TGT (neg : bool) (calls : nat) (cnt : bool) (fs : Fs.Fs) : TSet :=
  t_emit (W1 (lineZ neg)) (t_emit (W1 (rep (lineZ neg) (calls - 1))) (t_exit (Z_to_bv 64 0) fs)).     (* [comment removed for export] *)

Lemma den_tgt : forall vk vs5 neg E fs calls cnt,
  (1 <= calls <= 4)%nat -> uE E (EVar vk) = Z.of_nat calls -> (uE E (EVar vs5) <= MAXS <-> cnt = false) ->
  t_eq (DEN (shapeB_of vk neg) (sC2s_of vs5 neg) E fs) (TGT neg calls cnt fs).
Proof.
  intros vk vs5 neg E fs calls cnt Hc Hk Hs. unfold DEN, shapeB_of, TGT. cbn [sd].
  assert (HW : Wp E 1 [SPLit (fst (line_of neg)); SPLit (snd (line_of neg))] = W1 (lineZ neg)).
  { unfold Wp, W1, lineZ. cbn [flat_map piece_den]. rewrite app_nil_r, !map_app. reflexivity. }
  rewrite HW. apply t_emit_congr.
  assert (Hhole : forall j, (1 <= j <= 4)%nat ->
            t_eq (HOLES_C (sC2s_of vs5 neg) j E fs)
                 (t_emit (W1 (rep (lineZ neg) (j - 1))) (t_exit (Z_to_bv 64 0) fs))).
  { intros j Hj. unfold HOLES_C, sC2, sC2s_of. rewrite (hole_cls_small j ltac:(lia)).
    assert (Hnth : nth j (SNil :: map (fun j0 => SCase (EVar vs5) MAXS (sc2_of neg j0 0) (sc2_of neg j0 0)) [1; 2; 3; 4]%nat) SNil
                   = SCase (EVar vs5) MAXS (sc2_of neg j 0) (sc2_of neg j 0)).
    { destruct j as [|[|[|[|[|j]]]]]; try lia; reflexivity. }
    rewrite Hnth. cbn [sd]. change (bv_unsigned (edenot E (EVar vs5))) with (uE E (EVar vs5)).
    assert (Hsd : forall ex, t_eq (sd HUChain.noHOLES t_nil E fs (sc2_of neg j ex)) (t_emit (W1 (rep (lineZ neg) (j - 1))) (t_exit (Z_to_bv 64 ex) fs))).
    { intros ex. destruct j as [|[|j]]; [lia | |].
      - cbn [sc2_of sd Nat.sub rep W1 map]. apply t_eq_sym. apply t_emit_nil_eq. apply t_emit_has_nil.
      - cbn [sc2_of sd]. unfold Wp, W1. cbn [flat_map piece_den]. rewrite app_nil_r. apply t_eq_refl. }
    destruct (uE E (EVar vs5) <=? MAXS); apply Hsd. }
  change (bv_unsigned (edenot E (EVar vk))) with (uE E (EVar vk)). rewrite Hk.
  destruct calls as [|[|[|[|[|c]]]]]; try lia; cbn [Z.of_nat Pos.of_succ_nat Pos.succ Z.leb Z.compare Pos.compare Pos.compare_cont]; apply Hhole; lia.
Qed.

(* [comment removed for export] *)
Lemma den_tgt_flat : forall vk neg E fs calls cnt,
  (1 <= calls <= 4)%nat -> uE E (EVar vk) = Z.of_nat calls ->
  t_eq (DEN (shapeB_of vk neg) (sC2s_flat_of neg) E fs) (TGT neg calls cnt fs).
Proof.
  intros vk neg E fs calls cnt Hc Hk. unfold DEN, shapeB_of, TGT. cbn [sd].
  assert (HW : Wp E 1 [SPLit (fst (line_of neg)); SPLit (snd (line_of neg))] = W1 (lineZ neg)).
  { unfold Wp, W1, lineZ. cbn [flat_map piece_den]. rewrite app_nil_r, !map_app. reflexivity. }
  rewrite HW. apply t_emit_congr.
  assert (Hhole : forall j, (1 <= j <= 4)%nat ->
            t_eq (HOLES_C (sC2s_flat_of neg) j E fs) (t_emit (W1 (rep (lineZ neg) (j - 1))) (t_exit (Z_to_bv 64 0) fs))).
  { intros j Hj. unfold HOLES_C, sC2, sC2s_flat_of. rewrite (hole_cls_small j ltac:(lia)).
    assert (Hnth : nth j (SNil :: map (fun j0 => sc2_of neg j0 0) [1; 2; 3; 4]%nat) SNil = sc2_of neg j 0).
    { destruct j as [|[|[|[|[|j]]]]]; try lia; reflexivity. }
    rewrite Hnth. destruct j as [|[|j]]; [lia | |].
    - cbn [sc2_of sd Nat.sub rep W1 map]. apply t_eq_sym. apply t_emit_nil_eq. apply t_emit_has_nil.
    - cbn [sc2_of sd]. unfold Wp, W1. cbn [flat_map piece_den]. rewrite app_nil_r. apply t_eq_refl. }
  change (bv_unsigned (edenot E (EVar vk))) with (uE E (EVar vk)). rewrite Hk.
  destruct calls as [|[|[|[|[|c]]]]]; try lia; cbn [Z.of_nat Pos.of_succ_nat Pos.succ Z.leb Z.compare Pos.compare Pos.compare_cont]; apply Hhole; lia.
Qed.

Fixpoint shapes_eqb (a b : list shape) : bool :=
  match a, b with
  | [], [] => true
  | x :: a', y :: b' => (shape_eqb x y && shapes_eqb a' b')%bool
  | _, _ => false
  end.
Lemma shapes_eqb_eq : forall a b, shapes_eqb a b = true -> a = b.
Proof.
  induction a as [|x a IH]; intros [|y b] H; cbn [shapes_eqb] in H; try discriminate; [reflexivity|].
  apply andb_prop in H as [H1 H2]. apply shape_eqb_eq in H1. rewrite H1, (IH b H2). reflexivity.
Qed.
Definition ln_neg_ok (short : bool) (ln : lnum) : bool :=
  match ln with
  | LN a b => if short then Z.leb b 10 else Z.leb 11 a
  | LQ qa _ _ _ => (negb short && Z.leb 1 qa)%bool
  end.

Section FamilyThm.
  Variables (sp : word) (STR0 LIM : Z) (fs : Fs.Fs).
  Variable S0 : acs.
  Hypothesis S0_log : s_log (a_ss S0) = [].
  Variables (vk vs5 vq vr : nat).
  Variable K : Z.
  Variable HASHF : kentry.
  Hypothesis HK : 0 <= K <= 10.
  Variable fam : list gsel.
  Variable cov qcov : list (Z * Z * nat * nat).
  Variable QMIN : Z.

  Definition shp_chk (g : gsel) : bool :=
    (shape_eqb (gs_shapeB g) (shapeB_of vk (gs_short g))
     && (shapes_eqb (gs_sC2s g) (sC2s_of vs5 (gs_short g)) || shapes_eqb (gs_sC2s g) (sC2s_flat_of (gs_short g)))
     && forallb (fun x => ln_neg_ok (gs_short g) (fst x)) (gs_tab g))%bool.

  Hypothesis HG : forall g, In g fam -> grp_stmt sp STR0 LIM fs (gs_G g).
  Hypothesis HBASE : forall g, In g fam -> gs_S0 g = inst_list S0 (gs_sub g).
  Hypothesis SIDE : forallb grp_side (map gs_G fam) = true.
  Hypothesis CHK : fam_chk vk vq vr K HASHF fam cov qcov QMIN = true.
  Hypothesis SHP : forallb shp_chk fam = true.

  Theorem family_num : forall (PHIb : env -> Prop) t E R FULL model,
    tin_ok K t -> eok vk vs5 vq vr HASHF t E ->
    cs_ok HSEGS H0T LIM (SINVg PHIb sp STR0) (argHt STR0) (bv_unsigned sp) fs E S0 R FULL model ->
    crz HSEGS (cfg_of HSEGS R (pc S0) FULL model) (TGT (t_n t <? 11) (Z.to_nat (t_calls t)) (t_cnt t) (m_fs model)).
  Proof.
    intros PHIb t E R FULL model Ht He HC.
    destruct (select_x vk vs5 vq vr K HASHF HK fam cov qcov QMIN CHK t E Ht He) as (g & x & v & o & Hg & Hx & Hin & H1 & H2 & H3 & H4 & H5 & H6).
    assert (HGm : forall G, In G (map gs_G fam) -> grp_stmt sp STR0 LIM fs G).
    { intros G HGi. apply in_map_iff in HGi as [g' [<- Hg']]. exact (HG g' Hg'). }
    assert (HBm : forall G, In G (map gs_G fam) -> g_S0 G = inst_list S0 (g_sub G)).
    { intros G HGi. apply in_map_iff in HGi as [g' [<- Hg']]. exact (HBASE g' Hg'). }
    pose proof (drive_sel sp STR0 LIM fs S0 S0_log (map gs_G fam) HGm HBm SIDE PHIb E R FULL model (gs_G g) v (snd x) o
                  (conj H1 (conj H2 (conj H3 (conj H4 (conj H5 H6))))) HC) as HD.
    eapply crz_conseq; [exact HD|]. cbn [gs_G g_shapeB g_sC2s].
    pose proof (proj1 (forallb_forall _ _) SHP g Hg) as Sg. unfold shp_chk in Sg.
    apply andb_prop in Sg as [Sg S3]. apply andb_prop in Sg as [S1 S2]. apply shape_eqb_eq in S1. rewrite S1.
    pose proof (proj1 (forallb_forall _ _) S3 x Hx) as Sx. cbn beta in Sx.
    assert (Hneg : gs_short g = (t_n t <? 11)).
    { destruct Ht as (Hn & _). destruct (fst x) as [a b|qa qb ra rb]; cbn [ln_neg_ok ln_in] in Sx, Hin.
      - destruct (gs_short g); apply Z.leb_le in Sx; symmetry; [apply Z.ltb_lt | apply Z.ltb_ge]; lia.
      - apply andb_prop in Sx as [Sa Sb]. apply Z.leb_le in Sb. destruct (gs_short g); [discriminate Sa|]. symmetry. apply Z.ltb_ge.
        pose proof (Z.div_mod (t_n t) 4096 ltac:(lia)). pose proof (Z.mod_pos_bound (t_n t) 4096 ltac:(lia)). lia. }
    destruct He as (_ & _ & _ & _ & Ek & Es & _). destruct Ht as (_ & Hcl & Hb2 & _).
    assert (Hcalls : 1 <= t_calls t <= 4).
    { unfold t_calls. destruct (t_cl t =? 0); [lia|]. pose proof (Z.mod_pos_bound (t_b2 t) 4 ltac:(lia)). lia. }
    apply orb_prop in S2 as [S2|S2].
    - apply shapes_eqb_eq in S2. rewrite S2, Hneg. apply den_tgt; [lia | rewrite Ek; lia | exact Es].
    - apply shapes_eqb_eq in S2. rewrite S2, Hneg. apply den_tgt_flat; [lia | rewrite Ek; lia].
  Qed.
End FamilyThm.

(* [comment removed for export] *)
Definition eokx (vk vs5 vq vr : nat) (HASHF : kentry) (t : tin) (E : env) : Prop :=
  uE E (EVar 4) = t_n t /\ uE E (EVar 8) = t_cl t /\ uE E (EVar 9) = t_b2 t
  /\ uE E (EVar vk) = t_calls t /\ (uE E (EVar vs5) <= 9223372036854775807 <-> t_cnt t = false)
  /\ uE E (EVar vq) = t_n t / 4096 /\ uE E (EVar vr) = t_n t mod 4096
  /\ pure_holds E HASHF.

Theorem family_numx : forall (sp : word) (STR0 LIM : Z) (fs : Fs.Fs) (S0 : acs), s_log (a_ss S0) = [] ->
  forall (vk vs5 vq vr : nat) (K : Z) (HASHF : kentry), 0 <= K <= 10 ->
  forall (fam : list gsel) (cov qcov : list (Z * Z * nat * nat)) (QMIN : Z),
  (forall g, In g fam -> grp_stmt sp STR0 LIM fs (gs_G g)) ->
  (forall g, In g fam -> gs_S0 g = inst_list S0 (gs_sub g)) ->
  forallb grp_side (map gs_G fam) = true ->
  fam_chk vk vq vr K HASHF fam cov qcov QMIN = true ->
  forallb (shp_chk vk vs5) fam = true ->
  forall (PHIb : env -> Prop) t E R FULL model,
    tin_ok K t -> eokx vk vs5 vq vr HASHF t E ->
    cs_ok HSEGS H0T LIM (SINVg PHIb sp STR0) (argHt STR0) (bv_unsigned sp) fs E S0 R FULL model ->
    crz HSEGS (cfg_of HSEGS R (pc S0) FULL model) (TGT (t_n t <? 11) (Z.to_nat (t_calls t)) (t_cnt t) (m_fs model)).
Proof.
  intros sp STR0 LIM fs S0 Hlog vk vs5 vq vr K HASHF HK fam cov qcov QMIN HG HB SIDE CHK SHP PHIb t E R FULL model Ht (E4 & E8 & E9 & Ek & Es & Eq & Er & HH) HC.
  apply (family_num sp STR0 LIM fs S0 Hlog vk vs5 vq vr K HASHF HK fam cov qcov QMIN HG HB SIDE CHK SHP PHIb t E R FULL model Ht); [|exact HC].
  pose proof (co_sinv _ _ _ _ _ _ _ _ _ _ _ _ HC) as [HS _]. destruct HS as (_ & _ & _ & H1 & _).
  unfold eok. repeat split; try assumption; try (apply (proj1 Es)); try (apply (proj2 Es)).
  unfold uE. change (EVar 1) with (EVar V_ARGC). rewrite H1. apply u64_lit. lia.
Qed.
