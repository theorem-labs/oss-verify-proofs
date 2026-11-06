(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.jsoncons.fuzz_json_encoder.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PropExec AxSymExec3 AxSymExec3B AxSymExec3Sound AsanPlanCore LibSym SegRun SegPlan Pm4PlanKit.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PmLibDefs PmEncSpecs PmLibSpecsW PmRef PmRefFacts RelLeaf.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutCert Require Import CutCert CutOps CutHeap CutAuto CutLib CutHeap2 CutAutoX Pm4CutKit CutCertA CutHeapA CutAutoXA.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutGen Require Import PsoInstXA ParseSomeChkXA.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutGenW Require Import RelObsXA PsoWTabXA PsoWKit2XA.
Import ListNotations. Import AX2. Import AX2S.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module PSOWT2.
Import PSOC.
Definition leqb (l1 l2 : list nat) : bool := if list_eq_dec Nat.eq_dec l1 l2 then true else false.
Module G := PSO.G.
(* [comment removed for export] *)
Definition visw_leaf (i : nat) (c : CC.cutpoint) (k : nat) (ps : SR.post_spec) : bool :=
  match CH2.ret_of G.RETS i k, PSO.pview (CC.cp_know c), PSO.pview (SR.ps_cells ps) with
  | Some j, Some t, Some l =>
      match PSOWK2.ldec c (SR.ps_cells ps) (PSOWT.woff i) (PSOWT.ppv i) with
      | Some (st, _, a) => (OBSXA.act_eqb a PMR.ALitDone && Z.eqb (PSOWT.woff j + Z.max 0 (PSO.d_adv (PSO.mkdelta (SR.ps_cells ps) t l))) (PSOWT.woff i)
                          && negb (existsb (PSO.region_eqb (PE, 220, ELit 1)) (CC.cp_F c)) && negb (Z.eqb st PML.ST_STRING) && negb (Z.eqb st PML.ST_NUMBER))%bool
      | None => false end
  | _, _, _ => false end.
Definition visw_chk (i : nat) (c : CC.cutpoint) (k : nat) (ps : SR.post_spec) (tg : CC.tag) : bool :=
  match tg with CC.TOther pc => if negb (Z.eqb pc VNULL || Z.eqb pc VBOOL)%bool then true else if PSO.dead_chk i ps pc then true else visw_leaf i c k ps | _ => true end.
  (* [comment removed for export] *)
Lemma VISW_all : CH2.leaves_all G.CPS G.TAGS visw_chk = true. Proof. vm_compute. reflexivity. Qed.
Lemma VISW : forall pc i c k ps0, CH2.is_leaf G.CPS G.TAGS i c k ps0 (CC.TOther pc) -> pc = VNULL \/ pc = VBOOL -> PSO.dead_chk i ps0 pc = false ->
  forall j t l, CH2.ret_of G.RETS i k = Some j -> PSO.pview (CC.cp_know c) = Some t -> PSO.pview (SR.ps_cells ps0) = Some l ->
  exists st bv a, PSOWK2.ldec c (SR.ps_cells ps0) (PSOWT.woff i) (PSOWT.ppv i) = Some (st, bv, a) /\ a = PMR.ALitDone /\
    PSOWT.woff j + Z.max 0 (PSO.d_adv (PSO.mkdelta (SR.ps_cells ps0) t l)) = PSOWT.woff i /\ existsb (PSO.region_eqb (PE, 220, ELit 1)) (CC.cp_F c) = false /\
    st <> PML.ST_STRING /\ st <> PML.ST_NUMBER.
Proof.
  intros pc i c k ps0 IL Hpc Hd j t l Hj Ht Hl. pose proof (CH2.leaves_all_sound _ _ _ VISW_all _ _ _ _ _ IL) as X. cbn [visw_chk] in X.
  assert (E : (Z.eqb pc VNULL || Z.eqb pc VBOOL)%bool = true) by (destruct Hpc as [-> | ->]; reflexivity). rewrite E, Hd in X. cbn [negb] in X.
  unfold visw_leaf in X. rewrite Hj, Ht, Hl in X.
  destruct (PSOWK2.ldec c (SR.ps_cells ps0) (PSOWT.woff i) (PSOWT.ppv i)) as [[[st bv] a]|]; [|discriminate X].
  apply andb_prop in X as [X X5]. apply andb_prop in X as [X X4]. apply andb_prop in X as [X X3]. apply andb_prop in X as [X1 X2].
  apply PSOWK2.act_eqb_eq in X1. apply Z.eqb_eq in X2. apply negb_true_iff in X3. apply negb_true_iff, Z.eqb_neq in X4. apply negb_true_iff, Z.eqb_neq in X5.
  exists st, bv, a. exact (conj eq_refl (conj X1 (conj X2 (conj X3 (conj X4 X5))))).
Qed.

(* [comment removed for export] *)
Definition beforew_leaf (isparent : bool) (i : nat) (c : CC.cutpoint) (k : nat) (ps : SR.post_spec) : bool :=
  let cells := SR.ps_cells ps in
  match CH2.ret_of G.RETS i k, PSO.pview (CC.cp_know c), PSO.pview cells with
  | Some j, Some t, Some l =>
      if PSOWT.eofk j then (PSO.kind_eqb (PSO.kind_of i) PSO.KSm && PSOWK2.eof_leaf c cells)%bool
      else (Z.eqb (PSOWT.woff j + Z.max 0 (PSO.d_adv (PSO.mkdelta cells t l))) (PSOWT.woff i) &&
            match PSO.tst c cells t with Some z => PSOWK2.ntok z | None => false end &&
            leqb (PSOWT.ppv j) ((if isparent then [(CC.cp_nx (PSO.cutn j) - APC.NCS - 1)%nat] else []) ++ PSOWT.ppv i) && forallb (fun v => Nat.ltb v (CC.cp_nx c)) (PSOWT.ppv i) &&
            negb (PSO.kind_eqb (PSO.kind_of i) PSO.KSm))%bool
  | _, _, _ => false end.
Definition callw_chk (i : nat) (c : CC.cutpoint) (k : nat) (ps : SR.post_spec) (tg : CC.tag) : bool :=
  match tg with
  | CC.TOther pc => if pc =? ERRH then (if PSO.dead_chk i ps pc then true else beforew_leaf false i c k ps)
                    else if pc =? PARENT then (if PSO.dead_chk i ps pc then true else beforew_leaf true i c k ps) else true
  | _ => true end.
Lemma CALLW_all : CH2.leaves_all G.CPS G.TAGS callw_chk = true. Proof. vm_compute. reflexivity. Qed.
Lemma BEFW : forall pc (b : bool) i c k ps0, CH2.is_leaf G.CPS G.TAGS i c k ps0 (CC.TOther pc) -> (pc = ERRH /\ b = false) \/ (pc = PARENT /\ b = true) -> PSO.dead_chk i ps0 pc = false ->
  forall j t l, CH2.ret_of G.RETS i k = Some j -> PSO.pview (CC.cp_know c) = Some t -> PSO.pview (SR.ps_cells ps0) = Some l ->
  (PSOWT.eofk j = true /\ PSO.kind_of i = PSO.KSm /\ PSOWK2.eof_leaf c (SR.ps_cells ps0) = true) \/
  (PSOWT.eofk j = false /\ PSOWT.woff j + Z.max 0 (PSO.d_adv (PSO.mkdelta (SR.ps_cells ps0) t l)) = PSOWT.woff i /\
   (exists z, PSO.tst c (SR.ps_cells ps0) t = Some z /\ 1 <= z <= 28 /\ z <> PML.ST_STRING /\ z <> PML.ST_NUMBER) /\
   PSOWT.ppv j = (if b then [(CC.cp_nx (PSO.cutn j) - APC.NCS - 1)%nat] else []) ++ PSOWT.ppv i /\
   (forall v, In v (PSOWT.ppv i) -> (v < CC.cp_nx c)%nat) /\
   PSO.kind_of i <> PSO.KSm).
Proof.
  intros pc b i c k ps0 IL Hpc Hd j t l Hj Ht Hl. pose proof (CH2.leaves_all_sound _ _ _ CALLW_all _ _ _ _ _ IL) as X. cbn [callw_chk] in X.
  assert (X' : beforew_leaf b i c k ps0 = true).
  { destruct Hpc as [[-> ->] | [-> ->]]; [rewrite Z.eqb_refl, Hd in X; exact X|]. replace (PARENT =? ERRH) with false in X by reflexivity. rewrite Z.eqb_refl, Hd in X. exact X. }
  clear X. unfold beforew_leaf in X'. rewrite Hj, Ht, Hl in X'. destruct (PSOWT.eofk j) eqn:EK.
  - left. apply andb_prop in X' as [X1 X2]. apply PSO.kind_eqb_eq in X1. split; [reflexivity | exact (conj X1 X2)].
  - right. apply andb_prop in X' as [X' X4]. apply andb_prop in X' as [X' X3b]. apply andb_prop in X' as [X' X3]. apply andb_prop in X' as [X1 X2].
    apply Z.eqb_eq in X1. split; [reflexivity|]. split; [exact X1|].
    split; [destruct (PSO.tst c (SR.ps_cells ps0) t) as [z|]; [|discriminate X2]; exists z; unfold PSOWK2.ntok in X2;
            apply andb_prop in X2 as [X2 N2]; apply andb_prop in X2 as [X2 N1]; apply andb_prop in X2 as [Z1 Z2];
            apply Z.leb_le in Z1; apply Z.leb_le in Z2; apply negb_true_iff, Z.eqb_neq in N1; apply negb_true_iff, Z.eqb_neq in N2; split; [reflexivity | exact (conj (conj Z1 Z2) (conj N1 N2))]|].
    split; [|split; [|apply negb_true_iff in X4; intros E; rewrite E in X4; discriminate X4]].
    + unfold leqb in X3. destruct (list_eq_dec Nat.eq_dec _ _) as [EQ|NE]; [exact EQ | discriminate X3].
    + intros v Hv. pose proof (proj1 (forallb_forall _ _) X3b v Hv) as Y. apply Nat.ltb_lt in Y. exact Y.
Qed.
(* [comment removed for export] *)
Lemma KSM_u0 : forall i, PSO.kind_of i = PSO.KSm -> PSO.u0 i = true.
Proof.
  intros i Hk. assert (X : forallb (fun j => negb (PSO.kind_eqb (PSO.kind_of j) PSO.KSm) || PSO.u0 j) (seq 0 PSO.NCUT) = true) by (vm_compute; reflexivity).
  destruct (Nat.lt_ge_cases i PSO.NCUT) as [L|G].
  - rewrite forallb_forall in X. specialize (X i ltac:(apply in_seq; lia)). rewrite Hk in X. exact X.
  - exfalso. unfold PSO.kind_of in Hk. rewrite nth_overflow in Hk; [discriminate Hk|].
    assert (LEN : length PSO.INFO = PSO.NCUT) by (vm_compute; reflexivity). rewrite LEN. exact G.
Qed.

(* [comment removed for export] *)
Definition setecw_leaf (i : nat) (c : CC.cutpoint) (k : nat) (ps : SR.post_spec) : bool :=
  match PSO.kind_of i with
  | PSO.KSe => (expr_eqb (PSO.reg_of ps 11) (EVar PSOWT.SEV) && Nat.ltb PSOWT.SEV (CC.cp_nx c))%bool
  | PSO.KErrh => if PSOWT.eofk i then expr_eqb (PSO.reg_of ps 11) (ELit PMR.E_EOF)
                 else match PSOWK2.ldec c (SR.ps_cells ps) (PSOWT.woff i) (PSOWT.ppv i) with
                      | Some (_, _, PMR.AErr code _) => (expr_eqb (PSO.reg_of ps 11) (ELit code) && (1 <=? code) && (code <=? 31))%bool
                      | _ => false end
  | _ => false end.
Definition setecw_chk (i : nat) (c : CC.cutpoint) (k : nat) (ps : SR.post_spec) (tg : CC.tag) : bool :=
  match tg with CC.TOther pc => if pc =? SETEC then (if PSO.dead_chk i ps pc then true else setecw_leaf i c k ps) else true | _ => true end.
Lemma SETECW_all : CH2.leaves_all G.CPS G.TAGS setecw_chk = true. Proof. vm_compute. reflexivity. Qed.
Lemma SETECW : forall i c k ps0, CH2.is_leaf G.CPS G.TAGS i c k ps0 (CC.TOther SETEC) -> PSO.dead_chk i ps0 SETEC = false ->
  (PSO.kind_of i = PSO.KSe /\ PSO.reg_of ps0 11 = EVar PSOWT.SEV /\ (PSOWT.SEV < CC.cp_nx c)%nat) \/
  (PSO.kind_of i = PSO.KErrh /\ PSOWT.eofk i = true /\ PSO.reg_of ps0 11 = ELit PMR.E_EOF) \/
  (PSO.kind_of i = PSO.KErrh /\ PSOWT.eofk i = false /\ exists st bv code kk, PSOWK2.ldec c (SR.ps_cells ps0) (PSOWT.woff i) (PSOWT.ppv i) = Some (st, bv, PMR.AErr code kk) /\
     PSO.reg_of ps0 11 = ELit code /\ 1 <= code <= 31).
Proof.
  intros i c k ps0 IL Hd. pose proof (CH2.leaves_all_sound _ _ _ SETECW_all _ _ _ _ _ IL) as X. cbn [setecw_chk] in X. rewrite Z.eqb_refl, Hd in X.
  unfold setecw_leaf in X. destruct (PSO.kind_of i); try discriminate X.
  - left. apply andb_prop in X as [X1 X2]. apply expr_eqb_eq in X1. apply Nat.ltb_lt in X2. exact (conj eq_refl (conj X1 X2)).
  - right. destruct (PSOWT.eofk i) eqn:EK.
    + left. apply expr_eqb_eq in X. exact (conj eq_refl (conj eq_refl X)).
    + right. destruct (PSOWK2.ldec c (SR.ps_cells ps0) (PSOWT.woff i) (PSOWT.ppv i)) as [[[st bv] a]|]; [|discriminate X].
      destruct a; try discriminate X. apply andb_prop in X as [X X3]. apply andb_prop in X as [X1 X2]. apply expr_eqb_eq in X1. apply Z.leb_le in X2. apply Z.leb_le in X3.
      split; [reflexivity|]. split; [reflexivity|]. exists st, bv, code, consumed. exact (conj eq_refl (conj X1 (conj X2 X3))).
Qed.

(* [comment removed for export] *)
Definition popw_leaf (i : nat) (c : CC.cutpoint) (k : nat) (ps : SR.post_spec) : bool :=
  let cells := SR.ps_cells ps in
  match CH2.ret_of G.RETS i k, PSO.pview (CC.cp_know c), PSO.pview cells with
  | Some j, Some t, Some l =>
      match PSO.kind_of i with
      | PSO.KCsl => match PSOWK2.ldec c cells (PSOWT.woff i) (PSOWT.ppv i) with
                    | Some (_, _, PMR.APop kk) => Z.eqb (PSOWT.woff j + Z.max 0 (PSO.d_adv (PSO.mkdelta cells t l))) (PSOWT.woff i + (if kk then 1 else 0))
                    | _ => false end
      | PSO.KSm => PSOWK2.eof_leafm 1 c cells
      | _ => false end
  | _, _, _ => false end.
Definition popw_chk (i : nat) (c : CC.cutpoint) (k : nat) (ps : SR.post_spec) (tg : CC.tag) : bool :=
  match tg with CC.TOther pc => if pc =? POPST then (if PSO.dead_chk i ps pc then true else popw_leaf i c k ps) else true | _ => true end.
Lemma POPW_all : CH2.leaves_all G.CPS G.TAGS popw_chk = true. Proof. vm_compute. reflexivity. Qed.
Lemma POPW : forall i c k ps0, CH2.is_leaf G.CPS G.TAGS i c k ps0 (CC.TOther POPST) -> PSO.dead_chk i ps0 POPST = false ->
  forall j t l, CH2.ret_of G.RETS i k = Some j -> PSO.pview (CC.cp_know c) = Some t -> PSO.pview (SR.ps_cells ps0) = Some l ->
  (PSO.kind_of i = PSO.KCsl /\ exists st bv kk, PSOWK2.ldec c (SR.ps_cells ps0) (PSOWT.woff i) (PSOWT.ppv i) = Some (st, bv, PMR.APop kk) /\
     PSOWT.woff j + Z.max 0 (PSO.d_adv (PSO.mkdelta (SR.ps_cells ps0) t l)) = PSOWT.woff i + (if kk then 1 else 0)) \/
  (PSO.kind_of i = PSO.KSm /\ PSOWK2.eof_leafm 1 c (SR.ps_cells ps0) = true).
Proof.
  intros i c k ps0 IL Hd j t l Hj Ht Hl. pose proof (CH2.leaves_all_sound _ _ _ POPW_all _ _ _ _ _ IL) as X. cbn [popw_chk] in X. rewrite Z.eqb_refl, Hd in X.
  unfold popw_leaf in X. rewrite Hj, Ht, Hl in X. destruct (PSO.kind_of i); try discriminate X.
  - right. exact (conj eq_refl X).
  - left. destruct (PSOWK2.ldec c (SR.ps_cells ps0) (PSOWT.woff i) (PSOWT.ppv i)) as [[[st bv] a]|]; [|discriminate X]. destruct a; try discriminate X.
    apply Z.eqb_eq in X. split; [reflexivity|]. exists st, bv, consume. exact (conj eq_refl X).
Qed.

(* [comment removed for export] *)
Definition vpushw_leaf (i : nat) (c : CC.cutpoint) (k : nat) (ps : SR.post_spec) : bool :=
  let cells := SR.ps_cells ps in
  match CH2.ret_of G.RETS i k, PSO.pview (CC.cp_know c), PSO.pview cells with
  | Some j, Some t, Some l =>
      match PSOWK2.ldec c cells (PSOWT.woff i) (PSOWT.ppv i), PSOWT.ract j with
      | Some (st, _, a), Some a' => (OBSXA.act_eqb a a' && Z.eqb (PSOWT.woff j + Z.max 0 (PSO.d_adv (PSO.mkdelta cells t l))) (PSOWT.woff i) && PSOWK2.ntok st)%bool
      | _, _ => false end
  | _, _, _ => false end.
Definition vpushw_chk (i : nat) (c : CC.cutpoint) (k : nat) (ps : SR.post_spec) (tg : CC.tag) : bool :=
  match tg with CC.TOther pc => if pc =? VPUSH then (if PSO.dead_chk i ps pc then true else vpushw_leaf i c k ps) else true | _ => true end.
Lemma VPUSHW_all : CH2.leaves_all G.CPS G.TAGS vpushw_chk = true. Proof. vm_compute. reflexivity. Qed.
Lemma VPUSHW : forall i c k ps0, CH2.is_leaf G.CPS G.TAGS i c k ps0 (CC.TOther VPUSH) -> PSO.dead_chk i ps0 VPUSH = false ->
  forall j t l, CH2.ret_of G.RETS i k = Some j -> PSO.pview (CC.cp_know c) = Some t -> PSO.pview (SR.ps_cells ps0) = Some l ->
  exists st bv a, PSOWK2.ldec c (SR.ps_cells ps0) (PSOWT.woff i) (PSOWT.ppv i) = Some (st, bv, a) /\ PSOWT.ract j = Some a /\
    PSOWT.woff j + Z.max 0 (PSO.d_adv (PSO.mkdelta (SR.ps_cells ps0) t l)) = PSOWT.woff i /\ 1 <= st <= 28 /\ st <> PML.ST_STRING /\ st <> PML.ST_NUMBER.
Proof.
  intros i c k ps0 IL Hd j t l Hj Ht Hl. pose proof (CH2.leaves_all_sound _ _ _ VPUSHW_all _ _ _ _ _ IL) as X. cbn [vpushw_chk] in X. rewrite Z.eqb_refl, Hd in X.
  unfold vpushw_leaf in X. rewrite Hj, Ht, Hl in X.
  destruct (PSOWK2.ldec c (SR.ps_cells ps0) (PSOWT.woff i) (PSOWT.ppv i)) as [[[st bv] a]|]; [|discriminate X]. destruct (PSOWT.ract j) as [a'|]; [|discriminate X].
  apply andb_prop in X as [X X3]. apply andb_prop in X as [X1 X2]. apply PSOWK2.act_eqb_eq in X1. subst a'. apply Z.eqb_eq in X2.
  unfold PSOWK2.ntok in X3. apply andb_prop in X3 as [X3 N2]. apply andb_prop in X3 as [X3 N1]. apply andb_prop in X3 as [Z1 Z2].
  apply Z.leb_le in Z1. apply Z.leb_le in Z2. apply negb_true_iff, Z.eqb_neq in N1. apply negb_true_iff, Z.eqb_neq in N2.
  exists st, bv, a. exact (conj eq_refl (conj eq_refl (conj X2 (conj (conj Z1 Z2) (conj N1 N2))))).
Qed.

(* [comment removed for export] *)
Definition pushbw_leaf (i : nat) (c : CC.cutpoint) (k : nat) (ps : SR.post_spec) : bool :=
  let cells := SR.ps_cells ps in
  match PSO.pview (CC.cp_know c), PSO.pview cells with
  | Some t, Some l =>
      match PSOWK2.ldec c cells (PSOWT.woff i) (PSOWT.ppv i) with
      | Some (st, bv, PMR.ANumber) =>
          (PSOWK2.ntok st && Z.eqb (PSO.d_adv (PSO.mkdelta cells t l)) 0 && Z.eqb (PSOWT.woff i) 0 &&
           match PSO.reg_of ps 11 with
           | EVar v => Nat.eqb v bv
           | ELit z => RLF.all_bytes (fun b => negb (RLF.byte_adm bv cells b) || (b =? z))
           | _ => false end)%bool
      | _ => false end
  | _, _ => false end.
Definition pushbw_chk (i : nat) (c : CC.cutpoint) (k : nat) (ps : SR.post_spec) (tg : CC.tag) : bool :=
  match tg with CC.TOther pc => if pc =? PUSHB then (if PSO.dead_chk i ps pc then true else pushbw_leaf i c k ps) else true | _ => true end.
Lemma PUSHBW_all : CH2.leaves_all G.CPS G.TAGS pushbw_chk = true. Proof. vm_compute. reflexivity. Qed.
Lemma PUSHBW : forall i c k ps0, CH2.is_leaf G.CPS G.TAGS i c k ps0 (CC.TOther PUSHB) -> PSO.dead_chk i ps0 PUSHB = false ->
  forall t l, PSO.pview (CC.cp_know c) = Some t -> PSO.pview (SR.ps_cells ps0) = Some l ->
  exists st bv, PSOWK2.ldec c (SR.ps_cells ps0) (PSOWT.woff i) (PSOWT.ppv i) = Some (st, bv, PMR.ANumber) /\
    1 <= st <= 28 /\ st <> PML.ST_STRING /\ st <> PML.ST_NUMBER /\ PSO.d_adv (PSO.mkdelta (SR.ps_cells ps0) t l) = 0 /\ PSOWT.woff i = 0 /\
    ((exists v, PSO.reg_of ps0 11 = EVar v /\ v = bv) \/
     (exists z, PSO.reg_of ps0 11 = ELit z /\ RLF.all_bytes (fun b => negb (RLF.byte_adm bv (SR.ps_cells ps0) b) || (b =? z)) = true)).
Proof.
  intros i c k ps0 IL Hd t l Ht Hl. pose proof (CH2.leaves_all_sound _ _ _ PUSHBW_all _ _ _ _ _ IL) as X. cbn [pushbw_chk] in X. rewrite Z.eqb_refl, Hd in X.
  unfold pushbw_leaf in X. rewrite Ht, Hl in X.
  destruct (PSOWK2.ldec c (SR.ps_cells ps0) (PSOWT.woff i) (PSOWT.ppv i)) as [[[st bv] a]|]; [|discriminate X]. destruct a; try discriminate X.
  apply andb_prop in X as [X R11]. apply andb_prop in X as [X W0]. apply andb_prop in X as [N D0]. apply Z.eqb_eq in D0. apply Z.eqb_eq in W0.
  unfold PSOWK2.ntok in N. apply andb_prop in N as [N N2]. apply andb_prop in N as [N N1]. apply andb_prop in N as [Z1 Z2].
  apply Z.leb_le in Z1. apply Z.leb_le in Z2. apply negb_true_iff, Z.eqb_neq in N1. apply negb_true_iff, Z.eqb_neq in N2.
  exists st, bv. split; [reflexivity|]. split; [exact (conj Z1 Z2)|]. split; [exact N1|]. split; [exact N2|]. split; [exact D0|]. split; [exact W0|].
  destruct (PSO.reg_of ps0 11) as [z|v| | | | | |]; try discriminate R11; [right; exists z; exact (conj eq_refl R11) | left; exists v; apply Nat.eqb_eq in R11; exact (conj eq_refl R11)].
Qed.

(* [comment removed for export] *)
Definition gsew_leaf (i : nat) (c : CC.cutpoint) (k : nat) (ps : SR.post_spec) (j : nat) (s : CC.subst) : bool :=
  let cells := SR.ps_cells ps in
  match CC.slook s PSOWT.SEV with
  | ELit z => match PSO.kind_of i with
              | PSO.KSm => ((z =? 1) && PSOWK2.eof_leaf c cells)%bool
              | PSO.KErrh => if PSOWT.eofk i then z =? 1
                             else match PSOWK2.ldec c cells (PSOWT.woff i) (PSOWT.ppv i) with
                                  | Some (_, _, PMR.AErr code _) => ((z =? code) && (1 <=? code) && (code <=? 31))%bool | _ => false end
              | _ => false end
  | _ => false end.
Definition gsew_chk (i : nat) (c : CC.cutpoint) (k : nat) (ps : SR.post_spec) (tg : CC.tag) : bool :=
  match tg with CC.TGoto j s => if PSO.kind_eqb (PSO.kind_of j) PSO.KSe then gsew_leaf i c k ps j s else true | _ => true end.
Lemma GSEW_all : CH2.leaves_all G.CPS G.TAGS gsew_chk = true. Proof. vm_compute. reflexivity. Qed.
Lemma GSEW : forall i c k ps0 j s, CH2.is_leaf G.CPS G.TAGS i c k ps0 (CC.TGoto j s) -> PSO.kind_of j = PSO.KSe ->
  exists z, CC.slook s PSOWT.SEV = ELit z /\
    ((PSO.kind_of i = PSO.KSm /\ z = 1 /\ PSOWK2.eof_leaf c (SR.ps_cells ps0) = true) \/
     (PSO.kind_of i = PSO.KErrh /\ PSOWT.eofk i = true /\ z = 1) \/
     (PSO.kind_of i = PSO.KErrh /\ PSOWT.eofk i = false /\ exists st bv kk, PSOWK2.ldec c (SR.ps_cells ps0) (PSOWT.woff i) (PSOWT.ppv i) = Some (st, bv, PMR.AErr z kk) /\ 1 <= z <= 31)).
Proof.
  intros i c k ps0 j s IL KJ. pose proof (CH2.leaves_all_sound _ _ _ GSEW_all _ _ _ _ _ IL) as X. cbn [gsew_chk] in X. rewrite KJ in X. cbn [PSO.kind_eqb] in X.
  unfold gsew_leaf in X. destruct (CC.slook s PSOWT.SEV) as [z| | | | | | |]; try discriminate X. exists z. split; [reflexivity|].
  destruct (PSO.kind_of i); try discriminate X.
  - left. apply andb_prop in X as [X1 X2]. apply Z.eqb_eq in X1. exact (conj eq_refl (conj X1 X2)).
  - right. destruct (PSOWT.eofk i) eqn:EK.
    + left. apply Z.eqb_eq in X. exact (conj eq_refl (conj eq_refl X)).
    + right. destruct (PSOWK2.ldec _ _ _ _) as [[[st bv] a]|]; [|discriminate X]. destruct a; try discriminate X.
      apply andb_prop in X as [X X3]. apply andb_prop in X as [X1 X2]. apply Z.eqb_eq in X1. subst code. apply Z.leb_le in X2. apply Z.leb_le in X3.
      split; [reflexivity|]. split; [reflexivity|]. exists st, bv, consumed. exact (conj eq_refl (conj X2 X3)).
Qed.

(* [comment removed for export] *)
Definition offk (kj : PSO.kind) : Z := if PSO.kind_eqb kj PSO.KL2 then 1 else 0.
Definition ectest (nx : nat) (cells : list kentry) (t : PSO.pv) : bool :=      (* [comment removed for export] *)
  match PSO.v_ec t with Some (EVar v) => (PSO.rng_in cells (EVar v) 1 4294967295 && Nat.ltb v nx)%bool | _ => false end.
Definition gsamew_leaf (i : nat) (c : CC.cutpoint) (k : nat) (ps : SR.post_spec) (j : nat) (s : CC.subst) : bool :=
  let cells := SR.ps_cells ps in
  match PSO.pview (CC.cp_know c), PSO.pview cells with
  | Some t, Some l =>
    let d := PSO.mkdelta cells t l in let dd := Z.max 0 (PSO.d_adv d) in let kj := PSO.kind_of j in
    let nf220 := negb (existsb (PSO.region_eqb (PE, 220, ELit 1)) (CC.cp_F c)) in
    if PSO.is_loopk kj then
      (negb (PSO.kind_eqb kj PSO.KCsl) &&
       match PSO.kind_of i with
       | PSO.KH | PSO.KHQ | PSO.KL | PSO.KLQ | PSO.KLZ | PSO.KL3 => (Z.eqb (offk kj + dd) 0 && negb (PSO.kind_eqb kj PSO.KL2) && nf220)%bool
       | PSO.KL2 => (Z.eqb (offk kj + dd) 1 && nf220)%bool
       | PSO.KCsl => match PSOWK2.ldec c cells (PSOWT.woff i) (PSOWT.ppv i) with
                     | Some (st, _, PMR.AGoto st' true) => ((st' =? st) && Z.eqb (offk kj + dd) (PSOWT.woff i + 1) && PSOWK2.ntok st)%bool
                     | _ => false end
       | PSO.KPt _ => (Z.eqb (offk kj + dd) (match PSOWT.ract i with Some PMR.AComma => 1 | _ => 0 end) && implb (PSO.d_adv d =? 1) (negb (PSO.curk (PSO.kind_of i))) &&
                       implb (PSO.kind_eqb kj PSO.KL2) (match PSOWT.ract i with Some PMR.AComma => true | _ => false end) && nf220)%bool
       | PSO.KSm => ((dd =? 0) && PSO.kind_eqb kj PSO.KH && nf220)%bool
       | PSO.KDead => true
       | _ => false end)%bool
    else if PSO.kind_eqb kj PSO.KRetx then
       match PSO.kind_of i with
       | PSO.KH | PSO.KHQ | PSO.KL | PSO.KLQ | PSO.KLZ | PSO.KL3 => (negb (PSO.d_adv d =? 1) && nf220)%bool
       | PSO.KPt _ => (negb (PSO.d_adv d =? 1) && (match PSOWT.ract i with Some PMR.AComma => ectest (CC.cp_nx c) cells t | _ => true end) && nf220)%bool
       | PSO.KSetec => true
       | PSO.KSm => negb (PSO.d_adv d =? 1)
       | PSO.KDead => true
       | _ => false end
    else true
  | _, _ => false end.
Definition gsamew_chk (i : nat) (c : CC.cutpoint) (k : nat) (ps : SR.post_spec) (tg : CC.tag) : bool :=
  match tg with CC.TGoto j s =>
    match PSO.pview (CC.cp_know c), PSO.pview (SR.ps_cells ps) with
    | Some t, Some l => match PSO.gclass i c (SR.ps_cells ps) t l (PSO.mkdelta (SR.ps_cells ps) t l) with Some PSO.GSame => gsamew_leaf i c k ps j s | _ => true end
    | _, _ => true end
  | _ => true end.
Lemma GSAMEW_all : CH2.leaves_all G.CPS G.TAGS gsamew_chk = true. Proof. vm_compute. reflexivity. Qed. (* [comment removed for export] *)
Lemma GSAMEW : forall i c k ps0 j s t l, CH2.is_leaf G.CPS G.TAGS i c k ps0 (CC.TGoto j s) ->
  PSO.pview (CC.cp_know c) = Some t -> PSO.pview (SR.ps_cells ps0) = Some l ->
  PSO.gclass i c (SR.ps_cells ps0) t l (PSO.mkdelta (SR.ps_cells ps0) t l) = Some PSO.GSame -> gsamew_leaf i c k ps0 j s = true.
Proof.
  intros i c k ps0 j s t l IL Ht Hl HG. pose proof (CH2.leaves_all_sound _ _ _ GSAMEW_all _ _ _ _ _ IL) as X. cbn [gsamew_chk] in X. rewrite Ht, Hl, HG in X. exact X.
Qed.

(* [comment removed for export] *)
Definition gaccw_leaf (i : nat) (c : CC.cutpoint) (k : nat) (ps : SR.post_spec) (j : nat) (s : CC.subst) : bool :=
  let cells := SR.ps_cells ps in
  match PSO.pview (CC.cp_know c), PSO.pview cells with
  | Some t, Some l =>
    let d := PSO.mkdelta cells t l in let kj := PSO.kind_of j in
    (negb (PSO.d_adv d =? 1) &&
     match PSO.kind_of i with
     | PSO.KSm => PSO.kind_eqb kj PSO.KRetx
     | PSO.KH | PSO.KHQ => (expr_eqb (PSO.v_wptr t) PSO.CURH && PSO.lo_ge (CC.cp_know c) (EVar JV) 1)%bool
     | _ => false end &&
     ((PSO.is_loopk kj && negb (PSO.kind_eqb kj PSO.KCsl) && negb (PSO.kind_eqb kj PSO.KL2)) || PSO.kind_eqb kj PSO.KRetx))%bool
  | _, _ => false end.
Definition gaccw_chk (i : nat) (c : CC.cutpoint) (k : nat) (ps : SR.post_spec) (tg : CC.tag) : bool :=
  match tg with CC.TGoto j s =>
    match PSO.pview (CC.cp_know c), PSO.pview (SR.ps_cells ps) with
    | Some t, Some l => match PSO.gclass i c (SR.ps_cells ps) t l (PSO.mkdelta (SR.ps_cells ps) t l) with Some PSO.GAccept => gaccw_leaf i c k ps j s | _ => true end
    | _, _ => true end
  | _ => true end.
Lemma GACCW_all : CH2.leaves_all G.CPS G.TAGS gaccw_chk = true. Proof. vm_compute. reflexivity. Qed.
Lemma GACCW : forall i c k ps0 j s t l, CH2.is_leaf G.CPS G.TAGS i c k ps0 (CC.TGoto j s) ->
  PSO.pview (CC.cp_know c) = Some t -> PSO.pview (SR.ps_cells ps0) = Some l ->
  PSO.gclass i c (SR.ps_cells ps0) t l (PSO.mkdelta (SR.ps_cells ps0) t l) = Some PSO.GAccept -> gaccw_leaf i c k ps0 j s = true.
Proof.
  intros i c k ps0 j s t l IL Ht Hl HG. pose proof (CH2.leaves_all_sound _ _ _ GACCW_all _ _ _ _ _ IL) as X. cbn [gaccw_chk] in X. rewrite Ht, Hl, HG in X. exact X.
Qed.
(* [comment removed for export] *)
Definition tgt_loopw (kj : PSO.kind) : bool := (PSO.is_loopk kj && negb (PSO.kind_eqb kj PSO.KCsl) && negb (PSO.kind_eqb kj PSO.KL2))%bool.
Definition gstepw_leaf (i : nat) (c : CC.cutpoint) (k : nat) (ps : SR.post_spec) (j : nat) (s : CC.subst) (s2 : Z) : bool :=
  let cells := SR.ps_cells ps in
  match PSO.pview (CC.cp_know c), PSO.pview cells with
  | Some t, Some l =>
    let d := PSO.mkdelta cells t l in let kj := PSO.kind_of j in
    (PSO.is_same (PSO.d_done d) && PSOWK2.ntok s2 && tgt_loopw kj && (PSOWT.woff i + 1 =? Z.max 0 (PSO.d_adv d)) &&
     match PSO.kind_of i with
     | PSO.KCsl => match PSOWK2.ldec c cells (PSOWT.woff i) (PSOWT.ppv i) with Some (_, _, PMR.AGoto s2' true) => s2' =? s2 | _ => false end
     | PSO.KErrh => negb (PSOWT.eofk i) && match PSOWK2.ldec c cells (PSOWT.woff i) (PSOWT.ppv i) with Some (_, _, PMR.AGoto s2' true) => s2' =? s2 | _ => false end
     | PSO.KVis _ => expr_eqb (PSO.v_level t) (EVar LEVELV) &&
                     (((s2 =? PML.ST_ACCEPT) && PSO.rng_in cells (EVar LEVELV) 0 (2 ^ 32 - 1) &&
                        PSO.has cells (KRange (EAlu Instr.ALU_SLTU (EAlu Instr.ALU_SUB (EExt true 0 4 (EVar LEVELV)) (ELit 0)) (ELit 1)) 1 1))      (* [comment removed for export] *)
                      || ((s2 =? PML.ST_EXPECT_COMMA_OR_END) && PSO.rng_in cells (EVar LEVELV) 1 (2 ^ 32 - 1)))
     | _ => false end)%bool
  | _, _ => false end.
Definition gstepw_chk (i : nat) (c : CC.cutpoint) (k : nat) (ps : SR.post_spec) (tg : CC.tag) : bool :=
  match tg with CC.TGoto j s =>
    match PSO.pview (CC.cp_know c), PSO.pview (SR.ps_cells ps) with
    | Some t, Some l => match PSO.gclass i c (SR.ps_cells ps) t l (PSO.mkdelta (SR.ps_cells ps) t l) with Some (PSO.GStep _ s2) => gstepw_leaf i c k ps j s s2 | _ => true end
    | _, _ => true end
  | _ => true end.
Lemma GSTEPW_all : CH2.leaves_all G.CPS G.TAGS gstepw_chk = true. Proof. vm_compute. reflexivity. Qed.
Lemma GSTEPW : forall i c k ps0 j s t l s1 s2, CH2.is_leaf G.CPS G.TAGS i c k ps0 (CC.TGoto j s) ->
  PSO.pview (CC.cp_know c) = Some t -> PSO.pview (SR.ps_cells ps0) = Some l ->
  PSO.gclass i c (SR.ps_cells ps0) t l (PSO.mkdelta (SR.ps_cells ps0) t l) = Some (PSO.GStep s1 s2) -> gstepw_leaf i c k ps0 j s s2 = true.
Proof.
  intros i c k ps0 j s t l s1 s2 IL Ht Hl HG. pose proof (CH2.leaves_all_sound _ _ _ GSTEPW_all _ _ _ _ _ IL) as X. cbn [gstepw_chk] in X. rewrite Ht, Hl, HG in X. exact X.
Qed.
Definition gpopw_leaf (i : nat) (c : CC.cutpoint) (k : nat) (ps : SR.post_spec) (j : nat) (s : CC.subst) : bool :=
  let cells := SR.ps_cells ps in
  match PSO.pview (CC.cp_know c), PSO.pview cells with
  | Some t, Some l =>
    let d := PSO.mkdelta cells t l in let kj := PSO.kind_of j in
    (PSO.is_same (PSO.d_done d) && (PSOWT.woff i =? Z.max 0 (PSO.d_adv d)) && PSO.kind_eqb (PSO.kind_of i) PSO.KPop && (tgt_loopw kj || PSO.kind_eqb kj PSO.KRetx))%bool
  | _, _ => false end.
Definition gpopw_chk (i : nat) (c : CC.cutpoint) (k : nat) (ps : SR.post_spec) (tg : CC.tag) : bool :=
  match tg with CC.TGoto j s =>
    match PSO.pview (CC.cp_know c), PSO.pview (SR.ps_cells ps) with
    | Some t, Some l => match PSO.gclass i c (SR.ps_cells ps) t l (PSO.mkdelta (SR.ps_cells ps) t l) with Some (PSO.GPop _) => gpopw_leaf i c k ps j s | _ => true end
    | _, _ => true end
  | _ => true end.
Lemma GPOPW_all : CH2.leaves_all G.CPS G.TAGS gpopw_chk = true. Proof. vm_compute. reflexivity. Qed.
Lemma GPOPW : forall i c k ps0 j s t l v, CH2.is_leaf G.CPS G.TAGS i c k ps0 (CC.TGoto j s) ->
  PSO.pview (CC.cp_know c) = Some t -> PSO.pview (SR.ps_cells ps0) = Some l ->
  PSO.gclass i c (SR.ps_cells ps0) t l (PSO.mkdelta (SR.ps_cells ps0) t l) = Some (PSO.GPop v) -> gpopw_leaf i c k ps0 j s = true.
Proof.
  intros i c k ps0 j s t l v IL Ht Hl HG. pose proof (CH2.leaves_all_sound _ _ _ GPOPW_all _ _ _ _ _ IL) as X. cbn [gpopw_chk] in X. rewrite Ht, Hl, HG in X. exact X.
Qed.
Definition gpushw_leaf (i : nat) (c : CC.cutpoint) (k : nat) (ps : SR.post_spec) (j : nat) (s : CC.subst) (s2 : Z) : bool :=
  let cells := SR.ps_cells ps in
  match PSO.pview (CC.cp_know c), PSO.pview cells with
  | Some t, Some l =>
    let d := PSO.mkdelta cells t l in let kj := PSO.kind_of j in
    (PSO.is_same (PSO.d_done d) && PSOWK2.ntok s2 && tgt_loopw kj && (PSOWT.woff i + 1 =? Z.max 0 (PSO.d_adv d)) && PSO.kind_eqb (PSO.kind_of i) PSO.KVpush &&
     match PSOWT.ract i with Some PMR.ASlash => s2 =? PML.ST_SLASH | Some PMR.APushCr => s2 =? PML.ST_CR | _ => false end)%bool
  | _, _ => false end.
Definition gpushw_chk (i : nat) (c : CC.cutpoint) (k : nat) (ps : SR.post_spec) (tg : CC.tag) : bool :=
  match tg with CC.TGoto j s =>
    match PSO.pview (CC.cp_know c), PSO.pview (SR.ps_cells ps) with
    | Some t, Some l => match PSO.gclass i c (SR.ps_cells ps) t l (PSO.mkdelta (SR.ps_cells ps) t l) with Some (PSO.GPush _ s2) => gpushw_leaf i c k ps j s s2 | _ => true end
    | _, _ => true end
  | _ => true end.
Lemma GPUSHW_all : CH2.leaves_all G.CPS G.TAGS gpushw_chk = true. Proof. vm_compute. reflexivity. Qed.
Lemma GPUSHW : forall i c k ps0 j s t l s1 s2, CH2.is_leaf G.CPS G.TAGS i c k ps0 (CC.TGoto j s) ->
  PSO.pview (CC.cp_know c) = Some t -> PSO.pview (SR.ps_cells ps0) = Some l ->
  PSO.gclass i c (SR.ps_cells ps0) t l (PSO.mkdelta (SR.ps_cells ps0) t l) = Some (PSO.GPush s1 s2) -> gpushw_leaf i c k ps0 j s s2 = true.
Proof.
  intros i c k ps0 j s t l s1 s2 IL Ht Hl HG. pose proof (CH2.leaves_all_sound _ _ _ GPUSHW_all _ _ _ _ _ IL) as X. cbn [gpushw_chk] in X. rewrite Ht, Hl, HG in X. exact X.
Qed.
End PSOWT2.
