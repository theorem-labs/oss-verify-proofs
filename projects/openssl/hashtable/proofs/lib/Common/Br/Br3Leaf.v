(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Uint63 PrimString.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType RiscvSemantics Fs State Run.
From OSSVerify.Proofs.openssl.hashtable.lib.Common.Cfg Require Import ShapeAlgBase ShapeCfg NodesCfg LedgerCfg LazyCfg.
From OSSVerify.Proofs.openssl.hashtable.lib.Common.FX Require Import
  W64 ITrie FxSpec FxInstr FxState FxMem FxExec FxRel FxKind FxMemSound FxImage FxRun FxRn FxHandoff FxLazy FxCellFrame
  FxDrive FxDrive3.
From OSSVerify.Proofs.openssl.hashtable.lib Require Import PropExec AsanAcct AxSymExec3 AxSymExec3Sound BackingAlgebra AsanCeil.
From OSSVerify.Proofs.openssl.hashtable.lib.Common.Cx Require Import CxPlan CxPlanSound CxOpt.
From OSSVerify.Proofs.openssl.hashtable.lib.Common.Br Require Import BrEnv BrMem BrLedger BrMain BrRev BrRevLedger BrClass Br3Root Br3Ops.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

(* [comment removed for export] *)
Definition is_commit (o : vop) : bool := match fst o with OpCommit => true | _ => false end.

(* [comment removed for export] *)
Definition ops3_chk (n : int) (ops : list vop) : bool :=
  forallb (fun o : vop => (0 <? to_Z (snd (snd o)))
                          && (if is_commit o then (to_Z (fent_tag (snd o)) <? to_Z n) else (to_Z n <=? to_Z (fent_tag (snd o))))) ops.

Lemma ops3_get n ops o : ops3_chk n ops = true -> In o ops ->
  0 < to_Z (snd (snd o)) /\ (is_commit o = true -> to_Z (fent_tag (snd o)) < to_Z n)
  /\ (is_commit o = false -> to_Z n <= to_Z (fent_tag (snd o))).
Proof.
  unfold ops3_chk. intros Hc Ho. rewrite forallb_forall in Hc. pose proof (Hc o Ho) as H1.
  apply andb_prop in H1 as [Hl Ht]. apply Z.ltb_lt in Hl. split; [exact Hl|].
  destruct (is_commit o); split; intros Hq; try discriminate; [apply Z.ltb_lt | apply Z.leb_le]; exact Ht.
Qed.

Lemma pw_disj_app : forall l1 l2 p q, pw_disj (l1 ++ l2) -> In p l1 -> In q l2 -> e_disj p q.
Proof.
  induction l1 as [|a l1 IH]; intros l2 p q Hd Hp Hq; [destruct Hp|].
  cbn [app pw_disj] in Hd. destruct Hd as [Ha Hd]. destruct Hp as [<-|Hp].
  - exact (proj1 (Forall_forall _ _) Ha q (in_or_app _ _ _ (or_intror Hq))).
  - exact (IH l2 p q Hd Hp Hq).
Qed.

Lemma pw_disj_nth : forall (l : list (word * word)) i j p q,
  pw_disj l -> i <> j -> nth_error l i = Some p -> nth_error l j = Some q -> e_disj p q.
Proof.
  induction l as [|x l IH]; intros i j p q Hd Hne Hi Hj; [destruct i; discriminate|].
  destruct Hd as [Hx Hl]. rewrite Forall_forall in Hx.
  destruct i as [|i], j as [|j]; cbn [nth_error] in Hi, Hj.
  - contradiction.
  - injection Hi as <-. apply Hx. exact (nth_error_In _ _ Hj).
  - injection Hj as <-. apply e_disj_sym. apply Hx. exact (nth_error_In _ _ Hi).
  - apply (IH i j); [exact Hl | congruence | exact Hi | exact Hj].
Qed.

Lemma pw_disj_seps : forall l, pw_disj l -> CXS.seps l.
Proof.
  induction l as [|p l IH]; intros Hd; [constructor|].
  destruct Hd as [Hp Hl]. constructor; [|exact (IH Hl)].
  apply Forall_forall. intros q Hq. pose proof (proj1 (Forall_forall _ _) Hp q Hq) as Hpq.
  unfold CXS.iv_disjoint. unfold e_disj, e_hi, e_lo, e_sz in Hpq. exact Hpq.
Qed.

Lemma maps_match_exact_rev E : forall ms l, CAP.no_fog ms = true -> l = map (CXS.amap_den E) ms -> CXS.maps_match E ms l.
Proof.
  induction ms as [|am ms IH]; intros l Hnf ->; [reflexivity|].
  cbn [CAP.no_fog forallb] in Hnf. apply andb_prop in Hnf as [H1 H2]. apply negb_true_iff in H1.
  cbn [CXS.maps_match map]. rewrite H1. right. exists (map (CXS.amap_den E) ms). split; [reflexivity | exact (IH _ H2 eq_refl)].   (* [comment removed for export] *)
Qed.

Lemma amap_eqb_eq (x y : CAP.amap) : CAP.amap_eqb x y = true -> x = y.
Proof.
  destruct x as [b1 l1 k1], y as [b2 l2 k2]. unfold CAP.amap_eqb. cbn [CAP.am_base CAP.am_len CAP.am_kind].
  intros H. apply andb_prop in H as [H Hk]. apply andb_prop in H as [Hb Hl].
  apply AX2S.expr_eqb_eq in Hb, Hl. subst. destruct k1, k2; try discriminate; reflexivity.
Qed.
Definition amap_mem (x : CAP.amap) (l : list CAP.amap) : bool := existsb (CAP.amap_eqb x) l.
Lemma amap_mem_In x l : amap_mem x l = true -> In x l.
Proof. unfold amap_mem. intros H. apply existsb_exists in H as (y & Hy & He). rewrite (amap_eqb_eq _ _ He). exact Hy. Qed.

(* [comment removed for export] *)
Lemma page_base_inside (a : word) lo hi : lo mod 4096 = 0 -> hi mod 4096 = 0 -> lo <= bv_unsigned a < hi ->
  bv_unsigned (page_base a) mod 4096 = 0 /\ lo <= bv_unsigned (page_base a) /\ bv_unsigned (page_base a) + 4096 <= hi.
Proof.
  intros Hlo Hhi Ha. pose proof (br_u64 a) as Hu.
  assert (Ep : bv_unsigned (page_base a) = bv_unsigned a / 4096 * 4096).
  { unfold page_base, page_base_of, page_size. rewrite Z_to_bv_unsigned. apply bv_wrap_small.
    change (bv_modulus 64) with (2 ^ 64). clear - Hu. Z.div_mod_to_equations. lia. }
  rewrite Ep. clear - Hlo Hhi Ha. Z.div_mod_to_equations. lia.
Qed.

(* [comment removed for export] *)
Definition xt_find (XT : list (int * AX2.lin)) (t : int) : option AX2.lin :=
  if (t =? 0)%uint63 then Some (0, [])
  else match List.find (fun p => (fst p =? t)%uint63) XT with Some p => Some (snd p) | None => None end.

Definition ent_chkX (XT : list (int * AX2.lin)) (am : CAP.amap) (e : fent) : bool :=
  let '(t, off, len) := e in
  match CAP.am_len am, xt_find XT t with
  | AX2.ELit l, Some lt => (l =? to_Z len) && lin_match (AX2.lin_of (CAP.am_base am)) lt (to_Z off)
  | _, _ => false
  end.

Fixpoint ents_chkX (XT : list (int * AX2.lin)) (ms : list CAP.amap) (es : list fent) : bool :=
  match ms, es with
  | [], [] => true
  | am :: ms', e :: es' => ent_chkX XT am e && ents_chkX XT ms' es'
  | _, _ => false
  end.

(* [comment removed for export] *)
Lemma pair_eqb_eq (x y : AX2.expr * AX2.expr) : CAP.pair_eqb x y = true -> x = y.
Proof.
  destruct x as [a b], y as [c d]. unfold CAP.pair_eqb. cbn [fst snd]. intros H. apply andb_prop in H as [H1 H2].
  apply AX2S.expr_eqb_eq in H1, H2. subst. reflexivity.
Qed.
Definition pair_mem (x : AX2.expr * AX2.expr) (l : list (AX2.expr * AX2.expr)) : bool := existsb (CAP.pair_eqb x) l.
Lemma pair_mem_In x l : pair_mem x l = true -> In x l.
Proof. unfold pair_mem. intros H. apply existsb_exists in H as (y & Hy & He). rewrite (pair_eqb_eq _ _ He). exact Hy. Qed.

Fixpoint rem1 (p : AX2.expr * AX2.expr) (l : list (AX2.expr * AX2.expr)) : option (list (AX2.expr * AX2.expr)) :=
  match l with
  | [] => None
  | q :: r => if CAP.pair_eqb p q then Some r else option_map (cons q) (rem1 p r)
  end.

Fixpoint ab_split (L' old : list (AX2.expr * AX2.expr)) : list (AX2.expr * AX2.expr) :=
  match L' with
  | [] => []
  | p :: r => match rem1 p old with Some old' => ab_split r old' | None => p :: ab_split r old end
  end.

Definition new_bnd (p : AX2.expr * AX2.expr) : option Z :=
  match snd p with AX2.ELit l => if (0 <=? l) && (l <? 2 ^ 62) then Some (l + l / 8 + 16384) else None | _ => None end.

Fixpoint new_bound (l : list (AX2.expr * AX2.expr)) : option Z :=
  match l with
  | [] => Some 0
  | p :: r => match new_bnd p, new_bound r with Some a, Some b => Some (a + b) | _, _ => None end
  end.

(* [comment removed for export] *)
Notation "a &&& b" := (if a then b else false) (at level 40, left associativity, only parsing).
Notation "a ||| b" := (if a then true else b) (at level 50, left associativity, only parsing).

Section LeafModel.
Variable segs : list Segment.
Variable A : CAP.atable.
Variable Lim : Z.
Variable SINV : AX2.env -> (word -> option byte) -> Prop.
Variable argH : AX2.env -> word -> bool.
Variable ISP : Z.
Variable FS0 : Fs.Fs.
(* [comment removed for export] *)
Variable E1 : AX2.env.
Variable CS : CAP.acs.
Variable R : bvmap 5 word.
Variable FULL : word -> option byte.
Variable m : Model.
Hypothesis HCS : CXS.cs_ok segs A Lim SINV argH ISP FS0 E1 CS R FULL m.
Hypothesis Hlx : CxOpt.ledger_exact E1 (CAP.a_maps CS).     (* [comment removed for export] *)
Let Hnf : CAP.no_fog (CAP.a_maps CS) = true := CxOpt.ledger_exact_nf _ _ Hlx.
Hypothesis Hres : res_chk segs A = true.
Variable n : int.                       (* [comment removed for export] *)
Variable rho : int -> word.
Variable ALL0 : list fent.              (* [comment removed for export] *)
Hypothesis Hmaps0 : vm_maps (m_vmmaps m) = map (den rho) ALL0.
Hypothesis Htags0 : Forall (fun e => to_Z (fent_tag e) < to_Z n) ALL0.

(* [comment removed for export] *)
Variable rho' : int -> word.
Variable m' : Model.
Variable ALL' : list fent.
Variable ops : list vop.
Variables c' S' fE' : Z.
Local Notation V := (m_vmmaps m).
Local Notation V' := (m_vmmaps m').
Local Notation R0 := (segments_reserved segs).
Hypothesis Hrho : forall t, to_Z t < to_Z n -> rho' t = rho t.
Hypothesis Hmaps' : vm_maps V' = map (den rho') ALL'.
Hypothesis Hna' : vm_noaccess V' = na_apply rho' ops (vm_noaccess V).
Hypothesis Hlz' : m_vm_lazy m' = lz_apply rho' ops (m_vm_lazy m).
Hypothesis Hfacts' :
  vm_reserved V' = R0
  /\ sp_window_lo <= bv_unsigned (vm_init_sp V') <= sp_window_hi
  /\ Forall (fun p => 0 < e_sz p) (vm_maps V')
  /\ Forall (fun p => e_lo p mod page_size = 0 /\ e_sz p mod page_size = 0) (vm_maps V')
  /\ Forall (fun p => 0 < e_lo p /\ e_hi p <= alloc_top V') (vm_maps V')
  /\ Forall (fun p => Forall (e_disj p) R0) (vm_maps V')
  /\ pw_disj (vm_maps V') /\ Z.of_nat (length (vm_maps V')) <= c' /\ live_bytes (vm_maps V') <= S'.
Hypothesis Hwfna' : Forall (fun q => e_hi q <= 2 ^ 64) (vm_noaccess V').
Hypothesis Hwflz' : Forall (fun q => e_hi q <= 2 ^ 64) (m_vm_lazy m').
Hypothesis Hsame : same_but_vm m m'.
Hypothesis Hisp' : vm_init_sp V' = vm_init_sp V.
Hypothesis Hsbrk' : vm_start_brk V' = vm_start_brk V.
Hypothesis Hbrk' : vm_brk V' = vm_brk V.
Hypothesis Hhalt' : m_halted m' = None.
Hypothesis Hlim' : Lim <= vm_limit V'.   (* [comment removed for export] *)
Hypothesis HE' : LazyCfg.eager_used m' <= fE'.
Hypothesis Hops : Forall (op_ok rho' m' ALL') ops.      (* [comment removed for export] *)
Hypothesis HopsR : forall o x p, In o ops -> In p R0 ->
                     e_lo (den rho' (snd o)) <= x < e_hi (den rho' (snd o)) -> ~ (e_lo p <= x < e_hi p).
Hypothesis Hopchk : ops3_chk n ops = true.
(* [comment removed for export] *)
Variable fresh : list fent.
Hypothesis HALL : ALL' = fresh ++ ALL0.

Lemma leaf_atop : alloc_top V' = alloc_top V.
Proof. unfold alloc_top. rewrite Hisp'. reflexivity. Qed.

Lemma leaf_den0 e : In e ALL0 -> den rho' e = den rho e.
Proof.
  intros He. pose proof (proj1 (Forall_forall _ _) Htags0 e He) as Ht. destruct e as [[t off] len].
  cbn [fent_tag fst] in Ht. unfold den, adr. rewrite (Hrho t Ht). reflexivity.
Qed.

Lemma leaf_maps0_in z : CXS.in_ivs z (vm_maps V) = true -> CXS.in_ivs z (vm_maps V') = true.
Proof.
  intros H. apply in_ivs_true in H as (p & Hp & Hz). apply in_ivs_true.
  rewrite Hmaps0 in Hp. apply in_map_iff in Hp as (e & <- & He).
  exists (den rho' e). split; [|rewrite (leaf_den0 e He); exact Hz].
  rewrite Hmaps', HALL. apply in_map. apply in_or_app. right. exact He.
Qed.

(* [comment removed for export] *)
Lemma leaf_seps : CXS.seps (vm_maps V').
Proof.
  destruct Hfacts' as (_ & _ & _ & _ & _ & _ & Hd & _). exact (pw_disj_seps _ Hd).
Qed.

(* [comment removed for export] *)
Lemma off_hull lo hi : lo < hi ->
  (forall x p, In p R0 -> lo <= x < hi -> ~ (e_lo p <= x < e_hi p)) ->
  hi <= CAP.img_lo A \/ CAP.img_hi A <= lo.
Proof.
  intros Hlt Hoff.
  destruct (Z_le_gt_dec hi (CAP.img_lo A)) as [Ha|Ha]; [left; exact Ha|].
  destruct (Z_le_gt_dec (CAP.img_hi A) lo) as [Hb|Hb]; [right; exact Hb|].
  exfalso. set (z := Z.max lo (CAP.img_lo A)). pose proof (res_hull_ne segs A Hres) as Hne.
  destruct (res_cover_ex segs A Hres z ltac:(unfold z; lia)) as (r & Hr & Hz).
  apply (Hoff z r Hr); [unfold z; lia | exact Hz].
Qed.

Lemma leaf_bounds :
  Forall (fun iv => 0 < bv_unsigned (snd iv)
                    /\ bv_unsigned (fst iv) mod 4096 = 0 /\ bv_unsigned (snd iv) mod 4096 = 0
                    /\ (bv_unsigned (fst iv) + bv_unsigned (snd iv) <= CAP.img_lo A \/ CAP.img_hi A <= bv_unsigned (fst iv))
                    /\ bv_unsigned (fst iv) + bv_unsigned (snd iv) <= alloc_top V') (vm_maps V').
Proof.
  destruct Hfacts' as (_ & _ & Hpos & Hal & Htop & HdR & _).
  apply Forall_forall. intros p Hp.
  pose proof (proj1 (Forall_forall _ _) Hpos p Hp) as H1.
  pose proof (proj1 (Forall_forall _ _) Hal p Hp) as [H2 H3].
  pose proof (proj1 (Forall_forall _ _) Htop p Hp) as [H4 H5].
  pose proof (proj1 (Forall_forall _ _) HdR p Hp) as H6.
  unfold e_hi, e_lo, e_sz, page_size in *.
  split; [exact H1|]. split; [exact H2|]. split; [exact H3|]. split; [|exact H5].
  apply off_hull; [lia|]. intros x r Hr Hx Hxr.
  pose proof (proj1 (Forall_forall _ _) H6 r Hr) as Hd. unfold e_disj, e_hi, e_lo, e_sz in *. lia.
Qed.

Lemma leaf_wf : model_ivs_wf m'.
Proof.
  destruct Hfacts' as (_ & Hsp & _ & _ & Htop & _).
  pose proof (alloc_top_lt V') as Hat. unfold two_pow_64 in Hat.
  unfold model_ivs_wf. split; [|split; [|split]].
  - intros q Hq. pose proof (proj1 (Forall_forall _ _) Htop q Hq) as [_ H2].
    unfold iv_wf, BackingAlgebra.B, BackingAlgebra.S. unfold e_hi, e_lo, e_sz in H2. lia.
  - exact (ivs_wf_of_Forall _ Hwfna').
  - exact (ivs_wf_of_Forall _ Hwflz').
  - unfold init_sp_ok. exact (proj1 Hsp).
Qed.

Lemma root_wf_na : ivs_wf (vm_noaccess V).
Proof. exact (proj1 (proj2 (CXS.co_wf _ _ _ _ _ _ _ _ _ _ _ _ HCS))). Qed.
Lemma root_wf_lz : ivs_wf (m_vm_lazy m).
Proof. exact (proj1 (proj2 (proj2 (CXS.co_wf _ _ _ _ _ _ _ _ _ _ _ _ HCS)))). Qed.

Lemma leaf_na_mono z : CXS.in_ivs z (vm_noaccess V') = true -> CXS.in_ivs z (vm_noaccess V) = true.
Proof. rewrite Hna'. exact (na_apply_in rho' ops _ z root_wf_na). Qed.

Lemma leaf_nasub : forall z, CXS.in_ivs z (vm_noaccess V') = true -> CXS.in_ivs z (vm_maps V') = true.
Proof.
  intros z Hz. apply leaf_maps0_in. apply (CXS.co_nasub _ _ _ _ _ _ _ _ _ _ _ _ HCS). exact (leaf_na_mono z Hz).
Qed.

(* [comment removed for export] *)
Variable END : CAP.acs.
Variable XT : list (int * AX2.lin).
Hypothesis Hrho0' : rho' 0%uint63 = Z_to_bv 64 0.
Hypothesis HXT : Forall (fun p => AX2S.eqm (AX2S.lden E1 (snd p)) (bv_unsigned (rho' (fst p)))) XT.
Variable LZ' : list fent.
Hypothesis Hpw' : lazy_pw rho' (m_vm_lazy m') LZ'.

Lemma xt_find_sound t lt : xt_find XT t = Some lt -> AX2S.eqm (AX2S.lden E1 lt) (bv_unsigned (rho' t)).
Proof.
  unfold xt_find. destruct (t =? 0)%uint63 eqn:Et.
  - apply Uint63.eqb_spec in Et. subst t. intros H. injection H as <-. rewrite Hrho0'.
    change (bv_unsigned (Z_to_bv 64 0)) with 0. exists 0. reflexivity.
  - destruct (List.find (fun p => (fst p =? t)%uint63) XT) as [p|] eqn:Ef; [|discriminate].
    intros H. injection H as <-. destruct (List.find_some _ _ Ef) as [Hin Hp]. apply Uint63.eqb_spec in Hp. subst t.
    exact (proj1 (Forall_forall _ _) HXT p Hin).
Qed.

Lemma ent_chkX_den am e : ent_chkX XT am e = true -> CXS.amap_den E1 am = den rho' e.
Proof.
  destruct e as [[t off] len]. unfold ent_chkX.
  destruct (CAP.am_len am) as [l| | | | | | |] eqn:El; try discriminate.
  destruct (xt_find XT t) as [lt|] eqn:Ex; [|discriminate].
  intros Hc. apply andb_prop in Hc as [Hl Hm]. apply Z.eqb_eq in Hl. subst l.
  pose proof (lin_match_sound E1 _ _ _ Hm) as Hq.
  pose proof (AX2S.lin_of_sound E1 (CAP.am_base am)) as Hb. pose proof (xt_find_sound t lt Ex) as Ht.
  unfold CXS.amap_den, den. rewrite El. cbn [AX2.edenot]. f_equal.
  apply bv_eq. unfold adr. rewrite bv_add_unsigned, Z_to_bv_unsigned. unfold bv_wrap.
  change (bv_modulus 64) with (2 ^ 64). rewrite Zplus_mod_idemp_r.
  pose proof (br_u64 (AX2.edenot E1 (CAP.am_base am))) as Hu.
  destruct Hq as [q1 Hq1]. destruct Hb as [q2 Hb2]. destruct Ht as [q3 Ht3]. unfold AX2S.uE in *.
  apply (Z.mod_unique_pos _ _ (q2 - q3 - q1)); [exact Hu|]. lia.
Qed.

Lemma ents_chkX_den : forall ms es, ents_chkX XT ms es = true -> map (CXS.amap_den E1) ms = map (den rho') es.
Proof.
  induction ms as [|am ms IH]; intros [|e es] Hc; cbn [ents_chkX] in Hc; try discriminate; [reflexivity|].
  apply andb_prop in Hc as [H1 H2]. cbn [map]. rewrite (ent_chkX_den am e H1), (IH es H2). reflexivity.
Qed.

Lemma ents_chkX_pair : forall ms es am e, ents_chkX XT ms es = true -> In (am, e) (combine ms es) -> ent_chkX XT am e = true.
Proof.
  induction ms as [|am0 ms IH]; intros [|e0 es] am e Hc Hin; cbn [ents_chkX combine] in *; try discriminate; try (destruct Hin; fail).
  apply andb_prop in Hc as [H1 H2]. destruct Hin as [Heq|Hin]; [injection Heq as <- <-; exact H1 | exact (IH es am e H2 Hin)].
Qed.

Definition kind_is_none (am : CAP.amap) : bool :=
  match CAP.am_kind am with CAP.KNONE | CAP.KNONELAZY => true | _ => false end.

(* [comment removed for export] *)
Definition kind3_chk (p : CAP.amap * fent) : bool :=
  let '(am, e) := p in
  match CAP.am_kind am with
  | CAP.KRW => true
  | CAP.KNONE | CAP.KNONELAZY => amap_mem am (CAP.a_maps CS)
  | CAP.KRWLAZY => fent_mem e LZ' && (amap_mem am (CAP.a_maps CS) || fent_mem e fresh)
  | _ => false
  end.

Definition ledger3_chk : bool :=
  CAP.no_fog (CAP.a_maps END) && ents_chkX XT (CAP.a_maps END) ALL'
  && forallb kind3_chk (combine (CAP.a_maps END) ALL').

Hypothesis Hled : ledger3_chk = true.

Lemma led3_parts : CAP.no_fog (CAP.a_maps END) = true /\ ents_chkX XT (CAP.a_maps END) ALL' = true
  /\ forallb kind3_chk (combine (CAP.a_maps END) ALL') = true.
Proof. unfold ledger3_chk in Hled. apply andb_prop in Hled as [H H3]. apply andb_prop in H as [H1 H2]. tauto. Qed.

Lemma leaf_maps_eq : vm_maps V' = map (CXS.amap_den E1) (CAP.a_maps END).
Proof. destruct led3_parts as (_ & H2 & _). rewrite Hmaps'. symmetry. exact (ents_chkX_den _ _ H2). Qed.

Lemma leaf_maps : CXS.maps_match E1 (CAP.a_maps END) (vm_maps V').
Proof. destruct led3_parts as (H1 & _). exact (maps_match_exact_rev E1 _ _ H1 leaf_maps_eq). Qed.

Lemma leaf_holes ylo l : Forall (CXS.hole_ok E1 ylo l) (CAP.a_maps END).
Proof.
  destruct led3_parts as (H1 & _). apply Forall_forall. intros am Ham Hh. exfalso.
  unfold CAP.no_fog in H1. rewrite forallb_forall in H1. specialize (H1 am Ham). apply negb_true_iff in H1.
  unfold CAP.is_hole in Hh. unfold CAP.is_fog, CAP.is_tok_kind in H1. destruct (CAP.am_kind am); discriminate.
Qed.

(* [comment removed for export] *)
Lemma leaf_pair am : In am (CAP.a_maps END) ->
  exists e, In (am, e) (combine (CAP.a_maps END) ALL') /\ In e ALL' /\ CXS.amap_den E1 am = den rho' e.
Proof.
  destruct led3_parts as (_ & H2 & _). intros Ham.
  assert (Hlen : length (CAP.a_maps END) = length ALL').
  { pose proof (f_equal (@length _) (ents_chkX_den _ _ H2)) as Hl. rewrite !length_map in Hl. exact Hl. }
  destruct (In_nth_error _ _ Ham) as [i Hi].
  destruct (nth_error ALL' i) as [e|] eqn:He.
  2:{ apply nth_error_None in He. pose proof (proj1 (nth_error_Some (CAP.a_maps END) i) ltac:(rewrite Hi; discriminate)). lia. }
  exists e. assert (Hc : In (am, e) (combine (CAP.a_maps END) ALL')).
  { clear - Hi He. revert i ALL' Hi He. induction (CAP.a_maps END) as [|a l IH]; intros [|i] [|e0 es] Hi He; cbn in *; try discriminate.
    - injection Hi as <-. injection He as <-. left. reflexivity.
    - right. exact (IH i es Hi He). }
  split; [exact Hc|]. split; [exact (nth_error_In _ _ He)|]. exact (ent_chkX_den am e (ents_chkX_pair _ _ am e H2 Hc)).
Qed.

(* [comment removed for export] *)
Lemma start_entry am : In am (CAP.a_maps CS) ->
  exists e0, In e0 ALL0 /\ In e0 ALL' /\ den rho' e0 = CXS.amap_den E1 am /\ In (CXS.amap_den E1 am) (vm_maps V).
Proof.
  intros Ham.
  assert (Hin : In (CXS.amap_den E1 am) (vm_maps V)).
  { rewrite (CxOpt.maps_exact_D1 E1 _ _ Hlx (CXS.co_maps _ _ _ _ _ _ _ _ _ _ _ _ HCS)). apply in_map. exact Ham. }
  pose proof Hin as Hin2. rewrite Hmaps0 in Hin2. apply in_map_iff in Hin2 as (e0 & Ed & He0).
  exists e0. split; [exact He0|]. split; [rewrite HALL; apply in_or_app; right; exact He0|].
  split; [rewrite (leaf_den0 e0 He0); exact Ed | exact Hin].
Qed.

(* [comment removed for export] *)
Lemma op_nonempty o : In o ops -> e_lo (den rho' (snd o)) < e_hi (den rho' (snd o)).
Proof.
  intros Ho. destruct (ops3_get n ops o Hopchk Ho) as (Hl & _). unfold e_hi. rewrite (e_sz_den rho' (snd o)). lia.
Qed.

Lemma cut_misses e0 o : In e0 ALL0 -> In o ops -> is_cut o = true -> is_commit o = false ->
  e_lo (den rho' (snd o)) < e_hi (den rho' (snd o)) /\ e_disj (den rho' e0) (den rho' (snd o)).
Proof.
  intros He0 Ho Hcut Hnc. split; [exact (op_nonempty o Ho)|].
  destruct (ops3_get n ops o Hopchk Ho) as (_ & _ & Ht). specialize (Ht Hnc).
  pose proof (proj1 (Forall_forall _ _) Hops o Ho) as Hok. unfold op_ok in Hok. cbv zeta in Hok.
  pose proof (proj1 (Forall_forall _ _) Htags0 e0 He0) as Ht0.
  assert (Hin' : In e0 ALL') by (rewrite HALL; apply in_or_app; right; exact He0).
  unfold is_cut in Hcut. unfold is_commit in Hnc.
  destruct (fst o); try discriminate. apply (proj1 Hok e0 Hin'). cbv beta in Ht0. lia.
Qed.

(* [comment removed for export] *)
Variable ORD' : list (int * int * Z).       (* [comment removed for export] *)
Hypothesis Hord' : Forall (fun o : int * int * Z => bv_unsigned (rho' (fst (fst o))) + snd o <= bv_unsigned (rho' (snd (fst o)))) ORD'.

Definition ord_has' (ta tb : int) (P : Z -> bool) : bool :=
  existsb (fun o : int * int * Z => (fst (fst o) =? ta)%uint63 && (snd (fst o) =? tb)%uint63 && P (snd o)) ORD'.

Lemma ord_has'_sound ta tb P : ord_has' ta tb P = true ->
  exists dd, P dd = true /\ bv_unsigned (rho' ta) + dd <= bv_unsigned (rho' tb).
Proof.
  unfold ord_has'. intros H. apply existsb_exists in H as ([[a b] dd] & Hin & Hc). cbn [fst snd] in Hc.
  apply andb_prop in Hc as [Hc HP]. apply andb_prop in Hc as [Ha Hb]. apply Uint63.eqb_spec in Ha, Hb. subst a b.
  exists dd. split; [exact HP|]. exact (proj1 (Forall_forall _ _) Hord' _ Hin).
Qed.

(* [comment removed for export] *)
Definition covers (e c : fent) : bool :=
  let '(te, oe, le) := e in
  let '(t, off, len) := c in
  ((te =? t)%uint63 && (to_Z oe <=? to_Z off) && (to_Z off + to_Z len <=? to_Z oe + to_Z le))
  || ((oe =? 0)%uint63 && ord_has' te t (fun d1 => 0 <=? d1 + to_Z off)
      && ord_has' t te (fun d2 => to_Z off + to_Z len - d2 <=? to_Z le)).

Lemma adr_mod (r : int -> word) t y : bv_unsigned (adr r t y) = (bv_unsigned (r t) + y) mod 2 ^ 64.
Proof.
  unfold adr. rewrite bv_add_unsigned, Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
  rewrite Zplus_mod_idemp_r. reflexivity.
Qed.

Lemma covers_sound e c : In e ALL' -> covers e c = true ->
  e_lo (den rho' e) <= e_lo (den rho' c) /\ e_hi (den rho' c) <= e_hi (den rho' e).
Proof.
  intros He Hc. destruct e as [[te oe] le]. destruct c as [[t off] len].
  assert (Hp : In (den rho' (te, oe, le)) (vm_maps V')) by (rewrite Hmaps'; apply in_map; exact He).
  destruct Hfacts' as (_ & _ & _ & _ & Htop & _).
  pose proof (proj1 (Forall_forall _ _) Htop _ Hp) as [_ Hhi]. pose proof (alloc_top_lt V') as Hat. unfold two_pow_64 in Hat.
  unfold e_hi in *. rewrite !e_sz_den in *. cbn [snd] in *. unfold e_lo in *. cbn [den fst] in *.
  pose proof (i63_range oe) as Hoe. pose proof (i63_range off) as Hoff. pose proof (i63_range len) as Hlen. pose proof (i63_range le) as Hle.
  pose proof (br_u64 (adr rho' te (to_Z oe))) as Hue.
  unfold covers in Hc. apply orb_prop in Hc as [Hc|Hc].
  - apply andb_prop in Hc as [Hc H3]. apply andb_prop in Hc as [Ht H2]. apply Uint63.eqb_spec in Ht. subst te.
    apply Z.leb_le in H2, H3.
    assert (Ea : bv_unsigned (adr rho' t (to_Z off)) = bv_unsigned (adr rho' t (to_Z oe)) + (to_Z off - to_Z oe)).
    { rewrite !adr_mod. replace (bv_unsigned (rho' t) + to_Z off) with ((bv_unsigned (rho' t) + to_Z oe) + (to_Z off - to_Z oe)) by lia.
      rewrite <- Zplus_mod_idemp_l. apply Z.mod_small. rewrite adr_mod in Hhi, Hue. lia. }
    lia.
  - apply andb_prop in Hc as [Hc H3]. apply andb_prop in Hc as [Ho H2]. apply Uint63.eqb_spec in Ho. subst oe.
    destruct (ord_has'_sound _ _ _ H2) as (d1 & P1 & F1). destruct (ord_has'_sound _ _ _ H3) as (d2 & P2 & F2).
    apply Z.leb_le in P1, P2. change (to_Z 0%uint63) with 0 in *.
    assert (E0 : bv_unsigned (adr rho' te 0) = bv_unsigned (rho' te)).
    { rewrite adr_mod, Z.add_0_r. apply Z.mod_small. exact (br_u64 (rho' te)). }
    rewrite E0 in *. pose proof (br_u64 (rho' te)) as Hu1.
    rewrite (adr_unsigned_z rho' t (to_Z off)) by lia. lia.
Qed.

Definition is_krw (am : CAP.amap) : bool := match CAP.am_kind am with CAP.KRW => true | _ => false end.

Definition commit3_chk : bool :=
  forallb (fun o : vop =>
     if is_commit o then
       existsb (fun p : CAP.amap * fent => is_krw (fst p) && (to_Z (fent_tag (snd p)) <? to_Z n) && covers (snd p) (snd o))
               (combine (CAP.a_maps END) ALL')
     else true) ops.
Hypothesis Hcommit : commit3_chk = true.

Lemma nth_error_combine {T U : Type} : forall (l1 : list T) (l2 : list U) j a b,
  nth_error (combine l1 l2) j = Some (a, b) -> nth_error l1 j = Some a /\ nth_error l2 j = Some b.
Proof.
  induction l1 as [|x l1 IH]; intros [|y l2] j a b H; try (destruct j; discriminate).
  destruct j as [|j]; cbn [combine nth_error] in *; [injection H as <- <-; split; reflexivity | exact (IH l2 j a b H)].
Qed.

Lemma commit_cover o : In o ops -> is_commit o = true ->
  exists j am e, nth_error (CAP.a_maps END) j = Some am /\ nth_error ALL' j = Some e /\ CAP.am_kind am = CAP.KRW
                 /\ to_Z (fent_tag e) < to_Z n
                 /\ e_lo (den rho' e) <= e_lo (den rho' (snd o)) /\ e_hi (den rho' (snd o)) <= e_hi (den rho' e).
Proof.
  intros Ho Hcm. unfold commit3_chk in Hcommit. rewrite forallb_forall in Hcommit. pose proof (Hcommit o Ho) as H1.
  rewrite Hcm in H1. apply existsb_exists in H1 as ([am e] & Hin & Hc). cbn [fst snd] in Hc.
  apply andb_prop in Hc as [Hc Hcov]. apply andb_prop in Hc as [Hk Ht]. apply Z.ltb_lt in Ht.
  destruct (In_nth_error _ _ Hin) as [j Hj]. destruct (nth_error_combine _ _ _ _ _ Hj) as [J1 J2].
  exists j, am, e. split; [exact J1|]. split; [exact J2|].
  split; [unfold is_krw in Hk; destruct (CAP.am_kind am); try discriminate; reflexivity|]. split; [exact Ht|].
  exact (covers_sound e (snd o) (nth_error_In _ _ J2) Hcov).
Qed.

(* [comment removed for export] *)
Lemma commit_misses am e o : In (am, e) (combine (CAP.a_maps END) ALL') -> CAP.am_kind am <> CAP.KRW ->
  In o ops -> is_commit o = true -> e_disj (den rho' e) (den rho' (snd o)).
Proof.
  intros Hpair Hk Ho Hcm. destruct (commit_cover o Ho Hcm) as (j & amc & ec & J1 & J2 & Kc & _ & C1 & C2).
  destruct (In_nth_error _ _ Hpair) as [i Hi]. destruct (nth_error_combine _ _ _ _ _ Hi) as [I1 I2].
  assert (Hij : i <> j) by (intros ->; rewrite I1 in J1; injection J1 as <-; contradiction).
  destruct Hfacts' as (_ & _ & _ & _ & _ & _ & Hpw & _). rewrite Hmaps' in Hpw.
  pose proof (pw_disj_nth _ _ _ _ _ Hpw Hij (map_nth_error (den rho') _ _ I2) (map_nth_error (den rho') _ _ J2)) as Hd.
  unfold e_disj in *. lia.
Qed.

Lemma leaf_none : Forall (fun am => CAP.am_kind am = CAP.KNONE \/ CAP.am_kind am = CAP.KNONELAZY ->
                          In (CXS.amap_den E1 am) (vm_noaccess V')) (CAP.a_maps END).
Proof.
  destruct led3_parts as (_ & _ & H3). rewrite forallb_forall in H3.
  apply Forall_forall. intros am Ham Hk. destruct (leaf_pair am Ham) as (e & Hpair & _ & _).
  pose proof (H3 _ Hpair) as Hc. unfold kind3_chk in Hc.
  assert (Hst : In am (CAP.a_maps CS)) by (destruct Hk as [Hk|Hk]; rewrite Hk in Hc; exact (amap_mem_In _ _ Hc)).
  destruct (start_entry am Hst) as (e0 & He0 & _ & Ed & Hin).
  pose proof (proj1 (Forall_forall _ _) (CXS.co_none _ _ _ _ _ _ _ _ _ _ _ _ HCS) am Hst Hk) as Hna0.
  pose proof (proj1 (Forall_forall _ _) (CXS.co_bounds _ _ _ _ _ _ _ _ _ _ _ _ HCS) _ Hin) as (Hsz & _).
  rewrite Hna'. apply na_apply_keeps; [exact Hna0 | unfold e_sz; exact Hsz |].
  intros o Ho Hcut. split; [exact (op_nonempty o Ho)|].
  destruct (is_commit o) eqn:Ecm.
  - destruct (leaf_pair am Ham) as (e' & Hpair' & _ & Ed').
    assert (Hnk : CAP.am_kind am <> CAP.KRW) by (destruct Hk as [Hk|Hk]; rewrite Hk; discriminate).
    pose proof (commit_misses am e' o Hpair' Hnk Ho Ecm) as Hd. rewrite <- Ed' in Hd. unfold e_disj in Hd. exact Hd.
  - destruct (cut_misses e0 o He0 Ho Hcut Ecm) as [_ Hd]. rewrite Ed in Hd. unfold e_disj in Hd. exact Hd.
Qed.

Lemma leaf_kinds : Forall (fun am => CAP.am_kind am = CAP.KRWLAZY ->
    forall a : word, bv_unsigned (AX2.edenot E1 (CAP.am_base am)) <= bv_unsigned a
                     < bv_unsigned (AX2.edenot E1 (CAP.am_base am)) + bv_unsigned (AX2.edenot E1 (CAP.am_len am)) ->
      CXS.in_ivs (bv_unsigned a) (vm_noaccess V') = false
      /\ page_in_ranges (page_base a) (m_vm_lazy m') = true) (CAP.a_maps END).
Proof.
  destruct led3_parts as (_ & _ & H3). rewrite forallb_forall in H3.
  apply Forall_forall. intros am Ham Hk a Ha. destruct (leaf_pair am Ham) as (e & Hpair & HeA & Ed).
  pose proof (H3 _ Hpair) as Hc. unfold kind3_chk in Hc. rewrite Hk in Hc. apply andb_prop in Hc as [Hlz Hsrc].
  assert (Hin' : In (CXS.amap_den E1 am) (vm_maps V')) by (rewrite leaf_maps_eq; apply in_map; exact Ham).
  destruct Hfacts' as (_ & _ & _ & Hal & _ & _ & Hpw & _).
  pose proof (proj1 (Forall_forall _ _) Hal _ Hin') as [Hal1 Hal2]. unfold e_lo, e_sz, page_size, CXS.amap_den in Hal1, Hal2. cbn [fst snd] in Hal1, Hal2.
  split.
  - apply not_true_is_false. intros Hna.
    pose proof (CXS.co_nasub _ _ _ _ _ _ _ _ _ _ _ _ HCS _ (leaf_na_mono _ Hna)) as Hm0.
    apply orb_prop in Hsrc as [Hst|Hfr].
    + apply amap_mem_In in Hst.
      pose proof (proj1 (Forall_forall _ _) (CXS.co_kinds _ _ _ _ _ _ _ _ _ _ _ _ HCS) am Hst Hk a Ha) as [Hn0 _].
      rewrite (leaf_na_mono _ Hna) in Hn0. discriminate.
    + apply fent_mem_In in Hfr. apply in_ivs_true in Hm0 as (p0 & Hp0 & Hz0).
      rewrite Hmaps0 in Hp0. apply in_map_iff in Hp0 as (e0 & <- & He0).
      rewrite Hmaps', HALL, map_app in Hpw.
      pose proof (pw_disj_app _ _ (den rho' e) (den rho' e0) Hpw (in_map _ _ _ Hfr) (in_map _ _ _ He0)) as Hd.
      rewrite (leaf_den0 e0 He0) in Hd. rewrite <- Ed in Hd.
      unfold e_disj, e_hi, e_lo, e_sz, CXS.amap_den in Hd, Hz0. cbn [fst snd] in Hd. lia.
  - apply fent_mem_In in Hlz.
    destruct (page_base_inside a _ _ Hal1 ltac:(rewrite Z.add_mod, Hal1, Hal2 by lia; reflexivity) Ha) as (P1 & P2 & P3).
    apply (Hpw' e (page_base a) Hlz P1); rewrite <- Ed; unfold e_hi, e_lo, e_sz, CXS.amap_den; cbn [fst snd]; lia.
Qed.

(* [comment removed for export] *)
Lemma leaf_lazyb :
  Forall (fun iv => (bv_unsigned (fst iv) + bv_unsigned (snd iv) <= CAP.img_lo A \/ CAP.img_hi A <= bv_unsigned (fst iv))
                    /\ bv_unsigned (fst iv) + bv_unsigned (snd iv) <= alloc_top V') (m_vm_lazy m').
Proof.
  rewrite Hlz'. apply lz_apply_forall.
  - intros q r [Hh Ht] H1 H2. unfold e_hi, e_lo, e_sz in *. split; lia.
  - exact root_wf_lz.
  - rewrite leaf_atop. exact (CXS.co_lazyb _ _ _ _ _ _ _ _ _ _ _ _ HCS).
  - intros o Ho Hl.
    pose proof (op_nonempty o Ho) as Hne.
    pose proof (proj1 (Forall_forall _ _) Hops o Ho) as Hok. unfold op_ok in Hok. cbv zeta in Hok.
    unfold is_lazyop in Hl. destruct (fst o); try discriminate. destruct Hok as (_ & _ & Htop).
    pose proof (alloc_top_lt V') as Hat. unfold two_pow_64 in Hat.
    split; [|lia]. split; [|exact Htop].
    apply (off_hull _ _ Hne). intros x r Hr Hx. exact (HopsR o x r Ho Hr Hx).
Qed.

(* [comment removed for export] *)
Definition afd_eqb (x y : CAP.afd) : bool :=
  match x, y with
  | CAP.FdStd, CAP.FdStd | CAP.FdDir, CAP.FdDir => true
  | CAP.FdFile k l o, CAP.FdFile k' l' o' => Nat.eqb k k' && AX2.expr_eqb l l' && AX2.expr_eqb o o'
  | _, _ => false
  end.
Lemma afd_eqb_eq x y : afd_eqb x y = true -> x = y.
Proof.
  destruct x, y; cbn [afd_eqb]; try discriminate; try reflexivity. intros H.
  apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2]. apply Nat.eqb_eq in H1.
  apply AX2S.expr_eqb_eq in H2, H3. subst. reflexivity.
Qed.

Definition same3_chk : bool :=
  AX2.expr_eqb (CAP.a_brk END) (CAP.a_brk CS) && afd_eqb (CAP.a_fd END) (CAP.a_fd CS)
  && Bool.eqb (CAP.a_tidset END) (CAP.a_tidset CS)
  && (live_bytes R0 + S' <=? CAP.a_totsz END) && (fE' <=? CAP.a_eager END).
Hypothesis Hsame3 : same3_chk = true.

Lemma same3_parts : CAP.a_brk END = CAP.a_brk CS /\ CAP.a_fd END = CAP.a_fd CS /\ CAP.a_tidset END = CAP.a_tidset CS
  /\ live_bytes R0 + S' <= CAP.a_totsz END /\ fE' <= CAP.a_eager END.
Proof.
  unfold same3_chk in Hsame3. apply andb_prop in Hsame3 as [H H5]. apply andb_prop in H as [H H4].
  apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2].
  apply AX2S.expr_eqb_eq in H1. apply afd_eqb_eq in H2. apply Bool.eqb_prop in H3. apply Z.leb_le in H4, H5. tauto.
Qed.

Lemma leaf_totsz : CXS.sum_sizes (vm_reserved V' ++ vm_maps V') <= CAP.a_totsz END.
Proof.
  destruct same3_parts as (_ & _ & _ & H4 & _). destruct Hfacts' as (Hr & _ & _ & _ & _ & _ & _ & _ & HS).
  rewrite sum_sizes_live, live_bytes_app, Hr. lia.
Qed.

Lemma leaf_eager : AsanAcct.eager_used m' <= CAP.a_eager END.
Proof. destruct same3_parts as (_ & _ & _ & _ & H5). unfold LazyCfg.eager_used in HE'. unfold AsanAcct.eager_used. lia. Qed.

Lemma leaf_brk : vm_brk V' = AX2.edenot E1 (CAP.a_brk END).
Proof. destruct same3_parts as (H1 & _). rewrite H1, Hbrk'. exact (CXS.co_brk _ _ _ _ _ _ _ _ _ _ _ _ HCS). Qed.

Lemma leaf_sbrk : bv_unsigned (vm_start_brk V') <= bv_unsigned (vm_brk V').
Proof. rewrite Hsbrk', Hbrk'. exact (CXS.co_sbrk _ _ _ _ _ _ _ _ _ _ _ _ HCS). Qed.

Lemma leaf_isp : bv_unsigned (vm_init_sp V') = ISP /\ CXS.uE E1 CAP.e_spw = ISP.
Proof. rewrite Hisp'. exact (CXS.co_isp _ _ _ _ _ _ _ _ _ _ _ _ HCS). Qed.

Lemma leaf_top : CAP.CEIL <= alloc_top V' <= CAP.TOPMAX.
Proof. rewrite leaf_atop. exact (CXS.co_top _ _ _ _ _ _ _ _ _ _ _ _ HCS). Qed.

Lemma leaf_fs : m_fs m' = FS0.
Proof. destruct Hsame as (_ & _ & Hf & _). unfold m_fs. rewrite Hf. exact (CXS.co_fs _ _ _ _ _ _ _ _ _ _ _ _ HCS). Qed.

Lemma leaf_fds : CXS.fds_ok E1 (CAP.a_fd END) m'.
Proof.
  destruct same3_parts as (_ & H2 & _). rewrite H2. destruct Hsame as (Hfd & _ & Hf & _).
  pose proof (CXS.co_fds _ _ _ _ _ _ _ _ _ _ _ _ HCS) as H0. unfold CXS.fds_ok, m_fds, m_fs in *. rewrite Hfd, Hf. exact H0.
Qed.

Lemma leaf_tid : CAP.a_tidset END = false -> m_tid m' = None.
Proof.
  destruct same3_parts as (_ & _ & H3 & _). rewrite H3. intros Ht. destruct Hsame as (_ & _ & _ & Hp & _).
  unfold m_tid. rewrite Hp. exact (CXS.co_tid _ _ _ _ _ _ _ _ _ _ _ _ HCS Ht).
Qed.

(* [comment removed for export] *)
Local Notation OLD := (CAP.a_vis CS ++ CAP.a_ghost CS).
Local Notation NEWL := (CAP.a_vis END ++ CAP.a_ghost END).
Local Notation AB l := (AsanAcct.A_bytes (flat_map (CXS.allow1 A E1) l)).

Lemma allow1_nonneg p : 0 <= AsanAcct.A_bytes (CXS.allow1 A E1 p).
Proof.
  unfold CXS.allow1. cbn [AsanAcct.A_bytes fst snd].
  pose proof (CXS.pagedown_le (CXS.uE E1 (fst p))). pose proof (CXS.pageup_ge (CXS.uE E1 (fst p) + CXS.uE E1 (snd p))).
  pose proof (CXS.pagedown_le (CXS.sh_lo A E1 p)). pose proof (CXS.pageup_ge (CXS.sh_hi A E1 p)).
  pose proof (br_u64 (AX2.edenot E1 (snd p))) as Hn. pose proof (br_u64 (AX2.edenot E1 (fst p))) as Hb.
  unfold CXS.sh_lo, CXS.sh_hi, CXS.uE in *.
  assert (bv_unsigned (AX2.edenot E1 (fst p)) / 8 <= (bv_unsigned (AX2.edenot E1 (fst p)) + bv_unsigned (AX2.edenot E1 (snd p))) / 8)
    by (apply Z.div_le_mono; lia).
  lia.
Qed.

Lemma AB_cons p l : AB (p :: l) = AsanAcct.A_bytes (CXS.allow1 A E1 p) + AB l.
Proof. cbn [flat_map]. apply CXS.A_bytes_app. Qed.

Lemma AB_nonneg : forall l, 0 <= AB l.
Proof. induction l as [|p l IH]; [cbn; lia|]. rewrite AB_cons. pose proof (allow1_nonneg p). lia. Qed.

Lemma rem1_sum : forall old p old', rem1 p old = Some old' -> AB old = AsanAcct.A_bytes (CXS.allow1 A E1 p) + AB old'.
Proof.
  induction old as [|q r IH]; intros p old' H; cbn [rem1] in H; [discriminate|].
  destruct (CAP.pair_eqb p q) eqn:Epq.
  - injection H as <-. rewrite (pair_eqb_eq _ _ Epq). apply AB_cons.
  - destruct (rem1 p r) as [r'|] eqn:Er; [|discriminate]. cbn [option_map] in H. injection H as <-.
    rewrite !AB_cons, (IH p r' Er). lia.
Qed.

Lemma ab_split_le : forall L old, AB L <= AB old + AB (ab_split L old).
Proof.
  induction L as [|p r IH]; intros old; cbn [ab_split]; [pose proof (AB_nonneg old); cbn; lia|].
  destruct (rem1 p old) as [old'|] eqn:Er.
  - rewrite AB_cons, (rem1_sum old p old' Er). specialize (IH old'). lia.
  - rewrite !AB_cons. specialize (IH old). lia.
Qed.

Lemma new_bnd_sound p b : new_bnd p = Some b -> AsanAcct.A_bytes (CXS.allow1 A E1 p) <= b.
Proof.
  unfold new_bnd. destruct (snd p) as [l| | | | | | |] eqn:En; try discriminate.
  destruct ((0 <=? l) && (l <? 2 ^ 62)) eqn:El; [|discriminate]. intros H. injection H as <-.
  apply andb_prop in El as [H0 H1]. apply Z.leb_le in H0. apply Z.ltb_lt in H1.
  unfold CXS.allow1. cbn [AsanAcct.A_bytes fst snd]. unfold CXS.sh_lo, CXS.sh_hi, CXS.uE. rewrite En. cbn [AX2.edenot].
  rewrite (br_lit_small l) by lia. pose proof (br_u64 (AX2.edenot E1 (fst p))) as Hb.
  set (u := bv_unsigned (AX2.edenot E1 (fst p))) in *. set (K := CAP.shadow_off A).
  unfold CXS.pagedown, CXS.pageup. clear - H0 H1 Hb. Z.div_mod_to_equations. lia.
Qed.

Lemma new_bound_sound : forall l b, new_bound l = Some b -> AB l <= b.
Proof.
  induction l as [|p r IH]; intros b H; cbn [new_bound] in H; [injection H as <-; cbn; lia|].
  destruct (new_bnd p) as [a|] eqn:Ea; [|discriminate]. destruct (new_bound r) as [b'|] eqn:Eb; [|discriminate].
  injection H as <-. rewrite AB_cons. pose proof (new_bnd_sound p a Ea). specialize (IH b' eq_refl). lia.
Qed.

Definition abytes3_chk : bool :=
  match new_bound (ab_split NEWL OLD) with
  | Some b => CAP.a_abytes CS + b <=? CAP.a_abytes END
  | None => false
  end.

Lemma leaf_abytes : abytes3_chk = true -> AsanAcct.A_bytes (CXS.allowA A E1 END) <= CAP.a_abytes END.
Proof.
  unfold abytes3_chk. destruct (new_bound (ab_split NEWL OLD)) as [b|] eqn:Eb; [|discriminate]. intros H. apply Z.leb_le in H.
  pose proof (CXS.co_abytes _ _ _ _ _ _ _ _ _ _ _ _ HCS) as H0. unfold CXS.allowA in *.
  pose proof (ab_split_le NEWL OLD) as H1. pose proof (new_bound_sound _ b Eb) as H2. lia.
Qed.

(* [comment removed for export] *)
Variable AL' : list fent.               (* [comment removed for export] *)
Variable SHP : list (int * int).        (* [comment removed for export] *)
Hypothesis Hshp : Forall (fun q => bv_unsigned (rho' (fst q)) = bv_unsigned (rho' (snd q)) / 8 + to_Z shadow_K) SHP.
Hypothesis HshK : CAP.shadow_off A = to_Z shadow_K.
(* [comment removed for export] *)
Variable XA : list fent.
Variable PB : list (int * (Z * Z * Z)).    (* [comment removed for export] *)
Hypothesis HPB : Forall (fun q : int * (Z * Z * Z) =>
                           let '(clo, chi, bnd) := snd q in
                           clo <= bv_unsigned (rho' (fst q)) <= chi /\ bv_unsigned (rho' (fst q)) + bnd < 2 ^ 63) PB.
Hypothesis Hpi' : LazyCfg.page_inv (map (denA rho') AL' ++ map (denA rho') XA ++ CXS.allowA A E1 CS) m'.
Hypothesis Hmat' : Forall (fun p => page_in_ranges p (m_vm_lazy m') = true) (m_vm_materialized m').

Definition xt_match (b : AX2.expr) (t : int) : bool :=
  match xt_find XT t with Some lt => lin_match (AX2.lin_of b) lt 0 | None => false end.

Lemma xt_match_sound b t : xt_match b t = true -> CXS.uE E1 b = bv_unsigned (rho' t).
Proof.
  unfold xt_match. destruct (xt_find XT t) as [lt|] eqn:Ex; [|discriminate]. intros Hm.
  pose proof (lin_match_sound E1 _ _ _ Hm) as Hq. pose proof (AX2S.lin_of_sound E1 b) as Hb.
  pose proof (xt_find_sound t lt Ex) as Ht. unfold CXS.uE.
  apply br_eqm_small; [|apply br_u64|apply br_u64].
  destruct Hq as [q1 Hq1]. destruct Hb as [q2 Hb2]. destruct Ht as [q3 Ht3]. unfold AX2S.uE in *.
  exists (q1 + q3 - q2). lia.
Qed.

Definition allow_ent_chk (f : fent) : bool :=
  let '(t, off, len) := f in
  (off =? 0)%uint63
  && existsb (fun p : AX2.expr * AX2.expr =>
                match snd p with
                | AX2.ELit l =>
                    (0 <=? l) && (l <? 2 ^ 62)
                    && (((to_Z len <=? l) && xt_match (fst p) t)
                        || existsb (fun q : int * int => (fst q =? t)%uint63 && xt_match (fst p) (snd q) && (8 * to_Z len <=? l)) SHP)
                | _ => false
                end) NEWL.

(* [comment removed for export] *)
Definition xa_q_chk (ts : int) (off len : Z) (p : AX2.expr * AX2.expr) : bool :=
  match snd p with
  | AX2.ELit l =>
      (0 <=? l) && (l <? 2 ^ 62)
      && existsb (fun q : int * int =>
           (* [comment removed for export] *)
           if (fst q =? ts)%uint63 then
              match xt_find XT (snd q) with
              | Some lt =>
                  let c := AX2.snorm (fst (AX2.lin_of (fst p)) - fst lt) in
                  lin_match (AX2.lin_of (fst p)) lt c && (0 <=? c) && (c <=? 8 * off) && (8 * (off + len) <=? c + l)
                  && existsb (fun b : int * (Z * Z * Z) =>
                                let '(clo, chi, bnd) := snd b in
                                (fst b =? snd q)%uint63 && (c + l <=? bnd)
                                && ((chi + c + l <=? span_lo) || (span_hi <=? clo + c)) && (chi + c + l <=? 2 ^ 47)) PB
              | None => false
              end
           else false) SHP
  | _ => false
  end.

Definition xa_ent_chk (f : fent) : bool :=
  let '(ts, off, len) := f in existsb (xa_q_chk ts (to_Z off) (to_Z len)) (CAP.a_vis END).

Lemma xa_q_sound ts off len p : 0 <= off -> 0 <= len -> xa_q_chk ts off len p = true ->
  CXS.sh_lo A E1 p <= bv_unsigned (rho' ts) + off /\ bv_unsigned (rho' ts) + off + len <= CXS.sh_hi A E1 p
  /\ (forall z, CXS.sh_lo A E1 p <= z < CXS.sh_hi A E1 p -> in_shadow z).
Proof.
  intros Hoff Hlen Hc. unfold xa_q_chk in Hc. destruct (snd p) as [l| | | | | | |] eqn:El; try discriminate.
  apply andb_prop in Hc as [Hl Hex]. apply andb_prop in Hl as [Hl0 Hl1]. apply Z.leb_le in Hl0. apply Z.ltb_lt in Hl1.
  apply existsb_exists in Hex as ([ts' tp] & Hq & Hqc). cbn [fst snd] in Hqc.
  destruct (ts' =? ts)%uint63 eqn:Hts; [|discriminate]. apply Uint63.eqb_spec in Hts. subst ts'.
  destruct (xt_find XT tp) as [lt|] eqn:Ex; [|discriminate]. cbv zeta in Hqc.
  set (c := AX2.snorm (fst (AX2.lin_of (fst p)) - fst lt)) in *.
  apply andb_prop in Hqc as [Hqc Hpb]. apply andb_prop in Hqc as [Hqc H8h]. apply andb_prop in Hqc as [Hqc H8l].
  apply andb_prop in Hqc as [Hm Hc0]. apply Z.leb_le in Hc0, H8l, H8h.
  apply existsb_exists in Hpb as ([tb [[clo chi] B]] & HB & Hbc). cbn [fst snd] in Hbc.
  apply andb_prop in Hbc as [Hbc H47]. apply andb_prop in Hbc as [Hbc Hside]. apply andb_prop in Hbc as [Htb HcB].
  apply Uint63.eqb_spec in Htb. subst tb. apply Z.leb_le in HcB, H47.
  pose proof (proj1 (Forall_forall _ _) HPB _ HB) as Hbnd. cbn [fst snd] in Hbnd. destruct Hbnd as [Hcc Hbnd].
  pose proof (proj1 (Forall_forall _ _) Hshp _ Hq) as Esh. cbn [fst snd] in Esh.
  pose proof (br_u64 (rho' tp)) as Hup.
  assert (Eub : CXS.uE E1 (fst p) = bv_unsigned (rho' tp) + c).
  { unfold CXS.uE. apply br_eqm_small; [|apply br_u64|lia].
    pose proof (lin_match_sound E1 _ _ _ Hm) as [q1 Hq1]. pose proof (AX2S.lin_of_sound E1 (fst p)) as [q2 Hq2].
    pose proof (xt_find_sound tp lt Ex) as [q3 Hq3]. unfold AX2S.uE in *. exists (q1 + q3 - q2). lia. }
  assert (Eun : CXS.uE E1 (snd p) = l) by (unfold CXS.uE; rewrite El; cbn [AX2.edenot]; apply br_lit_small; lia).
  unfold CXS.sh_lo, CXS.sh_hi. rewrite HshK, Eub, Eun, Esh.
  set (u := bv_unsigned (rho' tp)) in *.
  assert (H1 : (u + c) / 8 <= u / 8 + off).
  { replace (u / 8 + off) with ((u + off * 8) / 8) by (rewrite Z.div_add by lia; reflexivity). apply Z.div_le_mono; lia. }
  assert (H2 : u / 8 + (off + len) <= (u + c + l) / 8).
  { replace (u / 8 + (off + len)) with ((u + (off + len) * 8) / 8) by (rewrite Z.div_add by lia; reflexivity). apply Z.div_le_mono; lia. }
  split; [lia|]. split; [lia|].
  intros z Hz. unfold in_shadow, lsh_lo, lsh_hi, hsh_lo, hsh_hi. change (to_Z shadow_K) with 2147450880 in *.
  unfold span_lo, span_hi in Hside.
  apply orb_prop in Hside as [Hs|Hs]; apply Z.leb_le in Hs; [left | right]; clear - Hz Hs Hcc H47 Hup Hc0 Hl0; Z.div_mod_to_equations; lia.
Qed.

Definition allow3_chk : bool :=
  forallb (fun p => pair_mem p NEWL) OLD && forallb allow_ent_chk AL' && forallb xa_ent_chk XA
  && (CAP.a_eager END + CAP.a_abytes END <=? Lim).

Lemma allowed_iv_incl (Aset : list (Z * Z)) (lo hi lo' hi' : Z) (P : word) :
  In (lo', hi') Aset -> lo' <= lo -> hi <= hi' ->
  (lo <=? bv_unsigned P) && (bv_unsigned P + page_size <=? hi) = true -> AsanAcct.page_allowedb Aset P = true.
Proof.
  intros Hin H1 H2 Hp. apply andb_prop in Hp as [P1 P2]. apply Z.leb_le in P1, P2.
  unfold AsanAcct.page_allowedb. apply existsb_exists. exists (lo', hi'). split; [exact Hin|]. cbn [fst snd].
  apply andb_true_iff. split; apply Z.leb_le; lia.
Qed.

Lemma leaf_minv : abytes3_chk = true -> allow3_chk = true -> AsanAcct.MInv (CXS.allowA A E1 END) m'.
Proof.
  intros Hab Hc. unfold allow3_chk in Hc. apply andb_prop in Hc as [Hc HL]. apply andb_prop in Hc as [Hc Hxa]. apply andb_prop in Hc as [Hold Hnew].
  apply Z.leb_le in HL. destruct Hpi' as [Hnd Hal Hallow Hbud]. constructor.
  - exact Hnd.
  - intros P HP. exact (proj1 (Forall_forall _ _) Hal P HP).
  - intros P HP. pose proof (proj1 (Forall_forall _ _) Hallow P HP) as Ha. cbv beta in Ha.
    unfold LazyCfg.page_allowedb in Ha. apply existsb_exists in Ha as (iv & Hiv & Hp).
    apply in_app_iff in Hiv as [Hiv|Hiv].
    + (* [comment removed for export] *)
      apply in_map_iff in Hiv as ([[t off] len] & <- & Hf). rewrite forallb_forall in Hnew.
      pose proof (Hnew _ Hf) as Hck. unfold allow_ent_chk in Hck. apply andb_prop in Hck as [Hoff Hex].
      apply Uint63.eqb_spec in Hoff. subst off. apply existsb_exists in Hex as (p & Hp' & Hpc).
      destruct (snd p) as [l| | | | | | |] eqn:En; try discriminate.
      apply andb_prop in Hpc as [Hl Hways]. apply andb_prop in Hl as [Hl0 Hl1]. apply Z.leb_le in Hl0. apply Z.ltb_lt in Hl1.
      pose proof (i63_range len) as Hlen. unfold denA in Hp. cbn [fst snd] in Hp. change (to_Z 0) with 0 in Hp. rewrite Z.add_0_r in Hp.
      assert (Hun : CXS.uE E1 (snd p) = l) by (unfold CXS.uE; rewrite En; cbn [AX2.edenot]; apply br_lit_small; lia).
      apply orb_prop in Hways as [Hpl|Hsh].
      * apply andb_prop in Hpl as [Hle Hm]. apply Z.leb_le in Hle. pose proof (xt_match_sound _ _ Hm) as Eu.
        apply (allowed_iv_incl _ (pg_dn (bv_unsigned (rho' t))) (pg_upZ (bv_unsigned (rho' t) + to_Z len))
                 (CXS.pagedown (CXS.uE E1 (fst p))) (CXS.pageup (CXS.uE E1 (fst p) + CXS.uE E1 (snd p))) P); [| | |exact Hp].
        -- unfold CXS.allowA. apply in_flat_map. exists p. split; [exact Hp'|]. left. reflexivity.
        -- rewrite Eu. unfold pg_dn, CXS.pagedown. apply Z.mul_le_mono_nonneg_r; [lia|]. apply Z.div_le_mono; lia.
        -- rewrite Eu, Hun. unfold pg_upZ, CXS.pageup. apply Z.mul_le_mono_nonneg_r; [lia|]. apply Z.div_le_mono; lia.
      * apply existsb_exists in Hsh as ([ts tp] & Hq & Hqc). cbn [fst snd] in Hqc.
        apply andb_prop in Hqc as [Hqc H8]. apply andb_prop in Hqc as [Hts Hm]. apply Uint63.eqb_spec in Hts. subst ts.
        apply Z.leb_le in H8. pose proof (xt_match_sound _ _ Hm) as Eu.
        pose proof (proj1 (Forall_forall _ _) Hshp _ Hq) as Esh. cbn [fst snd] in Esh.
        apply (allowed_iv_incl _ (pg_dn (bv_unsigned (rho' t))) (pg_upZ (bv_unsigned (rho' t) + to_Z len))
                 (CXS.pagedown (CXS.sh_lo A E1 p)) (CXS.pageup (CXS.sh_hi A E1 p)) P); [| | |exact Hp].
        -- unfold CXS.allowA. apply in_flat_map. exists p. split; [exact Hp'|]. right. left. reflexivity.
        -- unfold CXS.sh_lo. rewrite Eu, HshK, Esh. unfold pg_dn, CXS.pagedown.
           apply Z.mul_le_mono_nonneg_r; [lia|]. apply Z.div_le_mono; lia.
        -- unfold CXS.sh_hi. rewrite Eu, Hun, HshK, Esh. unfold pg_upZ, CXS.pageup.
           apply Z.mul_le_mono_nonneg_r; [lia|]. apply Z.div_le_mono; [lia|].
           assert (bv_unsigned (rho' tp) / 8 + to_Z len <= (bv_unsigned (rho' tp) + l) / 8).
           { replace (bv_unsigned (rho' tp) / 8 + to_Z len) with ((bv_unsigned (rho' tp) + to_Z len * 8) / 8) by (rewrite Z.div_add by lia; reflexivity).
             apply Z.div_le_mono; lia. }
           lia.
    + apply in_app_iff in Hiv as [Hiv|Hiv].
      { (* [comment removed for export] *)
        apply in_map_iff in Hiv as ([[ts off] len] & <- & Hf). rewrite forallb_forall in Hxa.
        pose proof (Hxa _ Hf) as Hck. unfold xa_ent_chk in Hck. apply existsb_exists in Hck as (p & Hp' & Hpc).
        pose proof (i63_range off) as Hoff. pose proof (i63_range len) as Hlen.
        destruct (xa_q_sound ts (to_Z off) (to_Z len) p ltac:(lia) ltac:(lia) Hpc) as (S1 & S2 & S3).
        unfold denA in Hp. cbn [fst snd] in Hp.
        apply (allowed_iv_incl _ (pg_dn (bv_unsigned (rho' ts) + to_Z off)) (pg_upZ (bv_unsigned (rho' ts) + to_Z off + to_Z len))
                 (CXS.pagedown (CXS.sh_lo A E1 p)) (CXS.pageup (CXS.sh_hi A E1 p)) P); [| | |exact Hp].
        - unfold CXS.allowA. apply in_flat_map. exists p. split; [apply in_or_app; left; exact Hp'|]. right. left. reflexivity.
        - unfold pg_dn, CXS.pagedown. apply Z.mul_le_mono_nonneg_r; [lia|]. apply Z.div_le_mono; lia.
        - unfold pg_upZ, CXS.pageup. apply Z.mul_le_mono_nonneg_r; [lia|]. apply Z.div_le_mono; lia. }
      (* [comment removed for export] *)
      unfold CXS.allowA in Hiv. apply in_flat_map in Hiv as (p & Hp0 & Hiv).
      rewrite forallb_forall in Hold. pose proof (pair_mem_In _ _ (Hold p Hp0)) as Hp1.
      unfold AsanAcct.page_allowedb. apply existsb_exists. exists iv. split; [|exact Hp].
      unfold CXS.allowA. apply in_flat_map. exists p. split; [exact Hp1 | exact Hiv].
  - intros P HP. exact (proj1 (Forall_forall _ _) Hmat' P HP).
  - pose proof leaf_eager as H1. pose proof (leaf_abytes Hab) as H2. pose proof Hlim'. lia.
Qed.

(* [comment removed for export] *)
Local Notation kn := (CAP.kn CS).
Local Notation Mr := (CXS.Mr A argH E1 CS m FULL).

Lemma leaf_kn : AX2S.know_ok segs E1 Mr kn.
Proof. exact (CXS.co_know _ _ _ _ _ _ _ _ _ _ _ _ HCS). Qed.

Lemma page_base_range (a : word) :
  bv_unsigned (page_base a) <= bv_unsigned a < bv_unsigned (page_base a) + page_size.
Proof.
  pose proof (br_u64 a) as Hu. unfold page_base, page_base_of, page_size. rewrite Z_to_bv_unsigned.
  rewrite bv_wrap_small by (change (bv_modulus 64) with (2 ^ 64); clear - Hu; Z.div_mod_to_equations; lia).
  clear. Z.div_mod_to_equations. lia.
Qed.

Lemma op_hi64 o : In o ops -> is_lazyop o = true -> e_hi (den rho' (snd o)) <= 2 ^ 64.
Proof.
  intros Ho Hl. pose proof (proj1 (Forall_forall _ _) Hops o Ho) as Hok. unfold op_ok in Hok. cbv zeta in Hok.
  unfold is_lazyop in Hl. pose proof (alloc_top_lt V') as Hat. unfold two_pow_64 in Hat.
  destruct (fst o); try discriminate. destruct Hok as (_ & _ & Htop). lia.
Qed.

(* [comment removed for export] *)
Lemma root_entry_off z o e0 : In e0 ALL0 -> e_lo (den rho e0) <= z < e_hi (den rho e0) -> In o ops ->
  match fst o with OpShadow | OpCommit => False | _ => True end ->
  ~ (e_lo (den rho' (snd o)) <= z < e_hi (den rho' (snd o))).
Proof.
  intros He0 Hz Ho Hk Hin.
  destruct (ops3_get n ops o Hopchk Ho) as (_ & _ & Ht).
  assert (Hnc : is_commit o = false) by (unfold is_commit; destruct (fst o); try reflexivity; contradiction).
  specialize (Ht Hnc).
  pose proof (proj1 (Forall_forall _ _) Hops o Ho) as Hok. unfold op_ok in Hok. cbv zeta in Hok.
  pose proof (proj1 (Forall_forall _ _) Htags0 e0 He0) as Ht0. cbv beta in Ht0.
  assert (Hin' : In e0 ALL') by (rewrite HALL; apply in_or_app; right; exact He0).
  rewrite <- (leaf_den0 e0 He0) in Hz.
  assert (Hd : e_disj (den rho' e0) (den rho' (snd o))).
  { destruct (fst o); try contradiction; try discriminate;
      [apply (proj1 Hok e0 Hin') | apply (proj1 (proj2 Hok) e0 Hin') | apply (proj1 (proj2 Hok) e0 Hin')]; lia. }
  unfold e_disj in Hd. lia.
Qed.

Definition avis_keep_chk : bool := forallb (fun p => pair_mem p (CAP.a_vis END)) (CAP.a_vis CS).

Lemma leaf_allow_mono : avis_keep_chk = true -> forall z, CXS.in_allow A E1 CS z = true -> CXS.in_allow A E1 END z = true.
Proof.
  unfold avis_keep_chk. intros Hc z Hz. rewrite forallb_forall in Hc.
  unfold CXS.in_allow, CXS.in_vis, CXS.in_sh in *. apply orb_prop in Hz as [Hz|Hz]; apply orb_true_iff; [left | right];
    apply existsb_exists in Hz as (p & Hp & Hpz); apply existsb_exists; exists p; (split; [exact (pair_mem_In _ _ (Hc p Hp)) | exact Hpz]).
Qed.

Theorem leaf_vis_mono : avis_keep_chk = true ->
  forall a : word, CXS.vis A E1 CS m a = true -> CXS.vis A E1 END m' a = true.
Proof.
  intros Hk a Hv. unfold CXS.vis in *. cbv zeta in *. rewrite leaf_atop.
  apply orb_prop in Hv as [Hv|Hv]; [rewrite Hv; reflexivity|].
  apply andb_prop in Hv as [Hv Hal]. apply andb_prop in Hv as [Hm Hn]. apply negb_true_iff in Hn.
  apply orb_true_iff. right. apply andb_true_iff. split; [apply andb_true_iff; split|].
  - exact (leaf_maps0_in _ Hm).
  - apply negb_true_iff. apply not_true_is_false. intros Hna. rewrite (leaf_na_mono _ Hna) in Hn. discriminate.
  - apply orb_prop in Hal as [Hnl|Hal]; [|apply orb_true_iff; right; exact (leaf_allow_mono Hk _ Hal)].
    apply orb_true_iff. left. apply negb_true_iff in Hnl. apply negb_true_iff. apply not_true_is_false. intros Hl'.
    rewrite Hlz' in Hl'. destruct (lz_apply_page rho' ops _ (page_base a) root_wf_lz op_hi64 Hl') as [Hl0 | (o & Ho & Hlo & H1 & H2)].
    + rewrite Hl0 in Hnl. discriminate.
    + apply in_ivs_true in Hm as (p0 & Hp0 & Hz0). rewrite Hmaps0 in Hp0. apply in_map_iff in Hp0 as (e0 & <- & He0).
      pose proof (page_base_range a) as Hpb.
      apply (root_entry_off (bv_unsigned a) o e0 He0 Hz0 Ho); [unfold is_lazyop in Hlo; destruct (fst o); try discriminate; exact I | lia].
Qed.

Theorem leaf_hid_mono : avis_keep_chk = true ->
  forall a : word, CXS.hid A argH E1 END m' a = true -> CXS.hid A argH E1 CS m a = true.
Proof.
  intros Hk a Hh. unfold CXS.hid in *. apply orb_prop in Hh as [Hh|Hh]; [rewrite Hh; reflexivity|].
  apply orb_true_iff. right. apply negb_true_iff in Hh. apply negb_true_iff. apply not_true_is_false. intros Hv.
  rewrite (leaf_vis_mono Hk a Hv) in Hh. discriminate.
Qed.

(* [comment removed for export] *)
Definition avis_in3 (p : AX2.expr * AX2.expr) : bool :=
  CAP.xinsideJ kn (fst p) 0 (snd p) (AX2.ELit 0) (CAP.img_lo A) (AX2.ELit (CAP.img_hi A - CAP.img_lo A))
  || ((12 <=? AX2.ealign kn (fst p)) && CAP.xinsideJ kn (fst p) 0 (snd p) CAP.e_spw (- 8392703) (AX2.ELit (2 ^ 40)))
  || existsb (fun am => CAP.xinsideJ kn (fst p) 0 (snd p) (CAP.am_base am) 0 (CAP.am_len am)) (CAP.a_maps CS).

(* [comment removed for export] *)
Definition ph_parents_chk : bool :=
  forallb (fun o : vop =>
     match fst o with
     | OpShadow => let '(ts, _, _) := snd o in
                   existsb (fun e : fent => let '(g, off, _) := e in (g =? ts - 1)%uint63 && (off =? 0)%uint63) ALL'
     | _ => true
     end) ops.
Definition avis_ph (p : AX2.expr * AX2.expr) : bool :=
  match fst p, snd p with
  | AX2.ELit 0, AX2.ELit l => (0 <=? l) && (l <=? 4096) && ph_parents_chk
  | _, _ => false
  end.
Definition avis_in (p : AX2.expr * AX2.expr) : bool := avis_in3 p || avis_ph p.

Definition span_kinds_chk : bool :=
  forallb (fun am => negb (is_span_lit am)
                     || match CAP.am_kind am with CAP.KRWLAZY | CAP.KNONE | CAP.KNONELAZY => true | _ => false end) (CAP.a_maps CS).

Definition shadow_parent_chk : bool :=
  forallb (fun o : vop =>
     match fst o with
     | OpShadow =>
         let '(ts, off, sl) := snd o in
         (off =? 0)%uint63
         && existsb (fun o' : vop =>
              match fst o' with
              | OpGrant | OpLazy =>
                  let '(g, off', lg) := snd o' in
                  (g =? ts - 1)%uint63 && (off' =? 0)%uint63 && (8 * to_Z sl <=? to_Z lg) && (to_Z lg mod 4096 =? 0)
              | _ => false
              end) ops
     | _ => true
     end) ops.

Definition avis3_chk : bool :=
  forallb (fun p => zapart CS p && (3 <=? AX2.ealign kn (fst p)) && avis_in p) (CAP.a_vis CS)
  && span_kinds_chk && span_chk CS && (CAP.img_hi A <=? span_lo) && (0 <=? CAP.img_lo A)
  && shadow_parent_chk && (CAP.shadow_off A =? to_Z shadow_K).

Lemma den0 t len : e_lo (den rho' (t, 0%uint63, len)) = bv_unsigned (rho' t)
                   /\ e_hi (den rho' (t, 0%uint63, len)) = bv_unsigned (rho' t) + to_Z len.
Proof.
  unfold e_hi. rewrite (e_sz_den rho' (t, 0%uint63, len)). unfold e_lo. cbn [den fst snd].
  change (to_Z 0) with 0. rewrite adr_0. split; reflexivity.
Qed.

Theorem leaf_untouched : avis3_chk = true ->
  forall x : word, CXS.vis A E1 CS m x = true -> ~ touched rho' (List.filter (fun o => negb (is_commit o)) ops) (bv_unsigned x).
Proof.
  unfold avis3_chk. intros Hc x Hv (o & Ho & Hin). apply filter_In in Ho as [Ho Hncm].
  apply andb_prop in Hc as [Hc HK]. apply andb_prop in Hc as [Hc Hsp]. apply andb_prop in Hc as [Hc Hil].
  apply andb_prop in Hc as [Hc Hih]. apply andb_prop in Hc as [Hc Hsc]. apply andb_prop in Hc as [Hav Hsk].
  apply Z.eqb_eq in HK. apply Z.leb_le in Hih, Hil.
  set (z := bv_unsigned x) in *. pose proof (res_hull_ne segs A Hres) as Hne.
  destruct (CXS.co_top _ _ _ _ _ _ _ _ _ _ _ _ HCS) as [Htop1 _]. unfold CAP.CEIL in Htop1.
  destruct (CXS.co_isp _ _ _ _ _ _ _ _ _ _ _ _ HCS) as [Eisp Espw].
  assert (Hat : alloc_top V = ISP - 8388608) by (unfold alloc_top, stack_max_size; rewrite Eisp; lia).
  pose proof (proj1 (Forall_forall _ _) Hops o Ho) as Hok. unfold op_ok in Hok. cbv zeta in Hok.
  destruct (ops3_get n ops o Hopchk Ho) as (Hlen & _ & _).
  assert (Hcm : match fst o with OpCommit => false | _ => true end = true)
    by (unfold is_commit in Hncm; destruct (fst o); try reflexivity; discriminate Hncm).
  (* [comment removed for export] *)
  assert (Hplain : forall (o1 : vop) (y : Z), In o1 ops -> match fst o1 with OpShadow | OpCommit => False | _ => True end ->
            e_lo (den rho' (snd o1)) <= y < e_hi (den rho' (snd o1)) ->
            ~ (CAP.img_lo A <= y < CAP.img_hi A) /\ y < alloc_top V).
  { intros o1 y Ho1 Hk1 Hy. split.
    - intros Hh. destruct (res_cover_ex segs A Hres y Hh) as (r & Hr & Hyr). exact (HopsR o1 y r Ho1 Hr Hy Hyr).
    - pose proof (proj1 (Forall_forall _ _) Hops o1 Ho1) as Hok1. unfold op_ok in Hok1. cbv zeta in Hok1.
      rewrite <- leaf_atop. destruct (fst o1); try contradiction; [destruct Hok1 as (_ & Ht) | destruct Hok1 as (_ & _ & Ht) | destruct Hok1 as (_ & _ & Ht)]; lia. }
  unfold CXS.vis in Hv. cbv zeta in Hv. fold z in Hv.
  destruct (fst o) eqn:Ek; try discriminate.
  1,2,3: (assert (Hk : match fst o with OpShadow | OpCommit => False | _ => True end) by (rewrite Ek; exact I);
          destruct (Hplain o z Ho Hk Hin) as [Hnh Hlt];
          apply orb_prop in Hv as [Hv|Hv];
          [ apply orb_prop in Hv as [Hv|Hv];
            [ unfold CXS.in_hull in Hv; apply andb_prop in Hv as [V1 V2]; apply Z.leb_le in V1; apply Z.ltb_lt in V2; lia
            | apply Z.leb_le in Hv; lia ]
          | apply andb_prop in Hv as [Hv _]; apply andb_prop in Hv as [Hm _];
            apply in_ivs_true in Hm as (p0 & Hp0 & Hz0); rewrite Hmaps0 in Hp0; apply in_map_iff in Hp0 as (e0 & <- & He0);
            apply (root_entry_off z o e0 He0 Hz0 Ho); [rewrite Ek; exact I | exact Hin] ]).
  (* [comment removed for export] *)
  destruct Hok as (Htag & Ebase & Hspan). pose proof (Hspan z Hin) as Hzs.
  apply orb_prop in Hv as [Hv|Hv].
  { apply orb_prop in Hv as [Hv|Hv].
    - unfold CXS.in_hull in Hv. apply andb_prop in Hv as [V1 V2]. apply Z.ltb_lt in V2. lia.
    - apply Z.leb_le in Hv. unfold span_hi in Hzs. lia. }
  apply andb_prop in Hv as [Hv Hal]. apply andb_prop in Hv as [Hm Hn]. apply negb_true_iff in Hn.
  (* [comment removed for export] *)
  destruct (span_cover_sound _ _ _ _ Hsc z Hzs) as (q & Hq & Hzq).
  destruct (span_lit_in segs A Lim SINV argH ISP FS0 E1 CS R FULL m HCS Hlx q Hq) as (j & am & Hj & Esl & Hvj & Elo & Ehi).
  pose proof (nth_error_In _ _ Hj) as Ham.
  unfold span_kinds_chk in Hsk. rewrite forallb_forall in Hsk. pose proof (Hsk am Ham) as Hkd.
  unfold is_span_lit in Hkd. rewrite Esl in Hkd. cbn [negb orb] in Hkd.
  assert (Hzam : bv_unsigned (AX2.edenot E1 (CAP.am_base am)) <= z
                 < bv_unsigned (AX2.edenot E1 (CAP.am_base am)) + bv_unsigned (AX2.edenot E1 (CAP.am_len am))).
  { unfold e_hi, e_lo, e_sz, CXS.amap_den in Elo, Ehi. cbn [fst snd] in Elo, Ehi. lia. }
  assert (Hlz0 : page_in_ranges (page_base x) (m_vm_lazy m) = true).
  { destruct (CAP.am_kind am) eqn:Ekd; try discriminate.
    - exact (proj2 (proj1 (Forall_forall _ _) (CXS.co_kinds _ _ _ _ _ _ _ _ _ _ _ _ HCS) am Ham Ekd x Hzam)).
    - exfalso. pose proof (proj1 (Forall_forall _ _) (CXS.co_none _ _ _ _ _ _ _ _ _ _ _ _ HCS) am Ham (or_introl Ekd)) as Hin0.
      assert (Hna0 : CXS.in_ivs z (vm_noaccess V) = true) by (apply in_ivs_true; exists (CXS.amap_den E1 am); split; [exact Hin0 | lia]).
      rewrite Hna0 in Hn. discriminate.
    - exfalso. pose proof (proj1 (Forall_forall _ _) (CXS.co_none _ _ _ _ _ _ _ _ _ _ _ _ HCS) am Ham (or_intror Ekd)) as Hin0.
      assert (Hna0 : CXS.in_ivs z (vm_noaccess V) = true) by (apply in_ivs_true; exists (CXS.amap_den E1 am); split; [exact Hin0 | lia]).
      rewrite Hna0 in Hn. discriminate. }
  rewrite Hlz0 in Hal. cbn [negb orb] in Hal. unfold CXS.in_allow in Hal. rewrite forallb_forall in Hav.
  apply orb_prop in Hal as [Hal|Hal].
  { unfold CXS.in_vis in Hal. apply existsb_exists in Hal as (p & Hp & Hpz). pose proof (Hav p Hp) as Hpc.
    apply andb_prop in Hpc as [Hpc _]. apply andb_prop in Hpc as [Hza _].
    apply andb_prop in Hpz as [I1 I2]. apply Z.leb_le in I1. apply Z.ltb_lt in I2.
    exact (zapart_span segs A Lim SINV argH ISP FS0 E1 CS R FULL m HCS p z Hza Hzs (conj I1 I2)). }
  unfold CXS.in_sh in Hal. apply existsb_exists in Hal as (p & Hp & Hpz). pose proof (Hav p Hp) as Hpc.
  apply andb_prop in Hpc as [Hpc Hain]. apply andb_prop in Hpc as [_ Hal8]. apply Z.leb_le in Hal8.
  apply andb_prop in Hpz as [I1 I2]. apply Z.leb_le in I1. apply Z.ltb_lt in I2.
  unfold CXS.sh_lo in I1. unfold CXS.sh_hi in I2. rewrite HK in I1, I2. unfold CXS.uE in I1, I2.
  set (ub := bv_unsigned (AX2.edenot E1 (fst p))) in *. set (un := bv_unsigned (AX2.edenot E1 (snd p))) in *.
  pose proof (br_u64 (AX2.edenot E1 (fst p))) as Hub. fold ub in Hub.
  pose proof (br_u64 (AX2.edenot E1 (snd p))) as Hun. fold un in Hun.
  destruct (AX2S.ealign_sound segs E1 Mr kn (fst p) leaf_kn) as [_ Hdiv]. fold ub in Hdiv.
  destruct (div8_facts ub un _ ltac:(lia) ltac:(lia) Hal8 Hdiv) as [Hm8 Hsplit]. rewrite Hsplit in I2.
  unfold avis_in in Hain. apply orb_prop in Hain as [Hain|Hph].
  2:{ (* [comment removed for export] *)
      unfold avis_ph in Hph. destruct (fst p) as [zb| | | | | | |] eqn:Efp; try discriminate Hph.
      destruct zb; try discriminate Hph. destruct (snd p) as [l| | | | | | |] eqn:Esp; try discriminate Hph.
      apply andb_prop in Hph as [Hph Hpp]. apply andb_prop in Hph as [Hl0 Hl1]. apply Z.leb_le in Hl0, Hl1.
      assert (Eub : ub = 0) by (unfold ub; cbn [AX2.edenot]; reflexivity).
      assert (Eun : un = l) by (unfold un; cbn [AX2.edenot]; apply br_lit_small; lia).
      unfold ph_parents_chk in Hpp. rewrite forallb_forall in Hpp. pose proof (Hpp o Ho) as Hpo. rewrite Ek in Hpo.
      unfold shadow_parent_chk in Hsp. rewrite forallb_forall in Hsp. pose proof (Hsp o Ho) as Hpar. rewrite Ek in Hpar.
      destruct (snd o) as [[ts off] sl] eqn:Eo. apply andb_prop in Hpar as [Hoff _]. apply Uint63.eqb_spec in Hoff. subst off.
      apply existsb_exists in Hpo as ([[g off2] len2] & He2 & Hgc). apply andb_prop in Hgc as [Hg2 Ho2].
      apply Uint63.eqb_spec in Hg2, Ho2. subst g off2. cbn [fent_tag fst] in Ebase.
      assert (Hin2 : In (den rho' ((ts - 1)%uint63, 0%uint63, len2)) (vm_maps V')) by (rewrite Hmaps'; apply in_map; exact He2).
      destruct Hfacts' as (_ & _ & _ & Hpg & Htop2 & _).
      pose proof (proj1 (Forall_forall _ _) Htop2 _ Hin2) as [Hlo2 _]. pose proof (proj1 (Forall_forall _ _) Hpg _ Hin2) as [Hal2 _].
      destruct (den0 (ts - 1)%uint63 len2) as [Dlo2 _]. rewrite Dlo2 in Hlo2, Hal2. unfold page_size in Hal2.
      destruct (den0 ts sl) as [Dlo _]. rewrite Dlo in Hin. change (to_Z shadow_K) with 2147450880 in *.
      clear - Hin Ebase Hlo2 Hal2 I2 Eub Eun Hl1. subst ub un. Z.div_mod_to_equations. lia. }
  (* [comment removed for export] *)
  unfold shadow_parent_chk in Hsp. rewrite forallb_forall in Hsp. pose proof (Hsp o Ho) as Hpar. rewrite Ek in Hpar.
  destruct (snd o) as [[ts off] sl] eqn:Eo. apply andb_prop in Hpar as [Hoff Hpar]. apply Uint63.eqb_spec in Hoff. subst off.
  apply existsb_exists in Hpar as (o' & Ho' & Hpc'). cbn [fent_tag fst] in Ebase, Htag.
  destruct (den0 ts sl) as [Dlo Dhi]. rewrite Dlo, Dhi in Hin.
  destruct (fst o') eqn:Ek'; try discriminate.
  all: destruct (snd o') as [[g off'] lg] eqn:Eo'; apply andb_prop in Hpc' as [Hpc' Hl4]; apply andb_prop in Hpc' as [Hpc' Hl8];
    apply andb_prop in Hpc' as [Hg Hoff']; apply Uint63.eqb_spec in Hg, Hoff'; subst g off'; apply Z.leb_le in Hl8; apply Z.eqb_eq in Hl4;
    pose proof (proj1 (Forall_forall _ _) Hops o' Ho') as Hok'; unfold op_ok in Hok'; cbv zeta in Hok'; rewrite Ek', Eo' in Hok';
    cbn [fent_tag fst] in Hok'; destruct Hok' as (Hg4 & _ & Htopg);
    destruct (den0 (ts - 1)%uint63 lg) as [Glo Ghi]; rewrite Ghi in Htopg;
    set (rg := bv_unsigned (rho' (ts - 1)%uint63)) in *;
    set (y := 8 * (z - to_Z shadow_K));
    assert (Hyg : e_lo (den rho' (snd o')) <= y < e_hi (den rho' (snd o'))) by
      (rewrite Eo', Glo, Ghi; fold rg; unfold y; clear - Hin Ebase Hg4 Hl8; Z.div_mod_to_equations; lia);
    assert (Hyp : ub <= y < ub + un) by (unfold y; clear - I1 I2 Hm8 Hub Hun; Z.div_mod_to_equations; lia);
    assert (Hk' : match fst o' with OpShadow | OpCommit => False | _ => True end) by (rewrite Ek'; exact I);
    destruct (Hplain o' y Ho' Hk' Hyg) as [Hnh Hlt];
    unfold avis_in3 in Hain; apply orb_prop in Hain as [Hain|Hent]; [apply orb_prop in Hain as [Hhull|Htopc]|].
  all: try (destruct (CXS.xinsideJ_sound segs E1 Mr kn _ _ _ _ _ _ leaf_kn Hhull) as [X1 X2];
            unfold AX2S.estart, AX2S.elenZ in X1, X2; cbn [AX2.a_base AX2.a_off AX2.edenot] in X1, X2;
            change (bv_unsigned (Z_to_bv 64 0)) with 0 in X1, X2; fold ub in X1, X2; fold un in X2;
            rewrite (br_lit_small (CAP.img_hi A - CAP.img_lo A)) in X2 by (unfold span_lo in Hih; lia); lia).
  all: try (apply andb_prop in Htopc as [Hal12 Hx]; apply Z.leb_le in Hal12;
            destruct (CXS.xinsideJ_sound segs E1 Mr kn _ _ _ _ _ _ leaf_kn Hx) as [X1 _];
            unfold AX2S.estart in X1; cbn [AX2.a_base AX2.a_off] in X1; fold ub in X1;
            change (bv_unsigned (AX2.edenot E1 CAP.e_spw)) with (CXS.uE E1 CAP.e_spw) in X1; rewrite Espw in X1;
            assert (Hub12 : ub mod 4096 = 0) by
              (destruct Hdiv as [qq Hqq]; rewrite Hqq;
               replace (AX2.ealign kn (fst p)) with ((AX2.ealign kn (fst p) - 12) + 12) by lia;
               rewrite Z.pow_add_r by lia; rewrite Z.mul_assoc; apply Z.mod_mul; lia);
            rewrite Eo', Glo, Ghi in Hyg; fold rg in Hyg; rewrite leaf_atop in Htopg;
            clear - Hyg Hyp Htopg Hat X1 Hub12 Hg4 Hl4 Hlt; Z.div_mod_to_equations; lia).
  all: apply existsb_exists in Hent as (am0 & Ham0 & Hx);
       destruct (CXS.xinsideJ_sound segs E1 Mr kn _ _ _ _ _ _ leaf_kn Hx) as [X1 X2];
       unfold AX2S.estart, AX2S.elenZ in X1, X2; cbn [AX2.a_base AX2.a_off] in X1, X2; fold ub in X1, X2; fold un in X2;
       destruct (start_entry am0 Ham0) as (e0 & He0 & _ & Ed & _);
       apply (root_entry_off y o' e0 He0); [ | exact Ho' | rewrite Ek'; exact I | exact Hyg];
       rewrite <- (leaf_den0 e0 He0), Ed; unfold e_hi, e_lo, e_sz, CXS.amap_den; cbn [fst snd]; lia.
Qed.

(* [comment removed for export] *)
Variable IM : fimage.
Variables M0 M1 : itrie region.
Variable FULL' : word -> option byte.
Variable EX' : list fent.
Variable TT : list (int * AX2.expr).
Hypothesis SEGS_in_hull : forall a : word, CXS.in_hull A (bv_unsigned a) = false -> find_segment segs (bv_unsigned a) 1 = None.
Hypothesis argH_high : forall E (a : word), argH E a = true -> CAP.CEIL <= bv_unsigned a /\ ISP <= bv_unsigned a.
Hypothesis Hrho_tt : forall t, rho t = AX2.edenot E1 (BrRev.tte TT t).
Hypothesis Hfr' : forall x : word, ~ touched rho' ops (bv_unsigned x) ->
                    (~ claimed_wr IM rho M0 x \/ ~ cell_expl rho' M1 x) -> FULL' x = FULL x.
(* [comment removed for export] *)
Definition xain (z : Z) : bool :=
  existsb (fun e : fent => let '(t, o, l) := e in
             (bv_unsigned (rho' t) + to_Z o <=? z) && (z <? bv_unsigned (rho' t) + to_Z o + to_Z l)) XA.
Hypothesis Hcw : forall x, claimed_wr IM rho M0 x -> CXS.hid A argH E1 CS m x = false \/ xain (bv_unsigned x) = true.
Hypothesis HShZ' : forall x : word, in_shadow (bv_unsigned x) -> no_region rho' M1 (bv_unsigned x) ->
                     ~ exempted rho' EX' (bv_unsigned x) ->
                     rview segs FULL' x = Some (Z_to_bv 8 0) /\ wview segs FULL' x <> None.
Hypothesis HM1 : forall t rg, iget t M1 = Some rg -> region_ok rho' t rg.
Hypothesis Hspok' : forall t rg, iget t M1 = Some rg -> span_ok R0 rho' M1 t rg.
Hypothesis Hexcov' : lazy_cov ALL' EX'.

Definition exb (z : Z) : bool :=
  existsb (fun e => (e_lo (den rho' e) <? 8 * (z - to_Z shadow_K) + 8) && (8 * (z - to_Z shadow_K) <? e_hi (den rho' e))) EX'.

(* [comment removed for export] *)
Lemma xa_in_allow : forallb xa_ent_chk XA = true -> forall z, xain z = true -> CXS.in_allow A E1 END z = true.
Proof.
  intros Hc z Hz. unfold xain in Hz. apply existsb_exists in Hz as ([[ts off] len] & Hf & Hzc).
  apply andb_prop in Hzc as [Z1 Z2]. apply Z.leb_le in Z1. apply Z.ltb_lt in Z2.
  rewrite forallb_forall in Hc. pose proof (Hc _ Hf) as Hck. unfold xa_ent_chk in Hck.
  apply existsb_exists in Hck as (p & Hp & Hpc).
  pose proof (i63_range off) as Hoff. pose proof (i63_range len) as Hlen.
  destruct (xa_q_sound ts (to_Z off) (to_Z len) p ltac:(lia) ltac:(lia) Hpc) as (S1 & S2 & S3).
  unfold CXS.in_allow. apply orb_true_iff. right. unfold CXS.in_sh. apply existsb_exists. exists p. split; [exact Hp|].
  apply andb_true_iff. split; [apply Z.leb_le | apply Z.ltb_lt]; lia.
Qed.

(* [comment removed for export] *)
Definition al8 (q : AX2.expr * AX2.expr) : bool := (3 <=? AX2.ealign kn (fst q)) && (3 <=? AX2.ealign kn (snd q)).

Lemma pow_div8 k u : 3 <= k -> (2 ^ k | u) -> u mod 8 = 0.
Proof.
  intros Hk [c Hc]. rewrite Hc. replace k with ((k - 3) + 3) by lia. rewrite Z.pow_add_r by lia.
  rewrite Z.mul_assoc. apply Z.mod_mul. lia.
Qed.

Lemma in_sh_intro (q : AX2.expr * AX2.expr) y : In q (CAP.a_vis END) ->
  CXS.uE E1 (fst q) mod 8 = 0 -> (CXS.uE E1 (fst q) + CXS.uE E1 (snd q)) mod 8 = 0 ->
  CXS.uE E1 (fst q) <= y < CXS.uE E1 (fst q) + CXS.uE E1 (snd q) ->
  CXS.in_allow A E1 END (y / 8 + to_Z shadow_K) = true.
Proof.
  intros Hq H8 H8' Hy. unfold CXS.in_allow. apply orb_true_iff. right. unfold CXS.in_sh. apply existsb_exists.
  exists q. split; [exact Hq|]. unfold CXS.sh_lo, CXS.sh_hi. rewrite HshK.
  apply andb_true_iff. split; [apply Z.leb_le | apply Z.ltb_lt]; clear - H8 H8' Hy; Z.div_mod_to_equations; lia.
Qed.

Lemma al8_sound q : In q (CAP.a_vis CS) -> al8 q = true ->
  CXS.uE E1 (fst q) mod 8 = 0 /\ (CXS.uE E1 (fst q) + CXS.uE E1 (snd q)) mod 8 = 0.
Proof.
  intros _ Hc. unfold al8 in Hc. apply andb_prop in Hc as [H1 H2]. apply Z.leb_le in H1, H2.
  destruct (AX2S.ealign_sound segs E1 Mr kn (fst q) leaf_kn) as [_ D1].
  destruct (AX2S.ealign_sound segs E1 Mr kn (snd q) leaf_kn) as [_ D2].
  pose proof (pow_div8 _ _ H1 D1) as M1'. pose proof (pow_div8 _ _ H2 D2) as M2'. unfold CXS.uE.
  split; [exact M1'|]. rewrite Z.add_mod, M1', M2' by lia. reflexivity.
Qed.

(* [comment removed for export] *)
Definition hullq (q : AX2.expr * AX2.expr) : bool :=
  match fst q, snd q with
  | AX2.ELit b, AX2.ELit l => (0 <=? b) && (b <=? CAP.img_lo A) && (CAP.img_hi A <=? b + l) && (b mod 8 =? 0) && (l mod 8 =? 0) && (b + l <? 2 ^ 62)
  | _, _ => false
  end.

Definition parent_vis (p : int) (rgp : region) : bool :=
  ((to_Z p <? to_Z n)
   && existsb (fun q => al8 q && pair_mem q (CAP.a_vis END)
                        && CAP.xinsideJ kn (BrRev.tte TT p) (to_Z (rg_lo rgp)) (AX2.ELit (to_Z (rg_len rgp) - to_Z (rg_lo rgp))) (fst q) 0 (snd q))
              (CAP.a_vis CS))
  || existsb (fun q => match snd q with
                       | AX2.ELit l => (0 <=? l) && (l <? 2 ^ 62) && (l mod 8 =? 0) && (to_Z (rg_len rgp) <=? l) && xt_match (fst q) p
                       | _ => false
                       end) (CAP.a_vis END).

(* [comment removed for export] *)
Definition xa_reg_chk (rg : region) (p : int) : bool :=
  (0 <=? to_Z (rg_lo rg)) && (to_Z (rg_lo rg) <=? to_Z (rg_len rg)) && (8 * to_Z (rg_len rg) <? 2 ^ 62)
  && existsb (fun e : fent => fent_mem e ALL'
                              && covers e (p, of_Z (8 * to_Z (rg_lo rg)), of_Z (8 * (to_Z (rg_len rg) - to_Z (rg_lo rg))))) EX'.

Definition regvis_chk : bool :=
  existsb (fun q => hullq q && pair_mem q (CAP.a_vis END)) (CAP.a_vis END)
  && forallb (fun tr : int * region =>
                match rg_kind (snd tr) with
                | RK_plain => true
                | RK_shadow p => match iget p M1 with Some rgp => parent_vis p rgp || xa_reg_chk (snd tr) p | None => false end
                end) (ielements M1).

Lemma region_allowed : regvis_chk = true ->
  forall t rg z, iget t M1 = Some rg -> in_ival rho' t rg z -> span_lo <= z < span_hi ->
    CXS.in_allow A E1 END z = true \/ exb z = true.
Proof.
  unfold regvis_chk. intros Hc t rg z Hg Hin Hzs. apply andb_prop in Hc as [Hhq Hall].
  pose proof (Hspok' t rg Hg) as Hso. unfold span_ok in Hso. unfold in_ival in Hin.
  destruct (HM1 t rg Hg) as (_ & _ & _ & _ & _ & _ & Hkind).
  rewrite forallb_forall in Hall. pose proof (Hall (t, rg) (proj2 (ielements_spec M1 t rg) Hg)) as Hck. cbn [snd] in Hck.
  destruct (rg_kind rg) as [|p] eqn:Ek.
  - destruct Hso as [[Hm|Hm] | (_ & _ & Hpre)]; [lia | lia |].
    destruct (Hpre z Hin) as (r & Hr & R1 & R2).
    pose proof (proj1 (Forall_forall _ _) (res_in_hull segs A Hres) r Hr) as [Rh1 Rh2].
    apply existsb_exists in Hhq as (q & Hq & Hqc). apply andb_prop in Hqc as [Hqc _]. unfold hullq in Hqc.
    destruct (fst q) as [b| | | | | | |] eqn:Eb; try discriminate. destruct (snd q) as [l| | | | | | |] eqn:El; try discriminate.
    apply andb_prop in Hqc as [Hqc Q6]. apply andb_prop in Hqc as [Hqc Q5]. apply andb_prop in Hqc as [Hqc Q4].
    apply andb_prop in Hqc as [Hqc Q3]. apply andb_prop in Hqc as [Q1 Q2].
    apply Z.leb_le in Q1, Q2, Q3. apply Z.eqb_eq in Q4, Q5. apply Z.ltb_lt in Q6.
    assert (Eub : CXS.uE E1 (fst q) = b) by (unfold CXS.uE; rewrite Eb; cbn [AX2.edenot]; apply br_lit_small; lia).
    assert (Eun : CXS.uE E1 (snd q) = l) by (unfold CXS.uE; rewrite El; cbn [AX2.edenot]; apply br_lit_small; lia).
    left. replace z with (8 * (z - to_Z shadow_K) / 8 + to_Z shadow_K) by (rewrite Z.mul_comm, Z.div_mul by lia; lia).
    apply (in_sh_intro q _ Hq); rewrite ?Eub, ?Eun; [exact Q4 | rewrite Z.add_mod, Q4, Q5 by lia; reflexivity | lia].
  - destruct Hso as (_ & rgp & Hgp & Hal3 & Hlo8 & Hlen8). rewrite Hgp in Hck. cbn in Hkind. destruct Hkind as [_ Ebase].
    apply orb_prop in Hck as [Hck|Hxa].
    2:{ (* [comment removed for export] *)
      right. unfold xa_reg_chk in Hxa. apply andb_prop in Hxa as [Hxa Hex]. apply andb_prop in Hxa as [Hxa Hl62'].
      apply andb_prop in Hxa as [Hlo0' Hlole]. apply Z.leb_le in Hlo0', Hlole. apply Z.ltb_lt in Hl62'.
      apply existsb_exists in Hex as (e & Hee & Hec). apply andb_prop in Hec as [Hmem Hcov].
      pose proof (covers_sound e _ (fent_mem_In _ _ Hmem) Hcov) as [C1 C2].
      destruct (HM1 p rgp Hgp) as (_ & _ & Hnwp & _).
      pose proof (br_u64 (rho' p)) as Hup. pose proof (i63_range (rg_len rgp)) as Hlp.
      assert (E8lo : to_Z (of_Z (8 * to_Z (rg_lo rg))) = 8 * to_Z (rg_lo rg)) by (apply of_Z_small; lia).
      assert (E8ln : to_Z (of_Z (8 * (to_Z (rg_len rg) - to_Z (rg_lo rg)))) = 8 * (to_Z (rg_len rg) - to_Z (rg_lo rg))) by (apply of_Z_small; lia).
      unfold e_hi in C2. rewrite e_sz_den in C2. cbn [snd] in C2. unfold e_lo in C1, C2. cbn [den fst] in C1, C2.
      rewrite E8lo, E8ln in *. rewrite (adr_unsigned_z rho' p (8 * to_Z (rg_lo rg))) in C1, C2 by lia.
      unfold exb. apply existsb_exists. exists e. split; [exact Hee|].
      change (to_Z shadow_K) with 2147450880 in *.
      apply andb_true_iff. split; apply Z.ltb_lt; unfold e_hi, e_lo in *; clear - Hin Ebase C1 C2 Hlo0' Hup; Z.div_mod_to_equations; lia. }
    destruct (HM1 p rgp Hgp) as (_ & Hl62 & Hnw & _ & Halp & _).
    assert (Hp8 : bv_unsigned (rho' p) mod 8 = 0).
    { apply (pow_div8 (to_Z (rg_align rgp))); [exact Hal3|]. apply Z.mod_divide; [lia|]. exact Halp. }
    set (y := 8 * (z - to_Z shadow_K)).
    assert (Hy : bv_unsigned (rho' p) + to_Z (rg_lo rgp) <= y < bv_unsigned (rho' p) + to_Z (rg_len rgp)).
    { unfold y. change (to_Z shadow_K) with 2147450880. clear - Hin Ebase Hp8 Hlo8 Hlen8. Z.div_mod_to_equations. lia. }
    replace z with (y / 8 + to_Z shadow_K) by (unfold y; rewrite Z.mul_comm, Z.div_mul by lia; lia).
    pose proof (i63_range (rg_lo rgp)) as Hlo0. pose proof (i63_range (rg_len rgp)) as Hlen0.
    unfold parent_vis in Hck. apply orb_prop in Hck as [Hold|Hnew].
    + apply andb_prop in Hold as [Hpn Hold]. apply Z.ltb_lt in Hpn. apply existsb_exists in Hold as (q & Hq & Hqc).
      apply andb_prop in Hqc as [Hqc Hx]. apply andb_prop in Hqc as [Hal Hmem].
      destruct (al8_sound q Hq Hal) as [A1 A2].
      destruct (CXS.xinsideJ_sound segs E1 Mr kn _ _ _ _ _ _ leaf_kn Hx) as [X1 X2].
      unfold AX2S.estart, AX2S.elenZ in X1, X2. cbn [AX2.a_base AX2.a_off AX2.edenot] in X1, X2.
      rewrite <- (Hrho_tt p), <- (Hrho p Hpn) in X1, X2.
      rewrite (br_lit_small (to_Z (rg_len rgp) - to_Z (rg_lo rgp))) in X2 by lia.
      left. apply (in_sh_intro q y (pair_mem_In _ _ Hmem) A1 A2). unfold CXS.uE. lia.
    + apply existsb_exists in Hnew as (q & Hq & Hqc). destruct (snd q) as [l| | | | | | |] eqn:El; try discriminate.
      apply andb_prop in Hqc as [Hqc Hm]. apply andb_prop in Hqc as [Hqc Q4]. apply andb_prop in Hqc as [Hqc Q3].
      apply andb_prop in Hqc as [Q1 Q2]. apply Z.leb_le in Q1, Q4. apply Z.ltb_lt in Q2. apply Z.eqb_eq in Q3.
      pose proof (xt_match_sound _ _ Hm) as Eub.
      assert (Eun : CXS.uE E1 (snd q) = l) by (unfold CXS.uE; rewrite El; cbn [AX2.edenot]; apply br_lit_small; lia).
      left. apply (in_sh_intro q y Hq); rewrite ?Eub, ?Eun; [exact Hp8 | rewrite Z.add_mod, Hp8, Q3 by lia; reflexivity | lia].
Qed.

(* [comment removed for export] *)
Lemma shadow_op_block o z : shadow_parent_chk = true -> In o ops -> fst o = OpShadow ->
  e_lo (den rho' (snd o)) <= z < e_hi (den rho' (snd o)) ->
  to_Z shadow_K <= z
  /\ exists o', In o' ops /\ match fst o' with OpShadow | OpCommit => False | _ => True end
       /\ forall y, 8 * (z - to_Z shadow_K) <= y < 8 * (z - to_Z shadow_K) + 8 ->
                    e_lo (den rho' (snd o')) <= y < e_hi (den rho' (snd o')).
Proof.
  intros Hsp Ho Ek Hin. unfold shadow_parent_chk in Hsp. rewrite forallb_forall in Hsp. pose proof (Hsp o Ho) as Hpar. rewrite Ek in Hpar.
  pose proof (proj1 (Forall_forall _ _) Hops o Ho) as Hok. unfold op_ok in Hok. cbv zeta in Hok. rewrite Ek in Hok.
  destruct Hok as (_ & Ebase & _).
  destruct (snd o) as [[ts off] sl] eqn:Eo. apply andb_prop in Hpar as [Hoff Hpar]. apply Uint63.eqb_spec in Hoff. subst off.
  apply existsb_exists in Hpar as (o' & Ho' & Hpc'). cbn [fent_tag fst] in Ebase.
  destruct (den0 ts sl) as [Dlo Dhi]. rewrite Dlo, Dhi in Hin.
  assert (Hgen : forall g off' lg, snd o' = (g, off', lg) ->
            (g =? ts - 1)%uint63 && (off' =? 0)%uint63 && (8 * to_Z sl <=? to_Z lg) && (to_Z lg mod 4096 =? 0) = true ->
            bv_unsigned (rho' (fent_tag (snd o'))) mod 4096 = 0 ->
            to_Z shadow_K <= z /\ forall y, 8 * (z - to_Z shadow_K) <= y < 8 * (z - to_Z shadow_K) + 8 ->
                    e_lo (den rho' (snd o')) <= y < e_hi (den rho' (snd o'))).
  { intros g off' lg Eo' Hc Hg4. apply andb_prop in Hc as [Hc _]. apply andb_prop in Hc as [Hc Hl8].
    apply andb_prop in Hc as [Hg Hoff']. apply Uint63.eqb_spec in Hg, Hoff'. subst g off'. apply Z.leb_le in Hl8.
    rewrite Eo' in *. cbn [fent_tag fst] in Hg4. destruct (den0 (ts - 1)%uint63 lg) as [Glo Ghi]. rewrite Glo, Ghi.
    pose proof (br_u64 (rho' (ts - 1)%uint63)) as Hu.
    split; [clear - Hin Ebase Hu; Z.div_mod_to_equations; lia|].
    intros y Hy. clear - Hin Ebase Hg4 Hl8 Hy. Z.div_mod_to_equations. lia. }
  pose proof (proj1 (Forall_forall _ _) Hops o' Ho') as Hok'. unfold op_ok in Hok'. cbv zeta in Hok'.
  destruct (snd o') as [[g off'] lg] eqn:Eo'.
  destruct (fst o') eqn:Ek'; try discriminate; destruct (Hgen g off' lg eq_refl Hpc' (proj1 Hok')) as [HK Hblk];
    (split; [exact HK|]); exists o'; rewrite Ek', Eo'; (split; [exact Ho'|]); (split; [exact I | exact Hblk]).
Qed.

(* [comment removed for export] *)
Definition commit_al_chk : bool :=
  forallb (fun o : vop =>
     if is_commit o then
       let '(t, off, len) := snd o in
       (to_Z off mod 4096 =? 0) && (to_Z len mod 4096 =? 0)
       && match iget t M1 with
          | Some rg => (12 <=? to_Z (rg_align rg)) && (to_Z (rg_align rg) <=? 62) && (to_Z off + to_Z len <=? to_Z (rg_len rg))
          | None => false
          end
     else true) ops.

Lemma commit_gone o (x : word) : commit_al_chk = true -> In o ops -> is_commit o = true ->
  e_lo (den rho' (snd o)) <= bv_unsigned x < e_hi (den rho' (snd o)) ->
  CXS.in_ivs (bv_unsigned x) (vm_noaccess V') = false /\ page_in_ranges (page_base x) (m_vm_lazy m') = false.
Proof.
  intros Hal Ho Hcm Hx.
  assert (Hcut : is_cut o = true) by (unfold is_cut; unfold is_commit in Hcm; destruct (fst o); try discriminate; reflexivity).
  destruct (commit_cover o Ho Hcm) as (j & amc & ec & J1 & J2 & Kc & Htc & C1 & C2).
  assert (Hec : In ec ALL') by exact (nth_error_In _ _ J2).
  assert (Hp : In (den rho' ec) (vm_maps V')) by (rewrite Hmaps'; apply in_map; exact Hec).
  pose proof Hfacts' as Hf. destruct Hf as (_ & _ & _ & _ & Htop & _).
  pose proof (proj1 (Forall_forall _ _) Htop _ Hp) as [_ Hhi]. pose proof (alloc_top_lt V') as Hat. unfold two_pow_64 in Hat.
  split.
  - rewrite Hna'. exact (na_apply_cut_pt rho' ops _ o (bv_unsigned x) root_wf_na Ho Hcut Hx).
  - rewrite Hlz'.
    unfold commit_al_chk in Hal. rewrite forallb_forall in Hal. pose proof (Hal o Ho) as H1. rewrite Hcm in H1.
    destruct (snd o) as [[t off] len] eqn:Eso.
    apply andb_prop in H1 as [H1 Hrg]. apply andb_prop in H1 as [Ho4 Hl4]. apply Z.eqb_eq in Ho4, Hl4.
    destruct (iget t M1) as [rg|] eqn:Hg; [|discriminate].
    apply andb_prop in Hrg as [Hrg Hin]. apply andb_prop in Hrg as [A1 A2]. apply Z.leb_le in A1, A2, Hin.
    destruct (HM1 t rg Hg) as (_ & _ & Hb63 & _ & Hm & _).
    pose proof (br_u64 (rho' t)) as Hu. pose proof (i63_range off) as Hoff. pose proof (i63_range len) as Hlen.
    assert (Elo : e_lo (den rho' (t, off, len)) = bv_unsigned (rho' t) + to_Z off).
    { unfold e_lo. cbn [den fst]. apply adr_unsigned_z. lia. }
    assert (Ehi : e_hi (den rho' (t, off, len)) = bv_unsigned (rho' t) + to_Z off + to_Z len).
    { unfold e_hi. rewrite Elo, e_sz_den. reflexivity. }
    assert (Hr12 : bv_unsigned (rho' t) mod 4096 = 0).
    { assert (Hd : (2 ^ to_Z (rg_align rg) | bv_unsigned (rho' t))) by (apply Z.mod_divide; [lia | exact Hm]).
      destruct Hd as [c Hc']. rewrite Hc'. replace (to_Z (rg_align rg)) with ((to_Z (rg_align rg) - 12) + 12) by lia.
      rewrite Z.pow_add_r by lia. change (2 ^ 12) with 4096. rewrite Z.mul_assoc. apply Z.mod_mul. lia. }
    rewrite Elo, Ehi in Hx.
    destruct (page_base_inside x (bv_unsigned (rho' t) + to_Z off) (bv_unsigned (rho' t) + to_Z off + to_Z len)
                ltac:(clear - Hr12 Ho4; Z.div_mod_to_equations; lia) ltac:(clear - Hr12 Ho4 Hl4; Z.div_mod_to_equations; lia) Hx)
      as (_ & P2 & P3).
    apply (lz_apply_cut_page rho' ops _ o (page_base x) root_wf_lz op_hi64 Ho Hcut).
    + rewrite ?Eso, Ehi. lia.
    + rewrite ?Eso, Elo. exact P2.
    + rewrite ?Eso, Ehi. unfold page_size. exact P3.
    + intros o2 Ho2 Hl2 [Q1 Q2].
      destruct (ops3_get n ops o2 Hopchk Ho2) as (_ & _ & Ht2).
      assert (Hnc2 : is_commit o2 = false) by (unfold is_commit; unfold is_lazyop in Hl2; destruct (fst o2); try discriminate; reflexivity).
      specialize (Ht2 Hnc2).
      pose proof (proj1 (Forall_forall _ _) Hops o2 Ho2) as Hok. unfold op_ok in Hok. cbv zeta in Hok.
      unfold is_lazyop in Hl2. destruct (fst o2); try discriminate. destruct Hok as (_ & Hold & _).
      pose proof (Hold ec Hec ltac:(lia)) as Hd. rewrite ?Eso in C1, C2. rewrite Elo in C1. rewrite Ehi in C2.
      unfold e_disj in Hd. unfold page_size in Q2. lia.
Qed.

Lemma commit_visible o (x : word) : commit_al_chk = true -> In o ops -> is_commit o = true ->
  e_lo (den rho' (snd o)) <= bv_unsigned x < e_hi (den rho' (snd o)) -> CXS.hid A argH E1 END m' x = false.
Proof.
  intros Hal Ho Hcm Hx. destruct (commit_gone o x Hal Ho Hcm Hx) as [Hna Hlz].
  destruct (commit_cover o Ho Hcm) as (j & amc & ec & J1 & J2 & Kc & Htc & C1 & C2).
  assert (Hec : In ec ALL') by exact (nth_error_In _ _ J2).
  assert (Hp : In (den rho' ec) (vm_maps V')) by (rewrite Hmaps'; apply in_map; exact Hec).
  pose proof Hfacts' as Hf. destruct Hf as (_ & _ & _ & _ & Htop & _).
  pose proof (proj1 (Forall_forall _ _) Htop _ Hp) as [_ Hhi].
  destruct (CXS.co_isp _ _ _ _ _ _ _ _ _ _ _ _ HCS) as [Eisp _].
  assert (Hat : alloc_top V' = ISP - 8388608) by (rewrite leaf_atop; unfold alloc_top, stack_max_size; rewrite Eisp; lia).
  unfold CXS.hid. apply orb_false_iff. split.
  - destruct (argH E1 x) eqn:Ea; [|reflexivity]. destruct (argH_high E1 x Ea) as [_ Hsp]. lia.
  - apply negb_false_iff. unfold CXS.vis. cbv zeta. apply orb_true_iff. right.
    apply andb_true_iff. split; [apply andb_true_iff; split|].
    + apply in_ivs_true. exists (den rho' ec). split; [exact Hp|]. lia.
    + rewrite Hna. reflexivity.
    + rewrite Hlz. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma root_zero (a : word) :
  CXS.hid A argH E1 CS m a = true -> CXS.in_ivs (bv_unsigned a) (vm_maps V) = true ->
  CXS.in_ivs (bv_unsigned a) (vm_noaccess V) = false -> page_in_ranges (page_base a) (m_vm_lazy m) = true ->
  CXS.in_ghost E1 CS (bv_unsigned a) = false -> ~ touched rho' ops (bv_unsigned a) ->
  xain (bv_unsigned a) = false ->
  FULL' a = Some (Z_to_bv 8 0).
Proof.
  intros Hh Hm Hn Hl Hg Hnt Hnx. rewrite (Hfr' a Hnt).
  - exact (CXS.co_zero _ _ _ _ _ _ _ _ _ _ _ _ HCS a Hh Hm Hn Hl Hg).
  - left. intros Hc. destruct (Hcw a Hc) as [Hc'|Hc']; [rewrite Hc' in Hh; discriminate | rewrite Hc' in Hnx; discriminate].
Qed.

Definition ghost_keep_chk : bool := forallb (fun p => pair_mem p (CAP.a_ghost END)) (CAP.a_ghost CS).

Definition fresh_vis_chk : bool :=
  forallb (fun e : fent =>
     (to_Z n <=? to_Z (fent_tag e))
     && let '(t, off, len) := e in
        (off =? 0)%uint63
        && existsb (fun q : AX2.expr * AX2.expr =>
                      match snd q with
                      | AX2.ELit l => (0 <=? l) && (l <? 2 ^ 62) && (to_Z len <=? l) && xt_match (fst q) t
                      | _ => false
                      end) (CAP.a_vis END)) fresh.

Definition spanlazy_chk : bool :=
  forallb (fun am => match span_lit am, CAP.am_kind am with
                     | Some (b, h), CAP.KRWLAZY => (h <=? lsh_hi) || (hsh_lo <=? b)
                     | _, _ => true
                     end) (CAP.a_maps CS).

Definition inreg (z : Z) : bool :=
  existsb (fun tr : int * region => (bv_unsigned (rho' (fst tr)) + to_Z (rg_lo (snd tr)) <=? z)
                                    && (z <? bv_unsigned (rho' (fst tr)) + to_Z (rg_len (snd tr)))) (ielements M1).

Definition zero3_chk : bool :=
  avis_keep_chk && avis3_chk && regvis_chk && ghost_keep_chk && fresh_vis_chk && spanlazy_chk
  && forallb (fun e => to_Z (fent_tag e) <? to_Z n) EX' && commit_al_chk.

Lemma inreg_false z : inreg z = false -> no_region rho' M1 z.
Proof.
  intros Hf t rg Hg Hin. unfold in_ival in Hin.
  assert (Ht : inreg z = true); [|rewrite Ht in Hf; discriminate].
  unfold inreg. apply existsb_exists. exists (t, rg). split; [exact (proj2 (ielements_spec M1 t rg) Hg)|]. cbn [fst snd].
  apply andb_true_iff. split; [apply Z.leb_le | apply Z.ltb_lt]; lia.
Qed.

Lemma inreg_true z : inreg z = true -> exists t rg, iget t M1 = Some rg /\ in_ival rho' t rg z.
Proof.
  unfold inreg. intros H. apply existsb_exists in H as ([t rg] & Hin & Hc). cbn [fst snd] in Hc.
  apply andb_prop in Hc as [H1 H2]. apply Z.leb_le in H1. apply Z.ltb_lt in H2.
  exists t, rg. split; [exact (proj1 (ielements_spec M1 t rg) Hin) | unfold in_ival; lia].
Qed.

Lemma exb_false z : exb z = false -> ~ exempted rho' EX' z.
Proof.
  intros Hf (e & y & He & Hy & Ez). assert (Ht : exb z = true); [|rewrite Ht in Hf; discriminate].
  unfold exb. apply existsb_exists. exists e. split; [exact He|].
  apply andb_true_iff. split; apply Z.ltb_lt; clear - Hy Ez; Z.div_mod_to_equations; lia.
Qed.

Lemma fresh_tags : fresh_vis_chk = true -> forall e, In e fresh -> to_Z n <= to_Z (fent_tag e).
Proof.
  unfold fresh_vis_chk. intros Hc e He. rewrite forallb_forall in Hc. pose proof (Hc e He) as H1.
  apply andb_prop in H1 as [H1 _]. apply Z.leb_le in H1. exact H1.
Qed.

Lemma exb_true z : fresh_vis_chk = true -> forallb (fun e => to_Z (fent_tag e) <? to_Z n) EX' = true -> exb z = true ->
  exists e0 y, In e0 ALL0 /\ e_lo (den rho e0) <= y < e_hi (den rho e0)
               /\ 8 * (z - to_Z shadow_K) <= y < 8 * (z - to_Z shadow_K) + 8.
Proof.
  intros Hfv Hext H. unfold exb in H. apply existsb_exists in H as (e & He & Hc).
  apply andb_prop in Hc as [C1 C2]. apply Z.ltb_lt in C1, C2.
  destruct (proj1 (Forall_forall _ _) Hexcov' e He) as (Hpos & e2 & He2 & Hw).
  rewrite forallb_forall in Hext. pose proof (Hext e He) as Hte. apply Z.ltb_lt in Hte.
  assert (He20 : In e2 ALL0).
  { rewrite HALL in He2. apply in_app_iff in He2 as [Hfr|H0]; [|exact H0]. exfalso.
    pose proof (fresh_tags Hfv e2 Hfr) as Ht2. destruct Hw as (Et & _). rewrite Et in Ht2. lia. }
  assert (Hin2 : In (den rho' e2) (vm_maps V')) by (rewrite Hmaps'; apply in_map; exact He2).
  destruct Hfacts' as (_ & _ & _ & _ & Htop & _). pose proof (proj1 (Forall_forall _ _) Htop _ Hin2) as [_ Hhi2].
  pose proof (alloc_top_lt V') as Hat. unfold two_pow_64 in Hat.
  pose proof (den_within rho' e e2 Hw ltac:(lia)) as [W1 W2].
  exists e2, (Z.max (e_lo (den rho' e)) (8 * (z - to_Z shadow_K))). split; [exact He20|].
  rewrite <- (leaf_den0 e2 He20). pose proof (e_sz_den rho' e) as Hsz. unfold e_hi in *. lia.
Qed.

Theorem leaf_zero : forallb xa_ent_chk XA = true -> zero3_chk = true ->
  forall a : word, CXS.hid A argH E1 END m' a = true ->
    CXS.in_ivs (bv_unsigned a) (vm_maps V') = true ->
    CXS.in_ivs (bv_unsigned a) (vm_noaccess V') = false ->
    page_in_ranges (page_base a) (m_vm_lazy m') = true ->
    CXS.in_ghost E1 END (bv_unsigned a) = false ->
    FULL' a = Some (Z_to_bv 8 0).
Proof.
  unfold zero3_chk. intros Hxac Hc a Hh Hm Hn Hl Hg.
  apply andb_prop in Hc as [Hc Hcal].
  assert (Hncm : forall o, In o ops -> is_commit o = true -> ~ (e_lo (den rho' (snd o)) <= bv_unsigned a < e_hi (den rho' (snd o)))).
  { intros o Ho Hcm Hin. destruct (commit_gone o a Hcal Ho Hcm Hin) as [_ Hlz0]. rewrite Hlz0 in Hl. discriminate. }
  apply andb_prop in Hc as [Hc Hext]. apply andb_prop in Hc as [Hc Hsl]. apply andb_prop in Hc as [Hc Hfv].
  apply andb_prop in Hc as [Hc Hgk]. apply andb_prop in Hc as [Hc Hrv]. apply andb_prop in Hc as [Hak Hav].
  set (z := bv_unsigned a) in *.
  pose proof Hav as Hav0. unfold avis3_chk in Hav0.
  apply andb_prop in Hav0 as [Hav0 _]. apply andb_prop in Hav0 as [Hav0 Hspar]. apply andb_prop in Hav0 as [Hav0 _].
  apply andb_prop in Hav0 as [Hav0 _]. apply andb_prop in Hav0 as [Hav0 Hsc]. apply andb_prop in Hav0 as [_ Hsk].
  (* [comment removed for export] *)
  pose proof Hm as Hm'. apply in_ivs_true in Hm' as (p' & Hp' & Hzp'). rewrite Hmaps' in Hp'. apply in_map_iff in Hp' as (e' & <- & He').
  assert (Hin' : In (den rho' e') (vm_maps V')) by (rewrite Hmaps'; apply in_map; exact He').
  destruct Hfacts' as (_ & _ & _ & _ & Htop & _). pose proof (proj1 (Forall_forall _ _) Htop _ Hin') as [_ Hhi'].
  destruct (CXS.co_isp _ _ _ _ _ _ _ _ _ _ _ _ HCS) as [Eisp _].
  assert (Hat : alloc_top V' = ISP - 8388608) by (rewrite leaf_atop; unfold alloc_top, stack_max_size; rewrite Eisp; lia).
  (* [comment removed for export] *)
  assert (Hnv : CXS.vis A E1 END m' a = false).
  { unfold CXS.hid in Hh. apply orb_prop in Hh as [Ha|Hv]; [|apply negb_true_iff in Hv; exact Hv].
    exfalso. destruct (argH_high E1 a Ha) as [_ Hisp]. fold z in Hisp. lia. }
  assert (Hvis_if : CXS.in_allow A E1 END z = true -> False).
  { intros Hal. unfold CXS.vis in Hnv. cbv zeta in Hnv. fold z in Hnv. rewrite Hm, Hn, Hal in Hnv.
    cbn [negb andb] in Hnv. rewrite !orb_true_r in Hnv. discriminate. }
  assert (Hnx : xain z = false).
  { destruct (xain z) eqn:Ex; [|reflexivity]. exfalso. exact (Hvis_if (xa_in_allow Hxac z Ex)). }
  pose proof (leaf_hid_mono Hak a Hh) as Hh0.
  assert (Hg0 : CXS.in_ghost E1 CS z = false).
  { apply not_true_is_false. intros Hg1. unfold CXS.in_ghost in Hg1. apply existsb_exists in Hg1 as (q & Hq & Hqz).
    unfold ghost_keep_chk in Hgk. rewrite forallb_forall in Hgk.
    assert (Ht : CXS.in_ghost E1 END z = true) by (unfold CXS.in_ghost; apply existsb_exists; exists q; split; [exact (pair_mem_In _ _ (Hgk q Hq)) | exact Hqz]).
    rewrite Ht in Hg. discriminate. }
  rewrite HALL in He'. apply in_app_iff in He' as [Hfr|He0].
  { (* [comment removed for export] *)
    exfalso. apply Hvis_if. unfold fresh_vis_chk in Hfv. rewrite forallb_forall in Hfv. pose proof (Hfv e' Hfr) as Hck.
    apply andb_prop in Hck as [_ Hck]. destruct e' as [[t off] len]. apply andb_prop in Hck as [Hoff Hex].
    apply Uint63.eqb_spec in Hoff. subst off. apply existsb_exists in Hex as (q & Hq & Hqc).
    destruct (snd q) as [l| | | | | | |] eqn:El; try discriminate.
    apply andb_prop in Hqc as [Hqc Hxm]. apply andb_prop in Hqc as [Hqc Q3]. apply andb_prop in Hqc as [Q1 Q2].
    apply Z.leb_le in Q1, Q3. apply Z.ltb_lt in Q2. pose proof (xt_match_sound _ _ Hxm) as Eub.
    assert (Eun : CXS.uE E1 (snd q) = l) by (unfold CXS.uE; rewrite El; cbn [AX2.edenot]; apply br_lit_small; lia).
    destruct (den0 t len) as [Dlo Dhi]. rewrite Dlo, Dhi in Hzp'.
    unfold CXS.in_allow. apply orb_true_iff. left. unfold CXS.in_vis. apply existsb_exists. exists q. split; [exact Hq|].
    rewrite Eub, Eun. apply andb_true_iff. split; [apply Z.leb_le | apply Z.ltb_lt]; lia. }
  (* [comment removed for export] *)
  rewrite (leaf_den0 e' He0) in Hzp'.
  assert (Hm0 : CXS.in_ivs z (vm_maps V) = true) by (apply in_ivs_true; exists (den rho e'); split; [rewrite Hmaps0; apply in_map; exact He0 | exact Hzp']).
  assert (Hplain_off : forall o, In o ops -> match fst o with OpShadow => False | _ => True end ->
            ~ (e_lo (den rho' (snd o)) <= z < e_hi (den rho' (snd o)))).
  { intros o Ho Hk. destruct (is_commit o) eqn:Ecm; [exact (Hncm o Ho Ecm)|].
    apply (root_entry_off z o e' He0 Hzp' Ho). unfold is_commit in Ecm. destruct (fst o); try exact I; try contradiction; discriminate Ecm. }
  destruct (Z_lt_dec z span_lo) as [Hlow|Hge]; [|destruct (Z_le_dec span_hi z) as [Hhigh|Hlt]].
  1,2: (apply (root_zero a Hh0 Hm0); [ | | exact Hg0 | | exact Hnx]).
  1,4: (apply not_true_is_false; intros Hna0;
        assert (Hk : CXS.in_ivs z (vm_noaccess V') = true);
        [rewrite Hna'; apply (na_apply_keeps_pt rho' ops _ z root_wf_na Hna0) | rewrite Hk in Hn; discriminate];
        intros o Ho Hcut; apply (Hplain_off o Ho); unfold is_cut in Hcut; destruct (fst o); try discriminate; exact I).
  1,3: (rewrite Hlz' in Hl; destruct (lz_apply_page rho' ops _ (page_base a) root_wf_lz op_hi64 Hl) as [Hl0 | (o & Ho & Hlo & H1 & H2)]; [exact Hl0|];
        exfalso; pose proof (page_base_range a) as Hpb; fold z in Hpb;
        apply (Hplain_off o Ho); [unfold is_lazyop in Hlo; destruct (fst o); try discriminate; exact I | lia]).
  1,2: (intros (o & Ho & Hin); destruct (fst o) eqn:Ek;
        try (apply (Hplain_off o Ho); [rewrite Ek; exact I | exact Hin]);
        pose proof (proj1 (Forall_forall _ _) Hops o Ho) as Hok; unfold op_ok in Hok; cbv zeta in Hok; rewrite Ek in Hok;
        destruct Hok as (_ & _ & Hspan); pose proof (Hspan z Hin); lia).
  (* [comment removed for export] *)
  assert (Hzs : span_lo <= z < span_hi) by lia.
  destruct (span_cover_sound _ _ _ _ Hsc z Hzs) as (q & Hq & Hzq).
  destruct (span_lit_in segs A Lim SINV argH ISP FS0 E1 CS R FULL m HCS Hlx q Hq) as (j & am & Hj & Esl & Hvj & Elo & Ehi).
  pose proof (nth_error_In _ _ Hj) as Ham.
  unfold span_kinds_chk in Hsk. rewrite forallb_forall in Hsk. pose proof (Hsk am Ham) as Hkd.
  unfold is_span_lit in Hkd. rewrite Esl in Hkd. cbn [negb orb] in Hkd.
  assert (Hzam : bv_unsigned (AX2.edenot E1 (CAP.am_base am)) <= z
                 < bv_unsigned (AX2.edenot E1 (CAP.am_base am)) + bv_unsigned (AX2.edenot E1 (CAP.am_len am))).
  { unfold e_hi, e_lo, e_sz, CXS.amap_den in Elo, Ehi. cbn [fst snd] in Elo, Ehi. lia. }
  destruct (CAP.am_kind am) eqn:Ekd; try discriminate.
  2,3: (exfalso; destruct (start_entry am Ham) as (e0 & He00 & _ & Ed & Hin0);
        assert (Hnone : CAP.am_kind am = CAP.KNONE \/ CAP.am_kind am = CAP.KNONELAZY) by (rewrite Ekd; tauto);
        pose proof (proj1 (Forall_forall _ _) (CXS.co_none _ _ _ _ _ _ _ _ _ _ _ _ HCS) am Ham Hnone) as Hna0;
        pose proof (proj1 (Forall_forall _ _) (CXS.co_bounds _ _ _ _ _ _ _ _ _ _ _ _ HCS) _ Hin0) as (Hsz & _);
        assert (Ht : CXS.in_ivs z (vm_noaccess V') = true);
        [ rewrite Hna'; apply (na_apply_keeps_pt rho' ops _ z root_wf_na);
          [ apply in_ivs_true; exists (CXS.amap_den E1 am); split; [exact Hna0 | unfold e_hi, e_lo, e_sz, CXS.amap_den; cbn [fst snd]; lia]
          | intros o Ho Hcut Hzo; destruct (is_commit o) eqn:Ecm;
            [ exact (Hncm o Ho Ecm Hzo)
            | destruct (cut_misses e0 o He00 Ho Hcut Ecm) as [_ Hd]; rewrite Ed in Hd;
              unfold e_disj, e_hi, e_lo, e_sz, CXS.amap_den in Hd; cbn [fst snd] in Hd; unfold e_hi, e_lo, e_sz in Hzo; lia ] ]
        | rewrite Ht in Hn; discriminate ]).
  destruct (proj1 (Forall_forall _ _) (CXS.co_kinds _ _ _ _ _ _ _ _ _ _ _ _ HCS) am Ham Ekd a Hzam) as [Hn0 Hl0].
  (* [comment removed for export] *)
  assert (Htail : (z < to_Z shadow_K \/ exb z = true) -> FULL' a = Some (Z_to_bv 8 0)).
  { intros Hother.
    apply (root_zero a Hh0 Hm0 Hn0 Hl0 Hg0); [|exact Hnx]. intros (o & Ho & Hin). destruct (fst o) eqn:Ek;
      try (apply (Hplain_off o Ho); [rewrite Ek; exact I | exact Hin]).
    destruct (shadow_op_block o z Hspar Ho Ek Hin) as (HKz & o' & Ho' & Hk' & Hblk).
    destruct Hother as [Hlowz | Hexb]; [lia|].
    destruct (exb_true z Hfv Hext Hexb) as (e0 & y & He00 & Hy0 & Hyb).
    apply (root_entry_off y o' e0 He00 Hy0 Ho'); [destruct (fst o'); try contradiction; exact I | exact (Hblk y Hyb)]. }
  destruct (inreg z) eqn:Eir.
  { destruct (inreg_true z Eir) as (t & rg & Hgr & Hinr).
    destruct (region_allowed Hrv t rg z Hgr Hinr Hzs) as [Hal|Hexb]; [exfalso; exact (Hvis_if Hal) | exact (Htail (or_intror Hexb))]. }
  (* [comment removed for export] *)
  assert (Hroute : (lsh_lo <= z < lsh_hi \/ hsh_lo <= z < hsh_hi) /\ exb z = false \/ (z < to_Z shadow_K \/ exb z = true)).
  { unfold spanlazy_chk in Hsl. rewrite forallb_forall in Hsl. pose proof (Hsl am Ham) as Hs. rewrite Esl, Ekd in Hs.
    destruct q as [qb qh]. cbn [fst snd] in Hzq. destruct (exb z); [right; right; reflexivity|].
    apply orb_prop in Hs as [Hs|Hs]; [apply Z.leb_le in Hs | apply Z.leb_le in Hs].
    - destruct (Z_lt_dec z lsh_lo); [right; left; unfold lsh_lo in *; change (to_Z shadow_K) with 2147450880; lia | left; split; [left; lia | reflexivity]].
    - left. split; [right; unfold hsh_hi, span_hi in *; lia | reflexivity]. }
  destruct Hroute as [[Hzone Hexb] | Hother]; [|exact (Htail Hother)].
  destruct (HShZ' a Hzone (inreg_false z Eir) (exb_false z Hexb)) as [Hrv0 _].
  apply (rview_noseg segs FULL' a _ Hrv0). apply SEGS_in_hull. unfold CXS.in_hull. apply andb_false_iff. right.
  apply Z.ltb_ge. unfold avis3_chk in Hav. do 3 (apply andb_prop in Hav as [Hav _]). apply andb_prop in Hav as [_ Hih]. apply Z.leb_le in Hih. fold z. lia.
Qed.

(* [comment removed for export] *)
Lemma leaf_fresh_visible : fresh_vis_chk = true -> forall e, In e fresh ->
  forall x : word, e_lo (den rho' e) <= bv_unsigned x < e_hi (den rho' e) -> CXS.hid A argH E1 END m' x = false.
Proof.
  intros Hfv e Hfr x Hx. set (z := bv_unsigned x) in *.
  assert (He' : In e ALL') by (rewrite HALL; apply in_or_app; left; exact Hfr).
  assert (Hin' : In (den rho' e) (vm_maps V')) by (rewrite Hmaps'; apply in_map; exact He').
  destruct Hfacts' as (_ & _ & _ & _ & Htop & _ & Hpw & _). pose proof (proj1 (Forall_forall _ _) Htop _ Hin') as [_ Hhi'0].
  destruct (CXS.co_isp _ _ _ _ _ _ _ _ _ _ _ _ HCS) as [Eisp _].
  assert (Hat : alloc_top V' = ISP - 8388608) by (rewrite leaf_atop; unfold alloc_top, stack_max_size; rewrite Eisp; lia).
  unfold CXS.hid. apply orb_false_iff. split.
  - apply not_true_is_false. intros Ha. destruct (argH_high E1 x Ha) as [_ Hisp]. fold z in Hisp. lia.
  - apply negb_false_iff. unfold CXS.vis. cbv zeta. fold z.
    assert (Hm : CXS.in_ivs z (vm_maps V') = true) by (apply in_ivs_true; exists (den rho' e); split; [exact Hin' | exact Hx]).
    assert (Hn : CXS.in_ivs z (vm_noaccess V') = false).
    { apply not_true_is_false. intros Hna.
      pose proof (CXS.co_nasub _ _ _ _ _ _ _ _ _ _ _ _ HCS _ (leaf_na_mono _ Hna)) as Hm0.
      apply in_ivs_true in Hm0 as (p0 & Hp0 & Hz0). rewrite Hmaps0 in Hp0. apply in_map_iff in Hp0 as (e0 & <- & He0).
      rewrite Hmaps', HALL, map_app in Hpw.
      pose proof (pw_disj_app _ _ (den rho' e) (den rho' e0) Hpw (in_map _ _ _ Hfr) (in_map _ _ _ He0)) as Hd.
      rewrite (leaf_den0 e0 He0) in Hd. unfold e_disj in Hd. lia. }
    assert (Hal : CXS.in_allow A E1 END z = true).
    { unfold fresh_vis_chk in Hfv. rewrite forallb_forall in Hfv. pose proof (Hfv e Hfr) as Hck.
      apply andb_prop in Hck as [_ Hck]. destruct e as [[t off] len]. apply andb_prop in Hck as [Hoff Hex].
      apply Uint63.eqb_spec in Hoff. subst off. apply existsb_exists in Hex as (q & Hq & Hqc).
      destruct (snd q) as [l| | | | | | |] eqn:El; try discriminate.
      apply andb_prop in Hqc as [Hqc Hxm]. apply andb_prop in Hqc as [Hqc Q3]. apply andb_prop in Hqc as [Q1 Q2].
      apply Z.leb_le in Q1, Q3. apply Z.ltb_lt in Q2. pose proof (xt_match_sound _ _ Hxm) as Eub.
      assert (Eun : CXS.uE E1 (snd q) = l) by (unfold CXS.uE; rewrite El; cbn [AX2.edenot]; apply br_lit_small; lia).
      destruct (den0 t len) as [Dlo Dhi]. rewrite Dlo, Dhi in Hx.
      unfold CXS.in_allow. apply orb_true_iff. left. unfold CXS.in_vis. apply existsb_exists. exists q. split; [exact Hq|].
      rewrite Eub, Eun. apply andb_true_iff. split; [apply Z.leb_le | apply Z.ltb_lt]; lia. }
    rewrite Hm, Hn, Hal. cbn [negb andb]. rewrite !orb_true_r. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma zone_allow_visible (x : word) : zones_chk CS = true -> in_shadow (bv_unsigned x) ->
  CXS.in_allow A E1 END (bv_unsigned x) = true -> CXS.hid A argH E1 END m' x = false.
Proof.
  intros Hzc Hzone Hal. set (z := bv_unsigned x) in *.
  destruct (zones_facts segs A Lim SINV argH ISP FS0 E1 CS R FULL m HCS Hlx Hzc x Hzone) as (Hm0 & Hn0 & _).
  fold z in Hm0, Hn0.
  assert (Hm : CXS.in_ivs z (vm_maps V') = true) by exact (leaf_maps0_in _ Hm0).
  assert (Hn : CXS.in_ivs z (vm_noaccess V') = false).
  { apply not_true_is_false. intros Hna. rewrite (leaf_na_mono _ Hna) in Hn0. discriminate. }
  destruct (CXS.co_isp _ _ _ _ _ _ _ _ _ _ _ _ HCS) as [Eisp _].
  assert (Hat : alloc_top V' = ISP - 8388608) by (rewrite leaf_atop; unfold alloc_top, stack_max_size; rewrite Eisp; lia).
  unfold CXS.hid. apply orb_false_iff. split.
  - apply not_true_is_false. intros Ha. destruct (argH_high E1 x Ha) as [_ Hisp]. fold z in Hisp.
    apply in_ivs_true in Hm as (p' & Hp' & Hzp'). destruct Hfacts' as (_ & _ & _ & _ & Htop & _).
    pose proof (proj1 (Forall_forall _ _) Htop _ Hp') as [_ Hhi']. lia.
  - apply negb_false_iff. unfold CXS.vis. cbv zeta. fold z. rewrite Hm, Hn, Hal. cbn [negb andb]. rewrite !orb_true_r. reflexivity.
Qed.

Lemma xa_visible : zones_chk CS = true -> forallb xa_ent_chk XA = true ->
  forall x : word, xain (bv_unsigned x) = true -> CXS.hid A argH E1 END m' x = false.
Proof.
  intros Hzc Hxc x Hx. set (z := bv_unsigned x) in *.
  pose proof (xa_in_allow Hxc z Hx) as Hal.
  assert (Hzone : in_shadow z).
  { unfold xain in Hx. apply existsb_exists in Hx as ([[ts off] len] & Hf & Hzc').
    apply andb_prop in Hzc' as [Z1 Z2]. apply Z.leb_le in Z1. apply Z.ltb_lt in Z2.
    rewrite forallb_forall in Hxc. pose proof (Hxc _ Hf) as Hck. unfold xa_ent_chk in Hck.
    apply existsb_exists in Hck as (p & Hp & Hpc).
    pose proof (i63_range off) as Hoff. pose proof (i63_range len) as Hlen.
    destruct (xa_q_sound ts (to_Z off) (to_Z len) p ltac:(lia) ltac:(lia) Hpc) as (S1 & S2 & S3). apply S3. lia. }
  exact (zone_allow_visible x Hzc Hzone Hal).
Qed.

(* [comment removed for export] *)
Lemma leaf_fresh_shadow_visible : zones_chk CS = true -> avis3_chk = true -> fresh_vis_chk = true ->
  forall t len ts, In (t, 0%uint63, len) fresh -> In (ts, t) SHP ->
  forall (x : word) dd, 0 <= dd -> 8 * dd + 8 <= to_Z len -> bv_unsigned x = bv_unsigned (rho' ts) + dd ->
    CXS.hid A argH E1 END m' x = false.
Proof.
  intros Hzc Hav Hfv t len ts Hfr Hsp x dd Hd0 Hd8 Ex.
  pose proof (proj1 (Forall_forall _ _) Hshp _ Hsp) as Esh. cbn [fst snd] in Esh.
  unfold avis3_chk in Hav. apply andb_prop in Hav as [Hav _]. apply andb_prop in Hav as [Hav _]. apply andb_prop in Hav as [Hav _].
  apply andb_prop in Hav as [Hav _]. apply andb_prop in Hav as [_ Hsc].
  assert (He' : In (t, 0%uint63, len) ALL') by (rewrite HALL; apply in_or_app; left; exact Hfr).
  assert (Hin' : In (den rho' (t, 0%uint63, len)) (vm_maps V')) by (rewrite Hmaps'; apply in_map; exact He').
  pose proof Hfacts' as Hf. destruct Hf as (_ & _ & _ & Hpg & Htop & _ & Hpw & _).
  pose proof (proj1 (Forall_forall _ _) Htop _ Hin') as [Hlo0 Hhi'0].
  pose proof (proj1 (Forall_forall _ _) Hpg _ Hin') as [Hal4 _].
  destruct (den0 t len) as [Dlo Dhi]. rewrite Dlo in Hlo0, Hal4. rewrite Dhi in Hhi'0. unfold page_size in Hal4.
  destruct leaf_top as [_ Htm]. unfold CAP.TOPMAX in Htm.
  set (u := bv_unsigned (rho' t)) in *. set (y := u + 8 * dd).
  change (to_Z shadow_K) with 2147450880 in *.
  assert (Ez : bv_unsigned x = y / 8 + 2147450880).
  { rewrite Ex, Esh. unfold y. clear - Hal4 Hd0. Z.div_mod_to_equations. lia. }
  (* [comment removed for export] *)
  assert (Hside : y < span_lo \/ span_hi <= y).
  { destruct (Z_lt_dec y span_lo) as [?|Hge]; [left; assumption|]. right.
    destruct (Z_le_dec span_hi y) as [?|Hlt]; [assumption|]. exfalso.
    destruct (span_cover_sound _ _ _ _ Hsc y ltac:(lia)) as (q & Hq & Hyq).
    destruct (span_lit_in segs A Lim SINV argH ISP FS0 E1 CS R FULL m HCS Hlx q Hq) as (j & am & Hj & Esl & Hvj & Elo & Ehi).
    destruct (start_entry am (nth_error_In _ _ Hj)) as (e0 & He00 & _ & Ed & _).
    rewrite Hmaps', HALL, map_app in Hpw.
    pose proof (pw_disj_app _ _ (den rho' (t, 0%uint63, len)) (den rho' e0) Hpw (in_map _ _ _ Hfr) (in_map _ _ _ He00)) as Hdj.
    rewrite Ed in Hdj. unfold e_disj in Hdj. rewrite Dlo, Dhi, Elo, Ehi in Hdj. fold u in Hdj. unfold y in *. lia. }
  apply (zone_allow_visible x Hzc).
  - rewrite Ez. unfold in_shadow, lsh_lo, lsh_hi, hsh_lo, hsh_hi, span_lo, span_hi in *.
    assert (Hy0 : 0 <= y) by (unfold y; lia). assert (Hy47 : y < 140737488355328) by (unfold y; lia).
    destruct Hside as [Hs|Hs]; [left | right]; clear - Hs Hy0 Hy47; Z.div_mod_to_equations; lia.
  - (* [comment removed for export] *)
    unfold fresh_vis_chk in Hfv. rewrite forallb_forall in Hfv. pose proof (Hfv _ Hfr) as Hck.
    apply andb_prop in Hck as [_ Hck]. apply andb_prop in Hck as [_ Hex]. apply existsb_exists in Hex as (q & Hq & Hqc).
    destruct (snd q) as [l| | | | | | |] eqn:El; try discriminate.
    apply andb_prop in Hqc as [Hqc Hxm]. apply andb_prop in Hqc as [Hqc Q3]. apply andb_prop in Hqc as [Q1 Q2].
    apply Z.leb_le in Q1, Q3. apply Z.ltb_lt in Q2. pose proof (xt_match_sound _ _ Hxm) as Eub.
    assert (Eun : CXS.uE E1 (snd q) = l) by (unfold CXS.uE; rewrite El; cbn [AX2.edenot]; apply br_lit_small; lia).
    unfold CXS.in_allow. apply orb_true_iff. right. unfold CXS.in_sh. apply existsb_exists. exists q. split; [exact Hq|].
    unfold CXS.sh_lo, CXS.sh_hi. rewrite HshK, Eub, Eun, Ez. fold u. change (to_Z shadow_K) with 2147450880.
    assert (Hy8 : y + 8 <= u + l) by (unfold y; lia). assert (Hyu : u <= y) by (unfold y; lia).
    apply andb_true_iff. split; [apply Z.leb_le | apply Z.ltb_lt]; clear - Hy8 Hyu; Z.div_mod_to_equations; lia.
Qed.

(* [comment removed for export] *)
Hypothesis SINV_frame : forall E M M', (forall a, argH E a = true -> M' a = M a) -> SINV E M -> SINV E M'.
Hypothesis Hhi' : forall x : word, argH E1 x = true -> FULL' x = FULL x.

Definition model3_chk : bool := ledger3_chk && same3_chk && abytes3_chk && allow3_chk && zero3_chk.

Theorem leaf_cs_ok (R' : bvmap 5 word) :
  model3_chk = true ->
  AX2S.regs_ok E1 (AX2.s_regs (CAP.a_ss END)) R' ->
  AX2.s_log (CAP.a_ss END) = [] ->
  AX2S.know_ok segs E1 (CXS.Mr A argH E1 END m' FULL') (CAP.kn END) ->
  CXS.cs_ok segs A Lim SINV argH ISP FS0 E1 END R' FULL' m'.
Proof.
  unfold model3_chk. intros Hc Hregs Hlog Hknow.
  apply andb_prop in Hc as [Hc Hz]. apply andb_prop in Hc as [Hc Hal]. apply andb_prop in Hc as [Hc Hab].
  apply andb_prop in Hc as [_ _].
  constructor.
  - exact Hregs.
  - exact Hlog.
  - exact Hknow.
  - exact Hhalt'.
  - exact leaf_fds.
  - exact leaf_fs.
  - exact leaf_tid.
  - exact (proj1 Hfacts').
  - exact Hlim'.
  - exact leaf_maps.
  - apply leaf_holes.
  - exact leaf_seps.
  - exact leaf_wf.
  - exact leaf_bounds.
  - exact leaf_lazyb.
  - exact leaf_nasub.
  - exact leaf_none.
  - exact leaf_kinds.
  - exact leaf_totsz.
  - exact I.
  - exact leaf_brk.
  - exact leaf_sbrk.
  - exact leaf_eager.
  - exact (leaf_abytes Hab).
  - exact (leaf_minv Hab Hal).
  - refine (leaf_zero _ Hz). unfold allow3_chk in Hal. apply andb_prop in Hal as [Hal _]. apply andb_prop in Hal as [_ Hxa]. exact Hxa.
  - exact (SINV_frame E1 FULL FULL' Hhi' (CXS.co_sinv _ _ _ _ _ _ _ _ _ _ _ _ HCS)).
  - exact leaf_isp.
  - exact leaf_top.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Variable XV : list (int * nat).           (* [comment removed for export] *)
Hypothesis HXV : Forall (fun p => bv_unsigned (AX2.ev E1 (snd p)) = bv_unsigned (rho' (fst p)) / 4096) XV.


Definition side_am (a : AX2.saddr) (nn : AX2.expr) : CAP.amap := CAP.AM (AX2.a_base a) nn CAP.KRW.

Fixpoint find_idx (a : AX2.saddr) (nn : AX2.expr) (es : list fent) (i : nat) : option (nat * fent) :=
  match es with
  | [] => None
  | e :: r => if ent_chkX XT (side_am a nn) e then Some (i, e) else find_idx a nn r (Datatypes.S i)
  end.

Lemma find_idx_sound a nn : forall es i k e, find_idx a nn es i = Some (k, e) ->
  exists k0, k = (i + k0)%nat /\ nth_error es k0 = Some e /\ ent_chkX XT (side_am a nn) e = true.
Proof.
  induction es as [|e0 r IH]; intros i k e Hf; cbn [find_idx] in Hf; [discriminate|].
  destruct (ent_chkX XT (side_am a nn) e0) eqn:Ec.
  - injection Hf as <- <-. exists O. split; [lia|]. split; [reflexivity | exact Ec].
  - destruct (IH _ _ _ Hf) as (k0 & -> & Hn & Hc). exists (Datatypes.S k0). split; [lia|]. split; [exact Hn | exact Hc].
Qed.

(* [comment removed for export] *)
Definition side_ent (a : AX2.saddr) (nn : AX2.expr) : option (nat * fent) :=
  if (AX2.a_off a =? 0) then find_idx a nn ALL' O else None.

Lemma side_den a nn e : AX2.a_off a = 0 -> ent_chkX XT (side_am a nn) e = true ->
  AX2S.estart E1 a = e_lo (den rho' e) /\ AX2S.elenZ E1 nn = e_sz (den rho' e).
Proof.
  intros Ho Hc. pose proof (ent_chkX_den _ _ Hc) as Hd. unfold CXS.amap_den, side_am in Hd. cbn [CAP.am_base CAP.am_len] in Hd.
  unfold AX2S.estart, AX2S.elenZ, e_lo, e_sz. rewrite <- Hd, Ho. cbn [fst snd]. split; lia.
Qed.

Lemma side_ent_sound a nn k e : side_ent a nn = Some (k, e) ->
  nth_error (vm_maps V') k = Some (den rho' e) /\ In e ALL'
  /\ AX2S.estart E1 a = e_lo (den rho' e) /\ AX2S.elenZ E1 nn = e_sz (den rho' e).
Proof.
  unfold side_ent. destruct (AX2.a_off a =? 0) eqn:Eo; [|discriminate]. apply Z.eqb_eq in Eo. intros Hf.
  destruct (find_idx_sound a nn _ _ _ _ Hf) as (k0 & -> & Hn & Hc). cbn [Nat.add].
  split; [rewrite Hmaps'; exact (map_nth_error (den rho') _ _ Hn)|]. split; [exact (nth_error_In _ _ Hn)|].
  exact (side_den a nn e Eo Hc).
Qed.

(* [comment removed for export] *)
Definition is_grantop (o : vop) : bool := match fst o with OpGrant | OpLazy => true | _ => false end.

Definition side_dead (a : AX2.saddr) (nn : AX2.expr) : option fent :=
  if (AX2.a_off a =? 0) then
    match List.find (fun o : vop => is_grantop o && ent_chkX XT (side_am a nn) (snd o)) ops with
    | Some o => Some (snd o)
    | None => None
    end
  else None.

Lemma grantop_ok o : In o ops -> is_grantop o = true ->
  (forall e', In e' ALL' -> to_Z (fent_tag e') < to_Z (fent_tag (snd o)) -> e_disj (den rho' e') (den rho' (snd o)))
  /\ e_hi (den rho' (snd o)) <= alloc_top V'.
Proof.
  intros Hin Hg. pose proof (proj1 (Forall_forall _ _) Hops o Hin) as Hok. unfold op_ok in Hok. unfold is_grantop in Hg.
  destruct (fst o); try discriminate; destruct Hok as (_ & H1 & H2); split; assumption.
Qed.

Lemma side_dead_sound a nn e : side_dead a nn = Some e ->
  (forall e', In e' ALL' -> to_Z (fent_tag e') < to_Z (fent_tag e) -> e_disj (den rho' e') (den rho' e))
  /\ e_hi (den rho' e) <= alloc_top V'
  /\ AX2S.estart E1 a = e_lo (den rho' e) /\ AX2S.elenZ E1 nn = e_sz (den rho' e).
Proof.
  unfold side_dead. destruct (AX2.a_off a =? 0) eqn:Eo; [|discriminate]. apply Z.eqb_eq in Eo.
  destruct (List.find _ ops) as [o|] eqn:Ef; [|discriminate]. intros Hq. injection Hq as <-.
  destruct (List.find_some _ _ Ef) as [Hin Hp]. apply andb_prop in Hp as [Hg Hc].
  destruct (grantop_ok o Hin Hg) as [H1 H2]. split; [exact H1|]. split; [exact H2|]. exact (side_den a nn _ Eo Hc).
Qed.

(* [comment removed for export] *)
Definition side_lit (a : AX2.saddr) (nn : AX2.expr) : option (Z * Z) :=
  match AX2.a_base a, nn with
  | AX2.ELit b, AX2.ELit l =>
      if (0 <=? b) && (b <? 2 ^ 64) && (0 <=? l) && (l <? 2 ^ 64) then Some (b + AX2.a_off a, b + AX2.a_off a + l) else None
  | _, _ => None
  end.

Lemma side_lit_sound a nn lo hi : side_lit a nn = Some (lo, hi) ->
  AX2S.estart E1 a = lo /\ AX2S.estart E1 a + AX2S.elenZ E1 nn = hi.
Proof.
  unfold side_lit. destruct (AX2.a_base a) as [b| | | | | | |] eqn:Eb; try discriminate.
  destruct nn as [l| | | | | | |]; try discriminate.
  destruct ((0 <=? b) && (b <? 2 ^ 64) && (0 <=? l) && (l <? 2 ^ 64)) eqn:Ec; [|discriminate].
  apply andb_prop in Ec as [Ec H4]. apply andb_prop in Ec as [Ec H3]. apply andb_prop in Ec as [H1 H2].
  apply Z.leb_le in H1, H3. apply Z.ltb_lt in H2, H4. intros Hq. injection Hq as <- <-.
  unfold AX2S.estart, AX2S.elenZ. rewrite Eb. cbn [AX2.edenot]. rewrite !br_lit_small by lia. split; reflexivity.
Qed.

(* [comment removed for export] *)
Definition lit_ivs' : list (Z * Z) :=
  flat_map (fun e : fent => let '(t, off, len) := e in if (t =? 0)%uint63 then [(to_Z off, to_Z off + to_Z len)] else []) ALL'.

Lemma lit_cov_sound lo hi : coverZ lit_ivs' (Datatypes.S (length ALL')) lo hi = true ->
  forall x, lo <= x < hi -> exists e', In e' ALL' /\ fent_tag e' = 0%uint63 /\ e_lo (den rho' e') <= x < e_hi (den rho' e').
Proof.
  intros Hcov x Hx. destruct (coverZ_sound _ _ _ _ Hcov x Hx) as (q & Hq & Hxq).
  unfold lit_ivs' in Hq. apply in_flat_map in Hq as ([[t off] len] & He & Hq).
  destruct (t =? 0)%uint63 eqn:Et; [|destruct Hq]. destruct Hq as [<-|[]]. apply Uint63.eqb_spec in Et. subst t.
  exists (0%uint63, off, len). split; [exact He|]. split; [reflexivity|]. cbn [fst snd] in Hxq.
  pose proof (i63_range off) as Hoff. pose proof (i63_range len) as Hlen.
  unfold e_hi, e_lo. rewrite (e_sz_den rho' (0%uint63, off, len)). cbn [den fst snd].
  rewrite (adr0_lit rho' _ Hrho0'), (br_lit_small (to_Z off)) by lia. exact Hxq.
Qed.

(* [comment removed for export] *)
Lemma ivs_apart lo1 hi1 lo2 hi2 : lo1 < hi1 -> lo2 < hi2 ->
  (forall x, lo1 <= x < hi1 -> ~ (lo2 <= x < hi2)) -> hi1 <= lo2 \/ hi2 <= lo1.
Proof.
  intros H1 H2 Hno. destruct (Z_le_gt_dec hi1 lo2) as [Ha|Ha]; [left; exact Ha|].
  destruct (Z_le_gt_dec hi2 lo1) as [Hb|Hb]; [right; exact Hb|]. exfalso.
  apply (Hno (Z.max lo1 lo2)); lia.
Qed.

(* [comment removed for export] *)
Definition side_top (a : AX2.saddr) : bool :=
  let kn := CAP.kn CS in
  CAP.xinsideJ kn (AX2.a_base a) (AX2.a_off a) (AX2.ELit 1) CAP.e_spw (-8388608) (AX2.ELit (2 ^ 62))
  ||| ((12 <=? AX2.ealign kn (AX2.a_base a)) && (AX2.a_off a mod 4096 =? 0)
       &&& CAP.xinsideJ kn (AX2.a_base a) (AX2.a_off a) (AX2.ELit 1) CAP.e_spw (-8392703) (AX2.ELit (2 ^ 62))).

Lemma side_top_sound a g : side_top a = true -> g <= alloc_top V' -> g mod 4096 = 0 -> g <= AX2S.estart E1 a.
Proof.
  intros Hc Hg Hal. rewrite leaf_atop in Hg.
  destruct (CXS.co_isp _ _ _ _ _ _ _ _ _ _ _ _ HCS) as [Hi1 Hi2].
  assert (Eat : alloc_top V = bv_unsigned (AX2.edenot E1 CAP.e_spw) - 8388608).
  { unfold alloc_top, stack_max_size. rewrite Hi1, <- Hi2. reflexivity. }
  pose proof (CXS.co_know _ _ _ _ _ _ _ _ _ _ _ _ HCS) as Hkn.
  unfold side_top in Hc. apply orb_prop in Hc as [Hc|Hc].
  - destruct (CXS.xinsideJ_sound segs E1 _ (CAP.kn CS) _ _ _ _ _ _ Hkn Hc) as [X1 _].
    unfold AX2S.estart in *. cbn [AX2.a_base AX2.a_off] in X1. lia.
  - apply andb_prop in Hc as [Hc Hx]. apply andb_prop in Hc as [Ha Ho]. apply Z.leb_le in Ha. apply Z.eqb_eq in Ho.
    destruct (CXS.xinsideJ_sound segs E1 _ (CAP.kn CS) _ _ _ _ _ _ Hkn Hx) as [X1 _].
    destruct (AX2S.ealign_sound segs E1 _ (CAP.kn CS) (AX2.a_base a) Hkn) as [Hr Hdiv].
    assert (Hd12 : (2 ^ 12 | bv_unsigned (AX2.edenot E1 (AX2.a_base a)))).
    { apply (Z.divide_trans _ (2 ^ AX2.ealign (CAP.kn CS) (AX2.a_base a))); [|exact Hdiv].
      exists (2 ^ (AX2.ealign (CAP.kn CS) (AX2.a_base a) - 12)). rewrite <- Z.pow_add_r by lia. f_equal. lia. }
    destruct Hd12 as [q Hq]. change (2 ^ 12) with 4096 in Hq.
    unfold AX2S.estart in *. cbn [AX2.a_base AX2.a_off] in X1.
    rewrite Hq in *. clear - X1 Eat Hg Hal Ho. Z.div_mod_to_equations. lia.
Qed.

(* [comment removed for export] *)
Lemma live_facts e : In e ALL' ->
  0 < e_lo (den rho' e) /\ 0 < e_sz (den rho' e)
  /\ e_lo (den rho' e) mod 4096 = 0 /\ e_sz (den rho' e) mod 4096 = 0
  /\ e_hi (den rho' e) <= alloc_top V'
  /\ (e_hi (den rho' e) <= CAP.img_lo A \/ CAP.img_hi A <= e_lo (den rho' e)).
Proof.
  intros He. assert (Hp : In (den rho' e) (vm_maps V')) by (rewrite Hmaps'; apply in_map; exact He).
  destruct Hfacts' as (_ & _ & Hpos & Hal & Htop & _).
  pose proof (proj1 (Forall_forall _ _) Hpos _ Hp) as H1.
  pose proof (proj1 (Forall_forall _ _) Hal _ Hp) as [H2 H3].
  pose proof (proj1 (Forall_forall _ _) Htop _ Hp) as [H4 H5].
  pose proof (proj1 (Forall_forall _ _) leaf_bounds _ Hp) as (_ & _ & _ & H6 & _).
  unfold page_size in *. unfold e_hi, e_lo, e_sz in *. repeat split; try assumption.
Qed.

(* [comment removed for export] *)
Definition disj_rule (a1 : AX2.saddr) (n1 : AX2.expr) (a2 : AX2.saddr) (n2 : AX2.expr) : bool :=
  match side_ent a2 n2 with
  | Some (j, e2) =>
      match side_ent a1 n1 with Some (i, _) => negb (Nat.eqb i j) | None => false end
      ||| match side_lit a1 n1 with
          | Some (lo, hi) =>
              (lo <? hi)
              && (((CAP.img_lo A <=? lo) && (hi <=? CAP.img_hi A))
                  || (negb (fent_tag e2 =? 0)%uint63 && coverZ lit_ivs' (Datatypes.S (length ALL')) lo hi))
          | None => false
          end
      ||| side_top a1
  | None =>
      match side_dead a2 n2 with
      | Some e2 =>
          (0 <? to_Z (fent_tag e2)) && (0 <? to_Z (snd e2))
          && match side_lit a1 n1 with
             | Some (lo, hi) => (lo <? hi) && coverZ lit_ivs' (Datatypes.S (length ALL')) lo hi
             | None => false
             end
      | None => false
      end
  end.

Lemma disj_rule_sound a1 n1 a2 n2 : disj_rule a1 n1 a2 n2 = true ->
  AX2S.estart E1 a1 + AX2S.elenZ E1 n1 <= AX2S.estart E1 a2 \/ AX2S.estart E1 a2 + AX2S.elenZ E1 n2 <= AX2S.estart E1 a1.
Proof.
  unfold disj_rule. intros Hc.
  destruct (side_ent a2 n2) as [[j e2]|] eqn:E2.
  - destruct (side_ent_sound _ _ _ _ E2) as (Hn2 & Hin2 & Hs2 & Hl2).
    destruct (live_facts e2 Hin2) as (F1 & F2 & F3 & F4 & F5 & F6). unfold e_hi in *.
    apply orb_prop in Hc as [Hc|Htop]; [apply orb_prop in Hc as [Hc|Hc]|].
    + destruct (side_ent a1 n1) as [[i e1]|] eqn:E1'; [|discriminate].
      destruct (side_ent_sound _ _ _ _ E1') as (Hn1 & _ & Hs1 & Hl1).
      apply negb_true_iff in Hc. apply Nat.eqb_neq in Hc.
      destruct Hfacts' as (_ & _ & _ & _ & _ & _ & Hpw & _).
      pose proof (pw_disj_nth _ _ _ _ _ Hpw Hc Hn1 Hn2) as Hd. unfold e_disj, e_hi in Hd. lia.
    + destruct (side_lit a1 n1) as [[lo hi]|] eqn:El; [|discriminate].
      destruct (side_lit_sound _ _ _ _ El) as [L1 L2]. apply andb_prop in Hc as [Hlt Hc]. apply Z.ltb_lt in Hlt.
      apply orb_prop in Hc as [Hc|Hc].
      * apply andb_prop in Hc as [H1 H2]. apply Z.leb_le in H1, H2. lia.
      * apply andb_prop in Hc as [Ht Hcov]. apply negb_true_iff in Ht.
        assert (Hno : forall x, lo <= x < hi -> ~ (e_lo (den rho' e2) <= x < e_lo (den rho' e2) + e_sz (den rho' e2))).
        { intros x Hx Hx2. destruct (lit_cov_sound lo hi Hcov x Hx) as (e' & He' & Ht' & Hxe').
          destruct (In_nth_error _ _ He') as [i Hi].
          assert (Hij : i <> j).
          { intros ->. rewrite Hmaps' in Hn2. pose proof (map_nth_error (den rho') _ _ Hi) as Hi'.
            assert (Hee : nth_error ALL' j = Some e2).
            { unfold side_ent in E2. destruct (AX2.a_off a2 =? 0); [|discriminate].
              destruct (find_idx_sound _ _ _ _ _ _ E2) as (k0 & Ek & Hk & _). cbn [Nat.add] in Ek. subst k0. exact Hk. }
            rewrite Hi in Hee. injection Hee as <-. rewrite Ht' in Ht. rewrite Uint63.eqb_refl in Ht. discriminate. }
          destruct Hfacts' as (_ & _ & _ & _ & _ & _ & Hpw & _).
          pose proof (pw_disj_nth _ _ _ _ _ Hpw Hij (eq_ind_r (fun l => nth_error l i = _) (map_nth_error (den rho') _ _ Hi) Hmaps') Hn2) as Hd.
          unfold e_disj, e_hi in Hd, Hxe'. lia. }
        destruct (ivs_apart lo hi (e_lo (den rho' e2)) (e_lo (den rho' e2) + e_sz (den rho' e2)) Hlt ltac:(lia) Hno) as [Hd|Hd]; lia.
    + pose proof (side_top_sound a1 (e_lo (den rho' e2) + e_sz (den rho' e2)) Htop F5
                    ltac:(clear - F3 F4; Z.div_mod_to_equations; lia)) as Hd. lia.
  - destruct (side_dead a2 n2) as [e2|] eqn:E2d; [|discriminate].
    destruct (side_dead_sound _ _ _ E2d) as (Hold & _ & Hs2 & Hl2).
    apply andb_prop in Hc as [Hc Hl]. apply andb_prop in Hc as [Ht Hsz]. apply Z.ltb_lt in Ht, Hsz.
    destruct (side_lit a1 n1) as [[lo hi]|] eqn:El; [|discriminate].
    destruct (side_lit_sound _ _ _ _ El) as [L1 L2]. apply andb_prop in Hl as [Hlt Hcov]. apply Z.ltb_lt in Hlt.
    assert (Hsz2 : 0 < e_sz (den rho' e2)) by (rewrite e_sz_den; exact Hsz).
    assert (Hno : forall x, lo <= x < hi -> ~ (e_lo (den rho' e2) <= x < e_lo (den rho' e2) + e_sz (den rho' e2))).
    { intros x Hx Hx2. destruct (lit_cov_sound lo hi Hcov x Hx) as (e' & He' & Ht' & Hxe').
      pose proof (Hold e' He' ltac:(rewrite Ht'; change (to_Z 0%uint63) with 0; exact Ht)) as Hd.
      unfold e_disj, e_hi in Hd, Hxe'. lia. }
    destruct (ivs_apart lo hi (e_lo (den rho' e2)) (e_lo (den rho' e2) + e_sz (den rho' e2)) Hlt ltac:(lia) Hno) as [Hd|Hd]; lia.
Qed.

(* [comment removed for export] *)
Definition range_rule (v : nat) (lo hi : Z) : bool :=
  match List.find (fun p : int * nat => Nat.eqb (snd p) v) XV with
  | Some (t, _) =>
      match List.find (fun e : fent => (fent_tag e =? t)%uint63) ALL' with
      | Some (_, off, len) =>
          (off =? 0)%uint63 && ((lo <=? 1) || ((CAP.img_lo A <=? to_Z len) && (lo <=? CAP.img_hi A / 4096)))
          && ((CAP.TOPMAX - to_Z len) / 4096 <=? hi)
      | None =>
          match List.find (fun o : vop => is_grantop o && (fent_tag (snd o) =? t)%uint63) ops with
          | Some (_, (_, off, len)) => (off =? 0)%uint63 && (lo <=? 0) && ((CAP.TOPMAX - to_Z len) / 4096 <=? hi)
          | None => false
          end
      end
  | None => false
  end.

Lemma adr_0 (r : int -> word) t : adr r t 0 = r t.
Proof. unfold adr. apply bv_eq. rewrite bv_add_unsigned. change (bv_unsigned (Z_to_bv 64 0)) with 0. rewrite Z.add_0_r.
  apply bv_wrap_small. exact (br_u64 (r t)). Qed.

Lemma range_rule_sound v lo hi : range_rule v lo hi = true ->
  lo <= bv_unsigned (AX2.ev E1 v) <= hi.
Proof.
  unfold range_rule. destruct (List.find _ XV) as [[t v']|] eqn:Ef; [|discriminate].
  destruct (List.find_some _ _ Ef) as [Hin Hv]. apply Nat.eqb_eq in Hv. cbn [snd] in Hv. subst v'.
  pose proof (proj1 (Forall_forall _ _) HXV _ Hin) as Hev. cbn [fst snd] in Hev. rewrite Hev.
  pose proof (CXS.co_top _ _ _ _ _ _ _ _ _ _ _ _ HCS) as [_ Htm]. rewrite <- leaf_atop in Htm.
  destruct (List.find (fun e : fent => (fent_tag e =? t)%uint63) ALL') as [[[t1 off] len]|] eqn:Ee.
  - destruct (List.find_some _ _ Ee) as [He Ht]. cbn [fent_tag fst] in Ht. apply Uint63.eqb_spec in Ht. subst t1.
    intros Hc. apply andb_prop in Hc as [Hc Hhi]. apply andb_prop in Hc as [Ho Hlo].
    apply Uint63.eqb_spec in Ho. subst off. apply Z.leb_le in Hhi.
    destruct (live_facts _ He) as (F1 & F2 & F3 & F4 & F5 & F6).
    unfold e_hi in F5, F6. rewrite (e_sz_den rho' (t, 0%uint63, len)) in F2, F4, F5, F6. cbn [snd] in F2, F4, F5, F6.
    unfold e_lo in F1, F3, F5, F6. cbn [den fst] in F1, F3, F5, F6. change (to_Z 0%uint63) with 0 in F1, F3, F5, F6.
    rewrite adr_0 in F1, F3, F5, F6.
    set (b := bv_unsigned (rho' t)) in *.
    split.
    + apply orb_prop in Hlo as [Hlo|Hlo]; [apply Z.leb_le in Hlo | apply andb_prop in Hlo as [Hl1 Hl2]; apply Z.leb_le in Hl1, Hl2].
      * assert (1 <= b / 4096) by (clear - F1 F3; Z.div_mod_to_equations; lia). lia.
      * assert (CAP.img_hi A <= b) by lia.
        pose proof (Z.div_le_mono (CAP.img_hi A) b 4096 ltac:(lia) H) as Hd. lia.
    + pose proof (Z.div_le_mono b (CAP.TOPMAX - to_Z len) 4096 ltac:(lia) ltac:(lia)) as Hd. lia.
  - destruct (List.find (fun o : vop => is_grantop o && (fent_tag (snd o) =? t)%uint63) ops) as [[k [[t1 off] len]]|] eqn:Eo; [|discriminate].
    destruct (List.find_some _ _ Eo) as [Hino Hp]. apply andb_prop in Hp as [Hg Ht]. cbn [snd fent_tag fst] in Ht.
    apply Uint63.eqb_spec in Ht. subst t1.
    intros Hc. apply andb_prop in Hc as [Hc Hhi]. apply andb_prop in Hc as [Ho Hlo].
    apply Uint63.eqb_spec in Ho. subst off. apply Z.leb_le in Hhi, Hlo.
    destruct (grantop_ok _ Hino Hg) as [_ Htop]. cbn [snd] in Htop.
    unfold e_hi in Htop. rewrite (e_sz_den rho' (t, 0%uint63, len)) in Htop. cbn [snd] in Htop.
    unfold e_lo in Htop. cbn [den fst] in Htop. change (to_Z 0%uint63) with 0 in Htop. rewrite adr_0 in Htop.
    pose proof (br_u64 (rho' t)) as Hu. set (b := bv_unsigned (rho' t)) in *.
    split.
    + assert (0 <= b / 4096) by (apply Z.div_pos; lia). lia.
    + pose proof (Z.div_le_mono b (CAP.TOPMAX - to_Z len) 4096 ltac:(lia) ltac:(lia)) as Hd. lia.
Qed.

Definition pure3_chk (K : AX2.kentry) : bool :=
  match K with
  | AX2.KDisj a1 n1 a2 n2 => disj_rule a1 n1 a2 n2 ||| disj_rule a2 n2 a1 n1
  | AX2.KRange (AX2.EVar v) lo hi => range_rule v lo hi
  | _ => false
  end.

Theorem pure3_sound K (M : word -> option byte) : pure3_chk K = true -> AX2S.kentry_ok segs E1 M K.
Proof.
  destruct K as [a w v | a nn | a nn j | lo hi | e m0 | e lo hi | a nn | a1 n1 a2 n2 | a nn c | a nn];
    cbn [pure3_chk]; try discriminate.
  - destruct e as [z|v| | | | | |]; try discriminate. intros Hc. cbn [AX2S.kentry_ok AX2.edenot].
    exact (range_rule_sound v lo hi Hc).
  - intros Hc. cbn [AX2S.kentry_ok]. apply orb_prop in Hc as [Hc|Hc].
    + exact (disj_rule_sound _ _ _ _ Hc).
    + destruct (disj_rule_sound _ _ _ _ Hc) as [Hd|Hd]; [right | left]; exact Hd.
Qed.

End LeafModel.
