(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Uint63 PrimString.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType RiscvSemantics State Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Mmap Mprotect.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Common.Cfg Require Import
  ShapeAlgBase ShapeCfg NodesCfg LedgerCfg AllocCfg LazyCfg LazyAccCfg AllocLazyCfg EagerCfg CountCfg.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Common.FX Require Import
  W64 ITrie FxSpec FxInstr FxState FxMem FxExec FxRel FxMemSound FxValSound FxStepSound FxStepMain FxRun FxRn
  FxLazy FxSys FxDrive FxCellFrame.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition BIG : Z := 2 ^ 62.
Definition erase_vm (wb : word) (h : VmMaps) : VmMaps :=
  mkVmMapsFull (vm_reserved h) (vm_maps h) [] wb wb BIG (vm_mmap_base h) (vm_init_sp h).
Definition erase (wb : word) (m : Model) : Model :=
  mkModelOf (m_fd m) (mkVmState (erase_vm wb (m_vmmaps m)) [] [])
            (m_io m) (m_fsys m) (m_proc m) (m_lim m) (m_time m).

Lemma erase_vmmaps wb m : m_vmmaps (erase wb m) = erase_vm wb (m_vmmaps m).
Proof. reflexivity. Qed.
Lemma erase_halted wb m : m_halted (erase wb m) = m_halted m.
Proof. reflexivity. Qed.
Lemma erase_nolazy wb m : model_nolazy (erase wb m).
Proof. split; reflexivity. Qed.
Lemma erase_lazy_frame wb m m' : lazy_frame m m' -> erase wb m' = erase wb m.
Proof. intros [mat' ->]. reflexivity. Qed.
Lemma erase_same_but_vm wb m : same_but_vm (erase wb m) m.
Proof. repeat split; reflexivity. Qed.
Lemma same_but_vm_erase wb m : same_but_vm m (erase wb m).
Proof. repeat split; reflexivity. Qed.
Lemma lazy_frame_same_but_vm m m' : lazy_frame m m' -> same_but_vm m m'.
Proof. intros [mat' ->]. repeat split; reflexivity. Qed.
Lemma same_but_vm_sym m m' : same_but_vm m m' -> same_but_vm m' m.
Proof. intros (A1 & A2 & A3 & A4 & A5 & A6). repeat split; congruence. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition pg_dn (z : Z) : Z := z / 4096 * 4096.
Definition pg_upZ (z : Z) : Z := (z + 4095) / 4096 * 4096.

(* [comment removed for export] *)
Definition denA (rho : int -> word) (e : fent) : Z * Z :=
  let '(t, off, len) := e in
  (pg_dn (bv_unsigned (rho t) + to_Z off), pg_upZ (bv_unsigned (rho t) + to_Z off + to_Z len)).

(* [comment removed for export] *)
Inductive opk : Set := OpCut | OpLazy | OpGrant | OpShadow | OpCommit.
Definition vop : Type := (opk * fent)%type.

Record fledger3 : Type := FL3 {
  fl3       : fledger;      (* [comment removed for export] *)
  fl_all    : list fent;    (* [comment removed for export] *)
  fl_ops    : list vop;     (* [comment removed for export] *)
  fl_lazy   : list fent;    (* [comment removed for export] *)
  fl_allow  : list fent;    (* [comment removed for export] *)
  fl_Ab     : Z;            (* [comment removed for export] *)
  fl_E      : Z;            (* [comment removed for export] *)
  fl_ex     : list fent;    (* [comment removed for export] *)
  fl_ord    : list (int * int * Z);  (* [comment removed for export] *)
  fl_res    : list (int * Z * Z)     (* [comment removed for export] *)
}.

(* [comment removed for export] *)
Definition res_ok (n : int) (rho : int -> word) (o : int * Z * Z) : Prop :=
  to_Z (fst (fst o)) < to_Z n /\ 0 < snd (fst o) /\ bv_unsigned (rho (fst (fst o))) mod snd (fst o) = snd o.

Lemma ress_ok_ext n rho n' rho' l :
  to_Z n <= to_Z n' -> (forall t, to_Z t < to_Z n -> rho' t = rho t) -> Forall (res_ok n rho) l -> Forall (res_ok n' rho') l.
Proof.
  intros Hn Hrho H. eapply Forall_impl; [|exact H]. intros o (H1 & H2 & H3).
  split; [lia|]. split; [exact H2|]. rewrite (Hrho _ H1). exact H3.
Qed.

(* [comment removed for export] *)
Definition ord_ok (n : int) (rho : int -> word) (o : int * int * Z) : Prop :=
  to_Z (fst (fst o)) < to_Z n /\ to_Z (snd (fst o)) < to_Z n
  /\ bv_unsigned (rho (fst (fst o))) + snd o <= bv_unsigned (rho (snd (fst o))).

Lemma ord_ok_ext n rho n' rho' o :
  to_Z n <= to_Z n' -> (forall t, to_Z t < to_Z n -> rho' t = rho t) -> ord_ok n rho o -> ord_ok n' rho' o.
Proof.
  intros Hn Hrho (H1 & H2 & H3). split; [lia|]. split; [lia|]. rewrite (Hrho _ H1), (Hrho _ H2). exact H3.
Qed.

Lemma ords_ok_ext n rho n' rho' l :
  to_Z n <= to_Z n' -> (forall t, to_Z t < to_Z n -> rho' t = rho t) -> Forall (ord_ok n rho) l -> Forall (ord_ok n' rho') l.
Proof. intros Hn Hrho H. eapply Forall_impl; [|exact H]. intros o. apply ord_ok_ext; assumption. Qed.

Definition acct_ok (Lim : Z) (L3 : fledger3) : bool := (fl_E L3 + fl_Ab L3 <=? Lim)%Z.

(* [comment removed for export] *)
Definition na_step (rho : int -> word) (na : list (word * word)) (o : vop) : list (word * word) :=
  match fst o with
  | OpCut | OpCommit => maps_subtract na (e_lo (den rho (snd o))) (e_hi (den rho (snd o)))
  | _ => na
  end.
Definition lz_step (rho : int -> word) (lz : list (word * word)) (o : vop) : list (word * word) :=
  match fst o with
  | OpCut | OpCommit => maps_subtract lz (e_lo (den rho (snd o))) (e_hi (den rho (snd o)))
  | OpLazy => den rho (snd o) :: lz
  | _ => lz
  end.
Definition na_apply (rho : int -> word) (ops : list vop) (na0 : list (word * word)) : list (word * word) :=
  fold_left (na_step rho) ops na0.
Definition lz_apply (rho : int -> word) (ops : list vop) (lz0 : list (word * word)) : list (word * word) :=
  fold_left (lz_step rho) ops lz0.

Lemma na_apply_snoc rho ops o na0 : na_apply rho (ops ++ [o]) na0 = na_step rho (na_apply rho ops na0) o.
Proof. unfold na_apply. rewrite fold_left_app. reflexivity. Qed.
Lemma lz_apply_snoc rho ops o lz0 : lz_apply rho (ops ++ [o]) lz0 = lz_step rho (lz_apply rho ops lz0) o.
Proof. unfold lz_apply. rewrite fold_left_app. reflexivity. Qed.

Lemma ops_apply_ext rho rho' (ops : list vop) :
  (forall o, In o ops -> den rho' (snd o) = den rho (snd o)) ->
  (forall na0, na_apply rho' ops na0 = na_apply rho ops na0)
  /\ (forall lz0, lz_apply rho' ops lz0 = lz_apply rho ops lz0).
Proof.
  induction ops as [|o ops IH]; intros H; [split; reflexivity|].
  destruct (IH (fun o0 Ho0 => H o0 (or_intror Ho0))) as [IH1 IH2].
  pose proof (H o (or_introl eq_refl)) as Eo.
  assert (E1 : forall l, na_step rho' l o = na_step rho l o) by (intros l; unfold na_step; rewrite Eo; reflexivity).
  assert (E2 : forall l, lz_step rho' l o = lz_step rho l o) by (intros l; unfold lz_step; rewrite Eo; reflexivity).
  split; intros l0; cbn [na_apply lz_apply fold_left].
  - rewrite E1. apply IH1.
  - rewrite E2. apply IH2.
Qed.

(* [comment removed for export] *)
Definition span_lo : Z := 2147446784.            (* [comment removed for export] *)
Definition span_hi : Z := 17594333495296.        (* [comment removed for export] *)
Definition in_span (x : Z) : Prop := span_lo <= x < span_hi.

(* [comment removed for export] *)
Definition op_ok (rho : int -> word) (m : Model) (all : list fent) (o : vop) : Prop :=
  let e := snd o in
  let older := forall e', In e' all -> to_Z (fent_tag e') < to_Z (fent_tag e) -> e_disj (den rho e') (den rho e) in
  let top := e_hi (den rho e) <= alloc_top (m_vmmaps m) in
  match fst o with
  | OpGrant | OpLazy => bv_unsigned (rho (fent_tag e)) mod 4096 = 0 /\ older /\ top
  | OpCut => older /\ top
  | OpShadow =>
      0 < to_Z (fent_tag e)
      /\ bv_unsigned (rho (fent_tag e)) = bv_unsigned (rho (fent_tag e - 1)%uint63) / 8 + to_Z shadow_K
      /\ (forall x, e_lo (den rho e) <= x < e_hi (den rho e) -> span_lo <= x < span_hi)
  | OpCommit => True
  end.

Lemma op_ok_model rho m m' all o :
  alloc_top (m_vmmaps m') = alloc_top (m_vmmaps m) -> op_ok rho m all o -> op_ok rho m' all o.
Proof. intros E H. unfold op_ok in *. rewrite E. exact H. Qed.

(* [comment removed for export] *)
Lemma op_ok_ext (n : int) rho rho' m m' all all' o :
  (forall t, to_Z t < to_Z n -> rho' t = rho t) ->
  to_Z (fent_tag (snd o)) < to_Z n -> Forall (fun e => to_Z (fent_tag e) < to_Z n) all ->
  alloc_top (m_vmmaps m') = alloc_top (m_vmmaps m) ->
  (forall e', In e' all' -> to_Z (fent_tag e') < to_Z (fent_tag (snd o)) -> In e' all) ->
  op_ok rho m all o -> op_ok rho' m' all' o.
Proof.
  intros Hrho Ht Hall Etop Hsub H. destruct o as [k e]. cbn [snd fst] in *.
  assert (Hden : forall e0 : fent, to_Z (fent_tag e0) < to_Z n -> den rho' e0 = den rho e0).
  { intros [[t0 o0] l0] Ht0. cbn [fent_tag fst] in Ht0. cbn [den]. unfold adr. rewrite (Hrho t0 Ht0). reflexivity. }
  assert (Hold : (forall e', In e' all -> to_Z (fent_tag e') < to_Z (fent_tag e) -> e_disj (den rho e') (den rho e)) ->
                 forall e', In e' all' -> to_Z (fent_tag e') < to_Z (fent_tag e) -> e_disj (den rho' e') (den rho' e)).
  { intros Ho e' He' Hlt. rewrite (Hden e Ht), (Hden e') by lia. exact (Ho e' (Hsub e' He' Hlt) Hlt). }
  unfold op_ok in *. cbn [snd fst] in *. cbv zeta in *.
  destruct k.
  - destruct H as [H1 H2]. split; [exact (Hold H1)|]. rewrite (Hden e Ht), Etop. exact H2.
  - destruct H as (H0 & H1 & H2). split; [rewrite (Hrho _ Ht); exact H0|]. split; [exact (Hold H1)|].
    rewrite (Hden e Ht), Etop. exact H2.
  - destruct H as (H0 & H1 & H2). split; [rewrite (Hrho _ Ht); exact H0|]. split; [exact (Hold H1)|].
    rewrite (Hden e Ht), Etop. exact H2.
  - destruct H as (Hpos & H1 & H2). split; [exact Hpos|].
    assert (Hm1 : to_Z (fent_tag e - 1)%uint63 < to_Z n).
    { rewrite sub_spec, to_Z_1. pose proof (to_Z_bounded (fent_tag e)) as Hb.
      rewrite Z.mod_small by lia. lia. }
    split; [rewrite (Hrho _ Ht), (Hrho _ Hm1); exact H1|]. rewrite (Hden e Ht). exact H2.
  - exact I.
Qed.
(* [comment removed for export] *)
Definition lsh_lo : Z := 2147450880.             (* [comment removed for export] *)
Definition lsh_hi : Z := 2415882240.             (* [comment removed for export] *)
Definition hsh_lo : Z := 2201439137792.          (* [comment removed for export] *)
Definition hsh_hi : Z := 17594333495296.         (* [comment removed for export] *)
Definition in_shadow (x : Z) : Prop := lsh_lo <= x < lsh_hi \/ hsh_lo <= x < hsh_hi.

(* [comment removed for export] *)
Definition exempted (rho : int -> word) (l : list fent) (x : Z) : Prop :=
  exists e z, In e l /\ e_lo (den rho e) <= z < e_hi (den rho e) /\ x = z / 8 + to_Z shadow_K.

(* [comment removed for export] *)
Definition lazy_pw (rho : int -> word) (lazy : list (word * word)) (l : list fent) : Prop :=
  forall e (p : word), In e l -> bv_unsigned p mod 4096 = 0 ->
    e_lo (den rho e) <= bv_unsigned p -> bv_unsigned p + 4096 <= e_hi (den rho e) ->
    page_in_ranges p lazy = true.

(* [comment removed for export] *)
Definition mat_lazy (m : Model) : Prop :=
  Forall (fun p => page_in_ranges p (m_vm_lazy m) = true) (m_vm_materialized m).

(* [comment removed for export] *)
Definition touched (rho : int -> word) (ops : list vop) (x : Z) : Prop :=
  exists o, In o ops /\ e_lo (den rho (snd o)) <= x < e_hi (den rho (snd o)).

Lemma touched_app rho l1 l2 x : touched rho (l1 ++ l2) x <-> touched rho l1 x \/ touched rho l2 x.
Proof.
  split.
  - intros (o & Ho & Hx). apply in_app_iff in Ho as [Ho|Ho]; [left | right]; exists o; split; assumption.
  - intros [(o & Ho & Hx) | (o & Ho & Hx)]; exists o; (split; [apply in_app_iff|exact Hx]); [left | right]; exact Ho.
Qed.

Lemma touched_ext rho rho' ops x :
  (forall o, In o ops -> den rho' (snd o) = den rho (snd o)) -> touched rho ops x -> touched rho' ops x.
Proof. intros H (o & Ho & Hx). exists o. rewrite (H o Ho). split; assumption. Qed.

Lemma e_sz_den rho e : e_sz (den rho e) = to_Z (snd e).
Proof.
  destruct e as [[t off] len]. unfold e_sz. cbn [den snd]. apply u64_lit.
  pose proof (i63_range len). lia.
Qed.

(* [comment removed for export] *)
Definition ent_within (e e' : fent) : Prop :=
  fent_tag e' = fent_tag e
  /\ to_Z (snd (fst e')) <= to_Z (snd (fst e))
  /\ to_Z (snd (fst e)) + to_Z (snd e) <= to_Z (snd (fst e')) + to_Z (snd e').
Definition lazy_cov (all lazy : list fent) : Prop :=
  Forall (fun e => 0 < to_Z (snd e) /\ exists e', In e' all /\ ent_within e e') lazy.

Lemma lazy_cov_mono (all all' lazy : list fent) :
  (forall e', In e' all -> In e' all') -> lazy_cov all lazy -> lazy_cov all' lazy.
Proof.
  intros Hsub H. eapply Forall_impl; [|exact H]. intros e (Hp & e' & He' & Hw).
  split; [exact Hp|]. exists e'. split; [exact (Hsub e' He') | exact Hw].
Qed.

Lemma lazy_cov_tags (all lazy : list fent) (n : int) :
  lazy_cov all lazy -> Forall (fun e => to_Z (fent_tag e) < to_Z n) all ->
  Forall (fun e => to_Z (fent_tag e) < to_Z n) lazy.
Proof.
  intros H Ht. eapply Forall_impl; [|exact H]. intros e (_ & e' & He' & (Et & _)).
  cbv beta. rewrite <- Et. exact (proj1 (Forall_forall _ _) Ht e' He').
Qed.

Lemma ent_within_refl e : ent_within e e.
Proof. unfold ent_within. repeat split; lia. Qed.

Lemma den_within rho e e' :
  ent_within e e' -> e_hi (den rho e') < 2 ^ 64 -> e_inside (den rho e) (den rho e').
Proof.
  destruct e as [[t o] l], e' as [[t' o'] l']. unfold ent_within. cbn [fent_tag fst snd]. intros (-> & H1 & H2) Hhi.
  unfold e_inside, e_hi, e_lo, e_sz in *. cbn [den fst snd] in *.
  pose proof (i63_range o) as Ho. pose proof (i63_range l) as Hl. pose proof (i63_range o') as Ho'. pose proof (i63_range l') as Hl'.
  rewrite !(u64_lit (to_Z _)) in * by lia.
  unfold adr in *. rewrite !bv_add_unsigned in *. rewrite !(u64_lit (to_Z _)) in * by lia.
  unfold bv_wrap in *. change (bv_modulus 64) with (2 ^ 64) in *.
  set (R := bv_unsigned (rho t)) in *. pose proof (u64_range (rho t)) as HR. fold R in HR.
  assert (E : (R + to_Z o) mod 2 ^ 64 = (R + to_Z o') mod 2 ^ 64 + (to_Z o - to_Z o')).
  { replace (R + to_Z o) with ((R + to_Z o') + (to_Z o - to_Z o')) by lia.
    rewrite <- Z.add_mod_idemp_l by lia. apply Z.mod_small.
    pose proof (Z.mod_pos_bound (R + to_Z o') (2 ^ 64) ltac:(lia)). lia. }
  rewrite E. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section Kinds.
Variable IM : fimage.
Variable code : itrie finstr.

Definition same_kinds (M M' : itrie region) : Prop :=
  forall t, option_map rg_kind (iget t M') = option_map rg_kind (iget t M).

Lemma same_kinds_refl M : same_kinds M M.
Proof. intros t. reflexivity. Qed.
Lemma same_kinds_trans M1 M2 M3 : same_kinds M1 M2 -> same_kinds M2 M3 -> same_kinds M1 M3.
Proof. intros H12 H23 t. rewrite (H23 t). exact (H12 t). Qed.

Lemma fm_store_kinds M a sz v M' : fm_store IM M a sz v = Some M' -> same_kinds M M'.
Proof.
  destruct a as [t0 [top off]]. intros Hst t.
  destruct (fm_store_inv _ _ _ _ _ _ _ _ Hst) as (rg & p & Hrg & _ & _ & _ & _ & _ & ->).
  rewrite iget_iset. destruct (t =? t0)%uint63 eqn:E; [|reflexivity].
  apply Uint63.eqb_spec in E. subst t0. rewrite Hrg. reflexivity.
Qed.

Lemma fx_step_kinds F F' : fx_step IM code F = FNext F' -> same_kinds (f_mem F) (f_mem F').
Proof.
  intros H. destruct (fx_step_mem IM code F F' H) as [E | (a & sz & v & Hst)].
  - rewrite E. apply same_kinds_refl.
  - exact (fm_store_kinds _ _ _ _ _ Hst).
Qed.

Lemma fx_run_kinds : forall bp k F F' r cnt,
  fx_run IM code bp k F = (F', r, cnt) -> same_kinds (f_mem F) (f_mem F').
Proof.
  intros bp k. induction k as [|k IH]; intros F F' r cnt H; cbn [fx_run] in H.
  - destruct (f_pc F =? bp)%uint63; [injection H as <- _ _; apply same_kinds_refl|].
    destruct (fx_step IM code F) as [s'| |c] eqn:Es; injection H as <- _ _;
      [exact (fx_step_kinds _ _ Es) | apply same_kinds_refl | apply same_kinds_refl].
  - destruct (fx_run IM code bp k F) as [[s1 r1] n1] eqn:E1.
    destruct (stop_is_fuel r1).
    + destruct (fx_run IM code bp k s1) as [[s2 r2] n2] eqn:E2. injection H as <- _ _.
      exact (same_kinds_trans _ _ _ (IH _ _ _ _ E1) (IH _ _ _ _ E2)).
    + injection H as <- _ _. exact (IH _ _ _ _ E1).
Qed.
End Kinds.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma materialize_mat_lazy m l m' :
  materialize_model_accesses m l = Some m' -> mat_lazy m -> mat_lazy m'.
Proof.
  unfold materialize_model_accesses, materialize_accesses, mat_lazy. intros Hm Hl.
  set (new := newly_materialized_pages (m_vm_lazy m) (m_vm_materialized m) l) in *.
  assert (Hnew : forall p, In p new -> page_in_ranges p (m_vm_lazy m) = true).
  { intros p Hp. unfold new, newly_materialized_pages in Hp. apply List.filter_In in Hp as [_ Hb].
    apply andb_prop in Hb as [Hb _]. exact Hb. }
  destruct new as [|q qs] eqn:En.
  - injection Hm as <-. exact Hl.
  - destruct (vm_backing_used m + Z.of_nat (length (q :: qs)) * page_size <=? vm_limit (m_vmmaps m)); [|discriminate].
    injection Hm as <-.
    change (Forall (fun p => page_in_ranges p (m_vm_lazy m) = true) ((q :: qs) ++ m_vm_materialized m)).
    apply Forall_app. split; [apply Forall_forall; exact Hnew | exact Hl].
Qed.

Section MatLazy.
Variable segs : list Segment.

Lemma account_step_mat_lazy ms m ms' m' :
  mi_account_step segs ms m = MachineOk (ms', m') -> mat_lazy m -> mat_lazy m'.
Proof.
  unfold mi_account_step. intros Hs Hl.
  destruct (RiscvSemantics.step_accesses segs ms) as [report| |]; try discriminate.
  destruct (materialize_model_accesses m (accessed_ranges _ report)) as [m1|] eqn:Hm; [|discriminate].
  injection Hs as _ <-. exact (materialize_mat_lazy m _ m1 Hm Hl).
Qed.

Lemma asteps_mat_lazy : forall k ms m ms' m',
  asteps segs k (ms, m) = MachineOk (ms', m') -> mat_lazy m -> mat_lazy m'.
Proof.
  induction k as [|k IH]; intros ms m ms' m' Ha Hl; cbn [asteps fst snd] in Ha.
  - injection Ha as _ <-. exact Hl.
  - destruct (ms_svc_pending ms); [injection Ha as _ <-; exact Hl|].
    destruct (mi_account_step segs ms m) as [[ms1 m1]| |] eqn:Hs; try discriminate.
    exact (IH ms1 m1 ms' m' Ha (account_step_mat_lazy ms m ms1 m1 Hs Hl)).
Qed.
End MatLazy.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section LZB.
Variable segs : list Segment.
Variable IM : fimage.

(* [comment removed for export] *)
Definition region_lazy_ok (rho : int -> word) (lazy : list (word * word)) (A : list (Z * Z))
    (t : int) (rg : region) : Prop :=
  (forall r, In r lazy ->
     bv_unsigned (rho t) + to_Z (rg_len rg) <= bv_unsigned (fst r)
     \/ bv_unsigned (fst r) + bv_unsigned (snd r) <= bv_unsigned (rho t) + to_Z (rg_lo rg))
  \/ (exists iv, In iv A /\ fst iv mod 4096 = 0 /\ snd iv mod 4096 = 0
                 /\ fst iv <= bv_unsigned (rho t) + to_Z (rg_lo rg)
                 /\ bv_unsigned (rho t) + to_Z (rg_len rg) <= snd iv).

(* [comment removed for export] *)
Lemma LZ_region rho (lazy : list (word * word)) (A : list (Z * Z)) M mem t rg pn p x :
  mem_ok segs IM rho M mem -> iget t M = Some rg ->
  region_lazy_ok rho lazy A t rg ->
  to_Z pn < 2 ^ 50 -> page_at IM rg t pn = Some p -> 0 <= x < 4096 ->
  to_Z pn * 4096 + x < to_Z (rg_len rg) ->
  page_in_ranges (page_base_of (bv_unsigned (rho t) + to_Z pn * 4096 + x)) lazy = true ->
  page_allowedb A (page_base_of (bv_unsigned (rho t) + to_Z pn * 4096 + x)) = true.
Proof.
  intros [Hmem _] Hg Hcase Hpn Hp Hx Hhi Hlz.
  destruct (Hmem t rg Hg) as [Hreg Hpages]. destruct (Hpages pn p Hpn Hp) as (_ & Hlo & _).
  set (z := bv_unsigned (rho t) + to_Z pn * 4096 + x) in *.
  pose proof (u64_range (rho t)) as Hr. pose proof (i63_range pn) as Hpn0.
  assert (Hz0 : 0 <= z) by (unfold z; lia).
  assert (Hq : bv_unsigned (page_base_of z) = z / 4096 * 4096 /\ z / 4096 * 4096 <= z < z / 4096 * 4096 + 4096).
  { unfold page_base_of, page_size. split.
    - apply u64_lit. pose proof (region_ok_nowrap_lz rho t rg Hreg) as Hnw.
      assert (z < 2 ^ 63) by (unfold z; lia). clear - Hz0 H. Z.div_mod_to_equations. lia.
    - clear - Hz0. Z.div_mod_to_equations. lia. }
  destruct Hq as [Eq Hqz].
  destruct Hcase as [Hdisj | (iv & Hiv & Ha1 & Ha2 & Hb1 & Hb2)].
  - exfalso. unfold page_in_ranges in Hlz. apply existsb_exists in Hlz as (r & Hr' & Hb).
    apply andb_true_iff in Hb as [B1 B2]. apply Z.leb_le in B1, B2. unfold page_size in B2.
    rewrite Eq in B1, B2. destruct (Hdisj r Hr') as [Hd|Hd]; unfold z in *; lia.
  - unfold page_allowedb. apply existsb_exists. exists iv. split; [exact Hiv|].
    apply andb_true_iff. rewrite Eq. unfold page_size. split; apply Z.leb_le.
    + clear - Ha1 Hb1 Hlo Hqz Hx Hpn0 Hr. unfold z in *. Z.div_mod_to_equations. lia.
    + clear - Ha2 Hb2 Hhi Hqz Hx Hpn0 Hr. unfold z in *. Z.div_mod_to_equations. lia.
Qed.

(* [comment removed for export] *)
Lemma LZ_build rho rho' (lazy lazy' : list (word * word)) (A A' : list (Z * Z)) M M' mem' :
  mem_ok segs IM rho' M' mem' ->
  LZ IM rho lazy A M ->
  (forall pb, page_allowedb A pb = true -> page_allowedb A' pb = true) ->
  (forall t rg, iget t M' = Some rg ->
     region_lazy_ok rho' lazy' A' t rg
     \/ (iget t M = Some rg /\ rho' t = rho t
         /\ forall z, bv_unsigned (rho t) + to_Z (rg_lo rg) <= z < bv_unsigned (rho t) + to_Z (rg_len rg) ->
               page_in_ranges (page_base_of z) lazy' = true -> page_in_ranges (page_base_of z) lazy = true)) ->
  LZ IM rho' lazy' A' M'.
Proof.
  intros Hmem HLZ HA Hcases t rg pn p x Hg Hpn Hp Hx Hhi Hlz.
  destruct (Hcases t rg Hg) as [Hrl | (Hg0 & Er & Hl)].
  - exact (LZ_region rho' lazy' A' M' mem' t rg pn p x Hmem Hg Hrl Hpn Hp Hx Hhi Hlz).
  - rewrite Er in *. apply HA. apply (HLZ t rg pn p x Hg0 Hpn Hp Hx Hhi). apply Hl; [|exact Hlz].
    destruct (proj1 Hmem t rg Hg) as [_ Hpages]. destruct (Hpages pn p Hpn Hp) as (_ & Hlo & _). lia.
Qed.

End LZB.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section Frame.
Variable IM : fimage.

(* [comment removed for export] *)
Definition mfr (rho : int -> word) (F : fstate) (L3 : fledger3) (ms : machine_state)
               (n' : int) (rho' : int -> word) (F' : fstate) (L3' : fledger3) (ms' : machine_state) : Prop :=
  exists new, fl_ops L3' = fl_ops L3 ++ new
    /\ Forall (fun o : vop => to_Z (fent_tag (snd o)) < to_Z n') new
    /\ (forall x, ~ touched rho' new (bv_unsigned x) ->
                   (~ claimed_wr IM rho (f_mem F) x \/ ~ cell_expl rho' (f_mem F') x) ->
                   ms_mem ms' x = ms_mem ms x)
    /\ (forall x, claimed_wr IM rho' (f_mem F') x ->
                   claimed_wr IM rho (f_mem F) x \/ touched rho' new (bv_unsigned x))
    /\ (forall x, cell_expl rho (f_mem F) x ->
                   cell_expl rho' (f_mem F') x \/ touched rho' new (bv_unsigned x)).

Lemma mfr_refl rho F L3 ms n : mfr rho F L3 ms n rho F L3 ms.
Proof.
  exists []. split; [symmetry; apply app_nil_r|]. split; [constructor|]. split; [|split].
  - intros; reflexivity.
  - intros x Hx. left. exact Hx.
  - intros x Hx. left. exact Hx.
Qed.

(* [comment removed for export] *)
Lemma mfr_same rho F L3 ms n F' ms' :
  (forall x, ~ claimed_wr IM rho (f_mem F) x \/ ~ cell_expl rho (f_mem F') x -> ms_mem ms' x = ms_mem ms x) ->
  (forall x, claimed_wr IM rho (f_mem F') x -> claimed_wr IM rho (f_mem F) x) ->
  (forall x, cell_expl rho (f_mem F) x -> cell_expl rho (f_mem F') x) ->
  mfr rho F L3 ms n rho F' L3 ms'.
Proof.
  intros HA HB HB'. exists []. split; [symmetry; apply app_nil_r|]. split; [constructor|]. split; [|split].
  - intros x _ Hx. exact (HA x Hx).
  - intros x Hx. left. exact (HB x Hx).
  - intros x Hx. left. exact (HB' x Hx).
Qed.

Lemma mfr_trans rho1 F1 L1 ms1 n2 rho2 F2 L2 ms2 n3 rho3 F3 L3 ms3 :
  to_Z n2 <= to_Z n3 -> (forall t, to_Z t < to_Z n2 -> rho3 t = rho2 t) ->
  mfr rho1 F1 L1 ms1 n2 rho2 F2 L2 ms2 -> mfr rho2 F2 L2 ms2 n3 rho3 F3 L3 ms3 ->
  mfr rho1 F1 L1 ms1 n3 rho3 F3 L3 ms3.
Proof.
  intros Hn Hrho (new12 & E12 & T12 & A12 & B12 & C12) (new23 & E23 & T23 & A23 & B23 & C23).
  assert (Hden : forall o, In o new12 -> den rho3 (snd o) = den rho2 (snd o)).
  { intros [k [[t off] len]] Ho. pose proof (proj1 (Forall_forall _ _) T12 _ Ho) as Ht.
    cbn [snd fent_tag fst] in *. cbn [den]. unfold adr. rewrite (Hrho t Ht). reflexivity. }
  exists (new12 ++ new23). split; [rewrite E23, E12, app_assoc; reflexivity|]. split.
  { apply Forall_app. split; [|exact T23]. eapply Forall_impl; [|exact T12]. cbv beta. intros; lia. }
  assert (Hsplit : forall x, ~ touched rho3 (new12 ++ new23) x -> ~ touched rho2 new12 x /\ ~ touched rho3 new23 x).
  { intros x Ht. split; intros H; apply Ht; apply touched_app; [left | right]; [exact (touched_ext rho2 rho3 _ _ Hden H) | exact H]. }
  split; [|split].
  - intros x Ht Hc. destruct (Hsplit _ Ht) as [Ht12 Ht23].
    destruct Hc as [Hc1 | He3].
    + rewrite (A23 x Ht23); [exact (A12 x Ht12 (or_introl Hc1))|].
      left. intros Hc2. destruct (B12 x Hc2) as [H|H]; [exact (Hc1 H) | exact (Ht12 H)].
    + rewrite (A23 x Ht23 (or_intror He3)). apply (A12 x Ht12). right.
      intros He2. destruct (C23 x He2) as [H|H]; [exact (He3 H) | exact (Ht23 H)].
  - intros x Hc3. destruct (B23 x Hc3) as [Hc2 | H23]; [|right; apply touched_app; right; exact H23].
    destruct (B12 x Hc2) as [Hc1 | H12]; [left; exact Hc1|].
    right. apply touched_app. left. exact (touched_ext rho2 rho3 _ _ Hden H12).
  - intros x He1. destruct (C12 x He1) as [He2 | H12].
    + destruct (C23 x He2) as [He3 | H23]; [left; exact He3 | right; apply touched_app; right; exact H23].
    + right. apply touched_app. left. exact (touched_ext rho2 rho3 _ _ Hden H12).
Qed.

End Frame.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section Drive3.
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
(* [comment removed for export] *)
Variable wb0 : word.
Variable na0 lz0 : list (word * word).
Variable brk0 : word.
(* [comment removed for export] *)
Variable A0 : list (Z * Z).

Local Abbreviation DI := (DInv cfg segs IM R0 BIG RTgt keep mem0 XI xtags).
Local Abbreviation Rn := (FxRn.Rn segs IM).
Local Abbreviation erase := (FxDrive3.erase wb0).
Local Abbreviation mfr := (FxDrive3.mfr IM).

(* [comment removed for export] *)
Definition allowed (rho : int -> word) (L3 : fledger3) : list (Z * Z) := map (denA rho) (fl_allow L3) ++ A0.

Record lazy_part (n : int) (rho : int -> word) (F : fstate) (L3 : fledger3) (m : Model) : Prop := mk_lazy_part {
  lp_pi    : page_inv (allowed rho L3) m;
  lp_LZ    : LZ IM rho (m_vm_lazy m) (allowed rho L3) (f_mem F);
  lp_pw    : lazy_pw rho (m_vm_lazy m) (fl_lazy L3);
  lp_mat   : mat_lazy m;
  lp_cov   : lazy_cov (fl_all L3) (fl_lazy L3);
  lp_Ab    : A_bytes (allowed rho L3) <= fl_Ab L3;
  lp_lim   : vm_limit (m_vmmaps m) = Lim;                                     (* [comment removed for export] *)
  lp_maps  : vm_maps (m_vmmaps m) = map (den rho) (fl_all L3);
  lp_na    : vm_noaccess (m_vmmaps m) = na_apply rho (fl_ops L3) na0;
  lp_lz    : m_vm_lazy m = lz_apply rho (fl_ops L3) lz0;
  lp_v2in  : Forall (fun e => In e (fl_all L3)) (fl_maps (fl3 L3));
  lp_class : Forall (fun e => In e (fl_maps (fl3 L3)) \/ fent_tag e = 0%uint63
                              \/ iget (fent_tag e) (f_mem F) = None)          (* [comment removed for export] *)
                    (fl_all L3);
  lp_tags  : Forall (fun e => to_Z (fent_tag e) < to_Z n) (fl_all L3 ++ map snd (fl_ops L3) ++ fl_allow L3);
  lp_E     : eager_used m <= fl_E L3;
  lp_acct  : fl_E L3 + fl_Ab L3 <= Lim;
  lp_wfna  : Forall (fun q => e_hi q <= 2 ^ 64) (vm_noaccess (m_vmmaps m));
  lp_wflz  : Forall (fun q => e_hi q <= 2 ^ 64) (m_vm_lazy m);
  lp_opsR  : forall o x p, In o (fl_ops L3) -> In p R0 ->
               e_lo (den rho (snd o)) <= x < e_hi (den rho (snd o)) -> ~ (e_lo p <= x < e_hi p);
  lp_ord   : Forall (ord_ok n rho) (fl_ord L3);
  lp_opsF  : Forall (op_ok rho m (fl_all L3)) (fl_ops L3);                     (* [comment removed for export] *)
  lp_res   : Forall (res_ok n rho) (fl_res L3)                                 (* [comment removed for export] *)
}.

(* [comment removed for export] *)
Definition span_ok (rho : int -> word) (M : itrie region) (t : int) (rg : region) : Prop :=
  match rg_kind rg with
  | RK_plain =>
      (bv_unsigned (rho t) + to_Z (rg_len rg) <= span_lo \/ span_hi <= bv_unsigned (rho t) + to_Z (rg_lo rg))
      \/ (span_lo <= bv_unsigned (rho t) + to_Z (rg_lo rg)
          /\ bv_unsigned (rho t) + to_Z (rg_len rg) <= span_hi
          /\ forall y, bv_unsigned (rho t) + to_Z (rg_lo rg) <= y < bv_unsigned (rho t) + to_Z (rg_len rg) ->
               exists p, In p R0 /\ e_lo p <= 8 * (y - to_Z shadow_K)
                         /\ 8 * (y - to_Z shadow_K) + 8 <= e_hi p)
  | RK_shadow p =>
      t = (p + 1)%uint63
      /\ exists rgp, iget p M = Some rgp /\ 3 <= to_Z (rg_align rgp)
                     /\ to_Z (rg_lo rgp) <= 8 * to_Z (rg_lo rg)
                     /\ 8 * to_Z (rg_len rg) <= to_Z (rg_len rgp)
  end.

Record shadow_part (rho : int -> word) (F : fstate) (L3 : fledger3) (ms : machine_state) : Prop := mk_shadow_part {
  sp_ShZ : forall x : word, in_shadow (bv_unsigned x) -> no_region rho (f_mem F) (bv_unsigned x) ->
             ~ exempted rho (fl_ex L3) (bv_unsigned x) ->
             rview segs (ms_mem ms) x = Some (Z_to_bv 8 0) /\ wview segs (ms_mem ms) x <> None;
  sp_cov : forall x, in_span x -> exists e, In e (fl_all L3) /\ fent_tag e = 0%uint63
                                            /\ e_lo (den rho e) <= x < e_hi (den rho e);
  sp_ok  : forall t rg, iget t (f_mem F) = Some rg -> span_ok rho (f_mem F) t rg;
  sp_ex  : lazy_cov (fl_all L3) (fl_ex L3)
}.

Definition xpart (rho : int -> word) (F : fstate) (ms : machine_state) (m : Model) : Prop :=
  ms_fregs ms = fr0 /\ ms_fcsr ms = fc0 /\ ms_rom ms = rom0
  /\ (forall x, hi x -> alloc_top (m_vmmaps m) <= bv_unsigned x
                      /\ no_region rho (f_mem F) (bv_unsigned x)
                      /\ ms_mem ms x = mem0 x)
  /\ vm_brk (m_vmmaps m) = brk0.

Definition DInv3 (n : int) (rho : int -> word) (F : fstate) (L3 : fledger3)
    (ms : machine_state) (m : Model) : Prop :=
  DI n rho F (fl3 L3) ms (erase m) /\ lazy_part n rho F L3 m
  /\ shadow_part rho F L3 ms /\ xpart rho F ms m.

(* [comment removed for export] *)
Definition pext (n : int) (rho : int -> word) (F : fstate) (L3 : fledger3) (ms : machine_state) (m : Model)
                (n' : int) (rho' : int -> word) (F' : fstate) (L3' : fledger3) (ms' : machine_state) (m' : Model) : Prop :=
  dext n rho m n' rho' m' /\ mfr rho F L3 ms n' rho' F' L3' ms'.

Lemma pext_refl n rho F L3 ms m : pext n rho F L3 ms m n rho F L3 ms m.
Proof. split; [exact (dext_refl R0 rom0 hi n rho m) | apply (mfr_refl IM)]. Qed.

Lemma pext_trans n1 rho1 F1 L1 ms1 m1 n2 rho2 F2 L2 ms2 m2 n3 rho3 F3 L3 ms3 m3 :
  pext n1 rho1 F1 L1 ms1 m1 n2 rho2 F2 L2 ms2 m2 -> pext n2 rho2 F2 L2 ms2 m2 n3 rho3 F3 L3 ms3 m3 ->
  pext n1 rho1 F1 L1 ms1 m1 n3 rho3 F3 L3 ms3 m3.
Proof.
  intros [D12 M12] [D23 M23]. split; [exact (dext_trans R0 _ _ _ _ _ _ _ _ _ D12 D23)|].
  destruct D23 as (Hn & Hrho & _). exact (mfr_trans IM _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hn Hrho M12 M23).
Qed.

Lemma DInv3_DInv n rho F L3 ms m : DInv3 n rho F L3 ms m -> DI n rho F (fl3 L3) ms (erase m).
Proof. intros H. exact (proj1 H). Qed.

Lemma DInv3_R n rho F L3 ms m : DInv3 n rho F L3 ms m -> R segs IM rho F ms.
Proof. intros ((HRn & H0 & _) & _). exact (Rn_R segs IM n rho F ms HRn H0). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma lazy_part_LZ n rho F L3 m :
  lazy_part n rho F L3 m -> LZ IM rho (m_vm_lazy m) (allowed rho L3) (f_mem F).
Proof. intros H. exact (lp_LZ _ _ _ _ _ H). Qed.

(* [comment removed for export] *)
Lemma lazy_part_minv n rho F L3 m :
  lazy_part n rho F L3 m ->
  Forall (fun p => page_in_ranges p (m_vm_lazy m) = true) (m_vm_materialized m).
Proof. intros H. exact (lp_mat _ _ _ _ _ H). Qed.

(* [comment removed for export] *)
Lemma lazy_cov_inside rho (all lazy : list fent) maps e :
  lazy_cov all lazy -> maps = map (den rho) all -> (forall p, In p maps -> e_hi p < 2 ^ 64) ->
  In e lazy -> exists e', In e' all /\ fent_tag e' = fent_tag e /\ e_inside (den rho e) (den rho e').
Proof.
  intros Hcov -> Hcut He.
  destruct (proj1 (Forall_forall _ _) Hcov e He) as (_ & e' & He' & Hw).
  exists e'. split; [exact He'|]. split; [exact (proj1 Hw)|].
  apply den_within; [exact Hw|]. apply Hcut. apply in_map. exact He'.
Qed.

(* [comment removed for export] *)
Lemma lazy_part_eager n rho F L3 m : lazy_part n rho F L3 m -> eager_used m <= fl_E L3.
Proof. intros H. exact (lp_E _ _ _ _ _ H). Qed.

(* [comment removed for export] *)
Lemma lazy_part_budget n rho F L3 m nZ :
  lazy_part n rho F L3 m ->
  fl_E L3 + fl_Ab L3 + nZ <= Lim ->
  vm_backing_used m + nZ <= vm_limit (m_vmmaps m).
Proof.
  intros HL Hacc. pose proof (lp_E _ _ _ _ _ HL) as HE. pose proof (lp_Ab _ _ _ _ _ HL) as HAb.
  pose proof (page_inv_lazy_inv _ _ (lp_pi _ _ _ _ _ HL)) as Hu. unfold lazy_inv in Hu.
  pose proof (lp_lim _ _ _ _ _ HL). lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma span_ok_shape rho M M' t rg rg' :
  same_shape M M' -> same_kinds M M' ->
  iget t M = Some rg -> iget t M' = Some rg' -> span_ok rho M t rg -> span_ok rho M' t rg'.
Proof.
  intros Hs Hk Hg Hg' Hok.
  pose proof (Hk t) as Ek. rewrite Hg, Hg' in Ek. cbn [option_map] in Ek. injection Ek as Ek.
  pose proof (Hs t) as Est. rewrite Hg, Hg' in Est. destruct Est as (E1 & E2 & _).
  unfold span_ok in *. rewrite Ek, E1, E2. destruct (rg_kind rg) as [|p]; [exact Hok|].
  destruct Hok as (Et & rgp & Hgp & Hal & Hlo & Hlen). split; [exact Et|].
  destruct (same_shape_get' _ _ _ _ Hs Hgp) as (rgp' & Hgp' & F1 & F2).
  pose proof (Hs p) as Esp. rewrite Hgp, Hgp' in Esp. destruct Esp as (_ & _ & F3 & _).
  exists rgp'. rewrite F1, F2, F3. repeat split; assumption.
Qed.

Lemma no_region_shape rho M M' x : same_shape M M' -> no_region rho M x -> no_region rho M' x.
Proof.
  intros Hs Hno t rg' Hg' Hin. destruct (same_shape_get _ _ _ _ Hs Hg') as (rg & Hg & E1 & E2).
  apply (Hno t rg Hg). exact (in_ival_shape rho t rg rg' _ E1 E2 Hin).
Qed.

Lemma no_region_shape' rho M M' x : same_shape M M' -> no_region rho M' x -> no_region rho M x.
Proof.
  intros Hs Hno t rg Hg Hin. destruct (same_shape_get' _ _ _ _ Hs Hg) as (rg' & Hg' & E1 & E2).
  apply (Hno t rg' Hg'). unfold in_ival in *. rewrite E1, E2. exact Hin.
Qed.

(* [comment removed for export] *)
Lemma eager_used_lazy_frame m m' : lazy_frame m m' -> eager_used m' = eager_used m.
Proof. intros [mat' ->]. destruct m as [fd [maps lazy mat] io fs proc lim tm]. reflexivity. Qed.

(* [comment removed for export] *)
Lemma lazy_part_next n rho F F' L3 m m' :
  LZ IM rho (m_vm_lazy m) (allowed rho L3) (f_mem F') -> lazy_frame m m' -> page_inv (allowed rho L3) m' ->
  mat_lazy m' ->
  (forall t, iget t (f_mem F) = None -> iget t (f_mem F') = None) ->          (* [comment removed for export] *)
  lazy_part n rho F L3 m -> lazy_part n rho F' L3 m'.
Proof.
  intros HLZ' Hfr Hpi Hml Hnone HL.
  destruct (lazy_frame_facts m m' Hfr) as (_ & Evm & Elz & _).
  pose proof (eager_used_lazy_frame m m' Hfr) as EE.
  destruct HL as [? ? ? ? ? ? ? ? ? ? ? Hcl ? ? ? ? ? ? ? Hopsf]. constructor; rewrite ?Elz, ?Evm, ?EE; try assumption.
  - eapply Forall_impl; [|exact Hcl]. intros e [H|[H|H]]; [left; exact H | right; left; exact H | right; right; exact (Hnone _ H)].
  - eapply Forall_impl; [|exact Hopsf]. intros o. apply op_ok_model. rewrite Evm. reflexivity.
Qed.

Lemma same_kinds_none M M' t : same_kinds M M' -> iget t M = None -> iget t M' = None.
Proof. intros H E. pose proof (H t) as Ht. rewrite E in Ht. destruct (iget t M'); [discriminate Ht | reflexivity]. Qed.

(* [comment removed for export] *)
Lemma DInv3_run n rho F L3 ms m bp k F1 r cnt :
  (k <= 61)%nat ->
  fx_run IM code bp k F = (F1, r, cnt) ->
  DInv3 n rho F L3 ms m ->
  exists ms1, rsteps segs (nat_of_int cnt) ms = MachineOk ms1
    /\ (r = SEcall -> RiscvSemantics.step segs ms1 = MachineOk (ms_pend ms1))
    /\ mfr rho F L3 ms n rho F1 L3 ms1
    /\ (forall T, (forall m1, lazy_frame m m1 -> DInv3 n rho F1 L3 ms1 m1 ->
                     realizes_cfg cfg segs (mkCfg ms1 m1) T) ->
                  realizes_cfg cfg segs (mkCfg ms m) T)
    /\ (exists m1, lazy_frame m m1 /\ DInv3 n rho F1 L3 ms1 m1
                   /\ star_cfg segs cfg (mkCfg ms m) [] (mkCfg ms1 m1)).
Proof.
  intros Hk Hrun (HD & HL & HS & HX).
  destruct (DInv_run cfg segs IM code Hcode R0 BIG RTgt keep mem0 XI xtags n rho F (fl3 L3) ms (erase m)
              bp k F1 r cnt Hk Hrun HD) as (ms1 & Hsteps & HD1 & Hec).
  pose proof HD as (HRn & H0 & Hh & _).
  change (m_halted (erase m)) with (m_halted m) in Hh.
  pose proof (Rn_R segs IM n rho F ms HRn H0) as HR.
  pose proof (lp_pi _ _ _ _ _ HL) as Hpi.
  destruct (fx_run_pages_Rn segs IM rho H0 code Hcode (m_vm_lazy m) (allowed rho L3) cfg n bp k F F1 r cnt ms m
              Hk Hrun HRn Hh eq_refl Hpi (lazy_part_LZ n rho F L3 m HL))
    as (ms1' & Hsteps' & _ & HLZ1 & _ & Hframe & Hmono & Erom & Efr & Efc & _ & _).
  rewrite Hsteps in Hsteps'. injection Hsteps' as <-.
  destruct (fx_run_touch segs IM rho H0 code Hcode (m_vm_lazy m) (allowed rho L3) bp k F F1 r cnt Hk Hrun)
    as (_ & Htouch).
  pose proof (Htouch ms HR (lazy_part_LZ n rho F L3 m HL)) as Ht.
  destruct (asteps_pages segs (allowed rho L3) _ ms ms1 m Hsteps Hpi Ht) as (m1 & Ha & Hfr & Hpi1).
  pose proof (asteps_mat_lazy segs _ ms m ms1 m1 Ha (lp_mat _ _ _ _ _ HL)) as Hml1.
  pose proof (fx_run_shape IM code _ _ _ _ _ _ Hrun) as Hshape.
  pose proof (fx_run_kinds IM code _ _ _ _ _ _ Hrun) as Hkinds.
  assert (Hunch : forall x, no_region rho (f_mem F) (bv_unsigned x) -> ms_mem ms1 x = ms_mem ms x).
  { intros x Hno. apply Hframe. intros Hc.
    destruct (claimed_in_region segs IM R0 (fun _ => None) rho F ms x HR Hc) as (t & rg & Hg & Hin).
    exact (Hno t rg Hg Hin). }
  assert (Hnext : DInv3 n rho F1 L3 ms1 m1).
  { destruct (lazy_frame_facts m m1 Hfr) as (_ & Evm & _).
    split; [rewrite (erase_lazy_frame wb0 m m1 Hfr); exact HD1|].
    split; [exact (lazy_part_next n rho F F1 L3 m m1 HLZ1 Hfr Hpi1 Hml1
                     (fun t => same_kinds_none _ _ t (fx_run_kinds IM code bp k F F1 r cnt Hrun)) HL)|].
    split.
    - destruct HS as [Hz Hcov Hsp Hex]. constructor.
      + intros x Hx Hno Hne. pose proof (no_region_shape' rho _ _ _ Hshape Hno) as Hno0.
        destruct (Hz x Hx Hno0 Hne) as [Z1 Z2]. unfold rview, wview in *.
        rewrite (Hunch x Hno0). split; assumption.
      + exact Hcov.
      + intros t rg' Hg'. destruct (same_shape_get _ _ _ _ Hshape Hg') as (rg & Hg & _).
        exact (span_ok_shape rho _ _ t rg rg' Hshape Hkinds Hg Hg' (Hsp t rg Hg)).
      + exact Hex.
    - destruct HX as (X1 & X2 & X3 & X4 & X5). split; [congruence|]. split; [congruence|]. split; [congruence|].
      split; [|rewrite Evm; exact X5].
      intros x Hx. destruct (X4 x Hx) as (Ht' & Hno & Hm). rewrite Evm. split; [exact Ht'|]. split.
      + exact (no_region_shape rho _ _ _ Hshape Hno).
      + rewrite (Hunch x Hno). exact Hm. }
  exists ms1. split; [exact Hsteps|]. split; [exact Hec|].
  split.
  { apply (mfr_same IM rho F L3 ms n F1 ms1); [|exact Hmono|].
    - intros x [Hx|Hx]; [exact (Hframe x Hx)|].
      exact (fx_run_cellframe segs IM rho H0 code Hcode bp k F F1 r cnt Hk Hrun ms ms1 HR Hsteps x Hx).
    - exact (fx_run_cell_mono IM rho code bp k F F1 r cnt Hrun). }
  split.
  - intros T HT. apply (rzc_asteps cfg segs _ ms m ms1 m1 T Hh Ha). exact (HT m1 Hfr Hnext).
  - exists m1. split; [exact Hfr|]. split; [exact Hnext|].
    exact (asteps_star_cfg cfg segs _ ms m ms1 m1 Hh Ha).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma DInv3_lazy_frame n rho F L3 ms m m1 :
  DInv3 n rho F L3 ms m -> lazy_frame m m1 -> page_inv (allowed rho L3) m1 -> mat_lazy m1 ->
  DInv3 n rho F L3 ms m1.
Proof.
  intros (HD & HL & HS & HX) Hfr Hpi1 Hml1. destruct (lazy_frame_facts m m1 Hfr) as (_ & Evm & _).
  split; [rewrite (erase_lazy_frame wb0 m m1 Hfr); exact HD|].
  split; [exact (lazy_part_next n rho F F L3 m m1 (lazy_part_LZ n rho F L3 m HL) Hfr Hpi1 Hml1 (fun t H => H) HL)|].
  split; [exact HS|].
  destruct HX as (X1 & X2 & X3 & X4 & X5). split; [exact X1|]. split; [exact X2|]. split; [exact X3|].
  split; [|rewrite Evm; exact X5].
  intros x Hx. rewrite Evm. exact (X4 x Hx).
Qed.

(* [comment removed for export] *)
Lemma step_pend_touch_ok lazy A ms :
  RiscvSemantics.step segs ms = MachineOk (ms_pend ms) -> touch_ok segs lazy A ms.
Proof.
  intros Hstep report Hacc. unfold RiscvSemantics.step in Hstep. rewrite Hacc in Hstep.
  cbn [drop_access_report] in Hstep. injection Hstep as Hst.
  assert (Hsvc : ms_svc_pending (access_value _ report) = Some (ms_reg ms 17)) by (rewrite Hst; reflexivity).
  assert (Hdec : forall w, decode_exec_accesses segs ms w = MachineOk report ->
                           accessed_ranges _ report = []).
  { intros w Hd. unfold decode_exec_accesses in Hd. destruct (is_ecall w).
    - injection Hd as <-. reflexivity.
    - destruct (decode_any w) as [[i isz]|]; [|destruct (is_defined_illegal w); discriminate].
      match type of Hd with context [interp_eff_accesses ?a ?b ?c] => destruct (interp_eff_accesses a b c) as [r0| |] end;
        try discriminate.
      destruct (access_value _ r0) as [c m']. injection Hd as <-. cbn [access_value ms_svc_pending] in Hsvc. discriminate. }
  unfold step_accesses in Hacc.
  assert (Hnil : accessed_ranges _ report = []).
  { destruct (fetch_word segs (ms_pc ms)) as [w|]; [exact (Hdec w Hacc)|].
    destruct (fetch_word_ov segs (ms_mem ms) (ms_pc ms)) as [w|]; [exact (Hdec w Hacc)|].
    destruct (fetch_tail_any segs (ms_mem ms) (ms_pc ms)) as [w|]; [exact (Hdec w Hacc)|].
    destruct (fetch_failure segs (ms_mem ms) (ms_pc ms)); try discriminate. injection Hacc as <-. reflexivity. }
  rewrite Hnil. apply touch_allowed_nil.
Qed.

Lemma mfr_pend n rho F L3 ms : mfr rho F L3 ms n rho F L3 (ms_pend ms).
Proof. apply (mfr_same IM); [intros; reflexivity | intros x Hx; exact Hx | intros x Hx; exact Hx]. Qed.

Lemma DInv3_pend n rho F L3 ms m :
  DInv3 n rho F L3 ms m -> RiscvSemantics.step segs ms = MachineOk (ms_pend ms) ->
  (forall T, (forall m1, lazy_frame m m1 -> DInv3 n rho F L3 ms m1 ->
                realizes_cfg cfg segs (mkCfg (ms_pend ms) m1) T) ->
             realizes_cfg cfg segs (mkCfg ms m) T)
  /\ (exists m1, lazy_frame m m1 /\ DInv3 n rho F L3 ms m1
                 /\ star_cfg segs cfg (mkCfg ms m) [] (mkCfg (ms_pend ms) m1)).
Proof.
  intros HD Hstep. pose proof HD as ((HRn & H0 & Hh & _) & HL & _).
  change (m_halted (erase m)) with (m_halted m) in Hh.
  pose proof (lp_pi _ _ _ _ _ HL) as Hpi.
  pose proof (R_svc _ _ _ _ _ (Rn_R segs IM n rho F ms HRn H0)) as Hsvc.
  assert (Hr : rsteps segs 1 ms = MachineOk (ms_pend ms)).
  { cbn [rsteps]. rewrite Hsvc, Hstep. reflexivity. }
  assert (Ht : forall j msj, (j < 1)%nat -> rsteps segs j ms = MachineOk msj ->
                 touch_ok segs (m_vm_lazy m) (allowed rho L3) msj).
  { intros j msj Hj Hrj. assert (j = 0)%nat by lia. subst j. cbn [rsteps] in Hrj. injection Hrj as <-.
    apply step_pend_touch_ok. exact Hstep. }
  destruct (asteps_pages segs (allowed rho L3) 1 ms (ms_pend ms) m Hr Hpi Ht) as (m1 & Ha & Hfr & Hpi1).
  pose proof (asteps_mat_lazy segs _ ms m (ms_pend ms) m1 Ha (lp_mat _ _ _ _ _ HL)) as Hml1.
  pose proof (DInv3_lazy_frame n rho F L3 ms m m1 HD Hfr Hpi1 Hml1) as HD1.
  split.
  - intros T HT. apply (rzc_asteps cfg segs 1 ms m (ms_pend ms) m1 T Hh Ha). exact (HT m1 Hfr HD1).
  - exists m1. split; [exact Hfr|]. split; [exact HD1|].
    exact (asteps_star_cfg cfg segs 1 ms m (ms_pend ms) m1 Hh Ha).
Qed.

End Drive3.
