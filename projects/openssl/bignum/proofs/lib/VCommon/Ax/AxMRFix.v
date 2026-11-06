(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith Lia Bool List.
From Stdlib Require Import Uint63.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType Fs State Monad Specs Run.
From OSSVerify.Proofs.openssl.bignum.lib.VCommon.Ax Require Import AxLin AxVal AxSys AxAcct AxMeasure AxSysFix AxSysUnmap0 AxSysProt0.
From OSSVerify.Proofs.openssl.bignum.lib.VCommon.Ax Require Import AxFd AxLz AxModelRel.
Import ListNotations.

Local Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Lemma pw_disj_map_in {A : Type} (f : A -> word * word) (l : list A) (x y : A) :
  pw_disj (map f l) -> In x l -> In y l -> x <> y ->
  bas (f x) + bsz (f x) <= bas (f y) \/ bas (f y) + bsz (f y) <= bas (f x).
Proof.
  intros Hpw Hx Hy Hne. destruct (in_split x l Hx) as [l1 [l2 E]]. subst l.
  apply in_app_or in Hy as [Hy|[Hy|Hy]]; [|exfalso; exact (Hne Hy)|].
  - destruct (in_split y l1 Hy) as [l3 [l4 E]]. subst l1.
    pose proof (Hpw (map f l3) (f y) (map f (l4 ++ x :: l2))) as X.
    rewrite <- app_assoc, map_app in X. cbn [app map] in X. specialize (X eq_refl (f x)).
    rewrite map_app in X. cbn [map] in X. specialize (X ltac:(apply in_or_app; right; left; reflexivity)).
    unfold iv_disj in X. lia.
  - pose proof (Hpw (map f l1) (f x) (map f l2)) as X. rewrite map_app in X. cbn [map] in X.
    specialize (X eq_refl (f y) (in_map f l2 y Hy)). unfold iv_disj in X. lia.
Qed.

Lemma pw_disj_sub {A : Type} (f : A -> word * word) (g : A -> bool) (l : list A) :
  pw_disj (map f l) -> pw_disj (map f (List.filter g l)).
Proof.
  induction l as [|a r IH]; intros H; [exact H|]. cbn [List.filter].
  assert (Hr : pw_disj (map f r)) by (exact (proj2 (pw_disj_inv _ _ H))).
  destruct (g a); [|exact (IH Hr)]. cbn [map]. intros l1 p l2 E q Hq. destruct l1 as [|p1 l1']; cbn [app] in E.
  - injection E as <- <-. apply (proj1 (pw_disj_inv _ _ H)). apply in_map_iff in Hq as [b [<- Hb]]. apply in_map.
    apply filter_In in Hb as [Hb _]. exact Hb.
  - injection E as <- E. exact (IH Hr l1' p l2 E q Hq).
Qed.

Section MRFix.
Variable segs : list Segment.
Variable fs0 : Fs.Fs.

Notation MRm := (MR segs fs0).

Definition add_exp (am : amodel) (e0 : aent) (f : lin) (n : Z) : amodel :=
  AM (am_maps am) (am_brk0 am) (am_brk am) (am_tid am) (am_shadow am) (am_next am) (am_atop am) (am_out am)
     (if ae_na e0 then (e0, f, n) :: am_exp am else am_exp am) (am_fd am).

Definition del_ent (am : amodel) (e0 : aent) : amodel :=
  AM (List.filter (fun e => negb (aent_eqb e e0)) (am_maps am)) (am_brk0 am) (am_brk am) (am_tid am) (am_shadow am)
     (am_next am) (am_atop am) (am_out am)
     (List.filter (fun x => negb (aent_eqb (fst (fst x)) e0)) (am_exp am)) (am_fd am).

Section Range.
Variable ρ : valuation.
Variable am : amodel.
Variable m : Model.
Hypothesis HM : MRm ρ am m.
Variable e0 : aent.
Hypothesis He0 : In e0 (am_maps am).
Variable f : lin.
Variable n : Z.
Hypothesis Hn : 0 < n.
Hypothesis Hlo : leval ρ (ae_base e0) <= leval ρ f.
Hypothesis Hhi : leval ρ f + n <= leval ρ (ae_base e0) + ae_size e0.

Let addr : word := Z_to_bv 64 (leval ρ f).
Let nw : word := Z_to_bv 64 n.

Lemma rng_ok : ent_ok ρ e0.
Proof. exact (MR_ent segs fs0 ρ am m e0 HM He0). Qed.

Lemma rng_addr : bv_unsigned addr = leval ρ f.
Proof. destruct rng_ok as (H1 & H2 & H3). unfold addr. apply u_Z_to_bv. lia. Qed.

Lemma rng_n : bv_unsigned nw = n.
Proof. destruct rng_ok as (H1 & H2 & H3). unfold nw. apply u_Z_to_bv. lia. Qed.

Lemma rng_top : leval ρ f + n <= alloc_top (m_vmmaps m).
Proof.
  pose proof (mr_top segs fs0 ρ am m HM _ (MR_ent_in segs fs0 ρ am m e0 HM He0)) as Ht.
  rewrite (ent_val_bas ρ e0 rng_ok), (ent_val_bsz ρ e0 rng_ok) in Ht. lia.
Qed.

Lemma rng_two64 : leval ρ f + n <= two64.
Proof. pose proof rng_top. pose proof (alloc_top_lt (m_vmmaps m)) as Ha. change two_pow_64 with two64 in Ha. lia. Qed.

Lemma rng_other (e : aent) (z : Z) : In e (am_maps am) -> e <> e0 -> in_ent ρ e z -> ~ (leval ρ f <= z < leval ρ f + n).
Proof.
  intros He Hne Hz Hr. pose proof (mr_pw segs fs0 ρ am m HM) as Hpw. rewrite (mr_maps segs fs0 ρ am m HM) in Hpw.
  pose proof (pw_disj_map_in (ent_val ρ) (am_maps am) e e0 Hpw He He0 Hne) as D.
  pose proof (MR_ent segs fs0 ρ am m e HM He) as Hok.
  rewrite (ent_val_bas ρ e Hok), (ent_val_bsz ρ e Hok), (ent_val_bas ρ e0 rng_ok), (ent_val_bsz ρ e0 rng_ok) in D.
  unfold in_ent in Hz. lia.
Qed.

Lemma rng_other_val (e : aent) : In e (am_maps am) -> e <> e0 ->
  bas (ent_val ρ e) + bsz (ent_val ρ e) <= leval ρ f \/ leval ρ f + n <= bas (ent_val ρ e).
Proof.
  intros He Hne. pose proof (mr_pw segs fs0 ρ am m HM) as Hpw. rewrite (mr_maps segs fs0 ρ am m HM) in Hpw.
  pose proof (pw_disj_map_in (ent_val ρ) (am_maps am) e e0 Hpw He He0 Hne) as D.
  rewrite (ent_val_bas ρ e0 rng_ok), (ent_val_bsz ρ e0 rng_ok) in D. lia.
Qed.

Lemma rng_ents_disj (e : aent) : In e (am_maps am) -> e <> e0 -> ent_hi ρ e <= ent_lo ρ e0 \/ ent_hi ρ e0 <= ent_lo ρ e.
Proof.
  intros He Hne. pose proof (mr_pw segs fs0 ρ am m HM) as Hpw. rewrite (mr_maps segs fs0 ρ am m HM) in Hpw.
  pose proof (pw_disj_map_in (ent_val ρ) (am_maps am) e e0 Hpw He He0 Hne) as D.
  pose proof (MR_ent segs fs0 ρ am m e HM He) as Hok.
  rewrite (ent_val_bas ρ e Hok), (ent_val_bsz ρ e Hok), (ent_val_bas ρ e0 rng_ok), (ent_val_bsz ρ e0 rng_ok) in D.
  unfold ent_lo, ent_hi. lia.
Qed.

Lemma rng_in_e0 : ent_lo ρ e0 <= bv_unsigned addr /\ bv_unsigned addr + bv_unsigned nw <= ent_hi ρ e0.
Proof. rewrite rng_addr, rng_n. unfold ent_lo, ent_hi. lia. Qed.

Lemma rng_res (q : word * word) : In q (vm_reserved (m_vmmaps m)) -> iv_disj (leval ρ f) (leval ρ f + n) q.
Proof.
  intros Hq. pose proof (mr_disj segs fs0 ρ am m HM _ q (MR_ent_in segs fs0 ρ am m e0 HM He0) Hq) as D.
  rewrite (ent_val_bas ρ e0 rng_ok), (ent_val_bsz ρ e0 rng_ok) in D. unfold iv_disj in *. lia.
Qed.

Lemma rng_repl_lazy_top (flags : word) (p : word * word) :
  In p (repl_lazy flags addr nw (m_vm_lazy m)) -> bv_unsigned (fst p) + bv_unsigned (snd p) <= alloc_top (m_vmmaps m).
Proof.
  pose proof (MR_lazy_nowrap segs fs0 ρ am m HM) as Hnw. pose proof rng_top as Ht. pose proof rng_two64 as H64.
  assert (Hsub : In p (maps_subtract (m_vm_lazy m) (bv_unsigned addr) (bv_unsigned addr + bv_unsigned nw)) ->
                 bv_unsigned (fst p) + bv_unsigned (snd p) <= alloc_top (m_vmmaps m)).
  { intros Hp. destruct (subtract_within _ _ _ p Hnw Hp) as (q & Hq & H1 & H2).
    pose proof (mr_lazy segs fs0 ρ am m HM q Hq) as Hl. unfold bas, bsz in *. lia. }
  unfold repl_lazy. destruct (mmap_noreserve_b flags); [|exact Hsub].
  intros Hp. apply in_app_or in Hp as [Hp|Hp]; [|exact (Hsub Hp)].
  destruct (lazy_interior_within addr nw p ltac:(rewrite rng_addr, rng_n; exact H64) Hp) as (_ & H1 & H2).
  rewrite rng_addr, rng_n in *. unfold bas, bsz in *. lia.
Qed.

Lemma rng_repl_lazy_res (flags : word) (p q : word * word) :
  In p (repl_lazy flags addr nw (m_vm_lazy m)) -> In q (vm_reserved (m_vmmaps m)) -> iv_disj (bas p) (bas p + bsz p) q.
Proof.
  pose proof (MR_lazy_nowrap segs fs0 ρ am m HM) as Hnw. pose proof rng_two64 as H64.
  intros Hp Hq. unfold repl_lazy in Hp.
  assert (Hsub : In p (maps_subtract (m_vm_lazy m) (bv_unsigned addr) (bv_unsigned addr + bv_unsigned nw)) -> iv_disj (bas p) (bas p + bsz p) q).
  { intros Hp'. exact (res_subtract _ _ _ _ Hnw (mr_lazy_res segs fs0 ρ am m HM) p q Hp' Hq). }
  destruct (mmap_noreserve_b flags); [|exact (Hsub Hp)].
  apply in_app_or in Hp as [Hp|Hp]; [|exact (Hsub Hp)].
  apply (res_interior addr nw (vm_reserved (m_vmmaps m)) ltac:(rewrite rng_addr, rng_n; exact H64)); [|exact Hp | exact Hq].
  intros q' Hq'. rewrite rng_addr, rng_n. exact (rng_res q' Hq').
Qed.

Lemma rng_na_cov (exps : list (aent * lin * Z)) :
  (forall e z, in_exp ρ (am_exp am) e z -> in_exp ρ exps e z) ->
  (forall z, leval ρ f <= z < leval ρ f + n -> ae_na e0 = true -> in_exp ρ exps e0 z) ->
  forall e z, In e (am_maps am) -> ae_na e = true -> in_ent ρ e z -> ~ in_exp ρ exps e z ->
  inl (maps_subtract (vm_noaccess (m_vmmaps m)) (bv_unsigned addr) (bv_unsigned addr + bv_unsigned nw)) z.
Proof.
  intros Hmono Hnew e z He Hna Hz Hne. apply (inl_subtract1 _ _ _ z (mr_na segs fs0 ρ am m HM)). split.
  - apply (mr_nacov segs fs0 ρ am m HM e z He Hna Hz). intros X. exact (Hne (Hmono e z X)).
  - rewrite rng_addr, rng_n. intros Hr. destruct (aent_eq_dec e e0) as [->|Hd].
    + exact (Hne (Hnew z Hr Hna)).
    + exact (rng_other e z He Hd Hz Hr).
Qed.

Lemma rng_na_cov2 (e : aent) :
  In e (am_maps am) -> e <> e0 -> In (ent_val ρ e) (vm_noaccess (m_vmmaps m)) ->
  In (ent_val ρ e) (maps_subtract (vm_noaccess (m_vmmaps m)) (bv_unsigned addr) (bv_unsigned addr + bv_unsigned nw)).
Proof.
  intros He Hne Hin. pose proof (MR_ent segs fs0 ρ am m e HM He) as Hok.
  apply piece_keep; [exact Hin | rewrite (ent_val_bsz ρ e Hok); exact (proj1 (proj2 Hok)) | rewrite rng_n; lia|].
  rewrite rng_addr, rng_n. exact (rng_other_val e He Hne).
Qed.

Lemma rng_na_maps (z : Z) :
  inl (maps_subtract (vm_noaccess (m_vmmaps m)) (bv_unsigned addr) (bv_unsigned addr + bv_unsigned nw)) z ->
  inl (vm_maps (m_vmmaps m)) z.
Proof.
  intros H. apply (inl_subtract1 _ _ _ z (mr_na segs fs0 ρ am m HM)) in H as [H _]. exact (mr_na_maps segs fs0 ρ am m HM z H).
Qed.

Hypothesis Hcal : leval ρ f mod 4096 = 0 /\ n mod 4096 = 0.
Lemma rng_al : bv_unsigned addr mod 4096 = 0 /\ bv_unsigned nw mod 4096 = 0.
Proof. rewrite rng_addr, rng_n. exact Hcal. Qed.

Theorem MR_fix (flags : word) :

  (mmap_noreserve_b flags = true -> BIGMIN <= ae_size e0) ->
  (lzfull e0 = true -> mmap_noreserve_b flags = true /\ leval ρ f mod 4096 = 0 /\ n mod 4096 = 0) ->
  MRm ρ (add_exp am e0 f n) (fix_rw_model flags addr nw m).
Proof.
  intros Hbig Hfull.
  pose proof HM as [H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 H17 H18 H19 H20 H21].
  assert (Ev : m_vmmaps (fix_rw_model flags addr nw m) = mmap_fixed_rw_next (m_vmmaps m) addr nw)
    by (unfold fix_rw_model; rewrite repl_vmmaps_eq, with_vmmaps_vmmaps_eq; reflexivity).
  assert (El : m_vm_lazy (fix_rw_model flags addr nw m) = repl_lazy flags addr nw (m_vm_lazy m))
    by (unfold fix_rw_model; rewrite repl_lazy_eq, with_vmmaps_lazy_eq; reflexivity).
  constructor; rewrite ?Ev, ?El; cbn [add_exp am_maps am_brk0 am_brk am_tid am_shadow am_next am_atop am_out am_exp am_fd
    mmap_fixed_rw_next vm_reserved vm_maps vm_noaccess vm_start_brk vm_brk alloc_top vm_init_sp]; try assumption.
  - unfold fix_rw_model. rewrite repl_tid. exact H7.
  - unfold fix_rw_model. rewrite repl_fds. exact H8.
  - unfold fix_rw_model. rewrite repl_fs. exact H9.
  - intros p Hp. exact (rng_repl_lazy_top flags p Hp).
  - apply nowrap_subtract. exact H13.
  - apply rng_na_cov.
    + intros e z [x [Hx Hxe]]. exists x. split; [|exact Hxe]. destruct (ae_na e0); [right; exact Hx | exact Hx].
    + intros z Hz Hna. rewrite Hna. exists (e0, f, n). split; [left; reflexivity|]. cbn [fst snd]. split; [reflexivity | exact Hz].
  - exact rng_na_maps.
  - intros e He Hna Hnx. destruct (aent_eq_dec e e0) as [->|Hd].
    + exfalso. rewrite Hna in Hnx. apply (Hnx (e0, f, n)); [left; reflexivity | reflexivity].
    + apply (rng_na_cov2 e He Hd). apply (H19 e He Hna). intros x Hx. apply Hnx. destruct (ae_na e0); [right; exact Hx | exact Hx].
  - intros p q Hp Hq. exact (rng_repl_lazy_res flags p q Hp Hq).
  - apply (LZr_fix ρ (am_maps am) (m_vm_lazy m) (vm_noaccess (m_vmmaps m)) H21 (MR_lazy_nowrap segs fs0 ρ am m HM) H13 e0 He0 rng_ents_disj
             addr nw rng_in_e0 ltac:(rewrite rng_n; exact Hn) ltac:(rewrite rng_addr, rng_n; exact rng_two64) rng_al flags Hbig).
    intros Hf. rewrite rng_addr, rng_n. exact (Hfull Hf).
Qed.

Theorem MR_prot : MRm ρ (add_exp am e0 f n) (mprotect_model_next m addr nw).
Proof.
  pose proof HM as [H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 H17 H18 H19 H20 H21].
  unfold mprotect_model_next. cbv zeta.
  constructor; rewrite ?with_vmmaps_vmmaps_eq, ?with_vmmaps_lazy_eq;
    cbn [add_exp am_maps am_brk0 am_brk am_tid am_shadow am_next am_atop am_out am_exp am_fd
         vm_reserved vm_maps vm_noaccess vm_start_brk vm_brk alloc_top vm_init_sp]; try assumption.
  - apply nowrap_subtract. exact H13.
  - apply rng_na_cov.
    + intros e z [x [Hx Hxe]]. exists x. split; [|exact Hxe]. destruct (ae_na e0); [right; exact Hx | exact Hx].
    + intros z Hz Hna. rewrite Hna. exists (e0, f, n). split; [left; reflexivity|]. cbn [fst snd]. split; [reflexivity | exact Hz].
  - exact rng_na_maps.
  - intros e He Hna Hnx. destruct (aent_eq_dec e e0) as [->|Hd].
    + exfalso. rewrite Hna in Hnx. apply (Hnx (e0, f, n)); [left; reflexivity | reflexivity].
    + apply (rng_na_cov2 e He Hd). apply (H19 e He Hna). intros x Hx. apply Hnx. destruct (ae_na e0); [right; exact Hx | exact Hx].
  - exact (LZr_prot ρ (am_maps am) (m_vm_lazy m) (vm_noaccess (m_vmmaps m)) H21 H13 addr nw rng_al).
Qed.

Theorem MR_none (flags : word) : ae_na e0 = false ->
  (mmap_noreserve_b flags = true -> BIGMIN <= ae_size e0) -> lzfull e0 = false ->
  MRm ρ am (fix_none_model flags addr nw m).
Proof.
  intros Hna0 Hbig Hnfull.
  pose proof HM as [H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 H17 H18 H19 H20 H21].
  assert (Ev : m_vmmaps (fix_none_model flags addr nw m) =
    mkVmMapsFull (vm_reserved (m_vmmaps m)) (vm_maps (m_vmmaps m))
      ((addr, nw) :: maps_subtract (vm_noaccess (m_vmmaps m)) (bv_unsigned addr) (bv_unsigned addr + bv_unsigned nw))
      (vm_start_brk (m_vmmaps m)) (vm_brk (m_vmmaps m)) (vm_limit (m_vmmaps m)) (vm_mmap_base (m_vmmaps m)) (vm_init_sp (m_vmmaps m)))
    by (unfold fix_none_model; rewrite repl_vmmaps_eq, with_vmmaps_vmmaps_eq; reflexivity).
  assert (El : m_vm_lazy (fix_none_model flags addr nw m) = repl_lazy flags addr nw (m_vm_lazy m))
    by (unfold fix_none_model; rewrite repl_lazy_eq, with_vmmaps_lazy_eq; reflexivity).
  constructor; rewrite ?Ev, ?El; cbn [vm_reserved vm_maps vm_noaccess vm_start_brk vm_brk alloc_top vm_init_sp]; try assumption.
  - unfold fix_none_model. rewrite repl_tid. exact H7.
  - unfold fix_none_model. rewrite repl_fds. exact H8.
  - unfold fix_none_model. rewrite repl_fs. exact H9.
  - intros p Hp. exact (rng_repl_lazy_top flags p Hp).
  - apply nowrap_cons; [rewrite bas_mk, bsz_mk, rng_addr, rng_n; exact rng_two64 | apply nowrap_subtract; exact H13].
  - intros e z He Hna Hz Hne. apply inl_cons. right.
    refine (rng_na_cov (am_exp am) (fun e z X => X) _ e z He Hna Hz Hne). intros z' _ Hc. rewrite Hna0 in Hc. discriminate Hc.
  - intros z Hz. apply inl_cons in Hz as [Hz|Hz]; [|exact (rng_na_maps z Hz)].
    rewrite bas_mk, bsz_mk, rng_addr, rng_n in Hz. apply (MR_in_ent_inl segs fs0 ρ am m e0 z HM He0). unfold in_ent. lia.
  - intros e He Hna Hnx. right. assert (Hd : e <> e0) by (intros ->; rewrite Hna0 in Hna; discriminate Hna).
    exact (rng_na_cov2 e He Hd (H19 e He Hna Hnx)).
  - intros p q Hp Hq. exact (rng_repl_lazy_res flags p q Hp Hq).
  - exact (LZr_none ρ (am_maps am) (m_vm_lazy m) (vm_noaccess (m_vmmaps m)) H21 (MR_lazy_nowrap segs fs0 ρ am m HM) H13 e0 He0 rng_ents_disj
             addr nw rng_in_e0 ltac:(rewrite rng_n; exact Hn) ltac:(rewrite rng_addr, rng_n; exact rng_two64) rng_al flags Hbig Hnfull).
Qed.

End Range.

Section Unmap.
Variable ρ : valuation.
Variable am : amodel.
Variable m : Model.
Hypothesis HM : MRm ρ am m.
Variable e0 : aent.
Hypothesis He0 : In e0 (am_maps am).
Hypothesis Hvar : am_shadow am = true -> var_ent e0 = true.
Hypothesis Hnfull : lzfull e0 = false.
Hypothesis Hual : leval ρ (ae_base e0) mod 4096 = 0 /\ ae_size e0 mod 4096 = 0.

Let addr : word := fst (ent_val ρ e0).
Let nw : word := snd (ent_val ρ e0).

Lemma um_ok : ent_ok ρ e0.
Proof. exact (MR_ent segs fs0 ρ am m e0 HM He0). Qed.

Lemma um_addr : bv_unsigned addr = leval ρ (ae_base e0).
Proof. exact (ent_val_bas ρ e0 um_ok). Qed.

Lemma um_n : bv_unsigned nw = ae_size e0.
Proof. exact (ent_val_bsz ρ e0 um_ok). Qed.

Lemma um_other (e : aent) : In e (am_maps am) -> e <> e0 ->
  bas (ent_val ρ e) + bsz (ent_val ρ e) <= bv_unsigned addr \/ bv_unsigned addr + bv_unsigned nw <= bas (ent_val ρ e).
Proof.
  intros He Hne. rewrite um_addr, um_n.
  apply (rng_other_val ρ am m HM e0 He0 (ae_base e0) (ae_size e0)); first [lia | assumption].
Qed.

Lemma um_remove : map_remove (vm_maps (m_vmmaps m)) addr = map (ent_val ρ) (List.filter (fun e => negb (aent_eqb e e0)) (am_maps am)).
Proof.
  rewrite (mr_maps segs fs0 ρ am m HM). unfold map_remove.
  assert (X : forall l, (forall e, In e l -> In e (am_maps am)) ->
    List.filter (fun p => negb (bv_eqb (fst p) addr)) (map (ent_val ρ) l) = map (ent_val ρ) (List.filter (fun e => negb (aent_eqb e e0)) l)).
  { induction l as [|e r IH]; intros Hsub; [reflexivity|]. cbn [map List.filter].
    rewrite (IH (fun e' H' => Hsub e' (or_intror H'))). destruct (aent_eqb e e0) eqn:E.
    - apply aent_eqb_eq in E. subst e. cbn [negb]. fold addr.
      replace (bv_eqb addr addr) with true by (symmetry; apply bv_eqb_eq; reflexivity). reflexivity.
    - cbn [negb map]. assert (Hne : e <> e0) by (intros ->; rewrite aent_eqb_refl in E; discriminate E).
      pose proof (um_other e (Hsub e (or_introl eq_refl)) Hne) as D.
      pose proof (MR_ent segs fs0 ρ am m e HM (Hsub e (or_introl eq_refl))) as Hok.
      destruct (bv_eqb (fst (ent_val ρ e)) addr) eqn:E2; [|reflexivity].
      exfalso. apply bv_eqb_eq in E2. unfold bas at 1 2 in D. rewrite E2 in D.
      rewrite (ent_val_bsz ρ e Hok) in D. destruct Hok as (_ & K & _). destruct um_ok as (_ & K0 & _). rewrite um_n in D. lia. }
  apply X. intros e H. exact H.
Qed.

Theorem MR_unmap : MRm ρ (del_ent am e0) (munmap_model addr nw m).
Proof.
  pose proof HM as [H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 H17 H18 H19 H20 H21].
  pose proof (MR_lazy_nowrap segs fs0 ρ am m HM) as Hlnw.
  assert (Ev : m_vmmaps (munmap_model addr nw m) =
    mkVmMapsFull (vm_reserved (m_vmmaps m)) (map_remove (vm_maps (m_vmmaps m)) addr)
      (maps_subtract (vm_noaccess (m_vmmaps m)) (bv_unsigned addr) (bv_unsigned addr + bv_unsigned nw))
      (vm_start_brk (m_vmmaps m)) (vm_brk (m_vmmaps m)) (vm_limit (m_vmmaps m)) (vm_mmap_base (m_vmmaps m)) (vm_init_sp (m_vmmaps m)))
    by (unfold munmap_model; rewrite destroyed_vmmaps_eq; reflexivity).
  assert (El : m_vm_lazy (munmap_model addr nw m) = maps_subtract (m_vm_lazy m) (bv_unsigned addr) (bv_unsigned addr + bv_unsigned nw))
    by (unfold munmap_model; rewrite destroyed_lazy_eq; reflexivity).
  assert (Hsubm : forall p, In p (map_remove (vm_maps (m_vmmaps m)) addr) -> In p (vm_maps (m_vmmaps m)))
    by (intros p Hp; unfold map_remove in Hp; apply filter_In in Hp as [Hp _]; exact Hp).
  assert (Hfl : forall e, In e (List.filter (fun e => negb (aent_eqb e e0)) (am_maps am)) -> In e (am_maps am) /\ e <> e0).
  { intros e He. apply filter_In in He as [He Hb]. split; [exact He|]. intros ->. rewrite aent_eqb_refl in Hb. discriminate Hb. }
  assert (Hexp : forall e z, e <> e0 -> in_exp ρ (am_exp am) e z -> in_exp ρ (List.filter (fun x => negb (aent_eqb (fst (fst x)) e0)) (am_exp am)) e z).
  { intros e z Hne [x [Hx [Hxe Hz]]]. exists x. split; [|split; assumption]. apply filter_In. split; [exact Hx|].
    rewrite Hxe. destruct (aent_eqb e e0) eqn:E; [apply aent_eqb_eq in E; contradiction | reflexivity]. }
  constructor; rewrite ?Ev, ?El; cbn [del_ent am_maps am_brk0 am_brk am_tid am_shadow am_next am_atop am_out am_exp am_fd
    vm_reserved vm_maps vm_noaccess vm_start_brk vm_brk alloc_top vm_init_sp]; try assumption.
  - exact um_remove.
  - apply Forall_forall. intros e He. exact (MR_ent segs fs0 ρ am m e HM (proj1 (Hfl e He))).
  - intros p Hp. destruct (subtract_within _ _ _ p Hlnw Hp) as (q & Hq & Q1 & Q2). pose proof (H10 q Hq). unfold bas, bsz, alloc_top in *. cbn [vm_init_sp]. lia.
  - intros Hs. destruct (H11 Hs) as (A & B & C). specialize (Hvar Hs).
    assert (N : forall e, In e (am_maps am) -> var_ent e = false -> In e (List.filter (fun e => negb (aent_eqb e e0)) (am_maps am))).
    { intros e He Hv. apply filter_In. split; [exact He|]. destruct (aent_eqb e e0) eqn:E; [|reflexivity].
      apply aent_eqb_eq in E. subst e. rewrite Hvar in Hv. discriminate Hv. }
    split; [|split]; apply N; first [assumption | reflexivity].
  - intros p q Hp Hq. exact (H12 p q (Hsubm p Hp) Hq).
  - apply nowrap_subtract. exact H13.
  - rewrite um_remove. apply pw_disj_sub. rewrite <- H2. exact H14.
  - intros e z He Hna Hz Hne. destruct (Hfl e He) as [He' Hd]. apply (inl_subtract1 _ _ _ z H13). split.
    + apply (H15 e z He' Hna Hz). intros X. exact (Hne (Hexp e z Hd X)).
    + pose proof (um_other e He' Hd) as D. pose proof (MR_ent segs fs0 ρ am m e HM He') as Hok.
      rewrite (ent_val_bas ρ e Hok), (ent_val_bsz ρ e Hok) in D. unfold in_ent in Hz. lia.
  - intros z Hz. apply (inl_subtract1 _ _ _ z H13) in Hz as [Hz Hout].
    destruct (MR_inl_ent segs fs0 ρ am m z HM (H16 z Hz)) as [e [He Hze]].
    assert (Hd : e <> e0). { intros ->. unfold in_ent in Hze. rewrite um_addr, um_n in Hout. lia. }
    rewrite um_remove. exists (ent_val ρ e). split.
    + apply in_map. apply filter_In. split; [exact He|]. destruct (aent_eqb e e0) eqn:E; [apply aent_eqb_eq in E; contradiction | reflexivity].
    + pose proof (MR_ent segs fs0 ρ am m e HM He) as Hok. rewrite (ent_val_bas ρ e Hok), (ent_val_bsz ρ e Hok). exact Hze.
  - intros p Hp. exact (H17 p (Hsubm p Hp)).
  - intros Hs e He Hv. exact (H18 Hs e (proj1 (Hfl e He)) Hv).
  - intros e He Hna Hnx. destruct (Hfl e He) as [He' Hd]. pose proof (MR_ent segs fs0 ρ am m e HM He') as Hok.
    apply piece_keep.
    + apply (H19 e He' Hna). intros x Hx Hxe. apply (Hnx x); [|exact Hxe]. apply filter_In. split; [exact Hx|].
      rewrite Hxe. destruct (aent_eqb e e0) eqn:E; [apply aent_eqb_eq in E; contradiction | reflexivity].
    + rewrite (ent_val_bsz ρ e Hok). exact (proj1 (proj2 Hok)).
    + pose proof (bv_unsigned_in_range 64 nw). lia.
    + exact (um_other e He' Hd).
  - intros p q Hp Hq. exact (res_subtract _ _ _ _ Hlnw H20 p q Hp Hq).
  - pose proof (LZr_unmap ρ (am_maps am) (m_vm_lazy m) (vm_noaccess (m_vmmaps m)) e0 H21 Hlnw H13 He0) as X.
    unfold ent_lo, ent_hi in X. rewrite um_addr, um_n. apply X; [|exact Hnfull | exact (proj1 (proj2 um_ok)) | exact (proj1 Hual)
      | destruct Hual as [U1 U2]; rewrite Z.add_mod, U1, U2 by lia; reflexivity].
    intros e He Hne. pose proof (um_other e He Hne) as D. pose proof (MR_ent segs fs0 ρ am m e HM He) as Hok.
    rewrite (ent_val_bas ρ e Hok), (ent_val_bsz ρ e Hok), um_addr, um_n in D. lia.
Qed.

End Unmap.

End MRFix.
