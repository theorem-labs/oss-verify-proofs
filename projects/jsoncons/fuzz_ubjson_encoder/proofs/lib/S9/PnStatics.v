(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.

From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S9 Require Import PropExec StoreOk HeapIface LibIface L5Defs L5Core.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import PmLayout.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S9 Require Import PmModel PmModelFacts PmStatics.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import PnLayout.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S9 Require Import BMode.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module PNST.

Inductive bax : Type := AX0 | AXc | AXs | AXcs | AXsc.
Definition bax_cat (ax : bax) : bool := match ax with AXc | AXcs | AXsc => true | _ => false end.
Definition bax_dec (ax : bax) : bool := match ax with AXs | AXcs | AXsc => true | _ => false end.

Definition bax_add_cat (ax : bax) : bax := match ax with AX0 => AXc | AXs => AXsc | x => x end.
Definition bax_add_dec (ax : bax) : bax := match ax with AX0 => AXs | AXc => AXcs | x => x end.

Definition bax_le (ax ax' : bax) : Prop :=
  match ax, ax' with
  | AX0, _ => True
  | AXc, (AXc | AXcs) => True
  | AXs, (AXs | AXsc) => True
  | AXcs, AXcs => True
  | AXsc, AXsc => True
  | _, _ => False
  end.
Lemma bax_le_refl ax : bax_le ax ax.
Proof. destruct ax; exact I. Qed.
Lemma bax_le_trans a b c : bax_le a b -> bax_le b c -> bax_le a c.
Proof. destruct a, b, c; cbn; tauto. Qed.
Lemma bax_le_cat ax : bax_le ax (bax_add_cat ax).
Proof. destruct ax; exact I. Qed.
Lemma bax_le_dec ax : bax_le ax (bax_add_dec ax).
Proof. destruct ax; exact I. Qed.
Lemma bax_cat_add ax : bax_cat (bax_add_cat ax) = true.
Proof. destruct ax; reflexivity. Qed.
Lemma bax_dec_add ax : bax_dec (bax_add_dec ax) = true.
Proof. destruct ax; reflexivity. Qed.
Lemma bax_add_cat_id ax : bax_cat ax = true -> bax_add_cat ax = ax.
Proof. destruct ax; cbn; congruence. Qed.
Lemma bax_add_dec_id ax : bax_dec ax = true -> bax_add_dec ax = ax.
Proof. destruct ax; cbn; congruence. Qed.
Lemma bax_le_cat_mono ax ax' : bax_le ax ax' -> bax_cat ax = true -> bax_cat ax' = true.
Proof. destruct ax, ax'; cbn; tauto. Qed.
Lemma bax_le_dec_mono ax ax' : bax_le ax ax' -> bax_dec ax = true -> bax_dec ax' = true.
Proof. destruct ax, ax'; cbn; tauto. Qed.

Record st : Type := ST { st_loc : bool; st_sys : bool; st_ax : bax }.
Definition g0 : st := ST false false AX0.

Definition st_le (g g' : st) : Prop :=
  (st_loc g = true -> st_loc g' = true) /\ (st_sys g = true -> st_sys g' = true) /\ bax_le (st_ax g) (st_ax g').

Definition pn_foot (A : pm_addrs) (AN : PNL.pn_addrs) : list (Z * Z) := pm_foot A ++ PNL.pn_d128_foot AN.

Section Statics.
Variable segs : list Segment. Context {bmK : BMode}.
Variable A : pm_addrs.
Variable AN : PNL.pn_addrs.

Definition bax_list (ax : bax) : list (Z * Z) :=
  let cat := (pa_errcat_dtor A, pa_errcat_obj A) in
  let inf := (PNL.pn_str_dtor AN, PNL.pn_inf_obj AN) in
  let nan := (PNL.pn_str_dtor AN, PNL.pn_nan_obj AN) in
  match ax with AX0 => [] | AXc => [cat] | AXs => [inf; nan] | AXcs => [cat; inf; nan] | AXsc => [inf; nan; cat] end.

Definition bax_drv : Z * Z := (PNL.pn_drv_call AN, PNL.pn_drv_guard AN).

Definition drv_init_cells : list (Z * Z * Z) :=
  let X := pa_atexit A in [(X + 8, 4, 1); (X + 16, 8, X + 24); (X + 32, 8, fst bax_drv); (X + 288, 8, snd bax_drv)].

Definition drv_init_clear : list (Z * Z) :=
  let X := pa_atexit A in [(X, X + 8); (X + 12, X + 16); (X + 24, X + 32); (X + 40, X + 288); (X + 296, X + 544)].

Fixpoint slots_at (M : word -> option byte) (X : Z) (i : Z) (l : list (Z * Z)) : Prop :=
  match l with
  | [] => True
  | (f, a) :: r => L5.u64_at segs M (X + 32 + 8 * i) f /\ L5.u64_at segs M (X + 288 + 8 * i) a /\ slots_at M X (i + 1) r
  end.
Definition batexit_st (M : word -> option byte) (ax : bax) : Prop :=
  let X := pa_atexit A in let l := bax_drv :: bax_list ax in let n := Z.of_nat (length l) in
  L5.img_clear M X (X + 8) /\ L5.u32_at segs M (X + 8) n /\ L5.img_clear M (X + 12) (X + 16)
  /\ L5.u64_at segs M (X + 16) (X + 24) /\ L5.img_clear M (X + 24) (X + 32)
  /\ slots_at M X 0 l /\ L5.img_clear M (X + 32 + 8 * n) (X + 288) /\ L5.img_clear M (X + 288 + 8 * n) (X + 544).

Definition sso_lit (M : word -> option byte) (o n : Z) : Prop := L5.u8_at segs M o (2 * n) /\ L5.defined M (o + 1) n.
Definition bdec_ok (M : word -> option byte) (d : bool) : Prop :=
  if d then L5.u8_at segs M (PNL.pn_inf_guard AN) 1 /\ L5.u8_at segs M (PNL.pn_nan_guard AN) 1
            /\ sso_lit M (PNL.pn_inf_obj AN) 8 /\ sso_lit M (PNL.pn_nan_obj AN) 3
  else L5.img_clear M (PNL.pn_inf_guard AN) (PNL.pn_inf_guard AN + 8) /\ L5.img_clear M (PNL.pn_nan_guard AN) (PNL.pn_nan_guard AN + 8)
       /\ L5.img_clear M (PNL.pn_inf_obj AN) (PNL.pn_inf_obj AN + 24) /\ L5.img_clear M (PNL.pn_nan_obj AN) (PNL.pn_nan_obj AN + 24).

Definition berr_ok (M : word -> option byte) (ax : bax) : Prop :=
  (if bax_cat ax then L5.u8_at segs M (pa_errcat_guard A) 1 else L5.img_clear M (pa_errcat_guard A) (pa_errcat_guard A + 2))
  /\ bdec_ok M (bax_dec ax) /\ batexit_st M ax.

Definition cat_W : list L5.range := [(pa_errcat_guard A, 2); (pa_atexit A, 544)].
Definition dec_W : list L5.range :=
  [(PNL.pn_inf_guard AN, 8); (PNL.pn_nan_guard AN, 8); (PNL.pn_inf_obj AN, 24); (PNL.pn_nan_obj AN, 24); (pa_atexit A, 544)].
Definition berr_W : list L5.range := cat_W ++ dec_W.

Definition ls_ok (g : st) (M : word -> option byte) : Prop :=
  PMST.base_ok segs A M /\ PMST.loc_ok segs A M (st_loc g) /\ PMST.sys_ok segs A M (st_sys g) /\ berr_ok M (st_ax g).

Record addrs_wf : Prop := AWF {
  aw_j : PMST.addrs_wf A;
  aw_infg : 0 <= PNL.pn_inf_guard AN < 2 ^ 40;
  aw_nang : 0 <= PNL.pn_nan_guard AN < 2 ^ 40;
  aw_info : 0 <= PNL.pn_inf_obj AN < 2 ^ 40;
  aw_nano : 0 <= PNL.pn_nan_obj AN < 2 ^ 40;

  aw_apart : pa_errcat_guard A <> pa_atexit A /\ pa_syscat_guard A <> pa_atexit A
             /\ PNL.pn_inf_guard AN <> pa_atexit A /\ PNL.pn_nan_guard AN <> pa_atexit A
             /\ PNL.pn_inf_obj AN <> pa_atexit A /\ PNL.pn_nan_obj AN <> pa_atexit A
             /\ (forall iv, In iv (pa_loc_foot A) -> fst iv <> pa_atexit A)
}.

Definition dep (a : Z) : Prop :=
  (exists iv, In iv (pn_foot A AN) /\ fst iv <= a < snd iv) \/ (pa_canary A <= a < pa_canary A + 8)
  \/ (exists iv, In iv (pm_initc A) /\ fst iv <= a < snd iv).

Lemma dep_of_j a : PMST.dep A a -> dep a.
Proof.
  intros [(iv & Hin & H)|[H|H]]; [left|right; left; exact H|right; right; exact H].
  exists iv. split; [unfold pn_foot; apply in_or_app; left; exact Hin| exact H].
Qed.
Lemma in_foot_d128 iv a : In iv (PNL.pn_d128_foot AN) -> fst iv <= a < snd iv -> dep a.
Proof. intros Hin H. left. exists iv. split; [unfold pn_foot; apply in_or_app; right; exact Hin| exact H]. Qed.
Lemma in_foot_infg a : PNL.pn_inf_guard AN <= a < PNL.pn_inf_guard AN + 8 -> dep a.
Proof. intros H. apply (in_foot_d128 (PNL.pn_inf_guard AN, PNL.pn_inf_guard AN + 8)); [cbn; auto| cbn; lia]. Qed.
Lemma in_foot_info a : PNL.pn_inf_obj AN <= a < PNL.pn_inf_obj AN + 24 -> dep a.
Proof. intros H. apply (in_foot_d128 (PNL.pn_inf_obj AN, PNL.pn_inf_obj AN + 24)); [cbn; auto| cbn; lia]. Qed.
Lemma in_foot_nang a : PNL.pn_nan_guard AN <= a < PNL.pn_nan_guard AN + 8 -> dep a.
Proof. intros H. apply (in_foot_d128 (PNL.pn_nan_guard AN, PNL.pn_nan_guard AN + 8)); [cbn; auto 6| cbn; lia]. Qed.
Lemma in_foot_nano a : PNL.pn_nan_obj AN <= a < PNL.pn_nan_obj AN + 24 -> dep a.
Proof. intros H. apply (in_foot_d128 (PNL.pn_nan_obj AN, PNL.pn_nan_obj AN + 24)); [cbn; auto 6| cbn; lia]. Qed.

Section Frame.
Hypothesis WF : addrs_wf.
Variables M M' : word -> option byte.
Hypothesis AG : forall a, 0 <= a < 2 ^ 64 -> dep a -> M' (Z_to_bv 64 a) = M (Z_to_bv 64 a).
Hypothesis RO : forall a, 65536 <= a < pa_rw_lo A -> M (Z_to_bv 64 a) = None -> M' (Z_to_bv 64 a) = None.

Lemma clear_depB lo hi : 0 <= lo -> hi < 2 ^ 47 -> (forall a, lo <= a < hi -> dep a) -> L5.img_clear M lo hi -> L5.img_clear M' lo hi.
Proof. intros Hlo Hhi D C i Hi. rewrite AG; [apply C; exact Hi| lia| apply D; exact Hi]. Qed.
Lemma u8_depB a v : 0 <= a < 2 ^ 47 -> dep a -> L5.u8_at segs M a v -> L5.u8_at segs M' a v.
Proof. intros Ha D. apply (L5C.u8_at_agree segs M M'); [|lia|lia]. intros i Hi. apply AG; [lia|]. replace i with a by lia. exact D. Qed.
Lemma u32_depB a v : 0 <= a < 2 ^ 47 -> (forall i, a <= i < a + 4 -> dep i) -> L5.u32_at segs M a v -> L5.u32_at segs M' a v.
Proof.
  intros Ha D H. unfold L5.u32_at in *. rewrite (L5C.rdn_agree segs M M' 4%nat a); [exact H|lia|cbn; lia|].
  intros i Hi. apply AG; [cbn in Hi; lia|]. apply D. cbn in Hi. lia.
Qed.
Lemma u64_depB a v : 0 <= a < 2 ^ 47 -> (forall i, a <= i < a + 8 -> dep i) -> L5.u64_at segs M a v -> L5.u64_at segs M' a v.
Proof. intros Ha D. apply (L5C.u64_at_agree segs M M'); [|lia|lia]. intros i Hi. apply AG; [lia|]. apply D. exact Hi. Qed.
Lemma vstr_depB o s : 0 <= o < 2 ^ 40 -> (forall i, o <= i < o + 24 -> dep i) -> (exists n, s = PM.VShort n) ->
  PM.vstr_at segs (fun _ _ _ => True) M o s -> PM.vstr_at segs (fun _ _ _ => True) M' o s.
Proof.
  intros Ho D (n0 & E) H.
  apply (PMF.vstr_at_agree segs M M' o s); [lia|lia| |intros c n p E'; congruence| exact H].
  intros i Hi. apply AG; [lia| apply D; exact Hi].
Qed.

Local Ltac cdepB tac := lazymatch goal with |- L5.img_clear _ ?lo ?hi => apply (clear_depB lo hi); [lia| lia| tac| try assumption] end.

Lemma slots_frame X l : 0 <= X < 2 ^ 40 -> (forall a, X <= a < X + 544 -> dep a) ->
  forall i, 0 <= i -> i + Z.of_nat (length l) <= 32 -> slots_at M X i l -> slots_at M' X i l.
Proof.
  intros HX D. induction l as [|[f a] r IH]; intros i Hi Hl; cbn [slots_at]; [tauto|].
  cbn [length] in Hl. rewrite Nat2Z.inj_succ in Hl. intros (F & Ar & S). split; [|split].
  - apply u64_depB; [lia| intros; apply D; lia| exact F].
  - apply u64_depB; [lia| intros; apply D; lia| exact Ar].
  - apply (IH (i + 1)); [lia| lia| exact S].
Qed.

Lemma batexit_frame ax : batexit_st M ax -> batexit_st M' ax.
Proof.
  pose proof (PMST.aw_atexit A (aw_j WF)) as HX.
  assert (D : forall a, pa_atexit A <= a < pa_atexit A + 544 -> dep a) by (intros; apply dep_of_j, PMST.in_foot_atexit; lia).
  unfold batexit_st. cbv zeta.
  assert (LEN : Z.of_nat (length (bax_drv :: bax_list ax)) <= 4) by (destruct ax; cbn; lia).
  assert (LEN1 : 1 <= Z.of_nat (length (bax_drv :: bax_list ax))) by (cbn [length]; lia).
  intros (C1 & S & C2 & H & C3 & SL & C4 & C5).
  split; [cdepB ltac:(intros; apply D; lia)|].
  split; [apply u32_depB; [lia| intros; apply D; lia| exact S]|].
  split; [cdepB ltac:(intros; apply D; lia)|].
  split; [apply u64_depB; [lia| intros; apply D; lia| exact H]|].
  split; [cdepB ltac:(intros; apply D; lia)|].
  split; [apply (slots_frame (pa_atexit A) (bax_drv :: bax_list ax)); [lia| exact D| lia| lia| exact SL]|].
  split; cdepB ltac:(intros; apply D; lia).
Qed.

Lemma bdec_frame d : bdec_ok M d -> bdec_ok M' d.
Proof.
  pose proof (aw_infg WF). pose proof (aw_nang WF). pose proof (aw_info WF). pose proof (aw_nano WF).
  unfold bdec_ok. destruct d.
  - intros (G1 & G2 & S1 & S2). split; [|split; [|split]].
    + apply u8_depB; [lia| apply in_foot_infg; lia| exact G1].
    + apply u8_depB; [lia| apply in_foot_nang; lia| exact G2].
    + destruct S1 as (S1a & S1b). split; [apply u8_depB; [lia| apply in_foot_info; lia| exact S1a]|].
      apply (L5C.defined_agree M M'); [| exact S1b]. intros i Hi. apply AG; [lia| apply in_foot_info; lia].
    + destruct S2 as (S2a & S2b). split; [apply u8_depB; [lia| apply in_foot_nano; lia| exact S2a]|].
      apply (L5C.defined_agree M M'); [| exact S2b]. intros i Hi. apply AG; [lia| apply in_foot_nano; lia].
  - intros (C1 & C2 & C3 & C4). split; [|split; [|split]].
    + cdepB ltac:(intros; apply in_foot_infg; lia).
    + cdepB ltac:(intros; apply in_foot_nang; lia).
    + cdepB ltac:(intros; apply in_foot_info; lia).
    + cdepB ltac:(intros; apply in_foot_nano; lia).
Qed.

Lemma berr_frame ax : berr_ok M ax -> berr_ok M' ax.
Proof.
  pose proof (PMST.aw_errg A (aw_j WF)) as Heg.
  intros (ERG & DEC & ATX). split; [|split; [apply bdec_frame; exact DEC| apply batexit_frame; exact ATX]].
  destruct (bax_cat ax).
  - apply u8_depB; [lia| apply dep_of_j, PMST.in_foot_errg; lia| exact ERG].
  - cdepB ltac:(intros; apply dep_of_j, PMST.in_foot_errg; lia).
Qed.

Lemma ls_ok_frameB g : ls_ok g M -> ls_ok g M'.
Proof.
  intros ((RO0 & (can & Hcan & CAN) & NL & LL) & LOC & SYS & ERR).
  pose proof (aw_j WF) as WJ.
  pose proof (PMST.aw_rw A WJ) as Hrw. pose proof (PMST.aw_canary A WJ) as Hcn. pose proof (PMST.aw_sysg A WJ) as Hsg.
  pose proof (PMST.aw_gloc A WJ) as Hgl. pose proof (PMST.aw_nl A WJ) as Hnl. pose proof (PMST.aw_ll A WJ) as Hll.
  split; [|split; [|split]].
  - split; [|split; [|split]].
    + intros i Hi. apply RO; [exact Hi| apply RO0; exact Hi].
    + exists can. split; [exact Hcan|]. apply u64_depB; [lia| intros i Hi; right; left; exact Hi| exact CAN].
    + cdepB ltac:(intros; apply dep_of_j, PMST.in_foot_nl; lia).
    + cdepB ltac:(intros; apply dep_of_j, PMST.in_foot_ll; lia).
  - unfold PMST.loc_ok in *. destruct (st_loc g).
    + destruct LOC as (G & P). destruct (PMST.aw_gloc_in A WJ) as (iv & Hin & Hlo & Hhi). split.
      * apply u8_depB; [lia| apply dep_of_j, (PMST.in_foot_loc A iv); [exact Hin| lia]| exact G].
      * apply u64_depB; [lia| intros i Hi; apply dep_of_j, (PMST.in_foot_loc A iv); [exact Hin| lia]| exact P].
    + intros iv Hin. destruct (PMST.aw_locfoot A WJ iv Hin) as [L1 L2].
      apply (clear_depB (fst iv) (snd iv)); [lia| lia| intros a Ha; apply dep_of_j, (PMST.in_foot_loc A iv); assumption| apply LOC; exact Hin].
  - unfold PMST.sys_ok in *. destruct (st_sys g).
    + apply u8_depB; [lia| apply dep_of_j, PMST.in_foot_sysg; lia| exact SYS].
    + cdepB ltac:(intros; apply dep_of_j, PMST.in_foot_sysg; lia).
  - apply berr_frame. exact ERR.
Qed.
End Frame.

Lemma pn_statics_exit g M : ls_ok g M -> batexit_st M (st_ax g) /\ bdec_ok M (bax_dec (st_ax g)).
Proof. intros (_ & _ & _ & (_ & D & X)). split; [exact X| exact D]. Qed.

Definition TopLS : lib_statics := {| ls_state := st; LibIface.ls_ok := ls_ok; ls_g0 := g0 |}.

Record lay_ok (Lay : lib_layout) : Prop := LAYOK {
  lk_segs : hl_segs (ll_heap Lay) = segs;
  lk_foot : ll_foot Lay = pn_foot A AN;
  lk_rw : ll_rw_lo Lay = pa_rw_lo A;
  lk_guard : ll_guard Lay = pa_canary A;
  lk_guard_initc : exists iv, In iv (ll_initc Lay) /\ fst iv <= pa_canary A /\ pa_canary A + 8 <= snd iv;
  lk_initc : forall iv, In iv (pm_initc A) -> exists iv', In iv' (ll_initc Lay) /\ fst iv' <= fst iv /\ snd iv <= snd iv';
  lk_init_initc : forall iv, In iv (pm_initc A) -> exists iv', In iv' (ll_init_img Lay) /\ fst iv' <= fst iv /\ snd iv <= snd iv';
  lk_init_ro : exists iv, In iv (ll_init_img Lay) /\ fst iv <= 65536 /\ pa_rw_lo A <= snd iv;

  lk_init_foot : forall iv, In iv (pn_foot A AN) -> fst iv = pa_atexit A \/ exists iv', In iv' (ll_init_img Lay) /\ fst iv' <= fst iv /\ snd iv <= snd iv';

  lk_init_ax : forall iv, In iv drv_init_clear -> exists iv', In iv' (ll_init_img Lay) /\ fst iv' <= fst iv /\ snd iv <= snd iv';
  lk_init_cells : ll_init_cells Lay = drv_init_cells
}.

Lemma pn_statics_frame Lay : addrs_wf -> lay_ok Lay -> lib_statics_frame Lay TopLS.
Proof.
  intros WF LK g M M' H FOOT RO INITC. cbn [LibIface.ls_ok TopLS] in *.
  apply (ls_ok_frameB WF M M'); [| |exact H].
  - intros a Ha [(iv & Hin & Hr)|[Hc|(iv & Hin & Hr)]].
    + apply FOOT; [exact Ha|]. exists iv. rewrite (lk_foot Lay LK). split; assumption.
    + apply INITC; [exact Ha|]. left. destruct (lk_guard_initc Lay LK) as (iv & Hin & H1 & H2). exists iv. split; [exact Hin| lia].
    + apply INITC; [exact Ha|]. left. destruct (lk_initc Lay LK iv Hin) as (iv' & Hin' & H1 & H2). exists iv'. split; [exact Hin'| lia].
  - intros a Ha Hn. pose proof (PMST.aw_rw A (aw_j WF)) as RW. apply RO; [rewrite (lk_rw Lay LK), L5.unsigned_lit by lia; lia| exact Hn].
Qed.

Lemma pn_statics_init Lay : addrs_wf -> lay_ok Lay -> lib_statics_init Lay TopLS.
Proof.
  intros WF LK av uid rnd tid canary hw M IF. cbn [LibIface.ls_ok TopLS ls_g0].
  unfold lib_init_facts in IF. cbv zeta in IF.
  pose proof (aw_apart WF) as (APe & APs & APig & APng & APio & APno & APloc).
  destruct IF as (IMG & _ & _ & _ & _ & _ & _ & GU & HC & REST).

  assert (CELLS : Forall (fun c : Z * Z * Z => cellz (hl_segs (ll_heap Lay)) M (fst (fst c)) (Z.to_nat (snd (fst c))) (snd c)) drv_init_cells).
  { rewrite <- (lk_init_cells Lay LK). repeat match type of REST with _ /\ _ => apply proj2 in REST end. exact REST. }
  rewrite (lk_segs Lay LK) in CELLS. unfold drv_init_cells in CELLS. cbv zeta in CELLS.
  pose proof (proj1 (Forall_cons_iff _ _ _) CELLS) as (C_slot & CELLS1).
  pose proof (proj1 (Forall_cons_iff _ _ _) CELLS1) as (C_head & CELLS2).
  pose proof (proj1 (Forall_cons_iff _ _ _) CELLS2) as (C_f0 & CELLS3).
  pose proof (proj1 (Forall_cons_iff _ _ _) CELLS3) as (C_a0 & _). clear CELLS CELLS1 CELLS2 CELLS3.
  cbn [fst snd Z.to_nat Pos.to_nat Pos.iter_op Nat.add] in C_slot, C_head, C_f0, C_a0. unfold cellz in C_slot, C_head, C_f0, C_a0.

  assert (CL : forall iv, In iv (pn_foot A AN) -> fst iv <> pa_atexit A -> L5.img_clear M (fst iv) (snd iv)).
  { intros iv Hin Hne. destruct (lk_init_foot Lay LK iv Hin) as [E|(iv' & Hin' & H1 & H2)]; [contradiction|]. intros i Hi. apply (IMG iv' i Hin'). lia. }
  assert (CLJ : forall iv, In iv (pm_foot A) -> fst iv <> pa_atexit A -> L5.img_clear M (fst iv) (snd iv)).
  { intros iv Hin Hne. apply CL; [unfold pn_foot; apply in_or_app; left; exact Hin| exact Hne]. }
  assert (CLD : forall iv, In iv (PNL.pn_d128_foot AN) -> fst iv <> pa_atexit A -> L5.img_clear M (fst iv) (snd iv)).
  { intros iv Hin Hne. apply CL; [unfold pn_foot; apply in_or_app; right; exact Hin| exact Hne]. }
  assert (CLX : forall iv, In iv drv_init_clear -> L5.img_clear M (fst iv) (snd iv)).
  { intros iv Hin. destruct (lk_init_ax Lay LK iv Hin) as (iv' & Hin' & H1 & H2). intros i Hi. apply (IMG iv' i Hin'). lia. }
  unfold ls_ok, g0. cbn [st_loc st_sys st_ax].
  split; [|split; [|split]].
  - split; [|split; [|split]].
    + destruct (lk_init_ro Lay LK) as (iv & Hin & H1 & H2). intros i Hi. apply (IMG iv i Hin). lia.
    + exists canary. split; [exact HC|]. unfold cellz in GU. rewrite (lk_guard Lay LK), (lk_segs Lay LK) in GU. exact GU.
    + destruct (lk_init_initc Lay LK (pa_need_locks A, pa_need_locks A + 1) ltac:(cbn; auto)) as (iv' & Hin' & H1 & H2).
      intros i Hi. apply (IMG iv' i Hin'). cbn [fst snd] in *. lia.
    + destruct (lk_init_initc Lay LK (pa_locale_lock A, pa_locale_lock A + 4) ltac:(cbn; auto)) as (iv' & Hin' & H1 & H2).
      intros i Hi. apply (IMG iv' i Hin'). cbn [fst snd] in *. lia.
  - unfold PMST.loc_ok. intros iv Hin. apply CLJ; [unfold pm_foot; cbn [app]; right; right; apply in_or_app; left; exact Hin| exact (APloc iv Hin)].
  - unfold PMST.sys_ok. apply (CLJ (pa_syscat_guard A, pa_syscat_guard A + 2)); [unfold pm_foot; cbn; auto| exact APs].
  - unfold berr_ok. cbn [bax_cat bax_dec]. split; [|split].
    + apply (CLJ (pa_errcat_guard A, pa_errcat_guard A + 2)); [unfold pm_foot; cbn; auto| exact APe].
    + unfold bdec_ok. split; [|split; [|split]].
      * apply (CLD (PNL.pn_inf_guard AN, PNL.pn_inf_guard AN + 8)); [cbn; auto| exact APig].
      * apply (CLD (PNL.pn_nan_guard AN, PNL.pn_nan_guard AN + 8)); [cbn; auto| exact APng].
      * apply (CLD (PNL.pn_inf_obj AN, PNL.pn_inf_obj AN + 24)); [cbn; auto| exact APio].
      * apply (CLD (PNL.pn_nan_obj AN, PNL.pn_nan_obj AN + 24)); [cbn; auto 8| exact APno].
    +
      unfold batexit_st, bax_list, bax_drv. cbn [length fst snd slots_at app]. change (Z.of_nat 1) with 1.
      replace (pa_atexit A + 32 + 8 * 1) with (pa_atexit A + 40) by lia. replace (pa_atexit A + 288 + 8 * 1) with (pa_atexit A + 296) by lia.
      split; [apply (CLX (pa_atexit A, pa_atexit A + 8)); cbn; auto|].
      split; [exact C_slot|].
      split; [apply (CLX (pa_atexit A + 12, pa_atexit A + 16)); cbn; auto|].
      split; [exact C_head|].
      split; [apply (CLX (pa_atexit A + 24, pa_atexit A + 32)); cbn; auto 6|].
      split; [split; [| split; [| exact I]]; [rewrite Z.mul_0_r, Z.add_0_r; exact C_f0 | rewrite Z.mul_0_r, Z.add_0_r; exact C_a0]|].
      split; [apply (CLX (pa_atexit A + 40, pa_atexit A + 288)); cbn; auto 8|].
      apply (CLX (pa_atexit A + 296, pa_atexit A + 544)); cbn; auto 10.
Qed.

End Statics.
End PNST.
