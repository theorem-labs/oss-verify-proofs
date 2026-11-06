(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib Require Import ShapeAlg.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Import PropExec MState Mem Cells Step Frame.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Import Ceil.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT Require Import LMeasure LBase.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT Require LSCPS.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.LSCPS.LStep.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT Require Import LSCPS.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT Require LSCPS2.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.LSCPS2.LNodesMM.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require Import BImg.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.AS Require PropExec AsanAcct AxSymExec3 AxSymExec3Sound AsanPlanCore AsanPlan AsanPlanSound BothPlanImages BackingAlgebra.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Import NElim.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Module APS := AS.AsanPlanSound.APS.
Module AP := AS.AsanPlan.AP.
Module AX2 := AS.AxSymExec3.AX2.
Module ACC := AS.AsanAcct.

Local Notation BSEGS := AS.BothPlanImages.BSEGS (only parsing).
(* [comment removed for export] *)
Lemma bsegs_no_wx : no_wx bsegs.
Proof.
  split; intros s Hs; cbn in Hs; destruct Hs as [<-|[<-|[<-|[<-|[]]]]];
    first [reflexivity | vm_compute; reflexivity | (vm_compute; lia)].
Qed.

(* [comment removed for export] *)
Lemma bsegs_layout :
  List.map (fun s => (Z.of_N (seg_base s), Z.of_N (seg_size s))) bsegs
  = [(0x10000, 0x20000); (0x30000, 0x71000); (0xa1000, 0x2000); (0xa3000, 0x55c000)].
Proof. vm_compute. reflexivity. Qed.

Lemma noseg_iff_hull : forall x : word, noseg bsegs x <-> ~ (0x10000 <= bv_unsigned x < 0x5ff000).
Proof.
  intros x. unfold noseg.
  assert (H : forall P : Segment -> Prop,
            (forall s, In s bsegs -> P s) <-> Forall P bsegs) by (intros; symmetry; apply Forall_forall).
  rewrite H. clear H.
  assert (E : forall P : Z * Z -> Prop,
     Forall (fun s => P (Z.of_N (seg_base s), Z.of_N (seg_size s))) bsegs <->
     Forall P (List.map (fun s => (Z.of_N (seg_base s), Z.of_N (seg_size s))) bsegs)).
  { intros P. rewrite Forall_map. reflexivity. }
  specialize (E (fun p => ~ (fst p <= bv_unsigned x < fst p + snd p))). cbn [fst snd] in E. rewrite E, bsegs_layout.
  split.
  - intros F. repeat (apply Forall_cons_iff in F as [? F]). cbn [fst snd] in *. lia.
  - intros N. repeat constructor; cbn [fst snd]; lia.
Qed.

Section Core.
Context {ACEIL : Ceil}.
Variables (LIMIT : Z) (SINV : AX2.env -> (word -> option byte) -> Prop) (argH : AX2.env -> word -> bool) (FS0 : Fs.Fs).
Variables (E : AX2.env) (cs : AP.acs) (R : bvmap 5 word) (FULL : word -> option byte) (model : Model).
Hypothesis HC : APS.cs_ok BSEGS AP.BOTH LIMIT SINV argH FS0 E cs R FULL model.
(* [comment removed for export] *)
Hypothesis HTOP : APS.atop model = alloc_ceiling.
Hypothesis HargH_hi : forall a, argH E a = true -> alloc_ceiling <= bv_unsigned a.

Local Notation maps := (vm_maps (m_vmmaps model)).
Local Notation na := (vm_noaccess (m_vmmaps model)).
Local Notation L := (m_vm_lazy model).

(* [comment removed for export] *)
(* [comment removed for export] *)

Definition clip (r : Z * Z) : Z * Z := (fst r, Z.min (snd r) (2^64)).
Definition G0 : gwin := List.map clip (APS.allowA AP.BOTH E cs).
Definition R0 : Z := Z.max 0 (LIMIT - AP.a_eager cs - AP.a_abytes cs).
Definition g0 : lghost := mkG G0 R0.

(* [comment removed for export] *)
Definition keepb (x : word) : bool :=
  if in_rangesb L x then in_winb G0 x else (APS.vis AP.BOTH E cs model x || argH E x).
Definition jvis : word -> option byte := fun x => if keepb x then FULL x else None.

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma in_ivs_rangesb : forall l (x : word), APS.in_ivs (bv_unsigned x) l = in_rangesb l x.
Proof. reflexivity. Qed.

Lemma lazy_entry : forall x, in_rangesb L x = true ->
  exists lo sz, In (lo, sz) L /\ bv_unsigned lo <= bv_unsigned x < bv_unsigned lo + bv_unsigned sz
    /\ bv_unsigned lo mod 4096 = 0 /\ bv_unsigned sz mod 4096 = 0
    /\ (bv_unsigned lo + bv_unsigned sz <= 0x10000 \/ 0x5ff000 <= bv_unsigned lo) /\ bv_unsigned lo + bv_unsigned sz <= alloc_ceiling
    /\ exists b k, In (b, k) maps /\ bv_unsigned b <= bv_unsigned lo /\ bv_unsigned lo + bv_unsigned sz <= bv_unsigned b + bv_unsigned k.
Proof.
  intros x Hx. apply in_rangesb_true in Hx as (lo & sz & Hin & Hb). exists lo, sz. split; [exact Hin|]. split; [exact Hb|].
  (nelimp (proj1 (Forall_forall _ _) (APS.co_lazywf _ _ _ _ _ _ _ _ _ _ _ HC) _ Hin) 7%nat; intros A1 A2 A3 [b k] Hm B1 B2).
  pose proof (proj1 (Forall_forall _ _) (APS.co_lazyb _ _ _ _ _ _ _ _ _ _ _ HC) _ Hin) as [C1 C2].
  unfold APS.hull_clear in C1. rewrite HTOP in C2. change (AS.AsanPlanCore.APC.img_lo AP.BOTH) with 0x10000 in C1.
  change (AS.AsanPlanCore.APC.img_hi AP.BOTH) with 0x5ff000 in C1.
  cbn [fst snd] in *. repeat (split; [assumption|]). exists b, k. auto.
Qed.

Lemma img_hi_val : AS.AsanPlanCore.APC.img_hi AP.BOTH = 0x5ff000. Proof. reflexivity. Qed.
Lemma img_lo_val : AS.AsanPlanCore.APC.img_lo AP.BOTH = 0x10000. Proof. reflexivity. Qed.

Lemma lazy_noseg_x : forall x, in_rangesb L x = true -> noseg bsegs x.
Proof.
  intros x Hx. (nelim (lazy_entry x Hx) 9%nat; intros lo sz _ Hb _ _ C1 C2 _).
  apply noseg_iff_hull. lia.
Qed.

Lemma lazy_below_ceil : forall x, in_rangesb L x = true -> bv_unsigned x < alloc_ceiling.
Proof. intros x Hx. (nelim (lazy_entry x Hx) 9%nat; intros lo sz _ Hb _ _ _ C2 _). lia. Qed.

Lemma lazy_in_maps : forall x, in_rangesb L x = true -> in_rangesb maps x = true.
Proof.
  intros x Hx. (nelim (lazy_entry x Hx) 13%nat; intros lo sz _ Hb _ _ _ _ b k Hm B1 B2).
  apply in_rangesb_true. exists b, k. split; [exact Hm| lia].
Qed.

(* [comment removed for export] *)
Lemma lazy_page : forall x, in_rangesb L x = true -> page_in_ranges (page_base x) L = true.
Proof.
  intros x Hx. (nelim (lazy_entry x Hx) 9%nat; intros lo sz Hin Hb A1 A2 _ C2 _).
  unfold page_in_ranges. apply existsb_exists. exists (lo, sz). split; [exact Hin|]. cbn [fst snd].
  rewrite page_base_unsigned, page_size_eq. pose proof (@alloc_ceiling_hi ACEIL) as CH.
  pose proof (bv_unsigned_in_range 64 x).
  apply andb_true_iff. split; [apply Z.leb_le| apply Z.leb_le]; Z.div_mod_to_equations; nia.
Qed.

Lemma page_lazy : forall x, page_in_ranges (page_base x) L = true -> in_rangesb L x = true.
Proof.
  intros x Hx. unfold page_in_ranges in Hx. apply existsb_exists in Hx as ([lo sz] & Hin & Hb). cbn [fst snd] in Hb.
  apply andb_true_iff in Hb as [B1 B2]. apply Z.leb_le in B1. apply Z.leb_le in B2.
  rewrite page_base_unsigned, page_size_eq in *. pose proof (bv_unsigned_in_range 64 x).
  pose proof (proj1 (Forall_forall _ _) (APS.co_lazyb _ _ _ _ _ _ _ _ _ _ _ HC) _ Hin) as [C1 C2]. cbn [fst snd] in C1, C2.
  rewrite HTOP in C2. pose proof (@alloc_ceiling_hi ACEIL) as CH.
  apply in_rangesb_true. exists lo, sz. split; [exact Hin|]. Z.div_mod_to_equations. lia.
Qed.

Lemma hull_vis : forall x, ~ noseg bsegs x -> APS.in_hull AP.BOTH (bv_unsigned x) = true.
Proof.
  intros x Hx. unfold APS.in_hull. rewrite img_lo_val, img_hi_val.
  destruct (Z.le_gt_cases 0x10000 (bv_unsigned x)); destruct (Z.lt_ge_cases (bv_unsigned x) 0x5ff000);
    try (exfalso; apply Hx; apply noseg_iff_hull; lia).
  apply andb_true_iff. split; [apply Z.leb_le| apply Z.ltb_lt]; lia.
Qed.

Lemma hull_seg : forall x, APS.in_hull AP.BOTH (bv_unsigned x) = true -> ~ noseg bsegs x.
Proof.
  intros x Hx Hn. apply noseg_iff_hull in Hn. unfold APS.in_hull in Hx. rewrite img_lo_val, img_hi_val in Hx.
  apply andb_true_iff in Hx as [A B]. apply Z.leb_le in A. apply Z.ltb_lt in B. lia.
Qed.

(* [comment removed for export] *)
Lemma allow1_win : forall p z, In p (AP.a_vis cs ++ AP.a_ghost cs) -> 0 <= z < 2^64 ->
  (APS.uE E (fst p) <= z < APS.uE E (fst p) + APS.uE E (snd p)
   \/ APS.sh_lo AP.BOTH E p <= z < APS.sh_hi AP.BOTH E p) ->
  in_winb G0 (Z_to_bv 64 z) = true.
Proof.
  intros p z Hin Hz Hr. unfold G0, APS.allowA. unfold in_winb. apply existsb_exists.
  rewrite (unsigned_lit z) by lia.
  destruct Hr as [Hr|Hr].
  - exists (clip (APS.pagedown (APS.uE E (fst p)), APS.pageup (APS.uE E (fst p) + APS.uE E (snd p)))). split.
    + apply in_map. apply in_flat_map. exists p. split; [exact Hin|]. left. reflexivity.
    + cbn [clip fst snd]. pose proof (APS.pagedown_le (APS.uE E (fst p))). pose proof (APS.pageup_ge (APS.uE E (fst p) + APS.uE E (snd p))).
      apply andb_true_iff. split; [apply Z.leb_le| apply Z.ltb_lt]; lia.
  - exists (clip (APS.pagedown (APS.sh_lo AP.BOTH E p), APS.pageup (APS.sh_hi AP.BOTH E p))). split.
    + apply in_map. apply in_flat_map. exists p. split; [exact Hin|]. right. left. reflexivity.
    + cbn [clip fst snd]. pose proof (APS.pagedown_le (APS.sh_lo AP.BOTH E p)). pose proof (APS.pageup_ge (APS.sh_hi AP.BOTH E p)).
      apply andb_true_iff. split; [apply Z.leb_le| apply Z.ltb_lt]; lia.
Qed.

Lemma in_allow_win : forall x, APS.in_allow AP.BOTH E cs (bv_unsigned x) = true -> in_winb G0 x = true.
Proof.
  intros x H. pose proof (bv_unsigned_in_range 64 x) as Rx. change (bv_modulus 64) with (2^64) in Rx.
  rewrite <- (Z_to_bv_bv_unsigned x). unfold APS.in_allow in H. apply orb_true_iff in H as [H|H].
  - unfold APS.in_vis in H. apply existsb_exists in H as (p & Hin & Hb). apply andb_true_iff in Hb as [A B].
    apply Z.leb_le in A. apply Z.ltb_lt in B. apply (allow1_win p); [apply in_or_app; left; exact Hin| lia| left; lia].
  - unfold APS.in_sh in H. apply existsb_exists in H as (p & Hin & Hb). apply andb_true_iff in Hb as [A B].
    apply Z.leb_le in A. apply Z.ltb_lt in B. apply (allow1_win p); [apply in_or_app; left; exact Hin| lia| right; lia].
Qed.

Lemma in_ghost_win : forall x, APS.in_ghost E cs (bv_unsigned x) = true -> in_winb G0 x = true.
Proof.
  intros x H. pose proof (bv_unsigned_in_range 64 x) as Rx. change (bv_modulus 64) with (2^64) in Rx.
  rewrite <- (Z_to_bv_bv_unsigned x). unfold APS.in_ghost in H. apply existsb_exists in H as (p & Hin & Hb).
  apply andb_true_iff in Hb as [A B]. apply Z.leb_le in A. apply Z.ltb_lt in B.
  apply (allow1_win p); [apply in_or_app; right; exact Hin| lia| left; lia].
Qed.

(* [comment removed for export] *)
Lemma vis_lazy_win : forall x, APS.vis AP.BOTH E cs model x = true -> in_rangesb L x = true -> in_winb G0 x = true.
Proof.
  intros x Hv Hl. unfold APS.vis in Hv. cbv zeta in Hv.
  apply orb_true_iff in Hv as [Hv|Hv]; [apply orb_true_iff in Hv as [Hv|Hv]|].
  - exfalso. apply (hull_seg x Hv). apply lazy_noseg_x. exact Hl.
  - apply Z.leb_le in Hv. rewrite HTOP in Hv. pose proof (lazy_below_ceil x Hl). lia.
  - apply andb_true_iff in Hv as [_ Hv]. apply orb_true_iff in Hv as [Hv|Hv].
    + rewrite (lazy_page x Hl) in Hv. discriminate.
    + apply in_allow_win. exact Hv.
Qed.

Lemma argH_not_lazy : forall x, argH E x = true -> in_rangesb L x = false.
Proof.
  intros x Ha. destruct (in_rangesb L x) eqn:El; [|reflexivity]. exfalso.
  pose proof (HargH_hi x Ha). pose proof (lazy_below_ceil x El). lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma seps_pwd : forall l, APS.seps l -> pwd l.
Proof.
  intros l H. induction H as [| p l Hp H IH]; [constructor|]. constructor; [| exact IH].
  intros e' He'. pose proof (proj1 (Forall_forall _ _) Hp e' He') as D. unfold APS.iv_disjoint in D. unfold rdisj, uz. exact D.
Qed.

Lemma LOK_of_cs_ok : LOK bsegs model.
Proof.
  (nelimp (APS.co_wf _ _ _ _ _ _ _ _ _ _ _ HC) 4%nat; intros W1 W2 W3 W4).
  constructor.
  - exact (APS.co_halt _ _ _ _ _ _ _ _ _ _ _ HC).
  - exact (APS.co_res _ _ _ _ _ _ _ _ _ _ _ HC).
  - (* [comment removed for export] *) exact HTOP.
  - intros b k Hin. (nelimp (proj1 (Forall_forall _ _) (APS.co_bounds _ _ _ _ _ _ _ _ _ _ _ HC) _ Hin) 6%nat; intros _ _ _ _ _ Hc).
    cbn [fst snd] in Hc. rewrite HTOP in Hc. exact Hc.
  - apply seps_pwd. exact (APS.co_seps _ _ _ _ _ _ _ _ _ _ _ HC).
  - intros b k Hin. pose proof (W2 (b, k) Hin) as Hw. unfold AS.BackingAlgebra.iv_wf, AS.BackingAlgebra.B, AS.BackingAlgebra.S in Hw. cbn [fst snd] in Hw. exact Hw.
  - intros lo sz Hin. pose proof (proj1 (Forall_forall _ _) (APS.co_lazyb _ _ _ _ _ _ _ _ _ _ _ HC) _ Hin) as [_ C2]. cbn [fst snd] in C2.
    rewrite HTOP in C2. exact C2.
  - exact lazy_noseg_x.
  - exact lazy_in_maps.
  - intros x Hx. rewrite <- !in_ivs_rangesb in *. apply (APS.co_nasub _ _ _ _ _ _ _ _ _ _ _ HC). exact Hx.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma allowA_aligned : Forall (fun r => 0 <= fst r < 2^64 /\ fst r <= snd r /\ fst r mod 4096 = 0 /\ snd r mod 4096 = 0) (APS.allowA AP.BOTH E cs).
Proof.
  unfold APS.allowA. apply Forall_flat_map. apply Forall_forall. intros p _. unfold APS.allow1.
  pose proof (bv_unsigned_in_range 64 (AX2.edenot E (fst p))) as R1. pose proof (bv_unsigned_in_range 64 (AX2.edenot E (snd p))) as R2.
  unfold APS.uE, APS.sh_lo, APS.sh_hi, APS.uE. change (AS.AsanPlanCore.APC.shadow_off AP.BOTH) with 0x7fff8000.
  change (bv_modulus 64) with (2^64) in R1, R2.
  constructor; [| constructor; [| constructor]]; cbn [fst snd]; unfold APS.pagedown, APS.pageup; Z.div_mod_to_equations; lia.
Qed.

Lemma G0_ok : Forall win_ok G0.
Proof.
  unfold G0. apply Forall_map. eapply Forall_impl; [| exact allowA_aligned].
  intros [lo hi] (A1 & A2 & A3 & A4). cbn [fst snd] in *. unfold win_ok, clip. cbn [fst snd].
  repeat split; try lia.
  destruct (Z.le_gt_cases hi (2^64)); [rewrite Z.min_l by lia; exact A4| rewrite Z.min_r by lia; reflexivity].
Qed.

Lemma npages_clip_le : forall A, Forall (fun r => 0 <= fst r < 2^64 /\ fst r <= snd r /\ fst r mod 4096 = 0 /\ snd r mod 4096 = 0) A ->
  4096 * npages (List.map clip A) <= ACC.A_bytes A.
Proof.
  intros A H. induction H as [| [lo hi] A (A1 & A2 & A3 & A4) H IH]; [cbn; unfold npages; cbn; lia|].
  cbn [List.map ACC.A_bytes fst snd]. rewrite npages_cons.
  replace (win_npages (clip (lo, hi))) with (Z.to_nat ((Z.min hi (2^64) - lo) / 4096)) by reflexivity. cbn [fst snd] in *.
  set (q := (Z.min hi (2 ^ 64) - lo) / 4096) in *.
  assert (Hq : 0 <= q /\ 4096 * q <= hi - lo).
  { subst q. destruct (Z.le_gt_cases hi (2^64)); [rewrite Z.min_l by lia| rewrite Z.min_r by lia]; Z.div_mod_to_equations; lia. }
  rewrite Z2Nat.id by lia. lia.
Qed.

Lemma BINV_of_cs_ok : BINV model g0.
Proof.
  pose proof (APS.co_minv _ _ _ _ _ _ _ _ _ _ _ HC) as MI. pose proof (ACC.minv_budget _ _ MI) as HB.
  pose proof (APS.co_eager _ _ _ _ _ _ _ _ _ _ _ HC) as HE. pose proof (APS.co_abytes _ _ _ _ _ _ _ _ _ _ _ HC) as HA.
  pose proof (APS.co_limit _ _ _ _ _ _ _ _ _ _ _ HC) as HL.
  pose proof (npages_clip_le _ allowA_aligned) as HP. fold G0 in HP.
  change (ACC.eager_used model) with (eager_used model) in HB, HE.
  unfold BINV, g0. cbn [g_win g_res]. split; [exact G0_ok|]. unfold R0. split; [lia|]. rewrite HL. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma page_base_aligned : forall p : word, bv_unsigned p mod 4096 = 0 -> page_base p = p.
Proof.
  intros p Hp. apply bv_eq. rewrite page_base_unsigned. pose proof (bv_unsigned_in_range 64 p).
  Z.div_mod_to_equations. lia.
Qed.

Lemma matok_of_cs_ok : matok G0 (m_vm_materialized model).
Proof.
  pose proof (APS.co_minv _ _ _ _ _ _ _ _ _ _ _ HC) as MI. split; [exact (ACC.minv_nodup _ _ MI)|].
  intros p Hp. pose proof (ACC.minv_allowed _ _ MI p Hp) as HA. pose proof (ACC.minv_aligned _ _ MI p Hp) as HAL.
  rewrite page_size_eq in HAL.
  rewrite <- (page_base_aligned p HAL). apply gpages_in; [exact G0_ok|].
  unfold ACC.page_allowedb in HA. apply existsb_exists in HA as ([lo hi] & Hin & Hb). cbn [fst snd] in Hb.
  apply andb_true_iff in Hb as [B1 B2]. apply Z.leb_le in B1. apply Z.leb_le in B2. rewrite page_size_eq in B2.
  pose proof (bv_unsigned_in_range 64 p) as Rp. change (bv_modulus 64) with (2^64) in Rp.
  unfold in_winb, G0. apply existsb_exists. exists (clip (lo, hi)). split; [apply in_map; exact Hin|].
  unfold clip; cbn [fst snd]. apply andb_true_iff. split; [apply Z.leb_le; lia| apply Z.ltb_lt].
  apply Z.min_glb_lt; lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma keepb_true : forall x, keepb x = true ->
  (in_rangesb L x = true /\ in_winb G0 x = true)
  \/ (in_rangesb L x = false /\ (APS.vis AP.BOTH E cs model x = true \/ argH E x = true)).
Proof.
  intros x H. unfold keepb in H. destruct (in_rangesb L x); [left; auto|]. right. split; [reflexivity|].
  apply orb_true_iff in H. exact H.
Qed.

Lemma keepb_false : forall x, keepb x = false ->
  (APS.vis AP.BOTH E cs model x = false /\ argH E x = false) \/ (in_rangesb L x = true /\ in_winb G0 x = false).
Proof.
  intros x H. unfold keepb in H. destruct (in_rangesb L x); [right; auto|]. left. apply orb_false_iff in H. exact H.
Qed.

Lemma magree_of_cs_ok : magree bsegs (lzf model) (lexc model G0) jvis FULL.
Proof.
  intros x. unfold lmem, jvis. destruct (keepb x) eqn:Ek.
  - (* [comment removed for export] *)
    destruct (FULL x) as [b|] eqn:Ef.
    + left. reflexivity.
    + destruct (lzf model x) eqn:Ez.
      * right. split; [reflexivity|]. pose proof (lzf_lazy model x Ez) as Hl. split; [apply lazy_noseg_x; exact Hl|].
        right. destruct (keepb_true x Ek) as [[_ Hw] | [Hn _]]; [exact Hw| rewrite Hn in Hl; discriminate].
      * left. reflexivity.
  - destruct (lzf model x) eqn:Ez.
    + pose proof (lzf_lazy model x Ez) as Hl.
      assert (Hna : APS.in_ivs (bv_unsigned x) na = false).
      { rewrite in_ivs_rangesb. unfold lzf in Ez. apply andb_true_iff in Ez as [_ Ez]. destruct (in_rangesb _ x); [discriminate| reflexivity]. }
      destruct (keepb_false x Ek) as [[Hv Ha] | [_ Hw]].
      * (* [comment removed for export] *)
        destruct (in_winb G0 x) eqn:Ew.
        -- right. split; [reflexivity|]. split; [apply lazy_noseg_x; exact Hl|]. right. exact Ew.
        -- left. apply (APS.co_zero _ _ _ _ _ _ _ _ _ _ _ HC x).
           ++ unfold APS.hid. rewrite Hv, Ha. reflexivity.
           ++ rewrite in_ivs_rangesb. apply lazy_in_maps. exact Hl.
           ++ exact Hna.
           ++ apply lazy_page. exact Hl.
           ++ destruct (APS.in_ghost E cs (bv_unsigned x)) eqn:Eg; [| reflexivity]. rewrite (in_ghost_win x Eg) in Ew. discriminate.
      * (* [comment removed for export] *)
        assert (Hv : APS.vis AP.BOTH E cs model x = false).
        { destruct (APS.vis AP.BOTH E cs model x) eqn:Ev; [| reflexivity]. rewrite (vis_lazy_win x Ev Hl) in Hw. discriminate. }
        assert (Ha : argH E x = false).
        { destruct (argH E x) eqn:Ea; [| reflexivity]. rewrite (argH_not_lazy x Ea) in Hl. discriminate. }
        left. apply (APS.co_zero _ _ _ _ _ _ _ _ _ _ _ HC x).
        -- unfold APS.hid. rewrite Hv, Ha. reflexivity.
        -- rewrite in_ivs_rangesb. apply lazy_in_maps. exact Hl.
        -- exact Hna.
        -- apply lazy_page. exact Hl.
        -- destruct (APS.in_ghost E cs (bv_unsigned x)) eqn:Eg; [| reflexivity]. rewrite (in_ghost_win x Eg) in Hw. discriminate.
    + (* [comment removed for export] *)
      destruct (FULL x) eqn:Ef; [| left; reflexivity].
      right. split; [reflexivity|]. split; [| left; exact Ez].
      destruct (keepb_false x Ek) as [[Hv Ha] | [Hl Hw]].
      * apply (proj2 (noseg_iff_hull x)). intros Hr.
        assert (Hh : APS.in_hull AP.BOTH (bv_unsigned x) = true).
        { unfold APS.in_hull. rewrite img_lo_val, img_hi_val. apply andb_true_iff. split; [apply Z.leb_le| apply Z.ltb_lt]; lia. }
        unfold APS.vis in Hv. rewrite Hh in Hv. discriminate.
      * apply lazy_noseg_x. exact Hl.
Qed.

Lemma hidden_of_cs_ok : forall x, in_rangesb L x = true -> in_winb G0 x = false -> jvis x = None.
Proof.
  intros x Hl Hw. unfold jvis, keepb. rewrite Hl, Hw. reflexivity.
Qed.

Lemma vdom_of_cs_ok : vdom bsegs model jvis.
Proof.
  intros x Hx. unfold jvis in Hx. destruct (keepb x) eqn:Ek; [| congruence].
  destruct (keepb_true x Ek) as [[Hl _] | [_ [Hv|Ha]]].
  - right; right. apply lazy_in_maps. exact Hl.
  - unfold APS.vis in Hv. cbv zeta in Hv. apply orb_true_iff in Hv as [Hv|Hv]; [apply orb_true_iff in Hv as [Hv|Hv]|].
    + right; left. apply hull_seg. exact Hv.
    + left. apply Z.leb_le in Hv. rewrite HTOP in Hv. exact Hv.
    + right; right. apply andb_true_iff in Hv as [Hv _]. apply andb_true_iff in Hv as [Hv _]. rewrite in_ivs_rangesb in Hv. exact Hv.
  - left. apply HargH_hi. exact Ha.
Qed.

Theorem LINV_of_cs_ok : LINV bsegs g0 model (m_vm_materialized model) jvis FULL.
Proof.
  apply LINV_intro.
  - exact bsegs_no_wx.
  - exact LOK_of_cs_ok.
  - exact BINV_of_cs_ok.
  - exact matok_of_cs_ok.
  - exact magree_of_cs_ok.
  - exact hidden_of_cs_ok.
  - exact vdom_of_cs_ok.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma jvis_Mr : forall x,
  APS.Mr AP.BOTH argH E cs model FULL x <> None \/ ~ noseg bsegs x ->
  jvis x = APS.Mr AP.BOTH argH E cs model FULL x.
Proof.
  intros x Hx. unfold APS.Mr, ACC.mrestrict in *. unfold jvis, keepb.
  destruct (APS.hid AP.BOTH argH E cs model x) eqn:Eh.
  - destruct Hx as [Hx|Hs]; [congruence|]. exfalso.
    unfold APS.hid in Eh. apply orb_true_iff in Eh as [Ea|Ev].
    + pose proof (HargH_hi x Ea) as Hc. pose proof (@alloc_ceiling_lo ACEIL) as CL. apply Hs. apply (proj2 (noseg_iff_hull x)). lia.
    + pose proof (hull_vis x Hs) as Hh. unfold APS.vis in Ev. rewrite Hh in Ev. discriminate.
  - unfold APS.hid in Eh. apply orb_false_iff in Eh as [Ea Ev]. apply negb_false_iff in Ev. rewrite Ev, Ea. cbn [orb].
    destruct (in_rangesb L x) eqn:El; [| reflexivity]. rewrite (vis_lazy_win x Ev El). reflexivity.
Qed.

Lemma jvis_arg : forall x, argH E x = true -> jvis x = FULL x.
Proof.
  intros x Ha. unfold jvis, keepb. rewrite Ha, (argH_not_lazy x Ha), orb_true_r. reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma jvis_lazy_win : forall x, in_rangesb L x = true -> in_winb G0 x = true -> jvis x = FULL x.
Proof. intros x Hl Hw. unfold jvis, keepb. rewrite Hl, Hw. reflexivity. Qed.

(* [comment removed for export] *)
Lemma lzf_vis_allow : forall x, lzf model x = true ->
  APS.vis AP.BOTH E cs model x = APS.in_allow AP.BOTH E cs (bv_unsigned x).
Proof.
  intros x Hz. pose proof (lzf_lazy model x Hz) as Hl. unfold APS.vis. cbv zeta.
  assert (Hh : APS.in_hull AP.BOTH (bv_unsigned x) = false).
  { destruct (APS.in_hull AP.BOTH (bv_unsigned x)) eqn:Eh; [| reflexivity]. exfalso. apply (hull_seg x Eh). apply lazy_noseg_x. exact Hl. }
  assert (Hc : (APS.atop model <=? bv_unsigned x) = false).
  { apply Z.leb_gt. rewrite HTOP. apply lazy_below_ceil. exact Hl. }
  rewrite Hh, Hc. cbn [orb]. rewrite in_ivs_rangesb, (lazy_in_maps x Hl).
  assert (Hna : APS.in_ivs (bv_unsigned x) na = false).
  { rewrite in_ivs_rangesb. unfold lzf in Hz. apply andb_true_iff in Hz as [_ Hz]. destruct (in_rangesb _ x); [discriminate| reflexivity]. }
  rewrite Hna, (lazy_page x Hl). reflexivity.
Qed.

Lemma gwin_hidden : forall x, lzf model x = true -> in_winb G0 x = true ->
  APS.in_allow AP.BOTH E cs (bv_unsigned x) = false -> APS.in_ghost E cs (bv_unsigned x) = false ->
  jvis x = Some (Z_to_bv 8 0).
Proof.
  intros x Hz Hw Ha Hg. pose proof (lzf_lazy model x Hz) as Hl. rewrite (jvis_lazy_win x Hl Hw).
  apply (APS.co_zero _ _ _ _ _ _ _ _ _ _ _ HC x).
  - unfold APS.hid. rewrite (lzf_vis_allow x Hz), Ha. destruct (argH E x); reflexivity.
  - rewrite in_ivs_rangesb. apply lazy_in_maps. exact Hl.
  - rewrite in_ivs_rangesb. unfold lzf in Hz. apply andb_true_iff in Hz as [_ Hz]. destruct (in_rangesb _ x); [discriminate| reflexivity].
  - apply lazy_page. exact Hl.
  - exact Hg.
Qed.

(* [comment removed for export] *)
Lemma gwin_wr : forall x lo n, wr_at bsegs jvis lo n -> lo <= bv_unsigned x < lo + n ->
  in_rangesb L x = true -> jvis x <> None.
Proof.
  intros x lo n (H0 & Hn & Hw) Hx Hl.
  specialize (Hw (bv_unsigned x - lo)). replace (lo + (bv_unsigned x - lo)) with (bv_unsigned x) in Hw by lia.
  unfold wa in Hw. rewrite Z_to_bv_bv_unsigned in Hw.
  intros E0. apply Hw; [lia|]. apply wview_noseg; [apply lazy_noseg_x; exact Hl | exact E0].
Qed.

End Core.
