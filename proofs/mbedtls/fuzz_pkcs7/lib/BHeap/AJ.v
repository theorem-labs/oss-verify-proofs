(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Mmap Madvise.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Mem SysStep.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.ABoot Require Import BackingAlgebra.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import ALazy AEvtA.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.AHeap Require Import ACeil ASys AVmLib.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import DietDestruct.   (* [comment removed for export] *)
Import ListNotations.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import LiaKitAH. (* [comment removed for export] *)
Local Ltac Stdlib.micromega.Lia.lia ::= lia_ah.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section NWMono.
Variable segs : list Segment.

(* [comment removed for export] *)
Definition nwmono (m m' : word -> option byte) : Prop := forall x : word, wview segs m x = None -> wview segs m' x = None.

#[using="Type"] Lemma nwmono_refl : forall m, nwmono m m. Proof. intros m x H; exact H. Qed.
#[using="Type"] Lemma nwmono_trans : forall a b c, nwmono a b -> nwmono b c -> nwmono a c.
Proof. intros a b c H1 H2 x H. apply H2, H1, H. Qed.

#[using="Type"] Lemma wview_upd_other : forall (m : word -> option byte) (a x : word) b,
  x <> a -> wview segs (fun y => if bv_eqb y a then Some b else m y) x = wview segs m x.
Proof.
  intros m a x b NE. unfold wview. destruct (bv_eqb x a) eqn:E; [| reflexivity].
  exfalso. apply NE. unfold bv_eqb in E. apply Z.eqb_eq in E. apply bv_eq. exact E.
Qed.

#[using="Type"] Lemma wview_upd_some : forall (m : word -> option byte) (a y : word) b,
  wview segs m y <> None -> wview segs (fun z => if bv_eqb z a then Some b else m z) y <> None.
Proof. intros m a y b H. unfold wview in *. destruct (bv_eqb y a); [discriminate| exact H]. Qed.

#[using="Type"] Lemma store_ok_mono : forall n (m m' : word -> option byte) a,
  (forall y, wview segs m y <> None -> wview segs m' y <> None) -> store_ok segs m a n = true -> store_ok segs m' a n = true.
Proof.
  induction n as [|n IH]; intros m m' a MO H; [reflexivity|]. cbn [store_ok] in *.
  destruct (wview segs m a) eqn:E; [| discriminate].
  destruct (wview segs m' a) eqn:E'; [| exfalso; apply (MO a); [rewrite E; discriminate| exact E']].
  eapply IH; eauto.
Qed.

#[using="Type"] Lemma write_absent : forall bs (m : word -> option byte) a x,
  store_ok segs m a (length bs) = true -> wview segs m x = None -> wview segs (write_to_mem m a bs) x = None.
Proof.
  induction bs as [|b rest IH]; intros m a x OK HX; [exact HX|].
  cbn [write_to_mem]. cbn [length store_ok] in OK.
  destruct (wview segs m a) eqn:E; [| discriminate].
  assert (NE : x <> a) by (intros ->; congruence).
  apply IH.
  - eapply store_ok_mono; [| exact OK]. intros y Hy. apply wview_upd_some. exact Hy.
  - rewrite wview_upd_other by exact NE. exact HX.
Qed.

#[using="Type"] Lemma interp_absent : forall t m r,
  interp_eff_accesses segs t m = MachineOk r -> nwmono m (snd (@access_value _ r)).
Proof.
  induction t as [c|c|c|c|c|c|n a k IH|n a v k IH]; intros m r H; cbn [interp_eff_accesses] in H; try discriminate.
  - inversion H; subst. cbn. apply nwmono_refl.
  - destruct (ov_read_bytes segs m a (width_bytes n)) as [bs|]; [| discriminate].
    destruct (interp_eff_accesses segs (k (bv_extract 0 n (le_bytes_to_word bs))) m) as [rep| |] eqn:E; try discriminate.
    inversion H; subst. cbn. exact (IH _ m rep E).
  - destruct (store_ok segs m a (width_bytes n)) eqn:OK; [| discriminate].
    destruct (interp_eff_accesses segs k (write_to_mem m a (Z_to_le_bytes (width_bytes n) (bv_unsigned v)))) as [rep| |] eqn:E; try discriminate.
    inversion H; subst. cbn. eapply nwmono_trans; [| exact (IH _ rep E)].
    intros x HX. apply write_absent; [| exact HX]. rewrite BvBase.length_Z_to_le_bytes. exact OK.
Qed.

#[using="Type"] Lemma decode_exec_absent : forall st w st' acc,
  decode_exec_accesses segs st w = MachineOk (@mkAccessReport machine_state st' acc) -> nwmono (ms_mem st) (ms_mem st').
Proof.
  intros st w st' acc H. unfold decode_exec_accesses in H.
  destruct (is_ecall w).
  - inversion H; subst. cbn. apply nwmono_refl.
  - destruct (decode_any w) as [[i isz]|]; [| destruct (is_defined_illegal w); discriminate].
    match type of H with context [interp_eff_accesses segs ?t ?m] => destruct (interp_eff_accesses segs t m) as [rep| |] eqn:E; try discriminate end.
    pose proof (interp_absent _ _ _ E) as NW. destruct (@access_value _ rep) as [c m'] eqn:EV. cbn in NW.
    inversion H; subst. cbn. exact NW.
Qed.

#[using="Type"] Lemma step_absent : forall st st' acc,
  step_accesses segs st = MachineOk (@mkAccessReport machine_state st' acc) -> nwmono (ms_mem st) (ms_mem st').
Proof.
  intros st st' acc H. unfold step_accesses in H.
  destruct (fetch_word segs (ms_pc st)) as [w|]; [eapply decode_exec_absent; exact H|].
  destruct (fetch_word_ov segs (ms_mem st) (ms_pc st)) as [w|]; [eapply decode_exec_absent; exact H|].
  destruct (fetch_tail_any segs (ms_mem st) (ms_pc st)) as [w|]; [eapply decode_exec_absent; exact H|].
  exfalso. unfold fetch_failure in H.
  repeat match type of H with context [if ?b then _ else _] => destruct b end; discriminate.
Qed.
End NWMono.

Section ARUN_1. Context {hAR : arun}.

Definition JF : Z := 0x65f000.   (* [comment removed for export] *)

Definition msep (M : list (word * word)) : Prop :=
  forall e1 e2, In e1 M -> In e2 M -> e1 = e2 \/ eB e1 + eS e1 <= eB e2 \/ eB e2 + eS e2 <= eB e1.
Definition ncov (N : list (word * word)) (x : Z) : Prop := exists e, In e N /\ eB e <= x < eB e + eS e.

(* [comment removed for export] *)
Definition jband (x : Z) : Prop := 0x7fff7000 <= x < 0x10007fff8000.
Definition JW : Z := 2^17.
Definition jwin (M N : list (word * word)) (x : Z) : Prop :=
  exists (a : Z) (e : word * word), In e M /\ eB e <= a /\ a + JW <= eB e + eS e /\ a <= x < a + JW /\ (forall y, a <= y < a + JW -> ncov N y).

Definition J (m : word -> option byte) (mo : Model) : Prop :=
  let M := vm_maps (m_vmmaps mo) in let N := vm_noaccess (m_vmmaps mo) in
  ivs_wf M /\ ivs_wf N /\ msep M
  /\ (forall e, In e N -> 0 < eS e /\ covers M (eB e) (eB e + eS e))
  /\ (forall x : word, JF <= bv_unsigned x -> ~ jband (bv_unsigned x) -> jwin M N (bv_unsigned x) -> m x = None).

(* [comment removed for export] *)
#[using="Type"] Lemma J_vmmaps : forall m mo mo', m_vmmaps mo' = m_vmmaps mo -> J m mo -> J m mo'.
Proof. intros m mo mo' E H. unfold J in *. rewrite E. exact H. Qed.

#[using="Type"] Lemma J_mat : forall m mo mo', mo_mat mo mo' -> J m mo -> J m mo'.
Proof. (intros m mo mo' dd_H; ddestruct dd_H as (_ & E & _); intros H). eapply J_vmmaps; eauto. Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma jwin_of_unit : forall M N U n x, JW <= n -> covers M U (U + n) -> (forall y, U <= y < U + n -> ncov N y) ->
  U <= x < U + n -> jwin M N x.
Proof.
  (intros M N U n x NW dd_H; ddestruct dd_H as (e & He & E1 & E2); intros NC Hx). dexists (Z.min x (U + n - JW)), e. unfold JW in *.
  split; [exact He|]. split; [lia|]. split; [lia|]. split; [lia|]. intros y Hy. apply NC. lia.
Qed.
#[using="Type"] Lemma J_absent : forall m mo U n, J m mo -> JF <= U -> (U + n <= 0x7fff7000 \/ 0x10007fff8000 <= U) -> JW <= n ->
  covers (vm_maps (m_vmmaps mo)) U (U + n) -> (forall y, U <= y < U + n -> ncov (vm_noaccess (m_vmmaps mo)) y) ->
  forall x : word, U <= bv_unsigned x < U + n -> m x = None.
Proof.
  (intros m mo U n dd_H; ddestruct dd_H as (_ & _ & _ & _ & J2); intros LF BND NW CV NC x Hx). apply J2; [lia| unfold jband; lia| exact (jwin_of_unit _ _ U n _ NW CV NC Hx)].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section Steps.
Variable segs : list Segment.
Hypothesis WVH : forall (m : word -> option byte) (x : word), JF <= bv_unsigned x -> wview segs m x = m x.

#[using="WVH"] Lemma J_nwmono : forall m m' mo, nwmono segs m m' -> J m mo -> J m' mo.
Proof.
  (intros m m' mo NW dd_H; ddestruct dd_H as (W1 & W2 & SEP & J1 & J2)). repeat (split; [assumption|]).
  intros x Hx HB HN. rewrite <- (WVH m' x Hx). apply NW. rewrite (WVH m x Hx). exact (J2 x Hx HB HN).
Qed.

Variable L : asan_layout.
#[using="Type"] Lemma mstepsA_nwmono : forall CS ms ms', mstepsA segs L CS ms ms' -> nwmono segs (ms_mem ms) (ms_mem ms').
Proof.
  intros CS ms ms' H. induction H as [ms | ms ms1 ms2 [_ (acc & ST & _)] _ IH]; [apply nwmono_refl|].
  eapply nwmono_trans; [exact (step_absent segs _ _ _ ST)| exact IH].
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma evtA_nwmono : forall CS (P : machine_state -> Prop) ms,
  evtA segs L CS P ms -> evtA segs L CS (fun ms' => P ms' /\ nwmono segs (ms_mem ms) (ms_mem ms')) ms.
Proof. (intros CS P ms dd_H; ddestruct dd_H as (ms' & H & HP)). exists ms'. split; [exact H|]. split; [exact HP| exact (mstepsA_nwmono CS ms ms' H)]. Qed.
End Steps.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
#[using="Type"] Lemma in_maps_subtract_inv : forall l lo hi q, In q (maps_subtract l lo hi) ->
  exists r, In r l /\ In q (iv_subtract (fst r) (snd r) lo hi).
Proof.
  induction l as [|[a sz] l IH]; intros lo hi q H; [destruct H|]. cbn [maps_subtract] in H. apply in_app_iff in H as [H|H].
  - exists (a, sz). split; [left; reflexivity| exact H].
  - ddestruct (IH lo hi q H) as (r & Hr & Hq). exists r. split; [right; exact Hr| exact Hq].
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma iv_subtract_sep : forall (a sz : word) lo hi q1 q2, bv_unsigned a + bv_unsigned sz <= 2^64 -> lo <= hi ->
  In q1 (iv_subtract a sz lo hi) -> In q2 (iv_subtract a sz lo hi) ->
  q1 = q2 \/ eB q1 + eS q1 <= eB q2 \/ eB q2 + eS q2 <= eB q1.
Proof.
  intros a sz lo hi q1 q2 WF LH H1 H2. pose proof (u64_range a) as Ra. pose proof (u64_range sz) as Rs.
  unfold iv_subtract in H1, H2.
  destruct (bv_unsigned a <? lo) eqn:EL; destruct (hi <? bv_unsigned a + bv_unsigned sz) eqn:ER;
    cbn [app In] in H1, H2; try apply Z.ltb_lt in EL; try apply Z.ltb_lt in ER;
    repeat match goal with H : _ \/ _ |- _ => destruct H | H : False |- _ => destruct H end; subst; try (left; reflexivity);
    right; cbn [fst snd]; rewrite ?u64_lit by lia; lia.
Qed.

#[using="Type"] Lemma msep_subtract : forall M lo hi, ivs_wf M -> lo <= hi -> msep M -> msep (maps_subtract M lo hi).
Proof.
  intros M lo hi WF LH SEP q1 q2 H1 H2.
  ddestruct (in_maps_subtract_inv M lo hi q1 H1) as (r1 & Hr1 & P1). ddestruct (in_maps_subtract_inv M lo hi q2 H2) as (r2 & Hr2 & P2).
  destruct (SEP r1 r2 Hr1 Hr2) as [E|AP].
  - subst r2. destruct r1 as [a sz]. cbn [fst snd] in *. exact (iv_subtract_sep a sz lo hi q1 q2 (WF (a, sz) Hr1) LH P1 P2).
  - right. destruct r1 as [a1 s1], r2 as [a2 s2]. cbn [fst snd] in *.
    dpose (iv_subtract_pieces a1 s1 lo hi q1 (WF (a1, s1) Hr1) P1) as (X1 & X2 & _).
    dpose (iv_subtract_pieces a2 s2 lo hi q2 (WF (a2, s2) Hr2) P2) as (Y1 & Y2 & _). lia.
Qed.

#[using="Type"] Lemma msep_cons : forall (a n : word) M, msep M -> clear M (bv_unsigned a) (bv_unsigned a + bv_unsigned n) -> msep ((a, n) :: M).
Proof.
  intros a n M SEP CL e1 e2 [<-|H1] [<-|H2]; [left; reflexivity| | |apply SEP; assumption].
  - right. specialize (CL e2 H2). cbn [fst snd]. lia.
  - right. specialize (CL e1 H1). cbn [fst snd]. lia.
Qed.

#[using="Type"] Lemma msep_remove : forall M a, msep M -> msep (map_remove M a).
Proof. intros M a SEP e1 e2 H1 H2. apply in_map_remove in H1. apply in_map_remove in H2. apply SEP; tauto. Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma j1_subtract_N : forall M N lo hi, ivs_wf N -> lo <= hi ->
  (forall e, In e N -> 0 < eS e /\ covers M (eB e) (eB e + eS e)) ->
  (forall e, In e (maps_subtract N lo hi) -> 0 < eS e /\ covers M (eB e) (eB e + eS e)).
Proof.
  intros M N lo hi WF LH J1 q Hq. split.
  - eapply maps_subtract_pos; [exact WF| intros e He; exact (proj1 (J1 e He))| exact Hq].
  - ddestruct (maps_subtract_pieces N lo hi q WF Hq) as (r & Hr & R1 & R2 & _).
    eapply covers_weaken; [exact (proj2 (J1 r Hr))| lia| lia].
Qed.

#[using="Type"] Lemma ncov_subtract : forall N lo hi x, ivs_wf N -> ncov (maps_subtract N lo hi) x -> ncov N x /\ (x < lo \/ hi <= x).
Proof.
  (intros N lo hi x WF dd_H; ddestruct dd_H as (q & Hq & Q)). ddestruct (maps_subtract_pieces N lo hi q WF Hq) as (r & Hr & R1 & R2 & R3).
  split; [exists r; split; [exact Hr| lia]| lia].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section Outcomes.
Variables (m : word -> option byte) (mo : Model).
Hypothesis HJ : J m mo.
Variables (addr nZ : Z).
Hypothesis A0 : 0 <= addr. Hypothesis N0 : 0 < nZ. Hypothesis AN : addr + nZ < 2^64.
Let a := Z_to_bv 64 addr. Let n := Z_to_bv 64 nZ.
Let UA : bv_unsigned a = addr. Proof. apply u64_lit. lia. Qed.
Let UN : bv_unsigned n = nZ. Proof. apply u64_lit. lia. Qed.

(* [comment removed for export] *)
#[using="HJ A0 N0 AN a UA UN"] Lemma J_fixrw_commit : forall flags, J (apply_zeros m [(wa addr, n)]) (fixrw_commit flags addr nZ mo).
Proof.
  intros flags. ddestruct HJ as (W1 & W2 & SEP & J1 & J2).
  unfold J, fixrw_commit, with_mmap_replacement. cbv zeta. rewrite vmmaps_with_mmap_backing. model_proj.
  unfold mmap_fixed_rw_next. cbn [vm_maps vm_noaccess]. fold a n. rewrite UA, UN.
  split; [exact W1|]. split; [apply maps_subtract_wf; [exact W2| lia]|]. split; [exact SEP|].
  split; [apply j1_subtract_N; [exact W2| lia| exact J1]|].
  (intros x Hx HB dd_H; ddestruct dd_H as (a0 & e & He & E1 & E2 & XA & NC)).
  destruct (ncov_subtract _ _ _ _ W2 (NC (bv_unsigned x) XA)) as [_ OUT].
  unfold n. rewrite (zeros_outside m addr nZ ltac:(lia) ltac:(lia) ltac:(lia) x OUT). apply (J2 x Hx HB).
  dexists a0, e. repeat (split; [assumption|]). intros y Hy. exact (proj1 (ncov_subtract _ _ _ _ W2 (NC y Hy))).
Qed.

(* [comment removed for export] *)
#[using="HJ A0 N0 AN UA UN"] Lemma J_fixrw_fresh : forall flags,
  region_free (vm_reserved (m_vmmaps mo) ++ vm_maps (m_vmmaps mo)) a n = true ->
  J (apply_zeros m [(wa addr, n)]) (fixrw_fresh flags addr nZ mo).
Proof.
  intros flags RF. ddestruct HJ as (W1 & W2 & SEP & J1 & J2).
  pose proof (region_free_clear _ a n ltac:(rewrite UN; lia) RF) as CL. apply clear_app_inv in CL. destruct CL as [_ CLM].
  unfold J, fixrw_fresh. cbv zeta. rewrite vmmaps_with_mmap_backing. model_proj. cbn [vm_maps vm_noaccess]. fold a n.
  split; [apply ivs_wf_cons; [apply iv_wf_intro; rewrite UA, UN; lia| exact W1]|]. split; [exact W2|].
  split; [apply msep_cons; assumption|].
  split; [intros e He; destruct (J1 e He) as [P C]; split; [exact P| apply covers_cons; exact C]|].
  (intros x Hx HB dd_H; ddestruct dd_H as (a0 & e0 & [<-|He0] & E1 & E2 & XA & NC)).
  - (* [comment removed for export] *)
    exfalso. ddestruct (NC (bv_unsigned x) XA) as (e & He & E). ddestruct (proj2 (J1 e He)) as (e' & He' & C1 & C2).
    specialize (CLM e' He'). cbn [fst snd] in E1, E2. rewrite UA, UN in CLM, E2. rewrite UA in E1. unfold JW in *. lia.
  - assert (XO : bv_unsigned x < addr \/ addr + nZ <= bv_unsigned x).
    { specialize (CLM e0 He0). rewrite UA, UN in CLM. unfold JW in *. lia. }
    unfold n. rewrite (zeros_outside m addr nZ ltac:(lia) ltac:(lia) ltac:(lia) x XO). apply (J2 x Hx HB).
    dexists a0, e0. repeat (split; [assumption|]). exact NC.
Qed.

(* [comment removed for export] *)
#[using="HJ A0 N0 AN a UA UN"] Lemma J_fixrw_destroyed : J (apply_unmaps m [(wa addr, n)]) (fixrw_destroyed addr nZ mo).
Proof.
  ddestruct HJ as (W1 & W2 & SEP & J1 & J2).
  unfold J, fixrw_destroyed, with_mmap_destroyed. cbv zeta. model_proj.
  unfold mmap_fixed_destroyed_next. cbn [vm_maps vm_noaccess]. fold a n. rewrite UA, UN.
  split; [apply maps_subtract_wf; [exact W1| lia]|]. split; [apply maps_subtract_wf; [exact W2| lia]|].
  split; [apply msep_subtract; [exact W1| lia| exact SEP]|].
  split.
  - intros q Hq. split; [eapply maps_subtract_pos; [exact W2| intros e He; exact (proj1 (J1 e He))| exact Hq]|].
    destruct (maps_subtract_pieces _ _ _ q W2 Hq) as (r & Hr & R1 & R2 & R3).
    assert (QP : 0 < eS q) by (eapply maps_subtract_pos; [exact W2| intros e He; exact (proj1 (J1 e He))| exact Hq]).
    apply covers_subtract; [exact W1| lia| lia| | lia].
    eapply covers_weaken; [exact (proj2 (J1 r Hr))| lia| lia].
  - (intros x Hx HB dd_H; ddestruct dd_H as (a0 & q & Hq & E1 & E2 & XA & NC)).
    destruct (ncov_subtract _ _ _ _ W2 (NC (bv_unsigned x) XA)) as [_ OUT].
    unfold n. rewrite (unmaps_outside m addr nZ ltac:(lia) ltac:(lia) ltac:(lia) x OUT). apply (J2 x Hx HB).
    destruct (maps_subtract_pieces _ _ _ q W1 Hq) as (r & Hr & R1 & R2 & R3).
    dexists a0, r. split; [exact Hr|]. split; [lia|]. split; [lia|]. split; [exact XA|]. intros y Hy. exact (proj1 (ncov_subtract _ _ _ _ W2 (NC y Hy))).
Qed.

(* [comment removed for export] *)
#[using="HJ A0 N0 AN UA UN"] Lemma J_norep_grant :
  region_free (vm_reserved (m_vmmaps mo) ++ vm_maps (m_vmmaps mo)) a n = true ->
  J (apply_unmaps m [(wa addr, n)]) (norep_grant addr nZ mo).
Proof.
  intros RF. ddestruct HJ as (W1 & W2 & SEP & J1 & J2).
  pose proof (region_free_clear _ a n ltac:(rewrite UN; lia) RF) as CL. apply clear_app_inv in CL. destruct CL as [_ CLM].
  unfold J, norep_grant. cbv zeta. rewrite vmmaps_with_mmap_backing. model_proj. cbn [vm_maps vm_noaccess]. fold a n.
  split; [apply ivs_wf_cons; [apply iv_wf_intro; rewrite UA, UN; lia| exact W1]|].
  split; [apply ivs_wf_cons; [apply iv_wf_intro; rewrite UA, UN; lia| exact W2]|].
  split; [apply msep_cons; assumption|].
  split.
  - intros e [<-|He]; cbn [fst snd].
    + split; [rewrite UN; lia| apply covers_cons_new; lia].
    + destruct (J1 e He) as [P C]. split; [exact P| apply covers_cons; exact C].
  - (intros x Hx HB dd_H; ddestruct dd_H as (a0 & e0 & [<-|He0] & E1 & E2 & XA & NC)); cbn [fst snd] in E1, E2.
    + rewrite UA in E1. rewrite UA, UN in E2. unfold n. rewrite apply_unmaps_spec by lia. unfold in_range.
      replace (addr <=? bv_unsigned x) with true by (symmetry; apply Z.leb_le; lia).
      replace (bv_unsigned x <? addr + nZ) with true by (symmetry; apply Z.ltb_lt; lia). reflexivity.
    + unfold n. rewrite apply_unmaps_spec by lia. destruct (in_range addr nZ x); [reflexivity|]. apply (J2 x Hx HB).
      specialize (CLM e0 He0). rewrite UA, UN in CLM.
      dexists a0, e0. repeat (split; [assumption|]). intros y Hy. ddestruct (NC y Hy) as (e & [<-|He] & E); cbn [fst snd] in E.
      * exfalso. rewrite UA, UN in E. lia.
      * exists e. split; [exact He| exact E].
Qed.
End Outcomes.

(* [comment removed for export] *)
#[using="Type"] Lemma J_anon_grant : forall m mo flags (a : word) nZ, J m mo -> 0 < nZ -> bv_unsigned a + nZ < 2^64 ->
  region_free (vm_reserved (m_vmmaps mo) ++ vm_maps (m_vmmaps mo)) a (Z_to_bv 64 nZ) = true ->
  J (apply_zeros m [(a, Z_to_bv 64 nZ)]) (anon_grant flags a nZ mo).
Proof.
  intros m mo flags a nZ HJ N0 AN RF. pose proof (u64_range a) as Ra.
  pose proof (J_fixrw_fresh m mo HJ (bv_unsigned a) nZ ltac:(lia) N0 AN flags) as X.
  unfold wa in X. rewrite Z_to_bv_bv_unsigned in X. specialize (X RF).
  unfold fixrw_fresh in X. rewrite Z_to_bv_bv_unsigned in X. exact X.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma J_munmap : forall m mo addr nZ, J m mo -> 0 <= addr -> 0 < nZ -> addr + nZ < 2^64 ->
  map_has (vm_maps (m_vmmaps mo)) (Z_to_bv 64 addr) (Z_to_bv 64 nZ) = true ->
  J (apply_unmaps m [(wa addr, Z_to_bv 64 nZ)]) (munmap_model addr nZ mo).
Proof.
  (intros m mo addr nZ dd_H; ddestruct dd_H as (W1 & W2 & SEP & J1 & J2); intros A0 N0 AN MH).
  assert (UA : bv_unsigned (Z_to_bv 64 addr) = addr) by (apply u64_lit; lia).
  assert (UN : bv_unsigned (Z_to_bv 64 nZ) = nZ) by (apply u64_lit; lia).
  assert (INM : In (Z_to_bv 64 addr, Z_to_bv 64 nZ) (vm_maps (m_vmmaps mo))).
  { unfold map_has in MH. apply existsb_exists in MH. ddestruct MH as ([b sz] & Hin & E). cbn [fst snd] in E.
    apply andb_prop in E. destruct E as [E1 E2]. apply bv_eqb_eq in E1. apply bv_eqb_eq in E2. subst. exact Hin. }
  unfold J, munmap_model, with_mmap_destroyed. cbv zeta. model_proj. cbn [vm_maps vm_noaccess].
  split; [apply ivs_wf_remove; exact W1|]. split; [apply maps_subtract_wf; [exact W2| lia]|].
  split; [apply msep_remove; exact SEP|].
  split.
  - intros q Hq.
    assert (QP : 0 < eS q) by (eapply maps_subtract_pos; [exact W2| intros e He; exact (proj1 (J1 e He))| exact Hq]).
    split; [exact QP|].
    destruct (maps_subtract_pieces _ _ _ q W2 Hq) as (r & Hr & R1 & R2 & R3).
    ddestruct (proj2 (J1 r Hr)) as (e & He & C1 & C2).
    exists e. split; [| lia]. apply in_map_remove. split; [exact He|]. intros FE.
    destruct (SEP e _ He INM) as [E|AP].
    + subst e. cbn [fst snd] in C1, C2. rewrite ?UA, ?UN in C1, C2. lia.
    + assert (EB : eB e = addr) by (rewrite FE; exact UA). cbn [fst snd] in AP. rewrite ?UA, ?UN in AP. lia.
  - (intros x Hx HB dd_H; ddestruct dd_H as (a0 & e0 & He0 & E1 & E2 & XA & NC)). destruct (ncov_subtract _ _ _ _ W2 (NC (bv_unsigned x) XA)) as [_ OUT].
    rewrite (unmaps_outside m addr nZ ltac:(lia) ltac:(lia) ltac:(lia) x OUT). apply (J2 x Hx HB).
    apply in_map_remove in He0. dexists a0, e0. split; [exact (proj1 He0)|]. split; [lia|]. split; [lia|]. split; [exact XA|].
    intros y Hy. exact (proj1 (ncov_subtract _ _ _ _ W2 (NC y Hy))).
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma J_madvise : forall m mo addr nZ, J m mo -> 0 <= addr -> 0 < nZ -> addr + nZ < 2^64 ->
  madvise_dontneed_ok (m_vmmaps mo) (Z_to_bv 64 addr) (Z_to_bv 64 nZ) = true ->
  J (apply_zeros m [(wa addr, Z_to_bv 64 nZ)]) (madvise_model addr nZ mo).
Proof.
  intros m mo addr nZ HJ A0 N0 AN OKG.
  assert (UA : bv_unsigned (Z_to_bv 64 addr) = addr) by (apply u64_lit; lia).
  assert (UN : bv_unsigned (Z_to_bv 64 nZ) = nZ) by (apply u64_lit; lia).
  unfold madvise_dontneed_ok in OKG. apply andb_prop in OKG. destruct OKG as [_ RFN].
  pose proof (region_free_clear _ _ _ ltac:(rewrite UN; lia) RFN) as CLN. rewrite UA, UN in CLN.
  apply (J_vmmaps _ mo); [reflexivity|].
  ddestruct HJ as (W1 & W2 & SEP & J1 & J2). repeat (split; [assumption|]).
  intros x Hx HB WIN. dpose WIN as (a0 & e0 & He0 & E1 & E2 & XA & NC). ddestruct (NC (bv_unsigned x) XA) as (e & He & E). specialize (CLN e He).
  rewrite (zeros_outside m addr nZ ltac:(lia) ltac:(lia) ltac:(lia) x ltac:(lia)). exact (J2 x Hx HB WIN).
Qed.

End ARUN_1.
