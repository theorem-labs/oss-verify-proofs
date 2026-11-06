(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.K5.Lib Require Import Tac.
From OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.K5.B08 Require Import ImageA.
From OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.K5.Lib Require Import RzCPS NodesA.
From OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.K5.B08 Require Import Layout.
From OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.K5.AG Require Import Shadow.
From OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.K5.B08 Require Import RT_iface RT_traces RT_gaps_iface D_kit Lept_kit Lept_iface Lept_objkit Cf_iface Cf_kit.
Import ListNotations.
Open Scope Z_scope.

Section CfFKit.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.

(* [comment removed for export] *)
Lemma inner_chunk_apart : forall Σ' (m : mem) p n live0 frs usp a,
  ART RT Σ' m -> In (p, n) (rt_live RT Σ') ->
  (forall e, In e live0 -> In e (rt_live RT Σ') /\ fst e <> p) -> (forall e, In e frs -> In e (rt_frames RT Σ')) ->
  rt_sp0 RT Σ' - STACK_WIN <= usp ->
  aclient live0 frs usp a -> a < p \/ p + n <= a.
Proof using AF.
  intros Σ' m p n live0 frs usp a HA INL SUBL SUBF SPL Ha.
  pose proof (af_live_range RT AF Σ' m p n HA INL) as (P0 & PHI & PSEG).
  unfold STACK_WIN, USTACK_TOP, SEGTOP_A in *.
  destruct Ha as [H|[H|[H|[H|H]]]].
  - right. lia.
  - pose proof (client_static_below a H) as HB. unfold SEGTOP_A in HB.
    destruct H as ((l & h & Hin & Hx) & _). unfold CLIENT_STATIC in Hin. cbn [In] in Hin.
    assert (X : 0x10000 <= a) by (repeat (destruct Hin as [E|Hin]; [injection E as <- <-; lia|]); destruct Hin).
    lia.
  - destruct H as (p' & n' & Hin & Hp). destruct (SUBL _ Hin) as [Hin' NE]. cbn [fst] in NE.
    pose proof (live_apart RT AF Σ' m p n p' n' HA INL Hin' ltac:(congruence)) as D. lia.
  - destruct H as (f & k & Hin & Hf). apply SUBF in Hin.
    pose proof (af_frames_range RT AF Σ' m f k HA Hin) as (_ & _ & _ & FLV). specialize (FLV p n INL). lia.
  - destruct H as (f & k & Hin & Hf). apply SUBF in Hin.
    pose proof (af_fshadow_apart RT AF Σ' m f k HA Hin) as (SA1 & _). specialize (SA1 p n INL). lia.
Qed.

(* [comment removed for export] *)
Lemma live_outside_walk1 : forall Σ (m : mem) fr usp slo q n a,
  ART RT Σ m -> In (fr, 1%nat) (rt_frames RT Σ) -> rt_sp0 RT Σ - STACK_WIN <= slo ->
  In (q, n) (rt_live RT Σ) -> q <= a < q + n ->
  outside [(slo, usp); (fr, fr + 120); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 16)] a.
Proof using AF.
  intros Σ m fr usp slo q n a HA FIN SLO QIN Ha.
  pose proof (af_live_range RT AF Σ m q n HA QIN) as (_ & R1 & _).
  pose proof (af_frames_range RT AF Σ m fr 1%nat HA FIN) as (_ & _ & _ & FLV). specialize (FLV q n QIN).
  pose proof (af_fshadow_apart RT AF Σ m fr 1%nat HA FIN) as (SA1 & _). specialize (SA1 q n QIN).
  change (fs_size 1) with 128 in *. unfold shad, SHB in SA1.
  cbn [outside]. repeat split; try exact I; first [lia | Z.div_mod_to_equations; lia].
Qed.
Lemma keeps_live_walk1 : forall Σ (m m' : mem) fr usp slo,
  ART RT Σ m -> In (fr, 1%nat) (rt_frames RT Σ) -> rt_sp0 RT Σ - STACK_WIN <= slo ->
  munch [(slo, usp); (fr, fr + 120); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 16)] m m' -> keeps_live (rt_live RT Σ) m m'.
Proof using AF.
  intros Σ m m' fr usp slo HA FIN SLO MU b k Hin a Ha. apply MU. exact (live_outside_walk1 Σ m fr usp slo b k _ HA FIN SLO Hin Ha).
Qed.

(* [comment removed for export] *)
Lemma chunk_outside_local : forall Σ (m : mem) fr k q n lo hi p a,
  ART RT Σ m -> In (fr, k) (rt_frames RT Σ) -> fr <= lo -> hi <= fr + fs_size k ->
  In (q, n) (rt_live RT Σ) -> In (p, 64) (rt_live RT Σ) -> q <> p -> q <= a < q + n ->
  outside [(lo, hi); (p + 20, p + 24)] a.
Proof using AF.
  intros Σ m fr k q n lo hi p a HA FIN L1 L2 QIN PIN NE Ha.
  pose proof (af_frames_range RT AF Σ m fr k HA FIN) as (_ & _ & _ & FLV). specialize (FLV q n QIN).
  pose proof (live_apart RT AF Σ m q n p 64 HA QIN PIN NE) as D.
  cbn [outside]. repeat split; try exact I; lia.
Qed.
End CfFKit.

Lemma rm_opt_sub : forall p (l : list (Z * Z)) e, In e (rm_opt p l) -> In e l.
Proof. intros p l e He. unfold rm_opt in He. destruct (p =? 0); [exact He| exact (live_remove_sub l p e He)]. Qed.
Lemma live_destroy_in : forall pix v cv (l : list (Z * Z)) e, In e (live_destroy pix v cv l) -> In e l /\ fst e <> pix.
Proof.
  intros pix v cv l e He. unfold live_destroy in He. apply live_remove_in in He as [He NE]. split; [| exact NE].
  apply rm_opt_sub in He. apply rm_opt_sub in He. apply rm_opt_sub in He. exact He.
Qed.

(* [comment removed for export] *)
Definition keeps_cmap (v : pixv) (m m' : mem) : Prop := p_cmap v = 0 \/ keeps_live [(p_cmap v, 24)] m m'.
Lemma keeps_cmap_refl : forall v m, keeps_cmap v m m.
Proof. intros v m. right. apply keeps_live_refl. Qed.
Lemma keeps_cmap_trans : forall v m1 m2 m3, keeps_cmap v m1 m2 -> keeps_cmap v m2 m3 -> keeps_cmap v m1 m3.
Proof. intros v m1 m2 m3 [Z1|K1] [Z2|K2]; [left; exact Z1| left; exact Z1| left; exact Z2| right; exact (keeps_live_trans _ _ _ _ K1 K2)]. Qed.
Lemma keeps_cmap_of_live : forall live0 live v cv (m0 m m' : mem) pix, pix_obj live0 m0 pix v cv -> (forall e, In e live0 -> In e live) ->
  keeps_live live m m' -> keeps_cmap v m m'.
Proof.
  intros live0 live v cv m0 m m' pix (_ & _ & _ & _ & [CZ|((_ & (CIN & _) & _) & _)]) SUB K; [left; exact CZ| right].
  intros b k [E|[]] a Ha. injection E as <- <-. exact (K _ _ (SUB _ CIN) a Ha).
Qed.
(* [comment removed for export] *)
Lemma keeps_cmap_of_agree : forall live0 lv frs sp W v cv (m0 m m' : mem) pix, pix_obj live0 m0 pix v cv ->
  agree_on (fun a => aclient lv frs sp a /\ outside W a) m m' ->
  (forall e, In e live0 -> In e lv) -> (p_cmap v <> 0 -> In (p_cmap v, 24) live0 -> forall x, p_cmap v <= x < p_cmap v + 24 -> outside W x) ->
  keeps_cmap v m m'.
Proof.
  intros live0 lv frs sp W v cv m0 m m' pix (_ & _ & _ & _ & [CZ|((_ & (CIN & P0 & _) & _) & _)]) AG SUB OUT; [left; exact CZ| right].
  apply (keeps_live_of_agree lv frs sp W m m' _ AG).
  - intros e [E|[]]. subst e. exact (SUB _ CIN).
  - intros b k x [E|[]] Hx. injection E as <- <-. apply OUT; [lia| exact CIN| exact Hx].
Qed.

(* [comment removed for export] *)
Lemma pix_obj_rc_rebuild : forall live live' (m m' : mem) pix v cv rc,
  pix_obj live m pix v cv -> (forall e, In e live -> In e live') -> rw_cells asegs m' pix (pix_cells_rc v rc) ->
  keeps_cmap v m m' -> pix_obj_rc live' m' pix v cv rc.
Proof.
  intros live live' m m' pix v cv rc (Hc & CH & HOK & HD & HCM) SUB Hc' KC.
  assert (CHM : forall p n, chunk live p n -> chunk live' p n) by (intros p n (I1 & R); exact (conj (SUB _ I1) R)).
  split; [exact Hc'|]. split; [exact (CHM _ _ CH)|]. split; [exact HOK|]. split.
  - destruct HD as [HD|(HD & R)]; [left; exact HD| right; exact (conj (CHM _ _ HD) R)].
  - destruct HCM as [HCM|(((pad & CC) & CH1 & CH2 & R1) & R2)]; [left; exact HCM| right].
    split; [| exact R2]. split; [exists pad| exact (conj (CHM _ _ CH1) (conj (CHM _ _ CH2) R1))].
    destruct KC as [CZ|KC]; [destruct CH1 as (_ & P0 & _); lia|].
    apply (keeps_live_cells [(p_cmap v, 24)] m m' (p_cmap v) 24 (p_cmap v) _ KC ltac:(left; reflexivity)); [lia| cbn; lia| exact CC].
Qed.

(* [comment removed for export] *)
Lemma cf_live_app : forall cf c (L : list (Z * Z)), cf_live cf c L = cf_live cf c [] ++ L.
Proof. reflexivity. Qed.
Lemma nodup_app_notin : forall (l1 l2 : list Z) x, List.NoDup (l1 ++ l2) -> In x l2 -> ~ In x l1.
Proof.
  induction l1 as [|y l1 IH]; intros l2 x ND Hx; [intros []|]. cbn [app] in ND. apply List.NoDup_cons_iff in ND. destruct ND as [NI ND].
  intros [E|Hin]; [subst y; apply NI; apply in_or_app; right; exact Hx| exact (IH l2 x ND Hx Hin)].
Qed.
