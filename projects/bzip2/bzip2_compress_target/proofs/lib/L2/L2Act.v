(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.AS Require Import ShapeAlg.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.Lib Require Import ImageA RzCPS.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A Require Import Layout RT_iface D_defs D_kit D_clx I_read.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A Require Import Shadow.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.L2 Require Import L2Kit.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require Import PropExec.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import Tac WalkLib SegsA0.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzArr CmpMem AsanKit.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require CmpSepV.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Open Scope Z_scope.
Module KMem := OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.Lib.Mem.
Module KMState := OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.Lib.MState.
Module KFrame := OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.Lib.Frame.
Module KStep := OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.Lib.Step.
Module KCells := OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.Lib.Cells.
#[local] Notation mem := (word -> option byte).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma pfp_of_nmunch : forall live frames sp W (m m' : mem), munch W m m' -> rt_pres_fp live frames sp W m m'.
Proof. intros live frames sp W m m' MU a _ Ho. exact (MU a Ho). Qed.
Lemma pfp_of_pres : forall live frames sp W (m m' : mem), rt_pres live frames sp m m' -> rt_pres_fp live frames sp W m m'.
Proof. intros live frames sp W m m' H a Ha _. exact (H a Ha). Qed.
Lemma pfp_of_ex : forall live frames sp d n (m m' : mem), rt_pres_ex live frames sp d n m m' -> rt_pres_fp live frames sp [(d, d + n)] m m'.
Proof. intros live frames sp d n m m' H a Ha Ho. apply (H a Ha). cbn [KFrame.outside] in Ho. tauto. Qed.
Lemma pfp_refl : forall live frames sp W (m : mem), rt_pres_fp live frames sp W m m.
Proof. intros live frames sp W m a _ _. reflexivity. Qed.
Lemma pfp_trans : forall live frames sp W (m1 m2 m3 : mem), rt_pres_fp live frames sp W m1 m2 -> rt_pres_fp live frames sp W m2 m3 -> rt_pres_fp live frames sp W m1 m3.
Proof. intros live frames sp W m1 m2 m3 H1 H2 a Ha Ho. rewrite (H2 a Ha Ho). exact (H1 a Ha Ho). Qed.
(* [comment removed for export] *)
Lemma pfp_weaken : forall live frames sp W W' (m m' : mem), rt_pres_fp live frames sp W m m' -> (forall x, ~ KFrame.outside W x -> ~ KFrame.outside W' x) ->
  rt_pres_fp live frames sp W' m m'.
Proof.
  intros live frames sp W W' m m' H HW a Ha Ho. apply (H a Ha). destruct (outside_dec W (bv_unsigned a)) as [O|O]; [exact O| exfalso; exact (HW _ O Ho)].
Qed.

(* [comment removed for export] *)
Lemma aclient_below : forall RT (AF : art_facts RT) Σ (m : mem) sp a, ART RT Σ m -> aclient (rt_live RT Σ) (rt_frames RT Σ) sp a -> a < USTACK_TOP.
Proof.
  intros RT AF Σ m sp a ART0 Ha. pose proof (af_sp0_range RT AF Σ m ART0) as SPR.
  destruct Ha as [H|H]; [lia|].
  destruct (aclient_split RT AF Σ m USTACK_TOP a ART0 (or_intror H)) as [E|E]; [| unfold STACK_WIN in *; lia].
  exfalso. destruct H as [H|[H|[H|H]]].
  - pose proof (client_static_range a H). unfold SEGTOP_A, USTACK_TOP in *. lia.
  - destruct H as (p & n & Hin & Hp). pose proof (af_live_range RT AF Σ m p n ART0 Hin). unfold STACK_WIN in *. lia.
  - destruct H as (f & k & Hin & Hf). pose proof (af_frames_range RT AF Σ m f k ART0 Hin) as (_ & H2 & _). unfold STACK_WIN in *. lia.
  - destruct H as (f & k & Hin & Hf). pose proof (af_frames_range RT AF Σ m f k ART0 Hin) as (_ & H2 & _).
    unfold shad, SHB in Hf. unfold STACK_WIN, USTACK_TOP, SEGTOP_A in *. Z.div_mod_to_equations. lia.
Qed.

(* [comment removed for export] *)
Lemma ASTA_switch : forall RT (Σ Σ' : rts RT) PMc Pm c, ASTA RT Σ PMc Pm c -> rt_allow RT Σ' = rt_allow RT Σ ->
  (forall mo, ARTM RT Σ mo -> ARTM RT Σ' mo) -> ASTA RT Σ' PMc Pm c.
Proof.
  intros RT Σ Σ' PMc Pm c H HA HM. unfold ASTA in *. rewrite HA.
  eapply AST_conseq; [exact H| auto|]. intros mo [H1 H2]. split; [apply HM; exact H1| exact H2].
Qed.

(* [comment removed for export] *)
Lemma newchunk_apart : forall RT (AF : art_facts RT) (Σ Σ1 : rts RT) (m1 : mem) p n usp a,
  ART RT Σ1 m1 -> rt_live RT Σ1 = (p, n) :: rt_live RT Σ -> rt_frames RT Σ1 = rt_frames RT Σ -> rt_sp0 RT Σ1 = rt_sp0 RT Σ ->
  rt_sp0 RT Σ - STACK_WIN <= usp -> aclient (rt_live RT Σ) (rt_frames RT Σ) usp a -> ~ (p <= a < p + n).
Proof.
  intros RT AF Σ Σ1 m1 p n usp a ART1 LV FRS SP0 LU Ha.
  assert (INP : In (p, n) (rt_live RT Σ1)) by (rewrite LV; left; reflexivity).
  pose proof (af_live_range RT AF Σ1 m1 p n ART1 INP) as (R0 & R1 & R2). rewrite SP0 in R1.
  pose proof (af_live_offshadow RT AF Σ1 m1 p n ART1 INP) as R3.
  destruct Ha as [H|[H|[H|[H|H]]]].
  - lia.
  - pose proof (client_static_range a H). unfold SEGTOP_A in *. lia.
  - destruct H as (p' & n' & Hin & Hp). destruct (af_live_disj RT AF Σ1 m1 p n p' n' [] (rt_live RT Σ) ART1 LV Hin) as [D|D]; lia.
  - destruct H as (f & k & Hin & Hf). rewrite <- FRS in Hin. pose proof (af_frames_range RT AF Σ1 m1 f k ART1 Hin) as (_ & _ & _ & F3).
    destruct (F3 p n INP); lia.
  - destruct H as (f & k & Hin & Hf). rewrite <- FRS in Hin. pose proof (af_fshadow_apart RT AF Σ1 m1 f k ART1 Hin) as (SL & _).
    destruct (SL p n INP); lia.
Qed.
Lemma live_remove_keep : forall (l : list (Z * Z)) p e, In e l -> fst e <> p -> In e (live_remove p l).
Proof.
  intros l p e He Hp. unfold live_remove. apply stdpp.base.list_elem_of_In. apply stdpp.list_basics.list.list_elem_of_filter.
  split; [| apply stdpp.base.list_elem_of_In; exact He]. apply Z.eqb_neq in Hp. rewrite Hp. exact I.
Qed.

(* [comment removed for export] *)
Record act_geom (RT : rt_sig) (lo P usp sp0 : Z) (hasf : bool) (k : nat) (FB SHF FSZ SSZ : Z) (fr : list (Z * nat)) (live0 : list (Z * Z)) (Wc : list (Z * Z)) : Prop := mkAG {
  (* [comment removed for export] *)
  ag_fsz : if hasf then fs_size k = FSZ else FSZ = 0;
  ag_ssz : FSZ = 8 * SSZ;
  ag_ssb : SSZ < 1048576;
  ag_ax : sanchor FB SHF;                                    (* [comment removed for export] *)
  ag_low : sp0 - STACK_WIN <= lo;
  ag_lor : lo + RT_STACK <= P;
  ag_pus : P <= usp;
  ag_spt : usp + 16 <= USTACK_TOP;
  ag_spa : P mod 16 = 0;
  ag_gfr : 0 < FB /\ FB + FSZ <= sp0 - STACK_WIN;
  ag_gsh : 0 <= SHF /\ SHF + SSZ <= sp0 - STACK_WIN;
  ag_sp0 : SEGTOP_A + STACK_WIN <= sp0 <= USTACK_TOP;
  (* [comment removed for export] *)
  ag_cap : forall x, aclient live0 fr usp x -> ~ ((P <= x < usp) \/ (FB <= x < FB + FSZ) \/ (SHF <= x < SHF + SSZ));
  (* [comment removed for export] *)
  ag_wcl : forall x, ~ outside Wc x -> aclient live0 fr usp x
}.

Arguments ag_fsz {RT lo P usp sp0 hasf k FB SHF FSZ SSZ fr live0 Wc} _.
Arguments ag_ssz {RT lo P usp sp0 hasf k FB SHF FSZ SSZ fr live0 Wc} _.
Arguments ag_ax {RT lo P usp sp0 hasf k FB SHF FSZ SSZ fr live0 Wc} _.
Arguments ag_low {RT lo P usp sp0 hasf k FB SHF FSZ SSZ fr live0 Wc} _.
Arguments ag_lor {RT lo P usp sp0 hasf k FB SHF FSZ SSZ fr live0 Wc} _.
Arguments ag_pus {RT lo P usp sp0 hasf k FB SHF FSZ SSZ fr live0 Wc} _.
Arguments ag_spt {RT lo P usp sp0 hasf k FB SHF FSZ SSZ fr live0 Wc} _.
Arguments ag_spa {RT lo P usp sp0 hasf k FB SHF FSZ SSZ fr live0 Wc} _.
Arguments ag_gfr {RT lo P usp sp0 hasf k FB SHF FSZ SSZ fr live0 Wc} _.
Arguments ag_gsh {RT lo P usp sp0 hasf k FB SHF FSZ SSZ fr live0 Wc} _.
Arguments ag_sp0 {RT lo P usp sp0 hasf k FB SHF FSZ SSZ fr live0 Wc} _.
Arguments ag_cap {RT lo P usp sp0 hasf k FB SHF FSZ SSZ fr live0 Wc} _.
Arguments ag_wcl {RT lo P usp sp0 hasf k FB SHF FSZ SSZ fr live0 Wc} _.

Section Act.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Variables (lo P usp sp0 : Z) (hasf : bool) (k : nat) (FB SHF FSZ SSZ : Z) (fr : list (Z * nat)) (live0 : list (Z * Z)) (Wc : list (Z * Z)).
Hypothesis G : act_geom RT lo P usp sp0 hasf k FB SHF FSZ SSZ fr live0 Wc.
Ltac ag_open := pose proof G as [FSZE SSZE SSB AX LOW LOR PUS SPT SPA GFR GSH SP0R CAP WCL].

(* [comment removed for export] *)
Definition sig_ok (Σ : rts RT) : Prop :=
  rt_frames RT Σ = (if hasf then [(FB, k)] else []) ++ fr /\ rt_sp0 RT Σ = sp0 /\ (forall e, In e live0 -> In e (rt_live RT Σ)).

Lemma sig_ok_eq : forall Σ Σ', sig_ok Σ -> rt_live RT Σ' = rt_live RT Σ -> rt_frames RT Σ' = rt_frames RT Σ -> rt_sp0 RT Σ' = rt_sp0 RT Σ -> sig_ok Σ'.
Proof. intros Σ Σ' (H1 & H2 & H3) E1 E2 E3. unfold sig_ok. rewrite E1, E2, E3. auto. Qed.
Lemma sig_ok_cons : forall Σ Σ' e, sig_ok Σ -> rt_live RT Σ' = e :: rt_live RT Σ -> rt_frames RT Σ' = rt_frames RT Σ -> rt_sp0 RT Σ' = rt_sp0 RT Σ -> sig_ok Σ'.
Proof. intros Σ Σ' e (H1 & H2 & H3) E1 E2 E3. unfold sig_ok. rewrite E1, E2, E3. split; [exact H1|]. split; [exact H2|]. intros e' He'. right. exact (H3 e' He'). Qed.
Lemma sig_INF : forall Σ, hasf = true -> sig_ok Σ -> In (FB, k) (rt_frames RT Σ).
Proof. intros Σ HF (H & _). rewrite H, HF. left. reflexivity. Qed.
Lemma hasf_cases : (hasf = true /\ fs_size k = FSZ) \/ (hasf = false /\ FSZ = 0 /\ SSZ = 0).
Proof. ag_open. clear - FSZE SSZE. destruct hasf; [left; split; [reflexivity| exact FSZE]| right; split; [reflexivity| lia]]. Qed.

Lemma SHFB : shad FB = SHF. Proof. ag_open. destruct AX as [_ E]. unfold shad, SHB. lia. Qed.
Lemma SHFE : shad (FB + FSZ) = SHF + SSZ.
Proof. ag_open. destruct AX as [A1 E]. unfold shad, SHB. rewrite E, SSZE. clear - A1. Z.div_mod_to_equations. lia. Qed.
Lemma P_unsigned : bv_unsigned (Z_to_bv 64 P) = P.
Proof. ag_open. apply unsigned_lit. unfold SEGTOP_A, STACK_WIN, RT_STACK, USTACK_TOP in *. lia. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma acl_stack : forall Σ x, P <= x < USTACK_TOP -> aclient (rt_live RT Σ) (rt_frames RT Σ) P x.
Proof. intros Σ x H. left. exact H. Qed.
Lemma acl_frame : forall Σ x, sig_ok Σ -> FB <= x < FB + FSZ - 8 -> aclient (rt_live RT Σ) (rt_frames RT Σ) P x.
Proof.
  intros Σ x S H. destruct hasf_cases as [[HF FSZE]|[HF [Z1 Z2]]]; [| exfalso; lia].
  right; right; right; left. exists FB, k. rewrite FSZE. split; [exact (sig_INF Σ HF S)| exact H].
Qed.
Lemma acl_shadow : forall Σ x, sig_ok Σ -> SHF <= x < SHF + SSZ -> aclient (rt_live RT Σ) (rt_frames RT Σ) P x.
Proof.
  intros Σ x S H. destruct hasf_cases as [[HF FSZE]|[HF [Z1 Z2]]]; [| exfalso; lia].
  right; right; right; right. exists FB, k. rewrite FSZE, SHFB, SHFE. split; [exact (sig_INF Σ HF S)| exact H].
Qed.
Lemma acl_live : forall Σ p l x, In (p, l) (rt_live RT Σ) -> p <= x < p + l -> aclient (rt_live RT Σ) (rt_frames RT Σ) P x.
Proof. intros Σ p l x H Hx. right; right; left. exists p, l. split; [exact H| exact Hx]. Qed.
Lemma acl_static : forall Σ x, client_static x -> aclient (rt_live RT Σ) (rt_frames RT Σ) P x.
Proof. intros Σ x H. right; left. exact H. Qed.
Lemma acl_caller : forall Σ x, sig_ok Σ -> aclient live0 fr usp x -> aclient (rt_live RT Σ) (rt_frames RT Σ) P x.
Proof.
  intros Σ x (S1 & S2 & S3) H. ag_open. apply (aclient_mono live0 fr usp _ _ P x H); [exact S3| | exact PUS].
  intros e He. rewrite S1. apply in_or_app. right. exact He.
Qed.

(* [comment removed for export] *)
Definition cls (Σ : rts RT) (a n : Z) : Prop := forall x, a <= x < a + n -> aclient (rt_live RT Σ) (rt_frames RT Σ) P x.
Lemma cls_stack : forall Σ a n, P <= a -> a + n <= USTACK_TOP -> cls Σ a n.
Proof. intros Σ a n H1 H2 x Hx. apply acl_stack. lia. Qed.
(* [comment removed for export] *)
Lemma cls_rframe : forall Σ a n, P <= a -> a + n <= usp -> cls Σ a n.
Proof. intros Σ a n H1 H2. ag_open. apply cls_stack; [exact H1| lia]. Qed.
Lemma cls_frame : forall Σ a n, sig_ok Σ -> FB <= a -> a + n <= FB + FSZ - 8 -> cls Σ a n.
Proof. intros Σ a n S H1 H2 x Hx. apply (acl_frame Σ x S). lia. Qed.
Lemma cls_shadow : forall Σ a n, sig_ok Σ -> SHF <= a -> a + n <= SHF + SSZ -> cls Σ a n.
Proof. intros Σ a n S H1 H2 x Hx. apply (acl_shadow Σ x S). lia. Qed.
Lemma cls_live : forall Σ p l a n, In (p, l) (rt_live RT Σ) -> p <= a -> a + n <= p + l -> cls Σ a n.
Proof. intros Σ p l a n H H1 H2 x Hx. apply (acl_live Σ p l x H). lia. Qed.
(* [comment removed for export] *)
Lemma cls_caller : forall Σ a n, sig_ok Σ -> (forall x, a <= x < a + n -> aclient live0 fr usp x) -> cls Σ a n.
Proof. intros Σ a n S H x Hx. exact (acl_caller Σ x S (H x Hx)). Qed.
Lemma cls_static : forall Σ a n, (forall x, a <= x < a + n -> client_static x) -> cls Σ a n.
Proof. intros Σ a n H x Hx. exact (acl_static Σ x (H x Hx)). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section Xfer.
Variables (Σ : rts RT) (W : list (Z * Z)) (m m' : mem).
Hypothesis STEP : rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) P W m m'.

Lemma x_agree : forall a n, cls Σ a n -> disjoint_from W a n -> agree_on (fun x => a <= x < a + n) m m'.
Proof. intros a n C D x Hx. apply STEP; [exact (C _ Hx)| exact (disjoint_outside W a n _ D Hx)]. Qed.

Lemma x_rw_cells : forall A cs, rw_cells a0segs m A cs -> cls Σ A (Z.of_nat (cells_size cs)) -> disjoint_from W A (Z.of_nat (cells_size cs)) ->
  rw_cells a0segs m' A cs.
Proof. intros A cs H C D. exact (n_rw_cells_agree a0segs m m' A cs H (x_agree _ _ C D)). Qed.
Lemma x_ro_cells : forall A cs, ro_cells a0segs m A cs -> cls Σ A (Z.of_nat (cells_size cs)) -> disjoint_from W A (Z.of_nat (cells_size cs)) ->
  ro_cells a0segs m' A cs.
Proof. intros A cs H C D. exact (n_ro_cells_agree a0segs m m' A cs H (x_agree _ _ C D)). Qed.
Lemma x_u8arr : forall A bs, u8arr a0segs m A bs -> cls Σ A (Z.of_nat (length bs)) -> disjoint_from W A (Z.of_nat (length bs)) -> u8arr a0segs m' A bs.
Proof. intros A bs H C D. exact (n_u8arr_agree a0segs m m' A bs H (x_agree _ _ C D)). Qed.
Lemma x_u32arr : forall A ws, u32arr a0segs m A ws -> cls Σ A (4 * Z.of_nat (length ws)) -> disjoint_from W A (4 * Z.of_nat (length ws)) -> u32arr a0segs m' A ws.
Proof. intros A ws H C D. exact (n_u32arr_agree a0segs m m' A ws H (x_agree _ _ C D)). Qed.
Lemma x_bytes_at : forall A bs, bytes_at a0segs m A bs -> cls Σ A (Z.of_nat (length bs)) -> disjoint_from W A (Z.of_nat (length bs)) -> bytes_at a0segs m' A bs.
Proof. intros A bs H C D. exact (bytes_at_agree a0segs m m' A bs H (x_agree _ _ C D)). Qed.
Lemma x_stk : forall a b, stk a0segs m a b -> cls Σ a (b - a) -> disjoint_from W a (b - a) -> stk a0segs m' a b.
Proof.
  intros a b H C D. apply (stk_agree_nw asegs m m' a b H). intros x Hx. cbv beta in Hx. apply (x_agree a (b - a) C D). cbv beta. lia.
Qed.
Lemma x_wr_at : forall a n, wr_at asegs m a n -> cls Σ a n -> disjoint_from W a n -> wr_at asegs m' a n.
Proof. intros a n H C D. exact (wr_at_agree_nw asegs m m' a n H (x_agree _ _ C D)). Qed.
End Xfer.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition ours (x : Z) : Prop := (P <= x < usp) \/ (FB <= x < FB + FSZ) \/ (SHF <= x < SHF + SSZ).
Variable mi : mem.              (* [comment removed for export] *)
Definition PRESI (m : mem) : Prop := agree_on (fun x => aclient live0 fr usp x /\ outside Wc x) mi m.

Lemma presi_refl : PRESI mi. Proof. intros a _. reflexivity. Qed.

(* [comment removed for export] *)
Lemma pres_step : forall Σ W (m m' : mem), sig_ok Σ -> PRESI m -> rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) P W m m' ->
  (forall x, ~ KFrame.outside W x -> ours x \/ ~ outside Wc x) -> PRESI m'.
Proof.
  intros Σ W m m' S H STEP HW a [Ha Ho]. ag_open. rewrite <- (H a (conj Ha Ho)). apply STEP; [exact (acl_caller Σ _ S Ha)|].
  destruct (outside_dec W (bv_unsigned a)) as [O|O]; [exact O| exfalso]. destruct (HW _ O) as [E|E]; [exact (CAP _ Ha E)| exact (E Ho)].
Qed.
(* [comment removed for export] *)
Lemma pres_step_ours : forall Σ d n (m m' : mem), sig_ok Σ -> PRESI m -> rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) P [(d, d + n)] m m' ->
  ((P <= d /\ d + n <= usp) \/ (FB <= d /\ d + n <= FB + FSZ) \/ (SHF <= d /\ d + n <= SHF + SSZ)) -> PRESI m'.
Proof.
  intros Σ d n m m' S H STEP HD. apply (pres_step Σ _ m m' S H STEP). intros x Hx. left. unfold ours.
  assert (E : d <= x < d + n). { destruct (Z_lt_dec x d) as [L|L]; [exfalso; apply Hx; cbn; split; [lia| exact I]|].
    destruct (Z_le_dec (d + n) x) as [L'|L']; [exfalso; apply Hx; cbn; split; [lia| exact I]| lia]. }
  lia.
Qed.
(* [comment removed for export] *)
Lemma pres_step_nil : forall Σ (m m' : mem), sig_ok Σ -> PRESI m -> rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) P [] m m' -> PRESI m'.
Proof. intros Σ m m' S H STEP. apply (pres_step Σ [] m m' S H STEP). intros x Hx. exfalso. apply Hx. exact I. Qed.

(* [comment removed for export] *)
Lemma after_l1 : forall Σ W (m m' : mem), sig_ok Σ -> ART RT Σ m -> KMem.mem_inv asegs m -> stk asegs m lo P -> PRESI m ->
  NMem.mem_inv a0segs m' -> munch W m m' -> wmono a0segs m m' ->
  (forall x, ~ KFrame.outside W x -> (P <= x < usp) \/ (FB <= x < FB + FSZ - 8) \/ (SHF <= x < SHF + SSZ) \/ ~ outside Wc x) ->
  ART RT Σ m' /\ KMem.mem_inv asegs m' /\ stk asegs m' lo P /\ PRESI m' /\ rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) P W m m'.
Proof.
  intros Σ W m m' S ART0 MI0 ST0 PR NMI MU WM HW. pose proof S as (S1 & S2 & S3). ag_open.
  assert (HA : forall x, ~ KFrame.outside W x -> aclient (rt_live RT Σ) (rt_frames RT Σ) P x).
  { intros x Hx. destruct (HW x Hx) as [E|[E|[E|E]]].
    - apply acl_stack. lia.
    - exact (acl_frame Σ x S E).
    - exact (acl_shadow Σ x S E).
    - exact (acl_caller Σ x S (WCL x E)). }
  split; [| split; [| split; [| split]]].
  - apply (art_of_munch RT AF Σ m m' W P ART0 ltac:(rewrite S2; unfold RT_STACK in *; lia) MU WM HA).
  - apply (kmem_inv_munch' asegs W m m' MI0 MU NMI). intros x Hx. unfold KMem.UTOP. pose proof (aclient_below RT AF Σ m P x ART0 (HA x Hx)) as B.
    unfold USTACK_TOP in B. exact B.
  - apply (stk_agree_nw asegs m m' lo P ST0). intros a Ha. cbv beta in Ha. apply MU.
    destruct (outside_dec W (bv_unsigned a)) as [O|O]; [exact O| exfalso]. destruct (HW _ O) as [E|[E|[E|E]]]; [lia| lia| lia|].
    assert (AC : aclient (rt_live RT Σ) (rt_frames RT Σ) usp (bv_unsigned a)).
    { apply (aclient_mono live0 fr usp _ _ usp _ (WCL _ E)); [exact S3| intros e He; rewrite S1; apply in_or_app; right; exact He| lia]. }
    destruct (aclient_split RT AF Σ m usp _ ART0 AC) as [E1|E1]; [lia| rewrite S2 in E1; lia].
  - apply (pres_step Σ W m m' S PR (pfp_of_nmunch _ _ _ W m m' MU)). intros x Hx. destruct (HW x Hx) as [E|[E|[E|E]]].
    + left; left; exact E.
    + left; right; left; lia.
    + left; right; right; exact E.
    + right; exact E.
  - exact (pfp_of_nmunch _ _ _ W m m' MU).
Qed.

(* [comment removed for export] *)
Lemma after_l1_leaf : forall Σ W D (m m' : mem), sig_ok Σ -> ART RT Σ m -> KMem.mem_inv asegs m -> PRESI m ->
  NMem.mem_inv a0segs m' -> munch W m m' -> wmono a0segs m m' -> 0 <= D -> lo + RT_STACK <= P - D ->
  (forall x, ~ KFrame.outside W x -> (P - D <= x < usp) \/ (FB <= x < FB + FSZ - 8) \/ (SHF <= x < SHF + SSZ) \/ ~ outside Wc x) ->
  ART RT Σ m' /\ KMem.mem_inv asegs m' /\ PRESI m' /\ rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) P W m m'.
Proof.
  intros Σ W D m m' S ART0 MI0 PR NMI MU WM HD HLO HW. pose proof S as (S1 & S2 & S3). ag_open.
  assert (HA : forall x, ~ KFrame.outside W x -> aclient (rt_live RT Σ) (rt_frames RT Σ) (P - D) x).
  { intros x Hx. destruct (HW x Hx) as [E|[E|[E|E]]].
    - left. lia.
    - apply (aclient_mono _ _ P _ _ (P - D) x (acl_frame Σ x S E)); [auto| auto| lia].
    - apply (aclient_mono _ _ P _ _ (P - D) x (acl_shadow Σ x S E)); [auto| auto| lia].
    - apply (aclient_mono _ _ P _ _ (P - D) x (acl_caller Σ x S (WCL x E))); [auto| auto| lia]. }
  split; [| split; [| split]].
  - apply (art_of_munch RT AF Σ m m' W (P - D) ART0 ltac:(rewrite S2; unfold RT_STACK in *; lia) MU WM HA).
  - apply (kmem_inv_munch' asegs W m m' MI0 MU NMI). intros x Hx. unfold KMem.UTOP. pose proof (aclient_below RT AF Σ m (P - D) x ART0 (HA x Hx)) as B.
    unfold USTACK_TOP in B. exact B.
  - intros a [Ha Ho]. rewrite <- (PR a (conj Ha Ho)). apply MU.
    destruct (outside_dec W (bv_unsigned a)) as [O|O]; [exact O| exfalso]. destruct (HW _ O) as [E|[E|[E|E]]].
    + assert (AC : aclient (rt_live RT Σ) (rt_frames RT Σ) usp (bv_unsigned a)).
      { apply (aclient_mono live0 fr usp _ _ usp _ Ha); [exact S3| intros e He; rewrite S1; apply in_or_app; right; exact He| lia]. }
      destruct (aclient_split RT AF Σ m usp _ ART0 AC) as [E1|E1].
      * exact (CAP _ Ha (or_introl (conj ltac:(lia) (proj2 E)))) || (apply (CAP _ Ha); left; lia).
      * rewrite S2 in E1. unfold RT_STACK in *. lia.
    + apply (CAP _ Ha). right; left. lia.
    + apply (CAP _ Ha). right; right. exact E.
    + exact (E Ho).
  - exact (pfp_of_nmunch _ _ _ W m m' MU).
Qed.

(* [comment removed for export] *)
Lemma after_call : forall Σ Σ' W (m m' : mem), sig_ok Σ -> rt_live RT Σ' = rt_live RT Σ -> rt_frames RT Σ' = rt_frames RT Σ -> rt_sp0 RT Σ' = rt_sp0 RT Σ ->
  PRESI m -> rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) P W m m' -> (forall x, ~ KFrame.outside W x -> ours x \/ ~ outside Wc x) ->
  sig_ok Σ' /\ PRESI m'.
Proof. intros Σ Σ' W m m' S E1 E2 E3 PR STEP HW. split; [exact (sig_ok_eq Σ Σ' S E1 E2 E3)| exact (pres_step Σ W m m' S PR STEP HW)]. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma cdst_frame : forall Σ (m : mem) d n, sig_ok Σ -> acc asegs m d n -> wr_at asegs m d n -> FB <= d -> d + n <= FB + FSZ - 8 ->
  checked_dst RT Σ m (Z_to_bv 64 P) d n.
Proof.
  intros Σ m d n S ACC WR H1 H2. destruct hasf_cases as [[HF FSZE]|[HF [Z1 Z2]]].
  - split; [intros _; split; [exact ACC|]| split; [| exact WR]].
    + right; left. exists FB, k. rewrite FSZE. split; [exact (sig_INF Σ HF S)| lia].
    + intros i Hi. rewrite P_unsigned. apply (acl_frame Σ _ S). lia.
  - split; [intros; lia| split; [intros; lia| exact WR]].
Qed.
Lemma cdst_stack : forall Σ (m : mem) d n, sig_ok Σ -> ART RT Σ m -> wr_at asegs m d n -> P <= d -> d + n <= USTACK_TOP - 16 ->
  checked_dst RT Σ m (Z_to_bv 64 P) d n.
Proof.
  intros Σ m d n S ART0 WR H1 H2. pose proof S as (S1 & S2 & S3). ag_open. unfold RT_STACK in *.
  split; [intros _; split| split; [| exact WR]].
  - apply (af_acc_stack RT AF Σ m d n ART0); rewrite ?S2; lia.
  - right; right; left. rewrite S2. lia.
  - intros i Hi. rewrite P_unsigned. apply acl_stack. lia.
Qed.
Lemma cdst_live : forall Σ (m : mem) p l d n, ART RT Σ m -> In (p, l) (rt_live RT Σ) -> p <= d -> d + n <= p + l -> 0 <= n ->
  checked_dst RT Σ m (Z_to_bv 64 P) d n.
Proof.
  intros Σ m p l d n ART0 LIV H1 H2 H3. destruct (af_acc_live RT AF Σ m p l ART0 LIV) as [WR ACC].
  split; [intros _; split| split].
  - exact (acc_sub asegs m p l d n ACC H1 H2).
  - left. exists p, l. split; [exact LIV| lia].
  - intros i Hi. rewrite P_unsigned. apply (acl_live Σ p l _ LIV). lia.
  - exact (wr_at_sub asegs m p l d n WR H1 H2 H3).
Qed.
Lemma csrc_frame : forall Σ (m : mem) s n, sig_ok Σ -> acc asegs m s n -> FB <= s -> s + n <= FB + FSZ - 8 -> checked_src RT Σ m (Z_to_bv 64 P) lo s n.
Proof.
  intros Σ m s n S ACC H1 H2. ag_open. destruct hasf_cases as [[HF FSZE']|[HF [Z1 Z2]]].
  - split; [intros _; split; [exact ACC|]| left; lia].
    right; left. exists FB, k. rewrite FSZE'. split; [exact (sig_INF Σ HF S)| lia].
  - split; [intros; lia| left; lia].
Qed.
Lemma csrc_stack : forall Σ (m : mem) s n, sig_ok Σ -> ART RT Σ m -> P <= s -> s + n <= USTACK_TOP - 16 -> checked_src RT Σ m (Z_to_bv 64 P) lo s n.
Proof.
  intros Σ m s n S ART0 H1 H2. pose proof S as (S1 & S2 & S3). ag_open. unfold RT_STACK in *.
  split; [intros _; split| right; rewrite P_unsigned; exact H1].
  - apply (af_acc_stack RT AF Σ m s n ART0); rewrite ?S2; lia.
  - right; right; left. rewrite S2. lia.
Qed.
Lemma csrc_live : forall Σ (m : mem) p l s n, sig_ok Σ -> ART RT Σ m -> In (p, l) (rt_live RT Σ) -> p <= s -> s + n <= p + l -> checked_src RT Σ m (Z_to_bv 64 P) lo s n.
Proof.
  intros Σ m p l s n S ART0 LIV H1 H2. pose proof S as (S1 & S2 & S3). ag_open. destruct (af_acc_live RT AF Σ m p l ART0 LIV) as [WR ACC].
  pose proof (af_live_range RT AF Σ m p l ART0 LIV) as (R0 & R1 & _). rewrite S2 in R1.
  split; [intros _; split| left; lia].
  - exact (acc_sub asegs m p l s n ACC H1 H2).
  - left. exists p, l. split; [exact LIV| lia].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Variable PMc : Model -> Prop.
Hypothesis FDO : fdfs_only PMc. Hypothesis MST : mat_stable PMc.

Lemma call_ok_P : forall Σ (m : mem), sig_ok Σ -> stk asegs m lo P -> call_ok RT Σ m (Z_to_bv 64 P) lo.
Proof.
  intros Σ m (S1 & S2 & S3) ST. ag_open. unfold call_ok. rewrite P_unsigned, S2.
  split; [exact ST|]. split; [exact LOW|]. split; [exact LOR|]. split; [lia| exact SPA].
Qed.

(* [comment removed for export] *)
Lemma ss_call : forall Σ v off n (m : mem) (ra gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc T c,
  (forall v, In v set_shadow_vals -> set_shadow_contract RT v) ->
  sig_ok Σ -> In v set_shadow_vals -> ((0 <=? off) && (off + n <=? SSZ) && (0 <=? n))%bool = true ->
  ART RT Σ m -> KMem.mem_inv asegs m -> stk asegs m lo P -> wr_at asegs m SHF SSZ ->
  ASTA RT Σ PMc (eq (MS (mkR ra (Z_to_bv 64 P) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (SHF + off)) (Z_to_bv 64 n) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                        F (Z_to_bv 64 (e_set_shadow v)) fc None m (seg_rom a0segs))) c ->
  (forall c' (m' : mem) (u0 u1 u2 v0 e1 e2 e3 e4 e5 e6 e7 u3 u4 u5 u6 : word) F' fc',
     ASTA RT Σ PMc (eq (MS (mkR ra (Z_to_bv 64 P) gp tp u0 u1 u2 s0 s1 v0 e1 e2 e3 e4 e5 e6 e7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 u3 u4 u5 u6)
                           F' (KMState.ret_pc ra) fc' None m' (seg_rom a0segs))) c' ->
     ART RT Σ m' -> KMem.mem_inv asegs m' -> stk asegs m' lo P -> wmono asegs m m' ->
     bytes_at asegs m' (SHF + off) (repeat (Z_to_bv 8 v) (Z.to_nat n)) ->
     rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) P [(SHF + off, SHF + off + n)] m m' ->
     realizes asegs c' T) ->
  realizes asegs c T.
Proof.
  intros Σ v off n m ra gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc T c SSH S Hv HB ART0 MI0 ST0 WRS Hc Hk.
  apply andb_prop in HB as [HB Hn]. apply andb_prop in HB as [D0 D1]. apply Z.leb_le in D0, D1, Hn. ag_open.
  refine (cps_realizes asegs _ _ T c _ Hc _).
  { eapply (SSH v Hv Σ PMc _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m (SHF + off) n lo FDO MST Hv).
    - reflexivity.
    - reflexivity.
    - lia.
    - intros i Hi. destruct hasf_cases as [[HF FSZE']|[HF [Z1 Z2]]]; [| exfalso; lia].
      exists FB, k. rewrite FSZE', SHFB, SHFE. split; [exact (sig_INF Σ HF S)| lia].
    - apply (wr_at_sub asegs m SHF SSZ (SHF + off) n WRS); lia.
    - exact ART0.
    - exact MI0.
    - exact (call_ok_P Σ m S ST0). }
  intros c1 (v0 & Hc1). unfold icpt_post in Hc1.
  destruct (ASTA_unpack RT Σ _ _ c1 Hc1) as (ms1 & (m1 & RS1 & (ART1 & MI1 & WM1 & ST1) & PRES1 & BY1) & Hc1'). clear Hc1.
  destruct RS1 as (u0 & u1 & u2 & e1 & e2 & e3 & e4 & e5 & e6 & e7 & u3 & u4 & u5 & u6 & F1 & fc1 & ->).
  rewrite P_unsigned in ST1, PRES1.
  exact (Hk c1 m1 u0 u1 u2 v0 e1 e2 e3 e4 e5 e6 e7 u3 u4 u5 u6 F1 fc1 Hc1' ART1 MI1 ST1 WM1 BY1 (pfp_of_ex _ _ _ _ _ m m1 PRES1)).
Qed.

(* [comment removed for export] *)
Lemma memset_call : forall Σ d n (cb : byte) (m : mem) (ra gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc T c,
  memset_icontract RT e_asan_memset ->
  sig_ok Σ -> 0 <= d <= 2^47 -> 0 <= n < 2^40 -> checked_dst RT Σ m (Z_to_bv 64 P) d n ->
  ART RT Σ m -> KMem.mem_inv asegs m -> stk asegs m lo P ->
  ASTA RT Σ PMc (eq (MS (mkR ra (Z_to_bv 64 P) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 d) (Z_to_bv 64 (bv_unsigned cb)) (Z_to_bv 64 n) a3 a4 a5 a6 a7
                             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                        F (Z_to_bv 64 e_asan_memset) fc None m (seg_rom a0segs))) c ->
  (forall c' (m' : mem) (u0 u1 u2 e1 e2 e3 e4 e5 e6 e7 u3 u4 u5 u6 : word) F' fc',
     ASTA RT Σ PMc (eq (MS (mkR ra (Z_to_bv 64 P) gp tp u0 u1 u2 s0 s1 (Z_to_bv 64 d) e1 e2 e3 e4 e5 e6 e7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 u3 u4 u5 u6)
                           F' (KMState.ret_pc ra) fc' None m' (seg_rom a0segs))) c' ->
     ART RT Σ m' -> KMem.mem_inv asegs m' -> stk asegs m' lo P -> wmono asegs m m' ->
     bytes_at asegs m' d (repeat cb (Z.to_nat n)) ->
     rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) P [(d, d + n)] m m' ->
     realizes asegs c' T) ->
  realizes asegs c T.
Proof.
  intros Σ d n cb m ra gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc T c MSET S Hd Hn CD ART0 MI0 ST0 Hc Hk.
  refine (cps_realizes asegs _ _ T c _ Hc _).
  { eapply (MSET Σ PMc _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m d n cb lo FDO MST).
    - reflexivity.
    - reflexivity.
    - reflexivity.
    - exact Hd.
    - exact Hn.
    - exact CD.
    - exact ART0.
    - exact MI0.
    - exact (call_ok_P Σ m S ST0). }
  intros c1 Hc1. unfold icpt_post in Hc1.
  destruct (ASTA_unpack RT Σ _ _ c1 Hc1) as (ms1 & (m1 & RS1 & (ART1 & MI1 & WM1 & ST1) & PRES1 & BY1) & Hc1'). clear Hc1.
  destruct RS1 as (u0 & u1 & u2 & e1 & e2 & e3 & e4 & e5 & e6 & e7 & u3 & u4 & u5 & u6 & F1 & fc1 & ->).
  rewrite P_unsigned in ST1, PRES1.
  exact (Hk c1 m1 u0 u1 u2 e1 e2 e3 e4 e5 e6 e7 u3 u4 u5 u6 F1 fc1 Hc1' ART1 MI1 ST1 WM1 BY1 (pfp_of_ex _ _ _ _ _ m m1 PRES1)).
Qed.

(* [comment removed for export] *)
Lemma memcpy_call : forall Σ d s (bs : list byte) (m : mem) (ra gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc T c,
  memcpy_icontract RT e_asan_memcpy ->
  sig_ok Σ -> 0 <= d <= 2^47 -> 0 <= s <= 2^47 -> Z.of_nat (length bs) < 2^40 -> bytes_at asegs m s bs ->
  checked_src RT Σ m (Z_to_bv 64 P) lo s (Z.of_nat (length bs)) -> checked_dst RT Σ m (Z_to_bv 64 P) d (Z.of_nat (length bs)) ->
  (d + Z.of_nat (length bs) <= s \/ s + Z.of_nat (length bs) <= d) ->
  ART RT Σ m -> KMem.mem_inv asegs m -> stk asegs m lo P ->
  ASTA RT Σ PMc (eq (MS (mkR ra (Z_to_bv 64 P) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 d) (Z_to_bv 64 s) (Z_to_bv 64 (Z.of_nat (length bs))) a3 a4 a5 a6 a7
                             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                        F (Z_to_bv 64 e_asan_memcpy) fc None m (seg_rom a0segs))) c ->
  (forall c' (m' : mem) (u0 u1 u2 e1 e2 e3 e4 e5 e6 e7 u3 u4 u5 u6 : word) F' fc',
     ASTA RT Σ PMc (eq (MS (mkR ra (Z_to_bv 64 P) gp tp u0 u1 u2 s0 s1 (Z_to_bv 64 d) e1 e2 e3 e4 e5 e6 e7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 u3 u4 u5 u6)
                           F' (KMState.ret_pc ra) fc' None m' (seg_rom a0segs))) c' ->
     ART RT Σ m' -> KMem.mem_inv asegs m' -> stk asegs m' lo P -> wmono asegs m m' ->
     bytes_at asegs m' d bs ->
     rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) P [(d, d + Z.of_nat (length bs))] m m' ->
     realizes asegs c' T) ->
  realizes asegs c T.
Proof.
  intros Σ d s bs m ra gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc T c MCPY S Hd Hs Hn BS CS CD DJ ART0 MI0 ST0 Hc Hk.
  refine (cps_realizes asegs _ _ T c _ Hc _).
  { eapply (MCPY Σ PMc _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m d s bs lo FDO MST).
    - reflexivity.
    - reflexivity.
    - reflexivity.
    - exact Hd.
    - exact Hs.
    - exact Hn.
    - exact BS.
    - exact CS.
    - exact CD.
    - exact DJ.
    - exact ART0.
    - exact MI0.
    - exact (call_ok_P Σ m S ST0). }
  intros c1 Hc1. unfold icpt_post in Hc1.
  destruct (ASTA_unpack RT Σ _ _ c1 Hc1) as (ms1 & (m1 & RS1 & (ART1 & MI1 & WM1 & ST1) & PRES1 & BY1) & Hc1'). clear Hc1.
  destruct RS1 as (u0 & u1 & u2 & e1 & e2 & e3 & e4 & e5 & e6 & e7 & u3 & u4 & u5 & u6 & F1 & fc1 & ->).
  rewrite P_unsigned in ST1, PRES1.
  exact (Hk c1 m1 u0 u1 u2 e1 e2 e3 e4 e5 e6 e7 u3 u4 u5 u6 F1 fc1 Hc1' ART1 MI1 ST1 WM1 BY1 (pfp_of_ex _ _ _ _ _ m m1 PRES1)).
Qed.


(* [comment removed for export] *)
Lemma malloc_call : forall Σ n (m : mem) (ra gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc T c,
  malloc_contract RT ->
  sig_ok Σ -> 1 <= n <= 0x8000000 -> tp = Z_to_bv 64 0x5fc0d8 -> Z.of_nat (length (rt_live RT Σ)) < LIVE_MAX -> mcost n <= rt_credit RT Σ ->
  ART RT Σ m -> KMem.mem_inv asegs m -> stk asegs m lo P -> PRESI m -> unwind_ch m ra s0 (Z_to_bv 64 P) ->
  ASTA RT Σ PMc (eq (MS (mkR ra (Z_to_bv 64 P) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 n) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                        F (Z_to_bv 64 e_malloc) fc None m (seg_rom a0segs))) c ->
  (forall c' (Σ' : rts RT) (m' : mem) (p : Z) (u0 u1 u2 e1 e2 e3 e4 e5 e6 e7 u3 u4 u5 u6 : word) F' fc',
     ASTA RT Σ' PMc (eq (MS (mkR ra (Z_to_bv 64 P) gp tp u0 u1 u2 s0 s1 (Z_to_bv 64 p) e1 e2 e3 e4 e5 e6 e7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 u3 u4 u5 u6)
                            F' (KMState.ret_pc ra) fc' None m' (seg_rom a0segs))) c' ->
     sig_ok Σ' -> rt_live RT Σ' = (p, n) :: rt_live RT Σ -> rt_frames RT Σ' = rt_frames RT Σ -> rt_credit RT Σ' = rt_credit RT Σ - mcost n ->
     0 < p -> p mod 16 = 0 -> p + n < USTACK_TOP ->
     ART RT Σ' m' -> KMem.mem_inv asegs m' -> stk asegs m' lo P -> wmono asegs m m' -> PRESI m' ->
     wr_at asegs m' p n -> acc asegs m' p n ->
     rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) P [] m m' ->
     (forall a, aclient (rt_live RT Σ) (rt_frames RT Σ) P a -> ~ (p <= a < p + n)) ->
     realizes asegs c' T) ->
  realizes asegs c T.
Proof.
  intros Σ n m ra gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc T c MAL S Hn TP LVM CRED ART0 MI0 ST0 PR UW Hc Hk.
  pose proof S as (S1 & S2 & S3). ag_open.
  refine (cps_realizes asegs _ _ T c _ Hc _).
  { eapply (MAL Σ PMc _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m n lo FDO MST Hn).
    - reflexivity.
    - exact TP.
    - exact LVM.
    - exact CRED.
    - exact ART0.
    - exact MI0.
    - exact (call_ok_P Σ m S ST0).
    - exact UW. }
  intros c1 (Σ' & p & Hq & LV' & FR' & SP' & CR' & P0 & P16 & PT).
  destruct (ASTA_unpack RT Σ' _ _ c1 Hq) as (ms1 & (m1 & RS1 & (ART1 & MI1 & WM1 & ST1) & PRES1 & WR1 & ACC1) & Hc1). clear Hq.
  destruct RS1 as (u0 & u1 & u2 & e1 & e2 & e3 & e4 & e5 & e6 & e7 & u3 & u4 & u5 & u6 & F1 & fc1 & ->).
  rewrite P_unsigned in ST1, PRES1.
  assert (STEP : rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) P [] m m1) by exact (pfp_of_pres _ _ _ [] m m1 PRES1).
  apply (Hk c1 Σ' m1 p u0 u1 u2 e1 e2 e3 e4 e5 e6 e7 u3 u4 u5 u6 F1 fc1 Hc1 (sig_ok_cons Σ Σ' (p, n) S LV' FR' SP') LV' FR' CR' P0 P16 PT ART1 MI1 ST1 WM1
           (pres_step_nil Σ m m1 S PR STEP) WR1 ACC1 STEP).
  intros a Ha. apply (newchunk_apart RT AF Σ Σ' m1 p n P a ART1 LV' FR' SP' ltac:(rewrite S2; unfold RT_STACK in *; lia) Ha).
Qed.

(* [comment removed for export] *)
Lemma free_call : forall Σ p n (m : mem) (ra gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc T c,
  free_contract RT ->
  sig_ok Σ -> In (p, n) (rt_live RT Σ) -> (forall e, In e live0 -> fst e <> p) -> tp = Z_to_bv 64 0x5fc0d8 ->
  ART RT Σ m -> KMem.mem_inv asegs m -> stk asegs m lo P -> PRESI m -> unwind_ch m ra s0 (Z_to_bv 64 P) ->
  ASTA RT Σ PMc (eq (MS (mkR ra (Z_to_bv 64 P) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 p) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                        F (Z_to_bv 64 e_free) fc None m (seg_rom a0segs))) c ->
  (forall c' (Σ' : rts RT) (m' : mem) (u0 u1 u2 v0 e1 e2 e3 e4 e5 e6 e7 u3 u4 u5 u6 : word) F' fc',
     ASTA RT Σ' PMc (eq (MS (mkR ra (Z_to_bv 64 P) gp tp u0 u1 u2 s0 s1 v0 e1 e2 e3 e4 e5 e6 e7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 u3 u4 u5 u6)
                            F' (KMState.ret_pc ra) fc' None m' (seg_rom a0segs))) c' ->
     sig_ok Σ' -> rt_live RT Σ' = live_remove p (rt_live RT Σ) -> rt_frames RT Σ' = rt_frames RT Σ -> rt_credit RT Σ' = rt_credit RT Σ ->
     ART RT Σ' m' -> KMem.mem_inv asegs m' -> stk asegs m' lo P -> PRESI m' ->
     rt_pres_fp (rt_live RT Σ') (rt_frames RT Σ') P [] m m' ->
     realizes asegs c' T) ->
  realizes asegs c T.
Proof.
  intros Σ p n m ra gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc T c FRE S LIV NL0 TP ART0 MI0 ST0 PR UW Hc Hk.
  pose proof S as (S1 & S2 & S3).
  refine (cps_realizes asegs _ _ T c _ Hc _).
  { eapply (FRE Σ PMc _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m p n lo FDO MST LIV).
    - reflexivity.
    - exact TP.
    - exact ART0.
    - exact MI0.
    - exact (call_ok_P Σ m S ST0).
    - exact UW. }
  intros c1 (Σ' & v0 & Hq & LV' & FR' & SP' & CR').
  destruct (ASTA_unpack RT Σ' _ _ c1 Hq) as (ms1 & (m1 & RS1 & (ART1 & MI1 & ST1) & PRES1) & Hc1). clear Hq.
  destruct RS1 as (u0 & u1 & u2 & e1 & e2 & e3 & e4 & e5 & e6 & e7 & u3 & u4 & u5 & u6 & F1 & fc1 & ->).
  rewrite P_unsigned in ST1, PRES1.
  assert (S' : sig_ok Σ').
  { unfold sig_ok. rewrite FR', SP', LV'. split; [exact S1|]. split; [exact S2|]. intros e He. apply live_remove_keep; [exact (S3 e He)| exact (NL0 e He)]. }
  assert (STEP : rt_pres_fp (rt_live RT Σ') (rt_frames RT Σ') P [] m m1) by (rewrite FR'; exact (pfp_of_pres _ _ _ [] m m1 PRES1)).
  apply (Hk c1 Σ' m1 u0 u1 u2 v0 e1 e2 e3 e4 e5 e6 e7 u3 u4 u5 u6 F1 fc1 Hc1 S' LV' FR' CR' ART1 MI1 ST1 (pres_step_nil Σ' m m1 S' PR STEP) STEP).
Qed.

(* [comment removed for export] *)
Lemma release_inline : forall Σ (m : mem), hasf = true -> sig_ok Σ -> ART RT Σ m ->
  exists (Σ' : rts RT) (fl : Z),
    KStep.rw_cells asegs m fl [KCells.C1 (Z_to_bv 8 1)] /\ KStep.ro_cells asegs m (FB + FSZ - 8) [KCells.C8 (Z_to_bv 64 fl)] /\ 0 < fl /\ fl + 1 <= sp0 - STACK_WIN /\
    forall (m' : mem), munch [(fl, fl + 1)] m m' -> wmono a0segs m m' -> KStep.rw_cells asegs m' fl [KCells.C1 (Z_to_bv 8 0)] ->
      KMem.mem_inv asegs m -> NMem.mem_inv a0segs m' -> stk asegs m lo P -> PRESI m ->
      ART RT Σ' m' /\ rt_frames RT Σ' = fr /\ rt_live RT Σ' = rt_live RT Σ /\ rt_sp0 RT Σ' = sp0 /\ rt_credit RT Σ' = rt_credit RT Σ
      /\ rt_allow RT Σ' = rt_allow RT Σ /\ (forall mo, ARTM RT Σ mo -> ARTM RT Σ' mo)
      /\ KMem.mem_inv asegs m' /\ stk asegs m' lo P /\ PRESI m'.
Proof.
  intros Σ m HF S ART0. pose proof S as (S1 & S2 & S3). rewrite HF in S1. cbn [app] in S1. ag_open. rewrite HF in FSZE.
  destruct (af_frame_release RT AF Σ m FB k fr ART0 S1) as (Σ' & fl & FLC & NAC & FL0 & FLW & FW & REL).
  rewrite S2 in FLW. rewrite FSZE in FW.
  exists Σ', fl. split; [exact FLC|]. split; [exact FW|]. split; [exact FL0|]. split; [exact FLW|].
  intros m' MU WM FLC' MI0 NMI ST0 PR.
  destruct (REL m' MU WM FLC') as (ART' & FRS' & LV' & SP' & CR' & AL' & AM').
  split; [exact ART'|]. split; [exact FRS'|]. split; [exact LV'|]. split; [rewrite SP'; exact S2|]. split; [exact CR'|]. split; [exact AL'|]. split; [exact AM'|].
  split; [| split].
  - apply (kmem_inv_munch' asegs [(fl, fl + 1)] m m' MI0 MU NMI). intros x Hx. revert Hx. refine (not_outside_cons _ _ _ _ _ _ _); [intro| refine (not_outside_nil _ _)].
    unfold KMem.UTOP. unfold STACK_WIN, USTACK_TOP in *. lia.
  - apply (stk_agree_nw asegs m m' lo P ST0). intros a Ha. cbv beta in Ha. apply MU. cbn [outside]. split; [lia| exact I].
  - intros a [Ha Ho]. rewrite <- (PR a (conj Ha Ho)). apply MU. cbn [outside]. split; [| exact I]. intros Hfl.
    assert (E : bv_unsigned a = fl) by lia. unfold RT_STACK in *.
    destruct Ha as [H|[H|[H|[H|H]]]]; [lia| | | |]; apply NAC; rewrite <- E.
    + right; left. exact H.
    + right; right; left. destruct H as (p & n & Hin & Hp). exists p, n. split; [exact (S3 _ Hin)| exact Hp].
    + right; right; right; left. destruct H as (f & k' & Hin & Hf). exists f, k'. split; [rewrite S1; right; exact Hin| exact Hf].
    + right; right; right; right. destruct H as (f & k' & Hin & Hf). exists f, k'. split; [rewrite S1; right; exact Hin| exact Hf].
Qed.

(* [comment removed for export] *)
Lemma release_inline2 : forall Σ (m : mem), hasf = true -> sig_ok Σ -> ART RT Σ m ->
  exists (Σ' : rts RT) (fl : Z),
    KStep.rw_cells asegs m fl [KCells.C1 (Z_to_bv 8 1)] /\ KStep.ro_cells asegs m (FB + FSZ - 8) [KCells.C8 (Z_to_bv 64 fl)] /\ 0 < fl /\ fl + 1 <= sp0 - STACK_WIN /\
    (forall a n, cls Σ a n -> a + n <= fl \/ fl + 1 <= a) /\
    forall (m' : mem), munch [(fl, fl + 1)] m m' -> wmono a0segs m m' -> KStep.rw_cells asegs m' fl [KCells.C1 (Z_to_bv 8 0)] ->
      KMem.mem_inv asegs m -> NMem.mem_inv a0segs m' -> stk asegs m lo P -> PRESI m ->
      ART RT Σ' m' /\ rt_frames RT Σ' = fr /\ rt_live RT Σ' = rt_live RT Σ /\ rt_sp0 RT Σ' = sp0 /\ rt_credit RT Σ' = rt_credit RT Σ
      /\ rt_allow RT Σ' = rt_allow RT Σ /\ (forall mo, ARTM RT Σ mo -> ARTM RT Σ' mo)
      /\ KMem.mem_inv asegs m' /\ stk asegs m' lo P /\ PRESI m'.
Proof.
  intros Σ m HF S ART0. pose proof S as (S1 & S2 & S3). pose proof S1 as S1'. rewrite HF in S1'. cbn [app] in S1'. ag_open.
  destruct (af_frame_release RT AF Σ m FB k fr ART0 S1') as (Σ' & fl & FLC & NAC & FL0 & FLW & FW & REL).
  destruct (release_inline Σ m HF S ART0) as (Σ2 & fl2 & R1 & R2 & R3 & R4 & R5).
  (* [comment removed for export] *)
  clear Σ2 fl2 R1 R2 R3 R4 R5.
  assert (FSZE' : fs_size k = FSZ) by (rewrite HF in FSZE; exact FSZE).
  rewrite S2 in FLW. rewrite FSZE' in FW.
  exists Σ', fl. split; [exact FLC|]. split; [exact FW|]. split; [exact FL0|]. split; [exact FLW|]. split.
  - intros a n C. destruct (Z_le_dec (a + n) fl) as [L|L]; [left; exact L|]. destruct (Z_le_dec (fl + 1) a) as [L'|L']; [right; exact L'|]. exfalso.
    assert (Hin : a <= fl < a + n) by lia. pose proof (C fl Hin) as AC. unfold RT_STACK in *.
    destruct AC as [H|H]; [lia|]. apply NAC. right. exact H.
  - intros m' MU WM FLC' MI0 NMI ST0 PR.
    destruct (REL m' MU WM FLC') as (ART' & FRS' & LV' & SP' & CR' & AL' & AM').
    split; [exact ART'|]. split; [exact FRS'|]. split; [exact LV'|]. split; [rewrite SP'; exact S2|]. split; [exact CR'|]. split; [exact AL'|]. split; [exact AM'|].
    split; [| split].
    + apply (kmem_inv_munch' asegs [(fl, fl + 1)] m m' MI0 MU NMI). intros x Hx. revert Hx. refine (not_outside_cons _ _ _ _ _ _ _); [intro| refine (not_outside_nil _ _)].
      unfold KMem.UTOP. unfold STACK_WIN, USTACK_TOP in *. lia.
    + apply (stk_agree_nw asegs m m' lo P ST0). intros a Ha. cbv beta in Ha. apply MU. cbn [outside]. split; [lia| exact I].
    + intros a [Ha Ho]. rewrite <- (PR a (conj Ha Ho)). apply MU. cbn [outside]. split; [| exact I]. intros Hfl.
      assert (E : bv_unsigned a = fl) by lia. unfold RT_STACK in *.
      destruct Ha as [H|[H|[H|[H|H]]]]; [lia| | | |]; apply NAC; rewrite <- E.
      * right; left. exact H.
      * right; right; left. destruct H as (p & n & Hin & Hp). exists p, n. split; [exact (S3 _ Hin)| exact Hp].
      * right; right; right; left. destruct H as (f & k' & Hin & Hf). exists f, k'. split; [rewrite S1'; right; exact Hin| exact Hf].
      * right; right; right; right. destruct H as (f & k' & Hin & Hf). exists f, k'. split; [rewrite S1'; right; exact Hin| exact Hf].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma pres_step_free : forall live (m m' : mem), (forall e, In e live0 -> In e live) -> PRESI m -> rt_pres live fr P m m' -> PRESI m'.
Proof.
  intros live m m' HL H PRES a [Ha Ho]. ag_open. rewrite <- (H a (conj Ha Ho)). apply PRES.
  apply (aclient_mono live0 fr usp live fr P _ Ha); [exact HL| auto| exact PUS].
Qed.

Lemma sfree_call : forall Σ size (m : mem) (ra gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc T c,
  stack_free_contract RT k -> (k = 6 \/ k = 7)%nat ->
  sig_ok Σ -> ((0 <? size) && (size <=? FSZ) && (size mod 8 =? 0))%bool = true ->
  ART RT Σ m -> KMem.mem_inv asegs m -> stk asegs m lo P -> PRESI m ->
  ASTA RT Σ PMc (eq (MS (mkR ra (Z_to_bv 64 P) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 FB) (Z_to_bv 64 size) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                        F (Z_to_bv 64 (e_stack_free k)) fc None m (seg_rom a0segs))) c ->
  (forall c' (Σ2 : rts RT) (m' : mem) (u0 u1 u2 v0 e1 e2 e3 e4 e5 e6 e7 u3 u4 u5 u6 : word) F' fc',
     ASTA RT Σ2 PMc (eq (MS (mkR ra (Z_to_bv 64 P) gp tp u0 u1 u2 s0 s1 v0 e1 e2 e3 e4 e5 e6 e7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 u3 u4 u5 u6)
                            F' (KMState.ret_pc ra) fc' None m' (seg_rom a0segs))) c' ->
     rt_frames RT Σ2 = fr -> rt_live RT Σ2 = rt_live RT Σ -> rt_sp0 RT Σ2 = sp0 -> rt_credit RT Σ2 = rt_credit RT Σ ->
     ART RT Σ2 m' -> KMem.mem_inv asegs m' -> stk asegs m' lo P -> wmono asegs m m' -> PRESI m' ->
     rt_pres_fp (rt_live RT Σ2) (rt_frames RT Σ2) P [] m m' ->
     realizes asegs c' T) ->
  realizes asegs c T.
Proof.
  intros Σ size m ra gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc T c SFREE Hk67 S HB ART0 MI0 ST0 PR Hc Hk.
  apply andb_prop in HB as [HB H8]. apply andb_prop in HB as [H0 H1]. apply Z.ltb_lt in H0. apply Z.leb_le in H1. apply Z.eqb_eq in H8.
  pose proof S as (S1 & S2 & S3). destruct hasf_cases as [[HF FSZE']|[HF [Z1 Z2]]]; [| exfalso; lia]. ag_open. rewrite HF in S1. cbn [app] in S1.
  refine (cps_realizes asegs _ _ T c _ Hc _).
  { eapply (SFREE Σ PMc _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m FB size fr lo FDO MST Hk67 S1).
    - reflexivity.
    - reflexivity.
    - rewrite FSZE'. lia.
    - exact H8.
    - exact ART0.
    - exact MI0.
    - exact (call_ok_P Σ m S ST0). }
  intros c1 (Σ2 & vret & Hq & FRS2 & LV2 & SP2 & CR2).
  destruct (ASTA_unpack RT Σ2 _ _ c1 Hq) as (ms1 & (m1 & RS1 & (ART1 & MI1 & WM1 & ST1) & PRES1) & Hc1). clear Hq.
  destruct RS1 as (u0 & u1 & u2 & e1 & e2 & e3 & e4 & e5 & e6 & e7 & u3 & u4 & u5 & u6 & F1 & fc1 & ->).
  rewrite P_unsigned in ST1, PRES1.
  apply (Hk c1 Σ2 m1 u0 u1 u2 vret e1 e2 e3 e4 e5 e6 e7 u3 u4 u5 u6 F1 fc1 Hc1 FRS2 LV2 ltac:(rewrite SP2; exact S2) CR2 ART1 MI1 ST1 WM1).
  - exact (pres_step_free (rt_live RT Σ) m m1 S3 PR PRES1).
  - rewrite LV2, FRS2. exact (pfp_of_pres _ _ _ [] m m1 PRES1).
Qed.

End Act.

Arguments SHFB {RT lo P usp sp0 hasf k FB SHF FSZ SSZ fr live0 Wc} G.
Arguments SHFE {RT lo P usp sp0 hasf k FB SHF FSZ SSZ fr live0 Wc} G.
Arguments P_unsigned {RT lo P usp sp0 hasf k FB SHF FSZ SSZ fr live0 Wc} G.
Arguments acl_frame {RT lo P usp sp0 hasf k FB SHF FSZ SSZ fr live0 Wc} G.
Arguments acl_shadow {RT lo P usp sp0 hasf k FB SHF FSZ SSZ fr live0 Wc} G.
Arguments acl_caller {RT lo P usp sp0 hasf k FB SHF FSZ SSZ fr live0 Wc} G.
Arguments cls_rframe {RT lo P usp sp0 hasf k FB SHF FSZ SSZ fr live0 Wc} G.
Arguments cls_frame {RT lo P usp sp0 hasf k FB SHF FSZ SSZ fr live0 Wc} G.
Arguments cls_shadow {RT lo P usp sp0 hasf k FB SHF FSZ SSZ fr live0 Wc} G.
Arguments cls_caller {RT lo P usp sp0 hasf k FB SHF FSZ SSZ fr live0 Wc} G.
Arguments pres_step {RT lo P usp sp0 hasf k FB SHF FSZ SSZ fr live0 Wc} G {mi}.
Arguments pres_step_ours {RT lo P usp sp0 hasf k FB SHF FSZ SSZ fr live0 Wc} G {mi}.
Arguments pres_step_nil {RT lo P usp sp0 hasf k FB SHF FSZ SSZ fr live0 Wc} G {mi}.
Arguments pres_step_free {RT lo P usp sp0 hasf k FB SHF FSZ SSZ fr live0 Wc} G {mi}.
Arguments after_l1 {RT} AF {lo P usp sp0 hasf k FB SHF FSZ SSZ fr live0 Wc} G {mi}.
Arguments after_l1_leaf {RT} AF {lo P usp sp0 hasf k FB SHF FSZ SSZ fr live0 Wc} G {mi}.
Arguments after_call {RT lo P usp sp0 hasf k FB SHF FSZ SSZ fr live0 Wc} G {mi}.
Arguments cdst_frame {RT lo P usp sp0 hasf k FB SHF FSZ SSZ fr live0 Wc} G.
Arguments cdst_stack {RT} AF {lo P usp sp0 hasf k FB SHF FSZ SSZ fr live0 Wc} G.
Arguments cdst_live {RT} AF {lo P usp sp0 hasf k FB SHF FSZ SSZ fr live0 Wc} G.
Arguments csrc_frame {RT lo P usp sp0 hasf k FB SHF FSZ SSZ fr live0 Wc} G.
Arguments csrc_stack {RT} AF {lo P usp sp0 hasf k FB SHF FSZ SSZ fr live0 Wc} G.
Arguments csrc_live {RT} AF {lo P usp sp0 hasf k FB SHF FSZ SSZ fr live0 Wc} G.
Arguments call_ok_P {RT lo P usp sp0 hasf k FB SHF FSZ SSZ fr live0 Wc} G.
Arguments ss_call {RT lo P usp sp0 hasf k FB SHF FSZ SSZ fr live0 Wc} G.
Arguments memset_call {RT lo P usp sp0 hasf k FB SHF FSZ SSZ fr live0 Wc} G.
Arguments memcpy_call {RT lo P usp sp0 hasf k FB SHF FSZ SSZ fr live0 Wc} G.
Arguments sfree_call {RT lo P usp sp0 hasf k FB SHF FSZ SSZ fr live0 Wc} G {mi}.
Arguments release_inline {RT} AF {lo P usp sp0 hasf k FB SHF FSZ SSZ fr live0 Wc} G {mi}.
Arguments release_inline2 {RT} AF {lo P usp sp0 hasf k FB SHF FSZ SSZ fr live0 Wc} G {mi}.
Arguments malloc_call {RT} AF {lo P usp sp0 hasf k FB SHF FSZ SSZ fr live0 Wc} G {mi}.
Arguments free_call {RT lo P usp sp0 hasf k FB SHF FSZ SSZ fr live0 Wc} G {mi}.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma act_setup : forall RT (AF : art_facts RT) (Σ Σ1 : rts RT) (m m2 : mem) k f SHF FSZ SSZ lo P usp Wc,
  fs_size k = FSZ -> FSZ = 8 * SSZ -> SSZ < 1048576 -> SHF = f / 8 + 2147450880 ->
  ART RT Σ m -> ART RT Σ1 m2 -> rt_frames RT Σ1 = (f, k) :: rt_frames RT Σ -> rt_live RT Σ1 = rt_live RT Σ -> rt_sp0 RT Σ1 = rt_sp0 RT Σ ->
  rt_sp0 RT Σ - STACK_WIN <= lo -> lo + RT_STACK <= P -> P <= usp -> usp + 16 <= USTACK_TOP -> P mod 16 = 0 ->
  (forall x, ~ outside Wc x -> aclient (rt_live RT Σ) (rt_frames RT Σ) usp x) ->
  act_geom RT lo P usp (rt_sp0 RT Σ) true k f SHF FSZ SSZ (rt_frames RT Σ) (rt_live RT Σ) Wc
  /\ sig_ok RT (rt_sp0 RT Σ) true k f (rt_frames RT Σ) (rt_live RT Σ) Σ1
  /\ f mod 64 = 0 /\ SEGTOP_A <= f /\ (f + FSZ <= 0x7fff7000 \/ 0x10007fff8000 <= f) /\ 2147450880 <= SHF /\ SHF + SSZ <= 17594333495296
  /\ (f + FSZ <= SHF \/ SHF + SSZ <= f)
  /\ (forall p n, In (p, n) (rt_live RT Σ) ->
        (f + FSZ <= p \/ p + n <= f) /\ (p + n <= SHF \/ SHF + SSZ <= p) /\ 0 < p /\ p + n <= rt_sp0 RT Σ - STACK_WIN
        /\ (p + n <= 0x7fff7000 \/ 0x10007fff8000 <= p) /\ (p + n <= 0x10000 \/ SEGTOP_A <= p)).
Proof.
  intros RT AF Σ Σ1 m m2 k f SHF FSZ SSZ lo P usp Wc FSZE SSZE SSB SHE ART0 ART2 FRS1 LV1 SP1 LOW LOR PUS SPT SPA WCL.
  assert (INk : In (f, k) (rt_frames RT Σ1)) by (rewrite FRS1; left; reflexivity).
  pose proof (af_frames_range RT AF Σ1 m2 f k ART2 INk) as (FR0 & FR1 & FR2 & FR3). rewrite FSZE, SP1 in FR1. rewrite FSZE in FR2.
  pose proof (af_frames_align RT AF Σ1 m2 f k ART2 INk) as (F64 & FSEG).
  pose proof (af_frames_hi RT AF Σ1 m2 f k ART2 INk) as FHI. rewrite FSZE in FHI.
  pose proof (af_fshadow_apart RT AF Σ1 m2 f k ART2 INk) as (FSL & FSF).
  pose proof (af_sp0_range RT AF Σ m ART0) as SP0R. pose proof (af_sp0_win RT AF Σ m ART0) as SP0W.
  assert (F8 : f mod 8 = 0) by (clear - F64; Z.div_mod_to_equations; lia).
  assert (SZ0 : 0 <= SSZ). { assert (0 <= fs_size k) by (unfold fs_size; apply Z.shiftl_nonneg; lia). lia. }
  assert (SHFB' : shad f = SHF) by (rewrite SHE; reflexivity).
  assert (SHFE' : shad (f + FSZ) = SHF + SSZ) by (rewrite SHE, SSZE; unfold shad, SHB; clear - F8; Z.div_mod_to_equations; lia).
  assert (SHR : 2147450880 <= SHF /\ SHF + SSZ <= 17594333495296).
  { rewrite <- SHFE'. rewrite SHE. unfold shad, SHB. unfold STACK_WIN, USTACK_TOP in *. clear - FR0 FR1 SP0R SZ0 SSZE. Z.div_mod_to_equations. lia. }
  assert (AXf : sanchor f SHF) by (split; [exact F8| exact SHE]).
  split; [| split; [| split; [exact F64| split; [exact FSEG| split; [exact FHI| split; [exact (proj1 SHR)| split; [exact (proj2 SHR)| split]]]]]]].
  - constructor; try assumption.
    + split; [exact FR0| exact FR1].
    + unfold STACK_WIN in *. lia.
    + intros x Hx.
      destruct (newframe_apart RT AF Σ Σ1 m2 f k usp x ART2 FRS1 LV1 SP1 ltac:(unfold RT_STACK in *; lia) Hx) as (N1 & N2).
      rewrite FSZE in N1, N2. rewrite SHFB', SHFE' in N2.
      destruct (aclient_split RT AF Σ m usp x ART0 Hx) as [E|E]; intros [C|[C|C]]; try tauto; unfold RT_STACK in *; lia.
  - unfold sig_ok. split; [exact FRS1|]. split; [exact SP1|]. intros e He. rewrite LV1. exact He.
  - pose proof (FSF f k INk) as GS. rewrite FSZE, SHFB', SHFE' in GS. exact GS.
  - intros p n Hin. assert (Hin1 : In (p, n) (rt_live RT Σ1)) by (rewrite LV1; exact Hin).
    pose proof (FR3 p n Hin1) as A1. rewrite FSZE in A1. pose proof (FSL p n Hin1) as A2. rewrite FSZE, SHFB', SHFE' in A2.
    pose proof (af_live_range RT AF Σ m p n ART0 Hin) as (R0 & R1 & R2).
    pose proof (af_live_offshadow RT AF Σ m p n ART0 Hin) as R3.
    split; [exact A1|]. split; [exact A2|]. split; [exact R0|]. split; [exact R1|]. split; [exact R3| exact R2].
Qed.

(* [comment removed for export] *)
Lemma pres_final : forall RT (AF : art_facts RT) Σ lo P usp Wc (m m1 m2 m' : mem),
  ART RT Σ m -> rt_sp0 RT Σ - STACK_WIN <= lo -> lo <= P -> P <= usp ->
  munch [(P, usp)] m m1 -> rt_pres (rt_live RT Σ) (rt_frames RT Σ) P m1 m2 ->
  PRESI usp (rt_frames RT Σ) (rt_live RT Σ) Wc m2 m' ->
  rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) usp Wc m m'.
Proof.
  intros RT AF Σ lo P usp Wc m m1 m2 m' ART0 LOW LOP PUS MU1 PRES2 PR a Ha Ho.
  rewrite (PR a (conj Ha Ho)).
  rewrite (PRES2 a (aclient_mono _ _ usp _ _ P _ Ha (fun e H => H) (fun e H => H) PUS)).
  apply MU1. cbn [outside]. split; [| exact I].
  destruct (aclient_split RT AF Σ m usp (bv_unsigned a) ART0 Ha) as [E|E]; lia.
Qed.

(* [comment removed for export] *)
Lemma act_setup_nf : forall RT (AF : art_facts RT) (Σ : rts RT) (m : mem) lo P usp Wc,
  ART RT Σ m -> rt_sp0 RT Σ - STACK_WIN <= lo -> lo + RT_STACK <= P -> P <= usp -> usp + 16 <= USTACK_TOP -> P mod 16 = 0 ->
  (forall x, ~ outside Wc x -> aclient (rt_live RT Σ) (rt_frames RT Σ) usp x) ->
  act_geom RT lo P usp (rt_sp0 RT Σ) false 0 8 2147450881 0 0 (rt_frames RT Σ) (rt_live RT Σ) Wc
  /\ sig_ok RT (rt_sp0 RT Σ) false 0 8 (rt_frames RT Σ) (rt_live RT Σ) Σ.
Proof.
  intros RT AF Σ m lo P usp Wc ART0 LOW LOR PUS SPT SPA WCL.
  pose proof (af_sp0_range RT AF Σ m ART0) as SP0R. pose proof (af_sp0_win RT AF Σ m ART0) as SP0W.
  split.
  - constructor; try assumption; try reflexivity; try lia.
    + split; reflexivity.
    + unfold SEGTOP_A, STACK_WIN in *. lia.
    + unfold STACK_WIN in *. lia.
    + intros x Hx. destruct (aclient_split RT AF Σ m usp x ART0 Hx) as [E|E]; intros [C|[C|C]]; unfold RT_STACK in *; lia.
  - unfold sig_ok. split; [reflexivity|]. split; [reflexivity|]. auto.
Qed.
(* [comment removed for export] *)
Lemma pres_final_nf : forall RT (AF : art_facts RT) Σ lo P usp Wc (m m1 m' : mem),
  ART RT Σ m -> rt_sp0 RT Σ - STACK_WIN <= lo -> lo <= P -> P <= usp ->
  munch [(P, usp)] m m1 -> PRESI usp (rt_frames RT Σ) (rt_live RT Σ) Wc m1 m' ->
  rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) usp Wc m m'.
Proof.
  intros RT AF Σ lo P usp Wc m m1 m' ART0 LOW LOP PUS MU1 PR a Ha Ho.
  rewrite (PR a (conj Ha Ho)). apply MU1. cbn [outside]. split; [| exact I].
  destruct (aclient_split RT AF Σ m usp (bv_unsigned a) ART0 Ha) as [E|E]; lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Inductive cclass : Type := CStack | CFrame | CShadow | CLive (p l : Z) | CStatic | CCaller.
Definition ckey (b : Z) (c : cclass) : Prop := True.
Lemma ck_intro : forall b c, ckey b c. Proof. intros. exact I. Qed.

Ltac x_base e := lazymatch e with Z.add ?x _ => x_base x | Z.sub ?x _ => x_base x | _ => e end.
(* [comment removed for export] *)
Ltac x_head t := lazymatch t with ?f _ => x_head f | _ => t end.
(* [comment removed for export] *)
Ltac x_unfold_cells :=
  repeat match goal with
         | |- context [cells_size ?l] => lazymatch l with cons _ _ => fail | nil => fail | _ => let h := x_head l in unfold h end
         end.
Ltac x_sizes :=
  x_unfold_cells;
  cbn [disjoint_from cells_size csize Nat.add];
  rewrite ?u32s_length, ?length_firstn, ?length_skipn, ?ovw_length_nat, ?ovb_length_nat, ?zw32_length_nat, ?zb8_length_nat, ?repeat_length, ?length_app.
Ltac x_disj := x_sizes; CmpSepV.slia_v.
Ltac x_in SOK :=
  first [ eassumption
        | lazymatch type of SOK with sig_ok _ _ _ _ _ _ _ _ => apply (proj2 (proj2 SOK)); eassumption end ].
Ltac x_cls_class G SOK c :=
  lazymatch c with
  | CStack => first [ apply (cls_rframe G); lia | apply cls_stack; [lia| unfold USTACK_TOP in *; lia] ]
  | CFrame => apply (cls_frame G _ _ _ SOK); lia
  | CShadow => apply (cls_shadow G _ _ _ SOK); lia
  | CLive ?p ?l => apply (cls_live _ _ _ p l); [x_in SOK| lia| lia]
  | CCaller => apply (cls_caller G _ _ _ SOK); eassumption
  | CStatic => apply cls_static; eassumption
  end.
Ltac x_cls G SOK :=
  x_sizes;
  lazymatch goal with
  | |- cls _ _ _ ?a _ =>
      let b := x_base a in
      first [ lazymatch goal with K : ckey b ?c |- _ => x_cls_class G SOK c end
            | idtac "note (xfer): no ckey for base" b "- trying every class";
              first [ x_cls_class G SOK CFrame | x_cls_class G SOK CStack | x_cls_class G SOK CShadow
                    | match goal with H : In (?p, ?l) _ |- _ => x_cls_class G SOK (CLive p l) end ] ]
  end.

(* [comment removed for export] *)
Ltac xfer_rt_chunk G SOK STEP m m' :=
  match goal with
  | H : rw_cells a0segs m ?A ?cs |- _ => first [ apply (x_rw_cells _ _ _ _ m m' STEP A cs) in H; [| x_cls G SOK| x_disj] | fail 3 "xfer_rt: cannot transfer" H ]
  | H : ro_cells a0segs m ?A ?cs |- _ => first [ apply (x_ro_cells _ _ _ _ m m' STEP A cs) in H; [| x_cls G SOK| x_disj] | fail 3 "xfer_rt: cannot transfer" H ]
  | H : u8arr a0segs m ?A ?bs |- _ => first [ apply (x_u8arr _ _ _ _ m m' STEP A bs) in H; [| x_cls G SOK| x_disj] | fail 3 "xfer_rt: cannot transfer" H ]
  | H : u32arr a0segs m ?A ?ws |- _ => first [ apply (x_u32arr _ _ _ _ m m' STEP A ws) in H; [| x_cls G SOK| x_disj] | fail 3 "xfer_rt: cannot transfer" H ]
  | H : bytes_at a0segs m ?A ?bs |- _ => first [ apply (x_bytes_at _ _ _ _ m m' STEP A bs) in H; [| x_cls G SOK| x_disj] | fail 3 "xfer_rt: cannot transfer" H ]
  | H : stk a0segs m ?a ?b |- _ => first [ apply (x_stk _ _ _ _ m m' STEP a b) in H; [| x_cls G SOK| x_disj] | fail 3 "xfer_rt: cannot transfer" H ]
  end.
(* [comment removed for export] *)
Ltac xfer_wr_mono m m' WM :=
  match goal with
  | H : NMem.wr_at a0segs m ?a ?n |- _ => apply (wr_at_transport a0segs m m' a n) in H; [| exact WM]
  | H : wr_at asegs m ?a ?n |- _ => apply (wr_at_transport a0segs m m' a n) in H; [| exact WM]
  end.
(* [comment removed for export] *)
Ltac xfer_wr_agree G SOK STEP m m' :=
  match goal with
  | H : NMem.wr_at a0segs m ?a ?n |- _ => first [ apply (x_wr_at _ _ _ _ m m' STEP a n) in H; [| x_cls G SOK| x_disj] | fail 3 "xfer_rtf: cannot transfer" H ]
  | H : wr_at asegs m ?a ?n |- _ => first [ apply (x_wr_at _ _ _ _ m m' STEP a n) in H; [| x_cls G SOK| x_disj] | fail 3 "xfer_rtf: cannot transfer" H ]
  end.
(* [comment removed for export] *)
Ltac xfer_check m :=
  lazymatch goal with
  | H : rw_cells a0segs m _ _ |- _ => fail "xfer: stale chunk" H
  | H : ro_cells a0segs m _ _ |- _ => fail "xfer: stale chunk" H
  | H : u8arr a0segs m _ _ |- _ => fail "xfer: stale chunk" H
  | H : u32arr a0segs m _ _ |- _ => fail "xfer: stale chunk" H
  | H : bytes_at a0segs m _ _ |- _ => fail "xfer: stale chunk" H
  | H : stk a0segs m _ _ |- _ => fail "xfer: stale chunk" H
  | H : NMem.wr_at a0segs m _ _ |- _ => fail "xfer: stale chunk" H
  | H : wr_at asegs m _ _ |- _ => fail "xfer: stale chunk" H
  | _ => idtac
  end.
Ltac xfer_rt G SOK STEP WM m m' := repeat xfer_rt_chunk G SOK STEP m m'; repeat xfer_wr_mono m m' WM; xfer_check m.
Ltac xfer_rtf G SOK STEP m m' := repeat xfer_rt_chunk G SOK STEP m m'; repeat xfer_wr_agree G SOK STEP m m'; xfer_check m.

(* [comment removed for export] *)
Ltac xfer_l1_one m m' MU WM :=
  let W := lazymatch type of MU with munch ?W _ _ => W end in
  match goal with
  | H : rw_cells a0segs m ?A ?cs |- _ => first [ apply (rw_cells_transport a0segs W m m' A cs) in H; [| exact MU| exact WM| x_disj] | fail 3 "xfer_l1: cannot transfer" H ]
  | H : ro_cells a0segs m ?A ?cs |- _ => first [ apply (ro_cells_transport a0segs W m m' A cs) in H; [| exact MU| x_disj] | fail 3 "xfer_l1: cannot transfer" H ]
  | H : u8arr a0segs m ?A ?bs |- _ => first [ apply (u8arr_transport a0segs W m m' A bs) in H; [| exact MU| exact WM| x_disj] | fail 3 "xfer_l1: cannot transfer" H ]
  | H : u32arr a0segs m ?A ?ws |- _ => first [ apply (u32arr_transport a0segs W m m' A ws) in H; [| exact MU| exact WM| x_disj] | fail 3 "xfer_l1: cannot transfer" H ]
  | H : bytes_at a0segs m ?A ?bs |- _ => first [ apply (bytes_at_transport a0segs W m m' A bs) in H; [| exact MU| x_disj] | fail 3 "xfer_l1: cannot transfer" H ]
  | H : stk a0segs m ?a ?b |- _ => first [ apply (stk_transport_disjoint a0segs W m m' a b) in H; [| exact MU| exact WM| x_disj] | fail 3 "xfer_l1: cannot transfer" H ]
  | H : NMem.wr_at a0segs m ?a ?n |- _ => apply (wr_at_transport a0segs m m' a n) in H; [| exact WM]
  | H : wr_at asegs m ?a ?n |- _ => apply (wr_at_transport a0segs m m' a n) in H; [| exact WM]
  end.
Ltac xfer_l1 m m' MU WM := repeat xfer_l1_one m m' MU WM; xfer_check m.

(* [comment removed for export] *)
Ltac xfer_fl_one G SOK FLD m m' MU WM :=
  let W := lazymatch type of MU with munch ?W _ _ => W end in
  match goal with
  | H : rw_cells a0segs m ?A ?cs |- _ => first [ apply (rw_cells_transport a0segs W m m' A cs) in H; [| exact MU| exact WM| cbn [disjoint_from]; split; [apply FLD; x_cls G SOK| exact I]] | fail 3 "xfer_fl: cannot transfer" H ]
  | H : ro_cells a0segs m ?A ?cs |- _ => first [ apply (ro_cells_transport a0segs W m m' A cs) in H; [| exact MU| cbn [disjoint_from]; split; [apply FLD; x_cls G SOK| exact I]] | fail 3 "xfer_fl: cannot transfer" H ]
  | H : u8arr a0segs m ?A ?bs |- _ => first [ apply (u8arr_transport a0segs W m m' A bs) in H; [| exact MU| exact WM| cbn [disjoint_from]; split; [apply FLD; x_cls G SOK| exact I]] | fail 3 "xfer_fl: cannot transfer" H ]
  | H : u32arr a0segs m ?A ?ws |- _ => first [ apply (u32arr_transport a0segs W m m' A ws) in H; [| exact MU| exact WM| cbn [disjoint_from]; split; [apply FLD; x_cls G SOK| exact I]] | fail 3 "xfer_fl: cannot transfer" H ]
  | H : bytes_at a0segs m ?A ?bs |- _ => first [ apply (bytes_at_transport a0segs W m m' A bs) in H; [| exact MU| cbn [disjoint_from]; split; [apply FLD; x_cls G SOK| exact I]] | fail 3 "xfer_fl: cannot transfer" H ]
  | H : stk a0segs m ?a ?b |- _ => first [ apply (stk_transport_disjoint a0segs W m m' a b) in H; [| exact MU| exact WM| cbn [disjoint_from]; split; [apply FLD; x_cls G SOK| exact I]] | fail 3 "xfer_fl: cannot transfer" H ]
  | H : NMem.wr_at a0segs m ?a ?n |- _ => apply (wr_at_transport a0segs m m' a n) in H; [| exact WM]
  | H : wr_at asegs m ?a ?n |- _ => apply (wr_at_transport a0segs m m' a n) in H; [| exact WM]
  end.
Ltac xfer_fl G SOK FLD m m' MU WM := repeat xfer_fl_one G SOK FLD m m' MU WM; xfer_check m.

