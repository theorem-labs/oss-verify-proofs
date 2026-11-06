(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.K5.AS Require Import ShapeAlg AsanAcct.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.K5.Lib Require Import Tac.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.K5.A9 Require Import ImageA.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.K5.Lib Require Import RzCPS NodesA SysStep Arr FP.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.K5.A9 Require Import Layout.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.K5.AG Require Import Shadow.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.K5.A9 Require Import RT_iface RT_traces RT_gaps_iface LeptTac D_kit D_iface D_defs Lept_kit Lept_iface Lept_env LeptC_kit Lept_objkit LeptL_kit Lept_deserkit Ed_fp Ed_iface Numa_kit.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Lemma delta_rebox : nan_box (sgnj_val F_SGNJ (unbox_s DELTA_W) (unbox_s DELTA_W)) = DELTA_W.
Proof. vm_compute. reflexivity. Qed.
Lemma delta_not_neg : flt_s DELTA_W S_ZERO = false.
Proof. vm_compute. reflexivity. Qed.

(* [comment removed for export] *)
Lemma ms_fcsr_MS : forall R F pc fc rv (m ro : mem), ms_fcsr (MS R F pc fc rv m ro) = fc.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Definition CAPS : list Z := [50; 100; 200; 400; 800; 1600; 3200; 6400; 12800; 25600].
Lemma caps_facts : forall c, In c CAPS -> 50 <= c <= 25600 /\ (c <= 12800 -> In (2 * c) CAPS) /\ (c <= 6400 -> mcost (8 * c) = 0).
Proof.
  intros c H. unfold CAPS in *. cbn [In] in H. unfold mcost.
  repeat (destruct H as [E|H]; [subst c; repeat split; intros; first [lia | vm_compute; lia]|]). destruct H.
Qed.
Lemma caps_12800 : forall c, In c CAPS -> 12800 < c -> c = 25600.
Proof. intros c H Hc. unfold CAPS in H. cbn [In] in H. lia. Qed.
Lemma EGC_val : EXTREMA_GROWTH_COST = 221184.
Proof. vm_compute. reflexivity. Qed.
(* [comment removed for export] *)
Definition ext_spent (c : Z) : Z := if c <=? 12800 then 0 else EXTREMA_GROWTH_COST.
Lemma ext_spent_grow : forall c, In c CAPS -> c <= 12800 -> ext_spent c + mcost (8 * c) = ext_spent (2 * c).
Proof.
  intros c H Hc. unfold CAPS in H. cbn [In] in H. unfold ext_spent, EXTREMA_GROWTH_COST, mcost.
  repeat (destruct H as [E|H]; [subst c; first [lia | vm_compute; lia]|]). destruct H.
Qed.
Lemma ext_spent_le : forall c, 0 <= ext_spent c <= EXTREMA_GROWTH_COST.
Proof. intros c. unfold ext_spent. pose proof EGC_val. destruct (c <=? 12800); lia. Qed.
Lemma ext_spent_50 : ext_spent 50 = 0.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Lemma lrm_notin : forall p (l : list (Z * Z)), (forall e, In e l -> fst e <> p) -> live_remove p l = l.
Proof.
  intros p l H. induction l as [|e l IH]; [reflexivity|]. rewrite lrm_cons.
  destruct (Z.eqb_spec (fst e) p) as [E|E]; [exfalso; exact (H e (or_introl eq_refl) E)|].
  rewrite IH; [reflexivity|]. intros e' He'. apply H. right. exact He'.
Qed.

(* [comment removed for export] *)
Lemma numa_arr_parts : forall (m : mem) arr cap vals junk, rw_cells asegs m arr (numa_arr_cells cap vals junk) -> Z.of_nat (length vals) <= cap ->
  cells_wf (numa_arr_cells cap vals junk) /\ bytes_at asegs m arr (u32s vals ++ junk) /\ wr_at asegs m arr (4 * cap)
  /\ Z.of_nat (length (u32s vals ++ junk)) = 4 * cap.
Proof.
  intros m arr cap vals junk [[W B] A] L. pose proof W as W0. unfold numa_arr_cells in W, B, A |- *.
  apply cells_wf_app in W. destruct W as [_ [LJ _]]. cbn [cell_wf] in LJ.
  rewrite cells_bytes_app, cells_bytes_mapC4 in B. cbn [cells_bytes cbytes] in B. rewrite app_nil_r in B.
  rewrite cells_size_app, cells_size_mapC4 in A. cbn [cells_size csize] in A.
  split; [exact W0|]. split; [exact B|]. split.
  - replace (4 * cap) with (Z.of_nat (4 * length vals + (Z.to_nat (4 * cap - 4 * Z.of_nat (length vals)) + 0))) by lia. exact A.
  - rewrite length_app, u32s_length, LJ. lia.
Qed.
Lemma numa_arr_rejoin : forall (m : mem) arr cap vals junk, cells_wf (numa_arr_cells cap vals junk) ->
  bytes_at asegs m arr (u32s vals ++ junk) -> wr_at asegs m arr (4 * cap) -> Z.of_nat (length vals) <= cap ->
  rw_cells asegs m arr (numa_arr_cells cap vals junk).
Proof.
  intros m arr cap vals junk W B A L. pose proof W as W0. unfold numa_arr_cells in W0 |- *.
  apply cells_wf_app in W0. destruct W0 as [_ [LJ _]]. cbn [cell_wf] in LJ.
  split; [split; [exact W|]|].
  - rewrite cells_bytes_app, cells_bytes_mapC4. cbn [cells_bytes cbytes]. rewrite app_nil_r. exact B.
  - rewrite cells_size_app, cells_size_mapC4. cbn [cells_size csize].
    replace (Z.of_nat (4 * length vals + (Z.to_nat (4 * cap - 4 * Z.of_nat (length vals)) + 0))) with (4 * cap) by lia. exact A.
Qed.

(* [comment removed for export] *)
Lemma keeps_live_of_munch : forall live W (m m' : mem), munch W m m' ->
  (forall b k a, In (b, k) live -> b <= a < b + k -> outside W a) -> keeps_live live m m'.
Proof. intros live W m m' MU H b k Hin a Ha. apply MU. exact (H b k _ Hin Ha). Qed.
Lemma keeps_live_of_agree : forall live (P : Z -> Prop) (m m' : mem), agree_on P m m' ->
  (forall b k a, In (b, k) live -> b <= a < b + k -> P a) -> keeps_live live m m'.
Proof. intros live P m m' AG H b k Hin a Ha. apply AG. exact (H b k _ Hin Ha). Qed.
(* [comment removed for export] *)
Lemma acc_agree : forall (m m' : mem) (P : Z -> Prop) a n, acc asegs m a n -> agree_on P m m' -> 0 <= a ->
  (forall x, shad a <= x <= shad (a + n) -> P x) -> acc asegs m' a n.
Proof.
  intros m m' P a n H AG Ha HP i Hi. destruct (H i Hi) as (b & Hb & OK). exists b. split; [| exact OK].
  apply (bytes_at_agree asegs m m' _ _ Hb). eapply agree_sub; [exact AG|]. cbv beta. intros x Hx. apply HP.
  cbn [length] in Hx. unfold shad in *. Z.div_mod_to_equations. lia.
Qed.

(* [comment removed for export] *)
Lemma le8_of_bytes : forall bs : list byte, length bs = 8%nat -> le8 (le_bytes_to_word bs) = bs.
Proof.
  intros bs HL. unfold le8, word_to_le_bytes, le_bytes_to_word.
  pose proof (bytes_le_to_Z_range' bs) as HR. rewrite HL in HR. change (2 ^ (8 * Z.of_nat 8))%Z with (2^64)%Z in HR.
  rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64)%Z with (2^64)%Z.
  rewrite Z.mod_small by lia. rewrite <- HL. exact (le_bytes_roundtrip bs).
Qed.
Lemma cb8_c8 : forall (m : mem) A bs, rw_cells asegs m A [CB 8 bs] -> exists w : word, rw_cells asegs m A [C8 w].
Proof.
  intros m A bs H. exists (le_bytes_to_word bs).
  pose proof H as [[[L _] _] _]. cbn in L.
  apply (rw_cells_recell m A _ _ H); [cbn; tauto| | reflexivity].
  cbn [cells_bytes cbytes app]. rewrite le8_of_bytes by exact L. reflexivity.
Qed.

Section ExtDefs.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.

(* [comment removed for export] *)
Lemma live_apart_seg : forall Σ (m0 : mem) fr k p n a,
  ART RT Σ m0 -> In (fr, k) (rt_frames RT Σ) -> In (p, n) (rt_live RT Σ) -> p <= a < p + n ->
  a < rt_sp0 RT Σ - STACK_WIN /\ (a < fr \/ fr + fs_size k <= a) /\ (a < shad fr \/ shad (fr + fs_size k) <= a).
Proof using AF.
  intros Σ m0 fr k p n a HA HF HL Ha.
  pose proof (af_live_range RT AF Σ m0 p n HA HL) as (_ & R1 & _).
  pose proof (af_frames_range RT AF Σ m0 fr k HA HF) as (_ & _ & _ & R2). specialize (R2 p n HL).
  pose proof (af_fshadow_apart RT AF Σ m0 fr k HA HF) as (R3 & _). specialize (R3 p n HL).
  repeat split; lia.
Qed.
Lemma keeps_live_sub : forall (l l' : list (Z * Z)) (m m' : mem), (forall e, In e l -> In e l') -> keeps_live l' m m' -> keeps_live l m m'.
Proof. intros l l' m m' S K b k Hin a Ha. exact (K b k (S _ Hin) a Ha). Qed.

(* [comment removed for export] *)
Lemma live_head_notin : forall Σ (m : mem) p n l, ART RT Σ m -> rt_live RT Σ = (p, n) :: l -> 0 < n ->
  (forall e, In e l -> 0 < snd e) -> forall e, In e l -> fst e <> p.
Proof using AF.
  intros Σ m p n l HA HL Hn Hl e He E. destruct e as [q k]. cbn [fst] in E. subst q.
  pose proof (af_live_disj RT AF Σ m p n p k [] l HA HL He) as D. pose proof (Hl _ He) as K. cbn [snd] in K. lia.
Qed.

(* [comment removed for export] *)
Definition ext_post (Σ : rts RT) PMc (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (m : mem) (lo : Z) (vals : list word) : config -> Prop :=
  fun c => exists (Σ' : rts RT) (nad capd arrd : Z) (vd : list word),
       ASTA RT Σ' PMc (fun ms => exists m', ret_st ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 nad) m' ms
          /\ lpost_f RT Σ Σ' m m' sp lo /\ keepsL RT (rt_live RT Σ) Σ sp [] m m'
          /\ numa_obj (rt_live RT Σ') m' nad capd arrd vd) c
       /\ Z.of_nat (length vd) + 1 <= Z.max 1 (Z.of_nat (length vals))
       /\ rt_live RT Σ' = numa_live nad capd arrd (rt_live RT Σ)
       /\ rt_frames RT Σ' = rt_frames RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ
       /\ rt_credit RT Σ - EXTREMA_COST <= rt_credit RT Σ'.

(* [comment removed for export] *)
Definition ext_shadow : list cell :=
  [C1 (Z_to_bv 8 (-15)); C1 (Z_to_bv 8 (-15)); C1 (Z_to_bv 8 (-15)); C1 (Z_to_bv 8 (-15));
   C1 (Z_to_bv 8 4); C1 (Z_to_bv 8 (-14)); C1 (Z_to_bv 8 4); C1 (Z_to_bv 8 (-13))].

(* [comment removed for export] *)
Definition ext_rest_stmt : Prop :=
  forall (Σ Σ2 : rts RT) PMc (m mm : mem)
         (rae s0e s1e s2e s3e s4e s5e s6e s7e s8e s9 s10e s11e fs0e fs1e fs2e gp : word)
         (rax t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (F1 : bvmap 5 word) (fc1 : bv 32)
         (sp : word) (usp0 lo fr nas cap arr nad arrd : Z) (vals : list word) (navw sv vl : word) (hd0 hd1 hd2 : word),
  fdfs_only PMc -> mat_stable PMc ->
  rt_live RT Σ2 = numa_live nad 50 arrd (rt_live RT Σ) -> rt_frames RT Σ2 = (fr, 0%nat) :: rt_frames RT Σ -> rt_sp0 RT Σ2 = rt_sp0 RT Σ ->
  rt_credit RT Σ - 1 <= rt_credit RT Σ2 ->
  ART RT Σ2 mm -> mem_inv asegs mm -> LIBH mm -> io_ssp mm -> stk asegs mm lo usp0 ->
  numa_obj (rt_live RT Σ) mm nas cap arr vals -> numa_obj (rt_live RT Σ2) mm nad 50 arrd [] -> 1 <= Z.of_nat (length vals) <= 20000 ->
  rw_cells asegs mm ((bv_unsigned sp) + -128) [C8 fs2e; C8 fs1e; C8 fs0e; C8 s11e; C8 s10e; C8 s9; C8 s8e; C8 s7e; C8 s6e; C8 s5e; C8 s4e;
                                            C8 s3e; C8 s2e; C8 s1e; C8 s0e; C8 rae] ->
  rw_cells asegs mm (usp0 + 24) [C8 navw] -> wr_at asegs mm usp0 (bv_unsigned sp - usp0) ->
  rw_cells asegs mm fr [C8 hd0; C8 hd1; C8 hd2] -> rw_cells asegs mm (fr + 32) [C4 sv] -> rw_cells asegs mm (fr + 48) [C4 vl] ->
  rw_cells asegs mm (fr / 8 + SHB) ext_shadow ->
  agree_on (fun a => aclient (rt_live RT Σ) (rt_frames RT Σ) (bv_unsigned sp) a /\ outside (@nil (Z * Z)) a) m mm ->
  rt_sp0 RT Σ - STACK_WIN <= lo -> lo + LSTK 6 <= (bv_unsigned sp) -> (bv_unsigned sp) + 16 <= USTACK_TOP -> (bv_unsigned sp) mod 16 = 0 -> (bv_unsigned sp) <= rt_sp0 RT Σ ->
  (bv_unsigned sp) - 208 <= usp0 <= (bv_unsigned sp) - 192 -> usp0 mod 32 = 0 ->
  Z.of_nat (length (rt_frames RT Σ)) + 2 <= Z.of_nat FRAMES_MAX -> Z.of_nat (length (rt_live RT Σ)) + 3 <= LIVE_MAX -> EXTREMA_COST <= rt_credit RT Σ ->
  (forall p n, In (p, n) (rt_live RT Σ) -> 0 < n) ->
  cps asegs (ASTA RT Σ2 PMc (eq (MS (mkR rax (Z_to_bv 64 usp0) gp (Z_to_bv 64 TP_A) t0 t1 t2 (Z_to_bv 64 (bv_unsigned sp)) (Z_to_bv 64 usp0)
                                        a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 fr) (Z_to_bv 64 nas) (Z_to_bv 64 nad) (Z_to_bv 64 (Z.of_nat (length vals)))
                                        (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 (fr + 32)) s9 (Z_to_bv 64 fr) (Z_to_bv 64 (fr / 8 + SHB)) t3 t4 t5 t6)
                                   F1 (Z_to_bv 64 0xee95c) (frm_clear fc1) None mm (seg_rom asegs))))
    (ext_post Σ PMc rae sp gp (Z_to_bv 64 TP_A) s0e s1e s2e s3e s4e s5e s6e s7e s8e s9 s10e s11e m lo vals).

(* [comment removed for export] *)
Definition ext_case (al : Z) : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         F fc (m : mem) (lo : Z) (nas cap arr : Z) (vals : list word) (ras : list Z),
  fdfs_only PMc -> mat_stable PMc -> tp = Z_to_bv 64 TP_A ->
  a0 = Z_to_bv 64 nas -> freg_is F fa0 DELTA_W -> a1 = Z_to_bv 64 0 ->
  numa_obj (rt_live RT Σ) m nas cap arr vals -> 1 <= Z.of_nat (length vals) <= 20000 ->
  uctx m sp s0 ras -> numaCreate_trace_ok (bv_unsigned ra :: ras) ->
  lenv RT Σ m sp lo (LSTK 6) -> lres RT Σ 2 3 EXTREMA_COST -> bv_unsigned sp mod 32 = al ->
  cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_numaFindExtrema m)))
    (fun c => exists (Σ' : rts RT) (nad capd arrd : Z) (vd : list word),
       ASTA RT Σ' PMc (fun ms => exists m', ret_st ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 nad) m' ms
          /\ lpost_f RT Σ Σ' m m' sp lo /\ keepsL RT (rt_live RT Σ) Σ sp [] m m'
          /\ numa_obj (rt_live RT Σ') m' nad capd arrd vd) c
       /\ Z.of_nat (length vd) + 1 <= Z.max 1 (Z.of_nat (length vals))
       /\ rt_live RT Σ' = numa_live nad capd arrd (rt_live RT Σ)
       /\ rt_frames RT Σ' = rt_frames RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ
       /\ rt_credit RT Σ - EXTREMA_COST <= rt_credit RT Σ').

Lemma ext_cases : ext_case 0 -> ext_case 16 -> numaFindExtrema_cps RT.
Proof.
  intros C0 C16 Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo nas cap arr vals ras
    H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 ENV H12.
  assert (AL : bv_unsigned sp mod 32 = 0 \/ bv_unsigned sp mod 32 = 16).
  { destruct ENV as (_ & _ & _ & _ & _ & _ & _ & _ & SPA & _). Z.div_mod_to_equations. lia. }
  destruct AL as [AL|AL]; [eapply C0| eapply C16]; eassumption.
Qed.
End ExtDefs.
