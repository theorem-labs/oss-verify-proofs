(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.K5.AS Require Import ShapeAlg AsanAcct.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.K5.Lib Require Import Tac.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.K5.A9 Require Import ImageA.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.K5.Lib Require Import RzCPS NodesA SysStep.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.K5.Lib Require Import StoreFast.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.K5.PG Require Import Str_tac Startup_glue.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.K5.Malloc Require Import MallocKit_AB.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.K5.A9 Require Import Layout.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.K5.AG Require Import Shadow.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.K5.A9 Require Import RT_iface RT_traces RT_gaps_iface LeptTac D_kit Lept_kit Lept_iface Lept_env LeptC_kit Lept_leaf Lept_chain D_iface D_defs.
Import ListNotations.
Open Scope Z_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.

Lemma accok_live_mono : forall live live' frames (m : mem) a n, (forall e, In e live -> In e live') ->
  accok live frames m a n -> accok live' frames m a n.
Proof. intros live live' frames m a n S [(p & k & Hin & H)|OF]; [left; exists p, k; split; [exact (S _ Hin)| exact H]| right; exact OF]. Qed.

Lemma live_remove_ne : forall (l : list (Z * Z)) p e, In e (live_remove p l) -> fst e <> p.
Proof.
  intros l p e He. unfold live_remove in He. apply stdpp.base.list_elem_of_In in He.
  apply stdpp.list_basics.list.list_elem_of_filter in He. destruct He as [Hp _]. intros E. rewrite E, Z.eqb_refl in Hp. exact Hp.
Qed.

Lemma live_remove_len : forall (l : list (Z * Z)) p, (length (live_remove p l) <= length l)%nat.
Proof. intros l p. unfold live_remove. apply stdpp.list_basics.list.length_filter. Qed.

Lemma traces_ra_lo : Forall (Forall (fun x => 4096 <= x)) CLIENT_TRACES.
Proof.
  apply Forall_forall. intros t Ht. apply Forall_forall. intros x Hx.
  assert (B : forallb (fun t => forallb (fun x => 4096 <=? x) t) CLIENT_TRACES = true) by (vm_compute; reflexivity).
  rewrite forallb_forall in B. specialize (B t Ht). rewrite forallb_forall in B. specialize (B x Hx). apply Z.leb_le in B. exact B.
Qed.

(* [comment removed for export] *)
Ltac frame_release_g RT AF GP MST Σ0 fr k SZ PF AGF PFS usp lo pcafter ivt pft live0 livesub getacl :=
  cps_stop;
  art_now RT AF ivt;
  lazymatch goal with AGFx : agree_on ?PFx _ ?mm, MUx : munch _ ?mm _ |- _ => is_var PFx; agf_munch AGFx MUx pft end;
  lazymatch goal with A : ART RT ?S ?mm |- cps _ (ASTA RT ?S _ (eq (MS _ _ _ _ _ ?mm _))) _ =>
    let FRSc := fresh "FRSc" in
    assert (FRSc : rt_frames RT S = (fr, k) :: rt_frames RT Σ0)
      by (repeat match goal with H : rt_frames _ _ = _ |- _ => rewrite H end; reflexivity);
    let S2 := fresh "S2" in let fl := fresh "fl" in let FLC := fresh "FLC" in let FLN := fresh "FLN" in let FL0 := fresh "FL0" in
    let FLHI := fresh "FLHI" in let FLP := fresh "FLP" in let REL := fresh "REL" in
    destruct (af_frame_release RT AF S mm fr k _ A FRSc) as (S2 & fl & FLC & FLN & FL0 & FLHI & FLP & REL);
    change (fs_size k) with SZ in FLP;
    let off := eval vm_compute in (SZ - 8)%Z in replace (fr + SZ - 8)%Z with (fr + off)%Z in FLP by lia;
    repeat match goal with H : rt_sp0 RT _ = _ |- _ => rewrite H in FLHI end; unfold STACK_WIN in FLHI;
    (* [comment removed for export] *)
    repeat match goal with
    | IN : In (?b, ?kk) _ |- _ =>
        lazymatch goal with
        | _ : fl < b \/ b + kk <= fl |- _ => fail
        | _ => let FA := fresh "FLA" in
               assert (FA : fl < b \/ b + kk <= fl)
                 by (apply (flag_apart _ _ fl b (b + kk) FLN); let x := fresh "x" in let Hx := fresh "Hx" in intros x Hx;
                     right; right; left; exists b, kk; split; [solve [in_live_tac] | lia])
        end
    end;
    let LHs := fresh "LHs" in let SSPs := fresh "SSPs" in
    lazymatch goal with LHx : LIBH mm |- _ => pose proof LHx as LHs; hide LHs end;
    lazymatch goal with SSPx : io_ssp mm |- _ => pose proof SSPx as SSPs; hide SSPs end;
    walk_to AF MST [(fl, fl + 1)] [pcafter];
    cps_stop;
    lazymatch goal with MUx : munch [(fl, fl + 1)] mm ?m', WMx : wmono asegs mm ?m', FLC' : rw_cells asegs ?m' fl _ |- _ =>
      let ART2 := fresh "ART2" in let FRS2 := fresh "FRS2" in let LV2 := fresh "LV2" in let SP2 := fresh "SP2" in
      let CR2 := fresh "CR2" in let AL2 := fresh "AL2" in let AM2 := fresh "AM2" in let AGS := fresh "AGS" in
      destruct (REL m' MUx WMx FLC') as (ART2 & FRS2 & LV2 & SP2 & CR2 & AL2 & AM2);
      assert (AGS : agree_on client_static mm m')
        by (let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha; apply MUx; cbn [outside]; split; [| exact I];
            let Hin := fresh "Hin" in intros Hin; apply FLN; replace fl with (bv_unsigned a) by lia; right; left; exact Ha);
      unfold hid in LHs, SSPs;
      let LH2 := fresh "LH" in let SSP2 := fresh "SSP" in
      assert (LH2 : LIBH m') by (exact (LIBH_agree RT GP client_static mm m' LHs AGS (fun a Ha => Ha)));
      assert (SSP2 : io_ssp m') by (exact (io_ssp_agree RT GP client_static S2 mm m' SSPs ART2 AGS (fun a Ha => Ha)));
      agf_munch AGF MUx ltac:(fun Hx => cbn [outside]; split; [| exact I]; let Hin := fresh "Hin" in intros Hin;
        lazymatch type of Hx with PF ?z =>
          apply (flag_not_client _ _ live0 (rt_frames RT Σ0) fl lo usp FLN ltac:(lia) ltac:(lia));
          [ livesub | solve [frames_sub_tac] | replace fl with z by lia; getacl Hx ] end);
      apply (cps_ASTA_switch RT _ S2 _ _ _ AL2 AM2);
      clear REL LHs SSPs FLC AGS      (* [comment removed for export] *)
    end
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac lvf_ne He :=
  match goal with
  | H : forall e, In e _ -> fst e <> _ |- _ => exact (H _ He)
  | H : forall e, In e _ -> fst e <> _ /\ fst e <> _ |- _ => first [exact (proj1 (H _ He)) | exact (proj2 (H _ He))]
  end.
(* [comment removed for export] *)
Ltac lvf_keep LVFS He :=
  repeat match goal with H : rt_live _ _ = _ |- _ => rewrite H end;
  repeat (apply live_remove_keep; [| solve [lvf_ne He]]);
  exact (LVFS _ He).
(* [comment removed for export] *)
Ltac live_eq_tac :=
  repeat match goal with H : rt_live _ _ = _ |- _ => rewrite H end;
  repeat match goal with x := _ : Z |- _ => subst x end;
  repeat match goal with L := live_destroy _ _ _ _ |- _ => subst L end;
  unfold live_destroy, rm_opt;
  repeat (match goal with
          | |- context [(?x =? 0)] =>
              first [ replace (x =? 0) with false by (symmetry; apply Z.eqb_neq; lia)
                    | replace (x =? 0) with true by (symmetry; apply Z.eqb_eq; lia) ]
          end; cbv iota);
  reflexivity.


Section DESTROY_DEFS.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.

(* [comment removed for export] *)
Lemma live_chunks_disj : forall Σ (m : mem) p1 n1 p2 n2, ART RT Σ m -> In (p1, n1) (rt_live RT Σ) -> In (p2, n2) (rt_live RT Σ) ->
  p1 <> p2 -> p1 + n1 <= p2 \/ p2 + n2 <= p1.
Proof using AF.
  intros Σ m p1 n1 p2 n2 HA I1 I2 NE. destruct (in_split _ _ I1) as (l1 & l2 & EL).
  assert (IN2 : In (p2, n2) (l1 ++ l2)).
  { rewrite EL in I2. apply in_app_or in I2. apply in_or_app. destruct I2 as [X|[X|X]]; [left; exact X| congruence| right; exact X]. }
  exact (af_live_disj RT AF Σ m p1 n1 p2 n2 l1 l2 HA EL IN2).
Qed.

(* [comment removed for export] *)
Lemma removed_chunk_apart : forall Σ (m : mem) p n live0 usp a,
  ART RT Σ m -> In (p, n) (rt_live RT Σ) -> (forall e, In e live0 -> In e (rt_live RT Σ) /\ fst e <> p) ->
  rt_sp0 RT Σ - STACK_WIN <= usp ->
  aclient live0 (rt_frames RT Σ) usp a -> a < p \/ p + n <= a.
Proof using AF.
  intros Σ m p n live0 usp a HA INL SUB SPL Ha.
  pose proof (af_live_range RT AF Σ m p n HA INL) as (P0 & PHI & PSEG).
  unfold STACK_WIN, USTACK_TOP, SEGTOP_A in *.
  destruct Ha as [H|[H|[H|[H|H]]]].
  - right. lia.
  - pose proof (client_static_below a H) as HB. unfold SEGTOP_A in HB.
    destruct H as ((l & h & Hin & Hx) & _). unfold CLIENT_STATIC in Hin. cbn [In] in Hin.
    assert (X : 0x10000 <= a) by (repeat (destruct Hin as [E|Hin]; [injection E as <- <-; lia|]); destruct Hin).
    lia.
  - destruct H as (p' & n' & Hin & Hp). destruct (SUB _ Hin) as [HinL NE]. cbn [fst] in NE.
    destruct (in_split _ _ INL) as (l1 & l2 & EL).
    assert (IN2 : In (p', n') (l1 ++ l2)).
    { rewrite EL in HinL. apply in_app_or in HinL. apply in_or_app. destruct HinL as [X|[X|X]]; [left; exact X| congruence| right; exact X]. }
    pose proof (af_live_disj RT AF Σ m p n p' n' l1 l2 HA EL IN2) as D. lia.
  - destruct H as (f & k & Hin & Hf).
    pose proof (af_frames_range RT AF Σ m f k HA Hin) as (_ & _ & _ & FLV). specialize (FLV p n INL). lia.
  - destruct H as (f & k & Hin & Hf).
    pose proof (af_fshadow_apart RT AF Σ m f k HA Hin) as (SA1 & _). specialize (SA1 p n INL). lia.
Qed.


(* [comment removed for export] *)
Definition pixDestroy_case (al : Z) (dnz cnz : bool) : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         F fc (m : mem) (lo : Z) (pp pix : Z) (v : pixv) (cv : cmapv) (ras : list Z),
  fdfs_only PMc -> mat_stable PMc -> tp = Z_to_bv 64 TP_A ->
  a0 = Z_to_bv 64 pp -> optrL RT (live_destroy pix v cv (rt_live RT Σ)) Σ m pp 8 -> rw_cells asegs m pp [C8 (Z_to_bv 64 pix)] ->
  pix_obj (rt_live RT Σ) m pix v cv ->
  uctx m sp s0 ras -> Forall (fun f => In (f :: bv_unsigned ra :: ras) CLIENT_TRACES) DESTROY_FREE_RAS ->
  lenv RT Σ m sp lo (LSTK 4) -> lres RT Σ 1 0 1 ->
  bv_unsigned sp mod 32 = al -> (if dnz then p_data v <> 0 else p_data v = 0) -> (if cnz then p_cmap v <> 0 else p_cmap v = 0) ->
  cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_pixDestroy m)))
    (fun c => exists (Σ' : rts RT) (rv : word),
       ASTA RT Σ' PMc (fun ms => exists m', ret_st ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 rv m' ms
          /\ lpost_f RT Σ Σ' m m' sp lo /\ keeps RT Σ Σ' sp [(pp, pp + 8)] m m' /\ rw_cells asegs m' pp [C8 (Z_to_bv 64 0)]) c
       /\ rt_live RT Σ' = live_destroy pix v cv (rt_live RT Σ)
       /\ rt_frames RT Σ' = rt_frames RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ /\ rt_credit RT Σ - 1 <= rt_credit RT Σ').

(* [comment removed for export] *)
Lemma pixDestroy_of_cases :
  (forall dnz cnz, pixDestroy_case 0 dnz cnz) -> (forall dnz cnz, pixDestroy_case 16 dnz cnz) -> pixDestroy_cps RT.
Proof using Type.
  intros H0 H16 Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo pp pix v cv ras
    FDO MST TP A0 OP PPC POBJ UCTX TRS ENV RES.
  assert (SPA : bv_unsigned sp mod 16 = 0) by (unfold lenv in ENV; tauto).
  assert (AL : bv_unsigned sp mod 32 = 0 \/ bv_unsigned sp mod 32 = 16) by (clear - SPA; Z.div_mod_to_equations; lia).
  destruct (Z.eq_dec (p_data v) 0) as [D|D]; destruct (Z.eq_dec (p_cmap v) 0) as [C|C]; destruct AL as [AL|AL].
  - exact (H0 false false Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo pp pix v cv ras FDO MST TP A0 OP PPC POBJ UCTX TRS ENV RES AL D C).
  - exact (H16 false false Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo pp pix v cv ras FDO MST TP A0 OP PPC POBJ UCTX TRS ENV RES AL D C).
  - exact (H0 false true Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo pp pix v cv ras FDO MST TP A0 OP PPC POBJ UCTX TRS ENV RES AL D C).
  - exact (H16 false true Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo pp pix v cv ras FDO MST TP A0 OP PPC POBJ UCTX TRS ENV RES AL D C).
  - exact (H0 true false Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo pp pix v cv ras FDO MST TP A0 OP PPC POBJ UCTX TRS ENV RES AL D C).
  - exact (H16 true false Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo pp pix v cv ras FDO MST TP A0 OP PPC POBJ UCTX TRS ENV RES AL D C).
  - exact (H0 true true Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo pp pix v cv ras FDO MST TP A0 OP PPC POBJ UCTX TRS ENV RES AL D C).
  - exact (H16 true true Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo pp pix v cv ras FDO MST TP A0 OP PPC POBJ UCTX TRS ENV RES AL D C).
Qed.
End DESTROY_DEFS.
