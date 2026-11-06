(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.AS Require Import ShapeAlg AsanAcct.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.Lib Require Import Tac RzCPS NodesA SysStep Arr StoreFast.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.PG Require Import Str_tac Startup_glue.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.AG Require Import Shadow.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.A02 Require Import ImageA Layout RT_iface RT_traces RT_gaps_iface LeptTac D_kit Lept_kit D_iface D_defs
  Lept_iface Lept_env LeptC_kit Lept_leaf LeptL_kit LeptL_gmax_loop RT_fk RT_fk_iface Bi_fktw Bi_fkkit Bi_fkweak LeptF_iface LeptF_weak LeptF_kit.
Import ListNotations.
Open Scope Z_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.

(* [comment removed for export] *)
Ltac frame_release_w RT AF GP MST Σ0 fr k SZ PF AGF PFS usp lo pcafter ivt pft getacl pre :=
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
    pre fl FLN;
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
          apply (flag_not_client _ _ (rt_live RT Σ0) (rt_frames RT Σ0) fl lo usp FLN ltac:(lia) ltac:(lia));
          [ first [ solve [live_sub_tac] | solve [live_add_tac] ] | solve [frames_sub_tac] | replace fl with z by lia; getacl Hx ] end);
      apply (cps_ASTA_switch RT _ S2 _ _ _ AL2 AM2);
      clear REL LHs SSPs FLC FLN AGS
    end
  end.

(* [comment removed for export] *)
Lemma accok_keep_fp : forall live frames (m m' : mem) live' frames' sp W a n, accok live frames m a n ->
  agree_on (fun x => aclient live' frames' sp x /\ outside W x) m m' -> 0 <= n ->
  (forall e, In e frames -> In e frames') -> (forall x, shad a <= x < shad a + (n + 7) / 8 -> outside W x) ->
  accok live frames m' a n.
Proof.
  intros live frames m m' live' frames' sp W a n [H|(f & k & Hin & H1 & H2 & H8 & H0 & HT & Hb)] AG Hn HF HW; [left; exact H| right].
  exists f, k. repeat (split; [first [assumption | lia]|]).
  apply (bytes_at_agree asegs m m' _ _ Hb). eapply agree_sub; [exact AG|]. cbv beta. intros x Hx.
  rewrite (ushadow_length n Hn) in Hx. split; [| apply HW; exact Hx].
  right; right; right; right. exists f, k. split; [exact (HF _ Hin)|]. unfold shad in *. Z.div_mod_to_equations. lia.
Qed.

(* [comment removed for export] *)
Lemma cb4_c4 : forall (m : mem) A bs, rw_cells asegs m A [CB 4 bs] -> exists x : word, rw_cells asegs m A [C4 x].
Proof.
  intros m A bs H. pose proof H as [[W _] _]. cbn in W. destruct W as [L _].
  destruct (u32s_exists 1 bs L) as (ws & E & LW). destruct ws as [|x [|y ws]]; try discriminate. exists x.
  apply (rw_cells_recell m A _ [C4 x] H); [cbn; tauto | cbn [cells_bytes cbytes u32s] in *; rewrite <- E; reflexivity | reflexivity].
Qed.

(* [comment removed for export] *)
Lemma pix_obj_agree : forall (live : list (Z * Z)) (P : Z -> Prop) (m m' : mem) pix v cv,
  pix_obj live m pix v cv -> agree_on P m m' -> (forall q k a, In (q, k) live -> q <= a < q + k -> P a) ->
  rw_cells asegs m' pix (pix_cells v) -> pix_obj live m' pix v cv.
Proof.
  intros live P m m' pix v cv (PXC & PCH & HOK & PDATA & PCMAP) AG PL PXC'.
  split; [exact PXC'|]. split; [exact PCH|]. split; [exact HOK|]. split; [exact PDATA|].
  destruct PCMAP as [Z0|(((pad & CMC) & CCH & ACH & COK & CNE) & NN)]; [left; exact Z0| right].
  split; [| exact NN]. split; [| exact (conj CCH (conj ACH (conj COK CNE)))].
  exists pad. apply (rw_cells_agree_nw asegs m m' _ _ CMC). intros a Ha. apply AG. destruct CCH as (CIN & _).
  cbn [cells_size cmap_cells csize Nat.add] in Ha. apply (PL (p_cmap v) 24 _ CIN). lia.
Qed.

(* [comment removed for export] *)
Ltac local_acc FSH fr idx off FR64 FR1 NAME :=
  let T := fresh "T" in let T2 := fresh "T" in let T3 := fresh "T" in let B := fresh "B" in
  pose proof FSH as T; split_at T idx T2; split_at T2 1%nat T3; clear T T3;
  lazymatch type of T2 with rw_cells _ ?mm _ _ =>
    assert (NAME : acc asegs mm (fr + off) 4)
      by (destruct T2 as [[_ B] _]; apply (acc_ushadow asegs mm (fr + off) 4); [clear - FR64; Z.div_mod_to_equations; lia| lia| lia|];
          let c := eval vm_compute in (2147450880 + Z.of_nat idx) in
          replace (shad (fr + off)) with (fr / 8 + c) by (unfold shad, SHB; clear - FR64; Z.div_mod_to_equations; lia);
          exact B) end; clear T2.

(* [comment removed for export] *)
Definition gmax_case (RT : rt_sig) (al : Z) : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         F fc (m : mem) (lo : Z) (pix pmax : Z) (v : pixv) (cv : cmapv) (x : word),
  fdfs_only PMc -> mat_stable PMc -> tp = Z_to_bv 64 TP_A ->
  a0 = Z_to_bv 64 pix -> a1 = Z_to_bv 64 pmax -> pix_obj (rt_live RT Σ) m pix v cv -> p_data v <> 0 -> p_d v <= 8 -> optrF RT Σ m pmax 4 ->
  rw_cells asegs m pmax [C4 x] ->
  lenv RT Σ m sp lo (LSTK 4) -> lres RT Σ 1 0 2 -> bv_unsigned sp mod 32 = al ->
  cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_pixGetMaxColorIndex m)))
    (fun c => exists (Σ' : rts RT) (rv y : word),
       ASTA RT Σ' PMc (fun ms => exists m', ret_stF ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 rv F m' ms
          /\ lpost RT Σ Σ' m m' sp lo /\ keeps RT Σ Σ' sp [(pmax, pmax + 4)] m m' /\ rw_cells asegs m' pmax [C4 y]) c
       /\ rt_live RT Σ' = rt_live RT Σ
       /\ rt_frames RT Σ' = rt_frames RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ /\ rt_credit RT Σ - 2 <= rt_credit RT Σ').
