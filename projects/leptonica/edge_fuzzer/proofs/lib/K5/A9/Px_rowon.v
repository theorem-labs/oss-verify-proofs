(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.K5.AS Require Import ShapeAlg AsanAcct.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.K5.Lib Require Import Tac RzCPS NodesA SysStep Arr StoreFast.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.K5.PG Require Import Str_tac Startup_glue.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.K5.AG Require Import Shadow.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.K5.A9 Require Import ImageA Layout RT_iface RT_traces RT_gaps_iface LeptTac D_kit Lept_kit D_iface D_defs
  Lept_iface Lept_env LeptC_kit Lept_leaf LeptL_kit Lept_objkit Lept_gmax_defs Ed_iface Px_defs Px_defs2 Px_kit Px_son.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.

Section ROWON.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Hypothesis GP : rt_gaps RT.
Hypothesis GETPIX : pixGetPixel1_cps RT.

Lemma row_on : forall (loc y : Z) (Σk : rts RT) PMc (mc : mem)
    (ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 s9 : word) (gp s0w s5w s10w : word) (F : bvmap 5 word) (fc : bv 32)
    (spa fr pix lo : Z) (v : pixv) (cv : cmapv) (live : list (Z * Z)) (frames : list (Z * nat)) (w3 h3 v3 : word),
  0 <= loc <= p_w v - 1 -> 0 <= y < p_h v ->
  fdfs_only PMc -> mat_stable PMc ->
  rt_live RT Σk = live -> rt_frames RT Σk = (fr, 4%nat) :: frames ->
  pix_obj live mc pix v cv -> p_d v = 1 -> p_data v <> 0 ->
  rw_cells asegs mc (fr + 368) [C4 w3] -> rw_cells asegs mc (fr + 384) [C4 h3] -> rw_cells asegs mc (fr + 400) [C4 v3] ->
  rw_cells asegs mc (fr / 8 + 2147450926) [C1 (Z_to_bv 8 (-8)); C1 (Z_to_bv 8 (-14)); C1 (Z_to_bv 8 (-8)); C1 (Z_to_bv 8 (-14)); C1 (Z_to_bv 8 (-8))] ->
  rw_cells asegs mc (spa + 32) [C8 (Z_to_bv 64 (fr + 384)); C8 (Z_to_bv 64 (fr + 336)); C8 (Z_to_bv 64 (fr + 320))] ->
  LIBH mc -> io_ssp mc -> ART RT Σk mc -> mem_inv asegs mc -> stk asegs mc lo spa ->
  rt_sp0 RT Σk - STACK_WIN <= lo -> lo + LSTK 4 <= spa -> spa + 272 <= USTACK_TOP -> spa mod 16 = 0 -> spa + 256 <= rt_sp0 RT Σk ->
  0 < fr -> fr mod 64 = 0 -> fr + 1024 <= rt_sp0 RT Σk - STACK_WIN -> SEGTOP_A <= fr -> (fr + 1024 <= 0x7fff7000 \/ 0x10007fff8000 <= fr) ->
  Z.of_nat (length frames) + 2 <= Z.of_nat FRAMES_MAX -> Z.of_nat (length live) + 0 <= LIVE_MAX -> p_w v - loc <= rt_credit RT Σk ->
  (forall p n, In (p, n) live -> 0 < n) ->
  cps asegs (ASTA RT Σk PMc (eq (MS (mkR ra (Z_to_bv 64 spa) gp (Z_to_bv 64 TP_A) t0 t1 t2 s0w (Z_to_bv 64 spa) a0 a1 a2 a3 a4 a5 a6 a7
                                        (Z_to_bv 64 loc) (Z_to_bv 64 (fr + 368)) (Z_to_bv 64 (fr / 8 + 2147450880)) s5w (Z_to_bv 64 pix) (Z_to_bv 64 1)
                                        (Z_to_bv 64 y) s9 s10w (Z_to_bv 64 (fr + 400)) t3 t4 t5 t6)
                                   F (Z_to_bv 64 0x121b3c) (frm_clear fc) None mc (seg_rom asegs))))
    (fun c => exists (Σ' : rts RT) (loc' vb : Z) (w3' h3' : word),
       ASTA RT Σ' PMc (fun ms => exists (m' : mem) (ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (F' : bvmap 5 word) (fc' : bv 32),
          ms = MS (mkR ra' (Z_to_bv 64 spa) gp (Z_to_bv 64 TP_A) t0' t1' t2' s0w (Z_to_bv 64 spa) a0' a1' a2' a3' a4' a5' a6' a7'
                      (Z_to_bv 64 loc') (Z_to_bv 64 (fr + 368)) (Z_to_bv 64 (fr / 8 + 2147450880)) s5w (Z_to_bv 64 pix) (Z_to_bv 64 1)
                      (Z_to_bv 64 y) s9 s10w (Z_to_bv 64 (fr + 400)) t3' t4' t5' t6')
                 F' (Z_to_bv 64 0x121b00) (frm_clear fc') None m' (seg_rom asegs)
          /\ rt_after RT Σ' spa lo mc m'
          /\ rt_pres_fp live ((fr, 4%nat) :: frames) spa [(fr + 368, fr + 404); (fr / 8 + 2147450926, fr / 8 + 2147450931)] mc m'
          /\ LIBH m' /\ io_ssp m'
          /\ rw_cells asegs m' (fr + 368) [C4 w3'] /\ rw_cells asegs m' (fr + 384) [C4 h3'] /\ rw_cells asegs m' (fr + 400) [C4 (Z_to_bv 64 vb)]
          /\ rw_cells asegs m' (fr / 8 + 2147450926) [C1 (Z_to_bv 8 (-8)); C1 (Z_to_bv 8 (-14)); C1 (Z_to_bv 8 (-8)); C1 (Z_to_bv 8 (-14)); C1 (Z_to_bv 8 (-8))]
          /\ loc - 1 <= loc' <= p_w v - 1) c
       /\ rt_live RT Σ' = live /\ rt_frames RT Σ' = (fr, 4%nat) :: frames /\ rt_sp0 RT Σ' = rt_sp0 RT Σk
       /\ rt_credit RT Σk - (p_w v - loc) <= rt_credit RT Σ').
Proof using AF GP GETPIX.
  intros loc y Σk PMc mc ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 s9 gp s0w s5w s10w F fc spa fr pix lo v cv live frames w3 h3 v3
    HL HY FDO MST LVK FRS POBJ D1 VDATA W3 H3 V3 SHON SPL LH SSP ART0 MI ST LOW LOR SPT SPA SPB FR0 FR64 FRHI FRSEG FRSH FRB LVB CRB LVP.
  destruct HL as [HL0 HL1]. destruct HY as [HY0 HY1].
  unfold LSTK, STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *.
  destruct (af_client_consts RT AF Σk mc ART0) as (G1 & G2 & G3 & G4).
  pose proof (af_sp0_range RT AF Σk mc ART0) as SP0R. pose proof (af_sp0_win RT AF Σk mc ART0) as SP0W.
  unfold g_GOT_shadow_offset_cell, g_shadow_memory_dynamic_address, g_GOT_detect_uar, g_detect_stack_use_after_return in *.
  unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A, SHB in *.
  lazymatch goal with |- cps _ _ ?Q => set (QF := Q) end.
  pose proof ST as (STa & STb & _).
  set (PF := fun a => aclient live ((fr, 4%nat) :: frames) spa a /\ outside [(fr + 368, fr + 404); (fr / 8 + 2147450926, fr / 8 + 2147450931)] a).
  pose proof (agree_refl PF mc) as AGF.
  assert (PFS : forall a, PF a -> spa <= a \/ a < lo).
  { intros a [Ha _]. destruct (aclient_split RT AF Σk mc spa a ART0) as [H|H]; [rewrite LVK, FRS; exact Ha| left; exact H| right; unfold STACK_WIN in H; lia]. }
  pose proof POBJ as (PXC & (PIN & PX0 & PX16 & _) & (HD1 & HW1 & HH1 & HWPL & HRS) & PDATA & _).
  destruct PDATA as [DZ|((DIN & D0 & D16 & DSZ) & DNE)]; [contradiction|].
  unfold pix_cells in PXC. rewrite D1 in PXC.
  hide POBJ.
  chunk_facts RT AF GP pix 64. chunk_facts RT AF GP (p_data v) (rsize v). unfold rsize in *.
  fframe_chunk RT AF fr 4%nat 1024 pix 64. fframe_chunk RT AF fr 4%nat 1024 (p_data v) (4 * (p_wpl v * p_h v)).
  refresh RT AF. unfold shad, SHB in *. clear_acc. park_disj.
  (* [comment removed for export] *)
  pwalk_to AF MST [(spa - 16, spa); (fr + 368, fr + 404); (fr / 8 + 2147450926, fr / 8 + 2147450931)] [0x121b4c].
  cps_stop.
  art_now RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac| exact I]]]).
  lazymatch goal with AGFx : agree_on ?PFx _ ?mm, MUx : munch _ ?mm _ |- _ => is_var PFx; agf_munch AGFx MUx ltac:(fun Hx => pose proof (PFS _ Hx) as HxS; destruct Hx as [_ HxO]; revert HxO HxS; clear - LOR; cbn [outside]; intros HxO HxS; repeat split; try exact I; lia) end.
  lazymatch goal with MUx : munch ?W mc ?mb |- _ =>
    assert (KL : keeps_live live mc mb)
      by (apply (keeps_live_of_munch live W mc mb MUx); intros b kk a Hb Ha;
          pose proof (chunk_vs_frame RT AF Σk mc fr 4%nat b kk a ART0 ltac:(rewrite FRS; left; reflexivity) ltac:(rewrite LVK; exact Hb) Ha) as (X1 & X2 & X3 & X4);
          change (fs_size 4%nat) with 1024 in X1, X2; unfold shad, SHB in X2; revert X1 X2 X3 X4 LOW LOR; clear; unfold STACK_WIN; intros; cbn [outside]; repeat split; try exact I; lia);
    unfold hid in POBJ; apply (pix_obj_keep live mc mb pix v cv KL) in POBJ; hide POBJ; clear KL end.
  refresh RT AF. unfold shad, SHB in *.
  lazymatch goal with |- cps _ (ASTA _ _ _ (eq (MS _ _ _ _ _ ?mm _))) _ =>
    assert (ACC368 : acc asegs mm (fr + 368) 4) by (pose proof SHON as T; destruct T as [[_ B] _]; apply (acc_ushadow asegs mm (fr + 368) 4); [clear - FR64; Z.div_mod_to_equations; lia| lia| lia|];
      replace (shad (fr + 368)) with (fr / 8 + 2147450926) by (unfold shad, SHB; clear - FR64; Z.div_mod_to_equations; lia);
      apply (bytes_at_mid mm (fr / 8 + 2147450926) _ 0 1) in B; [cbn in B; rewrite Z.add_0_r in B; exact B| cbn; lia]) end.
  lazymatch goal with |- cps _ (ASTA _ _ _ (eq (MS _ _ _ _ _ ?mm _))) _ =>
    assert (ACC384 : acc asegs mm (fr + 384) 4) by (pose proof SHON as T; split_at T 2%nat T2; destruct T2 as [[_ B] _]; apply (acc_ushadow asegs mm (fr + 384) 4); [clear - FR64; Z.div_mod_to_equations; lia| lia| lia|];
      replace (shad (fr + 384)) with (fr / 8 + 2147450928) by (unfold shad, SHB; clear - FR64; Z.div_mod_to_equations; lia);
      apply (bytes_at_mid mm _ _ 0 1) in B; [cbn in B; rewrite Z.add_0_r in B; exact B| cbn; lia]) end.
  park_disj.
  (* [comment removed for export] *)
  pwalk_to AF MST [(spa - 16, spa); (fr + 368, fr + 404); (fr / 8 + 2147450926, fr / 8 + 2147450931)] [0x121b74].
  sx32_fix. brF.
  pwalk [0x121b74].
  cps_stop.
  art_now RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac| exact I]]]).
  lazymatch goal with AGFx : agree_on ?PFx _ ?mm, MUx : munch _ ?mm _ |- _ => is_var PFx; agf_munch AGFx MUx ltac:(fun Hx => pose proof (PFS _ Hx) as HxS; destruct Hx as [_ HxO]; revert HxO HxS; clear - LOR; cbn [outside]; intros HxO HxS; repeat split; try exact I; lia) end.
  lazymatch goal with MUx : munch ?W ?ma ?mb |- cps _ (ASTA _ _ _ (eq (MS _ _ _ _ _ ?mb _))) _ =>
    assert (KL : keeps_live live ma mb)
      by (apply (keeps_live_of_munch live W ma mb MUx); intros b kk a Hb Ha;
          pose proof (chunk_vs_frame RT AF Σk mc fr 4%nat b kk a ART0 ltac:(rewrite FRS; left; reflexivity) ltac:(rewrite LVK; exact Hb) Ha) as (X1 & X2 & X3 & X4);
          change (fs_size 4%nat) with 1024 in X1, X2; unfold shad, SHB in X2; revert X1 X2 X3 X4 LOW LOR; clear; unfold STACK_WIN; intros; cbn [outside]; repeat split; try exact I; lia);
    unfold hid in POBJ; apply (pix_obj_keep live ma mb pix v cv KL) in POBJ; hide POBJ; clear KL end.
  rewrite ?(sx32_small (p_w v)) in W3 by lia. rewrite ?(sx32_small (p_h v)) in H3 by lia.
  (* [comment removed for export] *)
  eapply cps_seq.
  { eapply (son_loop RT AF GP GETPIX (Z.to_nat (p_w v - loc)) loc) with (lo := lo) (v := v) (cv := cv) (live := live) (frames := frames).
    - clear - HL0 HL1; lia.
    - clear - HL0 HL1; lia.
    - clear - HY0 HY1; lia.
    - exact FDO.
    - exact MST.
    - first [exact LVK | transitivity (rt_live RT Σk); [assumption | exact LVK]].
    - first [exact FRS | transitivity (rt_frames RT Σk); [assumption | exact FRS]].
    - unfold hid in POBJ; exact POBJ.
    - exact D1.
    - exact VDATA.
    - eassumption.
    - exact SHON.
    - exact W3.
    - assumption.
    - assumption.
    - assumption.
    - assumption.
    - eassumption.
    - repeat match goal with H : rt_sp0 _ _ = _ |- _ => rewrite H end; unfold STACK_WIN in *; lia.
    - unfold LSTK, RT_STACK in *; lia.
    - unfold USTACK_TOP in *; lia.
    - exact SPA.
    - repeat match goal with H : rt_sp0 _ _ = _ |- _ => rewrite H end; lia.
    - exact FR0.
    - exact FR64.
    - repeat match goal with H : rt_sp0 _ _ = _ |- _ => rewrite H end; unfold STACK_WIN in *; lia.
    - unfold SEGTOP_A in *; lia.
    - clear - FRSH; unfold parked in *; lia.
    - exact FRB.
    - exact LVB.
    - repeat match goal with H : rt_credit _ _ = _ |- _ => rewrite H end; lia.
    - exact LVP. }
  after_call RT AF.
  fold_ag ltac:(fun Hx => destruct Hx as [Hx HxO]; split; [apply (aclient_mono _ _ spa _ _ _ _ Hx); [solve [live_sub_tac]| solve [frames_sub_tac]| lia] | revert HxO; clear; cbn [outside]; intros HxO; repeat split; try exact I; lia]).
  (* [comment removed for export] *)
  lazymatch goal with Hv : rw_cells asegs _ (fr + 400) [C4 (Z_to_bv 64 ?b)] |- cps _ (ASTA _ ?S _ (eq (MS (mkR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (Z_to_bv 64 ?l) _ _ _ _ _ _ _ _ _ _ _ _ _) _ _ _ _ _ _))) _ =>
    apply cps_finish; intros c Hc; subst QF; cbv beta; exists S, l, b end.
  lazymatch goal with Hw : rw_cells asegs _ (fr + 368) [C4 ?a], Hh : rw_cells asegs _ (fr + 384) [C4 ?b] |- _ => exists a, b end.
  split.
  2: { split; [repeat match goal with H : rt_live _ _ = _ |- _ => rewrite H end; reflexivity|].
       split; [repeat match goal with H : rt_frames _ _ = _ |- _ => rewrite H end; reflexivity|].
       split; [repeat match goal with H : rt_sp0 _ _ = _ |- _ => rewrite H end; reflexivity|].
       repeat match goal with H : rt_credit _ _ = _ |- _ => rewrite H in * end. lia. }
  eapply (ASTA_conseq RT); [exact Hc|]; intros ms <-.
  eexists. do 18 eexists. split; [reflexivity|].
  split; [split; [assumption| split; [assumption| split; [| assumption]]]|].
  { repeat match goal with H : wmono asegs _ _ |- _ => revert H end. clear. intros. eauto using wmono_trans. }
  split; [intros a Ha Ho; exact (AGF a (conj Ha Ho))|].
  split; [assumption|]. split; [assumption|].
  split; [assumption|]. split; [assumption|]. split; [assumption|].
  split; [assumption|].
  lia.
Qed.
End ROWON.
