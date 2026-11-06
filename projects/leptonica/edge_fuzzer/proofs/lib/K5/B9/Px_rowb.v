(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.K5.AS Require Import ShapeAlg AsanAcct.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.K5.Lib Require Import Tac RzCPS NodesA SysStep Arr StoreFast.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.K5.PG Require Import Str_tac Startup_glue.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.K5.AG Require Import Shadow.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.K5.B9 Require Import ImageA Layout RT_iface RT_traces RT_gaps_iface LeptTac D_kit Lept_kit D_iface D_defs
  Lept_iface Lept_env LeptC_kit Lept_leaf LeptL_kit Lept_objkit Lept_gmax_defs Ed_iface Px_defs Px_defs2 Px_kit Px_bkit LeptB_guard LeptB_guard2.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac guard_fix ::= try sx32_fix; repeat match goal with |- context [bv_unsigned (Z_to_bv 64 ?e)] => rewrite (unsigned_lit e) by lia end; swrap_fix; po_fix; al_fix; try mulh_fix.

Section ROWB.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Hypothesis GP : rt_gaps RT.
Hypothesis GETPIX : pixGetPixel1_cps RT.
Hypothesis SCANOFF : pixGetLastOffPixelInRunR_cps RT.
Hypothesis SCANON : pixGetLastOnPixelInRunL_cps RT.

(* [comment removed for export] *)
Local Ltac kl_of_munch KL live MUx S m0 fr A0 FRSx LVKx LOW LOR :=
  lazymatch type of MUx with munch ?W ?ma ?mb =>
    assert (KL : keeps_live live ma mb)
      by (apply (keeps_live_of_munch live W ma mb MUx);
          let b := fresh "b" in let kk := fresh "kk" in let a := fresh "a" in let Hb := fresh "Hb" in let Ha := fresh "Ha" in
          intros b kk a Hb Ha;
          let X1 := fresh "X" in let X2 := fresh "X" in let X3 := fresh "X" in let X4 := fresh "X" in
          pose proof (chunk_vs_frame RT AF S m0 fr 1%nat b kk a A0 ltac:(rewrite FRSx; left; reflexivity) ltac:(rewrite LVKx; exact Hb) Ha) as (X1 & X2 & X3 & X4);
          change (fs_size 1%nat) with 128 in X1, X2; unfold shad, SHB in X2; revert X1 X2 X3 X4 LOW LOR; clear; unfold STACK_WIN; intros; cbn [outside];
          repeat split; try exact I; lia) end.
Local Ltac kl_of_ag KL live AGx S m0 fr A0 FRSx LVKx LOW LOR :=
  lazymatch type of AGx with agree_on _ ?ma ?mb =>
    assert (KL : keeps_live live ma mb)
      by (apply (keeps_live_of_agree live _ ma mb AGx);
          let b := fresh "b" in let kk := fresh "kk" in let a := fresh "a" in let Hb := fresh "Hb" in let Ha := fresh "Ha" in
          intros b kk a Hb Ha; cbv beta;
          let X1 := fresh "X" in let X2 := fresh "X" in let X3 := fresh "X" in let X4 := fresh "X" in
          pose proof (chunk_vs_frame RT AF S m0 fr 1%nat b kk a A0 ltac:(rewrite FRSx; left; reflexivity) ltac:(rewrite LVKx; exact Hb) Ha) as (X1 & X2 & X3 & X4);
          change (fs_size 1%nat) with 128 in X1, X2; unfold shad, SHB in X2;
          split; [ right; right; left; exists b, kk; split; [ first [exact Hb | rewrite <- LVKx; exact Hb | repeat match goal with E : rt_live _ _ = _ |- _ => rewrite E end; exact Hb] | lia ]
                 | revert X1 X2 X3 X4 LOW LOR; clear; unfold STACK_WIN; intros; cbn [outside]; repeat split; try exact I; lia ]) end.

Local Ltac eqv :=
  repeat match goal with H : rt_live _ _ = _ |- _ => rewrite H end;
  repeat match goal with H : rt_frames _ _ = _ |- _ => rewrite H end;
  repeat match goal with H : rt_sp0 _ _ = _ |- _ => rewrite H end; reflexivity.

Lemma row_body : forall (loc y : Z) (Σk : rts RT) PMc (mc : mem)
    (ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (gp s0w : word) (F : bvmap 5 word) (fc : bv 32)
    (spa fr pix na lo : Z) (v : pixv) (cv : cmapv) (live : list (Z * Z)) (frames : list (Z * nat)) (vp : word),
  -1 <= loc <= p_w v - 1 -> 0 <= y < p_h v ->
  fdfs_only PMc -> mat_stable PMc ->
  rt_live RT Σk = live -> rt_frames RT Σk = (fr, 1%nat) :: frames ->
  pix_obj live mc pix v cv -> p_d v = 1 -> p_data v <> 0 ->
  rw_cells asegs mc (spa + 52) [C4 (Z_to_bv 64 loc)] ->
  rw_cells asegs mc (fr + 32) [C4 (Z_to_bv 64 (p_w v))] ->
  rw_cells asegs mc (fr + 80) [C4 vp] ->
  rw_cells asegs mc (fr / 8 + 2147450890) [C1 (Z_to_bv 8 4)] ->
  LIBH mc -> io_ssp mc -> ART RT Σk mc -> mem_inv asegs mc -> stk asegs mc lo spa ->
  rt_sp0 RT Σk - STACK_WIN <= lo -> lo + LSTK 5 <= spa -> spa + 176 <= USTACK_TOP -> spa mod 16 = 0 -> spa + 160 <= rt_sp0 RT Σk ->
  0 < fr -> fr mod 64 = 0 -> fr + 128 <= rt_sp0 RT Σk - STACK_WIN -> SEGTOP_A <= fr -> (fr + 128 <= 0x7fff7000 \/ 0x10007fff8000 <= fr) ->
  Z.of_nat (length frames) + 3 <= Z.of_nat FRAMES_MAX -> Z.of_nat (length live) + 0 <= LIVE_MAX -> p_w v + 3 <= rt_credit RT Σk ->
  (forall p n, In (p, n) live -> 0 < n) ->
  cps asegs (ASTA RT Σk PMc (eq (MS (mkR ra (Z_to_bv 64 spa) gp (Z_to_bv 64 TP_A) t0 t1 t2 s0w (Z_to_bv 64 spa) a0 a1 a2 a3 a4 a5 a6 a7
                                        (Z_to_bv 64 fr) (Z_to_bv 64 fr) (Z_to_bv 64 na) (Z_to_bv 64 1) (Z_to_bv 64 pix) (Z_to_bv 64 (fr + 32))
                                        (Z_to_bv 64 (fr + 48)) (Z_to_bv 64 (fr + 80)) (Z_to_bv 64 y) (Z_to_bv 64 (fr / 8 + 2147450880)) t3 t4 t5 t6)
                                   F (Z_to_bv 64 0x12ccdc) (frm_clear fc) None mc (seg_rom asegs))))
    (fun c => exists (Σ' : rts RT) (loc' vb : Z),
       ASTA RT Σ' PMc (fun ms => exists (m' : mem) (ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (F' : bvmap 5 word) (fc' : bv 32),
          ms = MS (mkR ra' (Z_to_bv 64 spa) gp (Z_to_bv 64 TP_A) t0' t1' t2' s0w (Z_to_bv 64 spa) a0' a1' a2' a3' a4' a5' a6' a7'
                      (Z_to_bv 64 fr) (Z_to_bv 64 fr) (Z_to_bv 64 na) (Z_to_bv 64 1) (Z_to_bv 64 pix) (Z_to_bv 64 (fr + 32))
                      (Z_to_bv 64 (fr + 48)) (Z_to_bv 64 (fr + 80)) (Z_to_bv 64 y) (Z_to_bv 64 (fr / 8 + 2147450880)) t3' t4' t5' t6')
                 F' (Z_to_bv 64 0x12ccc0) (frm_clear fc') None m' (seg_rom asegs)
          /\ rt_after RT Σ' spa lo mc m'
          /\ rt_pres_fp live ((fr, 1%nat) :: frames) spa [(fr + 80, fr + 84); (spa + 52, spa + 56)] mc m'
          /\ LIBH m' /\ io_ssp m'
          /\ rw_cells asegs m' (spa + 52) [C4 (Z_to_bv 64 loc')]
          /\ rw_cells asegs m' (fr + 80) [C4 (Z_to_bv 64 vb)]
          /\ -1 <= loc' <= p_w v - 1) c
       /\ rt_live RT Σ' = live /\ rt_frames RT Σ' = (fr, 1%nat) :: frames /\ rt_sp0 RT Σ' = rt_sp0 RT Σk
       /\ rt_credit RT Σk - (p_w v + 3) <= rt_credit RT Σ').
Proof using AF GP GETPIX SCANOFF SCANON.
  intros loc y Σk PMc mc ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 gp s0w F fc spa fr pix na lo v cv live frames vp
    HL HY FDO MST LVK FRS POBJ D1 VDATA LOCC FW VALP SH10 LH SSP ART0 MI ST LOW LOR SPT SPA SPB FR0 FR64 FRHI FRSEG FRSH FRB LVB CRB LVP.
  destruct HL as [HL0 HL1]. destruct HY as [HY0 HY1].
  unfold LSTK, STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *.
  destruct (af_client_consts RT AF Σk mc ART0) as (G1 & G2 & G3 & G4).
  pose proof (af_sp0_range RT AF Σk mc ART0) as SP0R. pose proof (af_sp0_win RT AF Σk mc ART0) as SP0W.
  unfold g_GOT_shadow_offset_cell, g_shadow_memory_dynamic_address, g_GOT_detect_uar, g_detect_stack_use_after_return in *.
  unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A, SHB in *.
  unfold SCANOFF_COST, SCANON_COST, GETPIXEL_COST in *.
  lazymatch goal with |- cps _ _ ?Q => set (QF := Q) end.
  pose proof ST as (STa & STb & _).
  set (PF := fun a => aclient live ((fr, 1%nat) :: frames) spa a /\ outside [(fr + 80, fr + 84); (spa + 52, spa + 56)] a).
  pose proof (agree_refl PF mc) as AGF.
  assert (PFS : forall a, PF a -> spa <= a \/ a < lo).
  { intros a [Ha _]. destruct (aclient_split RT AF Σk mc spa a ART0) as [H|H]; [rewrite LVK, FRS; exact Ha| left; exact H| right; unfold STACK_WIN in H; lia]. }
  pose proof POBJ as (PXC & (PIN & PX0 & PX16 & _) & (HD1 & HW1 & HH1 & HWPL & HRS) & PDATA & _).
  destruct PDATA as [DZ|((DIN & D0 & D16 & DSZ) & DNE)]; [contradiction|].
  assert (USPA : 0 <= spa < 2^64) by (change (2^64) with 18446744073709551616; lia).
  hide POBJ.
  chunk_facts RT AF GP pix 64. chunk_facts RT AF GP (p_data v) (rsize v). unfold rsize in *.
  fframe_chunk RT AF fr 1%nat 128 pix 64. fframe_chunk RT AF fr 1%nat 128 (p_data v) (4 * (p_wpl v * p_h v)).
  refresh RT AF. unfold shad, SHB in *. clear_acc. park_disj.
  (* [comment removed for export] *)
  walk_to AF MST [(spa + 52, spa + 56)] [e_pixGetPixel].
  rewrite ?(sx32_s32 loc) by lia.
  at_call RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| exact I])
                ltac:(fun Hx => destruct Hx as [_ HxO]; revert HxO; clear; cbn [outside]; intros HxO; repeat split; try exact I; lia).
  eapply cps_seq.
  { eapply GETPIX with (lo := lo) (pix := pix) (pval := fr + 80) (x := loc) (y := y) (v := v) (cv := cv) (old := vp).
    - exact FDO.
    - exact MST.
    - reflexivity.
    - reflexivity.
    - split; [lia| reflexivity].
    - split; [lia| reflexivity].
    - reflexivity.
    - unfold hid in POBJ; rewrite LVK; exact POBJ.
    - exact D1.
    - exact VDATA.
    - unfold optrF. split.
      2: { split; [lia|]. split; [clear - FR64; Z.div_mod_to_equations; lia|]. unfold SEGTOP_A in *. split; [clear - FRSH; unfold parked in FRSH; lia| lia]. }
      exists fr, 1%nat. rewrite FRS. change (fs_size 1) with 128.
      split; [left; reflexivity|]. split; [lia|]. split; [lia|]. split; [clear - FR64; Z.div_mod_to_equations; lia|]. split; [lia|]. split; [lia|].
      replace (shad (fr + 80)) with (fr / 8 + 2147450890) by (unfold shad, SHB; clear - FR64; Z.div_mod_to_equations; lia).
      destruct SH10 as [[_ B] _]; cbn [cells_bytes cbytes app] in B; change (ushadow 4) with [Z_to_bv 8 4]; exact B.
    - exact VALP.
    - lenv_tac.
    - unfold lres, GETPIXEL_COST; rewrite FRS, LVK; cbn [length]; unfold FRAMES_MAX, LIVE_MAX in *; repeat split; [lia| lia| lia| exact LVP]. }
  after_call RT AF.
  lazymatch goal with AGx : agree_on _ mc ?m1 |- _ =>
    kl_of_ag KL live AGx Σk mc fr ART0 FRS LVK LOW LOR;
    unfold hid in POBJ; apply (pix_obj_keep live mc m1 pix v cv KL) in POBJ; hide POBJ; clear KL end.
  fold_ag ltac:(fun Hx => destruct Hx as [Hx HxO]; split; [apply (aclient_mono _ _ spa _ _ _ _ Hx); [solve [live_sub_tac]| solve [frames_sub_tac]| lia] | revert HxO; clear; cbn [outside]; intros HxO; repeat split; try exact I; lia]).
  refresh RT AF. unfold shad, SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. park_disj.
  (* [comment removed for export] *)
  walk_to AF MST [(spa + 52, spa + 56)] [e_pixGetPixel; e_pixGetLastOffPixelInRun; e_pixGetLastOnPixelInRun].
  match goal with B : ?b = 0 \/ ?b = 1 |- _ => destruct B as [EB|EB]; rewrite EB in * end.
  - (* [comment removed for export] *)
    brF.
  awalk [e_pixGetPixel; e_pixGetLastOffPixelInRun; e_pixGetLastOnPixelInRun].
  rewrite ?(sx32_s32 loc) by lia.
  at_call RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| exact I])
                  ltac:(fun Hx => destruct Hx as [_ HxO]; revert HxO; clear; cbn [outside]; intros HxO; repeat split; try exact I; lia).
  lazymatch goal with MUx : munch _ ?ma ?mb |- cps _ (ASTA _ _ _ (eq (MS _ _ _ _ _ ?mb _))) _ =>
        kl_of_munch KL live MUx Σk mc fr ART0 FRS LVK LOW LOR;
        unfold hid in POBJ; apply (pix_obj_keep live ma mb pix v cv KL) in POBJ; hide POBJ; clear KL end.
  eapply cps_seq.
  { eapply SCANOFF with (lo := lo) (pix := pix) (ploc := spa + 52) (x := loc) (y := y) (v := v) (cv := cv) (old := Z_to_bv 64 loc).
  - exact FDO.
  - exact MST.
  - reflexivity.
  - reflexivity.
  - split; [lia| reflexivity].
  - split; [lia| reflexivity].
  - reflexivity.
  - reflexivity.
  - unfold hid in POBJ; lazymatch goal with |- pix_obj (rt_live RT ?S) _ _ _ _ => replace (rt_live RT S) with live by (symmetry; eqv) end; exact POBJ.
  - exact D1.
  - exact VDATA.
  - lia.
  - lia.
  - apply (optrS_frame spa 52); [change (2^64) with 18446744073709551616; lia| lia| unfold USTACK_TOP; lia| exact SPA| reflexivity].
  - eassumption.
  - lenv_tac.
  - unfold lres, SCANOFF_COST; repeat match goal with H : rt_frames _ _ = _ |- _ => rewrite H end; lazymatch goal with |- context [rt_live RT ?S] => replace (rt_live RT S) with live by (symmetry; eqv) end; cbn [length]; unfold FRAMES_MAX, LIVE_MAX, GETPIXEL_COST in *; repeat split; [lia| lia| lia| exact LVP].
  }
    after_call RT AF.
    lazymatch goal with AGx : agree_on _ ?ma ?mb |- cps _ (ASTA _ _ _ (eq (MS _ _ _ _ _ ?mb _))) _ =>
          kl_of_ag KL live AGx Σk mc fr ART0 FRS LVK LOW LOR;
          unfold hid in POBJ; apply (pix_obj_keep live ma mb pix v cv KL) in POBJ; hide POBJ; clear KL end.
    fold_ag ltac:(fun Hx => destruct Hx as [Hx HxO]; split; [apply (aclient_mono _ _ spa _ _ _ _ Hx); [solve [live_sub_tac]| solve [frames_sub_tac]| lia] | revert HxO; clear; cbn [outside]; intros HxO; repeat split; try exact I; lia]).
    lazymatch goal with H1 : 0 <= ?r, H2 : ?r <= loc + 1 |- _ => rename r into rr; rename H1 into RR0; rename H2 into RR1 end.
    refresh RT AF. unfold shad, SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. park_disj.
    walk_to AF MST [(spa + 52, spa + 56)] [e_pixGetPixel; e_pixGetLastOffPixelInRun; e_pixGetLastOnPixelInRun; 0x12ccc0].
    destruct (Z.eq_dec rr 0) as [RZ|RZ].
    + rewrite RZ in *.
    brF.
    awalk [e_pixGetPixel; e_pixGetLastOffPixelInRun; e_pixGetLastOnPixelInRun; 0x12ccc0].
      cps_stop.
      art_now RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| exact I]).
      lazymatch goal with AGFx : agree_on ?PFx _ ?mm, MUx : munch _ ?mm _ |- _ => is_var PFx; agf_munch AGFx MUx ltac:(fun Hx => destruct Hx as [_ HxO]; revert HxO; clear; cbn [outside]; intros HxO; repeat split; try exact I; lia) end.
      lazymatch goal with Hv : rw_cells asegs _ (fr + 80) [C4 (Z_to_bv 64 ?b)], Hl : rw_cells asegs _ (spa + 52) [C4 (Z_to_bv 64 ?l)] |- cps _ (ASTA _ ?S _ _) _ =>
              apply cps_finish; intros c Hc; subst QF; cbv beta; exists S, l, b end.
      split.
      2: {
      split; [eqv|].
      split; [eqv|].
      split; [eqv|].
      unfold GETPIXEL_COST, SCANOFF_COST, SCANON_COST in *. repeat match goal with H : rt_credit _ _ = _ |- _ => rewrite H in * end. lia.
      }
      eapply (ASTA_conseq RT); [exact Hc|]; intros ms <-.
      eexists. do 18 eexists. split; [reflexivity|].
      split; [split; [assumption| split; [assumption| split; [| assumption]]]|].
      { repeat match goal with H : wmono asegs _ _ |- _ => revert H end. clear. intros. eauto using wmono_trans.
      }
      split; [intros a Ha Ho; exact (AGF a (conj Ha Ho))|].
      split; [assumption|]. split; [assumption|].
      split; [assumption|]. split; [assumption|].
      lia.
    + brT.
    awalk [e_pixGetPixel; e_pixGetLastOffPixelInRun; e_pixGetLastOnPixelInRun; 0x12ccc0].
      cps_stop.
      art_now RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| exact I]).
      lazymatch goal with AGFx : agree_on ?PFx _ ?mm, MUx : munch _ ?mm _ |- _ => is_var PFx; agf_munch AGFx MUx ltac:(fun Hx => destruct Hx as [_ HxO]; revert HxO; clear; cbn [outside]; intros HxO; repeat split; try exact I; lia) end.
      lazymatch goal with Hv : rw_cells asegs _ (fr + 80) [C4 (Z_to_bv 64 ?b)], Hl : rw_cells asegs _ (spa + 52) [C4 (Z_to_bv 64 ?l)] |- cps _ (ASTA _ ?S _ _) _ =>
              apply cps_finish; intros c Hc; subst QF; cbv beta; exists S, l, b end.
      split.
      2: {
      split; [eqv|].
      split; [eqv|].
      split; [eqv|].
      unfold GETPIXEL_COST, SCANOFF_COST, SCANON_COST in *. repeat match goal with H : rt_credit _ _ = _ |- _ => rewrite H in * end. lia.
      }
      eapply (ASTA_conseq RT); [exact Hc|]; intros ms <-.
      eexists. do 18 eexists. split; [reflexivity|].
      split; [split; [assumption| split; [assumption| split; [| assumption]]]|].
      { repeat match goal with H : wmono asegs _ _ |- _ => revert H end. clear. intros. eauto using wmono_trans.
      }
      split; [intros a Ha Ho; exact (AGF a (conj Ha Ho))|].
      split; [assumption|]. split; [assumption|].
      split; [assumption|]. split; [assumption|].
      lia.
  - match goal with H : ~ in_pix v loc y -> _ |- _ => assert (LOC0 : 0 <= loc) by (destruct (Z_lt_ge_dec loc 0) as [Hl|Hl]; [exfalso; specialize (H ltac:(unfold in_pix; lia)); discriminate | lia]) end.
  brT.
  awalk [e_pixGetPixel; e_pixGetLastOffPixelInRun; e_pixGetLastOnPixelInRun].
  rewrite ?(sx32_s32 loc) by lia.
  at_call RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| exact I])
                  ltac:(fun Hx => destruct Hx as [_ HxO]; revert HxO; clear; cbn [outside]; intros HxO; repeat split; try exact I; lia).
  lazymatch goal with MUx : munch _ ?ma ?mb |- cps _ (ASTA _ _ _ (eq (MS _ _ _ _ _ ?mb _))) _ =>
        kl_of_munch KL live MUx Σk mc fr ART0 FRS LVK LOW LOR;
        unfold hid in POBJ; apply (pix_obj_keep live ma mb pix v cv KL) in POBJ; hide POBJ; clear KL end.
  eapply cps_seq.
  { eapply SCANON with (lo := lo) (pix := pix) (ploc := spa + 52) (x := loc) (y := y) (v := v) (cv := cv) (old := Z_to_bv 64 loc).
  - exact FDO.
  - exact MST.
  - reflexivity.
  - reflexivity.
  - split; [lia| reflexivity].
  - split; [lia| reflexivity].
  - reflexivity.
  - reflexivity.
  - unfold hid in POBJ; lazymatch goal with |- pix_obj (rt_live RT ?S) _ _ _ _ => replace (rt_live RT S) with live by (symmetry; eqv) end; exact POBJ.
  - exact D1.
  - exact VDATA.
  - lia.
  - lia.
  - apply (optrS_frame spa 52); [change (2^64) with 18446744073709551616; lia| lia| unfold USTACK_TOP; lia| exact SPA| reflexivity].
  - eassumption.
  - lenv_tac.
  - unfold lres, SCANON_COST; repeat match goal with H : rt_frames _ _ = _ |- _ => rewrite H end; lazymatch goal with |- context [rt_live RT ?S] => replace (rt_live RT S) with live by (symmetry; eqv) end; cbn [length]; unfold FRAMES_MAX, LIVE_MAX, GETPIXEL_COST in *; repeat split; [lia| lia| lia| exact LVP].
  }
  after_call RT AF.
  lazymatch goal with AGx : agree_on _ ?ma ?mb |- cps _ (ASTA _ _ _ (eq (MS _ _ _ _ _ ?mb _))) _ =>
        kl_of_ag KL live AGx Σk mc fr ART0 FRS LVK LOW LOR;
        unfold hid in POBJ; apply (pix_obj_keep live ma mb pix v cv KL) in POBJ; hide POBJ; clear KL end.
  fold_ag ltac:(fun Hx => destruct Hx as [Hx HxO]; split; [apply (aclient_mono _ _ spa _ _ _ _ Hx); [solve [live_sub_tac]| solve [frames_sub_tac]| lia] | revert HxO; clear; cbn [outside]; intros HxO; repeat split; try exact I; lia]).
  refresh RT AF. unfold shad, SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. park_disj.
  walk_to AF MST [(spa + 52, spa + 56)] [0x12ccc0].
    cps_stop.
    art_now RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| exact I]).
    lazymatch goal with AGFx : agree_on ?PFx _ ?mm, MUx : munch _ ?mm _ |- _ => is_var PFx; agf_munch AGFx MUx ltac:(fun Hx => destruct Hx as [_ HxO]; revert HxO; clear; cbn [outside]; intros HxO; repeat split; try exact I; lia) end.
    lazymatch goal with Hv : rw_cells asegs _ (fr + 80) [C4 (Z_to_bv 64 ?b)], Hl : rw_cells asegs _ (spa + 52) [C4 (Z_to_bv 64 ?l)] |- cps _ (ASTA _ ?S _ _) _ =>
            apply cps_finish; intros c Hc; subst QF; cbv beta; exists S, l, b end.
    split.
    2: {
    split; [eqv|].
    split; [eqv|].
    split; [eqv|].
    unfold GETPIXEL_COST, SCANOFF_COST, SCANON_COST in *. repeat match goal with H : rt_credit _ _ = _ |- _ => rewrite H in * end. lia.
    }
    eapply (ASTA_conseq RT); [exact Hc|]; intros ms <-.
    eexists. do 18 eexists. split; [reflexivity|].
    split; [split; [assumption| split; [assumption| split; [| assumption]]]|].
    { repeat match goal with H : wmono asegs _ _ |- _ => revert H end. clear. intros. eauto using wmono_trans.
    }
    split; [intros a Ha Ho; exact (AGF a (conj Ha Ho))|].
    split; [assumption|]. split; [assumption|].
    split; [assumption|]. split; [assumption|].
    lia.
Qed.
End ROWB.
