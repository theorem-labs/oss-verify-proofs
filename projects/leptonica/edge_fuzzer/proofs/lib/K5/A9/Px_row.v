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
  Lept_iface Lept_env LeptC_kit Lept_leaf LeptL_kit Lept_objkit Lept_gmax_defs Ed_iface Numa_kit Px_defs Px_defs2 Px_kit Px_rowon Px_rowoff Ed_fpkit.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.

Section ROW.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Hypothesis GP : rt_gaps RT.
Hypothesis GETPIX : pixGetPixel1_cps RT.
Hypothesis NADDF : numaAddNumber_fast_cps RT.

(* [comment removed for export] *)
Local Ltac kl_of_munch KL live MUx S m0 fr A0 FRSx LVKx LOW LOR :=
  lazymatch type of MUx with munch ?W ?ma ?mb =>
    assert (KL : keeps_live live ma mb)
      by (apply (keeps_live_of_munch live W ma mb MUx);
          let b := fresh "b" in let kk := fresh "kk" in let a := fresh "a" in let Hb := fresh "Hb" in let Ha := fresh "Ha" in
          intros b kk a Hb Ha;
          let X1 := fresh "X" in let X2 := fresh "X" in let X3 := fresh "X" in let X4 := fresh "X" in
          pose proof (chunk_vs_frame RT AF S m0 fr 4%nat b kk a A0 ltac:(rewrite FRSx; left; reflexivity) ltac:(rewrite LVKx; exact Hb) Ha) as (X1 & X2 & X3 & X4);
          change (fs_size 4%nat) with 1024 in X1, X2; unfold shad, SHB in X2; revert X1 X2 X3 X4 LOW LOR; clear; unfold STACK_WIN; intros; cbn [outside];
          repeat split; try exact I; lia) end.
Local Ltac kl_of_ag KL live AGx S m0 fr A0 FRSx LVKx LOW LOR :=
  lazymatch type of AGx with agree_on _ ?ma ?mb =>
    assert (KL : keeps_live live ma mb)
      by (apply (keeps_live_of_agree live _ ma mb AGx);
          let b := fresh "b" in let kk := fresh "kk" in let a := fresh "a" in let Hb := fresh "Hb" in let Ha := fresh "Ha" in
          intros b kk a Hb Ha; cbv beta;
          let X1 := fresh "X" in let X2 := fresh "X" in let X3 := fresh "X" in let X4 := fresh "X" in
          pose proof (chunk_vs_frame RT AF S m0 fr 4%nat b kk a A0 ltac:(rewrite FRSx; left; reflexivity) ltac:(rewrite LVKx; exact Hb) Ha) as (X1 & X2 & X3 & X4);
          change (fs_size 4%nat) with 1024 in X1, X2; unfold shad, SHB in X2;
          split; [ right; right; left; exists b, kk; split; [ repeat match goal with E : rt_live _ _ = _ |- _ => rewrite E end; first [exact Hb | rewrite <- LVKx; exact Hb] | lia ]
                 | revert X1 X2 X3 X4 LOW LOR; clear; unfold STACK_WIN; intros; cbn [outside]; repeat split; try exact I; lia ]) end.

Local Ltac eqv :=
  repeat match goal with H : rt_live _ _ = _ |- _ => rewrite H end;
  repeat match goal with H : rt_frames _ _ = _ |- _ => rewrite H end;
  repeat match goal with H : rt_sp0 _ _ = _ |- _ => rewrite H end; reflexivity.

Lemma row_loop : forall (k : nat) (y loc : Z) (Σk : rts RT) PMc (mc : mem)
    (ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 s9 : word) (gp s0w : word) (F : bvmap 5 word) (fc : bv 32)
    (spa fr pix na arr lo : Z) (v : pixv) (cv : cmapv) (live live0 : list (Z * Z)) (frames : list (Z * nat)) (ks : list Z)
    (w2 h2 v2 w3 h3 v3 vp : word),
  Z.of_nat k = p_h v - y -> 1 <= y <= p_h v - 1 -> -1 <= loc <= p_w v - 1 ->
  fdfs_only PMc -> mat_stable PMc ->
  rt_live RT Σk = live -> rt_frames RT Σk = (fr, 4%nat) :: frames -> live = (arr, 4 * p_h v) :: (na, 32) :: live0 ->
  pix_obj live0 mc pix v cv -> p_d v = 1 -> p_data v <> 0 ->
  numa_obj live mc na (p_h v) arr (map ival_w ks) -> Z.of_nat (length ks) = y -> Forall (fun q => loc_ok q /\ q <= p_w v - 1) ks ->
  rw_cells asegs mc (fr + 320) [C4 w2] -> rw_cells asegs mc (fr + 336) [C4 h2] -> rw_cells asegs mc (fr + 352) [C4 v2] ->
  rw_cells asegs mc (fr + 368) [C4 w3] -> rw_cells asegs mc (fr + 384) [C4 h3] -> rw_cells asegs mc (fr + 400) [C4 v3] ->
  rw_cells asegs mc (fr + 656) [C4 vp] ->
  rw_cells asegs mc (fr + 608) [C4 (Z_to_bv 64 (p_w v))] -> rw_cells asegs mc (fr + 624) [C4 (Z_to_bv 64 (p_h v))] ->
  rw_cells asegs mc (fr / 8 + 2147450920) [C1 (Z_to_bv 8 (-8)); C1 (Z_to_bv 8 (-14)); C1 (Z_to_bv 8 (-8)); C1 (Z_to_bv 8 (-14)); C1 (Z_to_bv 8 (-8))] ->
  rw_cells asegs mc (fr / 8 + 2147450926) [C1 (Z_to_bv 8 (-8)); C1 (Z_to_bv 8 (-14)); C1 (Z_to_bv 8 (-8)); C1 (Z_to_bv 8 (-14)); C1 (Z_to_bv 8 (-8))] ->
  rw_cells asegs mc (fr / 8 + 2147450962) [C1 (Z_to_bv 8 4)] ->
  rw_cells asegs mc (spa + 32) [C8 (Z_to_bv 64 (fr + 384)); C8 (Z_to_bv 64 (fr + 336)); C8 (Z_to_bv 64 (fr + 320))] ->
  rw_cells asegs mc (spa + 96) [C8 (Z_to_bv 64 (fr + 624))] -> rw_cells asegs mc (spa + 104) [C8 (Z_to_bv 64 (fr + 608))] ->
  rw_cells asegs mc (spa + 112) [C8 (Z_to_bv 64 (fr + 656)); C8 (Z_to_bv 64 na)] ->
  LIBH mc -> io_ssp mc -> ART RT Σk mc -> mem_inv asegs mc -> stk asegs mc lo spa ->
  rt_sp0 RT Σk - STACK_WIN <= lo -> lo + LSTK 5 <= spa -> spa + 272 <= USTACK_TOP -> spa mod 16 = 0 -> spa + 256 <= rt_sp0 RT Σk ->
  0 < fr -> fr mod 64 = 0 -> fr + 1024 <= rt_sp0 RT Σk - STACK_WIN -> SEGTOP_A <= fr -> (fr + 1024 <= 0x7fff7000 \/ 0x10007fff8000 <= fr) ->
  Z.of_nat (length frames) + 2 <= Z.of_nat FRAMES_MAX -> Z.of_nat (length live) + 0 <= LIVE_MAX ->
  (p_h v - y) * (p_w v + 1) <= rt_credit RT Σk -> (forall p n, In (p, n) live -> 0 < n) ->
  cps asegs (ASTA RT Σk PMc (eq (MS (mkR ra (Z_to_bv 64 spa) gp (Z_to_bv 64 TP_A) t0 t1 t2 s0w (Z_to_bv 64 spa) a0 a1 a2 a3 a4 a5 a6 a7
                                        (Z_to_bv 64 loc) (Z_to_bv 64 (fr + 368)) (Z_to_bv 64 (fr / 8 + 2147450880)) (Z_to_bv 64 (fr + 352)) (Z_to_bv 64 pix) (Z_to_bv 64 1)
                                        (Z_to_bv 64 y) s9 (Z_to_bv 64 fr) (Z_to_bv 64 (fr + 400)) t3 t4 t5 t6)
                                   F (Z_to_bv 64 0x121b1c) (frm_clear fc) None mc (seg_rom asegs))))
    (fun c => exists (Σ' : rts RT) (loc' : Z) (ks' : list Z) (w2' h2' v2' w3' h3' v3' vp' : word),
       ASTA RT Σ' PMc (fun ms => exists (m' : mem) (ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' s9' : word) (F' : bvmap 5 word) (fc' : bv 32),
          ms = MS (mkR ra' (Z_to_bv 64 spa) gp (Z_to_bv 64 TP_A) t0' t1' t2' s0w (Z_to_bv 64 spa) a0' a1' a2' a3' a4' a5' a6' a7'
                      (Z_to_bv 64 loc') (Z_to_bv 64 (fr + 368)) (Z_to_bv 64 (fr / 8 + 2147450880)) (Z_to_bv 64 (fr + 352)) (Z_to_bv 64 pix) (Z_to_bv 64 1)
                      (Z_to_bv 64 (p_h v)) s9' (Z_to_bv 64 fr) (Z_to_bv 64 (fr + 400)) t3' t4' t5' t6')
                 F' (Z_to_bv 64 0x1225e0) (frm_clear fc') None m' (seg_rom asegs)
          /\ rt_after RT Σ' spa lo mc m'
          /\ rt_pres_fp live ((fr, 4%nat) :: frames) spa
               [(na, na + 32); (arr, arr + 4 * p_h v); (fr + 320, fr + 404); (fr + 656, fr + 660); (fr / 8 + 2147450920, fr / 8 + 2147450931)] mc m'
          /\ LIBH m' /\ io_ssp m'
          /\ numa_obj live m' na (p_h v) arr (map ival_w ks') /\ Z.of_nat (length ks') = p_h v /\ Forall (fun q => loc_ok q /\ q <= p_w v - 1) ks'
          /\ rw_cells asegs m' (fr + 320) [C4 w2'] /\ rw_cells asegs m' (fr + 336) [C4 h2'] /\ rw_cells asegs m' (fr + 352) [C4 v2']
          /\ rw_cells asegs m' (fr + 368) [C4 w3'] /\ rw_cells asegs m' (fr + 384) [C4 h3'] /\ rw_cells asegs m' (fr + 400) [C4 v3']
          /\ rw_cells asegs m' (fr + 656) [C4 vp']
          /\ rw_cells asegs m' (fr / 8 + 2147450920) [C1 (Z_to_bv 8 (-8)); C1 (Z_to_bv 8 (-14)); C1 (Z_to_bv 8 (-8)); C1 (Z_to_bv 8 (-14)); C1 (Z_to_bv 8 (-8))]
          /\ rw_cells asegs m' (fr / 8 + 2147450926) [C1 (Z_to_bv 8 (-8)); C1 (Z_to_bv 8 (-14)); C1 (Z_to_bv 8 (-8)); C1 (Z_to_bv 8 (-14)); C1 (Z_to_bv 8 (-8))]) c
       /\ rt_live RT Σ' = live /\ rt_frames RT Σ' = (fr, 4%nat) :: frames /\ rt_sp0 RT Σ' = rt_sp0 RT Σk
       /\ rt_credit RT Σk - (p_h v - y) * (p_w v + 1) <= rt_credit RT Σ').
Proof using AF GP GETPIX NADDF.
  induction k as [|k IH]; intros y loc Σk PMc mc ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 s9 gp s0w F fc spa fr pix na arr lo v cv live live0 frames ks
    w2 h2 v2 w3 h3 v3 vp
    HK HY HL FDO MST LVK FRS LVSH POBJ D1 VDATA NOBJ KS KSF W2 H2 V2 W3 H3 V3 VALP FW FH SHOFF SHON SH82 SPL SPH1 SPW SPH3
    LH SSP ART0 MI ST LOW LOR SPT SPA SPB FR0 FR64 FRHI FRSEG FRSH FRB LVB CRB LVP.
  { exfalso; lia. }
  destruct HY as [HY0 HY1]. destruct HL as [HL0 HL1].
  assert (LV0 : forall e, In e live0 -> In e live) by (intros e He; rewrite LVSH; right; right; exact He).
  unfold LSTK, STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *.
  destruct (af_client_consts RT AF Σk mc ART0) as (G1 & G2 & G3 & G4).
  pose proof (af_sp0_range RT AF Σk mc ART0) as SP0R. pose proof (af_sp0_win RT AF Σk mc ART0) as SP0W.
  unfold g_GOT_shadow_offset_cell, g_shadow_memory_dynamic_address, g_GOT_detect_uar, g_detect_stack_use_after_return in *.
  unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A, SHB in *.
  lazymatch goal with |- cps _ _ ?Q => set (QF := Q) end.
  pose proof ST as (STa & STb & _).
  set (PF := fun a => aclient live ((fr, 4%nat) :: frames) spa a /\ outside [(na, na + 32); (arr, arr + 4 * p_h v); (fr + 320, fr + 404); (fr + 656, fr + 660); (fr / 8 + 2147450920, fr / 8 + 2147450931)] a).
  pose proof (agree_refl PF mc) as AGF.
  assert (PFS : forall a, PF a -> spa <= a \/ a < lo).
  { intros a [Ha _]. destruct (aclient_split RT AF Σk mc spa a ART0) as [H|H]; [rewrite LVK, FRS; exact Ha| left; exact H| right; unfold STACK_WIN in H; lia]. }
  pose proof POBJ as (PXC & (PIN & PX0 & PX16 & _) & (HD1 & HW1 & HH1 & HWPL & HRS) & PDATA & _).
  destruct PDATA as [DZ|((DIN & D0 & D16 & DSZ) & DNE)]; [contradiction|].
  pose proof (LV0 _ PIN) as PINL. pose proof (LV0 _ DIN) as DINL.
  hide POBJ.
  pose proof (numa_obj_facts _ _ _ _ _ _ NOBJ) as (NLEN & NCAP & NA0 & NA16 & AR0 & AR16 & INNA & INAR & NANE).
  rewrite length_map in NLEN.
  chunk_facts RT AF GP pix 64. chunk_facts RT AF GP (p_data v) (rsize v). unfold rsize in *.
  chunk_facts RT AF GP na 32. chunk_facts RT AF GP arr (4 * p_h v).
  fframe_chunk RT AF fr 4%nat 1024 pix 64. fframe_chunk RT AF fr 4%nat 1024 (p_data v) (4 * (p_wpl v * p_h v)).
  fframe_chunk RT AF fr 4%nat 1024 na 32. fframe_chunk RT AF fr 4%nat 1024 arr (4 * p_h v).
  assert (CRW : p_w v + 1 <= (p_h v - y) * (p_w v + 1)) by (clear - HY0 HY1 HW1; nia).
  refresh RT AF. unfold shad, SHB in *. park_disj.
  (* [comment removed for export] *)
  walk_to AF MST [(spa - 16, spa); (fr + 320, fr + 404); (fr / 8 + 2147450920, fr / 8 + 2147450931)] [e_pixGetPixel].
  at_call RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac| exact I]]])
                ltac:(fun Hx => pose proof (PFS _ Hx) as HxS; destruct Hx as [_ HxO]; revert HxO HxS; clear - LOR; cbn [outside]; intros HxO HxS; repeat split; try exact I; lia).
  eapply cps_seq.
  { eapply GETPIX with (lo := lo) (pix := pix) (pval := fr + 656) (x := loc) (y := y) (v := v) (cv := cv) (old := vp).
    - exact FDO.
    - exact MST.
    - reflexivity.
    - reflexivity.
    - split; [lia| reflexivity].
    - split; [lia| reflexivity].
    - reflexivity.
    - unfold hid in POBJ; rewrite LVK; exact (pix_obj_mono live0 live mc pix v cv LV0 POBJ).
    - exact D1.
    - exact VDATA.
    - unfold optrF. split.
      2: { split; [lia|]. split; [clear - FR64; Z.div_mod_to_equations; lia|]. unfold SEGTOP_A in *. split; [clear - FRSH; unfold parked in FRSH; lia| lia]. }
      exists fr, 4%nat. rewrite FRS. change (fs_size 4) with 1024.
      split; [left; reflexivity|]. split; [lia|]. split; [lia|]. split; [clear - FR64; Z.div_mod_to_equations; lia|]. split; [lia|]. split; [lia|].
      replace (shad (fr + 656)) with (fr / 8 + 2147450962) by (unfold shad, SHB; clear - FR64; Z.div_mod_to_equations; lia).
      destruct SH82 as [[_ B] _]; cbn [cells_bytes cbytes app] in B; change (ushadow 4) with [Z_to_bv 8 4]; exact B.
    - exact VALP.
    - lenv_tac.
    - unfold lres, GETPIXEL_COST; rewrite FRS, LVK; cbn [length]; unfold FRAMES_MAX, LIVE_MAX in *; repeat split; [lia| lia| lia| exact LVP]. }
  after_call RT AF.
  lazymatch goal with AGx : agree_on _ mc ?m1 |- _ =>
    kl_of_ag KL live AGx Σk mc fr ART0 FRS LVK LOW LOR;
    unfold hid in POBJ; apply (pix_obj_keep live0 mc m1 pix v cv (keeps_live_sub live live0 mc m1 LV0 KL)) in POBJ; hide POBJ;
    apply (numa_obj_keep live mc m1 na (p_h v) arr (map ival_w ks) KL) in NOBJ; clear KL end.
  fold_ag ltac:(fun Hx => destruct Hx as [Hx HxO]; split; [apply (aclient_mono _ _ spa _ _ _ _ Hx); [solve [live_sub_tac]| solve [frames_sub_tac]| lia] | revert HxO; clear; cbn [outside]; intros HxO; repeat split; try exact I; lia]).
  refresh RT AF. unfold shad, SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. park_disj.
  (* [comment removed for export] *)
  pwalk_to AF MST [(spa - 16, spa); (fr + 320, fr + 404); (fr / 8 + 2147450920, fr / 8 + 2147450931)] [e_pixGetPixel; 0x121ba0; 0x121b3c].
  match goal with B : ?b = 0 \/ ?b = 1 |- _ => destruct B as [EB|EB]; rewrite EB in * end.
  - (* [comment removed for export] *)
    replace (sx32 (Z_to_bv 64 0)) with (Z_to_bv 64 0) by (apply bv_eq; vm_compute; reflexivity).
    pwalk [e_pixGetPixel; 0x121ba0].
    cps_stop.
    art_now RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac| exact I]]]).
    lazymatch goal with AGFx : agree_on ?PFx _ ?mm, MUx : munch _ ?mm _ |- _ => is_var PFx; agf_munch AGFx MUx ltac:(fun Hx => pose proof (PFS _ Hx) as HxS; destruct Hx as [_ HxO]; revert HxO HxS; clear - LOR; cbn [outside]; intros HxO HxS; repeat split; try exact I; lia) end.
    lazymatch goal with MUx : munch _ ?ma ?mb |- cps _ (ASTA _ _ _ (eq (MS _ _ _ _ _ ?mb _))) _ =>
      kl_of_munch KL live MUx Σk mc fr ART0 FRS LVK LOW LOR;
      unfold hid in POBJ; apply (pix_obj_keep live0 ma mb pix v cv (keeps_live_sub live live0 ma mb LV0 KL)) in POBJ; hide POBJ;
      apply (numa_obj_keep live ma mb na (p_h v) arr (map ival_w ks) KL) in NOBJ; clear KL end.
    eapply cps_seq.
    { eapply (row_off RT AF GP GETPIX loc y) with (lo := lo) (v := v) (cv := cv) (live := live) (frames := frames).
      - clear - HL0 HL1; lia.
      - clear - HY0 HY1; lia.
      - exact FDO.
      - exact MST.
      - eqv.
      - eqv.
      - unfold hid in POBJ; exact (pix_obj_mono live0 live _ pix v cv LV0 POBJ).
      - exact D1.
      - exact VDATA.
      - exact W2.
      - exact H2.
      - exact V2.
      - exact SPW.
      - exact FW.
      - exact SHOFF.
      - exact SPL.
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
      - unfold GETPIXEL_COST in *; lia.
      - exact LVP. }
    after_call RT AF.
    lazymatch goal with AGx : agree_on _ ?ma ?mb |- cps _ (ASTA _ _ _ (eq (MS _ _ _ _ _ ?mb _))) _ =>
      kl_of_ag KL live AGx Σk mc fr ART0 FRS LVK LOW LOR;
      unfold hid in POBJ; apply (pix_obj_keep live0 ma mb pix v cv (keeps_live_sub live live0 ma mb LV0 KL)) in POBJ; hide POBJ;
      apply (numa_obj_keep live ma mb na (p_h v) arr (map ival_w ks) KL) in NOBJ; clear KL end.
    fold_ag ltac:(fun Hx => destruct Hx as [Hx HxO]; split; [apply (aclient_mono _ _ spa _ _ _ _ Hx); [solve [live_sub_tac]| solve [frames_sub_tac]| lia] | revert HxO; clear; cbn [outside]; intros HxO; repeat split; try exact I; lia]).
    lazymatch goal with H1 : 0 <= ?l, H2 : ?l <= p_w v - 1 |- cps _ (ASTA _ _ _ (eq (MS (mkR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (Z_to_bv 64 ?l) _ _ _ _ _ _ _ _ _ _ _ _ _) _ _ _ _ _ _))) _ =>
      rename l into loc'; assert (HL' : -1 <= loc' <= p_w v - 1) by lia end.
    refresh RT AF. unfold shad, SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. park_disj.
    (* [comment removed for export] *)
    pwalk_to AF MST [(spa - 16, spa); (fr + 320, fr + 404); (fr / 8 + 2147450920, fr / 8 + 2147450931)] [e_numaAddNumber].
    at_call RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac| exact I]]])
                  ltac:(fun Hx => pose proof (PFS _ Hx) as HxS; destruct Hx as [_ HxO]; revert HxO HxS; clear - LOR; cbn [outside]; intros HxO HxS; repeat split; try exact I; lia).
    lazymatch goal with MUx : munch _ ?ma ?mb |- cps _ (ASTA _ _ _ (eq (MS _ _ _ _ _ ?mb _))) _ =>
      kl_of_munch KL live MUx Σk mc fr ART0 FRS LVK LOW LOR;
      unfold hid in POBJ; apply (pix_obj_keep live0 ma mb pix v cv (keeps_live_sub live live0 ma mb LV0 KL)) in POBJ; hide POBJ;
      apply (numa_obj_keep live ma mb na (p_h v) arr (map ival_w ks) KL) in NOBJ; clear KL end.
    eapply cps_seq.
    { eapply NADDF with (lo := lo) (na := na) (cap := p_h v) (arr := arr) (vals := map ival_w ks) (v := ival_w loc').
      - exact FDO.
      - exact MST.
      - reflexivity.
      - reflexivity.
      - unfold freg_is, ival_w, fa0; apply freg_get_same; reflexivity.
      - lazymatch goal with |- numa_obj (rt_live RT ?S) _ _ _ _ _ => replace (rt_live RT S) with live by (symmetry; eqv) end; exact NOBJ.
      - rewrite length_map; lia.
      - lenv_tac.
      - unfold lres;
        lazymatch goal with |- context [rt_frames RT ?S] => replace (rt_frames RT S) with ((fr, 4%nat) :: frames) by (symmetry; eqv) end;
        lazymatch goal with |- context [rt_live RT ?S] => replace (rt_live RT S) with live by (symmetry; eqv) end;
        cbn [length]; unfold FRAMES_MAX, LIVE_MAX, GETPIXEL_COST in *; repeat split; [lia| exact LVB| lia| exact LVP]. }
    clear NOBJ.
    after_call RT AF.
    lazymatch goal with AGx : agree_on _ ?ma ?mb |- cps _ (ASTA _ _ _ (eq (MS _ _ _ _ _ ?mb _))) _ =>
      assert (KL0 : keeps_live live0 ma mb)
        by (apply (keeps_live_of_agree live0 _ ma mb AGx); intros b kk a Hb Ha; cbv beta;
            assert (ACL : aclient live0 ((fr, 4%nat) :: frames) spa a) by (right; right; left; exists b, kk; split; [exact Hb| lia]);
            pose proof (live_chunk_apart RT AF Σk mc [(arr, 4 * p_h v)] na 32 live0 live0 ((fr, 4%nat) :: frames) spa a ART0
                          ltac:(rewrite LVK, LVSH; reflexivity) ltac:(intros e He; apply in_or_app; right; exact He) FRS ltac:(unfold STACK_WIN; lia) ACL) as NAX;
            pose proof (live_chunk_apart RT AF Σk mc [] arr (4 * p_h v) ((na, 32) :: live0) live0 ((fr, 4%nat) :: frames) spa a ART0
                          ltac:(rewrite LVK, LVSH; reflexivity) ltac:(intros e He; right; exact He) FRS ltac:(unfold STACK_WIN; lia) ACL) as ARX;
            split; [ right; right; left; exists b, kk; split; [repeat match goal with E : rt_live _ _ = _ |- _ => rewrite E end; first [apply LV0; exact Hb | rewrite <- LVK; apply LV0; exact Hb] | lia]
                   | revert NAX ARX; clear; intros; cbn [outside]; repeat split; try exact I; lia ]);
      unfold hid in POBJ; apply (pix_obj_keep live0 ma mb pix v cv KL0) in POBJ; hide POBJ; clear KL0 end.
    lazymatch goal with H : numa_obj _ _ na _ arr (_ ++ _) |- _ => rename H into NOBJ end.
    lazymatch type of NOBJ with numa_obj (rt_live RT ?S) _ _ _ _ _ => replace (rt_live RT S) with live in NOBJ by (symmetry; eqv) | _ => idtac end.
    change [ival_w loc'] with (map ival_w [loc']) in NOBJ. rewrite <- map_app in NOBJ.
    fold_ag ltac:(fun Hx => destruct Hx as [Hx HxO]; split; [apply (aclient_mono _ _ spa _ _ _ _ Hx); [solve [live_sub_tac]| solve [frames_sub_tac]| lia] | revert HxO; clear; cbn [outside]; intros HxO; repeat split; try exact I; lia]).
    refresh RT AF. unfold shad, SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. park_disj.
    (* [comment removed for export] *)
    pwalk_to AF MST [(spa - 16, spa); (fr + 320, fr + 404); (fr / 8 + 2147450920, fr / 8 + 2147450931)] [0x1225e0; 0x121b1c].
    sx32_fix. swrap32_fix.
    assert (KS' : Z.of_nat (length (ks ++ [loc'])) = y + 1) by (rewrite length_app; cbn [length]; lia).
    assert (KSF' : Forall (fun q => loc_ok q /\ q <= p_w v - 1) (ks ++ [loc'])) by (apply Forall_app; split; [exact KSF| constructor; [unfold loc_ok, LOC_LO, LOC_HI; lia| constructor]]).
    destruct k as [|k'].
    + (* [comment removed for export] *)
      brT.
      cps_stop.
      art_now RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac| exact I]]]).
      lazymatch goal with AGFx : agree_on ?PFx _ ?mm, MUx : munch _ ?mm _ |- _ => is_var PFx; agf_munch AGFx MUx ltac:(fun Hx => pose proof (PFS _ Hx) as HxS; destruct Hx as [_ HxO]; revert HxO HxS; clear - LOR; cbn [outside]; intros HxO HxS; repeat split; try exact I; lia) end.
      lazymatch goal with Xw2 : rw_cells asegs _ (fr + 320) [C4 ?xw2], Xh2 : rw_cells asegs _ (fr + 336) [C4 ?xh2], Xv2 : rw_cells asegs _ (fr + 352) [C4 ?xv2],
                          Xw3 : rw_cells asegs _ (fr + 368) [C4 ?xw3], Xh3 : rw_cells asegs _ (fr + 384) [C4 ?xh3], Xv3 : rw_cells asegs _ (fr + 400) [C4 ?xv3],
                          Xvp : rw_cells asegs _ (fr + 656) [C4 ?xvp] |- cps _ (ASTA _ ?S _ _) _ =>
        apply cps_finish; intros c Hc; subst QF; cbv beta; exists S, loc', (ks ++ [loc']), xw2, xh2, xv2, xw3; exists xh3, xv3, xvp end.
      split.
      2: { split; [eqv|].
           split; [eqv|].
           split; [eqv|].
           unfold GETPIXEL_COST in *. repeat match goal with H : rt_credit _ _ = _ |- _ => rewrite H in * end. lia. }
      eapply (ASTA_conseq RT); [exact Hc|]; intros ms <-.
      eexists. do 19 eexists. split; [replace (y + 1) with (p_h v) by lia; reflexivity|].
      split; [split; [assumption| split; [assumption| split; [| assumption]]]|].
      { repeat match goal with H : wmono asegs _ _ |- _ => revert H end. clear. intros. eauto using wmono_trans. }
      split; [intros a Ha Ho; exact (AGF a (conj Ha Ho))|].
      split; [assumption|]. split; [assumption|].
      split; [exact NOBJ|].
      split; [rewrite KS'; lia|]. split; [exact KSF'|].
      repeat (split; [assumption|]). assumption.
    + (* [comment removed for export] *)
      brF.
      pwalk [0x1225e0; 0x121b1c].
      cps_stop.
      eapply cps_conseq; [ | intros c Hc; exact Hc | ].
      * eapply (IH (y + 1) loc').
        9: unfold hid in POBJ; exact POBJ.
        6: eqv.
        6: eqv.
        6: exact LVSH.
        1: clear - HK; lia.
        1: clear - HK HY0 HY1; lia.
        1: lia.
        1: exact FDO.
        1: exact MST.
        1: exact D1.
        1: exact VDATA.
        1: exact NOBJ.
        1: exact KS'.
        1: exact KSF'.
        1: eassumption.
        1: eassumption.
        1: eassumption.
        1: eassumption.
        1: eassumption.
        1: eassumption.
        1: eassumption.
        1: assumption.
        1: assumption.
        1: assumption.
        1: assumption.
        1: assumption.
        1: assumption.
        1: assumption.
        1: assumption.
        1: assumption.
        1: assumption.
        1: assumption.
        1: assumption.
        1: assumption.
        1: eassumption.
        1: repeat match goal with H : rt_sp0 _ _ = _ |- _ => rewrite H end; lia.
        1: lia.
        1: lia.
        1: exact SPA.
        1: repeat match goal with H : rt_sp0 _ _ = _ |- _ => rewrite H end; lia.
        1: exact FR0.
        1: exact FR64.
        1: repeat match goal with H : rt_sp0 _ _ = _ |- _ => rewrite H end; lia.
        1: lia.
        1: clear - FRSH; unfold parked in *; lia.
        1: exact FRB.
        1: exact LVB.
        1: unfold GETPIXEL_COST in *; repeat match goal with H : rt_credit _ _ = _ |- _ => rewrite H in * end;
           revert CRB CRW HY0 HY1 HL0 HL1; repeat match goal with Hc : context [rt_credit] |- _ => revert Hc end; match goal with H : 0 < p_w v |- _ => revert H end; clear; intros; nia.
        1: exact LVP.
      * intros c (Σ' & locf & ksf & xw2 & xh2 & xv2 & xw3 & xh3 & xv3 & xvp & HA & L1 & F1 & S1 & C1). subst QF; cbv beta.
        exists Σ', locf, ksf, xw2, xh2, xv2, xw3; exists xh3, xv3, xvp. split.
        2: { split; [rewrite L1; eqv|].
             split; [rewrite F1; eqv|].
             split; [rewrite S1; eqv|].
             unfold GETPIXEL_COST in *. repeat match goal with H : rt_credit _ _ = _ |- _ => rewrite H in * end.
             revert C1 CRW HY0 HY1 HL0 HL1; repeat match goal with Hc : context [rt_credit] |- _ => revert Hc end; match goal with H : 0 < p_w v |- _ => revert H end; clear; intros; nia. }
        eapply (ASTA_conseq RT); [exact HA|]. cbv beta. intros ms (m' & X).
        destruct X as (ra' & t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & s9' & F' & fc' & E & (A1 & A2 & A3 & A4) & P & R).
        exists m', ra', t0', t1', t2', a0', a1', a2', a3', a4', a5', a6', a7', t3', t4', t5', t6', s9', F', fc'.
        split; [exact E|]. split; [split; [exact A1| split; [exact A2| split; [| exact A4]]]|].
        { repeat match goal with H : wmono asegs _ _ |- _ => revert H end. clear. intros. eauto using wmono_trans. }
        split; [| exact R].
        intros a Ha Ho. rewrite (P a Ha Ho). exact (AGF a (conj Ha Ho)).

  - (* [comment removed for export] *)
    replace (sx32 (Z_to_bv 64 1)) with (Z_to_bv 64 1) by (apply bv_eq; vm_compute; reflexivity).
    match goal with H : ~ in_pix v loc y -> _ |- _ => assert (LOC0 : 0 <= loc) by (destruct (Z_lt_ge_dec loc 0) as [Hl|Hl]; [exfalso; specialize (H ltac:(unfold in_pix; lia)); discriminate | lia]) end.
    pwalk [e_pixGetPixel; 0x121b3c].
    cps_stop.
    art_now RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac| exact I]]]).
    lazymatch goal with AGFx : agree_on ?PFx _ ?mm, MUx : munch _ ?mm _ |- _ => is_var PFx; agf_munch AGFx MUx ltac:(fun Hx => pose proof (PFS _ Hx) as HxS; destruct Hx as [_ HxO]; revert HxO HxS; clear - LOR; cbn [outside]; intros HxO HxS; repeat split; try exact I; lia) end.
    lazymatch goal with MUx : munch _ ?ma ?mb |- cps _ (ASTA _ _ _ (eq (MS _ _ _ _ _ ?mb _))) _ =>
      kl_of_munch KL live MUx Σk mc fr ART0 FRS LVK LOW LOR;
      unfold hid in POBJ; apply (pix_obj_keep live0 ma mb pix v cv (keeps_live_sub live live0 ma mb LV0 KL)) in POBJ; hide POBJ;
      apply (numa_obj_keep live ma mb na (p_h v) arr (map ival_w ks) KL) in NOBJ; clear KL end.
    eapply cps_seq.
    { eapply (row_on RT AF GP GETPIX loc y) with (lo := lo) (v := v) (cv := cv) (live := live) (frames := frames).
      - clear - LOC0 HL1; lia.
      - clear - HY0 HY1; lia.
      - exact FDO.
      - exact MST.
      - eqv.
      - eqv.
      - unfold hid in POBJ; exact (pix_obj_mono live0 live _ pix v cv LV0 POBJ).
      - exact D1.
      - exact VDATA.
      - exact W3.
      - exact H3.
      - exact V3.
      - exact SHON.
      - exact SPL.
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
      - unfold GETPIXEL_COST in *; lia.
      - exact LVP. }
    after_call RT AF.
    lazymatch goal with AGx : agree_on _ ?ma ?mb |- cps _ (ASTA _ _ _ (eq (MS _ _ _ _ _ ?mb _))) _ =>
      kl_of_ag KL live AGx Σk mc fr ART0 FRS LVK LOW LOR;
      unfold hid in POBJ; apply (pix_obj_keep live0 ma mb pix v cv (keeps_live_sub live live0 ma mb LV0 KL)) in POBJ; hide POBJ;
      apply (numa_obj_keep live ma mb na (p_h v) arr (map ival_w ks) KL) in NOBJ; clear KL end.
    fold_ag ltac:(fun Hx => destruct Hx as [Hx HxO]; split; [apply (aclient_mono _ _ spa _ _ _ _ Hx); [solve [live_sub_tac]| solve [frames_sub_tac]| lia] | revert HxO; clear; cbn [outside]; intros HxO; repeat split; try exact I; lia]).
    lazymatch goal with H1 : loc - 1 <= ?l, H2 : ?l <= p_w v - 1 |- cps _ (ASTA _ _ _ (eq (MS (mkR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (Z_to_bv 64 ?l) _ _ _ _ _ _ _ _ _ _ _ _ _) _ _ _ _ _ _))) _ =>
      rename l into loc'; assert (HL' : -1 <= loc' <= p_w v - 1) by lia end.
    refresh RT AF. unfold shad, SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. park_disj.
    (* [comment removed for export] *)
    pwalk_to AF MST [(spa - 16, spa); (fr + 320, fr + 404); (fr / 8 + 2147450920, fr / 8 + 2147450931)] [e_numaAddNumber].
    at_call RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac| exact I]]])
                  ltac:(fun Hx => pose proof (PFS _ Hx) as HxS; destruct Hx as [_ HxO]; revert HxO HxS; clear - LOR; cbn [outside]; intros HxO HxS; repeat split; try exact I; lia).
    lazymatch goal with MUx : munch _ ?ma ?mb |- cps _ (ASTA _ _ _ (eq (MS _ _ _ _ _ ?mb _))) _ =>
      kl_of_munch KL live MUx Σk mc fr ART0 FRS LVK LOW LOR;
      unfold hid in POBJ; apply (pix_obj_keep live0 ma mb pix v cv (keeps_live_sub live live0 ma mb LV0 KL)) in POBJ; hide POBJ;
      apply (numa_obj_keep live ma mb na (p_h v) arr (map ival_w ks) KL) in NOBJ; clear KL end.
    eapply cps_seq.
    { eapply NADDF with (lo := lo) (na := na) (cap := p_h v) (arr := arr) (vals := map ival_w ks) (v := ival_w loc').
      - exact FDO.
      - exact MST.
      - reflexivity.
      - reflexivity.
      - unfold freg_is, ival_w, fa0; apply freg_get_same; reflexivity.
      - lazymatch goal with |- numa_obj (rt_live RT ?S) _ _ _ _ _ => replace (rt_live RT S) with live by (symmetry; eqv) end; exact NOBJ.
      - rewrite length_map; lia.
      - lenv_tac.
      - unfold lres;
        lazymatch goal with |- context [rt_frames RT ?S] => replace (rt_frames RT S) with ((fr, 4%nat) :: frames) by (symmetry; eqv) end;
        lazymatch goal with |- context [rt_live RT ?S] => replace (rt_live RT S) with live by (symmetry; eqv) end;
        cbn [length]; unfold FRAMES_MAX, LIVE_MAX, GETPIXEL_COST in *; repeat split; [lia| exact LVB| lia| exact LVP]. }
    clear NOBJ.
    after_call RT AF.
    lazymatch goal with AGx : agree_on _ ?ma ?mb |- cps _ (ASTA _ _ _ (eq (MS _ _ _ _ _ ?mb _))) _ =>
      assert (KL0 : keeps_live live0 ma mb)
        by (apply (keeps_live_of_agree live0 _ ma mb AGx); intros b kk a Hb Ha; cbv beta;
            assert (ACL : aclient live0 ((fr, 4%nat) :: frames) spa a) by (right; right; left; exists b, kk; split; [exact Hb| lia]);
            pose proof (live_chunk_apart RT AF Σk mc [(arr, 4 * p_h v)] na 32 live0 live0 ((fr, 4%nat) :: frames) spa a ART0
                          ltac:(rewrite LVK, LVSH; reflexivity) ltac:(intros e He; apply in_or_app; right; exact He) FRS ltac:(unfold STACK_WIN; lia) ACL) as NAX;
            pose proof (live_chunk_apart RT AF Σk mc [] arr (4 * p_h v) ((na, 32) :: live0) live0 ((fr, 4%nat) :: frames) spa a ART0
                          ltac:(rewrite LVK, LVSH; reflexivity) ltac:(intros e He; right; exact He) FRS ltac:(unfold STACK_WIN; lia) ACL) as ARX;
            split; [ right; right; left; exists b, kk; split; [repeat match goal with E : rt_live _ _ = _ |- _ => rewrite E end; first [apply LV0; exact Hb | rewrite <- LVK; apply LV0; exact Hb] | lia]
                   | revert NAX ARX; clear; intros; cbn [outside]; repeat split; try exact I; lia ]);
      unfold hid in POBJ; apply (pix_obj_keep live0 ma mb pix v cv KL0) in POBJ; hide POBJ; clear KL0 end.
    lazymatch goal with H : numa_obj _ _ na _ arr (_ ++ _) |- _ => rename H into NOBJ end.
    lazymatch type of NOBJ with numa_obj (rt_live RT ?S) _ _ _ _ _ => replace (rt_live RT S) with live in NOBJ by (symmetry; eqv) | _ => idtac end.
    change [ival_w loc'] with (map ival_w [loc']) in NOBJ. rewrite <- map_app in NOBJ.
    fold_ag ltac:(fun Hx => destruct Hx as [Hx HxO]; split; [apply (aclient_mono _ _ spa _ _ _ _ Hx); [solve [live_sub_tac]| solve [frames_sub_tac]| lia] | revert HxO; clear; cbn [outside]; intros HxO; repeat split; try exact I; lia]).
    refresh RT AF. unfold shad, SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. park_disj.
    (* [comment removed for export] *)
    pwalk_to AF MST [(spa - 16, spa); (fr + 320, fr + 404); (fr / 8 + 2147450920, fr / 8 + 2147450931)] [0x1225e0; 0x121b1c].
    sx32_fix. swrap32_fix.
    assert (KS' : Z.of_nat (length (ks ++ [loc'])) = y + 1) by (rewrite length_app; cbn [length]; lia).
    assert (KSF' : Forall (fun q => loc_ok q /\ q <= p_w v - 1) (ks ++ [loc'])) by (apply Forall_app; split; [exact KSF| constructor; [unfold loc_ok, LOC_LO, LOC_HI; lia| constructor]]).
    destruct k as [|k'].
    + (* [comment removed for export] *)
      brT.
      cps_stop.
      art_now RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac| exact I]]]).
      lazymatch goal with AGFx : agree_on ?PFx _ ?mm, MUx : munch _ ?mm _ |- _ => is_var PFx; agf_munch AGFx MUx ltac:(fun Hx => pose proof (PFS _ Hx) as HxS; destruct Hx as [_ HxO]; revert HxO HxS; clear - LOR; cbn [outside]; intros HxO HxS; repeat split; try exact I; lia) end.
      lazymatch goal with Xw2 : rw_cells asegs _ (fr + 320) [C4 ?xw2], Xh2 : rw_cells asegs _ (fr + 336) [C4 ?xh2], Xv2 : rw_cells asegs _ (fr + 352) [C4 ?xv2],
                          Xw3 : rw_cells asegs _ (fr + 368) [C4 ?xw3], Xh3 : rw_cells asegs _ (fr + 384) [C4 ?xh3], Xv3 : rw_cells asegs _ (fr + 400) [C4 ?xv3],
                          Xvp : rw_cells asegs _ (fr + 656) [C4 ?xvp] |- cps _ (ASTA _ ?S _ _) _ =>
        apply cps_finish; intros c Hc; subst QF; cbv beta; exists S, loc', (ks ++ [loc']), xw2, xh2, xv2, xw3; exists xh3, xv3, xvp end.
      split.
      2: { split; [eqv|].
           split; [eqv|].
           split; [eqv|].
           unfold GETPIXEL_COST in *. repeat match goal with H : rt_credit _ _ = _ |- _ => rewrite H in * end. lia. }
      eapply (ASTA_conseq RT); [exact Hc|]; intros ms <-.
      eexists. do 19 eexists. split; [replace (y + 1) with (p_h v) by lia; reflexivity|].
      split; [split; [assumption| split; [assumption| split; [| assumption]]]|].
      { repeat match goal with H : wmono asegs _ _ |- _ => revert H end. clear. intros. eauto using wmono_trans. }
      split; [intros a Ha Ho; exact (AGF a (conj Ha Ho))|].
      split; [assumption|]. split; [assumption|].
      split; [exact NOBJ|].
      split; [rewrite KS'; lia|]. split; [exact KSF'|].
      repeat (split; [assumption|]). assumption.
    + (* [comment removed for export] *)
      brF.
      pwalk [0x1225e0; 0x121b1c].
      cps_stop.
      eapply cps_conseq; [ | intros c Hc; exact Hc | ].
      * eapply (IH (y + 1) loc').
        9: unfold hid in POBJ; exact POBJ.
        6: eqv.
        6: eqv.
        6: exact LVSH.
        1: clear - HK; lia.
        1: clear - HK HY0 HY1; lia.
        1: lia.
        1: exact FDO.
        1: exact MST.
        1: exact D1.
        1: exact VDATA.
        1: exact NOBJ.
        1: exact KS'.
        1: exact KSF'.
        1: eassumption.
        1: eassumption.
        1: eassumption.
        1: eassumption.
        1: eassumption.
        1: eassumption.
        1: eassumption.
        1: assumption.
        1: assumption.
        1: assumption.
        1: assumption.
        1: assumption.
        1: assumption.
        1: assumption.
        1: assumption.
        1: assumption.
        1: assumption.
        1: assumption.
        1: assumption.
        1: assumption.
        1: eassumption.
        1: repeat match goal with H : rt_sp0 _ _ = _ |- _ => rewrite H end; lia.
        1: lia.
        1: lia.
        1: exact SPA.
        1: repeat match goal with H : rt_sp0 _ _ = _ |- _ => rewrite H end; lia.
        1: exact FR0.
        1: exact FR64.
        1: repeat match goal with H : rt_sp0 _ _ = _ |- _ => rewrite H end; lia.
        1: lia.
        1: clear - FRSH; unfold parked in *; lia.
        1: exact FRB.
        1: exact LVB.
        1: unfold GETPIXEL_COST in *; repeat match goal with H : rt_credit _ _ = _ |- _ => rewrite H in * end;
           revert CRB CRW HY0 HY1 HL0 HL1 LOC0; repeat match goal with Hc : context [rt_credit] |- _ => revert Hc end; match goal with H : 0 < p_w v |- _ => revert H end; clear; intros; nia.
        1: exact LVP.
      * intros c (Σ' & locf & ksf & xw2 & xh2 & xv2 & xw3 & xh3 & xv3 & xvp & HA & L1 & F1 & S1 & C1). subst QF; cbv beta.
        exists Σ', locf, ksf, xw2, xh2, xv2, xw3; exists xh3, xv3, xvp. split.
        2: { split; [rewrite L1; eqv|].
             split; [rewrite F1; eqv|].
             split; [rewrite S1; eqv|].
             unfold GETPIXEL_COST in *. repeat match goal with H : rt_credit _ _ = _ |- _ => rewrite H in * end.
             revert C1 CRW HY0 HY1 HL0 HL1 LOC0; repeat match goal with Hc : context [rt_credit] |- _ => revert Hc end; match goal with H : 0 < p_w v |- _ => revert H end; clear; intros; nia. }
        eapply (ASTA_conseq RT); [exact HA|]. cbv beta. intros ms (m' & X).
        destruct X as (ra' & t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & s9' & F' & fc' & E & (A1 & A2 & A3 & A4) & P & R).
        exists m', ra', t0', t1', t2', a0', a1', a2', a3', a4', a5', a6', a7', t3', t4', t5', t6', s9', F', fc'.
        split; [exact E|]. split; [split; [exact A1| split; [exact A2| split; [| exact A4]]]|].
        { repeat match goal with H : wmono asegs _ _ |- _ => revert H end. clear. intros. eauto using wmono_trans. }
        split; [| exact R].
        intros a Ha Ho. rewrite (P a Ha Ho). exact (AGF a (conj Ha Ho)).

Qed.
End ROW.
