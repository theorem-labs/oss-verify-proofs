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
  Lept_iface Lept_env LeptC_kit Lept_leaf LeptL_kit Lept_objkit Lept_gmax_defs Ed_iface Numa_kit Px_defs Px_defs2 Px_kit Px_bkit Px_rowb LeptB_guard LeptB_guard2 Ed_fpkit.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac guard_fix ::= try sx32_fix; repeat match goal with |- context [bv_unsigned (Z_to_bv 64 ?e)] => rewrite (unsigned_lit e) by lia end; swrap_fix; po_fix; al_fix; try mulh_fix.

Section ROW.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Hypothesis GP : rt_gaps RT.
Hypothesis GETPIX : pixGetPixel1_cps RT.
Hypothesis SCANOFF : pixGetLastOffPixelInRunR_cps RT.
Hypothesis SCANON : pixGetLastOnPixelInRunL_cps RT.
Hypothesis NADDF : numaAddNumber_fast_cps RT.

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

Lemma row_loop : forall (k : nat) (y loc : Z) (Σk : rts RT) PMc (mc : mem)
    (ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (gp s0w : word) (F : bvmap 5 word) (fc : bv 32)
    (spa fr pix na arr lo : Z) (v : pixv) (cv : cmapv) (live live0 : list (Z * Z)) (frames : list (Z * nat)) (ks : list Z) (vp : word),
  Z.of_nat k = p_h v - y -> 1 <= y <= p_h v - 1 -> -1 <= loc <= p_w v - 1 ->
  fdfs_only PMc -> mat_stable PMc ->
  rt_live RT Σk = live -> rt_frames RT Σk = (fr, 1%nat) :: frames -> live = (arr, 4 * p_h v) :: (na, 32) :: live0 ->
  pix_obj live0 mc pix v cv -> p_d v = 1 -> p_data v <> 0 ->
  numa_obj live mc na (p_h v) arr (map ival_w ks) -> Z.of_nat (length ks) = y -> Forall (fun q => loc_ok q /\ q <= p_w v - 1) ks ->
  rw_cells asegs mc (spa + 52) [C4 (Z_to_bv 64 loc)] ->
  rw_cells asegs mc (fr + 32) [C4 (Z_to_bv 64 (p_w v))] -> rw_cells asegs mc (fr + 48) [C4 (Z_to_bv 64 (p_h v))] ->
  rw_cells asegs mc (fr + 80) [C4 vp] ->
  rw_cells asegs mc (fr / 8 + 2147450890) [C1 (Z_to_bv 8 4)] ->
  LIBH mc -> io_ssp mc -> ART RT Σk mc -> mem_inv asegs mc -> stk asegs mc lo spa ->
  rt_sp0 RT Σk - STACK_WIN <= lo -> lo + LSTK 5 <= spa -> spa + 176 <= USTACK_TOP -> spa mod 16 = 0 -> spa + 160 <= rt_sp0 RT Σk ->
  0 < fr -> fr mod 64 = 0 -> fr + 128 <= rt_sp0 RT Σk - STACK_WIN -> SEGTOP_A <= fr -> (fr + 128 <= 0x7fff7000 \/ 0x10007fff8000 <= fr) ->
  Z.of_nat (length frames) + 3 <= Z.of_nat FRAMES_MAX -> Z.of_nat (length live) + 0 <= LIVE_MAX ->
  (p_h v - y) * (p_w v + 3) <= rt_credit RT Σk -> (forall p n, In (p, n) live -> 0 < n) ->
  cps asegs (ASTA RT Σk PMc (eq (MS (mkR ra (Z_to_bv 64 spa) gp (Z_to_bv 64 TP_A) t0 t1 t2 s0w (Z_to_bv 64 spa) a0 a1 a2 a3 a4 a5 a6 a7
                                        (Z_to_bv 64 fr) (Z_to_bv 64 fr) (Z_to_bv 64 na) (Z_to_bv 64 1) (Z_to_bv 64 pix) (Z_to_bv 64 (fr + 32))
                                        (Z_to_bv 64 (fr + 48)) (Z_to_bv 64 (fr + 80)) (Z_to_bv 64 y) (Z_to_bv 64 (fr / 8 + 2147450880)) t3 t4 t5 t6)
                                   F (Z_to_bv 64 0x12ccdc) (frm_clear fc) None mc (seg_rom asegs))))
    (fun c => exists (Σ' : rts RT) (loc' : Z) (ks' : list Z) (vp' : word),
       ASTA RT Σ' PMc (fun ms => exists (m' : mem) (ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (F' : bvmap 5 word) (fc' : bv 32),
          ms = MS (mkR ra' (Z_to_bv 64 spa) gp (Z_to_bv 64 TP_A) t0' t1' t2' s0w (Z_to_bv 64 spa) a0' a1' a2' a3' a4' a5' a6' a7'
                      (Z_to_bv 64 fr) (Z_to_bv 64 fr) (Z_to_bv 64 na) (Z_to_bv 64 1) (Z_to_bv 64 pix) (Z_to_bv 64 (fr + 32))
                      (Z_to_bv 64 (fr + 48)) (Z_to_bv 64 (fr + 80)) (Z_to_bv 64 (p_h v)) (Z_to_bv 64 (fr / 8 + 2147450880)) t3' t4' t5' t6')
                 F' (Z_to_bv 64 0x12cfbc) (frm_clear fc') None m' (seg_rom asegs)
          /\ rt_after RT Σ' spa lo mc m'
          /\ rt_pres_fp live ((fr, 1%nat) :: frames) spa
               [(na, na + 32); (arr, arr + 4 * p_h v); (fr + 80, fr + 84); (spa + 52, spa + 56)] mc m'
          /\ LIBH m' /\ io_ssp m'
          /\ numa_obj live m' na (p_h v) arr (map ival_w ks') /\ Z.of_nat (length ks') = p_h v /\ Forall (fun q => loc_ok q /\ q <= p_w v - 1) ks'
          /\ rw_cells asegs m' (spa + 52) [C4 (Z_to_bv 64 loc')]
          /\ rw_cells asegs m' (fr + 80) [C4 vp']) c
       /\ rt_live RT Σ' = live /\ rt_frames RT Σ' = (fr, 1%nat) :: frames /\ rt_sp0 RT Σ' = rt_sp0 RT Σk
       /\ rt_credit RT Σk - (p_h v - y) * (p_w v + 3) <= rt_credit RT Σ').
Proof using AF GP GETPIX SCANOFF SCANON NADDF.
  induction k as [|k IH]; intros y loc Σk PMc mc ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 gp s0w F fc spa fr pix na arr lo v cv live live0 frames ks vp
    HK HY HL FDO MST LVK FRS LVSH POBJ D1 VDATA NOBJ KS KSF LOCC FW FH VALP SH10
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
  set (PF := fun a => aclient live ((fr, 1%nat) :: frames) spa a /\ outside [(na, na + 32); (arr, arr + 4 * p_h v); (fr + 80, fr + 84); (spa + 52, spa + 56)] a).
  pose proof (agree_refl PF mc) as AGF.
  assert (PFS : forall a, PF a -> spa <= a \/ a < lo).
  { intros a [Ha _]. destruct (aclient_split RT AF Σk mc spa a ART0) as [H|H]; [rewrite LVK, FRS; exact Ha| left; exact H| right; unfold STACK_WIN in H; lia]. }
  pose proof POBJ as (PXC & (PIN & PX0 & PX16 & _) & (HD1 & HW1 & HH1 & HWPL & HRS) & PDATA & _).
  destruct PDATA as [DZ|((DIN & D0 & D16 & DSZ) & DNE)]; [contradiction|].
  pose proof (LV0 _ PIN) as PINL. pose proof (LV0 _ DIN) as DINL.
  clear PXC.
  hide POBJ.
  pose proof (numa_obj_facts _ _ _ _ _ _ NOBJ) as (NLEN & NCAP & NA0 & NA16 & AR0 & AR16 & INNA & INAR & NANE).
  rewrite length_map in NLEN.
  assert (CRW : p_w v + 3 <= (p_h v - y) * (p_w v + 3)) by (clear - HY0 HY1 HW1; nia).
  chunk_facts RT AF GP pix 64. chunk_facts RT AF GP (p_data v) (rsize v). unfold rsize in *.
  chunk_facts RT AF GP na 32. chunk_facts RT AF GP arr (4 * p_h v).
  fframe_chunk RT AF fr 1%nat 128 pix 64. fframe_chunk RT AF fr 1%nat 128 (p_data v) (4 * (p_wpl v * p_h v)).
  fframe_chunk RT AF fr 1%nat 128 na 32. fframe_chunk RT AF fr 1%nat 128 arr (4 * p_h v).
  refresh RT AF. unfold shad, SHB in *. park_disj.
  (* [comment removed for export] *)
  eapply cps_seq.
  { eapply (row_body RT AF GP GETPIX SCANOFF SCANON loc y) with (lo := lo) (v := v) (cv := cv) (live := live) (frames := frames) (vp := vp).
    - lia.
    - lia.
    - exact FDO.
    - exact MST.
    - exact LVK.
    - exact FRS.
    - unfold hid in POBJ; exact (pix_obj_mono live0 live mc pix v cv LV0 POBJ).
    - exact D1.
    - exact VDATA.
    - exact LOCC.
    - exact FW.
    - exact VALP.
    - exact SH10.
    - exact LH.
    - exact SSP.
    - exact ART0.
    - exact MI.
    - exact ST.
    - unfold STACK_WIN; lia.
    - unfold LSTK, RT_STACK; lia.
    - unfold USTACK_TOP; lia.
    - exact SPA.
    - lia.
    - exact FR0.
    - exact FR64.
    - unfold STACK_WIN; lia.
    - unfold SEGTOP_A; lia.
    - exact FRSH.
    - exact FRB.
    - exact LVB.
    - lia.
    - exact LVP. }
  (* [comment removed for export] *)
  after_call RT AF.
  lazymatch goal with AGx : agree_on _ mc ?m1 |- _ =>
      kl_of_ag KL live AGx Σk mc fr ART0 FRS LVK LOW LOR;
      unfold hid in POBJ; apply (pix_obj_keep live0 mc m1 pix v cv (keeps_live_sub live live0 mc m1 LV0 KL)) in POBJ; hide POBJ;
      apply (numa_obj_keep live mc m1 na (p_h v) arr (map ival_w ks) KL) in NOBJ; clear KL end.
  fold_ag ltac:(fun Hx => destruct Hx as [Hx HxO]; split; [apply (aclient_mono _ _ spa _ _ _ _ Hx); [solve [live_sub_tac]| solve [frames_sub_tac]| lia] | revert HxO; clear; cbn [outside]; intros HxO; repeat split; try exact I; lia]).
  lazymatch goal with H1 : -1 <= ?l, H2 : ?l <= p_w v - 1, HC : rw_cells asegs _ (spa + 52) [C4 (Z_to_bv 64 ?l)] |- _ => rename l into loc'; rename H1 into HL0'; rename H2 into HL1' end.
  refresh RT AF. unfold shad, SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. park_disj.
  walk_to AF MST [(spa + 52, spa + 56)] [0x12ccc4; e_numaAddNumber].
  rewrite ?(sx32_s32 loc') by lia.
  pwalk [e_numaAddNumber].
  at_call RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| exact I])
                  ltac:(fun Hx => destruct Hx as [_ HxO]; revert HxO; clear; cbn [outside]; intros HxO; repeat split; try exact I; lia).
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
          lazymatch goal with |- context [rt_frames RT ?S] => replace (rt_frames RT S) with ((fr, 1%nat) :: frames) by (symmetry; eqv) end;
          lazymatch goal with |- context [rt_live RT ?S] => replace (rt_live RT S) with live by (symmetry; eqv) end;
          cbn [length]; unfold FRAMES_MAX, LIVE_MAX, GETPIXEL_COST in *; repeat split; [lia| exact LVB| lia| exact LVP].
  }
  clear NOBJ.
  after_call RT AF.
  lazymatch goal with AGx : agree_on _ ?ma ?mb |- cps _ (ASTA _ _ _ (eq (MS _ _ _ _ _ ?mb _))) _ =>
        assert (KL0 : keeps_live live0 ma mb)
          by (apply (keeps_live_of_agree live0 _ ma mb AGx); intros b kk a Hb Ha; cbv beta;
              assert (ACL : aclient live0 ((fr, 1%nat) :: frames) spa a) by (right; right; left; exists b, kk; split; [exact Hb| lia]);
              pose proof (live_chunk_apart RT AF Σk mc [(arr, 4 * p_h v)] na 32 live0 live0 ((fr, 1%nat) :: frames) spa a ART0
                            ltac:(rewrite LVK, LVSH; reflexivity) ltac:(intros e He; apply in_or_app; right; exact He) FRS ltac:(unfold STACK_WIN; lia) ACL) as NAX;
              pose proof (live_chunk_apart RT AF Σk mc [] arr (4 * p_h v) ((na, 32) :: live0) live0 ((fr, 1%nat) :: frames) spa a ART0
                            ltac:(rewrite LVK, LVSH; reflexivity) ltac:(intros e He; right; exact He) FRS ltac:(unfold STACK_WIN; lia) ACL) as ARX;
              split; [ right; right; left; exists b, kk; split; [repeat match goal with E : rt_live _ _ = _ |- _ => rewrite E end; first [apply LV0; exact Hb | rewrite <- LVK; apply LV0; exact Hb] | lia]
                     | revert NAX ARX; clear; intros; cbn [outside]; repeat split; try exact I; lia ]);
        unfold hid in POBJ; apply (pix_obj_keep live0 ma mb pix v cv KL0) in POBJ; hide POBJ; clear KL0 end.
  lazymatch goal with H : numa_obj _ _ na _ arr (_ ++ _) |- _ => rename H into NOBJ end.
  lazymatch type of NOBJ with numa_obj (rt_live RT ?S) _ _ _ _ _ => replace (rt_live RT S) with live in NOBJ by (symmetry; eqv) | _ => idtac end.
  change [ival_w loc'] with (map ival_w [loc']) in NOBJ. rewrite <- map_app in NOBJ.
  fold_ag ltac:(fun Hx => destruct Hx as [Hx HxO]; split; [apply (aclient_mono _ _ spa _ _ _ _ Hx); [solve [live_sub_tac]| solve [frames_sub_tac]| lia] | revert HxO; clear; cbn [outside]; intros HxO; repeat split; try exact I; lia]).
  refresh RT AF. unfold shad, SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. park_disj.
  walk_to AF MST [(spa + 52, spa + 56)] [0x12cfbc; 0x12ccdc].
  (* [comment removed for export] *)
  assert (KS' : Z.of_nat (length (ks ++ [loc'])) = y + 1) by (rewrite length_app; cbn [length]; lia).
  assert (KSF' : Forall (fun q => loc_ok q /\ q <= p_w v - 1) (ks ++ [loc'])) by (apply Forall_app; split; [exact KSF| constructor; [unfold loc_ok, LOC_LO, LOC_HI; lia| constructor]]).
  destruct k as [|k'].
  + brT.
  cps_stop.
  art_now RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| exact I]).
  lazymatch goal with AGFx : agree_on ?PFx _ ?mm, MUx : munch _ ?mm _ |- _ => is_var PFx; agf_munch AGFx MUx ltac:(fun Hx => destruct Hx as [_ HxO]; revert HxO; clear; cbn [outside]; intros HxO; repeat split; try exact I; lia) end.
  lazymatch goal with Xvp : rw_cells asegs _ (fr + 80) [C4 ?xvp] |- cps _ (ASTA _ ?S _ _) _ =>
          apply cps_finish; intros c Hc; subst QF; cbv beta; exists S, loc', (ks ++ [loc']), xvp end.
  split.
  2: {
  split; [eqv|].
  split; [eqv|].
  split; [eqv|].
  unfold GETPIXEL_COST in *. repeat match goal with H : rt_credit _ _ = _ |- _ => rewrite H in * end. lia.
  }
  eapply (ASTA_conseq RT); [exact Hc|]; intros ms <-.
  eexists. do 18 eexists. split; [replace (y + 1) with (p_h v) by lia; reflexivity|].
  split; [split; [assumption| split; [assumption| split; [| assumption]]]|].
  { repeat match goal with H : wmono asegs _ _ |- _ => revert H end. clear. intros. eauto using wmono_trans.
  }
  split; [intros a Ha Ho; exact (AGF a (conj Ha Ho))|].
  split; [assumption|]. split; [assumption|].
  split; [exact NOBJ|].
  split; [rewrite KS'; lia|]. split; [exact KSF'|].
  split; [assumption|]. assumption.
  + brF.
  cps_stop.
  eapply cps_conseq; [ | intros c Hc; exact Hc | ].
  * eapply (IH (y + 1) loc') with (lo := lo) (v := v) (cv := cv) (live := live) (live0 := live0) (frames := frames) (ks := ks ++ [loc']) (na := na) (arr := arr) (fr := fr) (spa := spa) (pix := pix).
  -- clear - HK; lia.
  -- clear - HK HY0 HY1; lia.
  -- lia.
  -- exact FDO.
  -- exact MST.
  -- eqv.
  -- eqv.
  -- exact LVSH.
  -- unfold hid in POBJ; exact POBJ.
  -- exact D1.
  -- exact VDATA.
  -- exact NOBJ.
  -- exact KS'.
  -- exact KSF'.
  -- eassumption.
  -- eassumption.
  -- eassumption.
  -- eassumption.
  -- eassumption.
  -- assumption.
  -- assumption.
  -- assumption.
  -- assumption.
  -- eassumption.
  -- repeat match goal with H : rt_sp0 _ _ = _ |- _ => rewrite H end; unfold STACK_WIN; lia.
  -- unfold LSTK, RT_STACK; lia.
  -- unfold USTACK_TOP; lia.
  -- exact SPA.
  -- repeat match goal with H : rt_sp0 _ _ = _ |- _ => rewrite H end; lia.
  -- exact FR0.
  -- exact FR64.
  -- repeat match goal with H : rt_sp0 _ _ = _ |- _ => rewrite H end; unfold STACK_WIN; lia.
  -- unfold SEGTOP_A; lia.
  -- clear - FRSH; unfold parked in *; lia.
  -- exact FRB.
  -- exact LVB.
  -- unfold GETPIXEL_COST in *; repeat match goal with H : rt_credit _ _ = _ |- _ => rewrite H in * end;
             revert CRB CRW HY0 HY1; repeat match goal with Hc : context [rt_credit] |- _ => revert Hc end; match goal with H : 0 < p_w v |- _ => revert H end; clear; intros; nia.
  -- exact LVP.
  * 
    intros c (Σ' & locf & ksf & xvp & HA & L1 & F1 & S1 & C1). subst QF; cbv beta.
    exists Σ', locf, ksf, xvp. split.
    2: {
    split; [rewrite L1; eqv|].
    split; [rewrite F1; eqv|].
    split; [rewrite S1; eqv|].
    unfold GETPIXEL_COST in *. repeat match goal with H : rt_credit _ _ = _ |- _ => rewrite H in * end.
    revert C1 CRW HY0 HY1; repeat match goal with Hc : context [rt_credit] |- _ => revert Hc end; match goal with H : 0 < p_w v |- _ => revert H end; clear; intros; nia.
    }
    eapply (ASTA_conseq RT); [exact HA|]. cbv beta. intros ms (m' & X).
    destruct X as (ra' & t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & F' & fc' & E & (A1 & A2 & A3 & A4) & P & R).
    exists m', ra', t0', t1', t2', a0', a1', a2', a3', a4', a5', a6', a7', t3', t4', t5', t6', F', fc'.
    split; [exact E|]. split; [split; [exact A1| split; [exact A2| split; [| exact A4]]]|].
    { repeat match goal with H : wmono asegs _ _ |- _ => revert H end. clear. intros. eauto using wmono_trans.
    }
    split; [| exact R].
    intros a Ha Ho. rewrite (P a Ha Ho). exact (AGF a (conj Ha Ho)).
Qed.
End ROW.
