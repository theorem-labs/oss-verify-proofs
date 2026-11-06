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
  Lept_iface Lept_env LeptC_kit Lept_leaf LeptL_kit Lept_objkit Lept_gmax_defs Ed_iface Px_defs Px_kit.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.

Section SON.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Hypothesis GP : rt_gaps RT.
Hypothesis GETPIX : pixGetPixel1_cps RT.

Lemma son_loop : forall (k : nat) (x : Z) (Σk : rts RT) PMc (mc : mem)
    (ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (gp s0w s5w s9w s10w : word) (F : bvmap 5 word) (fc : bv 32)
    (spa fr pix y lo : Z) (v : pixv) (cv : cmapv) (live : list (Z * Z)) (frames : list (Z * nat)) (old : word),
  Z.of_nat k = p_w v - x -> 0 <= x <= p_w v - 1 -> 0 <= y < p_h v ->
  fdfs_only PMc -> mat_stable PMc ->
  rt_live RT Σk = live -> rt_frames RT Σk = (fr, 4%nat) :: frames ->
  pix_obj live mc pix v cv -> p_d v = 1 -> p_data v <> 0 ->
  rw_cells asegs mc (fr + 400) [C4 old] ->
  rw_cells asegs mc (fr / 8 + 2147450926) [C1 (Z_to_bv 8 4); C1 (Z_to_bv 8 (-14)); C1 (Z_to_bv 8 4); C1 (Z_to_bv 8 (-14)); C1 (Z_to_bv 8 4)] ->
  rw_cells asegs mc (fr + 368) [C4 (Z_to_bv 64 (p_w v))] ->
  LIBH mc -> io_ssp mc -> ART RT Σk mc -> mem_inv asegs mc -> stk asegs mc lo spa ->
  rt_sp0 RT Σk - STACK_WIN <= lo -> lo + LSTK 4 <= spa -> spa + 272 <= USTACK_TOP -> spa mod 16 = 0 -> spa + 256 <= rt_sp0 RT Σk ->
  0 < fr -> fr mod 64 = 0 -> fr + 1024 <= rt_sp0 RT Σk - STACK_WIN -> SEGTOP_A <= fr -> (fr + 1024 <= 0x7fff7000 \/ 0x10007fff8000 <= fr) ->
  Z.of_nat (length frames) + 2 <= Z.of_nat FRAMES_MAX -> Z.of_nat (length live) + 0 <= LIVE_MAX -> p_w v - x <= rt_credit RT Σk ->
  (forall p n, In (p, n) live -> 0 < n) ->
  cps asegs (ASTA RT Σk PMc (eq (MS (mkR ra (Z_to_bv 64 spa) gp (Z_to_bv 64 TP_A) t0 t1 t2 s0w (Z_to_bv 64 spa) a0 a1 a2 a3 a4 a5 a6 a7
                                        (Z_to_bv 64 x) (Z_to_bv 64 (fr + 368)) (Z_to_bv 64 (fr / 8 + 2147450880)) s5w (Z_to_bv 64 pix) (Z_to_bv 64 1)
                                        (Z_to_bv 64 y) s9w s10w (Z_to_bv 64 (fr + 400)) t3 t4 t5 t6)
                                   F (Z_to_bv 64 0x121b74) (frm_clear fc) None mc (seg_rom asegs))))
    (fun c => exists (Σ' : rts RT) (loc vb : Z),
       ASTA RT Σ' PMc (fun ms => exists (m' : mem) (ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (F' : bvmap 5 word) (fc' : bv 32),
          ms = MS (mkR ra' (Z_to_bv 64 spa) gp (Z_to_bv 64 TP_A) t0' t1' t2' s0w (Z_to_bv 64 spa) a0' a1' a2' a3' a4' a5' a6' a7'
                      (Z_to_bv 64 loc) (Z_to_bv 64 (fr + 368)) (Z_to_bv 64 (fr / 8 + 2147450880)) s5w (Z_to_bv 64 pix) (Z_to_bv 64 1)
                      (Z_to_bv 64 y) s9w s10w (Z_to_bv 64 (fr + 400)) t3' t4' t5' t6')
                 F' (Z_to_bv 64 0x121b00) (frm_clear fc') None m' (seg_rom asegs)
          /\ rt_after RT Σ' spa lo mc m'
          /\ rt_pres_fp live ((fr, 4%nat) :: frames) spa [(fr + 400, fr + 404); (fr / 8 + 2147450880 + 46, fr / 8 + 2147450880 + 51)] mc m'
          /\ LIBH m' /\ io_ssp m'
          /\ rw_cells asegs m' (fr + 400) [C4 (Z_to_bv 64 vb)]
          /\ rw_cells asegs m' (fr / 8 + 2147450926) [C1 (Z_to_bv 8 (-8)); C1 (Z_to_bv 8 (-14)); C1 (Z_to_bv 8 (-8)); C1 (Z_to_bv 8 (-14)); C1 (Z_to_bv 8 (-8))]
          /\ x - 1 <= loc <= p_w v - 1) c
       /\ rt_live RT Σ' = live /\ rt_frames RT Σ' = (fr, 4%nat) :: frames /\ rt_sp0 RT Σ' = rt_sp0 RT Σk
       /\ rt_credit RT Σk - (p_w v - x) <= rt_credit RT Σ').
Proof using AF GP GETPIX.
  induction k as [|k IH]; intros x Σk PMc mc ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 gp s0w s5w s9w s10w F fc spa fr pix y lo v cv live frames old
    HK HJ HY FDO MST LVK FRS POBJ D1 VDATA VALC SH5 FW LH SSP ART0 MI ST LOW LOR SPT SPA SPB FR0 FR64 FRHI FRSEG FRSH FRB LVB CRB LVP.
  { exfalso; lia. }
  destruct HJ as [HJ0 HJ1].
  unfold LSTK, STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *.
  destruct (af_client_consts RT AF Σk mc ART0) as (G1 & G2 & G3 & G4).
  pose proof (af_sp0_range RT AF Σk mc ART0) as SP0R. pose proof (af_sp0_win RT AF Σk mc ART0) as SP0W.
  unfold g_GOT_shadow_offset_cell, g_shadow_memory_dynamic_address, g_GOT_detect_uar, g_detect_stack_use_after_return in *.
  unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A, SHB in *.
  lazymatch goal with |- cps _ _ ?Q => set (QF := Q) end.
  pose proof ST as (STa & STb & _).
  set (PF := fun a => aclient live ((fr, 4%nat) :: frames) spa a /\ outside [(fr + 400, fr + 404); (fr / 8 + 2147450880 + 46, fr / 8 + 2147450880 + 51)] a).
  pose proof (agree_refl PF mc) as AGF.
  assert (PFS : forall a, PF a -> spa <= a \/ a < lo).
  { intros a [Ha _]. destruct (aclient_split RT AF Σk mc spa a ART0) as [H|H]; [rewrite LVK, FRS; exact Ha| left; exact H| right; unfold STACK_WIN in H; lia]. }
  pose proof POBJ as (PXC & (PIN & PX0 & PX16 & _) & (HD1 & HW1 & HH1 & HWPL & HRS) & PDATA & _).
  destruct PDATA as [DZ|((DIN & D0 & D16 & DSZ) & DNE)]; [contradiction|].
  hide POBJ.
  chunk_facts RT AF GP pix 64. chunk_facts RT AF GP (p_data v) (rsize v). unfold rsize in *.
  fframe_chunk RT AF fr 4%nat 1024 pix 64. fframe_chunk RT AF fr 4%nat 1024 (p_data v) (4 * (p_wpl v * p_h v)).
  refresh RT AF. unfold shad, SHB in *. park_disj.
  (* [comment removed for export] *)
  walk_to AF MST [(fr + 400, fr + 404); (fr / 8 + 2147450880 + 46, fr / 8 + 2147450880 + 51)] [e_pixGetPixel].
  at_call RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac| exact I]])
                ltac:(fun Hx => destruct Hx as [_ HxO]; exact HxO).
  swrap32_fix.
  eapply cps_seq.
  { eapply GETPIX with (lo := lo) (pix := pix) (pval := fr + 400) (x := x) (y := y) (v := v) (cv := cv) (old := old).
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
      exists fr, 4%nat. rewrite FRS. change (fs_size 4) with 1024.
      split; [left; reflexivity|]. split; [lia|]. split; [lia|]. split; [clear - FR64; Z.div_mod_to_equations; lia|]. split; [lia|]. split; [lia|].
      replace (shad (fr + 400)) with (fr / 8 + 2147450930) by (unfold shad, SHB; clear - FR64; Z.div_mod_to_equations; lia).
      pose proof SH5 as T; split_at T 4%nat T2; destruct T2 as [[_ B] _]; cbn [cells_bytes cbytes app] in B; change (ushadow 4) with [Z_to_bv 8 4]; exact B.
    - exact VALC.
    - lenv_tac.
    - unfold lres, GETPIXEL_COST; rewrite FRS, LVK; cbn [length]; unfold FRAMES_MAX, LIVE_MAX in *; repeat split; [lia| lia| lia| exact LVP]. }
  after_call RT AF.
  (* [comment removed for export] *)
  lazymatch goal with AGx : agree_on _ mc ?m1 |- _ =>
    assert (KL : keeps_live live mc m1)
      by (intros b kk Hb a Ha; apply AGx; pose proof (af_frames_range RT AF Σk mc fr 4%nat ART0 ltac:(rewrite FRS; left; reflexivity)) as (_ & _ & _ & R);
          specialize (R b kk ltac:(rewrite LVK; exact Hb)); change (fs_size 4) with 1024 in R;
          split; [right; right; left; exists b, kk; split; [repeat match goal with E : rt_live _ _ = _ |- _ => rewrite E end; exact Hb| lia]| cbn [outside]; split; [lia| exact I]]);
    unfold hid in POBJ; apply (pix_obj_keep live mc m1 pix v cv KL) in POBJ; hide POBJ; clear KL end.
  fold_ag ltac:(fun Hx => destruct Hx as [Hx HxO]; split; [apply (aclient_mono _ _ spa _ _ _ _ Hx); [solve [live_sub_tac]| solve [frames_sub_tac]| lia] | revert HxO; clear; cbn [outside]; intros HxO; repeat split; try exact I; lia]).
  refresh RT AF. unfold shad, SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. park_disj.
  (* [comment removed for export] *)
  walk_to AF MST [(fr + 400, fr + 404); (fr / 8 + 2147450880 + 46, fr / 8 + 2147450880 + 51)] [e_pixGetPixel; 0x121b74; 0x121b00].
  match goal with B : ?b = 0 \/ ?b = 1 |- _ => destruct B as [EB|EB]; rewrite EB in * end.
  - (* [comment removed for export] *)
    replace (sx32 (Z_to_bv 64 0)) with (Z_to_bv 64 0) by (apply bv_eq; vm_compute; reflexivity).
    awalk [e_pixGetPixel; 0x121b74; 0x121b00].
    swrap32_fix.
    cps_stop.
    art_now RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac| exact I]]).
    lazymatch goal with AGFx : agree_on ?PFx _ ?mm, MUx : munch _ ?mm _ |- _ => is_var PFx; agf_munch AGFx MUx ltac:(fun Hx => destruct Hx as [_ HxO]; exact HxO) end.
    apply cps_finish; intros c Hc; subst QF; cbv beta.
    lazymatch type of Hc with ASTA RT ?S _ _ _ => exists S, (x - 1), 0 end.
    split.
    2: { split; [repeat match goal with H : rt_live _ _ = _ |- _ => rewrite H end; reflexivity|].
         split; [repeat match goal with H : rt_frames _ _ = _ |- _ => rewrite H end; reflexivity|].
         split; [repeat match goal with H : rt_sp0 _ _ = _ |- _ => rewrite H end; reflexivity|].
         unfold GETPIXEL_COST in *; lia. }
    eapply (ASTA_conseq RT); [exact Hc|]; intros ms <-.
    eexists. do 18 eexists. split; [replace (x + -1) with (x - 1) by lia; reflexivity|].
    split; [split; [assumption| split; [assumption| split; [| assumption]]]|].
    { repeat match goal with H : wmono asegs _ _ |- _ => revert H end. clear. intros. eauto using wmono_trans. }
    split; [intros a Ha Ho; exact (AGF a (conj Ha Ho))|].
    split; [assumption|]. split; [assumption|].
    split; [assumption|].
    split; [exact SH5|].
    split; lia.
  - (* [comment removed for export] *)
    replace (sx32 (Z_to_bv 64 1)) with (Z_to_bv 64 1) by (apply bv_eq; vm_compute; reflexivity).
    awalk [e_pixGetPixel; 0x121b74; 0x121b00; 0x121aec].
    sx32_fix. swrap32_fix.
    destruct k as [|k'].
    + (* [comment removed for export] *)
      brF. awalk [e_pixGetPixel; 0x121b74; 0x121b00].
      swrap32_fix.
      cps_stop.
      art_now RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac| exact I]]).
      lazymatch goal with AGFx : agree_on ?PFx _ ?mm, MUx : munch _ ?mm _ |- _ => is_var PFx; agf_munch AGFx MUx ltac:(fun Hx => destruct Hx as [_ HxO]; exact HxO) end.
      apply cps_finish; intros c Hc; subst QF; cbv beta.
      lazymatch type of Hc with ASTA RT ?S _ _ _ => exists S, (p_w v - 1), 1 end.
      split.
      2: { split; [repeat match goal with H : rt_live _ _ = _ |- _ => rewrite H end; reflexivity|].
           split; [repeat match goal with H : rt_frames _ _ = _ |- _ => rewrite H end; reflexivity|].
           split; [repeat match goal with H : rt_sp0 _ _ = _ |- _ => rewrite H end; reflexivity|].
           unfold GETPIXEL_COST in *; lia. }
      eapply (ASTA_conseq RT); [exact Hc|]; intros ms <-.
      eexists. do 18 eexists. split; [first [replace (x + 0) with (p_w v - 1) by lia | replace (x + 1 + -1) with (p_w v - 1) by lia]; reflexivity|].
      split; [split; [assumption| split; [assumption| split; [| assumption]]]|].
      { repeat match goal with H : wmono asegs _ _ |- _ => revert H end. clear. intros. eauto using wmono_trans. }
      split; [intros a Ha Ho; exact (AGF a (conj Ha Ho))|].
      split; [assumption|]. split; [assumption|].
      split; [assumption|].
      split; [exact SH5|].
      split; lia.
    + (* [comment removed for export] *)
      brT.
      cps_stop.
      eapply cps_conseq; [ | intros c Hc; exact Hc | ].
      * eapply (IH (x + 1)).
        8: unfold hid in POBJ; exact POBJ.
        6: transitivity (rt_live RT Σk); [assumption | exact LVK].
        6: transitivity (rt_frames RT Σk); [assumption | exact FRS].
        1: clear - HK; lia.
        1: clear - HK HJ0 HJ1; lia.
        1: lia.
        1: exact FDO.
        1: exact MST.
        1: exact D1.
        1: exact VDATA.
        1: eassumption.
        1: exact SH5.
        1: exact FW.
        1: assumption.
        1: assumption.
        1: assumption.
        1: assumption.
        1: eassumption.
        1: repeat match goal with H : rt_sp0 _ _ = _ |- _ => rewrite H end; lia.
        1: lia.
        1: lia.
        1: lia.
        1: repeat match goal with H : rt_sp0 _ _ = _ |- _ => rewrite H end; lia.
        1: lia.
        1: lia.
        1: repeat match goal with H : rt_sp0 _ _ = _ |- _ => rewrite H end; lia.
        1: lia.
        1: clear - FRSH; unfold parked in *; lia.
        1: lia.
        1: exact LVB.
        1: unfold GETPIXEL_COST in *; lia.
        exact LVP.
      * intros c (Σ' & loc & vb & HA & L1 & F1 & S1 & C1). subst QF; cbv beta.
        exists Σ', loc, vb. split.
        2: { split; [exact L1|]. split; [exact F1|]. split; [rewrite S1; repeat match goal with H : rt_sp0 _ _ = _ |- _ => rewrite H end; reflexivity|].
             unfold GETPIXEL_COST in *. lia. }
        eapply (ASTA_conseq RT); [exact HA|]. cbv beta. intros ms (m' & X).
        destruct X as (ra' & t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & F' & fc' & E & (A1 & A2 & A3 & A4) & P & R1 & R2 & R3 & R4 & LR).
        exists m', ra', t0', t1', t2', a0', a1', a2', a3', a4', a5', a6', a7', t3', t4', t5', t6', F', fc'.
        split; [exact E|]. split; [split; [exact A1| split; [exact A2| split; [| exact A4]]]|].
        { repeat match goal with H : wmono asegs _ _ |- _ => revert H end. clear. intros. eauto using wmono_trans. }
        split; [| split; [exact R1| split; [exact R2| split; [exact R3| split; [exact R4| lia]]]]].
        intros a Ha Ho. rewrite (P a Ha Ho). exact (AGF a (conj Ha Ho)).
Qed.

End SON.
