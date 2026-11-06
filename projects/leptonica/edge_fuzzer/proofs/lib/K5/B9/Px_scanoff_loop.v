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
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.K5.B9 Require Import ImageA Layout RT_iface RT_traces RT_gaps_iface LeptTac D_kit Lept_kit D_iface D_defs
  Lept_iface Lept_env LeptC_kit Lept_leaf LeptL_kit Lept_objkit Lept_gmax_defs Ed_iface Px_defs Px_kit LeptB_guard LeptB_guard2.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac guard_fix ::= try sx32_fix; repeat match goal with |- context [bv_unsigned (Z_to_bv 64 ?e)] => rewrite (unsigned_lit e) by lia end; swrap_fix; po_fix; al_fix; try mulh_fix.

(* [comment removed for export] *)
Definition scan_fsh (jt : list byte) : list cell :=
  [C1 (Z_to_bv 8 (-15)); C1 (Z_to_bv 8 (-15)); C1 (Z_to_bv 8 (-15)); C1 (Z_to_bv 8 (-15));
   C1 (Z_to_bv 8 4); C1 (Z_to_bv 8 (-14)); C1 (Z_to_bv 8 4); C1 (Z_to_bv 8 (-14));
   C1 (Z_to_bv 8 4); C1 (Z_to_bv 8 (-13)); C1 (Z_to_bv 8 (-13)); C1 (Z_to_bv 8 (-13)); CB 4 jt].

Section SCANOFF_LOOP.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Hypothesis GP : rt_gaps RT.
Hypothesis GETPIX : pixGetPixel1_cps RT.

Lemma scanoff_loop : forall (k : nat) (c : Z) (Σk : rts RT) PMc (mc : mem)
    (ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 s7 : word) (gp s0w : word) (F : bvmap 5 word) (fc : bv 32)
    (spa fr pix ploc y lo : Z) (v : pixv) (cv : cmapv) (live : list (Z * Z)) (frames : list (Z * nat)) (old : word) (jt : list byte),
  Z.of_nat k = c + 1 -> 0 <= c <= p_w v - 1 -> 0 <= y < p_h v ->
  fdfs_only PMc -> mat_stable PMc ->
  rt_live RT Σk = live -> rt_frames RT Σk = (fr, 1%nat) :: frames ->
  pix_obj live mc pix v cv -> p_d v = 1 -> p_data v <> 0 ->
  rw_cells asegs mc (fr + 64) [C4 old] ->
  rw_cells asegs mc (fr / 8 + 2147450880) (scan_fsh jt) ->
  LIBH mc -> io_ssp mc -> ART RT Σk mc -> mem_inv asegs mc -> stk asegs mc lo spa ->
  rt_sp0 RT Σk - STACK_WIN <= lo -> lo + LSTK 4 <= spa -> spa + 192 <= USTACK_TOP -> spa mod 16 = 0 -> spa + 160 <= rt_sp0 RT Σk ->
  0 < fr -> fr mod 64 = 0 -> fr + 128 <= rt_sp0 RT Σk - STACK_WIN -> SEGTOP_A <= fr -> (fr + 128 <= 0x7fff7000 \/ 0x10007fff8000 <= fr) ->
  Z.of_nat (length frames) + 2 <= Z.of_nat FRAMES_MAX -> Z.of_nat (length live) + 0 <= LIVE_MAX -> c + 1 <= rt_credit RT Σk ->
  (forall p n, In (p, n) live -> 0 < n) ->
  cps asegs (ASTA RT Σk PMc (eq (MS (mkR ra (Z_to_bv 64 spa) gp (Z_to_bv 64 TP_A) t0 t1 t2 s0w (Z_to_bv 64 spa) a0 a1 a2 a3 a4 a5 a6 a7
                                        (Z_to_bv 64 fr) (Z_to_bv 64 ploc) (Z_to_bv 64 y) (Z_to_bv 64 c) (Z_to_bv 64 pix) s7
                                        (Z_to_bv 64 (fr + 64)) (Z_to_bv 64 fr) (Z_to_bv 64 1) (Z_to_bv 64 (fr / 8 + 2147450880)) t3 t4 t5 t6)
                                   F (Z_to_bv 64 0x12d4e4) (frm_clear fc) None mc (seg_rom asegs))))
    (fun cf => exists (Σ' : rts RT) (loc vb : Z),
       ASTA RT Σ' PMc (fun ms => exists (m' : mem) (ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' s7' : word) (F' : bvmap 5 word) (fc' : bv 32),
          ms = MS (mkR ra' (Z_to_bv 64 spa) gp (Z_to_bv 64 TP_A) t0' t1' t2' s0w (Z_to_bv 64 spa) a0' a1' a2' a3' a4' a5' a6' a7'
                      (Z_to_bv 64 fr) (Z_to_bv 64 ploc) (Z_to_bv 64 y) (Z_to_bv 64 loc) (Z_to_bv 64 pix) s7'
                      (Z_to_bv 64 (fr + 64)) (Z_to_bv 64 fr) (Z_to_bv 64 1) (Z_to_bv 64 (fr / 8 + 2147450880)) t3' t4' t5' t6')
                 F' (Z_to_bv 64 0x12d550) (frm_clear fc') None m' (seg_rom asegs)
          /\ rt_after RT Σ' spa lo mc m'
          /\ rt_pres_fp live ((fr, 1%nat) :: frames) spa [(fr + 64, fr + 68)] mc m'
          /\ LIBH m' /\ io_ssp m'
          /\ rw_cells asegs m' (fr + 64) [C4 (Z_to_bv 64 vb)]
          /\ rw_cells asegs m' (fr / 8 + 2147450880) (scan_fsh jt)
          /\ -1 <= loc <= c) cf
       /\ rt_live RT Σ' = live /\ rt_frames RT Σ' = (fr, 1%nat) :: frames /\ rt_sp0 RT Σ' = rt_sp0 RT Σk
       /\ rt_credit RT Σk - (c + 1) <= rt_credit RT Σ').
Proof using AF GP GETPIX.
  induction k as [|k IH]; intros c Σk PMc mc ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 s7 gp s0w F fc spa fr pix ploc y lo v cv live frames old jt
    HK HC HY FDO MST LVK FRS POBJ D1 VDATA VALC FSH LH SSP ART0 MI ST LOW LOR SPT SPA SPB FR0 FR64 FRHI FRSEG FRSH FRB LVB CRB LVP.
  { exfalso; lia. }
  destruct HC as [HC0 HC1]. destruct HY as [HY0 HY1].
  unfold scan_fsh in FSH.   (* [comment removed for export] *)
  unfold LSTK, STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *.
  destruct (af_client_consts RT AF Σk mc ART0) as (G1 & G2 & G3 & G4).
  pose proof (af_sp0_range RT AF Σk mc ART0) as SP0R. pose proof (af_sp0_win RT AF Σk mc ART0) as SP0W.
  unfold g_GOT_shadow_offset_cell, g_shadow_memory_dynamic_address, g_GOT_detect_uar, g_detect_stack_use_after_return in *.
  unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A, SHB in *.
  lazymatch goal with |- cps _ _ ?Q => set (QF := Q) end.
  pose proof ST as (STa & STb & _).
  set (PF := fun a => aclient live ((fr, 1%nat) :: frames) spa a /\ outside [(fr + 64, fr + 68)] a).
  pose proof (agree_refl PF mc) as AGF.
  assert (PFS : forall a, PF a -> spa <= a \/ a < lo).
  { intros a [Ha _]. destruct (aclient_split RT AF Σk mc spa a ART0) as [H|H]; [rewrite LVK, FRS; exact Ha| left; exact H| right; unfold STACK_WIN in H; lia]. }
  pose proof POBJ as (PXC & (PIN & PX0 & PX16 & _) & (HD1 & HW1 & HH1 & HWPL & HRS) & PDATA & _).
  destruct PDATA as [DZ|((DIN & D0 & D16 & DSZ) & DNE)]; [contradiction|].
  hide POBJ.
  chunk_facts RT AF GP pix 64. chunk_facts RT AF GP (p_data v) (rsize v). unfold rsize in *.
  fframe_chunk RT AF fr 1%nat 128 pix 64. fframe_chunk RT AF fr 1%nat 128 (p_data v) (4 * (p_wpl v * p_h v)).
  refresh RT AF. unfold shad, SHB in *. park_disj.
  (* [comment removed for export] *)
  walk_to AF MST [(fr + 64, fr + 68)] [e_pixGetPixel].
  at_call RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; fframe_tac | exact I])
                ltac:(fun Hx => destruct Hx as [_ HxO]; exact HxO).
  eapply cps_seq.
  { eapply GETPIX with (lo := lo) (pix := pix) (pval := fr + 64) (x := c) (y := y) (v := v) (cv := cv) (old := old).
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
      replace (shad (fr + 64)) with (fr / 8 + 2147450888) by (unfold shad, SHB; clear - FR64; Z.div_mod_to_equations; lia).
      pose proof FSH as T; split_at T 8%nat T2; split_at T2 1%nat T3; destruct T2 as [[_ B] _]; cbn [cells_bytes cbytes app] in B;
        change (ushadow 4) with [Z_to_bv 8 4]; exact B.
    - exact VALC.
    - lenv_tac.
    - unfold lres, GETPIXEL_COST; rewrite FRS, LVK; cbn [length]; unfold FRAMES_MAX, LIVE_MAX in *; repeat split; [lia| lia| lia| exact LVP]. }
  after_call RT AF.
  (* [comment removed for export] *)
  lazymatch goal with AGx : agree_on _ mc ?m1 |- _ =>
    assert (KL : keeps_live live mc m1)
      by (intros b kk Hb a Ha; apply AGx; pose proof (af_frames_range RT AF Σk mc fr 1%nat ART0 ltac:(rewrite FRS; left; reflexivity)) as (_ & _ & _ & R);
          specialize (R b kk ltac:(rewrite LVK; exact Hb)); change (fs_size 1) with 128 in R;
          split; [right; right; left; exists b, kk; split; [repeat match goal with E : rt_live _ _ = _ |- _ => rewrite E end; exact Hb| lia]| cbn [outside]; split; [lia| exact I]]);
    unfold hid in POBJ; apply (pix_obj_keep live mc m1 pix v cv KL) in POBJ; hide POBJ; clear KL end.
  fold_ag ltac:(fun Hx => destruct Hx as [Hx HxO]; split; [apply (aclient_mono _ _ spa _ _ _ _ Hx); [solve [live_sub_tac]| solve [frames_sub_tac]| lia] | revert HxO; clear; cbn [outside]; intros HxO; repeat split; try exact I; lia]).
  refresh RT AF. unfold shad, SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. park_disj.
  (* [comment removed for export] *)
  walk_to AF MST [(fr + 64, fr + 68)] [e_pixGetPixel; 0x12d4e4; 0x12d550].
  match goal with B : ?b = 0 \/ ?b = 1 |- _ => destruct B as [EB|EB]; rewrite EB in * end.
  - (* [comment removed for export] *)
    replace (sx32 (Z_to_bv 64 0)) with (Z_to_bv 64 0) by (apply bv_eq; vm_compute; reflexivity).
    awalk [e_pixGetPixel; 0x12d4e4; 0x12d550].
    destruct k as [|k'].
    + (* [comment removed for export] *)
      brF. awalk [e_pixGetPixel; 0x12d4e4; 0x12d550].
      cps_stop.
      art_now RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; fframe_tac | exact I]).
      lazymatch goal with AGFx : agree_on ?PFx _ ?mm, MUx : munch _ ?mm _ |- _ => is_var PFx; agf_munch AGFx MUx ltac:(fun Hx => destruct Hx as [_ HxO]; exact HxO) end.
      apply cps_finish; intros cf Hc; subst QF; cbv beta.
      lazymatch type of Hc with ASTA RT ?S _ _ _ => exists S, (-1), 0 end.
      split.
      2: { split; [repeat match goal with H : rt_live _ _ = _ |- _ => rewrite H end; reflexivity|].
           split; [repeat match goal with H : rt_frames _ _ = _ |- _ => rewrite H end; reflexivity|].
           split; [repeat match goal with H : rt_sp0 _ _ = _ |- _ => rewrite H end; reflexivity|].
           unfold GETPIXEL_COST in *; lia. }
      eapply (ASTA_conseq RT); [exact Hc|]; intros ms <-.
      eexists. do 19 eexists. split; [reflexivity|].
      split; [split; [assumption| split; [assumption| split; [| assumption]]]|].
      { repeat match goal with H : wmono asegs _ _ |- _ => revert H end. clear. intros. eauto using wmono_trans. }
      split; [intros a Ha Ho; exact (AGF a (conj Ha Ho))|].
      split; [assumption|]. split; [assumption|].
      split; [assumption|].
      split; [exact FSH|].
      clear - HK; lia.
    + (* [comment removed for export] *)
      brT.
      cps_stop.
      eapply cps_conseq; [ | intros cf Hc; exact Hc | ].
      * eapply (IH (c - 1)).
        8: unfold hid in POBJ; exact POBJ.
        6: transitivity (rt_live RT Σk); [assumption | exact LVK].
        6: transitivity (rt_frames RT Σk); [assumption | exact FRS].
        1: clear - HK; lia.
        1: clear - HK HC1; lia.
        1: clear - HY0 HY1; lia.
        1: exact FDO.
        1: exact MST.
        1: exact D1.
        1: exact VDATA.
        1: eassumption.
        1: exact FSH.
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
      * intros cf (Σ' & loc & vb & HA & L1 & F1 & S1 & C1). subst QF; cbv beta.
        exists Σ', loc, vb. split.
        2: { split; [exact L1|]. split; [exact F1|]. split; [rewrite S1; repeat match goal with H : rt_sp0 _ _ = _ |- _ => rewrite H end; reflexivity|].
             unfold GETPIXEL_COST in *. lia. }
        eapply (ASTA_conseq RT); [exact HA|]. cbv beta. intros ms (m' & X).
        destruct X as (ra' & t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & s7' & F' & fc' & E & (A1 & A2 & A3 & A4) & P & R).
        exists m', ra', t0', t1', t2', a0', a1', a2', a3', a4', a5', a6', a7', t3', t4', t5', t6', s7', F', fc'.
        split; [exact E|]. split; [split; [exact A1| split; [exact A2| split; [| exact A4]]]|].
        { repeat match goal with H : wmono asegs _ _ |- _ => revert H end. clear. intros. eauto using wmono_trans. }
        split; [| destruct R as (R1 & R2 & R3 & R4 & R5); split; [exact R1| split; [exact R2| split; [exact R3| split; [exact R4| clear - R5; lia]]]]].
        intros a Ha Ho. rewrite (P a Ha Ho). exact (AGF a (conj Ha Ho)).
  - (* [comment removed for export] *)
    replace (sx32 (Z_to_bv 64 1)) with (Z_to_bv 64 1) by (apply bv_eq; vm_compute; reflexivity).
    awalk [e_pixGetPixel; 0x12d4e4; 0x12d550].
    cps_stop.
    art_now RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; fframe_tac | exact I]).
    lazymatch goal with AGFx : agree_on ?PFx _ ?mm, MUx : munch _ ?mm _ |- _ => is_var PFx; agf_munch AGFx MUx ltac:(fun Hx => destruct Hx as [_ HxO]; exact HxO) end.
    apply cps_finish; intros cf Hc; subst QF; cbv beta.
    lazymatch type of Hc with ASTA RT ?S _ _ _ => exists S, c, 1 end.
    split.
    2: { split; [repeat match goal with H : rt_live _ _ = _ |- _ => rewrite H end; reflexivity|].
         split; [repeat match goal with H : rt_frames _ _ = _ |- _ => rewrite H end; reflexivity|].
         split; [repeat match goal with H : rt_sp0 _ _ = _ |- _ => rewrite H end; reflexivity|].
         unfold GETPIXEL_COST in *; lia. }
    eapply (ASTA_conseq RT); [exact Hc|]; intros ms <-.
    eexists. do 19 eexists. split; [reflexivity|].
    split; [split; [assumption| split; [assumption| split; [| assumption]]]|].
    { repeat match goal with H : wmono asegs _ _ |- _ => revert H end. clear. intros. eauto using wmono_trans. }
    split; [intros a Ha Ho; exact (AGF a (conj Ha Ho))|].
    split; [assumption|]. split; [assumption|].
    split; [assumption|].
    split; [exact FSH|].
    clear - HC0; lia.
Qed.

(* [comment removed for export] *)
Lemma scanoff_scan : forall (c : Z) (Σk : rts RT) PMc (mc : mem)
    (ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 s7 s10 : word) (gp s0w : word) (F : bvmap 5 word) (fc : bv 32)
    (spa fr pix ploc y lo : Z) (v : pixv) (cv : cmapv) (live : list (Z * Z)) (frames : list (Z * nat)) (old : word) (jt : list byte),
  -1 <= c <= p_w v - 1 -> 0 <= y < p_h v ->
  fdfs_only PMc -> mat_stable PMc ->
  rt_live RT Σk = live -> rt_frames RT Σk = (fr, 1%nat) :: frames ->
  pix_obj live mc pix v cv -> p_d v = 1 -> p_data v <> 0 ->
  rw_cells asegs mc (fr + 64) [C4 old] ->
  rw_cells asegs mc (fr / 8 + 2147450880) (scan_fsh jt) ->
  LIBH mc -> io_ssp mc -> ART RT Σk mc -> mem_inv asegs mc -> stk asegs mc lo spa ->
  rt_sp0 RT Σk - STACK_WIN <= lo -> lo + LSTK 4 <= spa -> spa + 192 <= USTACK_TOP -> spa mod 16 = 0 -> spa + 160 <= rt_sp0 RT Σk ->
  0 < fr -> fr mod 64 = 0 -> fr + 128 <= rt_sp0 RT Σk - STACK_WIN -> SEGTOP_A <= fr -> (fr + 128 <= 0x7fff7000 \/ 0x10007fff8000 <= fr) ->
  Z.of_nat (length frames) + 2 <= Z.of_nat FRAMES_MAX -> Z.of_nat (length live) + 0 <= LIVE_MAX -> c + 1 <= rt_credit RT Σk ->
  (forall p n, In (p, n) live -> 0 < n) ->
  cps asegs (ASTA RT Σk PMc (eq (MS (mkR ra (Z_to_bv 64 spa) gp (Z_to_bv 64 TP_A) t0 t1 t2 s0w (Z_to_bv 64 spa) a0 a1 a2 a3 a4 a5 a6 a7
                                        (Z_to_bv 64 fr) (Z_to_bv 64 ploc) (Z_to_bv 64 y) (Z_to_bv 64 c) (Z_to_bv 64 pix) s7
                                        (Z_to_bv 64 (fr + 64)) (Z_to_bv 64 fr) s10 (Z_to_bv 64 (fr / 8 + 2147450880)) t3 t4 t5 t6)
                                   F (Z_to_bv 64 0x12d4dc) (frm_clear fc) None mc (seg_rom asegs))))
    (fun cf => exists (Σ' : rts RT) (loc vb : Z),
       ASTA RT Σ' PMc (fun ms => exists (m' : mem) (ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' s7' s10' : word) (F' : bvmap 5 word) (fc' : bv 32),
          ms = MS (mkR ra' (Z_to_bv 64 spa) gp (Z_to_bv 64 TP_A) t0' t1' t2' s0w (Z_to_bv 64 spa) a0' a1' a2' a3' a4' a5' a6' a7'
                      (Z_to_bv 64 fr) (Z_to_bv 64 ploc) (Z_to_bv 64 y) (Z_to_bv 64 loc) (Z_to_bv 64 pix) s7'
                      (Z_to_bv 64 (fr + 64)) (Z_to_bv 64 fr) s10' (Z_to_bv 64 (fr / 8 + 2147450880)) t3' t4' t5' t6')
                 F' (Z_to_bv 64 0x12d550) (frm_clear fc') None m' (seg_rom asegs)
          /\ rt_after RT Σ' spa lo mc m'
          /\ rt_pres_fp live ((fr, 1%nat) :: frames) spa [(fr + 64, fr + 68)] mc m'
          /\ LIBH m' /\ io_ssp m'
          /\ rw_cells asegs m' (fr + 64) [C4 (Z_to_bv 64 vb)]
          /\ rw_cells asegs m' (fr / 8 + 2147450880) (scan_fsh jt)
          /\ -1 <= loc <= c) cf
       /\ rt_live RT Σ' = live /\ rt_frames RT Σ' = (fr, 1%nat) :: frames /\ rt_sp0 RT Σ' = rt_sp0 RT Σk
       /\ rt_credit RT Σk - (c + 1) <= rt_credit RT Σ').
Proof using AF GP GETPIX.
  intros c Σk PMc mc ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 s7 s10 gp s0w F fc spa fr pix ploc y lo v cv live frames old jt
    HC HY FDO MST LVK FRS POBJ D1 VDATA VALC FSH LH SSP ART0 MI ST LOW LOR SPT SPA SPB FR0 FR64 FRHI FRSEG FRSH FRB LVB CRB LVP.
  unfold LSTK, STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *.
  pose proof POBJ as (_ & _ & (_ & HW1 & HH1 & _) & _).   (* [comment removed for export] *)
  lazymatch goal with |- cps _ _ ?Q => set (QF := Q) end.
  cps_walk AF MST.
  destruct (Z.eq_dec c (-1)) as [CM|CM].
  - (* [comment removed for export] *)
    subst c. awalk [0x12d550; 0x12d4e4].
    cps_stop.
    apply cps_finish; intros cf Hc; subst QF; cbv beta.
    exists Σk, (-1), (bv_unsigned old).
    split; [| split; [exact LVK| split; [exact FRS| split; [reflexivity| lia]]]].
    eapply (ASTA_conseq RT); [exact Hc|]; intros ms <-.
    eexists. do 20 eexists. split; [reflexivity|].
    split; [split; [exact ART0| split; [exact MI| split; [apply wmono_refl| exact ST]]]|].
    split; [intros a _ _; reflexivity|].
    split; [exact LH|]. split; [exact SSP|]. split; [rewrite Z_to_bv_bv_unsigned; exact VALC|]. split; [exact FSH|]. lia.
  - (* [comment removed for export] *)
    assert (HC0 : 0 <= c) by (clear - HC CM; lia). clear CM.
    awalk [0x12d550; 0x12d4e4]. try brF. awalk [0x12d550; 0x12d4e4].
    cps_stop.
    eapply cps_conseq; [ | intros cf Hc; exact Hc | ].
    + eapply (scanoff_loop (Z.to_nat (c + 1)) c); try eassumption; try lia.
    + intros cf (Σ' & loc & vb & HA & REST). subst QF; cbv beta.
      exists Σ', loc, vb. split; [| exact REST].
      eapply (ASTA_conseq RT); [exact HA|]. cbv beta. intros ms (m' & X).
      destruct X as (ra' & t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & s7' & F' & fc' & E & R).
      exists m', ra', t0', t1', t2', a0', a1', a2', a3', a4', a5', a6', a7', t3', t4', t5', t6', s7', (Z_to_bv 64 1), F', fc'.
      split; [exact E| exact R].
Qed.

End SCANOFF_LOOP.
