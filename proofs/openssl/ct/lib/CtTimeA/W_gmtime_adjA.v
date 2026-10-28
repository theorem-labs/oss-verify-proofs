(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtLib Require Import ImageCtA.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Spec Require Import Prelim Malloc Prog CtTime.
From Stdlib Require Import ZArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Fpu Sem.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP Frame Cells Step Mem RzCPS. 
From OssFuzzTheorems.Proofs.openssl.ct.lib.Malloc Require Import MallocRep MallocBlocks Malloc_iface.
From OssFuzzTheorems.Proofs.openssl.ct.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtA Require Import Layout RT_iface RT_client_kit R_cache_defs R_prim_defs R_sec_defs D_defs D_cs.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtRepP Require Import ApCells.
From OssFuzzTheorems.Proofs.openssl.ct.lib.BnP Require Import BnKit BnKit2.
From OssFuzzTheorems.Proofs.openssl.ct.lib.BnW Require Import BnTac BnMem.
From OssFuzzTheorems.Proofs.openssl.ct.lib.BnAsan Require Import AsKit AsLoop.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtKitA Require Import RT_iface2 LibKitA ARun BnHeapA BnRepDefs BnRepA AsStruct RtCallA ImplA.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtFrameA Require Import AFrameKit AFrameCall AFrameTac.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtRepU Require Import ApUTac.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtRepA Require Import ApATac ApBImg ApWalkTac ApRepDefs ApRep.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtTimeP Require Import TimeDefs TimeKit TimeKit2 TimeMagic W_posix_to_tm.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtTimeA Require Import TimeDefsA TimeKitA W_tm_to_posixA W_posix_to_tmA Fr_OPENSSL_gmtime_adj.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtRepU Require Import ApUTac.   (* [comment removed for export] *)
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtTimeA Require Import BTacX.                (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac step := apre; OssFuzzTheorems.Proofs.openssl.ct.lib.Lib.Step.step.
Local Ltac zstep := apre; OssFuzzTheorems.Proofs.openssl.ct.lib.Lib.Step.zstep.
Local Ltac rstep := OssFuzzTheorems.Proofs.openssl.ct.lib.Lib.Step.zstep.     (* [comment removed for export] *)
Local Ltac alia := unfold BnHeapA.ACEIL, SEGTOP_A, SHHI, SHLO, STACK_WIN, USTACK_TOP in *; lia.
Local Ltac plia := unfold BnHeapA.ACEIL, SEGTOP_A, SHHI, SHLO, STACK_WIN, USTACK_TOP, RT_STACK in *; cbn [ar_FR ar_RT ar_SP0 ar_PMc push amb] in *; lia.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Lemma slt_signed_small : forall a b, - 2^63 <= a < 2^63 -> - 2^63 <= b < 2^63 ->
  (Z.lxor (Z.land a 18446744073709551615) 9223372036854775808 <? Z.lxor (Z.land b 18446744073709551615) 9223372036854775808) = (a <? b).
Proof.
  intros a b Ha Hb. rewrite !land64.
  rewrite !(zb_lxor_sign) by (change (2^64) with 18446744073709551616; split; [apply Z.mod_pos_bound| apply Z.mod_pos_bound]; lia).
  change (2^63) with 9223372036854775808 in *. change (2^64) with 18446744073709551616 in *.
  destruct (Z.ltb_spec a b) as [L|L]; [apply Z.ltb_lt| apply Z.ltb_ge]; Z.div_mod_to_equations; lia.
Qed.

(* [comment removed for export] *)
Lemma sltz_lit : forall a, - 2^63 <= a < 2^63 -> (Z.lxor (Z.land a 18446744073709551615) 9223372036854775808 <? 9223372036854775808) = (a <? 0).
Proof.
  intros a Ha. rewrite !land64.
  rewrite !(zb_lxor_sign) by (change (2^64) with 18446744073709551616; split; [apply Z.mod_pos_bound| apply Z.mod_pos_bound]; lia).
  change (2^63) with 9223372036854775808 in *. change (2^64) with 18446744073709551616 in *.
  destruct (Z.ltb_spec a 0) as [L|L]; [apply Z.ltb_lt| apply Z.ltb_ge]; Z.div_mod_to_equations; lia.
Qed.

Section WithRT.
Context {AR : ARun}.
Local Notation RTS := (@ar_RT AR).
Local Notation PMc := (@ar_PMc AR).
Local Notation FRM := (@ar_FR AR).
Local Notation ACEIL := (@BnHeapA.ACEIL AR).
Local Notation AHEAP := (@BnHeapA.AHEAP AR).

(* [comment removed for export] *)
Definition OPENSSL_GMTIME_ADJ_STACK_A : Z := 160 + RT_STACK.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma gmtime_adj_checksA : forall (x1 x2 gp tp x5 x6 x7 x8 x9 x12 x13 x14 x15 x16 x17 x18 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31 : word)
    (F : bvmap 5 word) fc (m : word -> option byte) (pt sec : Z),
  (- 2^50 <= pt <= 2^50)%Z -> (0 <= sec <= 86399)%Z ->
  evt ctasegs (fun ms' => exists x11', ms' =
      MS (mkR x1 x2 gp tp x5 x6 x7 x8 x9 (Z_to_bv 64 pt) x11' x12 x13 x14 x15 x16 x17 x18 (Z_to_bv 64 sec) s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
         F (Z_to_bv 64 0x27098c) fc None m (seg_rom ctasegs))
    (MS (mkR x1 x2 gp tp x5 x6 x7 x8 x9 (Z_to_bv 64 pt) (Z_to_bv 64 (9223372036854775807 - pt)) x12 x13 x14 x15 x16 x17 x18 (Z_to_bv 64 sec) s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
        F (Z_to_bv 64 0x270970) fc None m (seg_rom ctasegs)).
Proof.
  intros until sec. intros Hpt Hsec.
  assert (E63 : 2^63 = 9223372036854775808) by reflexivity. assert (E64 : 2^64 = 18446744073709551616) by reflexivity.
  assert (E50 : 2^50 = 1125899906842624) by reflexivity.
  destruct (Z_lt_le_dec 0 pt) as [P|NP].
  - (* [comment removed for export] *)
    rstep. brF ltsz. rstep. brF ltsz. rstep. brT ltsz. apply evt_done. eexists. reflexivity.
  - (* [comment removed for export] *)
    rstep. brT ltsz.
    destruct (Z.eq_dec pt 0) as [Z0|NZ].
    + (* [comment removed for export] *) rstep. brT ltsz. apply evt_done. eexists. reflexivity.
    + (* [comment removed for export] *)
      rstep. brF ltsz. rstep. setreg 11%Z (Z_to_bv 64 (9223372036854775808 - pt)) ltac:(wmodk Hpt).
      rstep. brT ltsz. apply evt_done. eexists. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma gadj_open_pt : forall Σ1 OW LB m3 f q,
  @BnHeapA.AHEAP (push AR f 0) Σ1 OW LB m3 -> (forall b, In b (OW ++ LB) -> off_fr f 0 b) -> @fr_geo (push AR f 0) f 0 ->
  rw_cells ctasegs m3 (shad f) gadj_shadow_pro -> ~ In q (map blk_id (OW ++ LB)) ->
  @BnHeapA.AHEAP (push AR f 0) Σ1 OW ((q, f + 32, 8) :: LB) m3.
Proof.
  intros Σ1 OW LB m3 f q HEAP FRESH GEO FRS Hq.
  destruct GEO as (G1 & G2 & G3 & G4 & G5).
  assert (F8 : f mod 8 = 0) by (clear - G2; Z.div_mod_to_equations; lia).
  apply (@frame_obj_open (push AR f 0) Σ1 OW LB m3 f 0%nat q (f + 32) 8 (or_introl eq_refl) HEAP); [clear; lia| change (fs_size 0) with 64; clear; lia| clear; lia| | exact Hq|].
  - apply (acc_of_shadow_cells m3 (shad f) gadj_shadow_pro 4%nat (f + 32) 8 FRS ltac:(clear - F8; Z.div_mod_to_equations; lia) ltac:(clear - G1; lia) ltac:(clear; lia));
      [rewrite (shad_aligned_add f 32 F8) by (clear; lia); clear; cbn; lia| clear; cbn; lia| reflexivity].
  - intros b Hb. pose proof (FRESH b (in_or_app _ _ _ (or_intror Hb))) as O. unfold off_fr in O. unfold blk_apart. change (fs_size 0) with 64 in O.
    cbn [blk_addr blk_size fst snd]. clear - O. lia.
Qed.

Lemma OPENSSL_gmtime_adj_cpsA : forall (Q : config -> Prop)
    (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (Σ : rts RTS) (OW LB : list block) (lo : Z) (pa : bptr) (A d sec : Z),
  AHEAP Σ OW LB m -> stk ctasegs m lo (bv_unsigned sp) -> ACEIL <= lo -> lo + OPENSSL_GMTIME_ADJ_STACK_A <= bv_unsigned sp ->
  bv_unsigned sp + 16 <= USTACK_TOP -> bv_unsigned sp mod 16 = 0 ->
  mem_inv ctasegs m -> tp = wz TP_A -> (length FRM < FRAMES_MAX)%nat -> 1 <= rt_credit RTS Σ ->
  In (pa, A, 56) (OW ++ LB) -> A mod 8 = 0 -> rw_cells ctasegs m A (tm_cells epoch_tm) ->
  (- 2^31 <= d < 2^31)%Z -> (0 <= sec <= 86399)%Z ->
  a0 = Z_to_bv 64 A -> a1 = Z_to_bv 64 d -> a2 = Z_to_bv 64 sec ->
  (forall (Σ' : rts RTS) (m' : word -> option byte) (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (F' : bvmap 5 word) (fc' : bv 32),
     AHEAP Σ' OW LB m' -> rt_credit RTS Σ' = rt_credit RTS Σ - 1 -> rt_live RTS Σ' = rt_live RTS Σ ->
     stk ctasegs m' lo (bv_unsigned sp) -> mem_inv ctasegs m' ->
     agree_on (fun a => aclient_addr (OW ++ LB) (bv_unsigned sp) a /\ ~ (A <= a < A + 56)) m m' ->
     rw_cells ctasegs m' A (p2tm_cells (d * 86400 + sec)) ->
     cps ctasegs (ASTA RTS Σ' PMc (eq
       (MS (mkR ra sp gp (wz TP_A) t0' t1' t2' s0 s1 (Z_to_bv 64 (p2tm_ret (d * 86400 + sec))) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
           F' (ret_pc ra) fc' None m' (seg_rom ctasegs)))) Q) ->
  cps ctasegs (ASTA RTS Σ PMc (eq
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 OPENSSL_GMTIME_ADJ_A) fc None m (seg_rom ctasegs)))) Q.
Proof.
  intros until sec. intros HEAP ST CEIL LO TOP AL16 MI -> FLEN CRED HINA ALA TM Hd Hsec -> -> -> K.
  unfold OPENSSL_GMTIME_ADJ_STACK_A, RT_STACK in LO.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
  pose proof (AH_ceil _ _ _ _ HEAP) as (C1 & C2 & C3). unfold SEGTOP_A, SHHI, STACK_WIN, USTACK_TOP in C1, C2, C3. unfold USTACK_TOP in TOP.
  pose proof (AH_range_gen _ _ _ _ _ HEAP HINA) as (A0 & _ & _ & AC & AI). cbn [blk_addr blk_size fst snd] in A0, AC, AI.
  assert (E63 : 2^63 = 9223372036854775808) by reflexivity. assert (E64 : 2^64 = 18446744073709551616) by reflexivity.
  change (Z_to_bv 64 OPENSSL_GMTIME_ADJ_A) with (wz GADJ_ENTRY).
  eapply (gadj_pro_cps Q) with (lo := lo) (OW := OW) (LB := LB);
    [exact HEAP| exact ST| exact CEIL| unfold GADJ_FRAME, RT_STACK; clear - LO; lia| unfold USTACK_TOP; exact TOP| exact AL16| exact MI| reflexivity| exact FLEN| exact CRED|].
  intros Σ1 m3 f spa g junk gj ra' t0' t1' t2' a3' a4' a5' a6' a7' t3' t4' t5' t6' F1 fc1 j0 jf24 jf32 jf40
         HEAP3 FRESH GEO CR1 LIVE1 ST3 MI3 AGF LOW HIGH FRC SHC SPA32 SPAL SPAH GSZ SAVJ.
  unfold GADJ_BODY, MallocRep.wz.
  pose proof GEO as (G1 & G2 & G3 & G4 & G5). change (fs_size 0) with 64 in G3, G5. unfold BnHeapA.ACEIL in G3. cbn [ar_SP0 push amb] in G3. unfold SEGTOP_A in G4.
  pose proof CEIL as CEILu. unfold BnHeapA.ACEIL in CEILu.
  assert (F8 : f mod 8 = 0) by (clear - G2; Z.div_mod_to_equations; lia).
  assert (ESPA : bv_unsigned (Z_to_bv 64 spa) = spa) by (apply unsigned_lit; clear - SPAL SPAH SPR LO CEIL C1; alia).
  pose proof (FRESH _ HINA) as OFA. unfold off_fr in OFA. change (fs_size 0) with 64 in OFA. cbn [blk_addr blk_size fst snd] in OFA.
  assert (A_SPA : A + 56 <= spa - 16) by (clear - AC CEIL LO SPAL; alia).
  (* [comment removed for export] *)
  apply (rw_cells_agree _ _ _ _ _ AGF) in TM; [| intros xa Hxa; right; right; exists (pa, A, 56); split; [exact HINA| cbn; cbn in Hxa; lia]].
  pose proof TM as TMc. unfold tm_cells, epoch_tm in TM. cbn [t_sec t_min t_hour t_mday t_mon t_year Z.sub] in TM.
  (* [comment removed for export] *)
  destruct (bptr_fresh (map blk_id (OW ++ LB))) as [q Hq].
  pose proof (gadj_open_pt Σ1 OW LB m3 f q HEAP3 FRESH GEO SHC Hq) as HEAPo.
  assert (HINA' : In (pa, A, 56) (OW ++ (q, f + 32, 8) :: LB)) by (apply in_app_or in HINA as [?|?]; apply in_or_app; [left; assumption| right; right; assumption]).
  assert (HINB : In (q, f + 32, 8) (OW ++ (q, f + 32, 8) :: LB)) by (apply in_or_app; right; left; reflexivity).
  (* [comment removed for export] *)
  destruct (proj1 (rw_cells_app m3 f [_; _; _; _] _) FRC) as [FRC1 FRC2]. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ Pos.add] in FRC2.
  destruct (proj1 (rw_cells_app m3 (f + 32) [_] _) FRC2) as [PT FRC3]. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ Pos.add] in FRC3.
  clear FRC FRC2.
  pose proof (munch_refl [(spa - 16, spa); (f + 32, f + 32 + 8)]%Z m3) as MU3. pose proof (wmono_refl ctasegs m3) as WM3.
  assert (AWO : Forall (@aclient_write_ok (push AR f 0) (OW ++ (q, f + 32, 8) :: LB)) [(spa - 16, spa); (f + 32, f + 32 + 8)]%Z).
  { constructor; [left; cbn [fst snd]; clear - CEILu LO SPAL SPAH TOP; plia|].
    constructor; [right; right; exists (q, f + 32, 8); split; [exact HINB| cbn; clear; lia]| constructor]. }
  apply cps_from_evt'.
  (* [comment removed for export] *)
  zstep.
  eapply evt_cut.
  { eapply (@OPENSSL_tm_to_posix_epoch_specA (push AR f 0) _ (Z_to_bv 64 spa)) with (lo := lo) (OW := OW) (LB := (q, f + 32, 8) :: LB) (pa := pa) (pb := q) (A := A) (B := f + 32) (junk8 := jf32);
      rewrite ?ESPA; try reflexivity.
    - exact HEAPo.
    - exact ST3.
    - exact MI3.
    - unfold BnHeapA.ACEIL. cbn [ar_SP0 push amb]. exact CEILu.
    - clear - LO SPAL; lia.
    - exact HINA'.
    - uchk_open. exact ALA.
    - destruct TMc as [TMr _]. exact TMr.
    - exact HINB.
    - clear - F8. uchk_open. Z.div_mod_to_equations. lia.
    - clear - OFA. lia.
    - exact PT. }
  intros msq PO. destruct PO as (y0 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & y8 & y9 & y10 & y11 & y12 & y13 & m4 & -> & MU4 & WM4 & MI4 & ST4 & PT4).
  rewrite ?ESPA in MU4. rewrite ?ESPA in ST4. clear PT.
  transport_after_call ctasegs m3 m4 MU4 WM4. clear MI3.
  rewrite (ret_pc_even 0x27094c) by (clear; lia).
  assert (HEAP4 : @BnHeapA.AHEAP (push AR f 0) Σ1 OW ((q, f + 32, 8) :: LB) m4) by (eapply (@AH_frame (push AR f 0)); [exact HEAPo| exact MU4| exact WM4| exact AWO]).
  (* [comment removed for export] *)
  zstep. brc.
  (* [comment removed for export] *)
  rstep. rstep. rstep.
  rstep. rstep. rstep. setreg 10%Z (Z_to_bv 64 (d * 86400)) ltac:(wmodk Hd).
  rstep. setreg 10%Z (Z_to_bv 64 (d * 86400)) ltac:(wmodk Hd).
  (* [comment removed for export] *)
  rstep. setreg 11%Z (Z_to_bv 64 (9223372036854775807 - d * 86400)) ltac:(wmodk Hd).
  eapply evt_cut; [eapply gmtime_adj_checksA; clear - Hd Hsec; lia|]. intros ms' [x11' ->].
  (* [comment removed for export] *)
  rstep. setreg 10%Z (Z_to_bv 64 (d * 86400 + sec)) ltac:(wmodk Hd).
  zstep. zstep.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
    lazymatch goal with MUx : munch _ m3 mx, WMx : wmono ctasegs m3 mx |- _ =>
      assert (HEAP4' : @BnHeapA.AHEAP (push AR f 0) Σ1 OW ((q, f + 32, 8) :: LB) mx) by (eapply (@AH_frame (push AR f 0)); [exact HEAPo| exact MUx| exact WMx| exact AWO]) end end.
  destruct (rw_cells_forget _ _ _ _ TM) as [junk56 TMJ]. cbn [cells_size csize Nat.add] in TMJ.
  apply evt_done. eapply cps_step_same.
  { eapply (@OPENSSL_posix_to_tm_specA (push AR f 0)) with (lo := lo) (OW := OW) (LB := (q, f + 32, 8) :: LB) (pd := pa) (junk := junk56) (t := d * 86400 + sec);
      rewrite ?ESPA; try reflexivity.
    - exact HEAP4'.
    - exact ST4.
    - unfold BnHeapA.ACEIL. cbn [ar_SP0 push amb]. exact CEILu.
    - unfold OPENSSL_POSIX_TO_TM_STACK_A, RT_STACK. clear - LO SPAL. lia.
    - unfold USTACK_TOP. clear - TOP SPAH. lia.
    - clear - SPA32. Z.div_mod_to_equations. lia.
    - exact MI4.
    - exact HINA'.
    - uchk_open. exact ALA.
    - exact TMJ.
    - clear - Hd Hsec. lia. }
  intros msM PO. unfold p2tm_postA in PO. rewrite ?ESPA in PO.
  destruct PO as (v0 & v1 & v2 & d1 & d2 & d3 & d4 & d5 & d6 & d7 & v3 & v4 & v5 & v6 & F3 & fc3 & m5 & -> & MI5 & ST5 & HEAP5 & WM5 & AG5 & TM5).
  rewrite (ret_pc_even 0x270998) by (clear; lia). unfold MallocRep.wz.
  (* [comment removed for export] *)
  apply (rw_cells_agree _ _ _ _ _ AG5) in LOW; [| intros xa Hxa; cbn in Hxa; split; [left; unfold USTACK_TOP; clear - Hxa TOP SPAH GSZ; lia| clear - Hxa A_SPA; lia]].
  apply (rw_cells_agree _ _ _ _ _ AG5) in HIGH; [| intros xa Hxa; cbn in Hxa; split; [left; unfold USTACK_TOP; clear - Hxa TOP SPAH; lia| clear - Hxa A_SPA SPAH; lia]].
  eapply (@frame_obj_close (push AR f 0)) in HEAP5; [| left; reflexivity| unfold in_fr; cbn [blk_addr blk_size fst snd]; change (fs_size 0) with 64; clear; lia].
  change (Z_to_bv 64 0x270998) with (wz GADJ_EXIT).
  eapply (gadj_epi_cps Q) with (lo := lo) (LB := LB) (gj := gj) (hrest := []);
    [exact HEAP5| intros b Hb; exact (FRESH b (in_or_app _ _ _ (or_intror Hb)))| exact ST5| exact CEIL| clear - LO SPAL; lia
    | unfold USTACK_TOP; exact TOP| exact SPAL| exact SPAH| exact GSZ| exact SAVJ| exact MI5| exact LOW| exact HIGH| reflexivity|].
  intros Σ' m' x11'' HEAP' CR' LIVE' ST' MI' AG'.
  eapply K; [exact HEAP'| rewrite CR'; exact CR1| rewrite LIVE'; exact LIVE1| exact ST'| exact MI'| |].
  - (* [comment removed for export] *)
    eapply agree_on_trans; [eapply agree_on_mono; [exact AGF| intros a [Ha _]; exact Ha]|].
    eapply agree_on_trans.
    { eapply agree_on_mono; [apply (agree_on_of_munch_nw _ _ _ MU4)|]. intros a [Ha Hn]. cbn [outside fst snd].
      split; [| split; [| exact I]].
      - destruct Ha as [Ha|[Ha|(b & Hb & Hr)]]; [clear - Ha SPAH; lia| |].
        + destruct Ha as [(l & h & Hin & Hr) _]. unfold CLIENT_STATIC in Hin. cbn [In] in Hin. destruct Hin as [E|[E|[E|[]]]]; injection E as <- <-; clear - Hr CEIL LO SPAL C1; alia.
        + pose proof (AH_range_gen _ _ _ _ b HEAP Hb) as (_ & _ & _ & B3' & _). clear - Hr B3' CEIL LO SPAL. alia.
      - destruct Ha as [Ha|[Ha|(b & Hb & Hr)]]; [clear - Ha G3 CEILu LO; lia| |].
        + destruct Ha as [(l & h & Hin & Hr) _]. unfold CLIENT_STATIC in Hin. cbn [In] in Hin. destruct Hin as [E|[E|[E|[]]]]; injection E as <- <-; clear - Hr G4; lia.
        + pose proof (FRESH b Hb) as O. unfold off_fr in O. change (fs_size 0) with 64 in O. destruct b as [[bq bA] bn]; cbn [blk_addr blk_size fst snd] in Hr, O. clear - Hr O. lia. }
    eapply agree_on_trans.
    { eapply agree_on_mono; [exact AG5|]. intros a [Ha Hn]. split; [| exact Hn].
      destruct Ha as [Ha|[Ha|Ha]]; [left; clear - Ha SPAH; unfold USTACK_TOP in *; lia| right; left; exact Ha| right; right].
      destruct Ha as (b & Hb & Hr). exists b. split; [| exact Hr]. apply in_app_or in Hb as [Hb|Hb]; apply in_or_app; [left; exact Hb| right; right; exact Hb]. }
    eapply agree_on_mono; [exact AG'|]. intros a [Ha _].
    destruct Ha as [Ha|[Ha|Ha]]; [left; clear - Ha SPAH; unfold USTACK_TOP in *; lia| right; left; exact Ha| right; right; exact Ha].
  - apply (rw_cells_agree _ _ _ _ _ AG') in TM5; [exact TM5|]. intros xa Hxa. right; right. exists (pa, A, 56). split; [exact HINA| cbn; cbn in Hxa].
    unfold p2tm_cells in Hxa. destruct (utc_from_posix (d * 86400 + sec)); cbn in Hxa; lia.
Qed.

End WithRT.
