(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.openssl.echconfiglist_parser.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib Require Import
  PropExec CatExec CatSim SeqExec StoreOk ShapeAlg Nodes Hoare Frame ShapeLaws SpecConsts AgentLib FileSim
  SymExec2 SymExec2Sound SymRun SymDrive SymDriveX MemSplit Spec LibTail RefPrintfLib RefMemcpyLib
  SReach RegsEquivM MainEqv HeapCeil LazyRestrict LazySR LazyFdNodes MainWalk_defs MainSegs MainMem.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import Mem Cells Arr Step Frame MState SysStep Exec CellsX.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import InNth.   (* [comment removed for export] *)
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.As Require Import ASegs AsShadow AsConst AsIface AsCXXHeap AsDriverLaws AsStack0
  AsCall AsCallX RefExitBase AsPrintfFirst AsExitDefs AsExit AsTailExit AsRefused AsDrvTails
  AsDrvHeap AsDrvRun AsDrvMem AsDrvDefs AsTRSegs AsMainWalk_defs AsMainSegs AsMainPre AsMainLoop AsDrvCells AsMainExit
  AsTail_open_defs AsTail_open AsTail_rderr_defs AsTail_rderr AsTail_usage_defs AsTail_usage AsMainTop ECH_Iface.
Import ListNotations.
Import SymExec2.SX2. Import SymExec2Sound.SX2S.
Import OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.PropExec.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.
Open Scope Z_scope.

Abbreviation RSEGS := AsanUbsan.M.loaded_segments.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
Lemma ot_cells_of : forall m, ACONST m -> cells_ok m adrv_cells -> cells_ok m AsTail_open_defs.ot_cells.
Proof.
  intros m AC CE. acells AC.
  lazymatch goal with F6 : rw_cells asegs m AINITED_CELL _ |- _ =>
    pose proof (cells_of_C1C1 m AINITED_CELL 1 1 F6 ltac:(unfold AINITED_CELL; lia) ltac:(unfold AINITED_CELL; lia)) as [I1 I2];
    change (AINITED_CELL + 1) with 6993369 in I2 end.
  lazymatch goal with X : rw_cells asegs m ACF_CHKPRINTF_CELL _ |- _ => pose proof (cell_of_C1 m _ _ X) as I3 end.
  pose proof (cell_of_C1 m _ _ (ACONST_cell m ACF_ISTRLEN_CELL _ AC ltac:(in_nth))) as I4.
  lazymatch goal with X : rw_cells asegs m ASHW_MSG_OPEN _ |- _ =>
    pose proof (cells_of_C8C8C8 m ASHW_MSG_OPEN 0 0 0 X ltac:(unfold ASHW_MSG_OPEN; lia) ltac:(unfold ASHW_MSG_OPEN; lia)) as [S1 [S2 S5]];
    change (ASHW_MSG_OPEN + 8) with 2147482208 in S2; change (ASHW_MSG_OPEN + 16) with 2147482216 in S5 end.
  unfold AsTail_open_defs.ot_cells, cells_ok.
  repeat apply Forall_cons; try apply Forall_nil;
    first [ apply cell_of_C8; assumption
          | apply cell_of_C4; assumption
          | exact S1 | exact S2 | exact S5
          | unfold cell_ok; first [exact I1 | exact I2 | exact I3 | exact I4]
          | eapply (cells_ok_In m adrv_cells); [exact CE | solve [in_solve]] ].
Qed.

Lemma rt_cells_eq : AsTail_rderr_defs.ot_cells = AsTail_open_defs.ot_cells.
Proof. reflexivity. Qed.

Lemma ut_cells_of : forall m, ACONST m -> cells_ok m adrv_cells -> cells_ok m AsTail_usage_defs.ot_cells.
Proof.
  intros m AC CE. acells AC.
  lazymatch goal with F6 : rw_cells asegs m AINITED_CELL _ |- _ =>
    pose proof (cells_of_C1C1 m AINITED_CELL 1 1 F6 ltac:(unfold AINITED_CELL; lia) ltac:(unfold AINITED_CELL; lia)) as [I1 I2];
    change (AINITED_CELL + 1) with 6993369 in I2 end.
  lazymatch goal with X : rw_cells asegs m ACF_CHKPRINTF_CELL _ |- _ => pose proof (cell_of_C1 m _ _ X) as I3 end.
  pose proof (cell_of_C1 m _ _ (ACONST_cell m ACF_ISTRLEN_CELL _ AC ltac:(in_nth))) as I4.
  lazymatch goal with X : rw_cells asegs m ASHW_MSG_USAGE _ |- _ =>
    pose proof (cells_of_C8C8 m ASHW_MSG_USAGE 0 0 X ltac:(unfold ASHW_MSG_USAGE; lia) ltac:(unfold ASHW_MSG_USAGE; lia)) as [S1 S2];
    change (ASHW_MSG_USAGE + 8) with 2147467816 in S2 end.
  unfold AsTail_usage_defs.ot_cells, cells_ok.
  repeat apply Forall_cons; try apply Forall_nil;
    first [ apply cell_of_C8; assumption
          | apply cell_of_C4; assumption
          | exact S1 | exact S2
          | unfold cell_ok; first [exact I1 | exact I2 | exact I3 | exact I4]
          | eapply (cells_ok_In m adrv_cells); [exact CE | solve [in_solve]] ].
Qed.

Section Tails.
  Context {HCEIL : HeapCeil}.
  Variable H : asr.
  Variable L : alib.
  Hypothesis LOK : alib_ok L.
  Hypothesis HH : asan_rt_hyps H.
  Hypothesis DL : asan_driver_laws H.

  Let rom := seg_rom asegs.

  (* [comment removed for export] *)
  Lemma stack0_sh0_all : forall m lo hi (l : Z),
    stack0 m lo hi -> lo <= l -> l mod 8 = 0 ->
    forall a, ASHADOW_BASE + l / 8 <= a < ASHADOW_BASE + hi / 8 -> m (Z_to_bv 64 a) = Some (Z_to_bv 8 0).
  Proof.
    intros m lo hi l ST Hl Hl8 a Ha. pose proof (stack0_bounds _ _ _ ST) as [B1 B2]. acb. rewrite ASHADOW_BASE_val in Ha.
    set (x := 8 * (a - 0x7fff8000)).
    assert (Hx : lo <= x /\ x + 1 <= hi) by (subst x; Z.div_mod_to_equations; lia).
    assert (Ex : wa (sh x) = Z_to_bv 64 a).
    { unfold wa, sh. rewrite ASHADOW_BASE_val. f_equal. subst x. Z.div_mod_to_equations. lia. }
    pose proof (stack0_read0 m lo hi x 1 (Z_to_bv 64 a) ST ltac:(lia) ltac:(lia) ltac:(lia) ltac:(symmetry; exact Ex)) as RD.
    rewrite ov_rdn in RD. cbn [rdn Lib.PropExec.rdn] in RD. unfold mrd in RD.
    destruct (m (Z_to_bv 64 a)) as [b|] eqn:E.
    - cbn in RD. unfold TacX.b8 in RD. congruence.
    - exfalso. change asegs with RSEGS in RD. rewrite (aseg_rom_high (Z_to_bv 64 a)) in RD; [discriminate|].
      rewrite u_small; [lia | unfold AAPP_HI in *; lia].
  Qed.

  (* [comment removed for export] *)
  Lemma rdn_above : forall (sp0 : word) m m0 (a : Z) n,
    (forall x : word, bv_unsigned sp0 <= bv_unsigned x -> m x = m0 x) ->
    bv_unsigned sp0 <= a -> a + Z.of_nat n <= 2 ^ 64 ->
    rdn RSEGS m (Z_to_bv 64 a) n = rdn RSEGS m0 (Z_to_bv 64 a) n.
  Proof.
    intros sp0 m m0 a n AB Ha Hn. pose proof (u64_range sp0). apply rdn_agree. intros j Hj. rewrite u_small by lia. apply AB. rewrite u_small by lia. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma exitH_of_mstatics : forall (sp0 : word) tid can mem0 mem (sp : word),
    mstatics H L sp0 tid can mem0 mem -> exitH mem sp tid (Z_to_bv 64 0) (Z_to_bv 64 0).
  Proof.
    intros sp0 tid can mem0 mem sp ST.
    destruct ST as [INV STK AC RELRO [G1 G2] CELLS OUT [TID Ht] [CAN Hc] RFS REG LIBP [OS1 OS2] [shi [SH0 Hshi]] ABOVE FR AUX].
    pose proof (fun c => cells_ok_In _ _ c OUT) as CO. pose proof (fun c => cells_ok_In _ _ c CELLS) as CE.
    split.
    - lia.
    - exact TID.
    - exact G1.
    - exact G2.
    - exact (CO (0x5ede90, 8%nat, 0) ltac:(in_solve)).
    - exact (CO (0x5ede98, 8%nat, 0) ltac:(in_solve)).
    - exact (CO (0x5edeb0, 8%nat, 0) ltac:(in_solve)).
    - exact (CO (0x5edec0, 8%nat, 0) ltac:(in_solve)).
    - apply ax_lit_cells_of; [exact AC | apply xdrv_of_adrv; exact CELLS | exact (CE (0x5edd34, 4%nat, 0xffffffff) ltac:(in_solve)) | exact (CO (0x5edf14, 4%nat, 0xffffffff) ltac:(in_solve)) | apply AsMainExit.adgc_cell0; exact OS2].
    - apply ax_atexit_cells_of_pre. exact REG.
    - apply AsMainExit.abi_none0. exact OS1.
    - exact (amem_inv_text_none _ INV).
    - intros a n Ha Hn. pose proof (ACONST_imgvis mem AC) as SV.
      change (sh AIMG_LO) with 0x7fffa000 in SV. change (sh AIMG_TOP) with 0x80178800 in SV.
      eapply stk_store_ok; [exact SV | lia | lia | lia].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Theorem atail_open : atail_open_stmt H L.
  Proof.
    intros sp0 argv s0 msF0 mo0 regs0 mem0 B tid can a0s path pp s msF mo regs mem Hva PRE Hargv Hpw Hstr HV HA R2 R4 R18 ST Hfd2.
    pose proof (am_vsp _ _ _ _ _ _ _ _ _ _ _ _ PRE) as Hvsp. pose proof Hvsp as (SPlo & SPhi & SP16). unfold sp_window_lo, sp_window_hi in SPlo, SPhi.
    pose proof (exitH_of_mstatics sp0 tid can mem0 mem (Z_to_bv 64 (bv_unsigned sp0 - 128)) ST) as XH.
    destruct ST as [INV STK AC RELRO GLB CELLS OUT [TID Ht] [CAN Hc] RFS REG LIBP OSSL [shi [SH0 Hshi]] ABOVE FR AUX].
    destruct Hstr as (PPlo & PPhi & NONUL & STR & [t8 T8]).
    assert (HPmax : Z.of_nat (length path) <= 131071).
    { destruct Hva as (_ & _ & LEN & _). rewrite Hargv in LEN. inversion LEN as [|x l Hx Hl]; subst. inversion Hl; subst. assumption. }
    assert (STR' : rdn RSEGS mem (Z_to_bv 64 pp) (length path + 1) = Some (path ++ [Z_to_bv 8 0])).
    { rewrite (rdn_above sp0 mem mem0 pp _ ABOVE) by lia. exact STR. }
    assert (T8' : rdn RSEGS mem (Z_to_bv 64 (bv_unsigned (Z_to_bv 64 pp) + Z.of_nat (length path))) 8 = Some t8).
    { rewrite u_small by lia. rewrite (rdn_above sp0 mem mem0 _ _ ABOVE) by lia. exact T8. }
    assert (STK' : stk asegs mem (bv_unsigned sp0 - 128 - OT_FR) (bv_unsigned sp0 - 128)).
    { destruct STK as (S1 & S2 & S3). unfold ATR_STACK in *. split; [unfold OT_FR; lia|]. split; [lia|]. intros a Ha. apply S3. unfold OT_FR in Ha. lia. }
    assert (SH' : forall a, ASHADOW_BASE + (bv_unsigned sp0 - 128 - 65536) / 8 <= a < ASHADOW_BASE + 2 ^ 44 -> mem (Z_to_bv 64 a) = Some (Z_to_bv 8 0)).
    { intros a Ha. apply (stack0_sh0_all mem _ shi (bv_unsigned sp0 - 128 - 65536) SH0);
        [unfold ATR_STACK; lia | clear - SP16; Z.div_mod_to_equations; lia | rewrite ASHADOW_BASE_val in Ha |- *; Z.div_mod_to_equations; lia]. }
    assert (PLO : bv_unsigned sp0 <= bv_unsigned (Z_to_bv 64 pp)) by (rewrite u_small by lia; lia).
    assert (PHI : bv_unsigned (Z_to_bv 64 pp) + Z.of_nat (length path) + 17 <= AAPP_HI) by (unfold AAPP_HI; rewrite u_small by lia; lia).
    apply (drv_lazy H DL s msF mo regs _ mem _ HV HA). intros Lz Sz Zr OK RS _.
    unfold t_die.
    apply (as_open_tail Lz Sz Zr sp0 mem mo (Z_to_bv 64 pp) path t8 can Hvsp Hfd2 STK' RELRO AC INV (ot_cells_of mem AC CELLS) CAN Hc STR' T8' NONUL
             PLO PHI SH' tid (Z_to_bv 64 0) (Z_to_bv 64 0) XH regs msF mo HPmax R2 R4 R18 OK (same_but_materialized_refl mo) RS).
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Theorem atail_rderr : atail_rderr_stmt H L.
  Proof.
    intros sp0 argv s0 msF0 mo0 regs0 mem0 B tid can a0s path pp s msF mo regs mem Hva PRE Hargv Hpw Hstr HV HA R2 R4 R18 ST Hfd2.
    pose proof (am_vsp _ _ _ _ _ _ _ _ _ _ _ _ PRE) as Hvsp. pose proof Hvsp as (SPlo & SPhi & SP16). unfold sp_window_lo, sp_window_hi in SPlo, SPhi.
    pose proof (exitH_of_mstatics sp0 tid can mem0 mem (Z_to_bv 64 (bv_unsigned sp0 - 128)) ST) as XH.
    destruct ST as [INV STK AC RELRO GLB CELLS OUT [TID Ht] [CAN Hc] RFS REG LIBP OSSL [shi [SH0 Hshi]] ABOVE FR AUX].
    destruct Hstr as (PPlo & PPhi & NONUL & STR & [t8 T8]).
    assert (HPmax : Z.of_nat (length path) <= 131071).
    { destruct Hva as (_ & _ & LEN & _). rewrite Hargv in LEN. inversion LEN as [|x l Hx Hl]; subst. inversion Hl; subst. assumption. }
    assert (STR' : rdn RSEGS mem (Z_to_bv 64 pp) (length path + 1) = Some (path ++ [Z_to_bv 8 0])).
    { rewrite (rdn_above sp0 mem mem0 pp _ ABOVE) by lia. exact STR. }
    assert (T8' : rdn RSEGS mem (Z_to_bv 64 (bv_unsigned (Z_to_bv 64 pp) + Z.of_nat (length path))) 8 = Some t8).
    { rewrite u_small by lia. rewrite (rdn_above sp0 mem mem0 _ _ ABOVE) by lia. exact T8. }
    assert (STK' : stk asegs mem (bv_unsigned sp0 - 128 - OT_FR) (bv_unsigned sp0 - 128)).
    { destruct STK as (S1 & S2 & S3). unfold ATR_STACK in *. split; [unfold OT_FR; lia|]. split; [lia|]. intros a Ha. apply S3. unfold OT_FR in Ha. lia. }
    assert (SH' : forall a, ASHADOW_BASE + (bv_unsigned sp0 - 128 - 65536) / 8 <= a < ASHADOW_BASE + 2 ^ 44 -> mem (Z_to_bv 64 a) = Some (Z_to_bv 8 0)).
    { intros a Ha. apply (stack0_sh0_all mem _ shi (bv_unsigned sp0 - 128 - 65536) SH0);
        [unfold ATR_STACK; lia | clear - SP16; Z.div_mod_to_equations; lia | rewrite ASHADOW_BASE_val in Ha |- *; Z.div_mod_to_equations; lia]. }
    assert (PLO : bv_unsigned sp0 <= bv_unsigned (Z_to_bv 64 pp)) by (rewrite u_small by lia; lia).
    assert (PHI : bv_unsigned (Z_to_bv 64 pp) + Z.of_nat (length path) + 17 <= AAPP_HI) by (unfold AAPP_HI; rewrite u_small by lia; lia).
    apply (drv_lazy H DL s msF mo regs _ mem _ HV HA). intros Lz Sz Zr OK RS _.
    unfold t_die.
    apply (as_rderr_tail Lz Sz Zr sp0 mem mo (Z_to_bv 64 pp) path t8 can Hvsp Hfd2 STK' RELRO AC INV
             ltac:(rewrite rt_cells_eq; exact (ot_cells_of mem AC CELLS)) CAN Hc STR' T8' NONUL
             PLO PHI SH' tid (Z_to_bv 64 0) (Z_to_bv 64 0) XH regs msF mo HPmax R2 R4 R18 OK (same_but_materialized_refl mo) RS).
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma amframe_tail : forall (sp0 : word) m m',
    valid_sp sp0 -> amframe sp0 m -> frame_mod m m' (tail_regions (Z_to_bv 64 (bv_unsigned sp0 - 128)) OT_FR) -> amframe sp0 m'.
  Proof.
    intros sp0 m m' (Hlo & Hhi & _) [F1 F2] FM. unfold sp_window_lo, sp_window_hi in Hlo, Hhi.
    assert (OUT : forall (a : Z) (n : nat), bv_unsigned sp0 - 128 <= a -> a + Z.of_nat n <= bv_unsigned sp0 ->
              rdn RSEGS m' (Z_to_bv 64 a) n = rdn RSEGS m (Z_to_bv 64 a) n).
    { intros a n Ha Hn. apply (frame_mod_rdn RSEGS m m' _ n (Z_to_bv 64 a) FM); [| rewrite u_small by lia; lia].
      intros i Hi. unfold tail_regions, OT_FR. cbn [OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Frame.outside].
      unfold OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Frame.in_rng. unorm. lia. }
    split.
    - rewrite OUT by (cbn; lia). exact F1.
    - intros i Hi. destruct (F2 i Hi) as [w Hw]. exists w. rewrite OUT by (cbn; lia). exact Hw.
  Qed.

  Theorem atail_usage : atail_usage_stmt H L.
  Proof.
    intros sp0 argv s0 msF0 mo0 regs0 mem0 B tid can s msF mo regs mem Hva PRE Hargc HV HA R2 R4 R8 R10 R11 ST Hfds.
    pose proof (am_vsp _ _ _ _ _ _ _ _ _ _ _ _ PRE) as Hvsp. pose proof Hvsp as (SPlo & SPhi & SP16). unfold sp_window_lo, sp_window_hi in SPlo, SPhi.
    pose proof (exitH_of_mstatics sp0 tid can mem0 mem (Z_to_bv 64 (bv_unsigned sp0 - 48)) ST) as XH.
    pose proof ST as ST0.
    destruct ST as [INV STK AC RELRO GLB CELLS OUT [TID Ht] [CAN Hc] RFS REG LIBP OSSL [shi [SH0 Hshi]] ABOVE FR AUX].
    destruct Hva as (LEN1 & _ & LENS & _).
    destruct argv as [|a0 rest]; [cbn in LEN1; lia|]. cbn [hd].
    destruct (am_args _ _ _ _ _ _ _ _ _ _ _ _ PRE 0%nat a0 ltac:(lia) eq_refl) as (pp & Hpw & Hstr).
    destruct Hstr as (PPlo & PPhi & NONUL & STR & [t8 T8]).
    assert (HPmax : Z.of_nat (length a0) <= 131071) by (inversion LENS; subst; assumption).
    assert (STR' : rdn RSEGS mem (Z_to_bv 64 pp) (length a0 + 1) = Some (a0 ++ [Z_to_bv 8 0])).
    { rewrite (rdn_above sp0 mem mem0 pp _ ABOVE) by lia. exact STR. }
    assert (T8' : rdn RSEGS mem (Z_to_bv 64 (bv_unsigned (Z_to_bv 64 pp) + Z.of_nat (length a0))) 8 = Some t8).
    { rewrite u_small by lia. rewrite (rdn_above sp0 mem mem0 _ _ ABOVE) by lia. exact T8. }
    assert (PW' : rdn RSEGS mem (Z_to_bv 64 (bv_unsigned sp0 + 8)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 pp))).
    { rewrite (rdn_above sp0 mem mem0 _ _ ABOVE) by lia. replace (bv_unsigned sp0 + 8) with (bv_unsigned sp0 + 8 + 8 * Z.of_nat 0) by lia. exact Hpw. }
    assert (Hfd2 : fd_lookup (m_fds mo) (Z_to_bv 64 2) = Some (FdChannel (Z_to_bv 64 2))).
    { rewrite Hfds, (am_fds _ _ _ _ _ _ _ _ _ _ _ _ PRE). reflexivity. }
    assert (STK' : stk asegs mem (bv_unsigned sp0 - 128 - OT_FR) (bv_unsigned sp0 - 128)).
    { destruct STK as (S1 & S2 & S3). unfold ATR_STACK in *. split; [unfold OT_FR; lia|]. split; [lia|]. intros a Ha. apply S3. unfold OT_FR in Ha. lia. }
    assert (SH' : forall a, ASHADOW_BASE + (bv_unsigned sp0 - 128 - 65536) / 8 <= a < ASHADOW_BASE + 2 ^ 44 -> mem (Z_to_bv 64 a) = Some (Z_to_bv 8 0)).
    { intros a Ha. apply (stack0_sh0_all mem _ shi (bv_unsigned sp0 - 128 - 65536) SH0);
        [unfold ATR_STACK; lia | clear - SP16; Z.div_mod_to_equations; lia | rewrite ASHADOW_BASE_val in Ha |- *; Z.div_mod_to_equations; lia]. }
    assert (PLO : bv_unsigned sp0 <= bv_unsigned (Z_to_bv 64 pp)) by (rewrite u_small by lia; lia).
    assert (PHI : bv_unsigned (Z_to_bv 64 pp) + Z.of_nat (length a0) + 17 <= AAPP_HI) by (unfold AAPP_HI; rewrite u_small by lia; lia).
    apply (drv_lazy H DL s msF mo regs _ mem _ HV HA). intros Lz Sz Zr OK RS BACK.
    unfold t_die.
    refine (as_usage_tail Lz Sz Zr sp0 mem mo (Z_to_bv 64 pp) a0 t8 can Hvsp Hfd2 STK' RELRO AC INV (ut_cells_of mem AC CELLS) CAN Hc STR' T8' NONUL
             PW' PLO PHI SH' (t_exit (exit_code 2) (m_fs mo)) (t_exit_has_nil _ _) _ regs msF mo HPmax R2 R4 R8 R11 OK (same_but_materialized_refl mo) RS).
    (* [comment removed for export] *)
    intros regs1 M1 msF1 mo1 Q2 Q4 Q8 OK1 SB1 FM1 RS1 E1 E2 E3 E4 E5.
    destruct (BACK msF1 mo1 _ OK1 (same_vm_sb _ _ SB1) RS1) as [HV1 HA1].
    destruct (AsTail_usage.tfacts sp0 mem (Z_to_bv 64 pp) a0 t8 can Hvsp STK' RELRO AC INV CAN STR' T8' PLO PHI SH' M1 FM1)
      as (ST1 & INV1 & AC1 & GOT1 & CAN1 & _).
    assert (STKf : stk asegs M1 (bv_unsigned sp0 - 128 - ATR_STACK) (bv_unsigned sp0)).
    { eapply astk_grows; [exact STK | unfold ATR_STACK; lia | lia | exact (proj2 FM1)]. }
    rewrite <- (same_but_materialized_fs _ _ SB1).
    eapply (aseg_X H DL sp0 Hvsp s msF1 mo1 regs1 M1 (Z_to_bv 64 2) _ Q2 Q4 Q8
              ltac:(eapply astk_stk_ok; [exact STKf | unfold MSTK, ATR_STACK; rewrite u_small by lia; lia | rewrite u_small by lia; lia | unfold MSTK; lia | lia])
              (amem_inv_ro_none _ INV1) GOT1 (amframe_tail sp0 mem M1 Hvsp FR FM1)); [| exact HV1 | exact HA1].
    intros regs3 msF3 mo3 HV3 HA3 SB3 T2 T4 T10 T1.
    apply (drv_lazy H DL s msF3 mo3 regs3 _ M1 _ HV3 HA3). intros Lz' Sz' Zr' OK3 RS3 _.
    rewrite <- (same_but_materialized_fs _ _ SB3).
    apply (tail_exit2 Lz' Sz' Zr' regs3 mem M1 msF3 mo3 (Z_to_bv 64 (bv_unsigned sp0 - 48)) 6080 tid can (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) XH);
      [ rewrite u_small by lia; rewrite <- Zminus_mod_idemp_l, SP16; reflexivity
      | unfold ASP_LO; rewrite u_small by lia; lia | unfold ASP_HI; rewrite u_small by lia; lia
      | apply (amem_inv_ro_none mem INV) | exact RELRO
      | eapply frame_mod_weaken; [| exact FM1]; intros a Ha; pose proof (u64_range a);
        unfold tail_regions, OT_FR in Ha |- *; cbn [OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Frame.outside] in Ha |- *;
        unfold OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Frame.in_rng in Ha |- *; cbn [fst snd] in Ha |- *; revert Ha; unorm; intros (N1 & N2 & _); lia
      | lia
      | eapply astk_stk_ok; [exact STKf | unfold ATR_STACK; rewrite u_small by lia; lia | rewrite u_small by lia; lia | lia | lia]
      | exact Hc | exact CAN1
      | exact E1 | exact E2 | exact E3 | exact E4 | exact E5
      | exact T2 | exact T4 | exact T10 | exact OK3 | exact RS3 ].
  Qed.
End Tails.
