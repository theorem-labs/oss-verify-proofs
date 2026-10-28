(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation Strings.String.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP Agree MonadX Ceiling.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.U0.P0 Require Import Segs.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.U0.Malloc Require Import MallocBlocks MallocTree MallocHINV Malloc_iface.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.Lib Require Import InitStack.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.Malloc Require Import InitMem.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.P0 Require Import Startup_lib.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.U0.P0 Require Import Segs RMallocRep RMallocTree RMalloc_iface.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.U0.P0 Require Import Stdio_base Printf_lib Startup RefImpl F_printf_iface Stdio_iface Stdio_init F_printf_diag RDriver_lib RDriver_kit RDriver_ctx RDriver_iface RF_main_A RF_main_B1 RF_main_B4 RF_main_C.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.U0.P0 Require Segs RMalloc_ifaceP.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.U0.P0 Require Import H_fuzz_stmt.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.U0.P0 Require Segs F_memset F_memcpy F_strlen.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.U0.P0 Require F_atexit.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.Spec Require Import Prelim STree Malloc Monad Stdio Driver Prog.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Open Scope mspec_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Ltac rpc := apply ret_pc_even; [lia| reflexivity].
Ltac fix_lit_store :=
  try (lazymatch goal with
       | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 8 ?z)) _) =>
           change (Z_to_le_bytes 8 z) with (le8 (Z_to_bv 64 z)); mem_after_store
       | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 4 ?z)) _) =>
           change (Z_to_le_bytes 4 z) with (le4 (Z_to_bv 64 z)); mem_after_store
       | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 1 ?z)) _) =>
           change (Z_to_le_bytes 1 z) with [Z_to_bv 8 z]; mem_after_store
       | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (le1 (Z_to_bv 64 ?z))) _) =>
           change (le1 (Z_to_bv 64 z)) with [Z_to_bv 8 z]; mem_after_store
       end).
Ltac zst := zstep; fix_lit_store.

Lemma CJ1_agree : forall (P : Z -> Prop) m m',
  agree_on rsegs P m m' -> (forall a, cj0_addr a -> P a) ->
  CJ1 m -> CJ1 m'.
Proof.
  intros until m'. intros AG HP (A1 & A2 & A3 & A4). unfold CJ1 in *.
  Ltac trc1 AG HP A := eapply rw_cells_agree; [exact AG| exact A| intros a Ha; apply HP; unfold cj0_addr; cbn in Ha; lia].
  split; [trc1 AG HP A1|]. split; [trc1 AG HP A2|]. split; [trc1 AG HP A3|].
  eapply GD_agree; [exact AG| | exact A4]. intros a Ha. apply HP. unfold cj0_addr. lia.
Qed.
Lemma CJ1_heap_pres : forall LB SP m m', rheap_pres LB SP m m' ->
  CJ1 m -> CJ1 m'.
Proof.
  intros until m'. intros HP. apply (CJ1_agree _ _ _ HP). intros a Ha. right; left.
  unfold cj0_addr, ralloc_static, RLIBC, RCTX, RERRNO, RSSP_GUARD, RGOT_SSP, RVMLOCK in *. lia.
Qed.
Lemma CJ1_munch : forall W m m', munch W m m' -> wmono rsegs m m' -> (forall a, cj0_addr a -> outside W a) ->
  CJ1 m -> CJ1 m'.
Proof. intros until m'. intros MU WM HW. apply (CJ1_agree _ _ _ (agree_on_of_munch rsegs _ _ _ MU WM)). intros a Ha. cbn. apply HW. exact Ha. Qed.

Lemma land3_range : forall a, 0 <= Z.land a 3 <= 3.
Proof.
  intros a. change (Z.land a 3) with (Z.land a (Z.ones 2)). rewrite Z.land_ones by lia.
  pose proof (Z.mod_pos_bound a (2 ^ 2) ltac:(lia)). lia.
Qed.

Lemma RHEAP_need_locks {HGW : HasGuard} {HCEIL : HasCeiling} : forall s LB m, RHEAP s LB m -> rw_cells rsegs m 0x5baab [C1 (Z_to_bv 8 0)].
Proof. intros s LB m (st & LB0 & _ & _ & MREP & _). destruct MREP as (_ & _ & (_ & NL & _) & _). exact NL. Qed.

Lemma RSTAT_reg_true : forall TID m m', RSTAT TID m ->
  agree_on rsegs (fun a => rstat_addr a /\ ~ F_atexit.atx_addr a) m m' ->
  F_atexit.atx_cells 0x5b878 1 F_atexit.RATX_CALLFN F_atexit.REXIT_GUARD m' -> RSTAT TID m'.
Proof.
  intros TID m m' (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9 & A10 & A11 & A12 & A13 & [reg [_ CB]]) AG AX. unfold RSTAT.
  Ltac trx AG A := eapply rw_cells_agree; [exact AG| exact A| intros a Ha; cbv beta; unfold rstat_addr, F_atexit.atx_addr, F_atexit.RAEF_INCB in *; cbn in Ha; lia].
  split; [trx AG A1|]. split; [trx AG A2|]. split; [trx AG A3|]. split; [trx AG A4|].
  split; [trx AG A5|]. split; [trx AG A6|]. split; [trx AG A7|]. split; [trx AG A8|].
  split; [trx AG A9|]. split; [trx AG A10|]. split; [trx AG A11|]. split; [trx AG A12|]. split; [trx AG A13|].
  exists true. unfold F_atexit.atx_state. split; [exact AX| trx AG CB].
Qed.

Section T.
  Context {HGW : HasGuard} {HCEIL : HasCeiling}.
  Variables (sp0 : word) (argv envp : list (list byte)) (uid hw : word) (rnd : EntryDraw) (arg0 arg1 : list byte) (TID : Z)
            (MPAD : list byte) (S4 S5 S6 S7 S8 S9 S10 S11 : word).
  Hypothesis VSP : valid_sp sp0.
  Hypothesis CEIL : alloc_ceiling = LO sp0.
  Hypothesis VARGV : valid_argv argv.
  Hypothesis VENVP : valid_envp envp.
  Hypothesis EARGV : argv = [arg0; arg1].
  Hypothesis HT : 0 < TID < 4194304.
  Hypothesis MALLOC : rmalloc_stmt.
  Hypothesis FREE : rfree_stmt.
  Hypothesis FPR : @fprintf_diag_stmt PState.
  Hypothesis EXK : exit_k_stmt.
  Hypothesis FWR : @fwrite_diag_stmt PState.
  Hypothesis TOW : towrite_stmt.

  Notation usp0 := (bv_unsigned sp0).
  Notation gpv := (Z_to_bv 64 0x10800).
  Notation tpv := (Z_to_bv 64 RATP).
  Notation IMGB := (build_stack_bytes rph sp0 argv envp uid hw rnd).
  Notation LO' := (LO sp0).
  Notation BASE' := (BASE sp0 argv envp uid hw rnd TID).
  Notation FRAME' mm := (MFRAME sp0 argv mm MPAD S7 S6 S5 S4).
  Notation RUN0' := (RUN0 sp0 argv envp uid hw rnd TID MPAD S4 S5 S6 S7 S8 S9 S10 S11).
  Notation rat_parser' := (rat_parser sp0 argv TID S4 S5 S6 S7 S8 S9 S10 S11).
  Notation ioS := (io_S ps_so set_so_ps).

  Notation TST pc x1 t0 t1 t2 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 t3 t4 t5 t6 F fc mm :=
    (MS (mkR x1 (Z_to_bv 64 (usp0 + -208)) gpv tpv t0 t1 t2 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 (Z_to_bv 64 RSV) (Z_to_bv 64 0) S8 S9 S10 S11 t3 t4 t5 t6)
        F (Z_to_bv 64 pc) fc None mm (seg_rom rsegs)).

  Notation GST pc x1 t0 t1 t2 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 t3 t4 t5 t6 F fc mm :=
    (MS (mkR x1 (Z_to_bv 64 (usp0 + -128)) gpv tpv t0 t1 t2 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 (Z_to_bv 64 RSV) (Z_to_bv 64 0) S8 S9 S10 S11 t3 t4 t5 t6)
        F (Z_to_bv 64 pc) fc None mm (seg_rom rsegs)).

  Definition BASE2 (mm : mem) : Prop :=
    stk rsegs mm LO' (usp0 + -128) /\ mem_inv rsegs mm /\ RSTAT TID mm /\ rauxv_ok mm usp0 /\ stderr_wfile0 mm.

  #[using="VSP CEIL HT FREE EXK"] Lemma free_exit : forall (code : Z) (s : PState) (bufp : bptr) (A cap : Z) (Q : at_parser (ptr:=bptr) -> PState -> machine_state -> Prop)
      x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 x18 x19 x20 x21 t3 t4 t5 t6 (F : bvmap 5 word) (fc : bv 32) (mm : mem) (errv : word),
    RHEAP s [(bufp, A, cap)] mm -> FRAME' mm -> BASE2 mm -> stdout_file mm (ps_so s) -> rw_cells rsegs mm RERRNO [C4 errv] ->
    implM rsegs (raw_free bufp ;;; exit_k ioS code) s Q
      (GST 0x13d10 x1 t0 t1 t2 (Z_to_bv 64 code) (Z_to_bv 64 A) a0 a1 a2 a3 a4 a5 a6 a7 x18 x19 x20 x21 t3 t4 t5 t6 F fc mm).
  Proof.
    intros until errv. intros P0 FR (ST & MI & RS & AUX & SE) SOF ERR.
    pose proof (sp_facts sp0 VSP CEIL) as SF. unfold LO in SF. unfold LO in ST. unfold RERRNO in ERR. unfold MFRAME in FR.
    pose proof (RMalloc_ifaceP.RHEAP_block_range_proof _ _ _ (bufp, A, cap) P0 ltac:(left; reflexivity)) as BR. cbn [blk_addr blk_size fst snd] in BR.
    pose proof BR as (BR1 & BR2 & BR3 & BR4 & BR5). idtac.
    unfold implM. iprefix. zstep. zstep. apply evt_done.
    lazymatch goal with |- impl _ _ (?tm _) _ ?msx => change (implM rsegs tm s Q msx) end.
    eapply implM_bind.
    { unfold rfree_stmt in FREE.
      eapply FREE with (lo := usp0 - 8388608) (B := usp0) (p := bufp) (A := A) (n := cap); try reflexivity; unfold RATP;
        rewrite ?(unsigned_lit 243744) by lia; rewrite ?(unsigned_lit (usp0 + -128)) by lia;
        first [ exact P0 | left; reflexivity | exact AUX | exact ST | exact MI | exact ERR | unfold RFREE_STACK; lia | lia ]. }
    cbv beta. intros [] s2 ms2 PO.
    destruct PO as (w0 & w1 & w2 & rb0 & d1 & d2 & d3 & d4 & d5 & d6 & d7 & w3 & w4 & w5 & w6 & m3 & -> & MI3 & ST3 & ERR3 & AUX3 & HPR3 & FAE3 & SOE3 & HEAP3).
    rewrite ?(unsigned_lit (usp0 + -128)) in ST3 by lia. rewrite ?(unsigned_lit (usp0 + -128)) in HPR3 by lia.
    replace (ret_pc (Z_to_bv 64 0x13d18)) with (Z_to_bv 64 0x13d18) by (symmetry; rpc).
    cbn [lb_remove filter bptr_eqb fst snd] in HEAP3, HPR3.
    eapply implM_evt; [| intros msx Hx; exact (EXK _ code _ Q msx Hx)].
    eapply (main_return sp0 argv TID VSP CEIL HT code s2).
    - unfold MFRAME. eapply rheap_pres_rw_cells; [exact HPR3| exact FR| left; cbn; lia].
    - unfold LO. first [exact ST3| replace (usp0 - 8388608) with (usp0 + -8388608) by lia; exact ST3].
    - eapply RSTAT_heap_pres; [exact HPR3| exact RS].
    - rewrite RDriver_lib.bptr_eqb_refl in HEAP3 || idtac. exact HEAP3.
    - rewrite SOE3. eapply stdout_file_heap_pres; [exact HPR3| exact SOF].
    - apply stderr_wfile0_file. eapply stderr_wfile0_heap_pres; [exact HPR3| exact SE].
    - exact MI3.
  Qed.

  #[using="VSP CEIL"] Lemma tr_calls : forall (Q : machine_state -> Prop) x1 t0 t1 t2 (x9 a0 a1 : word) a2 a3 a4 a5 a6 a7 (x20 x21 : word) t3 t4 t5 t6
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (A cap L PLv : Z) (DATA junk : list byte),
    rw_cells rsegs m A [CB (length DATA) DATA; CB (Z.to_nat (cap - Z.of_nat (length DATA))) junk] ->
    6 + L <= Z.of_nat (length DATA) -> 0 <= L < 32768 -> rblock_range A cap -> Z.of_nat (length DATA) <= cap -> 0 <= PLv < 2^27 ->
    (forall a0', evt rsegs Q (TST (if PLv =? 0 then 0x13e94 else 0x13e48) x1 t0 t1 t2 (Z_to_bv 64 PLv) x9 a0' a1 a2 a3 a4 a5 a6 a7
                                  (Z_to_bv 64 L) (Z_to_bv 64 (A + 2)) x20 (Z_to_bv 64 (1 + Z.land (if 0 <? L then znth (map bv_unsigned DATA) 2 else 0) 3)) t3 t4 t5 t6 F fc m)) ->
    evt rsegs Q (TST 0x13e34 x1 t0 t1 t2 (Z_to_bv 64 PLv) x9 a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 L) (Z_to_bv 64 (A + 2)) x20 x21 t3 t4 t5 t6 F fc m).
  Proof.
    intros until junk. intros BLK HL1 HL2 BR HC HPL K.
    pose proof (sp_facts sp0 VSP CEIL) as SF. unfold LO in SF.
    pose proof BR as (BR1 & BR2 & BR3 & BR4 & BR5). idtac.
    destruct (list6 DATA ltac:(lia)) as (d0 & d1 & d2 & d3 & d4 & d5 & rest & ED).
    pose proof BLK as BLKB. apply (proj1 (rw_cells_app _ _ _ [CB (length DATA) DATA] _)) in BLKB. destruct BLKB as [BLKB _].
    apply rw_cells_bytes_at in BLKB. cbn [cells_bytes cbytes app] in BLKB. rewrite app_nil_r in BLKB.
    zstep. if_cases K0; zify_cond K0.
    -
      replace (0 <? L) with false in K by (symmetry; apply Z.ltb_ge; rewrite ?unsigned_lit in K0 by lia; lia). cbn [Z.land Z.add] in K.
      zstep. zstep. if_cases K1; zify_cond K1.
      + replace (PLv =? 0) with false in K by (symmetry; apply Z.eqb_neq; rewrite ?unsigned_lit in K1 by lia; lia). apply K.
      + replace (PLv =? 0) with true in K by (symmetry; apply Z.eqb_eq; rewrite ?unsigned_lit in K1 by lia; lia). apply K.
    -
      replace (0 <? L) with true in K by (symmetry; apply Z.ltb_lt; rewrite ?unsigned_lit in K0 by lia; lia).
      rewrite ED in K. rewrite znth2_cons in K. rewrite ED in BLKB.
      pose proof (u8ro_read rsegs m _ _ 2 d2 (wa (A + 2)) BLKB eq_refl ltac:(lia) eq_refl) as R2.
      zstep. clear R2. cbv beta. zstep. zstep.
      replace (Z.land (bv_unsigned d2) 3 + 1) with (1 + Z.land (bv_unsigned d2) 3) by lia.
      zstep. if_cases K1; zify_cond K1.
      + replace (PLv =? 0) with true in K by (symmetry; apply Z.eqb_eq; rewrite ?unsigned_lit in K1 by lia; lia). apply K.
      + replace (PLv =? 0) with false in K by (symmetry; apply Z.eqb_neq; rewrite ?unsigned_lit in K1 by lia; lia). apply K.
  Qed.

  #[using="arg0 arg1 VSP CEIL VARGV EARGV HT MALLOC FREE EXK"] Lemma phaseT : forall bufp A cap DATA cw L cfg sc s ms (Q : at_parser (ptr:=bptr) -> PState -> machine_state -> Prop),
    RUN0' bufp A cap DATA cw L cfg sc s ms ->
    F_atexit.atx_state false (ms_mem ms) ->
    (forall ap s1 ms1, rat_parser' ap s1 ms1 -> ap_buf ap = bufp -> Q ap s1 ms1) ->
    implM rsegs (main_tail bufp (map bv_unsigned DATA) cw L cfg) s Q ms.
  Proof.
    intros bufp A cap DATA cw L cfg sc s ms Q RU AXS HQ.
    destruct RU as (x1 & t0 & t1 & t2 & a0 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & F & fc & mm & junk & errv
                    & -> & HD & P0 & SO0 & FA0 & BLK & FR & BA & CJ & ERR & FRM).
    destruct AXS as [AXC _]. change (F_atexit.atx_cells 0 0 0 0 mm) in AXC.
    pose proof (sp_facts sp0 VSP CEIL) as SF. unfold LO in SF.
    pose proof BA as (ST & MI & RS & AUX & IMG & SE & SOF & RSS). unfold LO in ST. unfold RERRNO in ERR. unfold MFRAME in FR.
    pose proof HD as (HD1 & HD2 & HD3 & BR & HCW & HL & HL2 & HL3 & ECW & ECFG & HCFG & HSC & HCNT). unfold MAX_INPUT in HD3.
    pose proof BR as (BR1 & BR2 & BR3 & BR4 & BR5). idtac.
    destruct CJ as (C1 & C2 & C3 & G0' & _).
    pose proof (RHEAP_need_locks _ _ _ P0) as NL.
    pose proof AXC as (X1 & X2 & X3 & X4 & X5 & X6 & X7).
    unfold main_tail. unfold HDR_MIN. unfold zlength. rewrite length_map.
    set (PL := Z.of_nat (length DATA) - 6 - L).

    assert (BLK' : id (rw_cells rsegs mm A [CB (length DATA) DATA; CB (Z.to_nat (cap - Z.of_nat (length DATA))) junk])) by exact BLK.
    assert (ERR' : id (rw_cells rsegs mm 243580 [C4 errv])) by exact ERR.
    assert (FR' : id (FRAME' mm)) by exact FR.
    assert (C2' : id (rw_cells rsegs mm 0x3b6e0 [CB 16 (repeat (Z_to_bv 8 0) 16)])) by exact C2.
    assert (C3' : id (rw_cells rsegs mm 0x2a108 [C8 (Z_to_bv 64 0)])) by exact C3.
    assert (G0'' : id (GD mm)) by exact G0'.
    pose proof (munch_refl [(usp0 - 256, usp0 + -128); (0x3b6d0, 0x3b6d1); (0x5b868, 0x5b86c); (0x5b870, 0x5b878); (0x5b880, 0x5b888); (0x5b980, 0x5b988)] mm) as MU.
    pose proof (wmono_refl rsegs mm) as WM.
    unfold implM. iprefix.

    zstep. zstep. zstep. zstep. zstep.

    zstep. carve_frame 80%nat ST.
    zst. zst. zst. zst. zst. zst. zst. zst. zst.
    zstep. zstep. zstep. zstep. zstep.

    zstep. zstep.
    zstep. if_cases K0; zify_cond K0; [| exfalso; apply K0; reflexivity]. clear K0.
    zstep. zst.
    zstep. zstep. zstep.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
      assert (AXm : F_atexit.atx_cells 0 0 0 0 mx) by exact (conj X1 (conj X2 (conj X3 (conj X4 (conj X5 (conj X6 X7)))))) end.
    clear X1 X2 X3 X4 X5 X6 X7.
    call_sp F_atexit.ratexit_spec; [exact ST| exact AXm| exact NL| exact MI| reflexivity| lia| lia| lia| ].
    zstep. if_cases K1; zify_cond K1; [| exfalso; apply K1; reflexivity]. clear K1.
    zstep. zstep.
    zstep. if_cases K2; zify_cond K2; [| exfalso; apply K2; reflexivity]. clear K2.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mq _) => rename mq into m1 end.
    lazymatch goal with H : rw_cells rsegs m1 (usp0 + -208) _ |- _ => rename H into TFR end.
    lazymatch goal with H : stk rsegs m1 _ _ |- _ => rename H into ST1 end.
    lazymatch goal with H : mem_inv rsegs m1 |- _ => rename H into MI1 end.
    lazymatch goal with H : rw_cells rsegs m1 243408 _ |- _ => rename H into C1' end.
    lazymatch goal with H : F_atexit.atx_cells 374904 _ _ _ m1 |- _ => rename H into AXT end.
    unfold id in BLK', ERR', FR', C2', C3', G0''.
    pose proof (agree_on_of_munch rsegs _ _ _ MU WM) as AG1.
    assert (OUT1 : forall a, ((a < usp0 - 256 \/ usp0 - 128 <= a) /\ a <> 0x3b6d0 /\ (a < 0x5b868 \/ 0x5b988 <= a)) ->
                   (fun a0 : Z => outside [(usp0 - 256, usp0 + -128); (0x3b6d0, 0x3b6d1); (0x5b868, 0x5b86c); (0x5b870, 0x5b878); (0x5b880, 0x5b888); (0x5b980, 0x5b988)] a0) a).
    { intros a Ha. cbn. lia. }
    assert (BLK1 : rw_cells rsegs m1 A [CB (length DATA) DATA; CB (Z.to_nat (cap - Z.of_nat (length DATA))) junk]).
    { eapply rw_cells_agree; [exact AG1| exact BLK'|]. intros a Ha. apply OUT1. cbn [cells_size csize Nat.add] in Ha. lia. }
    assert (ERR1 : rw_cells rsegs m1 243580 [C4 errv]).
    { eapply rw_cells_agree; [exact AG1| exact ERR'|]. intros a Ha. apply OUT1. cbn in Ha. lia. }
    assert (FR1 : FRAME' m1).
    { unfold MFRAME. eapply rw_cells_agree; [exact AG1| exact FR'|]. intros a Ha. apply OUT1. cbn in Ha. lia. }
    assert (C21 : rw_cells rsegs m1 0x3b6e0 [CB 16 (repeat (Z_to_bv 8 0) 16)]).
    { eapply rw_cells_agree; [exact AG1| exact C2'|]. intros a Ha. apply OUT1. cbn in Ha. lia. }
    assert (C31 : rw_cells rsegs m1 0x2a108 [C8 (Z_to_bv 64 0)]).
    { eapply rw_cells_agree; [exact AG1| exact C3'|]. intros a Ha. apply OUT1. cbn in Ha. lia. }
    assert (G1 : GD m1).
    { eapply GD_agree; [exact AG1| | exact G0'']. intros a Ha. apply OUT1. lia. }
    assert (P1 : RHEAP s [(bufp, A, cap)] m1).
    { eapply RMalloc_ifaceP.RHEAP_frame_proof; [exact P0| exact MU| exact WM|].
      constructor; [left; cbn [fst snd]; lia|].
      do 5 (constructor; [right; left; cbn [fst snd]; unfold RLIBC, RCTX, RSSP_GUARD, RGOT_SSP, RVMLOCK; lia|]).
      constructor. }
    assert (AUX1 : rauxv_ok m1 usp0).
    { eapply rauxv_ok_frame; [exact AUX| exact MU| exact WM|]. unfold RAUXV_CELL.
      do 6 (constructor; [cbn [fst snd]; lia|]). constructor. }
    assert (RS1 : RSTAT TID m1).
    { eapply RSTAT_reg_true; [exact RS| | exact AXT]. eapply agree_on_mono; [exact AG1|].
      intros a [Ha Hn]. cbn. unfold rstat_addr, F_atexit.atx_addr in *. lia. }
    assert (SE1 : stderr_wfile0 m1) by (eapply stderr_wfile0_munch; [exact MU| exact WM| intros a Ha; apply OUT1; unfold stderr_addr in Ha; lia| exact SE]).
    assert (SOF1 : stdout_file m1 stdout_init) by (eapply stdout_file_munch; [exact MU| exact WM| intros a Ha; apply OUT1; unfold stdout_addr in Ha; lia| exact SOF]).
    assert (CJ1' : CJ1 m1) by (split; [exact C1'| split; [exact C21| split; [exact C31| exact G1]]]).
    clear AG1 MU WM BLK' ERR' FR' C2' C3' G0'' AXT. try clear AXm. try clear AXC. try clear NL.
    try clear BLK. try clear ERR. try clear FR. try clear C2. try clear C3. try clear G0'. try clear ST. try clear MI. clear RS AUX SE SOF.

    eapply (tr_calls _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ A cap L PL DATA junk BLK1); [lia| lia| exact BR| lia| lia|].
    intros a0x. rewrite <- ECFG.
    destruct (Z.eq_dec PL 0) as [PL0|PLP].
    -
      rewrite (proj2 (Z.eqb_eq PL 0) PL0). replace (0 <? PL) with false by (symmetry; apply Z.ltb_ge; lia).
      zstep. zstep. zstep. zstep.
      apply evt_done.
      lazymatch goal with |- impl _ _ (?tm _) _ ?msx => change (implM rsegs tm s Q msx) end.
      apply implM_mret_bind. cbv beta iota. apply implM_ret. apply evt_done.
      apply HQ; [| reflexivity].
      unfold rat_parser. do 16 eexists. exists F, fc, m1, A, cap, L, sc, 0x3b6e0, 0, DATA, junk, MPAD. do 1 eexists. exists errv, [(bufp, A, cap)].
      unfold ap_payload_len. cbn [ap_content ap_config_len ap_calls ap_owned ap_buf ap_count]. unfold HDR_MIN, zlength. rewrite length_map. fold PL. rewrite PL0.
      split; [reflexivity|]. split; [exact FRM|].
      split; [reflexivity|]. split; [reflexivity|]. split; [exact HCNT|].
      split; [pose proof (land3_range cfg); lia|]. unfold MAX_INPUT.
      split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [exact BR|].
      split; [repeat split; reflexivity|].
      split; [exact P1|]. split; [exact SO0|]. split; [exact FA0|].
      split; [exact BLK1|]. split; [rewrite PL0 in TFR; exact TFR|]. split; [exact FR1|]. split; [exact ST1|].
      split; [exact MI1|]. split; [exact RS1|]. split; [exact AUX1|]. split; [exact SE1|]. split; [exact SOF1|]. split; [exact ERR1| exact CJ1'].
    -
      rewrite (proj2 (Z.eqb_neq PL 0) PLP). replace (0 <? PL) with true by (symmetry; apply Z.ltb_lt; lia).
      zstep. zstep. apply evt_done.
      lazymatch goal with |- impl _ _ (?tm _) _ ?msx => change (implM rsegs tm s Q msx) end.
      apply implM_bind_assoc. eapply implM_bind.
      { unfold rmalloc_stmt in MALLOC.
        eapply MALLOC with (lo := usp0 - 8388608) (B := usp0); try reflexivity; unfold RATP; rewrite ?(unsigned_lit 243744) by lia; rewrite ?(unsigned_lit (usp0 + -208)) by lia;
          first [ exact P1 | exact AUX1 | exact ST1 | exact ERR1 | exact MI1 | unfold RMALLOC_STACK; lia | lia ]. }
      cbv beta. intros r s1 ms1 PO.
      destruct PO as (u0 & u1 & u2 & ra0 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & m2 & errv2 & -> & MI2 & ST2 & ERR2 & AUX2 & HPR & FAE & SOE & RR).
      unfold RATP in ERR2. rewrite ?(unsigned_lit 243744) in ERR2 by lia. rewrite ?(unsigned_lit (usp0 + -208)) in ST2 by lia. rewrite ?(unsigned_lit (usp0 + -208)) in HPR by lia.
      change (243744 + -164) with 243580 in ERR2.
      replace (ret_pc (Z_to_bv 64 0x13e50)) with (Z_to_bv 64 0x13e50) by (symmetry; rpc).
      assert (FR2 : FRAME' m2) by (unfold MFRAME; eapply rheap_pres_rw_cells; [exact HPR| exact FR1| left; cbn; lia]).
      lazymatch type of TFR with rw_cells _ _ _ ?cs =>
        assert (TFR2 : rw_cells rsegs m2 (usp0 + -208) cs) by (eapply rheap_pres_rw_cells; [exact HPR| exact TFR| left; cbn; lia]) end.
      assert (BLK2 : rw_cells rsegs m2 A [CB (length DATA) DATA; CB (Z.to_nat (cap - Z.of_nat (length DATA))) junk]).
      { eapply rheap_pres_rw_cells; [exact HPR| exact BLK1|]. right; right. exists (bufp, A, cap). split; [left; reflexivity|]. cbn [blk_addr blk_size fst snd cells_size csize Nat.add]. lia. }
      assert (RS2 : RSTAT TID m2) by (eapply RSTAT_heap_pres; [exact HPR| exact RS1]).
      assert (SE2 : stderr_wfile0 m2) by (eapply stderr_wfile0_heap_pres; [exact HPR| exact SE1]).
      assert (SOF2 : stdout_file m2 stdout_init) by (eapply stdout_file_heap_pres; [exact HPR| exact SOF1]).
      assert (CJ2 : CJ1 m2) by (eapply CJ1_heap_pres; [exact HPR| exact CJ1']).
      clear TFR FR1 BLK1 RS1 SE1 SOF1 ST1 MI1 AUX1 ERR1.
      destruct r as [nb|].
      2:{
          destruct RR as [-> HEAP2].
          unfold implM. iprefix. zstep. if_cases K1; zify_cond K1; try (exfalso; lia). clear K1.
          zstep. zstep.

          do 10 zstep. release_frame TFR2 ST2 (usp0 + -128). zstep.
          replace (ret_pc (Z_to_bv 64 0x13c90)) with (Z_to_bv 64 0x13c90) by (symmetry; rpc).

          destruct (Z.lt_ge_cases sc 0) as [SNEG|SPOS].
          -
            replace (Z_to_bv 64 sc) with (Z_to_bv 64 (sc + 2^64)) by (apply Z_to_bv_eqm; rewrite <- (Z.mod_add sc 1) by lia; f_equal; lia).
            zstep. if_cases K2; zify_cond K2; [| exfalso; rewrite ?unsigned_lit in K2 by lia; lia]. clear K2.
            zstep. zstep. zstep. replace (ret_pc (Z_to_bv 64 0x13ca0)) with (Z_to_bv 64 0x13ca0) by (symmetry; rpc).
            zstep. zstep. zstep. if_cases K3; zify_cond K3; [| exfalso; rewrite ?unsigned_lit in K3 by lia; lia]. clear K3.
            apply evt_done.
            lazymatch goal with |- impl _ _ (?tm _) _ ?msx => change (implM rsegs tm s1 Q msx) end.
            apply implM_mret_bind. cbv beta iota.
            replace (main_status (Z.testbit cw 15) 2) with 0 by (unfold main_status; rewrite HCNT; replace (sc <? 0) with true by (symmetry; apply Z.ltb_lt; lia); reflexivity).
            eapply free_exit; [exact HEAP2| exact FR2| split; [exact ST2| split; [exact MI2| split; [exact RS2| split; [exact AUX2| exact SE2]]]]| rewrite SOE; rewrite SO0; exact SOF2| exact ERR2].
          - replace (main_status (Z.testbit cw 15) 2) with 2 by (unfold main_status; rewrite HCNT; replace (sc <? 0) with false by (symmetry; apply Z.ltb_ge; lia); reflexivity).
            zstep. if_cases K2; zify_cond K2; [exfalso; rewrite ?unsigned_lit in K2 by lia; lia|]. clear K2.
            zstep. zstep. apply evt_done.
            lazymatch goal with |- impl _ _ (?tm _) _ ?msx => change (implM rsegs tm s1 Q msx) end.
            apply implM_mret_bind. cbv beta iota.
            eapply free_exit; [exact HEAP2| exact FR2| split; [exact ST2| split; [exact MI2| split; [exact RS2| split; [exact AUX2| exact SE2]]]]| rewrite SOE; rewrite SO0; exact SOF2| exact ERR2]. }

      destruct RR as (A' & junk' & -> & BR' & HEAP2 & NBLK & HEXP).
      pose proof BR' as (BQ1 & BQ2 & BQ3 & BQ4 & BQ5). idtac.
      pose proof (RMalloc_ifaceP.RHEAP_blocks_nodup_proof _ _ _ HEAP2) as ND.
      assert (DISJ : A' + PL <= A \/ A + cap <= A').
      { pose proof (RMalloc_ifaceP.RHEAP_blocks_disjoint_proof _ _ _ (nb, A', PL) (bufp, A, cap) HEAP2 ltac:(left; reflexivity) ltac:(right; left; reflexivity)) as D.
        cbn [blk_id blk_addr blk_size fst snd] in D. apply D. cbn [map blk_id fst] in ND. inversion ND as [|xh lt NI ND']; subst. intros E. apply NI. rewrite E. left. reflexivity. }

      pose proof BLK2 as SRC. apply (proj1 (rw_cells_app _ _ _ [CB (length DATA) DATA] _)) in SRC. destruct SRC as [SRC _].
      pose proof (rw_cells_bytes_at _ _ _ _ SRC) as SRCB. cbn [cells_bytes cbytes app] in SRCB. rewrite app_nil_r in SRCB. clear SRC.
      assert (PAYB : bytes_at rsegs m2 (A + 6 + L) (skipn (Z.to_nat (6 + L)) DATA)).
      { rewrite <- (firstn_skipn (Z.to_nat (6 + L)) DATA) in SRCB. apply bytes_at_app in SRCB. destruct SRCB as [_ X].
        rewrite length_firstn in X. replace (A + Z.of_nat (Nat.min (Z.to_nat (6 + L)) (length DATA))) with (A + 6 + L) in X by lia. exact X. }
      unfold implM. iprefix. zstep. if_cases K1; zify_cond K1; try (exfalso; rewrite ?unsigned_lit in K1 by lia; lia). clear K1.
      zstep. zstep. zstep. zstep.

      eapply evt_cut.
      { eapply RDriver_lib.memcpy_callv with (src := skipn (Z.to_nat (6 + L)) DATA) (junk := junk');
          [exact PAYB| rewrite length_skipn; lia| lia| lia| lia| exact NBLK| lia| exact MI2]. }
      cbv beta. intros ms' PO.
      destruct PO as (v0 & v1 & v2 & c1 & c2 & c3 & c4 & c5 & c6 & c7 & v3 & v4 & v5 & v6 & m3 & -> & MUc & WMc & MI3 & NB3 & _).
      transport_after_call rsegs m2 m3 MUc WMc.
      replace (ret_pc (Z_to_bv 64 0x13e64)) with (Z_to_bv 64 0x13e64) by (symmetry; rpc).
      assert (P3 : RHEAP s1 [(nb, A', PL); (bufp, A, cap)] m3).
      { eapply RMalloc_ifaceP.RHEAP_frame_proof; [exact HEAP2| exact MUc| exact WMc|].
        constructor; [| constructor]. right; right. exists (nb, A', PL). split; [left; reflexivity|]. cbn [fst snd blk_addr blk_size]. lia. }
      pose proof (agree_on_of_munch rsegs _ _ _ MUc WMc) as AG3.
      assert (OUT3 : forall a, (a < A' \/ A' + PL <= a) -> (fun a0 : Z => outside [(A', A' + PL)] a0) a) by (intros a Ha; cbn; lia).
      assert (RS3 : RSTAT TID m3) by (eapply (RSTAT_agree TID _ _ _ AG3); [intros a Ha; apply OUT3; unfold rstat_addr in Ha; lia| exact RS2]).
      assert (SE3 : stderr_wfile0 m3) by (eapply (stderr_wfile0_agree _ _ _ AG3); [intros a Ha; apply OUT3; unfold stderr_addr in Ha; lia| exact SE2]).
      assert (SOF3 : stdout_file m3 stdout_init) by (eapply (stdout_file_agree _ _ _ _ AG3); [intros a Ha; apply OUT3; unfold stdout_addr in Ha; lia| exact SOF2]).
      assert (AUX3 : rauxv_ok m3 usp0).
      { eapply rauxv_ok_frame; [exact AUX2| exact MUc| exact WMc|]. unfold RAUXV_CELL. constructor; [cbn [fst snd]; lia| constructor]. }
      assert (CJ3 : CJ1 m3) by (eapply (CJ1_agree _ _ _ AG3); [intros a Ha; apply OUT3; unfold cj0_addr in Ha; lia| exact CJ2]).
      assert (FR3 : FRAME' m3) by (unfold MFRAME; eapply rw_cells_agree; [exact AG3| exact FR2| intros a Ha; apply OUT3; cbn in Ha; lia]).

      zstep. zstep. zstep. zstep.
      apply evt_done.
      lazymatch goal with |- impl _ _ (?tm _) _ ?msx => change (implM rsegs tm s1 Q msx) end.
      apply implM_mret_bind. cbv beta iota. apply implM_ret. apply evt_done.
      apply HQ; [| reflexivity].
      unfold rat_parser. do 16 eexists. exists F, fc, m3, A, cap, L, sc, A', A', DATA, junk, MPAD. do 1 eexists. exists errv2, [(nb, A', PL); (bufp, A, cap)].
      unfold ap_payload_len. cbn [ap_content ap_config_len ap_calls ap_owned ap_buf ap_count]. unfold HDR_MIN, zlength. rewrite length_map. fold PL.
      split; [reflexivity|]. split; [exact FRM|].
      split; [reflexivity|]. split; [reflexivity|]. split; [exact HCNT|].
      split; [pose proof (land3_range cfg); lia|]. unfold MAX_INPUT.
      split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [exact BR|].
      split; [split; [lia|]; split; [reflexivity|]; split; [reflexivity|]; split; [exact BR'| exact NB3]|].
      split; [exact P3|]. split; [rewrite SOE; exact SO0|]. split; [rewrite FAE; exact FA0|].
      split; [exact BLK2|]. split; [exact TFR2|]. split; [exact FR3|].
      split; [first [exact ST2| eapply (stk_agree rsegs _ _ _ _ _ AG3); [exact ST2| intros a Ha; apply OUT3; lia]]|].
      split; [exact MI3|]. split; [exact RS3|]. split; [exact AUX3|]. split; [exact SE3|]. split; [exact SOF3|].
      split; [first [exact ERR2| eapply (rw_cells_agree rsegs _ _ _ _ _ AG3); [exact ERR2| intros a Ha; apply OUT3; cbn in Ha; lia]]| exact CJ3].
  Qed.
End T.
