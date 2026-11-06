(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Import Tac Bytes SCPS.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require Import Prelim Stdio Malloc Prog MEX_defs MEX_iface MEX_main.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require KB_SiteM0.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.KB_SiteM0.KB_Sites.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared Require Import MallocBlocks Malloc_ifaceP.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U Require Import UImg CJ_iface CJ_tree.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U Require CJ_phex4.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.CJ_phex4.CJ_parse_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U Require Import F_pad Exit F_printf_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U Require SO_piface.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.SO_piface.Stdio_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U Require SO_piface.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.SO_piface.SO_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U Require Import F_memcpy.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require Import Printf_model.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U Require RRealloc_iface.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.RRealloc_iface.RMalloc_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U Require Import RRealloc_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U Require CJ_heap_instR.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.CJ_heap_instR.CJ_heap_inst0.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U Require CJ_heap_instR.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.CJ_heap_instR.CJ_heap_inst.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U Require Import CJ_fuzz CJ_fuzz_top.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U Require Drv_heap.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.Drv_heap.KB_drv.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U Require Import Drv_base Drv_heap.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U Require Drv_open.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.Drv_open.Drv_stmt.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U Require Import Drv_atexit Drv_trun_A Drv_trun_B.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib Require Import ShapeAlg ShapeSpec.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope Z_scope.

From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib Require Import SspGuard.

(* [comment removed for export] *)
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require StoreCache.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.StoreCache.StoreFast.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
(* [comment removed for export] *)
Local Ltac gonly_lia := let HI := fresh "HI" in pose proof I as HI; clear - HI; Zify.zify; xlia zchecker.
Local Ltac gonly_refute := lazymatch goal with |- ?G => assert (~ G) by gonly_lia end.
Local Ltac tslia ::= first [ exact I | gonly_lia | gonly_refute; fail 1 | tlia | split; [ tlia | exact I ] ].
(* [comment removed for export] *)
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require StoreCache.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.StoreCache.StoreFast.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Import StoreCache.
Local Ltac mem_after_store ::= mem_after_store_cached.
Local Ltac addr_eq_tac ::= addr_eq_tac_cached.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_cached segs m m' MU WM.



(* [comment removed for export] *)
Section CeilWrap.
Context {ACEIL : Ceil} {AGRD : Guard}.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Ltac fix_lit_store :=
  lazymatch goal with
  | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 8 ?z)) _) =>
      change (Z_to_le_bytes 8 z) with (le8 (Z_to_bv 64 z)); mem_after_store
  | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 4 ?z)) _) =>
      change (Z_to_le_bytes 4 z) with (le4 (Z_to_bv 64 z)); mem_after_store
  | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 1 ?z)) _) =>
      change (Z_to_le_bytes 1 z) with [Z_to_bv 8 z]; mem_after_store
  | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (le1 (Z_to_bv 64 ?z))) _) =>
      change (le1 (Z_to_bv 64 z)) with [Z_to_bv 8 z]; mem_after_store
  | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ _) _) => mem_after_store
  | _ => idtac
  end.

(* [comment removed for export] *)
Ltac if_lit :=
  lazymatch goal with
  | |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
      first [ replace c with false by (vm_compute; reflexivity) | replace c with true by (vm_compute; reflexivity) ]; cbv iota
  end.

Section S.
  Hypothesis Hr : realloc_scps_stmt LHEAPd.
  Hypothesis Hrn : rrealloc_null_stmt.
  Hypothesis SO_EMIT1 : so_emit_first_stmt.
  Hypothesis SO_EMIT2 : so_emit_again_stmt.
  Variables (sp gp tp : word) (fs : Fs) (lo SPB : Z) (tid : word)
            (fj : list byte) (v0 v1 v2 v3 v4 v5 v6 v7 ra0 : word) (ms0 ms1 ms2 ms3 ms4 ms5 s6 s7 s8 s9 s10 s11 : word)
            (A cap : Z).
  Hypothesis TP : tp = wz PTP.
  Hypothesis LO : lo + 2^22 <= bv_unsigned sp + 80.
  Hypothesis GT : alloc_ceiling <= lo.
  Hypothesis SPH : bv_unsigned sp + 128 <= 0x800000000000.
  Hypothesis SPBE : SPB = bv_unsigned sp + 128.
  Hypothesis SPAL : bv_unsigned sp mod 16 = 0.
  Hypothesis TID : 0 < bv_unsigned tid < 2^22.

  Notation TRET := (trun_ret sp gp tp fs lo SPB tid fj v0 v1 v2 v3 v4 v5 v6 v7 ra0 ms0 ms1 ms2 ms3 ms4 ms5 s6 s7 s8 s9 s10 s11 A cap).

  Notation TITER := (titer sp fs lo SPB tid fj v0 v1 v2 v3 v4 v5 v6 v7 ra0 ms0 ms1 ms2 ms3 ms4 ms5 s6 s7 A cap).
  Notation MFRAME m := (rw_cells usegs m (bv_unsigned sp) (mframe fj v0 v1 v2 v3 v4 v5 v6 v7 ra0)).
  Notation TFRAME m uj := (rw_cells usegs m (bv_unsigned sp - 80) [CB 8 uj; C8 s7; C8 s6; C8 ms5; C8 ms4; C8 ms3; C8 ms2; C8 ms1; C8 ms0; C8 (Z_to_bv 64 0x132e0)]).
  (* [comment removed for export] *)
  Notation EST pc Fv fcv mm rav x5 x6 x7 plen x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 cnt x28 x29 x30 x31 :=
    (MS (mkR rav (Z_to_bv 64 (bv_unsigned sp - 80)) gp tp x5 x6 x7 (Z_to_bv 64 plen) x9 x10 x11 x12 x13 x14 x15 x16 x17
             x18 x19 (Z_to_bv 64 PINITFLAG) (Z_to_bv 64 cnt) s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
        Fv (Z_to_bv 64 pc) fcv None mm (seg_rom usegs)) (only parsing).

  (* [comment removed for export] *)
  Lemma trun_empty : forall (c : nat) (F : bvmap 5 word) fc m mo cs (p : bptr) (e : word) uj (KT : TSet)
      rav x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x28 x29 x30 x31,
    DHEAP cs [(p, A, cap)] SPB m mo -> DMOD fs FDS0 mo -> frm0 fc ->
    stk usegs m lo (bv_unsigned sp - 80) -> mem_inv usegs m -> CJST m -> rw_cells usegs m PERRNO [C4 e] ->
    DSTAT true tid m -> rw_cells usegs m PINCB [C1 (Z_to_bv 8 0)] -> stdout_file m stdout_init -> stderr_wfile0 m -> MFRAME m -> TFRAME m uj ->
    (1 <= c <= 4)%nat -> KT [] ->
    (forall ms' mo', TRET 0 (so_after (c - 1)) ms' mo' -> realizes usegs (mkCfg ms' mo') KT) ->
    realizes usegs (mkCfg (EST 0x134e4 F fc m rav x5 x6 x7 0 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 (Z.of_nat c) x28 x29 x30 x31) mo)
             (t_emit (W 1 emit_line) KT).
  Proof.
    intros until x31. intros DH DM FRM ST MI CJ ER DS INC SOF SEF MFR TFR Hc HK KB.
    pose proof DM as [MOK' MFDS HFS].
    eapply rz_step_evt; [exact MOK'|].
    unfold PINITFLAG. do 4 step. apply evt_done.
    change (Z_to_bv 64 215232) with (Z_to_bv 64 PINITFLAG).
    eapply (trun_rounds Hr Hrn SO_EMIT1 SO_EMIT2 sp gp tp fs lo SPB tid fj v0 v1 v2 v3 v4 v5 v6 v7 ra0 ms0 ms1 ms2 ms3 ms4 ms5 s6 s7 s8 s9 s10 s11
              A cap (215232 + 16) 0 0 [] TP LO GT SPH SPBE SPAL ltac:(lia) ltac:(left; reflexivity) c [(A, cap)] fc m mo F KT);
      [| exact Hc| exact HK| exact KB].
    split. { pose proof (dheap_lheap _ _ _ _ _ DH) as HL. cbn [map bview blk_addr blk_size fst snd] in HL. exact HL. }
    split; [left; reflexivity|]. split; [left; reflexivity|]. split; [left; lia|].
    split; [exact CJ|]. split; [exists e; exact ER|]. split; [exact MI|]. split; [exact ST|]. split; [exists uj; exact TFR|].
    split; [exact MFR|]. split; [exact DS|]. split; [exact INC|]. split; [exact SEF|]. split; [exact SOF|]. split; [exact DM| exact FRM].
  Qed.

  (* [comment removed for export] *)
  Lemma trun_alloc : forall (c : nat) (F : bvmap 5 word) fc m mo cs (d : dblk) (p : bptr) (junk data : list byte) (cl : Z) (e : word) uj (KT : TSet)
      rav x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x28 x29 x30 x31,
    let len := zlength data in
    let plen := len - 6 - cl in
    DHEAP cs [(p, A, cap)] SPB m mo -> RP1 cs d ->
    rw_cells usegs m A [CB (Z.to_nat len) data; CB (Z.to_nat (cap - len)) junk] ->
    0 <= cl -> 6 + cl <= len -> len < 2^26 -> len <= cap -> plen <> 0 ->
    DMOD fs FDS0 mo -> frm0 fc ->
    stk usegs m lo (bv_unsigned sp - 80) -> mem_inv usegs m -> CJST m -> rw_cells usegs m PERRNO [C4 e] ->
    DSTAT true tid m -> rw_cells usegs m PINCB [C1 (Z_to_bv 8 0)] -> stdout_file m stdout_init -> stderr_wfile0 m -> MFRAME m -> TFRAME m uj ->
    (1 <= c <= 4)%nat -> KT [] ->
    (forall ms' mo', TRET 0 (so_after (c - 1)) ms' mo' -> realizes usegs (mkCfg ms' mo') KT) ->
    realizes usegs (mkCfg (EST 0x13498 F fc m rav x5 x6 x7 plen (Z_to_bv 64 (A + 6 + cl)) x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 (Z.of_nat c) x28 x29 x30 x31) mo)
             (t_emit (W 1 emit_line) KT).
  Proof.
    intros until x31. intros len plen DH RP BUF CL0 CL6 LEN2 LENC PNZ DM FRM ST MI CJ ER DS INC SOF SEF MFR TFR Hc HK KB. unfold PINCB in INC.
    pose proof DM as [MOK' MFDS HFS].
    pose proof (dheap_block_range _ _ _ _ _ (p, A, cap) DH ltac:(left; reflexivity)) as BR. cbn [blk_addr blk_size fst snd] in BR.
    pose proof BR as (BR1 & BR2 & BR3 & BR4 & BR5). unfold alloc_ceiling in BR4.
    try (assert (BR6 : 0x56000 <= A) by (destruct BR5; lia); clear BR5).   (* [comment removed for export] *)
    assert (PL : 0 < plen < 2^26) by (subst plen len; unfold zlength in *; lia).
    assert (PL64 : 0 <= plen < 2^64) by (clear - PL; lia).
    unfold PERRNO in ER.
    eapply rz_step_evt; [exact MOK'|].
    do 2 step. apply evt_done.
    (* [comment removed for export] *)
    destruct (rp1_RP _ _ RP) as (fl & lo1 & HRP).
    pose proof (rp_site _ _ _ _ plen HRP ltac:(lia)) as SITE.
    pose proof (rp_bounds_small rp_bounds _ _ _ _ HRP) as SMALL.
    eapply (drv_malloc_site _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m mo cs [(p, A, cap)] SPB plen lo
              (if plen <? MMAP_THRESHOLD then 2 ^ 20 else plen + 20) (if plen <? MMAP_THRESHOLD then 4096 else plen + 20) e);
      first [exact DH| exact SITE| exact SMALL| exact ER| exact MI| exact TP| reflexivity
            | destruct (plen <? MMAP_THRESHOLD); lia
            | rewrite ?unsigned_lit by lia; first [exact ST | unfold CJ_iface.RMALLOC_STACK; lia ] | idtac].
    - (* [comment removed for export] *)
      intros msy mo2 m2 errv2 cs' c' off' D junk' RPO VO MI2 ST2 ER2 PR BR' NIN BLK' DH2 LEAF.
      destruct RPO as (y5 & y6 & y7 & y11 & y12 & y13 & y14 & y15 & y16 & y17 & y28 & y29 & y30 & y31 & ->).
      rewrite ?unsigned_lit in ST2 by lia. rewrite ?unsigned_lit in PR by lia.
      replace (ret_pc (Z_to_bv 64 0x134a0)) with (Z_to_bv 64 0x134a0) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
      pose proof (dheap_mok _ _ _ _ _ DH2) as MOK2. pose proof BR' as (BQ1 & BQ2 & BQ3 & BQ4 & BQ5). unfold alloc_ceiling in BQ4.
      try (assert (BQ6 : 0x56000 <= D) by (destruct BQ5; lia); clear BQ5).   (* [comment removed for export] *)
      cbn [map bview blk_addr blk_size fst snd] in PR. cbn [map blk_addr fst snd] in NIN.
      assert (NE : D <> A) by (intros E; apply NIN; left; symmetry; exact E). clear NIN LEAF.
      pose proof (dheap_blocks_disjoint _ _ _ _ _ D plen A cap DH2 ltac:(left; reflexivity) ltac:(right; left; reflexivity) NE) as DISJ.
      (* [comment removed for export] *)
      assert (BUF2 : rw_cells usegs m2 A [CB (Z.to_nat len) data; CB (Z.to_nat (cap - len)) junk]).
      { eapply cj_pres_rw_cells; [exact PR| exact BUF| right; right; exists A, cap; split; [left; reflexivity| cbn; lia]]. }
      pose proof (proj1 (rw_cells_CB_bytes _ _ _ _ (proj1 (proj1 (rw_cells_app usegs _ A [CB (Z.to_nat len) data] _) BUF2)))) as BYA.
      rewrite <- (firstn_skipn (Z.to_nat (6 + cl)) data) in BYA. apply bytes_at_app in BYA. destruct BYA as [_ SRC].
      rewrite length_firstn in SRC. replace (A + Z.of_nat (Z.to_nat (6 + cl) `min` length data)) with (A + 6 + cl) in SRC by (subst len; unfold zlength in *; lia).
      assert (LSRC : length (skipn (Z.to_nat (6 + cl)) data) = Z.to_nat plen) by (rewrite length_skipn; subst plen len; unfold zlength in *; lia).
      assert (TFR2 : TFRAME m2 uj) by (eapply cj_pres_rw_cells; [exact PR| exact TFR| left; cbn; lia]).
      assert (MFR2 : MFRAME m2) by (eapply cj_pres_rw_cells; [exact PR| exact MFR| left; cbn; lia]).
      pose proof (DSTAT_cj_pres _ _ _ _ _ _ DS PR) as DS2. pose proof (CJST_pres _ _ _ _ PR CJ) as CJ2.
      assert (INC2 : rw_cells usegs m2 215236 [C1 (Z_to_bv 8 0)]) by (eapply cj_pres_rw_cells; [exact PR| exact INC| right; left; unfold PDATA_LO, PIMG_HI, PLIBC, PCTX_END, PERRNO, PSSP, PGOT_SSP; cbn; lia]).
      pose proof (stdout_file_cj_pres _ _ _ _ _ SOF PR) as SOF2. pose proof (stderr_wfile0_cj_pres _ _ _ _ SEF PR) as SEF2.
      unfold PERRNO in ER2.
      (* [comment removed for export] *)
      eapply rz_step_evt; [exact MOK2|]. unfold wz.
      step. if_cases K'; zify_cond K'; [exfalso; lia|]. clear K'.
      do 4 step.
      eapply evt_cut.
      { eapply (memcpy_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m2 (skipn (Z.to_nat (6 + cl)) data) junk');
          rewrite ?unsigned_lit by lia; [exact SRC| exact LSRC| exact BLK'| lia| exact MI2]. }
      intros ms3x (z5 & z6 & z7 & z11 & z12 & z13 & z14 & z15 & z16 & z17 & z28 & z29 & z30 & z31 & m3 & -> & MU3 & WM3 & MI3 & DST3 & SRC3).
      rewrite (unsigned_lit D) in MU3 by lia. rewrite (unsigned_lit plen) in MU3 by lia.
      rewrite (unsigned_lit D) in DST3 by lia. rewrite (unsigned_lit plen) in DST3 by lia.
      rewrite (unsigned_lit (A + 6 + cl)) in SRC3 by lia.
      replace (ret_pc (Z_to_bv 64 0x134b4)) with (Z_to_bv 64 0x134b4) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
      do 4 step. apply evt_done.
      (* [comment removed for export] *)
      eapply (trun_rounds Hr Hrn SO_EMIT1 SO_EMIT2 sp gp tp fs lo SPB tid fj v0 v1 v2 v3 v4 v5 v6 v7 ra0 ms0 ms1 ms2 ms3 ms4 ms5 s6 s7 s8 s9 s10 s11
                A cap D plen D (skipn (Z.to_nat (6 + cl)) data) TP LO GT SPH SPBE SPAL ltac:(lia) ltac:(right; split; [reflexivity| exact NE])
                c [(D, plen); (A, cap)] fc m3 mo2 F KT);
        [| exact Hc| exact HK| exact KB].
      pose proof GT as GT'. try rewrite <- alloc_ceiling_eq in GT'.
      split.
      { assert (DH3 : DHEAP cs' [(c', off', D, plen); (p, A, cap)] SPB m3 mo2).
        { eapply dheap_frame_ext; [exact DH2| exact MU3| exact WM3|].
          solve_Forall ltac:(right; right; right; right; exists D, plen; split; [left; reflexivity| cbn [fst snd]; lia]). }
        pose proof (dheap_lheap _ _ _ _ _ DH3) as HL. cbn [map bview blk_addr blk_size fst snd] in HL. exact HL. }
      split; [right; left; reflexivity|]. split; [right; left; reflexivity|]. split.
      { right. split; [left; reflexivity|]. split; [exact (proj1 (rw_cells_CB_bytes _ _ _ _ DST3))|]. rewrite LSRC. lia. }
      split. { xport CJ2 MU3 WM3 CJ3. exact CJ3. }
      split. { xport ER2 MU3 WM3 ER3. exists errv2. exact ER3. }
      split; [exact MI3|].
      split. { eapply stk_transport_disjoint; [exact ST2| exact MU3| exact WM3| cbn; lia]. }
      split. { xport TFR2 MU3 WM3 TFR3. exists uj. exact TFR3. }
      split. { xport MFR2 MU3 WM3 MFR3. exact MFR3. }
      split. { xport DS2 MU3 WM3 DS3. exact DS3. }
      split. { xport INC2 MU3 WM3 INC3. exact INC3. }
      split. { xport SEF2 MU3 WM3 SEF3. exact SEF3. }
      split. { xport SOF2 MU3 WM3 SOF3. exact SOF3. }
      split; [| exact FRM]. eapply DMOD_vm_only; [exact DM| exact VO| exact MOK2].
  Qed.

  (* [comment removed for export] *)
  Lemma tcalls_pos : forall cl data b, 0 < cl -> nth_error data 2 = Some b ->
    Z.land (bv_unsigned b) 3 + 1 = Z.of_nat (tcalls cl data) /\ (1 <= tcalls cl data <= 4)%nat.
  Proof.
    intros cl data b Hcl Hb. unfold tcalls. destruct (Z.to_nat cl) eqn:E; [lia|].
    rewrite (nth_error_nth _ _ _ Hb). change 3 with (Z.ones 2). rewrite Z.land_ones by lia. change (2 ^ 2) with 4.
    pose proof (Z.mod_pos_bound (bv_unsigned b) 4 ltac:(lia)). split; lia.
  Qed.

  Lemma tcalls_zero : forall data, tcalls 0 data = 1%nat.
  Proof. intros data. reflexivity. Qed.

  (* [comment removed for export] *)
  Lemma DSTAT_prologue : forall ph m m' a b,
    DSTAT ph tid m -> munch [(a, b); (PINITFLAG, PINITFLAG + 1)] m m' -> wmono usegs m m' -> 0x56000 <= a -> DSTAT ph tid m'.
  Proof.
    intros ph m m' a b D MU WM Ha. eapply DSTAT_magree; [exact D|].
    eapply magree_of_munch; [exact MU| exact WM|]. intros x Hx Hd.
    unfold dstat_addr, PINITFLAG in *. cbn. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma DSTAT_atexit : forall m m' a b,
    DSTAT false tid m ->
    munch [(a, b); (PATEX + 8, PATEX + 12); (PATEX + 16, PATEX + 24); (PATEX + 32, PATEX + 40); (PATEX + 288, PATEX + 296)] m m' ->
    wmono usegs m m' -> 0x56000 <= a -> ATEX true m' -> DSTAT true tid m'.
  Proof.
    intros m m' a b D MU WM Ha [AT1 AT2]. unfold DSTAT, ATEX, PDSO, PINCB, PATEX, PCXAFIN in *.
    destruct D as (D1 & D2 & D3 & D4 & D5 & D6 & D7 & D8 & D9 & D10 & D11 & D12 & D13 & D14 & D15 & D16 & _).
    repeat match goal with |- _ /\ _ => split end.
    all: try exact AT1; try exact AT2.
    all: try lazymatch type of MU with munch _ ?mm _ => match goal with |- rw_cells _ _ ?A ?cs => match goal with Dm : rw_cells _ mm A cs |- _ =>
                   exact (rw_cells_transport _ _ _ _ _ _ Dm MU WM ltac:(cbn; lia)) end end end.
  Qed.

  Theorem trun_main : trun_stmt sp gp tp fs lo SPB tid fj v0 v1 v2 v3 v4 v5 v6 v7 ra0 ms0 ms1 ms2 ms3 ms4 ms5 s6 s7 s8 s9 s10 s11 A cap.
  Proof.
    intros t0 t1 t2 a4 a5 a6 a7 t3 t4 t5 t6 F fc m mo cs d p junk data cl e KT len plen.
    intros DH RP BUF CL0 CL6 LEN2 LENC DM FRM ST MI CJ ER IFL DS SOF SEF MFR HK KB.
    pose proof DM as [MOK' MFDS HFS].
    pose proof (dheap_block_range _ _ _ _ _ (p, A, cap) DH ltac:(left; reflexivity)) as BR. cbn [blk_addr blk_size fst snd] in BR.
    pose proof BR as (BR1 & BR2 & BR3 & BR4 & BR5). unfold alloc_ceiling in BR4.
    try (assert (BR6 : 0x56000 <= A) by (destruct BR5; lia); clear BR5).   (* [comment removed for export] *)
    assert (PL : 0 <= plen < 2^26) by (subst plen len; unfold zlength in *; lia).
    unfold wz, PTRUN in *. unfold PERRNO in ER. unfold PINITFLAG in IFL.
    pose proof DS as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & G13 & _ & _ & AT0). unfold wz in G13.
    pose proof (munch_refl [(bv_unsigned sp - 80, bv_unsigned sp); (PINITFLAG, PINITFLAG + 1)] m) as MU. pose proof (wmono_refl usegs m) as WM.
    unfold PINITFLAG in MU.
    eapply rz_step_evt; [exact MOK'|].
    carve_frame 80%nat ST.
    (* [comment removed for export] *)
    step. step. fix_lit_store. do 14 step.
    step. step. if_lit.                             (* [comment removed for export] *)
    step. step. fix_lit_store. step. step.          (* [comment removed for export] *)
    (* [comment removed for export] *)
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?m1 _) =>
      assert (DH1 : DHEAP cs [(p, A, cap)] SPB m1 mo) by (eapply dheap_frame_ext; [exact DH| exact MU| exact WM| solve_Forall ltac:(drv_write_ok_tac)]);
      assert (DS1 : DSTAT false tid m1) by (eapply DSTAT_prologue; [exact DS| exact MU| exact WM| lia]);
      xport CJ MU WM CJ1; xport SOF MU WM SOF1; xport SEF MU WM SEF1
    end.
    replace (bv_unsigned sp + -80) with (bv_unsigned sp - 80) in FR, ST by lia.
    clear DH DS SOF SEF IFL.
    (* [comment removed for export] *)
    pose proof (dheap_lheap _ _ _ _ _ DH1) as HL1. cbn [map bview blk_addr blk_size fst snd] in HL1.
    destruct (lhd_libc_cells _ _ _ _ HL1) as (cdt & thr & sec & tm1 & LC1). clear HL1.
    pose proof DS1 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & AT1).
    step.
    eapply evt_cut.
    { eapply (atexit_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ lo cdt thr sec tm1);
        rewrite ?unsigned_lit by lia;
        first [exact ST| exact AT1| exact LC1| exact MI| reflexivity| unfold ATEXIT_STACK; lia| lia]. }
    intros msA (z0 & z1 & z2 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & z3 & z4 & z5 & z6 & mq2 & -> & MUa & WMa & MI2 & ST2 & AT2).
    rewrite ?unsigned_lit in MUa by lia. rewrite ?unsigned_lit in ST2 by lia. unfold ATEXIT_STACK, P_ATEX in MUa.
    replace (ret_pc (Z_to_bv 64 0x134d0)) with (Z_to_bv 64 0x134d0) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    (* [comment removed for export] *)
    assert (DH2 : DHEAP cs [(p, A, cap)] SPB mq2 mo) by (eapply dheap_frame_ext; [exact DH1| exact MUa| exact WMa| solve_Forall ltac:(drv_write_ok_tac)]).
    assert (DS2 : DSTAT true tid mq2) by (eapply DSTAT_atexit; [exact DS1| unfold PATEX; exact MUa| exact WMa| lia| exact AT2]).
    pose proof DS2 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & INC2 & _). unfold PINCB in INC2.
    xport CJ1 MUa WMa CJ2. xport SOF1 MUa WMa SOF2. xport SEF1 MUa WMa SEF2. xport ER MUa WMa ER2. xport G13 MUa WMa G13b.
    xport FR MUa WMa FR2. xport MFR MUa WMa MFR2. xport BUF MUa WMa BUF2.
    clear DH1 DS1 SOF1 SEF1 AT1 LC1 MU WM. try clear ER G13 FR MFR BUF ST MI.
    (* [comment removed for export] *)
    step. if_lit. step. step. step. if_lit.
    (* [comment removed for export] *)
    step. if_cases K; zify_cond K; rewrite ?unsigned_lit in K by lia.
    - (* [comment removed for export] *)
      rewrite K, tcalls_zero in KB.
      do 2 step. if_cases K2; zify_cond K2; rewrite ?unsigned_lit in K2 by lia.
      + (* [comment removed for export] *)
        apply evt_done.
        change (Z_to_bv 64 1) with (Z_to_bv 64 (Z.of_nat 1)). change (Z_to_bv 64 215232) with (Z_to_bv 64 PINITFLAG).
        eapply (trun_alloc 1%nat); first [exact DH2| exact RP| exact BUF2| exact DM| exact FRM| exact ST2| exact MI2| exact CJ2| exact ER2| exact DS2| exact INC2| exact SOF2| exact SEF2
                                          | exact MFR2| exact FR2| exact HK| exact KB| lia].
      + (* [comment removed for export] *)
        apply evt_done.
        rewrite K2. change (Z_to_bv 64 1) with (Z_to_bv 64 (Z.of_nat 1)). change (Z_to_bv 64 215232) with (Z_to_bv 64 PINITFLAG).
        eapply (trun_empty 1%nat); first [exact DH2| exact DM| exact FRM| exact ST2| exact MI2| exact CJ2| exact ER2| exact DS2| exact INC2| exact SOF2| exact SEF2
                                          | exact MFR2| exact FR2| exact HK| exact KB| lia].
    - (* [comment removed for export] *)
      pose proof (proj1 (rw_cells_CB_bytes _ _ _ _ (proj1 (proj1 (rw_cells_app usegs _ A [CB (Z.to_nat len) data] _) BUF2)))) as BYA.
      destruct (nth_error data 2) as [b2|] eqn:Hb2. 2:{ exfalso. apply nth_error_None in Hb2. subst len; unfold zlength in *; lia. }
      pose proof (u8ro_read usegs _ A data 2 b2 _ BYA Hb2 ltac:(lia) eq_refl) as RD2.
      pose proof (bv_unsigned_in_range 8 b2) as Rb2. change (bv_modulus 8) with 256 in Rb2.
      destruct (tcalls_pos cl data b2 ltac:(lia) Hb2) as [TC TCB].
      do 3 step. unfold zxb. rewrite (unsigned_lit (bv_unsigned b2)) by lia. rewrite TC.
      change (Z_to_bv 64 215232) with (Z_to_bv 64 PINITFLAG).
      step. if_cases K2; zify_cond K2; rewrite ?unsigned_lit in K2 by lia.
      + (* [comment removed for export] *)
        apply evt_done. rewrite K2.
        eapply (trun_empty (tcalls cl data)); first [exact DH2| exact DM| exact FRM| exact ST2| exact MI2| exact CJ2| exact ER2| exact DS2| exact INC2| exact SOF2| exact SEF2
                                          | exact MFR2| exact FR2| exact HK| exact KB| exact TCB].
      + (* [comment removed for export] *)
        apply evt_done.
        eapply (trun_alloc (tcalls cl data)); first [exact DH2| exact RP| exact BUF2| exact DM| exact FRM| exact ST2| exact MI2| exact CJ2| exact ER2| exact DS2| exact INC2| exact SOF2| exact SEF2
                                          | exact MFR2| exact FR2| exact HK| exact KB| exact TCB| lia].
  Qed.
End S.

(* [comment removed for export] *)
Theorem trun_proof :
  realloc_scps_stmt LHEAPd -> rrealloc_null_stmt -> so_emit_first_stmt -> so_emit_again_stmt ->
  forall sp gp tp fs lo SPB tid fj v0 v1 v2 v3 v4 v5 v6 v7 ra0 ms0 ms1 ms2 ms3 ms4 ms5 s6 s7 s8 s9 s10 s11 A cap,
    trun_side sp tp lo SPB -> trun_stmt sp gp tp fs lo SPB tid fj v0 v1 v2 v3 v4 v5 v6 v7 ra0 ms0 ms1 ms2 ms3 ms4 ms5 s6 s7 s8 s9 s10 s11 A cap.
Proof.
  intros Hr Hrn SE1 SE2. intros until cap. intros (TP & LO & GT & SPH & SPBE & SPAL).
  eapply trun_main; eassumption.
Qed.



End CeilWrap.
(* [comment removed for export] *)
Ltac fix_lit_store :=
  lazymatch goal with
  | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 8 ?z)) _) =>
      change (Z_to_le_bytes 8 z) with (le8 (Z_to_bv 64 z)); mem_after_store
  | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 4 ?z)) _) =>
      change (Z_to_le_bytes 4 z) with (le4 (Z_to_bv 64 z)); mem_after_store
  | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 1 ?z)) _) =>
      change (Z_to_le_bytes 1 z) with [Z_to_bv 8 z]; mem_after_store
  | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (le1 (Z_to_bv 64 ?z))) _) =>
      change (le1 (Z_to_bv 64 z)) with [Z_to_bv 8 z]; mem_after_store
  | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ _) _) => mem_after_store
  | _ => idtac
  end.
Ltac if_lit :=
  lazymatch goal with
  | |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
      first [ replace c with false by (vm_compute; reflexivity) | replace c with true by (vm_compute; reflexivity) ]; cbv iota
  end.
