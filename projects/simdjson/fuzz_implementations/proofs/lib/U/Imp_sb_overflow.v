(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.simdjson.fuzz_implementations.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP MonadX StoreFast.
From OSSVerify.Proofs.simdjson.fuzz_implementations.lib.Malloc Require Import MallocBlocks Malloc_iface.
From OSSVerify.Proofs.simdjson.fuzz_implementations.lib.MallocU Require Import RMallocRep RMallocTree RMalloc_iface.
From OSSVerify.Proofs.simdjson.fuzz_implementations.lib.Spec Require Import Prelim STree Malloc Monad Stdio SjModel PjModel ImpModel Target Prog PjImpl.
From OSSVerify.Proofs.simdjson.fuzz_implementations.lib.P Require Import Str_tac Sj_stage1_kit.
From OSSVerify.Proofs.simdjson.fuzz_implementations.lib.U Require Import Layout Exit Printf_wfile Sj_iface Sj_kit Sj_new Sj_h_kit F_memcpy F_memset F_memmove_t2 Pj_loc_kit Pj_os_kit.
From OSSVerify.Proofs.simdjson.fuzz_implementations.lib.U Require Import Pj_kit Imp_oss_defs Imp_str_grow.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
From OSSVerify.Proofs.simdjson.fuzz_implementations.lib.Lib Require Import Ceiling.
From OSSVerify.Proofs.simdjson.fuzz_implementations.lib.P Require Import Rnd.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Local Ltac std_lia__ := lia.
Local Ltac lia := first [std_lia__ | try (pose proof alloc_ceiling_range as CEIL_RANGE__); std_lia__].

Ltac PROBEH := try (match goal with H : ?T |- _ => lazymatch T with rw_cells _ _ _ _ => idtac H ":" T | munch _ _ _ => idtac H ":" T | stk _ _ _ _ => idtac H ":" T | u8arr _ _ _ _ => idtac H ":" T | _ => fail end; fail end).
Ltac PROBE := PROBEH; match goal with |- evt _ _ (MS ?r _ ?pc _ _ ?m _) => idtac "PC:" pc "MEM:" m; idtac "REGS:" r end; fail "PROBE".
Ltac br_is b tac := lazymatch goal with |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) => replace c with b by (symmetry; tac) end; cbv_concl_iota.

Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.

Definition append_long_post (ra : word) (q : Z) (gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (lo P A alloc sz n : Z) (m : mem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' (bs : list byte),
    ms' = MS (mkR ra (Z_to_bv 64 q) gp (Z_to_bv 64 RATP) t0 t1 t2 s0 s1 (Z_to_bv 64 P) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom usegs)
    /\ munch [(q - 80, q); (P + 8, P + 16); (A + sz, A + sz + n + 1)]%Z m m' /\ wmono usegs m m' /\ mem_inv usegs m'
    /\ stk usegs m' lo q
    /\ rw_cells usegs m' P [C8 (Z_to_bv 64 (alloc + 1)); C8 (Z_to_bv 64 (sz + n)); C8 (Z_to_bv 64 A)]
    /\ rw_cells usegs m' A [CB (Z.to_nat alloc) bs].

Definition append_long_stmt : Prop :=
  forall (ra gp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem) (q lo P A alloc sz n : Z) (bs : list byte),
  stk usegs m lo q -> lo <= q - 80 -> GLOBALS_TOP <= lo ->
  rw_cells usegs m P [C8 (Z_to_bv 64 (alloc + 1)); C8 (Z_to_bv 64 sz); C8 (Z_to_bv 64 A)] -> alloc mod 16 = 0 ->
  rw_cells usegs m A [CB (Z.to_nat alloc) bs] -> 0 < A -> A + alloc < 2^63 -> q <= P -> P + 24 < 2^63 ->
  A + alloc <= lo ->
  1 <= n -> 0 <= sz -> sz + n <= alloc - 1 -> mem_inv usegs m ->
  evt usegs (append_long_post ra q gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo P A alloc sz n m)
      (MS (mkR ra (Z_to_bv 64 q) gp (Z_to_bv 64 RATP) t0 t1 t2 s0 s1 (Z_to_bv 64 P) (Z_to_bv 64 n) (Z_to_bv 64 0) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 OSS_APPEND) fc None m (seg_rom usegs)).

Lemma append_long_proof : append_long_stmt.
Proof.
  unfold append_long_stmt, OSS_APPEND. intros until bs. intros ST LO GLO REP M16 BLK A0 AHI PSEP PHI ALO N1 SZ0 ROOM MI.
  unfold GLOBALS_TOP in *.
  assert (LO0 : (0 <= lo)%Z) by (destruct ST as [? _]; assumption).
  assert (LBS : length bs = Z.to_nat alloc) by (destruct BLK as [[[HLx _] _] _]; exact HLx).
  pose proof (munch_refl [(q - 80, q); (P + 8, P + 16); (A + sz, A + sz + n + 1)]%Z m) as MU. pose proof (wmono_refl usegs m) as WM.
  carve_frame 80%nat ST.

  do 11 lstep. lstep.
  lstep. if_cases K; zify_cond K; [exfalso; rewrite ?unsigned_lit in K by lia; lia| clear K].
  lstep.

  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => pose proof (rw_cells_C8_read1_g usegs mx _ _ _ REP) as RD end. rewrite unsigned_lit in RD by lia.
  lstep. lstep. lstep. rewrite u8_lit, long_byte0 by (Z.div_mod_to_equations; lia). lstep. if_true.

  lstep. rewrite ?(unsigned_lit (alloc + 1)) by lia. rewrite long_capmask by (Z.div_mod_to_equations; lia).
  lstep. lstep.
  replace (Z.land (alloc + 1) 1) with 1 by (rewrite land1_mod2; Z.div_mod_to_equations; lia).
  lstep. if_false. lstep. lstep. lstep.
  if_cases K; zify_cond K; [clear K| exfalso; rewrite ?unsigned_lit in K by lia; lia].

  lstep. if_false. lstep. lstep. lstep. lstep. lstep. lstep. lstep.

  destruct (rw_cells_CB_at _ _ _ _ sz BLK ltac:(lia)) as [B1 B23].
  destruct (rw_cells_CB_at _ _ _ _ n B23 ltac:(lia)) as [B2 B3]. clear B23.
  lstep. call memset_callZ; [exact B2| assumption| lia| lia| lia| lia|].
  rename POST into B2.

  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => pose proof (rw_cells_C8_read1_g usegs mx _ _ _ REP) as RD2 end. rewrite unsigned_lit in RD2 by lia.
  lstep. lstep. rewrite u8_lit, long_byte0 by (Z.div_mod_to_equations; lia). lstep. if_true.
  lstep. lstep.

  apply u8arr_of_rw_cells in B3.
  pose proof (u8arr_store_ok usegs _ _ _ 0 (Z_to_bv 64 (A + (sz + n))) B3 ltac:(rewrite !length_skipn, LBS; lia) ltac:(unfold wa; f_equal; lia)) as SOK.
  zstep. first [change (le1 (Z_to_bv 64 0)) with [Z_to_bv 8 0] | change (Z_to_le_bytes 1 0) with [Z_to_bv 8 0] | idtac].
  replace (Z_to_bv 64 (A + (sz + n))) with (wa (A + sz + n + 0)) by (unfold wa; f_equal; lia).
  pose proof (u8arr_write usegs _ _ _ 0 (Z_to_bv 8 0) B3 ltac:(rewrite !length_skipn, LBS; lia)) as B3'. clear B3. store_done.
  apply rw_cells_of_u8arr in B3'. rewrite upd_length, !length_skipn, LBS in B3'.

  pose proof (rw_cells_CB_join2 _ _ _ _ _ _ _ B1 B2 ltac:(lia)) as B12.
  pose proof (rw_cells_CB_join2 _ _ _ _ _ _ _ B12 B3' ltac:(lia)) as BALL. clear B1 B2 B12 B3'.
  replace (Z.to_nat sz + Z.to_nat n + (Z.to_nat alloc - Z.to_nat sz - Z.to_nat n))%nat with (Z.to_nat alloc) in BALL by lia.

  lstep. do 10 lstep. lstep. release_frame FR ST q. lstep.
  apply evt_done. unfold append_long_post. sys_finish. exact BALL.
Qed.

Section Proofs.
  Hypothesis PB : push_back_stmt.

  Theorem overflow_proof : overflow_stmt.
  Proof.
    unfold overflow_stmt, OSS_OVERFLOW. intros until f. intros HEAP AUX QB B63 ST CEIL GLO LO ERR MI QO OB HL INV FULL EF CR OK.
    unfold OSS_OV_STACK, OSS_PB_STACK, RMALLOC_STACK, GLOBALS_TOP in *.
    assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    pose proof CEIL as CEIL'. unfold OSSVerify.Proofs.simdjson.fuzz_implementations.lib.Spec.Malloc.MCEIL in CEIL; try (pose proof alloc_ceiling_range as CEIL_RANGE__).
    pose proof (OSNUM_cap24 len st ltac:(apply INV)) as CAP24. pose proof (PJ_CAPMAX_bound len HL) as CMB.
    pose proof OK as OKB. apply chain_ok_spec in OK.
    destruct st as [D cap blk fuel w]. unfold os_lim in FULL. cbn [os_data os_cap os_blk os_fuel os_w] in *. subst fuel. subst w.
    destruct INV as ((PUTC & (hm & HMC & HMR) & (j108 & MODE)) & REP & NUM).
    unfold sb_cellsI, os_lim in PUTC. cbn [os_data os_cap os_blk os_fuel os_w] in PUTC. cbn [os_data os_w] in HMR.
    pose proof NUM as (WB & FU & CB16 & HB). unfold os_lim, os_k in WB, FU, CB16, HB. cbn [os_data os_cap os_blk os_fuel os_w] in WB, FU, CB16, HB.
    unfold OSS_SB_VPTR, OSS_CLASSIC in PUTC.
    assert (ELX : LX_ERRNO = 1004708) by reflexivity. rewrite ELX in ERR.
    assert (BLB : forall a, in_block LB0 a -> a < alloc_ceiling).
    { intros a (b & Hb & Hr). pose proof (LH_block_range _ _ _ _ HEAP ltac:(apply in_or_app; right; exact Hb)) as (_ & _ & _ & BC & _).
      unfold OSSVerify.Proofs.simdjson.fuzz_implementations.lib.Spec.Malloc.MCEIL in BC. lia. }
    set (lim := match blk with Some _ => cap - 1 | None => 22 end) in *.
    assert (LIMR : 22 <= lim < cap) by (subst lim; destruct blk; [lia| destruct HB as [EC _]; unfold IMP_SCAP0 in EC; lia]).
    assert (DR : 0 < D /\ D + cap < 2^63).
    { unfold STRREP in REP. cbn [os_blk os_data os_cap] in REP. destruct blk.
      - destruct REP as (_ & _ & (A0 & A16 & _ & AC & AS)). unfold OSSVerify.Proofs.simdjson.fuzz_implementations.lib.Spec.Malloc.MCEIL in AC. lia.
      - destruct REP as (_ & _ & ->). destruct HB as [EC _]. unfold IMP_SCAP0 in EC. lia. }

    apply (PjImpl.implM_pj_part_grow usegs raw_malloc raw_free ps_so set_so_ps f len cap blk (2 * cap)); [exact OKB|].
    pose proof (munch_refl [(q - 80, q)]%Z m) as MU. pose proof (wmono_refl usegs m) as WM.
    hide REP.
    unfold implM. iprefix.
    lstep. carve_frame 80%nat ST.
    apply (rw_cells_split_CB usegs _ _ [] 80 junk [] [8;8;8;8;8;8;8;8;8;8]%nat) in FR; [|reflexivity]. cbn [mk_CB_cells app] in FR.

    do 10 lstep. lstep. lstep. if_cases K; zify_cond K; [exfalso; rewrite ?unsigned_lit in K by lia; lia| clear K].

    lstep. lstep. lstep. lstep. lstep. if_cases K; zify_cond K; [clear K| exfalso; rewrite ?unsigned_lit in K by lia; lia].

    lstep. lstep. lstep. lstep. if_true.

    do 7 lstep. lstep.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m1 end.
    assert (HEAP1 : RHEAP s (osblocks (mkOss D cap blk (S f) lim) ++ LB0) m1).
    { eapply LH_frame; [exact HEAP| exact MU| exact WM|]. constructor; [apply W_ok_stack; cbn; lia| constructor]. }
    assert (AUX1 : rauxv_ok m1 B).
    { eapply rauxv_ok_frame; [exact AUX| exact MU| exact WM|]. constructor; [cbn; unfold RAUXV_CELL; lia| constructor]. }
    assert (PRES1 : lx_pres LB0 q [(O + 8, O + 112)] m m1).
    { eapply lx_pres_of_munch; [exact MU| exact WM|].
      intros a Ha [HX HC]. cbn [outside]. split; [| exact I]. destruct HC as [HC|[HC|HC]]; [lia| specialize (BLB a HC); lia| lia]. }
    unhide REP. pose proof (agree_on_of_munch _ _ _ MU WM) as AG01.
    assert (REP1 : STRREP m1 O (mkOss D cap blk (S f) lim)).
    { unfold STRREP in REP |- *. cbn [os_blk os_data os_cap] in REP |- *. destruct blk as [b|].
      - destruct REP as (R3 & (bs & BLK) & RB). pose proof RB as (A0 & A16 & _ & AC & AS). unfold OSSVerify.Proofs.simdjson.fuzz_implementations.lib.Spec.Malloc.MCEIL in AC.
        split; [| split; [| exact RB]].
        + eapply rw_cells_agree; [exact AG01| exact R3| intros a Ha; cbn in Ha; cbn [outside]; split; [lia| exact I]].
        + exists bs. eapply rw_cells_agree; [exact AG01| exact BLK| intros a Ha; cbn [cells_size csize Nat.add] in Ha; cbn [outside]; split; [lia| exact I]].
      - destruct REP as (R1 & (bs & R23) & ED). split; [| split; [| exact ED]].
        + eapply rw_cells_agree; [exact AG01| exact R1| intros a Ha; cbn in Ha; cbn [outside]; split; [lia| exact I]].
        + exists bs. eapply rw_cells_agree; [exact AG01| exact R23| intros a Ha; cbn [cells_size csize Nat.add] in Ha; cbn [outside]; split; [lia| exact I]]. }
    clear REP AG01 MU WM.
    replace (Z_to_bv 64 (O + 8 + 64)) with (Z_to_bv 64 (O + 72)) by (f_equal; lia).
    ihere. to_implM. eapply implM_bind.
    { eapply PB with (m := m1) (s := s) (LB0 := LB0) (q := q + -80) (lo := lo) (B := B) (errv := errv) (O := O) (len := len) (st := mkOss D cap blk (S f) lim);
        [exact HEAP1| exact AUX1| lia| lia| exact ST| exact CEIL'| unfold GLOBALS_TOP; lia| unfold OSS_PB_STACK, RMALLOC_STACK; lia
        | rewrite ELX; exact ERR| assumption| lia| lia| exact HL| exact REP1| exact NUM| reflexivity| exact OKB]. }
    cbv beta. intros pn s2' ms2 PO. unfold pb_post in PO. cbn [os_cap os_blk os_lim os_data os_w os_fuel] in PO.
    destruct PO as (r5 & r6 & r7 & r10 & r11 & r12 & r13 & r14 & r15 & r16 & r17 & r28 & r29 & r30 & r31 & m2 & errv2 & NEW
                    & -> & MI2 & ST2 & ERR2 & AUX2 & FA2 & SO2 & HEAP2 & REP2 & (bn & NEWC) & BRN & N16 & PRES2).
    replace (ret_pc (Z_to_bv 64 0x862e4)) with (Z_to_bv 64 0x862e4) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    rewrite ELX in ERR2.
    pose proof BRN as (N0 & NA16 & _ & NC & NS). unfold OSSVerify.Proofs.simdjson.fuzz_implementations.lib.Spec.Malloc.MCEIL in NC.

    pose proof (agree_of_lx_pres _ _ _ _ _ PRES2) as AG2.
    assert (CL : forall a, (q + -80 <= a < O + 72 \/ O + 96 <= a < O + 264) -> lx_client LB0 (q + -80) [(O + 72, O + 96)] a).
    { intros a Ha. split; [cbn [rin_ivs fst snd]; lia| left; lia]. }
    apply (rw_cells_agree _ _ _ _ _ AG2) in FR; [| intros a Ha; cbn in Ha; apply CL; lia].
    apply (rw_cells_agree _ _ _ _ _ AG2) in PUTC; [| intros a Ha; cbn in Ha; apply CL; lia].
    apply (rw_cells_agree _ _ _ _ _ AG2) in HMC; [| intros a Ha; cbn in Ha; apply CL; lia].
    apply (rw_cells_agree _ _ _ _ _ AG2) in MODE; [| intros a Ha; cbn in Ha; apply CL; lia].
    clear AG2 CL.

    apply implM_pj_part_stop; [lia|].
    unfold os_lim in REP2. cbn [os_blk os_cap] in REP2. change (match blk with Some _ => cap - 1 | None => 22 end) with lim in REP2.

    lstep.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => pose proof (rw_cells_C8_read1_g usegs mx _ _ _ REP2) as RD end. rewrite unsigned_lit in RD by lia.
    lstep. lstep. lstep. rewrite u8_lit, long_byte0 by (Z.div_mod_to_equations; lia). lstep. if_true. clear RD.

    lstep. rewrite ?(unsigned_lit (2 * cap + 1)) by lia. rewrite long_capmask by (Z.div_mod_to_equations; lia).
    lstep. lstep. replace (Z.land (2 * cap + 1) 1) with 1 by (rewrite land1_mod2; Z.div_mod_to_equations; lia). lstep. if_false.
    lstep. lstep. if_cases K; zify_cond K; [exfalso; rewrite ?unsigned_lit in K by lia; lia| clear K].

    lstep. lstep. lstep. lstep.
    replace (Z_to_bv 64 (2 * cap + -1 + - (lim + 1))) with (Z_to_bv 64 (2 * cap - lim - 2)) by (f_equal; lia).
    pose proof (munch_refl [(q - 80 - 80, q); (O + 8, O + 112); (NEW, NEW + 2 * cap)]%Z m2) as MU. pose proof (wmono_refl usegs m2) as WM.
    call (append_long_proof _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (q + -80) lo (O + 72) NEW (2 * cap) (lim + 1) (2 * cap - lim - 2) bn);
      [exact ST2| lia| unfold GLOBALS_TOP; lia| exact REP2| exact N16| exact NEWC| lia| lia| lia| lia| lia| lia| lia| lia| assumption|].
    rename PC0 into REP3. rename POST into NEWC3. rename PC into ST3.
    replace (lim + 1 + (2 * cap - lim - 2)) with (2 * cap - 1) in REP3 by lia.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m3 end.

    lstep. pose proof (rw_cells_C8_read1_g usegs m3 _ _ _ REP3) as RD. rewrite unsigned_lit in RD by lia.
    lstep. lstep. rewrite u8_lit, long_byte0 by (Z.div_mod_to_equations; lia). lstep. if_false. clear RD.

    lstep. lstep. lstep. lstep. lstep. if_true.

    lstep. lstep. lstep. lstep. lstep. lstep. lstep. lstep. lstep.
    if_cases K; zify_cond K; [clear K| exfalso; rewrite ?unsigned_lit in K by lia; lia].

    lstep. lstep. lstep. lstep. lstep. if_false.

    lstep. if_cases K; zify_cond K; [exfalso; rewrite ?unsigned_lit in K by lia; lia| clear K]. lstep.
    replace (NEW + (D + lim + - D) + 1) with (NEW + (lim + 1)) in PUTC by lia.
    replace (NEW + (D + lim + - D) + 1) with (NEW + (lim + 1)) in HMC by lia.

    assert (LBN : length x14 = Z.to_nat (2 * cap)) by (destruct NEWC3 as [[[HLx _] _] _]; exact HLx).
    apply u8arr_of_rw_cells in NEWC3.
    pose proof (u8arr_store_ok usegs _ _ _ lim (Z_to_bv 64 (NEW + (D + lim + - D))) NEWC3 ltac:(rewrite LBN; lia) ltac:(unfold wa; f_equal; lia)) as SOK.
    zstep. rewrite ?le1_smallZ by lia.
    replace (Z_to_bv 64 (NEW + (D + lim + - D))) with (wa (NEW + lim)) by (unfold wa; f_equal; lia).
    pose proof (u8arr_write usegs _ _ _ lim (Z_to_bv 8 c) NEWC3 ltac:(rewrite LBN; lia)) as NEWC4. clear NEWC3. store_done.
    apply rw_cells_of_u8arr in NEWC4. rewrite upd_length, LBN in NEWC4.

    lstep. lstep. lstep. do 10 lstep. lstep. release_frame FR ST3 q. lstep.
    replace (Z.land c 255) with c by (change 255 with (Z.ones 8); rewrite Z.land_ones by lia; symmetry; apply Z.mod_small; lia).
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m9 end.
    apply evt_done. unfold ov_post, os_grown, osblocks, os_ch, SBINV, PUTCELLS, STRREP, sb_cellsI, os_lim. cbn [os_data os_cap os_blk os_fuel os_w Nat.pred].
    do 14 eexists. exists m9, errv2, pn, NEW.
    split; [cbv delta [mkR]; reflexivity|].
    split; [assumption|]. split; [exact ST3|]. split; [rewrite ELX; exact ERR2|].
    split. { eapply rauxv_ok_frame; [exact AUX2| exact MU| exact WM|].
             constructor; [cbn; unfold RAUXV_CELL; lia|]. constructor; [cbn; unfold RAUXV_CELL; lia|]. constructor; [cbn; unfold RAUXV_CELL; lia| constructor]. }
    split; [exact FA2|]. split; [exact SO2|]. split; [reflexivity|].
    split. { eapply LH_frame; [exact HEAP2| exact MU| exact WM|].
             constructor; [apply W_ok_stack; cbn; lia|]. constructor; [apply W_ok_stack; cbn; lia|]. constructor; [| constructor].
             eapply (W_ok_block _ (pn, NEW, 2 * cap)); [left; reflexivity| cbn; lia| cbn; lia]. }
    split.
    { split.
      - unfold OSS_SB_VPTR, OSS_CLASSIC. split; [exact PUTC|]. split; [exists (NEW + (lim + 1)); split; [exact HMC| lia]| exists j108; exact MODE].
      - split; [split; [exact REP3| split; [eexists; exact NEWC4| exact BRN]]|].
        apply (OSNUM_grown len (mkOss D cap blk (S f) lim) pn NEW f HL NUM eq_refl eq_refl OKB). }
    eapply lx_pres_trans; [exact PRES1|]. eapply lx_pres_trans.
    { eapply lx_pres_weaken; [exact PRES2| lia| intros b0 Hb0; exact Hb0|]. intros a Ha. cbn [rin_ivs fst snd] in *. lia. }
    eapply lx_pres_of_munch; [exact MU| exact WM|].
    pose proof (LH_head_disj _ _ _ _ _ _ HEAP2) as DJN.
    intros a Ha [HX HC]. cbn [rin_ivs fst snd] in HX. cbn [outside]. split; [| split; [clear - HX; lia|]].
    - destruct HC as [HC|[HC|HC]]; [lia| specialize (BLB a HC); lia| lia].
    - split; [| exact I]. destruct HC as [HC|[HC|HC]]; [lia| | lia].
      intros Hs. apply (DJN a); [exact HC| lia].
  Qed.
End Proofs.
End WithCeiling0.
