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
From OSSVerify.Proofs.simdjson.fuzz_implementations.lib.P Require Import Str_tac Startup_glue Sj_stage1_kit.
From OSSVerify.Proofs.simdjson.fuzz_implementations.lib.U Require Import Layout Exit Printf_wfile Sj_iface Sj_kit Sj_new Sj_h_kit F_memcpy F_memmove_t2 Pj_loc_kit Pj_os_kit.
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

Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.

Definition xsp_frame (j8 : list byte) (ra s0 s1 s2 s3 s4 s5 : word) : list cell :=
  [CB 8 j8; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

Section Proofs.
  Hypothesis OVF : overflow_stmt.

  Lemma xsputn_exit : forall (ra gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
      (xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs4 xt3 xt4 xt5 xt6 : word) (j8 : list byte)
      (F : bvmap 5 word) (fc : bv 32) (m0 m : mem) (s0' s : PState) (LB0 : list block) (q lo B : Z) (errv : word)
      (O len N : Z) (st0 st : ossst),
    RHEAP s (osblocks st ++ LB0) m -> rauxv_ok m B -> q <= B -> B < 2^63 ->
    stk usegs m lo (q + -64) -> alloc_ceiling <= lo -> GLOBALS_TOP <= lo -> lo <= q - 64 ->
    rw_cells usegs m LX_ERRNO [C4 errv] -> mem_inv usegs m -> q <= O -> O + 264 <= B ->
    0 <= len <= SJ_PADMAX -> SBINV m O len st -> os_w st = os_w st0 + N -> 0 <= N < 2^63 ->
    ps_fa s = ps_fa s0' -> ps_so s = ps_so s0' ->
    lx_pres LB0 q [(O + 8, O + 112)] m0 m ->
    rw_cells usegs m (q + -64) (xsp_frame j8 ra s0 s1 s2 s3 s4 s5) ->
    implM usegs (pj_part raw_malloc raw_free ps_so set_so_ps (os_fuel st) len (os_cap st) (os_blk st)) s
          (xsputn_post ra q gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s0' LB0 lo B O len N st0 m0)
          (MS (mkR xra (Z_to_bv 64 (q + -64)) gp (Z_to_bv 64 RATP) xt0 xt1 xt2 (Z_to_bv 64 N) (Z_to_bv 64 N) xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7
                   xs2 (Z_to_bv 64 (O + 8)) xs4 (Z_to_bv 64 (-1)) s6 s7 s8 s9 s10 s11 xt3 xt4 xt5 xt6)
              F (Z_to_bv 64 0x85658) fc None m (seg_rom usegs)).
  Proof.
    intros until st. intros HEAP AUX QB B63 ST CEIL GLO LOQ ERR MI QO OB HL INV W N63 FA SO PRES FR.
    unfold GLOBALS_TOP in *. assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    pose proof (OSNUM_cap24 len st ltac:(apply INV)) as C24.
    apply implM_pj_part_stop; [lia|].
    destruct INV as ((PUTC & (hm & HMC & HMR) & (j108 & MODE)) & REP & NUM). hide REP. hide PUTC. hide HMC. hide MODE.
    pose proof (munch_refl [(q - 64, q)]%Z m) as MU. pose proof (wmono_refl usegs m) as WM.
    unfold xsp_frame in FR.

    step. do 7 step. step. release_frame FR ST q. step.
    apply evt_done. unfold xsputn_post.
    do 14 eexists. exists m, errv, st.
    split; [cbv delta [mkR]; reflexivity|].

    split; [assumption|]. split; [exact ST|]. split; [exact ERR|]. split; [exact AUX|].
    split; [exact FA|]. split; [exact SO|]. split; [reflexivity|]. split; [exact W|].
    split; [exact HEAP|]. split; [| exact PRES].
    unhide REP. unhide PUTC. unhide HMC. unhide MODE.
    split; [| split; [exact REP| exact NUM]]. split; [exact PUTC|]. split; [exists hm; split; [exact HMC| exact HMR]| exists j108; exact MODE].
  Qed.

  Lemma xsputn_loop : forall (k : nat) (ra gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
      (xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs4 xt3 xt4 xt5 xt6 : word) (j8 : list byte)
      (F : bvmap 5 word) (fc : bv 32) (m0 m : mem) (s0' s : PState) (LB0 : list block) (q lo B : Z) (errv : word)
      (O len S N i : Z) (st0 st : ossst) (bs : list byte),
    N - i <= Z.of_nat k ->
    RHEAP s (osblocks st ++ LB0) m -> rauxv_ok m B -> q <= B -> B < 2^63 ->
    stk usegs m lo (q + -64) -> alloc_ceiling <= lo -> GLOBALS_TOP <= lo -> lo <= q - OSS_XSPUTN_STACK ->
    rw_cells usegs m LX_ERRNO [C4 errv] -> mem_inv usegs m -> q <= O -> O + 264 <= B -> imp_vt_rows m ->
    0 <= len <= SJ_PADMAX -> SBINV m O len st -> os_w st = os_w st0 + i -> 0 <= i < N -> N < 2^40 ->
    rw_cells usegs m S [CB (Z.to_nat N) bs] -> 0 <= S -> src_ok LB0 O B S N ->
    os_w st + (N - i) <= PJ_OUTMAX len ->
    ps_fa s = ps_fa s0' -> ps_so s = ps_so s0' ->
    lx_pres LB0 q [(O + 8, O + 112)] m0 m ->
    rw_cells usegs m (q + -64) (xsp_frame j8 ra s0 s1 s2 s3 s4 s5) ->
    implM usegs (pj_part raw_malloc raw_free ps_so set_so_ps (os_fuel st) len (os_cap st) (os_blk st)) s
          (xsputn_post ra q gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s0' LB0 lo B O len N st0 m0)
          (MS (mkR xra (Z_to_bv 64 (q + -64)) gp (Z_to_bv 64 RATP) xt0 xt1 xt2 (Z_to_bv 64 i) (Z_to_bv 64 N) xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7
                   (Z_to_bv 64 (S + i)) (Z_to_bv 64 (O + 8)) xs4 (Z_to_bv 64 (-1)) s6 s7 s8 s9 s10 s11 xt3 xt4 xt5 xt6)
              F (Z_to_bv 64 0x855f8) fc None m (seg_rom usegs)).
  Proof.
    induction k as [|k IH]; intros until bs; intros HK HEAP AUX QB B63 ST CEIL GLO LO ERR MI QO OB VT HL INV W IR NB BUFC S0 SRC ACC FA SO PRES FR; [lia|].
    unfold OSS_XSPUTN_STACK, OSS_OV_STACK, OSS_PB_STACK, RMALLOC_STACK, GLOBALS_TOP in *.
    assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    pose proof CEIL as CEIL'. unfold OSSVerify.Proofs.simdjson.fuzz_implementations.lib.Spec.Malloc.MCEIL in CEIL; try (pose proof alloc_ceiling_range as CEIL_RANGE__).
    assert (ELX : LX_ERRNO = 1004708) by reflexivity. rewrite ELX in ERR.
    assert (BLB : forall a, in_block LB0 a -> a < alloc_ceiling).
    { intros a (b & Hb & Hr). pose proof (LH_block_range _ _ _ _ HEAP ltac:(apply in_or_app; right; exact Hb)) as (_ & _ & _ & BC & _).
      unfold OSSVerify.Proofs.simdjson.fuzz_implementations.lib.Spec.Malloc.MCEIL in BC. lia. }
    assert (SSEP : S + N <= lo \/ (O + 264 <= S /\ S + N <= B)).
    { destruct SRC as [(bk & Hbk & Hlo & Hhi)|[H1 H2]]; [left| right; split; [exact H1| exact H2]].
      pose proof (LH_block_range _ _ _ _ HEAP ltac:(apply in_or_app; right; exact Hbk)) as (_ & _ & _ & BC & _).
      unfold OSSVerify.Proofs.simdjson.fuzz_implementations.lib.Spec.Malloc.MCEIL in BC. lia. }
    assert (LBS : length bs = Z.to_nat N) by (destruct BUFC as [[[HLx _] _] _]; exact HLx).
    pose proof (OSNUM_cap24 len st ltac:(apply INV)) as CAP24. pose proof (PJ_CAPMAX_bound len HL) as CMB.
    destruct st as [D cap blk fuel w]. cbn [os_data os_cap os_blk os_fuel os_w] in *.
    destruct INV as ((PUTC & (hm & HMC & HMR) & (j108 & MODE)) & REP & NUM).
    unfold sb_cellsI, os_lim in PUTC. cbn [os_data os_cap os_blk os_fuel os_w] in PUTC. cbn [os_data os_w] in HMR.
    pose proof NUM as (WB & FU & CB16 & HB). unfold os_lim, os_k in WB, FU, CB16, HB. cbn [os_data os_cap os_blk os_fuel os_w] in WB, FU, CB16, HB.
    unfold OSS_SB_VPTR, OSS_CLASSIC in PUTC.
    set (lim := match blk with Some _ => cap - 1 | None => 22 end) in *.
    assert (LIMR : 22 <= lim < cap) by (subst lim; destruct blk; [lia| destruct HB as [EC _]; unfold IMP_SCAP0 in EC; lia]).
    assert (DR : 0 < D /\ D + cap < 2^63 /\ (D + cap <= lo \/ q <= D)).
    { unfold STRREP in REP. cbn [os_blk os_data os_cap] in REP. destruct blk.
      - destruct REP as (_ & _ & (A0 & A16 & _ & AC & AS)). unfold OSSVerify.Proofs.simdjson.fuzz_implementations.lib.Spec.Malloc.MCEIL in AC. lia.
      - destruct REP as (_ & _ & ->). destruct HB as [EC _]. unfold IMP_SCAP0 in EC. lia. }
    unfold xsp_frame in FR.
    destruct (Z.eq_dec w lim) as [FULL|ROOM].
    -
      destruct (OSNUM_fuel len (mkOss D cap blk fuel w) HL NUM) as [f EF]. cbn [os_fuel] in EF. subst fuel.
      assert (OKB : chain_ok len cap (2 * cap) = true).
      { apply (os_grow_ok len (mkOss D cap blk (Datatypes.S f) w) (N - i) ltac:(lia) NUM); [| lia| cbn [os_w]; lia].
        unfold os_lim. cbn [os_w os_blk os_cap]. change (match blk with Some _ => cap - 1 | None => 22 end) with lim. exact FULL. }
      apply implM_pj_part_seq.
      destruct VT as (V1 & V2 & V3 & V4). unfold OSS_GOT_VT, OSS_VTT, OSS_VBOFF, OSS_SBVT, OSS_XSPUTN, OSS_OVERFLOW, OSS_OS_VPTR, OSS_OS_CVPTR, OSS_IOS_CVPTR, OSS_IOS_VPTR, OSS_SB_VPTR, OSS_SBB_VPTR in V1, V2, V3, V4.

      assert (LBS' : (Z.to_nat i < length bs)%nat) by lia.
      destruct (nth_error bs (Z.to_nat i)) as [b|] eqn:Hn; [| exfalso; apply nth_error_None in Hn; lia].
      pose proof (u8arr_read usegs m S bs i b (Z_to_bv 64 (S + i)) (u8arr_of_rw_cells _ _ _ _ _ BUFC) Hn ltac:(lia) ltac:(reflexivity)) as RD.
      pose proof (bv_unsigned_in_range 8 b) as BR. unfold bv_modulus in BR. cbn in BR.
      hide REP.
      unfold implM. iprefix.

      lstep. lstep. lstep. if_cases K; zify_cond K; [clear K| exfalso; rewrite ?unsigned_lit in K by lia; lia].

      lstep. lstep. lstep. lstep. lstep.
      ihere. to_implM. eapply implM_bind.
      { eapply OVF with (m := m) (s := s) (LB0 := LB0) (q := q + -64) (lo := lo) (B := B) (errv := errv) (O := O) (len := len)
                        (st := mkOss D cap blk (Datatypes.S f) w) (f := f);
          [exact HEAP| exact AUX| lia| lia| exact ST| exact CEIL'| unfold GLOBALS_TOP; lia| unfold OSS_OV_STACK, OSS_PB_STACK, RMALLOC_STACK; lia
          | exact ERR| assumption| lia| lia| exact HL
          | unhide REP; split; [split; [exact PUTC| split; [exists hm; split; [exact HMC| exact HMR]| exists j108; exact MODE]]| split; [exact REP| exact NUM]]
          | unfold os_lim; cbn [os_w os_blk os_cap]; change (match blk with Some _ => cap - 1 | None => 22 end) with lim; exact FULL
          | reflexivity| lia| exact OKB]. }
      cbv beta. intros ch s' ms' PO. unfold ov_post in PO.
      destruct PO as (r5 & r6 & r7 & r11 & r12 & r13 & r14 & r15 & r16 & r17 & r28 & r29 & r30 & r31 & m2 & errv2 & b' & NEW
                      & -> & MI2 & ST2 & ERR2 & AUX2 & FA2 & SO2 & ECH & HEAP2 & INV2 & PRES2).
      subst ch. replace (ret_pc (Z_to_bv 64 0x85640)) with (Z_to_bv 64 0x85640) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
      rewrite ELX in ERR2. unfold os_ch. cbn [ch_fuel ch_cap ch_blk os_fuel os_cap os_blk os_grown fst snd Nat.pred].

      pose proof (agree_of_lx_pres _ _ _ _ _ PRES2) as AG2.
      apply (rw_cells_agree _ _ _ _ _ AG2) in FR; [| intros a Ha; cbn in Ha; split; [cbn [rin_ivs fst snd]; lia| left; lia]].
      apply (rw_cells_agree _ _ _ _ _ AG2) in BUFC.
      2:{ intros a Ha. cbn [cells_size csize Nat.add] in Ha. split; [cbn [rin_ivs fst snd]; lia|].
          destruct SRC as [(bk & Hbk & Hlo & Hhi)|[H1 H2]]; [right; left; exists bk; split; [exact Hbk| lia]| left; lia]. }
      assert (STC : forall a, 913408 <= a < 924400 -> lx_client LB0 (q + -64) [(O + 8, O + 112)] a).
      { intros a Ha. split; [cbn [rin_ivs fst snd]; lia| right; right]. split; [lia|].
        unfold ralloc_static, RMallocRep.RLIBC, RMallocRep.RCTX, RMallocRep.RERRNO, RMallocRep.RSSP_GUARD, RMallocRep.RGOT_SSP. lia. }
      apply (rw_cells_agree _ _ _ _ _ AG2) in V1; [| intros a Ha; cbn in Ha; apply STC; lia].
      apply (rw_cells_agree _ _ _ _ _ AG2) in V2; [| intros a Ha; cbn in Ha; apply STC; lia].
      apply (rw_cells_agree _ _ _ _ _ AG2) in V3; [| intros a Ha; cbn in Ha; apply STC; lia].
      apply (rw_cells_agree _ _ _ _ _ AG2) in V4; [| intros a Ha; cbn in Ha; apply STC; lia].
      assert (VT2 : imp_vt_rows m2) by (split; [exact V1| split; [exact V2| split; [exact V3| exact V4]]]).
      assert (PRES02 : lx_pres LB0 q [(O + 8, O + 112)] m0 m2).
      { eapply lx_pres_trans; [exact PRES|]. eapply lx_pres_weaken; [exact PRES2| lia| intros b0 Hb0; exact Hb0| intros a Ha; exact Ha]. }
      clear AG2 STC HEAP AUX ST PRES ERR MI RD.
      unfold implM. iprefix.

      lstep. if_cases K; zify_cond K; [exfalso; rewrite ?unsigned_lit in K by lia; lia| try clear K].
      lstep. lstep. lstep. if_cases K; zify_cond K; rewrite ?signed_lit in K by lia.
      +
        replace (Z_to_bv 64 (S + i + 1)) with (Z_to_bv 64 (S + (i + 1))) by (f_equal; lia).
        ihere. to_implM.
        eapply (IH _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m0 m2 s0' s' LB0 q lo B errv2 O len S N (i + 1) st0 (os_grown (mkOss D cap blk (Datatypes.S f) w) b' NEW) bs);
          [lia| exact HEAP2| exact AUX2| lia| lia| exact ST2| exact CEIL'| unfold GLOBALS_TOP; lia| unfold OSS_XSPUTN_STACK, OSS_OV_STACK, OSS_PB_STACK, RMALLOC_STACK; lia
          | exact ERR2| assumption| lia| lia| exact VT2| exact HL| exact INV2| cbn [os_w os_grown]; lia| lia| lia| exact BUFC| lia| exact SRC
          | cbn [os_w os_grown]; lia| congruence| congruence| exact PRES02| unfold xsp_frame; exact FR].
      +
        lstep.
        replace (Z_to_bv 64 (i + 1)) with (Z_to_bv 64 N) by (f_equal; lia).
        ihere. to_implM.
        eapply xsputn_exit with (m0 := m0) (s0' := s0') (st0 := st0) (st := os_grown (mkOss D cap blk (Datatypes.S f) w) b' NEW) (LB0 := LB0) (lo := lo) (B := B) (len := len) (errv := errv2);
          [exact HEAP2| exact AUX2| lia| lia| exact ST2| exact CEIL'| unfold GLOBALS_TOP; lia| lia| exact ERR2| assumption| lia| lia| exact HL| exact INV2
          | cbn [os_w os_grown]; lia| lia| congruence| congruence| exact PRES02| unfold xsp_frame; exact FR].
    -
      pose proof (munch_refl [(q - 64 - 80 - 64 - 16 - 8192, q); (O + 8, O + 112)]%Z m) as MU. pose proof (wmono_refl usegs m) as WM.
      hide REP.
      unfold implM. iprefix.

      lstep. lstep. lstep. if_cases K; zify_cond K; [exfalso; rewrite ?unsigned_lit in K by lia; lia| try clear K].

      lstep. lstep.
      set (n := Z.min (N - i) (lim - w)).
      assert (NR : 1 <= n /\ n <= N - i /\ n <= lim - w) by (subst n; lia).

      assert (DBUF : exists dlen dbs, rw_cells usegs m D [CB dlen dbs] /\ lim + 1 <= Z.of_nat dlen <= cap
                     /\ dlen = match blk with None => 23%nat | Some _ => Z.to_nat cap end
                     /\ match blk with None => rw_cells usegs m (O + 72) [C1 (Z_to_bv 8 44)] /\ D = O + 73
                                      | Some _ => rw_cells usegs m (O + 72) [C8 (Z_to_bv 64 (cap + 1)); C8 (Z_to_bv 64 (cap - 1)); C8 (Z_to_bv 64 D)] /\ rblock_range D cap end).
      { unhide REP. unfold STRREP in REP. cbn [os_blk os_data os_cap] in REP. destruct blk.
        - destruct REP as (R3 & (dbs & BLK) & RB). exists (Z.to_nat cap), dbs. split; [exact BLK|]. split; [lia|]. split; [reflexivity|]. split; [exact R3| exact RB].
        - destruct REP as (R1 & (dbs & R23) & ED). exists 23%nat, dbs. rewrite <- ED in R23. split; [exact R23|].
          destruct HB as [EC _]. unfold IMP_SCAP0 in EC. split; [lia|]. split; [reflexivity|]. split; [exact R1| exact ED]. }
      clear REP. destruct DBUF as (dlen & dbs & DBUF & DLEN & EDL & REPX).

      assert (SEP2 : S + N <= D \/ D + lim + 1 <= S).
      { destruct SRC as [(bk & Hbk & Hlo & Hhi)|[H1 H2]].
        - destruct blk as [b|].
          + destruct REPX as [_ RB]. cbn [osblocks os_blk os_data os_cap app] in HEAP.
            destruct bk as [[pk Ak] nk]. cbn [blk_addr blk_size fst snd] in Hlo, Hhi.
            pose proof (LH_head_sep _ _ _ _ _ _ pk Ak nk HEAP Hbk). lia.
          + destruct REPX as [_ ED]. lia.
        - destruct blk as [b|]; [destruct REPX as [_ (A0 & A16 & _ & AC & AS)]; unfold OSSVerify.Proofs.simdjson.fuzz_implementations.lib.Spec.Malloc.MCEIL in AC| destruct REPX as [_ ED]]; lia. }
      lazymatch goal with |- evt ?sg ?Q (MS ?R ?FF _ ?fcc ?rv ?mm ?ro) =>
        lazymatch R with context C [Z_to_bv 64 (N + - i)] =>
          let R' := context C [Z_to_bv 64 n] in
          assert (JOIN : evt sg Q (MS R' FF (Z_to_bv 64 0x85614) fcc rv mm ro))
        end end.
      {

        lstep. if_cases K; zify_cond K; [exfalso; rewrite ?unsigned_lit in K by lia; lia| try clear K].
        lstep. lstep. lstep.

        destruct (rw_cells_CB_at _ _ _ _ i BUFC ltac:(lia)) as [SB1 SB2].
        destruct (rw_cells_CB_at _ _ _ _ n SB2 ltac:(lia)) as [SRCn SB3].
        pose proof SRCn as SRCb. apply rw_cells_bytes_at in SRCb. cbn [cells_bytes cbytes] in SRCb. rewrite app_nil_r in SRCb.
        assert (LSRC : length (firstn (Z.to_nat n) (skipn (Z.to_nat i) bs)) = Z.to_nat n) by (rewrite firstn_length_le; [reflexivity| rewrite length_skipn; lia]).
        destruct (rw_cells_CB_at _ _ _ _ w DBUF ltac:(lia)) as [DB1 DB2].
        destruct (rw_cells_CB_at _ _ _ _ n DB2 ltac:(lia)) as [DSTn DB3]. clear DB2 SB2.
        hide SRCn. hide SB1. hide SB3. hide DB1. hide DB3. hide BUFC. hide DBUF.
        eapply evt_cut.
        { eapply memmove_far_callZ with (Dst := D + w) (Src := S + i) (N := n);
            [exact SRCb| exact LSRC| exact DSTn| lia| lia| lia| lia| lia| lia| assumption]. }
        intros ms' PO. unfold memcpy_postZ in PO.
        destruct PO as (u5 & u6 & u7 & u11 & u12 & u13 & u14 & u15 & u16 & u17 & u28 & u29 & u30 & u31 & m4 & -> & MU4 & WM4 & MI4 & DST4 & SRC4).
        replace (ret_pc (Z_to_bv 64 0x85624)) with (Z_to_bv 64 0x85624) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
        pose proof (agree_on_of_munch _ _ _ MU4 WM4) as AG4.
        assert (DW : (D + cap <= lo /\ (D + cap <= 65536 \/ 1142784 <= D) /\ lim = cap - 1) \/ (D = O + 73 /\ lim = 22)).
        { destruct blk as [b|]; [left; destruct REPX as [_ (A0 & A16 & _ & AC & AS)]; unfold OSSVerify.Proofs.simdjson.fuzz_implementations.lib.Spec.Malloc.MCEIL in AC; repeat split; try lia; reflexivity
                                | right; destruct REPX as [_ ED]; split; [exact ED| reflexivity]]. }
        apply (rw_cells_agree _ _ _ _ _ AG4) in FR; [| intros a Ha; cbn in Ha; cbn [outside]; split; [lia| exact I]].
        apply (rw_cells_agree _ _ _ _ _ AG4) in PUTC; [| intros a Ha; cbn in Ha; cbn [outside]; split; [lia| exact I]].
        apply (rw_cells_agree _ _ _ _ _ AG4) in HMC; [| intros a Ha; cbn in Ha; cbn [outside]; split; [lia| exact I]].
        apply (rw_cells_agree _ _ _ _ _ AG4) in MODE; [| intros a Ha; cbn in Ha; cbn [outside]; split; [lia| exact I]].
        apply (rw_cells_agree _ _ _ _ _ AG4) in ERR; [| intros a Ha; cbn in Ha; cbn [outside]; split; [lia| exact I]].
        assert (VT4 : imp_vt_rows m4).
        { destruct VT as (V1 & V2 & V3 & V4). unfold imp_vt_rows, OSS_GOT_VT, OSS_VTT, OSS_VBOFF, OSS_SBVT in *.
          repeat split; (eapply rw_cells_agree; [exact AG4| eassumption| intros a Ha; cbn in Ha; cbn [outside]; split; [lia| exact I]]). }
        assert (REPX4 : match blk with None => rw_cells usegs m4 (O + 72) [C1 (Z_to_bv 8 44)] /\ D = O + 73
                        | Some _ => rw_cells usegs m4 (O + 72) [C8 (Z_to_bv 64 (cap + 1)); C8 (Z_to_bv 64 (cap - 1)); C8 (Z_to_bv 64 D)] /\ rblock_range D cap end).
        { destruct blk as [b|].
          - destruct REPX as [R3 RB]. split; [| exact RB]. eapply rw_cells_agree; [exact AG4| exact R3| intros a Ha; cbn in Ha; cbn [outside]; split; [lia| exact I]].
          - destruct REPX as [R1 ED]. split; [| exact ED]. eapply rw_cells_agree; [exact AG4| exact R1| intros a Ha; cbn in Ha; cbn [outside]; split; [lia| exact I]]. }
        unhide BUFC. apply (rw_cells_agree _ _ _ _ _ AG4) in BUFC; [| intros a Ha; cbn [cells_size csize Nat.add] in Ha; cbn [outside]; split; [lia| exact I]].
        unhide DB1. apply (rw_cells_agree _ _ _ _ _ AG4) in DB1; [| intros a Ha; cbn [cells_size csize Nat.add] in Ha; cbn [outside]; split; [lia| exact I]].
        unhide DB3. apply (rw_cells_agree _ _ _ _ _ AG4) in DB3; [| intros a Ha; cbn [cells_size csize Nat.add] in Ha; cbn [outside]; split; [lia| exact I]].
        pose proof (rw_cells_CB_join2 _ _ _ _ _ _ _ DB1 DST4 ltac:(lia)) as DB12.
        pose proof (rw_cells_CB_join2 _ _ _ _ _ _ _ DB12 DB3 ltac:(lia)) as DBUF4. clear DB1 DST4 DB12 DB3 SRCn SB1 SB3 DBUF DSTn SRCb SRC4.
        replace (Z.to_nat w + Z.to_nat n + (dlen - Z.to_nat w - Z.to_nat n))%nat with dlen in DBUF4 by lia.
        assert (HEAP4 : RHEAP s (osblocks (mkOss D cap blk fuel w) ++ LB0) m4).
        { eapply LH_frame; [exact HEAP| exact MU4| exact WM4|]. constructor; [| constructor].
          destruct blk as [b|]; [| apply W_ok_stack; cbn; destruct REPX as [_ ED]; lia].
          cbn [osblocks os_blk os_data os_cap app]. eapply (W_ok_block _ (b, D, cap)); [left; reflexivity| cbn; lia| cbn; lia]. }
        assert (AUX4 : rauxv_ok m4 B).
        { eapply rauxv_ok_frame; [exact AUX| exact MU4| exact WM4|]. constructor; [cbn; unfold RAUXV_CELL; lia| constructor]. }
        assert (ST4 : stk usegs m4 lo (q + -64)) by (eapply stk_transport_disjoint; [exact ST| exact MU4| exact WM4| cbn [disjoint_from]; lia]).
        assert (PRES4 : lx_pres LB0 q [(O + 8, O + 112)] m0 m4).
        { eapply lx_pres_trans; [exact PRES|]. eapply lx_pres_of_munch; [exact MU4| exact WM4|].
          intros a Ha [HX HC]. cbn [rin_ivs fst snd] in HX. cbn [outside]. split; [| exact I].
          destruct blk as [b|]; [| destruct REPX as [_ ED]; lia].
          cbn [osblocks os_blk os_data os_cap app] in HEAP. pose proof (LH_head_disj _ _ _ _ _ _ HEAP) as DJN.
          destruct HC as [HC|[HC|HC]]; [lia| | lia]. intros Hs. apply (DJN a); [exact HC| lia]. }
        clear AG4 MU4 WM4 HEAP AUX ST PRES MI MU WM.
        pose proof (munch_refl [(O + 56, O + 64)]%Z m4) as MU5. pose proof (wmono_refl usegs m4) as WM5.

        lstep. lstep. lstep. lstep. lstep. lstep. lstep.
        lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m5 end.
        replace (D + w + n) with (D + (w + n)) in PUTC by lia.
        pose proof (agree_on_of_munch _ _ _ MU5 WM5) as AG5.
        assert (HEAP5 : RHEAP s (osblocks (os_adv (mkOss D cap blk fuel w) n) ++ LB0) m5).
        { cbn [osblocks os_adv os_blk os_data os_cap]. eapply LH_frame; [exact HEAP4| exact MU5| exact WM5|]. constructor; [apply W_ok_stack; cbn; lia| constructor]. }
        assert (AUX5 : rauxv_ok m5 B).
        { eapply rauxv_ok_frame; [exact AUX4| exact MU5| exact WM5|]. constructor; [cbn; unfold RAUXV_CELL; lia| constructor]. }
        assert (VT5 : imp_vt_rows m5) by (eapply imp_vt_rows_transport; [exact VT4| exact MU5| exact WM5| cbn; lia]).
        assert (PRES5 : lx_pres LB0 q [(O + 8, O + 112)] m0 m5).
        { eapply lx_pres_trans; [exact PRES4|]. eapply lx_pres_of_munch; [exact MU5| exact WM5|].
          intros a Ha [HX HC]. cbn [rin_ivs fst snd] in HX. cbn [outside]. split; [lia| exact I]. }
        assert (INV5 : SBINV m5 O len (os_adv (mkOss D cap blk fuel w) n)).
        { unfold SBINV, PUTCELLS, STRREP, sb_cellsI, os_adv, os_lim. cbn [os_data os_cap os_blk os_fuel os_w]. split; [| split].
          - unfold OSS_SB_VPTR, OSS_CLASSIC. split; [exact PUTC|]. split; [exists hm; split; [exact HMC| lia]| exists j108; exact MODE].
          - destruct blk as [b|].
            + destruct REPX4 as [R3 RB]. split; [| split; [| exact RB]].
              * eapply rw_cells_agree; [exact AG5| exact R3| intros a Ha; cbn in Ha; cbn [outside]; split; [lia| exact I]].
              * subst dlen. eexists. exact DBUF4.
            + destruct REPX4 as [R1 ED]. split; [| split; [| exact ED]].
              * eapply rw_cells_agree; [exact AG5| exact R1| intros a Ha; cbn in Ha; cbn [outside]; split; [lia| exact I]].
              * subst dlen. rewrite <- ED. eexists. exact DBUF4.
          - apply (OSNUM_adv len (mkOss D cap blk fuel w) n NUM); [lia| unfold os_lim; cbn [os_w os_blk os_cap]; change (match blk with Some _ => cap - 1 | None => 22 end) with lim; lia]. }
        clear AG5 HEAP4 AUX4 VT4 PRES4 REPX4 DBUF4.
        if_cases K; zify_cond K.
        +
          rewrite ?signed_lit in K by lia.
          replace (Z_to_bv 64 (n + i)) with (Z_to_bv 64 N) by (f_equal; lia).
          ihere. to_implM.
          eapply xsputn_exit with (m0 := m0) (s0' := s0') (st0 := st0) (st := os_adv (mkOss D cap blk fuel w) n) (LB0 := LB0) (lo := lo) (B := B) (len := len) (errv := errv);
            [exact HEAP5| exact AUX5| lia| lia| exact ST4| exact CEIL'| unfold GLOBALS_TOP; lia| lia| exact ERR| assumption| lia| lia| exact HL| exact INV5
            | cbn [os_w os_adv]; lia| lia| exact FA| exact SO| exact PRES5| unfold xsp_frame; exact FR].
        +
          rewrite ?signed_lit in K by lia.
          replace (Z_to_bv 64 (S + i + n)) with (Z_to_bv 64 (S + (n + i))) by (f_equal; lia).
          ihere. to_implM.
          eapply (IH _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m0 m5 s0' s LB0 q lo B errv O len S N (n + i) st0 (os_adv (mkOss D cap blk fuel w) n) bs);
            [lia| exact HEAP5| exact AUX5| lia| lia| exact ST4| exact CEIL'| unfold GLOBALS_TOP; lia| unfold OSS_XSPUTN_STACK, OSS_OV_STACK, OSS_PB_STACK, RMALLOC_STACK; lia
            | exact ERR| assumption| lia| lia| exact VT5| exact HL| exact INV5| cbn [os_w os_adv]; lia| lia| lia| exact BUFC| lia| exact SRC
            | cbn [os_w os_adv]; lia| exact FA| exact SO| exact PRES5| unfold xsp_frame; exact FR]. }
      lstep. if_cases K; zify_cond K; rewrite ?signed_lit in K by lia.
      + exact_evt JOIN.
      + lstep. exact_evt JOIN.
  Qed.

  Theorem xsputn_proof : xsputn_stmt.
  Proof.
    unfold xsputn_stmt, OSS_XSPUTN. intros until bs. intros HEAP AUX QB B63 ST CEIL GLO LO ERR MI QO OB VT HL INV BUFC N1 S0 SRC ACC.
    unfold OSS_XSPUTN_STACK, OSS_OV_STACK, OSS_PB_STACK, RMALLOC_STACK, GLOBALS_TOP in *.
    assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    assert (BLB : forall a, in_block LB0 a -> a < alloc_ceiling).
    { intros a (b & Hb & Hr). pose proof (LH_block_range _ _ _ _ HEAP ltac:(apply in_or_app; right; exact Hb)) as (_ & _ & _ & BC & _).
      unfold OSSVerify.Proofs.simdjson.fuzz_implementations.lib.Spec.Malloc.MCEIL in BC. lia. }
    assert (NB : N < 2^40).
    { pose proof (PJ_CAPMAX_bound len HL). destruct INV as (_ & _ & (WB & _)). unfold PJ_CAPMAX in *. lia. }
    destruct INV as ((PUTC & (hm & HMC & HMR) & (j108 & MODE)) & REP & NUM).
    assert (ELX : LX_ERRNO = 1004708) by reflexivity. rewrite ELX in ERR.
    assert (SSEP : S + N <= lo \/ (O + 264 <= S /\ S + N <= B)).
    { destruct SRC as [(bk & Hbk & Hlo & Hhi)|[H1 H2]]; [left| right; split; [exact H1| exact H2]].
      pose proof (LH_block_range _ _ _ _ HEAP ltac:(apply in_or_app; right; exact Hbk)) as (_ & _ & _ & BC & _).
      unfold OSSVerify.Proofs.simdjson.fuzz_implementations.lib.Spec.Malloc.MCEIL in BC. lia. }
    pose proof (munch_refl [(q - 64, q)]%Z m) as MU. pose proof (wmono_refl usegs m) as WM.
    hide REP.
    unfold implM. iprefix.
    lstep. carve_frame 64%nat ST.
    apply (rw_cells_split_CB usegs _ _ [] 64 junk [] [8;8;8;8;8;8;8;8]%nat) in FR; [|reflexivity]. cbn [mk_CB_cells app] in FR.

    do 7 lstep. lstep. if_cases K; zify_cond K; [exfalso; rewrite ?unsigned_lit in K by lia; lia| try clear K].
    do 5 lstep. lstep.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m1 end.
    assert (HEAP1 : RHEAP s (osblocks st ++ LB0) m1).
    { eapply LH_frame; [exact HEAP| exact MU| exact WM|]. constructor; [apply W_ok_stack; cbn; lia| constructor]. }
    assert (AUX1 : rauxv_ok m1 B).
    { eapply rauxv_ok_frame; [exact AUX| exact MU| exact WM|]. constructor; [cbn; unfold RAUXV_CELL; lia| constructor]. }
    assert (VT1 : imp_vt_rows m1) by (eapply imp_vt_rows_transport; [exact VT| exact MU| exact WM| cbn; lia]).
    assert (PRES1 : lx_pres LB0 q [(O + 8, O + 112)] m m1).
    { eapply lx_pres_of_munch; [exact MU| exact WM|].
      intros a Ha [HX HC]. cbn [outside]. split; [| exact I]. destruct HC as [HC|[HC|HC]]; [lia| specialize (BLB a HC); lia| lia]. }
    unhide REP.
    assert (INV1 : SBINV m1 O len st).
    { split; [split; [exact PUTC| split; [exists hm; split; [exact HMC| exact HMR]| exists j108; exact MODE]]| split; [| exact NUM]].
      pose proof (agree_on_of_munch _ _ _ MU WM) as AG.
      unfold STRREP in REP |- *. destruct (os_blk st).
      - destruct REP as (R3 & (bsr & BLK) & RB). pose proof RB as (A0 & A16 & _ & AC & AS). unfold OSSVerify.Proofs.simdjson.fuzz_implementations.lib.Spec.Malloc.MCEIL in AC.
        split; [| split; [| exact RB]].
        + eapply rw_cells_agree; [exact AG| exact R3| intros a Ha; cbn in Ha; cbn [outside]; split; [lia| exact I]].
        + exists bsr. eapply rw_cells_agree; [exact AG| exact BLK| intros a Ha; cbn [cells_size csize Nat.add] in Ha; cbn [outside]; split; [lia| exact I]].
      - destruct REP as (R1 & (bsr & R23) & ED). split; [| split; [| exact ED]].
        + eapply rw_cells_agree; [exact AG| exact R1| intros a Ha; cbn in Ha; cbn [outside]; split; [lia| exact I]].
        + exists bsr. eapply rw_cells_agree; [exact AG| exact R23| intros a Ha; cbn [cells_size csize Nat.add] in Ha; cbn [outside]; split; [lia| exact I]]. }
    clear REP MU WM HEAP AUX VT.
    replace (Z_to_bv 64 S) with (Z_to_bv 64 (S + 0)) by (f_equal; lia).
    ihere. to_implM.
    eapply (xsputn_loop (Z.to_nat N) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m m1 s s LB0 q lo B errv O len S N 0 st st bs);
      [lia| exact HEAP1| exact AUX1| lia| lia| exact ST| exact CEIL| unfold GLOBALS_TOP; lia| unfold OSS_XSPUTN_STACK, OSS_OV_STACK, OSS_PB_STACK, RMALLOC_STACK; lia
      | exact ERR| assumption| lia| lia| exact VT1| exact HL| exact INV1| lia| lia| exact NB| exact BUFC| lia| exact SRC
      | lia| reflexivity| reflexivity| exact PRES1| unfold xsp_frame; exact FR].
  Qed.
End Proofs.
End WithCeiling0.
