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

Lemma str_short_tail : forall (ra gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
    (xt0 xt1 xt2 xa3 xa4 xa5 xa6 xa7 xs0 xs1 xs2 xs3 xs5 xt3 xt4 xt5 xt6 : word) (j8 : list byte)
    (F : bvmap 5 word) (fc : bv 32) (m0 m : mem) (q lo O R D L : Z) (dlen : nat) (dbs junk : list byte),
  stk usegs m lo (q + -64) -> GLOBALS_TOP <= lo -> lo <= q - 64 -> 0 <= q ->
  q <= O -> O + 264 < 2^62 -> q <= R -> R + 24 < 2^62 -> (R + 24 <= O \/ O + 264 <= R) ->
  0 <= L <= 22 -> 0 < D -> D + Z.of_nat dlen < 2^62 -> L <= Z.of_nat dlen -> (D + Z.of_nat dlen <= R \/ R + 24 <= D) -> (D + Z.of_nat dlen <= lo \/ q <= D) ->
  rw_cells usegs m (O + 48) [C8 (Z_to_bv 64 D); C8 (Z_to_bv 64 (D + L))] -> rw_cells usegs m (O + 96) [C8 (Z_to_bv 64 (D + L))] ->
  rw_cells usegs m D [CB dlen dbs] -> rw_cells usegs m R [CB 24 junk] ->
  rw_cells usegs m (q + -64) [CB 8 j8; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
  munch [(q - 64, q); (R, R + 24); (O + 96, O + 104)]%Z m0 m -> wmono usegs m0 m -> mem_inv usegs m ->
  evt usegs (str_short_post ra q gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo O R L m0)
      (MS (mkR ra (Z_to_bv 64 (q + -64)) gp (Z_to_bv 64 RATP) xt0 xt1 xt2 xs0 xs1 (Z_to_bv 64 R) (Z_to_bv 64 (O + 8)) (Z_to_bv 64 (D + L)) xa3 xa4 xa5 xa6 xa7
               xs2 xs3 (Z_to_bv 64 (D + L)) xs5 s6 s7 s8 s9 s10 s11 xt3 xt4 xt5 xt6)
          F (Z_to_bv 64 0x85ff8) fc None m (seg_rom usegs)).
Proof.
  intros until junk. intros ST GLO LO Q0 QO OHI QR RHI RSEP LR D0 DHI LD SEPRD DLO PB HMC DBUF RC FR MU WM MI.
  unfold GLOBALS_TOP in *.
  assert (LDB : length dbs = dlen) by (destruct DBUF as [[[HLx _] _] _]; exact HLx).

  lstep. lstep. replace (D + L + - D) with L by lia.
  lstep. lstep. if_cases K; zify_cond K; [exfalso; rewrite ?unsigned_lit in K by lia; lia| try clear K].
  lstep. lstep. if_cases K; zify_cond K; [exfalso; rewrite ?unsigned_lit in K by lia; lia| try clear K].

  apply (rw_cells_split_CB usegs _ _ [] 24 junk [] [1; 23]%nat) in RC; [|reflexivity]. cbn [mk_CB_cells app] in RC. forget_junk RC.
  lstep. zstep. rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 1) with 2. rewrite le1_smallZ by lia. mem_after_store.
  replace (L * 2) with (2 * L) in RC by lia.
  lstep. lstep.
  destruct (Z.eq_dec L 0) as [L0|L1].
  -
    subst L. if_cases K; zify_cond K; [exfalso; rewrite ?unsigned_lit in K by lia; lia| try clear K].
    lstep.

    lstep. lstep. do 7 lstep. lstep. release_frame FR ST q. lstep.
    lazymatch goal with H : rw_cells usegs _ R _ |- _ => rename H into RC9 end.
    merge_at RC9 1%nat 2%nat.
    apply evt_done. unfold str_short_post. sys_finish. all: try exact RC9. all: eexists; exact HMC.
  -
    if_cases K; zify_cond K; [try clear K| exfalso; rewrite ?unsigned_lit in K by lia; lia].
    lstep. lstep. lstep. lstep.
    destruct (rw_cells_CB_at _ _ _ _ L DBUF ltac:(lia)) as [SRCL _].
    pose proof SRCL as SRCb. apply rw_cells_bytes_at in SRCb. cbn [cells_bytes cbytes] in SRCb. rewrite app_nil_r in SRCb.
    assert (LSRC : length (firstn (Z.to_nat L) dbs) = Z.to_nat L) by (rewrite firstn_length_le; [reflexivity| lia]).
    takeZ RC 1%nat (R + 1) RB0.
    destruct (rw_cells_CB_at _ _ _ _ L RC ltac:(lia)) as [DSTL DREST]. clear RC.
    hide DREST. hide DBUF. hide SRCL.
    eapply evt_cut.
    { eapply memmove_far_callZ with (Dst := R + 1) (Src := D) (N := L);
        [exact SRCb| exact LSRC| exact DSTL| lia| lia| lia| lia| lia| lia| assumption]. }
    intros ms' PO. unfold memcpy_postZ in PO.
    destruct PO as (u5 & u6 & u7 & u11 & u12 & u13 & u14 & u15 & u16 & u17 & u28 & u29 & u30 & u31 & m4 & -> & MU4 & WM4 & MI4 & DST4 & SRC4).
    replace (ret_pc (Z_to_bv 64 0x8608c)) with (Z_to_bv 64 0x8608c) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    pose proof (agree_on_of_munch _ _ _ MU4 WM4) as AG4.
    apply (rw_cells_agree _ _ _ _ _ AG4) in FR; [| intros a Ha; cbn in Ha; cbn [outside]; split; [lia| exact I]].
    apply (rw_cells_agree _ _ _ _ _ AG4) in RB0; [| intros a Ha; cbn in Ha; cbn [outside]; split; [lia| exact I]].
    apply (rw_cells_agree _ _ _ _ _ AG4) in PB; [| intros a Ha; cbn in Ha; cbn [outside]; split; [lia| exact I]].
    apply (rw_cells_agree _ _ _ _ _ AG4) in HMC; [| intros a Ha; cbn in Ha; cbn [outside]; split; [lia| exact I]].
    unhide DREST. apply (rw_cells_agree _ _ _ _ _ AG4) in DREST; [| intros a Ha; cbn [cells_size csize Nat.add] in Ha; cbn [outside]; split; [lia| exact I]].
    assert (ST4 : stk usegs m4 lo (q + -64)) by (eapply stk_transport_disjoint; [exact ST| exact MU4| exact WM4| cbn [disjoint_from]; lia]).
    assert (MU5 : munch [(q - 64, q); (R, R + 24); (O + 96, O + 104)]%Z m0 m4).
    { eapply munch_trans; [exact MU|]. eapply munch_weaken; [| exact MU4]. unfold sub_fp. cbn [outside]. intros; lia. }
    assert (WM5 : wmono usegs m0 m4) by (eapply wmono_trans; [exact WM| exact WM4]).
    clear MU WM AG4 MU4 WM4 ST MI DSTL SRCb SRC4.

    lstep.
    assert (LDR : length (skipn (Z.to_nat L) jk0) = (23 - Z.to_nat L)%nat) by (destruct DREST as [[[HLx _] _] _]; exact HLx).
    apply u8arr_of_rw_cells in DREST.
    pose proof (u8arr_store_ok usegs _ _ _ 0 (Z_to_bv 64 (R + 1 + L)) DREST ltac:(rewrite LDR; lia) ltac:(unfold wa; f_equal; lia)) as SOK.
    zstep. first [change (le1 (Z_to_bv 64 0)) with [Z_to_bv 8 0] | change (Z_to_le_bytes 1 0) with [Z_to_bv 8 0] | idtac].
    replace (Z_to_bv 64 (R + 1 + L)) with (wa (R + 1 + L + 0)) by (unfold wa; f_equal; lia).
    pose proof (u8arr_write usegs _ _ _ 0 (Z_to_bv 8 0) DREST ltac:(rewrite LDR; lia)) as DREST'. clear DREST. store_done.
    apply rw_cells_of_u8arr in DREST'. rewrite upd_length, LDR in DREST'.
    pose proof (rw_cells_CB_join2 _ _ _ _ _ _ _ DST4 DREST' ltac:(lia)) as RC23. clear DST4 DREST'.
    replace (Z.to_nat L + (23 - Z.to_nat L))%nat with 23%nat in RC23 by lia.
    pose proof (rw_cells_join _ _ _ _ _ RB0 RC23 ltac:(cbn [app cells_size csize Nat.add]; lia)) as RC9. cbn [app] in RC9. clear RB0 RC23.

    do 7 lstep. lstep. release_frame FR ST4 q. lstep.
    apply evt_done. unfold str_short_post. sys_finish. all: try exact RC9. all: try (eexists; exact HMC).
Qed.

Theorem str_short_proof : str_short_stmt.
Proof.
  unfold str_short_stmt, OSS_STR. intros until junk. intros ST CEIL GLO LO Q0 QO OHI QR RHI RSEP RC INV WMAX MI.
  unfold GLOBALS_TOP in *.
  pose proof CEIL as CEIL'. unfold OSSVerify.Proofs.simdjson.fuzz_implementations.lib.Spec.Malloc.MCEIL in CEIL; try (pose proof alloc_ceiling_range as CEIL_RANGE__).
  destruct st as [D cap blk fuel w]. cbn [os_data os_cap os_blk os_fuel os_w] in *.
  destruct INV as [[PUTC [[hm [HMC HMR]] [j108 MODE]]] [REP NUM]]. unfold sb_cellsI, os_lim, OSS_SB_VPTR, OSS_CLASSIC in PUTC.
  cbn [os_data os_cap os_blk os_fuel os_w] in PUTC, HMR.
  pose proof NUM as (WB & FU & CB16 & HB). unfold os_lim, os_k in WB, FU, CB16, HB. cbn [os_data os_cap os_blk os_fuel os_w] in WB, FU, CB16, HB.

  assert (DBUF : exists dlen dbs, rw_cells usegs m D [CB dlen dbs] /\ w <= Z.of_nat dlen /\ 0 < D /\ D + Z.of_nat dlen < 2^62
                 /\ (D + Z.of_nat dlen <= R \/ R + 24 <= D) /\ (D + Z.of_nat dlen <= lo \/ (D = O + 73 /\ Z.of_nat dlen = 23))).
  { unfold STRREP in REP. cbn [os_blk os_data os_cap] in REP. destruct blk.
    - destruct REP as (_ & (dbs & BLK) & (A0 & A16 & _ & AC & AS)). unfold OSSVerify.Proofs.simdjson.fuzz_implementations.lib.Spec.Malloc.MCEIL in AC.
      exists (Z.to_nat cap), dbs. split; [exact BLK|]. repeat split; lia.
    - destruct REP as (_ & (dbs & R23) & ED). destruct HB as [EC _]. unfold IMP_SCAP0 in EC. subst D.
      exists 23%nat, dbs. split; [exact R23|]. repeat split; lia. }
  clear REP. destruct DBUF as (dlen & dbs & DBUF & LD & D0 & DHI & SEPRD & DLO).
  pose proof (munch_refl [(q - 64, q); (R, R + 24); (O + 96, O + 104)]%Z m) as MU. pose proof (wmono_refl usegs m) as WM.
  carve_frame 64%nat ST.
  apply (rw_cells_split_CB usegs _ _ [] 64 junk0 [] [8;8;8;8;8;8;8;8]%nat) in FR; [|reflexivity]. cbn [mk_CB_cells app] in FR.

  do 8 lstep. lstep. lstep. lstep. if_true.
  takeZ PUTC 5%nat (O + 48) PA. takeZ PUTC 2%nat (O + 64) PB.

  lstep. lstep.
  destruct (Z.eq_dec hm (D + w)) as [->|NE].
  - lstep. if_cases K; zify_cond K; [try clear K| exfalso; rewrite ?unsigned_lit in K by lia; lia].
    eapply str_short_tail with (m0 := m) (lo := lo) (dlen := dlen); try eassumption; try lia.
  - lstep. if_cases K; zify_cond K; [exfalso; rewrite ?unsigned_lit in K by lia; lia| try clear K].

    lstep. lstep.
    eapply str_short_tail with (m0 := m) (lo := lo) (dlen := dlen); try eassumption; try lia.
Qed.

Section Proofs.
  Hypothesis HM : rmalloc_stmt.

  Lemma str_long_tail : forall (A : Type) (K : bptr -> M PState A) (Q : A -> PState -> machine_state -> Prop)
      (ra gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
      (xt0 xt1 xt2 xa3 xa4 xa5 xa6 xa7 xs0 xs1 xs2 xs3 xs5 xt3 xt4 xt5 xt6 : word) (j8 : list byte)
      (F : bvmap 5 word) (fc : bv 32) (m0 m : mem) (s : PState) (LB : list block) (q lo B O R D L : Z) (errv : word) (dlen : nat) (dbs junk : list byte),
    RHEAP s LB m -> rauxv_ok m B -> q <= B -> B < 2^63 ->
    stk usegs m lo (q + -64) -> alloc_ceiling <= lo -> GLOBALS_TOP <= lo -> lo <= q - OSS_STR_STACK ->
    rw_cells usegs m LX_ERRNO [C4 errv] -> mem_inv usegs m ->
    q <= O -> O + 264 <= B -> q <= R -> R + 24 <= B -> (R + 24 <= O \/ O + 264 <= R) ->
    23 <= L -> L <= 67108864 -> 0 < D -> D + Z.of_nat dlen < 2^62 -> L <= Z.of_nat dlen ->
    ((exists bk, In bk LB /\ blk_addr bk <= D /\ D + Z.of_nat dlen <= blk_addr bk + blk_size bk) \/ (D = O + 73 /\ Z.of_nat dlen = 23)) ->
    rw_cells usegs m (O + 48) [C8 (Z_to_bv 64 D); C8 (Z_to_bv 64 (D + L))] -> rw_cells usegs m (O + 96) [C8 (Z_to_bv 64 (D + L))] ->
    rw_cells usegs m D [CB dlen dbs] -> rw_cells usegs m R [CB 24 junk] ->
    rw_cells usegs m (q + -64) [CB 8 j8; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
    lx_pres LB q [(R, R + 24); (O + 96, O + 104)] m0 m ->
    (forall b s' ms', str_long_post ra q gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LB lo B O R L m0 b s' ms' -> implM usegs (K b) s' Q ms') ->
    implM usegs (mbind (newnt lops (imp_S L)) K) s Q
      (MS (mkR ra (Z_to_bv 64 (q + -64)) gp (Z_to_bv 64 RATP) xt0 xt1 xt2 xs0 xs1 (Z_to_bv 64 R) (Z_to_bv 64 (O + 8)) (Z_to_bv 64 (D + L)) xa3 xa4 xa5 xa6 xa7
               xs2 xs3 (Z_to_bv 64 (D + L)) xs5 s6 s7 s8 s9 s10 s11 xt3 xt4 xt5 xt6)
          F (Z_to_bv 64 0x85ff8) fc None m (seg_rom usegs)).
  Proof.
    intros until junk. intros HEAP AUX QB B63 ST CEIL GLO LO ERR MI QO OB QR RB RSEP L23 LMAX D0 DHI LD DSRC PB HMC DBUF RC FR PRES KPOST.
    unfold OSS_STR_STACK, RMALLOC_STACK, GLOBALS_TOP in *.
    assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    pose proof CEIL as CEIL'. unfold OSSVerify.Proofs.simdjson.fuzz_implementations.lib.Spec.Malloc.MCEIL in CEIL; try (pose proof alloc_ceiling_range as CEIL_RANGE__).
    assert (ELX : LX_ERRNO = 1004708) by reflexivity. rewrite ELX in ERR.
    assert (LDB : length dbs = dlen) by (destruct DBUF as [[[HLx _] _] _]; exact HLx).
    assert (BLB : forall a, in_block LB a -> a < alloc_ceiling).
    { intros a (b & Hb & Hr). pose proof (LH_block_range _ _ _ _ HEAP Hb) as (_ & _ & _ & BC & _). unfold OSSVerify.Proofs.simdjson.fuzz_implementations.lib.Spec.Malloc.MCEIL in BC. lia. }
    assert (DLO : D + Z.of_nat dlen <= lo \/ (D = O + 73 /\ Z.of_nat dlen = 23)).
    { destruct DSRC as [(bk & Hbk & H1 & H2)|H]; [left| right; exact H].
      pose proof (LH_block_range _ _ _ _ HEAP Hbk) as (_ & _ & _ & BC & _). unfold OSSVerify.Proofs.simdjson.fuzz_implementations.lib.Spec.Malloc.MCEIL in BC. lia. }
    pose proof (imp_S_range L L23) as (SR1 & SR2 & SR3).
    unfold implM. iprefix.

    lstep. lstep. replace (D + L + - D) with L by lia.
    lstep. lstep. if_cases Kc; zify_cond Kc; [exfalso; rewrite ?unsigned_lit in Kc by lia; lia| try clear Kc].
    lstep. lstep. if_cases Kc; zify_cond Kc; [try clear Kc| exfalso; rewrite ?unsigned_lit in Kc by lia; lia].

    lstep. lstep. lstep.
    lazymatch goal with |- evt ?sg ?QQ (MS ?R ?FF _ ?fcc ?rv ?mm ?ro) =>
      lazymatch R with context C [Z_to_bv 64 (Z.lor L 7)] =>
        let R' := context C [Z_to_bv 64 (imp_S L)] in
        assert (JOIN : evt sg QQ (MS R' FF (Z_to_bv 64 0x8605c) fcc rv mm ro))
      end end.
    {
      lstep. lstep.
      ihere. to_implM. eapply implM_bind.
      { eapply (opnew_body HM) with (B := B) (lo := lo);
          [exact HEAP| exact AUX| lia| exact ST| exact CEIL'| unfold RMALLOC_STACK; lia| rewrite ELX; exact ERR| assumption| lia| lia]. }
      cbv beta. intros pn s2' ms2 PO. unfold opnew_postZ in PO.
      destruct PO as (r5 & r6 & r7 & r11 & r12 & r13 & r14 & r15 & r16 & r17 & r28 & r29 & r30 & r31 & m2 & errv2 & NEW & jnew
                      & -> & MI2 & ST2 & ERR2 & AUX2 & HP & FA2 & SO2 & BRN & HEAP2 & BLKN).
      replace (ret_pc (Z_to_bv 64 0x86064)) with (Z_to_bv 64 0x86064) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
      rewrite ELX in ERR2.
      pose proof BRN as (N0 & N16 & _ & NC & NS). unfold OSSVerify.Proofs.simdjson.fuzz_implementations.lib.Spec.Malloc.MCEIL in NC.
      pose proof (agree_of_heap_pres _ _ _ _ HP) as AG.
      apply (rw_cells_agree _ _ _ _ _ AG) in FR; [| intros a Ha; left; cbn in Ha; lia].
      apply (rw_cells_agree _ _ _ _ _ AG) in RC; [| intros a Ha; left; cbn in Ha; lia].
      apply (rw_cells_agree _ _ _ _ _ AG) in PB; [| intros a Ha; left; cbn in Ha; lia].
      apply (rw_cells_agree _ _ _ _ _ AG) in HMC; [| intros a Ha; left; cbn in Ha; lia].
      apply (rw_cells_agree _ _ _ _ _ AG) in DBUF.
      2:{ intros a Ha. cbn [cells_size csize Nat.add] in Ha. destruct DSRC as [(bk & Hbk & H1 & H2)|[ED EL]]; [| left; lia].
          right; right. exists bk. split; [exact Hbk| lia]. }
      assert (PRES2 : lx_pres LB q [(R, R + 24); (O + 96, O + 104)] m0 m2).
      { eapply lx_pres_trans; [exact PRES|]. apply lx_pres_of_heap_pres. eapply rheap_pres_weaken; [exact HP| lia| intros b Hb; exact Hb]. }

      assert (SEPN : D + Z.of_nat dlen <= NEW \/ NEW + imp_S L <= D).
      { destruct DSRC as [(bk & Hbk & H1 & H2)|[ED EL]].
        - destruct bk as [[pk Ak] nk]. cbn [blk_addr blk_size fst snd] in H1, H2.
          pose proof (LH_head_sep _ _ _ _ _ _ pk Ak nk HEAP2 Hbk). lia.
        - right. lia. }
      clear AG HP.
      pose proof (munch_refl [(q - 64, q); (R, R + 24); (NEW, NEW + imp_S L)]%Z m2) as MU. pose proof (wmono_refl usegs m2) as WM.
      unfold implM. iprefix.

      apply (rw_cells_split_CB usegs _ _ [] 24 junk [] [8; 8; 8]%nat) in RC; [|reflexivity]. cbn [mk_CB_cells app] in RC. forget_junk RC.
      lstep. lstep. lstep. lstep. lstep.
      lstep. if_cases Kc; zify_cond Kc; [exfalso; rewrite ?unsigned_lit in Kc by lia; lia| try clear Kc].

      lstep. lstep. lstep. lstep.

      destruct (rw_cells_CB_at _ _ _ _ L DBUF ltac:(lia)) as [SRCL _].
      pose proof SRCL as SRCb. apply rw_cells_bytes_at in SRCb. cbn [cells_bytes cbytes] in SRCb. rewrite app_nil_r in SRCb.
      assert (LSRC : length (firstn (Z.to_nat L) dbs) = Z.to_nat L) by (rewrite firstn_length_le; [reflexivity| lia]).
      destruct (rw_cells_CB_at _ _ _ _ L BLKN ltac:(lia)) as [DSTL DREST].
      hide DREST. hide DBUF. hide SRCL.
      eapply evt_cut.
      { eapply memmove_far_callZ with (Dst := NEW) (Src := D) (N := L);
          [exact SRCb| exact LSRC| exact DSTL| lia| lia| lia| lia| lia| lia| assumption]. }
      intros ms' PO. unfold memcpy_postZ in PO.
      destruct PO as (u5 & u6 & u7 & u11 & u12 & u13 & u14 & u15 & u16 & u17 & u28 & u29 & u30 & u31 & m4 & -> & MU4 & WM4 & MI4 & DST4 & SRC4).
      replace (ret_pc (Z_to_bv 64 0x8608c)) with (Z_to_bv 64 0x8608c) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
      pose proof (agree_on_of_munch _ _ _ MU4 WM4) as AG4.
      apply (rw_cells_agree _ _ _ _ _ AG4) in FR; [| intros a Ha; cbn in Ha; cbn [outside]; split; [lia| exact I]].
      apply (rw_cells_agree _ _ _ _ _ AG4) in RC; [| intros a Ha; cbn in Ha; cbn [outside]; split; [lia| exact I]].
      apply (rw_cells_agree _ _ _ _ _ AG4) in HMC; [| intros a Ha; cbn in Ha; cbn [outside]; split; [lia| exact I]].
      apply (rw_cells_agree _ _ _ _ _ AG4) in ERR2; [| intros a Ha; cbn in Ha; cbn [outside]; split; [lia| exact I]].
      unhide DREST. apply (rw_cells_agree _ _ _ _ _ AG4) in DREST; [| intros a Ha; cbn [cells_size csize Nat.add] in Ha; cbn [outside]; split; [lia| exact I]].
      assert (ST4 : stk usegs m4 lo (q + -64)) by (eapply stk_transport_disjoint; [exact ST2| exact MU4| exact WM4| cbn [disjoint_from]; lia]).
      assert (MU5 : munch [(q - 64, q); (R, R + 24); (NEW, NEW + imp_S L)]%Z m2 m4).
      { eapply munch_trans; [exact MU|]. eapply munch_weaken; [| exact MU4]. unfold sub_fp. cbn [outside]. intros; lia. }
      assert (WM5 : wmono usegs m2 m4) by (eapply wmono_trans; [exact WM| exact WM4]).
      assert (HEAP4 : RHEAP s2' ((pn, NEW, imp_S L) :: LB) m4).
      { eapply LH_frame; [exact HEAP2| exact MU5| exact WM5|]. constructor; [apply W_ok_stack; cbn; lia|]. constructor; [apply W_ok_stack; cbn; lia|]. constructor; [| constructor].
        eapply (W_ok_block _ (pn, NEW, imp_S L)); [left; reflexivity| cbn; lia| cbn; lia]. }
      assert (AUX4 : rauxv_ok m4 B).
      { eapply rauxv_ok_frame; [exact AUX2| exact MU5| exact WM5|]. constructor; [cbn; unfold RAUXV_CELL; lia|]. constructor; [cbn; unfold RAUXV_CELL; lia|]. constructor; [cbn; unfold RAUXV_CELL; lia| constructor]. }
      clear AG4 MU WM MU4 WM4 DSTL SRCb SRC4 MI2 ST2.
      pose proof (munch_refl [(q - 64, q); (R, R + 24); (NEW, NEW + imp_S L)]%Z m4) as MU6. pose proof (wmono_refl usegs m4) as WM6.

      lstep.
      assert (LDR : length (skipn (Z.to_nat L) jnew) = (Z.to_nat (imp_S L) - Z.to_nat L)%nat) by (destruct DREST as [[[HLx _] _] _]; exact HLx).
      apply u8arr_of_rw_cells in DREST.
      pose proof (u8arr_store_ok usegs _ _ _ 0 (Z_to_bv 64 (NEW + L)) DREST ltac:(rewrite LDR; lia) ltac:(unfold wa; f_equal; lia)) as SOK.
      zstep. first [change (le1 (Z_to_bv 64 0)) with [Z_to_bv 8 0] | change (Z_to_le_bytes 1 0) with [Z_to_bv 8 0] | idtac].
      replace (Z_to_bv 64 (NEW + L)) with (wa (NEW + L + 0)) by (unfold wa; f_equal; lia).
      pose proof (u8arr_write usegs _ _ _ 0 (Z_to_bv 8 0) DREST ltac:(rewrite LDR; lia)) as DREST'. clear DREST. store_done.
      apply rw_cells_of_u8arr in DREST'. rewrite upd_length, LDR in DREST'.
      pose proof (rw_cells_CB_join2 _ _ _ _ _ _ _ DST4 DREST' ltac:(lia)) as NEWC. clear DST4 DREST'.
      replace (Z.to_nat L + (Z.to_nat (imp_S L) - Z.to_nat L))%nat with (Z.to_nat (imp_S L)) in NEWC by lia.

      do 7 lstep. lstep. release_frame FR ST4 q. lstep.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m9 end.
      ihere. to_implM. apply KPOST. unfold str_long_post.
      do 15 eexists. exists m9, errv2, NEW.
      split; [cbv delta [mkR]; reflexivity|].
      split; [assumption|]. split; [exact ST4|]. split; [rewrite ELX; exact ERR2|].
      split. { eapply rauxv_ok_frame; [exact AUX4| exact MU6| exact WM6|].
               constructor; [cbn; unfold RAUXV_CELL; lia|]. constructor; [cbn; unfold RAUXV_CELL; lia|]. constructor; [cbn; unfold RAUXV_CELL; lia| constructor]. }
      split; [exact FA2|]. split; [exact SO2|].
      split. { eapply LH_frame; [exact HEAP4| exact MU6| exact WM6|].
               constructor; [apply W_ok_stack; cbn; lia|]. constructor; [apply W_ok_stack; cbn; lia|]. constructor; [| constructor].
               eapply (W_ok_block _ (pn, NEW, imp_S L)); [left; reflexivity| cbn; lia| cbn; lia]. }
      split; [exact RC|]. split; [eexists; exact NEWC|]. split; [exact BRN|]. split; [eexists; exact HMC|].
      eapply lx_pres_trans; [exact PRES2|].
      eapply lx_pres_of_munch; [exact MU5| exact WM5|].
      pose proof (LH_head_disj _ _ _ _ _ _ HEAP2) as DJN.
      intros a Ha [HX HC]. cbn [rin_ivs fst snd] in HX. cbn [outside]. split; [| split; [clear - HX; lia|]].
      - destruct HC as [HC|[HC|HC]]; [lia| specialize (BLB a HC); lia| lia].
      - split; [| exact I]. destruct HC as [HC|[HC|HC]]; [lia| | lia]. intros Hs. apply (DJN a); [exact HC| lia]. }

    lstep. if_cases Kc; zify_cond Kc; rewrite ?unsigned_lit in Kc by lia.
    - lstep. replace (Z_to_bv 64 (Z.lor L 7 + 1)) with (Z_to_bv 64 (imp_S L)) by (f_equal; unfold imp_S; destruct (Z.eqb_spec (Z.lor L 7) 23); lia). exact JOIN.
    - lstep. lstep. replace (Z_to_bv 64 26) with (Z_to_bv 64 (imp_S L)) by (f_equal; unfold imp_S; destruct (Z.eqb_spec (Z.lor L 7) 23); lia). exact JOIN.
  Qed.

  Theorem str_long_proof : str_long_stmt.
  Proof.
    unfold str_long_stmt, OSS_STR. intros until junk. intros HEAP AUX QB B63 ST CEIL GLO LO ERR MI QO OB QR RB RSEP RC HL INV L23 LMAX KPOST.
    pose proof LO as LO'. unfold OSS_STR_STACK, RMALLOC_STACK, GLOBALS_TOP in LO, GLO.
    assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    pose proof CEIL as CEIL'. unfold OSSVerify.Proofs.simdjson.fuzz_implementations.lib.Spec.Malloc.MCEIL in CEIL; try (pose proof alloc_ceiling_range as CEIL_RANGE__).
    assert (ELX : LX_ERRNO = 1004708) by reflexivity. rewrite ELX in ERR.
    assert (BLB : forall a, in_block (osblocks st ++ LB) a -> a < alloc_ceiling).
    { intros a (b & Hb & Hr). pose proof (LH_block_range _ _ _ _ HEAP Hb) as (_ & _ & _ & BC & _).
      unfold OSSVerify.Proofs.simdjson.fuzz_implementations.lib.Spec.Malloc.MCEIL in BC. lia. }
    pose proof (PJ_CAPMAX_bound len HL) as CMB. assert (LB26 : os_w st <= 67108864) by (unfold PJ_OUTMAX, SJ_PADMAX in *; lia).
    destruct st as [D cap blk fuel w]. cbn [os_data os_cap os_blk os_fuel os_w] in *.
    destruct INV as [[PUTC [[hm [HMC HMR]] [j108 MODE]]] [REP NUM]]. unfold sb_cellsI, os_lim, OSS_SB_VPTR, OSS_CLASSIC in PUTC.
    cbn [os_data os_cap os_blk os_fuel os_w] in PUTC, HMR.
    pose proof NUM as (WB & FU & CB16 & HB). unfold os_lim, os_k in WB, FU, CB16, HB. cbn [os_data os_cap os_blk os_fuel os_w] in WB, FU, CB16, HB.
    assert (DBUF : exists dlen dbs, rw_cells usegs m D [CB dlen dbs] /\ w <= Z.of_nat dlen /\ 0 < D /\ D + Z.of_nat dlen < 2^62
                   /\ ((exists bk, In bk (osblocks (mkOss D cap blk fuel w) ++ LB) /\ blk_addr bk <= D /\ D + Z.of_nat dlen <= blk_addr bk + blk_size bk) \/ (D = O + 73 /\ Z.of_nat dlen = 23))).
    { unfold STRREP in REP. cbn [os_blk os_data os_cap] in REP. destruct blk as [b|].
      - destruct REP as (_ & (dbs & BLK) & (A0 & A16 & _ & AC & AS)). unfold OSSVerify.Proofs.simdjson.fuzz_implementations.lib.Spec.Malloc.MCEIL in AC.
        exists (Z.to_nat cap), dbs. split; [exact BLK|]. split; [lia|]. split; [lia|]. split; [lia|].
        left. exists (b, D, cap). cbn [osblocks os_blk os_data os_cap app blk_addr blk_size fst snd]. split; [left; reflexivity| lia].
      - destruct REP as (_ & (dbs & R23) & ED). destruct HB as [EC _]. unfold IMP_SCAP0 in EC. subst D.
        exists 23%nat, dbs. split; [exact R23|]. repeat split; try lia. all: right; split; [reflexivity| reflexivity]. }
    clear REP. destruct DBUF as (dlen & dbs & DBUF & LD & D0 & DHI & DSRC).
    assert (DLO : D + Z.of_nat dlen <= lo \/ (D = O + 73 /\ Z.of_nat dlen = 23)).
    { destruct DSRC as [(bk & Hbk & H1 & H2)|H]; [left| right; exact H].
      pose proof (LH_block_range _ _ _ _ HEAP Hbk) as (_ & _ & _ & BC & _). unfold OSSVerify.Proofs.simdjson.fuzz_implementations.lib.Spec.Malloc.MCEIL in BC. lia. }
    pose proof (munch_refl [(q - 64, q); (O + 96, O + 104)]%Z m) as MU. pose proof (wmono_refl usegs m) as WM.
    unfold implM. iprefix.
    lstep. carve_frame 64%nat ST.
    apply (rw_cells_split_CB usegs _ _ [] 64 junk0 [] [8;8;8;8;8;8;8;8]%nat) in FR; [|reflexivity]. cbn [mk_CB_cells app] in FR.

    do 7 lstep. lstep. lstep. lstep. if_true.
    takeZ PUTC 5%nat (O + 48) PA. takeZ PUTC 2%nat (O + 64) PB.

    lstep. lstep.
    assert (TAIL : forall m1 j8, rw_cells usegs m1 (O + 96) [C8 (Z_to_bv 64 (D + w))] -> rw_cells usegs m1 D [CB dlen dbs] -> rw_cells usegs m1 R [CB 24 junk] ->
      rw_cells usegs m1 (O + 48) [C8 (Z_to_bv 64 D); C8 (Z_to_bv 64 (D + w))] ->
      rw_cells usegs m1 (q + -64) [CB 8 j8; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
      rw_cells usegs m1 1004708 [C4 errv] -> stk usegs m1 lo (q + -64) -> mem_inv usegs m1 ->
      munch [(q - 64, q); (O + 96, O + 104)] m m1 -> wmono usegs m m1 ->
      forall (xa3 : word),
      evt usegs (fun ms' => impl usegs (at_node usegs) ((x <- newnt lops (imp_S w);; K x) s) (epost (fun p => Q p.1 p.2)) ms')
        (MS (mkR ra (Z_to_bv 64 (q + -64)) gp (Z_to_bv 64 RATP) t0 t1 t2 s0 s1 (Z_to_bv 64 R) (Z_to_bv 64 (O + 8)) (Z_to_bv 64 (D + w)) xa3 a4 a5 a6 a7
                 s2 s3 (Z_to_bv 64 (D + w)) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 0x85ff8) fc None m1 (seg_rom usegs))).
    { intros m1 j8 HMC1 DBUF1 RC1 PB1 FR1 ERR1 ST1 MI1 MU1 WM1 xa3.
      ihere. to_implM.
      eapply str_long_tail with (m0 := m) (lo := lo) (B := B) (dlen := dlen) (errv := errv);
        [ eapply LH_frame; [exact HEAP| exact MU1| exact WM1|]; constructor; [apply W_ok_stack; cbn; lia|]; constructor; [apply W_ok_stack; cbn; lia| constructor]
        | eapply rauxv_ok_frame; [exact AUX| exact MU1| exact WM1|]; constructor; [cbn; unfold RAUXV_CELL; lia|]; constructor; [cbn; unfold RAUXV_CELL; lia| constructor]
        | lia| lia| exact ST1| exact CEIL'| unfold GLOBALS_TOP; lia| exact LO'| exact ERR1| exact MI1| lia| lia| lia| lia| exact RSEP| lia| lia| lia| lia| lia| exact DSRC
        | exact PB1| exact HMC1| exact DBUF1| exact RC1| exact FR1| | exact KPOST].
      eapply lx_pres_of_munch; [exact MU1| exact WM1|].
      intros a Ha [HX HC]. cbn [rin_ivs fst snd] in HX. cbn [outside].
      split; [destruct HC as [HC|[HC|HC]]; [lia| specialize (BLB a HC); lia| lia]|]. split; [lia| exact I]. }
    destruct (Z.eq_dec hm (D + w)) as [->|NE].
    - lstep. if_cases Kc; zify_cond Kc; [try clear Kc| exfalso; rewrite ?unsigned_lit in Kc by lia; lia].
      eapply TAIL; try eassumption.
    - lstep. if_cases Kc; zify_cond Kc; [exfalso; rewrite ?unsigned_lit in Kc by lia; lia| try clear Kc].
      lstep. lstep.
      eapply TAIL; try eassumption.
  Qed.
End Proofs.

End WithCeiling0.
