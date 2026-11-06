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
From OSSVerify.Proofs.simdjson.fuzz_implementations.lib.Spec Require Import Prelim STree Malloc Monad Stdio SjModel PjModel ImpModel Target Prog ImpImpl.
From OSSVerify.Proofs.simdjson.fuzz_implementations.lib.P Require Import Sj_h_arith Sj_stage1_kit.
From OSSVerify.Proofs.simdjson.fuzz_implementations.lib.U Require Import Layout Exit Printf_wfile Pj_loc_defs Sj_iface Sj_kit Sj_new Sj_new_t2 Sj_h_kit Sj_h_create Sj_h_active Sj_h_pid_front Sj_h_pdtor.
From OSSVerify.Proofs.simdjson.fuzz_implementations.lib.Sj Require SjAlloc.
From OSSVerify.Proofs.simdjson.fuzz_implementations.lib.U Require Import Sj_stage2_iface Sj_h_parse Printf_mlib Pj_pid Imp_defs Imp_kit Imp_iface Imp_lftoi2.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
From OSSVerify.Proofs.simdjson.fuzz_implementations.lib.Lib Require Import Ceiling.
From OSSVerify.Proofs.simdjson.fuzz_implementations.lib.P Require Import Rnd.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac std_lia__ := lia.
Local Ltac lia := first [std_lia__ | try (pose proof alloc_ceiling_range as CEIL_RANGE__); std_lia__].

Ltac GBNE := step; first [if_false | if_true].

Ltac GBLTU r := let K := fresh "KB" in step; if_cases K; [exfalso; zify_cond K; rewrite ?unsigned_lit in K by lia; pose proof (zr_word r) as KR; unfold inr64 in KR; lia|]; clear K.

Ltac GBGEU rv := let K := fresh "KU" in step; if_cases K;
  [exfalso; try (change (Z_to_bv 64 rv) with (MallocRep.wz rv) in K; rewrite MallocRep.sx32_wz in K by lia; unfold MallocRep.wz in K);
   zify_cond K; rewrite ?unsigned_lit in K by lia; lia|]; clear K.

Lemma mod16_off8 : forall q k, q mod 16 = 0 -> (q + 8 * k) mod 8 = 0.
Proof.
  intros q k H. apply Z.mod_divide; [lia|]. apply Z.mod_divide in H; [|lia]. destruct H as [c Hc]. exists (2 * c + k). lia.
Qed.

Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.

Definition sj_staticsB (mid : bool) (m : mem) : Prop := if mid then sj_statics_mid m else sj_statics m true.

Lemma getact_any_spec : forall (mid : bool) (ra gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem) (q lo : Z),
  stk usegs m lo q -> GLOBALS_TOP <= lo -> lo <= q - 64 -> 0 <= q < 2^64 -> mem_inv usegs m -> sj_staticsB mid m ->
  evt usegs (getact_post ra q gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m)
    (MS (mkR ra (Z_to_bv 64 q) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 SJ_GET_ACTIVE) fc None m (seg_rom usegs)).
Proof. intros [|]; [exact getact_mid_spec| exact getact_init_spec]. Qed.

Lemma sj_staticsB_agree : forall mid P m m', agree_on P m m' -> (forall a, sjs_addr a -> P a) -> sj_staticsB mid m -> sj_staticsB mid m'.
Proof. intros [|]; [exact sj_statics_mid_agree| exact (fun P m m' => sj_statics_agree P m m' true)]. Qed.

Lemma payload_ok_app : forall m OW LB D d, payload_ok m LB D d -> payload_ok m (OW ++ LB) D d.
Proof.
  intros m OW LB D d (P1 & P2 & P3 & P4 & P5 & P6). repeat (split; [assumption|]).
  destruct P6 as [E|(b & Hb & R)]; [left; exact E| right; exists b; split; [apply in_or_app; right; exact Hb| exact R]].
Qed.

Definition body_prog (rc : option Z) (len : Z) (p : bptr) : M PState (Z * option bptr) :=
  mbind (newnt lops (SJ_SBUF len)) (fun sb => mbind (newnt lops (SJ_TAPE len)) (fun tp => mbind (newnt lops SJ_IMPL) (fun im => mbind (newnt lops (SJ_IDX len)) (fun ix => mbind (newnt lops SJ_OC) (fun oc => mbind (newnt lops SJ_IA) (fun ia => mbind (imp_copy_phase lops len rc) (fun _ => mbind (del lops sb) (fun _ => mbind (del lops tp) (fun _ => mbind (del lops ia) (fun _ => mbind (del lops oc) (fun _ => mbind (del lops ix) (fun _ => mbind (del lops im) (fun _ => mret (0, Some p)))))))))))))).

Lemma out0_short : forall m q, rw_cells usegs m (q + 432) [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)] -> imp_out m q None.
Proof.
  intros m q H. exists (Z_to_bv 8 0), (MallocRep.zeros 23). split; [| reflexivity].
  eapply rw_cells_recast; [exact H| cbn; repeat split| vm_compute; reflexivity| reflexivity].
Qed.

Section Proofs.
  Hypothesis HM : rmalloc_stmt.
  Hypothesis HF : rfree_stmt.
  Hypothesis HS2 : stage2t_stmt.
  Hypothesis OKARM : imp_okarm_stmt.

  Lemma lftoi_body : forall (mid : bool) (x1 gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s7 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
      (m00 m : mem) (s00 s : PState) (LB OW' : list block) (D : Z) (d : list Z) (v : option bptr) (p : bptr)
      (q lo B : Z) (errv canary : word) (ra S0 S1 S2 S3 S4 S5 S6 S7 S8 S9 S10 S11 : word)
      (j16 jgap j1a j17a j57a j100a jsb : list byte),
    frm0 fc -> mem_inv usegs m -> stk usegs m lo q -> rw_cells usegs m LX_ERRNO [C4 errv] -> rauxv_ok m B ->
    ps_fa s = ps_fa s00 -> ps_so s = ps_so s00 ->
    alloc_ceiling <= lo -> GLOBALS_TOP <= lo -> lo <= q - 65536 -> 0 <= q -> q mod 16 = 0 -> q + IMP_FRAME <= B -> B < 2^62 ->
    RHEAP s00 LB m00 -> lx_statics m00 -> stderr_wfile m00 -> ssp_cells m00 canary -> payload_ok m00 LB D d ->
    RHEAP s (OW' ++ LB) m -> xnew v p OW' -> imp_vec m (OW' ++ LB) (Some p) -> sj_staticsB mid m -> aex_tbl m 3 -> lx_statics m ->
    lx_pres LB (q + IMP_FRAME) [LXW_IMP; LXW_SJ; LXW_AEX] m00 m ->
    rw_cells usegs m q [CB 8 j16] ->
    rw_cells usegs m (q + 8) [C8 (Z_to_bv 64 1); C8 (Z_to_bv 64 IMP_SBB_VPTR); C8 (Z_to_bv 64 IMP_SB_VPTR); C8 (Z_to_bv 64 IMP_IOS_VPTR); C8 (Z_to_bv 64 IMP_VTT); C8 (Z_to_bv 64 (zlength d))] ->
    rw_cells usegs m (q + 56) [CB 264 jgap] ->
    rw_cells usegs m (q + 320) (impl0_cells SJ_FALLBACK j1a j17a j57a j100a) ->
    impl0_tail_cells (q + 456) m -> impl0_tail_cells (q + 592) m -> impl0_tail_cells (q + 728) m ->
    rw_cells usegs m (q + 864) [CB 88 jsb] ->
    rw_cells usegs m (q + 952) (imp_saves ra S0 S1 S2 S3 S4 S5 S6 S7 S8 S9 S10 S11) ->
    implM usegs (body_prog (sj_root_copy d) (zlength d) p) s
      (rfuzz_one_post ra (Z_to_bv 64 (q + IMP_FRAME)) gp (Z_to_bv 64 RATP) S0 S1 S2 S3 S4 S5 S6 S7 S8 S9 S10 S11 s00 LB D d v lo B canary m00)
      (MS (mkR x1 (Z_to_bv 64 q) gp (Z_to_bv 64 RATP) t0 t1 t2 (Z_to_bv 64 0) (Z_to_bv 64 D) a0 a1 a2 a3 a4 a5 a6 a7
               (Z_to_bv 64 136) (Z_to_bv 64 1) (Z_to_bv 64 IMP_OS_VPTR) (Z_to_bv 64 12) (Z_to_bv 64 (zlength d)) s7
               (Z_to_bv 64 0) (Z_to_bv 64 1) (Z_to_bv 64 0) (Z_to_bv 64 64) t3 t4 t5 t6)
          F (Z_to_bv 64 IMP_LOOP) fc None m (seg_rom usegs)).
  Proof.
    intros mid. intros until jsb.
    intros FRM MI ST ERR AUX FA SO CEIL GLO LO Q0 AL16 QB B62 HEAP0 LXS0 SEW0 SSP0 PL0 HEAP XN VEC SJS AEXT LXS PRES F0 F16 F40 I0 T1 T2 T3 F848 F936.
    unfold IMP_LOOP, IMP_FRAME, IMP_IMPLS, GLOBALS_TOP in *.
    pose proof CEIL as CEIL'. unfold OSSVerify.Proofs.simdjson.fuzz_implementations.lib.Spec.Malloc.MCEIL in CEIL; try (pose proof alloc_ceiling_range as CEIL_RANGE__).
    assert (ELX : LX_ERRNO = 1004708) by reflexivity. rewrite ELX in ERR.
    set (len := zlength d) in *. assert (LEN0 : 0 <= len) by (subst len; unfold zlength; lia).
    pose proof PL0 as (_ & _ & D0 & DN & DLEN & _). change (2^26) with 67108864 in DLEN.
    assert (BLB : forall a, in_block LB a -> a < alloc_ceiling).
    { intros a (b & Hb & Hr). pose proof (LH_block_range _ _ _ _ HEAP0 Hb) as (_ & _ & _ & BC & _). unfold OSSVerify.Proofs.simdjson.fuzz_implementations.lib.Spec.Malloc.MCEIL in BC. lia. }
    assert (BLB2 : forall a, in_block (OW' ++ LB) a -> a < alloc_ceiling).
    { intros a (b & Hb & Hr). pose proof (LH_block_range _ _ _ _ HEAP Hb) as (_ & _ & _ & BC & _). unfold OSSVerify.Proofs.simdjson.fuzz_implementations.lib.Spec.Malloc.MCEIL in BC. lia. }

    pose proof VEC as VEC'. destruct VEC' as (A & INA & VC & AW).
    pose proof (LH_block_range _ _ _ _ HEAP INA) as (A0 & _ & _ & AC & AS). cbn [blk_addr blk_size fst snd] in A0, AC, AS. unfold OSSVerify.Proofs.simdjson.fuzz_implementations.lib.Spec.Malloc.MCEIL in AC.

    unfold impl0_cells in I0. cbv delta [MallocRep.wz] in I0.
    split_cells I0 1%nat IMPW I0r. split_cells I0r 2%nat P0 I0s. split_cells I0s 1%nat PIMPL I0t. split_cells I0t 3%nat P16 I0u.
    split_cells I0u 3%nat DOCC I0v. split_cells I0v 5%nat P48 I0w. split_cells I0w 4%nat ELC OUTC.
    pose proof (munch_refl [(q - 64, q); (SJ_STATICS_LO, SJ_STATICS_HI)]%Z m) as MU. pose proof (wmono_refl usegs m) as WM. unfold SJ_STATICS_LO, SJ_STATICS_HI in MU.
    unfold body_prog, implM. iprefix.
    destruct T1 as (j1b & j17b & j57b & j100b & T1). destruct T2 as (j1c & j17c & j57c & j100c & T2). destruct T3 as (j1d & j17d & j57d & j100d & T3).
    Ltac tr1 AG H tac := apply (rw_cells_agree _ _ _ _ _ AG) in H; [| intros a Ha; cbn in Ha; tac].

    zstep. zstep. zstep. GBNE. GBLTU s7.
    zstep. zstep. step. step. clear MU WM.
    eapply evt_cut. { eapply (getact_any_spec mid) with (lo := lo); [exact ST| unfold GLOBALS_TOP; lia| lia| lia| exact MI| exact SJS]. }
    intros ms' PO. unfold getact_post in PO.
    destruct PO as (v5 & v6 & v7 & v11 & v12 & v13 & v14 & v15 & v16 & v17 & v28 & v29 & v30 & v31 & m1 & -> & MU1 & WM1 & MI1 & ST1 & SJS1).
    unfold SJ_STATICS_LO, SJ_STATICS_HI in MU1.
    replace (ret_pc (Z_to_bv 64 0x3f01c)) with (Z_to_bv 64 0x3f01c) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    pose proof (agree_on_of_munch _ _ _ MU1 WM1) as AG1.
    Ltac o1 := cbn [outside]; lia.
    tr1 AG1 F0 o1. tr1 AG1 F16 o1. tr1 AG1 F40 o1. tr1 AG1 IMPW o1. tr1 AG1 P0 o1. tr1 AG1 PIMPL o1. tr1 AG1 P16 o1. tr1 AG1 DOCC o1. tr1 AG1 P48 o1. tr1 AG1 ELC o1. tr1 AG1 OUTC o1.
    unfold impl0_cells in T1, T2, T3. tr1 AG1 T1 o1. tr1 AG1 T2 o1. tr1 AG1 T3 o1. tr1 AG1 F848 o1. unfold imp_saves in F936. tr1 AG1 F936 o1.
    unfold imp_vec_cells, IMP_VEC_LO in VC. tr1 AG1 VC o1. tr1 AG1 AW o1. tr1 AG1 ERR o1.
    assert (HEAP1 : RHEAP s (OW' ++ LB) m1).
    { eapply LH_frame; [exact HEAP| exact MU1| exact WM1|]. constructor; [apply W_ok_stack; cbn; lia|]. constructor; [| constructor].
      right; left. cbn [fst snd]. unfold RMallocRep.RLIBC, RMallocRep.RCTX, RMallocRep.RSSP_GUARD, RMallocRep.RGOT_SSP. lia. }
    assert (AUX1 : rauxv_ok m1 B).
    { eapply rauxv_ok_frame; [exact AUX| exact MU1| exact WM1|]. constructor; [cbn; unfold RAUXV_CELL; lia|]. constructor; [cbn; unfold RAUXV_CELL; lia| constructor]. }
    assert (AEX1 : aex_tbl m1 3).
    { eapply aex_tbl_agree; [exact AG1| | exact AEXT]. intros a Ha. unfold aex_tbl_addr, AEX in Ha. o1. }
    assert (LXS1 : lx_statics m1).
    { eapply lx_statics_agree; [exact AG1| | exact LXS]. intros a Ha. pose proof (lxs_addr_lt a Ha) as [R1 R2]. unfold GLOBALS_TOP in R1.
      unfold lxs_addr, LX_GOT_STDERR, LX_STDERR_PTR, SJ_GOT_NOTHROW, SJ_IMPL_VT24, SJ_DPI_VPTR in Ha. cbn [outside]. clear - Ha R1 GLO LO. lia. }
    assert (CLI1 : forall a, 0 <= a < 2^64 -> lx_client LB (q + 1056) [LXW_IMP; LXW_SJ; LXW_AEX] a -> outside [(q - 64, q); (996096, 1002552)]%Z a).
    { intros a Ha [HX HC]. unfold LXW_IMP, LXW_SJ, LXW_AEX, IMP_VEC_LO, SJ_STATICS_LO, SJ_STATICS_HI in HX. cbn [rin_ivs fst snd] in HX. cbn [outside].
      refine (conj _ (conj _ I)); [destruct HC as [HC|[HC|HC]]; [lia| specialize (BLB a HC); lia| lia] | clear - HX Ha; lia]. }
    assert (PRES1 : lx_pres LB (q + 1056) [LXW_IMP; LXW_SJ; LXW_AEX] m00 m1).
    { eapply lx_pres_trans; [exact PRES|]. eapply lx_pres_of_munch; [exact MU1| exact WM1| exact CLI1]. }
    clear AG1 MU1 WM1 CLI1 HEAP AUX AEXT LXS SJS PRES MI ST VEC.

    destruct SJS1 as (SJC & LOCB1 & (E1 & uw & E2) & IOS1). unfold sj_cells, SJ_STATICS_LO in SJC. cbv delta [MallocRep.wz] in SJC.
    destruct LOCB1 as (k1 & k2 & k3 & k4 & k5 & k6 & k7 & k8 & k9 & k10 & k11 & k12 & k13 & k14 & k15 & LOCB1).
    pose proof (munch_refl [(q - 64, q); (996104, 996112)]%Z m1) as MU. pose proof (wmono_refl usegs m1) as WM.
    unfold SJ_ACTIVE_IMPL. step. hstep. step.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m2 end.
    assert (SJS2 : sj_statics m2 true).
    { split; [| split; [| split]].
      - unfold sj_cells, SJ_STATICS_LO. cbv delta [MallocRep.wz]. exact SJC.
      - do 15 eexists. exact LOCB1.
      - split; [exact E1| exists uw; exact E2].
      - eapply imp_ios_agree; [exact (agree_on_of_munch _ _ _ MU WM)| | exact IOS1]. intros a Ha. pose proof (imp_ios_addr_bounds a Ha) as HB. unfold IOS in HB. o1. }
    clear SJC LOCB1 E1 E2 IOS1.
    assert (PRES2 : lx_pres LB (q + 1056) [LXW_IMP; LXW_SJ; LXW_AEX] m00 m2).
    { eapply lx_pres_trans; [exact PRES1|]. eapply lx_pres_of_munch; [exact MU| exact WM|].
      intros a Ha [HX HC]. unfold LXW_IMP, LXW_SJ, LXW_AEX, IMP_VEC_LO, SJ_STATICS_LO, SJ_STATICS_HI in HX. cbn [rin_ivs fst snd] in HX. cbn [outside].
      refine (conj _ (conj _ I)); [destruct HC as [HC|[HC|HC]]; [lia| specialize (BLB a HC); lia| lia] | clear - HX Ha; lia]. }
    eapply LH_frame in HEAP1; [| exact MU| exact WM| constructor; [apply W_ok_stack; cbn; lia| constructor; [| constructor]]].
    2:{ right; left. cbn [fst snd]. unfold RMallocRep.RLIBC, RMallocRep.RCTX, RMallocRep.RSSP_GUARD, RMallocRep.RGOT_SSP. lia. }
    eapply rauxv_ok_frame in AUX1; [| exact MU| exact WM| constructor; [cbn; unfold RAUXV_CELL; lia| constructor; [cbn; unfold RAUXV_CELL; lia| constructor]]].
    assert (AEX2 : aex_tbl m2 3).
    { eapply aex_tbl_agree; [exact (agree_on_of_munch _ _ _ MU WM)| | exact AEX1]. intros a Ha. unfold aex_tbl_addr, AEX in Ha. o1. }
    assert (LXS2 : lx_statics m2).
    { eapply lx_statics_agree; [exact (agree_on_of_munch _ _ _ MU WM)| | exact LXS1]. intros a Ha. pose proof (lxs_addr_lt a Ha) as [R1 R2]. unfold GLOBALS_TOP in R1.
      unfold lxs_addr, LX_GOT_STDERR, LX_STDERR_PTR, SJ_GOT_NOTHROW, SJ_IMPL_VT24, SJ_DPI_VPTR in Ha. cbn [outside]. clear - Ha R1 GLO LO. lia. }
    rename HEAP1 into HEAP2. rename AUX1 into AUX2. clear AEX1 LXS1 PRES1.
    lazymatch goal with H : mem_inv _ m2 |- _ => rename H into MI2 end. lazymatch goal with H : stk _ m2 _ _ |- _ => rename H into ST2 end.
    assert (PL2 : payload_ok m2 (OW' ++ LB) D d).
    { apply payload_ok_app. eapply payload_ok_agree; [exact (agree_of_lx_pres _ _ _ _ _ PRES2)| exact PL0|]. intros b0 a Hb Ha. split; [| right; left; exists b0; split; assumption].
      pose proof (LH_block_range _ _ _ _ HEAP0 Hb) as (_ & _ & _ & _ & BS). unfold LXW_IMP, LXW_SJ, LXW_AEX, IMP_VEC_LO, SJ_STATICS_LO, SJ_STATICS_HI. cbn [rin_ivs fst snd].
      clear - Ha BS. lia. }

    apply (rw_cells_split_CB usegs _ _ [] 264 jgap [] [8;8;4;4;240]%nat) in F40; [|reflexivity]. cbn [mk_CB_cells app] in F40.
    split_cells F40 4%nat SRETC GAPC.
    lazymatch type of SRETC with rw_cells _ _ _ [_; _; _; CB 4 ?x] => set (jr20 := x) in * end.

    zstep. zstep. zstep. step. step. step. step.
    replace (Z_to_bv 64 (q + 352)) with (Z_to_bv 64 (q + 328 + 24)) by (f_equal; lia).
    replace (q + 336) with (q + 328 + 8) in PIMPL by lia. replace (q + 352) with (q + 328 + 24) in DOCC by lia. replace (q + 376) with (q + 328 + 48) in P48 by lia.
    clear MU WM.
    ihere. to_implM. unfold SJ_SBUF, SJ_TAPE, SJ_IMPL, SJ_IDX, SJ_OC, SJ_IA, sj_cap.
    pose proof LXS2 as (_ & _ & GOT & VT24 & VTD & _).
    eapply (pid_front_cps HM) with (B := B) (lo := lo) (SRET := q + 56) (PARSER := q + 328) (D := D) (len := len);
      [exact HEAP2| exact AUX2| lia| exact ST2| exact CEIL'| unfold GLOBALS_TOP; lia| unfold SJ_OPNEW_STACK, RMALLOC_STACK; lia
      | rewrite ELX; exact ERR| exact MI2| lia| lia| lia| lia
      | split; [exact GOT| split; [exact VT24| exact VTD]]
      | exact SJS2| exact PIMPL| exact DOCC| unfold p48_cells; exact P48|].
    intros psb ptp pim pix poc pia st3 ms3 MID.
    cbv beta. unfold imp_copy_phase. unfold SJ_PADMAX, SJ_COPY. fold (REST6 psb ptp pia poc pix pim p).
    set (cap := Z.max len 32) in *.

    assert (FIN : forall (ocp : option block) IMPL IDX OC IA TAPE SBUF lcapv s' ms',
      hpostF (Z_to_bv 64 0x3f044) q gp (Z_to_bv 64 0) (Z_to_bv 64 D) (Z_to_bv 64 136) (Z_to_bv 64 1) (Z_to_bv 64 IMP_OS_VPTR) (Z_to_bv 64 SJ_FALLBACK)
             (Z_to_bv 64 len) s7 (Z_to_bv 64 0) (Z_to_bv 64 (q + 320)) (Z_to_bv 64 0) (Z_to_bv 64 64) s lo B
        (pid_R (ocp_blocks ocp ++ (pia, IA, 1024) :: (poc, OC, 8192) :: (pix, IDX, 4 * (roundup64 cap + 9)) :: (pim, IMPL, 96) :: (ptp, TAPE, 8 * roundup64 (cap + 3))
                  :: (psb, SBUF, roundup64 (5 * (cap / 3) + 64)) :: OW' ++ LB)
               (OW' ++ LB) q (q + 56) (q + 328) m2 (Z_to_bv 8 0) j57a jr20 IMPL IDX OC IA TAPE SBUF cap (Z_to_bv 64 (match ocp with Some b => blk_addr b | None => 0 end)) lcapv) s' ms' ->
      (match ocp with Some _ => len <= 1048512 | None => True end) ->
      implM usegs (match ocp with Some b => mbind (imp_print lops len) (fun _ => mbind (del lops (blk_id b)) (fun _ => REST6 psb ptp pia poc pix pim p))
                               | None => REST6 psb ptp pia poc pix pim p end) s'
        (rfuzz_one_post ra (Z_to_bv 64 (q + 1056)) gp (Z_to_bv 64 RATP) S0 S1 S2 S3 S4 S5 S6 S7 S8 S9 S10 S11 s00 LB D d v lo B canary m00) ms').
    2:{ destruct (Z.leb_spec len 1048512) as [LE|GT].
        - apply implM_bind_assoc.
          eapply (implM_bind_ext usegs) with (f := fun cp => mbind (parse_model (SjAlloc.strip_bom d)) (fun _ =>
                     mbind (imp_print lops len) (fun _ => mbind (del lops cp) (fun _ => REST6 psb ptp pia poc pix pim p)))).
          { intros cp s' ms' H. apply implM_bind_assoc. eapply (implM_bind_ext usegs); [| exact H]. intros u s'' ms'' H2. apply implM_bind_assoc. exact H2. }
          eapply (pj_pid_copy_cps HM HS2) with (B := B) (lo := lo) (m00 := m2) (s00 := s);
            [exact MID| exact LE| exact HEAP2| exact PL2| exact FRM| lia| clear - B62; lia| exact CEIL'| unfold GLOBALS_TOP; lia
            | unfold SJ_S2_STACK, SJ_S2_FRAMES, RMALLOC_STACK; lia| lia| exact AL16| lia| lia| lia| apply (mod16_off8 q 41 AL16)| exact SRETC|].
          intros pcp s' ms' (IMPL & IDX & OC & IA & TAPE & SBUF & COPY & PO).
          exact (FIN (Some (pcp, COPY, len + 64)) IMPL IDX OC IA TAPE SBUF _ s' ms' PO LE).
        - apply implM_ret_bind.
          eapply (pj_pid_big_cps) with (B := B) (lo := lo) (m00 := m2) (s00 := s) (k := REST6 psb ptp pia poc pix pim p);
            [exact MID| lia| exact HEAP2| exact FRM| lia| clear - B62; lia| exact CEIL'| unfold GLOBALS_TOP; lia| lia| lia| lia| lia| lia| exact SRETC|].
          intros s' ms' (IMPL & IDX & OC & IA & TAPE & SBUF & PO).
          exact (FIN None IMPL IDX OC IA TAPE SBUF _ s' ms' PO I). }
    clear MID.
    intros ocp IMPL IDX OC IA TAPE SBUF lcapv s' ms' PO LE. unfold hpostF in PO.
    destruct PO as (u5 & u6 & u7 & u10 & u11 & u12 & u13 & u14 & u15 & u16 & u17 & u28 & u29 & u30 & u31 & F' & fc' & m3
                    & -> & FRM3 & MI3 & ST3 & (errv3 & ERR3) & AUX3 & FA3 & SO3 & RR).
    unfold pid_R in RR.
    destruct RR as (HEAP3 & PRES23 & (GOT3 & VT243 & VTD3) & SJS3 & PIMPL3 & DOCC3 & P483 & (r & SRET3 & OKR & RNZ)
                    & (vptr & nsi & p12 & nxt & p28 & capv & md & b48 & b49 & p50 & bufv & lenv & docv & THISC & ->) & BRTP & BRSB).
    replace (ret_pc (Z_to_bv 64 0x3f044)) with (Z_to_bv 64 0x3f044) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    pose proof (agree_of_lx_pres _ _ _ _ _ PRES23) as AG3.
    assert (XFR : forall a, rin_ivs (pid_front_X (q + 328) ++ pid_back_X (q + 56) (q + 328)) a -> ~ rin_ivs [LXW_SJ] a -> q + 56 <= a < q + 408).
    { intros a Ha NX. unfold pid_front_X, pid_back_X in Ha. cbn [app rin_ivs fst snd] in Ha, NX. clear - Ha NX. lia. }

    Ltac o3 := split; [unfold pid_front_X, pid_back_X, LXW_SJ, SJ_STATICS_LO, SJ_STATICS_HI; cbn [app rin_ivs fst snd]; lia| left; lia].
    tr1 AG3 F0 o3. tr1 AG3 F16 o3. tr1 AG3 GAPC o3. tr1 AG3 IMPW o3. tr1 AG3 P0 o3. tr1 AG3 P16 o3. tr1 AG3 ELC o3. tr1 AG3 OUTC o3.
    tr1 AG3 T1 o3. tr1 AG3 T2 o3. tr1 AG3 T3 o3. tr1 AG3 F848 o3. tr1 AG3 F936 o3.
    tr1 AG3 VC ltac:(split; [unfold pid_front_X, pid_back_X, LXW_SJ, SJ_STATICS_LO, SJ_STATICS_HI; cbn [app rin_ivs fst snd]; lia
                            | right; right; split; [lia| unfold ralloc_static, RMallocRep.RLIBC, RMallocRep.RCTX, RMallocRep.RERRNO, RMallocRep.RATP, RMallocRep.RSSP_GUARD, RMallocRep.RGOT_SSP; lia]]).
    tr1 AG3 AW ltac:(split; [unfold pid_front_X, pid_back_X, LXW_SJ, SJ_STATICS_LO, SJ_STATICS_HI; cbn [app rin_ivs fst snd]; lia
                            | right; left; exists (p, A, 8); split; [exact INA| cbn [blk_addr blk_size fst snd]; lia]]).
    assert (AEX3 : aex_tbl m3 3).
    { eapply aex_tbl_agree; [exact AG3| | exact AEX2]. intros a Ha. unfold aex_tbl_addr, AEX in Ha.
      split; [unfold pid_front_X, pid_back_X, LXW_SJ, SJ_STATICS_LO, SJ_STATICS_HI; cbn [app rin_ivs fst snd]; lia| right; right; split; [lia|]].
      unfold ralloc_static, RMallocRep.RLIBC, RMallocRep.RCTX, RMallocRep.RERRNO, RMallocRep.RATP, RMallocRep.RSSP_GUARD, RMallocRep.RGOT_SSP. lia. }
    assert (LXS3 : lx_statics m3).
    { eapply lx_statics_agree; [exact AG3| | exact LXS2]. intros a Ha. apply lxs_addr_client; [exact Ha|]. pose proof (lxs_addr_lt a Ha) as [R1 _]. unfold GLOBALS_TOP in R1.
      unfold lxs_addr, LX_GOT_STDERR, LX_STDERR_PTR, SJ_GOT_NOTHROW, SJ_IMPL_VT24, SJ_DPI_VPTR in Ha.
      unfold pid_front_X, pid_back_X, LXW_SJ, SJ_STATICS_LO, SJ_STATICS_HI. cbn [app rin_ivs fst snd]. clear - Ha R1 GLO LO. lia. }
    assert (VEC3 : imp_vec m3 (OW' ++ LB) (Some p)) by (exists A; split; [exact INA| split; [exact VC| exact AW]]).
    assert (PRES3 : lx_pres LB (q + 1056) [LXW_IMP; LXW_SJ; LXW_AEX] m00 m3).
    { eapply lx_pres_trans; [exact PRES2|]. eapply (lx_pres_sub LB (q + 1056) _ _ _ _ _ _ PRES23); [lia| intros b0 Hb0; apply in_or_app; right; exact Hb0|].
      intros a Ha NX. assert (NS : ~ rin_ivs [LXW_SJ] a) by (cbn [rin_ivs fst snd] in NX |- *; tauto).
      pose proof (XFR a Ha NS) as R. refine (conj _ (conj _ _)); [lia| intros IB; specialize (BLB a IB); lia| lia]. }
    assert (SSP3 : ssp_cells m3 canary).
    { pose proof (ssp_canary_0 _ _ _ _ HEAP0 SSP0) as EC. rewrite EC. eapply RHEAP_ssp. exact HEAP3. }
    clear AG3 XFR PRES2 HEAP2 AUX2 SJS2 AEX2 LXS2 PL2 PIMPL DOCC P48 SRETC GOT VT24 VTD MI2 ST2 ERR.
    replace (q + 328 + 8) with (q + 336) in PIMPL3 by lia. replace (q + 328 + 24) with (q + 352) in DOCC3, SRET3 by lia. replace (q + 328 + 48) with (q + 376) in P483 by lia.
    pose proof (LH_block_range _ _ _ _ HEAP3 ltac:(apply in_or_app; right; do 3 right; left; reflexivity)) as (IM0 & _ & _ & IMC & IMS).
    cbn [blk_addr blk_size fst snd] in IM0, IMC, IMS. unfold OSSVerify.Proofs.simdjson.fuzz_implementations.lib.Spec.Malloc.MCEIL in IMC.
    destruct OKR as [KE|(E0 & OKT)].
    -
      assert (ER : bv_eqb r (Z_to_bv 64 0) = false) by (unfold bv_eqb; rewrite unsigned_lit by lia; apply Z.eqb_neq; lia).
      unfold pj_res_cells in SRET3. rewrite ER in SRET3.
      rewrite <- (Z_to_bv_bv_unsigned r) in SRET3. set (rv := bv_unsigned r) in *.
      assert (GO : implM usegs (match ocp with Some b => mbind (del lops (blk_id b)) (fun _ => REST6 psb ptp pia poc pix pim p) | None => REST6 psb ptp pia poc pix pim p end) s'
                     (rfuzz_one_post ra (Z_to_bv 64 (q + 1056)) gp (Z_to_bv 64 RATP) S0 S1 S2 S3 S4 S5 S6 S7 S8 S9 S10 S11 s00 LB D d v lo B canary m00)
                     (MS (mkR (Z_to_bv 64 0x3f044) (Z_to_bv 64 q) gp (Z_to_bv 64 RATP) u5 u6 u7 (Z_to_bv 64 0) (Z_to_bv 64 D) u10 u11 u12 u13 u14 u15 u16 u17
                              (Z_to_bv 64 136) (Z_to_bv 64 1) (Z_to_bv 64 IMP_OS_VPTR) (Z_to_bv 64 SJ_FALLBACK) (Z_to_bv 64 len) s7
                              (Z_to_bv 64 0) (Z_to_bv 64 (q + 320)) (Z_to_bv 64 0) (Z_to_bv 64 64) u28 u29 u30 u31)
                         F' (Z_to_bv 64 0x3f044) fc' None m3 (seg_rom usegs))).
      { pose proof (munch_refl [(q + 424, q + 428)]%Z m3) as MU. pose proof (wmono_refl usegs m3) as WM.
        unfold implM. iprefix.

        step. GBGEU rv. step.
        if_cases KG.
        { exfalso. change (Z_to_bv 64 rv) with (MallocRep.wz rv) in KG. rewrite MallocRep.sx32_wz in KG by lia.
          unfold MallocRep.wz, bv_eqb in KG. rewrite !unsigned_lit in KG by lia. destruct (Z.eqb_spec rv 0); [lia| discriminate KG]. }
        clear KG.

        hide THISC. hide VC. hide AW. unfold p48_cells in P483. clear GOT3 VT243 VTD3.
        hstep. zstep. step.
        lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m4 end.
        pose proof (agree_on_of_munch _ _ _ MU WM) as AG4.
        unhide THISC. unhide VC. unhide AW.
        tr1 AG4 THISC ltac:(cbn [outside]; split; [clear - Ha IM0 IMC CEIL LO; lia| exact I]).
        tr1 AG4 VC ltac:(cbn [outside]; split; [lia| exact I]). tr1 AG4 AW ltac:(cbn [outside]; split; [lia| exact I]).
        eapply LH_frame in HEAP3; [| exact MU| exact WM| constructor; [apply W_ok_stack; cbn; lia| constructor]].
        eapply rauxv_ok_frame in AUX3; [| exact MU| exact WM| constructor; [cbn; unfold RAUXV_CELL; lia| constructor]].
        assert (SJS4 : sj_statics m4 true).
        { eapply sj_statics_agree; [exact AG4| | exact SJS3]. intros a Ha. pose proof (sjs_addr_lt a Ha) as [Ra _]. unfold GLOBALS_TOP in Ra. cbn [outside]. split; [lia| exact I]. }
        assert (AEX4 : aex_tbl m4 3).
        { eapply aex_tbl_agree; [exact AG4| | exact AEX3]. intros a Ha. unfold aex_tbl_addr, AEX in Ha. cbn [outside]. split; [lia| exact I]. }
        assert (VEC4 : imp_vec m4 (OW' ++ LB) (Some p)) by (exists A; split; [exact INA| split; [exact VC| exact AW]]).
        assert (PRES4 : lx_pres LB (q + 1056) [LXW_IMP; LXW_SJ; LXW_AEX] m00 m4).
        { eapply lx_pres_trans; [exact PRES3|]. eapply lx_pres_of_munch; [exact MU| exact WM|].
          intros a Ha [HX HC]. cbn [outside]. split; [| exact I]. destruct HC as [HC|[HC|HC]]; [lia| specialize (BLB a HC); lia| lia]. }
        pose proof (rw_cells_forget _ _ _ _ ELC) as [jel F392]. cbn [cells_size csize Nat.add cells_bytes] in F392.
        ihere. to_implM.
        lazymatch goal with |- implM ?sg ?pr ?st ?QQ ?ms => change (implM sg (mbind (del_opt lops (option_map blk_id (@None block))) (fun _ => pr)) st QQ ms) end.
        pose proof (rw_cells_join _ _ _ _ _ SRET3 GAPC ltac:(cbn [cells_size csize Nat.add]; lia)) as JB.
        apply rw_cells_forget in JB. destruct JB as [bs40 F40]. cbn [app cells_size csize Nat.add cells_bytes] in F40.
        lazymatch goal with H : stk _ m4 _ _ |- _ => rename H into ST4 end. lazymatch goal with H : mem_inv _ m4 |- _ => rename H into MI4 end.
        eapply (lftoi_tail HF None ocp) with (B := B) (lo := lo) (ne := 1);
          [exact FRM3| exact MI4| exact ST4| exact ERR3| exact AUX3| congruence| congruence| exact CEIL'| unfold GLOBALS_TOP; lia| lia| lia| unfold IMP_FRAME; lia| lia
          | exact HEAP0| exact LXS0| exact SEW0| exact SSP0| exact PL0| exact HEAP3| exact XN| exact VEC4| exact SJS4| exact AEX4| unfold IMP_FRAME; exact PRES4| lia
          | exact F0| exact F16| exact F40| exact IMPW| exact P0| exact PIMPL3| exact P16| exact DOCC3| exact P483| exact F392| apply out0_short; exact OUTC
          | do 4 eexists; exact T1| do 4 eexists; exact T2| do 4 eexists; exact T3| exact F848| exact F936| exact THISC]. }
      destruct ocp as [b|]; [| exact GO].
      apply (ImpImpl.implM_imp_gate_fail usegs raw_malloc raw_free ps_so set_so_ps len (fun _ => mbind (del lops (blk_id b)) (fun _ => REST6 psb ptp pia poc pix pim p))). exact GO.
    -
      subst r. destruct ocp as [b|]; [| exfalso; exact (RNZ eq_refl eq_refl)].
      unfold pj_res_cells in SRET3.
      lazymatch type of SRET3 with context [bv_eqb ?x ?y] => change (bv_eqb x y) with true in SRET3 end. cbv iota in SRET3.
      apply (ImpImpl.implM_imp_gate_ok_cps usegs raw_malloc raw_free ps_so set_so_ps len (fun _ => mbind (del lops (blk_id b)) (fun _ => REST6 psb ptp pia poc pix pim p))).
      pose proof (munch_refl [(q - 16, q)]%Z m3) as MU. pose proof (wmono_refl usegs m3) as WM.
      unfold implM. iprefix.

      step. GBGEU 0. step. if_true. clear MU WM.
      pose proof F16 as F16'. split_cells F16' 1%nat N16 VT24c.
      pose proof (rw_cells_forget _ _ _ _ ELC) as [jel F392]. cbn [cells_size csize Nat.add cells_bytes] in F392. clear ELC.
      cbn [ocp_blocks app] in HEAP3.
      ihere. to_implM.
      eapply (OKARM _ (fun cpy => mbind (del_opt lops cpy) (fun _ => mbind (del lops (blk_id b)) (fun _ => REST6 psb ptp pia poc pix pim p))))
        with (q := q) (lo := lo) (B := B) (len := len) (TAPE := TAPE) (SBUF := SBUF) (cap := cap) (ptp := ptp) (psb := psb) (canary := canary);
        [exact HEAP3| do 5 right; left; reflexivity| do 6 right; left; reflexivity| exact AUX3| unfold IMP_FRAME; lia| exact B62| exact ST3| exact CEIL'| unfold GLOBALS_TOP; lia
        | unfold IMP_OKARM_STACK; lia| exact ERR3| exact MI3| exact FRM3| exact AL16| lia| exact LXS3| exact SJS3| exact SSP3| subst cap; lia| reflexivity
        | exact VT24c| unfold IMP_DOC; exact SRET3| exact GAPC| exact F392| exact OUTC| exact F848| unfold IMP_DOC; exact DOCC3| right; split; [reflexivity| exact OKT]|].
      intros cpy sJ msJ PJ. unfold imp_okarm_post in PJ.
      destruct PJ as (y1 & w5 & w6 & w7 & w10 & w11 & w12 & w13 & w14 & w15 & w16 & w17 & w22 & w23 & w28 & w29 & w30 & w31 & FJ & fcJ & mJ & errvJ & ostr
                      & -> & ECPY & FRMJ & MIJ & STJ & ERRJ & AUXJ & FAJ & SOJ & HEAPJ & PRESJ & SJSJ & OUTJ & (bs40 & F40J) & (bsel & F392J) & (bsb & F848J)).
      subst cpy.
      pose proof (agree_of_lx_pres _ _ _ _ _ PRESJ) as AGJ.
      Ltac oJ := split; [unfold imp_okarm_X, LXW_SJ, SJ_STATICS_LO, SJ_STATICS_HI; cbn [rin_ivs fst snd]; lia| left; lia].
      tr1 AGJ F0 oJ. tr1 AGJ F16 oJ. tr1 AGJ IMPW oJ. tr1 AGJ P0 oJ. tr1 AGJ PIMPL3 oJ. tr1 AGJ P16 oJ. tr1 AGJ DOCC3 oJ. unfold p48_cells in P483. tr1 AGJ P483 oJ.
      tr1 AGJ T1 oJ. tr1 AGJ T2 oJ. tr1 AGJ T3 oJ. tr1 AGJ F936 oJ.
      tr1 AGJ THISC ltac:(split; [unfold imp_okarm_X, LXW_SJ, SJ_STATICS_LO, SJ_STATICS_HI; cbn [rin_ivs fst snd]; clear - Ha IM0 IMC IMS CEIL LO GLO; lia
                                 | right; left; exists (pim, IMPL, 96); split; [do 4 right; left; reflexivity| cbn [blk_addr blk_size fst snd]; lia]]).
      tr1 AGJ VC ltac:(split; [unfold imp_okarm_X, LXW_SJ, SJ_STATICS_LO, SJ_STATICS_HI; cbn [rin_ivs fst snd]; lia
                              | right; right; split; [lia| unfold ralloc_static, RMallocRep.RLIBC, RMallocRep.RCTX, RMallocRep.RERRNO, RMallocRep.RATP, RMallocRep.RSSP_GUARD, RMallocRep.RGOT_SSP; lia]]).
      tr1 AGJ AW ltac:(split; [unfold imp_okarm_X, LXW_SJ, SJ_STATICS_LO, SJ_STATICS_HI; cbn [rin_ivs fst snd]; lia
                              | right; left; exists (p, A, 8); split; [right; do 6 right; exact INA| cbn [blk_addr blk_size fst snd]; lia]]).
      assert (AEXJ : aex_tbl mJ 3).
      { eapply aex_tbl_agree; [exact AGJ| | exact AEX3]. intros a Ha. unfold aex_tbl_addr, AEX in Ha.
        split; [unfold imp_okarm_X, LXW_SJ, SJ_STATICS_LO, SJ_STATICS_HI; cbn [rin_ivs fst snd]; lia| right; right; split; [lia|]].
        unfold ralloc_static, RMallocRep.RLIBC, RMallocRep.RCTX, RMallocRep.RERRNO, RMallocRep.RATP, RMallocRep.RSSP_GUARD, RMallocRep.RGOT_SSP. lia. }
      assert (VECJ : imp_vec mJ (OW' ++ LB) (Some p)) by (exists A; split; [exact INA| split; [exact VC| exact AW]]).
      assert (PRESF : lx_pres LB (q + 1056) [LXW_IMP; LXW_SJ; LXW_AEX] m00 mJ).
      { eapply lx_pres_trans; [exact PRES3|]. eapply (lx_pres_sub LB (q + 1056) _ _ _ _ _ _ PRESJ); [lia| intros b0 Hb0; right; do 6 right; apply in_or_app; right; exact Hb0|].
        intros a Ha NX. unfold imp_okarm_X in Ha. cbn [rin_ivs fst snd] in Ha, NX. refine (conj _ (conj _ _)); [lia| intros IB; specialize (BLB a IB); lia| lia]. }
      eapply (lftoi_tail HF ostr (Some b)) with (B := B) (lo := lo) (ne := 0);
        [exact FRMJ| exact MIJ| exact STJ| exact ERRJ| exact AUXJ| congruence| congruence| exact CEIL'| unfold GLOBALS_TOP; lia| lia| lia| unfold IMP_FRAME; lia| lia
        | exact HEAP0| exact LXS0| exact SEW0| exact SSP0| exact PL0| exact HEAPJ| exact XN| exact VECJ| exact SJSJ| exact AEXJ| unfold IMP_FRAME; exact PRESF| lia
        | exact F0| exact F16| exact F40J| exact IMPW| exact P0| exact PIMPL3| exact P16| exact DOCC3| exact P483| exact F392J| exact OUTJ
        | do 4 eexists; exact T1| do 4 eexists; exact T2| do 4 eexists; exact T3| exact F848J| exact F936| exact THISC].
  Qed.
End Proofs.
End WithCeiling0.
