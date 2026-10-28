(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP MonadX StoreFast.
From OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.Malloc Require Import MallocBlocks Malloc_iface.
From OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.MallocU Require Import RMallocRep RMallocTree RMalloc_iface.
From OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.Spec Require Import Prelim STree Malloc Monad Stdio SjModel Target Prog.
From OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.P Require Import Sj_h_arith.
From OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.U Require Import Layout Exit Printf_wfile Sj_iface Sj_kit Sj_new Sj_h_kit Sj_h_setters.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
From OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.Lib Require Import Ceiling.
From OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.P Require Import Rnd.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac std_lia__ := lia.
Local Ltac lia := first [std_lia__ | try (pose proof alloc_ceiling_range as CEIL_RANGE__); std_lia__].

Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.

Definition dpi_vtable_cells : list cell :=
  [C8 (Z_to_bv 64 SJ_DPI_PARSE); C8 (Z_to_bv 64 SJ_DPI_STAGE1); C8 (Z_to_bv 64 SJ_DPI_STAGE2); C8 (Z_to_bv 64 SJ_DPI_STAGE2_NEXT);
   C8 (Z_to_bv 64 SJ_DPI_PARSE_STRING); C8 (Z_to_bv 64 SJ_DPI_PARSE_WOBBLY); C8 (Z_to_bv 64 SJ_DPI_SET_CAPACITY);
   C8 (Z_to_bv 64 SJ_DPI_SET_MAX_DEPTH); C8 (Z_to_bv 64 SJ_DPI_DTOR); C8 (Z_to_bv 64 SJ_DPI_DTOR_DEL)].

Definition create_R (LB : list block) (q DST cap : Z) (m : mem) (pim pix poc pia : bptr) : word -> PState -> mem -> Prop :=
  fun a0 s' m' => exists IMPL IDX OC IA ws junk1 junk2 p12 p28 p50,
     a0 = Z_to_bv 64 0
     /\ RHEAP s' ((pia, IA, 1024) :: (poc, OC, 8192) :: (pix, IDX, 4 * (roundup64 cap + 9)) :: (pim, IMPL, 96) :: LB) m'
     /\ lx_pres LB q [(DST, DST + 8)] m m'
     /\ rw_cells usegs m' DST [C8 (Z_to_bv 64 IMPL)]
     /\ rw_cells usegs m' IMPL (impl_cells16 (Z_to_bv 64 SJ_DPI_VPTR) (Z_to_bv 64 0) p12 (Z_to_bv 64 IDX) (Z_to_bv 64 0) p28 (Z_to_bv 64 cap) (Z_to_bv 64 1024)
                                             (Z_to_bv 8 0) (Z_to_bv 8 0) p50 (Z_to_bv 64 OC) (Z_to_bv 64 IA) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0))
     /\ u32arr usegs m' IDX ws /\ length ws = Z.to_nat (roundup64 cap + 9)
     /\ rw_cells usegs m' OC [CB (Z.to_nat 8192) junk1] /\ rw_cells usegs m' IA [CB (Z.to_nat 1024) junk2]
     /\ rblock_range IMPL 96 /\ rblock_range IDX (4 * (roundup64 cap + 9)) /\ rblock_range OC 8192 /\ rblock_range IA 1024.

Section Proofs.
  Hypothesis HM : rmalloc_stmt.
  Hypothesis HF : rfree_stmt.

  Lemma create_cps : forall {A} (k : bptr -> bptr -> bptr -> bptr -> M PState A) (Q : A -> PState -> machine_state -> Prop)
      (ra gp t0 t1 t2 s0 s1 a0 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (s : PState) (LB : list block) (q lo B : Z) (errv : word)
      (DST cap : Z),
    RHEAP s LB m -> rauxv_ok m B -> q <= B ->
    stk usegs m lo q -> alloc_ceiling <= lo -> lo <= q - (64 + SJ_OPNEW_STACK) ->
    rw_cells usegs m LX_ERRNO [C4 errv] -> mem_inv usegs m -> 0 <= q < 2^64 ->
    q <= DST -> DST + 8 <= B -> 32 <= cap <= 2^26 ->
    rw_cells usegs m SJ_GOT_NOTHROW [C8 (Z_to_bv 64 SJ_NOTHROW_TAG)] ->
    rw_cells usegs m SJ_DPI_VPTR dpi_vtable_cells ->
    rw_cells usegs m DST [C8 (Z_to_bv 64 0)] ->
    (forall pim pix poc pia s' ms',
        hpost ra q gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s lo B (create_R LB q DST cap m pim pix poc pia) s' ms' ->
        implM usegs (k pim pix poc pia) s' Q ms') ->
    implM usegs (mbind (newnt lops 96) (fun im => mbind (newnt lops (4 * (roundup64 cap + 9))) (fun ix =>
                 mbind (newnt lops 8192) (fun oc => mbind (newnt lops 1024) (fun ia => k im ix oc ia))))) s Q
      (MS (mkR ra (Z_to_bv 64 q) gp (Z_to_bv 64 RATP) t0 t1 t2 s0 s1 a0 (Z_to_bv 64 cap) (Z_to_bv 64 1024) (Z_to_bv 64 DST) a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 SJ_CREATE_DPI) fc None m (seg_rom usegs)).
  Proof.
    intros A k Q. intros until cap. intros HEAP AUX QB ST CEIL LO ERR MI Hq QD DB CAP GOT VT DSTC HK.
    unfold SJ_CREATE_DPI, SJ_OPNEW_STACK, RMALLOC_STACK, SJ_GOT_NOTHROW, SJ_NOTHROW_TAG, SJ_DPI_VPTR, dpi_vtable_cells in *.
    assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    pose proof CEIL as CEIL'. unfold OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.Spec.Malloc.MCEIL in CEIL; try (pose proof alloc_ceiling_range as CEIL_RANGE__).
    pose proof (munch_refl [(q - 32, q); (DST, DST + 8)]%Z m) as MU. pose proof (wmono_refl usegs m) as WM.
    assert (ELX : LX_ERRNO = 977220) by reflexivity. rewrite ELX in ERR.
    assert (BLB : forall b, In b LB -> blk_addr b + blk_size b <= alloc_ceiling).
    { intros b Hb. pose proof (LH_block_range _ _ _ _ HEAP Hb) as (_ & _ & _ & BC & _).
      unfold OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.Spec.Malloc.MCEIL in BC. exact BC. }
    assert (CLI : forall a, 0 <= a < 2^64 -> lx_client LB q [(DST, DST + 8)] a -> outside [(q - 32, q); (DST, DST + 8)] a).
    { intros a Ha [HX HC]. cbn [rin_ivs fst snd] in HX. cbn [outside]. split; [|split; [lia| exact I]].
      destruct HC as [HC|[(b & Hb & Hr)|HC]]; [lia| | lia]. specialize (BLB b Hb). lia. }
    unfold implM. iprefix.
    step. carve_frame 32%nat ST.
    apply (rw_cells_split_CB usegs _ _ [] 32 junk [] [8;8;8;8]%nat) in FR; [|reflexivity]. cbn [mk_CB_cells app] in FR.

    step. step. step. step. step. step. step. step. step. step. step.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m1 end.
    assert (HEAP1 : RHEAP s LB m1).
    { eapply LH_frame; [exact HEAP| exact MU| exact WM|].
      constructor; [apply W_ok_stack; cbn; lia|]. constructor; [apply W_ok_stack; cbn; lia| constructor]. }
    assert (AUX1 : rauxv_ok m1 B).
    { eapply rauxv_ok_frame; [exact AUX| exact MU| exact WM|].
      constructor; [cbn; unfold RAUXV_CELL; lia|]. constructor; [cbn; unfold RAUXV_CELL; lia| constructor]. }
    ihere. to_implM. eapply implM_bind.
    { eapply (opnew_nt_proof HM) with (B := B) (lo := lo);
        [exact HEAP1| exact AUX1| lia| exact ST| exact CEIL'| unfold SJ_OPNEW_STACK, RMALLOC_STACK; lia| rewrite ELX; exact ERR| exact MI| lia| lia]. }
    cbv beta. intros pim s1' ms1 PO. unfold opnew_postZ in PO.
    destruct PO as (r5 & r6 & r7 & r11 & r12 & r13 & r14 & r15 & r16 & r17 & r28 & r29 & r30 & r31 & m3 & errv3 & IMPL & junk1
                    & -> & MI3 & ST3 & ERR3 & AUX3 & HP & FA & SO & BR1 & HEAP3 & BLK1).
    replace (ret_pc (Z_to_bv 64 0x4176c)) with (Z_to_bv 64 0x4176c) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    apply (rw_cells_agree _ _ _ _ _ (agree_of_heap_pres _ _ _ _ HP)) in FR; [| intros a Ha; left; cbn in Ha; lia].
    apply (rw_cells_agree _ _ _ _ _ (agree_of_heap_pres _ _ _ _ HP)) in DSTC; [| intros a Ha; left; cbn in Ha; lia].
    apply (rw_cells_agree _ _ _ _ _ (agree_of_heap_pres _ _ _ _ HP)) in GOT;
      [| intros a Ha; right; left; cbn in Ha; unfold ralloc_static, RMallocRep.RLIBC, RMallocRep.RCTX, RMallocRep.RERRNO, RMallocRep.RATP, RMallocRep.RSSP_GUARD, RMallocRep.RGOT_SSP; lia].
    apply (rw_cells_agree _ _ _ _ _ (agree_of_heap_pres _ _ _ _ HP)) in VT;
      [| intros a Ha; right; left; cbn in Ha; unfold ralloc_static, RMallocRep.RLIBC, RMallocRep.RCTX, RMallocRep.RERRNO, RMallocRep.RATP, RMallocRep.RSSP_GUARD, RMallocRep.RGOT_SSP; lia].
    assert (PRES3 : lx_pres LB q [(DST, DST + 8)] m m3).
    { eapply lx_pres_trans; [eapply lx_pres_of_munch; [exact MU| exact WM| exact CLI]|].
      apply lx_pres_of_heap_pres. eapply rheap_pres_weaken; [exact HP| lia| auto]. }
    clear MU WM HEAP1 AUX1 HP.
    pose proof BR1 as (IM0 & _ & _ & IMC & IMS). unfold OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.Spec.Malloc.MCEIL in IMC.
    pose proof (LH_head_disj _ _ _ _ _ _ HEAP3) as DJ.
    pose proof (munch_refl [(q - 32, q); (DST, DST + 8); (IMPL, IMPL + 96)]%Z m3) as MU. pose proof (wmono_refl usegs m3) as WM.
    assert (CLI3 : forall a, 0 <= a < 2^64 -> lx_client LB q [(DST, DST + 8)] a -> outside [(q - 32, q); (DST, DST + 8); (IMPL, IMPL + 96)] a).
    { intros a Ha HC. destruct (CLI a Ha HC) as (O1 & O2 & _). cbn [outside]. split; [exact O1|]. split; [exact O2|]. split; [| exact I].
      destruct HC as [HX [HC|[HC|HC]]]; [lia| apply DJ; exact HC| lia]. }
    change (Z.to_nat 96) with 96%nat in BLK1.
    apply (rw_cells_split_CB usegs _ _ [] 96 junk1 [] [8;4;4;8;4;4;8;8;2;6;8;8;8;8;8]%nat) in BLK1; [|reflexivity]. cbn [mk_CB_cells app] in BLK1.
    rewrite ELX in ERR3.
    unfold implM. iprefix.

    step.
    if_cases K1; zify_cond K1; [exfalso; rewrite ?unsigned_lit in K1 by lia; lia|]. clear K1.
    zstep. step. rewrite (land15_aligned IMPL) by (destruct BR1 as (? & AL16 & _); first [lia| exact AL16]). if_false.
    step. hstep. hstep. hstep. hstep. step. step. hstep. hstep. hstep. hstep. hstep. hstep. hstep. hstep.
    apply (rw_cells_C2_split _ _ [_; _; _; _; _; _; _; _]) in BLK1. cbn [app] in BLK1.
    lazymatch type of BLK1 with rw_cells _ _ _ [_; _; CB 4 ?a; _; _; CB 4 ?b; _; _; _; _; CB 6 ?c; _; _; _; _; _] =>
      remember a as p12 eqn:E12; remember b as p28 eqn:E28; remember c as p50 eqn:E50; clear E12 E28 E50 end.

    step. step. if_false. step.
    zstep. step. rewrite (land7_aligned IMPL) by (destruct BR1 as (? & AL16 & _); first [lia| exact AL16]). if_false.
    step. step. step. step.
    replace (ret_pc (Z_to_bv 64 SJ_DPI_SET_CAPACITY)) with (Z_to_bv 64 SJ_DPI_SET_CAPACITY)
      by (symmetry; apply ret_pc_even; [unfold SJ_DPI_SET_CAPACITY; lia| reflexivity]).
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m4 end.
    assert (HEAP4 : RHEAP s1' ((pim, IMPL, 96) :: LB) m4).
    { eapply LH_frame; [exact HEAP3| exact MU| exact WM|].
      constructor; [apply W_ok_stack; cbn; lia|]. constructor; [apply W_ok_stack; cbn; lia|].
      constructor; [eapply (W_ok_block _ (pim, IMPL, 96)); [left; reflexivity| cbn; lia| cbn; lia]| constructor]. }
    assert (AUX4 : rauxv_ok m4 B).
    { eapply rauxv_ok_frame; [exact AUX3| exact MU| exact WM|].
      constructor; [cbn; unfold RAUXV_CELL; lia|]. constructor; [cbn; unfold RAUXV_CELL; lia|].
      constructor; [cbn; unfold RAUXV_CELL; lia| constructor]. }
    assert (PRES4 : lx_pres LB q [(DST, DST + 8)] m m4).
    { eapply lx_pres_trans; [exact PRES3|]. eapply lx_pres_of_munch; [exact MU| exact WM| exact CLI3]. }
    clear MU WM PRES3.
    ihere. to_implM.
    eapply (setcap_cps HM) with (B := B) (lo := lo) (pim := pim) (THIS := IMPL) (cap := cap);
      [exact HEAP4| left; reflexivity| exact AUX4| lia| exact ST3| exact CEIL'| unfold SJ_OPNEW_STACK, RMALLOC_STACK; lia
      | rewrite ELX; exact ERR3| assumption| lia| change (2^26) with 67108864; lia| exact GOT| unfold impl_cells16; exact BLK1|].
    intros pix s2' ms2 PO. unfold hpost in PO.
    destruct PO as (u5 & u6 & u7 & u10 & u11 & u12 & u13 & u14 & u15 & u16 & u17 & u28 & u29 & u30 & u31 & m5
                    & -> & MI5 & ST5 & (errv5 & ERR5) & AUX5 & FA5 & SO5 & RR).
    unfold setcap_R in RR. destruct RR as (IDX & ws & -> & HEAP5 & PRES45 & THISC5 & ARR & LWS & BR2).
    replace (ret_pc (Z_to_bv 64 268292)) with (Z_to_bv 64 268292) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    apply (rw_cells_agree _ _ _ _ _ (agree_of_lx_pres _ _ _ _ _ PRES45)) in FR; [| intros a Ha; cbn in Ha; split; [cbn [rin_ivs fst snd]; lia| left; lia]].
    apply (rw_cells_agree _ _ _ _ _ (agree_of_lx_pres _ _ _ _ _ PRES45)) in DSTC; [| intros a Ha; cbn in Ha; split; [cbn [rin_ivs fst snd]; lia| left; lia]].
    apply (rw_cells_agree _ _ _ _ _ (agree_of_lx_pres _ _ _ _ _ PRES45)) in GOT;
      [| intros a Ha; cbn in Ha; split; [cbn [rin_ivs fst snd]; lia| right; right; split; [lia|
           unfold ralloc_static, RMallocRep.RLIBC, RMallocRep.RCTX, RMallocRep.RERRNO, RMallocRep.RATP, RMallocRep.RSSP_GUARD, RMallocRep.RGOT_SSP; lia]]].
    apply (rw_cells_agree _ _ _ _ _ (agree_of_lx_pres _ _ _ _ _ PRES45)) in VT;
      [| intros a Ha; cbn in Ha; split; [cbn [rin_ivs fst snd]; lia| right; right; split; [lia|
           unfold ralloc_static, RMallocRep.RLIBC, RMallocRep.RCTX, RMallocRep.RERRNO, RMallocRep.RATP, RMallocRep.RSSP_GUARD, RMallocRep.RGOT_SSP; lia]]].
    assert (PRES5 : lx_pres LB q [(DST, DST + 8)] m m5).
    { eapply lx_pres_trans; [exact PRES4|].
      eapply (lx_pres_sub LB q _ _ _ _ _ _ PRES45); [lia| intros b Hb; right; exact Hb|].
      intros a Ha _. cbn [rin_ivs fst snd] in Ha. split; [lia|]. split; [intros IB; apply (DJ a IB); lia| lia]. }
    clear PRES4 PRES45 HEAP4 AUX4.
    pose proof BR2 as (IX0 & _ & _ & IXC & IXS). unfold OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.Spec.Malloc.MCEIL in IXC.
    pose proof (munch_refl [(q - 32, q)]%Z m5) as MU. pose proof (wmono_refl usegs m5) as WM.
    unfold impl_cells16 in THISC5.
    unfold implM. iprefix.

    step. step. if_false. step. if_false. step. step.
    if_cases K3; zify_cond K3; [exfalso; rewrite ?unsigned_lit in K3 by lia; lia|]. clear K3.
    zstep. step. rewrite (land7_aligned IMPL) by (destruct BR1 as (? & AL16 & _); first [lia| exact AL16]). if_false.
    step. step. step. step.
    replace (ret_pc (Z_to_bv 64 SJ_DPI_SET_MAX_DEPTH)) with (Z_to_bv 64 SJ_DPI_SET_MAX_DEPTH)
      by (symmetry; apply ret_pc_even; [unfold SJ_DPI_SET_MAX_DEPTH; lia| reflexivity]).
    ihere. to_implM.
    eapply (setmd_cps HM) with (B := B) (lo := lo) (pim := pim) (THIS := IMPL);
      [exact HEAP5| right; left; reflexivity| exact AUX5| lia| exact ST5| exact CEIL'| unfold SJ_OPNEW_STACK, RMALLOC_STACK; lia
      | exact ERR5| exact MI5| lia| exact GOT| unfold impl_cells16; exact THISC5|].
    intros poc pia s3' ms3 PO. unfold hpost in PO.
    destruct PO as (v5 & v6 & v7 & v10 & v11 & v12 & v13 & v14 & v15 & v16 & v17 & v28 & v29 & v30 & v31 & m7
                    & -> & MI7 & ST7 & (errv7 & ERR7) & AUX7 & FA7 & SO7 & RR).
    unfold setmd_R in RR. destruct RR as (OC & IA & junk2 & junk3 & -> & HEAP7 & PRES57 & THISC7 & BLKOC & BLKIA & BR3 & BR4).
    replace (ret_pc (Z_to_bv 64 0x41830)) with (Z_to_bv 64 0x41830) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    apply (rw_cells_agree _ _ _ _ _ (agree_of_lx_pres _ _ _ _ _ PRES57)) in FR; [| intros a Ha; cbn in Ha; split; [cbn [rin_ivs fst snd]; lia| left; lia]].
    unfold implM. iprefix.

    step. step. if_false. step. step. step. step. step. release_frame FR ST7 q. step.
    ihere. to_implM.
    apply HK. unfold hpost. do 15 eexists. exists m7.
    split; [cbv delta [mkR]; reflexivity|]. split; [exact MI7|]. split; [exact ST7|]. split; [exists errv7; exact ERR7|]. split; [exact AUX7|].
    split; [congruence|]. split; [congruence|].
    unfold create_R. exists IMPL, IDX, OC, IA, ws, junk2, junk3, p12, p28, p50.
    split; [reflexivity|]. split; [exact HEAP7|].
    pose proof (LH_head_disj _ _ _ _ _ _ HEAP5) as DJ5.
    split. { eapply lx_pres_trans; [exact PRES5|].
             eapply (lx_pres_sub LB q _ _ _ _ _ _ PRES57); [lia| intros b Hb; right; right; exact Hb|].
             intros a Ha _. cbn [rin_ivs fst snd] in Ha. split; [lia|]. split; [intros IB; apply (DJ a IB); lia| lia]. }
    split. { eapply (rw_cells_agree _ _ _ _ _ (agree_of_lx_pres _ _ _ _ _ PRES57)); [exact DSTC|].
             intros a Ha; cbn in Ha; split; [cbn [rin_ivs fst snd]; lia| left; lia]. }
    split; [exact THISC7|].
    pose proof (LH_head_sep _ _ _ _ _ _ _ _ _ HEAP5 ltac:(left; reflexivity)) as SEPI.
    pose proof (u32arr_bound _ _ _ _ ARR) as AB.
    split. { eapply (u32arr_agree _ _ _ _ _ (agree_of_lx_pres _ _ _ _ _ PRES57)); [exact ARR|].
             intros a Ha. split; [cbn [rin_ivs fst snd]; lia|]. right; left. exists (pix, IDX, 4 * (roundup64 cap + 9)).
             split; [left; reflexivity| cbn [blk_addr blk_size fst snd]; lia]. }
    split; [exact LWS|]. split; [exact BLKOC|]. split; [exact BLKIA|]. split; [exact BR1|]. split; [exact BR2|]. split; [exact BR3| exact BR4].
  Qed.
End Proofs.
End WithCeiling0.
