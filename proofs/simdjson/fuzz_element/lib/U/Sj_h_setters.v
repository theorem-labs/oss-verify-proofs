(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP MonadX StoreFast.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Malloc Require Import MallocBlocks Malloc_iface.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.MallocU Require Import RMallocRep RMallocTree RMalloc_iface.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Spec Require Import Prelim STree Malloc Monad Stdio SjModel Target Prog.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.P Require Import Sj_h_arith.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.U Require Import Layout Exit Printf_wfile Sj_iface Sj_kit Sj_new Sj_h_kit.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Lib Require Import Ceiling.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.P Require Import Rnd.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac std_lia__ := lia.
Local Ltac lia := first [std_lia__ | try (pose proof alloc_ceiling_range as CEIL_RANGE__); std_lia__].

Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.

Definition setcap_R (LB : list block) (q THIS cap : Z) (m : mem) (pix : bptr)
    (vptr : word) (p12 : list byte) (nxt : word) (p28 : list byte) (md : word) (b48 b49 : byte) (p50 : list byte) (oc ia bufv lenv docv : word)
    : word -> PState -> mem -> Prop :=
  fun a0 s' m' => exists IDX ws,
     a0 = Z_to_bv 64 0
     /\ RHEAP s' ((pix, IDX, 4 * (roundup64 cap + 9)) :: LB) m'
     /\ lx_pres LB q [(THIS, THIS + 96)] m m'
     /\ rw_cells usegs m' THIS (impl_cells16 vptr (Z_to_bv 64 0) p12 (Z_to_bv 64 IDX) nxt p28 (Z_to_bv 64 cap) md b48 b49 p50 oc ia bufv lenv docv)
     /\ u32arr usegs m' IDX ws /\ length ws = Z.to_nat (roundup64 cap + 9)
     /\ rblock_range IDX (4 * (roundup64 cap + 9)).

Definition setmd_R (LB : list block) (q THIS : Z) (m : mem) (poc pia : bptr)
    (vptr nsi : word) (p12 : list byte) (idx nxt : word) (p28 : list byte) (capv : word) (b48 b49 : byte) (p50 : list byte) (bufv lenv docv : word)
    : word -> PState -> mem -> Prop :=
  fun a0 s' m' => exists OC IA junk1 junk2,
     a0 = Z_to_bv 64 0
     /\ RHEAP s' ((pia, IA, 1024) :: (poc, OC, 8192) :: LB) m'
     /\ lx_pres LB q [(THIS, THIS + 96)] m m'
     /\ rw_cells usegs m' THIS (impl_cells16 vptr nsi p12 idx nxt p28 capv (Z_to_bv 64 1024) b48 b49 p50 (Z_to_bv 64 OC) (Z_to_bv 64 IA) bufv lenv docv)
     /\ rw_cells usegs m' OC [CB (Z.to_nat 8192) junk1] /\ rw_cells usegs m' IA [CB (Z.to_nat 1024) junk2]
     /\ rblock_range OC 8192 /\ rblock_range IA 1024.

Section Proofs.
  Hypothesis HM : rmalloc_stmt.
  Hypothesis HF : rfree_stmt.

  Lemma setcap_cps : forall {A} (k : bptr -> M PState A) (Q : A -> PState -> machine_state -> Prop)
      (ra gp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (s : PState) (LB : list block) (q lo B : Z) (errv : word)
      (THIS cap : Z) (pim : bptr)
      (vptr nsi : word) (p12 : list byte) (nxt : word) (p28 : list byte) (capv md : word) (b48 b49 : byte) (p50 : list byte) (oc ia bufv lenv docv : word),
    RHEAP s LB m -> In (pim, THIS, 96) LB -> rauxv_ok m B -> q <= B ->
    stk usegs m lo q -> alloc_ceiling <= lo -> lo <= q - (32 + SJ_OPNEW_STACK) ->
    rw_cells usegs m LX_ERRNO [C4 errv] -> mem_inv usegs m -> 0 <= q < 2^64 ->
    32 <= cap <= 2^26 ->
    rw_cells usegs m SJ_GOT_NOTHROW [C8 (Z_to_bv 64 SJ_NOTHROW_TAG)] ->
    rw_cells usegs m THIS (impl_cells16 vptr nsi p12 (Z_to_bv 64 0) nxt p28 capv md b48 b49 p50 oc ia bufv lenv docv) ->
    (forall pix s' ms',
        hpost ra q gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s lo B
              (setcap_R LB q THIS cap m pix vptr p12 nxt p28 md b48 b49 p50 oc ia bufv lenv docv) s' ms' ->
        implM usegs (k pix) s' Q ms') ->
    implM usegs (mbind (newnt lops (4 * (roundup64 cap + 9))) k) s Q
      (MS (mkR ra (Z_to_bv 64 q) gp (Z_to_bv 64 RATP) t0 t1 t2 s0 s1 (Z_to_bv 64 THIS) (Z_to_bv 64 cap) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 SJ_DPI_SET_CAPACITY) fc None m (seg_rom usegs)).
  Proof.
    intros A k Q. intros until docv. intros HEAP INT AUX QB ST CEIL LO ERR MI Hq CAP GOT THISC HK.
    unfold SJ_DPI_SET_CAPACITY, SJ_OPNEW_STACK, RMALLOC_STACK, SJ_GOT_NOTHROW, SJ_NOTHROW_TAG, impl_cells16 in *.
    assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    pose proof CEIL as CEIL'. unfold OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Spec.Malloc.MCEIL in CEIL; try (pose proof alloc_ceiling_range as CEIL_RANGE__).
    pose proof (LH_block_range _ _ _ _ HEAP INT) as (TH0 & _ & _ & THC & THS). cbn [blk_addr blk_size fst snd] in *.
    unfold OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Spec.Malloc.MCEIL in THC.
    pose proof (munch_refl [(q - 32, q); (THIS, THIS + 96)]%Z m) as MU. pose proof (wmono_refl usegs m) as WM.
    assert (ELX : LX_ERRNO = 980196) by reflexivity. rewrite ELX in ERR.
    pose proof (roundup64_ge cap) as NIX1. pose proof (roundup64_lt cap) as NIX2.
    set (rc := roundup64 cap) in *. change (2^26) with 67108864 in CAP.
    assert (BLB : forall b, In b LB -> blk_addr b + blk_size b <= alloc_ceiling).
    { intros b Hb. pose proof (LH_block_range _ _ _ _ HEAP Hb) as (_ & _ & _ & BC & _).
      unfold OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Spec.Malloc.MCEIL in BC. exact BC. }
    assert (CLI : forall a, 0 <= a < 2^64 -> lx_client LB q [(THIS, THIS + 96)] a -> outside [(q - 32, q); (THIS, THIS + 96)] a).
    { intros a Ha [HX HC]. cbn [rin_ivs fst snd] in HX. cbn [outside]. split; [|split; [lia| exact I]].
      destruct HC as [HC|[(b & Hb & Hr)|HC]]; [lia| | lia]. specialize (BLB b Hb). lia. }
    unfold implM. iprefix.
    step. carve_frame 32%nat ST.
    apply (rw_cells_split_CB usegs _ _ [] 32 junk [] [8;8;8;8]%nat) in FR; [|reflexivity]. cbn [mk_CB_cells app] in FR.

    step. step. step. zstep. zstep. zstep.
    assert (SH : Z.shiftr cap 32 = 0) by (rewrite Z.shiftr_div_pow2 by lia; apply Z.div_small; lia).
    rewrite SH. if_true.

    zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep.
    rewrite (idx_size_eq cap) by lia. fold rc.

    step. step. step.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m1 end.
    assert (HEAP1 : RHEAP s LB m1).
    { eapply LH_frame; [exact HEAP| exact MU| exact WM|].
      constructor; [apply W_ok_stack; cbn; lia|].
      constructor; [eapply (W_ok_block _ (pim, THIS, 96)); [exact INT| cbn; lia| cbn; lia]| constructor]. }
    assert (AUX1 : rauxv_ok m1 B).
    { eapply rauxv_ok_frame; [exact AUX| exact MU| exact WM|].
      constructor; [cbn; unfold RAUXV_CELL; lia|]. constructor; [cbn; unfold RAUXV_CELL; lia| constructor]. }
    ihere. to_implM. eapply implM_bind.
    { eapply (opnew_arr_nt_proof HM) with (B := B) (lo := lo);
        [exact HEAP1| exact AUX1| lia| exact ST| exact CEIL'| unfold SJ_OPNEW_STACK, RMALLOC_STACK; lia| rewrite ELX; exact ERR| exact MI| lia| lia]. }
    cbv beta. intros pix s1' ms1 PO. unfold opnew_postZ in PO.
    destruct PO as (r5 & r6 & r7 & r11 & r12 & r13 & r14 & r15 & r16 & r17 & r28 & r29 & r30 & r31 & m3 & errv3 & IDX & junk1
                    & -> & MI3 & ST3 & ERR3 & AUX3 & HP & FA & SO & BR1 & HEAP3 & BLK1).
    replace (ret_pc (Z_to_bv 64 0x5b1e0)) with (Z_to_bv 64 0x5b1e0) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    apply (rw_cells_agree _ _ _ _ _ (agree_of_heap_pres _ _ _ _ HP)) in FR; [| intros a Ha; left; cbn in Ha; lia].
    apply (rw_cells_agree _ _ _ _ _ (agree_of_heap_pres _ _ _ _ HP)) in THISC;
      [| intros a Ha; right; right; exists (pim, THIS, 96); split; [exact INT| cbn in Ha |- *; lia]].
    assert (PRES3 : lx_pres LB q [(THIS, THIS + 96)] m m3).
    { eapply lx_pres_trans; [eapply lx_pres_of_munch; [exact MU| exact WM| exact CLI]|].
      apply lx_pres_of_heap_pres. eapply rheap_pres_weaken; [exact HP| lia| auto]. }
    clear MU WM HEAP1 AUX1 HP.
    pose proof BR1 as (IX0 & _ & _ & IXC & IXS). unfold OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Spec.Malloc.MCEIL in IXC.
    pose proof (LH_head_disj _ _ _ _ _ _ HEAP3) as DJ.
    pose proof (LH_head_sep _ _ _ _ _ _ _ _ _ HEAP3 INT) as SEP.
    destruct (u32arr_of_block m3 IDX _ junk1 (Z.to_nat (rc + 9)) BLK1 ltac:(lia)) as (ws & ARR & LWS). clear BLK1.
    pose proof (munch_refl [(q - 32, q); (THIS, THIS + 96); (IDX, IDX + 4 * (rc + 9))]%Z m3) as MU. pose proof (wmono_refl usegs m3) as WM.
    assert (CLI3 : forall a, 0 <= a < 2^64 -> lx_client LB q [(THIS, THIS + 96)] a -> outside [(q - 32, q); (THIS, THIS + 96); (IDX, IDX + 4 * (rc + 9))] a).
    { intros a Ha HC. destruct (CLI a Ha HC) as (O1 & O2 & _). cbn [outside]. split; [exact O1|]. split; [exact O2|]. split; [| exact I].
      destruct HC as [HX [HC|[HC|HC]]]; [lia| apply DJ; exact HC| lia]. }
    rewrite ELX in ERR3.
    unfold implM. iprefix.

    zstep. step. rewrite (land3_aligned IDX) by (destruct BR1 as (? & AL16 & _); first [lia| exact AL16]). if_false.
    step. step. step. if_true. step.
    if_cases K1; zify_cond K1; [exfalso; rewrite ?unsigned_lit in K1 by lia; lia|]. clear K1.
    zstep. step. rewrite (land3_aligned IDX) by (destruct BR1 as (? & AL16 & _); first [lia| exact AL16]). if_false.
    pose proof (u32arr_store_ok usegs _ IDX ws 0 (wa (IDX + 0)) ARR ltac:(lia) ltac:(f_equal; lia)) as SOK.
    step.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?mm _ _) _) =>
      pose proof (u32arr_write usegs mm IDX ws 0 (Z_to_bv 64 0) ARR ltac:(lia)) as ARR' end.
    replace (IDX + 4 * 0) with (IDX + 0) in ARR' by lia. store_done.

    step. hstep. step. step. step. step. step. release_frame FR ST3 q. step.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m6 end.
    ihere. to_implM. apply HK. unfold hpost. do 15 eexists. exists m6.
    split; [cbv delta [mkR]; reflexivity|]. split; [assumption|]. split; [exact ST3|].
    split; [exists errv3; rewrite ELX; assumption|].
    split. { eapply rauxv_ok_frame; [exact AUX3| exact MU| exact WM|].
             constructor; [cbn; unfold RAUXV_CELL; lia|]. constructor; [cbn; unfold RAUXV_CELL; lia|].
             constructor; [cbn; unfold RAUXV_CELL; lia| constructor]. }
    split; [congruence|]. split; [congruence|].
    unfold setcap_R, impl_cells16. exists IDX, (upd ws (Z.to_nat 0) (Z_to_bv 64 0)). fold rc.
    split; [reflexivity|].
    split. { eapply LH_frame; [exact HEAP3| exact MU| exact WM|].
             constructor; [apply W_ok_stack; cbn; lia|].
             constructor; [eapply (W_ok_block _ (pim, THIS, 96)); [right; exact INT| cbn; lia| cbn; lia]|].
             constructor; [eapply (W_ok_block _ (pix, IDX, 4 * (rc + 9))); [left; reflexivity| cbn; lia| cbn; lia]| constructor]. }
    split. { eapply lx_pres_trans; [exact PRES3|]. eapply lx_pres_of_munch; [exact MU| exact WM| exact CLI3]. }
    split; [exact THISC|]. split; [assumption|]. split; [rewrite upd_length; exact LWS| exact BR1].
  Qed.
  Lemma setmd_cps : forall {A} (k : bptr -> bptr -> M PState A) (Q : A -> PState -> machine_state -> Prop)
      (ra gp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (s : PState) (LB : list block) (q lo B : Z) (errv : word)
      (THIS : Z) (pim : bptr)
      (vptr nsi : word) (p12 : list byte) (idx nxt : word) (p28 : list byte) (capv md : word) (b48 b49 : byte) (p50 : list byte) (bufv lenv docv : word),
    RHEAP s LB m -> In (pim, THIS, 96) LB -> rauxv_ok m B -> q <= B ->
    stk usegs m lo q -> alloc_ceiling <= lo -> lo <= q - (32 + SJ_OPNEW_STACK) ->
    rw_cells usegs m LX_ERRNO [C4 errv] -> mem_inv usegs m -> 0 <= q < 2^64 ->
    rw_cells usegs m SJ_GOT_NOTHROW [C8 (Z_to_bv 64 SJ_NOTHROW_TAG)] ->
    rw_cells usegs m THIS (impl_cells16 vptr nsi p12 idx nxt p28 capv md b48 b49 p50 (Z_to_bv 64 0) (Z_to_bv 64 0) bufv lenv docv) ->
    (forall poc pia s' ms',
        hpost ra q gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s lo B
              (setmd_R LB q THIS m poc pia vptr nsi p12 idx nxt p28 capv b48 b49 p50 bufv lenv docv) s' ms' ->
        implM usegs (k poc pia) s' Q ms') ->
    implM usegs (mbind (newnt lops 8192) (fun oc => mbind (newnt lops 1024) (fun ia => k oc ia))) s Q
      (MS (mkR ra (Z_to_bv 64 q) gp (Z_to_bv 64 RATP) t0 t1 t2 s0 s1 (Z_to_bv 64 THIS) (Z_to_bv 64 1024) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 SJ_DPI_SET_MAX_DEPTH) fc None m (seg_rom usegs)).
  Proof.
    intros A k Q. intros until docv. intros HEAP INT AUX QB ST CEIL LO ERR MI Hq GOT THISC HK.
    unfold SJ_DPI_SET_MAX_DEPTH, SJ_OPNEW_STACK, RMALLOC_STACK, SJ_GOT_NOTHROW, SJ_NOTHROW_TAG, impl_cells16 in *.
    assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    pose proof CEIL as CEIL'. unfold OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Spec.Malloc.MCEIL in CEIL; try (pose proof alloc_ceiling_range as CEIL_RANGE__).
    pose proof (LH_block_range _ _ _ _ HEAP INT) as (TH0 & _ & _ & THC & THS). cbn [blk_addr blk_size fst snd] in *.
    unfold OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Spec.Malloc.MCEIL in THC.
    pose proof (munch_refl [(q - 32, q); (THIS, THIS + 96)]%Z m) as MU. pose proof (wmono_refl usegs m) as WM.
    assert (ELX : LX_ERRNO = 980196) by reflexivity. rewrite ELX in ERR.
    assert (BLB : forall b, In b LB -> blk_addr b + blk_size b <= alloc_ceiling).
    { intros b Hb. pose proof (LH_block_range _ _ _ _ HEAP Hb) as (_ & _ & _ & BC & _).
      unfold OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Spec.Malloc.MCEIL in BC. exact BC. }
    assert (CLI : forall a, 0 <= a < 2^64 -> lx_client LB q [(THIS, THIS + 96)] a -> outside [(q - 32, q); (THIS, THIS + 96)] a).
    { intros a Ha [HX HC]. cbn [rin_ivs fst snd] in HX. cbn [outside]. split; [|split; [lia| exact I]].
      destruct HC as [HC|[(b & Hb & Hr)|HC]]; [lia| | lia]. specialize (BLB b Hb). lia. }
    unfold implM. iprefix.
    step. carve_frame 32%nat ST.
    apply (rw_cells_split_CB usegs _ _ [] 32 junk [] [8;8;8;8]%nat) in FR; [|reflexivity]. cbn [mk_CB_cells app] in FR.

    step. step. step. zstep. zstep. zstep. if_true.

    zstep. zstep. step. step. step.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m1 end.
    assert (HEAP1 : RHEAP s LB m1).
    { eapply LH_frame; [exact HEAP| exact MU| exact WM|].
      constructor; [apply W_ok_stack; cbn; lia|].
      constructor; [eapply (W_ok_block _ (pim, THIS, 96)); [exact INT| cbn; lia| cbn; lia]| constructor]. }
    assert (AUX1 : rauxv_ok m1 B).
    { eapply rauxv_ok_frame; [exact AUX| exact MU| exact WM|].
      constructor; [cbn; unfold RAUXV_CELL; lia|]. constructor; [cbn; unfold RAUXV_CELL; lia| constructor]. }
    ihere. to_implM. eapply implM_bind.
    { eapply (opnew_arr_nt_proof HM) with (B := B) (lo := lo);
        [exact HEAP1| exact AUX1| lia| exact ST| exact CEIL'| unfold SJ_OPNEW_STACK, RMALLOC_STACK; lia| rewrite ELX; exact ERR| exact MI| lia| lia]. }
    cbv beta. intros poc s1' ms1 PO. unfold opnew_postZ in PO.
    destruct PO as (r5 & r6 & r7 & r11 & r12 & r13 & r14 & r15 & r16 & r17 & r28 & r29 & r30 & r31 & m3 & errv3 & OC & junk1
                    & -> & MI3 & ST3 & ERR3 & AUX3 & HP & FA & SO & BR1 & HEAP3 & BLK1).
    replace (ret_pc (Z_to_bv 64 0x5b298)) with (Z_to_bv 64 0x5b298) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    apply (rw_cells_agree _ _ _ _ _ (agree_of_heap_pres _ _ _ _ HP)) in FR; [| intros a Ha; left; cbn in Ha; lia].
    apply (rw_cells_agree _ _ _ _ _ (agree_of_heap_pres _ _ _ _ HP)) in THISC;
      [| intros a Ha; right; right; exists (pim, THIS, 96); split; [exact INT| cbn in Ha |- *; lia]].
    apply (rw_cells_agree _ _ _ _ _ (agree_of_heap_pres _ _ _ _ HP)) in GOT;
      [| intros a Ha; right; left; cbn in Ha; unfold ralloc_static, RMallocRep.RLIBC, RMallocRep.RCTX, RMallocRep.RERRNO, RMallocRep.RATP, RMallocRep.RSSP_GUARD, RMallocRep.RGOT_SSP; lia].
    assert (PRES3 : lx_pres LB q [(THIS, THIS + 96)] m m3).
    { eapply lx_pres_trans; [eapply lx_pres_of_munch; [exact MU| exact WM| exact CLI]|].
      apply lx_pres_of_heap_pres. eapply rheap_pres_weaken; [exact HP| lia| auto]. }
    clear MU WM HEAP1 AUX1 HP.
    pose proof BR1 as (OC0 & _ & _ & OCC & OCS). unfold OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Spec.Malloc.MCEIL in OCC.
    pose proof (LH_head_sep _ _ _ _ _ _ _ _ _ HEAP3 INT) as SEP1.
    pose proof (munch_refl [(q - 32, q); (THIS, THIS + 96)]%Z m3) as MU. pose proof (wmono_refl usegs m3) as WM.
    rewrite ELX in ERR3.
    unfold implM. iprefix.

    zstep. step. rewrite (land7_aligned OC) by (destruct BR1 as (? & AL16 & _); first [lia| exact AL16]). if_false.

    step. step. step. if_true. step. step. step. step.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m4 end.
    assert (HEAP4 : RHEAP s1' ((poc, OC, 8192) :: LB) m4).
    { eapply LH_frame; [exact HEAP3| exact MU| exact WM|].
      constructor; [apply W_ok_stack; cbn; lia|].
      constructor; [eapply (W_ok_block _ (pim, THIS, 96)); [right; exact INT| cbn; lia| cbn; lia]| constructor]. }
    assert (AUX4 : rauxv_ok m4 B).
    { eapply rauxv_ok_frame; [exact AUX3| exact MU| exact WM|].
      constructor; [cbn; unfold RAUXV_CELL; lia|]. constructor; [cbn; unfold RAUXV_CELL; lia| constructor]. }
    ihere. to_implM. eapply implM_bind.
    { eapply (opnew_arr_nt_proof HM) with (B := B) (lo := lo);
        [exact HEAP4| exact AUX4| lia| exact ST3| exact CEIL'| unfold SJ_OPNEW_STACK, RMALLOC_STACK; lia| rewrite ELX; exact ERR3| exact MI3| lia| lia]. }
    cbv beta. intros pia s2' ms2 PO. unfold opnew_postZ in PO.
    destruct PO as (u5 & u6 & u7 & u11 & u12 & u13 & u14 & u15 & u16 & u17 & u28 & u29 & u30 & u31 & m5 & errv5 & IA & junk2
                    & -> & MI5 & ST5 & ERR5 & AUX5 & HP5 & FA5 & SO5 & BR2 & HEAP5 & BLK2).
    replace (ret_pc (Z_to_bv 64 0x5b2c4)) with (Z_to_bv 64 0x5b2c4) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    apply (rw_cells_agree _ _ _ _ _ (agree_of_heap_pres _ _ _ _ HP5)) in FR; [| intros a Ha; left; cbn in Ha; lia].
    apply (rw_cells_agree _ _ _ _ _ (agree_of_heap_pres _ _ _ _ HP5)) in THISC;
      [| intros a Ha; right; right; exists (pim, THIS, 96); split; [right; exact INT| cbn in Ha |- *; lia]].
    apply (rw_cells_agree _ _ _ _ _ (agree_of_heap_pres _ _ _ _ HP5)) in BLK1;
      [| intros a Ha; right; right; exists (poc, OC, 8192); split; [left; reflexivity| cbn in Ha |- *; lia]].
    assert (PRES5 : lx_pres LB q [(THIS, THIS + 96)] m m5).
    { eapply lx_pres_trans; [exact PRES3|].
      eapply lx_pres_trans; [eapply lx_pres_of_munch; [exact MU| exact WM| exact CLI]|].
      apply lx_pres_of_heap_pres. eapply rheap_pres_weaken; [exact HP5| lia| intros b Hb; right; exact Hb]. }
    clear MU WM HEAP4 AUX4 HP5 PRES3.
    pose proof BR2 as (IA0 & _ & _ & IAC & IAS). unfold OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Spec.Malloc.MCEIL in IAC.
    pose proof (LH_head_sep _ _ _ _ _ _ _ _ _ HEAP5 ltac:(right; exact INT)) as SEP2.
    pose proof (LH_head_sep _ _ _ _ _ _ _ _ _ HEAP5 ltac:(left; reflexivity)) as SEP3.
    pose proof (munch_refl [(q - 32, q); (THIS, THIS + 96)]%Z m5) as MU. pose proof (wmono_refl usegs m5) as WM.
    rewrite ELX in ERR5.
    unfold implM. iprefix.

    step. step. step. if_true. step. zstep. zstep. zstep. zstep. zstep. zstep. zstep.
    replace (0 <? IA) with true by (symmetry; apply Z.ltb_lt; lia).
    replace (0 <? OC) with true by (symmetry; apply Z.ltb_lt; lia).
    change (Z.land (Z.land (0 + - Z.land (Z.b2z true) (Z.b2z true)) 18446744073709551615) 1024) with 1024.
    change (Z.land (Z.land (Z.land (Z.b2z true) (Z.b2z true) + -1) 18446744073709551615) 2) with 0.

    hstep. step. step. step. step. release_frame FR ST5 q. step.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m6 end.
    ihere. to_implM. apply HK. unfold hpost. do 15 eexists. exists m6.
    split; [cbv delta [mkR]; reflexivity|]. split; [assumption|]. split; [exact ST5|].
    split; [exists errv5; rewrite ELX; assumption|].
    split. { eapply rauxv_ok_frame; [exact AUX5| exact MU| exact WM|].
             constructor; [cbn; unfold RAUXV_CELL; lia|]. constructor; [cbn; unfold RAUXV_CELL; lia| constructor]. }
    split; [congruence|]. split; [congruence|].
    unfold setmd_R, impl_cells16. exists OC, IA, junk1, junk2.
    split; [reflexivity|].
    split. { eapply LH_frame; [exact HEAP5| exact MU| exact WM|].
             constructor; [apply W_ok_stack; cbn; lia|].
             constructor; [eapply (W_ok_block _ (pim, THIS, 96)); [right; right; exact INT| cbn; lia| cbn; lia]| constructor]. }
    split. { eapply lx_pres_trans; [exact PRES5|]. eapply lx_pres_of_munch; [exact MU| exact WM| exact CLI]. }
    split; [exact THISC|]. split; [assumption|]. split; [assumption|]. split; [exact BR1| exact BR2].
  Qed.

End Proofs.
End WithCeiling0.
