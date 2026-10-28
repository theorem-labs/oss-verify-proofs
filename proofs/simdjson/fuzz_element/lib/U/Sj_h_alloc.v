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

Definition SJ_DOC_ALLOCATE : Z := 0x3ed28.

Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.

Definition allocate_R (LB : list block) (q DOC cap : Z) (m : mem) (psb ptp : bptr) : word -> PState -> mem -> Prop :=
  fun a0 s' m' => exists SBUF TAPE junk1 junk2,
     a0 = Z_to_bv 64 0
     /\ RHEAP s' ((ptp, TAPE, 8 * roundup64 (cap + 3)) :: (psb, SBUF, roundup64 (5 * (cap / 3) + 64)) :: LB) m'
     /\ lx_pres LB q [(DOC, DOC + 24)] m m'
     /\ rw_cells usegs m' DOC [C8 (Z_to_bv 64 TAPE); C8 (Z_to_bv 64 SBUF); C8 (Z_to_bv 64 cap)]
     /\ rw_cells usegs m' SBUF [CB (Z.to_nat (roundup64 (5 * (cap / 3) + 64))) junk1]
     /\ rw_cells usegs m' TAPE [CB (Z.to_nat (8 * roundup64 (cap + 3))) junk2]
     /\ rblock_range SBUF (roundup64 (5 * (cap / 3) + 64)) /\ rblock_range TAPE (8 * roundup64 (cap + 3)).

Section Proofs.
  Hypothesis HM : rmalloc_stmt.
  Hypothesis HF : rfree_stmt.

  Lemma allocate_cps : forall {A} (k : bptr -> bptr -> M PState A) (Q : A -> PState -> machine_state -> Prop)
      (ra gp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (s : PState) (LB : list block) (q lo B : Z) (errv : word)
      (DOC cap : Z),
    RHEAP s LB m -> rauxv_ok m B -> q <= B ->
    stk usegs m lo q -> alloc_ceiling <= lo -> lo <= q - (32 + SJ_OPNEW_STACK) ->
    rw_cells usegs m LX_ERRNO [C4 errv] -> mem_inv usegs m -> 0 <= q < 2^64 ->
    q <= DOC -> DOC + 24 <= B -> 32 <= cap <= 2^26 ->
    rw_cells usegs m SJ_GOT_NOTHROW [C8 (Z_to_bv 64 SJ_NOTHROW_TAG)] ->
    rw_cells usegs m DOC [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)] ->
    (forall psb ptp s' ms',
        hpost ra q gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s lo B (allocate_R LB q DOC cap m psb ptp) s' ms' ->
        implM usegs (k psb ptp) s' Q ms') ->
    implM usegs (mbind (newnt lops (roundup64 (5 * (cap / 3) + 64))) (fun sb => mbind (newnt lops (8 * roundup64 (cap + 3))) (fun tp => k sb tp))) s Q
      (MS (mkR ra (Z_to_bv 64 q) gp (Z_to_bv 64 RATP) t0 t1 t2 s0 s1 (Z_to_bv 64 DOC) (Z_to_bv 64 cap) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 SJ_DOC_ALLOCATE) fc None m (seg_rom usegs)).
  Proof.
    intros A k Q. intros until cap. intros HEAP AUX QB ST CEIL LO ERR MI Hq QD DB CAP GOT DOCC HK.
    unfold SJ_DOC_ALLOCATE, SJ_OPNEW_STACK, RMALLOC_STACK, SJ_GOT_NOTHROW, SJ_NOTHROW_TAG in *.
    assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    pose proof CEIL as CEIL'. unfold OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Spec.Malloc.MCEIL in CEIL; try (pose proof alloc_ceiling_range as CEIL_RANGE__).
    pose proof (munch_refl [(q - 32, q); (DOC, DOC + 24)]%Z m) as MU. pose proof (wmono_refl usegs m) as WM.
    assert (ELX : LX_ERRNO = 980196) by reflexivity. rewrite ELX in ERR.
    pose proof (roundup64_ge (5 * (cap / 3) + 64)) as NSB1. pose proof (roundup64_lt (5 * (cap / 3) + 64)) as NSB2.
    pose proof (roundup64_ge (cap + 3)) as NTP1. pose proof (roundup64_lt (cap + 3)) as NTP2.
    assert (D3 : 0 <= cap / 3 <= cap) by (split; [apply Z.div_pos; lia| apply Z.div_le_upper_bound; lia]).
    set (nsb := roundup64 (5 * (cap / 3) + 64)) in *. set (ntp := roundup64 (cap + 3)) in *.
    change (2^26) with 67108864 in CAP.
    assert (CLI : forall LBx, (forall b, In b LBx -> blk_addr b + blk_size b <= alloc_ceiling) ->
                  forall a, 0 <= a < 2^64 -> lx_client LBx q [(DOC, DOC + 24)] a -> outside [(q - 32, q); (DOC, DOC + 24)] a).
    { intros LBx HLB a Ha [HX HC]. cbn [rin_ivs fst snd] in HX. cbn [outside]. split; [|split; [lia| exact I]].
      destruct HC as [HC|[(b & Hb & Hr)|HC]]; [lia| | lia]. specialize (HLB b Hb). lia. }
    assert (BLB : forall b, In b LB -> blk_addr b + blk_size b <= alloc_ceiling).
    { intros b Hb. pose proof (LH_block_range _ _ _ _ HEAP Hb) as (_ & _ & _ & BC & _).
      unfold OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Spec.Malloc.MCEIL in BC. exact BC. }
    unfold implM. iprefix.
    step. carve_frame 32%nat ST.
    apply (rw_cells_split_CB usegs _ _ [] 32 junk [] [8;8;8;8]%nat) in FR; [|reflexivity]. cbn [mk_CB_cells app] in FR.
    step. step. step. step. step. step.
    if_cases K0; zify_cond K0; [exfalso; rewrite ?unsigned_lit in K0 by lia; lia|]. clear K0.
    zstep. zstep. zstep.
    assert (SH : Z.shiftr cap 32 = 0) by (rewrite Z.shiftr_div_pow2 by lia; apply Z.div_small; lia).
    rewrite SH. if_true.
    zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep.
    rewrite (sbuf_size_eq cap) by lia. fold nsb.

    step. step. step.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m1 end.
    assert (HEAP1 : RHEAP s LB m1).
    { eapply LH_frame; [exact HEAP| exact MU| exact WM|].
      constructor; [apply W_ok_stack; cbn; lia|]. constructor; [apply W_ok_stack; cbn; lia| constructor]. }
    assert (AUX1 : rauxv_ok m1 B).
    { eapply rauxv_ok_frame; [exact AUX| exact MU| exact WM|].
      constructor; [cbn; unfold RAUXV_CELL; lia|]. constructor; [cbn; unfold RAUXV_CELL; lia| constructor]. }
    ihere. to_implM. eapply implM_bind.
    { eapply (opnew_arr_nt_proof HM) with (B := B) (lo := lo);
        [exact HEAP1| exact AUX1| lia| exact ST| exact CEIL'| unfold SJ_OPNEW_STACK, RMALLOC_STACK; lia| rewrite ELX; exact ERR| exact MI| lia| lia]. }
    cbv beta. intros psb s1' ms1 PO. unfold opnew_postZ in PO.
    destruct PO as (r5 & r6 & r7 & r11 & r12 & r13 & r14 & r15 & r16 & r17 & r28 & r29 & r30 & r31 & m3 & errv3 & SBUF & junk1
                    & -> & MI3 & ST3 & ERR3 & AUX3 & HP & FA & SO & BR1 & HEAP3 & BLK1).
    replace (ret_pc (Z_to_bv 64 0x3edb8)) with (Z_to_bv 64 0x3edb8) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    apply (rw_cells_agree _ _ _ _ _ (agree_of_heap_pres _ _ _ _ HP)) in FR; [| intros a Ha; left; cbn in Ha; lia].
    apply (rw_cells_agree _ _ _ _ _ (agree_of_heap_pres _ _ _ _ HP)) in DOCC; [| intros a Ha; left; cbn in Ha; lia].
    apply (rw_cells_agree _ _ _ _ _ (agree_of_heap_pres _ _ _ _ HP)) in GOT;
      [| intros a Ha; right; left; cbn in Ha; unfold ralloc_static, RMallocRep.RLIBC, RMallocRep.RCTX, RMallocRep.RERRNO, RMallocRep.RATP, RMallocRep.RSSP_GUARD, RMallocRep.RGOT_SSP; lia].
    assert (PRES3 : lx_pres LB q [(DOC, DOC + 24)] m m3).
    { eapply lx_pres_trans; [eapply lx_pres_of_munch; [exact MU| exact WM| apply CLI; exact BLB]|].
      apply lx_pres_of_heap_pres. eapply rheap_pres_weaken; [exact HP| lia| auto]. }
    clear MU WM HEAP1 AUX1 HP.
    pose proof BR1 as (SB0 & _ & _ & SBC & SBS). unfold OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Spec.Malloc.MCEIL in SBC.
    pose proof (munch_refl [(q - 32, q); (DOC, DOC + 24)]%Z m3) as MU. pose proof (wmono_refl usegs m3) as WM.
    rewrite ELX in ERR3.
    unfold implM. iprefix.

    step. step. step. if_true.
    zstep. zstep. zstep. zstep. zstep. zstep.
    rewrite (tape_size_eq cap) by lia. fold ntp.

    step. step. step.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m4 end.
    assert (HEAP4 : RHEAP s1' ((psb, SBUF, nsb) :: LB) m4).
    { eapply LH_frame; [exact HEAP3| exact MU| exact WM|].
      constructor; [apply W_ok_stack; cbn; lia|]. constructor; [apply W_ok_stack; cbn; lia| constructor]. }
    assert (AUX4 : rauxv_ok m4 B).
    { eapply rauxv_ok_frame; [exact AUX3| exact MU| exact WM|].
      constructor; [cbn; unfold RAUXV_CELL; lia|]. constructor; [cbn; unfold RAUXV_CELL; lia| constructor]. }
    ihere. to_implM. eapply implM_bind.
    { eapply (opnew_arr_nt_proof HM) with (B := B) (lo := lo);
        [exact HEAP4| exact AUX4| lia| exact ST3| exact CEIL'| unfold SJ_OPNEW_STACK, RMALLOC_STACK; lia| rewrite ELX; exact ERR3| exact MI3| lia| lia]. }
    cbv beta. intros ptp s2' ms2 PO. unfold opnew_postZ in PO.
    destruct PO as (u5 & u6 & u7 & u11 & u12 & u13 & u14 & u15 & u16 & u17 & u28 & u29 & u30 & u31 & m5 & errv5 & TAPE & junk2
                    & -> & MI5 & ST5 & ERR5 & AUX5 & HP5 & FA5 & SO5 & BR2 & HEAP5 & BLK2).
    replace (ret_pc (Z_to_bv 64 0x3edf0)) with (Z_to_bv 64 0x3edf0) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    apply (rw_cells_agree _ _ _ _ _ (agree_of_heap_pres _ _ _ _ HP5)) in FR; [| intros a Ha; left; cbn in Ha; lia].
    apply (rw_cells_agree _ _ _ _ _ (agree_of_heap_pres _ _ _ _ HP5)) in DOCC; [| intros a Ha; left; cbn in Ha; lia].
    pose proof (rw_cells_bound _ _ _ _ BLK1) as BB1. cbn [cells_size csize Nat.add] in BB1.
    apply (rw_cells_agree _ _ _ _ _ (agree_of_heap_pres _ _ _ _ HP5)) in BLK1;
      [| intros a Ha; right; right; exists (psb, SBUF, nsb); split; [left; reflexivity| cbn in Ha |- *; lia]].
    assert (PRES5 : lx_pres LB q [(DOC, DOC + 24)] m m5).
    { eapply lx_pres_trans; [exact PRES3|].
      eapply lx_pres_trans; [eapply lx_pres_of_munch; [exact MU| exact WM| apply CLI; exact BLB]|].
      apply lx_pres_of_heap_pres. eapply rheap_pres_weaken; [exact HP5| lia| intros b Hb; right; exact Hb]. }
    clear MU WM HEAP4 AUX4 HP5 PRES3.
    pose proof BR2 as (TP0 & _ & _ & TPC & TPS). unfold OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Spec.Malloc.MCEIL in TPC.
    pose proof (munch_refl [(q - 32, q); (DOC, DOC + 24)]%Z m5) as MU. pose proof (wmono_refl usegs m5) as WM.
    rewrite ELX in ERR5.
    unfold implM. iprefix.

    zstep. step. rewrite (land7_aligned TAPE) by (destruct BR2 as (? & AL16 & _); first [lia| exact AL16]). if_false.

    step. step. step. if_true.

    step. step.
    if_cases K1; zify_cond K1; [exfalso; rewrite ?unsigned_lit in K1 by lia; lia|]. clear K1.
    step. step.
    if_cases K2; zify_cond K2; [exfalso; rewrite ?unsigned_lit in K2 by lia; lia|]. clear K2.

    step. step. step. step. step. step. step. step. step. release_frame FR ST5 q. step.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m6 end.
    ihere. to_implM. apply HK. unfold hpost. do 15 eexists. exists m6.
    split; [cbv delta [mkR]; reflexivity|]. split; [assumption|]. split; [exact ST5|].
    split; [exists errv5; rewrite ELX; assumption|].
    split. { eapply rauxv_ok_frame; [exact AUX5| exact MU| exact WM|].
             constructor; [cbn; unfold RAUXV_CELL; lia|]. constructor; [cbn; unfold RAUXV_CELL; lia| constructor]. }
    split; [congruence|]. split; [congruence|].
    unfold allocate_R. exists SBUF, TAPE, junk1, junk2. fold nsb ntp.
    split; [reflexivity|].
    split. { eapply LH_frame; [exact HEAP5| exact MU| exact WM|].
             constructor; [apply W_ok_stack; cbn; lia|]. constructor; [apply W_ok_stack; cbn; lia| constructor]. }
    split. { eapply lx_pres_trans; [exact PRES5|]. eapply lx_pres_of_munch; [exact MU| exact WM| apply CLI; exact BLB]. }
    split; [exact DOCC|]. split; [assumption|]. split; [assumption|]. split; [exact BR1| exact BR2].
  Qed.
End Proofs.
End WithCeiling0.
