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
From OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.Spec Require Import Prelim STree Malloc Monad Stdio SjModel PjModel Target Prog PjImpl.
From OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.U Require Import Layout Exit Printf_wfile Sj_iface Sj_kit Sj_new Sj_h_kit F_memcpy F_memmove_t2 Pj_defs Pj_kit Pj_copy.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
From OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.Lib Require Import Ceiling.
From OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.P Require Import Rnd.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Local Ltac std_lia__ := lia.
Local Ltac lia := first [std_lia__ | try (pose proof alloc_ceiling_range as CEIL_RANGE__); std_lia__].

Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.

Section Proofs.
  Hypothesis HM : rmalloc_stmt.
  Hypothesis HF : rfree_stmt.

  Lemma grow_proof : grow_stmt.
  Proof.
    unfold grow_stmt. intros until z. intros HEAP AUX QB B63 ST CEIL GLO LO ERR MI QSB SBB HL INV OK.
    destruct (SBINV_fuel _ _ _ _ HL INV) as [f EF].
    pose proof (SBINV_cap_pos _ _ _ _ INV) as CAP64.
    unfold PJ_GROW, PJ_GROW_STACK, RMALLOC_STACK, GLOBALS_TOP in *.
    assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    pose proof CEIL as CEIL'. unfold OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.Spec.Malloc.MCEIL in CEIL; try (pose proof alloc_ceiling_range as CEIL_RANGE__).
    destruct st as [buf size cap blk fuel]. unfold sb_grown, sbblocks in *. cbn [sb_buf sb_size sb_cap sb_blk sb_fuel] in *. subst fuel. cbn [Nat.pred].
    destruct INV as (SV & SZ & (bs & BUF) & (ji & INL) & FU & CAPB & BLK). cbn [sb_buf sb_size sb_cap sb_blk sb_fuel] in *.
    apply chain_ok_spec in OK. pose proof (PJ_CAPMAX_bound len HL) as CMB.
    assert (ELX : LX_ERRNO = 977220) by reflexivity. rewrite ELX in ERR.
    assert (BLB : forall a, in_block LB0 a -> a < alloc_ceiling).
    { intros a (b & Hb & Hr). pose proof (LH_block_range _ _ _ _ HEAP ltac:(apply in_or_app; right; exact Hb)) as (_ & _ & _ & BC & _).
      unfold OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.Spec.Malloc.MCEIL in BC. lia. }
    hide BLK. hide BUF. hide INL.
    pose proof (munch_refl [(q - 32, q)]%Z m) as MU. pose proof (wmono_refl usegs m) as WM.
    unfold pj_grow1. unfold implM. iprefix.
    step. carve_frame 32%nat ST.
    apply (rw_cells_split_CB usegs _ _ [] 32 junk [] [8;8;8;8]%nat) in FR; [|reflexivity]. cbn [mk_CB_cells app] in FR.

    do 4 step. step. step. step. step. step.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m1 end.
    assert (HEAP1 : RHEAP s (match blk with Some b => [(b, buf, cap)] | None => [] end ++ LB0) m1).
    { eapply LH_frame; [exact HEAP| exact MU| exact WM|]. constructor; [apply W_ok_stack; cbn; lia| constructor]. }
    assert (AUX1 : rauxv_ok m1 B).
    { eapply rauxv_ok_frame; [exact AUX| exact MU| exact WM|]. constructor; [cbn; unfold RAUXV_CELL; lia| constructor]. }
    assert (PRES1 : lx_pres LB0 q [(SB + 64, SB + 88)] m m1).
    { eapply lx_pres_of_munch; [exact MU| exact WM|].
      intros a Ha [HX HC]. cbn [outside]. split; [| exact I]. destruct HC as [HC|[HC|HC]]; [lia| specialize (BLB a HC); lia| lia]. }
    pose proof (agree_on_of_munch _ _ _ MU WM) as AG01.
    assert (BRNG : blk <> None -> rblock_range buf cap) by (intros NN; unhide BLK; destruct blk; [exact BLK| congruence]).
    assert (BSEP : forall a, buf <= a < buf + cap -> outside [(q - 32, q)] a).
    { intros a Ha. cbn [outside]. split; [| exact I]. unhide BLK. destruct blk as [b|].
      - destruct BLK as (_ & _ & _ & AC & _). lia.
      - destruct BLK as (-> & -> & _). lia. }
    unhide BUF. apply (rw_cells_agree _ _ _ _ _ AG01) in BUF; [| intros a Ha; cbn [cells_size csize Nat.add] in Ha; apply BSEP; lia].
    unhide INL. apply (rw_cells_agree _ _ _ _ _ AG01) in INL; [| intros a Ha; cbn [cells_size csize Nat.add] in Ha; cbn [outside]; split; [lia| exact I]].
    hide BUF. hide INL.
    clear MU WM AG01 BSEP.
    ihere. to_implM.
    eapply implM_bind.
    { eapply (opnew_body HM) with (B := B) (lo := lo);
        [exact HEAP1| exact AUX1| lia| exact ST| exact CEIL'| unfold RMALLOC_STACK; lia| rewrite ELX; exact ERR| assumption| lia| lia]. }
    cbv beta. intros pn s2' ms2 PO. unfold opnew_postZ in PO.
    destruct PO as (r5 & r6 & r7 & r11 & r12 & r13 & r14 & r15 & r16 & r17 & r28 & r29 & r30 & r31 & m2 & errv2 & NEW & jnew
                    & -> & MI2 & ST2 & ERR2 & AUX2 & HP & FA2 & SO2 & BRN & HEAP2 & BLKN).
    replace (ret_pc (Z_to_bv 64 262200)) with (Z_to_bv 64 262200) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    rewrite ELX in ERR2.
    pose proof BRN as (N0 & N16 & _ & NC & NS). unfold OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.Spec.Malloc.MCEIL in NC.
    pose proof (agree_of_heap_pres _ _ _ _ HP) as AG.
    apply (rw_cells_agree _ _ _ _ _ AG) in FR; [| intros a Ha; left; cbn in Ha; lia].
    apply (rw_cells_agree _ _ _ _ _ AG) in SV; [| intros a Ha; left; cbn in Ha; lia].
    unhide INL. apply (rw_cells_agree _ _ _ _ _ AG) in INL; [| intros a Ha; left; cbn in Ha; lia].
    unhide BUF. apply (rw_cells_agree _ _ _ _ _ AG) in BUF.
    2:{ intros a Ha. cbn [cells_size csize Nat.add] in Ha. unhide BLK. destruct blk as [b|].
        - right; right. exists (b, buf, cap). split; [left; reflexivity| cbn [blk_addr blk_size fst snd]; lia].
        - destruct BLK as (-> & -> & _). left. lia. }
    assert (PRES2 : lx_pres LB0 q [(SB + 64, SB + 88)] m m2).
    { eapply lx_pres_trans; [exact PRES1|]. apply lx_pres_of_heap_pres. eapply rheap_pres_weaken; [exact HP| lia| intros b Hb; apply in_or_app; right; exact Hb]. }

    assert (SEPN : forall b, blk = Some b -> NEW + z <= buf \/ buf + cap <= NEW).
    { intros b Hb. eapply (LH_head_sep _ _ _ _ _ _ b buf cap HEAP2). rewrite Hb. left. reflexivity. }
    clear AG PRES1 HEAP1 AUX1.
    assert (ZR : 128 <= z <= 134217728) by lia.
    assert (SBR : forall a, SB <= a < SB + 88 -> alloc_ceiling <= a /\ q <= a) by (intros a Ha; lia).

    assert (FIN : forall m6 st6 (errv6 : word) yra yt0 yt1 yt2 ya0 ya1 ya2 ya3 ya4 ya5 ya6 ya7 yt3 yt4 yt5 yt6,
      RHEAP st6 ((pn, NEW, z) :: LB0) m6 -> rauxv_ok m6 B -> mem_inv usegs m6 -> stk usegs m6 lo (q + -32) ->
      rw_cells usegs m6 977220 [C4 errv6] -> ps_fa st6 = ps_fa s -> ps_so st6 = ps_so s -> lx_pres LB0 q [(SB + 64, SB + 88)] m m6 ->
      rw_cells usegs m6 (SB + 64) [C8 (Z_to_bv 64 buf); C8 (Z_to_bv 64 size); C8 (Z_to_bv 64 cap)] ->
      (exists bn, rw_cells usegs m6 NEW [CB (Z.to_nat z) bn]) ->
      (exists ji6, rw_cells usegs m6 SB [CB 64 ji6]) ->
      rw_cells usegs m6 (q + -32) [C8 s2; C8 s1; C8 s0; C8 ra] ->
      evt usegs (fun ms' => impl usegs (at_node usegs) (mret pn st6)
                                 (epost (fun p => grow_post ra q gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LB0 lo B SB len
                                                            (mkSb buf size cap blk (S f)) z m (fst p) (snd p))) ms')
          (MS (mkR yra (Z_to_bv 64 (q + -32)) gp (Z_to_bv 64 RATP) yt0 yt1 yt2 (Z_to_bv 64 z) (Z_to_bv 64 SB) ya0 ya1 ya2 ya3 ya4 ya5 ya6 ya7
                   (Z_to_bv 64 NEW) s3 s4 s5 s6 s7 s8 s9 s10 s11 yt3 yt4 yt5 yt6)
              F (Z_to_bv 64 262264) fc None m6 (seg_rom usegs))).
    { intros m6 st6 errv6 yra yt0 yt1 yt2 ya0 ya1 ya2 ya3 ya4 ya5 ya6 ya7 yt3 yt4 yt5 yt6 HEAP6 AUX6 MI6 ST6 ERR6 FA6 SO6 PRES6 SV6 (bn & NEWC6) (ji6 & INL6) FR6.
      clear BUF INL FR SV ERR2 ST2 MI2 AUX2 HEAP2 BLKN HP ERR ST MI AUX HEAP.
      hide NEWC6. hide INL6.
      pose proof (munch_refl [(q - 32, q); (SB + 64, SB + 88)]%Z m6) as MU. pose proof (wmono_refl usegs m6) as WM.

      step. step. do 4 step. step. release_frame FR6 ST6 q. step.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m9 end.
      pose proof (agree_on_of_munch _ _ _ MU WM) as AG9.
      unhide NEWC6. apply (rw_cells_agree _ _ _ _ _ AG9) in NEWC6; [| intros a Ha; cbn [cells_size csize Nat.add] in Ha; cbn [outside]; repeat split; lia].
      unhide INL6. apply (rw_cells_agree _ _ _ _ _ AG9) in INL6; [| intros a Ha; cbn [cells_size csize Nat.add] in Ha; cbn [outside]; repeat split; lia].
      ihere. to_implM. apply implM_ret. apply evt_done. unfold grow_post, sb_grown, sbblocks. cbn [sb_buf sb_size sb_cap sb_blk sb_fuel Nat.pred].
      do 15 eexists. exists m9, errv6, NEW.
      split; [cbv delta [mkR]; reflexivity|].
      split; [assumption|]. split; [exact ST6|]. split; [rewrite ELX; exact ERR6|].
      split. { eapply rauxv_ok_frame; [exact AUX6| exact MU| exact WM|]. constructor; [cbn; unfold RAUXV_CELL; lia|]. constructor; [cbn; unfold RAUXV_CELL; lia| constructor]. }
      split; [exact FA6|]. split; [exact SO6|].
      split. { cbn [app]. eapply LH_frame; [exact HEAP6| exact MU| exact WM|]. constructor; [apply W_ok_stack; cbn; lia|]. constructor; [apply W_ok_stack; cbn; lia| constructor]. }
      split.
      2:{ eapply lx_pres_trans; [exact PRES6|]. eapply lx_pres_of_munch; [exact MU| exact WM|].
          intros a Ha [HX HC]. cbn [rin_ivs fst snd] in HX. cbn [outside]. split; [| split; [clear - HX; lia| exact I]].
          destruct HC as [HC|[HC|HC]]; [lia| specialize (BLB a HC); lia| lia]. }
      unfold SBINV. cbn [sb_buf sb_size sb_cap sb_blk sb_fuel].
      split; [exact SV6|]. split; [lia|]. split; [exists bn; exact NEWC6|]. split; [exists ji6; exact INL6|].
      split; [lia|]. split; [| exact BRN].
      unfold sb_k in *. cbn [sb_fuel] in *. split; [| lia].
      replace (Z.of_nat PJ_FUEL - Z.of_nat f) with (Z.succ (Z.of_nat PJ_FUEL - Z.of_nat (S f))) by lia.
      rewrite Z.pow_succ_r by lia. lia. }

    assert (MID : forall m3 xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6,
      RHEAP s2' ((pn, NEW, z) :: match blk with Some b => [(b, buf, cap)] | None => [] end ++ LB0) m3 -> rauxv_ok m3 B -> mem_inv usegs m3 ->
      stk usegs m3 lo (q + -32) -> rw_cells usegs m3 977220 [C4 errv2] -> lx_pres LB0 q [(SB + 64, SB + 88)] m m3 ->
      rw_cells usegs m3 (SB + 64) [C8 (Z_to_bv 64 buf); C8 (Z_to_bv 64 size); C8 (Z_to_bv 64 cap)] ->
      (exists bn, rw_cells usegs m3 NEW [CB (Z.to_nat z) bn]) ->
      (exists ji3, rw_cells usegs m3 SB [CB 64 ji3]) ->
      rw_cells usegs m3 (q + -32) [C8 s2; C8 s1; C8 s0; C8 ra] ->
      evt usegs (fun ms' => impl usegs (at_node usegs) (mbind (del_opt lops blk) (fun _ => mret pn) s2')
                                 (epost (fun p => grow_post ra q gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LB0 lo B SB len
                                                            (mkSb buf size cap blk (S f)) z m (fst p) (snd p))) ms')
          (MS (mkR xra (Z_to_bv 64 (q + -32)) gp (Z_to_bv 64 RATP) xt0 xt1 xt2 (Z_to_bv 64 z) (Z_to_bv 64 SB) xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7
                   (Z_to_bv 64 NEW) s3 s4 s5 s6 s7 s8 s9 s10 s11 xt3 xt4 xt5 xt6)
              F (Z_to_bv 64 262248) fc None m3 (seg_rom usegs))).
    { intros m3 xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6 HEAP3 AUX3 MI3 ST3 ERR3 PRES3 SV3 NEWC3 INL3 FR3.
      clear BUF INL FR SV ERR2 ST2 MI2 AUX2 HEAP2 BLKN HP ERR ST MI AUX HEAP.

      step. step. unhide BLK. destruct blk as [b|].
      +
        destruct BLK as (A0 & A16 & _ & AC & AS).
        if_cases K; zify_cond K; [exfalso; rewrite ?unsigned_lit in K by lia; lia| clear K].
        step. if_cases K; zify_cond K; [exfalso; rewrite ?unsigned_lit in K by lia; lia| clear K].

        step.
        pose proof (RHEAP_pull _ [(pn, NEW, z)] (b, buf, cap) LB0 _ HEAP3) as HEAP3'. cbn [app] in HEAP3'.
        assert (ND : List.NoDup (map blk_id ((b, buf, cap) :: (pn, NEW, z) :: LB0))) by (eapply LH_nodup; exact HEAP3').
        ihere. to_implM. eapply implM_bind.
        { eapply (opdel_arr_proof HF) with (B := B) (lo := lo) (A := buf) (n := cap);
            [exact HEAP3'| left; reflexivity| exact AUX3| lia| exact ST3| exact CEIL'| unfold RFREE_STACK; lia| rewrite ELX; exact ERR3| exact MI3| lia]. }
        cbv beta. intros [] s6' ms6 PO. unfold free_postZ in PO.
        destruct PO as (w5 & w6 & w7 & w10 & w11 & w12 & w13 & w14 & w15 & w16 & w17 & w28 & w29 & w30 & w31 & m6
                        & -> & MI6 & ST6 & ERR6 & AUX6 & HP6 & FA6 & SO6 & HEAP6).
        rewrite (lb_remove_hd _ _ _ _ ND) in HP6, HEAP6. rewrite ELX in ERR6.
        replace (ret_pc (Z_to_bv 64 262264)) with (Z_to_bv 64 262264) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
        pose proof (agree_of_heap_pres _ _ _ _ HP6) as AG6.
        destruct NEWC3 as (bn & NEWC3). destruct INL3 as (ji3 & INL3).
        unfold implM. iprefix.
        apply FIN with (errv6 := errv2); try assumption.
        * congruence.
        * congruence.
        * eapply lx_pres_trans; [exact PRES3|]. apply lx_pres_of_heap_pres. eapply rheap_pres_weaken; [exact HP6| lia| intros b0 Hb0; right; exact Hb0].
        * eapply rw_cells_agree; [exact AG6| eassumption| intros a Ha; left; cbn in Ha; lia].
        * exists bn. eapply rw_cells_agree; [exact AG6| eassumption|]. intros a Ha. cbn [cells_size csize Nat.add] in Ha. right; right.
          exists (pn, NEW, z). split; [left; reflexivity| cbn [blk_addr blk_size fst snd]; lia].
        * exists ji3. eapply rw_cells_agree; [exact AG6| eassumption| intros a Ha; left; cbn in Ha; lia].
        * eapply rw_cells_agree; [exact AG6| exact FR3| intros a Ha; left; cbn in Ha; lia].
      +
        destruct BLK as (EB & EC & _). subst buf cap. if_true.
        ihere. to_implM. apply implM_retb. unfold implM. iprefix. cbn [app] in HEAP3.
        apply FIN with (errv6 := errv2); try assumption; try reflexivity. }
    hide INL. hide BLK.
    unfold implM. iprefix.
    assert (BHI : 0 < buf /\ buf + cap < 2^63).
    { unhide BLK. destruct blk as [b|]; [destruct BLK as (A0 & A16 & _ & AC & AS); lia| destruct BLK as (-> & -> & _); lia]. }
    assert (OSB : buf + size <= lo \/ q + -32 <= buf).
    { unhide BLK. destruct blk as [b|]; [destruct BLK as (A0 & A16 & _ & AC & AS); lia| destruct BLK as (-> & -> & _); lia]. }
    assert (SEP : buf + size <= NEW \/ NEW + size <= buf).
    { unhide BLK. destruct blk as [b|]; [specialize (SEPN b eq_refl); lia| destruct BLK as (-> & -> & _); lia]. }

    step. step. zstep. gtrap.

    step. zstep. zstep. zstep. unz. change (Z.lxor 1 0) with 1%Z. zstep. if_false.

    step. step. step.
    try (replace (size + buf)%Z with (buf + size)%Z by lia).
    destruct (rw_cells_CB_at _ _ _ _ size BUF ltac:(lia)) as [SRC _].
    apply rw_cells_bytes_at in SRC. cbn [cells_bytes cbytes] in SRC. rewrite app_nil_r in SRC.
    destruct (rw_cells_CB_at _ _ _ _ size BLKN ltac:(lia)) as [NPRE NREST].
    assert (LBS : length bs = Z.to_nat cap) by (destruct BUF as [[[HLn _] _] _]; exact HLn).
    clear BUF BLKN. hide NREST.
    eapply evt_cut.
    { eapply (copy_spec PJ_COPY_G) with (lo := lo) (Dst := NEW) (Src := buf) (N := size) (src := firstn (Z.to_nat size) bs) (junk := firstn (Z.to_nat size) jnew);
        [left; reflexivity| exact ST2| unfold PJ_COPY_STACK; lia| unfold GLOBALS_TOP; lia| lia| exact MI2
        | exact SRC| rewrite firstn_length; lia| exact NPRE| lia| lia| lia| lia| lia| lia| lia| lia]. }
    intros ms' PO. unfold copy_post in PO.
    destruct PO as (u5 & u6 & u7 & u11 & u12 & u13 & u14 & u15 & u16 & u17 & u28 & u29 & u30 & u31 & m4 & -> & MU4 & WM4 & MI4 & ST4 & NPRE4 & SRC4).
    replace (ret_pc (Z_to_bv 64 262248)) with (Z_to_bv 64 262248) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    pose proof (agree_on_of_munch _ _ _ MU4 WM4) as AG4.
    unhide NREST. apply (rw_cells_agree _ _ _ _ _ AG4) in NREST; [| intros a Ha; cbn [cells_size csize Nat.add] in Ha; cbn [outside]; repeat split; lia].
    unhide INL. apply (rw_cells_agree _ _ _ _ _ AG4) in INL; [| intros a Ha; cbn [cells_size csize Nat.add] in Ha; cbn [outside]; repeat split; lia].
    apply (rw_cells_agree _ _ _ _ _ AG4) in FR; [| intros a Ha; cbn in Ha; cbn [outside]; repeat split; lia].
    apply (rw_cells_agree _ _ _ _ _ AG4) in SV; [| intros a Ha; cbn in Ha; cbn [outside]; repeat split; lia].
    apply (rw_cells_agree _ _ _ _ _ AG4) in ERR2; [| intros a Ha; cbn in Ha; cbn [outside]; repeat split; lia].
    apply MID; try assumption.
    + eapply LH_frame; [exact HEAP2| exact MU4| exact WM4|]. constructor; [apply W_ok_stack; cbn; lia| constructor; [| constructor]].
      eapply (W_ok_block _ (pn, NEW, z)); [left; reflexivity| cbn; lia| cbn; lia].
    + eapply rauxv_ok_frame; [exact AUX2| exact MU4| exact WM4|]. constructor; [cbn; unfold RAUXV_CELL; lia| constructor; [cbn; unfold RAUXV_CELL; lia| constructor]].
    + eapply lx_pres_trans; [exact PRES2|]. eapply lx_pres_of_munch; [exact MU4| exact WM4|].
      pose proof (LH_head_disj _ _ _ _ _ _ HEAP2) as DJN.
      intros a Ha [HX HC]. cbn [outside]. split; [| split; [| exact I]].
      * destruct HC as [HC|[HC|HC]]; [lia| specialize (BLB a HC); lia| lia].
      * destruct HC as [HC|[HC|HC]]; [lia| | lia].
        intros Hs. apply (DJN a); [| lia]. eapply in_block_incl; [| exact HC]. intros b0 Hb0. apply in_or_app. right. exact Hb0.
    + pose proof (rw_cells_CB_join2 _ _ _ _ _ _ _ NPRE4 NREST) as J.
      assert (EJ : NEW + size = NEW + Z.of_nat (Z.to_nat size)) by lia. specialize (J EJ).
      replace (Z.to_nat size + (Z.to_nat z - Z.to_nat size))%nat with (Z.to_nat z) in J by lia.
      eexists. exact J.
    + exists ji. exact INL.
  Qed.

End Proofs.
End WithCeiling0.
