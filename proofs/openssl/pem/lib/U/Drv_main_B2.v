(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation Strings.String.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP MonadX.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Malloc Require Import MallocBlocks Malloc_iface.
From OssFuzzTheorems.Proofs.openssl.pem.lib.MallocU Require Import RMallocRep RMallocTree RMalloc_iface RMalloc_ifaceP.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Spec Require Import Prelim STree Malloc Monad Stdio Harness Target Driver Prog StrFun.
From OssFuzzTheorems.Proofs.openssl.pem.lib.P Require Import Str_tac Startup_glue InitMem. From OssFuzzTheorems.Proofs.openssl.pem.lib.U Require Import Layout Exit Startup Stdio_iface Printf_lib Printf_stdio_iface Fz_iface Driver_iface Drv_kit Drv_facts Drv_main_defs Drv_main_A Drv_main_B.
From OssFuzzTheorems.Proofs.openssl.pem.lib.U Require Import Exit_walk.   (* [comment removed for export] *)
From OssFuzzTheorems.Proofs.openssl.pem.lib.U Require Drv_sys F_memcpy. From OssFuzzTheorems.Proofs.openssl.pem.lib.P Require Str_cpy.
From OssFuzzTheorems.openssl.pem.images Require Import Ubsan.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Open Scope mspec_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Notation usegs := Image.usegs.
Notation mem := (word -> option byte).
Notation wz := MallocRep.wz.
Notation pph := Ubsan.M.phdrs.
Ltac rpc := apply ret_pc_even; [lia| reflexivity].

From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import Ceiling.
From OssFuzzTheorems.Proofs.openssl.pem.lib.P Require Import Rnd.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Malloc Require Import CeilWin.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac std_lia__ := lia.
Local Ltac lia := first [std_lia__ | try (pose proof ceil_window_holds as CEIL_RANGE__); unfold ceil_window in *; std_lia__].
Local Ltac std_nia__ := nia.
Local Ltac nia := first [std_nia__ | try (pose proof ceil_window_holds as CEIL_RANGE__); unfold ceil_window in *; std_nia__].
Local Ltac OssFuzzTheorems.Proofs.openssl.pem.lib.Lib.ZBridge.flia ::= first [ assumption | OssFuzzTheorems.Proofs.openssl.pem.lib.Lib.ZBridge.slim; lia | lia ].
Local Ltac OssFuzzTheorems.Proofs.openssl.pem.lib.Lib.ZBridge.mlia ::= Z.div_mod_to_equations; lia.
Local Ltac OssFuzzTheorems.Proofs.openssl.pem.lib.Lib.Step.slia ::= first [ exact I | lia | split; [lia|exact I] ].
Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.
Section B2.
  Variable CS : cli_sig.
  Variables (sp0 : word) (argv envp : list (list byte)) (uid : word) (arg0 arg1 : list byte) (TID : Z) (PAD : list byte) (S4 S5 S6 S7 S8 S9 S10 S11 : word).
  Hypothesis VSP : valid_sp sp0.
  Hypothesis CEIL : ceil_ok sp0.
  Hypothesis VARGV : valid_argv argv.
  Hypothesis VENVP : valid_envp envp.
  Hypothesis EARGV : argv = [arg0; arg1].
  Hypothesis HT : 0 < TID < 4194304.
  Hypothesis MALLOC : rmalloc_stmt.
  Hypothesis FREE : rfree_stmt.
  Hypothesis FPR : @fprintf_diag_stmt PState.
  Hypothesis FWX : fwritex_stderr_stmt.
  Hypothesis SWF : stdio_write_flush_stmt.
  Hypothesis FWR : @fwrite_diag_stmt PState.

  Notation usp0 := (bv_unsigned sp0).
  Notation LO' := (LO sp0).
  Notation BASE' := (BASE sp0 argv envp uid TID).
  Notation FRAME' mm := (MFRAME sp0 argv mm PAD S7 S6 S5 S4).
  Notation RDHEAD' := (RDHEAD CS sp0 argv envp uid TID PAD S4 S5 S6 S7 S8 S9 S10 S11).
  Notation RDBRK' := (RDBRK CS sp0 argv envp uid TID PAD S4 S5 S6 S7 S8 S9 S10 S11).
  Notation POSTBODY' := (POSTBODY CS sp0 argv envp uid TID PAD S4 S5 S6 S7 S8 S9 S10 S11).
  Ltac hyps := first [exact VSP | exact CEIL | exact VARGV | exact VENVP | exact EARGV | exact HT | exact MALLOC | exact FREE | exact FPR | exact FWX | exact SWF | exact FWR].

  Notation GST pc x1 t0 t1 t2 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 t3 t4 t5 t6 F fc mm :=
    (MS (mkR x1 (Z_to_bv 64 (usp0 + -128)) (Z_to_bv 64 0x10800) (Z_to_bv 64 RATP) t0 t1 t2 (Z_to_bv 64 2) x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 S8 S9 S10 S11 t3 t4 t5 t6)
        F (Z_to_bv 64 pc) fc None mm (seg_rom usegs)).

  (* [comment removed for export] *)
  Lemma rd_body : forall (fd P1v : Z) (st : rd_st) (s : PState) ms,
    3 <= fd < 2^32 -> nth_error (argv_ptrs sp0 argv envp) 1 = Some (Z_to_bv 64 P1v) ->
    RDHEAD' fd P1v st s ms ->
    implM usegs (read_loop_body io raw_malloc raw_free ustage fd (map bv_unsigned arg1) st) s (POSTBODY' fd P1v) ms.
  Proof.
    intros fd P1v st s ms FD HP1 RI.
    destruct RI as (x1 & t0 & t1 & t2 & a0 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & F & fc & mm & A & DATA & junk & errv
                    & -> & HC & BU & SG & FR & BA & EX & ERR & FRM).
    pose proof (sp_facts sp0 VSP CEIL) as SF. unfold LO in SF. try (pose proof alloc_ceiling_range as CEIL_RANGE).
    assert (LENZ : zlength (rd_content st) = Z.of_nat (length DATA)) by (rewrite HC; unfold zlength; rewrite length_map; reflexivity).
    pose proof BU as (P0 & HA & BLK & [CAPR [k [K0' CAPK]]] & LENR & BR). unfold MAX_INPUT in CAPR.
    rewrite read_loop_body_eq. unfold rd_grow_part. rewrite LENZ.
    pose proof BA as (ST & MI & ES & AUX & SSP & LXS & IMG). unfold LO in ST. unfold RMallocRep.RERRNO in ERR. unfold MFRAME in FR.
    pose proof BR as (BR1 & BR2 & BR3 & BR4 & BR5). try (pose proof alloc_ceiling_range as CEIL_RANGE).
    unfold implM. iprefix.
    zstep. if_cases K00; zify_cond K00.
    2:{ (* [comment removed for export] *)
      replace (Z.of_nat (length DATA) =? rd_cap st) with false by (symmetry; apply Z.eqb_neq; lia).
      zstep. zstep. apply evt_done.
      lazymatch goal with |- impl _ _ (?tm _) _ ?msx => change (implM usegs tm s (POSTBODY' fd P1v) msx) end.
      apply implM_retb. cbv iota beta.
      rewrite <- LENZ. eapply (rd_read CS sp0 argv envp uid arg0 arg1 TID PAD S4 S5 S6 S7 S8 S9 S10 S11);
        first [hyps | exact FD | exact HP1 | exact HC | exact BU | exact SG | exact BA | exact EX | unfold MFRAME; exact FR | unfold RMallocRep.RERRNO; exact ERR | exact FRM | lia]. }
    (* [comment removed for export] *)
    replace (Z.of_nat (length DATA) =? rd_cap st) with true by (symmetry; apply Z.eqb_eq; lia).
    zstep. zstep. if_cases K0; zify_cond K0.
    { (* [comment removed for export] *)
      assert (GE : 67108864 <= rd_cap st).
      { destruct (Z.lt_ge_cases (rd_cap st) 67108864) as [L|G]; [| exact G]. exfalso. apply K0.
        apply (proj2 (shiftr26_zero_iff (Z.of_nat (length DATA)) ltac:(lia))). lia. }
      replace (MAX_INPUT <=? rd_cap st) with true by (symmetry; apply Z.leb_le; unfold MAX_INPUT; lia).
      pose proof LXS as (G1 & G2 & _). unfold LX_GOT_STDERR, LX_STDERR_PTR, LX_STDERR_FILE in G1, G2. cbv delta [MallocRep.wz] in G1, G2.
      zstep. zstep. zstep. zstep. zstep. zstep. apply evt_done.
      lazymatch goal with |- impl _ _ (?tm _) _ ?msx => change (implM usegs tm s (POSTBODY' fd P1v) msx) end.
      apply implM_bind_assoc. cbn [io_diag io io_S].
      eapply (fprintf_exit CS sp0 argv envp uid TID S8 S9 S10 S11 VSP CEIL HT FPR FWX SWF DTooBig);
        [| exact BA| exact P0| exact EX| exact FRM| intros ms'' AE; apply implM_retb; cbv beta iota; apply implM_ret; apply evt_done; exact AE].
      cbn [diag_args]. split; [reflexivity|]. rewrite unsigned_lit by lia. reflexivity. }
    (* [comment removed for export] *)
    assert (LTM : rd_cap st < 67108864).
    { rewrite <- K00. apply (proj1 (shiftr26_zero_iff (Z.of_nat (length DATA)) ltac:(lia))). exact K0. }
    replace (MAX_INPUT <=? rd_cap st) with false by (symmetry; apply Z.leb_gt; unfold MAX_INPUT; lia).
    zstep. zstep. zstep. apply evt_done.
    lazymatch goal with |- impl _ _ (?tm _) _ ?msx => change (implM usegs tm s (POSTBODY' fd P1v) msx) end.
    apply implM_bind_assoc.
    replace (Z.shiftl (Z.of_nat (length DATA)) 1) with (rd_cap st * 2) by (rewrite Z.shiftl_mul_pow2 by lia; lia).
    eapply implM_bind.
    { unfold rmalloc_stmt in MALLOC.
      eapply MALLOC with (lo := usp0 - 8388608) (B := usp0); try reflexivity; unfold RATP; rewrite ?(unsigned_lit RMallocRep.RATP) by (unfold RMallocRep.RATP; lia); rewrite ?(unsigned_lit (usp0 + -128)) by lia;
        unfold RMallocRep.RATP; cbn [Z.add];
        first [ exact P0 | exact AUX | exact ST | exact ERR | exact MI | unfold RMALLOC_STACK; lia | lia ]. }
    cbv beta. intros r s1 ms1 PO.
    destruct PO as (u0 & u1 & u2 & ra0 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & m1 & errv1 & -> & MI1 & ST1 & ERR1 & AUX1 & HPR & FAE & SOE & RR).
    unfold RATP in ERR1. rewrite ?(unsigned_lit RMallocRep.RATP) in ERR1 by (unfold RMallocRep.RATP; lia). unfold RMallocRep.RATP in ERR1. cbn [Z.add] in ERR1.
    rewrite ?(unsigned_lit (usp0 + -128)) in ST1 by lia. rewrite ?(unsigned_lit (usp0 + -128)) in HPR by lia.
    replace (ret_pc (Z_to_bv 64 0xe1674)) with (Z_to_bv 64 0xe1674) by (symmetry; rpc).
    assert (FR1 : FRAME' m1) by (unfold MFRAME; eapply rheap_pres_rw_cells; [exact HPR| exact FR| left; cbn; lia]). unfold MFRAME in FR1.
    assert (SG1 : STG m1) by (eapply (STG_heap sp0); [exact HPR| exact SG]).
    assert (BLK1 : rw_cells usegs m1 A [CB (length DATA) DATA; CB (Z.to_nat (rd_cap st - Z.of_nat (length DATA))) junk]).
    { eapply rheap_pres_rw_cells; [exact HPR| exact BLK|]. right; right. exists (rd_buf st, A, rd_cap st). split; [left; reflexivity|]. cbn [blk_addr blk_size fst snd cells_size csize Nat.add]. lia. }
    destruct r as [nb|].
    2:{ (* [comment removed for export] *)
        destruct RR as [-> HEAP1].
        assert (BA1 : BASE' m1) by (eapply (BASE_heap sp0 argv envp uid TID); [exact BA| exact HPR| exact MI1| unfold LO; exact ST1| exact AUX1| exact HEAP1]).
        assert (EX1 : EXTRA CS m1 s1) by (eapply (EXTRA_heap CS sp0); [exact HPR| exact SOE| exact EX]).
        clear FR BLK ST MI AUX IMG ES SSP ERR.
        pose proof BA1 as (ST & MI & ES & AUX & SSP & LXS' & IMG). unfold LO in ST.
        pose proof LXS' as (G1 & G2 & _). unfold LX_GOT_STDERR, LX_STDERR_PTR, LX_STDERR_FILE in G1, G2. cbv delta [MallocRep.wz] in G1, G2.
        unfold implM. iprefix. zstep. if_cases K1; zify_cond K1; [| exfalso; rewrite ?unsigned_lit in K1 by lia; lia].
        zstep. zstep. zstep. zstep. zstep. zstep. zstep. apply evt_done.
        lazymatch goal with |- impl _ _ (?tm _) _ ?msx => change (implM usegs tm s1 (POSTBODY' fd P1v) msx) end.
        apply implM_bind_assoc. cbn [io_diag io io_S].
        eapply (fwrite_exit CS sp0 argv envp uid TID S8 S9 S10 S11 VSP CEIL HT FWR);
          [exact BA1| exact HEAP1| exact EX1| intros ms'' AE; apply implM_retb; cbv beta iota; apply implM_ret; apply evt_done; exact AE]. }
    (* [comment removed for export] *)
    destruct RR as (A' & junk' & -> & BR' & HEAP1 & NBLK & HEXP).
    specialize (HEXP ltac:(apply raddr_exposed_big; unfold MMAP_THRESHOLD; lia)).
    assert (BA1 : BASE' m1) by (eapply (BASE_heap sp0 argv envp uid TID); [exact BA| exact HPR| exact MI1| unfold LO; exact ST1| exact AUX1| exact HEAP1]).
    assert (EX1 : EXTRA CS m1 s1) by (eapply (EXTRA_heap CS sp0); [exact HPR| exact SOE| exact EX]).
    clear FR BLK ST MI AUX IMG ES SSP ERR SG LXS.
    pose proof BR' as (BQ1 & BQ2 & BQ3 & BQ4 & BQ5).
    pose proof (RHEAP_blocks_nodup_proof _ _ _ HEAP1) as ND.
    assert (DISJ : A' + rd_cap st * 2 <= A \/ A + rd_cap st <= A').
    { pose proof (RHEAP_blocks_disjoint_proof _ _ _ (nb, A', rd_cap st * 2) (rd_buf st, A, rd_cap st) HEAP1 ltac:(left; reflexivity) ltac:(right; left; reflexivity)) as D.
      cbn [blk_id blk_addr blk_size fst snd] in D. apply D. cbn [map blk_id fst] in ND. inversion ND as [|x l NI ND']; subst. intros E. apply NI. rewrite E. left. reflexivity. }
    apply implM_bind_assoc.
    pose proof BA1 as (ST & MI & ES & AUX & SSP & LXS & IMG). unfold LO in ST.
    unfold implM. iprefix. zstep. if_cases K1; zify_cond K1; [exfalso; rewrite ?unsigned_lit in K1 by lia; lia|]. clear K1.
    zstep. zstep. if_cases K2; zify_cond K2; [exfalso; lia|]. clear K2.
    zstep. zstep. zstep. zstep.
    (* [comment removed for export] *)
    apply (rw_cells_split_CB _ _ _ [] _ _ [] [length DATA; Z.to_nat (rd_cap st * 2) - length DATA]%nat) in NBLK; [| cbn; lia]. cbn [mk_CB_cells app] in NBLK.
    apply (proj1 (rw_cells_app _ _ _ [CB (length DATA) (firstn (length DATA) junk')] _)) in NBLK. destruct NBLK as [NB1 NB2]. cbn [cells_size csize Nat.add] in NB2.
    pose proof BLK1 as SRC. apply (proj1 (rw_cells_app _ _ _ [CB (length DATA) DATA] _)) in SRC. destruct SRC as [SRC _].
    pose proof (rw_cells_bytes_at _ _ _ _ SRC) as SRCB. cbn [cells_bytes cbytes app] in SRCB. rewrite app_nil_r in SRCB. clear SRC.
    eapply evt_cut.
    { eapply (F_memcpy.memcpy_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m1 DATA (firstn (length DATA) junk'));
        rewrite ?unsigned_lit by lia;
        [exact SRCB| lia| replace (Z.to_nat (Z.of_nat (length DATA))) with (length DATA) by lia; exact NB1| lia| exact MI]. }
    cbv beta. intros ms' PO.
    destruct PO as (v0 & v1 & v2 & c1 & c2 & c3 & c4 & c5 & c6 & c7 & v3 & v4 & v5 & v6 & m2 & -> & MUc & WMc & MI2 & NB1' & _).
    rewrite !unsigned_lit in MUc by lia. rewrite !unsigned_lit in NB1' by lia.
    replace (ret_pc (Z_to_bv 64 0xe1694)) with (Z_to_bv 64 0xe1694) by (symmetry; rpc).
    assert (WOKW : Forall (WOK sp0) [(A', A' + Z.of_nat (length DATA))]).
    { unfold WOK. constructor; [cbn [fst snd]; lia| constructor]. }
    assert (P2 : RHEAP s1 [(nb, A', rd_cap st * 2); (rd_buf st, A, rd_cap st)] m2).
    { eapply (RHEAP_munchW sp0 VSP CEIL); [apply WOK_WOKE; exact WOKW| exact MUc| exact WMc| | exact HEAP1].
      intros iv [<-|[]]. cbn [fst snd]. intros _ _. exists (nb, A', rd_cap st * 2). split; [left; reflexivity|]. cbn [fst snd blk_addr blk_size]. lia. }
    assert (BA2 : BASE' m2) by (eapply (BASE_munch sp0 argv envp uid TID VSP CEIL); [exact BA1| apply WOK_WOKE; exact WOKW| exact MUc| exact WMc| exact MI2| unfold LO; eapply stk_agree; [eapply agree_on_of_munch; [exact MUc| exact WMc]| exact ST| intros a Ha; cbn; lia]]).
    assert (EX2 : EXTRA CS m2 s1) by (eapply (EXTRA_munch CS sp0 VSP CEIL); [exact WOKW| exact MUc| exact WMc| reflexivity| exact EX1]).
    assert (FR2 : rw_cells usegs m2 (usp0 + -128) [CB 8 PAD; C8 S7; C8 S6; C8 S5; C8 S4; C8 (wz (envp_addr sp0 argv)); C8 (wz RMAIN); C8 (wz (argc argv)); C8 (wz (usp0 + 8)); C8 (wz RMAIN_RET)]).
    { eapply rw_cells_agree; [eapply agree_on_of_munch; [exact MUc| exact WMc]| exact FR1|]. intros a Ha. cbn in Ha |- *. lia. }
    assert (SG2 : STG m2) by (eapply STG_munch; [exact MUc| exact WMc| intros a Ha; cbn; lia| exact SG1]).
    assert (NB2' : rw_cells usegs m2 (A' + Z.of_nat (length DATA + 0)) [CB (Z.to_nat (rd_cap st * 2) - length DATA) (take (Z.to_nat (rd_cap st * 2) - length DATA) (drop (length DATA) junk'))]).
    { eapply rw_cells_agree; [eapply agree_on_of_munch; [exact MUc| exact WMc]| exact NB2|]. intros a Ha. cbn in Ha |- *. lia. }
    assert (ERR2 : rw_cells usegs m2 3344580 [C4 errv1]).
    { eapply rw_cells_agree; [eapply agree_on_of_munch; [exact MUc| exact WMc]| exact ERR1|]. intros a Ha. cbn in Ha |- *. lia. }
    clear MUc WMc BA1 EX1 ST MI ES AUX SSP LXS IMG WOKW NB2 ERR1 SG1.
    pose proof BA2 as (ST & MI & ES & AUX & SSP & LXS & IMG). unfold LO in ST.
    (* [comment removed for export] *)
    zstep. zstep. apply evt_done.
    lazymatch goal with |- impl _ _ (?tm _) _ ?msx => change (implM usegs tm s1 (POSTBODY' fd P1v) msx) end.
    eapply implM_bind.
    { apply implM_leaves. unfold rfree_stmt in FREE.
      eapply FREE with (lo := usp0 - 8388608) (B := usp0) (p := rd_buf st) (A := A) (n := rd_cap st); try reflexivity; unfold RATP;
        rewrite ?(unsigned_lit RMallocRep.RATP) by (unfold RMallocRep.RATP; lia); rewrite ?(unsigned_lit (usp0 + -128)) by lia; unfold RMallocRep.RATP; cbn [Z.add];
        first [ exact P2 | right; left; reflexivity | exact AUX | exact ST | exact MI | exact ERR2 | unfold RFREE_STACK; lia | lia ]. }
    cbv beta. intros [] s2 ms2 [PO LEAF].
    destruct PO as (w0 & w1 & w2 & rb0 & d1 & d2 & d3 & d4 & d5 & d6 & d7 & w3 & w4 & w5 & w6 & m3 & -> & MI3 & ST3 & ERR3 & AUX3 & HPR3 & FAE3 & SOE3 & HEAP3).
    unfold RATP in ERR3. rewrite ?(unsigned_lit RMallocRep.RATP) in ERR3 by (unfold RMallocRep.RATP; lia). unfold RMallocRep.RATP in ERR3. cbn [Z.add] in ERR3.
    rewrite ?(unsigned_lit (usp0 + -128)) in ST3 by lia. rewrite ?(unsigned_lit (usp0 + -128)) in HPR3 by lia.
    replace (ret_pc (Z_to_bv 64 0xe16a0)) with (Z_to_bv 64 0xe16a0) by (symmetry; rpc).
    rewrite (lb_remove_second (rd_buf st) (nb, A', rd_cap st * 2) (rd_buf st, A, rd_cap st) eq_refl ND) in HPR3, HEAP3.
    assert (BA3 : BASE' m3) by (eapply (BASE_heap sp0 argv envp uid TID); [exact BA2| exact HPR3| exact MI3| unfold LO; exact ST3| exact AUX3| exact HEAP3]).
    assert (EX3 : EXTRA CS m3 s2) by (eapply (EXTRA_heap CS sp0); [exact HPR3| exact SOE3| exact EX2]).
    assert (FR3 : FRAME' m3) by (unfold MFRAME; eapply rheap_pres_rw_cells; [exact HPR3| exact FR2| left; cbn; lia]).
    assert (SG3 : STG m3) by (eapply (STG_heap sp0); [exact HPR3| exact SG2]).
    assert (NB3 : rw_cells usegs m3 A' [CB (length DATA) DATA; CB (Z.to_nat (rd_cap st * 2 - Z.of_nat (length DATA))) (firstn (Z.to_nat (rd_cap st * 2) - length DATA)%nat (skipn (length DATA) junk'))]).
    { eapply rheap_pres_rw_cells; [exact HPR3| |].
      - apply (proj2 (rw_cells_app _ _ _ [CB (length DATA) DATA] _)). split; [replace (length DATA) with (Z.to_nat (Z.of_nat (length DATA))) at 1 by lia; exact NB1'|].
        cbn [cells_size csize Nat.add]. replace (Z.to_nat (rd_cap st * 2 - Z.of_nat (length DATA))) with (Z.to_nat (rd_cap st * 2) - length DATA)%nat by lia. exact NB2'.
      - right; right. exists (nb, A', rd_cap st * 2). split; [left; reflexivity|]. cbn [blk_addr blk_size fst snd cells_size csize Nat.add]. lia. }
    (* [comment removed for export] *)
    assert (HA3 : A' = ptr_addr s2 nb).
    { rewrite HEXP. symmetry. apply (rfree_keeps_ptr_proof s1 s2 [(nb, A', rd_cap st * 2); (rd_buf st, A, rd_cap st)] m2 (rd_buf st) A (rd_cap st) (nb, A', rd_cap st * 2)); [exact P2| right; left; reflexivity| exact LEAF|].
      rewrite (lb_remove_second (rd_buf st) (nb, A', rd_cap st * 2) (rd_buf st, A, rd_cap st) eq_refl ND). left; reflexivity. }
    clear HPR3 FR1 NB1' NB2' LEAF.
    (* [comment removed for export] *)
    apply implM_retb. cbv beta iota.
    rewrite <- LENZ.
    eapply (rd_read CS sp0 argv envp uid arg0 arg1 TID PAD S4 S5 S6 S7 S8 S9 S10 S11 VSP CEIL VARGV VENVP EARGV HT FPR FWX SWF fd P1v (mkRd nb (rd_cap st * 2) (rd_content st)) s2);
      cbn [rd_buf rd_cap rd_content]; first [exact FD | exact HP1 | exact HC | exact SG3 | exact FR3 | exact BA3 | exact EX3 | unfold RMallocRep.RERRNO; exact ERR3 | exact FRM | lia | idtac].
    split; [exact HEAP3|]. split; [exact HA3|]. split; [exact NB3|].
    assert (CAP2 : rd_cap st * 2 <= 67108864).
    { rewrite CAPK in LTM |- *. change 67108864 with (2 ^ 26) in LTM |- *. apply Z.pow_lt_mono_r_iff in LTM; [| lia| lia].
      replace (2 ^ k * 2) with (2 ^ (k + 1)) by (rewrite Z.pow_add_r by lia; lia). apply Z.pow_le_mono_r; lia. }
    unfold MAX_INPUT. split; [split; [lia| exists (k + 1); split; [lia| rewrite CAPK, Z.pow_add_r by lia; lia]]|]. split; [lia| exact BR'].
  Qed.

  (* [comment removed for export] *)
  Definition POSTLOOP (fd P1v : Z) (r : rd_result) (s : PState) (ms : machine_state) : Prop :=
    match r with
    | RdExit => at_exit ps_so 2 s ms
    | RdDone b c => RDBRK' fd P1v b c s ms
    end.

  Lemma rd_loop : forall (fuel : nat) (fd P1v : Z) (st : rd_st) (s : PState) ms,
    3 <= fd < 2^32 -> nth_error (argv_ptrs sp0 argv envp) 1 = Some (Z_to_bv 64 P1v) ->
    RDHEAD' fd P1v st s ms ->
    implM usegs (mloop fuel (read_loop_body io raw_malloc raw_free ustage fd (map bv_unsigned arg1)) st) s (POSTLOOP fd P1v) ms.
  Proof.
    induction fuel as [|fuel IH]; intros fd P1v st s ms FD HP1 RI.
    - cbn [mloop]. apply implM_unr.
    - apply implM_loop_S. eapply implM_mono; [apply rd_body; [exact FD| exact HP1| exact RI]|].
      intros [st'|[|b c]] s' ms' PO; cbn [POSTBODY POSTLOOP] in PO |- *.
      + apply IH; [exact FD| exact HP1| exact PO].
      + apply evt_done. exact PO.
      + apply evt_done. exact PO.
  Qed.

End B2.
End WithCeiling0.
