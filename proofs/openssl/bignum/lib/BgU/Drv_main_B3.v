(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgLib Require Import ImageBg.

From Stdlib Require Import ZArith List Lia Bool Permutation Strings.String.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP MonadX.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.Malloc Require Import MallocBlocks Malloc_iface.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgMallocU Require Import RMallocRep RMallocTree RMalloc_iface RMalloc_ifaceP.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.Spec Require Import Prelim STree Malloc Monad Stdio HexModel Target Driver Prog StrFun LibProg ProgG.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.P Require Import Str_tac Startup_glue InitMem.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgU Require Import Layout Exit Startup Stdio_iface Printf_lib Printf_stdio_iface Lib_iface Exit_defs Driver_iface Drv_kit Drv_facts Drv_main_defs Drv_main_A Drv_main_B Drv_main_B2.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.P Require Str_cpy.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgU Require Drv_sys F_memcpy.
From OssFuzzTheorems.openssl.bignum.images Require Import Ubsan.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Open Scope mspec_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Notation bgusegs := ImageBg.bgusegs.
Notation mem := (word -> option byte).
Notation wz := MallocRep.wz.
Notation pph := Ubsan.M.phdrs.
Ltac rpc := apply ret_pc_even; [lia| reflexivity].

From OssFuzzTheorems.Proofs.openssl.bignum.lib.Lib Require Import Ceiling.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.P Require Import Rnd.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.Malloc Require Import CeilWin.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Local Lemma implM_unfold__ : forall {St A : Type} (segs : list LinuxProcessSemantics.LinuxProcessSem.MemImageType.Segment)
  (c : @OssFuzzTheorems.Proofs.openssl.bignum.lib.Spec.Monad.M St A) (s : St)
  (Q : A -> St -> LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.machine_state -> Prop) ms,
  OssFuzzTheorems.Proofs.openssl.bignum.lib.Spec.Monad.implM segs c s Q ms ->
  OssFuzzTheorems.Proofs.openssl.bignum.lib.Lib.ITree.impl segs (OssFuzzTheorems.Proofs.openssl.bignum.lib.Lib.Nodes.at_node segs) (c s)
    (OssFuzzTheorems.Proofs.openssl.bignum.lib.Lib.ITree.epost (fun p => Q (fst p) (snd p))) ms.
Proof. intros St A segs c s Q ms H. exact H. Qed.

Local Ltac std_lia__ := lia.
Local Ltac lia := first [std_lia__ | try (pose proof ceil_window_holds as CEIL_RANGE__); unfold ceil_window in *; std_lia__].
Local Ltac std_nia__ := nia.
Local Ltac nia := first [std_nia__ | try (pose proof ceil_window_holds as CEIL_RANGE__); unfold ceil_window in *; std_nia__].
Local Ltac OssFuzzTheorems.Proofs.openssl.bignum.lib.Lib.ZBridge.flia ::= first [ assumption | OssFuzzTheorems.Proofs.openssl.bignum.lib.Lib.ZBridge.slim; lia | lia ].
Local Ltac OssFuzzTheorems.Proofs.openssl.bignum.lib.Lib.ZBridge.mlia ::= Z.div_mod_to_equations; lia.
Local Ltac OssFuzzTheorems.Proofs.openssl.bignum.lib.Lib.Step.slia ::= first [ exact I | lia | split; [lia|exact I] ].
Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd} {LM : LibModel} {LSP : LibSpec} {LL : LibLaws}.
Section B3.
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
  Notation IMGB := (build_stack_bytes pph sp0 argv envp uid run_hw run_draw).
  Notation RDHEAD' := (RDHEAD sp0 argv envp uid TID PAD S4 S5 S6 S7 S8 S9 S10 S11).
  Notation RDBRK' := (RDBRK sp0 argv envp uid TID PAD S4 S5 S6 S7 S8 S9 S10 S11).
  Notation POSTBODY' := (POSTBODY sp0 argv envp uid TID PAD S4 S5 S6 S7 S8 S9 S10 S11).
  Notation POSTLOOP' := (POSTLOOP sp0 argv envp uid TID PAD S4 S5 S6 S7 S8 S9 S10 S11).

  Notation GST pc x1 t0 t1 t2 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 t3 t4 t5 t6 F fc mm :=
    (MS (mkR x1 (Z_to_bv 64 (usp0 + -128)) (Z_to_bv 64 0x10800) (Z_to_bv 64 RATP) t0 t1 t2 (Z_to_bv 64 2) x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 S8 S9 S10 S11 t3 t4 t5 t6)
        F (Z_to_bv 64 pc) fc None mm (seg_rom bgusegs)).
  Notation RST pc x1 t0 t1 t2 x9 a0 a1 a2 a3 a4 a5 a6 a7 P1v len fd cap x23 t3 t4 t5 t6 F fc mm :=
    (GST pc x1 t0 t1 t2 x9 a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 P1v) (Z_to_bv 64 len) (Z_to_bv 64 fd) (Z_to_bv 64 cap) (Z_to_bv 64 RSTAGE) x23 t3 t4 t5 t6 F fc mm).

  Definition RDONE (bufp : bptr) (content : list Z) (s : PState) (ms : machine_state) : Prop :=
    exists (x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 x23 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (mm : mem)
           (A cap P1v fd : Z) (DATA junk : list byte) (errv : word),
      ms = RST 0xe16d8 x1 t0 t1 t2 (Z_to_bv 64 A) a0 a1 a2 a3 a4 a5 a6 a7 P1v (zlength content) fd cap x23 t3 t4 t5 t6 F fc mm
      /\ content = map bv_unsigned DATA
      /\ BUF mm s bufp A cap DATA junk
      /\ FRAME' mm /\ BASE' mm /\ EXTRA mm s /\ rw_cells bgusegs mm RMallocRep.RERRNO [C4 errv] /\ frm0 fc.

  Definition POSTB (r : rd_result) (s : PState) (ms : machine_state) : Prop :=
    match r with
    | RdExit => at_exit 2 s ms
    | RdDone b c => RDONE b c s ms
    end.

  Lemma main_read_all : forall (t0 t1 t2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (fc : bv 32) (mm : mem),
    FRAME' mm -> BASE' mm -> RHEAP (ps_init (reservedZ bgusegs)) [] mm -> EXTRA mm (ps_init (reservedZ bgusegs)) ->
    rw_cells bgusegs mm RMallocRep.RERRNO [C4 (Z_to_bv 64 0)] -> STG mm -> frm0 fc ->
    implM bgusegs (read_all io raw_malloc raw_free bgustage (map bv_unsigned arg1)) (ps_init (reservedZ bgusegs)) POSTB
      (MS (mkR (Z_to_bv 64 RMAIN_RET) (Z_to_bv 64 (usp0 + -128)) (Z_to_bv 64 0x10800) (Z_to_bv 64 RATP) t0 t1 t2
               (Z_to_bv 64 2) (Z_to_bv 64 2) (Z_to_bv 64 2) (Z_to_bv 64 (usp0 + 8)) (Z_to_bv 64 (envp_addr sp0 argv)) a3 a4 a5 a6 a7
               (Z_to_bv 64 RMAIN) (Z_to_bv 64 (envp_addr sp0 argv)) S4 S5 S6 S7 S8 S9 S10 S11 t3 t4 t5 t6)
          bvmap_empty (Z_to_bv 64 RP1) fc None mm (seg_rom bgusegs)).
  Proof.
    intros until mm. intros FR BA HP0 EX ERR SG FRM.
    pose proof (sp_facts sp0 VSP CEIL) as SF. unfold LO in SF. try (pose proof alloc_ceiling_range as CEIL_RANGE). pose proof (IMGB_bound sp0 argv envp uid VSP VARGV VENVP) as IL. try (pose proof alloc_ceiling_range as CEIL_RANGE).
    pose proof BA as (ST & MI & ES & AUX & SSP & LXS & IMG). unfold LO in ST. unfold RMallocRep.RERRNO in ERR. unfold MFRAME in FR.
    pose proof VARGV as (_ & _ & ARGLEN & NONUL & _).
    unfold RMAIN_RET, RMAIN, RP1.

    destruct (argv_cstring sp0 argv envp uid mm IMG 1 arg1 ltac:(rewrite EARGV; reflexivity) ltac:(clear -SF; Z.div_mod_to_equations; lia))
      as (P1v & slack1 & HP1 & P1LO & P1HI & STR1 & SLK1). unfold str_base, struct_size, argc, envc in P1LO.
    destruct (stack_pieces sp0 argv envp uid mm IMG) as (_ & ARGVP & _).
    assert (A1NN : ~ In (Z_to_bv 8 0) arg1) by (rewrite EARGV in NONUL; inversion NONUL as [|? ? ? X]; inversion X; assumption).
    assert (A1LEN : Z.of_nat (length arg1) <= 131071) by (rewrite EARGV in ARGLEN; inversion ARGLEN as [|? ? ? X]; inversion X; assumption).
    assert (STR1' : bytes_at bgusegs mm P1v (arg1 ++ [Z_to_bv 8 0])).
    { change (arg1 ++ Z_to_bv 8 0 :: slack1) with (arg1 ++ ([Z_to_bv 8 0] ++ slack1)) in STR1. rewrite app_assoc in STR1. apply bytes_at_app in STR1. destruct STR1 as [S1 _]. exact S1. }
    pose proof SSP as [G1 G2]. unfold got_ssp, ssp_guard in G1, G2. cbv delta [MallocRep.wz] in G1, G2.
    unfold read_all. unfold implM. iprefix.
    pose proof (rd_u64s_g bgusegs mm (usp0 + 8) (argv_ptrs sp0 argv envp ++ [Z_to_bv 64 0]) 1 (Z_to_bv 64 P1v) (Z_to_bv 64 (usp0 + 16))
                  ARGVP ltac:(rewrite nth_error_app1 by (rewrite argv_ptrs_length, EARGV; cbn; lia); exact HP1) ltac:(unfold wa; f_equal; lia)) as RD.
    zstep. clear RD. zstep. zstep. zstep. zstep.
    remember READ_FUEL as rf eqn:Erf. clear Erf.
    apply evt_done.
    lazymatch goal with |- impl _ _ (?tm _) _ ?msx => apply (implM_unfold__ bgusegs tm (ps_init (reservedZ bgusegs)) POSTB msx) end.
    replace (map (Z_to_bv 8) (map bv_unsigned arg1)) with arg1 by (symmetry; apply zbytes_map_unsigned').
    eapply implM_bind.
    { eapply implM_of_enode.
      eapply Drv_sys.open_spec with (lo := usp0 - 8388608) (errv := Z_to_bv 64 0) (canary := rr_guard);
        [ rewrite (unsigned_lit (usp0 + -128)) by lia; exact ST
        | rewrite (unsigned_lit P1v) by lia; exact STR1'
        | unfold RATP; rewrite (unsigned_lit RMallocRep.RATP) by (unfold RMallocRep.RATP; lia); exact ERR
        | unfold RATP; rewrite (unsigned_lit RMallocRep.RATP) by (unfold RMallocRep.RATP; lia); exact (exit_statics_cancel _ _ (proj1 ES))
        | exact G1 | exact G2 | exact MI | reflexivity | exact A1NN | ..].
      all: unfold RATP, Drv_sys.got_ssp, Drv_sys.ssp_guard, RMallocRep.RATP; rewrite ?(unsigned_lit 3346328) by lia; rewrite ?(unsigned_lit (usp0 + -128)) by lia; rewrite ?(unsigned_lit P1v) by lia; cbn [Z.add]; lia. }
    cbv beta. intros r s' ms' [PO ->].
    destruct PO as (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & m1 & -> & MUc & WMc & MI1 & ST1 & ERR1 & _ & _ & _ & FDR).
    unfold RATP in MUc, ERR1. rewrite ?(unsigned_lit RMallocRep.RATP) in MUc by (unfold RMallocRep.RATP; lia). rewrite ?(unsigned_lit (usp0 + -128)) in MUc by lia.
    rewrite ?(unsigned_lit (usp0 + -128)) in ST1 by lia. rewrite ?(unsigned_lit RMallocRep.RATP) in ERR1 by (unfold RMallocRep.RATP; lia).
    unfold RMallocRep.RATP in MUc, ERR1. cbn [Z.add] in MUc, ERR1.
    replace (ret_pc (Z_to_bv 64 0xe1600)) with (Z_to_bv 64 0xe1600) by (symmetry; rpc).
    assert (WOKW : Forall (WOK sp0) [(usp0 + -128 - 144, usp0 + -128); (3346164, 3346164 + 4)]).
    { unfold WOK, LO, RMallocRep.RERRNO. constructor; [cbn [fst snd]; lia|]. constructor; [cbn [fst snd]; lia| constructor]. }
    assert (HP1' : RHEAP (ps_init (reservedZ bgusegs)) [] m1).
    { eapply (RHEAP_munchW sp0 VSP CEIL); [apply WOK_WOKE; exact WOKW| exact MUc| exact WMc| | exact HP0]. intros iv [<-|[<-|[]]]; cbn [fst snd]; intros; lia. }
    assert (BA1 : BASE' m1) by (eapply (BASE_munch sp0 argv envp uid TID VSP CEIL); [exact BA| apply WOK_WOKE; exact WOKW| exact MUc| exact WMc| exact MI1| unfold LO; exact ST1]).
    assert (EX1 : EXTRA m1 (ps_init (reservedZ bgusegs))) by (eapply (EXTRA_munch sp0 VSP CEIL); [exact WOKW| exact MUc| exact WMc| reflexivity| exact EX]).
    assert (FR1 : rw_cells bgusegs m1 (usp0 + -128) [CB 8 PAD; C8 S7; C8 S6; C8 S5; C8 S4; C8 (wz (envp_addr sp0 argv)); C8 (wz Driver_iface.RMAIN); C8 (wz (argc argv)); C8 (wz (usp0 + 8)); C8 (wz Drv_main_defs.RMAIN_RET)]).
    { eapply rw_cells_agree; [eapply agree_on_of_munch; [exact MUc| exact WMc]| exact FR|]. intros a Ha. cbn in Ha |- *. lia. }
    assert (STR2 : bytes_at bgusegs m1 P1v (arg1 ++ Z_to_bv 8 0 :: slack1)).
    { eapply bytes_at_agree; [eapply agree_on_of_munch; [exact MUc| exact WMc]| exact STR1|]. intros a Ha. cbn in Ha |- *. lia. }
    assert (SG1 : STG m1) by (eapply STG_munch; [exact MUc| exact WMc| intros a Ha; cbn; lia| exact SG]).
    clear MUc WMc BA WOKW HP0 G1 G2 ST MI ES AUX SSP LXS IMG EX FR STR1 STR1' SG.
    pose proof BA1 as (ST & MI & ES & AUX & SSP & LXS & IMG). unfold LO in ST.
    unfold implM. iprefix.
    destruct r as [e|fd]; cbn [Drv_sys.open_ret Drv_sys.open_errno] in *.
    -
      pose proof LXS as (G1 & G2). unfold LX_GOT_STDERR, LX_STDERR_PTR, LX_STDERR_FILE in G1, G2. cbv delta [MallocRep.wz] in G1, G2.
      replace (Z_to_bv 64 (-1)) with (Z_to_bv 64 18446744073709551615) by (apply Z_to_bv_eqm; reflexivity).
      zstep. if_cases K0; zify_cond K0; [| exfalso; revert K0; clear; intros K0; rewrite ?unsigned_lit in K0 by lia; lia]. clear K0.
      zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. apply evt_done.
      lazymatch goal with |- impl _ _ (?tm _) _ ?msx => apply (implM_unfold__ bgusegs tm (ps_init (reservedZ bgusegs)) POSTB msx) end.
      cbn [io_diag io io_S].
      eapply (fprintf_exit sp0 argv envp uid TID S8 S9 S10 S11 VSP CEIL HT FPR FWX SWF (DCannotOpen (map bv_unsigned arg1)));
        [| exact BA1| exact HP1'| exact EX1| exact FRM| exact ERR1| intros ms'' AE; apply implM_ret; apply evt_done; exact AE].
      cbn [diag_args]. split; [reflexivity|]. exists slack1. rewrite unsigned_lit by lia.
      rewrite zb_map_unsigned. unfold zlength. rewrite !length_map.
      split; [exact STR2|]. split; [apply map_unsigned_pos; exact A1NN|]. split; [lia|].
      split; [lia|]. split; [right; lia| unfold GLOBALS_TOP; lia].
    -
      zstep. if_cases K0; zify_cond K0; [exfalso; rewrite ?unsigned_lit in K0 by lia; lia|]. clear K0.
      zstep. zstep. zstep. zstep. zstep. apply evt_done.
      lazymatch goal with |- impl _ _ (?tm _) _ ?msx => apply (implM_unfold__ bgusegs tm (ps_init (reservedZ bgusegs)) POSTB msx) end.
      eapply implM_bind.
      { unfold rmalloc_stmt in MALLOC.
        eapply MALLOC with (lo := usp0 - 8388608) (B := usp0); try reflexivity; unfold RATP; rewrite ?(unsigned_lit RMallocRep.RATP) by (unfold RMallocRep.RATP; lia); rewrite ?(unsigned_lit (usp0 + -128)) by lia;
          unfold RMallocRep.RATP; cbn [Z.add];
          first [ exact HP1' | exact AUX | exact ST | exact ERR1 | exact MI | unfold RMALLOC_STACK; lia | lia ]. }
      cbv beta. intros r s1 ms1 PO.
      destruct PO as (v0 & v1 & v2 & ra0 & c1 & c2 & c3 & c4 & c5 & c6 & c7 & v3 & v4 & v5 & v6 & m2 & errv2 & -> & MI2 & ST2 & ERR2 & AUX2 & HPR & FAE & SOE & RR).
      unfold RATP in ERR2. rewrite ?(unsigned_lit RMallocRep.RATP) in ERR2 by (unfold RMallocRep.RATP; lia). unfold RMallocRep.RATP in ERR2. cbn [Z.add] in ERR2.
      rewrite ?(unsigned_lit (usp0 + -128)) in ST2 by lia. rewrite ?(unsigned_lit (usp0 + -128)) in HPR by lia.
      replace (ret_pc (Z_to_bv 64 0xe1618)) with (Z_to_bv 64 0xe1618) by (symmetry; rpc).
      assert (FR2 : FRAME' m2) by (unfold MFRAME; eapply rheap_pres_rw_cells; [exact HPR| exact FR1| left; cbn; lia]).
      assert (SG2 : STG m2) by (eapply (STG_heap sp0); [exact HPR| exact SG1]).
      destruct r as [buf|].
      2:{
          destruct RR as [-> HEAP2].
          assert (BA2 : BASE' m2) by (eapply (BASE_heap sp0 argv envp uid TID); [exact BA1| exact HPR| exact MI2| unfold LO; exact ST2| exact AUX2| exact HEAP2]).
          assert (EX2 : EXTRA m2 s1) by (eapply (EXTRA_heap sp0); [exact HPR| exact SOE| exact EX1]).
          clear FR1 ST MI ES AUX SSP LXS IMG ERR1.
          pose proof BA2 as (ST & MI & ES & AUX & SSP & LXS & IMG). unfold LO in ST.
          pose proof LXS as (G1 & G2). unfold LX_GOT_STDERR, LX_STDERR_PTR, LX_STDERR_FILE in G1, G2. cbv delta [MallocRep.wz] in G1, G2.
          unfold implM. iprefix.
          zstep. if_cases K1; zify_cond K1; [| exfalso; rewrite ?unsigned_lit in K1 by lia; lia]. clear K1.
          zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. apply evt_done.
          lazymatch goal with |- impl _ _ (?tm _) _ ?msx => apply (implM_unfold__ bgusegs tm s1 POSTB msx) end.
          cbn [io_diag io io_S].
          eapply (fwrite_exit sp0 argv envp uid TID S8 S9 S10 S11 VSP CEIL HT FWR);
            [exact BA2| exact HEAP2| exact EX2| exact ERR2| intros ms'' AE; apply implM_ret; apply evt_done; exact AE]. }
      destruct RR as (A & junk & -> & BR & HEAP2 & BLK & HEXP).
      specialize (HEXP ltac:(apply raddr_exposed_init; reflexivity)).
      assert (BA2 : BASE' m2) by (eapply (BASE_heap sp0 argv envp uid TID); [exact BA1| exact HPR| exact MI2| unfold LO; exact ST2| exact AUX2| exact HEAP2]).
      assert (EX2 : EXTRA m2 s1) by (eapply (EXTRA_heap sp0); [exact HPR| exact SOE| exact EX1]).
      clear FR1 ST MI ES AUX SSP LXS IMG ERR1 SG1.
      pose proof BA2 as (ST & MI & ES & AUX & SSP & LXS & IMG). unfold LO in ST.
      pose proof BR as (BR1 & BR2 & BR3 & BR4 & BR5).
      unfold implM. iprefix.
      zstep. if_cases K1; zify_cond K1; [exfalso; rewrite ?unsigned_lit in K1 by lia; lia|]. clear K1.

      zstep. zstep. zstep. zstep. zstep. if_true. zstep. zstep. apply evt_done.
      lazymatch goal with |- impl _ _ (?tm _) _ ?msx => apply (implM_unfold__ bgusegs tm s1 POSTB msx) end.

      destruct rf as [|rf]; [eapply (@implM_bind _ _ _ _ _ _ _ (fun _ _ _ => False)); [cbn [mloop]; apply implM_unr| intros ? ? ? []]|].
      eapply implM_bind.
      { apply implM_loop_S. rewrite read_loop_body_eq. unfold rd_grow_part. cbn [rd_content rd_cap rd_buf zlength length Z.of_nat].
        replace (0 =? 65536) with false by reflexivity. apply implM_retb. cbv beta iota.
        eapply implM_mono.
        - change 0 with (zlength (rd_content (mkRd buf 65536 []))).
          eapply (rd_read sp0 argv envp uid arg0 arg1 TID PAD S4 S5 S6 S7 S8 S9 S10 S11 VSP CEIL VARGV VENVP EARGV HT FPR FWX SWF fd P1v (mkRd buf 65536 []) s1)
            with (A := A) (DATA := []) (junk := junk) (errv := errv2);
            cbn [rd_content rd_cap rd_buf zlength length Z.of_nat]; first [lia | exact HP1 | reflexivity | exact SG2 | exact FR2 | exact BA2 | exact EX2 | exact ERR2 | exact FRM | idtac].
          split; [exact HEAP2|]. split; [exact HEXP|]. cbn [length Z.of_nat Z.sub].
          split; [replace (Z.to_nat (65536 - 0)) with (Z.to_nat 65536) by reflexivity; apply (proj2 (rw_cells_app _ _ _ [CB 0%nat []] _)); split; [| cbn [cells_size csize Nat.add]; rewrite Z.add_0_r; exact BLK] |].
          + apply rw_cells_CB0. lia.
          + unfold MAX_INPUT. split; [split; [lia| exists 16; split; [lia| reflexivity]]|]. split; [lia| exact BR].
        - intros [st'|[|b c]] s3 ms3 PO; cbn [POSTBODY POSTLOOP] in PO |- *.
          + apply (rd_loop sp0 argv envp uid arg0 arg1 TID PAD S4 S5 S6 S7 S8 S9 S10 S11 VSP CEIL VARGV VENVP EARGV HT MALLOC FREE FPR FWX SWF FWR rf fd P1v); [lia| exact HP1| exact PO].
          + apply evt_done. exact PO.
          + apply evt_done. exact PO. }
      cbv beta. intros res s2 ms2 PO.
      destruct res as [|b c]; cbn [POSTLOOP] in PO.
      { apply implM_ret. apply evt_done. exact PO. }

      clear dependent m2.
      destruct PO as (x1 & w0 & w1 & w2 & d0 & d1 & d2 & d3 & d4 & d5 & d6 & d7 & x23 & w3 & w4 & w5 & w6 & F2 & fc2 & m3 & A3 & cap3 & DATA3 & junk3 & errv3
                      & -> & HC3 & BU3 & SG3 & FR3 & BA3 & EX3 & ERR3 & FRM3).
      pose proof BA3 as (ST & MI & ES & AUX & SSP & LXS & IMG). unfold LO in ST. unfold RMallocRep.RERRNO in ERR3. unfold MFRAME in FR3.
      pose proof BU3 as (P3 & HA3 & BLK3 & CAP3 & LEN3 & BRR3).
      pose proof BRR3 as (BQ1 & BQ2 & BQ3 & BQ4 & BQ5).
      unfold implM. iprefix. zstep. zstep. zstep. apply evt_done.
      lazymatch goal with |- impl _ _ (?tm _) _ ?msx => apply (implM_unfold__ bgusegs tm s2 POSTB msx) end.

      pose proof (exit_statics_cancel _ _ (proj1 ES)) as CAN. unfold RMallocRep.RATP in CAN. cbn [Z.add] in CAN.
      eapply implM_bind.
      { eapply implM_of_enode.
        eapply Drv_sys.close_spec with (lo := usp0 - 8388608) (errv := errv3); try reflexivity; unfold RATP; rewrite ?(unsigned_lit RMallocRep.RATP) by (unfold RMallocRep.RATP; lia); rewrite ?(unsigned_lit (usp0 + -128)) by lia;
          unfold RMallocRep.RATP; cbn [Z.add];
          first [ exact ST | exact ERR3 | exact CAN | exact MI | lia ]. }
      cbv beta. intros r3 s3 ms3 [PO ->].
      destruct PO as (y0 & y1 & y2 & e1 & e2 & e3 & e4 & e5 & e6 & e7 & y3 & y4 & y5 & y6 & m4 & -> & MUc & WMc & MI4 & ST4 & ERR4).
      unfold RATP in MUc, ERR4. rewrite ?(unsigned_lit RMallocRep.RATP) in MUc by (unfold RMallocRep.RATP; lia). rewrite ?(unsigned_lit (usp0 + -128)) in MUc by lia.
      rewrite ?(unsigned_lit (usp0 + -128)) in ST4 by lia. rewrite ?(unsigned_lit RMallocRep.RATP) in ERR4 by (unfold RMallocRep.RATP; lia).
      unfold RMallocRep.RATP in MUc, ERR4. cbn [Z.add] in MUc, ERR4.
      replace (ret_pc (Z_to_bv 64 0xe16d8)) with (Z_to_bv 64 0xe16d8) by (symmetry; rpc).
      assert (WOKW : Forall (WOK sp0) [(usp0 + -128 - 64, usp0 + -128); (3346164, 3346164 + 4)]).
      { unfold WOK, LO, RMallocRep.RERRNO. constructor; [cbn [fst snd]; lia|]. constructor; [cbn [fst snd]; lia| constructor]. }
      assert (P4 : RHEAP s2 [(b, A3, cap3)] m4).
      { eapply (RHEAP_munchW sp0 VSP CEIL); [apply WOK_WOKE; exact WOKW| exact MUc| exact WMc| | exact P3]. intros iv [<-|[<-|[]]]; cbn [fst snd]; intros; lia. }
      assert (BA4 : BASE' m4) by (eapply (BASE_munch sp0 argv envp uid TID VSP CEIL); [exact BA3| apply WOK_WOKE; exact WOKW| exact MUc| exact WMc| exact MI4| unfold LO; exact ST4]).
      assert (EX4 : EXTRA m4 s2) by (eapply (EXTRA_munch sp0 VSP CEIL); [exact WOKW| exact MUc| exact WMc| reflexivity| exact EX3]).
      assert (FR4 : FRAME' m4) by (unfold MFRAME; eapply (MFRAME_munch sp0 argv VSP CEIL); [apply WOK_WOKE; exact WOKW| exact MUc| exact WMc| exact FR3]).
      assert (BLK4 : rw_cells bgusegs m4 A3 [CB (length DATA3) DATA3; CB (Z.to_nat (cap3 - Z.of_nat (length DATA3))) junk3]).
      { eapply rw_cells_agree; [eapply agree_on_of_munch; [exact MUc| exact WMc]| exact BLK3|]. intros a Ha. cbn in Ha |- *. lia. }
      apply implM_ret. apply evt_done. cbn [POSTB]. unfold RDONE.
      do 17 eexists. exists F2, fc2, m4, A3, cap3, P1v, fd, DATA3. exists junk3, (Drv_sys.close_errno r3 errv3).
      split; [reflexivity|]. split; [exact HC3|]. split; [| split; [exact FR4| split; [exact BA4| split; [exact EX4| split; [exact ERR4| exact FRM3]]]]].
      split; [exact P4|]. split; [exact HA3|]. split; [exact BLK4|]. split; [exact CAP3|]. split; [exact LEN3| exact BRR3].
  Qed.
End B3.
End WithCeiling0.
