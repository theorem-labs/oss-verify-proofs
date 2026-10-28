(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation Strings.String.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP MonadX.
From OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.Malloc Require Import MallocBlocks Malloc_iface.
From OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.MallocU Require Import RMallocRep RMallocTree RMalloc_iface RMalloc_ifaceP.
From OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.Spec Require Import Prelim STree Malloc Monad Stdio SjModel Target Driver Prog StrFun.
From OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.P Require Import Str_tac Startup_glue InitMem.
From OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.U Require Import Layout Exit Startup Stdio_iface Printf_lib Printf_stdio_iface Sj_iface Driver_iface Drv_kit Drv_facts Drv_main_defs Drv_main_A Drv_main_B Drv_main_B2 Drv_main_B3.
From OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.P Require Str_cpy.
From OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.U Require Drv_sys F_memcpy.
From OssFuzzTheorems.simdjson.fuzz_print_json.images Require Import Ubsan.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
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

From OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.Lib Require Import Ceiling.
From OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.P Require Import Rnd.
From OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.Malloc Require Import CeilWin.

Local Ltac std_lia__ := lia.
Local Ltac lia := first [std_lia__ | try (pose proof ceil_window_holds as CEIL_RANGE__); unfold ceil_window in *; std_lia__].
Local Ltac std_nia__ := nia.
Local Ltac nia := first [std_nia__ | try (pose proof ceil_window_holds as CEIL_RANGE__); unfold ceil_window in *; std_nia__].
Local Ltac OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.Lib.ZBridge.flia ::= first [ assumption | OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.Lib.ZBridge.slim; lia | lia ].
Local Ltac OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.Lib.ZBridge.mlia ::= Z.div_mod_to_equations; lia.
Local Ltac OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.Lib.Step.slia ::= first [ exact I | lia | split; [lia|exact I] ].
Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.
Lemma byte_range : forall b : byte, 0 <= bv_unsigned b < 256.
Proof. intros b. pose proof (bv_unsigned_in_range 8 b) as R. unfold bv_modulus in R. cbn in R. lia. Qed.

Definition sx8 (c : Z) : Z := if c <? 128 then c else c - 256.
Lemma signed_byte : forall b : byte, bv_signed b = sx8 (bv_unsigned b).
Proof.
  intros b. pose proof (byte_range b) as R. unfold bv_signed, sx8. unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus.
  cbn -[bv_unsigned Z.modulo Z.add Z.sub Z.ltb Z.mul]. change (2 ^ 8 / 2) with 128. change (2 ^ 8) with 256.
  destruct (Z.ltb_spec (bv_unsigned b) 128).
  - rewrite Z.mod_small; lia.
  - replace (bv_unsigned b + 128) with ((bv_unsigned b - 128) + 1 * 256) by lia. rewrite Z_mod_plus_full. rewrite Z.mod_small; lia.
Qed.

Lemma list6 : forall (l : list byte), (6 <= length l)%nat -> exists d0 d1 d2 d3 d4 d5 r, l = d0 :: d1 :: d2 :: d3 :: d4 :: d5 :: r.
Proof.
  intros l H. destruct l as [|d0 [|d1 [|d2 [|d3 [|d4 [|d5 r]]]]]]; cbn in H; try lia. do 7 eexists. reflexivity.
Qed.
Lemma skipn4 : forall (l : list byte) n, (n + 4 <= length l)%nat -> exists q0 q1 q2 q3 r, skipn n l = q0 :: q1 :: q2 :: q3 :: r.
Proof.
  intros l n H. pose proof (length_skipn n l) as L.
  destruct (skipn n l) as [|q0 [|q1 [|q2 [|q3 r]]]]; cbn in L; try lia. do 5 eexists. reflexivity.
Qed.
Lemma land15_mod : forall x, Z.land x 32767 = x mod 32768.
Proof. intros. change 32767 with (Z.ones 15). rewrite Z.land_ones by lia. reflexivity. Qed.
Lemma land_shiftl_small : forall a b k, 0 <= k -> 0 <= a < 2^k -> Z.land (Z.shiftl b k) a = 0.
Proof.
  intros a b k Hk Ha. rewrite Z.shiftl_mul_pow2 by lia.
  replace a with (Z.land a (Z.ones k)) by (rewrite Z.land_ones by lia; apply Z.mod_small; lia).
  rewrite (Z.land_comm a), Z.land_assoc, Z.land_ones by lia. rewrite Z_mod_mult. apply Z.land_0_l.
Qed.
Lemma lor_shiftl_add : forall a b k, 0 <= k -> 0 <= a < 2^k -> Z.lor (Z.shiftl b k) a = a + b * 2^k.
Proof.
  intros a b k Hk Ha. rewrite <- Z.lxor_lor by (apply land_shiftl_small; lia).
  rewrite <- Z.add_nocarry_lxor by (apply land_shiftl_small; lia). rewrite Z.shiftl_mul_pow2 by lia. lia.
Qed.
Lemma lor_mul_add : forall a b k, 0 <= k -> 0 <= a < 2^k -> Z.lor (b * 2^k) a = a + b * 2^k.
Proof. intros a b k Hk Ha. rewrite <- Z.shiftl_mul_pow2 by lia. rewrite lor_shiftl_add by lia. rewrite Z.shiftl_mul_pow2 by lia. reflexivity. Qed.
Lemma le16_cons : forall d0 d1 (r : list byte), le16 (map bv_unsigned (d0 :: d1 :: r)) = bv_unsigned d0 + bv_unsigned d1 * 256.
Proof. intros. reflexivity. Qed.
Lemma znth2_cons : forall d0 d1 d2 (r : list byte), znth (map bv_unsigned (d0 :: d1 :: d2 :: r)) 2 = bv_unsigned d2.
Proof. intros. reflexivity. Qed.

Lemma testbit15 : forall c0 c1, 0 <= c0 < 256 -> 0 <= c1 < 256 -> Z.testbit (c0 + c1 * 256) 15 = (128 <=? c1).
Proof.
  intros c0 c1 H0 H1. rewrite Z.testbit_eqb by lia. change (2 ^ 15) with 32768.
  replace ((c0 + c1 * 256) / 32768) with (c1 / 128) by (Z.div_mod_to_equations; nia).
  destruct (Z.leb_spec 128 c1).
  - replace (c1 / 128) with 1 by (Z.div_mod_to_equations; nia). reflexivity.
  - replace (c1 / 128) with 0 by (Z.div_mod_to_equations; nia). reflexivity.
Qed.

Lemma cfg15_Z : forall u0 u1, 0 <= u0 < 256 -> 0 <= u1 < 256 ->
  Z.lor (Z.shiftr (Z.land (Z.shiftl ((sx8 u1) mod 2^64) 57) 18446744073709551615) 49) u0 = Z.land (u0 + u1 * 256) 32767.
Proof.
  intros u0 u1 H0 H1.
  change 18446744073709551615 with (Z.ones 64). rewrite Z.land_ones by lia.
  rewrite Z.shiftl_mul_pow2 by lia. rewrite Z.shiftr_div_pow2 by lia.
  rewrite land15_mod.
  assert (E : (sx8 u1 mod 2 ^ 64 * 2 ^ 57) mod 2 ^ 64 / 2 ^ 49 = (u1 mod 128) * 2^8).
  { unfold sx8. destruct (Z.ltb_spec u1 128).
    - rewrite (Z.mod_small u1) by lia. rewrite (Z.mod_small u1) by lia.
      rewrite Z.mod_small by (split; [lia|]; change (2^64) with (2^7 * 2^57); apply Z.mul_lt_mono_pos_r; lia).
      change (2^57) with (2^49 * 2^8). rewrite Z.mul_assoc, (Z.mul_comm u1), <- Z.mul_assoc. rewrite Z.mul_comm.
      rewrite Z.div_mul by lia. lia.
    - replace ((u1 - 256) mod 2^64) with (2^64 - 256 + u1) by (Z.div_mod_to_equations; nia).
      replace ((2 ^ 64 - 256 + u1) * 2 ^ 57) with ((u1 - 128) * 2^57 + (2^57 - 1) * 2^64) by lia.
      rewrite Z.mod_add by lia. rewrite Z.mod_small by lia.
      replace (u1 mod 128) with (u1 - 128) by (Z.div_mod_to_equations; lia).
      change (2^57) with (2^8 * 2^49). rewrite Z.mul_assoc. rewrite Z.div_mul by lia. reflexivity. }
  rewrite E. rewrite lor_mul_add by lia. Z.div_mod_to_equations. lia.
Qed.

Section C.
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
  Notation RDONE' := (RDONE sp0 argv envp uid TID PAD S4 S5 S6 S7 S8 S9 S10 S11).

  Notation GST pc x1 t0 t1 t2 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 t3 t4 t5 t6 F fc mm :=
    (MS (mkR x1 (Z_to_bv 64 (usp0 + -128)) (Z_to_bv 64 0x10800) (Z_to_bv 64 RATP) t0 t1 t2 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 S8 S9 S10 S11 t3 t4 t5 t6)
        F (Z_to_bv 64 pc) fc None mm (seg_rom usegs)).

  Definition RQEXIT (code : Z) (s : PState) : machine_state -> Prop := at_exit ps_so code s.

  Definition main_tail (buf : bptr) (cw cfg : Z) (payload : list Z) : M PState Z :=
    status <- run cfg payload ;;
    status' <- (if Z.testbit cw 15 then
                  n <- alloc_count ;; mret (if n <? COUNT_MAX then n else COUNT_MAX)
                else mret status) ;;
    raw_free buf ;;;
    mret status'.

  Definition main_rest (buf : bptr) (content : list Z) : M PState Z :=
    let len := zlength content in
    if len <? HDR_MIN then io_diag io DShortHdr ;;; raw_free buf ;;; mret 2
    else
      let cfg_word := le16 content in
      let config_len := Z.land cfg_word 0x7fff in
      if len <? HDR_MIN + config_len then io_diag io DCfgOverrun ;;; raw_free buf ;;; mret 2
      else
        let bitmap := le32 (skipn (Z.to_nat (2 + config_len)) content) in
        let payload := skipn (Z.to_nat (6 + config_len)) content in
        let cfg := if 0 <? config_len then znth content 2 else 0 in
        alloc_init bitmap ;;; main_tail buf cfg_word cfg payload.

  Lemma main_model_eq : main_model io raw_malloc raw_free ustage alloc_init run alloc_count (argv_Z argv)
    = (ra <- read_all io raw_malloc raw_free ustage (map bv_unsigned arg1) ;;
       match ra with RdExit => mret 2 | RdDone buf content => main_rest buf content end).
  Proof. unfold main_model, argv_Z. rewrite EARGV. reflexivity. Qed.

  Definition HDR (A cap : Z) (DATA : list byte) (cw L cfg sc : Z) : Prop :=
    6 + L <= Z.of_nat (length DATA) /\ Z.of_nat (length DATA) <= cap /\ cap <= MAX_INPUT /\ rblock_range A cap
    /\ 0 <= cw < 65536 /\ L = Z.land cw 32767 /\ 0 <= L < 32768 /\ L <= cw /\ cw = le16 (map bv_unsigned DATA)
    /\ cfg = (if 0 <? L then znth (map bv_unsigned DATA) 2 else 0) /\ 0 <= cfg < 256
    /\ -128 <= sc < 128 /\ (Z.testbit cw 15 = (sc <? 0)).

  Definition RUN0 (bufp : bptr) (A cap : Z) (DATA : list byte) (cw L cfg sc : Z) (s : PState) (ms : machine_state) : Prop :=
    exists (x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 x23 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (mm : mem)
           (junk : list byte) (errv : word),
      ms = GST 0x3ca08 x1 t0 t1 t2 (Z_to_bv 64 (A + 2)) (Z_to_bv 64 A) a0 a1 a2 a3 a4 a5 a6 a7
               (Z_to_bv 64 L) (Z_to_bv 64 (A + 6 + L)) (Z_to_bv 64 (Z.of_nat (length DATA) - 6 - L)) (Z_to_bv 64 sc) (Z_to_bv 64 RSTAGE) x23 t3 t4 t5 t6 F fc mm
      /\ HDR A cap DATA cw L cfg sc
      /\ RHEAP s [(bufp, A, cap)] mm
      /\ rw_cells usegs mm A [CB (length DATA) DATA; CB (Z.to_nat (cap - Z.of_nat (length DATA))) junk]
      /\ FRAME' mm /\ BASE' mm /\ EXTRA mm s /\ rw_cells usegs mm RMallocRep.RERRNO [C4 errv] /\ frm0 fc.

  Lemma main_return : forall (code : Z) (s : PState) (LB : list block) (x1 t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (mm : mem),
    0 <= code < 2^64 ->
    FRAME' mm -> stk usegs mm LO' (usp0 + -128) ->
    ESTAT TID mm -> RHEAP s LB mm -> stdout_file mm (ps_so s) -> stderr_file mm -> mem_inv usegs mm ->
    evt usegs (at_exit ps_so code s)
      (GST 0x3caa4 x1 t0 t1 t2 (Z_to_bv 64 code) s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 t3 t4 t5 t6 F fc mm).
  Proof.
    intros until mm. intros CR FR ST ES HP SOF SEF MI. pose proof (sp_facts sp0 VSP CEIL) as SF. unfold LO in *. try (pose proof alloc_ceiling_range as CEIL_RANGE). unfold MFRAME in FR.
    unfold Drv_main_defs.RMAIN_RET, RMAIN in FR. cbv delta [MallocRep.wz] in FR.
    do 11 zstep. release_frame FR ST (usp0 + -48). zstep.
    replace (ret_pc (Z_to_bv 64 0xbf19c)) with (Z_to_bv 64 0xbf19c) by (symmetry; rpc).
    zstep.
    replace (ret_pc (Z_to_bv 64 0xbf1a0)) with (Z_to_bv 64 0xbf1a0) by (symmetry; rpc).
    apply evt_done. eapply (at_exit_intro TID HT code s LB); [exact ST| lia| lia| lia| exact ES| exact HP| exact SOF| exact SEF| exact MI].
  Qed.

  Lemma diagC_exit : forall (d : diag_msg) (msg : list Z) (PA : Z) (s : PState) (bufp : bptr) (A cap : Z)
      x1 t0 t1 t2 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 t3 t4 t5 t6 (F : bvmap 5 word) (fc : bv 32) (mm : mem) (errv : word),
    s_diag (St:=PState) d = stderr_fwrite msg -> ro_bytes_b usegs PA (to_bytes msg) = true -> zlength msg = 31 -> Forall (fun c => 0 <= c < 256) msg ->
    0x10000 <= PA -> PA + 31 <= 0xd5000 ->
    RHEAP s [(bufp, A, cap)] mm -> EXTRA mm s -> FRAME' mm -> BASE' mm -> rw_cells usegs mm RMallocRep.RERRNO [C4 errv] ->
    implM usegs (s_diag d ;;; raw_free bufp ;;; mret 2) s RQEXIT
      (GST 0x3ca98 x1 t0 t1 t2 (Z_to_bv 64 2) (Z_to_bv 64 A) (Z_to_bv 64 PA) (Z_to_bv 64 31) (Z_to_bv 64 1) (Z_to_bv 64 RSTDERR) x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 t3 t4 t5 t6 F fc mm).
  Proof.
    intros until errv. intros ED RO ML RNG LOA HIA P0 EX FR BA ERR.
    pose proof (sp_facts sp0 VSP CEIL) as SF. unfold LO in SF. try (pose proof alloc_ceiling_range as CEIL_RANGE).
    pose proof BA as (ST & MI & ES & AUX & SSP & LXS & IMG). unfold LO in ST. unfold RMallocRep.RERRNO in ERR. pose proof FR as FR0. unfold MFRAME in FR.
    pose proof EX as (SOF & SE & FL & IB).
    pose proof (RHEAP_block_range_proof _ _ _ (bufp, A, cap) P0 ltac:(left; reflexivity)) as BR. cbn [blk_addr blk_size fst snd] in BR.
    pose proof BR as (BR1 & BR2 & BR3 & BR4 & BR5). try (pose proof alloc_ceiling_range as CEIL_RANGE).
    rewrite ED.
    unfold implM. iprefix. zstep. apply evt_done.
    lazymatch goal with |- impl _ _ (?tm _) _ ?msx => change (implM usegs tm s RQEXIT msx) end.
    eapply implM_bind.
    { eapply (FWR) with (lo := usp0 - 8388608) (canary := rr_guard) (s := msg);
        [exact SE| rewrite unsigned_lit by lia; change (map _ msg) with (to_bytes msg); apply rodata_bytes; [exact MI| exact RO| lia| lia]
        | exact RNG | rewrite ML; lia| rewrite ML; reflexivity| reflexivity| reflexivity
        | rewrite unsigned_lit by lia; exact ST
        | rewrite unsigned_lit by lia; unfold FWRITE_DEPTH; lia| unfold GLOBALS_TOP; lia
        | rewrite !unsigned_lit by lia; lia
        | rewrite !unsigned_lit by lia; lia
        | exact SSP| exact MI]. }
    cbv beta. intros [] st' ms' PO.
    destruct PO as (u0 & u1 & u2 & b0 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & m1 & -> & MUc & WMc & MI1 & ST1 & SEW & SSP1 & ->).
    rewrite !unsigned_lit in MUc by lia. rewrite !unsigned_lit in ST1 by lia.
    replace (ret_pc (Z_to_bv 64 0x3ca9c)) with (Z_to_bv 64 0x3ca9c) by (symmetry; rpc).
    assert (WOKW : Forall (WOKE sp0) [(usp0 - 8388608, usp0 + -128); (RSTDERR, RSTDERR + 232)]).
    { unfold WOKE, WOK, LO. constructor; [cbn [fst snd]; lia|]. constructor; [cbn [fst snd]; lia| constructor]. }
    assert (BA1 : BASE' m1) by (eapply (BASE_munch sp0 argv envp uid TID VSP CEIL); [exact BA| exact WOKW| exact MUc| exact WMc| exact MI1| unfold LO; exact ST1]).
    assert (P1 : RHEAP s [(bufp, A, cap)] m1).
    { eapply (RHEAP_munchW sp0 VSP CEIL); [exact WOKW| exact MUc| exact WMc| | exact P0].
      intros iv [<-|[<-|[]]]; cbn [fst snd]; intros H1 H2; lia. }
    assert (EX1 : EXTRA m1 s) by (eapply (EXTRA_stdio sp0 VSP CEIL); [exact WOKW| exact MUc| exact WMc| reflexivity| exact SEW| exact EX]).
    assert (FR1 : FRAME' m1) by (unfold MFRAME; eapply (MFRAME_munch sp0 argv VSP CEIL); [exact WOKW| exact MUc| exact WMc| exact FR0]).
    assert (ERR1 : rw_cells usegs m1 977220 [C4 errv]).
    { eapply rw_cells_agree; [eapply agree_on_of_munch; [exact MUc| exact WMc]| exact ERR|]. intros a Ha. cbn in Ha |- *. lia. }
    clear MUc WMc ST MI ES AUX SSP LXS IMG.
    pose proof BA1 as (ST & MI & ES & AUX & SSP & LXS & IMG). unfold LO in ST.

    unfold implM. iprefix. zstep. zstep. apply evt_done.
    lazymatch goal with |- impl _ _ (?tm _) _ ?msx => change (implM usegs tm s RQEXIT msx) end.
    eapply implM_bind.
    { unfold rfree_stmt in FREE.
      eapply FREE with (lo := usp0 - 8388608) (B := usp0) (p := bufp) (A := A) (n := cap); try reflexivity; unfold RATP;
        rewrite ?(unsigned_lit RMallocRep.RATP) by (unfold RMallocRep.RATP; lia); rewrite ?(unsigned_lit (usp0 + -128)) by lia; unfold RMallocRep.RATP; cbn [Z.add];
        first [ exact P1 | left; reflexivity | exact AUX | exact ST | exact MI | exact ERR1 | unfold RFREE_STACK; lia | lia ]. }
    cbv beta. intros [] s2 ms2 PO.
    destruct PO as (w0 & w1 & w2 & rb0 & d1 & d2 & d3 & d4 & d5 & d6 & d7 & w3 & w4 & w5 & w6 & m3 & -> & MI3 & ST3 & ERR3 & AUX3 & HPR3 & FAE3 & SOE3 & HEAP3).
    rewrite ?(unsigned_lit (usp0 + -128)) in ST3 by lia. rewrite ?(unsigned_lit (usp0 + -128)) in HPR3 by lia.
    replace (ret_pc (Z_to_bv 64 0x3caa4)) with (Z_to_bv 64 0x3caa4) by (symmetry; rpc).
    rewrite (lb_remove_head bufp A cap [] ltac:(cbn; constructor; [intros []| constructor])) in HEAP3, HPR3.
    assert (BA3 : BASE' m3) by (eapply (BASE_heap sp0 argv envp uid TID); [exact BA1| exact HPR3| exact MI3| unfold LO; exact ST3| exact AUX3| exact HEAP3]).
    assert (EX3 : EXTRA m3 s2) by (eapply (EXTRA_heap sp0); [exact HPR3| exact SOE3| exact EX1]).
    pose proof BA3 as (ST4 & MI4 & ES4 & _). pose proof EX3 as (SOF4 & SE4 & _).
    apply implM_ret. unfold RQEXIT.
    eapply (main_return 2 s2 []); [lia| eapply (MFRAME_heap sp0 argv); [exact HPR3| exact FR1]| exact ST4| exact ES4| exact HEAP3| exact SOF4| apply stderr_wfile0_file; exact SE4| exact MI4].
  Qed.

  Lemma phaseC : forall bufp content s ms,
    RDONE' bufp content s ms ->
    (forall DATA A cap cw L cfg sc s1 ms1, content = map bv_unsigned DATA -> RUN0 bufp A cap DATA cw L cfg sc s1 ms1 ->
       implM usegs (main_tail bufp cw cfg (skipn (Z.to_nat (6 + L)) content)) s1 RQEXIT ms1) ->
    implM usegs (main_rest bufp content) s RQEXIT ms.
  Proof.
    intros bufp content s ms RD K.
    destruct RD as (x1 & t0 & t1 & t2 & a0 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & x23 & t3 & t4 & t5 & t6 & F & fc & mm & A & cap & P1v & fd & DATA & junk & errv
                    & -> & HC & BU & FR & BA & EX & ERR & FRM).
    pose proof (sp_facts sp0 VSP CEIL) as SF. unfold LO in SF. try (pose proof alloc_ceiling_range as CEIL_RANGE).
    pose proof BA as (ST & MI & ES & AUX & SSP & LXS & IMG). unfold LO in ST. pose proof ERR as ERR0. unfold RMallocRep.RERRNO in ERR. pose proof FR as FR0. unfold MFRAME in FR.
    pose proof BU as (P0 & HA & BLK & [CAPR CAPK] & LENR & BR). unfold MAX_INPUT in CAPR.
    pose proof BR as (BR1 & BR2 & BR3 & BR4 & BR5). try (pose proof alloc_ceiling_range as CEIL_RANGE).
    assert (LENZ : zlength content = Z.of_nat (length DATA)) by (rewrite HC; unfold zlength; rewrite length_map; reflexivity).
    pose proof BLK as BLKB. apply (proj1 (rw_cells_app _ _ _ [CB (length DATA) DATA] _)) in BLKB. destruct BLKB as [BLKB _].
    apply rw_cells_bytes_at in BLKB. cbn [cells_bytes cbytes app] in BLKB. rewrite app_nil_r in BLKB.
    unfold main_rest. rewrite LENZ. unfold HDR_MIN.
    remember (length DATA) as nD eqn:HnD.
    pose proof LXS as (G1 & G2 & _). unfold LX_GOT_STDERR, LX_STDERR_PTR, LX_STDERR_FILE in G1, G2. cbv delta [MallocRep.wz] in G1, G2.
    unfold implM. iprefix. zstep. zstep. if_cases K0; zify_cond K0.
    {
      replace (Z.of_nat nD <? 6) with true by (symmetry; apply Z.ltb_lt; lia). cbv iota.
      zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. apply evt_done.
      lazymatch goal with |- impl _ _ (?tm _) _ ?msx => change (implM usegs tm s RQEXIT msx) end.
      cbn [io_diag io io_S].
      eapply (diagC_exit DShortHdr s_short S_SHORT); [reflexivity| apply s_short_ro| reflexivity| apply lit_range
        | unfold S_SHORT; lia| unfold S_SHORT; lia| exact P0| exact EX| exact FR0| exact BA| exact ERR0]. }

    replace (Z.of_nat nD <? 6) with false by (symmetry; apply Z.ltb_ge; lia). cbv iota.
    destruct (list6 DATA ltac:(lia)) as (d0 & d1 & d2 & d3 & d4 & d5 & rest & ED). subst DATA. subst content.
    pose proof (byte_range d0) as Rd0. pose proof (byte_range d1) as Rd1. pose proof (byte_range d2) as Rd2.
    rewrite le16_cons.
    remember (bv_unsigned d0 + bv_unsigned d1 * 256) as cw eqn:Ecw.
    assert (RL : 0 <= Z.land cw 32767 <= cw) by (rewrite land15_mod; Z.div_mod_to_equations; lia).
    pose proof (u8ro_read usegs mm _ _ 1 d1 (wa (A + 1)) BLKB eq_refl ltac:(lia) eq_refl) as R1.
    zstep. clear R1. cbv beta.
    pose proof (u8ro_read usegs mm _ _ 0 d0 (wa (A + 0)) BLKB eq_refl ltac:(lia) eq_refl) as R0.
    zstep. clear R0. cbv beta.

    zstep. zstep. zstep.
    replace (bv_unsigned (sxb d1)) with ((sx8 (bv_unsigned d1)) mod 2^64) by (unfold sxb; rewrite Z_to_bv_unsigned, signed_byte; reflexivity).
    rewrite (cfg15_Z _ _ Rd0 Rd1). rewrite <- Ecw.
    remember (Z.land cw 32767) as L eqn:EL.
    zstep. zstep. if_cases K1; zify_cond K1.
    {
      replace (Z.of_nat nD <? 6 + L) with true by (symmetry; apply Z.ltb_lt; lia). cbv iota.
      zstep. zstep. zstep. zstep. zstep. zstep. zstep. apply evt_done.
      lazymatch goal with |- impl _ _ (?tm _) _ ?msx => change (implM usegs tm s RQEXIT msx) end.
      cbn [io_diag io io_S].
      eapply (diagC_exit DCfgOverrun s_over S_OVER); [reflexivity| apply s_over_ro| reflexivity| apply lit_range
        | unfold S_OVER; lia| unfold S_OVER; lia| exact P0| exact EX| exact FR0| exact BA| exact ERR0]. }
    replace (Z.of_nat nD <? 6 + L) with false by (symmetry; apply Z.ltb_ge; lia). cbv iota.
    zstep. zstep.

    destruct (skipn4 (d0 :: d1 :: d2 :: d3 :: d4 :: d5 :: rest) (Z.to_nat (2 + L)) ltac:(cbn [length] in *; lia)) as (q0 & q1 & q2 & q3 & rest' & EQ4).
    pose proof (byte_range q0) as Rq0. pose proof (byte_range q1) as Rq1. pose proof (byte_range q2) as Rq2. pose proof (byte_range q3) as Rq3.
    assert (QB : bytes_at usegs mm (A + 2 + L) (q0 :: q1 :: q2 :: q3 :: rest')).
    { rewrite <- EQ4. rewrite <- (firstn_skipn (Z.to_nat (2 + L)) (d0 :: d1 :: d2 :: d3 :: d4 :: d5 :: rest)) in BLKB.
      apply bytes_at_app in BLKB. destruct BLKB as [_ X]. rewrite length_firstn in X.
      replace (A + Z.of_nat (Nat.min (Z.to_nat (2 + L)) (length (d0 :: d1 :: d2 :: d3 :: d4 :: d5 :: rest)))) with (A + 2 + L) in X by (cbn [length] in *; lia). exact X. }
    assert (SH1 : 0 <= Z.shiftl (bv_unsigned q1) 8 < 2^64) by (rewrite Z.shiftl_mul_pow2 by lia; lia).
    assert (SH2 : 0 <= Z.shiftl (bv_unsigned q2) 16 < 2^64) by (rewrite Z.shiftl_mul_pow2 by lia; lia).
    assert (SH3 : 0 <= Z.shiftl (bv_unsigned q3) 24 < 2^64) by (rewrite Z.shiftl_mul_pow2 by lia; lia).
    pose proof (u8ro_read usegs mm _ _ 1 q1 (wa (A + 2 + L + 1)) QB eq_refl ltac:(lia) eq_refl) as R1.
    zstep. clear R1. cbv beta.
    pose proof (u8ro_read usegs mm _ _ 0 q0 (wa (A + 2 + L)) QB eq_refl ltac:(lia) ltac:(unfold wa; f_equal; lia)) as R0.
    zstep. clear R0. cbv beta.
    pose proof (u8ro_read usegs mm _ _ 2 q2 (wa (A + 2 + L + 2)) QB eq_refl ltac:(lia) eq_refl) as R2.
    zstep. clear R2. cbv beta.
    pose proof (u8ro_read usegs mm _ _ 3 q3 (wa (A + 2 + L + 3)) QB eq_refl ltac:(lia) eq_refl) as R3.
    zstep. clear R3. cbv beta.
    zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep.

    zstep. zstep.
    replace (ret_pc (Z_to_bv 64 0x3ca08)) with (Z_to_bv 64 0x3ca08) by (symmetry; rpc).
    apply evt_done.
    lazymatch goal with |- impl _ _ (?tm _) _ ?msx => change (implM usegs tm s RQEXIT msx) end.
    unfold alloc_init. apply implM_retb.
    replace (Z_to_bv 64 (A + 2 + L + 4)) with (Z_to_bv 64 (A + 6 + L)) by (f_equal; lia).
    replace (Z_to_bv 64 (Z.of_nat nD + - L + -6)) with (Z_to_bv 64 (Z.of_nat (length (d0 :: d1 :: d2 :: d3 :: d4 :: d5 :: rest)) - 6 - L)) by (f_equal; lia).
    replace (sxb d1) with (Z_to_bv 64 (sx8 (bv_unsigned d1))) by (unfold sxb; rewrite signed_byte; reflexivity).
    eapply (K (d0 :: d1 :: d2 :: d3 :: d4 :: d5 :: rest) A cap cw L _ (sx8 (bv_unsigned d1))); [reflexivity|].
    unfold RUN0. do 20 eexists. exists junk, errv. split; [reflexivity|].
    split.
    { unfold HDR. cbn [length] in *. rewrite le16_cons, znth2_cons. unfold MAX_INPUT.
      split; [lia|]. split; [lia|]. split; [lia|]. split; [exact BR|]. split; [lia|]. split; [exact EL|].
      split; [rewrite EL, land15_mod; Z.div_mod_to_equations; lia|]. split; [lia|]. split; [exact Ecw|]. split; [reflexivity|].
      split; [destruct (0 <? L); lia|].
      split; [unfold sx8; destruct (Z.ltb_spec (bv_unsigned d1) 128); lia|].
      rewrite Ecw, (testbit15 _ _ Rd0 Rd1). unfold sx8.
      destruct (Z.ltb_spec (bv_unsigned d1) 128); [rewrite (proj2 (Z.leb_gt _ _)) by lia; symmetry; apply Z.ltb_ge; lia | rewrite (proj2 (Z.leb_le _ _)) by lia; symmetry; apply Z.ltb_lt; lia]. }
    split; [exact P0|]. split; [rewrite HnD in BLK; exact BLK|]. split; [exact FR0|]. split; [exact BA|]. split; [exact EX|]. split; [exact ERR0| exact FRM].
  Qed.
End C.
End WithCeiling0.
