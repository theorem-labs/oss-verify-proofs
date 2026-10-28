(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation Strings.String.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP Agree MonadX Ceiling.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.U0.P0 Require Import Segs.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.U0.Malloc Require Import MallocBlocks MallocTree MallocHINV Malloc_iface.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.Lib Require Import InitStack.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.Malloc Require Import InitMem.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.P0 Require Import Startup_lib.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.U0.P0 Require Import Segs RMallocRep RMallocTree RMalloc_iface.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.U0.P0 Require Import Stdio_base Printf_lib Startup RefImpl F_printf_iface Stdio_iface Stdio_init F_printf_diag RDriver_lib RDriver_kit RDriver_ctx RF_main_A RF_main_B1 RF_main_B4.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.U0.P0 Require Import F_atexit.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.U0.P0 Require Segs RMalloc_ifaceP.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.U0.P0 Require Segs F_memset F_memcpy F_strlen.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.Spec Require Import Prelim STree Malloc Monad Stdio Driver Prog.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Open Scope mspec_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Ltac ua := idtac.
Ltac rpc := apply ret_pc_even; [lia| reflexivity].

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
Lemma le32_cons : forall q0 q1 q2 q3 (r : list byte),
  le32 (map bv_unsigned (q0 :: q1 :: q2 :: q3 :: r)) = bv_unsigned q0 + bv_unsigned q1 * 256 + bv_unsigned q2 * 65536 + bv_unsigned q3 * 16777216.
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

Lemma bm_Z : forall q0 q1 q2 q3, 0 <= q0 < 256 -> 0 <= q1 < 256 -> 0 <= q2 < 256 -> 0 <= q3 < 256 ->
  (Z.lor (Z.lor (Z.shiftl q1 8) q0) (Z.lor (Z.shiftl q2 16) (Z.land (bv_swrap 32 (Z.shiftl q3 24)) 18446744073709551615))) mod 2^32
  = q0 + q1 * 256 + q2 * 65536 + q3 * 16777216.
Proof.
  intros q0 q1 q2 q3 H0 H1 H2 H3.
  rewrite !Z.shiftl_mul_pow2 by lia.
  change 18446744073709551615 with (Z.ones 64). rewrite Z.land_ones by lia.
  assert (C3 : exists c3, (c3 = q3 \/ c3 = q3 + 2^40 - 2^8) /\ bv_swrap 32 (q3 * 2 ^ 24) mod 2 ^ 64 = c3 * 2^24).
  { unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus. cbn [Z.of_N N.div].
    change (2^32) with 4294967296 in *. change (Z.pow_pos 2 32) with 4294967296. change (4294967296 / 2) with 2147483648.
    destruct (Z.lt_ge_cases q3 128).
    - exists q3. split; [lia|]. rewrite (Z.mod_small (q3 * 2^24 + 2147483648)) by lia. rewrite Z.add_simpl_r. apply Z.mod_small. lia.
    - exists (q3 + 2^40 - 2^8). split; [lia|].
      replace ((q3 * 2 ^ 24 + 2147483648) mod 4294967296) with (q3 * 2 ^ 24 + 2147483648 - 4294967296) by (Z.div_mod_to_equations; lia).
      Z.div_mod_to_equations. lia. }
  destruct C3 as (c3 & Hc3 & ->).
  rewrite (Z.lor_comm (q2 * 2^16) (c3 * 2^24)). rewrite (lor_mul_add (q2 * 2^16) c3 24) by lia.
  rewrite (lor_mul_add q0 q1 8) by lia.
  replace (q2 * 2 ^ 16 + c3 * 2 ^ 24) with ((q2 + c3 * 2^8) * 2^16) by lia.
  rewrite (Z.lor_comm (q0 + q1 * 2^8)). rewrite (lor_mul_add (q0 + q1 * 2^8) (q2 + c3 * 2^8) 16) by lia.
  destruct Hc3 as [-> | ->]; Z.div_mod_to_equations; lia.
Qed.

Section C.
  Context {HGW : HasGuard} {HCEIL : HasCeiling}.
  Variables (sp0 : word) (argv envp : list (list byte)) (uid hw : word) (rnd : EntryDraw) (arg0 arg1 : list byte) (TID : Z)
            (MPAD : list byte) (S4 S5 S6 S7 S8 S9 S10 S11 : word).
  Hypothesis VSP : valid_sp sp0.
  Hypothesis CEIL : alloc_ceiling = LO sp0.
  Hypothesis VARGV : valid_argv argv.
  Hypothesis VENVP : valid_envp envp.
  Hypothesis EARGV : argv = [arg0; arg1].
  Hypothesis HT : 0 < TID < 4194304.
  Hypothesis MALLOC : rmalloc_stmt.
  Hypothesis FREE : rfree_stmt.
  Hypothesis FPR : @fprintf_diag_stmt PState.
  Hypothesis EXK : exit_k_stmt.
  Hypothesis FWR : @fwrite_diag_stmt PState.
  Hypothesis TOW : towrite_stmt.

  Notation usp0 := (bv_unsigned sp0).
  Notation gpv := (Z_to_bv 64 0x10800).
  Notation tpv := (Z_to_bv 64 RATP).
  Notation IMGB := (build_stack_bytes rph sp0 argv envp uid hw rnd).
  Notation LO' := (LO sp0).
  Notation BASE' := (BASE sp0 argv envp uid hw rnd TID).
  Notation FRAME' mm := (MFRAME sp0 argv mm MPAD S7 S6 S5 S4).
  Notation RDONE' := (RDONE sp0 argv envp uid hw rnd TID MPAD S4 S5 S6 S7 S8 S9 S10 S11).
  Notation ioS := (io_S ps_so set_so_ps).
  Ltac hyps := first [exact VSP | exact CEIL | exact VARGV | exact VENVP | exact EARGV | exact HT | exact MALLOC | exact FREE | exact FPR | exact EXK | exact FWR | exact TOW].

  Notation GST pc x1 t0 t1 t2 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 t3 t4 t5 t6 F fc mm :=
    (MS (mkR x1 (Z_to_bv 64 (usp0 + -128)) gpv tpv t0 t1 t2 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 (Z_to_bv 64 RSV) (Z_to_bv 64 0) S8 S9 S10 S11 t3 t4 t5 t6)
        F (Z_to_bv 64 pc) fc None mm (seg_rom rsegs)).

  Definition main_tail (buf : bptr) (content : list Z) (cw L cfg : Z) : M PState at_parser :=
    let payload_len := zlength content - HDR_MIN - L in
    let calls := 1 + Z.land cfg 3 in
    copy <- (if 0 <? payload_len then
               p <- raw_malloc payload_len ;;
               mret (match p with None => None | Some p' => Some (Some p') end)
             else mret (Some None)) ;;
    match copy with
    | None => raw_free buf ;;; exit_k ioS (main_status (Z.testbit cw 15) 2)
    | Some owned => mret (mkAP buf content (Z.testbit cw 15) L calls owned)
    end.

  Definition main_rest (buf : bptr) (content : list Z) : M PState at_parser :=
    let len := zlength content in
    if len <? HDR_MIN then io_diag ioS DShortHdr ;;; raw_free buf ;;; exit_k ioS 2
    else
      let cfg_word := le16 content in
      let config_len := Z.land cfg_word 0x7fff in
      if len <? HDR_MIN + config_len then io_diag ioS DCfgOverrun ;;; raw_free buf ;;; exit_k ioS 2
      else
        let cfg := if 0 <? config_len then znth content 2 else 0 in
        main_tail buf content cfg_word config_len cfg.

  #[using="arg0 EARGV"] Lemma drv_pre_eq : drv_pre ioS raw_malloc raw_free RSV (argv_Z argv)
    = (ra <- read_all ioS raw_malloc raw_free RSV (map bv_unsigned arg1) ;;
       match ra with RdExit => exit_k ioS 2 | RdDone buf content => main_rest buf content end).
  Proof. unfold drv_pre, argv_Z. rewrite EARGV. reflexivity. Qed.

  Definition HDR (A cap : Z) (DATA : list byte) (cw L cfg sc : Z) : Prop :=
    6 + L <= Z.of_nat (length DATA) /\ Z.of_nat (length DATA) <= cap /\ cap <= MAX_INPUT /\ rblock_range A cap
    /\ 0 <= cw < 65536 /\ L = Z.land cw 32767 /\ 0 <= L < 32768 /\ L <= cw /\ cw = le16 (map bv_unsigned DATA)
    /\ cfg = (if 0 <? L then znth (map bv_unsigned DATA) 2 else 0) /\ 0 <= cfg < 256
    /\ -128 <= sc < 128 /\ (Z.testbit cw 15 = (sc <? 0)).

  Definition RUN0 (bufp : bptr) (A cap : Z) (DATA : list byte) (cw L cfg sc : Z) (s : PState) (ms : machine_state) : Prop :=
    exists (x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (mm : mem)
           (junk : list byte) (errv : word),
      ms = GST 0x13c7c x1 t0 t1 t2 (Z_to_bv 64 (A + 2)) (Z_to_bv 64 A) a0 a1 a2 a3 a4 a5 a6 a7
               (Z_to_bv 64 L) (Z_to_bv 64 (A + 6 + L)) (Z_to_bv 64 (Z.of_nat (length DATA) - 6 - L)) (Z_to_bv 64 sc) t3 t4 t5 t6 F fc mm
      /\ HDR A cap DATA cw L cfg sc
      /\ RHEAP s [(bufp, A, cap)] mm /\ ps_so s = stdout_init /\ ps_fa s = (0, 0)
      /\ rw_cells rsegs mm A [CB (length DATA) DATA; CB (Z.to_nat (cap - Z.of_nat (length DATA))) junk]
      /\ FRAME' mm /\ BASE' mm /\ CJ0 mm /\ rw_cells rsegs mm RERRNO [C4 errv] /\ frm0 fc.

  #[using="Type"] Lemma RUN0_atx : forall bufp A cap DATA cw L cfg sc s ms,
    RUN0 bufp A cap DATA cw L cfg sc s ms -> atx_state false (ms_mem ms).
  Proof.
    intros bufp A cap DATA cw L cfg sc s ms R.
    destruct R as (x1 & t0 & t1 & t2 & a0 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & F & fc & mm & junk & errv
                   & -> & _ & _ & _ & _ & _ & _ & _ & CJ & _ & _).
    unfold CJ0 in CJ. exact (proj2 (proj2 (proj2 (proj2 CJ)))).
  Qed.

  #[using="VSP CEIL HT FREE EXK FWR TOW"] Lemma diagC_exit : forall (d : diag_msg) (msg : list Z) (PA : Z) (s : PState) (bufp : bptr) (A cap : Z) (Q : at_parser (ptr:=bptr) -> PState -> machine_state -> Prop)
      x1 t0 t1 t2 x14 x15 x16 x17 x18 x19 x20 x21 t3 t4 t5 t6 (F : bvmap 5 word) (fc : bv 32) (mm : mem) (errv : word),
    s_diag (St:=PState) d = stderr_fwrite msg -> ro_bytes_b rsegs PA (zb msg) = true -> zlength msg = 31 -> Forall (fun c => 0 <= c < 256) msg ->
    0x10000 <= PA -> PA + 31 <= 0x2a000 ->
    RHEAP s [(bufp, A, cap)] mm -> ps_so s = stdout_init -> FRAME' mm -> BASE' mm -> rw_cells rsegs mm RERRNO [C4 errv] ->
    implM rsegs (io_diag ioS d ;;; raw_free bufp ;;; exit_k ioS 2) s Q
      (GST 0x13d0c x1 t0 t1 t2 (Z_to_bv 64 2) (Z_to_bv 64 A) (Z_to_bv 64 PA) (Z_to_bv 64 31) (Z_to_bv 64 1) (Z_to_bv 64 0x2b480) x14 x15 x16 x17 x18 x19 x20 x21 t3 t4 t5 t6 F fc mm).
  Proof.
    intros until errv. intros ED RO ML RNG LOA HIA P0 SO FR BA ERR.
    pose proof (sp_facts sp0 VSP CEIL) as SF. unfold LO in SF.
    pose proof BA as (ST & MI & RS & AUX & IMG & SE & SOF & RSS). unfold LO in ST. unfold RERRNO in ERR. unfold MFRAME in FR.
    pose proof (RMalloc_ifaceP.RHEAP_block_range_proof _ _ _ (bufp, A, cap) P0 ltac:(left; reflexivity)) as BR. cbn [blk_addr blk_size fst snd] in BR.
    pose proof BR as (BR1 & BR2 & BR3 & BR4 & BR5). idtac.
    cbn [io_diag io_S]. rewrite ED.
    unfold implM. iprefix. zstep. apply evt_done.
    lazymatch goal with |- impl _ _ (?tm _) _ ?msx => change (implM rsegs tm s Q msx) end.
    eapply implM_bind.
    { eapply (FWR) with (lo := usp0 - 8388608) (s := msg);
        [exact TOW| exact SE| rewrite unsigned_lit by lia; apply rodata_bytes; [exact MI| exact RO| lia| lia]
        | exact RNG | rewrite ML; lia| rewrite ML; reflexivity| reflexivity| reflexivity
        | rewrite unsigned_lit by lia; exact ST
        | rewrite unsigned_lit by lia; unfold FWRITE_DEPTH; lia| unfold GLOBALS_TOP; lia
        | rewrite unsigned_lit by lia; lia
        | rewrite !unsigned_lit by lia; lia
        | rewrite !unsigned_lit by lia; lia
        | rewrite !unsigned_lit by lia; lia
        | apply (RHEAP_ssp _ _ _ P0)| exact MI]. }
    cbv beta. intros [] st' ms' PO.
    destruct PO as (u0 & u1 & u2 & b0 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & m1 & -> & MUc & WMc & MI1 & ST1 & SEW & SSP1 & ->).
    ua. rewrite !unsigned_lit in MUc by lia. rewrite !unsigned_lit in ST1 by lia.
    replace (ret_pc (Z_to_bv 64 0x13d10)) with (Z_to_bv 64 0x13d10) by (symmetry; rpc).
    pose proof (agree_on_of_munch rsegs _ _ _ MUc WMc) as AG.
    assert (OUT : forall a, (usp0 - 128 <= a /\ ~ (0x2b480 <= a < 0x2b480 + 232)) -> (fun a0 : Z => outside [(usp0 - 8388608, usp0 + -128); (0x2b480, 0x2b480 + 232)] a0) a).
    { intros a Ha. cbn. lia. }
    assert (OUT2 : forall a, (0x10000 <= a < 0x5d000 /\ ~ (0x2b480 <= a < 0x2b480 + 232)) -> (fun a0 : Z => outside [(usp0 - 8388608, usp0 + -128); (0x2b480, 0x2b480 + 232)] a0) a).
    { intros a Ha. cbn. lia. }
    apply (rw_cells_agree rsegs _ _ _ _ _ AG) in FR; [| intros a Ha; apply OUT; cbn in Ha; lia].
    apply (rw_cells_agree rsegs _ _ _ _ _ AG) in ERR; [| intros a Ha; apply OUT2; cbn in Ha; lia].
    assert (RS1 : RSTAT TID m1) by (eapply (RSTAT_agree TID _ _ _ AG); [intros a Ha; apply OUT2; unfold rstat_addr in Ha; lia| exact RS]).
    assert (SOF1 : stdout_file m1 stdout_init) by (eapply (stdout_file_agree _ _ _ _ AG); [intros a Ha; apply OUT2; unfold stdout_addr in Ha; lia| exact SOF]).
    assert (AUX1 : rauxv_ok m1 usp0).
    { eapply rauxv_ok_frame; [exact AUX| exact MUc| exact WMc|]. unfold RAUXV_CELL, RLIBC in *.
      constructor; [cbn [fst snd]; lia|]. constructor; [cbn [fst snd]; lia| constructor]. }
    assert (P1 : RHEAP s [(bufp, A, cap)] m1).
    { eapply RMalloc_ifaceP.RHEAP_frame_proof; [exact P0| exact MUc| exact WMc|].
      constructor; [left; cbn [fst snd]; lia|]. constructor; [| constructor].
      right; left. cbn [fst snd]. unfold RLIBC, RCTX, RSSP_GUARD, RGOT_SSP, RVMLOCK. lia. }
    clear MUc WMc AG OUT OUT2.

    unfold implM. iprefix. zstep. zstep. apply evt_done.
    lazymatch goal with |- impl _ _ (?tm _) _ ?msx => change (implM rsegs tm s Q msx) end.
    eapply implM_bind.
    { unfold rfree_stmt in FREE.
      eapply FREE with (lo := usp0 - 8388608) (B := usp0) (p := bufp) (A := A) (n := cap); try reflexivity; unfold RATP;
        rewrite ?(unsigned_lit 243744) by lia; rewrite ?(unsigned_lit (usp0 + -128)) by lia;
        first [ exact P1 | left; reflexivity | exact AUX1 | exact ST1 | exact MI1 | exact ERR | unfold RFREE_STACK; lia | lia ]. }
    cbv beta. intros [] s2 ms2 PO.
    destruct PO as (w0 & w1 & w2 & rb0 & d1 & d2 & d3 & d4 & d5 & d6 & d7 & w3 & w4 & w5 & w6 & m3 & -> & MI3 & ST3 & ERR3 & AUX3 & HPR3 & FAE3 & SOE3 & HEAP3).
    rewrite ?(unsigned_lit (usp0 + -128)) in ST3 by lia. rewrite ?(unsigned_lit (usp0 + -128)) in HPR3 by lia.
    replace (ret_pc (Z_to_bv 64 0x13d18)) with (Z_to_bv 64 0x13d18) by (symmetry; rpc).
    cbn [lb_remove filter bptr_eqb fst snd] in HEAP3, HPR3.
    eapply implM_evt; [| intros msx Hx; exact (EXK at_parser 2 _ Q msx Hx)].
    eapply (main_return sp0 argv TID VSP CEIL HT 2 s2).
    - unfold MFRAME. eapply rheap_pres_rw_cells; [exact HPR3| exact FR| left; cbn; lia].
    - unfold LO. first [exact ST3| replace (usp0 - 8388608) with (usp0 + -8388608) by lia; exact ST3].
    - eapply RSTAT_heap_pres; [exact HPR3| exact RS1].
    - rewrite bptr_eqb_refl in HEAP3 || idtac. exact HEAP3.
    - rewrite SOE3, SO. eapply stdout_file_heap_pres; [exact HPR3| exact SOF1].
    - apply stderr_wfile0_file. eapply stderr_wfile0_heap_pres; [exact HPR3| exact SEW].
    - exact MI3.
  Qed.

  #[using="VSP CEIL HT FREE EXK FWR TOW"] Lemma phaseC : forall bufp content s ms (Q : at_parser (ptr:=bptr) -> PState -> machine_state -> Prop),
    RDONE' bufp content s ms ->
    (forall DATA A cap cw L cfg sc s1 ms1, content = map bv_unsigned DATA -> RUN0 bufp A cap DATA cw L cfg sc s1 ms1 ->
       implM rsegs (main_tail bufp content cw L cfg) s1 Q ms1) ->
    implM rsegs (main_rest bufp content) s Q ms.
  Proof.
    intros bufp content s ms Q RD K.
    destruct RD as (x1 & t0 & t1 & t2 & a0 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & F & fc & mm & A & cap & P1v & fd & DATA & junk & errv
                    & -> & HC & BU & FR & BA & CJ & ERR & FRM).
    pose proof (sp_facts sp0 VSP CEIL) as SF. unfold LO in SF.
    pose proof BA as (ST & MI & RS & AUX & IMG & SE & SOF & RSS). unfold LO in ST. pose proof ERR as ERR0. unfold RERRNO in ERR. pose proof FR as FR0. unfold MFRAME in FR.
    pose proof BU as (P0 & FA0 & SO0 & BLK & [CAPR CAPK] & LENR & BR). unfold MAX_INPUT in CAPR.
    pose proof BR as (BR1 & BR2 & BR3 & BR4 & BR5). idtac.
    assert (LENZ : zlength content = Z.of_nat (length DATA)) by (rewrite HC; unfold zlength; rewrite length_map; reflexivity).
    pose proof BLK as BLKB. apply (proj1 (rw_cells_app _ _ _ [CB (length DATA) DATA] _)) in BLKB. destruct BLKB as [BLKB _].
    apply rw_cells_bytes_at in BLKB. cbn [cells_bytes cbytes app] in BLKB. rewrite app_nil_r in BLKB.
    unfold main_rest. rewrite LENZ. unfold HDR_MIN.
    remember (length DATA) as nD eqn:HnD.
    pose proof RS as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & G28 & GD0 & _ & _).
    unfold implM. iprefix. zstep. zstep. if_cases K0; zify_cond K0.
    {
      replace (Z.of_nat nD <? 6) with true by (symmetry; apply Z.ltb_lt; lia). cbv iota.
      zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. apply evt_done.
      lazymatch goal with |- impl _ _ (?tm _) _ ?msx => change (implM rsegs tm s Q msx) end.
      eapply (diagC_exit DShortHdr s_short S_SHORT); [reflexivity| apply s_short_ro| reflexivity| unfold s_short; apply Forall_app; split; [apply str_range| constructor; [lia| constructor]]
        | unfold S_SHORT; lia| unfold S_SHORT; lia| exact P0| exact SO0| exact FR0| exact BA| exact ERR0]. }

    replace (Z.of_nat nD <? 6) with false by (symmetry; apply Z.ltb_ge; lia). cbv iota.
    destruct (list6 DATA ltac:(lia)) as (d0 & d1 & d2 & d3 & d4 & d5 & rest & ED). subst DATA. subst content.
    pose proof (byte_range d0) as Rd0. pose proof (byte_range d1) as Rd1. pose proof (byte_range d2) as Rd2.
    rewrite le16_cons.
    remember (bv_unsigned d0 + bv_unsigned d1 * 256) as cw eqn:Ecw.
    assert (RL : 0 <= Z.land cw 32767 <= cw) by (rewrite land15_mod; Z.div_mod_to_equations; lia).
    pose proof (u8ro_read rsegs mm _ _ 1 d1 (wa (A + 1)) BLKB eq_refl ltac:(lia) eq_refl) as R1.
    zstep. clear R1. cbv beta.
    pose proof (u8ro_read rsegs mm _ _ 0 d0 (wa (A + 0)) BLKB eq_refl ltac:(lia) eq_refl) as R0.
    zstep. clear R0. cbv beta.

    zstep. zstep. zstep.
    replace (bv_unsigned (sxb d1)) with ((sx8 (bv_unsigned d1)) mod 2^64) by (unfold sxb; rewrite Z_to_bv_unsigned, signed_byte; reflexivity).
    rewrite (cfg15_Z _ _ Rd0 Rd1). rewrite <- Ecw.
    remember (Z.land cw 32767) as L eqn:EL.
    zstep. zstep. if_cases K1; zify_cond K1.
    {
      replace (Z.of_nat nD <? 6 + L) with true by (symmetry; apply Z.ltb_lt; lia). cbv iota.
      zstep. zstep. zstep. zstep. zstep. zstep. zstep. apply evt_done.
      lazymatch goal with |- impl _ _ (?tm _) _ ?msx => change (implM rsegs tm s Q msx) end.
      eapply (diagC_exit DCfgOverrun s_over S_OVER); [reflexivity| apply s_over_ro| reflexivity| unfold s_over; apply Forall_app; split; [apply str_range| constructor; [lia| constructor]]
        | unfold S_OVER; lia| unfold S_OVER; lia| exact P0| exact SO0| exact FR0| exact BA| exact ERR0]. }
    replace (Z.of_nat nD <? 6 + L) with false by (symmetry; apply Z.ltb_ge; lia). cbv iota.
    zstep. zstep.

    destruct (skipn4 (d0 :: d1 :: d2 :: d3 :: d4 :: d5 :: rest) (Z.to_nat (2 + L)) ltac:(cbn [length] in *; lia)) as (q0 & q1 & q2 & q3 & rest' & EQ4).
    pose proof (byte_range q0) as Rq0. pose proof (byte_range q1) as Rq1. pose proof (byte_range q2) as Rq2. pose proof (byte_range q3) as Rq3.
    assert (QB : bytes_at rsegs mm (A + 2 + L) (q0 :: q1 :: q2 :: q3 :: rest')).
    { rewrite <- EQ4. rewrite <- (firstn_skipn (Z.to_nat (2 + L)) (d0 :: d1 :: d2 :: d3 :: d4 :: d5 :: rest)) in BLKB.
      apply bytes_at_app in BLKB. destruct BLKB as [_ X]. rewrite length_firstn in X.
      replace (A + Z.of_nat (Nat.min (Z.to_nat (2 + L)) (length (d0 :: d1 :: d2 :: d3 :: d4 :: d5 :: rest)))) with (A + 2 + L) in X by (cbn [length] in *; lia). exact X. }
    assert (SH1 : 0 <= Z.shiftl (bv_unsigned q1) 8 < 2^64) by (rewrite Z.shiftl_mul_pow2 by lia; lia).
    assert (SH2 : 0 <= Z.shiftl (bv_unsigned q2) 16 < 2^64) by (rewrite Z.shiftl_mul_pow2 by lia; lia).
    assert (SH3 : 0 <= Z.shiftl (bv_unsigned q3) 24 < 2^64) by (rewrite Z.shiftl_mul_pow2 by lia; lia).
    pose proof (u8ro_read rsegs mm _ _ 1 q1 (wa (A + 2 + L + 1)) QB eq_refl ltac:(lia) eq_refl) as R1.
    zstep. clear R1. cbv beta.
    pose proof (u8ro_read rsegs mm _ _ 0 q0 (wa (A + 2 + L)) QB eq_refl ltac:(lia) ltac:(unfold wa; f_equal; lia)) as R0.
    zstep. clear R0. cbv beta.
    pose proof (u8ro_read rsegs mm _ _ 2 q2 (wa (A + 2 + L + 2)) QB eq_refl ltac:(lia) eq_refl) as R2.
    zstep. clear R2. cbv beta.
    pose proof (u8ro_read rsegs mm _ _ 3 q3 (wa (A + 2 + L + 3)) QB eq_refl ltac:(lia) eq_refl) as R3.
    zstep. clear R3. cbv beta.
    zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep.

    zstep. zstep. replace (ret_pc (Z_to_bv 64 0x13c7c)) with (Z_to_bv 64 0x13c7c) by (symmetry; rpc).
    apply evt_done.
    lazymatch goal with |- impl _ _ (?tm _) _ ?msx => change (implM rsegs tm s Q msx) end.
    replace (Z_to_bv 64 (A + 2 + L + 4)) with (Z_to_bv 64 (A + 6 + L)) by (f_equal; lia).
    replace (Z_to_bv 64 (Z.of_nat nD + - L + -6)) with (Z_to_bv 64 (Z.of_nat (length (d0 :: d1 :: d2 :: d3 :: d4 :: d5 :: rest)) - 6 - L)) by (f_equal; lia).
    replace (sxb d1) with (Z_to_bv 64 (sx8 (bv_unsigned d1))) by (unfold sxb; rewrite signed_byte; reflexivity).
    eapply (K (d0 :: d1 :: d2 :: d3 :: d4 :: d5 :: rest) A cap cw L _ (sx8 (bv_unsigned d1))); [reflexivity|].
    unfold RUN0. do 21 eexists. split; [reflexivity|].
    split.
    { unfold HDR. cbn [length] in *. rewrite le16_cons, znth2_cons. unfold MAX_INPUT.
      split; [lia|]. split; [lia|]. split; [lia|]. split; [exact BR|]. split; [lia|]. split; [exact EL|].
      split; [rewrite EL, land15_mod; Z.div_mod_to_equations; lia|]. split; [lia|]. split; [exact Ecw|]. split; [reflexivity|].
      split; [destruct (0 <? L); lia|].
      split; [unfold sx8; destruct (Z.ltb_spec (bv_unsigned d1) 128); lia|].
      rewrite Ecw, (testbit15 _ _ Rd0 Rd1). unfold sx8.
      destruct (Z.ltb_spec (bv_unsigned d1) 128); [rewrite (proj2 (Z.leb_gt _ _)) by lia; symmetry; apply Z.ltb_ge; lia | rewrite (proj2 (Z.leb_le _ _)) by lia; symmetry; apply Z.ltb_lt; lia]. }
    split; [exact P0|]. split; [exact SO0|]. split; [exact FA0|].
    split; [rewrite HnD in BLK; exact BLK|]. split; [exact FR0|]. split; [exact BA|]. split; [exact CJ|]. split; [exact ERR0| exact FRM].
  Qed.
End C.
