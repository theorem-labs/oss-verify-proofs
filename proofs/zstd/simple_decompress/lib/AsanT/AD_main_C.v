(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation Strings.String.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP MonadX Bytes InitMem.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import DrvAgree Keeps FmtFp F_fmt_fp_lib Printf_fmts Printf_pieces.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Spec Require Import Prelim STree Monad Stdio Driver Adapter Prog AsanCtrl AsanEmbed Harness ProgA AsanProgDeps.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.LibA Require Import ExecF ITreeA SysStepF Shadow.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.AsanT Require Import BImg ABase RtCells AProto AMalloc_iface AProg_kit AHarness_iface
     F_syscalls StdioFiles Stdio_kit Stdio_kit2 Stdio_iface F_printf_iface MonadF Strnlen_iface I_printf_formats I_read I_memcpy ADriver_iface AD_kit AD_ctx AD_diag AD_main_A AD_main_B1 AD_main_B2 AD_main_B3 AD_main_B4.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.LibA Require Import StepF.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import RunDraw.
Import ListNotations.
Set Keyed Unification.   (* [comment removed for export] *)
Import ITree.Exc.
Open Scope Z_scope.
Open Scope mspec_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.

Ltac rpc := apply ret_pc_even; [lia| reflexivity].
Ltac fix_ret := match goal with |- context [ret_pc (Z_to_bv 64 ?n)] =>
  lazymatch n with Zpos _ => idtac end; replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; rpc) end.
Notation wz := (Z_to_bv 64).
Notation gpv := (Z_to_bv 64 0x10800).
Notation tpv := (Z_to_bv 64 ATP).





Section CANSEC1. Context {rc : runConstT}.
Lemma byte_range : forall b : byte, 0 <= bv_unsigned b < 256.
Proof. intros b. pose proof (bv_unsigned_in_range 8 b) as R. unfold bv_modulus in R. cbn in R. lia. Qed.

(* [comment removed for export] *)
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
(* [comment removed for export] *)
Lemma testbit15 : forall c0 c1, 0 <= c0 < 256 -> 0 <= c1 < 256 -> Z.testbit (c0 + c1 * 256) 15 = (128 <=? c1).
Proof.
  intros c0 c1 H0 H1. rewrite Z.testbit_eqb by lia. change (2 ^ 15) with 32768.
  replace ((c0 + c1 * 256) / 32768) with (c1 / 128) by (Z.div_mod_to_equations; nia).
  destruct (Z.leb_spec 128 c1).
  - replace (c1 / 128) with 1 by (Z.div_mod_to_equations; nia). reflexivity.
  - replace (c1 / 128) with 0 by (Z.div_mod_to_equations; nia). reflexivity.
Qed.

(* [comment removed for export] *)
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

(* [comment removed for export] *)
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

(* [comment removed for export] *)
Section C.
  (* [comment removed for export] *)
  Variable AI : AMallocIface.
  Notation CI := (aci AI).
  Variable rng_fs : alayout -> footprint -> Prop.
  Hypothesis rng_fs_mono : forall L R R', fp_le R R' -> rng_fs L R -> rng_fs L R'.
  Variables (usp TID : Z) (S0 S1 S2 S3 S4 S5 S6 S7 S8 S9 S10 S11 : word) (RSTK : region) (canary : word) (L : alayout).
  Hypothesis RSTK_lo : r_lo RSTK <= ALO usp.
  Hypothesis RSTK_hi : usp + -128 <= r_hi RSTK.
  Hypothesis RSTK_rlo : ATOP <= r_rlo RSTK.
  Hypothesis USP16 : usp mod 16 = 0.
  Hypothesis USPLO : ATOP + 8388608 <= usp.
  Hypothesis USPHI : usp + 24 <= 2^47.
  Hypothesis DRV_CI : forall iv, In iv drv_img_ranges -> In iv CI.
  Hypothesis CLI_CI : forall iv, In iv cli_img_ranges -> In iv CI.
  Hypothesis CI_WF : forall iv, In iv CI -> 0 <= fst iv.
  Hypothesis HT : 0 < TID < 4194304.
  Hypothesis SPG : usp = al_sp0 L.
  Hypothesis BOT : ATOP + 4096 <= ALO usp.
  Hypothesis DMALLOC : dmalloc_stmt AI.
  Hypothesis DFREE : dfree_stmt AI.
  Hypothesis DFREEN : dfree_null_stmt AI.
  Hypothesis ASHENV : ashenv_law AI.
  Hypothesis FUZZ : fuzz_oneA_stmt AI rng_fs.
  Hypothesis HSTRN : strnlen_a_stmt.
  Variables (argv : list (list byte)) (P0 P1 : Z) (slack0 slack1 : list byte) (RA0 RA1 : region).
  Hypothesis VARGV : valid_argv argv.
  Notation argc := (Z.of_nat (length argv)).
  Notation arg0 := (map bv_unsigned (nth 0 argv [])).
  Notation arg1 := (map bv_unsigned (nth 1 argv [])).
  (* [comment removed for export] *)
  Variable J8 : list byte.
  Notation ABASE' := (ABASE usp TID S0 S1 S2 S3 S4 S5 S6 S7 J8 RSTK canary).
  Notation AMFRAME' := (AMFRAME usp S0 S1 S2 S3 S4 S5 S6 S7 J8).
  Notation LO := (ALO usp).
  Notation RNGS' := (RNGS rng_fs usp RSTK L argv P0 P1 slack0 slack1 RA0 RA1).
  Notation AARGV' := (AARGV usp argv P0 P1 slack0 slack1 RA0 RA1).
  Let WOKo := WOK_outside usp USP16 USPLO USPHI.
  Let geoA' := geoA usp USP16 USPLO USPHI.
  (* [comment removed for export] *)
  Hypothesis UM_e48 : In [AMALLOC_PC; 0x825dc] (al_U L).
  Hypothesis UM_e9c : In [AMALLOC_PC; 0x82630] (al_U L).
  Hypothesis UF_ec0 : In [AFREE_PC; 0x82654] (al_U L).
  Hypothesis UF_ff0 : In [AFREE_PC; 0x82784] (al_U L).
  Hypothesis UM_14c : In [AMALLOC_PC; 0x828bc] (al_U L).
  Hypothesis UF_1a0 : In [AFREE_PC; 0x82950] (al_U L).
  Hypothesis UM0 : In [AMALLOC_PC] (al_U L).
  Hypothesis UF0 : In [AFREE_PC] (al_U L).
  (* [comment removed for export] *)
  Notation GST pc x1 t0 t1 t2 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 t3 t4 t5 t6 F fc mm :=
    (MS (mkR x1 (Z_to_bv 64 (usp + -128)) gpv tpv t0 t1 t2 (Z_to_bv 64 2) x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 S8 S9 S10 S11 t3 t4 t5 t6)
        F (Z_to_bv 64 pc) fc None mm (seg_rom bsegs)).
  (* [comment removed for export] *)

  Notation ioS := (ioA AAllocAsan).
  Notation BUF' := (BUF AI L).
  Notation RDONE' := (RDONE AI rng_fs usp TID S0 S1 S2 S3 S4 S5 S6 S7 S8 S9 S10 S11 RSTK canary L argv P0 P1 slack0 slack1 RA0 RA1 J8).
  Hypothesis ARGC2 : argc = 2.

  (* [comment removed for export] *)
  Definition RQEXIT (code : Z) (s : APS) (RNG : footprint) (ms : machine_state) : Prop := aat_exit code s RNG ms.

  (* [comment removed for export] *)
  Definition main_tail (buf : AsanCtrl.aptr) (cw cfg : Z) (payload : list Z) : @Monad.M APS Z :=
    status <- runA AAllocAsan cfg payload ;;
    status' <- (if Z.testbit cw 15 then
                  n <- alloc_countA AAllocAsan ;; mret (if n <? COUNT_MAX then n else COUNT_MAX)
                else mret status) ;;
    afree_M buf ;;;
    mret status'.

  Definition main_rest (buf : AsanCtrl.aptr) (content : list Z) : @Monad.M APS Z :=
    let len := zlength content in
    if len <? HDR_MIN then io_diag ioS DShortHdr ;;; afree_M buf ;;; mret 2
    else
      let cfg_word := le16 content in
      let config_len := Z.land cfg_word 0x7fff in
      if len <? HDR_MIN + config_len then io_diag ioS DCfgOverrun ;;; afree_M buf ;;; mret 2
      else
        let bitmap := le32 (skipn (Z.to_nat (2 + config_len)) content) in
        let payload := skipn (Z.to_nat (6 + config_len)) content in
        let cfg := if 0 <? config_len then znth content 2 else 0 in
        alloc_initA AAllocAsan bitmap ;;; main_tail buf cfg_word cfg payload.

  Lemma main_model_eq :
    main_model ioS amalloc_M afree_M ASTAGE (alloc_initA AAllocAsan) (runA AAllocAsan) (alloc_countA AAllocAsan) (argv_Z argv)
    = (ra <- read_all ioS amalloc_M afree_M ASTAGE arg1 ;;
       match ra with RdExit => mret 2 | RdDone buf content => main_rest buf content end).
  Proof. unfold main_model, argv_Z. rewrite length_map. rewrite ARGC2. cbn [Z.eqb Pos.eqb negb]. rewrite (nth_argv_Z argv 1). reflexivity. Qed.

  (* [comment removed for export] *)
  Definition HDR (A cap : Z) (DATA : list byte) (cw Lc cfg sc : Z) : Prop :=
    6 + Lc <= Z.of_nat (length DATA) /\ Z.of_nat (length DATA) <= cap /\ cap <= MAX_INPUT /\ ablock_range A cap
    /\ 0 <= cw < 65536 /\ Lc = Z.land cw 32767 /\ 0 <= Lc < 32768 /\ Lc <= cw /\ cw = le16 (map bv_unsigned DATA)
    /\ cfg = (if 0 <? Lc then znth (map bv_unsigned DATA) 2 else 0) /\ 0 <= cfg < 256
    /\ -128 <= sc < 128 /\ (Z.testbit cw 15 = (sc <? 0)).

  (* [comment removed for export] *)
  Notation GST8 pc x1 t0 t1 t2 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 t3 t4 t5 t6 F fc mm :=
    (MS (mkR x1 (Z_to_bv 64 (usp + -128)) gpv tpv t0 t1 t2 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 S8 S9 S10 S11 t3 t4 t5 t6)
        F (Z_to_bv 64 pc) fc None mm (seg_rom bsegs)).

  (* [comment removed for export] *)
  Definition RUN0 (bufp : AsanCtrl.aptr) (A cap : Z) (DATA : list byte) (cw Lc cfg sc : Z) (s : APS) (RNG : footprint) (ms : machine_state) : Prop :=
    exists (x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 x23 : word) (F : bvmap 5 word) (fc : bv 32) (mm : amem) (junk : list byte),
      ms = GST8 0x826e8 x1 t0 t1 t2 (Z_to_bv 64 (A + 2)) (Z_to_bv 64 A) a0 a1 a2 a3 a4 a5 a6 a7
               (Z_to_bv 64 Lc) (Z_to_bv 64 (A + 6 + Lc)) (Z_to_bv 64 (Z.of_nat (length DATA) - 6 - Lc)) (Z_to_bv 64 sc) (Z_to_bv 64 ASTAGE) x23 t3 t4 t5 t6 F fc mm
      /\ HDR A cap DATA cw Lc cfg sc
      /\ BUF' mm s RNG bufp A cap DATA junk
      /\ ABASE' stdout_init mm /\ AARGV' mm /\ RNGS' RNG /\ frm0 fc.

  (* [comment removed for export] *)
  Lemma diagC_exit : forall (d : diag_msg) (msg : list Z) (PA : Z) (s : APS) RNG (bufp : AsanCtrl.aptr) (A cap : Z) (DATA junk : list byte)
      x1 t0 t1 t2 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 t3 t4 t5 t6 (F : bvmap 5 word) (fc : bv 32) (mm : amem),
    s_diag (St:=APS) d = stderr_fwrite msg -> ro_bytes_b bsegs PA (zb msg) = true -> zlength msg = 31 -> Forall (fun c => 0 <= c < 256) msg ->
    0x10000 + 64 <= PA -> PA + 31 + 64 <= 0x210c0 ->
    BUF' mm s RNG bufp A cap DATA junk -> ABASE' stdout_init mm -> RNGS' RNG ->
    implMA RNG (s_diag d ;;; afree_M bufp ;;; mret 2) s RQEXIT
      (GST8 0x82778 x1 t0 t1 t2 (Z_to_bv 64 2) (Z_to_bv 64 A) (Z_to_bv 64 PA) (Z_to_bv 64 31) (Z_to_bv 64 1) (Z_to_bv 64 RSTDERR) x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 t3 t4 t5 t6 F fc mm).
  Proof.
    intros until mm. intros ED RO ML MRNG LOA HIA BU BA RG.
    pose proof geoA' as (G1 & G2 & G3 & G4 & G5). unfold KHIGH in *.
    destruct BU as (P0h & SO0 & RK & HA & BLK & [CAPR CAPK] & LENR & BR & RGA & RGAS). pose proof BR as (BR1 & BR2 & BR3 & BR4).
    pose proof BA as (ST & MI & FR & AS & SE & GU & TR & HI & ROD & RCS & RCB & RSG & [errv ERR] & SOF). unfold AMFRAME in FR.
    pose proof RG as (RGstk & RGtop & RGimg & RGimsh & RGfs & RRS & RRF & RRB & RG0 & _).
    destruct (drv_got_of_aheap AI _ _ _ _ _ P0h) as (_ & _ & _ & GSSP).
    rewrite ED.
    apply implMA_from_evtF. zstep. apply evtF_done.
    eapply implMA_bind.
    { apply implMA_of_implAM.
      eapply (afwrite_diag_proof RNG) with (lo := LO) (s := msg) (A := PA); rewrite ?unsigned_lit by lia;
        first [ exact SE | reflexivity | exact ST | exact MI | exact ROD | exact RGimg | exact RRF | exact MRNG
              | split; [exact GSSP| exact GU] | exact (ASHENV _ _ _ _ _ P0h) | idtac ].
      all: first [ apply fmt_bytes_at; [exact MI| exact RO| lia| rewrite ML; lia]
                 | rewrite ML; lia
                 | rewrite ML; reflexivity
                 | lia
                 | unfold AFWRITE_DEPTH; lia | unfold KHIGH; lia
                 | eapply rng_sub'; [exact RGstk| lia] ]. }
    cbv beta. intros [] st' RNG' ms' [-> PO].
    destruct PO as (u0 & u1 & u2 & b0 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & m1 & -> & MU1 & WM1 & MI1 & ST1 & SEW & SSP1 & ->).
    rewrite ?unsigned_lit in MU1, ST1 by lia. fix_ret.
    assert (HW1 : Forall (WOK usp) [(LO, usp + -128); (RSTDERR, RSTDERR + 232)]) by (constructor; [left; cbn; lia| constructor; [right; right; left; cbn; split; reflexivity| constructor]]).
    assert (HP1 : AHEAP AI L RNG (aps_m s) [HB bufp A cap] m1).
    { eapply (AI_frame AI); [exact P0h| exact MU1| exact WM1|]. pose proof (AI_layout AI _ _ _ _ _ P0h) as (Y1 & Y2 & Y3 & Y4 & _). unfold ALO in *.
      constructor; [| constructor; [| constructor]]; cbn [fst snd].
      - left. left. lia.
      - left. right; left. exists (RSTDERR, RSTDERR + 232)%Z. split; [apply DRV_CI; unfold drv_img_ranges; cbn; tauto| cbn; lia]. }
    assert (BA1 : ABASE' stdout_init m1).
    { eapply (ABASE_munch usp TID S0 S1 S2 S3 S4 S5 S6 S7 J8 RSTK USP16 USPLO USPHI canary); [exact BA| exact HW1| exact MU1| exact WM1| exact MI1| exact ST1| exact SEW|].
      exists errv. eapply rw_cells_magree; [eapply magree_of_munch; [exact MU1| exact WM1]| exact ERR|]. intros a' Ha'. rewrite ?errno_addr_ATP in Ha'. cbn in Ha' |- *. lia. }
    pose proof BA1 as (ST1' & _ & FR1 & AS1 & SE1 & GU1 & TR1 & HI1 & ROD1 & RCS1 & RCB1 & RSG1 & [errv1 ERR1] & SOF1). unfold AMFRAME in FR1.
    clear MU1 WM1.
    (* [comment removed for export] *)
    apply implMA_from_evtF. zstep. zstep. apply evtF_done.
    eapply implMA_bind.
    { eapply (dfree_M AI DFREE L RNG) with (lo := LO) (p := bufp) (A := A) (n := cap); try reflexivity; rewrite ?(unsigned_lit (usp + -128)) by lia;
        first [ exact HP1 | left; reflexivity | exact MI1 | exact ST1 | exact BOT | unfold AFREE_STACK; lia | exact UF_ff0 | exact UF0 | exact RGtop | match goal with Hr : rng ?R ?l _ |- rng ?R ?l _ => eapply (rng_sub _ _ _ _ _ Hr); lia end | match goal with H : aps_ok _ _ |- aps_ok _ _ => exact H end | idtac ].
      all: rewrite ?unsigned_lit by lia; unfold AFREE_PC; lia. }
    cbv beta. intros [] s2 RNG2 ms3 [SOE3 PO].
    destruct PO as (LE2 & w0 & w1 & w2 & rb0 & d1 & d2 & d3 & d4 & d5 & d6 & d7 & w3 & w4 & w5 & w6 & m3 & -> & MI3 & ST3 & HPR3 & HSP3 & HEAP3).
    rewrite ?(unsigned_lit (usp + -128)) in ST3, HPR3, HSP3 by lia.
    fix_ret. cbn [aps_m aset_m fst snd] in HEAP3.
    pose proof (AI_hb_ids AI _ _ _ _ _ HP1) as ND.
    rewrite (lb_remove_headA bufp A cap [] ND) in HPR3, HEAP3.
    assert (BA3 : ABASE' stdout_init m3).
    { eapply (ABASE_after_dpost AI usp TID S0 S1 S2 S3 S4 S5 S6 S7 J8 RSTK RSTK_rlo USP16 USPLO USPHI DRV_CI CLI_CI canary);
        [exact HPR3| exact HSP3| exact HEAP3| exact MI3| exact ST3| exact BA1]. }
    pose proof BA3 as (_ & _ & FR3 & AS3 & SE3 & GU3 & _).
    assert (RG2' : RNGS' RNG2) by (eapply (RNGS_mono rng_fs rng_fs_mono); [exact LE2| exact RG]).
    pose proof RG2' as (RGstk2 & _ & RGimg2 & RGimsh2 & _ & _ & _ & _ & RG02 & _).
    apply implMA_ret. unfold RQEXIT.
    eapply (amain_return AI usp TID S0 S1 S2 S3 S4 S5 S6 S7 J8 USP16 USPLO USPHI canary);
      first [exact FR3 | exact ST3 | exact AS3 | exact HEAP3 | exact MI3 | exact HT | exact RGimg2 | exact RGimsh2 | exact RG02 | exact GU3 | idtac].
    - rewrite (aps_so_of_rest _ _ SOE3). cbn [aps_so aset_m]. rewrite SO0. destruct BA3 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & SOF3). exact SOF3.
    - apply stderr_wfile0_file. exact SE3.
    - eapply rng_sub'; [exact RGstk2| lia].
  Qed.

  (* [comment removed for export] *)
  Lemma phaseC : forall bufp content s RNG ms,
    RDONE' bufp content s RNG ms ->
    (forall DATA A cap cw Lc cfg sc s1 RNG1 ms1, content = map bv_unsigned DATA -> RUN0 bufp A cap DATA cw Lc cfg sc s1 RNG1 ms1 ->
       implMA RNG1 (main_tail bufp cw cfg (skipn (Z.to_nat (6 + Lc)) content)) s1 RQEXIT ms1) ->
    implMA RNG (main_rest bufp content) s RQEXIT ms.
  Proof.
    intros bufp content s RNG ms RD K.
    destruct RD as (x1 & t0 & t1 & t2 & a0 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & x23 & F & fc & mm & A & cap & fd & DATA & junk
                    & -> & HC & BU & BA & ARG & RG & FRM).
    pose proof geoA' as (G1 & G2 & G3 & G4 & G5). unfold KHIGH in *.
    pose proof BA as (ST & MI & FR & AS & SE & GU & TR & HI & ROD & RCS & RCB & RSG & [errv ERR] & SOF). unfold AMFRAME in FR.
    pose proof BU as (P0h & SO0 & RK & HA & BLK & [CAPR CAPK] & LENR & BR & RGA & RGAS). unfold MAX_INPUT in CAPR.
    pose proof BR as (BR1 & BR2 & BR3 & BR4).
    pose proof RG as (RGstk & RGtop & RGimg & RGimsh & RGfs & RRS & RRF & RRB & RG0 & _).
    assert (LENZ : zlength content = Z.of_nat (length DATA)) by (rewrite HC; unfold zlength; rewrite length_map; reflexivity).
    pose proof BLK as BLKB. apply (proj1 (rw_cells_app _ _ _ [CB (length DATA) DATA] _)) in BLKB. destruct BLKB as [BLKB _].
    apply rw_cells_bytes_at in BLKB. cbn [cells_bytes cbytes app] in BLKB. rewrite app_nil_r in BLKB.
    destruct (drv_got_of_aheap AI _ _ _ _ _ P0h) as (GSE & PSE & _ & GSSP). unfold AGOT_STDERRP, ASTDERRP in GSE, PSE.
    unfold main_rest. rewrite LENZ. unfold HDR_MIN.
    remember (length DATA) as nD eqn:HnD.
    apply implMA_from_evtF. zstep. zstep. if_cases K0; zify_cond K0.
    { (* [comment removed for export] *)
      replace (Z.of_nat nD <? 6) with true by (symmetry; apply Z.ltb_lt; lia). cbv iota.
      zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. apply evtF_done.
      cbn [io_diag ioA io_S].
      eapply (diagC_exit DShortHdr s_short AS_SHORT); [reflexivity| apply s_short_ro| reflexivity| unfold s_short; apply Forall_app; split; [apply str_range| constructor; [lia| constructor]]
        | unfold AS_SHORT; lia| unfold AS_SHORT; lia| exact BU| exact BA| exact RG]. }
    (* [comment removed for export] *)
    replace (Z.of_nat nD <? 6) with false by (symmetry; apply Z.ltb_ge; lia). cbv iota.
    destruct (list6 DATA ltac:(lia)) as (d0 & d1 & d2 & d3 & d4 & d5 & rest & ED). subst DATA. subst content.
    pose proof (byte_range d0) as Rd0. pose proof (byte_range d1) as Rd1. pose proof (byte_range d2) as Rd2.
    rewrite le16_cons.
    remember (bv_unsigned d0 + bv_unsigned d1 * 256) as cw eqn:Ecw.
    assert (RL : 0 <= Z.land cw 32767 <= cw) by (rewrite land15_mod; Z.div_mod_to_equations; lia).
    pose proof (u8ro_read bsegs mm _ _ 1 d1 (wa (A + 1)) BLKB eq_refl ltac:(lia) eq_refl) as R1.
    zstep. clear R1. cbv beta.
    pose proof (u8ro_read bsegs mm _ _ 0 d0 (wa (A + 0)) BLKB eq_refl ltac:(lia) eq_refl) as R0.
    zstep. clear R0. cbv beta.
    (* [comment removed for export] *)
    zstep. zstep. zstep.
    replace (bv_unsigned (sxb d1)) with ((sx8 (bv_unsigned d1)) mod 2^64) by (unfold sxb; rewrite Z_to_bv_unsigned, signed_byte; reflexivity).
    rewrite (cfg15_Z _ _ Rd0 Rd1). rewrite <- Ecw.
    remember (Z.land cw 32767) as Lc eqn:EL.
    zstep. zstep. if_cases K1; zify_cond K1.
    { (* [comment removed for export] *)
      replace (Z.of_nat nD <? 6 + Lc) with true by (symmetry; apply Z.ltb_lt; lia). cbv iota.
      zstep. zstep. zstep. zstep. zstep. zstep. zstep. apply evtF_done.
      cbn [io_diag ioA io_S].
      eapply (diagC_exit DCfgOverrun s_over AS_OVER); [reflexivity| apply s_over_ro| reflexivity| unfold s_over; apply Forall_app; split; [apply str_range| constructor; [lia| constructor]]
        | unfold AS_OVER; lia| unfold AS_OVER; lia| first [exact BU | rewrite <- HnD; exact BU | rewrite HnD in BU; exact BU]| exact BA| exact RG]. }
    replace (Z.of_nat nD <? 6 + Lc) with false by (symmetry; apply Z.ltb_ge; lia). cbv iota.
    zstep. zstep.
    (* [comment removed for export] *)
    destruct (skipn4 (d0 :: d1 :: d2 :: d3 :: d4 :: d5 :: rest) (Z.to_nat (2 + Lc)) ltac:(cbn [length] in *; lia)) as (q0 & q1 & q2 & q3 & rest' & EQ4).
    pose proof (byte_range q0) as Rq0. pose proof (byte_range q1) as Rq1. pose proof (byte_range q2) as Rq2. pose proof (byte_range q3) as Rq3.
    assert (QB : bytes_at bsegs mm (A + 2 + Lc) (q0 :: q1 :: q2 :: q3 :: rest')).
    { rewrite <- EQ4. rewrite <- (firstn_skipn (Z.to_nat (2 + Lc)) (d0 :: d1 :: d2 :: d3 :: d4 :: d5 :: rest)) in BLKB.
      apply bytes_at_app in BLKB. destruct BLKB as [_ X]. rewrite length_firstn in X.
      replace (A + Z.of_nat (Nat.min (Z.to_nat (2 + Lc)) (length (d0 :: d1 :: d2 :: d3 :: d4 :: d5 :: rest)))) with (A + 2 + Lc) in X by (cbn [length] in *; lia). exact X. }
    rewrite skipn_map, EQ4, le32_cons.
    remember (bv_unsigned q0 + bv_unsigned q1 * 256 + bv_unsigned q2 * 65536 + bv_unsigned q3 * 16777216) as BM eqn:EBM.
    assert (SH1 : 0 <= Z.shiftl (bv_unsigned q1) 8 < 2^64) by (rewrite Z.shiftl_mul_pow2 by lia; lia).
    assert (SH2 : 0 <= Z.shiftl (bv_unsigned q2) 16 < 2^64) by (rewrite Z.shiftl_mul_pow2 by lia; lia).
    assert (SH3 : 0 <= Z.shiftl (bv_unsigned q3) 24 < 2^64) by (rewrite Z.shiftl_mul_pow2 by lia; lia).
    pose proof (u8ro_read bsegs mm _ _ 1 q1 (wa (A + 2 + Lc + 1)) QB eq_refl ltac:(lia) eq_refl) as R1.
    zstep. clear R1. cbv beta.
    pose proof (u8ro_read bsegs mm _ _ 0 q0 (wa (A + 2 + Lc)) QB eq_refl ltac:(lia) ltac:(unfold wa; f_equal; lia)) as R0.
    zstep. clear R0. cbv beta.
    pose proof (u8ro_read bsegs mm _ _ 2 q2 (wa (A + 2 + Lc + 2)) QB eq_refl ltac:(lia) eq_refl) as R2.
    zstep. clear R2. cbv beta.
    pose proof (u8ro_read bsegs mm _ _ 3 q3 (wa (A + 2 + Lc + 3)) QB eq_refl ltac:(lia) eq_refl) as R3.
    zstep. clear R3. cbv beta.
    zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep.
    (* [comment removed for export] *)
    zstep. apply evtF_done.
    eapply implMA_bind. { apply atarget_alloc_init_spec. }
    cbv beta. intros [] s' RNG' ms' (-> & -> & ->).
    fix_ret.
    replace (Z_to_bv 64 (A + 2 + Lc + 4)) with (Z_to_bv 64 (A + 6 + Lc)) by (f_equal; lia).
    replace (Z_to_bv 64 (Z.of_nat nD + - Lc + -6)) with (Z_to_bv 64 (Z.of_nat (length (d0 :: d1 :: d2 :: d3 :: d4 :: d5 :: rest)) - 6 - Lc)) by (f_equal; lia).
    replace (sxb d1) with (Z_to_bv 64 (sx8 (bv_unsigned d1))) by (unfold sxb; rewrite signed_byte; reflexivity).
    eapply (K (d0 :: d1 :: d2 :: d3 :: d4 :: d5 :: rest) A cap cw Lc _ (sx8 (bv_unsigned d1))); [reflexivity|].
    unfold RUN0. do 21 eexists. split; [reflexivity|].
    split.
    { unfold HDR. cbn [length] in *. rewrite le16_cons, znth2_cons. unfold MAX_INPUT.
      split; [lia|]. split; [lia|]. split; [lia|]. split; [exact BR|]. split; [lia|]. split; [exact EL|].
      split; [rewrite EL, land15_mod; Z.div_mod_to_equations; lia|]. split; [lia|]. split; [exact Ecw|]. split; [reflexivity|].
      split; [destruct (0 <? Lc); lia|].
      split; [unfold sx8; destruct (Z.ltb_spec (bv_unsigned d1) 128); lia|].
      rewrite Ecw, (testbit15 _ _ Rd0 Rd1). unfold sx8.
      destruct (Z.ltb_spec (bv_unsigned d1) 128); [rewrite (proj2 (Z.leb_gt _ _)) by lia; symmetry; apply Z.ltb_ge; lia | rewrite (proj2 (Z.leb_le _ _)) by lia; symmetry; apply Z.ltb_lt; lia]. }
    split; [first [exact BU | rewrite <- HnD; exact BU | rewrite HnD in BU; exact BU]|]. split; [exact BA|]. split; [exact ARG|]. split; [exact RG| exact FRM].
  Qed.
End C.
End CANSEC1.
