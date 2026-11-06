(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation Strings.String.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Common Require Import ShapeAlg ShapeAlgCfg.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import Tac Image ZBridge SysStep ITree ITreeCfg Nodes NodesCfg Decode Arr FP InitMem.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import Images.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Top Require Import ImplRz ImplRzCfg TrzNodesCfg TrzStdioCfg TrzLeafCfg ImplSplitCfg.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Agent Require Import MallocBlocks.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.MS Require Import Malloc_iface.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Spec Require Import Prelim STree Malloc Monad StdioBase Stdio FmtFp Driver RawAlloc MSafe MLive.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.U Require Import UMallocRep UMallocTree UMalloc_iface U_StartupLib U_Startup U_Exit UF_pad.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.R Require Import RF_stdio_lib.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.U Require Import UStdio_iface UF_printf_iface UStdio_init UF_syscalls UF_memcpy UF_fwritex_gen.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.R Require Import Printf_model.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.U Require Import UDrv_iface UDrv_ctx UDrv_kio UDrv_A UDrv_B UDrv_C UDrv_run UDrv_run2.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Ltac rpc := apply ret_pc_even; [lia| reflexivity].

(* [comment removed for export] *)
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
Proof. intros l H. destruct l as [|d0 [|d1 [|d2 [|d3 [|d4 [|d5 r]]]]]]; cbn in H; try lia. do 7 eexists. reflexivity. Qed.
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

Section D.
  Context {RC__ : OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib.RunCeiling.RunCeiling}.
  Variables (sp0 : word) (argv envp : list (list byte)) (uid hw : word) (rnd : EntryDraw) (arg0 arg1 : list byte) (TID : Z)
            (PAD : list byte) (S4 S5 S6 S7 S8 S9 S10 S11 : word).
  Hypothesis VSP : valid_sp sp0.
  Hypothesis RCSP : rc_sp = bv_unsigned sp0.          (* [comment removed for export] *)
  Hypothesis RCS : rc_secret = bv_unsigned (secret_of (at_random_bytes (ed_random rnd))).   (* [comment removed for export] *)
  Hypothesis EFIT : entry_stack_fits sp0 argv envp.   (* [comment removed for export] *)
  Hypothesis VARGV : valid_argv argv.
  Hypothesis VENVP : valid_envp envp.
  Hypothesis EARGV : argv = [arg0; arg1].
  Hypothesis HT : 0 < TID < 4194304.
  Variable HKG : HKG_T.
  Hypothesis DI : drv_iface HKG.
  Variable FS0 : Fs.Fs.
  Notation HK := (HKG (G_fs FS0)).

  Notation usp0 := (bv_unsigned sp0).
  Notation gpv := (Z_to_bv 64 0x10800).
  Notation tpv := (Z_to_bv 64 RATP).
  Notation IMGB := (build_stack_bytes rph sp0 argv envp uid hw rnd).
  Notation LO' := (LO sp0).
  Notation BASE' := (BASE sp0 argv envp uid hw rnd TID).
  Notation FRAME' mm := (MFRAME sp0 argv mm PAD S7 S6 S5 S4).

  (* [comment removed for export] *)
  Notation GST pc x1 t0 t1 t2 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x23 t3 t4 t5 t6 F fc mm :=
    (MS (mkR x1 (Z_to_bv 64 (usp0 + -128)) gpv tpv t0 t1 t2 (Z_to_bv 64 2) x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 (Z_to_bv 64 RSTAGE) x23 S8 S9 S10 S11 t3 t4 t5 t6)
        F (Z_to_bv 64 pc) fc None mm (seg_rom usegs)).

  Let DIR := di_run HKG DI.
  Hypothesis YF : yfuzz_rz_stmt HK.
  Notation RDBRK' := (RDBRK sp0 argv envp uid hw rnd TID PAD S4 S5 S6 S7 S8 S9 S10 S11 HKG FS0).
  Variables (P1v : Z) (pathb : list byte).

  (* [comment removed for export] *)
  Definition KEXIT (counting : bool) (status : Z) (so : stdout_st) : TSet :=
    ShapeAlg.t_emit (Wz 1 (fst (exit_flush_pure so)))
                    (t_exit (bv_and (Z_to_bv 64 (if counting then 0 else status)) (Z_to_bv 64 255)) FS0).
  Definition KDONE (FILE : list byte) : TSet :=
    if (length FILE <? 6)%nat then TDIE pieces_short_hdr stdout_init FS0
    else
      let b0 := bv_unsigned (nth 0 FILE (Z_to_bv 8 0)) in
      let b1 := bv_unsigned (nth 1 FILE (Z_to_bv 8 0)) in
      let L := (b0 + 256 * b1) mod 32768 in
      let counting := 128 <=? b1 in
      if (Z.of_nat (length FILE) <? 6 + L) then TDIE pieces_cfg_overrun stdout_init FS0
      else
        let PL := Z.of_nat (length FILE) - 6 - L in
        let calls := if L =? 0 then 1%nat else S (Z.to_nat (bv_unsigned (nth 2 FILE (Z_to_bv 8 0)) mod 4)) in
        ShapeAlg.t_emit (Wz 1 (fst (emits calls stdout_init))) (KEXIT counting 0 (snd (emits calls stdout_init))).

  Lemma KEXIT_nil : forall c st so, KEXIT c st so []. Proof. intros. apply ShapeAlg.t_emit_has_nil. Qed.
  Lemma KDONE_nil : forall FILE, KDONE FILE [].
  Proof.
    intros FILE. unfold KDONE. destruct (length FILE <? 6)%nat; [apply TDIE_nil|]. cbv zeta.
    destruct (_ <? _); [apply TDIE_nil|]. apply ShapeAlg.t_emit_has_nil.
  Qed.

  (* [comment removed for export] *)
  Lemma rz_fwrite_ret : forall (msg : list Z) (PA : Z) (s : PState) (bufp : bptr) (A cap : Z) mo
      x1 t0 t1 t2 x14 x15 x16 x17 x18 x19 x20 x21 x23 t3 t4 t5 t6 (F : bvmap 5 word) (fc : bv 32) (mm : mem) (errv : word),
    ro_bytes_b usegs PA (zb msg) = true -> zlength msg = 31 -> Forall (fun c => 0 <= c < 256) msg ->
    0x10000 <= PA -> PA + 31 <= 0x24000 ->
    HK s [(bufp, A, cap)] mm mo -> FRAME' mm -> BASE' mm -> rw_cells usegs mm RERRNO [C4 errv] -> m_fs mo = FS0 ->
    realizes_cfg acfg usegs (mkCfg (GST 0x136f0 x1 t0 t1 t2 (Z_to_bv 64 A) (Z_to_bv 64 PA) (Z_to_bv 64 31) (Z_to_bv 64 1) (Z_to_bv 64 0x25368) x14 x15 x16 x17 x18 x19 x20 x21 x23 t3 t4 t5 t6 F fc mm) mo)
             (TDIE [msg] stdout_init FS0).
  Proof.
    intros until errv. intros RO ML RNG LOA HIA HKx FR BA ERR FS.
    pose proof (sp_facts sp0 VSP RCSP) as SF. unfold LO in SF.
    pose proof BA as (ST & MI & RS & AUX & IMG & SE & SOF & YSx & TRx). unfold LO in ST. unfold RERRNO in ERR. unfold MFRAME in FR.
    destruct (di_blocks HKG DI _ _ _ _ _ HKx) as (RNGB & _ & _). pose proof (RNGB (bufp, A, cap) ltac:(left; reflexivity)) as BR. cbn [blk_addr blk_size fst snd] in BR.
    pose proof BR as (BR1 & BR2 & BR3 & BR4 & BR5). unfold alloc_ceiling in BR4.
    destruct (DIR _ _ _ _ _ HKx) as (Hmi & Hh & Hl).
    destruct (di_ssp HKG DI _ _ _ _ _ HKx) as [G1 G2]. unfold RGOT_SSP, RSSP_GUARD in G1, G2.
    unfold TDIE. cbn [concat]. rewrite app_nil_r.
    rz_seg Hh Hl. zstep. apply evt_done.
    eapply (rz_fwrite_diag) with (lo := usp0 - 8388608) (canary := rc_guard) (s := msg) (st := s);
      [ apply TEXIT2_nil | exact Hmi | exact Hh | exact SE
      | rewrite unsigned_lit by lia; apply rodata_bytes; [exact MI| exact RO| lia| lia]
      | exact RNG | rewrite ML; lia | rewrite ML; reflexivity | reflexivity | reflexivity
      | rewrite unsigned_lit by lia; exact ST
      | rewrite unsigned_lit by lia; unfold FWRITE_DEPTH; lia | unfold GLOBALS_TOP; lia
      | rewrite !unsigned_lit by lia; lia
      | rewrite !unsigned_lit by lia; lia
      | rewrite !unsigned_lit by lia; lia
      | split; [exact G1 | exact G2] | exact MI
      | rewrite ML; unfold WRITEV_MAX; lia | ].
    intros u0 u1 u2 b0 b1 b2 b3 b4 b5 b6 b7 u3 u4 u5 u6 m1 MUc WMc MI1 ST1 SEW SSP1.
    rewrite !unsigned_lit in MUc by lia. rewrite !unsigned_lit in ST1 by lia.
    replace (ret_pc (Z_to_bv 64 0x136f4)) with (Z_to_bv 64 0x136f4) by (symmetry; rpc).
    pose proof (agree_on_of_munch _ _ _ MUc WMc) as AG.
    assert (OUT : forall a, (usp0 - 128 <= a /\ ~ (0x25368 <= a < 0x25368 + 232)) -> (fun a0 : Z => outside [(usp0 - 8388608, usp0 + -128); (0x25368, 0x25368 + 232)] a0) a).
    { intros a Ha. cbn. lia. }
    assert (OUT2 : forall a, (0x10000 <= a < 0x57000 /\ ~ (0x25368 <= a < 0x25368 + 232)) -> (fun a0 : Z => outside [(usp0 - 8388608, usp0 + -128); (0x25368, 0x25368 + 232)] a0) a).
    { intros a Ha. cbn. lia. }
    apply (rw_cells_agree _ _ _ _ _ AG) in FR; [| intros a Ha; apply OUT; cbn in Ha; lia].
    apply (rw_cells_agree _ _ _ _ _ AG) in ERR; [| intros a Ha; apply OUT2; cbn in Ha; lia].
    assert (RS1 : RSTAT TID m1) by (eapply (RSTAT_agree TID _ _ _ AG); [intros a Ha; apply OUT2; unfold rstat_addr in Ha; lia| exact RS]).
    assert (SOF1 : stdout_file m1 stdout_init) by (eapply (stdout_file_agree _ _ _ _ AG); [intros a Ha; apply OUT2; unfold stdout_addr in Ha; lia| exact SOF]).
    assert (AUX1 : rauxv_ok m1 usp0).
    { eapply rauxv_ok_frame; [exact AUX| exact MUc| exact WMc|]. unfold RAUXV_CELL, RLIBC, alloc_ceiling in *.
      constructor; [cbn [fst snd]; lia|]. constructor; [cbn [fst snd]; lia| constructor]. }
    assert (HK1 : HK s [(bufp, A, cap)] m1 mo).
    { eapply (di_frame HKG DI); [exact HKx| exact MUc| exact WMc|].
      constructor; [left; cbn [fst snd]; unfold alloc_ceiling in *; lia|]. constructor; [| constructor].
      right; left. cbn [fst snd]. unfold RLIBC, RCTX, RSSP_GUARD, RGOT_SSP. lia. }
    clear MUc WMc AG OUT OUT2.
    (* [comment removed for export] *)
    rz_seg Hh Hl. zstep. zstep. apply evt_done.
    eapply (di_freeX HKG DI (G_fdfs (m_fds mo) FS0) (frame_ok_G_fdfs _ _)) with (lo := usp0 - 8388608) (B := usp0) (p := bufp) (A := A) (n := cap);
      try reflexivity.
    all: unfold RATP; rewrite ?(unsigned_lit 0x356a0) by lia; rewrite ?(unsigned_lit (usp0 + -128)) by lia.
    - apply TEXIT2_nil.
    - apply (di_pin_fds HKG DI). exact HK1.
    - left; reflexivity.
    - exact AUX1.
    - lia.
    - exact ST1.
    - lia.
    - unfold RFREE_STACK. lia.
    - exact ERR.
    - exact MI1.
    - intros w0 w1 w2 rb0 d1 d2 d3 d4 d5 d6 d7 w3 w4 w5 w6 m3 mo3 s3 MI3 ST3 ERR3 AUX3 HPR3 HK3.
      rewrite ?(unsigned_lit (usp0 + -128)) in ST3 by lia. rewrite ?(unsigned_lit (usp0 + -128)) in HPR3 by lia.
      replace (ret_pc (Z_to_bv 64 0x136fc)) with (Z_to_bv 64 0x136fc) by (symmetry; rpc).
      destruct (di_fdfs HKG DI _ _ _ _ _ _ HK3) as [_ FS3].
      unfold TEXIT2. rewrite <- FS3.
      eapply (rz_main_return sp0 argv TID VSP RCSP HT (HKG _) (DIR _) (di_ssp HKG DI _) (di_libc_head HKG DI _) 2 s3 ps0 _ mo3).
      + unfold MFRAME. eapply rheap_pres_rw_cells; [exact HPR3| exact FR| left; cbn; lia].
      + unfold LO. exact ST3.
      + eapply RSTAT_heap_pres; [exact HPR3 | exact RS1].
      + exact HK3.
      + eapply stdout_file_heap_pres; [exact HPR3 | exact SOF1].
      + apply stderr_wfile0_file. eapply stderr_wfile0_heap_pres; [exact HPR3 | exact SEW].
      + exact MI3.
      + unfold zlength, STDOUT_BUFSIZ. cbn. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma rz_after_run : forall (x23 : word) (bufp : bptr) (A cap L PL : Z) (d1 : byte) (status : Z) so s mo mm fc
      (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (F : bvmap 5 word),
    0 <= status < 2^32 ->
    RETINV sp0 argv envp uid hw rnd TID PAD S4 S5 S6 S7 HKG FS0 bufp A cap so s mo mm fc ->
    realizes_cfg acfg usegs (mkCfg (MS (mkR (Z_to_bv 64 0x13674) (Z_to_bv 64 (usp0 + -128)) gpv tpv t0 t1 t2 (Z_to_bv 64 (A + 2)) (Z_to_bv 64 A) (Z_to_bv 64 status) a1 a2 a3 a4 a5 a6 a7
                                      (Z_to_bv 64 L) (Z_to_bv 64 (A + 6 + L)) (Z_to_bv 64 PL) (Z_to_bv 64 (sx8 (bv_unsigned d1))) (Z_to_bv 64 RSTAGE) x23 S8 S9 S10 S11 t3 t4 t5 t6)
                               F (Z_to_bv 64 0x13674) fc None mm (seg_rom usegs)) mo)
             (KEXIT (128 <=? bv_unsigned d1) status so).
  Proof.
    intros until F. intros STR RI.
    destruct RI as (LB & errv & FR & ST & MI & RS & AUX & IMG & SE & YS & SOF & SOB & HKx & INB & FS & ERR & FRM).
    pose proof (sp_facts sp0 VSP RCSP) as SF. unfold LO in SF. unfold LO in ST. unfold RERRNO in ERR. pose proof FR as FR0. unfold MFRAME in FR.
    pose proof (byte_range d1) as Rd1.
    destruct (DIR _ _ _ _ _ HKx) as (Hmi & Hh & Hl).
    destruct (di_blocks HKG DI _ _ _ _ _ HKx) as (RNGB & _ & _). pose proof (RNGB (bufp, A, cap) INB) as BR. cbn [blk_addr blk_size fst snd] in BR.
    pose proof BR as (BR1 & BR2 & BR3 & BR4 & BR5). unfold alloc_ceiling in BR4.
    (* [comment removed for export] *)
    assert (STEP : forall K, K [] ->
      (forall (x1 u0 u1 u2 b1 b2 b3 b4 b5 b6 b7 u3 u4 u5 u6 : word),
         realizes_cfg acfg usegs (mkCfg (MS (mkR x1 (Z_to_bv 64 (usp0 + -128)) gpv tpv u0 u1 u2
                                      (Z_to_bv 64 (if 128 <=? bv_unsigned d1 then 0 else status)) (Z_to_bv 64 A) (Z_to_bv 64 A) b1 b2 b3 b4 b5 b6 b7
                                      (Z_to_bv 64 L) (Z_to_bv 64 (A + 6 + L)) (Z_to_bv 64 PL) (Z_to_bv 64 (sx8 (bv_unsigned d1))) (Z_to_bv 64 RSTAGE) x23 S8 S9 S10 S11 u3 u4 u5 u6)
                               F (Z_to_bv 64 0x136f8) fc None mm (seg_rom usegs)) mo) K) ->
      realizes_cfg acfg usegs (mkCfg (MS (mkR (Z_to_bv 64 0x13674) (Z_to_bv 64 (usp0 + -128)) gpv tpv t0 t1 t2 (Z_to_bv 64 (A + 2)) (Z_to_bv 64 A) (Z_to_bv 64 status) a1 a2 a3 a4 a5 a6 a7
                                      (Z_to_bv 64 L) (Z_to_bv 64 (A + 6 + L)) (Z_to_bv 64 PL) (Z_to_bv 64 (sx8 (bv_unsigned d1))) (Z_to_bv 64 RSTAGE) x23 S8 S9 S10 S11 t3 t4 t5 t6)
                               F (Z_to_bv 64 0x13674) fc None mm (seg_rom usegs)) mo) K).
    { intros K HK0 HKK.
      destruct (Z.ltb_spec (bv_unsigned d1) 128) as [LT|GE].
      - assert (E8 : sx8 (bv_unsigned d1) = bv_unsigned d1) by (unfold sx8; destruct (Z.ltb_spec0 (bv_unsigned d1) 128); lia).
        rewrite E8 in HKK |- *. replace (128 <=? bv_unsigned d1) with false in HKK by (symmetry; apply Z.leb_gt; lia).
        replace (128 <=? bv_unsigned d1) with false by (symmetry; apply Z.leb_gt; lia).
        rz_seg Hh Hl.
        zstep. if_cases K1; zify_cond K1; [exfalso; rewrite ?unsigned_lit in K1 by lia; lia|].
        zstep. zstep. zstep. apply evt_done. apply HKK.
      - assert (E8 : Z_to_bv 64 (sx8 (bv_unsigned d1)) = Z_to_bv 64 (bv_unsigned d1 - 256 + 2^64)).
        { unfold sx8. destruct (Z.ltb_spec0 (bv_unsigned d1) 128); [lia|].
          apply Z_to_bv_eqm. rewrite <- (Z.mod_add (bv_unsigned d1 - 256) 1) by lia. f_equal; lia. }
        rewrite E8 in HKK |- *. replace (128 <=? bv_unsigned d1) with true in HKK by (symmetry; apply Z.leb_le; lia).
        replace (128 <=? bv_unsigned d1) with true by (symmetry; apply Z.leb_le; lia).
        rz_seg Hh Hl.
        zstep. if_cases K1; zify_cond K1; [| exfalso; rewrite ?unsigned_lit in K1 by lia; lia].
        zstep. zstep. zstep.
        replace (ret_pc (Z_to_bv 64 0x13684)) with (Z_to_bv 64 0x13684) by (symmetry; rpc).
        zstep. zstep. zstep. if_cases K2; zify_cond K2; [| exfalso; rewrite ?unsigned_lit in K2 by lia; lia].
        zstep. apply evt_done. apply HKK. }
    apply STEP; [apply KEXIT_nil|]. intros x1 u0 u1 u2 b1 b2 b3 b4 b5 b6 b7 u3 u4 u5 u6.
    set (code := if 128 <=? bv_unsigned d1 then 0 else status).
    assert (CR : 0 <= code < 2^32) by (subst code; destruct (128 <=? _); lia).
    (* [comment removed for export] *)
    rz_seg Hh Hl. zstep. apply evt_done.
    eapply (di_freeX HKG DI (G_fdfs (m_fds mo) FS0) (frame_ok_G_fdfs _ _)) with (lo := usp0 - 8388608) (B := usp0) (p := bufp) (A := A) (n := cap);
      try reflexivity.
    all: unfold RATP; rewrite ?(unsigned_lit 0x356a0) by lia; rewrite ?(unsigned_lit (usp0 + -128)) by lia.
    - apply KEXIT_nil.
    - apply (di_pin_fds HKG DI). exact HKx.
    - exact INB.
    - exact AUX.
    - lia.
    - exact ST.
    - lia.
    - unfold RFREE_STACK. lia.
    - exact ERR.
    - exact MI.
    - intros w0 w1 w2 rb0 e1 e2 e3 e4 e5 e6 e7 w3 w4 w5 w6 m3 mo3 s3 MI3 ST3 ERR3 AUX3 HPR3 HK3.
      rewrite ?(unsigned_lit (usp0 + -128)) in ST3 by lia. rewrite ?(unsigned_lit (usp0 + -128)) in HPR3 by lia.
      replace (ret_pc (Z_to_bv 64 0x136fc)) with (Z_to_bv 64 0x136fc) by (symmetry; rpc).
      destruct (di_fdfs HKG DI _ _ _ _ _ _ HK3) as [_ FS3].
      unfold KEXIT. fold code. rewrite <- FS3.
      eapply (rz_main_return sp0 argv TID VSP RCSP HT (HKG _) (DIR _) (di_ssp HKG DI _) (di_libc_head HKG DI _) code s3 (set_so_ps so ps0) _ mo3);
        rewrite ?ps_get_set.
      + unfold MFRAME. eapply rheap_pres_rw_cells; [exact HPR3| exact FR| left; cbn; lia].
      + unfold LO. exact ST3.
      + eapply RSTAT_heap_pres; [exact HPR3 | exact RS].
      + exact HK3.
      + eapply stdout_file_heap_pres; [exact HPR3 | exact SOF].
      + apply stderr_wfile0_file. eapply stderr_wfile0_heap_pres; [exact HPR3 | exact SE].
      + exact MI3.
      + exact SOB.
  Qed.

  (* [comment removed for export] *)
  Lemma rz_after_loop : forall (FILE : list byte) cap s mo ms,
    RDBRK' 3 P1v (FdFile pathb (Z_to_bv 64 (Z.of_nat (length FILE)))) cap FILE s mo ms ->
    Z.of_nat (length FILE) < cap ->
    realizes_cfg acfg usegs (mkCfg ms mo) (KDONE FILE).
  Proof.
    intros FILE cap s mo ms RB LTC.
    destruct RB as (x1 & t0 & t1 & t2 & a0 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & x23 & t3 & t4 & t5 & t6 & F & fc & mm & A & -> & RC).
    destruct RC as (junk & stg & errv & bufp & BU & HKx & FD & FS & FR & BA & ERR & RSG & FRM).
    destruct BU as (BLK & [CAPR CAPK] & LENR & BR). pose proof BR as (BR1 & BR2 & BR3 & BR4 & BR5). unfold alloc_ceiling in BR4. unfold MAX_INPUT in CAPR.
    pose proof (sp_facts sp0 VSP RCSP) as SF. unfold LO in SF.
    pose proof BA as (ST & MI & RS & AUX & IMG & SE & SOF & YSx & TRx). unfold LO in ST. pose proof FR as FR0. unfold MFRAME in FR. pose proof ERR as ERR0. unfold RERRNO in ERR.
    destruct (DIR _ _ _ _ _ HKx) as (Hmi & Hh & Hl).
    set (LEN := Z.of_nat (length FILE)) in *.
    rz_seg Hh Hl. zstep. zstep. apply evt_done.
    (* [comment removed for export] *)
    pose proof (close_spec (Z_to_bv 64 0x135fc) (Z_to_bv 64 (usp0 + -128)) gpv tpv t0 t1 t2 (Z_to_bv 64 2) (Z_to_bv 64 A)
                  (Z_to_bv 64 3) a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 P1v) (Z_to_bv 64 LEN) (Z_to_bv 64 3) (Z_to_bv 64 cap) (Z_to_bv 64 RSTAGE) x23 S8 S9 S10 S11 t3 t4 t5 t6 F fc mm
                  3 errv (usp0 - 8388608)) as IMC.
    specialize (IMC ltac:(rewrite (unsigned_lit (usp0 + -128)) by lia; exact ST) ltac:(unfold RATP; rewrite (unsigned_lit 0x356a0) by lia; exact ERR) MI eq_refl ltac:(lia)).
    do 2 (specialize (IMC ltac:(unfold RATP; rewrite ?(unsigned_lit 0x356a0) by lia; rewrite ?(unsigned_lit (usp0 + -128)) by lia; lia))).
    specialize (IMC ltac:(unfold RATP; rewrite ?(unsigned_lit 0x356a0) by lia; lia)).
    eapply (rz_close 3 _ _ mo); [exact IMC | exact Hmi | exact Hh | lia | apply KDONE_nil |].
    unfold close_out. rewrite FD. cbn [fst snd].
    intros ms' rsp evs Hst PO Hmi2 Hh2.
    destruct PO as (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & m1 & -> & MUc & WMc & MI1 & ST1 & ERR1).
    cbn [close_ret close_errno] in *.
    unfold RATP in MUc, ERR1. rewrite ?(unsigned_lit 0x356a0) in MUc by lia. rewrite ?(unsigned_lit (usp0 + -128)) in MUc by lia. rewrite ?(unsigned_lit 0x356a0) in ERR1 by lia.
    rewrite ?(unsigned_lit (usp0 + -128)) in ST1 by lia. change (0x356a0 + -164) with RERRNO in MUc, ERR1.
    replace (ret_pc (Z_to_bv 64 0x135fc)) with (Z_to_bv 64 0x135fc) by (symmetry; rpc).
    set (mo1 := with_fds (fd_remove (m_fds mo) (Z_to_bv 64 3)) mo) in *.
    assert (WOKW : Forall (WOK sp0) [(usp0 + -128 - 32, usp0 + -128); (RERRNO, RERRNO + 4)]).
    { unfold WOK, LO, RERRNO. constructor; [cbn [fst snd]; lia|]. constructor; [cbn [fst snd]; lia| constructor]. }
    assert (BA1 : BASE' m1) by (eapply (BASE_munch sp0 argv envp uid hw rnd TID VSP RCSP VARGV VENVP); [exact BA| exact WOKW| exact MUc| exact WMc| exact MI1| unfold LO; exact ST1]).
    pose proof (agree_on_of_munch _ _ _ MUc WMc) as AG.
    assert (FR1 : FRAME' m1) by (unfold MFRAME; eapply rw_cells_agree; [exact AG | exact FR | intros ax Ha; cbn in Ha |- *; unfold RERRNO; lia]).
    assert (BLK1 : rw_cells usegs m1 A [CB (length FILE) FILE; CB (Z.to_nat (cap - LEN)) junk]).
    { eapply rw_cells_agree; [exact AG | exact BLK | intros ax Ha; cbn [cells_size csize Nat.add] in Ha; cbn; unfold RERRNO; lia]. }
    assert (HK1 : HK s [(bufp, A, cap)] m1 mo1).
    { eapply (di_mo HKG DI) with (n := NClose 3); [| exact I | exact Hst | subst mo1; apply m_vmmaps_with_fds | unfold G_fs; subst mo1; rewrite m_fs_with_fds; exact FS].
      eapply (di_frame HKG DI); [exact HKx | exact MUc | exact WMc |].
      constructor; [left; cbn [fst snd]; unfold alloc_ceiling in *; lia|].
      constructor; [| constructor]. right; left. cbn [fst snd]. unfold RERRNO, RLIBC, RCTX, RSSP_GUARD, RGOT_SSP. lia. }
    assert (FS1 : m_fs mo1 = FS0) by (subst mo1; rewrite m_fs_with_fds; exact FS).
    clear MUc WMc WOKW AG ST MI RS AUX IMG SE SOF YSx TRx FR BLK ERR IMC.
    pose proof BA1 as (ST & MI & RS & AUX & IMG & SE & SOF & YSx & TRx). unfold LO in ST.
    pose proof RS as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & G78 & GD0).
    pose proof BLK1 as BLKB. apply (proj1 (rw_cells_app _ _ _ [CB (length FILE) FILE] _)) in BLKB. destruct BLKB as [BLKB _].
    apply rw_cells_bytes_at in BLKB. cbn [cells_bytes cbytes app] in BLKB. rewrite app_nil_r in BLKB.
    destruct (DIR _ _ _ _ _ HK1) as (_ & Hh1 & Hl1).
    unfold KDONE.
    rz_seg Hh1 Hl1. zstep. zstep. if_cases K0; zify_cond K0.
    { (* [comment removed for export] *)
      replace (length FILE <? 6)%nat with true by (symmetry; apply Nat.ltb_lt; lia).
      zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. apply evt_done.
      change pieces_short_hdr with [s_short].
      eapply (rz_fwrite_ret s_short S_SHORT s bufp A cap mo1); [apply s_short_ro | reflexivity | unfold s_short; apply Forall_app; split; [apply str_range| constructor; [lia| constructor]]
        | unfold S_SHORT; lia | unfold S_SHORT; lia | exact HK1 | exact FR1 | exact BA1 | unfold RERRNO; exact ERR1 | exact FS1]. }
    replace (length FILE <? 6)%nat with false by (symmetry; apply Nat.ltb_ge; lia).
    destruct (list6 FILE ltac:(lia)) as (d0 & d1 & d2 & d3 & d4 & d5 & rest & ED).
    pose proof (byte_range d0) as Rd0. pose proof (byte_range d1) as Rd1. pose proof (byte_range d2) as Rd2.
    assert (N0 : nth 0 FILE (Z_to_bv 8 0) = d0) by (rewrite ED; reflexivity).
    assert (N1 : nth 1 FILE (Z_to_bv 8 0) = d1) by (rewrite ED; reflexivity).
    rewrite N0, N1. cbv zeta.
    remember (bv_unsigned d0 + 256 * bv_unsigned d1) as cw eqn:Ecw.
    set (L := cw mod 32768). assert (RL : 0 <= L <= cw) by (subst L; Z.div_mod_to_equations; lia).
    pose proof (u8ro_read usegs m1 _ _ 1 d1 (wa (A + 1)) BLKB ltac:(rewrite ED; reflexivity) ltac:(lia) eq_refl) as R1.
    zstep. clear R1. cbv beta.
    pose proof (u8ro_read usegs m1 _ _ 0 d0 (wa (A + 0)) BLKB ltac:(rewrite ED; reflexivity) ltac:(lia) eq_refl) as R0.
    zstep. clear R0. cbv beta.
    (* [comment removed for export] *)
    zstep. zstep. zstep.
    replace (bv_unsigned (sxb d1)) with ((sx8 (bv_unsigned d1)) mod 2^64) by (unfold sxb; rewrite Z_to_bv_unsigned, signed_byte; reflexivity).
    rewrite (cfg15_Z _ _ Rd0 Rd1). rewrite land15_mod. replace (bv_unsigned d0 + bv_unsigned d1 * 256) with cw by lia. fold L.
    zstep. zstep. if_cases K1; zify_cond K1.
    { (* [comment removed for export] *)
      replace (LEN <? 6 + L) with true by (symmetry; apply Z.ltb_lt; lia).
      zstep. zstep. zstep. zstep. zstep. zstep. zstep. apply evt_done.
      change pieces_cfg_overrun with [s_over].
      eapply (rz_fwrite_ret s_over S_OVER s bufp A cap mo1); [apply s_over_ro | reflexivity | unfold s_over; apply Forall_app; split; [apply str_range| constructor; [lia| constructor]]
        | unfold S_OVER; lia | unfold S_OVER; lia | exact HK1 | exact FR1 | exact BA1 | unfold RERRNO; exact ERR1 | exact FS1]. }
    replace (LEN <? 6 + L) with false by (symmetry; apply Z.ltb_ge; lia).
    zstep. zstep.
    (* [comment removed for export] *)
    destruct (skipn4 FILE (Z.to_nat (2 + L)) ltac:(lia)) as (q0 & q1 & q2 & q3 & rest' & EQ4).
    pose proof (byte_range q0) as Rq0. pose proof (byte_range q1) as Rq1. pose proof (byte_range q2) as Rq2. pose proof (byte_range q3) as Rq3.
    assert (QB : bytes_at usegs m1 (A + 2 + L) (q0 :: q1 :: q2 :: q3 :: rest')).
    { rewrite <- EQ4. rewrite <- (firstn_skipn (Z.to_nat (2 + L)) FILE) in BLKB.
      apply bytes_at_app in BLKB. destruct BLKB as [_ X]. rewrite length_firstn in X.
      replace (A + Z.of_nat (Nat.min (Z.to_nat (2 + L)) (length FILE))) with (A + 2 + L) in X by lia. exact X. }
    assert (SH1 : 0 <= Z.shiftl (bv_unsigned q1) 8 < 2^64) by (rewrite Z.shiftl_mul_pow2 by lia; lia).
    assert (SH2 : 0 <= Z.shiftl (bv_unsigned q2) 16 < 2^64) by (rewrite Z.shiftl_mul_pow2 by lia; lia).
    assert (SH3 : 0 <= Z.shiftl (bv_unsigned q3) 24 < 2^64) by (rewrite Z.shiftl_mul_pow2 by lia; lia).
    pose proof (u8ro_read usegs m1 _ _ 1 q1 (wa (A + 2 + L + 1)) QB eq_refl ltac:(lia) eq_refl) as R1.
    zstep. clear R1. cbv beta.
    pose proof (u8ro_read usegs m1 _ _ 0 q0 (wa (A + 2 + L)) QB eq_refl ltac:(lia) ltac:(unfold wa; f_equal; lia)) as R0.
    zstep. clear R0. cbv beta.
    pose proof (u8ro_read usegs m1 _ _ 2 q2 (wa (A + 2 + L + 2)) QB eq_refl ltac:(lia) eq_refl) as R2.
    zstep. clear R2. cbv beta.
    pose proof (u8ro_read usegs m1 _ _ 3 q3 (wa (A + 2 + L + 3)) QB eq_refl ltac:(lia) eq_refl) as R3.
    zstep. clear R3. cbv beta.
    zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep.
    (* [comment removed for export] *)
    zstep. zstep.
    replace (ret_pc (Z_to_bv 64 0x13660)) with (Z_to_bv 64 0x13660) by (symmetry; rpc).
    zstep. zstep. zstep. zstep. zstep. apply evt_done.
    (* [comment removed for export] *)
    replace (LEN - L + -6) with (LEN - 6 - L) by lia.
    replace (A + 2 + L + 4) with (A + 6 + L) by lia.
    set (PL := LEN - 6 - L).
    replace (sxb d1) with (Z_to_bv 64 (sx8 (bv_unsigned d1))) by (unfold sxb; rewrite signed_byte; reflexivity).
    subst PL. set (PL := Z.of_nat (length FILE) - 6 - L) in *. subst LEN.
    assert (HPL : 0 <= PL) by (subst PL; lia).
    assert (HLEN : Z.of_nat (length FILE) = 6 + L + PL) by (subst PL; lia).
    assert (HCAPM' : cap <= 67108864) by lia.
    eapply (rz_target_run sp0 argv envp uid hw rnd arg0 arg1 TID PAD S4 S5 S6 S7 x23 S8 S9 S10 S11 VSP RCSP EFIT VARGV VENVP EARGV HKG DI FS0 YF
              bufp A cap L PL (sx8 (bv_unsigned d1)) FILE (proj1 RL) HPL HLEN LTC HCAPM' (fun st so => KEXIT (128 <=? bv_unsigned d1) st so)
              ltac:(intros; apply KEXIT_nil)).
    - intros status so s' mo' mm' fc' v0 v1 v2 c1 c2 c3 c4 c5 c6 c7 v3 v4 v5 v6 F' SR RI. eapply (rz_after_run x23); [exact SR | exact RI].
    - exact FR1.
    - exact BA1.
    - exact HK1.
    - exact FS1.
    - exact BLK1.
    - exact BR.
    - exact ERR1.
    - exact FRM.
  Qed.
End D.
