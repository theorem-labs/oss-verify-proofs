(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation Strings.String.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Common Require Import ShapeAlgCfg.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import Tac Image ZBridge ITree Nodes NodesCfg Decode Arr FP InitMem Frame Mem Cells SysStep.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.LibA Require Import StepA AImages ExecA LazyModel NodesA ImplRzA CompatE2.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Spec Require Import Prelim StdioBase Stdio Driver.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Top Require Import TrzNodes TrzStdio.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.R Require Import Printf_model R_StartupLib.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.A Require Import A_iface A_iface5x ADrv_ctx ADrv_A ADrv_B ADrv_C ADrv_run.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.A Require Import AX_atexit.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Ltac rpc := apply ret_pc_even; [lia| reflexivity].
Ltac aceil := first [pose proof alloc_ceiling_range as CEILB | idtac].
Ltac aceil_in H := aceil.

(* [comment removed for export] *)
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import RunCeiling.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Section RC__1.
Context {RC__ : OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib.RunCeiling.RunCeiling}.
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

Lemma cfg15_Zm : forall u0 u1, 0 <= u0 < 256 -> 0 <= u1 < 256 ->
  Z.lor (Z.shiftr ((Z.shiftl ((sx8 u1) mod 2^64) 57) mod 18446744073709551616) 49) u0 = Z.land (u0 + u1 * 256) 32767.
Proof.
  intros u0 u1 H0 H1. rewrite <- (cfg15_Z u0 u1 H0 H1). change 18446744073709551616 with (2^64). change 18446744073709551615 with (Z.ones 64).
  rewrite Z.land_ones by lia. reflexivity.
Qed.

Section D.
  Variables (sp0 : word) (argv envp : list (list byte)) (uid hw : word) (rnd : EntryDraw) (arg0 arg1 : list byte)
            (PAD : list byte) (S4 S5 S6 S7 S8 S9 S10 S11 : word).
  Hypothesis VSP : valid_sp sp0.
  Hypothesis RCSP : rc_sp = bv_unsigned sp0.
  Hypothesis EFIT : entry_stack_fits sp0 argv envp.
  Hypothesis VARGV : valid_argv argv.
  Hypothesis VENVP : valid_envp envp.
  Hypothesis EARGV : argv = [arg0; arg1].
  Variable D : adrv_params.
  Hypothesis DI : a_drv_iface asegs ACONSTS AFMTS D.
  Hypothesis DIx : a_drv_iface5x asegs ACONSTS D.
  Notation AHK := (p_AHK D).
  Notation SO := (p_SO D).
  Notation AHEAD := (p_AHEAD D).

  Notation usp0 := (bv_unsigned sp0).
  Notation gpv := (Z_to_bv 64 0x10800).
  Notation tpv := (Z_to_bv 64 0x5e0b10).
  Notation IMGB := (build_stack_bytes aph sp0 argv envp uid hw rnd).
  Notation LO' := (LO sp0).
  Notation ABASE' := (ABASE sp0 argv envp uid hw rnd).
  Notation FRAME' mm := (MFRAME sp0 argv mm PAD S7 S6 S5 S4).
  Notation GST pc x1 t0 t1 t2 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x23 t3 t4 t5 t6 F fc mm :=
    (MS (mkR x1 (Z_to_bv 64 (usp0 + -128)) gpv tpv t0 t1 t2 (Z_to_bv 64 2) x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 (Z_to_bv 64 RSTAGE) x23 S8 S9 S10 S11 t3 t4 t5 t6)
        F (Z_to_bv 64 pc) fc None mm (seg_rom asegs)).
  Let PSTK := PSTK sp0 VSP RCSP.

  Variable FS0 : Fs.Fs.
  Notation RDBRK' := (RDBRK sp0 argv envp uid hw rnd PAD S4 S5 S6 S7 S8 S9 S10 S11 D FS0).
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
  Lemma az_fwrite_ret : forall (msg : list Z) (PA : Z) s (A cap : Z) LF mo
      x1 t0 t1 t2 x14 x15 x16 x17 x18 x19 x20 x21 x23 t3 t4 t5 t6 (F : bvmap 5 word) (fc : bv 32) (mm : mem),
    ro_bytes_b asegs PA (zb msg) = true -> zlength msg = 31 -> Forall (fun c => 0 <= c < 256) msg ->
    0x10000 <= PA -> PA + 31 <= 0x21020 ->
    AHK s [mkABlock A cap] LF mm mo -> (exists k X H, AHEAD k X H s mo) -> SO s = stdout_init -> FRAME' mm -> ABASE' mm -> frm0 fc -> m_fs mo = FS0 ->
    realizes_cfg acfg asegs (mkCfg (GST 0x81c94 x1 t0 t1 t2 (Z_to_bv 64 A) (Z_to_bv 64 PA) (Z_to_bv 64 31) (Z_to_bv 64 1) (Z_to_bv 64 0xa9088) x14 x15 x16 x17 x18 x19 x20 x21 x23 t3 t4 t5 t6 F fc mm) mo)
              (TDIE [msg] stdout_init FS0).
  Proof.
    intros until mm. intros RO ML RNG LOA HIA HKx (hk & hX & hH & HDp) SO0 FR BA FRM FS.
    pose proof (sp_facts sp0 VSP RCSP) as SF. unfold LO in SF.
    pose proof BA as (ST & MI & IMG & AS). unfold LO in ST. unfold MFRAME in FR.
    destruct (adi_blocks _ _ _ _ DI _ _ _ _ _ HKx) as (RNGB & _ & _). pose proof (RNGB (mkABlock A cap) ltac:(left; reflexivity)) as BR. cbn [ab_addr ab_size] in BR.
    pose proof BR as (BR1 & BR2 & BR3 & BR4 & BR5). aceil_in BR4.
    unfold TDIE. cbn [concat]. rewrite app_nil_r.
    pose proof (PSTK [mkABlock A cap]) as PS.
    aseg DI HKx. zstepA. aleaf. intros mo1 Hag1 HK1 Efs1 Efds1 Hh1.
    eapply (adi_fwrite _ _ _ _ DI) with (lo := usp0 - 8388608);
      [ apply TEXIT2_nil | exact HK1
      | apply rodata_bytes; [exact MI| exact RO| lia| lia]
      | exact RNG | rewrite ML; lia | cbn [c_img_lo ACONSTS]; lia | lia
      | rewrite unsigned_lit by lia; exact ST | aceil; lia
      | rewrite unsigned_lit by lia; unfold AICP_STACK; lia | rewrite unsigned_lit by lia; lia | reflexivity | exact FRM
      | reflexivity | rewrite ML; reflexivity | reflexivity | reflexivity | ].
    intros u0 u1 u2 b0 b1 b2 b3 b4 b5 b6 b7 u3 u4 u5 u6 Ft fc' m1 mo2 s2 ST1 MUc WMc FRM1 HK2 AS2 SO2 Efs2 Efds2 VS2.
    rewrite !unsigned_lit in MUc by lia. rewrite !unsigned_lit in ST1 by lia.
    replace (ret_pc (Z_to_bv 64 0x81c98)) with (Z_to_bv 64 0x81c98) by (symmetry; rpc).
    pose proof (agree_on_of_munch _ _ _ MUc WMc) as AG.
    apply (rw_cells_agree _ _ _ _ _ AG) in FR; [| intros a Ha; cbn in Ha |- *; lia].
    pose proof (adi_mem_inv _ _ _ _ DI _ _ _ _ _ HK2) as MI1.
    assert (AX1 : atx_ok_on asegs m1).
    { destruct AS as (_ & _ & AX0). eapply (atx_ok_agree _ _ _ AG); [| exact AX0]. intros a Ha. cbn [c_stderr_F ACONSTS]. cbn. lia. }
    clear MUc WMc AG.
    (* [comment removed for export] *)
    pose proof (PSTK [mkABlock A cap]) as PS1.
    aseg DI HK2. zstepA. zstepA. aleaf. intros mo3 Hag3 HK3 Efs3 Efds3 Hh3.
    eapply (adi_free _ _ _ _ DI) with (lo := usp0 - 8388608) (A := A);
      [ apply TEXIT2_nil | exact HK3 | right; exists (mkABlock A cap); split; [left; reflexivity| reflexivity]
      | rewrite unsigned_lit by lia; exact ST1 | aceil; lia
      | rewrite unsigned_lit by lia; unfold AMALLOC_STACK; lia | clear -SF; rewrite unsigned_lit by lia; Z.div_mod_to_equations; lia
      | rewrite unsigned_lit by lia; lia
      | reflexivity | apply (adi_uanchorC _ _ _ _ DI); [in_lits| rewrite unsigned_lit by lia; aceil; lia]
      | exact FRM1 | reflexivity
      | pose proof (adi_hd_reserve _ _ _ _ DI _ _ _ _ _ (adi_hd_aps _ _ _ _ DI _ _ _ _ _ _ (adi_hd_magree _ _ _ _ DI _ _ _ _ _ _ (adi_hd_magree _ _ _ _ DI _ _ _ _ _ _ HDp Hag1) VS2) AS2)) as RS2;
        unfold afree_cost; destruct (A =? 0); lia
      | apply nbig_small; cbn [length]; lia | ].
    intros w0 w1 w2 rb0 d1 d2 d3 d4 d5 d6 d7 w3 w4 w5 w6 F3 fc3 m3 mo4 s4 ST3 HPR3 FRM3 SOE3 HK4 REL4 FS4 FDS4 CR4.
    rewrite ?(unsigned_lit (usp0 + -128)) in ST3 by lia. rewrite ?(unsigned_lit (usp0 + -128)) in HPR3 by lia.
    replace (ret_pc (Z_to_bv 64 0x81ca0)) with (Z_to_bv 64 0x81ca0) by (symmetry; rpc).
    unfold TEXIT2. replace FS0 with (m_fs mo4) by (rewrite FS4, Efs3, Efs2, Efs1; exact FS). rewrite <- SO0, <- SO2, <- SOE3.
    eapply (az_main_return sp0 argv VSP RCSP D DI DIx 2 s4 _ LF mo4).
    - unfold MFRAME. eapply rw_cells_agree; [eapply aheap_pres_agree; exact HPR3| exact FR| intros ax Ha; left; cbn in Ha; lia].
    - unfold LO. exact ST3.
    - exact HK4.
    - (* [comment removed for export] *)
      eapply (atx_ok_agree _ _ _ (aheap_pres_agree _ _ _ _ _ _ HPR3)); [| exact AX1]. intros a Ha. right; right; right.
      unfold adrv_static. cbn [c_seg3_lo c_seg3_hi c_initialized c_ystat_lo c_ystat_hi ACONSTS]. lia.
    - exact (adi_mem_inv _ _ _ _ DI _ _ _ _ _ HK4).
    - exact FRM3.
    - lia.
  Qed.

  (* [comment removed for export] *)
  Lemma az_after_run : forall (x23 : word) (A cap L PL : Z) (d1 : byte) (status : Z) so s mo mm fc
      (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (F : bvmap 5 word),
    0 <= status < 2^32 ->
    RETINV sp0 argv envp uid hw rnd PAD S4 S5 S6 S7 D FS0 A cap so s mo mm fc ->
    realizes_cfg acfg asegs (mkCfg (MS (mkR (Z_to_bv 64 0x81c18) (Z_to_bv 64 (usp0 + -128)) gpv tpv t0 t1 t2 (Z_to_bv 64 (A + 2)) (Z_to_bv 64 A) (Z_to_bv 64 status) a1 a2 a3 a4 a5 a6 a7
                                        (Z_to_bv 64 L) (Z_to_bv 64 (A + 6 + L)) (Z_to_bv 64 PL) (Z_to_bv 64 (sx8 (bv_unsigned d1))) (Z_to_bv 64 RSTAGE) x23 S8 S9 S10 S11 t3 t4 t5 t6)
                                F (Z_to_bv 64 0x81c18) fc None mm (seg_rom asegs)) mo)
              (KEXIT (128 <=? bv_unsigned d1) status so).
  Proof.
    intros until F. intros STR RI.
    destruct RI as (LB & LF & FR & BA & SOE & SOB & HKx & INB & LBL & FS & FRM & CR1).
    pose proof (sp_facts sp0 VSP RCSP) as SF. unfold LO in SF.
    pose proof BA as (ST & MI & IMG & AS). unfold LO in ST. pose proof FR as FR0. unfold MFRAME in FR.
    pose proof (byte_range d1) as Rd1.
    destruct (adi_blocks _ _ _ _ DI _ _ _ _ _ HKx) as (RNGB & _ & _). pose proof (RNGB (mkABlock A cap) INB) as BR. cbn [ab_addr ab_size] in BR.
    pose proof BR as (BR1 & BR2 & BR3 & BR4 & BR5). aceil_in BR4.
    pose proof (PSTK LB) as PS.
    (* [comment removed for export] *)
    assert (STEP : forall K, K [] ->
      (forall (x1 u0 u1 u2 b1 b2 b3 b4 b5 b6 b7 u3 u4 u5 u6 : word) mo1,
         magree mo mo1 -> AHK s LB LF mm mo1 ->
         realizes_cfg acfg asegs (mkCfg (MS (mkR x1 (Z_to_bv 64 (usp0 + -128)) gpv tpv u0 u1 u2
                                      (Z_to_bv 64 (if 128 <=? bv_unsigned d1 then 0 else status)) (Z_to_bv 64 A) (Z_to_bv 64 A) b1 b2 b3 b4 b5 b6 b7
                                      (Z_to_bv 64 L) (Z_to_bv 64 (A + 6 + L)) (Z_to_bv 64 PL) (Z_to_bv 64 (sx8 (bv_unsigned d1))) (Z_to_bv 64 RSTAGE) x23 S8 S9 S10 S11 u3 u4 u5 u6)
                                F (Z_to_bv 64 0x81c9c) fc None mm (seg_rom asegs)) mo1) K) ->
      realizes_cfg acfg asegs (mkCfg (MS (mkR (Z_to_bv 64 0x81c18) (Z_to_bv 64 (usp0 + -128)) gpv tpv t0 t1 t2 (Z_to_bv 64 (A + 2)) (Z_to_bv 64 A) (Z_to_bv 64 status) a1 a2 a3 a4 a5 a6 a7
                                      (Z_to_bv 64 L) (Z_to_bv 64 (A + 6 + L)) (Z_to_bv 64 PL) (Z_to_bv 64 (sx8 (bv_unsigned d1))) (Z_to_bv 64 RSTAGE) x23 S8 S9 S10 S11 t3 t4 t5 t6)
                                F (Z_to_bv 64 0x81c18) fc None mm (seg_rom asegs)) mo) K).
    { intros K HK0 HKK.
      destruct (Z.ltb_spec (bv_unsigned d1) 128) as [LT|GE].
      - assert (E8 : sx8 (bv_unsigned d1) = bv_unsigned d1) by (unfold sx8; destruct (Z.ltb_spec0 (bv_unsigned d1) 128); lia).
        rewrite E8 in HKK |- *. replace (128 <=? bv_unsigned d1) with false in HKK by (symmetry; apply Z.leb_gt; lia).
        aseg DI HKx.
        zstepA. if_cases K1; zify_cond K1; [exfalso; rewrite ?unsigned_lit in K1 by lia; lia|].
        zstepA. zstepA. zstepA. aleaf. intros mo1 Hag1 HK1 Efs1 Efds1 Hh1. apply (HKK _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ mo1 Hag1 HK1).
      - assert (E8 : Z_to_bv 64 (sx8 (bv_unsigned d1)) = Z_to_bv 64 (bv_unsigned d1 - 256 + 2^64)).
        { unfold sx8. destruct (Z.ltb_spec0 (bv_unsigned d1) 128); [lia|].
          apply Z_to_bv_eqm. rewrite <- (Z.mod_add (bv_unsigned d1 - 256) 1) by lia. f_equal; lia. }
        rewrite E8 in HKK |- *. replace (128 <=? bv_unsigned d1) with true in HKK by (symmetry; apply Z.leb_le; lia).
        aseg DI HKx.
        zstepA. if_cases K1; zify_cond K1; [| exfalso; rewrite ?unsigned_lit in K1 by lia; lia].
        zstepA. zstepA. zstepA.
        replace (ret_pc (Z_to_bv 64 0x81c28)) with (Z_to_bv 64 0x81c28) by (symmetry; rpc).
        zstepA. zstepA. zstepA. if_cases K2; zify_cond K2; [| exfalso; rewrite ?unsigned_lit in K2 by lia; lia].
        zstepA. aleaf. intros mo1 Hag1 HK1 Efs1 Efds1 Hh1. apply (HKK _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ mo1 Hag1 HK1). }
    apply STEP; [apply KEXIT_nil|]. intros x1 u0 u1 u2 b1 b2 b3 b4 b5 b6 b7 u3 u4 u5 u6 mo1 Hag1 HK1.
    set (code := if 128 <=? bv_unsigned d1 then 0 else status).
    assert (CR : 0 <= code < 2^32) by (subst code; destruct (128 <=? _); lia).
    pose proof (proj1 (proj2 (proj2 (proj2 (magree_frame _ _ Hag1))))) as Efs1.
    (* [comment removed for export] *)
    aseg DI HK1. zstepA. aleaf. intros mo2 Hag2 HK2 Efs2 Efds2 Hh2.
    eapply (adi_free _ _ _ _ DI) with (lo := usp0 - 8388608) (A := A);
      [ apply KEXIT_nil | exact HK2 | right; exists (mkABlock A cap); split; [exact INB| reflexivity]
      | rewrite unsigned_lit by lia; exact ST | aceil; lia
      | rewrite unsigned_lit by lia; unfold AMALLOC_STACK; lia | clear -SF; rewrite unsigned_lit by lia; Z.div_mod_to_equations; lia
      | rewrite unsigned_lit by lia; lia
      | reflexivity | apply (adi_uanchorC _ _ _ _ DI); [in_lits| rewrite unsigned_lit by lia; aceil; lia]
      | exact FRM | reflexivity | unfold afree_cost; destruct (A =? 0); lia | apply nbig_small; lia | ].
    intros w0 w1 w2 rb0 e1 e2 e3 e4 e5 e6 e7 w3 w4 w5 w6 F3 fc3 m3 mo3 s3 ST3 HPR3 FRM3 SOE3 HK3 REL3 FS3 FDS3 CR3.
    rewrite ?(unsigned_lit (usp0 + -128)) in ST3 by lia. rewrite ?(unsigned_lit (usp0 + -128)) in HPR3 by lia.
    replace (ret_pc (Z_to_bv 64 0x81ca0)) with (Z_to_bv 64 0x81ca0) by (symmetry; rpc).
    unfold KEXIT. fold code. replace FS0 with (m_fs mo3) by (rewrite FS3, Efs2, Efs1; exact FS). rewrite <- SOE, <- SOE3.
    eapply (az_main_return sp0 argv VSP RCSP D DI DIx code s3 _ LF mo3).
    - unfold MFRAME. eapply rw_cells_agree; [eapply aheap_pres_agree; exact HPR3| exact FR| intros ax Ha; left; cbn in Ha; lia].
    - unfold LO. exact ST3.
    - exact HK3.
    - (* [comment removed for export] *)
      destruct AS as (_ & _ & AX0).
      eapply (atx_ok_agree _ _ _ (aheap_pres_agree _ _ _ _ _ _ HPR3)); [| exact AX0]. intros a Ha. right; right; right.
      unfold adrv_static. cbn [c_seg3_lo c_seg3_hi c_initialized c_ystat_lo c_ystat_hi ACONSTS]. lia.
    - exact (adi_mem_inv _ _ _ _ DI _ _ _ _ _ HK3).
    - exact FRM3.
    - exact CR.
  Qed.

  (* [comment removed for export] *)
  Lemma az_after_loop : forall (FILE : list byte) cap s mo ms,
    RDBRK' 3 P1v (FdFile pathb (Z_to_bv 64 (Z.of_nat (length FILE)))) cap FILE s mo ms ->
    Z.of_nat (length FILE) < cap ->
    realizes_cfg acfg asegs (mkCfg ms mo) (KDONE FILE).
  Proof.
    intros FILE cap s mo ms RB LTC.
    destruct RB as (x1 & t0 & t1 & t2 & a0 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & x23 & t3 & t4 & t5 & t6 & F & fc & mm & A & -> & RC).
    destruct RC as (junk & H & BU & HKx & HD & HB & SO0 & FD & FS & FR & BA & FRM).
    destruct BU as (BLK & [CAPR CAPK] & LENR & BR). pose proof BR as (BR1 & BR2 & BR3 & BR4 & BR5).
    aceil_in BR4. unfold MAX_INPUT in CAPR. cbn [c_img_hi ACONSTS] in BR5.
    pose proof (sp_facts sp0 VSP RCSP) as SF. unfold LO in SF.
    pose proof BA as (ST & MI & IMG & AS). unfold LO in ST. pose proof FR as FR0. unfold MFRAME in FR.
    pose proof (PSTK [mkABlock A cap]) as PS.
    aseg DI HKx. zstepA. zstepA. aleaf. intros moa Haga HKa Efsa Efdsa Hha.
    (* [comment removed for export] *)
    eapply (adi_close _ _ _ _ DI) with (lo := usp0 - 8388608) (fd := 3);
      [ apply KDONE_nil | exact HKa | lia | rewrite unsigned_lit by lia; exact ST | aceil; lia
      | rewrite unsigned_lit by lia; lia | reflexivity | reflexivity | ].
    intros u0 u1 u2 b0 b1 b2 b3 b4 b5 b6 b7 u3 u4 u5 u6 m1 mo1 s1 ST1 MUc WMc HK1 AS1 SO1 Efs1 Efds1 Hag1.
    rewrite ?(unsigned_lit (usp0 + -128)) in MUc by lia. rewrite ?(unsigned_lit (usp0 + -128)) in ST1 by lia. cbn [c_errno ACONSTS] in MUc.
    replace (ret_pc (Z_to_bv 64 0x81ba0)) with (Z_to_bv 64 0x81ba0) by (symmetry; rpc).
    assert (VS1 : vm_same moa (snd (close_out 3 moa))).
    { unfold close_out. destruct (fd_lookup (m_fds moa) (Z_to_bv 64 3)); cbn [snd]; [apply vm_same_with_fds | apply vm_same_refl]. }
    assert (WOKW : Forall (AWOK sp0) [(usp0 - 8388608, usp0 + -128); (0x5e0a6c, 0x5e0a6c + 4)]).
    { unfold AWOK, LO. constructor; [cbn [fst snd]; lia|]. constructor; [cbn [fst snd]; lia| constructor]. }
    pose proof (adi_mem_inv _ _ _ _ DI _ _ _ _ _ HK1) as MI1.
    assert (BA1 : ABASE' m1) by (eapply (ABASE_munch sp0 argv envp uid hw rnd VSP RCSP VARGV VENVP); [exact BA| exact WOKW| exact MUc| exact WMc| exact MI1| unfold LO; exact ST1]).
    pose proof (agree_on_of_munch _ _ _ MUc WMc) as AG.
    assert (FR1 : FRAME' m1) by (unfold MFRAME; eapply rw_cells_agree; [exact AG | exact FR | intros ax Ha; cbn in Ha |- *; lia]).
    assert (BLK1 : rw_cells asegs m1 A [CB (length FILE) FILE; CB (Z.to_nat (cap - Z.of_nat (length FILE))) junk]).
    { eapply rw_cells_agree; [exact AG | exact BLK | intros ax Ha; cbn [cells_size csize Nat.add] in Ha; cbn; lia]. }
    pose proof (adi_hd_aps _ _ _ _ DI _ _ _ _ _ _ (adi_hd_magree _ _ _ _ DI _ _ _ _ _ _ (adi_hd_vmsame _ _ _ _ DI _ _ _ _ _ _ (adi_hd_magree _ _ _ _ DI _ _ _ _ _ _ HD Haga) VS1) Hag1) AS1) as HD1.
    assert (FS1 : m_fs mo1 = FS0) by (rewrite Efs1, Efsa; exact FS).
    clear MUc WMc WOKW AG ST MI IMG AS FR BLK.
    pose proof BA1 as (ST & MI & IMG & (G & E & IB)). unfold LO in ST.
    pose proof BLK1 as BLKB. apply (proj1 (rw_cells_app _ _ _ [CB (length FILE) FILE] _)) in BLKB. destruct BLKB as [BLKB _].
    apply rw_cells_bytes_at in BLKB. cbn [cells_bytes cbytes app] in BLKB. rewrite app_nil_r in BLKB.
    pose proof (PSTK [mkABlock A cap]) as PS1. pose proof (pol_img [mkABlock A cap]) as PI1.
    pose proof (pol_blk [mkABlock A cap] (mkABlock A cap)) as PB1. cbn [ab_addr ab_size] in PB1. specialize (fun a n => PB1 a n (or_introl eq_refl) BR).
    unfold KDONE.
    aseg DI HK1. zstepA. zstepA. if_cases K0; zify_cond K0.
    { (* [comment removed for export] *)
      replace (length FILE <? 6)%nat with true by (symmetry; apply Nat.ltb_lt; lia).
      do 8 zstepA. aleaf. intros mo2 Hag2 HK2 Efs2 Efds2 Hh2.
      change pieces_short_hdr with [s_short].
      eapply (az_fwrite_ret s_short A_S_short s1 A cap [] mo2); [apply s_short_ro | reflexivity | unfold s_short; apply Forall_app; split; [apply str_range| constructor; [lia| constructor]]
        | unfold A_S_short; lia | unfold A_S_short; lia | exact HK2 | eexists; eexists; eexists; eapply (adi_hd_magree _ _ _ _ DI); [exact HD1| exact Hag2] | rewrite SO1; exact SO0 | exact FR1 | exact BA1 | exact FRM | rewrite Efs2; exact FS1]. }
    replace (length FILE <? 6)%nat with false by (symmetry; apply Nat.ltb_ge; lia).
    destruct (list6 FILE ltac:(lia)) as (d0 & d1 & d2 & d3 & d4 & d5 & rest & ED).
    pose proof (byte_range d0) as Rd0. pose proof (byte_range d1) as Rd1. pose proof (byte_range d2) as Rd2.
    assert (N0 : nth 0 FILE (Z_to_bv 8 0) = d0) by (rewrite ED; reflexivity).
    assert (N1 : nth 1 FILE (Z_to_bv 8 0) = d1) by (rewrite ED; reflexivity).
    rewrite N0, N1. cbv zeta.
    remember (bv_unsigned d0 + 256 * bv_unsigned d1) as cw eqn:Ecw.
    set (L := cw mod 32768). assert (RL : 0 <= L < 32768 /\ L <= cw) by (subst L; Z.div_mod_to_equations; lia).
    pose proof (u8ro_read asegs m1 _ _ 1 d1 (wa (A + 1)) BLKB ltac:(rewrite ED; reflexivity) ltac:(lia) eq_refl) as R1.
    zstepA. clear R1. cbv beta.
    pose proof (u8ro_read asegs m1 _ _ 0 d0 (wa (A + 0)) BLKB ltac:(rewrite ED; reflexivity) ltac:(lia) eq_refl) as R0.
    zstepA. clear R0. cbv beta.
    (* [comment removed for export] *)
    zstepA. zstepA. zstepA.
    replace (bv_unsigned (sxb d1)) with ((sx8 (bv_unsigned d1)) mod 2^64) by (unfold sxb; rewrite Z_to_bv_unsigned, signed_byte; reflexivity).
    rewrite (cfg15_Zm _ _ Rd0 Rd1). rewrite land15_mod. replace (bv_unsigned d0 + bv_unsigned d1 * 256) with cw by lia. fold L.
    zstepA. zstepA. if_cases K1; zify_cond K1.
    { (* [comment removed for export] *)
      replace (Z.of_nat (length FILE) <? 6 + L) with true by (symmetry; apply Z.ltb_lt; lia).
      do 7 zstepA. aleaf. intros mo2 Hag2 HK2 Efs2 Efds2 Hh2.
      change pieces_cfg_overrun with [s_over].
      eapply (az_fwrite_ret s_over A_S_overrun s1 A cap [] mo2); [apply s_over_ro | reflexivity | unfold s_over; apply Forall_app; split; [apply str_range| constructor; [lia| constructor]]
        | unfold A_S_overrun; lia | unfold A_S_overrun; lia | exact HK2 | eexists; eexists; eexists; eapply (adi_hd_magree _ _ _ _ DI); [exact HD1| exact Hag2] | rewrite SO1; exact SO0 | exact FR1 | exact BA1 | exact FRM | rewrite Efs2; exact FS1]. }
    replace (Z.of_nat (length FILE) <? 6 + L) with false by (symmetry; apply Z.ltb_ge; lia).
    zstepA. zstepA.
    (* [comment removed for export] *)
    destruct (skipn4 FILE (Z.to_nat (2 + L)) ltac:(lia)) as (q0 & q1 & q2 & q3 & rest' & EQ4).
    pose proof (byte_range q0) as Rq0. pose proof (byte_range q1) as Rq1. pose proof (byte_range q2) as Rq2. pose proof (byte_range q3) as Rq3.
    assert (QB : bytes_at asegs m1 (A + 2 + L) (q0 :: q1 :: q2 :: q3 :: rest')).
    { rewrite <- EQ4. rewrite <- (firstn_skipn (Z.to_nat (2 + L)) FILE) in BLKB.
      apply bytes_at_app in BLKB. destruct BLKB as [_ X]. rewrite length_firstn in X.
      replace (A + Z.of_nat (Nat.min (Z.to_nat (2 + L)) (length FILE))) with (A + 2 + L) in X by lia. exact X. }
    assert (SH1 : 0 <= Z.shiftl (bv_unsigned q1) 8 < 2^64) by (rewrite Z.shiftl_mul_pow2 by lia; lia).
    assert (SH2 : 0 <= Z.shiftl (bv_unsigned q2) 16 < 2^64) by (rewrite Z.shiftl_mul_pow2 by lia; lia).
    assert (SH3 : 0 <= Z.shiftl (bv_unsigned q3) 24 < 2^64) by (rewrite Z.shiftl_mul_pow2 by lia; lia).
    pose proof (u8ro_read asegs m1 _ _ 1 q1 (wa (A + 2 + L + 1)) QB eq_refl ltac:(lia) eq_refl) as R1.
    zstepA. clear R1. cbv beta.
    pose proof (u8ro_read asegs m1 _ _ 0 q0 (wa (A + 2 + L)) QB eq_refl ltac:(lia) ltac:(unfold wa; f_equal; lia)) as R0.
    zstepA. clear R0. cbv beta.
    pose proof (u8ro_read asegs m1 _ _ 2 q2 (wa (A + 2 + L + 2)) QB eq_refl ltac:(lia) eq_refl) as R2.
    zstepA. clear R2. cbv beta.
    pose proof (u8ro_read asegs m1 _ _ 3 q3 (wa (A + 2 + L + 3)) QB eq_refl ltac:(lia) eq_refl) as R3.
    zstepA. clear R3. cbv beta.
    do 9 zstepA.
    (* [comment removed for export] *)
    zstepA. zstepA.
    replace (ret_pc (Z_to_bv 64 0x81c04)) with (Z_to_bv 64 0x81c04) by (symmetry; rpc).
    zstepA. zstepA. zstepA. zstepA. zstepA. aleaf. intros mo2 Hag2 HK2 Efs2 Efds2 Hh2.
    (* [comment removed for export] *)
    replace (Z.of_nat (length FILE) - L + -6) with (Z.of_nat (length FILE) - 6 - L) by lia.
    replace (A + 2 + L + 4) with (A + 6 + L) by lia.
    replace (sxb d1) with (Z_to_bv 64 (sx8 (bv_unsigned d1))) by (unfold sxb; rewrite signed_byte; reflexivity).
    set (PL := Z.of_nat (length FILE) - 6 - L) in *.
    assert (HPL : 0 <= PL) by (subst PL; lia).
    assert (HLEN : Z.of_nat (length FILE) = 6 + L + PL) by (subst PL; lia).
    assert (HCAPM' : cap <= 67108864) by lia.
    eapply (az_target_run sp0 argv envp uid hw rnd arg0 arg1 PAD S4 S5 S6 S7 x23 S8 S9 S10 S11 VSP RCSP EFIT VARGV VENVP EARGV D DI DIx FS0
              A cap L PL (sx8 (bv_unsigned d1)) FILE H (abud cap) (proj1 RL) HPL HLEN LTC HCAPM' HB (fun st so => KEXIT (128 <=? bv_unsigned d1) st so)
              ltac:(intros; apply KEXIT_nil)).
    - intros status so s' mo' mm' fc' v0 v1 v2 c1 c2 c3 c4 c5 c6 c7 v3 v4 v5 v6 F' SR RI. eapply (az_after_run x23); [exact SR | exact RI].
    - exact FR1.
    - exact BA1.
    - exact HK2.
    - eapply (adi_hd_magree _ _ _ _ DI); [exact HD1| exact Hag2].
    - (* [comment removed for export] *) destruct CAPK as [kk [Kk0 CAPK']]. rewrite CAPK'.
      pose proof (abud_ge kk) as GE. destruct (Z_lt_le_dec 26 kk) as [Lk|Lk].
      + exfalso. pose proof (Z.pow_lt_mono_r 2 26 kk ltac:(lia) ltac:(lia) Lk). lia.
      + specialize (GE (conj Kk0 Lk)). lia.
    - rewrite SO1; exact SO0.
    - rewrite Efs2; exact FS1.
    - exact BLK1.
    - exact BR.
    - exact FRM.
  Qed.
End D.
End RC__1.
