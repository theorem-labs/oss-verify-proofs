(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation Strings.String.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP Agree MonadX Ceiling.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Lib Require Import RunWord.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.A0.ZAW Require Import Segs Shadow Contracts Globals IcptA0 AllocA0.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Lib Require Import InitStack EntrySecret.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Spec Require Import Prelim STree Monad Stdio Driver Prog.
From OSSVerify.pupnp.FuzzHttp.images Require Import Asan.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.ASN Require Import AsanAcct.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Top Require Import AllocIF.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.A0.T7 Require Import RealizeS SeamA0 A0Prog AssembleA0.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.A0.T7A0 Require Import ShadowKit GlobalsShadow Stdio_base Printf_lib F_printf_iface Stdio_iface F_printf_diag Exit RDriverA_kit RDriverA_ctx RDriverA_main RDriverA_exit RF_mainA_A.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.A0.T7A0 Require Import F_syscalls RDriverA_lib RDriverA_iface RF_mainA_B1 RF_mainA_B2 RF_mainA_B3 RF_mainA_B4.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Open Scope mspec_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
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
  Context {HC : HasCeiling} {HG : HasGuard}.
  Variable FI : fs_if.
  Variable AI : am_if FI.
  Hypothesis AMS : forall lo hi, a0_static lo hi -> am_static FI AI lo hi.
  Variable PZ : mem -> Prop.
  Hypothesis PZ_agree : forall (P : Z -> Prop) m m', gagree_on P m m' -> (forall a, pz_band a -> P a) -> PZ m -> PZ m'.
  Variables (sp0 : word) (argv envp : list (list byte)) (uid hw : word) (rnd : EntryDraw) (arg0 arg1 : list byte) (TID : Z)
            (MPAD : list byte) (S4 S5 S6 S7 S8 S9 S10 S11 : word).
  Hypothesis VSP : valid_sp sp0.
  Hypothesis CEIL : alloc_ceiling = LO sp0.
  Hypothesis VARGV : valid_argv argv.
  Hypothesis VENVP : valid_envp envp.
  Hypothesis ESF : entry_stack_fits sp0 argv envp.
  Hypothesis EARGV : argv = [arg0; arg1].
  Hypothesis HT : 0 < TID < 2^31.
  Hypothesis AC : am_contracts FI AI (JA FI AI).
  Hypothesis FPR : @fprintf_diag_stmt HC ASt.
  Hypothesis EXK : forall TID, 0 < TID < 2^31 -> exit_k_stmtA TID.
  Hypothesis FWR : @fwrite_diagA_stmt HC ASt.
  Hypothesis MCI : memcpy_i_stmt.
  Hypothesis RDF : read_front_stmt.
  Hypothesis RDB : read_back_stmt.
  Hypothesis BSR : forall s LB m b, RHEAP_A FI AI s LB m -> In b LB -> sh_readable m (blk_addr b) (blk_size b).

  Notation usp0 := (bv_unsigned sp0).
  Notation gpv := (Z_to_bv 64 0x10800).
  Notation tpv := (Z_to_bv 64 RATPA).
  Notation IMGB := (build_stack_bytes rph sp0 argv envp uid hw rnd).
  Notation LO' := (LO sp0).
  Notation BASE' := (BASE_A PZ sp0 argv envp uid hw rnd TID stdout_init).
  Notation FRAME' mm := (MFRAME sp0 argv mm MPAD S7 S6 S5 S4).
  Notation RDONE' := (RDONE FI AI PZ sp0 argv envp uid hw rnd TID MPAD S4 S5 S6 S7 S8 S9 S10 S11).
  Local Notation K := (am_K FI AI).

  Notation GST pc x1 t0 t1 t2 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 t3 t4 t5 t6 F fc mm :=
    (MS (mkR x1 (Z_to_bv 64 (usp0 + -128)) gpv tpv t0 t1 t2 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 (Z_to_bv 64 RSVA) (Z_to_bv 64 0) S8 S9 S10 S11 t3 t4 t5 t6)
        F (Z_to_bv 64 pc) fc None mm (seg_rom asegs)).

  Definition main_tailA (buf : unit) (content : list Z) (cw L cfg : Z) : M ASt (at_parser (ptr:=unit)) :=
    let payload_len := zlength content - HDR_MIN - L in
    let calls := 1 + Z.land cfg 3 in
    copy <- (if 0 <? payload_len then
               p <- amalloc0 payload_len ;;
               mret (match p with None => None | Some p' => Some (Some p') end)
             else mret (Some None)) ;;
    match copy with
    | None => afree0 buf ;;; exit_k ioA (main_status (Z.testbit cw 15) 2)
    | Some owned => mret (mkAP buf content (Z.testbit cw 15) L calls owned)
    end.

  Definition main_restA (buf : unit) (content : list Z) : M ASt (at_parser (ptr:=unit)) :=
    let len := zlength content in
    if len <? HDR_MIN then io_diag ioA DShortHdr ;;; afree0 buf ;;; exit_k ioA 2
    else
      let cfg_word := le16 content in
      let config_len := Z.land cfg_word 0x7fff in
      if len <? HDR_MIN + config_len then io_diag ioA DCfgOverrun ;;; afree0 buf ;;; exit_k ioA 2
      else
        let cfg := if 0 <? config_len then znth content 2 else 0 in
        main_tailA buf content cfg_word config_len cfg.

  #[using="arg0 EARGV"] Lemma drv_preA_eq : drv_preA RSVA (argv_Z argv)
    = (ra <- read_all ioA amalloc0 afree0 RSVA (map bv_unsigned arg1) ;;
       match ra with RdExit => exit_k ioA 2 | RdDone buf content => main_restA buf content end).
  Proof. unfold drv_preA, drv_pre, argv_Z. rewrite EARGV. reflexivity. Qed.

  Definition HDR (A cap : Z) (DATA : list byte) (cw L cfg sc : Z) : Prop :=
    6 + L <= Z.of_nat (length DATA) /\ Z.of_nat (length DATA) <= cap /\ cap <= MAX_INPUT
    /\ (0x609000 <= A /\ A + cap + 16 <= alloc_ceiling /\ A mod 16 = 0 /\ win_ok A (cap + 16))
    /\ 0 <= cw < 65536 /\ L = Z.land cw 32767 /\ 0 <= L < 32768 /\ L <= cw /\ cw = le16 (map bv_unsigned DATA)
    /\ cfg = (if 0 <? L then znth (map bv_unsigned DATA) 2 else 0) /\ 0 <= cfg < 256
    /\ -128 <= sc < 128 /\ (Z.testbit cw 15 = (sc <? 0)).

  Definition RUN0 (b : unit) (A cap : Z) (DATA : list byte) (cw L cfg sc : Z) (so : ASt) (ms : machine_state) (g : gst) : Prop :=
    exists (x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (mm : mem)
           (junk : list byte) (errv : word) (kb : K),
      ms = GST 0x861d4 x1 t0 t1 t2 (Z_to_bv 64 (A + 2)) (Z_to_bv 64 A) a0 a1 a2 a3 a4 a5 a6 a7
               (Z_to_bv 64 L) (Z_to_bv 64 (A + 6 + L)) (Z_to_bv 64 (Z.of_nat (length DATA) - 6 - L)) (Z_to_bv 64 sc) t3 t4 t5 t6 F fc mm
      /\ HDR A cap DATA cw L cfg sc
      /\ HEAP FI AI mm g [(kb, A, cap)] /\ so = stdout_init
      /\ rw_cells asegs mm A [CB (length DATA) DATA; CB (Z.to_nat (cap - Z.of_nat (length DATA))) junk]
      /\ rw_cells asegs mm (sh A) (shadow_cells (block_shadow cap))
      /\ FRAME' mm /\ BASE' mm /\ CJ0 mm /\ rw_cells asegs mm RERRNOA [C4 errv] /\ frm0 fc.

  #[using="Type"] Lemma lb_remove_self : forall (k : K) A n, lb_remove (am_K_eqb FI AI) k [(k, A, n)] = [].
  Proof.
    intros k A n. unfold lb_remove. rewrite filter_cons, filter_nil. cbn [blk_id fst].
    replace (am_K_eqb FI AI k k) with true by (symmetry; apply (proj2 (am_K_eqb_eq FI AI k k)); reflexivity).
    cbn [negb]. destruct (decide (Is_true false)) as [Y|N]; [exfalso; exact Y| reflexivity].
  Qed.

  #[using="AMS PZ_agree VSP CEIL ESF HT AC EXK FWR"] Lemma diagC_exit : forall (d : diag_msg) (msg : list Z) (PA : Z) (so : ASt) (b : unit) (kb : K) (A cap : Z)
      (Q : at_parser (ptr:=unit) -> ASt -> machine_state -> gst -> Prop) (g : gst)
      x1 t0 t1 t2 x14 x15 x16 x17 x18 x19 x20 x21 t3 t4 t5 t6 (F : bvmap 5 word) (fc : bv 32) (mm : mem),
    s_diag (St:=ASt) d = stderr_fwrite msg -> ro_bytes_b asegs PA (zb msg) = true -> zlength msg = 31 -> Forall (fun c => 0 <= c < 256) msg ->
    0x10000 <= PA -> PA + 31 <= 0x213e0 ->
    HEAP FI AI mm g [(kb, A, cap)] -> so = stdout_init -> FRAME' mm -> BASE' mm ->
    djM (io_diag ioA d ;;; afree0 b ;;; exit_k ioA 2) so Q
      (GST 0x86264 x1 t0 t1 t2 (Z_to_bv 64 2) (Z_to_bv 64 A) (Z_to_bv 64 PA) (Z_to_bv 64 31) (Z_to_bv 64 1) (Z_to_bv 64 RSTDERR) x14 x15 x16 x17 x18 x19 x20 x21 t3 t4 t5 t6 F fc mm) g.
  Proof.
    intros until mm. intros ED RO ML RNG LOA HIA HP0 SO FR BA. subst so.
    pose proof (sp_facts sp0 VSP CEIL) as SF. pose proof (IMGB_len47 sp0 argv envp uid hw rnd ESF) as IL47. pose proof alloc_ceiling_bounds as CB'. unfold LO in SF.
    pose proof BA as (ST & MI & EX & MC & IMG & SE & SOF & RSS & SI & SZ & ENV & GSH & HPZ & CRT). unfold LO in ST. unfold MFRAME in FR.
    destruct MC as (G28 & GSE & SSP).
    cbn [io_diag ioA io_S]. rewrite ED.
    eapply djM_evt; [| intros msr' H; exact H]. zstep. apply evt_done.

    eapply djM_bind.
    { eapply djM_of_implM; [| fdt].
      eapply (FWR) with (lo := usp0 - 8388608) (s := msg) (canary := guard_word); rewrite ?unsigned_lit by lia;
        first [ exact SE | exact RO | exact RNG | rewrite ML; lia | rewrite ML; reflexivity | reflexivity | exact ST | exact SSP | exact MI | exact ENV
              | unfold RO_LO; lia | unfold RO_LO, RO_SZ; lia | unfold FWRITE_DEPTH, A0_RT_STACK; lia | unfold GLOBALS_TOP; lia | lia
              | unfold RO_LO, RO_SZ; apply (SHZ_ro sp0 argv envp uid hw rnd); exact SZ ]. }
    cbv beta. intros [] so1 ms1 g1 [PO ->].
    destruct PO as (u0 & u1 & u2 & b0 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & m1 & -> & MUc & WMc & MI1 & ST1 & SEW & SSP1 & ENV1 & ->).
    rewrite !unsigned_lit in MUc by lia. rewrite !unsigned_lit in ST1 by lia.
    replace (ret_pc (Z_to_bv 64 0x86268)) with (Z_to_bv 64 0x86268) by (symmetry; rpc).
    pose proof (gagree_on_of_munch _ _ _ MUc WMc) as AG.
    assert (BA1 : BASE' m1).
    { eapply (BASE_A_agree_se PZ PZ_agree sp0 argv envp uid hw rnd TID VSP CEIL ESF HT stdout_init); [exact BA| exact AG| | exact WMc| exact MI1| unfold LO; exact ST1| | exact ENV1| exact SEW].
      - intros a Ha Hs. unfold base_addr, exitc_addr, stdout_addr, stderr_addr, stdin_addr, pz_band, sh, SHADOW_OFF, SH_HI in *. cbn [outside fst snd].
        clear -Ha Hs SF IL47 CB'. split; [| split; [| exact I]]; Z.div_mod_to_equations; lia.
      - eapply stk_gagree; [exact AG| exact RSS| intros a Ha; cbn [outside fst snd]; unfold RSVA in *; lia]. }
    assert (HP1 : HEAP FI AI m1 g [(kb, A, cap)]).
    { destruct HP0 as (sA & stA & RH & RF & Eg). exists sA, stA. split; [| split; [| exact Eg]].
      - eapply (am_heap_frame FI AI); [exact RH| exact MUc| exact WMc|].
        repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd];
          first [ left; lia | right; left; exists 0xae6c0, 0xaedc0; split; [apply AMS; unfold a0_static; lia| unfold a0_wsafe; lia] ].
      - pose proof (fsb_ok FI) as FB. unfold app_mem in FB.
        eapply (rfake_frame FI); [exact RF| exact MUc| exact WMc|].
        repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd]; left; unfold sh, SHADOW_OFF in *; Z.div_mod_to_equations; lia. }
    assert (FR1 : FRAME' m1).
    { unfold MFRAME. eapply rw_cells_transport; [exact FR| exact MUc| exact WMc| cbn [disjoint_from]; simpl_sizes; lia]. }
    clear MUc WMc AG BA FR ST MI EX G28 GSE SSP IMG SE SOF RSS SI SZ ENV GSH HPZ CRT HP0.
    pose proof BA1 as (ST & MI & EX & MC & IMG & SE & SOF & RSS & SI & SZ & ENV & GSH & HPZ & CRT). unfold LO in ST. destruct MC as (G28 & GSE & SSP).

    eapply djM_evt; [| intros msr' H; exact H]. zstep. zstep. apply evt_done.
    apply djM_mret_bind.
    destruct HP1 as (sA & stA & RH & RF & Eg & _ & _). subst g.
    pose proof (am_stack_ok FI AI) as SOK.
    eapply djM_seam.
    { eapply ((ac_free_any FI AI (JA FI AI) AC)) with (lo := usp0 - 8388608) (k := kb) (A := A) (n := cap);
        rewrite ?unsigned_lit by lia;
        first [ exact RH | left; reflexivity | exact ENV | exact RF | exact ST | exact MI | reflexivity | lia | unfold A0_RT_STACK; lia
              | cbn [fpchain]; unfold valid_frame; lia
              | cbn; tauto
              | clear -SF; Z.div_mod_to_equations; lia ]. }
    cbv beta. intros msr2 g2 (s2 & LB2 & -> & PO).
    destruct PO as (w0 & w1 & w2 & ra0 & d1 & d2 & d3 & d4 & d5 & d6 & d7 & w3 & w4 & w5 & w6 & m2 & -> & AFR & -> & RH2).
    rewrite lb_remove_self in AFR, RH2.
    assert (BA2 : BASE' m2) by (eapply (BASE_A_alloc FI AI AMS PZ PZ_agree sp0 argv envp uid hw rnd TID VSP CEIL ESF HT stdout_init); [exact BA1| unfold LO; exact AFR]).
    destruct AFR as (MI2 & ST2 & ENV2 & RF2 & AP2).
    assert (FR2 : FRAME' m2) by (unfold MFRAME in *; eapply (apres_rw_cells FI AI); [exact AP2| exact FR1| apply aclient_range_above; lia]).
    replace (ret_pc (Z_to_bv 64 0x86270)) with (Z_to_bv 64 0x86270) by (symmetry; rpc).
    pose proof BA2 as (ST3 & MI3 & EX3 & MC3 & IMG3 & SE3 & SOF3 & RSS3 & SI3 & SZ3 & ENV3 & GSH3 & HPZ3 & CRT3). destruct MC3 as (G28' & GSE' & [GG GU]).
    unfold got_ssp, ssp_guard in GG, GU.

    eapply djM_evt.
    { eapply (main_return sp0 argv TID VSP CEIL 2 stdout_init);
        [exact FR2| unfold LO; exact ST3| exact EX3| exact CRT3| exact ENV3| exact GSH3| exact GG| exact GU| exact SOF3| apply stderr_wfile0_file; exact SE3| exact SI3| exact MI3]. }
    cbv beta. intros msx Hx. eapply djM_mono; [eapply (djM_of_implM _ _ (fun (_ : at_parser) (_ : ASt) (_ : machine_state) => False)); [exact (EXK TID HT _ 2 _ _ msx Hx)| fdt] |].
    cbv beta. intros r so' ms' g' [F0 _]. destruct F0.
  Qed.

  #[using="AMS PZ_agree VSP CEIL ESF HT AC EXK FWR"] Lemma phaseC : forall b content so ms g (Q : at_parser (ptr:=unit) -> ASt -> machine_state -> gst -> Prop),
    RDONE' b content so ms g ->
    (forall DATA A cap cw L cfg sc so1 ms1 g1, content = map bv_unsigned DATA -> RUN0 b A cap DATA cw L cfg sc so1 ms1 g1 ->
       djM (main_tailA b content cw L cfg) so1 Q ms1 g1) ->
    djM (main_restA b content) so Q ms g.
  Proof.
    intros b content so ms g Q RD K.
    destruct RD as (x1 & t0 & t1 & t2 & a0 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & F & fc & mm & A & cap & P1v & fd & DATA & junk & errv & kb
                    & -> & HCT & -> & BU & FR & BA & CJ & ERR & FRM).
    pose proof (sp_facts sp0 VSP CEIL) as SF. pose proof (IMGB_len47 sp0 argv envp uid hw rnd ESF) as IL47. pose proof alloc_ceiling_bounds as CB'. unfold LO in SF.
    pose proof BA as (ST & MI & EX & MC & IMG & SE & SOF & RSS & SI & SZ & ENV & GSH & HPZ & CRT). unfold LO in ST. destruct MC as (G28 & GSE & SSP).
    pose proof ERR as ERR0. unfold RERRNOA in ERR. pose proof FR as FR0. unfold MFRAME in FR.
    pose proof BU as (HP0 & BLK & BSH & [CAPR CAPK] & LENR & BR1 & BR2 & BR3 & BR4).
    assert (LENZ : zlength content = Z.of_nat (length DATA)) by (rewrite HCT; unfold zlength; rewrite length_map; reflexivity).
    pose proof BLK as BLKB. apply (proj1 (rw_cells_app _ _ _ [CB (length DATA) DATA] _)) in BLKB. destruct BLKB as [BLKB _].
    apply rw_cells_bytes_at in BLKB. cbn [cells_bytes cbytes app] in BLKB. rewrite app_nil_r in BLKB.
    unfold main_restA. rewrite LENZ. unfold HDR_MIN.
    remember (length DATA) as nD eqn:HnD.
    eapply djM_evt; [| intros msr' H; exact H].
    zstep. zstep. if_cases K0; zify_cond K0.
    {
      replace (Z.of_nat nD <? 6) with true by (symmetry; apply Z.ltb_lt; lia). cbv iota.
      zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. apply evt_done.
      eapply (diagC_exit DShortHdr s_short S_SHORT_A); [reflexivity| apply s_short_ro| reflexivity| unfold s_short; apply Forall_app; split; [apply str_range| constructor; [lia| constructor]]
        | unfold S_SHORT_A; lia| unfold S_SHORT_A; lia| exact HP0| reflexivity| exact FR0| exact BA]. }

    replace (Z.of_nat nD <? 6) with false by (symmetry; apply Z.ltb_ge; lia). cbv iota.
    destruct (list6 DATA ltac:(lia)) as (d0 & d1 & d2 & d3 & d4 & d5 & rest & ED). subst DATA. subst content.
    pose proof (byte_range d0) as Rd0. pose proof (byte_range d1) as Rd1. pose proof (byte_range d2) as Rd2.
    rewrite le16_cons.
    remember (bv_unsigned d0 + bv_unsigned d1 * 256) as cw eqn:Ecw.
    assert (RL : 0 <= Z.land cw 32767 <= cw) by (rewrite land15_mod; Z.div_mod_to_equations; lia).
    pose proof (u8ro_read asegs mm _ _ 1 d1 (wa (A + 1)) BLKB eq_refl ltac:(lia) eq_refl) as R1.
    zstep. clear R1. cbv beta.
    pose proof (u8ro_read asegs mm _ _ 0 d0 (wa (A + 0)) BLKB eq_refl ltac:(lia) eq_refl) as R0.
    zstep. clear R0. cbv beta.

    zstep. zstep. zstep.
    replace (bv_unsigned (sxb d1)) with ((sx8 (bv_unsigned d1)) mod 2^64) by (unfold sxb; rewrite Z_to_bv_unsigned, signed_byte; reflexivity).
    rewrite (cfg15_Z _ _ Rd0 Rd1). rewrite <- Ecw.
    remember (Z.land cw 32767) as L eqn:EL.
    zstep. zstep. if_cases K1; zify_cond K1.
    {
      replace (Z.of_nat nD <? 6 + L) with true by (symmetry; apply Z.ltb_lt; lia). cbv iota.
      zstep. zstep. zstep. zstep. zstep. zstep. zstep. apply evt_done.
      eapply (diagC_exit DCfgOverrun s_over S_OVER_A); [reflexivity| apply s_over_ro| reflexivity| unfold s_over; apply Forall_app; split; [apply str_range| constructor; [lia| constructor]]
        | unfold S_OVER_A; lia| unfold S_OVER_A; lia| exact HP0| reflexivity| exact FR0| exact BA]. }
    replace (Z.of_nat nD <? 6 + L) with false by (symmetry; apply Z.ltb_ge; lia). cbv iota.
    zstep. zstep.

    destruct (skipn4 (d0 :: d1 :: d2 :: d3 :: d4 :: d5 :: rest) (Z.to_nat (2 + L)) ltac:(cbn [length] in *; lia)) as (q0 & q1 & q2 & q3 & rest' & EQ4).
    pose proof (byte_range q0) as Rq0. pose proof (byte_range q1) as Rq1. pose proof (byte_range q2) as Rq2. pose proof (byte_range q3) as Rq3.
    assert (QB : bytes_at asegs mm (A + 2 + L) (q0 :: q1 :: q2 :: q3 :: rest')).
    { rewrite <- EQ4. rewrite <- (firstn_skipn (Z.to_nat (2 + L)) (d0 :: d1 :: d2 :: d3 :: d4 :: d5 :: rest)) in BLKB.
      apply bytes_at_app in BLKB. destruct BLKB as [_ X]. rewrite length_firstn in X.
      replace (A + Z.of_nat (Nat.min (Z.to_nat (2 + L)) (length (d0 :: d1 :: d2 :: d3 :: d4 :: d5 :: rest)))) with (A + 2 + L) in X by (cbn [length] in *; lia). exact X. }
    assert (SH1 : 0 <= Z.shiftl (bv_unsigned q1) 8 < 2^64) by (rewrite Z.shiftl_mul_pow2 by lia; lia).
    assert (SH2 : 0 <= Z.shiftl (bv_unsigned q2) 16 < 2^64) by (rewrite Z.shiftl_mul_pow2 by lia; lia).
    assert (SH3 : 0 <= Z.shiftl (bv_unsigned q3) 24 < 2^64) by (rewrite Z.shiftl_mul_pow2 by lia; lia).
    pose proof (u8ro_read asegs mm _ _ 1 q1 (wa (A + 2 + L + 1)) QB eq_refl ltac:(lia) eq_refl) as R1.
    zstep. clear R1. cbv beta.
    pose proof (u8ro_read asegs mm _ _ 0 q0 (wa (A + 2 + L)) QB eq_refl ltac:(lia) ltac:(unfold wa; f_equal; lia)) as R0.
    zstep. clear R0. cbv beta.
    pose proof (u8ro_read asegs mm _ _ 2 q2 (wa (A + 2 + L + 2)) QB eq_refl ltac:(lia) eq_refl) as R2.
    zstep. clear R2. cbv beta.
    pose proof (u8ro_read asegs mm _ _ 3 q3 (wa (A + 2 + L + 3)) QB eq_refl ltac:(lia) eq_refl) as R3.
    zstep. clear R3. cbv beta.
    zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep.

    zstep. zstep. replace (ret_pc (Z_to_bv 64 0x861d4)) with (Z_to_bv 64 0x861d4) by (symmetry; rpc).
    apply evt_done.
    replace (Z_to_bv 64 (A + 2 + L + 4)) with (Z_to_bv 64 (A + 6 + L)) by (f_equal; lia).
    replace (Z_to_bv 64 (Z.of_nat nD + - L + -6)) with (Z_to_bv 64 (Z.of_nat (length (d0 :: d1 :: d2 :: d3 :: d4 :: d5 :: rest)) - 6 - L)) by (f_equal; lia).
    replace (sxb d1) with (Z_to_bv 64 (sx8 (bv_unsigned d1))) by (unfold sxb; rewrite signed_byte; reflexivity).
    eapply (K (d0 :: d1 :: d2 :: d3 :: d4 :: d5 :: rest) A cap cw L _ (sx8 (bv_unsigned d1))); [reflexivity|].
    unfold RUN0. do 20 eexists. exists errv, kb. split; [reflexivity|].
    split.
    { unfold HDR. cbn [length] in *. rewrite le16_cons, znth2_cons. unfold MAX_INPUT.
      split; [lia|]. split; [lia|]. split; [lia|]. split; [split; [lia|]; split; [lia|]; split; [lia| exact BR4]|]. split; [lia|]. split; [exact EL|].
      split; [rewrite EL, land15_mod; Z.div_mod_to_equations; lia|]. split; [lia|]. split; [exact Ecw|]. split; [reflexivity|].
      split; [destruct (0 <? L); lia|].
      split; [unfold sx8; destruct (Z.ltb_spec (bv_unsigned d1) 128); lia|].
      rewrite Ecw, (testbit15 _ _ Rd0 Rd1). unfold sx8.
      destruct (Z.ltb_spec (bv_unsigned d1) 128); [rewrite (proj2 (Z.leb_gt _ _)) by lia; symmetry; apply Z.ltb_ge; lia | rewrite (proj2 (Z.leb_le _ _)) by lia; symmetry; apply Z.ltb_lt; lia]. }
    split; [exact HP0|]. split; [reflexivity|].
    split; [rewrite HnD in BLK; exact BLK|]. split; [exact BSH|]. split; [exact FR0|]. split; [exact BA|]. split; [exact CJ|]. split; [exact ERR0| exact FRM].
  Qed.
End C.
