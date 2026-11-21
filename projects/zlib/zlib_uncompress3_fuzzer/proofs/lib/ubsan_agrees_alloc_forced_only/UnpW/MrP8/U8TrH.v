(* reloc-zl14c *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only Require Import RunCtx. (* reloc-zl14c *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
Require OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.PropExec OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.StdModel OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.ShapeAlg OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.ShapeLaws OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.Spec OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.U8TargetPre OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.U8World OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.U8LibStmt OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.U8Atexit.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import Tac Image ZBridge Walk Arr InitMem.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.Spec Require SM09. Import SM09. Import SM09.STree. From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.Spec Require Import Malloc. From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.Spec Require Import KInv. From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.Spec Require Import KLink. From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.Spec Require Import KEv.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.Malloc Require MM15. Import MM15. Import MM15.ProgDeps. From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.Malloc Require MM13. Import MM13. Import MM13.MallocBlocks.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.PlainU8 Require Import PImg RMallocRep RMallocTree RMalloc_iface RMalloc_ifaceP.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.Common Require Import RunDraw.
Require Import OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.Mr.MrFeasNull OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.Mr.MrFeasNull44 OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.Mr.MrFeasSome1 OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.Mr.MrFeasLift2 OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.Mr.MrRoom OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.Mr.MrRulesU8.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.MrP8 Require Import U8HeapPre U8HBase U8HConv U8SoDefs U8TrTail U8TrInv U8TrRun.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* kitfix4 alias stage: Module OT := OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.U8TargetPre expanded *)
(* kitfix4 alias stage: Module OSA := OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.ShapeAlg expanded *)
(* kitfix4 alias stage: Module OSp := OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.Spec expanded *)
(* kitfix4 alias stage: Module OAX := OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.U8Atexit expanded *)

(* [comment removed for export] *)
Lemma byte_range : forall b : byte, 0 <= bv_unsigned b < 256.
Proof. intros b. pose proof (bv_unsigned_in_range 8 b) as R. unfold bv_modulus in R. cbn in R. lia. Qed.

Lemma t_target_run : forall (content : list byte) (fs : Fs.Fs),
  6 + OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.U8TargetPre.hdr_cfglen content <= Z.of_nat (length content) ->
  OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.ShapeAlg.t_eq (T_run fs (calls_n (OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.U8TargetPre.hdr_cfglen content) (bv_unsigned (nth 2 content (Z_to_bv 8 0)))))
           (OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.U8TargetPre.t_target content fs).
Proof.
  intros content fs LEN6. unfold OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.U8TargetPre.t_target, T_run, calls_n.
  set (c2 := bv_unsigned (nth 2 content (Z_to_bv 8 0))).
  pose proof (byte_range (nth 2 content (Z_to_bv 8 0))) as C2. fold c2 in C2.
  pose proof (byte_range (nth 0 content (Z_to_bv 8 0))) as B0.
  pose proof (byte_range (nth 1 content (Z_to_bv 8 0))) as B1.
  unfold OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.U8TargetPre.hdr_paylen, OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.U8TargetPre.hdr_cfglen, OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.U8TargetPre.hdr_cfg, OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.U8TargetPre.hdr_b0, OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.U8TargetPre.hdr_b1 in *.
  set (b0 := bv_unsigned (nth 0 content (Z_to_bv 8 0))) in *. set (b1 := bv_unsigned (nth 1 content (Z_to_bv 8 0))) in *.
  set (cfg := b0 + 256 * b1) in *.
  assert (CL : 0 <= cfg mod 32768 < 32768) by (apply Z.mod_pos_bound; lia).
  (* [comment removed for export] *)
  assert (EC : match Z.to_nat (cfg mod 32768) with 0%nat => 1%nat | S _ => S (Z.to_nat (c2 mod 4)) end
               = S (if cfg mod 32768 =? 0 then 0%nat else Z.to_nat (Z.land c2 3))).
  { destruct (Z.eqb_spec (cfg mod 32768) 0) as [E|E].
    - rewrite E. reflexivity.
    - destruct (Z.to_nat (cfg mod 32768)) eqn:EN; [lia|]. f_equal. f_equal.
      change 3 with (Z.ones 2). rewrite Z.land_ones by lia. reflexivity. }
  rewrite EC. set (n := if cfg mod 32768 =? 0 then 0%nat else Z.to_nat (Z.land c2 3)).
  (* [comment removed for export] *)
  assert (ES : OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.ShapeAlg.t_eq (ShapeAlg.t_emit (Spec.W 1 [Z_to_bv 8 48; Z_to_bv 8 10])
                           (ShapeAlg.t_emit (Spec.W 1 (Spec.zero_lines n)) (ShapeAlg.t_exit (Spec.exit_code 0) fs)))
                        (ShapeAlg.t_emit (Spec.W 1 (Spec.zero_lines (S n))) (ShapeAlg.t_exit (Spec.exit_code 0) fs))).
  { exact (ShapeLaws.t_emit_W_app 1 [Z_to_bv 8 48; Z_to_bv 8 10] (Spec.zero_lines n) _). }
  destruct (Z.eqb_spec (Z.of_nat (length content) - 6 - cfg mod 32768) 0) as [EP|NP].
  - replace (length content - 6 - Z.to_nat (cfg mod 32768))%nat with 0%nat by lia. exact ES.
  - destruct (length content - 6 - Z.to_nat (cfg mod 32768))%nat eqn:EN; [lia|].
    (* Tier-2b port: the payload copy is always served; no NULL exit on either side. *)
    exact ES.
Qed.

(* [comment removed for export] *)
Section S0.
Context {RCa1 : RunCtx}.  (* a worker (A1) tool *)
Context {rc : runConstT}.

Ltac forget_regsR R :=
  repeat match goal with |- context [reg_get R ?k] => let x := fresh "x" in set (x := reg_get R k); clearbody x end.

Theorem target_phase_h : U8LibStmt.zlib_u2_contract_U8 -> target_phase_h_stmt.
Proof.
  intros C7 sp0 buf cap content R M mo H. destruct H.
  destruct th_heap as (s & pb & HH & HOWN & HDRV & HROOM).
  destruct th_sp0 as [SP0 SP16]. destruct th_len as [[LEN6 LENB] LENC].
  destruct th_tid as (tid & TID & TIDC). destruct th_errno as [errv ERR].
  assert (CFGR : 0 <= OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.U8TargetPre.hdr_cfglen content < 32768) by (unfold OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.U8TargetPre.hdr_cfglen; apply Z.mod_pos_bound; lia).
  pose proof (byte_range (nth 1 content (Z_to_bv 8 0))) as B1R. fold (OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.U8TargetPre.hdr_b1 content) in B1R.
  pose proof (byte_range (nth 2 content (Z_to_bv 8 0))) as C2R.
  pose proof (RHEAP_block_range_proof _ _ _ (pb, buf, cap) HH ltac:(left; reflexivity)) as (BR1 & BR2 & BR3 & BR4 & BR5).
  cbn [blk_addr blk_size fst snd] in *.
  (* [comment removed for export] *)
  eapply ShapeAlg.rz_conseq; [| apply (t_target_run content (m_fs mo) LEN6)].
  (* [comment removed for export] *)
  apply rz_mkR. unfold mkR_of.
  rewrite (th_ra : reg_get R (Z_to_bv 5 1) = _), (th_sp : reg_get R (Z_to_bv 5 2) = _),
          (th_tp : reg_get R (Z_to_bv 5 4) = _), (th_a0 : reg_get R (Z_to_bv 5 10) = _), (th_a1 : reg_get R (Z_to_bv 5 11) = _),
          (th_a2 : reg_get R (Z_to_bv 5 12) = _), (th_a3 : reg_get R (Z_to_bv 5 13) = _), (th_s1 : reg_get R (Z_to_bv 5 9) = _),
          (th_s5 : reg_get R (Z_to_bv 5 21) = _).
  forget_regsR R. clear th_ra th_sp th_gp th_tp th_a0 th_a1 th_a2 th_a3 th_s1 th_s5.
  (* [comment removed for export] *)
  pose proof (stk_of_stack_writable M sp0 (sp0 - 120) ltac:(lia) ltac:(lia) ltac:(lia) th_stack) as ST0.
  destruct (stk_carve (run_segments psegs rc_inp rc_sp rc_mb) M _ _ 8%nat ST0 ltac:(lia)) as [ST (junk & FR0)].
  replace (sp0 - 120 - Z.of_nat 8) with (sp0 - 128) in * by lia.
  assert (SOK : forall a, sp0 - 6144513 <= a -> a + 8 <= sp0 -> store_ok (run_segments psegs rc_inp rc_sp rc_mb) M (wa a) 8 = true).
  { intros a A1 A2. specialize (th_stack (a - (sp0 - 6144513)) 8%nat ltac:(lia) ltac:(lia)).
    replace (sp0 - 6144513 + (a - (sp0 - 6144513))) with a in th_stack by lia. exact th_stack. }
  assert (FRM : rw_cells (run_segments psegs rc_inp rc_sp rc_mb) M (sp0 - 128)
                  [CB 8 junk; C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 (sp0 + 32));
                   C8 (Z_to_bv 64 0x14904); C8 (Z_to_bv 64 2); C8 (Z_to_bv 64 (sp0 + 8)); C8 (Z_to_bv 64 0x19fac)]).
  { destruct th_frame as [F_ra F_s0 F_s1 F_s2 F_s3 F_s4 F_s5 F_s6 F_s7].
    apply rw_cells_cons; [exact FR0|]. cbn [csize].
    Ltac cell8 F SOK := apply rw_cells_cons; [apply rw_cell8_of_cell; [ | apply SOK; lia | lia | lia];
                         match goal with |- U8World.cell _ ?a _ _ => replace a with ltac:(let t := type of F in match t with U8World.cell _ ?b _ _ => exact b end) by lia end; exact F |]; cbn [csize].
    cell8 F_s7 SOK. cell8 F_s6 SOK. cell8 F_s5 SOK. cell8 F_s4 SOK. cell8 F_s3 SOK. cell8 F_s2 SOK. cell8 F_s1 SOK. cell8 F_s0 SOK.
    apply rw_cell8_of_cell; [ | apply SOK; lia | lia | lia].
    match goal with |- U8World.cell _ ?a _ _ => replace a with (sp0 - 56) by lia end. exact F_ra. }
  (* [comment removed for export] *)
  pose proof (pristine_word M 0x341f9 0x34230 (fun a Ha => th_img 0x341f9 0x34230 a ltac:(cbn; tauto) Ha)) as NONE1.
  pose proof (pristine_word M 0x22000 0x22f88 (fun a Ha => th_img 0x22000 0x22f88 a ltac:(cbn; tauto) Ha)) as NONE2.
  rimg_chunk NONE1 M 0x34200%Z [C1 (Z_to_bv 8 0)] FL.
  rimg_chunk NONE2 M 0x22f50%Z [C8 (Z_to_bv 64 0)] GOT.
  (* [comment removed for export] *)
  rimg_chunk NONE1 M 0x34204%Z [C1 (Z_to_bv 8 0)] ICB.
  pose proof (pristine_word M 0x94340 0x94568 (fun a Ha => th_img 0x94340 0x94568 a ltac:(cbn; tauto) Ha)) as NONE3.
  assert (AX0 : OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.U8Atexit.atx_cells0 M).
  { apply OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.U8Atexit.atx_cells0_init. intros a Ha. unfold OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.U8Atexit.atx_addr, OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.U8Atexit.PATX, OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.U8Atexit.PATX_N, OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.U8Atexit.PAEF_INCB in Ha.
    destruct Ha as [Ha|Ha]; [apply NONE3; lia | apply NONE1; lia]. }
  (* [comment removed for export] *)
  pose proof (bytes_at_of_rdn _ M buf content th_content ltac:(lia) ltac:(lia)) as CT.
  assert (CBY : bytes_at (run_segments psegs rc_inp rc_sp rc_mb) M (buf + 2) [Z_to_bv 8 (bv_unsigned (nth 2 content (Z_to_bv 8 0)))]).
  { replace (Z_to_bv 8 (bv_unsigned (nth 2 content (Z_to_bv 8 0)))) with (nth 2 content (Z_to_bv 8 0))
      by (apply bv_eq; rewrite Z_to_bv_unsigned; symmetry; apply bv_wrap_small; apply bv_unsigned_in_range).
    rewrite <- (firstn_skipn 2 content) in CT. apply bytes_at_app in CT. destruct CT as [_ X].
    rewrite length_firstn in X. replace (Z.of_nat (Nat.min 2 (length content))) with 2 in X by lia.
    destruct (skipn 2 content) as [|c rest] eqn:SK.
    { exfalso. pose proof (f_equal (@length _) SK) as SL. rewrite length_skipn in SL. cbn in SL. lia. }
    assert (EC : nth 2 content (Z_to_bv 8 0) = c).
    { rewrite <- (firstn_skipn 2 content) at 1. rewrite app_nth2 by (rewrite length_firstn; lia).
      rewrite length_firstn, SK. replace (2 - Nat.min 2 (length content))%nat with 0%nat by lia. reflexivity. }
    rewrite EC. change (c :: rest) with ([c] ++ rest) in X. apply bytes_at_app in X. exact (proj1 X). }
  assert (PBY : bytes_at (run_segments psegs rc_inp rc_sp rc_mb) M (buf + 6 + OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.U8TargetPre.hdr_cfglen content) (skipn (Z.to_nat (6 + OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.U8TargetPre.hdr_cfglen content)) content)).
  { rewrite <- (firstn_skipn (Z.to_nat (6 + OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.U8TargetPre.hdr_cfglen content)) content) in CT. apply bytes_at_app in CT. destruct CT as [_ X].
    rewrite length_firstn in X.
    replace (buf + Z.of_nat (Nat.min (Z.to_nat (6 + OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.U8TargetPre.hdr_cfglen content)) (length content))) with (buf + 6 + OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.U8TargetPre.hdr_cfglen content) in X by lia.
    exact X. }
  (* [comment removed for export] *)
  assert (CLI : cli_inv sp0 M tid).
  { constructor; [exact th_aux | | exact TIDC | do 9 eexists; exact FRM].
    intros lo hi a IN Ha. unfold exit_ivs in IN. cbn [In] in IN.
    destruct IN as [IN|[IN|[IN|[IN|[IN|[IN|[IN|[]]]]]]]]; injection IN as <- <-.
    - apply (th_img 0x22000 0x22f88); [cbn; tauto | lia].
    - apply (th_img 0x22f90 0x241b0); [cbn; tauto | lia].
    - apply (th_img 0x22f90 0x241b0); [cbn; tauto | lia].
    - apply (th_img 0x241b1 0x241f9); [cbn; tauto | lia].
    - apply (th_img 0x94340 0x94568); [cbn; tauto | lia].     (* [comment removed for export] *)
    - apply (th_img 0x94340 0x94568); [cbn; tauto | lia].
    - apply (th_img 0x949a8 0x95000); [cbn; tauto | lia]. }
  assert (SOP : so_pristine M).
  { intros i [Hi|Hi]; [apply (th_img 0x22f90 0x241b0) | apply (th_img 0x949a8 0x95000)]; first [cbn; tauto | lia]. }
  eapply (trun_rz sp0 (conj (proj1 SP0) (proj2 SP0)) SP16 th_atop pb buf cap (m_fs mo) (OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.U8TargetPre.hdr_paylen content) (OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.U8TargetPre.hdr_b1 content) tid
            (sp0 - 6144513) B1R TID ltac:(lia) ltac:(lia) ltac:(unfold OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.U8TargetPre.hdr_paylen; lia) C7
            (OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.U8TargetPre.hdr_cfglen content) (bv_unsigned (nth 2 content (Z_to_bv 8 0))) (buf + 6 + OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.U8TargetPre.hdr_cfglen content) M s mo
            (skipn (Z.to_nat (6 + OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.U8TargetPre.hdr_cfglen content)) content) errv);
    try eassumption; try lia.
  - unfold OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.U8TargetPre.hdr_paylen. lia.
  - rewrite length_skipn. unfold OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.U8TargetPre.hdr_paylen. lia.
Qed.

End S0.

(* [comment removed for export] *)
