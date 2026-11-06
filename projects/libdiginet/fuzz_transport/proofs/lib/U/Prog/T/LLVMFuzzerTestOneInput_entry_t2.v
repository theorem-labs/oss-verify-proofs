(* LLVMFuzzerTestOneInput (ubsan) 0x13988 .. the first loop head 0x139dc: the abort() test of diginet_session_init's
   result (rc = SPEC_OK by the model: not taken), the exit 0x145e8 when the cursor is empty, the frame slots
   0x13990-0x139d8 (sp + 0x20 0x610f, sp + 0x28 0xffff, sp + 8 2^32 - 3, sp + 0x30 / 0x38 the bounds of sp + 0x60,
   sp + 0 &g_s) and the head with ops = 0. *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes ZBridge.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.U Require Import Img0.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require Import DgnSpec.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require Import TWorld TWorldLemmas TImg TWorldMem TCb TOps.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.U.Prog.T Require Import TImgU WMem TContract
  LLVMFuzzerTestOneInput_lh LLVMFuzzerTestOneInput_fr LLVMFuzzerTestOneInput_entry_m LLVMFuzzerTestOneInput_entry_d.
Import ListNotations.
Open Scope Z_scope.

(* the frame slots' cells as the loop's frame llvm_frame: the struct diginet_io (dead after init) as one cell *)
Lemma ent_frame_head : forall m Sp regs0 x1 x2 j10 x4 x5 x6 x7 j60,
  rw_cells rsegs m Sp ([C8 x1; C8 x2; CB 16 j10; C8 x4; C8 x5; C8 x6; C8 x7; C8 (Z_to_bv 64 0);
                        C8 (Z_to_bv 64 0x1482c); C8 (Z_to_bv 64 0x14b20); C8 (Z_to_bv 64 0x14bbc); CB 40 j60]
                       ++ llvm_saved regs0) ->
  x1 = Z_to_bv 64 (W_BASE_UBSAN + OFF_g_s) -> x2 = Z_to_bv 64 (2 ^ 32 - 3) -> x4 = Z_to_bv 64 0x610f ->
  x5 = Z_to_bv 64 0xffff -> x6 = Z_to_bv 64 (2 ^ 64 - 1 - (Sp + 96)) -> x7 = Z_to_bv 64 (2 ^ 64 - (Sp + 96)) ->
  rw_cells rsegs m Sp (llvm_frame regs0 Sp j10
    (cells_bytes [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0x1482c); C8 (Z_to_bv 64 0x14b20); C8 (Z_to_bv 64 0x14bbc)])
    j60).
Proof.
  intros m Sp regs0 x1 x2 j10 x4 x5 x6 x7 j60 H -> -> -> -> -> ->.
  unfold llvm_frame.
  exact (rw_cells_merge rsegs m Sp
           [C8 (Z_to_bv 64 (W_BASE_UBSAN + OFF_g_s)); C8 (Z_to_bv 64 (2 ^ 32 - 3)); CB 16 j10;
            C8 (Z_to_bv 64 0x610f); C8 (Z_to_bv 64 0xffff); C8 (Z_to_bv 64 (2 ^ 64 - 1 - (Sp + 96)));
            C8 (Z_to_bv 64 (2 ^ 64 - (Sp + 96)))]
           [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0x1482c); C8 (Z_to_bv 64 0x14b20); C8 (Z_to_bv 64 0x14bbc)]
           (CB 40 j60 :: llvm_saved regs0) H).
Qed.

Lemma ent_frame_lens : forall m Sp x1 x2 j10 x4 x5 x6 x7 x8 x9 x10 x11 j60 rest,
  rw_cells rsegs m Sp ([C8 x1; C8 x2; CB 16 j10; C8 x4; C8 x5; C8 x6; C8 x7; C8 x8; C8 x9; C8 x10; C8 x11;
                        CB 40 j60] ++ rest) ->
  length j10 = 16%nat /\ length j60 = 40%nat.
Proof.
  intros m Sp x1 x2 j10 x4 x5 x6 x7 x8 x9 x10 x11 j60 rest [[Hwf _] _].
  cbn [app cells_wf cell_wf] in Hwf.
  destruct Hwf as (_ & _ & H10 & _ & _ & _ & _ & _ & _ & _ & _ & H60 & _). split; [exact H10 | exact H60].
Qed.

Lemma ent_head_intro : forall data D regs0 m0 Sp lo c B F fc ms
    (ra t0 t1 t2 s0 a0 a1 a2 a3 a4 a5 a6 a7 s3 s6 t3 t4 t5 t6 : word) (m : word -> option byte)
    (j10 jio j60 : list byte),
  ms = MS (mkR ra (Z_to_bv 64 Sp) (reg_get regs0 3) (reg_get regs0 4) t0 t1 t2 s0 (Z_to_bv 64 1)
               a0 a1 a2 a3 a4 a5 a6 a7
               (Z_to_bv 64 0x39) s3 (Z_to_bv 64 7) (Z_to_bv 64 (data + fi_off c)) s6 (Z_to_bv 64 (fi_n c))
               (Z_to_bv 64 (W_BASE_UBSAN + OFF_M)) (Z_to_bv 64 (W_BASE_UBSAN + OFF_g_fail_next))
               (Z_to_bv 64 (W_BASE_UBSAN + OFF_g_s)) (Z_to_bv 64 0) t3 t4 t5 t6)
          F (Z_to_bv 64 LH_HEAD) fc None m (seg_rom rsegs) ->
  fi_n c <> 0 -> llvm_cursor D c -> llvm_mem data D regs0 m0 Sp lo B m j10 jio j60 ->
  llvm_head data D regs0 m0 Sp lo 0 c B F fc ms.
Proof.
  intros data D regs0 m0 Sp lo c B F fc ms ra t0 t1 t2 s0 a0 a1 a2 a3 a4 a5 a6 a7 s3 s6 t3 t4 t5 t6 m j10 jio j60
    -> HN HC HM.
  unfold llvm_head. do 19 eexists. exists m, j10, jio, j60.
  split; [reflexivity|]. split; [unfold OPS_MAX; lia|]. split; [exact HN|]. split; [exact HC|]. exact HM.
Qed.

Lemma ent_tl2 : forall data D regs0 m0 Sp lo o n B25 F fc ms,
  ent_num Sp lo -> 0 <= o -> 0 <= n -> o + n = Z.of_nat (length D) ->
  ent_dat data D m0 lo -> (D = [] -> n = 0) -> relro_img m0 -> g_fail_next B25 <= 1 ->
  (forall A, lh_heap_ok A ->
     exists Bw', LLVMFuzzerTestOneInput_loop_m (Z.to_nat OPS_MAX) timg_ubsan B25 A D (cur o n 14) O = Some (Bw', tt)) ->
  ent_s988 data regs0 m0 Sp lo o n 0 B25 F fc ms ->
  evt rsegs (ent_Q data D regs0 m0 Sp lo F fc) ms.
Proof.
  intros data D regs0 m0 Sp lo o n B25 F fc ms HNUM Ho Hn Hon HDAT HD0 RR GF HLOOP HS.
  destruct HS as (ra & t0 & t1 & t2 & s0 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & s2 & s3 & s4 & s6 & s11 &
                  t3 & t4 & t5 & t6 & m & -> & HM).
  destruct HM as (j0 & j60 & ST & MI & WM & MU0 & WMO0 & FR).
  unfold ent_frame, llvm_saved in FR. cbn [app] in FR.
  destruct HNUM as (H16 & Hlo & HK & H63 & HWL). unfold LH_K, LH_FRAME in *.
  assert (USp : bv_unsigned (Z_to_bv 64 Sp) = Sp) by (apply unsigned_lit; lia).
  lazymatch goal with |- evt _ ?Q _ => set (QQ := Q) end.
  wk_facts. wk_eq_fact OFF_g_fail_next. wk_eq_fact OFF_g_cfg. wk_eq_fact OFF_M.
  assert (Hc : 0 <= fi_off (cur o n 14) /\ 0 <= fi_n (cur o n 14) /\
               fi_off (cur o n 14) + fi_n (cur o n 14) <= Z.of_nat (length D)) by (unfold cur; cbn; lia).
  assert (HLEN : Z.of_nat (length D) <= lo)
    by (destruct HDAT as [HDe | (Hd0' & Hdl' & _)]; [subst D; cbn; lia | lia]).
  (* 0x13988 bnez a0: rc = 0 *)
  zstep. ebr false ltac:(reflexivity).
  (* 0x1398c beqz s7 *)
  zstep.
  destruct (Z.eqb_spec (fi_n (cur o n 14)) 0) as [E0 | E0].
  - ebr true ltac:(unfold bv_eqb; rewrite !unsigned_lit by lia; apply Z.eqb_eq; lia).
    apply evt_done. unfold QQ, ent_Q. left.
    eapply ent_out; [lia | lia | unfold LH_FRAME; lia | exact MI | exact MU0 | exact WMO0 | exact FR].
  - ebr false ltac:(unfold bv_eqb; rewrite !unsigned_lit by lia; apply Z.eqb_neq; lia).
    (* 0x13990 .. 0x139d8: s11 = 0, s1 = 1, a3 = sp + 0x60, s2 = 0x39, s4 = 7, the six frame slots *)
    do 19 zstep.
    apply evt_done. unfold QQ, ent_Q. right. exists (cur o n 14), B25. split; [|exact HLOOP].
    destruct HDAT as [HDe | (Hd0 & Hdl & How & HD)].
    { exfalso. specialize (HD0 HDe). subst n. unfold cur in E0. cbn [fi_off fi_n] in E0. lia. }
    pose proof (ent_frame_lens _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ FR) as [L10 L60].
    eapply ent_head_intro with
      (jio := cells_bytes [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0x1482c); C8 (Z_to_bv 64 0x14b20);
                           C8 (Z_to_bv 64 0x14bbc)]);
      [reflexivity | exact E0 | unfold llvm_cursor; lia | ].
    unfold llvm_mem.
    split; [exact Hd0|]. split; [exact Hdl|]. split; [exact How|].
    split.
    { eapply bytes_at_transport; [exact HD | exact MU0 |]. cbn [disjoint_from].
      unfold off_world, W_BASE_UBSAN, W_LEN in *. split; [lia | split; [lia | exact I]]. }
    split; [exact H16|]. split; [exact ST|]. split; [unfold LH_K; lia|]. split; [unfold LH_FRAME; lia|].
    split; [exact HWL|]. split; [exact MI|].
    split; [eapply lh_relro_munch; [exact RR | exact MU0 | lia]|].
    split; [exact WM|]. split; [exact GF|].
    split; [exact MU0|]. split; [exact WMO0|].
    split; [exact L10|]. split; [reflexivity|]. split; [exact L60|].
    eapply ent_frame_head; [exact FR | reflexivity | reflexivity | reflexivity | reflexivity | |].
    + rewrite zb_lxor_ones by lia. f_equal.
    + apply Z_to_bv_eqm. change (2 ^ 64) with 18446744073709551616.
      replace (18446744073709551616 - (Sp + 96)) with ((0 - (Sp + 96)) + 1 * 18446744073709551616) by lia.
      rewrite Z.mod_add by lia. reflexivity.
Qed.
