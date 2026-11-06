(* Case 4 of the ubsan LLVMFuzzerTestOneInput, the tagged arm's tail 0x1454c .. the latch 0x14574: g_ncmd++
   (fuzz_transport.c:1120, read signed and written back), the cursor's n after the take (s6 = sp+0x10 - n),
   s10 = &g_s reloaded from sp+0 (llvm_frame's first cell), settle(0) (:1121). *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes ZBridge.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.U Require Import Img0.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require Import DgnSpec.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require Import TWorld TImg TNeed TSess0 TCb TSess TOps
  TWorldLemmas TWorldMem.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.U.Prog.T Require Import TImgU WMem TContract TSessC settle_c
  LLVMFuzzerTestOneInput_lh LLVMFuzzerTestOneInput_fr LLVMFuzzerTestOneInput_op4_mid LLVMFuzzerTestOneInput_op4_lib
  LLVMFuzzerTestOneInput_op4_defs LLVMFuzzerTestOneInput_op4_tag_lib LLVMFuzzerTestOneInput_op4_tag_m.
Import ListNotations.
Open Scope Z_scope.

(* a cell list rewritten to another with the same bytes and size *)
Lemma rw_cells_conv : forall m A cs1 cs2, cells_wf cs2 -> cells_bytes cs1 = cells_bytes cs2 ->
  cells_size cs1 = cells_size cs2 -> rw_cells rsegs m A cs1 -> rw_cells rsegs m A cs2.
Proof.
  intros m A cs1 cs2 W EB ES [[_ HB] HW]. rewrite ES in HW. rewrite EB in HB.
  split; [split; [exact W | exact HB] | exact HW].
Qed.

Lemma rw_cells_c8_cb : forall m A (x : word) (r : list byte), length r = 8%nat ->
  rw_cells rsegs m A [CB 16 (le8 x ++ r)] -> rw_cells rsegs m A [C8 x; CB 8 r].
Proof.
  intros m A x r L H. eapply rw_cells_conv; [| | | exact H].
  - cbn [cells_wf cell_wf]. split; [exact I|]. split; [exact L | exact I].
  - cbn [cells_bytes cbytes]. rewrite !app_nil_r. reflexivity.
  - reflexivity.
Qed.

(* the cursor after the take *)
Lemma t4r_c5_n : forall D c3, fi_n (t4_c5 D c3) = fi_n (t4_c4 D c3) - t4_n D c3.
Proof. intros D c3. unfold t4_c5, t4_n, t4_tk, fuzz_take_m. reflexivity. Qed.

Lemma t4r_c5_off : forall D c3, fi_off (t4_c5 D c3) = fi_off (t4_c4 D c3) + t4_n D c3.
Proof. intros D c3. unfold t4_c5, t4_n, t4_tk, fuzz_take_m. reflexivity. Qed.

Lemma t4r_n_rng : forall D c3, llvm_cursor D c3 ->
  0 <= t4_n D c3 <= fi_n (t4_c4 D c3) /\ llvm_cursor D (t4_c4 D c3) /\ llvm_cursor D (t4_c5 D c3).
Proof.
  intros D c3 HC.
  pose proof (t4_cursor_u8 D c3 HC) as HC4. fold (t4_c4 D c3) in HC4.
  assert (HL : 0 <= t4_len D c3 - 3) by (unfold t4_len; pose proof (Z.mod_pos_bound (snd (fuzz_u8_m D c3)) 22); lia).
  pose proof (t4_cursor_take D (t4_c4 D c3) (t4_len D c3 - 3) HC4 HL) as HC5.
  change (fst (fst (fuzz_take_m (t4_c4 D c3) (t4_len D c3 - 3)))) with (t4_c5 D c3) in HC5.
  split; [|split; [exact HC4 | exact HC5]].
  destruct HC4 as (_ & HN4 & _).
  unfold t4_n, t4_tk, fuzz_take_m. cbn [snd].
  destruct (Z.ltb_spec (t4_len D c3 - 3) (fi_n (t4_c4 D c3))); lia.
Qed.

(* The machine at 0x1454c: s1 = 1, s3 / s6 the cursor after the take (its address, the take's n), s8 / s9 / s11 as at
   the loop head, the world B6, sp+0x10 = the cursor's n before the take. *)
Definition t4r_tl (data : Z) (D : list byte) (regs0 : bvmap 5 word) (m0 : word -> option byte)
    (Sp lo ops : Z) (c3 : fuzz_in) (B6 : list byte) (F : bvmap 5 word) (fc : bv 32) (ms : machine_state) : Prop :=
  exists (ra t0 t1 t2 s0 a0 a1 a2 a3 a4 a5 a6 a7 s2 s4 s5 s7 s10 t3 t4 t5 t6 : word) (m : word -> option byte)
         (jlo jio j60 : list byte),
    ms = MS (mkR ra (Z_to_bv 64 Sp) (reg_get regs0 3) (reg_get regs0 4) t0 t1 t2 s0 (Z_to_bv 64 1)
                 a0 a1 a2 a3 a4 a5 a6 a7
                 s2 (Z_to_bv 64 (data + fi_off (t4_c5 D c3))) s4 s5 (Z_to_bv 64 (t4_n D c3)) s7
                 (Z_to_bv 64 (W_BASE_UBSAN + OFF_M)) (Z_to_bv 64 (W_BASE_UBSAN + OFF_g_fail_next))
                 s10 (Z_to_bv 64 ops) t3 t4 t5 t6)
            F (Z_to_bv 64 0x1454c) fc None m (seg_rom rsegs) /\
    length jlo = 8%nat /\
    llvm_mem data D regs0 m0 Sp lo B6 m (le8 (Z_to_bv 64 (fi_n (t4_c4 D c3))) ++ jlo) jio j60.

Lemma t4r_tail : settle_contract ->
  forall data D regs0 m0 Sp lo ops c3 B6 B8 F fc ms,
  0 <= ops < OPS_MAX -> llvm_cursor D c3 ->
  settle_m (set_g_ncmd B6 ((g_ncmd B6 + 1) mod 2 ^ 32)) 0 = Some (B8, tt) ->
  t4r_tl data D regs0 m0 Sp lo ops c3 B6 F fc ms ->
  evt rsegs (llvm_latch data D regs0 m0 Sp lo ops (t4_c5 D c3) B8 F fc) ms.
Proof.
  intros STL data D regs0 m0 Sp lo ops c3 B6 B8 F fc ms HOPS HC3 HSE H.
  destruct H as (ra & t0 & t1 & t2 & s0 & a0 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & s2 & s4 & s5 & s7 & s10 &
                 t3 & t4 & t5 & t6 & m & jlo & jio & j60 & -> & LJ & HM).
  pose proof HM as HM0. unfold llvm_mem in HM.
  destruct HM as (HD0 & HDL & HOW & HD & HSP & HSTK & HLO & HSP2 & HWL & HMI & HRO & HWM & HFN & HMU & HWMO &
                  HJ1 & HJ2 & HJ3 & HRW).
  unfold LH_K, LH_FRAME in *.
  pose proof (wm_len _ _ _ _ HWM) as LB.
  destruct (t4r_n_rng D c3 HC3) as (HNR & HC4 & HC5).
  pose proof HC4 as (HO4 & HN4 & HD4). pose proof HC5 as (HO5 & HN5 & HD5).
  rewrite t4r_c5_n in HN5, HD5. rewrite t4r_c5_off in HO5, HD5 |- *.
  wk_facts. wk_eq_fact OFF_g_fail_next. wk_eq_fact OFF_M. wk_eq_fact OFF_g_s. wk_eq_fact OFF_g_ncmd.
  destruct (llvm_frame_split regs0 m Sp _ jio j60 HRW) as (F1 & F2 & F3 & F4 & F5 & F6).
  clear HRW HD HRO HMU HWMO.
  unfold llvm_saved in F6.
  apply (rw_cells_c8_cb _ _ _ _ LJ) in F2.
  pose proof (munch_refl [(Sp - 0, Sp); (W_BASE_UBSAN, W_BASE_UBSAN + W_LEN)] m) as MU.
  pose proof (wmono_refl rsegs m) as WMO.
  (* ---- 0x1454c lw a0, 0x10(s9); 0x14550 ld a1, 0x10(sp); 0x14554 sub s6, a1, s6; 0x14558 addi a0, a0, 1;
     0x1455c sw a0, 0x10(s9) ---- *)
  do 5 zstep.
  (* the world is set_g_ncmd B6 (g_ncmd B6 + 1) *)
  set (B7 := set_g_ncmd B6 ((g_ncmd B6 + 1) mod 2 ^ 32)) in HSE.
  assert (EB7 : upd B6 64984 (put 4 (s32_at B6 64984 + 1)) = B7)
    by (unfold B7; rewrite <- t4_ncmdw; reflexivity).
  assert (HFN7 : g_fail_next B7 <= 1).
  { unfold B7, set_g_ncmd. rewrite t4_gf_upd; [exact HFN | exact LB | unfold OFF_g_ncmd; lia | | ];
      rewrite length_put; unfold OFF_g_ncmd, OFF_g_fail_next, W_LEN; cbn [Z.of_nat]; lia. }
  lazymatch goal with
  | W : wmem rsegs ?m1 (upd B6 64984 (put 4 (s32_at B6 64984 + 1))) |- _ =>
      rewrite EB7 in W;
      assert (HM1 : llvm_mem data D regs0 m0 Sp lo B7 m1 (le8 (Z_to_bv 64 (fi_n (t4_c4 D c3))) ++ jlo) jio j60)
        by (eapply (llvm_mem_after_call data D regs0 m0 Sp lo 0 B6 B7 m m1);
              [ exact HM0 | unfold LH_K; lia | exact MU | exact WMO | exact HMI | exact HSTK | exact W
              | exact HFN7 ])
  end.
  clear HM0 MU WMO.
  (* ---- 0x14560 ld s10, 0(sp); 0x14564 li s2, 0x39; 0x14568 li s4, 7; 0x1456c mv a0, zero; 0x14570 jal settle ---- *)
  do 5 zstep.
  pose proof HM1 as HM1c. unfold llvm_mem in HM1c.
  destruct HM1c as (_ & _ & _ & _ & _ & HSTK1 & _ & _ & _ & HMI1 & _ & HWM1 & _ & _ & _ & _ & _ & _ & _).
  eapply evt_cut.
  { eapply (STL _ (Z_to_bv 64 Sp) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ lo
              B7 B8 0).
    - reflexivity.
    - lia.
    - exact HWM1.
    - exact HSE.
    - rewrite unsigned_lit by lia; exact HSP.
    - rewrite unsigned_lit by lia; exact HSTK1.
    - rewrite unsigned_lit by lia; unfold settle_FRAME; lia.
    - unfold w_off_stack; rewrite unsigned_lit by lia; unfold settle_FRAME; lia.
    - exact HMI1. }
  intros ms' Hpost.
  destruct Hpost as (r0 & r1 & r2 & r3 & r4 & r5 & r6 & r7 & r8 & r9 & r10 & r11 & r12 & r13 & r14 & m4 &
                     -> & MU4 & WMO4 & MI4 & ST4 & EB4 & WM4).
  rewrite unsigned_lit in MU4, ST4 by lia.
  subst B8.
  assert (HM4 : llvm_mem data D regs0 m0 Sp lo B7 m4 (le8 (Z_to_bv 64 (fi_n (t4_c4 D c3))) ++ jlo) jio j60).
  { eapply (llvm_mem_after_call data D regs0 m0 Sp lo settle_FRAME B7 B7 _ m4);
      [ exact HM1 | unfold settle_FRAME, LH_K; lia
      | apply lh_munch_add_world; exact MU4 | exact WMO4 | exact MI4 | exact ST4 | exact WM4 | exact HFN7 ]. }
  (* ---- the latch 0x14574 ---- *)
  rewrite (ret_pc_even 0x14574) by (first [lia | reflexivity]).
  apply evt_done. unfold llvm_latch. rewrite t4r_c5_n, t4r_c5_off.
  do 19 eexists. exists m4, (le8 (Z_to_bv 64 (fi_n (t4_c4 D c3))) ++ jlo), jio, j60.
  split; [reflexivity|].
  split; [exact HOPS|].
  split; [exact HC5|].
  exact HM4.
Qed.
