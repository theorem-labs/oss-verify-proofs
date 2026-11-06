(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Copyright 2026 Theorem Labs *)
(* New for libdiginet/fuzz_decode: the cut-free (SRcf) twin of llvm_front_holds (LLVMFuzzerTestOneInput_front.v), as
   libreac/fuzz_decode's released lib/U/Prog/fd_entry_cg.v is the twin of its fd_entry.v: from the entry 0x12cfc to
   0x12df8 for 0 < n < 2^26, g_run_cf around the evt walk ft_en1, g_malloc_cf for the call of malloc at 0x12d68
   (a0 = max (n - 1) 1, at the agree room room_ag from llvm_room_cf), g_run_cf around the evt walk ft_en2. The evt
   walks and the helpers of Section H are those of LLVMFuzzerTestOneInput_front.v. *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libdiginet.fuzz_decode.lib.U.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.libdiginet.fuzz_decode.lib.U.Reusable Require Import YO0i YO0f YO0d YO05 YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.libdiginet.fuzz_decode.lib.U.Reusable Require Import YL01 YL00 YL0g YI06 YI16 YI14.
From OSSVerify.Proofs.libdiginet.fuzz_decode.lib.U.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.libdiginet.fuzz_decode.lib.U Require Import Contract Img0.
From OSSVerify.Proofs.libdiginet.fuzz_decode.lib.Lib Require Import PropExec MState Mem Exec Frame Step Cells Tac Bytes.
From OSSVerify.Proofs.libdiginet.fuzz_decode.lib.Lib Require Regs6ss RegisterBridge.
From OSSVerify.Proofs.libdiginet.fuzz_decode.lib.U.Prog Require Import memcpy_c LLVMFuzzerTestOneInput_c
  LLVMFuzzerTestOneInput_fr LLVMFuzzerTestOneInput_glue LLVMFuzzerTestOneInput_mid LLVMFuzzerTestOneInput_front_evt.
From OSSVerify.Proofs.libdiginet.fuzz_decode.lib.U Require Import SlotAgree AgreeLift.
From OSSVerify.Proofs.libdiginet.fuzz_decode.lib.U.Prog Require Import LLVMFuzzerTestOneInput_front LLVMFuzzerTestOneInput_cfb
  LLVMFuzzerTestOneInput_glue_cg.
Import ListNotations.
Open Scope Z_scope.

Section N.
Context {fx : YK11.FPState} {rc : YM05.RunCeil} {LS : lib_shape}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Context {SH : sink_head} {SK : sink_syms}.
Hypothesis MALLOC : forall fx' : YK11.FPState, @malloc_contract_ag fx' rc B API.
Hypothesis ERRNO_LOW : errno_addr B + 4 <= YM05.alloc_ceiling.
Hypothesis BND : blocks_nodup B API.
Context (MC : memcpy_contract).

Theorem llvm_front_holds_cf : forall stk empty L0 A0 regs0 mem0 md0 ra p n pl b,
  llvm_binds B API -> LLVM_K <= stk ->
  lib_pre B API stk empty L0 A0 regs0 mem0 md0 ra p n ->
  n = Z.of_nat (length pl) -> blk_data B mem0 p pl ->
  spZ regs0 <= 2 ^ 47 -> res_ok_slots A0 b -> llvm_room_cf b ->
  ro_agree rsegs mem0 -> G_img_c B llvm_RELRO mem0 -> frm_zero (@fp_csr fx) -> 0 < n < 2 ^ 26 ->
  SRcf B (mkCfg (@YK11.mkst fx regs0 (Z_to_bv 64 LLVM_ENTRY) mem0 (YK11.seg_rom (ms_segs B))) md0)
    (front_post B API stk L0 A0 regs0 mem0 md0 n b).
Proof.
  intros stk empty L0 A0 regs0 mem0 md0 ra p n pl b (SEGS & HMAL & HFRE & HGG & HG & AX) Hk Hpre Hn Hpd Hsp
    Hres Hroom Hro Hrelro Hfrm H26.
  subst n.
  pose proof Hpre as (HM & HW & HB & HID & Hra1 & Hal & Hceil & H63 & Hstw & Htp & Herr & Hp & Hn1 & Hpl & Hrod).
  pose proof (lf_fr_init B API stk empty L0 A0 regs0 mem0 md0 ra p _ Hpre Hro) as FR0.
  unfold LLVM_K, LLVM_FRAME, ALLOC_STACK in Hk.
  pose proof YM05.alloc_ceiling_value as Hac. pose proof lf_ceiling as Hrt. unfold LF_RES_TOP in Hrt.
  destruct (mr_model B _ (aa_laws API) _ _ _ _ HM) as (Hh & Hl & _).
  assert (Esp : spZ regs0 = bv_unsigned (reg_get regs0 2)) by reflexivity.
  pose proof (bv_unsigned_in_range _ (reg_get regs0 2)) as Rsp. unfold bv_modulus in Rsp.
  change (2 ^ Z.of_N 64) with (2 ^ 64) in Rsp.
  assert (PAY : In (p, Z.of_nat (length pl)) (blocks L0 A0) /\ 4096 <= p /\
    p + Z.of_nat (length pl) <= YM05.alloc_ceiling).
  { destruct Hpl as [[E _] | [_ (q & Hq & Hqp)]]; [lia|].
    pose proof (mr_blocks_range B _ (aa_laws API) L0 A0 mem0 md0 q _ HM Hq) as (R1 & R2). rewrite Hqp in R1, R2.
    split; [apply blocks_In; exists q; split; [exact Hqp | exact Hq]|]. lia. }
  destruct PAY as (Hpin & Hp4 & Hpc).
  assert (E10 : reg_get regs0 10 = Z_to_bv 64 p) by exact Hp.
  assert (E11 : reg_get regs0 11 = Z_to_bv 64 (Z.of_nat (length pl))) by exact Hn1.
  assert (ST0 : Frame.stk rsegs (normalize rsegs mem0) (spZ regs0 - stk) (bv_unsigned (reg_get regs0 2))).
  { rewrite <- Esp. eapply (ft_norm_stk B SEGS); try eassumption; try lia; unfold LF_RES_TOP; lia. }
  pose proof (mem_inv_normalize rsegs mem0) as MI0.
  assert (HP1 : bytes_at rsegs (normalize rsegs mem0) p pl).
  { apply bytes_at_normalize; [exact Hro|]. apply (blk_bytes_at B); [exact SEGS | lia | lia | exact Hpd]. }
  rewrite SEGS.
  (* 0x12cfc - 0x12d68: the prologue, the UBSan checks of data, sel, and the call of malloc *)
  eapply g_run_cf with (stk := stk) (S := spZ regs0) (L0 := L0) (A0 := A0) (mem0 := mem0) (md0 := md0)
    (Q := q_f1 (@fp_regs fx) (@fp_csr fx) (reg_get regs0 3) (reg_get regs0 4) (normalize rsegs mem0)
            (bv_unsigned (reg_get regs0 2) - 496) p (Z.of_nat (length pl))
            [C8 (reg_get regs0 27); C8 (reg_get regs0 26); C8 (reg_get regs0 25); C8 (reg_get regs0 24);
             C8 (reg_get regs0 23); C8 (reg_get regs0 22); C8 (reg_get regs0 21); C8 (reg_get regs0 20);
             C8 (reg_get regs0 19); C8 (reg_get regs0 18); C8 (reg_get regs0 9); C8 (reg_get regs0 8);
             C8 (reg_get regs0 1)]).
  all: try eassumption. all: try lia.
  { unfold Regs6ss.mkR_of, LLVM_ENTRY.
    eapply ft_en1 with (lo := spZ regs0 - stk) (p := p) (pl := pl); try eassumption; lia. }
  { intros ms (R & m' & j & -> & _ & _ & _ & _ & _ & _ & _ & _ & MU & WM & _).
    exists R, (@fp_regs fx), (Z_to_bv 64 0x15028), (@fp_csr fx), m',
      [(bv_unsigned (reg_get regs0 2) - 496, bv_unsigned (reg_get regs0 2) - 496 + 496)].
    split; [reflexivity|]. split; [exact MU|]. split; [exact WM|].
    intros x Hx NO. left. apply ft_out1 in NO. lia. }
  intros R F pc' fc ma HQ regs1 m1 Hx Hrel FR1.
  destruct HQ as (R' & m'' & j & HE & R1 & R2 & R3 & R4 & R10 & R9 & R18 & R19 & MU1 & WM1 & RW1).
  injection HE as ER EF EP EC EM. subst R' F pc' fc m''.
  assert (G1 : YK11.getr regs1 1 = Z_to_bv 64 0x12d6c) by (rewrite (lf_getr_eqv _ _ _ Hx); exact R1).
  assert (G12 : YK11.getr regs1 2 = Z_to_bv 64 (spZ regs0 - 496)) by (rewrite (lf_getr_eqv _ _ _ Hx); exact R2).
  assert (G13 : YK11.getr regs1 3 = YK11.getr regs0 3) by (rewrite (lf_getr_eqv _ _ _ Hx); exact R3).
  assert (G14 : YK11.getr regs1 4 = YK11.getr regs0 4) by (rewrite (lf_getr_eqv _ _ _ Hx); exact R4).
  assert (G110 : YK11.getr regs1 10 = Z_to_bv 64 (Z.max (Z.of_nat (length pl) - 1) 1))
    by (rewrite (lf_getr_eqv _ _ _ Hx); exact R10).
  assert (G19 : YK11.getr regs1 9 = Z_to_bv 64 (Z.of_nat (length pl) - 1))
    by (rewrite (lf_getr_eqv _ _ _ Hx); exact R9).
  assert (G118 : YK11.getr regs1 18 = Z_to_bv 64 (Z.of_nat (length pl)))
    by (rewrite (lf_getr_eqv _ _ _ Hx); exact R18).
  assert (G119 : YK11.getr regs1 19 = Z_to_bv 64 p) by (rewrite (lf_getr_eqv _ _ _ Hx); exact R19).
  assert (Hsp1 : spZ regs1 = spZ regs0 - 496) by (unfold spZ at 1; rewrite G12; apply MState.unsigned_lit; lia).
  assert (Hra1' : YK0s.ret_ok (YK11.getr regs1 1)) by (rewrite G1; apply ret_ok_even; reflexivity).
  assert (Hal1 : spZ regs1 mod 16 = 0) by (rewrite Hsp1; Z.div_mod_to_equations; lia).
  assert (Htp1 : YK11.getr regs1 4 = Z_to_bv 64 (ms_tp B)) by (rewrite G14; exact Htp).
  assert (ROOM1 : room_ag b (Z.max (Z.of_nat (length pl) - 1) 1)).
  { destruct Hroom as (Hl1 & Hl2 & Hl3). apply lf_room_ag; lia. }
  pose proof (lf_rw_cells_rel m1 ma _ _ Hrel RW1) as RWa.
  rewrite <- SEGS. change (Z_to_bv 64 0x15028) with (Z_to_bv 64 LLVM_MALLOC).
  (* 0x12d68: malloc (max (n - 1) 1) *)
  eapply g_malloc_cf with (stk := stk) (S := spZ regs0) (L0 := L0) (A0 := A0) (mem0 := mem0) (md0 := md0)
    (n := Z.max (Z.of_nat (length pl) - 1) 1) (bres := b).
  all: try eassumption. all: try (rewrite ?Hsp1; lia). all: try (rewrite ?Hsp1; unfold ALLOC_STACK; lia).
  intros L1 A1 regs2 mem2 md2 res FR2 Hrp2 G210 Hr1 Hr2 Hr16 Hnimg (b1 & b2 & Eb1 & Eb2) Hres2 Habove2 Hkept2.
  rewrite G1, SEGS.
  pose proof FR2 as (HM2 & HW2 & HB2 & HID2 & _ & _ & _ & _ & _ & HwX2 & _ & _ & Hro2).
  assert (Hres_in : In (res, Z.max (Z.of_nat (length pl) - 1) 1) (blocks L1 A1))
    by (rewrite Eb1; apply in_or_app; right; left; reflexivity).
  assert (PW : pairwise ranges_disjoint (b1 ++ (res, Z.max (Z.of_nat (length pl) - 1) 1) :: b2)).
  { rewrite <- Eb1. exact (mr_blocks_disjoint B _ (aa_laws API) L1 A1 mem2 md2 HM2). }
  assert (MINE : forall a k, In (a, k) (blocks L0 A0) ->
      a + k <= res \/ res + Z.max (Z.of_nat (length pl) - 1) 1 <= a).
  { intros a k Hak. rewrite Eb2 in Hak. pose proof (ft_disj_mid b1 (res, _) b2 (a, k) PW Hak) as H.
    cbn [fst snd] in H. lia. }
  pose proof (MINE _ _ Hpin) as DPB.
  assert (Y2 : forall r, callee_saved r -> YK11.getr regs2 (Z_to_bv 5 r) = YK11.getr regs1 (Z_to_bv 5 r))
    by exact Hrp2.
  assert (E22 : reg_get regs2 2 = Z_to_bv 64 (bv_unsigned (reg_get regs0 2) - 496)).
  { change (reg_get regs2 2) with (YK11.getr regs2 (Z_to_bv 5 2)).
    rewrite (Y2 2 ltac:(unfold callee_saved; lia)). exact G12. }
  assert (E210 : reg_get regs2 10 = Z_to_bv 64 res) by exact G210.
  assert (E29 : reg_get regs2 9 = Z_to_bv 64 (Z.of_nat (length pl) - 1)).
  { change (reg_get regs2 9) with (YK11.getr regs2 (Z_to_bv 5 9)).
    rewrite (Y2 9 ltac:(unfold callee_saved; lia)). exact G19. }
  assert (E218 : reg_get regs2 18 = Z_to_bv 64 (Z.of_nat (length pl))).
  { change (reg_get regs2 18) with (YK11.getr regs2 (Z_to_bv 5 18)).
    rewrite (Y2 18 ltac:(unfold callee_saved; lia)). exact G118. }
  assert (E219 : reg_get regs2 19 = Z_to_bv 64 p).
  { change (reg_get regs2 19) with (YK11.getr regs2 (Z_to_bv 5 19)).
    rewrite (Y2 19 ltac:(unfold callee_saved; lia)). exact G119. }
  pose proof (mem_inv_normalize rsegs mem2) as MI2.
  assert (HP2 : bytes_at rsegs (normalize rsegs mem2) p pl).
  { assert (BD : blk_data B mem2 p pl) by (eapply ft_blk_keep; [exact FR2 | exact Hpin | exact Hpd]).
    apply bytes_at_normalize; [exact Hro2|]. apply (blk_bytes_at B); [exact SEGS | lia | lia | exact BD]. }
  destruct (ft_norm_blk B API SEGS AX L1 A1 mem2 md2 res (Z.max (Z.of_nat (length pl) - 1) 1) HM2 Hres_in
    ltac:(lia) Hro2) as [junk HJ].
  assert (RWb : forall a, spZ regs0 - 496 <= a < spZ regs0 ->
     mbyte rsegs mem2 a = mbyte rsegs m1 a /\ (writable_at rsegs m1 a <-> writable_at rsegs mem2 a)).
  { intros a Ha. pose proof (Habove2 a ltac:(rewrite Hsp1; lia)) as E. rewrite SEGS in E. exact E. }
  pose proof (lf_rw_cells_frame m1 mem2 _ _ RWa (fun a Ha => RWb a ltac:(cbn [cells_size csize] in Ha; lia))) as RW2.
  assert (NI : forall a, 0x50000 <= a -> ~ in_img B a)
    by (intros a Ha Hi; pose proof (lf_in_img_top B a SEGS Hi) as H; unfold LF_RES_TOP in H; lia).
  pose proof (lf_rw_cells_norm B mem2 _ _ SEGS Hro2
    (fun i Hi => NI (bv_unsigned (reg_get regs0 2) - 496 + i) ltac:(destruct Hi as [Hi0 _]; lia)) RW2) as RW3.
  (* 0x12d6c - 0x12df8: the NULL test, buf at sp + 8, the copy and the inlined spec_read_frame *)
  eapply g_run_cf with (stk := stk) (S := spZ regs0) (L0 := L0) (A0 := A0) (mem0 := mem0) (md0 := md0)
    (Q := q_f2 (@fp_regs fx) (@fp_csr fx) (reg_get regs2 3) (reg_get regs2 4) (normalize rsegs mem2)
            (bv_unsigned (reg_get regs0 2) - 496) res (Z.max (Z.of_nat (length pl) - 1) 1)
            [C8 (reg_get regs0 27); C8 (reg_get regs0 26); C8 (reg_get regs0 25); C8 (reg_get regs0 24);
             C8 (reg_get regs0 23); C8 (reg_get regs0 22); C8 (reg_get regs0 21); C8 (reg_get regs0 20);
             C8 (reg_get regs0 19); C8 (reg_get regs0 18); C8 (reg_get regs0 9); C8 (reg_get regs0 8);
             C8 (reg_get regs0 1)]).
  all: try eassumption. all: try lia.
  { unfold Regs6ss.mkR_of.
    eapply (ft_en2 MC) with (Sp := bv_unsigned (reg_get regs0 2) - 496) (buf := res) (n := Z.of_nat (length pl))
      (p := p) (pl := pl) (junk := junk) (j := j); try eassumption; try lia; reflexivity. }
  { intros ms (R0 & m' & body & bb & j0 & j1 & -> & _ & _ & _ & _ & _ & MU & WM & _).
    exists R0, (@fp_regs fx), (Z_to_bv 64 0x12df8), (@fp_csr fx), m',
      [(bv_unsigned (reg_get regs0 2) - 496, bv_unsigned (reg_get regs0 2) - 496 + 496);
       (res, res + Z.max (Z.of_nat (length pl) - 1) 1)].
    split; [reflexivity|]. split; [exact MU|]. split; [exact WM|].
    intros x Hx0 NO. apply ft_out2 in NO. destruct NO as [NO|NO]; [left; lia|].
    right. exists res, (Z.max (Z.of_nat (length pl) - 1) 1). split; [|lia].
    unfold lf_mine. split; [exact Hres_in|]. split; [lia | exact MINE]. }
  intros Rb F pc' fc mb HQ regs3 m3 Hx3 Hrel3 FR3.
  destruct HQ as (R' & m'' & body & bb & j0 & j1 & HE & Q2 & Q3 & Q4 & Q9 & Q18 & MU3 & WM3 & RW4 & BB3 & Hbd1
    & Hbd2).
  injection HE as ER EF EP EC EM. subst R' F pc' fc m''.
  apply (SRcf_ret B).
  pose proof (lf_rw_cells_rel m3 mb _ _ Hrel3 RW4) as RW5.
  pose proof (proj2 (bytes_at_rel rsegs m3 mb body bb Hrel3) BB3) as BB4.
  apply ft_rw_cells_cons in RW5 as [C0 RW5]. apply ft_rw_cells_cons in RW5 as [C1 RW5].
  apply ft_rw_cells_cons in RW5 as [C2 RW5].
  assert (G33 : YK11.getr regs3 3 = YK11.getr regs0 3).
  { rewrite (lf_getr_eqv _ _ _ Hx3). transitivity (YK11.getr regs2 (Z_to_bv 5 3)); [exact Q3|].
    rewrite (Y2 3 ltac:(unfold callee_saved; lia)). exact G13. }
  assert (G34 : YK11.getr regs3 4 = YK11.getr regs0 4).
  { rewrite (lf_getr_eqv _ _ _ Hx3). transitivity (YK11.getr regs2 (Z_to_bv 5 4)); [exact Q4|].
    rewrite (Y2 4 ltac:(unfold callee_saved; lia)). exact G14. }
  unfold front_post.
  exists (mkFP (@fp_regs fx) (@fp_csr fx)), L1, A1, regs3, m3, md2, res, body, bb.
  split; [rewrite SEGS; reflexivity|].
  split; [exact Hfrm|].
  split; [exact FR3|].
  split; [exact Hres2|].
  split; [unfold lf_mine, llvm_nn; split; [exact Hres_in|]; split; [lia | exact MINE]|].
  split; [rewrite (lf_getr_eqv _ _ _ Hx3); exact Q2|].
  split; [exact G33|]. split; [exact G34|].
  split; [rewrite (lf_getr_eqv _ _ _ Hx3); exact Q9|].
  split; [rewrite (lf_getr_eqv _ _ _ Hx3); exact Q18|].
  split; [eapply ft_rw_cells_at; [|exact RW5]; cbn [csize]; unfold LLVM_FRAME; lia|].
  split; [eapply ft_rw_cells_at; [|exact C1]; cbn [csize]; unfold LLVM_FRAME; lia|].
  split; [exists j0; eapply ft_rw_cells_at; [|exact C0]; unfold LLVM_FRAME; lia|].
  split; [exists j1; eapply ft_rw_cells_at; [|exact C2]; cbn [csize]; unfold LLVM_FRAME; lia|].
  split; [exact BB4|].
  split; [lia|]. split; [unfold llvm_nn; lia|]. split; [lia|]. unfold llvm_nn; lia.
Qed.

End N.
