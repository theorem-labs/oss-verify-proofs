(* The prologue of LLVMFuzzerTestOneInput (ubsan), 0x13760 .. 0x137f8: the frame (addi sp, -240; the 13 saves at
   sp + 0x88), the struct diginet_io copied from .data.rel.ro 0x21ef8 to sp + 0x40, the size test (size >> 26:
   the model's FUZZ_INPUT_MAX return, to the exit 0x145e8), and the flags byte (fuzz.h's fuzz_u8: 0 when size = 0,
   else the byte at data, with UBSan's pointer test data + 1 > 1 not taken). *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes ZBridge Image.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Regs6ss.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.U Require Import Img0.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require Import DgnSpec.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require Import TWorld TWorldLemmas TImg TWorldMem TCb TOps.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.U.Prog.T Require Import TImgU WMem TContract
  LLVMFuzzerTestOneInput_lh LLVMFuzzerTestOneInput_fr LLVMFuzzerTestOneInput_entry_m LLVMFuzzerTestOneInput_entry_d.
Import ListNotations.
Open Scope Z_scope.

(* .data.rel.ro is still the image's (relro_img): its bytes as bytes_at (check_state_desk.v csd_relro_bytes) *)
Lemma ent_img_nth : forall n a bs i, image_bytes rsegs a n = Some bs -> (i < n)%nat ->
  seg_rom rsegs (wa (a + Z.of_nat i)) = nth_error bs i.
Proof.
  induction n as [|n IH]; intros a bs i H Hi; cbn in H; [lia|].
  destruct (seg_rom rsegs (wa a)) as [b|] eqn:E1; [|discriminate].
  destruct (image_bytes rsegs (a + 1) n) as [bs'|] eqn:E2; [|discriminate].
  injection H as <-. destruct i as [|i]; cbn [nth_error].
  - rewrite Z.add_0_r. exact E1.
  - rewrite <- (IH (a + 1) bs' i E2 ltac:(lia)). f_equal. unfold wa. f_equal. lia.
Qed.

Lemma ent_relro_bytes : forall m a bs, relro_img m ->
  RELRO_BASE <= a -> a + Z.of_nat (length bs) <= RELRO_BASE + RELRO_LEN ->
  image_bytes rsegs a (length bs) = Some bs -> bytes_at rsegs m a bs.
Proof.
  intros m a bs RE H1 H2 HI. unfold RELRO_BASE, RELRO_LEN in H1, H2.
  split; [lia|]. split; [lia|].
  intros i Hi. rewrite <- (ent_img_nth (length bs) a bs i HI Hi).
  replace (a + Z.of_nat i) with (RELRO_BASE + (a + Z.of_nat i - RELRO_BASE)) by (unfold RELRO_BASE; lia).
  apply RE. unfold RELRO_BASE, RELRO_LEN. lia.
Qed.

(* one byte of the input buffer *)
Lemma ent_sub1 : forall (D : list byte) k, (k < length D)%nat -> firstn 1 (skipn k D) = [nth k D (b8 0)].
Proof.
  induction D as [|d D IH]; intros k Hk; cbn in Hk; [lia|].
  destruct k as [|k]; cbn; [reflexivity|]. apply IH. lia.
Qed.

Lemma ent_pro : forall data D regs0 F fc m lo B o n flags,
  reg_get regs0 10 = Z_to_bv 64 data -> reg_get regs0 11 = Z_to_bv 64 (Z.of_nat (length D)) ->
  bv_unsigned (reg_get regs0 2) mod 16 = 0 -> stk rsegs m lo (bv_unsigned (reg_get regs0 2)) ->
  lo + LH_FRAME + LH_K <= bv_unsigned (reg_get regs0 2) -> bv_unsigned (reg_get regs0 2) < 2 ^ 63 ->
  W_BASE_UBSAN + W_LEN <= lo ->
  ent_dat data D m lo -> mem_inv rsegs m -> relro_img m -> wmem rsegs m B ->
  fuzz_u8_m D (fuzz_in_m (Z.of_nat (length D))) = (FuzzIn o n, flags) ->
  (Z.of_nat (length D) < FUZZ_INPUT_MAX -> forall ms,
     ent_s7f8 data regs0 m (bv_unsigned (reg_get regs0 2) - LH_FRAME) lo B o n flags F fc ms ->
     evt rsegs (ent_Q data D regs0 m (bv_unsigned (reg_get regs0 2) - LH_FRAME) lo F fc) ms) ->
  evt rsegs (ent_Q data D regs0 m (bv_unsigned (reg_get regs0 2) - LH_FRAME) lo F fc)
    (MS (Regs6ss.mkR_of regs0) F (Z_to_bv 64 LH_ENTRY) fc None m (seg_rom rsegs)).
Proof.
  intros data D regs0 F fc m lo B o n flags E10 E11 S16 ST LO H63 HWL HDAT MI RR WM EC1 K.
  pose proof (ent_c1_facts D o n flags EC1) as (Ho & Hn & Hon & Hfl & HD0 & Hn0).
  unfold Regs6ss.mkR_of. rewrite E10, E11.
  lazymatch goal with |- evt _ ?Q _ => set (QQ := Q) end.
  unfold LH_ENTRY, LH_FRAME, LH_K in *.
  pose proof ST as (Hlo & _ & _).
  assert (HLEN : Z.of_nat (length D) < 2 ^ 63).
  { destruct HDAT as [-> | (Hd0 & Hdl & _)]; cbn [length Z.of_nat]; lia. }
  let v := eval vm_compute in (image_bytes rsegs 0x21ef8 32) in
  lazymatch v with
  | Some ?bs =>
      assert (HIO : bytes_at rsegs m 0x21ef8 bs)
        by (apply (ent_relro_bytes m 0x21ef8 bs RR);
            [ unfold RELRO_BASE; lia | unfold RELRO_BASE, RELRO_LEN; cbn [length]; lia | vm_compute; reflexivity ])
  end.
  wk_facts.
  carve_frame 240%nat ST.
  pose proof (munch_refl [(lo, bv_unsigned (reg_get regs0 2) + -240 + 240); (W_BASE_UBSAN, W_BASE_UBSAN + W_LEN)] m)
    as MU0.
  pose proof (wmono_refl rsegs m) as WMO0.
  (* 0x13760-0x13798: addi sp, sp, -240; the 13 saves; mv s0, a0 *)
  do 15 step.
  (* 0x1379c-0x137a4: auipc a0; srli a2, a1, 26; addi a0 = 0x21ef8 *)
  do 3 step.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    pose proof (bytes_at_ov_read rsegs mm 0x21ef8 _ 0 8 HIO ltac:(cbn [length]; lia)) as HR0;
    pose proof (bytes_at_ov_read rsegs mm 0x21ef8 _ 8 8 HIO ltac:(cbn [length]; lia)) as HR1;
    pose proof (bytes_at_ov_read rsegs mm 0x21ef8 _ 16 8 HIO ltac:(cbn [length]; lia)) as HR2;
    pose proof (bytes_at_ov_read rsegs mm 0x21ef8 _ 24 8 HIO ltac:(cbn [length]; lia)) as HR3
  end.
  cbv [firstn skipn] in HR0, HR1, HR2, HR3.
  change (0x21ef8 + Z.of_nat 0) with 0x21ef8 in HR0.
  change (0x21ef8 + Z.of_nat 8) with 0x21f00 in HR1.
  change (0x21ef8 + Z.of_nat 16) with 0x21f08 in HR2.
  change (0x21ef8 + Z.of_nat 24) with 0x21f10 in HR3.
  (* 0x137a8-0x137b4: the four ld of struct diginet_io; 0x137b8-0x137c4: the four sd at sp + 0x40 *)
  do 8 step.
  (* 0x137c8 bnez a2, size >> 26 *)
  step.
  rewrite (unsigned_lit (Z.of_nat (length D))) by lia.
  destruct (Z.ltb_spec (Z.of_nat (length D)) FUZZ_INPUT_MAX) as [HSZ | HSZ].
  2:{ (* size >= 2^26: the exit *)
    assert (Hq : 1 <= Z.shiftr (Z.of_nat (length D)) 26 < 2 ^ 64).
    { rewrite Z.shiftr_div_pow2 by lia. unfold FUZZ_INPUT_MAX in HSZ. split.
      - apply (Z.div_le_lower_bound _ (2 ^ 26)); lia.
      - apply Z.div_lt_upper_bound; lia. }
    ebr true ltac:(unfold bv_eqb; rewrite !unsigned_lit by lia; cbn [negb];
                   apply (proj2 (Bool.negb_true_iff _)); apply Z.eqb_neq; lia).
    apply evt_done. unfold QQ, ent_Q. left.
    eapply ent_out; [lia | lia | unfold LH_FRAME; lia | exact MI | exact MU0 | exact WMO0 | exact FR]. }
  assert (Hq : Z.shiftr (Z.of_nat (length D)) 26 = 0).
  { rewrite Z.shiftr_div_pow2 by lia. apply Z.div_small. unfold FUZZ_INPUT_MAX in HSZ. lia. }
  rewrite Hq.
  ebr false ltac:(reflexivity).
  (* 0x137cc beqz a1: size = 0 *)
  step.
  destruct (Z.eqb_spec (Z.of_nat (length D)) 0) as [L0 | L0].
  - ebr true ltac:(unfold bv_eqb; rewrite !unsigned_lit by lia; apply Z.eqb_eq; lia).
    (* 0x137f0 mv s7, zero; 0x137f4 mv s2, zero *)
    do 2 step.
    destruct (HD0 L0) as (-> & -> & ->).
    apply K; [exact HSZ|]. unfold ent_s7f8. rewrite Z.add_0_r.
    do 25 eexists. eexists. split; [reflexivity|].
    unfold ent_mem, ent_frame. eexists _, _.
    split; [exact ST|]. split; [exact MI|]. split; [exact WM|]. split; [exact MU0|]. split; [exact WMO0|].
    exact FR.
  - ebr false ltac:(unfold bv_eqb; rewrite !unsigned_lit by lia; apply Z.eqb_neq; lia).
    destruct HDAT as [-> | (Hd0 & Hdl & How & HD)]; [cbn in L0; lia|].
    unfold off_world in How.
    pose proof (bytes_at_bound rsegs m data D HD) as HDB.
    destruct (Hn0 L0) as (-> & -> & ->).
    assert (Udata : bv_unsigned (Z_to_bv 64 data) = data) by (apply unsigned_lit; lia).
    (* 0x137d0 addi a0, s0, 1; 0x137d4 li a2, 1; 0x137d8 bltu a2, a0: data + 1 > 1, the trap is not taken *)
    do 3 zstep.
    ebr true ltac:(unfold bv_ltu; rewrite !unsigned_lit by lia; apply Z.ltb_lt; lia).
    (* 0x137e0 lbu s2, 0(s0) *)
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      assert (HDm : bytes_at rsegs mm data D)
        by (eapply bytes_at_transport; [exact HD | exact MU0 | cbn [disjoint_from]; unfold W_BASE_UBSAN, W_LEN in *;
                                         split; [lia | split; [lia | exact I]]]);
      pose proof (bytes_at_read rsegs mm data D 0 1 HDm ltac:(lia) ltac:(cbn [Z.to_nat]; lia)) as HR
    end.
    rewrite ent_sub1 in HR by (cbn [Z.to_nat]; lia).
    zstep.
    (* 0x137e4 addi s7, a1, -1; 0x137e8 mv s0, a0; 0x137ec j 0x137f8 *)
    do 3 zstep.
    apply K; [exact HSZ|]. unfold ent_s7f8.
    do 25 eexists. eexists. split; [reflexivity|].
    unfold ent_mem, ent_frame. eexists _, _.
    split; [exact ST|]. split; [exact MI|]. split; [exact WM|]. split; [exact MU0|]. split; [exact WMO0|].
    exact FR.
Qed.
