From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame Tac Bytes.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib Require Import Img0.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Spec Require Import DgnSpec DgnLib.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Prog Require Import codec_owe codec_cells memcpy_c text_arg_c text_arg_z.
Import ListNotations.
Open Scope Z_scope.

Ltac addr_eq_tac ::= first [ apply wa_of_var; lia
                           | symmetry; first [ apply wa_of_Z_to_bv; lia | apply wa_of_var; lia | unfold wa; f_equal; lia ] ].

(** Paths of text_arg: the in-cursor has n = length data bytes at p. fuzz_u16 takes c = min 2 n of them
    (three paths, joined at 0x14b74 with x0, x1 the low and high byte, 0 when missing); the multiply-shift
    sequence 0x14b74-0x14b9c computes v mod 65 (ta_mod65_seq); bltu/mv give len = min (v mod 65) (n - c);
    0x14ba8-0x14bb4 store the cursor; memcpy copies len bytes; text[len] := 0. There is no abort and no
    branch outside these. *)

Lemma ta_len : forall data, Z.of_nat (text_len data) =
  Z.min (text_u16 data mod 65) (Z.of_nat (length data) - Z.of_nat (text_hdr data)).
Proof.
  intros data. unfold text_len, text_hdr.
  pose proof (Z.mod_pos_bound (text_u16 data) 65 ltac:(lia)). lia.
Qed.

Lemma ta_taken_len : forall data, length (text_taken data) = text_len data.
Proof.
  intros data. unfold text_taken, text_len, text_hdr.
  rewrite firstn_length_le; [reflexivity|]. rewrite length_skipn. lia.
Qed.

Lemma ta_le1_zero : le1 (Z_to_bv 64 0) = [b8 0].
Proof. first [ vm_compute; reflexivity | rewrite <- le1_zxb; f_equal; apply bv_eq; reflexivity ]. Qed.

Lemma ta_u16_nil : forall d : list byte, length d = 0%nat -> text_u16 d = 0.
Proof. intros [|x d] H; [vm_compute; reflexivity | discriminate]. Qed.

Lemma ta_u16_one : forall d : list byte, length d = 1%nat -> text_u16 d = bv_unsigned (nth 0 d (Z_to_bv 8 0)).
Proof.
  intros [|x [|y d]] H; try discriminate. unfold text_u16, b8. cbn [nth].
  replace (bv_unsigned (Z_to_bv 8 0)) with 0 by (vm_compute; reflexivity). lia.
Qed.

Lemma ta_u16_two : forall d : list byte,
  text_u16 d = bv_unsigned (nth 0 d (Z_to_bv 8 0)) + 256 * bv_unsigned (nth 1 d (Z_to_bv 8 0)).
Proof. intros d. reflexivity. Qed.

Section TA.
Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 a0 a1 : word) (F : bvmap 5 word) (fc : bv 32)
          (m : word -> option byte) (lo p : Z) (data tj : list byte).
Hypothesis MEMC : memcpy_contract.
Hypothesis Rsp : 0 <= bv_unsigned sp < 2^64.
Hypothesis HS0 : bv_unsigned sp <= bv_unsigned a0.
Hypothesis HS1 : bv_unsigned sp <= bv_unsigned a1.
Hypothesis HLO : p + Z.of_nat (length data) <= lo \/ bv_unsigned sp <= p.
Hypothesis LO : lo + 32 <= bv_unsigned sp.
Hypothesis D01 : bv_unsigned a0 + 16 <= bv_unsigned a1 \/ bv_unsigned a1 + 65 <= bv_unsigned a0.
Hypothesis Dp1 : p + Z.of_nat (length data) <= bv_unsigned a1 \/ bv_unsigned a1 + 65 <= p.
Hypothesis Dp0 : p + Z.of_nat (length data) <= bv_unsigned a0 \/ bv_unsigned a0 + 16 <= p.
Hypothesis Bd : 0 <= p /\ p + Z.of_nat (length data) <= 2^64.
Hypothesis BA0 : 0 <= bv_unsigned a0 /\ bv_unsigned a0 + 16 <= 2^64.
Hypothesis BA1 : 0 <= bv_unsigned a1 /\ bv_unsigned a1 + 65 <= 2^64.
Hypothesis HN : Z.of_nat (length data) < 2^64.
Hypothesis LT : length tj = 65%nat.

Definition Qt (ms' : machine_state) : Prop :=
  exists (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : word -> option byte),
    ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7'
                  s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
             F (ret_pc ra) fc None m' (seg_rom rsegs) /\
    munch [(bv_unsigned sp + -32, bv_unsigned sp); (bv_unsigned a0, bv_unsigned a0 + 16);
           (bv_unsigned a1, bv_unsigned a1 + 65)] m m' /\
    wmono rsegs m m' /\
    mem_inv rsegs m' /\
    stk rsegs m' lo (bv_unsigned sp) /\
    rw_cells rsegs m' (bv_unsigned a0)
      [C8 (Z_to_bv 64 (p + Z.of_nat (text_used data))); C8 (Z_to_bv 64 (Z.of_nat (length data - text_used data)))] /\
    rw_cells rsegs m' (bv_unsigned a1) [CB 65 (text_taken data ++ [b8 0] ++ skipn (S (text_len data)) tj)].

(** 0x14ba8 - return: the cursor stores, memcpy (text, p + c, len), text[len] := 0, epilogue. *)
Lemma ta_fin : forall (ra' t0' t1' t2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (j : list byte) (c L : Z)
                      (m1 : word -> option byte),
  c = Z.of_nat (text_hdr data) -> L = Z.of_nat (text_len data) ->
  rw_cells rsegs m1 (bv_unsigned sp + -32) [CB 8 j; C8 s1; C8 s0; C8 ra] ->
  stk rsegs m1 lo (bv_unsigned sp + -32) ->
  rw_cells rsegs m1 (bv_unsigned a0) [C8 (Z_to_bv 64 (p + c)); C8 (Z_to_bv 64 (Z.of_nat (length data) - c))] ->
  bytes_at rsegs m1 p data ->
  rw_cells rsegs m1 (bv_unsigned a1) [CB 65 tj] ->
  munch [(bv_unsigned sp + -32, bv_unsigned sp); (bv_unsigned a0, bv_unsigned a0 + 16);
         (bv_unsigned a1, bv_unsigned a1 + 65)] m m1 ->
  wmono rsegs m m1 -> mem_inv rsegs m1 ->
  evt rsegs Qt
    (MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -32)) gp tp t0' t1' t2' a1 (Z_to_bv 64 L) a0
             (Z_to_bv 64 (Z.of_nat (length data) - c)) (Z_to_bv 64 (p + c)) a3' a4' a5' a6' a7'
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
        F (Z_to_bv 64 0x14ba8) fc None m1 (seg_rom rsegs)).
Proof.
  intros ra' t0' t1' t2' a3' a4' a5' a6' a7' t3' t4' t5' t6' j c L m1 Hc HL FR ST HIN HD HT MU WM HMI.
  assert (Hc2 : 0 <= c <= 2) by (rewrite Hc; unfold text_hdr; lia).
  assert (HcN : c <= Z.of_nat (length data)) by (rewrite Hc; unfold text_hdr; lia).
  pose proof (ta_len data) as HLm. rewrite <- Hc, <- HL in HLm.
  pose proof (Z.mod_pos_bound (text_u16 data) 65 ltac:(lia)) as Hmod.
  assert (HL0 : 0 <= L <= 64) by lia.
  assert (HLn : c + L <= Z.of_nat (length data)) by lia.
  assert (UL : bv_unsigned (Z_to_bv 64 L) = L) by (apply unsigned_lit; lia).
  clear HLm Hmod.
  (* add a3, a2, s1; sub a1, a1, s1; sd a3, 0(a0); sd a1, 8(a0); mv a0, s0; mv a1, a2; mv a2, s1; jal memcpy *)
  do 8 zstep.
  match goal with H : rw_cells rsegs ?mm (bv_unsigned a1) [CB 65 tj] |- _ =>
    destruct (ta_rw_split rsegs mm _ (Z.to_nat L) 65 tj ltac:(lia) H) as [HT1 HT2]; clear H end.
  assert (HSRC : forall mm, bytes_at rsegs mm p data ->
                   bytes_at rsegs mm (bv_unsigned (Z_to_bv 64 (p + c))) (text_taken data)).
  { intros mm HDm. unfold text_taken. replace (text_hdr data) with (Z.to_nat c) by lia.
    apply ta_bytes_sub; [lia | | exact HDm]. lia. }
  call MEMC.
  { apply HSRC. eassumption. }
  { rewrite UL, ta_taken_len. lia. }
  { eapply ta_rw_cb_eq; [eassumption | rewrite UL; reflexivity]. }
  { rewrite UL. destruct (Z.eq_dec L 0) as [E0|E0].
    - pose proof (ta_u64 (Z_to_bv 64 (p + c))). lia.
    - rewrite (unsigned_lit (p + c)) by lia. lia. }
  { eassumption. }
  (* add s0, s0, s1 *)
  zstep.
  match goal with H : rw_cells rsegs ?mm (bv_unsigned a1 + Z.of_nat (Z.to_nat L)) _ |- _ =>
    rewrite (Z2Nat.id L) in H by lia;
    destruct (ta_rw_split rsegs mm _ 1 (65 - Z.to_nat L) _ ltac:(lia) H) as [HB1 HB2]; clear H end.
  change (Z.of_nat 1) with 1 in HB2.
  remember (bv_unsigned a1 + L) as T eqn:HeqT.
  (* sb zero, 0(s0): the stored byte le1 0 is b8 0 *)
  zstep.
  rewrite ta_le1_zero.
  mem_after_store.
  (* ld ra; ld s0; ld s1; addi sp; ret *)
  do 4 zstep.
  release_frame FR ST (bv_unsigned sp).
  zstep.
  finish.
  - eapply ta_rw_c8_eq; [eassumption | f_equal; unfold text_used; lia | f_equal; unfold text_used; lia].
  - eapply ta_text_final; [eassumption | eassumption | eassumption | lia | lia | ].
    apply (f_equal (fun z => text_taken data ++ z)). cbn [app].
    f_equal. all: first [ reflexivity | (rewrite skipn_skipn; f_equal; lia) | (apply bv_eq; vm_compute; reflexivity) ].
Qed.

(** 0x14b74 - 0x14ba4: v = x0 + 256 x1, s1 = v mod 65, then len = min (v mod 65) (n - c). *)
Lemma ta_mod : forall (ra' t0' t1' t2' x9 r1 r2 r3 r4 a5' a6' a7' t3' t4' t5' t6' w0 w1 : word) (j : list byte)
                      (c x0 x1 : Z) (m1 : word -> option byte),
  rw_cells rsegs m1 (bv_unsigned sp + -32) [CB 8 j; C8 s1; C8 s0; C8 ra] ->
  stk rsegs m1 lo (bv_unsigned sp + -32) ->
  rw_cells rsegs m1 (bv_unsigned a0) [C8 w0; C8 w1] ->
  bytes_at rsegs m1 p data ->
  rw_cells rsegs m1 (bv_unsigned a1) [CB 65 tj] ->
  munch [(bv_unsigned sp + -32, bv_unsigned sp); (bv_unsigned a0, bv_unsigned a0 + 16);
         (bv_unsigned a1, bv_unsigned a1 + 65)] m m1 ->
  wmono rsegs m m1 -> mem_inv rsegs m1 ->
  c = Z.of_nat (text_hdr data) ->
  0 <= x0 < 256 -> 0 <= x1 < 256 -> x0 + 256 * x1 = text_u16 data ->
  w0 = Z_to_bv 64 (p + c) -> w1 = Z_to_bv 64 (Z.of_nat (length data) - c) ->
  r1 = Z_to_bv 64 (Z.of_nat (length data) - c) -> r2 = Z_to_bv 64 (p + c) ->
  r3 = Z_to_bv 64 x0 -> r4 = Z_to_bv 64 x1 ->
  evt rsegs Qt
    (MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -32)) gp tp t0' t1' t2' a1 x9 a0 r1 r2 r3 r4 a5' a6' a7'
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
        F (Z_to_bv 64 0x14b74) fc None m1 (seg_rom rsegs)).
Proof.
  intros ra' t0' t1' t2' x9 r1 r2 r3 r4 a5' a6' a7' t3' t4' t5' t6' w0 w1 j c x0 x1 m1
         FR ST HIN HD HT MU WM HMI Hc Hx0 Hx1 Hv E0 E1 E2 E3 E4 E5.
  subst w0 w1 r1 r2 r3 r4.
  assert (Hc2 : 0 <= c <= 2) by (rewrite Hc; unfold text_hdr; lia).
  assert (HcN : c <= Z.of_nat (length data)) by (rewrite Hc; unfold text_hdr; lia).
  (* slli; lui; or; addiw; mul; srli; slli; subw; subw; slli; srli *)
  do 11 zstep.
  rewrite (ta_mod65_seq x0 x1 Hx0 Hx1), Hv.
  (* bltu s1, a1 *)
  zstep.
  if_cases K.
  - zify_cond K. eapply ta_fin; first [eassumption | rewrite ta_len; lia].
  - zify_cond K. zstep. eapply ta_fin; first [eassumption | rewrite ta_len; lia].
Qed.

(** Entry: prologue, the loads of p and n, and the three fuzz_u16 paths (n = 0, n = 1, n >= 2). *)
Lemma ta_entry : forall (t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
  rw_cells rsegs m (bv_unsigned a0) [C8 (Z_to_bv 64 p); C8 (Z_to_bv 64 (Z.of_nat (length data)))] ->
  bytes_at rsegs m p data ->
  rw_cells rsegs m (bv_unsigned a1) [CB 65 tj] ->
  mem_inv rsegs m -> stk rsegs m lo (bv_unsigned sp) ->
  evt rsegs Qt (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                   F (Z_to_bv 64 0x14b10) fc None m (seg_rom rsegs)).
Proof.
  intros t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 HIN HD HT HMI ST.
  pose proof (munch_refl [(bv_unsigned sp + -32, bv_unsigned sp); (bv_unsigned a0, bv_unsigned a0 + 16);
         (bv_unsigned a1, bv_unsigned a1 + 65)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  carve_frame 32%nat ST.
  (* addi sp; sd ra; sd s0; sd s1; ld a4, 8(a0); ld a2, 0(a0); mv s0, a1; beqz a4 *)
  do 8 zstep.
  if_cases K0.
  - (* n = 0: mv a1, zero; mv a3, zero; j 0x14b74 *)
    zify_cond K0. do 3 zstep.
    eapply ta_mod with (c := 0) (x0 := 0) (x1 := 0);
      first [ eassumption | lia | (f_equal; lia) | (unfold text_hdr; lia)
            | (rewrite ta_u16_nil by lia; lia) ].
  - zify_cond K0.
    (* addi a1, a4, -1; addi a5, a2, 1; sd a5, 0(a0); sd a1, 8(a0) *)
    do 4 zstep.
    match goal with HDm : bytes_at rsegs ?mm p data |- _ =>
      pose proof (ta_byte rsegs mm p data 0 HDm ltac:(lia)) as HR0 end.
    change (Z.to_nat 0) with 0%nat in HR0.
    pose proof (ta_u8 (nth 0 data (Z_to_bv 8 0))) as Rb0.
    (* lbu a3, 0(a2); beqz a1 *)
    do 2 zstep.
    if_cases K1.
    + (* n = 1: mv a4, zero; mv a2, a5 *)
      zify_cond K1. do 2 zstep.
      eapply ta_mod with (c := 1) (x0 := bv_unsigned (nth 0 data (Z_to_bv 8 0))) (x1 := 0);
        first [ eassumption | lia | (f_equal; lia) | (unfold text_hdr; lia)
              | (rewrite ta_u16_one by lia; lia) ].
    + (* n >= 2: addi a1, a4, -2; addi a5, a2, 2; sd a5; sd a1; lbu a4, 1(a2); j; mv a2, a5 *)
      zify_cond K1. do 4 zstep.
      match goal with HDm : bytes_at rsegs ?mm p data |- _ =>
        pose proof (ta_byte rsegs mm p data 1 HDm ltac:(lia)) as HR1 end.
      change (Z.to_nat 1) with 1%nat in HR1.
      pose proof (ta_u8 (nth 1 data (Z_to_bv 8 0))) as Rb1.
      do 3 zstep.
      eapply ta_mod with (c := 2) (x0 := bv_unsigned (nth 0 data (Z_to_bv 8 0)))
                         (x1 := bv_unsigned (nth 1 data (Z_to_bv 8 0)));
        first [ eassumption | lia | (f_equal; lia) | (unfold text_hdr; lia)
              | (rewrite ta_u16_two; lia) ].
Qed.

End TA.

Theorem text_arg_holds : memcpy_contract -> text_arg_contract.
Proof.
  intros MEMC. unfold text_arg_contract, text_arg_pre, TEXT_ARG, TEXT_ARG_DEPTH.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
         F fc m lo p data tj (HIN & HD & HT & DJ01 & DJp1 & DJp0 & HS0 & HS1 & HLO & HMI & ST & LO).
  unfold disj in DJ01, DJp1, DJp0.
  pose proof (bytes_at_bound rsegs m p data HD) as Bd.
  pose proof (rw_cells_bound rsegs m _ _ HIN) as BA0. pose proof (rw_cells_bound rsegs m _ _ HT) as BA1.
  cbn [cells_size csize Nat.add] in BA0, BA1.
  change (Z.of_nat 16) with 16 in BA0. change (Z.of_nat 65) with 65 in BA1.
  pose proof (ta_u64 sp) as Rsp.
  assert (HN : Z.of_nat (length data) < 2^64) by lia.
  assert (LT : length tj = 65%nat) by (destruct HT as [[[Hl _] _] _]; exact Hl).
  eapply ta_entry; eassumption.
Qed.
