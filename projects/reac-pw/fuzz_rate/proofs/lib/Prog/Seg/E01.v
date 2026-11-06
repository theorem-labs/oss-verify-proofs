(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Copyright 2026 Theorem Labs *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_decode/lib/Prog/LLVMFuzzerTestOneInput_fr.v, with its module paths and module names changed; 456 of its 574 lines of code are new or changed and 409 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_headamp/lib/Prog/Seg/Tac_slot.v, with its module paths and module names changed; 289 of its 323 lines of code are new or changed and 540 lines of the source are left out. *)
(* Segment E01 of reac-pw/fuzz_rate LLVMFuzzerTestOneInput (plain): [0x12fc0, 0x13154], ENTRY -> K13158
   (Prog/LLVMFuzzerTestOneInput_c.v's S_E01).
   The prologue (0x12fc0 `addi sp,sp,-0x220`; ra, s0 .. s11 saved at S - 8 .. S - 104), the n >= 2^26 exit not taken
   (0x12ff8 `srli a2,a1,26`, 0x12ffc `beqz a2`: GV bounds n below 2^26), the cursor 0x13004 `mv s5,a0` and the seven
   header reads (fuzz.h:37-56, 0x13008 .. 0x13144), eight paths by the input length n = 0, 1, .., 6 and n >= 7: each
   fuzz_u8 reads byte i when one is left, else gives 0 and every later value is 0. s6 = byte 0, s9 = byte 1,
   s10 = byte 2 mod 24 (0x1308c-0x130ac: the 8-byte .rodata constant 0x0aaaaaaaaaaaaaab at 0x104e0 through auipc/ld,
   `mulhu`, `slli 5`, `slli 3`, `sub`, `add`: e01_q24 checks the quotient for all 256 bytes), s7 = byte 3, the cell
   sp + 0x30 = byte 4 << 8 (`slliw a3,a0,8` / `sd a3,0x30(sp)`, or `sd zero,0x30(sp)` on the short paths),
   s11 = byte 5, s4 = byte 6 << 8, s0 = n - 7 or 0, s5 = data + min 7 n; then 0x13148 `lui s1,5`, `addiw s3,s1,-0x2e0`
   (19744), `mv a0,s3` and malloc(19744) at 0x13154 with ra = 0x13158 through Tac_b1.b1_malloc_call from hb = [],
   whose continuation gives Inv_K13158 (the cell survives malloc by its clause on the bytes of [fsp g, g_S g), the
   registers by regs_preserved). No other call.
   Adapted from reac-pw/fuzz_role's Prog/Seg/E01.v (itself fuzz_pin's
   Prog/Seg/E01.v and libreac/fuzz_ctrl's released segments A01 and F01, origin/ossv/recipes 25e3d17bdb50,
   Prog/Seg/): the run from Inv_ENTRY on the normalized memory, FR with hb = [], malloc as a Kind B step. *)
From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YL01 YL00 YL0g YI06 YI16 YI14.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib Require Import Contract Img0 FrameAPI.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Lib Require Import PropExec MState Mem Exec Frame Step Cells Tac.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Lib Require Import ZBridge.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Lib Require Regs6ss RegisterBridge.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Prog Require Import SlotFR SlotInv LLVMFuzzerTestOneInput_c.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Prog.Seg Require Import Tac_slot Tac_b1.
Import ListNotations.
Open Scope Z_scope.

(* ---- The header quantities (SlotInv's g_u8, g_k, g_src for inp = g_in g, p = g_p g) ---- *)
Definition e01_u8 (inp : list byte) (i : nat) : Z :=
  match nth_error inp i with Some b => bv_unsigned b | None => 0 end.
Definition e01_k (inp : list byte) : Z := Z.of_nat (length inp) - Z.min 7 (Z.of_nat (length inp)).
Definition e01_src (p : Z) (inp : list byte) : Z := p + Z.min 7 (Z.of_nat (length inp)).

(* ---- Bytes and words ---- *)
Lemma e01_rd0 : forall m (a : word) b l, bytes_at rsegs m (bv_unsigned a) (b :: l) ->
  ov_read_bytes rsegs m a 1 = Some [b].
Proof.
  intros m a b l H.
  assert (E : a = wa (bv_unsigned a + Z.of_nat 0)).
  { unfold wa. rewrite Z.add_0_r. symmetry. apply Z_to_bv_lit_self. }
  rewrite E. rewrite (bytes_at_ov_read rsegs m (bv_unsigned a) (b :: l) 0 1 H) by (cbn; lia). reflexivity.
Qed.

Lemma e01_first1 : forall (l : list byte) k b, nth_error l k = Some b -> firstn 1 (skipn k l) = [b].
Proof.
  induction l as [|x l IH]; intros k b E; destruct k as [|k]; cbn in E |- *; try discriminate.
  - injection E as ->. reflexivity.
  - exact (IH k b E).
Qed.

(* lbu at a + k, byte k of the input. *)
Lemma e01_rd : forall m a l (k : Z) b, bytes_at rsegs m a l -> 0 <= k -> nth_error l (Z.to_nat k) = Some b ->
  ov_read_bytes rsegs m (wa (a + k)) 1 = Some [b].
Proof.
  intros m a l k b H Hk E.
  assert (Hl : (Z.to_nat k < length l)%nat) by (apply nth_error_Some; congruence).
  rewrite (bytes_at_read rsegs m a l k 1 H Hk) by lia.
  rewrite (e01_first1 l (Z.to_nat k) b E). reflexivity.
Qed.

Lemma e01_weq_l : forall (x : word) e, bv_unsigned x mod 2 ^ 64 = e mod 2 ^ 64 -> x = Z_to_bv 64 e.
Proof. intros x e H. rewrite <- (Z_to_bv_lit_self x). apply Z_to_bv_eqm. exact H. Qed.

(* 0x12ff8 `srli a2,a1,26`; 0x12ffc `beqz a2`: taken for n < 2^26. *)
Lemma e01_cond : forall u, 0 <= u < 2 ^ 26 ->
  bv_eqb (Z_to_bv 64 (Z.shiftr u 26)) (Z_to_bv 64 0) = true.
Proof. intros u Hu. rewrite Z.shiftr_div_pow2 by lia. rewrite Z.div_small by lia. reflexivity. Qed.

(* 0x13098 `mulhu a2,a0,a2` with a2 = 0x0aaaaaaaaaaaaaab (the .rodata constant at 0x104e0): the high word of
   b * 0x0aaaaaaaaaaaaaab is b / 24 for every byte b. *)
Lemma e01_q24 : forall x, 0 <= x < 256 -> x * 768614336404564651 / 2 ^ 64 = x / 24.
Proof.
  intros x Hx.
  assert (C : forallb (fun k => Z.eqb (Z.of_nat k * 768614336404564651 / 2 ^ 64) (Z.of_nat k / 24))
                (seq 0 256) = true) by (vm_compute; reflexivity).
  rewrite forallb_forall in C.
  assert (HI : In (Z.to_nat x) (seq 0 256)) by (apply in_seq; lia).
  specialize (C _ HI). rewrite Z2Nat.id in C by lia. apply Z.eqb_eq. exact C.
Qed.

Ltac e01_m24 :=
  repeat match goal with
  | |- context [768614336404564651 mod 2 ^ 64] =>
      change (768614336404564651 mod 2 ^ 64) with 768614336404564651
  | |- context [?x * 768614336404564651 / 2 ^ 64] =>
      rewrite (e01_q24 x) by (Z.div_mod_to_equations; lia)
  end.

Lemma e01_hm32 : bv_half_modulus 32 = 2 ^ 31.
Proof. reflexivity. Qed.
Lemma e01_m32 : bv_modulus 32 = 2 ^ 32.
Proof. reflexivity. Qed.
Lemma e01_m64 : bv_modulus 64 = 2 ^ 64.
Proof. reflexivity. Qed.

Ltac e01_weq :=
  first [ reflexivity
        | apply e01_weq_l; unfold zxb; rewrite ?unsigned_lit_wrap;
          rewrite ?Z.shiftl_mul_pow2, ?Z.shiftr_div_pow2 by lia; e01_m24;
          unfold bv_swrap, bv_wrap; rewrite ?e01_hm32, ?e01_m32, ?e01_m64;
          Z.div_mod_to_equations; lia ].

(* A branch: keep the side the facts allow. *)
Ltac e01_if :=
  lazymatch goal with
  | |- evt _ _ (MS _ _ (if _ then _ else _) _ _ _ _) =>
      let H := fresh "EC" in if_cases H; zify_cond H; try (exfalso; lia)
  | _ => idtac
  end.

(* ---- The run: ENTRY to malloc's entry with ra = 0x13158 ---- *)
Definition e01_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (m : word -> option byte) (p : Z) (inp : list byte) (ms' : machine_state) : Prop :=
  exists (t0' t1' t2' s0' s1' a0' a1' a2' a3' a4' a5' a6' a7' s3' s4' s5' s6' s7' s9' s10' s11' t3' t4' t5' t6' : word)
         (m' : word -> option byte),
    ms' = MS (mkR (Z_to_bv 64 0x13158) (Z_to_bv 64 (bv_unsigned sp + -544)) gp tp t0' t1' t2' s0' s1' a0' a1' a2'
                  a3' a4' a5' a6' a7' s2 s3' s4' s5' s6' s7' s8 s9' s10' s11' t3' t4' t5' t6')
             F (Z_to_bv 64 0x16694) fc None m' (seg_rom rsegs) /\
    s0' = Z_to_bv 64 (e01_k inp) /\ s1' = Z_to_bv 64 0x5000 /\ a0' = Z_to_bv 64 POD_PROPS /\
    s3' = Z_to_bv 64 POD_PROPS /\ s4' = Z_to_bv 64 (e01_u8 inp 6 * 256) /\ s5' = Z_to_bv 64 (e01_src p inp) /\
    s6' = Z_to_bv 64 (e01_u8 inp 0) /\ s7' = Z_to_bv 64 (e01_u8 inp 3) /\ s9' = Z_to_bv 64 (e01_u8 inp 1) /\
    s10' = Z_to_bv 64 (e01_u8 inp 2 mod 24) /\ s11' = Z_to_bv 64 (e01_u8 inp 5) /\
    Frame.munch [(bv_unsigned sp - 544, bv_unsigned sp)] m m' /\ Frame.wmono rsegs m m' /\
    bytes_at rsegs m' (bv_unsigned sp - 544 + 48) (le8 (Z_to_bv 64 (e01_u8 inp 4 * 256))) /\
    bytes_at rsegs m' (bv_unsigned sp - 104)
      (le8 s11 ++ le8 s10 ++ le8 s9 ++ le8 s8 ++ le8 s7 ++ le8 s6 ++ le8 s5 ++ le8 s4 ++ le8 s3 ++ le8 s2 ++
       le8 s1 ++ le8 s0 ++ le8 ra).

(* The frame's cells at malloc's entry: [sp, sp + 48) junk, the cell sp + 0x30, junk up to the saved registers at
   sp + 440. *)
Lemma e01_cells : forall m A j1 c j2 cs,
  rw_cells rsegs m A (CB 48 j1 :: c :: CB 384 j2 :: cs) -> csize c = 8%nat ->
  bytes_at rsegs m (A + 48) (cbytes c) /\ bytes_at rsegs m (A + 440) (cells_bytes cs).
Proof.
  intros m A j1 c j2 cs [[Hwf Hb] _] Hc.
  destruct Hwf as (W1 & W2 & W3 & _).
  cbn [cell_wf] in W1, W3.
  pose proof (cbytes_length c W2) as L2. rewrite Hc in L2.
  cbn [cells_bytes cbytes] in Hb.
  apply bytes_at_app in Hb as [_ Hb]. rewrite W1 in Hb.
  apply bytes_at_app in Hb as [H1 Hb]. rewrite L2 in Hb.
  apply bytes_at_app in Hb as [_ Hb]. rewrite W3 in Hb.
  split; [exact H1|].
  replace (A + 440) with (A + Z.of_nat 48 + Z.of_nat 8 + Z.of_nat 384) by (cbn; lia). exact Hb.
Qed.

Ltac e01_eqs := unfold e01_k, e01_src, e01_u8, POD_PROPS; cbn [length nth_error]; e01_weq.

Ltac e01_conj SC SB :=
  lazymatch goal with
  | |- _ = _ /\ _ => split; [e01_eqs | e01_conj SC SB]
  | |- _ =>
      split; [assumption|]; split; [assumption|];
      split; [refine (bytes_at_ext rsegs _ _ _ _ SC _); f_equal; e01_eqs | exact SB]
  end.

Ltac e01_fin sp :=
  lazymatch goal with
  | FR : rw_cells _ _ _ (CB 48 _ :: _ :: CB 384 _ :: _) |- _ =>
      let SC := fresh "SC" in let SB := fresh "SB" in
      destruct (e01_cells _ _ _ _ _ _ FR eq_refl) as [SC SB];
      cbn [cells_bytes cbytes] in SC, SB; rewrite ?app_nil_r in SB;
      lazymatch type of SB with bytes_at _ _ ?x _ => replace x with (bv_unsigned sp - 104) in SB by lia end;
      lazymatch type of SC with bytes_at _ _ ?x _ => replace x with (bv_unsigned sp - 544 + 48) in SC by lia end;
      apply evt_done; unfold e01_post;
      do 26 eexists; split; [reflexivity|];
      e01_conj SC SB
  | FR : rw_cells _ _ _ ?cs |- _ => fail 100 "e01_fin: the frame cells are not [CB 48; cell; CB 384; saves]:" cs
  end.

Lemma e01_evt :
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo p : Z) (inp : list byte),
    stk rsegs m lo (bv_unsigned sp) -> lo + 544 <= bv_unsigned sp -> mem_inv rsegs m ->
    bv_unsigned a0 = p -> bv_unsigned a1 = Z.of_nat (length inp) -> Z.of_nat (length inp) < 2 ^ 26 ->
    p + Z.of_nat (length inp) <= lo -> bytes_at rsegs m p inp ->
    evt rsegs (e01_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m p inp)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x12fc0) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m lo p inp ST LO HMI0 Ep Ha1 H26 Hin Hb.
  subst p.
  pose proof (munch_refl [(bv_unsigned sp - 544, bv_unsigned sp)] m) as MU.
  assert (Hlo : 0 <= lo) by (destruct ST as [H _]; exact H).
  pose proof (wmono_refl rsegs m) as WM.
  pose proof (bv_unsigned_in_range 64 sp) as Rsp. unfold bv_modulus in Rsp. change (2 ^ Z.of_N 64) with (2 ^ 64) in Rsp.
  pose proof (bv_unsigned_in_range 64 a0) as Ra0. unfold bv_modulus in Ra0. change (2 ^ Z.of_N 64) with (2 ^ 64) in Ra0.
  pose proof (bv_unsigned_in_range 64 a1) as Ra1. unfold bv_modulus in Ra1. change (2 ^ Z.of_N 64) with (2 ^ 64) in Ra1.
  carve_frame 544%nat ST.
  do 16 step.
  if_true_by (e01_cond (bv_unsigned a1) ltac:(lia)).
  (* 0x13004 `mv s5,a0`; 0x13008 `beqz a1` *)
  step. step.
  destruct inp as [|b0 inp]; cbn [length] in Ha1, H26, Hin.
  { (* n = 0: 0x1303c .. 0x1305c, 0x13148 .. 0x13154 *)
    e01_if. do 13 step. e01_fin sp. }
  pose proof (b1_byte_rng b0) as R0.
  e01_if.
  (* 0x1300c `lbu s6,0(s5)`, `addi a0,zero,1`, `bne a1,a0` *)
  pose proof (e01_rd0 _ _ _ _ Hb) as HB0.
  do 3 step.
  destruct inp as [|b1 inp]; cbn [length] in Ha1, H26, Hin.
  { (* n = 1: 0x13018 .. 0x13038 *)
    e01_if. do 13 step. e01_fin sp. }
  pose proof (b1_byte_rng b1) as R1.
  e01_if.
  (* 0x13060 `lbu s9,1(s5)`, `addi a0,zero,2`, `bne a1,a0` *)
  pose proof (e01_rd _ _ _ 1 _ Hb ltac:(lia) eq_refl) as HB1.
  do 3 step.
  destruct inp as [|b2 inp]; cbn [length] in Ha1, H26, Hin.
  { (* n = 2: 0x1306c .. 0x13088 *)
    e01_if. do 12 step. e01_fin sp. }
  pose proof (b1_byte_rng b2) as R2.
  e01_if.
  (* 0x1308c `lbu a0,2(s5)`, the constant, `mulhu`, the remainder in s10, `addi a3,zero,3`, `bne a1,a3` *)
  pose proof (e01_rd _ _ _ 2 _ Hb ltac:(lia) eq_refl) as HB2.
  do 10 step.
  destruct inp as [|b3 inp]; cbn [length] in Ha1, H26, Hin.
  { (* n = 3: 0x130b4 .. 0x130cc *)
    e01_if. do 11 step. e01_fin sp. }
  pose proof (b1_byte_rng b3) as R3.
  e01_if.
  (* 0x130d0 `lbu s7,3(s5)`, `addi a0,zero,4`, `bne a1,a0` *)
  pose proof (e01_rd _ _ _ 3 _ Hb ltac:(lia) eq_refl) as HB3.
  do 3 step.
  destruct inp as [|b4 inp]; cbn [length] in Ha1, H26, Hin.
  { (* n = 4: 0x130dc .. 0x130f0 *)
    e01_if. do 10 step. e01_fin sp. }
  pose proof (b1_byte_rng b4) as R4.
  e01_if.
  (* 0x130f4 `lbu a0,4(s5)`, `addi a2,zero,5`, `slliw a3,a0,8`, `sd a3,0x30(sp)`, `bne a1,a2` *)
  pose proof (e01_rd _ _ _ 4 _ Hb ltac:(lia) eq_refl) as HB4.
  do 5 step.
  destruct inp as [|b5 inp]; cbn [length] in Ha1, H26, Hin.
  { (* n = 5: 0x13108 .. 0x13118 *)
    e01_if. do 9 step. e01_fin sp. }
  pose proof (b1_byte_rng b5) as R5.
  e01_if.
  (* 0x1311c `lbu s11,5(s5)`, `addi a0,zero,6`, `bne a1,a0` *)
  pose proof (e01_rd _ _ _ 5 _ Hb ltac:(lia) eq_refl) as HB5.
  do 3 step.
  destruct inp as [|b6 inp]; cbn [length] in Ha1, H26, Hin.
  { (* n = 6: 0x13128 .. 0x13134 *)
    e01_if. do 8 step. e01_fin sp. }
  pose proof (b1_byte_rng b6) as R6.
  e01_if.
  (* n >= 7: 0x13138 `lbu a0,6(s5)`, `addi s0,a1,-7`, `addi s5,s5,7`, `slli s4,a0,8`, then 0x13148 .. 0x13154 *)
  pose proof (e01_rd _ _ _ 6 _ Hb ltac:(lia) eq_refl) as HB6.
  do 8 step.
  e01_fin sp.
Qed.

(* ---- The segment ---- *)
Ltac e01_rp RP Hx r :=
  etransitivity; [exact (RP r ltac:(unfold callee_saved; lia))|]; rewrite (sl_getr_eqv _ _ _ Hx); reflexivity.

Section E01.
Context {fx : FPState} {rc : RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : RunCeil, AllocAPI B.
Context {LS : lib_shape} {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.
Hypothesis FF : frame_facts_plain B APIf LS SH SK ra empty.

Lemma seg_E01 : S_E01 B APIf ra empty.
Proof.
  unfold S_E01. intros H1 g c (Ec & HGV & Hpre & Hsp & Hsn & HMI & Hrel & Hres & Hfrm).
  subst c.
  pose proof (sl_segs B APIf ra empty FF) as SEGS.
  pose proof HGV as (Hn26 & Hpl & Hdat & HS16 & HSK & HS47 & _ & HGsp & HGtp).
  pose proof Hpre as (HM & HW & HB & HID & Hra & Hal & Hceil & H63 & Hstw & Htp & Herr & Hp & Hn & Hpp & Hrod).
  pose proof alloc_ceiling_value as Hac.
  pose proof sl_ceil as Hct.
  unfold SLOT_K, SLOT_STACK, SL_TOP in *.
  assert (Esp2 : bv_unsigned (YK11.getr (g_regs g) 2) = g_S g).
  { rewrite Hsp. apply MState.unsigned_lit. lia. }
  assert (Esp : spZ (g_regs g) = g_S g) by exact Esp2.
  (* The input block lies below alloc_ceiling, so below the stack window. *)
  assert (Hpb : 0 <= g_p g /\ g_p g + g_n g <= g_S g - 65536).
  { destruct Hpl as [(Hn0 & Hpe) | (Hn0 & Hin)].
    - rewrite Hn0, Hpe, (ff_empty_val B APIf ra empty FF). lia.
    - destruct (b1_blk B APIf ra empty FF _ _ _ _ _ _ HM Hin) as (_ & Hb1 & Hb2). lia. }
  assert (Ep : bv_unsigned (YK11.getr (g_regs g) 10) = g_p g).
  { rewrite Hp. apply MState.unsigned_lit. lia. }
  assert (En : bv_unsigned (YK11.getr (g_regs g) 11) = Z.of_nat (length (g_in g))).
  { rewrite Hn. apply MState.unsigned_lit. unfold g_n in *. lia. }
  unfold MI in HMI. rewrite SEGS in HMI.
  assert (Hdat' : bytes_at rsegs (normalize rsegs (g_mem g)) (g_p g) (g_in g)).
  { apply (proj1 (bytes_at_rel rsegs _ _ _ _ (mem_rel_normalize rsegs (g_mem g) HMI))).
    split; [lia|]. split; [unfold g_n in Hpb; lia|].
    intros k Hk. pose proof (Hdat (Z.of_nat k) ltac:(lia)) as E. rewrite Nat2Z.id, SEGS in E. exact E. }
  destruct (mr_model B _ (aa_laws (APIf rc)) _ _ _ _ HM) as (Hh & Hl & _).
  rewrite SEGS.
  eapply (sl_run (g_regs g) (Z_to_bv 64 ENTRY) (g_mem g) (g_md g)); [exact Hh | exact Hl | exact HMI | | |].
  - rewrite sl_mkR_of. unfold ENTRY.
    apply e01_evt with (lo := g_S g - 65536) (p := g_p g) (inp := g_in g).
    + rewrite Esp2. apply sl_stk_norm; [exact HMI | unfold SL_TOP; lia | lia |].
      intros a Ha. rewrite <- SEGS. apply Hstw. rewrite Esp. exact Ha.
    + rewrite Esp2. lia.
    + exact (mem_inv_normalize rsegs (g_mem g)).
    + exact Ep.
    + exact En.
    + unfold g_n in Hn26. lia.
    + unfold g_n in Hpb. lia.
    + exact Hdat'.
  - intros ms (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? &
               m'' & -> & _).
    do 3 eexists. reflexivity.
  - intros R pc' m0' HQ regs' m' Hx Hrel' Hsame.
    destruct HQ as (t0' & t1' & t2' & s0' & s1' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & s3' & s4' & s5' &
                    s6' & s7' & s9' & s10' & s11' & t3' & t4' & t5' & t6' & m'' & HE & E8 & E9 & E10 & E19 & E20 &
                    E21 & E22 & E23 & E25 & E26 & E27 & MU & WM & SC & SB).
    injection HE; intros; subst.
    rewrite Esp2 in MU, SC, SB.
    pose proof (mem_rel_normalize rsegs (g_mem g) HMI) as HR0.
    assert (MU' : Frame.munch [(g_S g - 544, g_S g)] (g_mem g) m')
      by exact (munch_rel rsegs _ (g_mem g) (normalize rsegs (g_mem g)) m' m'' HR0 Hrel' Hsame MU).
    assert (WM' : Frame.wmono rsegs (g_mem g) m')
      by exact (wmono_rel rsegs (g_mem g) (normalize rsegs (g_mem g)) m' m'' HR0 Hrel' Hsame WM).
    assert (Hro' : ro_agree rsegs m') by exact (ro_agree_same rsegs (g_mem g) m' HMI Hsame).
    pose proof (proj2 (bytes_at_rel rsegs m' m'' _ _ Hrel') SB) as SB'.
    assert (SC' : bytes_at rsegs m' (fsp g + 0x30) (le8 (Z_to_bv 64 (g_b4 g * 256)))).
    { replace (fsp g + 0x30) with (g_S g - 544 + 48) by (unfold fsp, SLOT_FRAME; lia).
      exact (proj2 (bytes_at_rel rsegs m' m'' _ _ Hrel') SC). }
    assert (HFR : FR B APIf ra empty g [] (g_L g) (g_A g) regs' m' (g_md g)).
    { apply (sl_fr_of B APIf ra empty FF) with (mem0 := g_mem g).
      - exact HGV.
      - exact HM.
      - exact HW.
      - exact HB.
      - exact HID.
      - exists (m_vmmaps (g_md g)). apply with_vmmaps_self.
      - intros a _ _ _. split; [reflexivity | tauto].
      - intros a _ _ _ _. split; [reflexivity | tauto].
      - intros a k i _ _. reflexivity.
      - intros a k Hin. exact Hin.
      - exact Herr.
      - exact Hsn.
      - exact (resb_start (g_b g) (g_A g) Hres).
      - intros a Ha. apply Hstw. rewrite Esp. unfold SLOT_K, SLOT_STACK in Ha. exact Ha.
      - exact Hrel.
      - apply (sl_unch _ _ _ (g_S g - 65536) (g_S g) MU').
        intros x Hx0 O. destruct (Z_le_dec (g_S g - 544) x); destruct (Z_lt_dec x (g_S g)); try lia;
          exfalso; apply O; cbn [Frame.outside]; (split; [lia | exact I]).
      - exact WM'.
      - exact Hro'.
      - rewrite (sl_getr_eqv _ _ _ Hx).
        transitivity (Z_to_bv 64 (bv_unsigned (YK11.getr (g_regs g) 2) + -544)); [reflexivity|].
        rewrite Esp2. unfold fsp, SLOT_FRAME. f_equal; lia.
      - rewrite (sl_getr_eqv _ _ _ Hx). reflexivity.
      - rewrite (sl_getr_eqv _ _ _ Hx). reflexivity.
      - unfold saved_bytes, SLOT_SAVE. rewrite <- Hra. exact SB'. }
    assert (E1 : YK11.getr regs' 1 = Z_to_bv 64 0x13158) by (rewrite (sl_getr_eqv _ _ _ Hx); reflexivity).
    assert (E10' : YK11.getr regs' 10 = Z_to_bv 64 POD_PROPS) by (rewrite (sl_getr_eqv _ _ _ Hx); reflexivity).
    rewrite <- SEGS.
    apply (b1_malloc_call B APIf ra empty FF g [] (g_L g) (g_A g) regs' m' (g_md g) regs' POD_PROPS);
      [exact HFR | cbn [app]; apply Permutation_refl | cbn; lia | cbn; lia | reflexivity | reflexivity | reflexivity
      | rewrite E1; vm_compute; reflexivity | exact E10' | unfold POD_PROPS; lia |].
    intros L' A' regs'' mem'' md' res HF'' HP'' RP Hres10 Hres0 Hres16 HK HKH.
    rewrite E1. apply H1. exists res, fx, L', A', regs'', mem'', md'.
    split; [reflexivity|]. split; [exact Hfrm|]. split; [exact HF''|]. split; [exact HP''|].
    unfold rg. split; [exact Hres10|]. split; [exact Hres0|]. split; [exact Hres16|].
    split; [e01_rp RP Hx 21|]. split; [e01_rp RP Hx 8|]. split; [e01_rp RP Hx 22|].
    split; [e01_rp RP Hx 25|]. split; [e01_rp RP Hx 26|]. split; [e01_rp RP Hx 23|].
    split.
    { apply (b1_ba_mbyte m' mem'' _ _ SC'). intros i Hi. rewrite length_le8 in Hi.
      apply HK. unfold fsp, SLOT_FRAME. lia. }
    split; [e01_rp RP Hx 27|]. split; [e01_rp RP Hx 20|]. split; [e01_rp RP Hx 19|].
    e01_rp RP Hx 9.
Qed.

End E01.
