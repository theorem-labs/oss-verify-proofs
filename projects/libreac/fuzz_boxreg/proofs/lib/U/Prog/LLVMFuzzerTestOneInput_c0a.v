From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.U.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.U.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.U.Reusable Require Import YL01 YL00 YL0g YI06 YI16 YI14.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.U.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.U Require Import Contract Img0.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Lib Require Import PropExec MState Mem Exec Frame Step Cells Tac Bytes ZBridge Image.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Lib Require Regs6ss RegisterBridge.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.U.Spec Require Import StrFun.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.U.Prog Require Import Boxreg BoxregRd.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.U.Prog Require Import
  LLVMFuzzerTestOneInput_c LLVMFuzzerTestOneInput_fr LLVMFuzzerTestOneInput_inv LLVMFuzzerTestOneInput_top
  LLVMFuzzerTestOneInput_seg.
Import ListNotations.
Open Scope Z_scope.

Definition c0_nch (pl : list byte) : Z := match pl with [] => 0 | x :: _ => bv_unsigned x end.
Definition c0_bu (pl : list byte) : Z := match pl with _ :: y :: _ => bv_unsigned y | _ => 0 end.
Definition c0_base (pl : list byte) : Z := match pl with _ :: y :: _ => bv_signed y | _ => 0 end.
Definition c0_used (pl : list byte) : Z := Z.min (Z.of_nat (length pl)) 2.

Lemma c0_rd1 : forall m a b l, bytes_at rsegs m a (b :: l) -> ov_read_bytes rsegs m (wa a) 1 = Some [b].
Proof.
  intros m a b l H. pose proof (bytes_at_read rsegs m a (b :: l) 0 1 H ltac:(lia) ltac:(cbn; lia)) as E.
  rewrite Z.add_0_r in E. exact E.
Qed.

Lemma c0_ne0 : forall z, 0 < z < 2 ^ 64 -> bv_eqb (Z_to_bv 64 z) (Z_to_bv 64 0) = false.
Proof. intros z Hz. rewrite eqb_lit by lia. apply Z.eqb_neq. lia. Qed.

Lemma c0_byte_signed : forall b : byte,
  (bv_signed b = bv_unsigned b /\ bv_unsigned b < 128) \/ (bv_signed b = bv_unsigned b - 256 /\ 128 <= bv_unsigned b).
Proof.
  intros b. pose proof (bv_unsigned_in_range 8 b) as R. change (bv_modulus 8) with 256 in R.
  unfold bv_signed, bv_swrap, bv_wrap, bv_half_modulus, bv_modulus. change (2 ^ Z.of_N 8) with 256.
  change (256 / 2) with 128.
  destruct (Z.ltb_spec (bv_unsigned b) 128); [left | right]; (split; [|lia]); Z.div_mod_to_equations; lia.
Qed.

Lemma c0_sl : forall b : byte, Z_to_bv 64 (Z.shiftl (bv_unsigned (zxb b)) 56) = Z_to_bv 64 (bv_signed b * 2 ^ 56).
Proof.
  intros b. pose proof (bv_unsigned_in_range 8 b) as R. change (bv_modulus 8) with 256 in R.
  unfold zxb. rewrite unsigned_lit by lia. rewrite Z.shiftl_mul_pow2 by lia. apply Z_to_bv_eqm.
  change (2 ^ 56) with 72057594037927936. change (2 ^ 64) with 18446744073709551616.
  destruct (c0_byte_signed b) as [[-> _] | [-> _]]; [reflexivity|].
  Z.div_mod_to_equations. lia.
Qed.

Lemma c0_sr : forall b : byte,
  Z_to_bv 64 (Z.shiftr (bv_signed (Z_to_bv 64 (Z.shiftl (bv_unsigned (zxb b)) 56))) 56) = Z_to_bv 64 (bv_signed b).
Proof.
  intros b. rewrite c0_sl. pose proof (bv_unsigned_in_range 8 b) as R. change (bv_modulus 8) with 256 in R.
  assert (Hs : -128 <= bv_signed b < 128) by (destruct (c0_byte_signed b) as [[E H] | [E H]]; rewrite E; lia).
  rewrite signed_lit by (change (2 ^ 56) with 72057594037927936; change (2 ^ 63) with 9223372036854775808; lia).
  rewrite Z.shiftr_div_pow2 by lia. rewrite Z.div_mul by (apply Z.pow_nonzero; lia). reflexivity.
Qed.

Lemma c0_rw2 : forall m A x y x' y', rw_cells rsegs m A [C8 x; C8 y] -> x = x' -> y = y' ->
  rw_cells rsegs m A [C8 x'; C8 y'].
Proof. intros m A x y x' y' H -> ->. exact H. Qed.

Ltac c0_weq :=
  match goal with |- Z_to_bv 64 ?a = Z_to_bv 64 ?b => replace a with b by first [ lia | (simpl; lia) | (rewrite skipn_O; lia) ]; reflexivity end.

Ltac c0_if := first [ if_true | if_false | c1_if ].

Ltac c0_rdstep :=
  match goal with
  | |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      match goal with
      | H : bytes_at rsegs mm ?a (?b :: ?l) |- _ => let RR := fresh "RR" in pose proof (c0_rd1 mm a b l H) as RR; step
      end
  end.

Ltac c0_go stop :=
  repeat (lazymatch goal with
          | |- evt _ _ (MS _ _ (Z_to_bv 64 ?pc) _ _ _ _) =>
              tryif constr_eq pc stop then fail else first [ step | c0_rdstep ]
          end; try c0_if).

Lemma llvm_c0_evt1 :
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (ip : Z) (pl : list byte),
    0 <= ip -> ip + 1 + Z.of_nat (length pl) <= bv_unsigned sp -> bv_unsigned sp + 360 <= 2 ^ 64 ->
    bytes_at rsegs m (ip + 1) pl ->
    rw_cells rsegs m (bv_unsigned sp + 344) [C8 (Z_to_bv 64 (ip + 1)); C8 (Z_to_bv 64 (Z.of_nat (length pl)))] ->
    mem_inv rsegs m ->
    evt rsegs
      (fun ms' => exists (a1' : word) (m' : word -> option byte),
         ms' = MS (mkR (Z_to_bv 64 0x12f5c) sp gp tp t0 t1 t2 s0 s1
                       (Z_to_bv 64 (bv_unsigned sp + 344)) a1' a2 a3 a4 a5 a6 a7
                       (Z_to_bv 64 (c0_bu pl)) (Z_to_bv 64 (c0_nch pl)) (Z_to_bv 64 (c0_base pl))
                       (Z_to_bv 64 (Z.of_nat (length pl))) (Z_to_bv 64 (c0_base pl * 2 ^ 56))
                       s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (Z_to_bv 64 0x13764) fc None m' (seg_rom rsegs) /\
         munch [(bv_unsigned sp + 344, bv_unsigned sp + 360)] m m' /\ wmono rsegs m m' /\ mem_inv rsegs m' /\
         rw_cells rsegs m' (bv_unsigned sp + 344)
           [C8 (Z_to_bv 64 (ip + 1 + c0_used pl)); C8 (Z_to_bv 64 (Z.of_nat (length (skipn 2 pl))))])
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
               (Z_to_bv 64 (1 + Z.of_nat (length pl))) (Z_to_bv 64 (ip + 1)) (Z_to_bv 64 ip)
               (Z_to_bv 64 (Z.of_nat (length pl))) (Z_to_bv 64 1) s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x12df4) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m ip pl Hip Hsp Htop HB CW MI.
  pose proof (munch_refl [(bv_unsigned sp + 344, bv_unsigned sp + 360)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  pose proof (bv_unsigned_in_range 64 sp) as Rsp. unfold bv_modulus in Rsp. change (2 ^ Z.of_N 64) with (2 ^ 64) in Rsp.
  destruct pl as [|v1 [|v2 rest]].
  - change (Z.of_nat (length [])) with 0 in *. change (c0_used []) with 0.
    change (Z.of_nat (length (skipn 2 []))) with 0. cbn [c0_base c0_nch c0_bu] in *. rewrite Z.add_0_r.
    c0_go 0x13764.
    finish.
  - change (Z.of_nat (length [v1])) with 1 in *. change (c0_used [v1]) with 1.
    change (Z.of_nat (length (skipn 2 [v1]))) with 0. cbn [c0_base c0_nch c0_bu] in *.
    c0_go 0x13764.
    finish.
  - cbn [c0_base c0_nch c0_bu skipn] in *.
    replace (c0_used (v1 :: v2 :: rest)) with 2 by (unfold c0_used; cbn [length]; lia).
    apply (proj1 (bytes_at_app rsegs m (ip + 1) [v1] (v2 :: rest))) in HB. destruct HB as [HB1 HB2].
    cbn [length] in HB2. change (Z.of_nat 1) with 1 in HB2.
    replace (Z.of_nat (length (v1 :: v2 :: rest))) with (2 + Z.of_nat (length rest)) in * by (cbn [length]; lia).
    c0_go 0x13764. rewrite c0_sr, c0_sl.
    finish.
    eapply c0_rw2; [exact CW | c0_weq | c0_weq].
Qed.
