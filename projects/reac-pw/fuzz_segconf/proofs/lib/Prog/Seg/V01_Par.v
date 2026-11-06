(* The parent loop of the inline m_split in reac-pw/fuzz_segconf LLVMFuzzerTestOneInput (plain, ELF 8dec0b814e6f),
   0x13dec .. 0x13e3c (plain binary; source H:339-344): [v01_par_stmt] of V01_Inv.v.
     0x13dec lbu a5,0(a1)    0x13df0 a3 = (a5 - 0x30) & 0xff  0x13df8 a4 = 11  0x13dfc bltu a3,a4 -> 0x13e34
     0x13e00 a3 = ((a5 & -0x21) - 0x41) & 0xff  0x13e0c a4 = 26  0x13e10 bltu a3,a4 -> 0x13e34
     0x13e14 a4 = (a5 & 0xff) - 0x2d  0x13e1c a3 = 0x32  0x13e20 bltu a3,a4 -> 0x13d74
     0x13e24 ld a3,0x28(sp) (the mask 2^50 + 3)  0x13e28 srl a3,a3,a4  0x13e2c andi a3,a3,1  0x13e30 beqz a3 -> 0x13d74
     0x13e34 a0 -= 1  0x13e38 a1 += 1  0x13e3c bnez a0 -> 0x13dec (else 0x13e40)
   The first test accepts digits and ':', the second letters, the mask bits 0, 1, 50 accept '-', '.', '_'. Each
   branch outcome agrees with SegModel.h_parent_ok of the byte: V01ParPure.byte_fact checks the boolean fact of the
   byte on its 256 values (seq 0 256 by vm_compute, as SegModel.parent_char). The loop goes by induction on the
   characters cs (a0 = k = length cs counts down), exits to 0x13d74 at the first refused one, else at 0x13e40.
   Part of the proof of LLVMFuzzerTestOneInput: this file is part of segment V01 of its walk; no released proof of
   fuzz_segconf's LLVMFuzzerTestOneInput exists. *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib Require Import Img0.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require Import SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require Import seg_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog.Seg Require Import Tac_b1 V01_Inv.
Import ListNotations.
Open Scope Z_scope.

Module V01ParPure.

Lemma byte_lit : forall b : byte, Z_to_bv 8 (bv_unsigned b) = b.
Proof.
  intros b. apply bv_eq. rewrite Z_to_bv_unsigned. apply bv_wrap_small. apply bv_unsigned_in_range.
Qed.

(* A boolean fact of a byte holds when it holds on the 256 values. *)
Lemma byte_all : forall g : byte -> bool,
  forallb (fun k => g (Z_to_bv 8 (Z.of_nat k))) (seq 0 256) = true -> forall b, g b = true.
Proof.
  intros g H b.
  pose proof (bv_unsigned_in_range 8 b) as R. change (bv_modulus 8) with 256 in R.
  assert (Rb : Z.of_nat 0 <= bv_unsigned b < Z.of_nat (0 + 256)).
  { change (Z.of_nat 0) with 0. change (Z.of_nat (0 + 256)) with 256. lia. }
  pose proof (forallb_seq_Z (fun z => g (Z_to_bv 8 z)) 0 256 H (bv_unsigned b) Rb) as E.
  cbv beta in E. rewrite byte_lit in E. exact E.
Qed.

Lemma implb_mp : forall p y, implb p y = true -> p = true -> y = true.
Proof. intros p y H ->. exact H. Qed.

Lemma forallb_zs_cons : forall (P : Z -> bool) (b : byte) cs,
  forallb P (zs (b :: cs)) = P (bv_unsigned b) && forallb P (zs cs).
Proof. reflexivity. Qed.

(* A goal [c = true], c a boolean of the byte b and literals only: byte_all, checked by vm_compute. *)
Ltac byte_fact b :=
  lazymatch goal with
  | |- ?c = true =>
      let g := eval pattern b in c in
      lazymatch g with
      | ?f b => refine (byte_all f _ b); vm_compute; reflexivity
      end
  end.

(* The tested boolean of a branch hypothesis K : c = v (if_cases). *)
Ltac kcond K := lazymatch type of K with ?c = _ => c end.

End V01ParPure.

Import V01ParPure.

(* The character at ptr, for the lbu at 0x13dec. *)
Lemma par_rd1 : forall m ptr b cs, bytes_at rsegs m ptr (b :: cs) ->
  ov_read_bytes rsegs m (wa (ptr + Z.of_nat 0)) 1 = Some [b].
Proof.
  intros m ptr b cs H.
  rewrite (bytes_at_ov_read rsegs m ptr _ 0 1 H) by (cbn [length Nat.add]; apply le_n_S, Nat.le_0_l).
  reflexivity.
Qed.

Lemma par_tail : forall m ptr b cs, bytes_at rsegs m ptr (b :: cs) -> bytes_at rsegs m (ptr + 1) cs.
Proof.
  intros m ptr b cs H. change (b :: cs) with ([b] ++ cs) in H. apply bytes_at_app in H as [_ H]. exact H.
Qed.

Lemma v01_par : v01_par_stmt.
Proof.
  unfold v01_par_stmt.
  intros Q m cs. induction cs as [|b cs IH];
    intros k ptr spv ra gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc
      Hk Hk1 Hptr Hspv HB HM KJ KE.
  { cbn in Hk. lia. }
  pose proof (bytes_at_bound _ _ _ _ HB) as HBb. cbn [length] in HBb, Hk.
  rewrite Nat2Z.inj_succ in HBb, Hk. unfold Z.succ in HBb, Hk.
  pose proof (par_rd1 m ptr b cs HB) as RD1.
  pose proof (par_tail m ptr b cs HB) as HB1.
  pose proof (b1_ld8 m (spv + 0x28) _ HM) as RD8.
  rewrite forallb_zs_cons in KJ, KE.
  (* 0x13e34 .. 0x13e3c, once the character b is accepted *)
  assert (ACC : h_parent_ok (bv_unsigned b) = true -> forall x3 x4 x5 : word,
    evt rsegs Q (vst 0x13e34 ra (Z_to_bv 64 spv) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 k) (Z_to_bv 64 ptr) a2 x3 x4 x5
                   a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m)).
  { intros HP x3 x4 x5. rewrite HP in KJ, KE. cbn [andb] in KJ, KE. unfold vst.
    zstep. zstep. zstep.
    if_cases K; cbv iota; zify_cond K.
    - assert (Hk2 : 1 <= k + -1) by (Z.div_mod_to_equations; lia).
      eapply IH; [lia | exact Hk2 | lia | exact Hspv | exact HB1 | exact HM | exact KJ | exact KE].
    - assert (Hk2 : k = 1) by (Z.div_mod_to_equations; lia).
      destruct cs as [|b' cs]; [|cbn [length] in Hk; rewrite Nat2Z.inj_succ in Hk; unfold Z.succ in Hk; lia].
      apply KE. reflexivity. }
  unfold vst in KJ, KE |- *.
  (* 0x13dec lbu a5,0(a1); 0x13df0 addi a3,a5,-0x30; 0x13df4 andi a3,a3,0xff; 0x13df8 li a4,11; 0x13dfc bltu *)
  zstep. zstep. zstep. zstep. zstep.
  if_cases K1; cbv iota.
  { eapply ACC. refine (implb_mp _ _ _ K1). byte_fact b. }
  (* 0x13e00 andi a3,a5,-0x21; 0x13e04 addi a3,a3,-0x41; 0x13e08 andi a3,a3,0xff; 0x13e0c li a4,26; 0x13e10 bltu *)
  zstep. zstep. zstep. zstep. zstep.
  if_cases K2; cbv iota.
  { eapply ACC.
    let c1 := kcond K1 in let c2 := kcond K2 in
    refine (implb_mp (negb c1 && c2) _ _ ltac:(rewrite K1, K2; reflexivity)).
    byte_fact b. }
  (* 0x13e14 andi a3,a5,0xff; 0x13e18 addi a4,a3,-0x2d; 0x13e1c li a3,0x32; 0x13e20 bltu a3,a4 *)
  zstep. zstep. zstep. zstep.
  if_cases K3; cbv iota.
  { assert (HF : h_parent_ok (bv_unsigned b) = false).
    { apply (proj1 (Bool.negb_true_iff _)).
      let c1 := kcond K1 in let c2 := kcond K2 in let c3 := kcond K3 in
      refine (implb_mp (negb c1 && negb c2 && c3) _ _ ltac:(rewrite K1, K2, K3; reflexivity)).
      byte_fact b. }
    apply KJ. rewrite HF. reflexivity. }
  (* 0x13e24 ld a3,0x28(sp); 0x13e28 srl a3,a3,a4; 0x13e2c andi a3,a3,1; 0x13e30 beqz a3 *)
  zstep. zstep. zstep. zstep.
  if_cases K4; cbv iota.
  { assert (HF : h_parent_ok (bv_unsigned b) = false).
    { apply (proj1 (Bool.negb_true_iff _)).
      let c1 := kcond K1 in let c2 := kcond K2 in let c3 := kcond K3 in let c4 := kcond K4 in
      refine (implb_mp (negb c1 && negb c2 && negb c3 && c4) _ _ ltac:(rewrite K1, K2, K3, K4; reflexivity)).
      byte_fact b. }
    apply KJ. rewrite HF. reflexivity. }
  { eapply ACC.
    let c1 := kcond K1 in let c2 := kcond K2 in let c3 := kcond K3 in let c4 := kcond K4 in
    refine (implb_mp (negb c1 && negb c2 && negb c3 && negb c4) _ _ ltac:(rewrite K1, K2, K3, K4; reflexivity)).
    byte_fact b. }
Qed.
