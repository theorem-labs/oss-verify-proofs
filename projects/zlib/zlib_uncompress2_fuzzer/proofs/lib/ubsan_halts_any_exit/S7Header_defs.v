(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_halts_any_exit Require Import RunCtx.
From LinuxProcessSemantics.LinuxProcessSem Require State Run.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_halts_any_exit.World Require Import Src_zlib_zlib_uncompress2_fuzzer_repro.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_halts_any_exit Require Import
  PropExec SymExec2 SymExec2Sound SymRun SymDrive SymDriveX S7LibStdioCall.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_halts_any_exit Require Import LiaFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Existing Instance PropExec.fx0.
Import ListNotations. Import SX2. Import SX2S.

#[local] Abbreviation RSEGS := Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments.

Definition STOPSh : list Z :=
  [0x20184; 0x20588; 0x20680; 0x206c4; 0x14d6c; 0x1a9c0; 0x190bc; 0x14b9c; 0x1b58c]%Z.
Definition FUELh : nat := 5000.
Definition scr0 : scripts := SCR [] [] [].
Definition runh {RCa1 : RunCtx}  (scr : scripts) (ss : sym_state) := sym_exec (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb) FUELh true STOPSh scr ss [].
Definition kn_after (r : sym_state * list sidecond * scripts) (kn : list kentry) : list kentry :=
  fst (fst (carry (s_log (fst (fst r))) kn [])).

Definition ENVh (content : list byte) (vals : list word) : env := Env (vals_ev vals) (blobs_ev [content]).

Definition spx (k : Z) : expr := EAlu ALU_ADD (EVar 0) (ELit k).
Definition ax (k : Z) : expr := EAlu ALU_ADD (EVar 2) (ELit k).
Definition gmx (k : Z) : expr := EAlu ALU_ADD (EVar 3) (ELit k).
Definition CW : expr := EVar 9.
Definition SW : expr := EVar 10.
Definition J (i : nat) : expr := EVar (11 + i).

Definition sr_H : list expr :=
  [ELit 0; J 1; spx (-128); ELit 0x10800; ELit 0x72f80; J 5; J 6; J 7;
   ELit 2; gmx 32; J 10; J 11; J 12; J 13; J 14; J 15;
   J 16; J 17; EVar 1; EVar 5; ELit 3; ELit 65536; ELit 0x22e79; ELit 0;
   J 24; J 25; J 26; J 27; J 28; J 29; J 30; J 31].

Definition kn_Hstack : list kentry :=
  [KAlign (EVar 0) 16; KRange (EVar 0) 0x7fff80000000 0x800000000000;
   KWr (SA (EVar 0) (-6144513)) 6144513;
   KWord (SA (EVar 0) (-56)) 8 (ELit 0x18c24);
   KWord (SA (EVar 0) (-64)) 8 (spx 8); KWord (SA (EVar 0) (-72)) 8 (ELit 2);
   KWord (SA (EVar 0) (-80)) 8 (ELit 0x148cc); KWord (SA (EVar 0) (-88)) 8 (spx 32);
   KWord (SA (EVar 0) (-96)) 8 (ELit 0); KWord (SA (EVar 0) (-104)) 8 (ELit 0);
   KWord (SA (EVar 0) (-112)) 8 (ELit 0); KWord (SA (EVar 0) (-120)) 8 (ELit 0)].

Definition area_x : expr := EAlu ALU_AND (ax 24) (ELit 18446744073709547520).

Definition kn_Hheap : list kentry :=
  [KAlign (EVar 2) 4096; KRange (EVar 2) 0x2000 0x7fffff7ff000;
   KAlign (EVar 3) 4096; KRange (EVar 3) 0x94000 0x7fffff7ef000;
   KWr (SA (EVar 3) 0) 69632;
   KDisj (SA (EVar 0) (-6144513)) 6144513 (SA (EVar 3) 0) 69632;
   KDisj (SA (EVar 0) (-6144513)) 6144513 (SA (EVar 2) 0) 4096;
   KDisj (SA (EVar 2) 0) 4096 (SA (EVar 3) 0) 69632;
   KDisj (SA (ELit 0) 0x10000) 0x64120 (SA (EVar 2) 0) 4096;
   KWr (SA (EVar 2) 0) 4096;
   KWord (SA (EVar 2) 0) 8 SW;
   KWord (SA area_x 0) 8 SW; KRange area_x 0x2000 0x7fffff7ff000;
   KDisj (SA (ELit 0) 0x10000) 0x64120 (SA area_x 0) 4096;
   KDisj (SA (EVar 0) (-6144513)) 6144513 (SA area_x 0) 4096;
   KWord (SA (EVar 2) 24) 8 (ax 24); KWord (SA (EVar 2) 32) 8 (ax 24);
   KWord (SA (EVar 2) 40) 8 (EVar 3);
   KWord (SA (EVar 2) 48) 4 (ELit 0); KWord (SA (EVar 2) 52) 4 (ELit 0);
   KWord (SA (EVar 2) 56) 8 (ELit 0x11b18);
   KWord (SA (EVar 3) 0) 8 (ax 24);
   KWord (SA (EVar 3) 28) 1 (ELit 0); KWord (SA (EVar 3) 29) 1 (ELit 160); KWord (SA (EVar 3) 30) 2 (ELit 1);
   KWord (SA (EVar 3) 65568) 1 (ELit 0);
   KWord (SA (EVar 3) 69623) 1 (ELit 0); KWord (SA (EVar 3) 69624) 4 (ELit 0xfdc);
   KZero (SA (EVar 3) 69628) (ELit 4)].

Definition kn_Himage : list kentry :=
  [KWr (SA (ELit 0) 0x22000) 0x52000;
   KImg 0x10000 0x22de0; KImg 0x22de1 0x22e29; KImg 0x32e29 0x72e60;
   KWord (SA (ELit 0) 0x72ec0) 4 (EVar 4); KWord (SA (ELit 0) 0x72ec4) 4 (EVar 8);
   KImg 0x92fc0 0x73218; KWord (SA (ELit 0) 0x73218) 8 CW;
   KImg 0x73239 0x73240; KImg 0x732a8 0x732b0;
   KWord (SA (ELit 0) 0x732b0) 8 SW;
   KWord (SA (ELit 0) 0x732c0) 8 (ELit 0);
   KWord (SA (ELit 0) 0x73460) 8 (ax 24);
   KWord (SA (ELit 0) 0x735e0) 8 (ELit 1);
   KWord (SA (ELit 0) 0x73640) 1 (ELit 1);
   KImg 0x73658 0x74000;
   KRange (EVar 4) 1 4194303].

Definition kn_H : list kentry := kn_Hstack ++ kn_Hheap ++ kn_Himage.
Definition kn_long : list kentry :=
  kn_H ++ [KRange (EVar 5) 6 65535;
           KWord (SA (EVar 3) 32) 1 (EVar 6); KWord (SA (EVar 3) 33) 1 (EVar 7);
           KRange (EVar 6) 0 255; KRange (EVar 7) 0 255].

Definition NXh : nat := 43.


Definition scr_taken : scripts := SCR [true] [] [].

Definition scr_fall : scripts := SCR [false] [] [].
Definition hkA {RCa1 : RunCtx}  := Eval vm_compute in runh scr_fall (SS 0x149c8 sr_H [] kn_long NXh).
Definition srK {RCa1 : RunCtx}  : list expr := Eval vm_compute in s_regs (fst (fst hkA)).
Definition cfglen_x {RCa1 : RunCtx}  : expr := Eval vm_compute in nth 11 srK (ELit 0).


From Stdlib Require Import Lia.

Definition cfgF {RCa1 : RunCtx}  (v6 v7 : word) : word :=
  edenot (Env (fun n => match n with 6%nat => v6 | 7%nat => v7 | _ => Z_to_bv 64 0 end) (blobs_ev []))
         cfglen_x.

Lemma cfglen_x_cfgF {RCa1 : RunCtx}  : forall vals bl,
  edenot (Env (vals_ev vals) (blobs_ev bl)) cfglen_x = cfgF (vals_ev vals 6) (vals_ev vals 7).
Proof. intros. reflexivity. Qed.

Definition zseq (n : nat) : list Z := map Z.of_nat (seq 0 n).

Lemma in_zseq : forall n z, In z (zseq n) <-> (0 <= z < Z.of_nat n)%Z.
Proof.
  intros n z. unfold zseq. rewrite in_map_iff. split.
  - intros (k & <- & Hk). apply in_seq in Hk. lia.
  - intros Hz. exists (Z.to_nat z). split; [lia|]. apply in_seq. lia.
Qed.

Lemma lor_shift8_byte : forall k b, (0 <= k)%Z -> (0 <= b < 256)%Z ->
  Z.lor (k * 256) b = (k * 256 + b)%Z.
Proof.
  intros k b Hk Hb.
  assert (Hand : Z.land (k * 256) b = 0%Z).
  { apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec, Z.bits_0.
    destruct (Z.lt_ge_cases i 8) as [Hi8|Hi8].
    - change 256%Z with (2 ^ 8)%Z. rewrite Z.mul_pow2_bits_low by lia. reflexivity.
    - destruct (Z.eq_dec b 0) as [->|Hb0].
      + rewrite Z.bits_0. apply andb_false_r.
      + rewrite (Z.bits_above_log2 b i); [apply andb_false_r|lia|].
        apply Z.lt_le_trans with 8%Z; [|lia]. apply Z.log2_lt_pow2; [lia|]. change (2 ^ 8)%Z with 256%Z. lia. }
  rewrite <- Z.lxor_lor by exact Hand. symmetry. apply Z.add_nocarry_lxor. exact Hand.
Qed.

Local Ltac cfgF_val_symbolic b0 b1 :=
  unfold cfgF, cfglen_x; cbn [edenot ev eb];
  unfold Sem.alu64, Sem.alu, Sem.mul_div, ext_val, ext_Z;
  rewrite bv_or_unsigned, bv_shiftr_unsigned, bv_and_unsigned, bv_mul_unsigned, !Z_to_bv_unsigned;
  change (Z.land (bv_wrap 64 49) (bv_wrap 64 63)) with 49%Z;
  change (2 ^ (8 * Z.of_nat 0))%Z with 1%Z; change (2 ^ (8 * Z.of_nat 1))%Z with 256%Z;
  change (8 * N.of_nat 1)%N with 8%N;
  rewrite !Z.div_1_r;
  rewrite (bv_wrap_small 64 b0) by (unfold bv_modulus; lia);
  rewrite (bv_wrap_small 64 b1) by (unfold bv_modulus; lia);
  rewrite (Z.mod_small b0 256) by lia; rewrite (Z.mod_small b1 256) by lia;
  change (bv_wrap 64 144115188075855872) with (2 ^ 57)%Z;
  rewrite Z.shiftr_div_pow2 by lia;
  unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus;
  change (2 ^ Z.of_N 8)%Z with 256%Z; change (256 `div` 2)%Z with 128%Z; change (2 ^ Z.of_N 64)%Z with (2 ^ 64)%Z;
  rewrite (Z.mod_small b0 (2 ^ 64)) by lia;
  let Hs := fresh "Hs" in
  destruct (Z.lt_ge_cases b1 128) as [Hs|Hs];
  [ rewrite (Z.mod_small (b1 + 128) 256) by lia;
    replace (b1 + 128 - 128)%Z with b1 by lia;
    rewrite (Z.mod_small b1 (2 ^ 64)) by lia;
    rewrite (Z.mod_small (2 ^ 57 * b1) (2 ^ 64)) by lia;
    replace (2 ^ 57 * b1)%Z with (b1 * 256 * 2 ^ 49)%Z by lia; rewrite Z.div_mul by lia;
    rewrite (Z.mod_small (b0 + 256 * b1) 32768) by lia;
    rewrite lor_shift8_byte by lia; lia
  | replace ((b1 + 128) mod 256)%Z with (b1 + 128 - 256)%Z
      by (apply Z.mod_unique with 1%Z; [left; lia | lia]);
    replace ((b1 + 128 - 256 - 128) mod 2 ^ 64)%Z with (2 ^ 64 + (b1 - 256))%Z
      by (apply Z.mod_unique with (-1)%Z; [left; lia | lia]);
    replace ((2 ^ 57 * (2 ^ 64 + (b1 - 256))) mod 2 ^ 64)%Z with (2 ^ 57 * (b1 - 128))%Z
      by (apply Z.mod_unique with (2 ^ 57 - 1)%Z; [left; lia | lia]);
    replace (2 ^ 57 * (b1 - 128))%Z with ((b1 - 128) * 256 * 2 ^ 49)%Z by lia; rewrite Z.div_mul by lia;
    replace ((b0 + 256 * b1) mod 32768)%Z with (b0 + 256 * b1 - 32768)%Z
      by (apply Z.mod_unique with 1%Z; [left; lia | lia]);
    rewrite lor_shift8_byte by lia; lia ].

Lemma cfgF_val {RCa1 : RunCtx}  : forall b0 b1, (0 <= b0 < 256)%Z -> (0 <= b1 < 256)%Z ->
  cfgF (Z_to_bv 64 b0) (Z_to_bv 64 b1) = Z_to_bv 64 ((b0 + 256 * b1) mod 32768).
Proof.
  intros b0 b1 H0 H1.
  pose proof (Z.mod_pos_bound (b0 + 256 * b1) 32768 ltac:(lia)) as HM.
  apply bv_eq. rewrite (u_small ((b0 + 256 * b1) mod 32768)) by lia.
  first
    [ solve [ cfgF_val_symbolic b0 b1 ]
    |
      idtac "S7Header_defs.cfgF_val: symbolic proof failed, falling back to the 65536-entry native table";
      assert (T : forallb (fun b1 => forallb (fun b0 =>
                Z.eqb (bv_unsigned (cfgF (Z_to_bv 64 b0) (Z_to_bv 64 b1))) ((b0 + 256 * b1) mod 32768))
                (zseq 256)) (zseq 256) = true) by (vm_cast_no_check (@eq_refl bool true));
      rewrite forallb_forall in T;
      specialize (T b1 (proj2 (in_zseq 256 b1) ltac:(cbn; lia))); rewrite forallb_forall in T;
      specialize (T b0 (proj2 (in_zseq 256 b0) ltac:(cbn; lia))); apply Z.eqb_eq in T; exact T ].
Qed.


From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_halts_any_exit Require Import S7TargetPre.
Lemma cfglen_val {RCa1 : RunCtx}  : forall content vals,
  vals_ev vals 6 = Z_to_bv 64 (hdr_b0 content) -> vals_ev vals 7 = Z_to_bv 64 (hdr_b1 content) ->
  edenot (ENVh content vals) cfglen_x = Z_to_bv 64 (hdr_cfglen content).
Proof.
  intros content vals P6 P7. unfold ENVh. rewrite cfglen_x_cfgF, P6, P7.
  pose proof (bv_unsigned_in_range _ (nth 0 content (Z_to_bv 8 0))) as B0.
  pose proof (bv_unsigned_in_range _ (nth 1 content (Z_to_bv 8 0))) as B1.
  change (bv_modulus 8) with 256%Z in B0, B1.
  unfold hdr_cfglen, hdr_cfg. apply cfgF_val; unfold hdr_b0, hdr_b1; lia.
Qed.

Lemma hdr_cfglen_range : forall content, (0 <= hdr_cfglen content < 32768)%Z.
Proof. intros. unfold hdr_cfglen. apply Z.mod_pos_bound. lia. Qed.

Definition sx8F (v7 : word) : word := ext_val true 0 1 v7.
Lemma sx8F_tab :
  forallb (fun b1 => Z.eqb (bv_unsigned (sx8F (Z_to_bv 64 b1)))
                           (if b1 <? 128 then b1 else b1 - 256 + 2 ^ 64)%Z) (zseq 256) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma sx8F_val : forall b1, (0 <= b1 < 256)%Z ->
  sx8F (Z_to_bv 64 b1) = Z_to_bv 64 (if b1 <? 128 then b1 else b1 - 256 + 2 ^ 64)%Z.
Proof.
  intros b1 H1. pose proof sx8F_tab as T. rewrite forallb_forall in T.
  specialize (T b1 (proj2 (in_zseq 256 b1) ltac:(cbn; lia))). apply Z.eqb_eq in T.
  apply bv_eq. rewrite T. symmetry. apply u_small. destruct (b1 <? 128)%Z eqn:Eb; [apply Z.ltb_lt in Eb|apply Z.ltb_ge in Eb]; lia.
Qed.

Lemma mod_eq_shift : forall a b k m, (0 < m)%Z -> (a = b + k * m)%Z -> (a mod m = b mod m)%Z.
Proof. intros a b k m Hm ->. apply Z_mod_plus_full. Qed.
