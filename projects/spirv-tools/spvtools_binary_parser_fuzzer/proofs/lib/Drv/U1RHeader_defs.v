(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.spirv_tools.spvtools_binary_parser_fuzzer.images Require Import Ubsan.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import PropExec SymExec2 SymExec2Sound SymRun SymDrive SymDriveX.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.Drv Require Import U1LibStdioCall U1Cells U1KnCells U1RKn U1KnIvs.
Require LinuxProcessSemantics.Riscv.Sem.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations. Import SX2. Import SX2S.

Abbreviation RSEGS := Ubsan.M.loaded_segments.

Section FXALL1.
Context {fx : FPState}.

Definition STOPSh : list Z :=
  [0xe2b9c; 0xe311c; 0xe36f0; 0xe2aa0; 0x12a64; 0x12bf0; 0xd56bc; 0xd1e54; 0x65b0c; 0xd70d4; 0xd3cf8]%Z.
Definition FUELh : nat := 5000.
Definition scr0 : scripts := SCR [] [] [].
Definition runh (scr : scripts) (ss : sym_state) := sym_exec RSEGS FUELh true STOPSh scr ss [].
Definition kn_after (r : sym_state * list sidecond * scripts) (kn : list kentry) : list kentry :=
  fst (fst (carry (s_log (fst (fst r))) kn [])).

Definition ENVh (content : list byte) (vals : list word) : env := Env (vals_ev vals) (blobs_ev [content]).

Definition spx (k : Z) : expr := EAlu ALU_ADD (EVar 0) (ELit k).
Definition ax (k : Z) : expr := EAlu ALU_ADD (EVar 2) (ELit k).
Definition gmx (k : Z) : expr := EAlu ALU_ADD (EVar 3) (ELit k).
Definition J (i : nat) : expr := EVar (9 + i).

Definition sr_H : list expr :=
  [ELit 0; J 1; spx (-128); ELit 0x10800; ELit 0x102418; J 5; J 6; J 7;
   ELit 2; EVar 3; J 10; J 11; J 12; J 13; J 14; J 15;
   J 16; J 17; EVar 1; EVar 5; ELit 3; EVar 2; ELit 0xf0249; J 23;
   J 24; J 25; J 26; J 27; J 28; J 29; J 30; J 31].

Definition kn_Hstack : list kentry :=
  [KAlign (EVar 0) 16; KRange (EVar 0) 0x7fff80000000 0x800000000000;
   KWr (SA (EVar 0) (-8388608)) 8388608;
   KWord (SA (EVar 0) (-56)) 8 (ELit 0xd1808);
   KWord (SA (EVar 0) (-64)) 8 (spx 8); KWord (SA (EVar 0) (-72)) 8 (ELit 2);
   KWord (SA (EVar 0) (-80)) 8 (ELit 0x6583c); KWord (SA (EVar 0) (-88)) 8 (spx 32);
   KWord (SA (EVar 0) (-96)) 8 (ELit 0); KWord (SA (EVar 0) (-104)) 8 (ELit 0);
   KWord (SA (EVar 0) (-112)) 8 (ELit 0); KWord (SA (EVar 0) (-120)) 8 (ELit 0)].

Definition kn_Hbuf : list kentry :=
  [KRange (EVar 3) 0x124000 0x7fffff800000; KRange (EVar 2) 65536 67108864].

Definition kn_Himage : list kentry :=
  [KWr (SA (ELit 0) 0xef000) 0x35000;
   KWord (SA (ELit 0) 0x102370) 4 (EVar 4);
   KWord (SA (ELit 0) 0x102350) 8 (ELit 0x102350);
   KWord (SA (ELit 0) 0x122688) 8 (EVar 8);
   KWord (SA (ELit 0) 0x1226d8) 8 (ELit 4096);
   KWord (SA (ELit 0) 0x1226ab) 1 (ELit 0);
   KRange (EVar 4) 1 4194303].

Definition kn_H : list kentry := kn_Hstack ++ kn_Hbuf ++ kn_Himage ++ kn_ivs ++ kn_drv_cells.

Definition kn_short : list kentry := kn_H ++ [KRange (EVar 5) 0 5].

Definition kn_long : list kentry :=
  kn_H ++ [KRange (EVar 5) 6 67108863;
           KWord (SA (EVar 3) 0) 1 (EVar 6); KWord (SA (EVar 3) 1) 1 (EVar 7);
           KRange (EVar 6) 0 255; KRange (EVar 7) 0 255].

Definition NXh : nat := 41.

Definition hsA := Eval vm_compute in runh scr0 (SS 0x65938 sr_H [] kn_short NXh).
Definition srSA : list expr := Eval vm_compute in s_regs (fst (fst hsA)).
Definition knSA : list kentry := Eval vm_compute in kn_after hsA kn_short.

Definition scS : stdio_res := Eval vm_compute in
  match stdio_call NXh srSA knSA with Some r => r | None => SCR_ 0 0 0 (ELit 0) (ELit 0) (ELit 0) (ELit 0) (ELit 0) (ELit 0) (ELit 0) [] [] end.
Definition NXh2 : nat := 73.
Definition srSB0 : list expr := Eval vm_compute in sc_sr scS.
Definition knSB0 : list kentry := Eval vm_compute in sc_kn scS.
Definition hsB := Eval vm_compute in runh scr0 (SS (sc_ret scS) srSB0 [] knSB0 NXh2).
Definition srSB : list expr := Eval vm_compute in s_regs (fst (fst hsB)).
Definition knSB : list kentry := Eval vm_compute in kn_after hsB knSB0.

Definition scr_taken : scripts := SCR [true] [] [].
Definition hoA := Eval vm_compute in runh scr_taken (SS 0x65938 sr_H [] kn_long NXh).
Definition srOA : list expr := Eval vm_compute in s_regs (fst (fst hoA)).
Definition knOA : list kentry := Eval vm_compute in kn_after hoA kn_long.
Definition scO : stdio_res := Eval vm_compute in
  match stdio_call NXh srOA knOA with Some r => r | None => SCR_ 0 0 0 (ELit 0) (ELit 0) (ELit 0) (ELit 0) (ELit 0) (ELit 0) (ELit 0) [] [] end.
Definition srOB0 : list expr := Eval vm_compute in sc_sr scO.
Definition knOB0 : list kentry := Eval vm_compute in sc_kn scO.
Definition hoB := Eval vm_compute in runh scr0 (SS (sc_ret scO) srOB0 [] knOB0 NXh2).
Definition srOB : list expr := Eval vm_compute in s_regs (fst (fst hoB)).
Definition knOB : list kentry := Eval vm_compute in kn_after hoB knOB0.

Definition scr_fall : scripts := SCR [false] [] [].
Definition hkA := Eval vm_compute in runh scr_fall (SS 0x65938 sr_H [] kn_long NXh).
Definition srK : list expr := Eval vm_compute in s_regs (fst (fst hkA)).

Definition cfglen_x : expr := Eval vm_compute in nth 11 srK (ELit 0).

Definition cfglen_v : expr := EVar 45.
Definition srT : list expr := Eval vm_compute in map (esub cfglen_x cfglen_v) srK.
Definition knT : list kentry := kn_long.

From Stdlib Require Import Lia.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.

Definition cfgF (v6 v7 : word) : word :=
  edenot (Env (fun n => match n with 6%nat => v6 | 7%nat => v7 | _ => Z_to_bv 64 0 end) (blobs_ev []))
         cfglen_x.

Lemma cfglen_x_cfgF : forall vals bl,
  edenot (Env (vals_ev vals) (blobs_ev bl)) cfglen_x = cfgF (vals_ev vals 6) (vals_ev vals 7).
Proof. intros. reflexivity. Qed.

Definition zseq (n : nat) : list Z := map Z.of_nat (seq 0 n).

Lemma in_zseq : forall n z, In z (zseq n) <-> (0 <= z < Z.of_nat n)%Z.
Proof.
  intros n z. unfold zseq. rewrite in_map_iff. split.
  - intros (k & <- & Hk). apply in_seq in Hk. lia.
  - intros Hz. exists (Z.to_nat z). split; [lia|]. apply in_seq. lia.
Qed.

Definition cfg_hi (b1 : Z) : word :=
  LinuxProcessSemantics.Riscv.Sem.alu64 ALU_SRL
    (LinuxProcessSemantics.Riscv.Sem.mul_div M_MUL (Z_to_bv 64 (2^57)) (ext_val true 0 1 (Z_to_bv 64 b1))) (Z_to_bv 64 49).
Lemma cfg_hi_tab : forallb (fun b1 => Z.eqb (bv_unsigned (cfg_hi b1)) ((b1 mod 128) * 256)) (zseq 256) = true.
Proof. vm_compute. reflexivity. Qed.

Lemma cfgF_split b0 b1 :
  cfgF (Z_to_bv 64 b0) (Z_to_bv 64 b1) = LinuxProcessSemantics.Riscv.Sem.alu64 ALU_OR (cfg_hi b1) (ext_val false 0 1 (Z_to_bv 64 b0)).
Proof. reflexivity. Qed.

Lemma lor_low8 k b : (0 <= k)%Z -> (0 <= b < 256)%Z -> Z.lor (k * 256) b = (k * 256 + b)%Z.
Proof.
  intros Hk Hb.
  assert (L : Z.land (k * 256) b = 0%Z).
  { apply Z.bits_inj_0. intros i. rewrite Z.land_spec.
    destruct (Z.lt_ge_cases i 0) as [Hi|Hi]; [now rewrite Z.testbit_neg_r by lia|].
    destruct (Z.lt_ge_cases i 8) as [Hi8|Hi8].
    - replace (k * 256)%Z with (Z.shiftl k 8) by (rewrite Z.shiftl_mul_pow2 by lia; reflexivity).
      rewrite Z.shiftl_spec_low by lia. reflexivity.
    - replace b with (b mod 2^8)%Z by (apply Z.mod_small; lia).
      rewrite Z.mod_pow2_bits_high by lia. apply andb_false_r. }
  rewrite <- Z.lxor_lor by exact L. rewrite <- Z.add_nocarry_lxor by exact L. reflexivity.
Qed.

Lemma cfgF_val : forall b0 b1, (0 <= b0 < 256)%Z -> (0 <= b1 < 256)%Z ->
  cfgF (Z_to_bv 64 b0) (Z_to_bv 64 b1) = Z_to_bv 64 ((b0 + 256 * b1) mod 32768).
Proof.
  intros b0 b1 H0 H1. rewrite cfgF_split.
  pose proof cfg_hi_tab as T. rewrite forallb_forall in T.
  specialize (T b1 (proj2 (in_zseq 256 b1) ltac:(cbn; lia))). apply Z.eqb_eq in T.
  pose proof (Z.mod_pos_bound b1 128 ltac:(lia)) as R. pose proof (Z.div_mod b1 128 ltac:(lia)) as DM.
  apply bv_eq. unfold LinuxProcessSemantics.Riscv.Sem.alu64, LinuxProcessSemantics.Riscv.Sem.alu.
  rewrite bv_or_unsigned, T.
  unfold ext_val, ext_Z. rewrite (u_small b0) by lia. change (2 ^ (8 * Z.of_nat 0))%Z with 1%Z. rewrite Z.div_1_r.
  change (2 ^ (8 * Z.of_nat 1))%Z with 256%Z. rewrite (Z.mod_small b0 256) by lia.
  rewrite (u_small b0) by lia.
  rewrite u_small by (pose proof (Z.mod_pos_bound (b0 + 256 * b1) 32768 ltac:(lia)); lia).
  rewrite lor_low8 by lia.
  apply (Z.mod_unique (b0 + 256 * b1) 32768 (b1 / 128)); lia.
Qed.

Lemma cfglen_val : forall content vals,
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

End FXALL1.
