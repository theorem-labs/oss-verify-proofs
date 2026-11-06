(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.coturn.FuzzStunClient.images Require Import Ubsan.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require Import PropExec.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib Require Import SymExec2 SymExec2Sound SymRun SymDrive SymDriveX UbLibStdioCall.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require Import WalkFastL.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require Import WalkFast.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require Import WalkFastK.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require Import WalkFastM.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib Require Import SumWalkFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Ltac OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common.WalkTac.gres ::= gres_fast.
#[local] Ltac OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common.WalkTac.vnorm ::= vnorm_fast.
#[local] Ltac OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common.StepTac.step_simpl ::= step_simpl_fast.
#[local] Ltac OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common.RefMemcpyLib.not_kept ::= not_kept_fast.
#[local] Ltac OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common.StoreOk.store_ok_peel ::= store_ok_peel_fast.
#[local] Ltac OSSVerify.Proofs.coturn.FuzzStunClient.lib.SumWalkTac.rdn_peel1 ::= rdn_peel1_fast.
(* [comment removed for export] *)
#[local] Existing Instance PropExec.fx0.  (* [comment removed for export] *)
Import ListNotations. Import SX2. Import SX2S.

#[local] Abbreviation RSEGS := Ubsan.M.loaded_segments.

(* [comment removed for export] *)
Definition STOPSh : list Z :=
  [0x23ae8; 0x23eec; 0x241e4; 0x239ec; 0x12a64; 0x12bf0; 0x1d81c; 0x1bfa0; 0x13d90; 0x1e3d0]%Z.
Definition FUELh : nat := 5000.
Definition scr0 : scripts := SCR [] [] [].
Definition runh (scr : scripts) (ss : sym_state) := sym_exec RSEGS FUELh true STOPSh scr ss [].
Definition kn_after (r : sym_state * list sidecond * scripts) (kn : list kentry) : list kentry :=
  fst (fst (carry (s_log (fst (fst r))) kn [])).

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition ENVh (content : list byte) (vals : list word) : env := Env (vals_ev vals) (blobs_ev [content]).

Definition spx (k : Z) : expr := EAlu ALU_ADD (EVar 0) (ELit k).
Definition ax (k : Z) : expr := EAlu ALU_ADD (EVar 2) (ELit k).
Definition gmx (k : Z) : expr := EAlu ALU_ADD (EVar 3) (ELit k).
Definition J (i : nat) : expr := EVar (9 + i).

(* [comment removed for export] *)
Definition sr_H : list expr :=
  [ELit 0; J 1; spx (-128); ELit 0x10800; ELit 0x36c60; J 5; J 6; J 7;
   ELit 2; gmx 32; J 10; J 11; J 12; J 13; J 14; J 15;
   J 16; J 17; EVar 1; EVar 5; ELit 3; ELit 65536; ELit 0x26b39; ELit 0;
   J 24; J 25; J 26; J 27; J 28; J 29; J 30; J 31].
Definition CANv : expr := EVar 41.
Definition SECv : expr := EVar 42.

(* [comment removed for export] *)
Definition kn_Hstack : list kentry :=
  [KAlign (EVar 0) 16; KRange (EVar 0) 0x7fff80000000 0x800000000000;
   KWr (SA (EVar 0) (-8388608)) 8388608;
   KWord (SA (EVar 0) (-56)) 8 (ELit 0x1ba3c);
   KWord (SA (EVar 0) (-64)) 8 (spx 8); KWord (SA (EVar 0) (-72)) 8 (ELit 2);
   KWord (SA (EVar 0) (-80)) 8 (ELit 0x13ac0); KWord (SA (EVar 0) (-88)) 8 (spx 32);
   KWord (SA (EVar 0) (-96)) 8 (ELit 0); KWord (SA (EVar 0) (-104)) 8 (ELit 0);
   KWord (SA (EVar 0) (-112)) 8 (ELit 0); KWord (SA (EVar 0) (-120)) 8 (ELit 0)].

(* [comment removed for export] *)
Definition area_x : expr := EAlu ALU_AND (ax 24) (ELit 18446744073709547520).

(* [comment removed for export] *)
Definition kn_Hheap : list kentry :=
  [KAlign (EVar 2) 4096; KRange (EVar 2) 0x2000 0x7fffff7ff000;
   KAlign (EVar 3) 4096; KRange (EVar 3) 0x58000 0x7fffff7ef000;
   KWr (SA (EVar 3) 0) 69632;
   KDisj (SA (EVar 0) (-8388608)) 0x80800000 (SA (EVar 3) 0) 69632;
   KDisj (SA (EVar 0) (-8388608)) 0x80800000 (SA (EVar 2) 0) 4096;
   KDisj (SA (EVar 2) 0) 4096 (SA (EVar 3) 0) 69632;
   (* [comment removed for export] *)
   KDisj (SA (ELit 0) 0x10000) 0x48000 (SA (EVar 2) 0) 4096;
   KWr (SA (EVar 2) 0) 4096;
   KWord (SA (EVar 2) 0) 8 SECv;
   KWord (SA area_x 0) 8 SECv; KRange area_x 0x2000 0x7fffff7ff000;
   KDisj (SA (ELit 0) 0x10000) 0x48000 (SA area_x 0) 4096;
   KDisj (SA (EVar 0) (-8388608)) 0x80800000 (SA area_x 0) 4096;
   KWord (SA (EVar 2) 24) 8 (ax 24); KWord (SA (EVar 2) 32) 8 (ax 24);
   KWord (SA (EVar 2) 40) 8 (EVar 3);
   KWord (SA (EVar 2) 48) 4 (ELit 0); KWord (SA (EVar 2) 52) 4 (ELit 0);
   KWord (SA (EVar 2) 56) 8 (ELit 0x11b20);
   KWord (SA (EVar 3) 0) 8 (ax 24);
   KWord (SA (EVar 3) 28) 1 (ELit 0); KWord (SA (EVar 3) 29) 1 (ELit 160); KWord (SA (EVar 3) 30) 2 (ELit 1);
   KWord (SA (EVar 3) 65568) 1 (ELit 0);
   KWord (SA (EVar 3) 69623) 1 (ELit 0); KWord (SA (EVar 3) 69624) 4 (ELit 0xfdc);
   KZero (SA (EVar 3) 69628) (ELit 4)].

(* [comment removed for export] *)
Definition kn_Himage : list kentry :=
  [KWr (SA (ELit 0) 0x26000) 0x32000;
   KImg 0x10000 0x26af0; KImg 0x26af1 0x26b39; KImg 0x36b39 0x36b90;
   KWord (SA (ELit 0) 0x36bb8) 4 (EVar 4); KWord (SA (ELit 0) 0x36bbc) 4 (EVar 8);
   KImg 0x36c78 0x36ce8; KImg 0x56ca8 0x56ed0; KWord (SA (ELit 0) 0x56ca0) 8 CANv;
   KImg 0x56ee9 0x56ef0; KImg 0x56f58 0x56f60;
   KWord (SA (ELit 0) 0x56f60) 8 SECv;
   KWord (SA (ELit 0) 0x56f70) 8 (ELit 0);
   KWord (SA (ELit 0) 0x57110) 8 (ax 24);
   KWord (SA (ELit 0) 0x57290) 8 (ELit 1);
   KWord (SA (ELit 0) 0x572f0) 1 (ELit 1);
   KImg 0x57308 0x58000;
   KRange (EVar 4) 1 4194303].

Definition kn_H : list kentry := kn_Hstack ++ kn_Hheap ++ kn_Himage.
(* [comment removed for export] *)
Definition kn_short : list kentry := kn_H ++ [KRange (EVar 5) 0 5].
(* [comment removed for export] *)
Definition kn_long : list kentry :=
  kn_H ++ [KRange (EVar 5) 6 65535;
           KWord (SA (EVar 3) 32) 1 (EVar 6); KWord (SA (EVar 3) 33) 1 (EVar 7);
           KRange (EVar 6) 0 255; KRange (EVar 7) 0 255].

Definition NXh : nat := 43.

(* [comment removed for export] *)
Definition hsA := Eval vm_compute in runh scr0 (SS 0x13bbc sr_H [] kn_short NXh).
Definition srSA : list expr := Eval vm_compute in s_regs (fst (fst hsA)).
Definition knSA : list kentry := Eval vm_compute in kn_after hsA kn_short.
(* [comment removed for export] *)
Definition scS : stdio_res := Eval vm_compute in
  match stdio_call NXh srSA knSA with Some r => r | None => SCR_ 0 0 0 (ELit 0) (ELit 0) (ELit 0) (ELit 0) (ELit 0) (ELit 0) (ELit 0) [] [] end.
Definition NXh2 : nat := 75.
Definition srSB0 : list expr := Eval vm_compute in sc_sr scS.
Definition knSB0 : list kentry := Eval vm_compute in sc_kn scS.
Definition hsB := Eval vm_compute in runh scr0 (SS (sc_ret scS) srSB0 [] knSB0 NXh2).
Definition srSB : list expr := Eval vm_compute in s_regs (fst (fst hsB)).
Definition knSB : list kentry := Eval vm_compute in kn_after hsB knSB0.
(* [comment removed for export] *)
Definition knSB2 : list kentry := Eval vm_compute in kn_unfill knSB (EVar 3) 0 69632.
Definition srSC0 : list expr := sr_upd srSB (ridx 10) (ELit 0).
Definition hsC := Eval vm_compute in runh scr0 (SS 0x1dc44 srSC0 [] knSB2 NXh2).
Definition srSC : list expr := Eval vm_compute in s_regs (fst (fst hsC)).
Definition knSC : list kentry := Eval vm_compute in kn_after hsC knSB2.

(* [comment removed for export] *)
Definition scr_taken : scripts := SCR [true] [] [].
Definition hoA := Eval vm_compute in runh scr_taken (SS 0x13bbc sr_H [] kn_long NXh).
Definition srOA : list expr := Eval vm_compute in s_regs (fst (fst hoA)).
Definition knOA : list kentry := Eval vm_compute in kn_after hoA kn_long.
Definition scO : stdio_res := Eval vm_compute in
  match stdio_call NXh srOA knOA with Some r => r | None => SCR_ 0 0 0 (ELit 0) (ELit 0) (ELit 0) (ELit 0) (ELit 0) (ELit 0) (ELit 0) [] [] end.
Definition srOB0 : list expr := Eval vm_compute in sc_sr scO.
Definition knOB0 : list kentry := Eval vm_compute in sc_kn scO.
Definition hoB := Eval vm_compute in runh scr0 (SS (sc_ret scO) srOB0 [] knOB0 NXh2).
Definition srOB : list expr := Eval vm_compute in s_regs (fst (fst hoB)).
Definition knOB : list kentry := Eval vm_compute in kn_after hoB knOB0.
Definition knOB2 : list kentry := Eval vm_compute in kn_unfill knOB (EVar 3) 0 69632.
Definition srOC0 : list expr := sr_upd srOB (ridx 10) (ELit 0).
Definition hoC := Eval vm_compute in runh scr0 (SS 0x1dc44 srOC0 [] knOB2 NXh2).
Definition srOC : list expr := Eval vm_compute in s_regs (fst (fst hoC)).
Definition knOC : list kentry := Eval vm_compute in kn_after hoC knOB2.

(* [comment removed for export] *)
Definition scr_fall : scripts := SCR [false] [] [].
Definition hkA := Eval vm_compute in runh scr_fall (SS 0x13bbc sr_H [] kn_long NXh).
Definition srK : list expr := Eval vm_compute in s_regs (fst (fst hkA)).
(* [comment removed for export] *)
Definition cfglen_x : expr := Eval vm_compute in nth 11 srK (ELit 0).
(* [comment removed for export] *)
Definition cfglen_v : expr := EVar 47.
Definition srT : list expr := Eval vm_compute in map (esub cfglen_x cfglen_v) srK.
Definition knT : list kentry := kn_long.

(* [comment removed for export] *)
Lemma hdr_itinerary_ok :
  (s_pc (fst (fst hsA)), snd (fst hsA)) = (0x1e3d0%Z, [])
  /\ stdio_call NXh srSA knSA = Some scS /\ (sc_ret scS, sc_f scS, sc_fd scS) = (0x1e7d8%Z, 0x26810%Z, 2%Z)
  /\ (s_pc (fst (fst hsB)), snd (fst hsB)) = (0x1dc40%Z, [])
  /\ (s_pc (fst (fst hsC)), snd (fst hsC)) = (0x1bfa0%Z, [])
  /\ (s_pc (fst (fst hoA)), snd (fst hoA)) = (0x1e3d0%Z, [SCBr true BC_LTU (EVar 5) (EAlu ALU_ADD cfglen_x (ELit 6))])
  /\ stdio_call NXh srOA knOA = Some scO /\ (sc_ret scO, sc_f scO, sc_fd scO) = (0x1e7d8%Z, 0x26810%Z, 2%Z)
  /\ (s_pc (fst (fst hoB)), snd (fst hoB)) = (0x1dc40%Z, [])
  /\ (s_pc (fst (fst hoC)), snd (fst hoC)) = (0x1bfa0%Z, [])
  /\ s_pc (fst (fst hkA)) = 0x13d90%Z /\ s_log (fst (fst hkA)) = [] /\ s_next (fst (fst hkA)) = 47%nat.
Proof. first [ wf_conj_vm | vm_compute; repeat split; reflexivity ]. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import Lia.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
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

(* [comment removed for export] *)
From LinuxProcessSemantics.Riscv Require Import Sem.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.
Lemma hd_land_shl : forall a b k, (0 <= a)%Z -> (0 <= k)%Z -> (0 <= b < 2 ^ k)%Z -> Z.land (a * 2 ^ k) b = 0%Z.
Proof.
  intros a b k Ha Hk Hb. apply Z.bits_inj'. intros i Hi.
  rewrite Z.land_spec, Z.bits_0.
  destruct (Z.lt_ge_cases i k) as [Hl|Hh].
  - rewrite Z.mul_pow2_bits_low by lia. reflexivity.
  - rewrite (Z_testbit_high k b i) by lia. apply Bool.andb_false_r.
Qed.
Lemma hd_lor_shl : forall a b k, (0 <= a)%Z -> (0 <= k)%Z -> (0 <= b < 2 ^ k)%Z -> Z.lor (a * 2 ^ k) b = (a * 2 ^ k + b)%Z.
Proof.
  intros a b k Ha Hk Hb. rewrite <- Z.lxor_lor by (apply hd_land_shl; lia).
  symmetry. apply Z.add_nocarry_lxor. apply hd_land_shl; lia.
Qed.

Lemma cfgF_val : forall b0 b1, (0 <= b0 < 256)%Z -> (0 <= b1 < 256)%Z ->
  cfgF (Z_to_bv 64 b0) (Z_to_bv 64 b1) = Z_to_bv 64 ((b0 + 256 * b1) mod 32768).
Proof.
  intros b0 b1 H0 H1. unfold cfgF, cfglen_x. cbn [edenot ev]. unfold alu64, alu, mul_div, ext_val.
  apply bv_eq. rewrite bv_or_unsigned, bv_shiftr_unsigned, bv_and_unsigned, bv_mul_unsigned.
  rewrite !Z_to_bv_unsigned. unfold ext_Z.
  change (8 * Z.of_nat 0) with 0. change (8 * Z.of_nat 1) with 8. change (8 * N.of_nat 1)%N with 8%N.
  change (2 ^ 0) with 1. change (2 ^ 8) with 256. rewrite !Z.div_1_r.
  unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with 18446744073709551616.
  rewrite (Z.mod_small 144115188075855872) by lia. rewrite (Z.mod_small 49) by lia. rewrite (Z.mod_small 63) by lia.
  change (Z.land 49 63) with 49.
  rewrite (Z.mod_small b0 18446744073709551616) by lia. rewrite (Z.mod_small b1 18446744073709551616) by lia.
  rewrite (Z.mod_small b0 256) by lia. rewrite (Z.mod_small b1 256) by lia.
  rewrite (Z.mod_small b0 18446744073709551616) by lia.
  (* [comment removed for export] *)
  assert (HM : (144115188075855872 * (bv_swrap 8 b1 mod 18446744073709551616)) mod 18446744073709551616
               = (b1 mod 128) * 2 ^ 57).
  { unfold bv_swrap, bv_half_modulus, bv_modulus, bv_wrap. change (2 ^ Z.of_N 8) with 256. change (256 `div` 2) with 128.
    change (bv_modulus 8) with 256. destruct (Z.ltb_spec b1 128) as [Hs|Hs].
    - rewrite (Z.mod_small (b1 + 128) 256) by lia. replace (b1 + 128 - 128) with b1 by lia.
      rewrite (Z.mod_small b1) by lia. rewrite (Z.mod_small b1 128) by lia. rewrite Z.mod_small by lia. lia.
    - replace ((b1 + 128) mod 256) with (b1 - 128) by (apply Z.mod_unique with 1; lia).
      replace ((b1 - 128 - 128) mod 18446744073709551616) with (b1 - 256 + 18446744073709551616)
        by (apply Z.mod_unique with (-1); lia).
      replace (b1 mod 128) with (b1 - 128) by (apply Z.mod_unique with 1; lia).
      symmetry. apply Z.mod_unique with (2 ^ 57 - 1); lia. }
  rewrite HM. rewrite Z.shiftr_div_pow2 by lia.
  replace ((b1 mod 128) * 2 ^ 57 / 2 ^ 49) with ((b1 mod 128) * 2 ^ 8)
    by (replace (2 ^ 57) with (2 ^ 8 * 2 ^ 49) by reflexivity; rewrite Z.mul_assoc, Z.div_mul by lia; reflexivity).
  rewrite hd_lor_shl by (pose proof (Z.mod_pos_bound b1 128 ltac:(lia)); lia).
  pose proof (Z.mod_pos_bound b1 128 ltac:(lia)) as Hm.
  pose proof (Z.div_mod b1 128 ltac:(lia)) as Hd.
  assert (Hq : 0 <= b1 / 128 <= 1) by lia.
  assert (HE : b1 mod 128 * 2 ^ 8 + b0 = (b0 + 256 * b1) mod 32768).
  { change (2 ^ 8) with 256. apply Z.mod_unique with (b1 / 128); lia. }
  rewrite HE. symmetry. apply Z.mod_small. pose proof (Z.mod_pos_bound (b0 + 256 * b1) 32768 ltac:(lia)). lia.
Qed.

(* [comment removed for export] *)
From OSSVerify.Proofs.coturn.FuzzStunClient.lib Require Import TargetSpec.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
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

(* [comment removed for export] *)
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

(* [comment removed for export] *)
Lemma mod_eq_shift : forall a b k m, (0 < m)%Z -> (a = b + k * m)%Z -> (a mod m = b mod m)%Z.
Proof. intros a b k m Hm ->. apply Z_mod_plus_full. Qed.
