(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib Require Import Tac.
From OSSVerify.Proofs.fast_float.from_chars.lib.LibAsan Require Import Shadow.
From OSSVerify.Proofs.fast_float.from_chars.lib.FF Require Spf_text.
From OSSVerify.Proofs.fast_float.from_chars.lib.FF Require Spf_text.
Import OSSVerify.Proofs.fast_float.from_chars.lib.FF.Spf_text OSSVerify.Proofs.fast_float.from_chars.lib.FF.Spf_text.Spf_swar.
From OSSVerify.fast_float.from_chars.images Require Import Asan.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Ltac ms_eq_tac ::=
  cbv beta delta [mkR];
  repeat first [ reflexivity
               | lazymatch goal with |- @eq (bv _) _ _ => ms_leaf_eq end
               | progress f_equal ].

Notation ASEGS := Asan.M.loaded_segments.
#[local] Notation U := bv_unsigned.

Lemma Z_to_bv_bv_unsigned8 : forall (x : bv 8), Z_to_bv 8 (bv_unsigned x) = x.
Proof. intros. apply bv_eq. rewrite Z_to_bv_unsigned. apply bv_wrap_small. apply bv_unsigned_in_range. Qed.

(* [comment removed for export] *)
Lemma ortree4s : forall z0 z1 z2 (b3 : bv 8),
  (0 <= z0 < 256 -> 0 <= z1 < 256 -> 0 <= z2 < 256 ->
  let V := Z.lor (U (Z_to_bv 64 (Z.lor (U (Z_to_bv 64 (Z.shiftl (U (sxb b3)) 24))) (U (Z_to_bv 64 (Z.shiftl (U (Z_to_bv 64 z2)) 16))))))
                 (U (Z_to_bv 64 (Z.lor (U (Z_to_bv 64 (Z.shiftl (U (Z_to_bv 64 z1)) 8))) (U (Z_to_bv 64 z0))))) in
  0 <= V < 2^64 /\ V mod 2^32 = v4 z0 z1 z2 (U b3))%Z.
Proof.
  intros z0 z1 z2 b3 H0 H1 H2. cbv zeta.
  pose proof (bv_unsigned_in_range 8 b3) as R3. unfold bv_modulus in R3. change (2 ^ Z.of_N 8)%Z with 256%Z in R3.
  set (z3 := U b3) in *.
  rewrite <- (Z_to_bv_bv_unsigned8 b3). fold z3.
  destruct (Z.lt_ge_cases z3 128) as [Hs|Hs].
  - rewrite (sxb_lit_pos z3) by lia.
    rewrite (ortree4_eq z0 z1 z2 z3) by lia.
    pose proof (v4_range z0 z1 z2 z3 H0 H1 H2 ltac:(lia)). split; [lia|]. apply Z.mod_small. lia.
  - rewrite (sxb_lit_neg z3) by lia.
    rewrite (unsigned_lit_wrap (z3 - 256)).
    replace ((z3 - 256) mod 2 ^ 64)%Z with (z3 - 256 + 2^64)%Z by (Z.div_mod_to_equations; lia).
    rewrite !Z.shiftl_mul_pow2 by lia.
    rewrite (unsigned_lit_wrap ((z3 - 256 + 2 ^ 64) * 2 ^ 24)).
    replace (((z3 - 256 + 2 ^ 64) * 2 ^ 24) mod 2 ^ 64)%Z with ((z3 + 2^40 - 256) * 2^24)%Z by (Z.div_mod_to_equations; lia).
    rewrite (unsigned_lit z2), (unsigned_lit z1), (unsigned_lit z0) by lia.
    rewrite (unsigned_lit (z2 * 2^16)), (unsigned_lit (z1 * 2^8)) by lia.
    rewrite (lor_mul (z3 + 2^40 - 256) (z2 * 2^16) 24) by lia.
    rewrite (lor_mul z1 z0 8) by lia.
    rewrite (unsigned_lit ((z3 + 2 ^ 40 - 256) * 2 ^ 24 + z2 * 2 ^ 16)) by lia.
    rewrite (unsigned_lit (z1 * 2 ^ 8 + z0)) by lia.
    replace ((z3 + 2 ^ 40 - 256) * 2 ^ 24 + z2 * 2 ^ 16)%Z with (((z3 + 2 ^ 40 - 256) * 2 ^ 8 + z2) * 2 ^ 16)%Z by lia.
    rewrite (lor_mul ((z3 + 2 ^ 40 - 256) * 2 ^ 8 + z2) (z1 * 2 ^ 8 + z0) 16) by lia.
    unfold v4. split; [lia|]. Z.div_mod_to_equations. lia.
Qed.

Lemma digs_snoc4 : forall bs lo k, digs bs lo k ->
  isdig (tx bs k) -> isdig (tx bs (k + 1)) -> isdig (tx bs (k + 2)) -> isdig (tx bs (k + 3)) -> digs bs lo (k + 4).
Proof.
  intros bs lo k H D0 D1 D2 D3.
  replace (k + 4)%Z with (k + 3 + 1)%Z by lia. apply digs_snoc; [|exact D3].
  replace (k + 3)%Z with (k + 2 + 1)%Z by lia. apply digs_snoc; [|exact D2].
  replace (k + 2)%Z with (k + 1 + 1)%Z by lia. apply digs_snoc; [|exact D1].
  apply digs_snoc; [exact H|exact D0].
Qed.

Section SW4F.
  Variables (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x16 x17 x18 x20 x21 x22 x23 x24 x25 x27 x28 x29 x30 x31 : word).
  Variables (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (bs : list byte) (T FP Y0 Y1 : Z).
  #[local] Notation L := (Z.of_nat (length bs)).
  #[local] Notation Zw z := (Z_to_bv 64 z).
  Hypothesis TXT : bytes_at ASEGS m T bs.
  Hypothesis HL : (1 <= L <= 128)%Z.
  Hypothesis HT : (6529024 <= T <= 140737488355072)%Z.
  Hypothesis SHT : shz ASEGS m (ASAN_B + Y0) (Y1 - Y0).
  Hypothesis HY : (8 * Y0 <= T /\ T + L <= 8 * Y1)%Z.
  Hypothesis HFP : (T <= FP)%Z.

  #[local] Notation WST pc x11 x12 x13 x14 x15 x26 :=
    (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 (Zw ASAN_B) x20 x21 x22 x23 x24 x25 x26 x27
             x28 x29 x30 x31)
        F (Zw pc) fc None m (seg_rom ASEGS)) (only parsing).

  Definition sw4_post : machine_state -> Prop := fun ms' =>
    exists y11 y12 y13 y14 y15 y26 : word,
      ms' = WST 0x9a308 y11 y12 y13 y14 y15 y26 /\
      (FP <= bv_unsigned y26 <= T + L)%Z /\ digs bs (FP - T) (bv_unsigned y26 - T).

  #[using="HY"] Lemma tx_gran : forall A, (T <= A < T + L)%Z -> (ASAN_B + Y0 <= A / 8 + ASAN_B)%Z /\ (A / 8 + ASAN_B + 1 <= ASAN_B + Y0 + (Y1 - Y0))%Z.
  Proof. LiaFast.lf_pins (fun (HY : LiaFast.U) => LiaFast.u0). intros A HA. destruct HY as [Y1a Y2a]. Z.div_mod_to_equations. lia. Qed.

  (* [comment removed for export] *)
  #[using="Y0 Y1 TXT HL HT SHT HY HFP"] Lemma blockW4 : forall (kc : Z) (x11 x12 x13 x14 x15 : word),
      (FP - T <= kc)%Z -> (kc + 4 <= L)%Z -> digs bs (FP - T) kc ->
      evt ASEGS sw4_post (WST 0x9a248 x11 x12 x13 x14 x15 (Zw (T + kc))).
  Proof. LiaFast.lf_pins (fun (Y0 Y1 TXT HL HT SHT HY HFP : LiaFast.U) => LiaFast.u0).
    intros kc x11 x12 x13 x14 x15 KC KC4 DGF.
    pose proof (shz_bound _ _ _ _ SHT) as BT.
    pose proof (tx_range bs kc) as R0. pose proof (tx_range bs (kc + 1)) as R1.
    pose proof (tx_range bs (kc + 2)) as R2. pose proof (tx_range bs (kc + 3)) as R3.
    pose proof (tx_gran (T + kc) ltac:(lia)) as G0.
    step. (* [comment removed for export] *) shr3.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    pose proof (tx_gran (T + kc + 3) ltac:(lia)) as G3.
    step. (* [comment removed for export] *) shr3.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    txt_rd TXT (kc + 1)%Z RD. step. (* [comment removed for export] *) clear RD. fold_tx bs (kc + 1)%Z.
    txt_rd TXT (kc + 0)%Z RD. step. (* [comment removed for export] *) clear RD. fold_tx bs (kc + 0)%Z. try rewrite (Z.add_0_r kc).
    txt_rd TXT (kc + 2)%Z RD. step. (* [comment removed for export] *) clear RD. fold_tx bs (kc + 2)%Z.
    txt_rd TXT (kc + 3)%Z RD. step. (* [comment removed for export] *) clear RD.
    lazymatch goal with |- context [sxb ?b] =>
      destruct (ortree4s (tx bs kc) (tx bs (kc + 1)) (tx bs (kc + 2)) b R0 R1 R2) as [VR VM];
      change (bv_unsigned b) with (tx bs (kc + 3)) in VM end.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    lazymatch type of VR with (0 <= ?v < _)%Z => set (Vv := v) in * end.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    rewrite ?(unsigned_lit Vv) by lia.
    step. (* [comment removed for export] *)
    if_cases H4.
    - clear H4. apply evt_done. do 6 eexists. split; [reflexivity|]. rewrite unsigned_lit by lia. split; [lia|].
      replace (T + kc - T)%Z with kc by lia. exact DGF.
    - rewrite ?(unsigned_lit Vv) in H4 by lia.
      destruct (swar4_dig Vv _ _ _ _ R0 R1 R2 R3 VR VM H4) as (D0 & D1 & D2 & D3). clear H4.
      do 16 step. (* [comment removed for export] *)
      apply evt_done. do 6 eexists. split; [reflexivity|]. rewrite unsigned_lit by lia. split; [lia|].
      replace (T + kc + 4 - T)%Z with (kc + 4)%Z by lia. apply digs_snoc4; assumption.
  Qed.
End SW4F.
