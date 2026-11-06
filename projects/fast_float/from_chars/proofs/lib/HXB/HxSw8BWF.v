(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib Require Import Tac.
From OSSVerify.Proofs.fast_float.from_chars.lib.LibAsan Require Import Shadow.
From OSSVerify.Proofs.fast_float.from_chars.lib.FF Require Spf_text.
From OSSVerify.Proofs.fast_float.from_chars.lib.FF Require Spf_text.
Import OSSVerify.Proofs.fast_float.from_chars.lib.FF.Spf_text OSSVerify.Proofs.fast_float.from_chars.lib.FF.Spf_text.Spf_swar.
From OSSVerify.fast_float.from_chars.images Require Import AsanUbsan.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Ltac ms_eq_tac ::=
  cbv beta delta [mkR];
  repeat first [ reflexivity
               | lazymatch goal with |- @eq (bv _) _ _ => ms_leaf_eq end
               | progress f_equal ].

Notation BSEGS := AsanUbsan.M.loaded_segments.

Lemma v8_facts : forall z0 z1 z2 z3 z4 z5 z6 z7,
  (0 <= z0 < 256 -> 0 <= z1 < 256 -> 0 <= z2 < 256 -> 0 <= z3 < 256 ->
   0 <= z4 < 256 -> 0 <= z5 < 256 -> 0 <= z6 < 256 -> 0 <= z7 < 256 ->
   0 <= v8 z0 z1 z2 z3 z4 z5 z6 z7 < 2^64 /\ v8 z0 z1 z2 z3 z4 z5 z6 z7 mod 2^32 = v4 z0 z1 z2 z3)%Z.
Proof.
  intros. pose proof (v4_range z0 z1 z2 z3). pose proof (v4_range z4 z5 z6 z7). unfold v8. split; [lia|].
  rewrite (Z.mul_comm (2^32)). rewrite Z.mod_add by lia. apply Z.mod_small. lia.
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

Section SW8.
  Variables (x2 x3 x4 x8 x9 x20 x21 x22 G6 : word).
  Variables (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (bs : list byte) (T FP Y0 Y1 : Z).
  #[local] Notation L := (Z.of_nat (length bs)).
  #[local] Notation Zw z := (Z_to_bv 64 z).
  Hypothesis TXT : bytes_at BSEGS m T bs.
  Hypothesis HL : (1 <= L <= 128)%Z.
  Hypothesis HT : (6537216 <= T <= 140737488355072)%Z.
  Hypothesis SHT : shz BSEGS m (ASAN_B + Y0) (Y1 - Y0).
  Hypothesis HY : (8 * Y0 <= T /\ T + L <= 8 * Y1)%Z.
  Hypothesis HFP : (T <= FP)%Z.

  #[local] Notation S8T pc x1 x5 x6 x7 x11 x12 x14 x15 x18 x23 x24 x27 :=
    (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 (Zw 10) x11 x12 (Zw 7) x14 x15 G6 (Zw 14974415777481871312) x18 (Zw ASAN_B) x20 x21 x22 x23 x24
             (Zw 42949672960001) (Zw 1095216660735) x27
             (Zw 9259542123273814144) (Zw 5063812098665367110) (Zw 100000000) (Zw 4294967296000100))
        F (Zw pc) fc None m (seg_rom BSEGS)) (only parsing).

  Definition sw8_post : machine_state -> Prop := fun ms' =>
    exists y1 y5 y6 y7 y11 y12 y14 y15 y18 y23 y24 y27 : word,
      ((ms' = S8T 0x9b6e0 y1 y5 y6 y7 y11 y12 y14 y15 y18 y23 y24 y27 /\ y6 = y24 /\ bv_unsigned y24 + 8 <= T + L)%Z \/
       (ms' = S8T 0x9b700 y1 y5 y6 y7 y11 y12 y14 y15 y18 y23 y24 y27 /\ bv_unsigned y12 = bv_unsigned y24 + 7 /\ y27 = G6 /\
        T + L - bv_unsigned y24 <= 7)%Z) /\
      (FP <= bv_unsigned y24 <= T + L)%Z /\ bv_unsigned y11 = (T + L - bv_unsigned y24)%Z /\
      digs bs (FP - T) (bv_unsigned y24 - T).

  #[using="HY"] Lemma gran8 : forall A, (T <= A < T + L)%Z -> (ASAN_B + Y0 <= A / 8 + ASAN_B)%Z /\ (A / 8 + ASAN_B + 1 <= ASAN_B + Y0 + (Y1 - Y0))%Z.
  Proof. LiaFast.lf_pins (fun (HY : LiaFast.U) => LiaFast.u0). intros A HA. destruct HY as [Y1a Y2a]. Z.div_mod_to_equations. lia. Qed.

  (* [comment removed for export] *)
  #[using="Y0 Y1 TXT HL HT SHT HY HFP"] Lemma loop8 : forall (n : nat) (kc : Z) (x5 x7 x14 x15 x18 x23 : word),
      (L - kc <= Z.of_nat n)%Z -> (FP - T <= kc)%Z -> (kc + 8 <= L)%Z -> digs bs (FP - T) kc ->
      evt BSEGS sw8_post (S8T 0x9b14c (Zw (ASAN_B + (T + kc) / 8)) x5 (Zw (T + kc)) x7 (Zw (L - kc)) (Zw (T + kc + 7)) x14 x15 x18 x23
                              (Zw (T + kc)) G6).
  Proof. LiaFast.lf_pins (fun (Y0 Y1 TXT HL HT SHT HY HFP : LiaFast.U) => LiaFast.u0).
    induction n as [|n IH]; intros kc x5 x7 x14 x15 x18 x23 Hn KC KC8 DGF; [exfalso; lia|].
    pose proof (shz_bound _ _ _ _ SHT) as BT.
    pose proof (tx_range bs kc) as R0. pose proof (tx_range bs (kc + 1)) as R1.
    pose proof (tx_range bs (kc + 2)) as R2. pose proof (tx_range bs (kc + 3)) as R3.
    pose proof (tx_range bs (kc + 4)) as R4. pose proof (tx_range bs (kc + 5)) as R5.
    pose proof (tx_range bs (kc + 6)) as R6. pose proof (tx_range bs (kc + 7)) as R7.
    pose proof (gran8 (T + kc) ltac:(lia)) as G0. pose proof (gran8 (T + kc + 7) ltac:(lia)) as G7.
    step. (* [comment removed for export] *) shr3.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    txt_rd TXT (kc + 1)%Z RD. step. clear RD. fold_tx bs (kc + 1)%Z.   (* [comment removed for export] *)
    txt_rd TXT (kc + 2)%Z RD. step. clear RD. fold_tx bs (kc + 2)%Z.   (* [comment removed for export] *)
    txt_rd TXT (kc + 3)%Z RD. step. clear RD. fold_tx bs (kc + 3)%Z.   (* [comment removed for export] *)
    txt_rd TXT (kc + 0)%Z RD. step. clear RD. fold_tx bs (kc + 0)%Z. try rewrite (Z.add_0_r kc).   (* [comment removed for export] *)
    do 4 step. (* [comment removed for export] *)
    txt_rd TXT (kc + 4)%Z RD. step. clear RD. fold_tx bs (kc + 4)%Z.   (* [comment removed for export] *)
    txt_rd TXT (kc + 5)%Z RD. step. clear RD. fold_tx bs (kc + 5)%Z.   (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    txt_rd TXT (kc + 6)%Z RD. step. clear RD. fold_tx bs (kc + 6)%Z.   (* [comment removed for export] *)
    txt_rd TXT (kc + 7)%Z RD. step. clear RD. fold_tx bs (kc + 7)%Z.   (* [comment removed for export] *)
    do 9 step. (* [comment removed for export] *)
    rewrite (ortree8_eq (tx bs kc) (tx bs (kc + 1)) (tx bs (kc + 2)) (tx bs (kc + 3))
                        (tx bs (kc + 4)) (tx bs (kc + 5)) (tx bs (kc + 6)) (tx bs (kc + 7))) by (apply tx_range).
    destruct (v8_facts _ _ _ _ _ _ _ _ R0 R1 R2 R3 R4 R5 R6 R7) as [VR VM].
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    if_cases Hsw.
    - clear Hsw. apply evt_done. do 12 eexists.
      split; [left; split; [reflexivity | split; [reflexivity | rewrite unsigned_lit by lia; lia]]|].
      rewrite !unsigned_lit by lia. split; [lia|]. split; [lia|]. replace (T + kc - T)%Z with kc by lia. exact DGF.
    - rewrite ?(unsigned_lit (v8 (tx bs kc) (tx bs (kc + 1)) (tx bs (kc + 2)) (tx bs (kc + 3))
                        (tx bs (kc + 4)) (tx bs (kc + 5)) (tx bs (kc + 6)) (tx bs (kc + 7)))) in Hsw by lia.
      destruct (swar8_dig _ _ _ _ _ _ _ _ _ R0 R1 R2 R3 R4 R5 R6 R7 eq_refl Hsw) as (D0 & D1 & D2 & D3 & D4 & D5 & D6 & D7).
      clear Hsw.
      assert (DGF' : digs bs (FP - T) (kc + 8)).
      { replace (kc + 8)%Z with (kc + 4 + 4)%Z by lia.
        apply digs_snoc4; [apply digs_snoc4; assumption | exact D4 | | |].
        - replace (kc + 4 + 1)%Z with (kc + 5)%Z by lia. exact D5.
        - replace (kc + 4 + 2)%Z with (kc + 6)%Z by lia. exact D6.
        - replace (kc + 4 + 3)%Z with (kc + 7)%Z by lia. exact D7. }
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      if_cases Hu; [| cond_cleanup Hu; exfalso; lia].
      cond_cleanup Hu. clear Hu.
      do 17 step. (* [comment removed for export] *)
      rewrite ?(unsigned_lit (L - kc)%Z) by lia.
      step. (* [comment removed for export] *)
      if_cases Hmore.
      + cond_cleanup Hmore. try rewrite signed_lit in Hmore by lia.
        pose proof (gran8 (T + kc + 8) ltac:(lia)) as G8.
        assert (EQ8 : ((T + kc + 8) / 8 = (T + kc) / 8 + 1)%Z) by (clear; Z.div_mod_to_equations; lia).
        step. (* [comment removed for export] *)
        step. (* [comment removed for export] *)
        step. (* [comment removed for export] *)
        step. (* [comment removed for export] *)
        goto (eapply (IH (kc + 8)%Z)); [lia | lia | lia | exact DGF'].
      + cond_cleanup Hmore. try rewrite signed_lit in Hmore by lia.
        step. (* [comment removed for export] *)
        apply evt_done. do 12 eexists.
        split; [right; split; [reflexivity | split; [rewrite !unsigned_lit by lia; lia | split; [reflexivity | rewrite unsigned_lit by lia; lia]]]|].
        rewrite !unsigned_lit by lia. split; [lia|]. split; [lia|]. replace (T + kc + 8 - T)%Z with (kc + 8)%Z by lia. exact DGF'.
  Qed.
End SW8.
