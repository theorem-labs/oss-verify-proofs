(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib Require Import Tac.
From OSSVerify.Proofs.fast_float.from_chars.lib.LibAsan Require Import Shadow.
From OSSVerify.Proofs.fast_float.from_chars.lib.FF Require Import Spf_text.
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

Section INT.
  Variables (x1 x2 x3 x4 x5 x6 x7 x8 x9 x17 x18 x20 x21 x24 x25 x26 x27 x28 x29 x30 x31 : word).
  Variables (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (bs : list byte) (T S Y0 Y1 : Z).
  #[local] Notation L := (Z.of_nat (length bs)).
  Hypothesis TXT : bytes_at ASEGS m T bs.
  Hypothesis HL : (1 <= L <= 128)%Z.
  Hypothesis HT : (6529024 <= T <= 140737488355072)%Z.
  Hypothesis HS : (T <= S <= T + L)%Z.
  Hypothesis SHT : shz ASEGS m (ASAN_B + Y0) (Y1 - Y0).
  Hypothesis HY : (8 * Y0 <= T /\ T + L <= 8 * Y1)%Z.

  Definition int_post : machine_state -> Prop := fun ms' =>
    exists a0 a1 a2 a3 a4 a5 a6 : word,
      ms' = MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 a0 a1 a2 a3 a4 a5 a6 x17 x18 (Z_to_bv 64 ASAN_B) x20 x21 (Z_to_bv 64 S) (Z_to_bv 64 (T + L)) x24 x25 x26 x27 x28 x29 x30 x31)
               F (Z_to_bv 64 0x99c60) fc None m (seg_rom ASEGS)
      /\ (S <= bv_unsigned a0 <= T + L)%Z /\ digs bs (S - T) (bv_unsigned a0 - T).

  (* [comment removed for export] *)
  #[using="HY"] Lemma tx_gran : forall A, (T <= A < T + L)%Z -> (ASAN_B + Y0 <= A / 8 + ASAN_B)%Z /\ (A / 8 + ASAN_B + 1 <= ASAN_B + Y0 + (Y1 - Y0))%Z.
  Proof. LiaFast.lf_pins (fun (HY : LiaFast.U) => LiaFast.u0). intros A HA. destruct HY as [Y1a Y2a]. Z.div_mod_to_equations. lia. Qed.

  (* [comment removed for export] *)
  #[using="Y0 Y1 TXT HL HT HS SHT HY"] Lemma loopI : forall (n : nat) (k : Z) (a4 a5 a6 : word),
      (T + L - (T + k) <= Z.of_nat n)%Z -> (S - T <= k < L)%Z -> digs bs (S - T) k ->
      evt ASEGS int_post
        (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 (Z_to_bv 64 (T + k)) (Z_to_bv 64 (T + k)) (Z_to_bv 64 10) (Z_to_bv 64 9) a4 a5 a6
                 x17 x18 (Z_to_bv 64 ASAN_B) x20 x21 (Z_to_bv 64 S) (Z_to_bv 64 (T + L)) x24 x25 x26 x27 x28 x29 x30 x31)
            F (Z_to_bv 64 0x99bb4) fc None m (seg_rom ASEGS)).
  Proof. LiaFast.lf_pins (fun (Y0 Y1 TXT HL HT HS SHT HY : LiaFast.U) => LiaFast.u0).
    induction n as [|n IH]; intros k a4 a5 a6 Hn HK DG; [exfalso; lia|].
    pose proof (shz_bound _ _ _ _ SHT) as BT.
    pose proof (tx_gran (T + k) ltac:(lia)) as G0.
    step. (* [comment removed for export] *) shr3.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    txt_rd TXT k RD. pose proof (tx_range bs k) as Rk.
    step. (* [comment removed for export] *)
    clear RD. fold_tx bs k.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    if_cases Hd.
    - cond_cleanup Hd. clear Hd. apply evt_done.
      do 7 eexists. split; [reflexivity|]. rewrite unsigned_lit by lia. split; [lia|]. replace (T + k - T)%Z with k by lia. exact DG.
    - cond_cleanup Hd. pose proof (dig_yes _ Rk Hd) as D. clear Hd.
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      if_cases Hmore.
      + cond_cleanup Hmore.
        goto (eapply (IH (k + 1)%Z)); [lia | lia | apply digs_snoc; assumption].
      + cond_cleanup Hmore.
        step. (* [comment removed for export] *)
        step. (* [comment removed for export] *)
        step. (* [comment removed for export] *)
        apply evt_done. do 7 eexists. split; [reflexivity|]. rewrite unsigned_lit by lia.
        split; [lia|]. replace (T + L - T)%Z with (k + 1)%Z by lia. apply digs_snoc; assumption.
  Qed.

  (* [comment removed for export] *)
  #[local] Ltac dig_rd j RD R :=
    txt_rd TXT (S - T + j)%Z RD; pose proof (tx_range bs (S - T + j)) as R.

  (* [comment removed for export] *)
  #[using="Y0 Y1 TXT HL HT HS SHT HY"] Lemma blockI : forall (a0 a1 a2 a3 a4 a5 a6 : word),
      evt ASEGS int_post
        (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 a0 a1 a2 a3 a4 a5 a6
                 x17 x18 (Z_to_bv 64 ASAN_B) x20 x21 (Z_to_bv 64 S) (Z_to_bv 64 (T + L)) x24 x25 x26 x27 x28 x29 x30 x31)
            F (Z_to_bv 64 0x99a8c) fc None m (seg_rom ASEGS)).
  Proof. LiaFast.lf_pins (fun (Y0 Y1 TXT HL HT HS SHT HY : LiaFast.U) => LiaFast.u0).
    intros a0 a1 a2 a3 a4 a5 a6.
    pose proof (shz_bound _ _ _ _ SHT) as BT.
    pose proof (digs_nil bs (S - T)) as DG0.
    step. (* [comment removed for export] *)
    if_cases Hend.
    { cond_cleanup Hend.
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      apply evt_done. do 7 eexists. split; [reflexivity|]. rewrite unsigned_lit by lia. split; [lia|]. exact DG0. }
    cond_cleanup Hend.
    pose proof (tx_gran S ltac:(lia)) as G0.
    step. (* [comment removed for export] *) shr3.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    txt_rd TXT (S - T)%Z RD. pose proof (tx_range bs (S - T)) as R0.
    replace (T + (S - T))%Z with S in RD by lia.
    step. (* [comment removed for export] *)
    clear RD. fold_tx bs (S - T)%Z.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    if_cases Hd0.
    { cond_cleanup Hd0. clear Hd0.
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      apply evt_done. do 7 eexists. split; [reflexivity|]. rewrite unsigned_lit by lia. split; [lia|]. exact DG0. }
    cond_cleanup Hd0. pose proof (dig_yes _ R0 Hd0) as D0. clear Hd0.
    pose proof (digs_snoc _ _ _ DG0 D0) as DG1.
    (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    if_cases He1.
    { cond_cleanup He1. apply evt_done. do 7 eexists. split; [reflexivity|]. rewrite unsigned_lit by lia. split; [lia|].
      replace (S + 1 - T)%Z with (S - T + 1)%Z by lia. exact DG1. }
    cond_cleanup He1.
    pose proof (tx_gran (S + 1) ltac:(lia)) as G1.
    step. (* [comment removed for export] *) shr3.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    txt_rd TXT (S - T + 1)%Z RD. pose proof (tx_range bs (S - T + 1)) as R1.
    replace (T + (S - T + 1))%Z with (S + 1)%Z in RD by lia.
    step. (* [comment removed for export] *)
    clear RD. fold_tx bs (S - T + 1)%Z.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    if_cases Hd1.
    { cond_cleanup Hd1. clear Hd1. apply evt_done. do 7 eexists. split; [reflexivity|]. rewrite unsigned_lit by lia. split; [lia|].
      replace (S + 1 - T)%Z with (S - T + 1)%Z by lia. exact DG1. }
    cond_cleanup Hd1. pose proof (dig_yes _ R1 Hd1) as D1. clear Hd1.
    pose proof (digs_snoc _ _ _ DG1 D1) as DG2. replace (S - T + 1 + 1)%Z with (S - T + 2)%Z in DG2 by lia.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    if_cases He2.
    { cond_cleanup He2. apply evt_done. do 7 eexists. split; [reflexivity|]. rewrite unsigned_lit by lia. split; [lia|].
      replace (S + 2 - T)%Z with (S - T + 2)%Z by lia. exact DG2. }
    cond_cleanup He2.
    pose proof (tx_gran (S + 2) ltac:(lia)) as G2.
    step. (* [comment removed for export] *) shr3.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    txt_rd TXT (S - T + 2)%Z RD. pose proof (tx_range bs (S - T + 2)) as R2.
    replace (T + (S - T + 2))%Z with (S + 2)%Z in RD by lia.
    step. (* [comment removed for export] *)
    clear RD. fold_tx bs (S - T + 2)%Z.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    if_cases Hd2.
    { cond_cleanup Hd2. clear Hd2. apply evt_done. do 7 eexists. split; [reflexivity|]. rewrite unsigned_lit by lia. split; [lia|].
      replace (S + 2 - T)%Z with (S - T + 2)%Z by lia. exact DG2. }
    cond_cleanup Hd2. pose proof (dig_yes _ R2 Hd2) as D2. clear Hd2.
    pose proof (digs_snoc _ _ _ DG2 D2) as DG3. replace (S - T + 2 + 1)%Z with (S - T + 3)%Z in DG3 by lia.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    if_cases He3.
    { cond_cleanup He3. apply evt_done. do 7 eexists. split; [reflexivity|]. rewrite unsigned_lit by lia. split; [lia|].
      replace (S + 3 - T)%Z with (S - T + 3)%Z by lia. exact DG3. }
    cond_cleanup He3.
    pose proof (tx_gran (S + 3) ltac:(lia)) as G3.
    step. (* [comment removed for export] *) shr3.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    txt_rd TXT (S - T + 3)%Z RD. pose proof (tx_range bs (S - T + 3)) as R3.
    replace (T + (S - T + 3))%Z with (S + 3)%Z in RD by lia.
    step. (* [comment removed for export] *)
    clear RD. fold_tx bs (S - T + 3)%Z.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    if_cases Hd3.
    { cond_cleanup Hd3. clear Hd3. apply evt_done. do 7 eexists. split; [reflexivity|]. rewrite unsigned_lit by lia. split; [lia|].
      replace (S + 3 - T)%Z with (S - T + 3)%Z by lia. exact DG3. }
    cond_cleanup Hd3. pose proof (dig_yes _ R3 Hd3) as D3. clear Hd3.
    pose proof (digs_snoc _ _ _ DG3 D3) as DG4. replace (S - T + 3 + 1)%Z with (S - T + 4)%Z in DG4 by lia.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    if_cases He4.
    { cond_cleanup He4. apply evt_done. do 7 eexists. split; [reflexivity|]. rewrite unsigned_lit by lia. split; [lia|].
      replace (S + 4 - T)%Z with (S - T + 4)%Z by lia. exact DG4. }
    cond_cleanup He4.
    pose proof (tx_gran (S + 4) ltac:(lia)) as G4.
    step. (* [comment removed for export] *) shr3.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    txt_rd TXT (S - T + 4)%Z RD. pose proof (tx_range bs (S - T + 4)) as R4.
    replace (T + (S - T + 4))%Z with (S + 4)%Z in RD by lia.
    step. (* [comment removed for export] *)
    clear RD. fold_tx bs (S - T + 4)%Z.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    if_cases Hd4.
    { cond_cleanup Hd4. clear Hd4. apply evt_done. do 7 eexists. split; [reflexivity|]. rewrite unsigned_lit by lia. split; [lia|].
      replace (S + 4 - T)%Z with (S - T + 4)%Z by lia. exact DG4. }
    cond_cleanup Hd4. pose proof (dig_yes _ R4 Hd4) as D4. clear Hd4.
    pose proof (digs_snoc _ _ _ DG4 D4) as DG5. replace (S - T + 4 + 1)%Z with (S - T + 5)%Z in DG5 by lia.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    if_cases He5.
    { cond_cleanup He5. apply evt_done. do 7 eexists. split; [reflexivity|]. rewrite unsigned_lit by lia. split; [lia|].
      replace (S + 5 - T)%Z with (S - T + 5)%Z by lia. exact DG5. }
    cond_cleanup He5.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    goto (eapply (loopI (Datatypes.S (Z.to_nat (L - (S - T + 5)))) (S - T + 5)%Z)); [lia | lia | exact DG5].
  Qed.
End INT.
