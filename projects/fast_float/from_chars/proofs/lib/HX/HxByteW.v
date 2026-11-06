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

Section BYTE.
  Variables (x1 x2 x3 x4 x6 x7 x8 x9 x10 x16 x17 x18 x19 x20 x21 x22 x24 x27 x28 x29 x30 x31 : word).
  Variables (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (bs : list byte) (T FP Y0 Y1 : Z).
  #[local] Notation L := (Z.of_nat (length bs)).
  #[local] Notation Zw z := (Z_to_bv 64 z).
  Hypothesis TXT : bytes_at ASEGS m T bs.
  Hypothesis HL : (1 <= L <= 128)%Z.
  Hypothesis HT : (6529024 <= T <= 140737488355072)%Z.
  Hypothesis SHT : shz ASEGS m (ASAN_B + Y0) (Y1 - Y0).
  Hypothesis HY : (8 * Y0 <= T /\ T + L <= 8 * Y1)%Z.
  Hypothesis HFP : (T <= FP <= T + L)%Z.

  #[local] Notation BST pc x5 x11 x12 x13 x14 x15 x26 :=
    (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 (Zw (T + L)) x24 (Zw ASAN_B) x26 x27
             x28 x29 x30 x31)
        F (Zw pc) fc None m (seg_rom ASEGS)) (only parsing).

  Definition byte_post : machine_state -> Prop := fun ms' =>
    exists y5 y11 y12 y13 y14 y15 y26 : word,
      ms' = BST 0x9326c y5 y11 y12 y13 y14 y15 y26 /\
      (FP <= bv_unsigned y26 <= T + L)%Z /\ digs bs (FP - T) (bv_unsigned y26 - T).

  #[using="HY"] Lemma tx_gran : forall A, (T <= A < T + L)%Z -> (ASAN_B + Y0 <= A / 8 + ASAN_B)%Z /\ (A / 8 + ASAN_B + 1 <= ASAN_B + Y0 + (Y1 - Y0))%Z.
  Proof. LiaFast.lf_pins (fun (HY : LiaFast.U) => LiaFast.u0). intros A HA. destruct HY as [Y1a Y2a]. Z.div_mod_to_equations. lia. Qed.

  (* [comment removed for export] *)
  #[using="Y0 Y1 TXT HL HT SHT HY HFP"] Lemma loopB : forall (n : nat) (k : Z) (x5 x14 x15 : word),
      (L - k <= Z.of_nat n)%Z -> (FP - T <= k < L)%Z -> digs bs (FP - T) k ->
      evt ASEGS byte_post (BST 0x93220 x5 (Zw (T + k)) (Zw 9) (Zw 10) x14 x15 (Zw (T + k))).
  Proof. LiaFast.lf_pins (fun (Y0 Y1 TXT HL HT SHT HY HFP : LiaFast.U) => LiaFast.u0).
    induction n as [|n IH]; intros k x5 x14 x15 Hn HK DG; [exfalso; lia|].
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
    step. (* [comment removed for export] *)
    if_cases Hd.
    - cond_cleanup Hd. clear Hd. apply evt_done.
      do 7 eexists. split; [reflexivity|]. rewrite unsigned_lit by lia. split; [lia|]. replace (T + k - T)%Z with k by lia. exact DG.
    - cond_cleanup Hd. pose proof (dig_yes_m _ Rk Hd) as D. clear Hd.
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
        apply evt_done. do 7 eexists. split; [reflexivity|]. rewrite unsigned_lit by lia.
        split; [lia|]. replace (T + L - T)%Z with (k + 1)%Z by lia. apply digs_snoc; assumption.
  Qed.

  (* [comment removed for export] *)
  #[using="Y0 Y1 TXT HL HT SHT HY HFP"] Lemma blockB : forall (k : Z) (x5 x11 x12 x13 x14 x15 : word),
      (FP - T <= k <= L)%Z -> digs bs (FP - T) k ->
      evt ASEGS byte_post (BST 0x93210 x5 x11 x12 x13 x14 x15 (Zw (T + k))).
  Proof. LiaFast.lf_pins (fun (Y0 Y1 TXT HL HT SHT HY HFP : LiaFast.U) => LiaFast.u0).
    intros k x5 x11 x12 x13 x14 x15 HK DG.
    rewrite ?(unsigned_lit (T + k)%Z), ?(unsigned_lit (T + L)%Z) by lia.
    step. (* [comment removed for export] *)
    if_cases Hend.
    { cond_cleanup Hend. apply evt_done. do 7 eexists. split; [reflexivity|]. rewrite unsigned_lit by lia. split; [lia|].
      replace (T + k - T)%Z with k by lia. exact DG. }
    cond_cleanup Hend.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    goto (eapply (loopB (Datatypes.S (Z.to_nat (L - k))) k)); [lia | lia | exact DG].
  Qed.
End BYTE.
