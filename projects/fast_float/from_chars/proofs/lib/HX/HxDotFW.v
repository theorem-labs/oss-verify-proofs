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

Section DOT.
  Variables (x1 x2 x3 x4 x5 x6 x7 x8 x9 x13 x14 x15 x16 x17 x18 x20 x21 x22 x25 x26 x27 x28 x29 x30 x31 : word).
  Variables (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (bs : list byte) (T IE Y0 Y1 T3 : Z).
  #[local] Notation L := (Z.of_nat (length bs)).
  #[local] Notation Zw z := (Z_to_bv 64 z).
  Hypothesis TXT : bytes_at ASEGS m T bs.
  Hypothesis HL : (1 <= L <= 128)%Z.
  Hypothesis HT : (6529024 <= T <= 140737488355072)%Z.
  Hypothesis SHT : shz ASEGS m (ASAN_B + Y0) (Y1 - Y0).
  Hypothesis HY : (8 * Y0 <= T /\ T + L <= 8 * Y1)%Z.
  Hypothesis HIE : (T <= IE <= T + L)%Z.
  Hypothesis HT3 : (T3 mod 256 = 46 /\ 0 <= T3 < 2 ^ 64)%Z.

  #[local] Notation DST pc x11 x12 :=
    (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 (Zw IE) x11 x12 x13 x14 x15 x16 x17 x18 (Zw ASAN_B) x20 x21 x22 (Zw (T + L)) (Zw T3) x25 x26 x27
             x28 x29 x30 x31)
        F (Zw pc) fc None m (seg_rom ASEGS)) (only parsing).

  Definition dot_post : machine_state -> Prop := fun ms' =>
    exists y11 y12 : word,
      ms' = DST 0x99e00 y11 y12 \/ (ms' = DST 0x99c88 y11 y12 /\ IE < T + L /\ tx bs (IE - T) = 46)%Z.

  #[using="Y0 Y1 TXT HL HT SHT HY HIE HT3"] Lemma blockD : forall (x11 x12 : word), evt ASEGS dot_post (DST 0x99c64 x11 x12).
  Proof. LiaFast.lf_pins (fun (Y0 Y1 TXT HL HT SHT HY HIE HT3 : LiaFast.U) => LiaFast.u0).
    intros x11 x12. pose proof (shz_bound _ _ _ _ SHT) as BT.
    rewrite ?(unsigned_lit IE), ?(unsigned_lit (T + L)%Z) by lia.
    step. (* [comment removed for export] *)
    if_cases Hend.
    { cond_cleanup Hend. apply evt_done. exists x11, x12. left. reflexivity. }
    cond_cleanup Hend.
    assert (G0 : (ASAN_B + Y0 <= IE / 8 + ASAN_B)%Z /\ (IE / 8 + ASAN_B + 1 <= ASAN_B + Y0 + (Y1 - Y0))%Z).
    { destruct HY as [Y1a Y2a]. Z.div_mod_to_equations. lia. }
    step. (* [comment removed for export] *) shr3.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    txt_rd TXT (IE - T)%Z RD. pose proof (tx_range bs (IE - T)) as R0.
    replace (T + (IE - T))%Z with IE in RD by lia.
    step. (* [comment removed for export] *)
    clear RD. fold_tx bs (IE - T)%Z.
    step. (* [comment removed for export] *)
    assert (ZB : Z_to_bv 64 (Z.land (bv_unsigned (Z_to_bv 64 T3)) 255) = Zw 46).
    { rewrite unsigned_lit by lia. change 255%Z with (2 ^ 8 - 1)%Z. rewrite zb_land_mask by lia.
      change (2 ^ 8)%Z with 256%Z. rewrite (proj1 HT3). reflexivity. }
    rewrite ZB.
    step. (* [comment removed for export] *)
    if_cases Hd.
    - cond_cleanup Hd. apply evt_done. do 2 eexists. left. reflexivity.
    - cond_cleanup Hd. apply evt_done. do 2 eexists. right. split; [reflexivity|]. split; [lia|].
      exact Hd.
  Qed.
End DOT.
