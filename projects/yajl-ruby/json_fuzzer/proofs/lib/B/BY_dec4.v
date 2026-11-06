(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import InitMem SysStep Arr Cells.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.MS Require Import MallocRep.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Spec Require Import Prelim YajlBase YajlLeaf YajlBuf YajlLex YajlParser YajlFactsBuf YajlDecode YajlFactsBits.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.R Require Import RYajlRep RY_lib RY_decode1.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.LibA Require Import StepA StepA2 SysStepA AImages Shadow.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.B Require Import BY_ubkit B_iface BI_shadow BYajlRep BYajl_iface BY_hand BY_dec1 BY_dec2 BY_dec3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import RunCeiling.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Ltac aceil := first [pose proof alloc_ceiling_range as CEILB | idtac].
Section RC__1.
Context {RC__ : OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib.RunCeiling.RunCeiling}.
Definition ADP_T0 : Z := 0x8b9ac.     (* [comment removed for export] *)
Definition ADP_NULCK : Z := 0x8b9ac.  (* [comment removed for export] *)
Definition ADP_RET3 : Z := 0x8ba0c.   (* [comment removed for export] *)

End RC__1.
Ltac kill K := exfalso; revert K; unfold wz; rewrite ?unsigned_lit by lia;
  try (change 18446744073709551615 with (Z.ones 64); rewrite ?Z.land_ones by lia; rewrite ?Z.mod_small by lia); lia.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section RC__2.
Context {RC__ : OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib.RunCeiling.RunCeiling}.
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma afield6 : forall cp, 0 <= cp < 2^64 -> (Z.land (cp ≪ 52) 18446744073709551615) ≫ 58 = Z.land (cp ≫ 6) 63.
Proof. aceil.
  intros cp H. change 18446744073709551615 with (Z.ones 64). rewrite Z.land_ones by lia.
  rewrite Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia. apply RY_decode1.bits6_52. lia.
Qed.
Lemma afield12 : forall cp, 0 <= cp < 2^64 -> (Z.land (cp ≪ 46) 18446744073709551615) ≫ 58 = Z.land (cp ≫ 12) 63.
Proof. aceil.
  intros cp H. change 18446744073709551615 with (Z.ones 64). rewrite Z.land_ones by lia.
  rewrite Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia. apply RY_decode1.bits12_46. lia.
Qed.

(* [comment removed for export] *)
Definition u8out (cp : Z) (ubs : list byte) : list byte :=
  zbytes (RY_decode1.u8enc cp) ++ Z_to_bv 8 0 :: skipn (S (length (RY_decode1.u8enc cp))) ubs.

End RC__2.
Ltac cellnorm FF := match goal with H : rw_cells bsegs _ (FF + 32) _ |- _ => try rewrite !Z.mod_small in H by lia end.
Ltac u8fin MU WM UE :=
  apply evtA_done;
  lazymatch goal with X : mem_inv bsegs ?mx |- _ => eexists _, _, _, _, mx end;
  split; [exact MU|]; split; [exact WM|]; split; [assumption|];
  split; [ lazymatch goal with U : rw_cells bsegs _ (?FF + 32) _ |- _ =>
             eapply rw_cells_reshape; [exact U | unfold u8out; rewrite UE; cbn; repeat split; reflexivity | unfold u8out; rewrite UE; reflexivity | reflexivity] end |];
  split; [assumption|]; split; [assumption|]; left; split; [lia | reflexivity].

(* [comment removed for export] *)
(* [comment removed for export] *)
Section RC__3.
Context {RC__ : OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib.RunCeiling.RunCeiling}.
Lemma seg_cp : forall (P : acc -> Prop) (rav sp gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s7 s11 t3 t4 t5 t6 : word) (w0 w96 sur cpw : word) (ubs : list byte)
    (F : bvmap 5 word) (fc : bv 32) (m : mem) (SQ FF B S n e cp : Z),
  mem_inv bsegs m ->
  rw_cells bsegs m SQ (dspill w0 w96 FF sur cpw) -> alloc_ceiling <= SQ -> SQ + 240 <= 2^47 ->
  rw_cells bsegs m (FF + 32) [CB 5 ubs] ->
  rw_cells bsegs m (FF / 8 + 2147450880) fsh_in ->
  (6303744 <= FF /\ (FF + 64 <= 2147446784 \/ 17594333495296 <= FF)) -> FF + 64 <= alloc_ceiling -> FF mod 64 = 0 ->
  0 <= cp < 65536 -> 0 < S < 2^47 ->
  pol P SQ (SQ + 120) -> pol P FF (FF + 64) -> pol P (FF / 8 + 2147450880) (FF / 8 + 2147450880 + 8) ->
  evtA bsegs P (fun ms' => exists (x0 x1 x2 x3 : word) (m' : mem),
       munch [(FF + 32, FF + 37)] m m' /\ wmono bsegs m m' /\ mem_inv bsegs m'
       /\ rw_cells bsegs m' (FF + 32) [CB 5 (u8out cp ubs)]
       /\ rw_cells bsegs m' SQ (dspill w0 w96 FF sur cpw) /\ rw_cells bsegs m' (FF / 8 + 2147450880) fsh_in
       /\ (  (cp <> 0 /\ ms' = MS (mkR rav (Z_to_bv 64 SQ) gp tp t0 t1 t2 sp (Z_to_bv 64 SQ) x0 x1 x2 x3 a4 a5 a6 a7
                      (Z_to_bv 64 (18446744073709551615 - S)) (Z_to_bv 64 S) (Z_to_bv 64 B) (Z_to_bv 64 n) (Z_to_bv 64 1) (Z_to_bv 64 (FF + 32)) (Z_to_bv 64 e) (Z_to_bv 64 (FF / 8 + 2147450880)) (Z_to_bv 64 2147450880) s11 t3 t4 t5 t6)
                     F (Z_to_bv 64 ADP_T0) fc None m' (seg_rom bsegs))
          \/ (cp = 0 /\ ms' = MS (mkR (Z_to_bv 64 ADP_RET3) (Z_to_bv 64 SQ) gp tp t0 t1 t2 sp (Z_to_bv 64 SQ) (Z_to_bv 64 B) (Z_to_bv 64 (FF + 32)) (Z_to_bv 64 1) a3 a4 a5 a6 a7
                      (Z_to_bv 64 (18446744073709551615 - S)) (Z_to_bv 64 S) (Z_to_bv 64 B) (Z_to_bv 64 n) (Z_to_bv 64 1) (Z_to_bv 64 (FF + 32)) (Z_to_bv 64 e) (Z_to_bv 64 (FF / 8 + 2147450880)) (Z_to_bv 64 2147450880) s11 t3 t4 t5 t6)
                     F (Z_to_bv 64 AY_BUF_APPEND) fc None m' (seg_rom bsegs))))
    (MS (mkR rav (Z_to_bv 64 SQ) gp tp t0 t1 t2 sp (Z_to_bv 64 SQ) (Z_to_bv 64 cp) a1 a2 a3 a4 a5 a6 a7
             (Z_to_bv 64 (18446744073709551615 - S)) (Z_to_bv 64 S) (Z_to_bv 64 B) (Z_to_bv 64 n) (Z_to_bv 64 1) s7 (Z_to_bv 64 e) (Z_to_bv 64 (FF / 8 + 2147450880)) (Z_to_bv 64 2147450880) s11 t3 t4 t5 t6)
        F (Z_to_bv 64 ADP_CP) fc None m (seg_rom bsegs)).
Proof. aceil.
  intros until cp. intros MI FR SQL SQH U5 FSH FF1 FF2 FF3 CPR SR PSTK PFF PFFS.
  unfold pol, ADP_CP, ADP_T0, ADP_RET3, AY_BUF_APPEND in *. unfold dspill in FR. unfold fsh_in, F1b, F3b in FSH.
  assert (SHFR : 2147450880 <= FF / 8 + 2147450880 /\ FF / 8 + 2147450880 + 8 <= 17594333495296) by (Z.div_mod_to_equations; lia).
  assert (LU : length ubs = 5%nat) by (destruct U5 as [[WF _] _]; cbn in WF; tauto).
  pose proof (munch_refl [(FF + 32, FF + 37)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
  destruct ubs as [|u0 [|u1 [|u2 [|u3 [|u4 [|? ?]]]]]]; try (cbn in LU; lia).
  eapply rw_cells_reshape with (cs' := [C1 u0; C1 u1; C1 u2; C1 u3; C1 u4]) in U5; [| cbn; repeat split; exact I| reflexivity| reflexivity].
  zstepA.                                                 (* [comment removed for export] *)
  zstepA. if_cases K1; zify_cond K1; rewrite ?unsigned_lit in K1 by lia.   (* [comment removed for export] *)
  - (* [comment removed for export] *)
    zstepA.                                               (* [comment removed for export] *)
    zstepA. zstepA. if_cases K2; zify_cond K2; rewrite ?unsigned_lit in K2 by lia.   (* [comment removed for export] *)
    + (* [comment removed for export] *)
      destruct (RY_decode1.u8enc_3 cp ltac:(lia)) as (UE & R0 & R1 & R2).
      pose proof (RY_decode1.shiftr_range cp 12 16 ltac:(lia) ltac:(lia)) as SR12. change (2 ^ (16 - 12)) with 16 in SR12.
      pose proof (RY_decode1.land63_range (cp ≫ 6) ltac:(apply Z.shiftr_nonneg; lia)) as L63b.
      pose proof (RY_decode1.land63_range cp ltac:(lia)) as L63.
      zstepA. rewrite ?(unsigned_lit cp) by lia.          (* [comment removed for export] *)
      zstepA. if_cases K3; zify_cond K3.                  (* [comment removed for export] *)
      { exfalso. apply K3. rewrite ?unsigned_lit by (rewrite Z.shiftr_div_pow2 by lia; split; [apply Z.div_pos; lia| apply Z.div_lt_upper_bound; lia]).
        rewrite Z.shiftr_div_pow2 by lia. apply Z.div_small. lia. }
      zstepA. rewrite ?(unsigned_lit cp) by lia.          (* [comment removed for export] *)
      zstepA. rewrite ?(unsigned_lit (cp ≫ 12)), ?RY_decode1.lead3 by lia.   (* [comment removed for export] *)
      zstepA. cellnorm FF.                                (* [comment removed for export] *)
      zstepA. ugd.                                        (* [comment removed for export] *)
      zstepA. rewrite ?(unsigned_lit cp) by lia.          (* [comment removed for export] *)
      zstepA. rewrite ?afield6 by lia.                    (* [comment removed for export] *)
      zstepA. rewrite ?(unsigned_lit (Z.land (cp ≫ 6) 63)) by lia.   (* [comment removed for export] *)
      zstepA. cellnorm FF.                                (* [comment removed for export] *)
      zstepA. ugd.                                        (* [comment removed for export] *)
      zstepA. rewrite ?(unsigned_lit cp) by lia.          (* [comment removed for export] *)
      zstepA. rewrite ?(unsigned_lit (Z.land cp 63)) by lia.          (* [comment removed for export] *)
      zstepA. cellnorm FF.                                (* [comment removed for export] *)
      zstepA. ugd.                                        (* [comment removed for export] *)
      zstepA. cellnorm FF.                                (* [comment removed for export] *)
      stepA.                                              (* [comment removed for export] *)
      u8fin MU WM UE.
    + (* [comment removed for export] *)
      destruct (RY_decode1.u8enc_2 cp ltac:(lia)) as (UE & R0 & R1).
      pose proof (RY_decode1.shiftr_range cp 6 11 ltac:(lia) ltac:(lia)) as SR6. change (2 ^ (11 - 6)) with 32 in SR6.
      pose proof (RY_decode1.land63_range cp ltac:(lia)) as L63.
      zstepA. rewrite ?(unsigned_lit cp) by lia.          (* [comment removed for export] *)
      zstepA. rewrite ?(unsigned_lit (cp ≫ 6)), ?RY_decode1.lead2 by lia.   (* [comment removed for export] *)
      zstepA. cellnorm FF.                                (* [comment removed for export] *)
      zstepA. ugd.                                        (* [comment removed for export] *)
      zstepA. rewrite ?(unsigned_lit cp) by lia.          (* [comment removed for export] *)
      zstepA. rewrite ?(unsigned_lit (Z.land cp 63)) by lia.          (* [comment removed for export] *)
      zstepA. cellnorm FF.                                (* [comment removed for export] *)
      zstepA. ugd.                                        (* [comment removed for export] *)
      zstepA. cellnorm FF.                                (* [comment removed for export] *)
      stepA.                                              (* [comment removed for export] *)
      u8fin MU WM UE.
  - (* [comment removed for export] *)
    zstepA.                                               (* [comment removed for export] *)
    zstepA. cellnorm FF.                                  (* [comment removed for export] *)
    zstepA. ugd.                                          (* [comment removed for export] *)
    zstepA. cellnorm FF.                                  (* [comment removed for export] *)
    zstepA. if_cases K2; zify_cond K2; rewrite ?unsigned_lit in K2 by lia.   (* [comment removed for export] *)
    + (* [comment removed for export] *)
      pose proof (RY_decode1.u8enc_1 cp ltac:(lia)) as UE.
      u8fin MU WM UE.
    + zstepA. stepA. zstepA. stepA.                       (* [comment removed for export] *)
      subst cp.
      apply evtA_done.
      lazymatch goal with X : mem_inv bsegs ?mx |- _ => exists (Z_to_bv 64 0), (Z_to_bv 64 0), (Z_to_bv 64 0), (Z_to_bv 64 0), mx end.
      split; [exact MU|]. split; [exact WM|]. split; [assumption|].
      split. { lazymatch goal with U : rw_cells bsegs _ (FF + 32) _ |- _ =>
               eapply rw_cells_reshape; [exact U | cbn; repeat split; reflexivity | reflexivity | reflexivity] end. }
      split; [assumption|]. split; [assumption|].
      right. split; [lia | reflexivity].
Qed.

Lemma afield18 : forall cp, 0 <= cp < 2^21 -> (Z.land (cp ≪ 46) 18446744073709551615) ≫ 58 = Z.land (cp ≫ 12) 63.
Proof. aceil. intros. apply afield12. lia. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma seg_4 : forall (P : acc -> Prop) (rav sp gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s11 t3 t4 t5 t6 : word) (w0 w96 sur cpw : word) (ubs : list byte)
    (F : bvmap 5 word) (fc : bv 32) (m : mem) (SQ FF B S n e cp : Z),
  mem_inv bsegs m ->
  rw_cells bsegs m SQ (dspill w0 w96 FF sur cpw) -> alloc_ceiling <= SQ -> SQ + 240 <= 2^47 ->
  rw_cells bsegs m (FF + 32) [CB 5 ubs] ->
  rw_cells bsegs m (FF / 8 + 2147450880) fsh_in ->
  (6303744 <= FF /\ (FF + 64 <= 2147446784 \/ 17594333495296 <= FF)) -> FF + 64 <= alloc_ceiling -> FF mod 64 = 0 ->
  65536 <= cp < 2097152 -> 0 < S < 2^47 ->
  pol P SQ (SQ + 120) -> pol P FF (FF + 64) -> pol P (FF / 8 + 2147450880) (FF / 8 + 2147450880 + 8) ->
  evtA bsegs P (fun ms' => exists (x0 x1 x2 x3 x4 : word) (m' : mem),
       ms' = MS (mkR rav (Z_to_bv 64 SQ) gp tp t0 t1 t2 sp (Z_to_bv 64 SQ) x0 x1 x2 x3 x4 a5 a6 a7
                      (Z_to_bv 64 (18446744073709551615 - S)) (Z_to_bv 64 S) (Z_to_bv 64 B) (Z_to_bv 64 n) (Z_to_bv 64 1) (Z_to_bv 64 (FF + 32)) (Z_to_bv 64 e) (Z_to_bv 64 (FF / 8 + 2147450880)) (Z_to_bv 64 2147450880) s11 t3 t4 t5 t6)
                     F (Z_to_bv 64 ADP_T0) fc None m' (seg_rom bsegs)
       /\ munch [(FF + 32, FF + 37)] m m' /\ wmono bsegs m m' /\ mem_inv bsegs m'
       /\ rw_cells bsegs m' (FF + 32) [CB 5 (u8out cp ubs)]
       /\ rw_cells bsegs m' SQ (dspill w0 w96 FF sur cpw) /\ rw_cells bsegs m' (FF / 8 + 2147450880) fsh_in)
    (MS (mkR rav (Z_to_bv 64 SQ) gp tp t0 t1 t2 sp (Z_to_bv 64 SQ) (Z_to_bv 64 cp) a1 a2 a3 a4 a5 a6 a7
             (Z_to_bv 64 (18446744073709551615 - S)) (Z_to_bv 64 S) (Z_to_bv 64 B) (Z_to_bv 64 n) (Z_to_bv 64 1) (Z_to_bv 64 (FF + 32)) (Z_to_bv 64 e) (Z_to_bv 64 (FF / 8 + 2147450880)) (Z_to_bv 64 2147450880) s11 t3 t4 t5 t6)
        F (Z_to_bv 64 ADP_J4) fc None m (seg_rom bsegs)).
Proof. aceil.
  intros until cp. intros MI FR SQL SQH U5 FSH FF1 FF2 FF3 CPR SR PSTK PFF PFFS.
  unfold pol, ADP_J4, ADP_T0 in *. unfold dspill in FR. unfold fsh_in, F1b, F3b in FSH.
  assert (SHFR : 2147450880 <= FF / 8 + 2147450880 /\ FF / 8 + 2147450880 + 8 <= 17594333495296) by (Z.div_mod_to_equations; lia).
  assert (LU : length ubs = 5%nat) by (destruct U5 as [[WF _] _]; cbn in WF; tauto).
  pose proof (munch_refl [(FF + 32, FF + 37)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
  destruct ubs as [|u0 [|u1 [|u2 [|u3 [|u4 [|? ?]]]]]]; try (cbn in LU; lia).
  eapply rw_cells_reshape with (cs' := [C1 u0; C1 u1; C1 u2; C1 u3; C1 u4]) in U5; [| cbn; repeat split; exact I| reflexivity| reflexivity].
  destruct (RY_decode1.u8enc_4 cp ltac:(lia)) as (UE & R0 & R1 & R2 & R3).
  pose proof (RY_decode1.shiftr_range cp 18 21 ltac:(lia) ltac:(lia)) as SR18. change (2 ^ (21 - 18)) with 8 in SR18.
  pose proof (RY_decode1.land63_range cp ltac:(lia)) as L63.
  pose proof (RY_decode1.land63_range (cp ≫ 6) ltac:(apply Z.shiftr_nonneg; lia)) as L63b.
  pose proof (RY_decode1.land63_range (cp ≫ 12) ltac:(apply Z.shiftr_nonneg; lia)) as L63c.
  zstepA. rewrite ?(unsigned_lit cp) by lia.          (* [comment removed for export] *)
  zstepA. rewrite ?(unsigned_lit (cp ≫ 18)), ?RY_decode1.lead4 by lia.   (* [comment removed for export] *)
  zstepA. cellnorm FF.                                (* [comment removed for export] *)
  zstepA. ugd.                                        (* [comment removed for export] *)
  zstepA. rewrite ?(unsigned_lit cp) by lia.          (* [comment removed for export] *)
  zstepA. rewrite ?afield18 by lia.                   (* [comment removed for export] *)
  zstepA. rewrite ?(unsigned_lit (Z.land (cp ≫ 12) 63)) by lia.  (* [comment removed for export] *)
  zstepA. cellnorm FF.                                (* [comment removed for export] *)
  zstepA. ugd.                                        (* [comment removed for export] *)
  zstepA. rewrite ?(unsigned_lit cp) by lia.          (* [comment removed for export] *)
  zstepA. rewrite ?afield6 by lia.                    (* [comment removed for export] *)
  zstepA. rewrite ?(unsigned_lit (Z.land (cp ≫ 6) 63)) by lia.   (* [comment removed for export] *)
  zstepA. cellnorm FF.                                (* [comment removed for export] *)
  zstepA. ugd.                                        (* [comment removed for export] *)
  zstepA. rewrite ?(unsigned_lit cp) by lia.          (* [comment removed for export] *)
  zstepA. rewrite ?(unsigned_lit (Z.land cp 63)) by lia.          (* [comment removed for export] *)
  zstepA. cellnorm FF.                                (* [comment removed for export] *)
  zstepA. ugd.                                        (* [comment removed for export] *)
  zstepA. cellnorm FF.                                (* [comment removed for export] *)
  stepA.                                              (* [comment removed for export] *)
  apply evtA_done. lazymatch goal with X : mem_inv bsegs ?mx |- _ => eexists _, _, _, _, _, mx end.
  split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [assumption|].
  split. { lazymatch goal with U : rw_cells bsegs _ (FF + 32) _ |- _ =>
           eapply rw_cells_reshape; [exact U | unfold u8out; rewrite UE; cbn; repeat split; reflexivity | unfold u8out; rewrite UE; reflexivity | reflexivity] end. }
  split; assumption.
Qed.
End RC__3.
