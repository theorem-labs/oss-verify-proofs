(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
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
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.A Require Import A_iface AI_shadow AYajlRep AYajl_iface AY_hand AY_dec1 AY_dec2 AY_dec3.
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
Definition ADP_T0 : Z := 0x8af38.     (* [comment removed for export] *)
Definition ADP_NULCK : Z := 0x8af20.
Definition ADP_RET3 : Z := 0x8ae50.   (* [comment removed for export] *)

End RC__1.
Ltac kill K := exfalso; revert K; unfold wz; rewrite ?unsigned_lit by lia;
  try (change 18446744073709551615 with (Z.ones 64); rewrite ?Z.land_ones by lia; rewrite ?Z.mod_small by lia); lia.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section RC__2.
Context {RC__ : OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib.RunCeiling.RunCeiling}.
Lemma seg_nulck : forall (P : acc -> Prop) (rav sp gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s2 s7 s9 s11 t3 t4 t5 t6 : word) (w0 w16 sur cpw : word) (u0 u1 u2 u3 u4 : byte)
    (F : bvmap 5 word) (fc : bv 32) (m : mem) (SQ FF B S n k : Z),
  mem_inv asegs m ->
  rw_cells asegs m SQ (dspill w0 w16 FF sur cpw) -> alloc_ceiling <= SQ -> SQ + 272 <= 2^47 ->
  rw_cells asegs m (FF + 32) [C1 u0; C1 u1; C1 u2; C1 u3; C1 u4] ->
  rw_cells asegs m (FF / 8 + 2147450880) fsh_in ->
  (6303744 <= FF /\ (FF + 64 <= 2147446784 \/ 17594333495296 <= FF)) -> FF + 64 <= alloc_ceiling -> FF mod 64 = 0 ->
  (k = 2 \/ k = 3 \/ k = 4) ->
  pol P SQ (SQ + 152) -> pol P FF (FF + 64) -> pol P (FF / 8 + 2147450880) (FF / 8 + 2147450880 + 8) ->
  evtA asegs P (fun ms' => exists (x1 x2 : word) (m' : mem),
       ms' = MS (mkR rav (Z_to_bv 64 SQ) gp tp t0 t1 t2 sp (Z_to_bv 64 SQ) (Z_to_bv 64 (FF + 32 + k)) x1 x2 a3 a4 a5 a6 a7
                      s2 (Z_to_bv 64 S) (Z_to_bv 64 B) (Z_to_bv 64 n) (Z_to_bv 64 92) (Z_to_bv 64 (FF + 32)) (Z_to_bv 64 2147450880) s9 (Z_to_bv 64 (FF / 8 + 2147450880)) s11 t3 t4 t5 t6)
                     F (Z_to_bv 64 ADP_T0) fc None m' (seg_rom asegs)
       /\ munch [(FF + 32, FF + 37)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
       /\ rw_cells asegs m' (FF + 32) [C1 u0; C1 u1; C1 (if k =? 2 then Z_to_bv 8 0 else u2); C1 (if k =? 3 then Z_to_bv 8 0 else u3); C1 (if k =? 4 then Z_to_bv 8 0 else u4)]
       /\ rw_cells asegs m' SQ (dspill w0 w16 FF sur cpw) /\ rw_cells asegs m' (FF / 8 + 2147450880) fsh_in)
    (MS (mkR rav (Z_to_bv 64 SQ) gp tp t0 t1 t2 sp (Z_to_bv 64 SQ) (Z_to_bv 64 (FF + 32 + k)) a1 a2 a3 a4 a5 a6 a7
             s2 (Z_to_bv 64 S) (Z_to_bv 64 B) (Z_to_bv 64 n) (Z_to_bv 64 92) s7 (Z_to_bv 64 2147450880) s9 (Z_to_bv 64 (FF / 8 + 2147450880)) s11 t3 t4 t5 t6)
        F (Z_to_bv 64 ADP_NULCK) fc None m (seg_rom asegs)).
Proof. aceil.
  intros until k. intros MI FR SQL SQH U5 FSH FF1 FF2 FF3 HK PSTK PFF PFFS.
  unfold pol, ADP_NULCK, ADP_T0, fsh_in, F1b, F3b, dspill in *.
  assert (SHFR : 2147450880 <= FF / 8 + 2147450880 /\ FF / 8 + 2147450880 + 8 <= 17594333495296) by (Z.div_mod_to_equations; lia).
  pose proof (munch_refl [(FF + 32, FF + 37)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  zstepA. shadow_addr.                                    (* [comment removed for export] *)
  replace ((FF + 32 + k) / 8) with (FF / 8 + 4) by (clear -CEILB FF3 HK; Z.div_mod_to_equations; lia).
  zstepA.                                                 (* [comment removed for export] *)
  zstepA. rewrite (sxb_small 5) by lia.                  (* [comment removed for export] *)
  zstepA. if_cases K0; zify_cond K0; [| kill K0].         (* [comment removed for export] *)
  zstepA.                                                 (* [comment removed for export] *)
  change 7 with (Z.ones 3). rewrite ?Z.land_ones by lia. change (2^3) with 8.
  replace ((FF + 32 + k) mod 8) with k by (clear -CEILB FF3 HK; Z.div_mod_to_equations; lia).
  zstepA. if_cases K1; zify_cond K1; [exfalso; revert K1; rewrite ?unsigned_lit, ?signed_lit_small by lia; lia|].   (* [comment removed for export] *)
  stepA.                                                  (* [comment removed for export] *)
  destruct HK as [-> |[-> | ->]]; cbn [Z.eqb Pos.eqb].
  all: zstepA.                                            (* [comment removed for export] *)
  all: zstepA.                                            (* [comment removed for export] *)
  all: apply evtA_done; lazymatch goal with |- exists x1 x2 m', MS _ _ _ _ _ ?mx _ = _ /\ _ => eexists _, _, mx end;
       split; [reflexivity|]; split; [exact MU|]; split; [exact WM|]; split; [assumption|]; split; [assumption|]; split; assumption.
Qed.

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
Ltac u8fin MU WM :=
  apply evtA_done;
  lazymatch goal with |- exists x0 x1 x2 x3 m', _ /\ _ /\ mem_inv asegs m' /\ _ =>
    lazymatch goal with X : mem_inv asegs ?mx |- _ => eexists _, _, _, _, mx end end;
  split; [exact MU|]; split; [exact WM|]; split; [assumption|];
  split; [| split; [assumption|]; split; [assumption|]].

(* [comment removed for export] *)
(* [comment removed for export] *)
Section RC__3.
Context {RC__ : OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib.RunCeiling.RunCeiling}.
Lemma seg_cp : forall (P : acc -> Prop) (rav sp gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s7 s11 t3 t4 t5 t6 : word) (w0 w16 sur cpw : word) (ubs : list byte)
    (F : bvmap 5 word) (fc : bv 32) (m : mem) (SQ FF B S n e cp : Z),
  mem_inv asegs m ->
  rw_cells asegs m SQ (dspill w0 w16 FF sur cpw) -> alloc_ceiling <= SQ -> SQ + 272 <= 2^47 ->
  rw_cells asegs m (FF + 32) [CB 5 ubs] ->
  rw_cells asegs m (FF / 8 + 2147450880) fsh_in ->
  (6303744 <= FF /\ (FF + 64 <= 2147446784 \/ 17594333495296 <= FF)) -> FF + 64 <= alloc_ceiling -> FF mod 64 = 0 ->
  0 <= cp < 65536 ->
  pol P SQ (SQ + 152) -> pol P FF (FF + 64) -> pol P (FF / 8 + 2147450880) (FF / 8 + 2147450880 + 8) ->
  evtA asegs P (fun ms' => exists (x0 x1 x2 x3 : word) (m' : mem),
       munch [(FF + 32, FF + 37)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
       /\ rw_cells asegs m' (FF + 32) [CB 5 (u8out cp ubs)]
       /\ rw_cells asegs m' SQ (dspill w0 w16 FF sur cpw) /\ rw_cells asegs m' (FF / 8 + 2147450880) fsh_in
       /\ (  (cp <> 0 /\ ms' = MS (mkR rav (Z_to_bv 64 SQ) gp tp t0 t1 t2 sp (Z_to_bv 64 SQ) x0 x1 x2 x3 a4 a5 a6 a7
                      (Z_to_bv 64 e) (Z_to_bv 64 S) (Z_to_bv 64 B) (Z_to_bv 64 n) (Z_to_bv 64 92) (Z_to_bv 64 (FF + 32)) (Z_to_bv 64 2147450880) (Z_to_bv 64 cp) (Z_to_bv 64 (FF / 8 + 2147450880)) s11 t3 t4 t5 t6)
                     F (Z_to_bv 64 ADP_T0) fc None m' (seg_rom asegs))
          \/ (cp = 0 /\ ms' = MS (mkR (Z_to_bv 64 ADP_RET3) (Z_to_bv 64 SQ) gp tp t0 t1 t2 sp (Z_to_bv 64 SQ) (Z_to_bv 64 B) (Z_to_bv 64 (FF + 32)) (Z_to_bv 64 1) a3 a4 a5 a6 a7
                      (Z_to_bv 64 e) (Z_to_bv 64 S) (Z_to_bv 64 B) (Z_to_bv 64 n) (Z_to_bv 64 92) (Z_to_bv 64 (FF + 32)) (Z_to_bv 64 2147450880) (Z_to_bv 64 cp) (Z_to_bv 64 (FF / 8 + 2147450880)) s11 t3 t4 t5 t6)
                     F (Z_to_bv 64 AY_BUF_APPEND) fc None m' (seg_rom asegs))))
    (MS (mkR rav (Z_to_bv 64 SQ) gp tp t0 t1 t2 sp (Z_to_bv 64 SQ) a0 a1 a2 a3 a4 a5 a6 a7
             (Z_to_bv 64 e) (Z_to_bv 64 S) (Z_to_bv 64 B) (Z_to_bv 64 n) (Z_to_bv 64 92) s7 (Z_to_bv 64 2147450880) (Z_to_bv 64 cp) (Z_to_bv 64 (FF / 8 + 2147450880)) s11 t3 t4 t5 t6)
        F (Z_to_bv 64 ADP_CP) fc None m (seg_rom asegs)).
Proof. aceil.
  intros until cp. intros MI FR SQL SQH U5 FSH FF1 FF2 FF3 CPR PSTK PFF PFFS.
  unfold pol, ADP_CP, ADP_T0, ADP_RET3, AY_BUF_APPEND, dspill, fsh_in, F1b, F3b in *.
  assert (SHFR : 2147450880 <= FF / 8 + 2147450880 /\ FF / 8 + 2147450880 + 8 <= 17594333495296) by (Z.div_mod_to_equations; lia).
  assert (LU : length ubs = 5%nat) by (destruct U5 as [[WF _] _]; cbn in WF; tauto).
  pose proof (munch_refl [(FF + 32, FF + 37)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  destruct ubs as [|u0 [|u1 [|u2 [|u3 [|u4 [|? ?]]]]]]; try (cbn in LU; lia).
  eapply rw_cells_reshape with (cs' := [C1 u0; C1 u1; C1 u2; C1 u3; C1 u4]) in U5; [| cbn; repeat split; exact I| reflexivity| reflexivity].
  pose proof (RY_decode1.land63_range cp ltac:(lia)) as L63.
  Ltac cellnorm FF := match goal with H : rw_cells asegs _ (FF + 32) _ |- _ => rewrite !Z.mod_small in H by lia end.
  Ltac nulck k PSTK PFF PFFS SQ FF w0 w16 sur cpw :=
    lazymatch goal with H : rw_cells asegs ?mx SQ ?cs |- _ => change (rw_cells asegs mx SQ cs) with (rw_cells asegs mx SQ (dspill w0 w16 FF sur cpw)) in H end;
    lazymatch goal with H : rw_cells asegs ?mx (FF / 8 + 2147450880) ?cs |- _ => change (rw_cells asegs mx (FF / 8 + 2147450880) cs) with (rw_cells asegs mx (FF / 8 + 2147450880) fsh_in) in H end;
    eapply evtA_cut;
    [ eapply (seg_nulck _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ k);
      [ assumption | eassumption | lia | lia | eassumption | assumption | lia | lia | lia | lia
      | exact PSTK | exact PFF | exact PFFS ]
    | ].
  zstepA.                                                 (* [comment removed for export] *)
  zstepA. if_cases K1; zify_cond K1; rewrite ?unsigned_lit in K1 by lia.   (* [comment removed for export] *)
  - (* [comment removed for export] *)
    zstepA. zstepA. if_cases K2; zify_cond K2; rewrite ?unsigned_lit in K2 by lia.   (* [comment removed for export] *)
    + (* [comment removed for export] *)
      destruct (RY_decode1.u8enc_3 cp ltac:(lia)) as (UE & R0 & R1 & R2).
      pose proof (RY_decode1.shiftr_range cp 12 16 ltac:(lia) ltac:(lia)) as SR12. change (2 ^ (16 - 12)) with 16 in SR12.
      pose proof (RY_decode1.land63_range (cp ≫ 6) ltac:(apply Z.shiftr_nonneg; lia)) as L63b.
      zstepA. rewrite ?(unsigned_lit cp) by lia.          (* [comment removed for export] *)
      zstepA. if_cases K3; zify_cond K3.                  (* [comment removed for export] *)
      { exfalso. apply K3. rewrite ?unsigned_lit by (rewrite Z.shiftr_div_pow2 by lia; split; [apply Z.div_pos; lia| apply Z.div_lt_upper_bound; lia]).
        rewrite Z.shiftr_div_pow2 by lia. apply Z.div_small. lia. }
      zstepA. rewrite ?(unsigned_lit cp) by lia.          (* [comment removed for export] *)
      zstepA. rewrite ?(unsigned_lit cp) by lia.          (* [comment removed for export] *)
      zstepA. rewrite ?(unsigned_lit cp) by lia.          (* [comment removed for export] *)
      zstepA. rewrite ?(unsigned_lit (cp ≫ 12)), ?RY_decode1.lead3 by lia.   (* [comment removed for export] *)
      zstepA. rewrite ?afield6 by lia.                    (* [comment removed for export] *)
      zstepA. rewrite ?(unsigned_lit (Z.land cp 63)) by lia.          (* [comment removed for export] *)
      zstepA. rewrite ?(unsigned_lit (Z.land (cp ≫ 6) 63)) by lia.   (* [comment removed for export] *)
      zstepA.                                             (* [comment removed for export] *)
      zstepA. zstepA. zstepA.                             (* [comment removed for export] *)
      cellnorm FF.
      zstepA.                                             (* [comment removed for export] *)
      stepA.                                              (* [comment removed for export] *)
      replace (FF + 35) with (FF + 32 + 3) by lia.
      nulck 3 PSTK PFF PFFS SQ FF w0 w16 sur cpw.
      cbv beta. intros ms2 (x1 & x2 & m2 & -> & MU2 & WM2 & MI2 & U52 & FR2 & FSH2). cbn [Z.eqb Pos.eqb] in U52.
      apply evtA_done. eexists _, _, _, _, m2.
      split; [eapply munch_trans; [exact MU | exact MU2] |].
      split; [eapply wmono_trans; [exact WM | exact WM2] |].
      split; [exact MI2|].
      split. { eapply rw_cells_reshape; [exact U52 | unfold u8out; rewrite UE; cbn; repeat split; reflexivity | unfold u8out; rewrite UE; reflexivity | reflexivity]. }
      split; [replace (FF + 32 + 3) with (FF + 35) by lia; exact FR2|]. split; [exact FSH2|].
      left. split; [lia | reflexivity].
    + (* [comment removed for export] *)
      destruct (RY_decode1.u8enc_2 cp ltac:(lia)) as (UE & R0 & R1).
      pose proof (RY_decode1.shiftr_range cp 6 11 ltac:(lia) ltac:(lia)) as SR6. change (2 ^ (11 - 6)) with 32 in SR6.
      zstepA. rewrite ?(unsigned_lit cp) by lia.          (* [comment removed for export] *)
      zstepA. rewrite ?(unsigned_lit cp) by lia.          (* [comment removed for export] *)
      zstepA. rewrite ?(unsigned_lit (cp ≫ 6)), ?RY_decode1.lead2 by lia.   (* [comment removed for export] *)
      zstepA. rewrite ?(unsigned_lit (Z.land cp 63)) by lia.          (* [comment removed for export] *)
      zstepA.                                             (* [comment removed for export] *)
      zstepA. zstepA.                                     (* [comment removed for export] *)
      cellnorm FF.
      zstepA.                                             (* [comment removed for export] *)
      stepA.                                              (* [comment removed for export] *)
      replace (FF + 34) with (FF + 32 + 2) by lia.
      nulck 2 PSTK PFF PFFS SQ FF w0 w16 sur cpw.
      cbv beta. intros ms2 (x1 & x2 & m2 & -> & MU2 & WM2 & MI2 & U52 & FR2 & FSH2). cbn [Z.eqb Pos.eqb] in U52.
      apply evtA_done. eexists _, _, _, _, m2.
      split; [eapply munch_trans; [exact MU | exact MU2] |].
      split; [eapply wmono_trans; [exact WM | exact WM2] |].
      split; [exact MI2|].
      split. { eapply rw_cells_reshape; [exact U52 | unfold u8out; rewrite UE; cbn; repeat split; reflexivity | unfold u8out; rewrite UE; reflexivity | reflexivity]. }
      split; [replace (FF + 32 + 2) with (FF + 34) by lia; exact FR2|]. split; [exact FSH2|].
      left. split; [lia | reflexivity].
  - (* [comment removed for export] *)
    zstepA.                                               (* [comment removed for export] *)
    zstepA.                                               (* [comment removed for export] *)
    zstepA.                                               (* [comment removed for export] *)
    cellnorm FF.
    zstepA. if_cases K2; zify_cond K2; rewrite ?unsigned_lit in K2 by lia.   (* [comment removed for export] *)
    + (* [comment removed for export] *)
      pose proof (RY_decode1.u8enc_1 cp ltac:(lia)) as UE.
      apply evtA_done.
      lazymatch goal with X : mem_inv asegs ?mx |- _ => eexists _, _, _, _, mx end.
      split; [exact MU|]. split; [exact WM|]. split; [assumption|].
      split. { lazymatch goal with U : rw_cells asegs _ (FF + 32) _ |- _ =>
               eapply rw_cells_reshape; [exact U | unfold u8out; rewrite UE; cbn; repeat split; reflexivity | unfold u8out; rewrite UE; reflexivity | reflexivity] end. }
      split; [assumption|]. split; [assumption|].
      left. split; [lia | reflexivity].
    + zstepA. stepA. zstepA. stepA.                       (* [comment removed for export] *)
      subst cp.
      apply evtA_done.
      lazymatch goal with X : mem_inv asegs ?mx |- _ => exists (Z_to_bv 64 0), (Z_to_bv 64 0), (Z_to_bv 64 0), (Z_to_bv 64 0), mx end.
      split; [exact MU|]. split; [exact WM|]. split; [assumption|].
      split. { lazymatch goal with U : rw_cells asegs _ (FF + 32) _ |- _ =>
               eapply rw_cells_reshape; [exact U | cbn; repeat split; reflexivity | reflexivity | reflexivity] end. }
      split; [assumption|]. split; [assumption|].
      right. split; [lia | reflexivity].
Qed.

Lemma afield18 : forall cp, 0 <= cp < 2^21 -> (Z.land (cp ≪ 46) 18446744073709551615) ≫ 58 = Z.land (cp ≫ 12) 63.
Proof. aceil. intros. apply afield12. lia. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma seg_4 : forall (P : acc -> Prop) (rav sp gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s7 s11 t3 t4 t5 t6 : word) (w0 w16 sur cpw : word) (ubs : list byte)
    (F : bvmap 5 word) (fc : bv 32) (m : mem) (SQ FF B S n e cp : Z),
  mem_inv asegs m ->
  rw_cells asegs m SQ (dspill w0 w16 FF sur cpw) -> alloc_ceiling <= SQ -> SQ + 272 <= 2^47 ->
  rw_cells asegs m (FF + 32) [CB 5 ubs] ->
  rw_cells asegs m (FF / 8 + 2147450880) fsh_in ->
  (6303744 <= FF /\ (FF + 64 <= 2147446784 \/ 17594333495296 <= FF)) -> FF + 64 <= alloc_ceiling -> FF mod 64 = 0 ->
  65536 <= cp < 2097152 ->
  pol P SQ (SQ + 152) -> pol P FF (FF + 64) -> pol P (FF / 8 + 2147450880) (FF / 8 + 2147450880 + 8) ->
  evtA asegs P (fun ms' => exists (x0 x1 x2 x3 x4 : word) (m' : mem),
       ms' = MS (mkR rav (Z_to_bv 64 SQ) gp tp t0 t1 t2 sp (Z_to_bv 64 SQ) x0 x1 x2 x3 x4 a5 a6 a7
                      (Z_to_bv 64 e) (Z_to_bv 64 S) (Z_to_bv 64 B) (Z_to_bv 64 n) (Z_to_bv 64 92) (Z_to_bv 64 (FF + 32)) (Z_to_bv 64 2147450880) (Z_to_bv 64 cp) (Z_to_bv 64 (FF / 8 + 2147450880)) s11 t3 t4 t5 t6)
                     F (Z_to_bv 64 ADP_T0) fc None m' (seg_rom asegs)
       /\ munch [(FF + 32, FF + 37)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
       /\ rw_cells asegs m' (FF + 32) [CB 5 (u8out cp ubs)]
       /\ rw_cells asegs m' SQ (dspill w0 w16 FF sur cpw) /\ rw_cells asegs m' (FF / 8 + 2147450880) fsh_in)
    (MS (mkR rav (Z_to_bv 64 SQ) gp tp t0 t1 t2 sp (Z_to_bv 64 SQ) a0 a1 a2 a3 a4 a5 a6 a7
             (Z_to_bv 64 e) (Z_to_bv 64 S) (Z_to_bv 64 B) (Z_to_bv 64 n) (Z_to_bv 64 92) s7 (Z_to_bv 64 2147450880) (Z_to_bv 64 cp) (Z_to_bv 64 (FF / 8 + 2147450880)) s11 t3 t4 t5 t6)
        F (Z_to_bv 64 ADP_J4) fc None m (seg_rom asegs)).
Proof. aceil.
  intros until cp. intros MI FR SQL SQH U5 FSH FF1 FF2 FF3 CPR PSTK PFF PFFS.
  unfold pol, ADP_J4, ADP_T0 in *. unfold dspill in FR. unfold fsh_in, F1b, F3b in FSH.
  assert (SHFR : 2147450880 <= FF / 8 + 2147450880 /\ FF / 8 + 2147450880 + 8 <= 17594333495296) by (Z.div_mod_to_equations; lia).
  assert (LU : length ubs = 5%nat) by (destruct U5 as [[WF _] _]; cbn in WF; tauto).
  pose proof (munch_refl [(FF + 32, FF + 37)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  destruct ubs as [|u0 [|u1 [|u2 [|u3 [|u4 [|? ?]]]]]]; try (cbn in LU; lia).
  eapply rw_cells_reshape with (cs' := [C1 u0; C1 u1; C1 u2; C1 u3; C1 u4]) in U5; [| cbn; repeat split; exact I| reflexivity| reflexivity].
  destruct (RY_decode1.u8enc_4 cp ltac:(lia)) as (UE & R0 & R1 & R2 & R3).
  pose proof (RY_decode1.shiftr_range cp 18 21 ltac:(lia) ltac:(lia)) as SR18. change (2 ^ (21 - 18)) with 8 in SR18.
  pose proof (RY_decode1.land63_range cp ltac:(lia)) as L63.
  pose proof (RY_decode1.land63_range (cp ≫ 6) ltac:(apply Z.shiftr_nonneg; lia)) as L63b.
  pose proof (RY_decode1.land63_range (cp ≫ 12) ltac:(apply Z.shiftr_nonneg; lia)) as L63c.
  zstepA. rewrite ?(unsigned_lit cp) by lia.          (* [comment removed for export] *)
  zstepA. rewrite ?(unsigned_lit cp) by lia.          (* [comment removed for export] *)
  zstepA. rewrite ?(unsigned_lit cp) by lia.          (* [comment removed for export] *)
  zstepA. rewrite ?(unsigned_lit cp) by lia.          (* [comment removed for export] *)
  zstepA. rewrite ?(unsigned_lit (cp ≫ 18)), ?RY_decode1.lead4 by lia.   (* [comment removed for export] *)
  zstepA. rewrite ?afield18 by lia.                   (* [comment removed for export] *)
  zstepA. rewrite ?afield6 by lia.                    (* [comment removed for export] *)
  zstepA. rewrite ?(unsigned_lit (Z.land cp 63)) by lia.          (* [comment removed for export] *)
  zstepA. rewrite ?(unsigned_lit (Z.land (cp ≫ 12) 63)) by lia.  (* [comment removed for export] *)
  zstepA. rewrite ?(unsigned_lit (Z.land (cp ≫ 6) 63)) by lia.   (* [comment removed for export] *)
  zstepA.                                             (* [comment removed for export] *)
  zstepA. zstepA. zstepA. zstepA.                     (* [comment removed for export] *)
  match goal with H : rw_cells asegs _ (FF + 32) _ |- _ => rewrite !Z.mod_small in H by lia end.
  zstepA.                                             (* [comment removed for export] *)
  stepA.                                              (* [comment removed for export] *)
  replace (FF + 36) with (FF + 32 + 4) by lia.
  lazymatch goal with H : rw_cells asegs ?mx SQ ?cs |- _ => change (rw_cells asegs mx SQ cs) with (rw_cells asegs mx SQ (dspill w0 w16 FF sur cpw)) in H end.
  lazymatch goal with H : rw_cells asegs ?mx (FF / 8 + 2147450880) ?cs |- _ => change (rw_cells asegs mx (FF / 8 + 2147450880) cs) with (rw_cells asegs mx (FF / 8 + 2147450880) fsh_in) in H end.
  eapply evtA_cut;
  [ eapply (seg_nulck _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ 4);
    [ assumption | eassumption | lia | lia | eassumption | assumption | lia | lia | lia | lia
    | exact PSTK | exact PFF | exact PFFS ]
  | ].
  cbv beta. intros ms2 (x1 & x2 & m2 & -> & MU2 & WM2 & MI2 & U52 & FR2 & FSH2). cbn [Z.eqb Pos.eqb] in U52.
  apply evtA_done. eexists _, _, _, _, _, m2.
  split; [reflexivity|].
  split; [eapply munch_trans; [exact MU | exact MU2] |].
  split; [eapply wmono_trans; [exact WM | exact WM2] |].
  split; [exact MI2|].
  split. { eapply rw_cells_reshape; [exact U52 | unfold u8out; rewrite UE; cbn; repeat split; reflexivity | unfold u8out; rewrite UE; reflexivity | reflexivity]. }
  split; [exact FR2 | exact FSH2].
Qed.
End RC__3.
