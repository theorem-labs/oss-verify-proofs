(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import Tac Image ZBridge SysStep SFModel SFW1_lemmas InitMem Arr.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import Images.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.R Require Import PortShim.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.U Require Import UMallocRep UMalloc_iface.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.R Require Import RYajlRep.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.U Require Import UYajlAlign UYajl_iface.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.R Require Import RY_lib.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Spec Require Import RawAlloc Prelim YajlBase YajlBuf YajlLex YajlDecode YajlFactsDecode YajlFactsBits.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import RunCeiling.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Section RC__1.
Context {RC__ : OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib.RunCeiling.RunCeiling}.
Section S.
Variable HK : RawAlloc.PState -> list MallocBlocks.block -> (word -> option byte) -> Model -> Prop.

Ltac kill K := exfalso; revert K; unfold wz; rewrite ?unsigned_lit by lia;
  try (change 18446744073709551615 with (Z.ones 64); rewrite ?Z.land_ones by lia; rewrite ?Z.mod_small by lia); lia.

Lemma vhc_ge_48 : forall c, is_vhc c = true -> 48 <= c < 256.
Proof.
  intros c Hv. pose proof (is_vhc_range c Hv) as R.
  pose proof (byte_forall (fun c => implb (is_vhc c) (48 <=? c)) ltac:(vm_compute; reflexivity) c R) as H.
  cbn beta in H. rewrite Hv in H. cbn [implb] in H. apply Z.leb_le in H. lia.
Qed.

(* [comment removed for export] *)
Lemma vhc_digit_noadj : forall h, is_vhc h = true -> h <= 64 -> Z.land (h + -48) 255 = hex_digit_adj h.
Proof.
  intros h Hv Hle. pose proof (is_vhc_range h Hv) as R.
  pose proof (byte_forall (fun c => implb (is_vhc c) (implb (c <=? 64) (Z.land (c + -48) 255 =? hex_digit_adj c)))
                ltac:(vm_compute; reflexivity) h R) as H.
  cbn beta in H. rewrite Hv in H. replace (h <=? 64) with true in H by (symmetry; apply Z.leb_le; lia).
  cbn [implb] in H. apply Z.eqb_eq in H. exact H.
Qed.
Lemma vhc_digit_adj : forall h, is_vhc h = true -> 64 < h ->
  Z.land (Z.land (Z.land h 223 + -55) 18446744073709551615) 255 = hex_digit_adj h.
Proof.
  intros h Hv Hlt. pose proof (is_vhc_range h Hv) as R.
  pose proof (byte_forall (fun c => implb (is_vhc c) (implb (64 <? c)
                 (Z.land (Z.land (Z.land c 223 + -55) 18446744073709551615) 255 =? hex_digit_adj c)))
                ltac:(vm_compute; reflexivity) h R) as H.
  cbn beta in H. rewrite Hv in H. replace (64 <? h) with true in H by (symmetry; apply Z.ltb_lt; lia).
  cbn [implb] in H. apply Z.eqb_eq in H. exact H.
Qed.
Lemma shl4_small : forall v, 0 <= v < 2^59 -> Z.land (Z.shiftl v 4) 18446744073709551615 = Z.shiftl v 4.
Proof.
  intros v Hv. change 18446744073709551615 with (Z.ones 64). rewrite Z.land_ones by lia.
  rewrite Z.shiftl_mul_pow2 in * by lia. apply Z.mod_small. lia.
Qed.

(* [comment removed for export] *)
Lemma hex_loop_walk : forall (rest pre : list Z) (ra gp tp t1 t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (sp : word) (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
    (VP SA v vmax lo : Z) (hs : list Z) (v' : Z) (ra0 : word) (junk : list byte) (P : Z),
  P = SA + Z.of_nat (length pre) ->
  hs = pre ++ rest -> length hs = 4%nat -> (1 <= length rest)%nat ->
  Forall (fun h => is_vhc h = true) hs ->
  rw_cells usegs m VP [C4 (wz v)] -> 0 <= v < vmax -> vmax * 16 ^ (Z.of_nat (length rest)) <= 2^32 ->
  bytes_at usegs m SA (zbytes hs) ->
  hex_loop v rest = Some v' ->
  (SA + 4 <= VP \/ VP + 4 <= SA) -> bv_unsigned sp + 16 <= VP -> (SA + 4 <= lo \/ bv_unsigned sp + 16 <= SA) ->
  stk usegs m lo (bv_unsigned sp) -> rw_cells usegs m (bv_unsigned sp) [CB 8 junk; C8 ra0] ->
  mem_inv usegs m -> 0 < SA -> SA + 4 < 2^64 ->
  evt usegs (fun ms' => exists (t0' t1' t2' a7' : word) (m' : word -> option byte),
        ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (wz VP) (wz SA) (wz 0) (wz 0) (wz 1) (wz 64) (wz 16) a7'
                      s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz 0x1765c) fc None m' (seg_rom usegs)
        /\ munch [(lo, bv_unsigned sp + 16); (VP, VP + 4)] m m' /\ wmono usegs m m' /\ mem_inv usegs m'
        /\ stk usegs m' lo (bv_unsigned sp) /\ rw_cells usegs m' (bv_unsigned sp) [CB 8 junk; C8 ra0]
        /\ rw_cells usegs m' VP [C4 (wz v')] /\ bytes_at usegs m' SA (zbytes hs))
    (MS (mkR ra sp gp tp (wz P) t1 t2 s0 s1 (wz VP) (wz SA) (wz 0) (wz (Z.of_nat (length rest))) (wz 1) (wz 64) (wz 16) (wz P)
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz 0x17608) fc None m (seg_rom usegs)).
Proof.
  induction rest as [|h rest IH]; intros until P; intros HP HS LEN K ALL VC V0 VB TB HL SEP1 SPV SEP2 STK FR MI SAP SAH; subst P.
  { cbn in K. lia. }
  pose proof (rw_cells_bound _ _ _ _ VC) as VCB. cbn [cells_size csize Nat.add] in VCB.
  pose proof (bytes_at_bound _ _ _ _ TB) as TBB. pose proof (zbytes_length hs) as ZL. rewrite LEN in ZL. rewrite ZL in TBB.
  pose proof (munch_refl [(lo, bv_unsigned sp + 16); (VP, VP + 4)] m) as MU. pose proof (wmono_refl usegs m) as WM.
  assert (DONE : (length pre + S (length rest) = 4)%nat).
  { apply (f_equal (@length Z)) in HS. rewrite length_app in HS. cbn [length] in HS. lia. }
  assert (NTH : nth_error hs (length pre) = Some h).
  { rewrite HS. rewrite nth_error_app2, Nat.sub_diag by lia. reflexivity. }
  assert (VH : is_vhc h = true). { rewrite Forall_forall in ALL. apply ALL. eapply nth_error_In. exact NTH. }
  pose proof (vhc_ge_48 h VH) as HR. pose proof (vhc_hex_digit h VH) as [HM HD].
  assert (P16 : 16 ^ Z.of_nat (length (h :: rest)) = 16 * 16 ^ Z.of_nat (length rest)).
  { cbn [length]. rewrite Nat2Z.inj_succ, Z.pow_succ_r by lia. reflexivity. }
  pose proof (Z.pow_pos_nonneg 16 (Z.of_nat (length rest)) ltac:(lia) ltac:(lia)) as PP.
  assert (VMAX : vmax <= 2^28) by nia.
  cbn [hex_loop] in HL. rewrite HM in HL. cbn [Z.eqb] in HL.
  unfold wz.
  (* [comment removed for export] *)
  zstep. if_cases G0; zify_cond G0. 1:{ kill G0. }
  zstep. zstep. zstep. if_cases G1; zify_cond G1. 1:{ exfalso. replace (SA + Z.of_nat (length pre) <? 1) with false in G1 by (symmetry; apply Z.ltb_ge; lia).
        replace (Z.lxor 1 (Z.b2z false)) with 1 in G1 by reflexivity. lia. }
  zstep. if_cases G2; zify_cond G2. 1:{ kill G2. }
  pose proof (u8ro_read usegs _ SA (zbytes hs) (Z.of_nat (length pre)) (Z_to_bv 8 h) _ TB
                ltac:(unfold zbytes; rewrite nth_error_map, Nat2Z.id, NTH; reflexivity) ltac:(lia) eq_refl) as RD.
  zstep. cbn beta.
  replace (bv_unsigned (Z_to_bv 8 h)) with h by (symmetry; apply (Z_to_bv_small 8); unfold bv_modulus; lia).
  (* [comment removed for export] *)
  eapply (evt_cut usegs (fun ms1 => ms1 = MS (mkR ra sp gp tp (Z_to_bv 64 (SA + Z.of_nat (length pre))) (Z_to_bv 64 (hex_digit_adj h)) t2 s0 s1 (Z_to_bv 64 VP) (Z_to_bv 64 SA)
              (Z_to_bv 64 0) (Z_to_bv 64 (Z.of_nat (length (h :: rest)))) (Z_to_bv 64 1) (Z_to_bv 64 64) (Z_to_bv 64 16) (Z_to_bv 64 (SA + Z.of_nat (length pre)))
              s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x17634) fc None m (seg_rom usegs))).
  { zstep. if_cases K0; zify_cond K0.
    - zstep. zstep. rewrite (vhc_digit_noadj h VH) by lia. apply evt_done. reflexivity.
    - zstep. zstep. zstep. zstep. rewrite (vhc_digit_adj h VH) by lia. apply evt_done. reflexivity. }
  intros ms1 ->.
  zstep. if_cases K1; zify_cond K1. 1:{ kill K1. }
  zstep. if_cases G3; zify_cond G3. 1:{ kill G3. }
  zstep. rewrite ysx32_small by lia.
  zstep. zstep. zstep. zstep.
  pose proof (lor_shiftl_small v (hex_digit_adj h) 4 ltac:(lia) ltac:(cbn; lia) ltac:(lia)) as LV. change (2^4) with 16 in LV.
  zstep. zstep. zstep. if_cases K2; zify_cond K2.
  - (* [comment removed for export] *)
    destruct rest as [|h2 rest2]; [cbn [length] in K2; kill K2|].
    replace (SA + Z.of_nat (length pre) + 1) with (SA + Z.of_nat (length (pre ++ [h]))) by (rewrite length_app; cbn [length]; lia).
    replace (Z.of_nat (length (h :: h2 :: rest2)) + -1) with (Z.of_nat (length (h2 :: rest2))) by (cbn [length]; lia).
    lazymatch goal with H : rw_cells _ _ VP _ |- _ => rewrite shl4_small in H by lia end.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
    eapply evt_mono; [ eapply (IH (pre ++ [h])) with (hs := hs) (vmax := vmax * 16) (v' := v') (lo := lo);
      [ reflexivity | rewrite HS, <- app_assoc; reflexivity | exact LEN | cbn [length]; lia | exact ALL
      | lazymatch goal with H : rw_cells _ mx VP _ |- _ => exact H end
      | rewrite LV; nia | rewrite P16 in VB; cbn [length]; cbn [length] in VB; nia
      | lazymatch goal with H : bytes_at _ mx SA _ |- _ => exact H end
      | exact HL | exact SEP1 | exact SPV | exact SEP2
      | lazymatch goal with H : stk _ mx _ _ |- _ => exact H end
      | lazymatch goal with H : rw_cells _ mx (bv_unsigned sp) _ |- _ => exact H end
      | assumption | exact SAP | exact SAH ] | ] end.
    cbv beta. intros ms' (t0' & t1' & t2' & a7' & m' & -> & MU2 & WM2 & MI2 & STK2 & FR2 & VC2 & TB2).
    exists t0', t1', t2', a7', m'. split; [reflexivity|].
    split; [eapply munch_trans; [exact MU| exact MU2]|]. split; [eapply wmono_trans; [exact WM| exact WM2]|].
    split; [exact MI2|]. split; [exact STK2|]. split; [exact FR2|]. split; [exact VC2| exact TB2].
  - (* [comment removed for export] *)
    destruct rest as [|h2 rest2]; [| cbn [length] in K2, DONE; kill K2].
    lazymatch goal with H : rw_cells _ _ VP _ |- _ => rewrite shl4_small in H by lia end.
    apply evt_done. eexists _, _, _, _, _.
    change (Z.of_nat (length [h]) + -1) with 0.
    split; [reflexivity|].
    cbn [hex_loop] in HL. injection HL as <-.
    split; [assumption|]. split; [assumption|]. split; [assumption|]. split; [assumption|].
    split; [assumption|]. split; [| assumption].
    lazymatch goal with H : rw_cells _ _ VP _ |- _ => exact H end.
Qed.

Lemma land3_of_mod4 : forall x, x mod 4 = 0 -> Z.land x 3 = 0.
Proof. intros x H. change 3 with (Z.ones 2). rewrite Z.land_ones by lia. exact H. Qed.

Lemma yhexToDigit_spec : yhexToDigit_stmt.
Proof.
  unfold yhexToDigit_stmt. intros until m. intros (VPA & SP0 & SH4) VC V16 TB V0 V1 V2 V3 HL SEP1 STK LO SPV SEP2 MI A0 A1.
  pose proof (rw_cells_bound _ _ _ _ VC) as VCB. cbn [cells_size csize Nat.add] in VCB.
  pose proof (bytes_at_bound _ _ _ _ TB) as TBB. cbn [zbytes map length] in TBB.
  assert (ZL : length (zbytes [h0; h1; h2; h3]) = 4%nat) by reflexivity.
  pose proof (proj1 STK) as LO0. pose proof (land3_of_mod4 _ VPA) as L3.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
  subst a0 a1. unfold RY_HEXTODIGIT, wz in *.
  pose proof (munch_refl [(lo, bv_unsigned sp); (VP, VP + 4)] m) as MU. pose proof (wmono_refl usegs m) as WM.
  step. carve_frame 16%nat STK.
  step. zstep. rewrite L3. step. zstep.
  replace (Z.b2z (0 <? S)) with 1 by (replace (0 <? S) with true by (symmetry; apply Z.ltb_lt; lia); reflexivity).
  step. step. step. step.
  change (Z_to_bv 64 4) with (Z_to_bv 64 (Z.of_nat (@length Z [h0; h1; h2; h3]))).
  eapply evt_cut.
  { eapply (hex_loop_walk [h0; h1; h2; h3] []) with (hs := [h0; h1; h2; h3]) (v := v) (vmax := 2^16) (lo := lo) (v' := v') (ra0 := ra) (junk := take 8 junk);
      [ cbn; lia | reflexivity | reflexivity | cbn; lia
      | apply Forall_cons; [exact V0|]; apply Forall_cons; [exact V1|]; apply Forall_cons; [exact V2|]; apply Forall_cons; [exact V3|]; apply Forall_nil
      | exact VC | lia | cbn; lia | exact TB | exact HL
      | exact SEP1 | rewrite unsigned_lit by lia; lia | rewrite unsigned_lit by lia; lia
      | rewrite unsigned_lit by lia; exact STK | rewrite unsigned_lit by lia; exact FR | exact MI | exact SP0 | exact SH4 ]. }
  cbv beta. intros ms' (t0' & t1' & t2' & a7' & m' & -> & MU2 & WM2 & MI2 & STK2 & FR2 & VC2 & TB2).
  rewrite unsigned_lit in MU2, STK2, FR2 by lia.
  clear STK FR VC TB MI.
  replace (bv_unsigned sp + -16 + 16) with (bv_unsigned sp) in MU2 by lia.
  pose proof (munch_trans _ _ _ _ MU MU2) as MU3. pose proof (wmono_trans _ _ _ _ WM WM2) as WM3. clear MU MU2 WM WM2 m0.
  rename MU3 into MU. rename WM3 into WM.
  unfold wz. step. step. step.
  release_frame FR2 STK2 (bv_unsigned sp).
  unfold yhexToDigit_rpost. finish.
Qed.
End S.
End RC__1.
