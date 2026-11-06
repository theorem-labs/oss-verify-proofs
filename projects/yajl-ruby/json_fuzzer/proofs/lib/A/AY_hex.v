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
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.MS Require Import MallocRep.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Spec Require Import Prelim YajlBase YajlBuf YajlLex YajlDecode YajlFactsDecode YajlFactsBits.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.LibA Require Import StepA StepA2 AImages Shadow.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import InitMem SysStep Arr.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.R Require Import RY_lib RY_hex.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.A Require Import A_iface AI_shadow AYajlRep AYajl_iface.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Ltac kill K := exfalso; revert K; unfold wz; rewrite ?unsigned_lit by lia;
  try (change 18446744073709551615 with (Z.ones 64); rewrite ?Z.land_ones by lia; rewrite ?Z.mod_small by lia); lia.

(* [comment removed for export] *)
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import RunCeiling.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Ltac aceil := first [pose proof alloc_ceiling_range as CEILB | idtac].
Section RC__1.
Context {RC__ : OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib.RunCeiling.RunCeiling}.
Lemma ahex_loop_walk : forall (rest pre : list Z) (P : acc -> Prop)
    (ra sp gp tp x6 x7 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem)
    (VP SA v vmax : Z) (hs : list Z) (v' : Z) (OA On : Z) (shb : list byte),
  hs = pre ++ rest -> length hs = 4%nat -> (1 <= length rest)%nat ->
  Forall (fun h => is_vhc h = true) hs ->
  rw_cells asegs m VP [C4 (Z_to_bv 64 v)] -> 0 <= v < vmax -> vmax * 16 ^ (Z.of_nat (length rest)) <= 2^32 ->
  bytes_at asegs m SA (zbytes hs) ->
  hex_loop v rest = Some v' ->
  OA mod 8 = 0 -> 0 < On -> u8arr asegs m (2147450880 + OA / 8) shb -> shb = blk_shadow On ->
  OA <= SA -> SA + 4 <= OA + On -> (6303744 <= OA /\ (OA + On <= 2147446784 \/ 17594333495296 <= OA)) -> OA + On <= alloc_ceiling ->
  alloc_ceiling <= VP -> VP + 4 <= 2^47 ->
  bytes_at asegs m (2147450880 + VP / 8) [Z_to_bv 8 0] ->
  mem_inv asegs m ->
  (forall a k, VP <= a -> a + Z.of_nat k <= VP + 4 -> P (Z_to_bv 64 a, k)) ->
  (forall a k, 2147450880 + VP / 8 <= a -> a + Z.of_nat k <= 2147450880 + VP / 8 + 1 -> P (Z_to_bv 64 a, k)) ->
  (forall a k, SA <= a -> a + Z.of_nat k <= SA + 4 -> P (Z_to_bv 64 a, k)) ->
  (forall a k, 2147450880 + OA / 8 <= a -> a + Z.of_nat k <= 2147450880 + OA / 8 + (On + 7) / 8 -> P (Z_to_bv 64 a, k)) ->
  evtA asegs P (fun ms' => exists (x6' x7' : word) (m' : mem),
        ms' = MS (mkR ra sp gp tp (Z_to_bv 64 (Z.land VP 7 + 3)) x6' x7' s0 s1 (Z_to_bv 64 VP) (Z_to_bv 64 (SA + 4)) (Z_to_bv 64 (SA + 4)) (Z_to_bv 64 0)
                      (Z_to_bv 64 64) (Z_to_bv 64 2147450880) (Z_to_bv 64 16) (Z_to_bv 64 (VP / 8 + 2147450880))
                      s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x8b144) fc None m' (seg_rom asegs)
        /\ munch [(VP, VP + 4)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
        /\ rw_cells asegs m' VP [C4 (Z_to_bv 64 v')] /\ bytes_at asegs m' SA (zbytes hs)
        /\ u8arr asegs m' (2147450880 + OA / 8) shb /\ bytes_at asegs m' (2147450880 + VP / 8) [Z_to_bv 8 0])
    (MS (mkR ra sp gp tp (Z_to_bv 64 (Z.land VP 7 + 3)) x6 x7 s0 s1 (Z_to_bv 64 VP) (Z_to_bv 64 (SA + Z.of_nat (length pre))) (Z_to_bv 64 (SA + Z.of_nat (length pre)))
             (Z_to_bv 64 (Z.of_nat (length rest))) (Z_to_bv 64 64) (Z_to_bv 64 2147450880) (Z_to_bv 64 16) (Z_to_bv 64 (VP / 8 + 2147450880))
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x8b0d8) fc None m (seg_rom asegs)).
Proof. aceil.
  induction rest as [|h rest IH]; intros until shb; intros HS LEN K ALL VC V0 VB TB HL BSa BSn BS BSeq OA1 OA2 OA3 OA4 VPL VPH VSH MI PV PVS PS PSH.
  { cbn in K. lia. }
  pose proof (rw_cells_bound _ _ _ _ VC) as VCB. cbn [cells_size csize Nat.add] in VCB.
  pose proof (bytes_at_bound _ _ _ _ TB) as TBB. pose proof (zbytes_length hs) as ZL. rewrite LEN in ZL. rewrite ZL in TBB.
  pose proof (blk_shadow_length On ltac:(lia)) as BSlen. rewrite <- BSeq in BSlen.
  pose proof (munch_refl [(VP, VP + 4)] m) as MU. pose proof (wmono_refl asegs m) as WM.
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
  (* [comment removed for export] *)
  assert (G8 : (SA + Z.of_nat (length pre)) mod 8 + 1 <= 8) by (clear; Z.div_mod_to_equations; lia).
  set (LST := fun (pc : Z) (x6v x7v : word) (a1v a3v : Z) (mm : mem) =>
    MS (mkR ra sp gp tp (Z_to_bv 64 (Z.land VP 7 + 3)) x6v x7v s0 s1 (Z_to_bv 64 VP) (Z_to_bv 64 a1v) (Z_to_bv 64 (SA + Z.of_nat (length pre)))
             (Z_to_bv 64 a3v) (Z_to_bv 64 64) (Z_to_bv 64 2147450880) (Z_to_bv 64 16) (Z_to_bv 64 (VP / 8 + 2147450880))
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 pc) fc None mm (seg_rom asegs)).
  eapply (evtA_cut asegs P (fun ms1 => exists x6' x7', ms1 = LST 0x8b0e8 x6' x7' (SA + Z.of_nat (length pre)) (Z.of_nat (length (h :: rest))) m)).
  { shadow_cases BS (SA + Z.of_nat (length pre)) 1.
    - apply evtA_done. do 2 eexists. reflexivity.
    - (* [comment removed for export] *)
      assert (L7 : forall a, Z.land a 7 = a mod 8) by (intros a; exact (Z.land_ones a 3 ltac:(lia))).
      zstepA. zstepA. if_cases Kc; zify_cond Kc.
      { exfalso. pose proof (Z.mod_pos_bound (SA + Z.of_nat (length pre)) 8 ltac:(lia)) as MB.
        revert Kc. rewrite ?sxb_small, ?zxb_small, ?L7 by lia. intro Kc.
        rewrite (signed_lit_small ((SA + Z.of_nat (length pre)) mod 8)) in Kc by (clear -CEILB MB; lia).
        rewrite (signed_lit_small k) in Kc by (clear -CEILB HK; lia). clear -CEILB Kc HK MB; lia. }
      stepA. apply evtA_done. do 2 eexists. reflexivity. }
  cbv beta. intros ms1 (x6a & x7a & ->). subst LST. cbv beta.
  (* [comment removed for export] *)
  pose proof (u8ro_read asegs _ SA (zbytes hs) (Z.of_nat (length pre)) (Z_to_bv 8 h) _ TB
                ltac:(unfold zbytes; rewrite nth_error_map, Nat2Z.id, NTH; reflexivity) ltac:(lia) eq_refl) as RD.
  zstepA. cbn beta. clear RD.
  replace (bv_unsigned (Z_to_bv 8 h)) with h by (symmetry; apply (Z_to_bv_small 8); unfold bv_modulus; lia).
  eapply (evtA_cut asegs P (fun ms2 => ms2 = MS (mkR ra sp gp tp (Z_to_bv 64 (Z.land VP 7 + 3)) (Z_to_bv 64 (hex_digit_adj h)) x7a s0 s1 (Z_to_bv 64 VP)
             (Z_to_bv 64 (SA + Z.of_nat (length pre))) (Z_to_bv 64 (SA + Z.of_nat (length pre)))
             (Z_to_bv 64 (Z.of_nat (length (h :: rest)))) (Z_to_bv 64 64) (Z_to_bv 64 2147450880) (Z_to_bv 64 16) (Z_to_bv 64 (VP / 8 + 2147450880))
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x8b100) fc None m (seg_rom asegs))).
  { zstepA. if_cases K0; zify_cond K0.
    - zstepA. zstepA. rewrite (vhc_digit_noadj h VH) by lia. apply evtA_done. reflexivity.
    - zstepA. zstepA. zstepA. zstepA. rewrite (vhc_digit_adj h VH) by lia. apply evtA_done. reflexivity. }
  intros ms2 ->.
  zstepA. if_cases K1; zify_cond K1. 1:{ exfalso. revert K1. rewrite ?unsigned_lit by lia. lia. }   (* [comment removed for export] *)
  (* [comment removed for export] *)
  pose proof (u8ro_read asegs _ (2147450880 + VP / 8) [Z_to_bv 8 0] 0 (Z_to_bv 8 0) (Z_to_bv 64 (VP / 8 + 2147450880)) VSH eq_refl ltac:(lia)
                ltac:(unfold wa; f_equal; lia)) as RD.
  zstepA. cbn beta. clear RD.                                       (* [comment removed for export] *)
  rewrite ?zxb_small, ?sxb_small by lia.
  zstepA. if_false.                                                 (* [comment removed for export] *)
  zstepA. rewrite ysx32_small by lia.                               (* [comment removed for export] *)
  zstepA. zstepA. zstepA. zstepA.                                   (* [comment removed for export] *)
  pose proof (lor_shiftl_small v (hex_digit_adj h) 4 ltac:(lia) ltac:(cbn; lia) ltac:(lia)) as LV. change (2^4) with 16 in LV.
  zstepA.                                                           (* [comment removed for export] *)
  zstepA.                                                           (* [comment removed for export] *)
  zstepA. if_cases K2; zify_cond K2.                                (* [comment removed for export] *)
  - (* [comment removed for export] *)
    destruct rest as [|h2 rest2]; [cbn [length] in K2; kill K2|].
    replace (SA + Z.of_nat (length pre) + 1) with (SA + Z.of_nat (length (pre ++ [h]))) by (rewrite length_app; cbn [length]; lia).
    replace (Z.of_nat (length (h :: h2 :: rest2)) + -1) with (Z.of_nat (length (h2 :: rest2))) by (cbn [length]; lia).
    lazymatch goal with H : rw_cells _ _ VP _ |- _ => rewrite shl4_small in H by lia end.
    lazymatch goal with |- evtA _ _ _ (MS _ _ _ _ _ ?mx _) =>
    eapply evtA_mono; [ eapply (IH (pre ++ [h]) P) with (hs := hs) (vmax := vmax * 16) (v' := v') (On := On);
      [ rewrite HS, <- app_assoc; reflexivity | exact LEN | cbn [length]; lia | exact ALL
      | lazymatch goal with H : rw_cells _ mx VP _ |- _ => exact H end
      | rewrite LV; nia | rewrite P16 in VB; cbn [length]; cbn [length] in VB; nia
      | lazymatch goal with H : bytes_at _ mx SA _ |- _ => exact H end
      | exact HL | exact BSa | exact BSn
      | lazymatch goal with H : u8arr _ mx _ _ |- _ => exact H end
      | exact BSeq | exact OA1 | exact OA2 | exact OA3 | exact OA4 | exact VPL | exact VPH
      | lazymatch goal with H : bytes_at _ mx (2147450880 + VP / 8) _ |- _ => exact H end
      | assumption | exact PV | exact PVS | exact PS | exact PSH ] | ] end.
    cbv beta. intros ms' (x6' & x7' & m' & -> & MU2 & WM2 & MI2 & VC2 & TB2 & BS2 & VSH2).
    exists x6', x7', m'. split; [reflexivity|].
    split; [eapply munch_trans; [exact MU| exact MU2]|]. split; [eapply wmono_trans; [exact WM| exact WM2]|].
    split; [exact MI2|]. split; [exact VC2|]. split; [exact TB2|]. split; [exact BS2| exact VSH2].
  - (* [comment removed for export] *)
    destruct rest as [|h2 rest2]; [| cbn [length] in K2, DONE; kill K2].
    stepA.
    lazymatch goal with H : rw_cells _ _ VP _ |- _ => rewrite shl4_small in H by lia end.
    apply evtA_done. eexists _, _, _.
    replace (SA + Z.of_nat (length pre) + 1) with (SA + 4) by (cbn [length] in DONE; lia).
    split; [reflexivity|].
    cbn [hex_loop] in HL. injection HL as <-.
    split; [assumption|]. split; [assumption|]. split; [assumption|].
    split; [lazymatch goal with H : rw_cells _ _ VP _ |- _ => exact H end|].
    split; [assumption|]. split; assumption.
Qed.

Theorem ayhexToDigit_proof : ayhexToDigit_stmt.
Proof. aceil.
  unfold ayhexToDigit_stmt. intros P VP S v lo h0 h1 h2 h3 v' OA On. intros until m.
  intros STA VC V16 TB V0 V1 V2 V3 HL BS OA1 OA2 OA3 OA4 MI ST LOC LO SPH SPV VPH VSH -> -> PSTK PIMG PV PVS PS PSH.
  unfold wz in *. unfold AY_HEXTODIGIT.
  destruct STA as (G1 & G2 & G3 & G4). unfold AY_GOT_SHADOW, AY_SHADOW_VAR, AY_GOT_UAR, AY_UAR_VAR, A_SB, wz in G1, G2, G3, G4.
  aceil.
  unfold opol, pol, oshw_lo, oshw_hi, A_SB, amem in PSTK, PIMG, PV, PVS, PS, PSH, OA3. unfold AY_IMG_LO, AY_IMG_HI in PIMG. unfold A_SB in VSH.
  unfold oshadow, A_SB in BS. open_shadow BS.
  pose proof (rw_cells_bound _ _ _ _ VC) as VCB. cbn [cells_size csize Nat.add] in VCB.
  pose proof (bv_unsigned_in_range 64 sp) as SR. unfold bv_modulus in SR. cbn in SR.
  assert (ZL : length (zbytes [h0; h1; h2; h3]) = 4%nat) by reflexivity.
  (* [comment removed for export] *)
  assert (TBLO : S + 4 <= lo) by lia.
  assert (VSHLO : 2147450880 + VP / 8 + 1 <= lo) by (clear -CEILB VPH LOC; Z.div_mod_to_equations; lia).
  assert (BSLO : 2147450880 + OA / 8 + Z.of_nat (length shb) <= lo) by (rewrite BSlen; clear -CEILB OA4 LOC OA3 BSn; Z.div_mod_to_equations; lia).
  assert (MU : munch [(lo, bv_unsigned sp); (VP, VP + 4)] m m) by apply munch_refl.
  assert (WM : wmono asegs m m) by apply wmono_refl.
  carve_frame 16%nat ST.
  stepA. stepA.              (* [comment removed for export] *)
  do 3 stepA.                (* [comment removed for export] *)
  stepA. stepA.              (* [comment removed for export] *)
  stepA.                     (* [comment removed for export] *)
  zstepA. shadow_addr.       (* [comment removed for export] *)
  zstepA.                    (* [comment removed for export] *)
  zstepA.                    (* [comment removed for export] *)
  zstepA.                    (* [comment removed for export] *)
  zstepA.                    (* [comment removed for export] *)
  replace (Z_to_bv 64 S) with (Z_to_bv 64 (S + Z.of_nat (@length Z []))) by (f_equal; cbn; lia).
  change (Z_to_bv 64 4) with (Z_to_bv 64 (Z.of_nat (@length Z [h0; h1; h2; h3]))).
  lazymatch goal with |- evtA _ _ _ (MS _ _ _ _ _ ?mx _) =>
  eapply evtA_cut;
   [ eapply (ahex_loop_walk [h0; h1; h2; h3] [] P) with (hs := [h0; h1; h2; h3]) (v := v) (vmax := 2^16) (v' := v') (On := On);
      [ reflexivity | reflexivity | cbn; lia
      | apply Forall_cons; [exact V0|]; apply Forall_cons; [exact V1|]; apply Forall_cons; [exact V2|]; apply Forall_cons; [exact V3|]; apply Forall_nil
      | lazymatch goal with H : rw_cells _ mx VP _ |- _ => exact H end
      | lia | cbn; lia
      | lazymatch goal with H : bytes_at _ mx S _ |- _ => exact H end
      | exact HL | exact BSa | exact BSn
      | lazymatch goal with H : u8arr _ mx _ _ |- _ => exact H end
      | exact BSeq | exact OA1 | exact OA2
      | lia | lia | lia | lia
      | lazymatch goal with H : bytes_at _ mx (2147450880 + VP / 8) _ |- _ => exact H end
      | assumption
      | intros a k H1 H2; apply PV; lia | intros a k H1 H2; apply PVS; lia | intros a k H1 H2; apply PS; lia | intros a k H1 H2; apply PSH; lia ]
   | ] end.
  cbv beta. intros ms' (x6' & x7' & m' & -> & MU2 & WM2 & MI2 & VC2 & TB2 & BS2 & VSH2).
  lazymatch goal with FR0 : rw_cells _ ?mx (bv_unsigned sp + -16) _, ST0 : stk _ ?mx _ _ |- _ =>
    pose proof (rw_cells_transport _ _ _ _ _ _ FR0 MU2 WM2 ltac:(cbn; lia)) as FR2;
    pose proof (stk_transport_disjoint _ _ _ _ _ _ ST0 MU2 WM2 ltac:(cbn; lia)) as ST2;
    pose proof (munch_trans _ _ _ _ MU (munch_weaken [(VP, VP + 4)] [(lo, bv_unsigned sp); (VP, VP + 4)] _ _ ltac:(unfold sub_fp; cbn [outside]; intros; lia) MU2)) as MU3;
    pose proof (wmono_trans _ _ _ _ WM WM2) as WM3;
    pose proof (rw_cells_transport _ _ _ _ _ _ G1 MU2 WM2 ltac:(cbn; lia)) as G1';
    pose proof (rw_cells_transport _ _ _ _ _ _ G2 MU2 WM2 ltac:(cbn; lia)) as G2';
    pose proof (rw_cells_transport _ _ _ _ _ _ G3 MU2 WM2 ltac:(cbn; lia)) as G3';
    pose proof (rw_cells_transport _ _ _ _ _ _ G4 MU2 WM2 ltac:(cbn; lia)) as G4';
    clear FR0 ST0 MU MU2 WM WM2 G1 G2 G3 G4 VC TB BS VSH; rename MU3 into MU; rename WM3 into WM
  end.
  stepA. stepA. stepA.       (* [comment removed for export] *)
  release_frame FR2 ST2 (bv_unsigned sp).
  unfold ayhexToDigit_rpost. finishA.
  - unfold oshadow, block_shadow, A_SB. split; [exact BSa|]. split; [exact BSn|]. rewrite <- BSeq. exact BS2.
  - unfold ay_statics, AY_GOT_SHADOW, AY_SHADOW_VAR, AY_GOT_UAR, AY_UAR_VAR, A_SB, wz. split; [|split; [|split]]; assumption.
Qed.
End RC__1.
