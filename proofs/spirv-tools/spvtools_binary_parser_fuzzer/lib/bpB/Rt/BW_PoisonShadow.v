(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BW_0Gc.
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BeapCeil.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BTac BImage BZBridge BSysStep BSFModel BellsX BArr BacX.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BothAllocModel.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BSegs BsShadow BllocWf BllocKit BllocRep BsAtomics B_memset BllocWalkKit.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import B8Store.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_n8 segs m a bs.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Section HCW.
  Context {HCEIL : HeapCeil}.

Local Unset Keyed Unification.

Definition poison_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (m : mem) (lo addr size v : Z) : machine_state -> Prop :=
  fun ms' => exists (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch [(bv_unsigned sp - 64, bv_unsigned sp); (sh addr, sh addr + size / 8)]%Z m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo (bv_unsigned sp)
    /\ poisoned m' addr (Z.to_nat (size / 8)) v.

Section Part2.
  Variables (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m0 m : mem).
  Variables (lo addr size v : Z) (j8 : list byte) (sbs : list byte).
  Hypothesis MI : mem_inv asegs m.
  Hypothesis MU : munch [(bv_unsigned sp - 64, bv_unsigned sp); (sh addr, sh addr + size / 8)]%Z m0 m.
  Hypothesis WM : wmono asegs m0 m.
  Hypothesis ST : stk asegs m lo (bv_unsigned sp + -64).
  Hypothesis LO : aceil <= lo.  Hypothesis HI : lo + 64 <= bv_unsigned sp.
  Hypothesis FR : rw_cells asegs m (bv_unsigned sp + -64) [CB 8 j8; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

  Hypothesis AR : ((AHI_LO <= addr /\ AHI_LO + 8 <= addr + size) \/ (0 <= addr /\ 8 <= addr + size /\ addr + size <= ALOWSH_LO))
                  /\ addr + size <= aceil /\ addr mod 8 = 0 /\ size mod 8 = 0 /\ 0 <= size.
  Hypothesis VR : 0 <= v < 256.
  Hypothesis SH : u8arr asegs m (sh addr) sbs.  Hypothesis SHL : Z.of_nat (length sbs) = size / 8.
  Hypothesis GOT : rw_cells asegs m AGOT_LO (map (fun v => C8 (wz v)) AGOT_VALS).
  Hypothesis CSHB : rw_cells asegs m ASHBASE_CELL [C8 (wz ASHADOW_BASE)].
  Hypothesis CHME : rw_cells asegs m AHIGHMEMEND [C8 (wz (2^47 - 1)); C8 (wz 0); C8 (wz 0)].
  Hypothesis CTHR : rw_cells asegs m (ACFLAGS + 120) [C8 (wz 0xffffffffffffffff)].
  Hypothesis CRMS : rw_cells asegs m AREALMEMSET [C8 (wz AMEMSET)].

  Ltac ps_prep :=
    unfold wz, AGOT_LO, AGOT_VALS, ASHBASE_CELL, ASHADOW_BASE, AHIGHMEMEND, ACFLAGS, AREALMEMSET, AMEMSET, AHI_LO, ALOWSH_LO in *; cbn [map] in GOT;
    change (2^47 - 1) with 140737488355327 in CHME; change (2239336 + 120) with 2239456 in CTHR;
    pose proof (bv_unsigned_in_range _ sp) as SPR; change (bv_modulus 64) with (2^64) in SPR; acb.

  Lemma poison_tail : forall x11 x13 x14 x15 x16 x17 x5 x7 x28,
    evt asegs (poison_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 lo addr size v)
      (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp x5 (Z_to_bv 64 1535652) x7 (Z_to_bv 64 (size / 8)) (Z_to_bv 64 2147450880)
               (Z_to_bv 64 (sh addr)) x11 (Z_to_bv 64 v) x13 x14 x15 x16 x17
               (Z_to_bv 64 ((addr + size + -8) / 8 + 1)) (Z_to_bv 64 1601864) s4 s5 s6 s7 s8 s9 s10 s11 x28 t4 t5 t6)
          F (Z_to_bv 64 0xbb790) fc None m (seg_rom asegs)).
  Proof.
    intros. destruct AR as (ARS & ARC & AR8 & SZ8 & SZ0). ps_prep.

    step. step. step. step. step. step. step. step. step. step. step. step.

    pose proof (rw_cells_of_u8arr asegs _ _ _ SH) as DST.
    release_frame FR ST (bv_unsigned sp).
    assert (SHR : 0 <= sh addr /\ sh addr + size / 8 <= 17594333495296) by (clear - ARS ARC SZ0 ACEILB; unfold sh, ASHADOW_BASE; Z.div_mod_to_equations; lia).
    clear ARS.
    eapply evt_mono.
    { eapply memset_spec; [| exact MI]. rewrite !unsigned_lit by (Z.div_mod_to_equations; lia).
      replace (Z.to_nat (size / 8)) with (length sbs) by lia. exact DST. }
    intros ms' PO. unfold memset_post in PO. destruct PO as (y5 & y6 & y7 & y11 & y12 & y13 & y14 & y15 & y16 & y17 & y28 & y29 & y30 & y31 & m' & E & MU2 & WM2 & MI2 & FILL).
    subst ms'. rewrite !unsigned_lit in MU2 by (Z.div_mod_to_equations; lia). rewrite !unsigned_lit in FILL by (Z.div_mod_to_equations; lia).
    unfold poison_post. do 15 eexists. exists m'. split; [reflexivity|].
    split. { eapply munch_trans; [exact MU|]. eapply munch_weaken; [| exact MU2]. unfold sub_fp; cbn [outside]; intros; lia. }
    split. { eapply wmono_trans; [exact WM| exact WM2]. }
    split. { exact MI2. }
    split. { eapply stk_transport_disjoint; [exact ST| exact MU2| exact WM2|]. cbn [disjoint_from]. lia. }
    unfold poisoned, SHAD, poison_bytes. split; [lia|]. split; [lia|].
    eapply u8arr_of_rw_cells. replace (v mod 256) with v in FILL by (symmetry; apply Z.mod_small; lia). exact FILL.
  Qed.

  Lemma poison_join : forall (x5 x6 x7 x13 x14 x15 x16 x17 x28 : word),
    evt asegs (poison_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 lo addr size v)
      (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp x5 x6 x7 s0 (Z_to_bv 64 2147450880) (Z_to_bv 64 addr) (Z_to_bv 64 (addr + size + -8)) (Z_to_bv 64 v)
               x13 x14 x15 x16 x17 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 t4 t5 t6)
          F (Z_to_bv 64 0xbb6ac) fc None m (seg_rom asegs)).
  Proof.
    intros. destruct AR as (ARS & ARC & AR8 & SZ8 & SZ0).
    assert (A0 : 0 <= addr /\ 8 <= addr + size) by (clear - ARS; unfold AHI_LO, ALOWSH_LO in *; lia). clear ARS. ps_prep.

    step. step. step. step. if_cases K; zify_cond K. { exfalso. rewrite ?unsigned_lit in K by lia. lia. } clear K.
    step. step. step. step. step.
    rewrite !(unsigned_lit addr), !Z.shiftr_div_pow2 by lia. change (2^3) with 8.
    rewrite !(unsigned_lit (addr + size + -8)) by lia. rewrite !(unsigned_lit ((addr + size + -8) / 8 + 1)) by (Z.div_mod_to_equations; lia).
    rewrite !(unsigned_lit (addr / 8)) by (Z.div_mod_to_equations; lia).
    replace ((addr + size + -8) / 8 + 1 - addr / 8) with (size / 8) by (Z.div_mod_to_equations; lia).
    replace (2147450880 + addr / 8) with (sh addr) by reflexivity.
    step. if_cases K; zify_cond K.
    - apply poison_tail.
    - step. step. step. step. if_cases K2; zify_cond K2. 2:{ exfalso. rewrite ?unsigned_lit in K2 by (Z.div_mod_to_equations; lia). Z.div_mod_to_equations; lia. }
      apply poison_tail.
  Qed.

  Lemma poison_walk2H : forall (x13 : word), AHI_LO <= addr ->
    evt asegs (poison_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 lo addr size v)
      (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp t0 t1 t2 s0 s1 (wz addr) (wz size) (wz v) x13 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0xbb45c) fc None m (seg_rom asegs)).
  Proof.
    intros x13 AH. destruct AR as (ARS & ARC & AR8 & SZ8 & SZ0).
    assert (ARH : AHI_LO <= addr /\ AHI_LO + 8 <= addr + size) by (clear - ARS AH SZ0; unfold AHI_LO, ALOWSH_LO in *; lia). clear ARS AH. ps_prep.

    step. rewrite (unsigned_lit addr) by lia. change 7 with (Z.ones 3). rewrite Z.land_ones by lia. change (2^3) with 8.
    replace (addr mod 8) with 0 by lia.
    step. if_cases K; zify_cond K. { exfalso. lia. } clear K.

    step. step. step. step. step.
    replace (v_sltu (Z_to_bv 64 2147450880) (Z_to_bv 64 2147450879)) with (Z_to_bv 64 0) by (apply bv_eq; vm_compute; reflexivity).
    step. step. step. if_cases K; zify_cond K. { exfalso. rewrite ?unsigned_lit in K by lia. lia. } clear K.

    step. step. step. step. step. step. step. step. if_cases K; zify_cond K. 2:{ exfalso. rewrite ?unsigned_lit in K by lia. lia. } clear K.

    step. step. step. step. step.
    step. if_cases K; zify_cond K. { exfalso. rewrite ?unsigned_lit in K by lia. lia. } clear K.
    step. if_cases K; zify_cond K. 2:{ exfalso. rewrite ?unsigned_lit in K by lia. lia. } clear K.

    step. step. step. step. if_cases K; zify_cond K. { exfalso. rewrite ?unsigned_lit in K by lia. lia. } clear K.
    step. if_cases K; zify_cond K. 2:{ exfalso. rewrite ?unsigned_lit in K by lia. lia. } clear K.

    step. rewrite (unsigned_lit size) by lia. change 7 with (Z.ones 3). rewrite Z.land_ones by lia. change (2^3) with 8.
    replace (size mod 8) with 0 by lia.
    step. if_cases K; zify_cond K. { exfalso. lia. } clear K.
    step. step. step. if_cases K; zify_cond K. { exfalso. rewrite ?unsigned_lit in K by lia. lia. } clear K.

    step. step. step. step. step. step. step. step. if_cases K; zify_cond K. 2:{ exfalso. rewrite ?unsigned_lit in K by lia. lia. } clear K.

    step. step. step. step. step. step. if_cases K; zify_cond K. { exfalso. rewrite ?unsigned_lit in K by lia. lia. } clear K.
    step. if_cases K; zify_cond K. { exfalso. rewrite ?unsigned_lit in K by lia. lia. } clear K.
    apply poison_join.
  Qed.

  Lemma poison_walk2L : forall (x13 : word), addr + size <= ALOWSH_LO ->
    evt asegs (poison_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 lo addr size v)
      (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp t0 t1 t2 s0 s1 (wz addr) (wz size) (wz v) x13 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0xbb45c) fc None m (seg_rom asegs)).
  Proof.
    intros x13 AL. destruct AR as (ARS & ARC & AR8 & SZ8 & SZ0).
    assert (ARL : 0 <= addr /\ 8 <= addr + size /\ addr + size <= ALOWSH_LO) by (clear - ARS AL SZ0; unfold AHI_LO, ALOWSH_LO in *; lia). clear ARS AL. ps_prep.

    step. rewrite (unsigned_lit addr) by lia. change 7 with (Z.ones 3). rewrite Z.land_ones by lia. change (2^3) with 8.
    replace (addr mod 8) with 0 by lia.
    step. if_cases K; zify_cond K. { exfalso. lia. } clear K.

    step. step. step. step. step.
    replace (v_sltu (Z_to_bv 64 2147450880) (Z_to_bv 64 2147450879)) with (Z_to_bv 64 0) by (apply bv_eq; vm_compute; reflexivity).
    step. step. step. if_cases K; zify_cond K. 2:{ exfalso. rewrite ?unsigned_lit in K by lia. lia. } clear K.

    step. rewrite (unsigned_lit size) by lia. change 7 with (Z.ones 3). rewrite Z.land_ones by lia. change (2^3) with 8.
    replace (size mod 8) with 0 by lia.
    step. if_cases K; zify_cond K. { exfalso. lia. } clear K.
    step. step. step. if_cases K; zify_cond K. 2:{ exfalso. rewrite ?unsigned_lit in K by lia. lia. } clear K.
    apply poison_join.
  Qed.

  Lemma poison_walk2 : forall (x13 : word),
    evt asegs (poison_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 lo addr size v)
      (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp t0 t1 t2 s0 s1 (wz addr) (wz size) (wz v) x13 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0xbb45c) fc None m (seg_rom asegs)).
  Proof.
    intros x13. destruct (proj1 AR) as [[H _]|(_ & _ & H)]; [apply poison_walk2H; exact H| apply poison_walk2L; exact H].
  Qed.
End Part2.

Section Spec.
  Variables (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : mem).
  Variables (lo addr size v : Z) (sbs : list byte).
  Hypothesis MI : mem_inv asegs m.
  Hypothesis ST : stk asegs m lo (bv_unsigned sp).
  Hypothesis LO : aceil <= lo.  Hypothesis HI : lo + 64 <= bv_unsigned sp.
  Hypothesis Ha0 : a0 = wz addr. Hypothesis Ha1 : a1 = wz size. Hypothesis Ha2 : a2 = wz v.

  Hypothesis AR : ((AHI_LO <= addr /\ AHI_LO + 8 <= addr + size) \/ (0 <= addr /\ 8 <= addr + size /\ addr + size <= ALOWSH_LO))
                  /\ addr + size <= aceil /\ addr mod 8 = 0 /\ size mod 8 = 0 /\ 0 <= size.
  Hypothesis VR : 0 <= v < 256.
  Hypothesis SH : u8arr asegs m (sh addr) sbs.  Hypothesis SHL : Z.of_nat (length sbs) = size / 8.
  Hypothesis CCAN : rw_cells asegs m ACANPOISON [C1 (b8 1)].
  Hypothesis GOT : rw_cells asegs m AGOT_LO (map (fun v => C8 (wz v)) AGOT_VALS).
  Hypothesis CSHB : rw_cells asegs m ASHBASE_CELL [C8 (wz ASHADOW_BASE)].
  Hypothesis CHME : rw_cells asegs m AHIGHMEMEND [C8 (wz (2^47 - 1)); C8 (wz 0); C8 (wz 0)].
  Hypothesis CTHR : rw_cells asegs m (ACFLAGS + 120) [C8 (wz 0xffffffffffffffff)].
  Hypothesis CRMS : rw_cells asegs m AREALMEMSET [C8 (wz AMEMSET)].

  Theorem poison_shadow_spec :
    evt asegs (poison_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m lo addr size v)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0xbb428) fc None m (seg_rom asegs)).
  Proof.
    subst a0 a1 a2. unfold wz, ACANPOISON, AGOT_LO, AGOT_VALS, ASHBASE_CELL, ASHADOW_BASE, AHIGHMEMEND, ACFLAGS, AREALMEMSET, AMEMSET in *. cbn [map] in GOT.
    pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR. acb.
    assert (SHR : 0 <= sh addr /\ sh addr + size / 8 <= 17594333495296) by (clear - AR ACEILB; unfold sh, ASHADOW_BASE, ALOWSH_LO, AHI_LO in *; Z.div_mod_to_equations; lia).
    assert (LEN8 : Z.of_nat (length sbs) = size / 8) by exact SHL.
    pose proof (munch_refl [(bv_unsigned sp - 64, bv_unsigned sp); (sh addr, sh addr + size / 8)]%Z m) as MU.
    pose proof (wmono_refl asegs m) as WM.
    step. carve_frame 64%nat ST. step. step. step. step. step. step. step.

    step. if_cases K; zify_cond K.
    - eapply poison_walk2; eauto.
    -
      step. step. step. step. if_cases K2; zify_cond K2. { exfalso. revert K2. vm_compute. discriminate. }
      eapply poison_walk2; eauto.
  Qed.
End Spec.

End HCW.

