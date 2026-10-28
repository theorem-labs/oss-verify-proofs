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
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BSegs BsShadow BllocWf BllocKit BllocRep BsAtomics BllocWalkKit BidBits.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BllocTacX.
Import ListNotations.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BllocStoreDj.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_rx8 segs m a bs.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Open Scope bv_scope.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Section HCW.
  Context {HCEIL : HeapCeil}.

Local Unset Keyed Unification.

End HCW.

Ltac regval n := lazymatch goal with |- evt _ _ (MS ?R _ _ _ _ _ _) =>
   let p := eval vm_compute in (bv_key (Z_to_bv 5 n)) in
   eval cbv beta iota delta [tget mkR] in (tget p R) end.
Ltac nbv H := rewrite ?v_sltu_b2z in H; rewrite ?Z_to_bv_unsigned in H; unfold bv_wrap in H;
  change (bv_modulus 64) with 18446744073709551616%Z in H; change (2^64)%Z with 18446744073709551616%Z in H;
  repeat match goal with R : (0 <= ?e < 18446744073709551616)%Z |- _ => rewrite !(Z.mod_small e 18446744073709551616 R) in H end.
Ltac remreg n name eqname :=
  let v := regval n in
  lazymatch v with
  | Some (Z_to_bv 64 ?E) => rewrite <- (Z_to_bv_mod64 E); remember (E mod 2^64)%Z as name eqn:eqname; nbv eqname;
       let R := fresh "R" name in
       assert (R : (0 <= name < 18446744073709551616)%Z) by (rewrite eqname; apply Z.mod_pos_bound; reflexivity)
  | ?other => fail "remreg: register holds" other
  end.

Section HCW2.
  Context {HCEIL : HeapCeil}.

Definition combined_hit_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (m : mem) (lo P CA c sb cnt mc : Z) (chunks : list Z) : machine_state -> Prop :=
  fun ms' => exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (j0 j1 j2 j3 : word) m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz (sb + c * 2^32 + hd 0 chunks * 16)) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch [(bv_unsigned sp - 48, bv_unsigned sp); (P, P + 4); (CA + 2576, CA + 2584)]%Z m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo (bv_unsigned sp)
    /\ rw_cells asegs m' P [C4 (wz (cnt - 1)); C4 (wz mc)]
    /\ u32arr asegs m' (P + 16) (wlist (rev (tl chunks)))
    /\ stk asegs m' (P + 16 + 4 * (cnt - 1)) (P + 80)
    /\ rw_cells asegs m' (CA + CACHE_STATS) [C8 j0; C8 j1; C8 j2; C8 j3].

Section Part2.
  Variables (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : mem).
  Variables (lo c CA sb cnt mc : Z) (chunks : list Z) (j1 j2 : word) .
  Variable m0 : mem.
  Hypothesis MI : mem_inv asegs m.
  Hypothesis MU : munch [(bv_unsigned sp - 48, bv_unsigned sp); (CA + PCLASS_SIZE * c, CA + PCLASS_SIZE * c + 4); (CA + 2576, CA + 2584)]%Z m0 m.
  Hypothesis WM : wmono asegs m0 m.
  Hypothesis ST : stk asegs m lo (bv_unsigned sp + -48).
  Hypothesis LO : aceil <= lo.  Hypothesis HI : lo + 48 <= bv_unsigned sp. Hypothesis SPA : bv_unsigned sp mod 16 = 0.
  Hypothesis FR : rw_cells asegs m (bv_unsigned sp + -48) [C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].
  Hypothesis HC : 1 <= c < 32.
  Hypothesis CAR : akobj CA 2592 /\ CA + 2592 <= aceil /\ CA mod 16 = 0.
  Hypothesis SBR : 0 <= sb /\ sb + kSpaceSize <= aceil.
  Hypothesis INST : rw_cells asegs m (AINST + OI_SPACEBEG) [C8 (wz sb)].
  Hypothesis PC1 : rw_cells asegs m (CA + PCLASS_SIZE * c) [C4 (wz cnt); C4 (wz mc)].
  Hypothesis PC2 : rw_cells asegs m (CA + PCLASS_SIZE * c + 8) [C8 (wz (class_size c))].
  Hypothesis PC3 : u32arr asegs m (CA + PCLASS_SIZE * c + 16) (wlist (rev chunks)).
  Hypothesis CNT : cnt = zlen chunks. Hypothesis HIT : 1 <= cnt <= 16.
  Hypothesis PC4 : stk asegs m (CA + PCLASS_SIZE * c + 16 + 4 * cnt) (CA + PCLASS_SIZE * c + 80).
  Hypothesis CPS : Forall (fun cp => 0 <= cp < 2^32) chunks.
  Variables (j0 j3 : word).
  Hypothesis STATS : rw_cells asegs m (CA + CACHE_STATS) [C8 j0; C8 j1; C8 j2; C8 j3].

  Let CAE : 4096 <= CA /\ CA + 2592 <= aceil. Proof. exact (akobj_env _ _ (proj1 CAR) ltac:(clear; lia)). Qed.
  Lemma walk2 : forall (x14 : word), evt asegs (combined_hit_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 lo (CA + PCLASS_SIZE * c) CA c sb cnt mc chunks)
    (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 (Z_to_bv 64 c) s1 (Z_to_bv 64 AINST) (Z_to_bv 64 CA) a2 (Z_to_bv 64 8) x14 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x96d88) fc None m (seg_rom asegs)).
  Proof.
    intros x14. unfold AINST, OI_SPACEBEG, PCLASS_SIZE, CACHE_STATS, kSpaceSize in *.
    pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR. acb. unfold AHI_LO in *.
      step. if_cases K; zify_cond K. { exfalso. rewrite ?unsigned_lit in K by lia. lia. } clear K.
      step. step. if_cases K; zify_cond K. { exfalso. rewrite ?unsigned_lit in K by lia. lia. } clear K.

    remember (CA + 80 * c) as P eqn:HP. assert (PB : CA + 80 <= P /\ P + 80 <= CA + 2560) by lia.
    assert (LEN : Z.of_nat (length (wlist (rev chunks))) = cnt) by (unfold wlist; rewrite length_map, length_rev; unfold zlen in CNT; lia). change (1628632 + 32) with 1628664 in INST.
    step. step. step. rewrite (unsigned_lit c) by lia. replace (CA + c * 80) with P by lia.
    step. rewrite sx32_wz by lia.   step. if_cases K; zify_cond K. { exfalso. rewrite ?wz_unsigned in K by lia. lia. } clear K.

    step. step. step. st1.

    step. step. step. rewrite shl32_shr30 by lia. step.
    assert (NTH : nth_error (wlist (rev chunks)) (Z.to_nat (cnt - 1)) = Some (wz (hd 0 chunks))).
    { destruct chunks as [|cp rest]; [cbn in CNT; unfold zlen in CNT; cbn in CNT; lia|]. unfold wlist. cbn [rev hd]. rewrite map_app. cbn [map].
      rewrite nth_error_app2 by (rewrite length_map, length_rev; unfold zlen in CNT; cbn in CNT; lia).
      rewrite length_map, length_rev. replace (Z.to_nat (cnt - 1) - length rest)%nat with 0%nat by (unfold zlen in CNT; cbn in CNT; lia). reflexivity. }
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
      pose proof (u32arr_read asegs mc _ _ (cnt - 1) _ (wa (P + 16 + 4 * (cnt - 1))) PC3 NTH ltac:(hci; lia) ltac:(hci; unfold wa; f_equal; lia)) as RD end.
    replace (P + 4 * (cnt + -1)) with (P + 4 * (cnt - 1)) by lia.
    step. rewrite zx32_wz by (apply (Forall_forall _ _) with (x := hd 0 chunks) in CPS; [lia|]; destruct chunks; [unfold zlen in CNT; cbn in CNT; lia| left; reflexivity]).

    assert (AL8 : (CA + 2576) mod 8 = 0) by (clear - CAR; try acb; destruct CAR as (_ & _ & M); Z.div_mod_to_equations; aunf; lia).
    assert (ALR : 0 <= CA + 2576 < 2^64) by lia.
    astep.

    step. step. step. step. step.
    assert (CP : 0 <= hd 0 chunks < 2^32).
    { apply (Forall_forall _ _) with (x := hd 0 chunks) in CPS; [lia|]. destruct chunks; [unfold zlen in CNT; cbn in CNT; lia| left; reflexivity]. }
    rewrite (unsigned_lit c), (wz_unsigned (hd 0 chunks)) by lia. rewrite !Z.shiftl_mul_pow2 by lia.
    replace (Z_to_bv 64 (hd 0 chunks * 2 ^ 4 + (c * 2 ^ 32 + sb))) with (wz (sb + c * 2^32 + hd 0 chunks * 16)) by (unfold wz; f_equal; lia).

    step. step. if_cases K; zify_cond K. 2:{ exfalso. rewrite ?unsigned_lit in K by lia. lia. } clear K.
    step. step. step. step. step. step. step. step.
    release_frame FR ST (bv_unsigned sp). finish.
    all: destruct chunks as [|cp rest]; [unfold zlen in CNT; cbn in CNT; lia|]; cbn [tl]; unfold wlist in *; cbn [rev] in PC3;
         rewrite map_app in PC3; apply u32arr_snoc in PC3; destruct PC3 as [PA PB3]; rewrite length_map, length_rev in PB3;
         replace (Z.of_nat (length rest)) with (cnt - 1) in PB3 by (unfold zlen in CNT; cbn in CNT; lia).
    all: lazymatch goal with
         | |- u32arr _ _ _ _ => exact PA
         | |- stk _ _ _ _ => eapply stk_merge; [eapply stk_of_rw_cells; exact PB3| | cbn; lia]; cbn [cells_size csize Nat.add];
                             replace (P + 16 + 4 * (cnt - 1) + Z.of_nat 4) with (P + 16 + 4 * cnt) by lia; exact PC4
         | |- rw_cells _ _ _ _ => exact STATS
         end.
  Qed.
End Part2.

Section Spec.
  Variables (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : mem).
  Variables (lo size CA sb cnt mc : Z) (chunks : list Z) (j0 j1 j2 j3 : word).
  Let c := class_id size.
  Hypothesis MI : mem_inv asegs m.
  Hypothesis ST : stk asegs m lo (bv_unsigned sp).
  Hypothesis LO : aceil <= lo.  Hypothesis HI : lo + 48 <= bv_unsigned sp. Hypothesis SPA : bv_unsigned sp mod 16 = 0.
  Hypothesis Ha0 : a0 = wz AINST. Hypothesis Ha1 : a1 = wz CA. Hypothesis Ha2 : a2 = wz size. Hypothesis Ha3 : a3 = wz 8.
  Hypothesis SZ : 17 <= size <= kMaxSize.
  Hypothesis CAR : akobj CA 2592 /\ CA + 2592 <= aceil /\ CA mod 16 = 0.
  Hypothesis SBR : 0 <= sb /\ sb + kSpaceSize <= aceil.
  Hypothesis INST : rw_cells asegs m (AINST + OI_SPACEBEG) [C8 (wz sb)].
  Hypothesis PC1 : rw_cells asegs m (CA + PCLASS_SIZE * c) [C4 (wz cnt); C4 (wz mc)].
  Hypothesis PC2 : rw_cells asegs m (CA + PCLASS_SIZE * c + 8) [C8 (wz (class_size c))].
  Hypothesis PC3 : u32arr asegs m (CA + PCLASS_SIZE * c + 16) (wlist (rev chunks)).
  Hypothesis CNT : cnt = zlen chunks. Hypothesis HIT : 1 <= cnt <= 16.
  Hypothesis PC4 : stk asegs m (CA + PCLASS_SIZE * c + 16 + 4 * cnt) (CA + PCLASS_SIZE * c + 80).
  Hypothesis CPS : Forall (fun cp => 0 <= cp < 2^32) chunks.
  Hypothesis STATS : rw_cells asegs m (CA + CACHE_STATS) [C8 j0; C8 j1; C8 j2; C8 j3].

  Let CAE : 4096 <= CA /\ CA + 2592 <= aceil. Proof. exact (akobj_env _ _ (proj1 CAR) ltac:(clear; lia)). Qed.
  Theorem combined_hit_spec :
    evt asegs (combined_hit_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m lo (CA + PCLASS_SIZE * c) CA c sb cnt mc chunks)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x96bf4) fc None m (seg_rom asegs)).
  Proof.
    subst a0 a1 a2 a3. pose proof (class_id_range size ltac:(hci; unfold kMaxSize in SZ; lia)) as HC. fold c in HC.
    pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp); (CA + PCLASS_SIZE * c, CA + PCLASS_SIZE * c + 4); (CA + 2576, CA + 2584)]%Z m) as MU.
    pose proof (wmono_refl asegs m) as WM.
    unfold wz, AINST, OI_SPACEBEG, PCLASS_SIZE, CACHE_STATS, kMaxSize, kSpaceSize, AHI_LO in *.
    assert (LEN : Z.of_nat (length (wlist (rev chunks))) = cnt) by (unfold wlist; rewrite length_map, length_rev; unfold zlen in CNT; lia).
    pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR. acb.
    step. carve_frame 48%nat ST. step. step. step. step. step. step.

    step. rewrite v_sltiu_b2z. rewrite unsigned_lit by lia. change (bv_wrap 64 1) with 1.
    replace (Z.b2z (size <? 1)) with 0 by (rewrite zb_b2z_if; destruct (Z.ltb_spec size 1); lia).
    step. rewrite ?(unsigned_lit 0), ?Z.add_0_r by lia.
    step. rewrite (unsigned_lit size), zb_lxor_ones by lia.
    step. if_cases K; zify_cond K. 2:{ exfalso. rewrite ?unsigned_lit in K by lia. lia. } clear K.

    step. step. step. if_cases K; zify_cond K. 2:{ exfalso. rewrite ?unsigned_lit in K by lia. lia. } clear K.

    step. step. if_cases K; zify_cond K. { exfalso. rewrite ?unsigned_lit in K by lia. lia. } clear K.
    step. if_cases K; zify_cond K. { exfalso. rewrite ?unsigned_lit in K by lia. lia. } clear K.
    step. step. if_cases K; zify_cond K.
    2:{
        rewrite ?unsigned_lit in K by lia.
        step. step. rewrite (unsigned_lit (size + 31)), Z.shiftr_div_pow2 by lia. change (2^5) with 32.
        replace ((size + 31) / 32) with c.
        2:{ unfold c, class_id. replace (size <=? 512) with true by (symmetry; apply Z.leb_le; lia). reflexivity. }
        step. eapply walk2; eauto. }
    rewrite ?unsigned_lit in K by lia.

    assert (Rsize : 0 <= size < 18446744073709551616) by lia.

    step. step. step. step. step. step. remreg 12 e1 E1.

    step. step. step. step. step. step. remreg 12 e2 E2.

    do 8 step. step. step. remreg 12 e3 E3.
    step. step. remreg 12 e4 E4.
    step. step. remreg 12 e5 E5.
    step. step. remreg 12 e6 E6.
      step. remreg 12 e7 E7.
      step. step. step. remreg 12 e8 E8.
      step. step. step. step. remreg 12 e9 E9.
      step. step. remreg 12 e10 E10.
      step. step. step. step. step. remreg 12 e11 E11.
      step. remreg 15 e12 E12.
      step.
      step. remreg 17 e13 E13.
      step. remreg 15 e14 E14.
      step. step. step. step. remreg 14 e15 E15.
      step. step. step. step. remreg 8 e16 E16.

    replace e16 with c in *.
    2:{ symmetry. unfold c. eapply (cidbits_ok size); try eassumption. lia. }
    eapply walk2; eauto.
  Qed.
End Spec.

End HCW2.

