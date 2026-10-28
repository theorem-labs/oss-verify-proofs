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
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BStrFun.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BSegs BsShadow BllocWf BllocKit BllocRep BsAtomics BllocWalkKit BW_Leaves.
Import ListNotations.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BllocStoreDj.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_rx8 segs m a bs.
Open Scope bv_scope.
Open Scope Z_scope.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Section HCW.
  Context {HCEIL : HeapCeil}.

Local Unset Keyed Unification.

End HCW.

Ltac deadK K := first [ exfalso; apply K; reflexivity
                      | exfalso; revert K; vm_compute; discriminate
                      | exfalso; revert K; rewrite ?unsigned_lit by lia; lia ].

Section HCW2.
  Context {HCEIL : HeapCeil}.

Definition mrto_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) (lo : Z)
    : machine_state -> Prop :=
  fun ms' => exists (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch [(bv_unsigned sp - 80, bv_unsigned sp)]%Z m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo (bv_unsigned sp).

Section Mrto.
  Variables (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : mem).
  Variables (lo sb ARI c nf : Z).
  Let R := ARI + REGIONINFO_SIZE * c.
  Hypothesis MI : mem_inv asegs m.
  Hypothesis ST : stk asegs m lo (bv_unsigned sp).
  Hypothesis LO : aceil <= lo.  Hypothesis HI : lo + 80 <= bv_unsigned sp.
  Hypothesis Ha0 : a0 = wz AINST. Hypothesis Ha2 : a2 = wz c. Hypothesis Ha3 : a3 = wz 0.
  Hypothesis CR : 1 <= c < kNumClasses. Hypothesis NFR : 0 <= nf < 2^64.
  Hypothesis ARIR : AHI_LO <= ARI /\ ARI + 4096 <= aceil /\ ARI mod 4096 = 0.
  Hypothesis IRI : rw_cells asegs m (AINST + 48) [C8 (wz ARI)].
  Hypothesis ISB : rw_cells asegs m (AINST + 32) [C8 (wz sb); C4 (wz 0xffffffff); C4 (wz 0)].
  Hypothesis GOT : rw_cells asegs m AGOT_LO (map (fun v => C8 (wz v)) AGOT_VALS).
  Hypothesis PSC : rw_cells asegs m APAGESZ [C8 (wz 4096)].
  Hypothesis RNF : rw_cells asegs m (R + 16) [C8 (wz nf)].

  Hypothesis RS8 : stk asegs m (R + 80) (R + 96).

  Lemma mrto_tail : forall (x5 x6 x7 x10 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 csz : word) (mX : mem) (j24 : list byte),
    mem_inv asegs mX -> munch [(bv_unsigned sp - 80, bv_unsigned sp)]%Z m mX -> wmono asegs m mX ->
    stk asegs mX lo (bv_unsigned sp + -80) ->
    rw_cells asegs mX (bv_unsigned sp + -80) [CB 8 j24; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
    evt asegs (mrto_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m lo)
      (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -80)) gp tp x5 x6 x7 a1 (wz c) x10 (wz (c * 128)) x12 x13 x14 x15 x16 x17
               csz (wz AINST) s4 (wz 0) (wz ARI) s7 s8 s9 s10 s11 x28 x29 x30 x31)
          F (Z_to_bv 64 0x9560c) fc None mX (seg_rom asegs)).
  Proof.
    intros until j24. intros MIX MU WM STX FR.
    unfold AHI_LO, REGIONINFO_SIZE, AINST, AGOT_LO, APAGESZ, kNumClasses in *. unfold AGOT_VALS in GOT. cbn [map] in GOT.
    change (1628632 + 48) with 1628680 in IRI. change (1628632 + 32) with 1628664 in ISB.
    pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR. acb.
    pose proof (bv_unsigned_in_range _ csz) as CSR. change (bv_modulus 64) with (2^64) in CSR.

    destruct (stk_cells _ _ _ RS8 ltac:(hci; clear; lia)) as [sj SJ].
    replace (R + 96 - (R + 80)) with 16 in SJ by (clear; lia). change (Z.to_nat 16) with 16%nat in SJ.
    apply (rw_cells_split_CB asegs _ _ [] 16 sj [] [8;8]%nat) in SJ; [| reflexivity]. cbn [mk_CB_cells app] in SJ.
    repeat match type of SJ with context [CB ?k (take ?i ?l)] => let J := fresh "jk" in remember (take i l) as J in SJ end.
    repeat match type of SJ with context [CB ?k (drop ?i ?l)] => let J := fresh "jk" in remember (drop i l) as J in SJ end.
    repeat match goal with H : _ = take _ _ |- _ => clear H | H : _ = drop _ _ |- _ => clear H end.
    transport_after_call asegs m mX MU WM.
    unfold wz in *.

    step. step. step. step. rewrite ?(unsigned_lit c), ?(unsigned_lit (c * 128)), ?(unsigned_lit ARI) by (clear - CR ARIR; try acb; lia).
    replace (ARI + c * 128) with R by (subst R; clear; lia).
    step. if_cases K; zify_cond K. { deadK K. } clear K.

    step. step. step. if_cases K; zify_cond K.
    -
      clear K. step. step. step. step. step. if_cases K2; zify_cond K2.
      + clear K2.   do 9 step. step. step. release_frame FR STX (bv_unsigned sp). finish.
      + clear K2. step. if_cases K3; zify_cond K3. { deadK K3. } clear K3.
        step. step. if_cases K4; zify_cond K4. 2:{ exfalso. revert K4. vm_compute. discriminate. } clear K4.
        do 9 step. step. step. release_frame FR STX (bv_unsigned sp). finish.
    - clear K. step.   do 9 step. step. step. release_frame FR STX (bv_unsigned sp). finish.
  Qed.

  Theorem mrto_spec :
    evt asegs (mrto_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m lo)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x95590) fc None m (seg_rom asegs)).
  Proof.
    pose proof mrto_tail as TL.
    unfold AHI_LO, REGIONINFO_SIZE, AINST, kNumClasses in *. subst a0 a2 a3.
    change (1628632 + 48) with 1628680 in IRI. change (1628632 + 32) with 1628664 in ISB.
    pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR. acb.
    pose proof (munch_refl [(bv_unsigned sp - 80, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl asegs m) as WM.
    clear RS8 RNF GOT PSC.
    unfold wz in *.

    step. carve_frame 80%nat ST. do 9 step.

    step. step. step. step. step. step. step.
    rewrite (unsigned_lit c) by (clear - CR; try acb; lia). rewrite (Z.shiftl_mul_pow2 c 7) by (clear; lia). change (2^7) with 128.
    step. if_cases K; zify_cond K.
    -
      step. step.
      eapply TL; eassumption.
    -
      step. step. if_cases K2; zify_cond K2.
      +
        do 9 step.
        eapply TL; eassumption.
      +
        step. step.
        eapply TL; eassumption.
  Qed.
End Mrto.

End HCW2.

