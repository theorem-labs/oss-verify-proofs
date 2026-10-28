(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Bs0Gc.
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BeapCeil.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BTac BArr BBytes BZBridge BacX BSFModel BSysStep.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BSegs BsShadow BsConst BsIface BsWalk BakeStackRep B5_tls B5_smkit RtB_Iface RtB_SMKit.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BStrFun BTRW_memset.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import B8Store.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_n8 segs m a bs.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Section FL6.
  Context {HCEIL : HeapCeil}.
  Variables (ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (SF : Z) (m0 : mem).
  Hypothesis SFR : 0 <= SF /\ SF + 512 < 2^64.

  Definition fl6_post : machine_state -> Prop :=
    fun ms' => exists m',
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (SF + 512)) (Z_to_bv 64 17723342345328784885) (Z_to_bv 64 (SF + 512)) a3 a4 a5 a6 a7
                    s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (Z_to_bv 64 0x9e4d0) fc None m' (seg_rom asegs)
      /\ u8arr asegs m' SF (repeat (Z_to_bv 8 245) 512) /\ mem_inv asegs m' /\ munch [(SF, SF + 512)] m0 m' /\ wmono asegs m0 m'.

  Lemma fl6 : forall (K : nat) (p : Z) (m : mem) (bs : list byte),
    Z.to_nat ((512 - p) / 8) = K -> 0 <= p <= 504 -> p mod 8 = 0 ->
    u8arr asegs m SF bs -> filled (Z_to_bv 8 245) bs (fun j => 0 <= j < p) -> length bs = Z.to_nat 512 ->
    mem_inv asegs m -> munch [(SF, SF + 512)] m0 m -> wmono asegs m0 m ->
    evt asegs fl6_post
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (SF + p)) (Z_to_bv 64 17723342345328784885) (Z_to_bv 64 (SF + 512)) a3 a4 a5 a6 a7
               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x9e4c4) fc None m (seg_rom asegs)).
  Proof.
    induction K as [|K IH]; intros p m bs HK Hp Hp8 ARR FIL LEN MI MU WM.
    { exfalso. Z.div_mod_to_equations. lia. }
    mst p 8%nat ltac:(first [ exact le8_f5 | (symmetry; exact le8_f5) | (vm_compute; reflexivity) ]).
    zstep. zstep. if_cases KK; zify_cond KK;
      change 18446744073709551615 with (Z.ones 64) in KK; rewrite ?Z.land_ones in KK by lia; rewrite ?Z.mod_small in KK by lia.
    -
      replace (SF + p + 8) with (SF + (p + 8)) by lia.
      assert (N8 : p + 8 <> 512) by lia.
      eapply (IH (p + 8)); try eassumption.
      + Z.div_mod_to_equations. lia.
      + Z.div_mod_to_equations. lia.
      + Z.div_mod_to_equations. lia.
      + eapply filled_mono; [exact FIL|]. cbv beta. intros j Hj. lia.
    -
      assert (E8 : p + 8 = 512) by lia.
      apply evt_done. unfold fl6_post.
      pose proof (filled_all _ _ _ FIL) as FA.
      rewrite LEN in FA. change (Z.of_nat (Z.to_nat 512)) with 512 in FA.
      assert (EB : forall j, 0 <= j < 512 -> (0 <= j < p \/ p <= j < p + Z.of_nat 8)) by (intros j Hj; lia).
      specialize (FA EB). rewrite FA in ARR. change (Z.to_nat 512) with 512%nat in ARR.
      eexists. split; [| split; [exact ARR| split; [exact MI| split; [exact MU| exact WM]]]].
      replace (SF + p + 8) with (SF + 512) by lia. reflexivity.
  Qed.
End FL6.

Section SF6.
  Context {HCEIL : HeapCeil}.
  Variable H : asr.
  Hypothesis RFS_is : forall LF m, as_RFS H LF m <-> RFSI (as_FSB H) LF m.

  Lemma stack_free_6_ok : stack_free_stmt H 6 AFS_FREE_6.
  Proof.
    intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m LF ff fp lo.
    intros RFS IN Ha0 FPC ST0 LO LOSP MI AC. subst a0.
    pose proof (proj1 (RFS_is LF m) RFS) as R.
    remember (as_FSB H) as fsb eqn:Hfsb.
    pose proof R as ((G1 & G2 & G3 & G4) & TLS & HDR & SL & ND & FL & STF & STS).
    acb; unfold AFS_STACK, AFS_FREE_6, AFS_SIZE, AFS_HDR, AIMG_TOP in *.
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. change (2 ^ Z.of_N 64) with (2^64) in SPR.

    destruct (SL _ IN) as (pos & SOK & EFF & EFP). cbn [ff_class ff_addr ff_flag fst snd] in SOK, EFF, EFP.
    pose proof SOK as [[K0 K1] PR]. unfold NF in PR. change (2 ^ (14 - 6)) with 256 in PR.
    assert (EFF' : ff = fsb + 6328320 + 4096 * pos) by (rewrite EFF; unfold frame_addr, AFS_HDR, fsz; cbn; lia).
    assert (EFP' : fp = fsb + 36352 + pos) by (rewrite EFP; unfold flag_addr, AFS_HDR; cbn; lia).
    clear EFF EFP.

    pose proof (FL 6 pos SOK) as CFP. unfold flagv in CFP.
    replace (liveb LF (flag_addr fsb 6 pos)) with true in CFP.
    2:{ symmetry. apply liveb_true. exists (6, ff, fp). split; [exact IN|]. cbn. rewrite EFP'. unfold flag_addr, AFS_HDR. cbn. lia. }
    replace (flag_addr fsb 6 pos) with fp in CFP by (rewrite EFP'; unfold flag_addr, AFS_HDR; cbn; lia).
    unfold fsz in FPC. change (64 * 2 ^ 6) with 4096 in FPC. replace (ff + 4096 - 8) with (ff + 4088) in FPC by lia.

    remember (sh ff) as SF eqn:HSF.
    assert (SFR : 2148356096 <= SF /\ SF + 512 <= 17594333495296 /\ sh fsb <= SF /\ SF + 512 <= sh (fsb + 11571200)).
    { subst SF. unfold sh. rewrite ASHADOW_BASE_val. Z.div_mod_to_equations. lia. }
    assert (SEP : fsb + 11571200 <= 2147446784 \/ 17594333495296 <= fsb)
      by (clear - G4; destruct G4 as [[X1 X2]|[X1 X2]]; unfold AIMG_TOP, ALOWSH_LO, AHI_LO, AFS_SIZE in X1, X2; lia).
    destruct (stk_split asegs m _ (SF + 512) _ STS ltac:(lia)) as [SSa SSc].
    destruct (stk_carve asegs m _ _ 512 SSa ltac:(lia)) as [SSa' [sjunk SRM]].
    replace (SF + 512 - Z.of_nat 512) with SF in SSa', SRM by lia. clear SSa SSc.

    pose proof (ACONST_mts m AC) as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6).
    unfold AGOT_SHBASE, ASHBASE_CELL, AGOT_MIDBEG, AMIDBEG_CELL, AGOT_MIDEND, AMIDEND_CELL, AGOT_HIEND, AHIEND_CELL, wz in Q1, Q2, Q3, Q4, Q5, Q6.

    pose proof (munch_refl [(bv_unsigned sp - 1024, bv_unsigned sp); (fp, fp + 1); (SF, SF + 512)] m) as MU.
    pose proof (wmono_refl asegs m) as WM.
    pose proof ST0 as ST. carve_frame 16%nat ST.

    zstep. st1. st1.

    zstep. st1. zstep. st1.

    zstep.
    call_pure mts_spec; try reflexivity; try eassumption;
      [clear - G4 EFF' PR; destruct G4 as [[G4a G4b]|[G4a G4b]]; unfold AIMG_TOP, ALOWSH_LO, AHI_LO, AAPP_HI, AFS_SIZE in *; [left | right]; acb; lia|].
    rewrite <- HSF.

    zstep. zstep. zstep.
    pose proof (rw_cells_CB_length _ _ _ _ _ SRM) as SLEN. apply u8arr_of_rw_cells in SRM.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
      pose proof (munch_refl [(SF, SF + 512)] mx) as MUL; pose proof (wmono_refl asegs mx) as WML end.
    replace (Z_to_bv 64 SF) with (Z_to_bv 64 (SF + 0)) by (rewrite Z.add_0_r; reflexivity).
    eapply evt_cut.
    { eapply (fl6 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ SF _ ltac:(lia) 64%nat 0); rewrite ?Z.add_0_r;
        first [ reflexivity | exact SRM | exact MUL | exact WML | eassumption | lia | idtac ].
      all: first [ (eapply filled_mono; [exact (filled_init _ _)|]; cbv beta; intros j Hj; lia) | (rewrite SLEN; reflexivity) ]. }
    intros ms' (mz & -> & SRM' & MIz & MUz & WMz).
    lazymatch type of MUL with munch _ ?mL _ => transport_after_call asegs mL mz MUz WMz end. clear MUL WML.

    zstep. zstep. zstep. zstep.
    clear ST0. release_frame FR ST (bv_unsigned sp).
    assert (FF8 : 0 <= ff /\ ff mod 8 = 0) by (rewrite EFF'; Z.div_mod_to_equations; lia).
    subst SF fsb. unfold stack_free_post. finish.
    all: lazymatch goal with
         | |- munch _ _ _ => exact MU
         | |- SHAD _ _ _ => split; [lia|]; split; [lia| exact SRM']
         | |- ACONST _ => eapply ACONST_frame; [exact AC| exact MU| exact WM|];
                          repeat apply Forall_cons; [| | |apply Forall_nil]; aconst5 G1 G4
         | |- as_RFS _ _ _ =>
              eapply (RFSI_release H RFS_is LF m _ _ 6 ff fp); [exact RFS| exact IN| exact MU| exact WM| |];
              [ unfold afs_write_ok, AFS_SIZE, ATLS_PRIV_LO, ATLS_PRIV_HI, ATP in *;
                repeat apply Forall_cons; [left; left; cbn; split; lia | right; cbn; split; reflexivity | left; left; cbn; split; lia | apply Forall_nil ]
              | erewrite rw_cells_C1_mrd; [reflexivity| eassumption] ]
         | _ => idtac
         end.
  Qed.
End SF6.
