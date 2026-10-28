(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.mbedtls.fuzz_pkcs7.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Walk AEvt AStep HeapIface Asn1Aux CellsX Cells Mem Step Frame.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BB Require Import SymExec2 SymExec2Sound.
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Heap Require Import SFModel.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.U Require Import UImg U_string U_platform_zeroize U_platform_zeroize_proof.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Spec Require Import Rep RepCrt CrtStmts.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import H3Tac.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import DietDestruct.   (* [comment removed for export] *)
Import ListNotations.
Import SX2. Import SX2S.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import LiaOrc. (* [comment removed for export] *)
Local Ltac Stdlib.micromega.Lia.lia ::= orc_lia. (* [comment removed for export] *)
Local Ltac dlia ::= orc_dlia. (* [comment removed for export] *)
Local Ltac plia ::= orc_plia. (* [comment removed for export] *)
Local Ltac clear_disj ::= fc_clear_disj. (* [comment removed for export] *)
Local Ltac prune_disj ::= fc_prune_disj. (* [comment removed for export] *)
#[local] Existing Instance PropExec.fx0.
Open Scope Z_scope.
Set Printing Width 200.

(* [comment removed for export] *)

Section Walk.
  Variable L : heap_layout.
  Variable HI : heap_iface usegs L.
  Hypothesis HFREE : hl_free L = 0x3fa98.
  Hypothesis HMSF : const_at L U_MEMSET_FUNC 8.

  Local Ltac2 Set LiaOrc.tbl := fun () => "00W0?L13073081279.87L21765854580.60L21887662552.59L21887662552.85L24933826362.63L25964571294.63L26639116935.63L27775132660.60L28812006843.86L28812073603.58L33510041944.60L33510041944.85L34290115814.60L37622523289.88L43061431732.58L50632325648.61L52103792382.65L52343768858.85L53446206258.62L53516847639.86L53516911919.58L53519189168.61L54748384003.60L54976524414.63L54976524414.64L55076832172.88L63443598013.87L64516921136.85L66083662040.60L66083662040.85L66151427842.17L66364310271.86L6737796091.65 L68667153938.58L7190915604.61 L9716869748.59 L9743939885.63 L9962237875.60 L9962237875.85 00000@00I00R00[00g01701H01Q01]01i02202;02D02R02b02k03S04704@04I04R04[04d05Z06V06d06m07607?07H07b07k08V08b09K09T09]09f09oS2sp1A2lo3SLO2ABS2sp1A2ABS2sp1A2ABS2sp1A2ABS2sp1A2HA2ABS2sp1A2lo3SLO2ABS2sp1A2lo4DISJ2ABS2sp1A2ABS2sp1A2HA2ABS2sp1A2HA2ABS2sp1A2ABS2sp1A2ABS2sp1A2ABS2sp1A2AB1x2HxS2sp1A2lo3SLO2ABS2sp1A2ABS1L2sp1A2lo2HA3SLO3DHI3SPR5CEILn2AB1a2HaS2sp1A2lo2HA3HAL3SLO3SPA4DISJ3SPR2ABS2sp1A2ABS2sp1A2ABS2sp1A2ABS2sp1A2ABS2sp1A2ABS2ra2sp1A2lo2HA3HAL3SLO3SPA4DISJ3SPR2AB2HB5Ha_st5Hl_stS2sp2s01A2lo2HA3HAL3SLO3SPA4DISJ3SPR2AB2HB5Ha_st5Hl_st2s12s2S2sp1A2AB1x2HxS2sp1A2ABS2sp1A2ABS2sp1A2ABS2sp1A2ABS2sp2r03SPA1q1r1H2H02q02H4S2sp1A2ABS1L2sp1A2lo2HA3SLO3DHI2DD3SPR5CEILn2AB1a2HaS2sp1A2HA2ABS1L2sp1A2lo2HA3SLO3SPR5CEILn9ACB_CEILn2ABS2sp1A2ABS2sp1A2ABS2sp1A2ABS2sp1A2AB". (* [comment removed for export] *)
  #[using="HI HFREE HMSF"] Theorem U_x509_crl_free_spec : x509_crl_free_stmt usegs L 0x3eed4.
  Proof.
    intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m A lo
           CZ HA HAL ST SLO CEIL SPA DISJ SO DHI DD MI ->.
    pose proof (bv_unsigned_in_range 64 sp) as SPR. change (bv_modulus 64) with (2 ^ 64) in SPR.
    pose proof CEIL as CEILn. pose proof alloc_ceiling_bounds as ACB_CEILn.
    pose proof (proj2 (rw_cells_bound usegs m A _ CZ)) as AB. cbn [cells_size csize Nat.add] in AB.
    pose proof (munch_refl [(A, A + 416); (bv_unsigned sp - X509_CRL_FREE_STACK, bv_unsigned sp)] m) as MU.
    pose proof (wmono_refl usegs m) as WM.
    unfold X509_CRL_FREE_STACK in *. unfold crl_zero in CZ.
    assert (SOK : id (statics_ok usegs L m)) by exact SO.
    step. carve_frame 32%nat ST.                       (* [comment removed for export] *)
    step. step. step. step. step. ifc false.           (* [comment removed for export] *)
    step. step. step.                                  (* [comment removed for export] *)
    step. step. rewrite land_7_mod. ifc false.         (* [comment removed for export] *)
    step.                                              (* [comment removed for export] *)
    step.                                              (* [comment removed for export] *)
    (* [comment removed for export] *)
    replace (Z_to_bv 64 260760 : word) with (Z_to_bv 64 (hl_free L) : word) by (rewrite HFREE; reflexivity).
    eapply evt_cut; [eapply (heap_free_null usegs L HI); reflexivity |]. intros ms' ->.
    replace (ret_pc (Z_to_bv 64 0x3ef10)) with (Z_to_bv 64 0x3ef10 : word) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]).
    step. step.                                        (* [comment removed for export] *)
    step. carve_frame 16%nat ST. step. step. step. ifc true. step. step. lazymatch goal with F0 : rw_cells _ _ (bv_unsigned sp + -48) _ |- _ => release_frame F0 ST (bv_unsigned sp + -32) end. step. step. (* [comment removed for export] *)
    step. step. ifc true.                              (* [comment removed for export] *)
    step. step. ifc true.                              (* [comment removed for export] *)
    step. step. step. step.                            (* [comment removed for export] *)
    replace (bv_extract 0 64 (le_bytes_to_word (firstn 8 (skipn 408 (zeros 416))))) with (Z_to_bv 64 0 : word) by (vm_compute; reflexivity).
    lazymatch goal with CZH : rw_cells usegs ?mm A [CB 416 ?zz] |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      change (CB 416 zz) with (CB (Z.to_nat 416) zz) in CZH end.
    pose proof (u_small (bv_unsigned sp + -32) ltac:(lia)) as USP.
    lazymatch goal with CZH : rw_cells usegs ?mm A [CB _ _], STH : stk usegs ?mm lo _, MIH : mem_inv usegs ?mm, MUH : munch _ m ?mm |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      pose proof (statics_ok_munch usegs L _ m mm SOK MUH ltac:(intros a Ha Hna; cbn [outside]; split; [lia | split; [lia | exact I]])) as SO1;
      eapply evt_cut;
      [ eapply (U_platform_zeroize_spec L) with (A := A) (n := 416) (lo := lo);
        [ exact CZH | lia | lia | rewrite USP; exact STH | rewrite USP; lia | exact CEIL
        | rewrite USP; clear - SPA SPR; Z.div_mod_to_equations; lia
        | rewrite USP; lia | exact SO1 | exact HMSF | exact DHI | exact DD | exact MIH | reflexivity | reflexivity ]
      | ] end.
    intros ms' PO. ddestruct PO as (v0 & v1 & v2 & va0 & va1 & va2 & va3 & va4 & va5 & va6 & va7 & v3 & v4 & v5 & v6 & m2 & -> & MU2 & WM2 & MI2 & CZ2 & ST2 & SO2).
    rewrite USP in MU2, ST2. change (Z.to_nat 416) with 416%nat in CZ2.
    replace (ret_pc (Z_to_bv 64 0x3ef5c)) with (Z_to_bv 64 0x3ef5c : word) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]).
    lazymatch goal with FRH : rw_cells usegs ?mm (bv_unsigned sp + -32) ?cs, MUH : munch ?W m ?mm, WMH : wmono _ m ?mm |- _ =>
      pose proof (rw_cells_transport usegs _ mm m2 _ _ FRH MU2 WM2 ltac:(cbn; lia)) as FR2;
      assert (SUBW : sub_fp [(A, A + 416); (bv_unsigned sp + -32 - 16, bv_unsigned sp + -32)] W)
        by (intros x Hx; cbn [outside] in Hx |- *; repeat split; try exact I; lia);
      pose proof (munch_trans _ _ _ _ MUH (munch_weaken _ _ _ _ SUBW MU2)) as MU3;
      pose proof (wmono_trans usegs _ _ _ WMH WM2) as WM3;
      clear FRH MUH WMH
    end.
    step. ifc true.                                    (* [comment removed for export] *)
    step. step. ifc true.                              (* [comment removed for export] *)
    step. step. step. step. step. step.                (* [comment removed for export] *)
    apply evt_done. unfold x509_crl_free_post.
    deexists 15. exists m2. split; [reflexivity|].
    split; [exact MU3|]. split; [exact WM3|]. split; [exact MI2|]. split; [exact CZ2|]. split; [|exact SO2].
    pose proof (stk_of_rw_cells usegs m2 _ _ FR2) as K. cbn [cells_size csize Nat.add] in K.
    eapply stk_merge; [exact ST2 | | lia]. replace (bv_unsigned sp) with (bv_unsigned sp + -32 + Z.of_nat 32) at 2 by lia. exact K.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
End Walk.
