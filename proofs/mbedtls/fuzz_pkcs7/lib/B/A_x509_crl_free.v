(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import CellsX.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Spec Require Import Rep RepCrt.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import AImg AImgRT A_alloc_lib A_platform_zeroize A_crt_stmts.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import HeapIface.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import AUnw. From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibB Require Import TacA.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import A_frame_lib.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import DietDestruct.   (* [comment removed for export] *)
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibB Require Import FF5. (* [comment removed for export] *)
Local Ltac pqlia ::= ff5_pqlia.
Local Ltac transport_after_call segs m m' MU WM ::= ff5_transport_after_call segs m m' MU WM.
Local Ltac solve_apart ::= ff5_solve_apart.
Local Ltac solve_apart0 ::= ff5_solve_apart0.
Local Ltac solve_disjoint ::= ff5_solve_disjoint.
(* [comment removed for export] *)
Local Ltac2 e25kn_keep_near (t : Init.constr) : Init.unit :=
  let seed := FF5.ffn_vars (FSet.empty FSet.Tags.ident_tag) t in
  let e := LiaTuning.zf_mkenv () in
  let (ids, _) := List.fold_left (fun acc h =>
      let (ids, cache) := acc in
      let (id, body, ty) := h in
      match body with
      | Init.Some _ => acc
      | Init.None =>
          let (isp, cache) := LiaTuning.zf_is_prop cache ty in
          if isp then
            (if LiaTuning.zf_plain_arith e ty then
               (if FSet.is_empty (FSet.inter seed (FF5.ffn_vars (FSet.empty FSet.Tags.ident_tag) ty))
                then (id :: ids, cache) else (ids, cache))
             else (id :: ids, cache))
          else (ids, cache)
      end) ([], { LiaTuning.zc_c := FMap.empty FSet.Tags.constant_tag; LiaTuning.zc_i := FMap.empty FSet.Tags.inductive_tag })
      (Control.hyps ()) in
  match ids with
  | [] => ()
  | _ :: _ => match Control.case (fun () => Std.clear ids) with
              | Init.Val _ => ()
              | Init.Err _ => List.iter (fun id => match Control.case (fun () => Std.clear [id]) with Init.Val _ => () | Init.Err _ => () end) ids
              end
  end.
Ltac ff_keep_near t ::= let f := ltac2:(t |- e25kn_keep_near (Option.get (Ltac1.to_constr t))) in f t.
Ltac2 gd_tbl_A_x509_crl_free () : Init.string Init.list := ["RocqVerifyHarness.AgentSubmission.LibB.ARt.art_layout"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.artA"; "RocqVerifyHarness.AgentSubmission.B.AImg.asegs"; "RocqVerifyHarness.AgentSubmission.B.AImg.asan_img_ok"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_AL"; "Corelib.Init.Logic.eq"; "Corelib.Numbers.BinNums.Z"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_free"; "A_WRAP_FREE"; "Stdlib.ZArith.BinInt.Z.le"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_need_free"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_need_amem"; "RocqVerifyHarness.AgentSubmission.B.A_platform_zeroize.platform_zeroize_stmtA"; "RocqVerifyHarness.AgentSubmission.B.A_platform_zeroize.A_PLATFORM_ZEROIZE"; "RocqVerifyHarness.AgentSubmission.B.A_crt_stmts.x509_crl_free_stmtA"; "X509_CRL_FREE_STACK_A"; "A_X509_CRL_FREE"].


Definition A_X509_CRL_FREE : Z := 0x0da5f8.   (* [comment removed for export] *)
Definition A_WRAP_FREE : Z := 0x6947c.          (* [comment removed for export] *)
(* [comment removed for export] *)
Definition X509_CRL_FREE_STACK_A (R : art_layout) : Z := 80 + Z.max (arl_need_free R) (arl_need_amem R).

From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import BX_zchk.
Local Ltac zchk_fails ::= constr:([0xda748]).
Local Ltac zchk_new ::= constr:([0xda634; 0xda638; 0xda690; 0xda694]).
Local Ltac zstep ::= zpre; step; zsimp; zpre.

Section Walk.
  Variable R : art_layout.
  #[local] Hint Extern 0 heap_layout => exact (arl_L R) : typeclass_instances.
  Variable HIA : artA asegs R.
  Local Notation AL := (arl_AL R).
  Local Notation L := (arl_L R).
  Hypothesis IMG : asan_img_ok AL.
  Hypothesis HFREE : arl_free R = A_WRAP_FREE.
  Hypothesis NEEDF : 0 <= arl_need_free R.
  Hypothesis NEEDA : 0 <= arl_need_amem R.
  Hypothesis PZ : platform_zeroize_stmtA asegs R HIA A_PLATFORM_ZEROIZE.

  #[using="IMG HFREE NEEDF NEEDA PZ"] Theorem x509_crl_freeA : x509_crl_free_stmtA asegs R HIA (X509_CRL_FREE_STACK_A R) A_X509_CRL_FREE.
  Proof.
    unfold x509_crl_free_stmtA, A_X509_CRL_FREE. intros h LB LF. intros until lo. intros HH CZ HA HAL OBJ CW DS ST LOS SLO TOP SPA MI TPV ->.
    unfold X509_CRL_FREE_STACK_A in SLO.
    pose proof (hcs_ok asegs R HIA h) as CSOK. pose proof (cs_ok_sb _ _ CSOK) as SB64.
    pose proof (art_alwf asegs R HIA) as ALWF'. unfold al_wf in ALWF'. pose proof IMG as IMG'. unfold asan_img_ok in IMG'. ddestruct IMG' as (EGOT & ELO & EHI).
    pose proof (art_lo asegs R HIA) as ALO. pose proof (alloc_ceiling_val R) as ACV.
    pose proof (hcs_stack asegs R HIA h) as SCS0. pose proof (hm_top asegs R HIA h LB LF m HH) as HTOP.
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn [Z.pow Z.of_N Pos.pow] in SPR.
    assert (SCS : crange (hcs asegs R HIA h) lo (bv_unsigned sp - lo)) by (eapply crange_sub; [exact SCS0| clear - LOS; lia| clear - SLO NEEDF NEEDA TOP HTOP; lia]).
    pose proof (rw_cells_bound _ _ _ _ CZ) as AB. cbn [cells_size csize Nat.add] in AB.
    pose proof (hm_wlow asegs R HIA h LB LF m HH) as WL.
    pose proof (presW_init asegs R HIA h LB LF m (bv_unsigned sp) (arl_stklo R) [(A, A + 416)] HH ltac:(clear; lia)) as PRES.
    unfold crl_zero in CZ.
    (* [comment removed for export] *)
    zstep. carve_frame 48%nat ST. zstep. zstep. zstep. zstep. zstep.
    (* [comment removed for export] *)
    zstep. if_cases K0; zify_cond K0; [rewrite ?unsigned_lit in K0 by (clear - HA AB; lia); exfalso; clear - K0 HA; lia|]. clear K0.
    (* [comment removed for export] *)
    zstep. zstep.
    lazymatch goal with |- _ (MS _ _ _ _ _ ?mc _) => lazymatch goal with HHc : HM _ _ _ h LB LF mc |- _ =>
      pose proof (hm_abase asegs R HIA h LB LF mc HHc) as AB0; pose proof (abase_got _ _ _ AB0) as GOT; pose proof (abase_gsb _ _ _ AB0) as GSB end end.
    rewrite EGOT in GOT.
    zstep. zstep. clear GOT GSB AB0.
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep. zstep. zstep. zstep.
    (* [comment removed for export] *)
    zstep.
    replace (bv_extract 0 64 (le_bytes_to_word (firstn 8 (skipn 400 (zeros 416))))) with (Z_to_bv 64 0 : word) by (vm_compute; reflexivity).
    (* [comment removed for export] *)
    zstep.
    replace (Z_to_bv 64 431228) with (Z_to_bv 64 (arl_free R)) by (rewrite HFREE; reflexivity).
    lazymatch goal with |- _ (MS _ _ _ _ _ ?mc _) => lazymatch goal with HHc : HM _ _ _ h LB LF mc |- _ =>
      callrt (bv_unsigned sp + -48) (eapply (heapA_free_null asegs R HIA) with (h := h) (LB := LB) (LF := LF) (lo := lo);
         rewrite ?(unsigned_lit (bv_unsigned sp + -48)) by (clear - SPR SLO NEEDF NEEDA LOS ALO ACV; lia);
         first [ exact HHc | exact LOS | exact TPV | reflexivity
               | lazymatch goal with
                 | |- stk _ mc lo _ => assumption
                 | |- lo <= _ => clear - SLO NEEDF NEEDA; lia
                 | |- _ <= htop _ _ _ _ => clear - TOP; lia
                 | |- _ mod 16 = 0 => clear - SPA; Z.div_mod_to_equations; lia
                 | |- mem_inv _ mc => assumption
                 end
               | match goal with |- ?g => idtac "FREE0-LEFT:" g end ]) end end.
    lazymatch goal with H : presA _ _ _ _ _ _ _ _ ?ma ?mb |- _ (MS _ _ _ _ _ ?mb _) =>
      rename H into HPf; presA_transport HPf; clear HPf;
      try (lazymatch goal with H' : mem_inv _ ma |- _ => clear H' end); try (lazymatch goal with H' : HM _ _ _ _ _ _ ma |- _ => clear H' end) end.
    lazymatch goal with H : exists h' : HST _ _ _, _ |- _ => destruct H as (h1 & E1cs & E1top & E1stk & E1flag & E1vol & E1fr & HKI1 & HH1) end.
    lazymatch goal with |- _ (MS _ _ _ _ _ ?mc _) => rename mc into m1 end.
    try (lazymatch goal with W : wmono _ _ m1 |- _ => clear W end).
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep. zstep. zstep.
    replace (bv_extract 0 64 (le_bytes_to_word (firstn 8 (skipn 152 (zeros 416))))) with (Z_to_bv 64 0 : word) by (vm_compute; reflexivity).
    zstep.
    (* [comment removed for export] *)
    lazymatch goal with STc : stk _ m1 lo (bv_unsigned sp + -48) |- _ => zstep; carve_frame 32%nat STc end.
    zstep. zstep. zstep.
    (* [comment removed for export] *)
    zstep.
    zstep. zstep. zstep. zstep. zstep.
    lazymatch goal with FRi : rw_cells _ ?mc (bv_unsigned sp + -80) _, STi : stk _ ?mc lo (bv_unsigned sp + -80) |- _ =>
      release_frame FRi STi (bv_unsigned sp + -48) end.
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep. zstep. zstep.
    replace (bv_extract 0 64 (le_bytes_to_word (firstn 8 (skipn 312 (zeros 416))))) with (Z_to_bv 64 0 : word) by (vm_compute; reflexivity).
    zstep.
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep. zstep. zstep.
    replace (bv_extract 0 64 (le_bytes_to_word (firstn 8 (skipn 16 (zeros 416))))) with (Z_to_bv 64 0 : word) by (vm_compute; reflexivity).
    zstep.
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep. zstep. zstep.
    replace (bv_extract 0 64 (le_bytes_to_word (firstn 8 (skipn 408 (zeros 416))))) with (Z_to_bv 64 0 : word) by (vm_compute; reflexivity).
    zstep. zstep. zstep.
    lazymatch goal with |- _ (MS _ _ _ _ _ ?mc _) => rename mc into m3 end.
    lazymatch type of CZ with rw_cells _ _ _ [CB 416 ?zz] => change (CB 416 zz) with (CB (Z.to_nat 416) zz) in CZ end.
    pose proof PZ as SPZ. unfold platform_zeroize_stmtA, A_PLATFORM_ZEROIZE in SPZ. specialize SPZ with (h := h1). rewrite E1cs, E1top in SPZ.
    callxA_sp (bv_unsigned sp + -48)
      (eapply SPZ with (LB := LB) (LF := LF) (A := A) (n := 416) (lo := lo);
       rewrite ?(unsigned_lit (bv_unsigned sp + -48)) by (clear - SPR SLO NEEDF NEEDA LOS ALO ACV; lia);
       first [ exact HH1 | exact CZ | exact HA | exact LOS | exact DS | reflexivity
             | lazymatch goal with
               | |- 0 <= 416 => clear; lia
               | |- 416 < _ => clear; lia
               | |- stk _ m3 lo _ => assumption
               | |- lo <= _ => clear - SLO NEEDF NEEDA; lia
               | |- _ <= htop _ _ _ _ => clear - TOP; lia
               | |- _ mod 16 = 0 => clear - SPA; Z.div_mod_to_equations; lia
               | |- A + 416 <= lo \/ _ => clear - DS; lia
               | |- mem_inv _ m3 => assumption
               | |- aobj _ _ _ m3 A 416 => assumption
               | |- client_wrange _ _ _ _ A 416 => eapply client_wrange_sp_mono; [| exact CW]; clear - LOS; lia
               end
             | match goal with |- ?g => idtac "PZ-LEFT:" g end ]).
    clear SPZ.
    lazymatch goal with |- _ (MS _ _ _ _ _ ?mc _) => rename mc into m4 end.
    (* [comment removed for export] *)
    zstep. if_cases KE; zify_cond KE; [| exfalso; apply KE; reflexivity]. clear KE.
    zstep. zstep.
    zstep. zstep. zstep. zstep. zstep. zstep. zstep.
    lazymatch goal with |- _ (MS _ _ _ _ _ ?mc _) => rename mc into m5 end.
    lazymatch goal with FRo : rw_cells _ m5 (bv_unsigned sp + -48) _, STo : stk _ m5 lo (bv_unsigned sp + -48) |- _ => release_frame FRo STo (bv_unsigned sp) end.
    apply evtA_done. unfold x509_crl_free_postA.
    deexists 15. dexists m5, h1.
    split; [reflexivity|].
    split; [assumption|]. split; [assumption|].
    split; [exact (presW_presA asegs R HIA h LB LF _ _ _ _ _ PRES)|].
    split; [assumption|]. split; [exact E1cs|]. split; [exact E1top|]. split; [exact E1stk|]. split; [exact E1flag|]. split; [exact E1vol|]. split; [exact E1fr|].
    split; [exact HKI1|].
    unfold crl_zero. lazymatch goal with H : rw_cells _ m5 A _ |- _ => exact H end.
  Qed.
End Walk.

Lemma A_x509_crl_free_spec : ltac2:(CDefT.buildp (gd_tbl_A_x509_crl_free ()) "PR,$0.PHIA,(1.$2.R1.)P,(3.(4.R2.))P,(5.$6.(7.R3.)$8.)P,(9.=(:.R4.))P,(9.=(;.R5.))P,(<.$2.R6.R5.$=.)(>.$2.R7.R6.(?.R7.)$10.)")
(* [comment removed for export] *).
Proof. intros. eapply x509_crl_freeA; eauto. Qed.
