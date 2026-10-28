(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib Require Import HeapCeil.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import Tac Arr Bytes ZBridge SysStep Exec CellsX TacX.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.As Require Import ASegs AsShadow AsConst AsIface AsIfaceX AsCXXHeap AsCall AsCallX AsStack0 ECH_AImg ECH_Xpres ECH_ARep ECH_ALib ECH_Iface
  ECH_AStmt_C1 ECH_AStmt_C5 ECH_AStmt_C13 ECH_AStmt_C12 ECH_AKit ECH_AsKit N6_iface
  ECH_AC1_malloc ECH_AC13_small ECH_AC13_ext ECH_AC12_hnpart ECH_AC12_vsn ECH_AC12_vpmfree ECH_AC12_addstr.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.As Require Import N6_tac.   (* [comment removed for export] *)
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Spec Require Import Prelim StrFun.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import StoreDj.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_n8 segs m a bs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Definition AAH_BR : Z := 0x432634.   (* [comment removed for export] *)
Definition ASHB12h : Z := 0x7fff8000.
Definition aah_frame (j : list byte) (L : Z) (s4 s3 s2 s1 s0 ra : word) : list cell := [CB 8 j; C8 (wz L); C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

Section S.
  Context {HCEIL : HeapCeil}.
  Local Ltac kill K := exfalso; revert K; rewrite ?unsigned_lit, ?signed_lit by lia; lia.
  Local Ltac retpc := match goal with |- context [ret_pc (Z_to_bv 64 ?v)] => replace (ret_pc (Z_to_bv 64 v)) with (Z_to_bv 64 v) by (symmetry; apply ret_pc_even; [lia| reflexivity]) end.
  Local Ltac reacc ACC0 MU NSW n :=
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
      let A := fresh "ACC" in
      assert (A : accessible mx _ n) by (unfold id in ACC0; eapply accessible_across; [exact ACC0| exact MU| exact NSW]) end.

  (* [comment removed for export] *)
  Lemma aah_segA :
    forall (ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (a name lo : Z) (ns slk : list byte),
      0 < a -> a mod 16 = 0 -> bv_unsigned sp mod 16 = 0 -> a + VPM_SIZE <= lo -> aapp a VPM_SIZE -> accessible m a VPM_SIZE ->
      0 < name -> name + zlength ns + 1 + zlength slk <= lo -> 1 <= zlength ns <= 255 ->
      rw_cells asegs m a (vpm_cells_h 0) ->
      bytes_at asegs m name (ns ++ Z_to_bv 8 0 :: slk) -> ~ In (Z_to_bv 8 0) ns -> zlength slk < 8 -> (- (name + zlength ns + 1)) mod 8 <= zlength slk ->
      accessible m name (zlength ns + 1) -> shvis m name (name + zlength ns + 1) -> in_app_mem name (name + zlength ns + 1) ->
      (name + zlength ns + 1 <= ALOWSH_LO \/ AHI_LO <= name) ->
      stack0 m lo (bv_unsigned sp) -> ACONST m ->
      stk asegs m lo (bv_unsigned sp) -> aceil <= lo -> lo <= bv_unsigned sp - 64 - AINTRIN_STACK - 48 -> mem_inv asegs m ->
      evt asegs (fun ms' => exists rax u0 u1 u2 b1 b2 b3 b4 b5 b6 b7 u3 u4 u5 u6 m1 j,
          ms' = MS (mkR rax (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp u0 u1 u2 sp (Z_to_bv 64 name)
                       (Z_to_bv 64 (if hostname_ok ns then 1 else 0)) b1 b2 b3 b4 b5 b6 b7
                       (Z_to_bv 64 a) (Z_to_bv 64 1) (Z_to_bv 64 ASHB12h) s5 s6 s7 s8 s9 s10 s11 u3 u4 u5 u6)
                   F (Z_to_bv 64 AAH_BR) fc None m1 (seg_rom asegs)
          /\ munch [(lo, bv_unsigned sp)] m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1 /\ ACONST m1
          /\ stk asegs m1 lo (bv_unsigned sp + -64)
          /\ rw_cells asegs m1 (bv_unsigned sp + -64) (aah_frame j (zlength ns) s4 s3 s2 s1 s0 ra)
          /\ rw_cells asegs m1 a (vpm_cells_h 0) /\ bytes_at asegs m1 name ns /\ stack0 m1 lo (bv_unsigned sp))
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 a) (Z_to_bv 64 name) (Z_to_bv 64 0) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 P_X509_VERIFY_PARAM_add1_host) fc None m (seg_rom asegs)).
  Proof.
    intros until slk. intros AP AAL SP16 AL AAP ACC0 NP NL LR BLK STR NONUL SLK PAD ACCN SHV IAM NSH SK0 AC0 ST CEIL LO MI.
    unfold P_X509_VERIFY_PARAM_add1_host, AAH_BR, ASHB12h. unfold zlength in *.
    pose proof (ACONST_shbase m AC0) as [GSB SHB0]. unfold AGOT_SHBASE, ASHBASE_CELL, wz in GSB, SHB0. rewrite ASHADOW_BASE_val in SHB0.
    unfold vpm_cells_h, wz in BLK. unfold VPM_SIZE in *. unfold AINTRIN_STACK in LO.
    pose proof (bytes_at_bound _ _ _ _ STR) as STRB. rewrite length_app in STRB. cbn [length] in STRB.
    acb. pose proof (aword_range sp) as SPR. assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    pose proof ACC0 as (_ & AHIa & _). pose proof ACCN as (_ & AHIn & _). unfold AAPP_HI in AHIa, AHIn.
    pose proof (stack0_bounds _ _ _ SK0) as [SB1 SB2]. unfold AAPP_HI in SB2.
    pose proof (munch_refl [(lo, bv_unsigned sp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
    assert (NSW : Forall (fun iv : Z * Z => snd iv <= ALOWSH_LO \/ AHI_LO <= fst iv) [(lo, bv_unsigned sp)]) by (constructor; [cbn; unfold AHI_LO; lia| constructor]).
    assert (SW : Forall stack0_ok [(lo, bv_unsigned sp)]) by (constructor; [apply stack0_ok_app; unfold AHI_LO; lia| constructor]).
    change (id (accessible m a 136)) in ACC0. change (id (accessible m name (Z.of_nat (length ns) + 1))) in ACCN. change (id (ACONST m)) in AC0.
    change (id (stack0 m lo (bv_unsigned sp))) in SK0. change (id (shvis m name (name + Z.of_nat (length ns) + 1))) in SHV.
    (* [comment removed for export] *)
    carve_frame 64%nat ST.
    do 8 step. step. step. step. step. st1. step.
    step. try (if_cases K0; zify_cond K0; [kill K0|]; clear K0).
    step. step. try if_lit. step. step. step.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
      assert (ACN : ACONST mx) by (unfold id in AC0; eapply ACONST_stack_frame13; [exact AC0| exact MU| exact WM| exact CEIL]);
      assert (ACCm : accessible mx name (Z.of_nat (length ns) + 1)) by (unfold id in ACCN; eapply accessible_across; [exact ACCN| exact MU| exact NSW]);
      assert (SHVm : shvis mx name (name + Z.of_nat (length ns) + 1))
        by (unfold id in SHV; eapply shvis_transport; [exact SHV| exact MU| exact WM|]; cbn;
            pose proof (hull_lo_le name ltac:(lia)) as (X1 & X2 & X3); pose proof (hull_hi_ge (name + Z.of_nat (length ns) + 1) ltac:(lia)) as (Y1 & Y2 & Y3);
            unfold sh, hull_lo, hull_hi, AHI_LO in *; rewrite ?ASHADOW_BASE_val in *; Z.div_mod_to_equations; lia)
    end.
    eapply evt_cut.
    { eapply strlen_icpt_ok with (str := ns) (slack := slk) (lo := lo); rewrite ?unsigned_lit by lia;
        first [exact STR| exact NONUL| exact PAD| exact ACCm| exact SHVm| exact ST| exact CEIL| exact ACN| exact IAM| lia | unfold AINTRIN_STACK; lia
              | lazymatch goal with H : mem_inv _ ?mx |- mem_inv _ ?my => exact H end
              | match goal with |- ?G => idtac "LEFTS:" G end]. }
    unfold astrlen_post. intros ms' PO.
    destruct PO as (u0 & u1 & u2 & e1 & e2 & e3 & e4 & e5 & e6 & e7 & u3 & u4 & u5 & u6 & mc & -> & MU' & WM' & MI' & ST' & STR' & AC').
    retpc. rewrite ?unsigned_lit in MU', ST', STR' by lia. unfold AINTRIN_STACK in MU'. clear ST ACN ACCm SHVm STR. carry MU' WM'. extend_munch MU WM MU' WM'. clear MI. rename MI' into MI. rename ST' into ST.
    assert (LNS : Z.of_nat (length (ns ++ Z_to_bv 8 0 :: slk)) = Z.of_nat (length ns) + 1 + Z.of_nat (length slk)) by (rewrite length_app; cbn [length]; lia).
    pose proof STR' as STRn. apply bytes_at_app in STRn. destruct STRn as [STRn _].
    (* [comment removed for export] *)
    st1. step. try (if_cases K0; zify_cond K0; [kill K0|]; clear K0). zstep. step. step.
    (* [comment removed for export] *)
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
      match goal with K : rw_cells _ mx (bv_unsigned sp + -64) _ |- _ =>
        lazymatch type of K with rw_cells _ _ ?ax (?c0 :: ?c1 :: ?rest) =>
          change (rw_cells asegs mx ax ([c0] ++ [c1] ++ rest)) in K end;
        apply (proj1 (rw_cells_app asegs _ _ _ _)) in K; destruct K as [FRj K];
        apply (proj1 (rw_cells_app asegs _ _ _ _)) in K; destruct K as [LEN FR]; cbn [cells_size csize Nat.add app] in LEN, FR;
        replace (bv_unsigned sp + -64 + Z.of_nat 8) with (bv_unsigned sp + -56) in LEN by lia;
        replace (bv_unsigned sp + -64 + Z.of_nat 8 + Z.of_nat 8) with (bv_unsigned sp + -48) in FR by lia end end.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
      assert (ACCm : accessible mx name (Z.of_nat (length ns) + 1)) by (unfold id in ACCN; eapply accessible_across; [exact ACCN| exact MU| exact NSW]);
      assert (SK1 : stack0 mx lo (bv_unsigned sp)) by (unfold id in SK0; eapply stack0_transport; [exact SK0| exact MU| exact WM| exact SW]);
      assert (ACN : ACONST mx) by (unfold id in AC0; eapply ACONST_stack_frame13; [exact AC0| exact MU| exact WM| exact CEIL]);
      assert (SHVm : shvis mx name (name + Z.of_nat (length ns) + 1))
        by (unfold id in SHV; eapply shvis_transport; [exact SHV| exact MU| exact WM|]; cbn;
            pose proof (hull_lo_le name ltac:(lia)) as (X1 & X2 & X3); pose proof (hull_hi_ge (name + Z.of_nat (length ns) + 1) ltac:(lia)) as (Y1 & Y2 & Y3);
            unfold sh, hull_lo, hull_hi, AHI_LO in *; rewrite ?ASHADOW_BASE_val in *; Z.div_mod_to_equations; lia)
    end.
    eapply evt_cut.
    { eapply avsn_spec with (lo := lo) (ns := ns) (rest := slk) (hi0 := bv_unsigned sp); unfold zlength; rewrite ?unsigned_lit by lia;
        first [reflexivity| exact STR'| exact NONUL| exact ACCm| exact SHVm| exact IAM| exact NSH| exact SK1| exact ST| exact CEIL| exact ACN| lia
              | unfold VSN_STACK, FR_validate_string_name, AINTRIN_STACK; lia
              | lazymatch goal with H : mem_inv _ ?mx |- mem_inv _ ?my => exact H end
              | lazymatch goal with |- rw_cells _ _ _ [C8 (wz _)] => unfold wz; exact LEN end
              | match goal with |- ?G => idtac "LEFTV:" G end]. }
    intros ms' PO.
    destruct PO as (w0 & w1 & w2 & f1 & f2 & f3 & f4 & f5 & f6 & f7 & w3 & w4 & w5 & w6 & md & -> & MU' & WM' & MI' & AC'' & ST' & LEN' & SK').
    retpc. rewrite ?unsigned_lit in MU', ST' by lia. clear ST ACCm SK1 SHVm LEN AC' ACN STR'. carry MU' WM'. extend_munch MU WM MU' WM'. clear MI. rename MI' into MI. rename ST' into ST.
    (* [comment removed for export] *)
    step. try if_lit.
    step. try (if_cases K0; zify_cond K0; [kill K0|]; clear K0). step. ubal_by AAL. step. if_lit.
    zstep. zstep. zstep. reacc ACC0 MU NSW 136. ck8_check ACC (a + 64). clear ACC.
    step. unfold wz in LEN'. step. step. try if_lit. step. step. step.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
      assert (ACCm : accessible mx name (Z.of_nat (length ns))) by (unfold id in ACCN; eapply accessible_sub; [eapply accessible_across; [exact ACCN| exact MU| exact NSW]| lia| lia| lia]) end.
    eapply evt_cut.
    { eapply ahnpart_spec with (lo := lo) (ns := ns) (rest := []); unfold zlength; rewrite ?app_nil_r; rewrite ?unsigned_lit by lia;
        first [reflexivity| exact STRn| exact ACCm| exact ST| exact CEIL| exact AC''| cbn [length Z.of_nat]; lia
              | unfold HNPART_STACK, FR_validate_hostname_part, CTYPE_STACK, FR_ossl_ctype_check; lia
              | lazymatch goal with H : mem_inv _ ?mx |- mem_inv _ ?my => exact H end
              | match goal with |- ?G => idtac "LEFTH:" G end]. }
    unfold ctype_post. intros ms' PO.
    destruct PO as (x0 & x1 & x2 & g1 & g2 & g3 & g4 & g5 & g6 & g7 & x3 & x4 & x5 & x6 & me & -> & MU' & WM' & MI' & AC3 & ST').
    retpc. rewrite ?unsigned_lit in MU', ST' by lia. clear ST ACCm. carry MU' WM'. extend_munch MU WM MU' WM'. clear MI. rename MI' into MI. rename ST' into ST.
    assert (SK3 : stack0 me lo (bv_unsigned sp)) by (unfold id in SK0; eapply stack0_transport; [exact SK0| exact MU| exact WM| exact SW]).
    unfold aah_frame.
    finish.
    all: try exact AC3. all: try exact SK3.
    all: try (lazymatch goal with |- rw_cells _ _ _ (CB 8 _ :: _) =>
                change (CB 8 ?jj :: C8 ?l :: ?rest) with ([CB 8 jj] ++ [C8 l] ++ rest);
                apply (proj2 (rw_cells_app asegs _ _ _ _)); split; [eassumption|];
                apply (proj2 (rw_cells_app asegs _ _ _ _)); split; cbn [cells_size csize Nat.add app];
                [replace (bv_unsigned sp + -64 + Z.of_nat 8) with (bv_unsigned sp + -56) by lia; unfold wz; eassumption
                | replace (bv_unsigned sp + -64 + Z.of_nat 8 + Z.of_nat 8) with (bv_unsigned sp + -48) by lia; eassumption] end).
  Qed.

  (* [comment removed for export] *)
  Lemma aah_segR :
    forall (rax sp gp tp t0 t1 t2 s1x a1 a2 a3 a4 a5 a6 a7 s2x s3x s4x s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 ra s0 s1 s2 s3 s4 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (L : Z) (j : list byte),
      rw_cells asegs m (bv_unsigned sp + -64) (aah_frame j L s4 s3 s2 s1 s0 ra) -> mem_inv asegs m ->
      evt asegs (fun ms' =>
          ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                   F (ret_pc ra) fc None m (seg_rom asegs))
        (MS (mkR rax (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp t0 t1 t2 sp s1x (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7
                 s2x s3x s4x s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 AAH_BR) fc None m (seg_rom asegs)).
  Proof.
    intros until j. intros FR MI. unfold AAH_BR. unfold aah_frame, wz in FR.
    pose proof (aword_range sp) as SPR.
    step. try if_lit. step. step. do 6 step. step. step. apply evt_done. reflexivity.
  Qed.

  (* [comment removed for export] *)
  Lemma aah_segT :
    forall (rax sp gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s3x s4x s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 ra s0 s1 s2 s3 s4 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (a name L : Z) (j : list byte),
      0 <= a -> a + VPM_SIZE < 2^64 -> 0 <= L < 2^64 ->
      rw_cells asegs m (bv_unsigned sp + -64) (aah_frame j L s4 s3 s2 s1 s0 ra) -> mem_inv asegs m ->
      evt asegs (fun ms' =>
          ms' = MS (mkR (Z_to_bv 64 R_X509_VERIFY_PARAM_add1_host_add_string_to_buffer_stack) (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp t0 t1 t2 sp (Z_to_bv 64 name)
                       (Z_to_bv 64 (a + O_VPM_HOSTS)) (Z_to_bv 64 name) (Z_to_bv 64 L) a3 a4 a5 a6 a7
                       (Z_to_bv 64 a) s3x s4x s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                   F (Z_to_bv 64 P_add_string_to_buffer_stack) fc None m (seg_rom asegs))
        (MS (mkR rax (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp t0 t1 t2 sp (Z_to_bv 64 name) (Z_to_bv 64 1) a1 a2 a3 a4 a5 a6 a7
                 (Z_to_bv 64 a) s3x s4x s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 AAH_BR) fc None m (seg_rom asegs)).
  Proof.
    intros until j. intros AP AL LR FR MI. unfold AAH_BR, P_add_string_to_buffer_stack, O_VPM_HOSTS, R_X509_VERIFY_PARAM_add1_host_add_string_to_buffer_stack.
    unfold aah_frame, wz in FR. unfold VPM_SIZE in AL.
    pose proof (aword_range sp) as SPR.
    step. try if_lit. step. step. step. step. apply evt_done. reflexivity.
  Qed.

  Lemma aah_segE :
    forall (sp gp tp t0 t1 t2 s1x a1 a2 a3 a4 a5 a6 a7 s2x s3x s4x s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 ra s0 s1 s2 s3 s4 rv : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (L : Z) (j : list byte),
      rw_cells asegs m (bv_unsigned sp + -64) (aah_frame j L s4 s3 s2 s1 s0 ra) -> mem_inv asegs m ->
      evt asegs (fun ms' =>
          ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 rv a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                   F (ret_pc ra) fc None m (seg_rom asegs))
        (MS (mkR (Z_to_bv 64 R_X509_VERIFY_PARAM_add1_host_add_string_to_buffer_stack) (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp t0 t1 t2 sp s1x rv a1 a2 a3 a4 a5 a6 a7
                 s2x s3x s4x s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (ret_pc (Z_to_bv 64 R_X509_VERIFY_PARAM_add1_host_add_string_to_buffer_stack)) fc None m (seg_rom asegs)).
  Proof.
    intros until j. intros FR MI. unfold R_X509_VERIFY_PARAM_add1_host_add_string_to_buffer_stack. retpc.
    unfold aah_frame, wz in FR.
    pose proof (aword_range sp) as SPR.
    step. step. do 8 step. step. apply evt_done. reflexivity.
  Qed.
End S.

(* [comment removed for export] *)
Section W.
  Context {HCEIL : HeapCeil}.
  Variable H : asr.
  Hypothesis HHx : asan_rt_hyps_x H.
  Let HH : asan_rt_hyps H := proj1 HHx.
  Hypothesis ASLACK : as_slack_law H.

  Lemma aadd1host_spec : add1host_stmt H.
  Proof.
    unfold add1host_stmt. intros until CH.
    intros VIS A0 A1 A2 VO VH VHO AL NIN STR NONUL LR PAD VSH ACCN HP KREL BUD BUDC AUX SPB ST CEIL LO SK0 ERR MI TP SP16 AC CHN CHS PF HAL MF IM GM RAE. subst a0 a1 a2.
    unfold ADD1HOST_STACK, FR_X509_VERIFY_PARAM_add1_host, HNPART_STACK, FR_validate_hostname_part, CTYPE_STACK, FR_ossl_ctype_check, VSN_STACK, FR_validate_string_name,
      ADDSTR_STACK, FR_add_string_to_buffer_stack, CSTRNDUP_STACK, SKNEW_STACK, SKPUSH_STACK, SKRESERVE_STACK, CARRAY_STACK, CREALLOC_ARRAY_STACK,
      CREALLOC_STACK, FR_CRYPTO_array, FR_CRYPTO_realloc, AREALLOC_STACK, FR_sk_new, FR_sk_insert, FR_sk_reserve,
      CZALLOC_STACK, CMALLOC_STACK, FR_CRYPTO_strndup, FR_CRYPTO_zalloc, FR_CRYPTO_malloc, AMALLOC_STACK, AINTRIN_STACK in LO.
    unfold ADD1HOST_BYTES, XBUF_SIZE, SK_SIZE in BUD. unfold ADD1HOST_COST, XBUF_SIZE, SK_SIZE in HAL.
    acb. subst tp. rewrite unsigned_lit in ERR by (unfold ATP; lia).
    pose proof (aword_range sp) as SPR. pose proof (aword_range ra) as RAR. pose proof (aword_range s0) as S0R.
    assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    assert (HB : forall b, In b LB -> blk_addr b + blk_size b <= aceil).
    { intros b Hb. pose proof (ah_blocks H HH _ _ _ _ HP Hb) as (_ & _ & _ & _ & Q5 & _). exact Q5. }
    pose proof (bytes_at_bound _ _ _ _ STR) as STRB. rewrite length_app in STRB. cbn [length] in STRB. unfold zlength in *.
    set (L := Z.of_nat (length ns)) in *.
    destruct VO as (VC & VIN & HOS). rewrite vpm_cells_h_eq, VH in VC.
    pose proof VSH as (TOP & SHA & _).
    pose proof (ah_blocks H HH _ _ _ _ HP VIN) as (K1 & K2 & K3 & K4 & K5 & K6 & K7). cbn [blk_addr blk_size fst snd] in K1, K2, K3, K4, K5, K6, K7.
    unfold AIMG_TOP in K4. unfold VPM_SIZE in K3, K5, K7, TOP, SHA. unfold AAPP_HI in TOP. clear K6.
    pose proof (ah_blocks H HH _ _ _ _ HP NIN) as (N1 & N2 & N3 & N4 & N5 & N6 & N7). cbn [blk_addr blk_size fst snd] in N1, N2, N3, N4, N5, N6, N7.
    unfold AIMG_TOP in N4. clear N6.
    pose proof (aapp_bounds name (L + 1) N7 ltac:(lia)) as (NB1' & NB2' & NB3' & NB4' & NB5'). unfold AAPP_HI in NB3'.
    pose proof (proj1 (proj2 (proj2 (ah_costs H HH)))) as CF0. pose proof (proj1 (ah_costs H HH)) as CM0. pose proof (proj1 (proj2 (ah_costs H HH))) as CMM.
    pose proof (CF0 0 ltac:(lia)) as CFZ. pose proof (CM0 16 ltac:(lia)) as CM16. pose proof (CM0 (L + 1) ltac:(lia)) as CML. pose proof (CM0 56 ltac:(lia)) as CM56. pose proof (CM0 32 ltac:(lia)) as CM32.
    pose proof (CMM (L + 1) 256 ltac:(lia)) as CML256.
    assert (ACCa : accessible m a 136) by (eapply addressable_accessible; [exact SHA| lia| lia| unfold AAPP_HI; lia]).
    pose proof (ah_blk_shvis H HH _ _ _ _ _ _ HP NIN) as SHV. replace (name + (L + 1)) with (name + L + 1) in SHV by lia.
    assert (IAM : in_app_mem name (name + L + 1)) by (eapply aapp_in_app_mem; [exact N7| lia| lia]).
    pose proof (aapp_not_shadowland _ _ N7) as NSH. replace (name + (L + 1)) with (name + L + 1) in NSH by lia.
    (* [comment removed for export] *)
    set (k := (- (name + L + 1)) mod 8) in *.
    assert (KR : 0 <= k < 8 /\ name + L + 1 + k <= aceil) by (unfold k; clear - N5 ACEILB; Z.div_mod_to_equations; lia).
    assert (STRk : bytes_at asegs m name (ns ++ Z_to_bv 8 0 :: firstn (Z.to_nat k) slack)).
    { replace (ns ++ Z_to_bv 8 0 :: firstn (Z.to_nat k) slack) with ((ns ++ [Z_to_bv 8 0]) ++ firstn (Z.to_nat k) slack) by (rewrite <- app_assoc; reflexivity).
      replace (ns ++ Z_to_bv 8 0 :: slack) with ((ns ++ [Z_to_bv 8 0]) ++ slack) in STR by (rewrite <- app_assoc; reflexivity).
      apply bytes_at_app in STR. destruct STR as [S1 S2]. apply bytes_at_app. split; [exact S1|].
      rewrite <- (firstn_skipn (Z.to_nat k) slack) in S2. apply bytes_at_app in S2. exact (proj1 S2). }
    assert (SLK : Z.of_nat (length (firstn (Z.to_nat k) slack)) = k) by (rewrite length_firstn; lia).
    clear STR. set (slk := firstn (Z.to_nat k) slack) in *.
    (* [comment removed for export] *)
    eapply (ahh_evt_then H HH); [exact KREL| exact VIS| eapply aah_segA with (lo := lo) (ns := ns) (slk := slk); unfold zlength, VPM_SIZE; fold L;
      first [exact VC| exact STRk| exact NONUL| exact K7| exact ACCa| exact ACCN| exact SHV| exact IAM| exact NSH| exact SK0| exact AC| exact ST| exact CEIL| exact MI| exact K2| exact SP16
            | lia | unfold AINTRIN_STACK; lia | match goal with |- ?G => idtac "LEFTA:" G end]|].
    intros msF1 mo1 KREL1 MP1 (rax & u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & m1 & j & VIS1 & MU1 & WM1 & MI1 & AC1 & ST1 & FR1 & VC1 & BS1 & SK1).
    fold L in FR1.
    assert (CW : Forall (aclient_write_ok H LB) [(lo, bv_unsigned sp)]) by (constructor; [left; cbn; lia| constructor]).
    assert (HP1 : as_RHEAP H s LB m1) by (eapply (ah_RHEAP_frame H HH); [exact HP| exact MU1| exact WM1| exact CW]).
    assert (AUX1 : as_rauxv_ok H m1 B) by (eapply (ah_rauxv_frame H HH); [exact AUX| exact MU1| exact WM1| exact CW]).
    assert (ERR1 : rw_cells asegs m1 (ATP + -164) [C4 errv]) by (eapply errno_across; [exact ERR| exact MU1| exact WM1| unfold ATP; cbn; lia]).
    assert (MF1 : MEMFLAG m1 1) by (eapply MEMFLAG_across; [exact MU1| exact WM1| unfold A_mem_inited; cbn; lia| exact MF]).
    assert (IM1 : IMPL_mem m1) by (eapply IMPL_across; [exact MU1| exact WM1| unfold A_malloc_impl; cbn; lia| exact IM]).
    assert (GM1 : GOT_mem m1) by (eapply GOT_across; [exact MU1| exact WM1| unfold A_got_CRYPTO_malloc; cbn; lia| exact GM]).
    assert (XP1 : xpres H LB (bv_unsigned sp) (memflag_foot ++ [(a, a + VPM_SIZE)]) m m1)
      by (eapply (xpres_of_munch H s LB _ _ _ m m m1); [exact HH| exact HP| exact MU1| exact WM1|]; constructor; [left; cbn; lia| constructor]).
    assert (CH1 : as_chain H m1 (bv_unsigned s0) CH)
      by (eapply (achain_below H HH m m1); [exact CHN| exact CHS| exact MU1|]; constructor; [left; cbn; lia| constructor]).
    clear CW.
    assert (SHA1 : addressable m1 a 136).
    { eapply addressable_transport; [exact SHA| exact MU1| exact WM1|]. cbn. pose proof (sh_aapp_range a 136 K7 ltac:(lia)) as (X1 & X2 & X3). unfold AHI_LO in *. lia. }
    assert (ACCN1 : accessible m1 name L).
    { eapply accessible_sub; [eapply accessible_across; [exact ACCN| exact MU1|]| lia| lia| lia]. constructor; [cbn; unfold AHI_LO; lia| constructor]. }
    unfold aah_frame in FR1. pose proof (stk_release asegs m1 lo _ _ ST1 FR1 ltac:(lia)) as ST1b. cbn [cells_size csize Nat.add] in ST1b.
    replace (bv_unsigned sp + -64 + Z.of_nat 64) with (bv_unsigned sp) in ST1b by lia.
    destruct (hostname_ok ns) eqn:HOK.
    - (* [comment removed for export] *)
      eapply (ahh_evt_then H HH); [exact KREL1| exact VIS1| eapply aah_segT with (a := a) (L := L); [lia| unfold VPM_SIZE; lia| lia| exact FR1| exact MI1]|].
      intros msF2 mo2 KREL2 MP2 VIS2.
      assert (CHa : as_chain H m1 (bv_unsigned sp) ((bv_unsigned sp, bv_unsigned ra) :: CH)).
      { eapply (ah_chain_cons H HH); [exact CH1| lia| lia| exact SP16| lia| lia|].
        pose proof FR1 as FR2.
        lazymatch type of FR2 with rw_cells _ _ ?ax (?c0 :: ?c1 :: ?c2 :: ?c3 :: ?c4 :: ?c5 :: ?rest) =>
          change (rw_cells asegs m1 ax ([c0; c1; c2; c3; c4; c5] ++ rest)) in FR2 end.
        apply (proj1 (rw_cells_app asegs _ _ _ _)) in FR2. destruct FR2 as [_ FR2]. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ Nat.mul Pos.mul Pos.add] in FR2.
        replace (bv_unsigned sp - 16) with (bv_unsigned sp + -64 + 48) by lia.
        first [exact FR2 | revert FR2; rewrite !Z_to_bv_bv_unsigned; intros FR2; exact FR2]. }
      assert (CHSa : forall fp' ra', In (fp', ra') ((bv_unsigned sp, bv_unsigned ra) :: CH) -> bv_unsigned sp + -64 + 16 <= fp')
        by (intros fp' ra' [E|Hin]; [injection E as <- <-; lia| specialize (CHS _ _ Hin); lia]).
      assert (SP16a : (bv_unsigned sp + -64) mod 16 = 0) by (replace (bv_unsigned sp + -64) with (bv_unsigned sp - 64) by lia; rewrite Zminus_mod, SP16; reflexivity).
      pose proof (aaddstr_spec H HHx ASLACK) as ASP. unfold aaddstr_stmt in ASP.
      eapply (ah_seq H HH).
      { eapply ASP with (lo := lo) (B := B) (LB := LB) (s := s) (v := 1) (a := a) (pa := vp_id V) (bN := (pn, name, L + 1)) (ns := ns)
                        (CH := (bv_unsigned sp, bv_unsigned ra) :: CH);
          [exact VIS2| reflexivity| reflexivity| unfold zlength; fold L; reflexivity| ..]; unfold zlength; fold L; cbn [blk_addr blk_size fst snd];
          rewrite ?unsigned_lit by (unfold R_X509_VERIFY_PARAM_add1_host_add_string_to_buffer_stack; lia).
        all: first [exact VC1| exact VIN| exact SHA1| exact BS1| exact NIN| exact ACCN1| exact NONUL| exact HP1| exact KREL2| exact AUX1| exact ST1| exact CEIL
                   | exact ERR1| exact MI1| reflexivity| exact SP16a| exact AC1| exact CHa| exact CHSa| exact MF1| exact IM1| exact GM1
                   | unfold R_X509_VERIFY_PARAM_add1_host_add_string_to_buffer_stack; eapply pf_ok_call; [exact PF| unfold PF_add1host; intros y Hy; exact Hy]
                   | unfold AADDSTR_BYTES, XBUF_SIZE, SK_SIZE, zlength; fold L; lia
                   | unfold AADDSTR_COST, XBUF_SIZE, SK_SIZE, zlength; fold L; lia
                   | lia
                   | unfold ADDSTR_STACK, FR_add_string_to_buffer_stack, CSTRNDUP_STACK, SKNEW_STACK, SKPUSH_STACK, SKRESERVE_STACK, CARRAY_STACK, CREALLOC_ARRAY_STACK,
                       CREALLOC_STACK, FR_CRYPTO_array, FR_CRYPTO_realloc, AREALLOC_STACK, FR_sk_new, FR_sk_insert, FR_sk_reserve,
                       CZALLOC_STACK, CMALLOC_STACK, FR_CRYPTO_strndup, FR_CRYPTO_zalloc, FR_CRYPTO_malloc, AMALLOC_STACK; lia
                   | match goal with |- ?G => idtac "LEFTD:" G end]. }
      clear ASP. intros [msF3 mo3] PO. unfold aaddstr_post in PO. cbn [cfg_ms cfg_model] in PO.
      destruct PO as (v0 & v1 & v2 & c1 & c2 & c3 & c4 & c5 & c6 & c7 & v3 & v4 & v5 & v6 & m3 & errv3 & s3' & st & K & X & NB &
                      VIS3 & KREL3 & MP3 & MI3 & AC3 & ST3 & ERR3 & AUX3 & XP3 & HEAP3 & VC3 & HOS3 & XL & HSH3 & PNB & LNB & BNB & MF3 & IM3 & GM3 & SHA3 & AL3).
      rewrite ?unsigned_lit in ST3, XP3 by lia.
      pose proof aceil_range as ACR.
      assert (FR3 : rw_cells asegs m3 (bv_unsigned sp + -64) [CB 8 j; C8 (wz L); C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]).
      { eapply (xpres_rw_cells' H); [exact XP3| exact FR1| left; cbn; lia|].
        unfold memflag_foot, A_mem_inited, VPM_SIZE. cbn [cells_size csize Nat.add app].
        constructor; [right; cbn [fst snd]; lia|]. constructor; [right; cbn [fst snd]; lia| constructor]. }
      pose proof (stk_release asegs m3 lo _ _ ST3 FR3 ltac:(lia)) as ST3b. cbn [cells_size csize Nat.add] in ST3b.
      replace (bv_unsigned sp + -64 + Z.of_nat 64) with (bv_unsigned sp) in ST3b by lia.
      eapply (ahh_evt H HH); [exact KREL3| exact VIS3| eapply aah_segE; [exact FR3| exact MI3]|].
      intros msF4 mo4 KREL4 MP4 VIS4.
      unfold add1host_post. cbn [cfg_ms cfg_model]. rewrite HOK.
      exists v0, v1, v2, c1, c2, c3, c4, c5, c6, c7, v3, v4, v5, v6, m3, errv3, s3', (mkVPM st (Some (K, [X])) (vp_id V)), NB.
      split; [exact VIS4|]. split; [exact KREL4|].
      split; [eapply (ah_mpres_trans H HH); [exact MP1| eapply (ah_mpres_trans H HH); [exact MP2| eapply (ah_mpres_trans H HH); [exact MP3| exact MP4]]]|].
      split; [exact MI3|]. split; [exact AC3|]. split; [exact ST3b|]. split; [exact ERR3|]. split; [exact AUX3|].
      split; [eapply (xpres_trans H); [exact XP1| eapply (xpres_weaken H); [exact XP3| lia| auto| auto]]|].
      split; [exact HEAP3|].
      split. { unfold VPMobj. cbn [vp_hosts vp_hosts_o vp_id]. rewrite vpm_cells_h_eq. cbn [vp_hosts]. split; [exact VC3|]. split; [apply in_or_app; right; exact VIN| exact HOS3]. }
      split; [reflexivity|].
      split. { unfold blocks_VPM. cbn [vp_hosts vp_hosts_o vp_id]. apply perm_skip. exact PNB. }
      split; [intros; discriminate|].
      split; [intros _; exists K, X; split; [reflexivity| exact XL]|].
      split; [lia|]. split; [unfold ADD1HOST_BYTES; rewrite BNB; unfold AADDSTR_BYTES, XBUF_SIZE, SK_SIZE, zlength; fold L; lia|].
      split. { unfold VPM_shad. cbn [vp_hosts vp_hosts_o]. unfold VPM_SIZE, AAPP_HI. split; [lia|]. split; [exact SHA3| exact HSH3]. }
      split. { eapply (stack0_xpres H); [exact XP3| exact SK1|]. unfold memflag_foot, A_mem_inited, VPM_SIZE.
               constructor; [right; cbn; unfold sh; rewrite ASHADOW_BASE_val; lia|]. constructor; [eapply stack0_ok_aapp; [exact K7| cbn; lia| cbn; lia]| constructor]. }
      split; [exact MF3|]. split; [exact IM3|]. split; [exact GM3|].
      unfold ADD1HOST_COST, XBUF_SIZE, SK_SIZE. unfold AADDSTR_COST, XBUF_SIZE, SK_SIZE, zlength in AL3. fold L in AL3. clear - AL3 CML256 HAL. lia.
    - (* [comment removed for export] *)
      eapply (ahh_evt H HH); [exact KREL1| exact VIS1| eapply aah_segR; [exact FR1| exact MI1]|].
      intros msF2 mo2 KREL2 MP2 VIS2.
      unfold add1host_post. cbn [cfg_ms cfg_model]. rewrite HOK.
      exists u0, u1, u2, b1, b2, b3, b4, b5, b6, b7, u3, u4, u5, u6, m1, errv, s, V, (@nil block).
      split; [exact VIS2|]. split; [exact KREL2|]. split; [eapply (ah_mpres_trans H HH); [exact MP1| exact MP2]|]. split; [exact MI1|]. split; [exact AC1|]. split; [exact ST1b|].
      split; [rewrite unsigned_lit by (unfold ATP; lia); exact ERR1|]. split; [exact AUX1|].
      split; [exact XP1|]. cbn [app].
      split; [exact HP1|].
      split. { unfold VPMobj. rewrite vpm_cells_h_eq, VH. split; [exact VC1|]. split; [exact VIN|]. rewrite VHO. reflexivity. }
      split; [reflexivity|].
      split. { unfold blocks_VPM. rewrite VH, VHO. cbn. apply Permutation_refl. }
      split; [intros _; split; reflexivity|]. split; [intros; discriminate|].
      split; [cbn; lia|]. split; [unfold ADD1HOST_BYTES, SK_SIZE; cbn; lia|].
      split. { unfold VPM_shad. rewrite VH, VHO. unfold VPM_SIZE, AAPP_HI. split; [lia|]. split; [exact SHA1| exact I]. }
      split; [exact SK1|].
      split; [exact MF1|]. split; [exact IM1|]. split; [exact GM1|].
      unfold ADD1HOST_COST, XBUF_SIZE, SK_SIZE. clear - HAL CM16 CML CM56 CM32 CFZ CML256. lia.
  Qed.
End W.
