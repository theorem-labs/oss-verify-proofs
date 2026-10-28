(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib Require Import HeapCeil.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import Tac Arr Bytes ZBridge SysStep Exec CellsX TacX Frame.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.As Require Import ASegs AsShadow AsConst AsIface AsIfaceX AsCXXHeap AsCall AsCallX AsStack0 ECH_AImg ECH_Xpres ECH_ARep ECH_ALib ECH_Iface
  ECH_AStmt_C1 ECH_AStmt_C5 ECH_AStmt_C13 ECH_AStmt_C12 ECH_AKit ECH_AsKit ECH_AsKitK N6_memchr ECH_AC13_small.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.As Require Import N6_tac.   (* [comment removed for export] *)
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Spec Require Import Prelim StrFun.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import StoreDj.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_n8 segs m a bs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Section S.
  Context {HCEIL : HeapCeil}.
  Local Ltac kill K := exfalso; revert K; rewrite ?unsigned_lit, ?signed_lit by lia; lia.
  Local Ltac retpc := match goal with |- context [ret_pc (Z_to_bv 64 ?v)] => replace (ret_pc (Z_to_bv 64 v)) with (Z_to_bv 64 v) by (symmetry; apply ret_pc_even; [lia| reflexivity]) end.

  (* [comment removed for export] *)
  Lemma shvis_acrossV : forall W m m' lo hi,
    shvis m lo hi -> munch W m m' -> wmono asegs m m' -> 0 <= lo -> lo <= hi <= AAPP_HI ->
    Forall (fun iv : Z * Z => snd iv <= ASHADOW_BASE \/ AHI_LO <= fst iv) W -> shvis m' lo hi.
  Proof.
    intros W m m' lo hi SV MU WM L0 LH HW. eapply shvis_transport; [exact SV| exact MU| exact WM|].
    pose proof (hull_lo_le lo L0) as (A1 & A2 & A3). pose proof (hull_hi_ge hi ltac:(lia)) as (B1 & B2 & B3).
    assert (S1 : ASHADOW_BASE <= sh (hull_lo lo)) by (unfold sh; Z.div_mod_to_equations; lia).
    assert (HH2 : hull_hi hi <= AAPP_HI) by (unfold hull_hi, AAPP_HI in *; Z.div_mod_to_equations; lia).
    assert (S2 : sh (hull_hi hi) <= AHI_LO) by (unfold sh, AHI_LO, AAPP_HI in *; rewrite ASHADOW_BASE_val; Z.div_mod_to_equations; lia).
    clear - HW S1 S2. induction W as [|[l h] W IH]; [exact I|]. cbn. pose proof (Forall_inv HW) as K1. cbn in K1.
    split; [lia| exact (IH (Forall_inv_tail HW))].
  Qed.

  Lemma avsn_spec : vsn_stmt.
  Proof.
    unfold vsn_stmt. intros until rest. intros A0 A1 NPOS BS NONUL L1 NLO LAL LEN LLO LNA ACCN SHV IAM NSH SK0 LHI LLO2 ST CEIL LO MI AC RAE. subst a0 a1.
    unfold P_validate_string_name, VSN_STACK, FR_validate_string_name, zlength in *. pose proof LO as LOA. unfold AINTRIN_STACK in LO.
    pose proof (ACONST_shbase m AC) as [GSB SHB0]. unfold AGOT_SHBASE, ASHBASE_CELL, wz in GSB, SHB0. rewrite ASHADOW_BASE_val in SHB0.
    acb. pose proof (aword_range sp) as SPR. pose proof (aword_range ra) as RAR. assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    pose proof (bytes_at_bound _ _ _ _ BS) as BB. rewrite length_app in BB. cbn [length] in BB.
    pose proof ACCN as (_ & AHIN & _). unfold AAPP_HI in AHIN.
    pose proof (stack0_bounds _ _ _ SK0) as [SB1 SB2]. unfold AAPP_HI in SB2.
    assert (LSP : bv_unsigned sp <= lenp) by lia.
    pose proof (munch_refl [(lo, bv_unsigned sp); (lenp, lenp + 8)] m) as MU. pose proof (wmono_refl asegs m) as WM.
    assert (NSW : Forall (fun iv : Z * Z => snd iv <= ALOWSH_LO \/ AHI_LO <= fst iv) [(lo, bv_unsigned sp); (lenp, lenp + 8)]).
    { constructor; [cbn; unfold AHI_LO; lia|]. constructor; [cbn; unfold AHI_LO; lia| constructor]. }
    assert (AW : Forall aconst_ok [(lo, bv_unsigned sp); (lenp, lenp + 8)]).
    { constructor; [apply aconst_ok_high; cbn [fst snd]; unfold sh, AIMG_TOP; rewrite ?ASHADOW_BASE_val; lia|].
      constructor; [apply aconst_ok_high; cbn [fst snd]; unfold sh, AIMG_TOP; rewrite ?ASHADOW_BASE_val; lia| constructor]. }
    assert (SW : Forall stack0_ok [(lo, bv_unsigned sp); (lenp, lenp + 8)]).
    { constructor; [apply stack0_ok_app; unfold AHI_LO; lia|]. constructor; [apply stack0_ok_app; unfold AHI_LO; lia| constructor]. }
    assert (ACCL : accessible m lenp 8) by (eapply stack0_accessible; [exact SK0| lia| lia| lia]).
    change (id (accessible m name (Z.of_nat (length ns) + 1))) in ACCN. change (id (accessible m lenp 8)) in ACCL. change (id (ACONST m)) in AC.
    Local Ltac reacc ACC0 MU NSW n :=
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
        let A := fresh "ACC" in
        assert (A : accessible mx _ n) by (unfold id in ACC0; eapply accessible_across; [exact ACC0| exact MU| exact NSW]) end.
    unfold wz in LEN.
    carve_frame 48%nat ST.
    do 6 st1. step.
    (* [comment removed for export] *)
    step. step. ubal_by LAL. step. if_lit. step. step. step. zstep. zstep. reacc ACCL MU NSW 8. ck8_check ACC lenp. clear ACC.
    (* [comment removed for export] *)
    step. if_cases K0; zify_cond K0; [kill K0|]. clear K0.
    step. step. if_cases K0; zify_cond K0; [kill K0|]. clear K0.
    (* [comment removed for export] *)
    zstep. zstep. step. rewrite ?zb_lxor_ones by lia. ub_dead. zstep. zstep. zstep.
    try replace (name + (Z.of_nat (length ns) + -1)) with (name + Z.of_nat (length ns) + -1) by lia.
    reacc ACCN MU NSW (Z.of_nat (length ns) + 1). ck1_load ACC (name + Z.of_nat (length ns) + -1) v V1 V2 Ha. clear ACC.
    ck_K 14 0x4326dc K.
    2:{ ck1_branch_blt (name + Z.of_nat (length ns) + -1) v V1 V2 Ha K. }
    intros tv. red_tset.
    (* [comment removed for export] *)
    destruct (nth_error ns (Z.to_nat (Z.of_nat (length ns) - 1))) as [b|] eqn:NTH; [| apply nth_error_None in NTH; lia].
    assert (NTH' : nth_error (ns ++ Z_to_bv 8 0 :: rest) (Z.to_nat (Z.of_nat (length ns) - 1)) = Some b) by (rewrite nth_error_app1 by lia; exact NTH).
    assert (BNZ : bv_unsigned b <> 0).
    { intros E. apply NONUL. replace (Z_to_bv 8 0) with b; [eapply nth_error_In; exact NTH|]. apply bv_eq. rewrite E. reflexivity. }
    pose proof (abyte_range b) as BR.
    pose proof (u8ro_read asegs _ name (ns ++ Z_to_bv 8 0 :: rest) (Z.of_nat (length ns) - 1) b _ BS NTH' ltac:(lia) eq_refl) as RD.
    replace (name + (Z.of_nat (length ns) - 1)) with (name + Z.of_nat (length ns) + -1) in RD by lia.
    step. change (zxb b) with (Z_to_bv 64 (bv_unsigned b)).
    step. if_cases K0; zify_cond K0; [kill K0|]. clear K0. step.
    step. if_cases K0; zify_cond K0; [kill K0|]. clear K0.
    (* [comment removed for export] *)
    step. step. step. step.
    pose proof BS as BSn. apply bytes_at_app in BSn. destruct BSn as [BSn _].
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
      assert (ACN : ACONST mx) by (unfold id in AC; eapply ACONST_frame; [exact AC| exact MU| exact WM| exact AW]);
      assert (ACCm : accessible mx name (Z.of_nat (length ns))) by (unfold id in ACCN; eapply accessible_sub; [eapply accessible_across; [exact ACCN| exact MU| exact NSW]| lia| lia| lia]);
      assert (SHVm : shvis mx name (name + Z.of_nat (length ns)))
        by (eapply shvis_sub; [eapply shvis_acrossV; [exact SHV| exact MU| exact WM| lia| unfold AAPP_HI; lia|]| lia| lia| lia| lia| lia];
            constructor; [cbn; unfold AHI_LO; lia|]; constructor; [cbn; unfold AHI_LO; lia| constructor])
    end.
    eapply evt_cut.
    { eapply memchr_icpt_ok with (buf := ns) (lo := lo); rewrite ?unsigned_lit by lia;
        first [exact BSn| lia| exact ACCm| exact SHVm| exact ST| exact CEIL| exact ACN
              | eapply in_app_mem_sub; [exact IAM| lia| lia]
              | lazymatch goal with H : mem_inv _ ?mx |- mem_inv _ ?my => exact H end
              | match goal with |- ?G => idtac "LEFTM:" G end]. }
    unfold amemchr_post. intros ms' PO.
    destruct PO as (u0 & u1 & u2 & e1 & e2 & e3 & e4 & e5 & e6 & e7 & u3 & u4 & u5 & u6 & mc & -> & MU' & WM' & MI' & ST' & BS' & AC').
    retpc. rewrite ?unsigned_lit in MU', ST', BS' by lia. clear ST ACN ACCm SHVm. carry MU' WM'. extend_munch MU WM MU' WM'.
    lazymatch goal with H : mem_inv _ ?mx, H2 : mem_inv _ mc |- _ => idtac end.
    rename ST' into ST.
    rewrite !unsigned_lit by lia. change (0 mod 256) with 0.
    replace (memchr_res name 0 (Z.of_nat (length ns)) ns) with 0.
    2:{ unfold memchr_res. rewrite firstn_all2 by lia. rewrite find_byte_notin; [reflexivity|].
        intros b' Hb' E. apply NONUL. replace (Z_to_bv 8 0) with b'; [exact Hb'|]. apply bv_eq. rewrite E. reflexivity. }
    (* [comment removed for export] *)
    step. if_true.
    reacc ACCL MU NSW 8. ck8_check ACC lenp. clear ACC.
    st1. step. step.
    do 5 st1. step. step.
    release_frame FR ST (bv_unsigned sp). finish.
    all: try (unfold id in AC; eapply ACONST_frame; [exact AC| exact MU| exact WM| exact AW]).
    all: try (eapply stack0_transport; [exact SK0| exact MU| exact WM| exact SW]).
  Qed.
End S.
