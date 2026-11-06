(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Walk Asn1Aux Asn1AuxA AStep CellsX MpiCoreAux HeapIface ZBridge.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Spec Require Import Rep RepFacts MpiVal MpiFacts MpiJourney.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.P Require Import PImg P_string P_platform_zeroize P_mpi_free P_mpi_addsub P_mpi_cmp P_mpi_add_abs_W.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import DietDestruct.   (* [comment removed for export] *)
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Ltac2 gd_tbl_P_mpi_add_abs_C () : Init.string Init.list := ["Corelib.Init.Datatypes.nat"; "stdpp.bitvector.definitions.bv"; "OSSVerify.KrLib.Lib.HeapIface.HST"; "OSSVerify.KrLib.P.PImg.psegs"; "Corelib.Init.Datatypes.list"; "OSSVerify.KrLib.Lib.HeapIface.blk"; "Corelib.Init.Datatypes.option"; "LinuxProcessSemantics.LinuxProcessSem.State.Model"; "Corelib.Numbers.BinNums.Z"; "Stdlib.ZArith.BinInt.Z.le"; "Stdlib.ZArith.BinInt.Z.sub"; "Stdlib.ZArith.BinInt.Z.of_nat"; "OSSVerify.KrLib.Spec.MpiJourney.XJ"; "OSSVerify.KrLib.Spec.MpiVal.mkMPD"; "OSSVerify.KrLib.P.P_mpi_add_abs_W.AA_FRAME"; "Corelib.Init.Datatypes.nil"; "OSSVerify.KrLib.Spec.Rep.LHeap"; "Corelib.Init.Logic.and"; "Corelib.Init.Logic.eq"; "Stdlib.ZArith.BinInt.Z.add"; "OSSVerify.KrLib.Spec.Rep.limbs_val"; "Stdlib.ZArith.BinInt.Z.pow"; "Stdlib.ZArith.BinInt.Z.mul"; "OSSVerify.KrLib.P.P_mpi_add_abs_W.AA_VAL"; "stdpp.bitvector.definitions.Z_to_bv"; "OSSVerify.KrLib.Lib.AEvt.aevtM"; "OSSVerify.KrLib.P.P_mpi_add_abs_W.AA_POST"; "OSSVerify.KrLib.Lib.MState.MS"; "OSSVerify.KrLib.Lib.Frame.mkR"; "stdpp.bitvector.definitions.bv_unsigned"; "Corelib.Init.Datatypes.None"; "OSSVerify.KrLib.Lib.PropExec.seg_rom"; "Stdlib.ZArith.BinInt.Z.lt"].


(* [comment removed for export] *)
Lemma w32_incr : forall w : word, w32 (Z_to_bv 64 (bv_swrap 32 (bv_unsigned (sx32 w) + 1))) = (w32 w + 1) mod 2^32.
Proof.
  intros w. rewrite Z_to_bv64_swrap32_mod32. rewrite bv_unsigned_sx32. fold (w32 w). apply sxz_add_mod32. apply w32_range.
Qed.

Lemma incr_mod64 : forall w : word, (bv_swrap 32 (bv_unsigned (sx32 w) + 1)) mod 2^64 = sxz ((w32 w + 1) mod 2^32).
Proof.
  intros w. rewrite swrap32_mod64. rewrite bv_unsigned_sx32. fold (w32 w). rewrite sxz_add_mod32 by apply w32_range. reflexivity.
Qed.

Lemma limb32_w32_nth : forall xs k w, nth_error xs k = Some w -> limb32 xs k = w32 w.
Proof. intros xs k w H. unfold limb32, w32. erewrite nth_error_nth by exact H. reflexivity. Qed.

(* [comment removed for export] *)
Section C.
  Variable L : heap_layout.
  Variable HI : heap_iface psegs L.
  Hypothesis HFREE : hl_free L = P_FREE.
  Hypothesis HCALLOC : hl_calloc L = P_CALLOC.
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
            (m : mem) (mo : Model) (h : HST psegs L HI) (LB : list blk) (dA dB : mpd) (lo : Z) (MSF : Z) (j0 : list byte)
            (X sX nX pX : Z) (xs0 : list word) (padX : word) (ownX : limb_own).
  Local Notation dX := (mkMPD X sX nX pX xs0 padX ownX).
  Hypothesis MSFE : MSF = P_MEMSET_FUNC.
  Hypothesis CA : const_at L MSF 8.
  Hypothesis TP : tp = Z_to_bv 64 (hl_tp L).
  Hypothesis SPA : bv_unsigned sp mod 16 = 0.
  Hypothesis SLO2 : lo <= bv_unsigned sp - 176 - hl_stack L.
  Local Notation FRAME := (AA_FRAME ra s0 s1 s2 s3 s4 s5 j0).
  Local Notation POST := (AA_POST L HI ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m mo h LB dA dB lo X sX nX pX xs0 padX ownX).
  Local Notation VAL := (AA_VAL dA dB).
  Hypothesis JCX : JC psegs L HI h LB m mo dX sp lo 64 FRAME.

  Local Ltac jc_open := pose proof JCX as [HLS SW DIMG HND ROIMG DHI HH MX NST XW XLS ACL FS0 SLO HTOP FSZ].
  Local Notation XJ0 := (XJ psegs L HI h LB m mo dX sp lo 64 FRAME []).
  Local Ltac xj_open J := pose proof J as [MI1 ST1 FR1 HH1 HT1 MF1 SOK1 MX1 AD1 PD1 NS1 OUT1 FRS1 HPX1 XP1]; cbn [app] in HH1.

  (* [comment removed for export] *)
  #[using="HFREE HCALLOC MSF MSFE CA TP SPA SLO2 JCX"] Lemma add_LOOP : ltac2:(CDefT.buildp (gd_tbl_P_mpi_add_abs_C ()) "Pk,$0.Pt0,(1.&40.)Pt1,(1.&40.)Pt2,(1.&40.)Praj,(1.&40.)Pa0,(1.&40.)Pa1,(1.&40.)Pa2,(1.&40.)Pa3,(1.&40.)Pa4,(1.&40.)Pa5,(1.&40.)Pa6,(1.&40.)Pa7,(1.&40.)Pt3,(1.&40.)Pt4,(1.&40.)Pt5,(1.&40.)Pt6,(1.&40.)Pr1,(1.&40.)Pr2,(1.&40.)Pr6,(1.&40.)Phc,(2.$3.VL,VHI,)PLBc,(4.$5.)Pmc,P,(1.&40.)(6.(1.&8.))Pmoc,$7.Pxs,(4.(1.&40.))PpXc,$8.PN,$8.PJ,$8.P,(9.(:.R2.R1.)(;.R1<.))P,(<.$3.VL,VHI,Vh,VLB,Vm,Vmo,(=.VX,VsX,VnX,VpX,Vxs0,VpadX,VownX,)Vsp,Vlo,+40.(>.Vra,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vj0,)(?.$5.)R9.R8.R7.R6.(=.VX,+1.R3.R4.R5.VpadX,$10.))P,(11.(9.+1.R3.)(9.R3.R4.))P,(12.$8.(13.(14.R7.)(15.+2.(16.+20.R4.)))(17.VdA,VdB,))P,(12.(1.&40.)R?.(18.&40.(13.R5.+1.)))P,(12.(1.&40.)R?.(18.&40.(:.(13.R8.(16.+4.R6.))+4.)))P,(12.(1.&40.)R?.(18.&40.(16.+4.R7.)))(19.$3.R<.(1:.VL,VHI,Vra,Vsp,Vgp,Vtp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VF,Vfc,Vm,Vmo,Vh,VLB,VdA,VdB,Vlo,VX,VsX,VnX,VpX,Vxs0,VpadX,VownX,)(1;.(1<.R1?.(18.&40.(:.(1=.&40.Vsp,)+40.))Vgp,Vtp,R22.R21.R20.(18.&40.VX,)R12.R1>.R1=.R1<.R1;.R1:.R19.R18.R17.(18.&40.R9.)R11.R10.(18.&40.+2710.)Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,R16.R15.R14.R13.)VF,(18.&40.+1?<28.)Vfc,(1>.(1.&40.))R=.(1?.$3.)))")
(* [comment removed for export] *).
  Proof.
    induction k as [|k IH]; intros until J; intros Hk J0 HJ HV -> -> ->.
    all: jc_open; pose proof (bv_unsigned_in_range 64 sp) as SPB; change (bv_modulus 64) with (2^64) in SPB; pose proof alloc_ceiling_pos as ACP.
    all: pose proof alloc_ceiling_bounds as ACV.
    all: pose proof (xj_facts _ _ _ _ _ _ _ _ _ _ _ _ JCX _ _ _ _ _ _ J0) as (HBR1 & HAP1 & ND1 & MK1 & XS & X0 & X16 & XAL & LEN1 & NR1 & OWN0 & OWN1); cbn [app] in HBR1, HAP1, ND1.
    all: cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in *.
    all: ddestruct (OWN1 ltac:(discriminate)) as (_ & N1 & XIN & XPAL & ARR1 & P0 & PC & PI).
    all: pose proof J0 as JX; xj_open JX; cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in *.
    all: pose proof (munch_refl [(pXc, pXc + 4 * N)] mc) as MU; pose proof (wmono_refl psegs mc) as WM.
    all: zstep; zstep; if_cases K0; zify_cond K0.
    all: swap 3 4.
    - (* [comment removed for export] *) exfalso. clear - K0 Hk HJ. lia.
    - (* [comment removed for export] *)
      zstep. if_cases K1; zify_cond K1.
      { (* [comment removed for export] *) eapply add_retm16; [exact JCX| exact J0]. }
      zstep. if_cases K2; zify_cond K2; [exfalso; clear - K2 K0; lia|].
      assert (EJ : J = N) by (clear - K0 HJ; lia). subst J.
      eapply add_G2; [exact HFREE| exact HCALLOC| exact MSFE| exact CA| exact TP| exact SPA| exact SLO2| exact JCX| exact J0| clear - K1; lia| exact HV].
    - (* [comment removed for export] *)
      zstep. if_cases K1; zify_cond K1.
      { (* [comment removed for export] *) eapply add_retm16; [exact JCX| exact J0]. }
      zstep. if_cases K2; zify_cond K2; [exfalso; clear - K2 K0; lia|].
      assert (EJ : J = N) by (clear - K0 HJ; lia). subst J.
      eapply add_G2; [exact HFREE| exact HCALLOC| exact MSFE| exact CA| exact TP| exact SPA| exact SLO2| exact JCX| exact J0| clear - K1; lia| exact HV].
    - (* [comment removed for export] *)
      zstep. zstep.
      destruct (nth_error xs (Z.to_nat J)) as [w|] eqn:NTH; [| apply nth_error_None in NTH; exfalso; clear - NTH LEN1 K0 HJ; lia].
      pose proof (u32arr_read psegs mc pXc xs J w _ ARR1 NTH ltac:(clear - HJ; lia) eq_refl) as RD.
      zstep. clear RD. zstep. zstep.
      pose proof (u32arr_store_ok psegs mc pXc xs J _ ARR1 ltac:(clear - HJ K0 LEN1; lia) eq_refl) as SOK.
      zstep.
      lazymatch goal with |- context [write_to_mem _ _ (le4 ?v)] =>
        pose proof (u32arr_write psegs mc pXc xs J v ARR1 ltac:(clear - HJ K0 LEN1; lia)) as ARR2 end.
      clear ARR1 MX1 HH1 SOK1 HPX1 FR1.
      store_done.
      lazymatch goal with |- aevtM _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m2 end.
      match goal with ST2 : stk psegs m2 _ _, MI2 : mem_inv psegs m2 |- _ =>
        pose proof (xj_limbs _ _ _ _ _ _ _ _ _ _ _ _ JCX _ _ _ _ _ _ _ _ _ _ _ _ _ J0 MU WM MI2 ST2
                      ltac:(intros a NO; left; destruct (outside_dec [(pXc, pXc + 4 * N)] a) as [O|O]; [exfalso; exact (NO O)| cbn in O; clear - O; lia])
                      ltac:(cbn; clear - PC ACL SLO HLS; lia) ltac:(cbn; pose proof (XP1 eq_refl); clear - H; lia) ARR2
                      ltac:(rewrite upd_length; reflexivity)) as J2 end.
      pose proof (limb32_w32_nth xs (Z.to_nat J) w NTH) as LW. pose proof (w32_range w) as WR.
      assert (LVU : limbs_val (upd xs (Z.to_nat J) (Z_to_bv 64 (bv_swrap 32 (bv_unsigned (sx32 w) + 1))))
                    = limbs_val xs + 2 ^ (32 * J) * ((w32 w + 1) mod 2 ^ 32 - w32 w)).
      { rewrite limbs_val_upd by (clear - HJ K0 LEN1; lia). fold (w32 (Z_to_bv 64 (bv_swrap 32 (bv_unsigned (sx32 w) + 1)))).
        rewrite w32_incr, LW. replace (Z.of_nat (Z.to_nat J)) with J by (clear - HJ; lia). reflexivity. }
      zstep. zstep. if_cases KB; zify_cond KB; rewrite incr_mod64 in KB.
      + (* [comment removed for export] *)
        assert (NZ : (w32 w + 1) mod 2 ^ 32 <> 0) by (intros E; apply KB; rewrite E; reflexivity).
        eapply add_ret; [exact JCX| exact J2|]. left. split; [reflexivity|]. split; [| reflexivity].
        unfold mpd_val. cbn [md_sg md_limbs]. rewrite LVU. rewrite Z.mod_small by (clear - WR NZ; lia). clear - HV. lia.
      + (* [comment removed for export] *)
        apply (proj1 (sxz_zero_iff _ ltac:(clear; apply Z.mod_pos_bound; lia))) in KB.
        eapply (IH _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ N (J + 1)); [clear - Hk K0; lia| exact J2| clear - HJ K0; lia| | f_equal; clear; lia| f_equal; clear; lia| f_equal; clear; lia].
        rewrite LVU, KB. replace (32 * (J + 1)) with (32 * J + 32) by (clear; lia). rewrite Z.pow_add_r by (clear - HJ; lia).
        assert (w32 w = 2 ^ 32 - 1) by (clear - KB WR; lia). clear - HV H. nia.
  Qed.
  (* [comment removed for export] *)
  #[using="HFREE HCALLOC MSF MSFE CA TP SPA SLO2 JCX"] Lemma add_ITER1 : ltac2:(CDefT.buildp (gd_tbl_P_mpi_add_abs_C ()) "Pt0,(1.&40.)Pt1,(1.&40.)Pt2,(1.&40.)Praj,(1.&40.)Pa1,(1.&40.)Pa2,(1.&40.)Pa3,(1.&40.)Pa4,(1.&40.)Pa5,(1.&40.)Pa6,(1.&40.)Pa7,(1.&40.)Px21,(1.&40.)Pt3,(1.&40.)Pt4,(1.&40.)Pt5,(1.&40.)Pt6,(1.&40.)Phc,(2.$3.VL,VHI,)PLBc,(4.$5.)Pmc,P,(1.&40.)(6.(1.&8.))Pmoc,$7.Pxs,(4.(1.&40.))PpXc,$8.PN,$8.Pj,$8.P,(<.$3.VL,VHI,Vh,VLB,Vm,Vmo,(=.VX,VsX,VnX,VpX,Vxs0,VpadX,VownX,)Vsp,Vlo,+40.(>.Vra,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vj0,)(?.$5.)R8.R7.R6.R5.(=.VX,+1.R2.R3.R4.VpadX,$10.))P,(11.(9.+1.R2.)(20.R2.R3.))P,(12.$8.(13.(14.R6.)(15.+2.(16.+20.R3.)))(17.VdA,VdB,))(19.$3.R8.(1:.VL,VHI,Vra,Vsp,Vgp,Vtp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VF,Vfc,Vm,Vmo,Vh,VLB,VdA,VdB,Vlo,VX,VsX,VnX,VpX,Vxs0,VpadX,VownX,)(1;.(1<.R18.(18.&40.(:.(1=.&40.Vsp,)+40.))Vgp,Vtp,R1;.R1:.R19.(18.&40.VX,)(18.&40.R4.)(18.&40.+1.)R17.R16.R15.R14.R13.R12.R11.(18.&40.R5.)(18.&40.R6.)(18.&40.(13.(16.+4.R4.)+4.))R10.Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,R?.R>.R=.R<.)VF,(18.&40.+1?;>0.)Vfc,(1>.(1.&40.))R9.(1?.$3.)))")
(* [comment removed for export] *).
  Proof.
    intros until j; intros J0 HJ HV.
    jc_open; pose proof (bv_unsigned_in_range 64 sp) as SPB; change (bv_modulus 64) with (2^64) in SPB; pose proof alloc_ceiling_pos as ACP.
    pose proof alloc_ceiling_bounds as ACV.
    pose proof (xj_facts _ _ _ _ _ _ _ _ _ _ _ _ JCX _ _ _ _ _ _ J0) as (HBR1 & HAP1 & ND1 & MK1 & XS & X0 & X16 & XAL & LEN1 & NR1 & OWN0 & OWN1); cbn [app] in HBR1, HAP1, ND1.
    cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in *.
    ddestruct (OWN1 ltac:(discriminate)) as (_ & N1 & XIN & XPAL & ARR1 & P0 & PC & PI).
    pose proof J0 as JX; xj_open JX; cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in *.
    clear MX1 HH1 SOK1 HPX1 FR1.
    pose proof (munch_refl [(pXc, pXc + 4 * N)] mc) as MU; pose proof (wmono_refl psegs mc) as WM.
    zstep.
    destruct (nth_error xs (Z.to_nat j)) as [w|] eqn:NTH; [| apply nth_error_None in NTH; exfalso; clear - NTH LEN1 HJ; lia].
    pose proof (u32arr_read psegs mc pXc xs j w _ ARR1 NTH ltac:(clear - HJ; lia) eq_refl) as RD.
    zstep. clear RD. zstep.
    pose proof (u32arr_store_ok psegs mc pXc xs j _ ARR1 ltac:(clear - HJ LEN1; lia) eq_refl) as SOK.
    zstep.
    lazymatch goal with |- context [write_to_mem _ _ (le4 ?v)] =>
      pose proof (u32arr_write psegs mc pXc xs j v ARR1 ltac:(clear - HJ LEN1; lia)) as ARR2 end.
    clear ARR1. store_done.
    lazymatch goal with |- aevtM _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m2 end.
    match goal with ST2 : stk psegs m2 _ _, MI2 : mem_inv psegs m2 |- _ =>
      pose proof (xj_limbs _ _ _ _ _ _ _ _ _ _ _ _ JCX _ _ _ _ _ _ _ _ _ _ _ _ _ J0 MU WM MI2 ST2
                    ltac:(intros a NO; left; destruct (outside_dec [(pXc, pXc + 4 * N)] a) as [O|O]; [exfalso; exact (NO O)| cbn in O; clear - O; lia])
                    ltac:(cbn; clear - PC ACL SLO HLS; lia) ltac:(cbn; pose proof (XP1 eq_refl); clear - H; lia) ARR2
                    ltac:(rewrite upd_length; reflexivity)) as J2 end.
    pose proof (limb32_w32_nth xs (Z.to_nat j) w NTH) as LW. pose proof (w32_range w) as WR.
    assert (LVU : limbs_val (upd xs (Z.to_nat j) (Z_to_bv 64 (bv_swrap 32 (bv_unsigned (sx32 w) + 1))))
                  = limbs_val xs + 2 ^ (32 * j) * ((w32 w + 1) mod 2 ^ 32 - w32 w)).
    { rewrite limbs_val_upd by (clear - HJ LEN1; lia). fold (w32 (Z_to_bv 64 (bv_swrap 32 (bv_unsigned (sx32 w) + 1)))).
      rewrite w32_incr, LW. replace (Z.of_nat (Z.to_nat j)) with j by (clear - HJ; lia). reflexivity. }
    zstep. if_cases KB; zify_cond KB; rewrite incr_mod64, bv_unsigned_sx32 in KB; fold (w32 w) in KB.
    - (* [comment removed for export] *)
      apply (proj1 (sxz_le_iff _ _ (w32_range w) ltac:(clear; apply Z.mod_pos_bound; lia))) in KB.
      eapply add_ret0; [exact JCX| exact J2| | reflexivity].
      unfold mpd_val. cbn [md_sg md_limbs]. rewrite LVU. rewrite Z.mod_small by (clear - WR KB; lia). clear - HV. lia.
    - (* [comment removed for export] *)
      apply (proj1 (sxz_lt_iff _ _ ltac:(clear; apply Z.mod_pos_bound; lia) (w32_range w))) in KB.
      zstep. zstep. zstep. zstep. zstep.
      eapply (add_LOOP (Z.to_nat (N - (j + 1))) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ N (j + 1));
        [clear - HJ; lia| exact J2| clear - HJ; lia| | f_equal; clear; lia| f_equal; clear; lia| f_equal; clear; lia].
      rewrite LVU. replace (32 * (j + 1)) with (32 * j + 32) by (clear; lia). rewrite Z.pow_add_r by (clear - HJ; lia).
      assert (w32 w = 2 ^ 32 - 1) by (clear - KB WR; lia). assert ((w32 w + 1) mod 2 ^ 32 = 0) by (rewrite H; reflexivity). clear - HV H H0. nia.
  Qed.

  (* [comment removed for export] *)
  #[using="HFREE HCALLOC MSF MSFE CA TP SPA SLO2 JCX"] Lemma add_FIRST : ltac2:(CDefT.buildp (gd_tbl_P_mpi_add_abs_C ()) "Pt0,(1.&40.)Pt1,(1.&40.)Pt2,(1.&40.)Praj,(1.&40.)Pa1,(1.&40.)Pa2,(1.&40.)Pa3,(1.&40.)Pa4,(1.&40.)Pa5,(1.&40.)Pa6,(1.&40.)Pa7,(1.&40.)Px18,(1.&40.)Px21,(1.&40.)Pt3,(1.&40.)Pt4,(1.&40.)Pt5,(1.&40.)Pt6,(1.&40.)Phc,(2.$3.VL,VHI,)PLBc,(4.$5.)Pmc,P,(1.&40.)(6.(1.&8.))Pmoc,$7.Pxs,(4.(1.&40.))PpXc,$8.PN,$8.Pj,$8.Pc,$8.P,(<.$3.VL,VHI,Vh,VLB,Vm,Vmo,(=.VX,VsX,VnX,VpX,Vxs0,VpadX,VownX,)Vsp,Vlo,+40.(>.Vra,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vj0,)(?.$5.)R9.R8.R7.R6.(=.VX,+1.R3.R4.R5.VpadX,$10.))P,(11.(9.+1.R3.)(9.R3.R4.))P,(11.(9.=R3.)(9.R3.+1.))P,(12.$8.(13.(14.R8.)(16.R4.(15.+2.(16.+20.R5.))))(17.VdA,VdB,))(19.$3.R:.(1:.VL,VHI,Vra,Vsp,Vgp,Vtp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VF,Vfc,Vm,Vmo,Vh,VLB,VdA,VdB,Vlo,VX,VsX,VnX,VpX,Vxs0,VpadX,VownX,)(1;.(1<.R1;.(18.&40.(:.(1=.&40.Vsp,)+40.))Vgp,Vtp,R1>.R1=.R1<.(18.&40.VX,)(18.&40.R6.)(18.&40.R5.)R1:.R19.R18.R17.R16.R15.R14.R13.(18.&40.R8.)(18.&40.(13.(16.+4.R6.)+4.))R12.Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,R11.R10.R?.R>.)VF,(18.&40.+1?;=4.)Vfc,(1>.(1.&40.))R;.(1?.$3.)))")
(* [comment removed for export] *).
  Proof.
    intros until c; intros J0 HJ HC HV.
    jc_open; pose proof (bv_unsigned_in_range 64 sp) as SPB; change (bv_modulus 64) with (2^64) in SPB; pose proof alloc_ceiling_pos as ACP.
    pose proof alloc_ceiling_bounds as ACV.
    pose proof (xj_facts _ _ _ _ _ _ _ _ _ _ _ _ JCX _ _ _ _ _ _ J0) as (HBR1 & HAP1 & ND1 & MK1 & XS & X0 & X16 & XAL & LEN1 & NR1 & OWN0 & OWN1); cbn [app] in HBR1, HAP1, ND1.
    cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in *.
    ddestruct (OWN1 ltac:(discriminate)) as (_ & N1 & XIN & XPAL & ARR1 & P0 & PC & PI).
    pose proof J0 as JX; xj_open JX; cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in *.
    pose proof MX1 as [(CX1 & _) _]. cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in CX1. unfold mpi_cells in CX1.
    pose proof (munch_refl ([] : list ivl) mc) as MU; pose proof (wmono_refl psegs mc) as WM.
    zstep. if_cases K0; zify_cond K0.
    { (* [comment removed for export] *) assert (c = 0) as -> by (clear - K0 HC; lia).
      eapply add_ret; [exact JCX| exact J0|]. left. split; [reflexivity|]. split; [| reflexivity]. unfold mpd_val. cbn [md_sg md_limbs]. clear - HV. lia. }
    assert (c = 1) as -> by (clear - K0 HC; lia).
    zstep. rewrite zx16_small by (clear - NR1; lia). zstep. if_cases K1; zify_cond K1.
    - (* [comment removed for export] *)
      assert (EJ : j = N) by (clear - K1 HJ; lia). subst j.
      zstep. zstep. zstep. zstep. zstep. if_cases K2; zify_cond K2.
      { (* [comment removed for export] *) eapply add_retm16; [exact JCX| exact J0]. }
      zstep. if_cases K3; zify_cond K3; [| exfalso; clear - K3; lia].
      eapply add_G3; [exact HFREE| exact HCALLOC| exact MSFE| exact CA| exact TP| exact SPA| exact SLO2| exact JCX| exact J0| clear - K2 NR1 N1; lia| clear - HV; lia].
    - (* [comment removed for export] *)
      eapply add_ITER1; [exact J0| clear - K1 HJ; lia| clear - HV; lia].
  Qed.
End C.
