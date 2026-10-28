(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib Require Import HeapCeil.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import Tac Arr Bytes ZBridge TacX SFModel SysStep.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.As Require Import ASegs AsShadow AsConst AsIface AsIfaceX AsWalk FakeStackRep N5_tls N5_smkit N5_smkitx.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.As Require Import N8Store.   (* [comment removed for export] *)
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_n8 segs m a bs.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Section HCW.
  Context {HCEIL : HeapCeil}.

Lemma rw_cells_C1_mrd : forall m a b, rw_cells asegs m a [C1 b] -> mrd asegs m (wa a) = Some b.
Proof.
  intros m a b RC. pose proof (rw_cells_read asegs m a [C1 b] 0 (C1 b) RC eq_refl) as R.
  rewrite Z.add_0_r in R. cbn [csize cbytes] in R. rewrite ov_rdn in R. cbn [rdn] in R.
  unfold mrd. destruct (m (wa a)) as [x|]; [| destruct (seg_rom asegs (wa a)) as [x|]]; cbn in R; congruence.
Qed.

Section SF6.
  Variable H : asr.
  Hypothesis RFS_is : forall LF m, as_RFS H LF m <-> RFSI (as_FSB H) LF m.

  Lemma stack_free_6_ok : stack_free_6_stmt H.
  Proof.
    intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m LF ff fp lo n junk1 junk2 spv.
    intros RFS IN FRM Ha0 Ha1 Hn ST0 LO LOSP MI AC. subst a0 a1.
    pose proof (proj1 (RFS_is LF m) RFS) as R. clear RFS.
    remember (as_FSB H) as fsb eqn:Hfsb.
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. change (2 ^ Z.of_N 64) with (2^64) in SPR.
    acb; unfold AFS_STACK, AFS_FREE_6, fsz, fshn in *. change (64 * 2 ^ 6) with 4096 in *. change (8 * 2 ^ 6) with 512 in *.
    change (Z.to_nat (4096 - 40)) with 4056%nat in FRM.
    pose proof R as ((G1 & G2 & G3 & G4) & TLS & (h0 & h1 & h2 & h3 & h4 & h5 & h6 & h7 & h8 & h9 & h10 & HDR) & SL & ND & FL & STF & STS).
    acb; unfold AIMG_TOP, AFS_SIZE, AFS_HDR in G1, G2, STF, STS. unfold hdr in HDR.
    destruct (SL _ IN) as (pos & SOK & EFF & EFP). cbn [ff_class ff_addr ff_flag fst snd] in SOK, EFF, EFP.
    pose proof SOK as [_ HP]. change (NF 6) with 256 in HP.
    assert (HFF : ff = fsb + 6328320 + 4096 * pos) by (rewrite EFF; unfold frame_addr, AFS_HDR, AsIface.fsz; cbn; lia).
    assert (HFP : fp = fsb + 36352 + pos) by (rewrite EFP; unfold flag_addr, AFS_HDR; cbn; lia).
    (* [comment removed for export] *)
    pose proof (FL 6 pos SOK) as CFP. rewrite <- EFP in CFP.
    (* [comment removed for export] *)
    remember (sh ff) as SF eqn:HSF.
    assert (SFR : 2148314624 <= SF /\ SF + 512 <= 17594333495296 /\ sh fsb <= SF /\ SF + 512 <= sh (fsb + 11571200)).
    { subst SF. rewrite HFF. unfold sh. rewrite ASHADOW_BASE_val. Z.div_mod_to_equations. lia. }
    assert (SEP : fsb + 11571200 <= 2147446784 \/ 17594333495296 <= fsb)
      by (clear - G4; destruct G4 as [[X1 X2]|[X1 X2]]; unfold AIMG_TOP, ALOWSH_LO, AHI_LO, AFS_SIZE in X1, X2; lia).
    assert (SFW : SF + 512 <= fsb \/ fsb + 11571200 <= SF).
    { subst SF. rewrite HFF. unfold sh. rewrite ASHADOW_BASE_val. clear - SEP HP G1. Z.div_mod_to_equations. lia. }
    assert (TPW : ATP + 48 <= bv_unsigned sp - 1024 /\ ATP + 48 <= SF) by (unfold ATP; acb; clear - SFR LO LOSP ST0 G1 G2; acb; lia).
    destruct (stk_split asegs m _ (SF + 512) _ STS ltac:(lia)) as [SSa SSc].
    destruct (stk_carve asegs m _ _ 512 SSa ltac:(lia)) as [SSa' [sjunk SRM]].
    replace (SF + 512 - Z.of_nat 512) with SF in SSa', SRM by lia. clear SSa SSc STF STS.
    (* [comment removed for export] *)
    pose proof (ACONST_mts m AC) as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6).
    unfold AGOT_SHBASE, ASHBASE_CELL, AGOT_MIDBEG, AMIDBEG_CELL, AGOT_MIDEND, AMIDEND_CELL, AGOT_HIEND, AHIEND_CELL, wz in Q1, Q2, Q3, Q4, Q5, Q6.
    unfold ATP, wz in TLS.
    (* [comment removed for export] *)
    pose proof (munch_refl [(bv_unsigned sp - 1024, bv_unsigned sp); (fp, fp + 1); (SF, SF + 512)] m) as MU.
    pose proof (wmono_refl asegs m) as WM.
    pose proof ST0 as ST. carve_frame 16%nat ST.
    (* [comment removed for export] *)
    zstep. st1. st1.
    (* [comment removed for export] *)
    zstep. zstep. zstep. st1.
    (* [comment removed for export] *)
    zstep.
    call_pure mts_spec; try reflexivity; try eassumption;
      [clear - G4 HFF HP; destruct G4 as [[G4a G4b]|[G4a G4b]]; unfold AIMG_TOP, ALOWSH_LO, AHI_LO, AAPP_HI, AFS_SIZE in *; [left | right]; acb; lia|].
    rewrite <- HSF.
    (* [comment removed for export] *)
    zstep. zstep. zstep.
    (* [comment removed for export] *)
    do 63 (st1; zstep; zstep; if_cases KL; zify_cond KL; [| exfalso; rewrite ?unsigned_lit in KL by lia; lia]; clear KL).
    st1. zstep. zstep. if_cases KL; zify_cond KL; [exfalso; rewrite ?unsigned_lit in KL by lia; lia|]. clear KL.
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep.
    match goal with Hfr : rw_cells asegs ?mx (bv_unsigned sp + -16) [C8 _; C8 _] |- _ => rename Hfr into FR end.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
      match goal with Hmu : munch _ m mx, Hwm : wmono asegs m mx, Hcf : rw_cells asegs mx fp [C1 _] |- _ =>
        rename Hmu into MUf; rename Hwm into WMf; rename Hcf into CFPf end end.
    release_frame FR ST (bv_unsigned sp).
    assert (FF8 : 0 <= ff /\ ff mod 8 = 0) by (rewrite HFF; Z.div_mod_to_equations; lia).
    unfold stack_free_post. finish.
    all: lazymatch goal with
         | |- munch _ _ _ => subst SF; exact MUf
         | |- SHAD _ _ _ => subst SF; apply shad512_f5; [lia| lia| eassumption]
         | |- ACONST _ => eapply ACONST_frame; [exact AC| exact MUf| exact WMf|];
                          repeat apply Forall_cons; [| | |apply Forall_nil]; subst SF fsb; aconst5 G1 G4
         | |- as_RFS _ _ _ => subst fsb; eapply (RFSI_release H RFS_is LF m _ _ 6 ff fp);
              [apply RFS_is; exact R| exact IN| exact MUf| exact WMf| | apply rw_cells_C1_mrd; exact CFPf];
              apply Forall_cons; [left; unfold afs_write_ok; cbn [fst snd]; left; unfold AFS_SIZE, ATLS_PRIV_LO, ATLS_PRIV_HI, ATP in *; clear - G2 LO LOSP TPW; lia|];
              apply Forall_cons; [right; cbn [fst snd]; split; reflexivity|];
              apply Forall_cons; [left; unfold afs_write_ok; cbn [fst snd]; left; unfold AFS_SIZE, ATLS_PRIV_LO, ATLS_PRIV_HI, ATP in *; clear - SFW TPW; lia|];
              apply Forall_nil
         | |- _ => idtac
         end.
  Qed.
End SF6.
End HCW.
