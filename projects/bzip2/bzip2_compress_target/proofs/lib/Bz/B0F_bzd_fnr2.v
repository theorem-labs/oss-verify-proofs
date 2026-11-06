(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import Wf_nat.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require Import PropExec.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import Tac WalkLib SegsA0 SegsB0 StoreFast.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzModel BzTac BzDefs BzInv BzTables BzLemmasT BzLemmasMtf S0_bzd_out BzSepTac.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import CmpMem CmpArith BzCLemmas1.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzArr BzCStream BzDState.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzDBlock.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzDBlock BzDOut BzDOK DecCutF DecTacF.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzArr OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCStream OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDState OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDBlock.BzDHuff OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDBlock OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDOut OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDOK OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.DecCutF OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.DecTacF.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import S0F_bzd_out.
(* [comment removed for export] *)
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzTac2 AsanKit AsanCut AsanCutB0 AsanKitB0 DecCutB B0F_decV B0F_bzdV B0F_bzd_uV.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require B0F_bzd_fnr1.
From Stdlib Require Lia. Unset Lia Cache.
Import ListNotations. Open Scope bv_scope.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require Import ACeil.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require StoreFastZ StoreFastC.   (* [comment removed for export] *)
Local Ltac mem_after_store ::= first [ StoreFastC.mem_after_store_fastzc | StoreFastZ.mem_after_store_fastz | mem_after_store_fast ].
(* [comment removed for export] *)
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import CpsOpen.
Ltac unhide_disj := repeat match goal with H : id (?A \/ ?B) |- _ => unfold id in H end.
Ltac hide_disj := repeat match goal with H : ?A \/ ?B |- _ => change (A \/ B) with (id (A \/ B)) in H end.
Local Ltac tlia ::= first [ Zify.zify; xlia zchecker
                         | sf_unhide; unhide_disj;
                           first [ zify_prune_neg; Zify.zify; xlia zchecker
                                 | zify_prune_plain; Zify.zify; xlia zchecker
                                 | Zify.zify; xlia zchecker ] ].
Local Ltac tslia ::= tslia_sep.
(* [comment removed for export] *)
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import NatLit.
Local Ltac Zify.zify_pre_hook ::= NatLit.natlen_ctx.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require NormFast RelLiaA SasFastF RelLiaS.
(* [comment removed for export] *)
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require StepFast.
Local Ltac Lib.Step.step_core segs R F pc fc rv m ro ::= StepFast.sf_step_core.
Local Ltac Lib.Step.zstep ::= StepFast.sf_zstep.
#[local] Ltac2 Set StepFast.sf_foldgoal := Ltac2.Init.true.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require RangeFast RangeFastEnv.
#[local] Ltac2 Set RangeFast.RF.rc_atom_facts := RangeFastEnv.env_atom_facts.
Local Ltac Lib.ZBridge.flia ::= RangeFast.rc_decide ltac:(first [ assumption | Lib.ZBridge.slim; lia | lia ]).
Local Ltac Lib.ZBridge.mlia ::= RangeFast.rc_decide ltac:(Z.div_mod_to_equations; lia).
Local Ltac Bz.BzTac.mlia ::= RangeFast.rc_decide ltac:(Z.div_mod_to_equations; lia).
#[local] Ltac2 Set RangeFast.RF.rc_or_boxes := fun () => [constr:(@id); constr:(Lib.StoreFast.sf_hide)].
Local Ltac Bz.BzSepTac.tlia2 ::= first [ RangeFast.rc_prune_lia | Lib.StoreFast.sf_unhide; Bz.BzSepTac.unhide_disj; first [ Lib.StoreFast.zify_prune_neg; Zify.zify; xlia zchecker | Lib.StoreFast.zify_prune_plain; Zify.zify; xlia zchecker | Zify.zify; xlia zchecker ] ].
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac lia ::= RelLiaA.lia_rf.
Local Ltac BzTac.bz32 ::= NormFast.bz32_m.
Local Ltac BzTac2.bz32l ::= NormFast.bz32l_m.
Local Ltac Zify.zify_pre_hook ::= NormFast.nf_pre_natlen.
Local Ltac DecCutF.unset_Z ::= NormFast.unset_Z_subst.
Local Ltac simpl_arr_sizes ::= SasFastF.sas6F_all.
Local Ltac tlia ::= RelLiaS.tlia_bzd_r.
Local Ltac BzSepTac.tlia1 ::= RelLiaS.tlia1_r.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac Lib.Step.solve_load ::= AsanKit.asan_solve_load.
Local Ltac AsanKit.a_norm ::= AsanKit.sh_fold.
Section ACeilS1. Context {ACEIL__ : ACeil}.

Section FNR.
  Variable c : foctx.
  Variable SHS : Z. Variable w0 : word.
  Notation cx := (o_cx c). Notation J := (o_J c). Notation d0 := (o_d c). Notation s0 := (o_s c).
  Notation S := (b_s (o_cx c)). Notation STRM := (b_strm (o_cx c)). Notation DST := (b_dst (o_cx c)). Notation dlen := (b_dlen (o_cx c)).
  Notation n := (b_n (o_cx c)). Notation TT := (b_tt (o_cx c)).
  Notation snb := (sv_nblock (d_sv (o_d c))). Notation av0 := (s_avail_out (o_s c)). Notation PP := (sv_nblock (d_sv (o_d c)) + 1)%Z.
  Notation cap := (100000 * b_n (o_cx c))%Z.
  Notation F := (o_F c). Notation fc := (o_fc c). Notation KQ := (o_KQ c). Notation m0 := (o_m0 c).
  Notation uspi := (bv_unsigned (o_SP c)).
  Notation RO := (FROfA DI_B0 c). Notation WB := (FWBA c).
  Hypothesis OK : foctx_okA c BIHI0. Hypothesis OKF : foctx_okFA c BIHI0. Hypothesis ALT : (b_tt (o_cx c) mod 4 = 0)%Z.
  Hypothesis ANS : sanchor S SHS.
  Hypothesis SH : obz_sh DI_B0 c WB m0.
  Hypothesis KJ : B0_FKjoin c SHS w0 (FROfA DI_B0 c) (FWBA c).
  Hypothesis KE : B0_FKexit c SHS w0 (FROfA DI_B0 c) (FWBA c).

  (* [comment removed for export] *)
  Notation KH1 := (K_H1 (d_tt (o_d c)) (100000 * b_n (o_cx c)) (sv_nblock (d_sv (o_d c)) + 1)).
  Notation KH2 := (K_H2 (d_tt (o_d c)) (100000 * b_n (o_cx c)) (sv_nblock (d_sv (o_d c)) + 1)).
  Notation KDR := (K_DR (d_tt (o_d c)) (100000 * b_n (o_cx c)) (sv_nblock (d_sv (o_d c)) + 1)).
  Notation KG := (ucG (d_tt (o_d c)) (100000 * b_n (o_cx c)) (sv_nblock (d_sv (o_d c)) + 1)).
  Notation KG2 := (G2 (d_tt (o_d c)) (100000 * b_n (o_cx c)) (sv_nblock (d_sv (o_d c)) + 1)).
  Notation CC r := (ccommit (o_d c) (o_s c) r).

  (* [comment removed for export] *)
  Notation FSLc m := (rw_cells b0segs m uspi
    (bzd_slots S SHS w0 (Z_to_bv 64 (SHS + 7)) (Z_to_bv 64 (SHS + 394)) (Z_to_bv 64 (SHS + 8)) (Z_to_bv 64 (SHS + 136)) (Z_to_bv 64 (SHS + 2))
               (Z_to_bv 64 (SHS + 1)) (Z_to_bv 64 (18446744073709551615 - TT)) (Z_to_bv 64 (SHS + -2147450744)) (Z_to_bv 64 (SHS + -2147442870)))).

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Ltac unRO H := let GOT := ident:(GOT) in cps_destruct H as (SAV & TTA & CRC & RNA & GOT & MI); unfold FGOTA in GOT; b0img.
  Ltac unDS H := cps_destruct H as (HD & NBU & MID & SM).
  Ltac unSH := let SHbf := ident:(SHbf) in let SH' := fresh "SH" in pose proof SH as SH';
    cps_destruct SH' as (SHs & SHt & SHd & SHc & SHr & SHbf & _); b0img;
    let OKF' := fresh "OKF" in pose proof OKF as OKF'; specialize (SHbf (proj1 OKF')); clear OKF'.
  Ltac prep :=
    let JWF := ident:(JWF) in let ENT := ident:(ENT) in let ALS := ident:(ALS) in let ALM := ident:(ALM) in let OK' := fresh "OK" in pose proof OK as OK';
    cps_destruct OK' as (HS & HSTRM & HDST & Hdlen & HSP & (ALS & ALM) & SEP_SM & SEP_SD & SEP_MD & IAS & IAM & IAD & HIHI & JWF & ENT);
    let OKF' := fresh "OKF" in pose proof OKF as OKF';
    cps_destruct OKF' as (HSM & HTT & SEP_ST & SEP_MT & SEP_DT & IAT);
    destruct (zmod16_lin _ ALS) as [qS EqS]; destruct (zmod8_lin _ ALM) as [qSTRM EqSTRM]; destruct (zmod4_lin _ ALT) as [qTT EqTT];
    clear ALS ALM;
    cps_destruct ENT as (En & Rn & Esm & Rsnb & Rsnb1 & Rav0 & Lout0 & Eol0 & RtP0 & NK0 & Rcb0 & Roc0 & Rr01 & Rrnd & _ & Rtt & _ & _);
    cps_destruct JWF as (Lp1 & Lp2 & Lp3 & Ls1 & Ls2 & Lq1 & Lq2);
    unfold disj, bzd_img_apart in *;
    unfold FWBA, FWB in *; cbn [app] in *; pose proof alloc_ceiling_range as ACR;
    pose proof (zw32_length (d_tt d0) cap ltac:(lia)) as TTL; pose proof rnums_words_length as RNL; pose proof crc_words_length as CRCL;
    pose proof (proj2 ANS : saddr S SHS) as ANS0;
    hide_disj.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Ltac ro_close := unfold FROfA, FGOTA; b0img; repeat match goal with |- _ /\ _ => split end; assumption.
  (* [comment removed for export] *)

  Notation csnb := (Z_to_bv 64 snb). Notation cpp := (Z_to_bv 64 (snb + 1)). Notation cnn := (Z_to_bv 64 (100000 * n)).
  Notation ctt := (Z_to_bv 64 TT).
  Notation optr av := (Z_to_bv 64 (DST + (dlen - av))).
  Notation hs7 := (Z_to_bv 64 (SHS + -2147450878)).
  Notation DESTc := (B0F_bzd_fnr1.DESTc c).
  Notation XS := (B0F_bzd_fnr1.XS c SHS w0). Notation GS := (B0F_bzd_fnr1.GS c SHS w0). Notation G2S := (B0F_bzd_fnr1.G2S c SHS w0).
  Notation HS := (B0F_bzd_fnr1.HS c SHS w0). Notation DRS := (B0F_bzd_fnr1.DRS c SHS w0).
  Let fnr_W := B0F_bzd_fnr1.fnr_W c SHS w0 OK OKF ALT ANS SH KJ.
  Let KEc := B0F_bzd_fnr1.KEc c SHS w0 OK KE.

  Ltac cc1 := lazymatch goal with |- evt _ (o_KQ c (ccommit _ _ (1%Z, ?X))) _ =>
    change (ccommit (o_d c) (o_s c) (1%Z, X)) with (1%Z, o_d c, o_s c) end.
  Ltac exitK := cc1;
    lazymatch goal with DSTA : u8arr _ _ DST _, DL : Z.of_nat (length _) = dlen, Edb : id (_ = _) |- _ =>
      unfold id in Edb;
      eapply KEc; [unfold DSgA; b0img; dvF_cbn; repeat match goal with |- _ /\ _ => split end; assumption
                  | exact DSTA | exact DL | exact Edb | unfold bzd_slots; assumption | ro_close | assumption | assumption] end.
  Ltac tt_load pc i :=
    brun_to pc;
    lazymatch goal with TTA : u32arr _ ?mm TT _ |- _ =>
      let RD := fresh "RD" in
      pose proof (zw32_read b0segs mm TT (d_tt d0) cap i _ TTA ltac:(lia) ltac:(unfold wa; f_equal; lia)) as RD;
      wstep; clear RD end.
  Ltac cinv_close := unfold cinv; ccbv; cbn [length]; repeat match goal with |- _ /\ _ => split end; first [lia | mlia].
  Ltac tp_rel := ccbv; apply u64_mod32_small; first [lia | mlia].
  Ltac mif_neq a b := rewrite (proj2 (Z.eqb_neq a b)) by lia; cbn [negb].
  Ltac mif_eq a b := rewrite (proj2 (Z.eqb_eq a b)) by lia; cbn [negb].

  (* [comment removed for export] *)
  Ltac dst_write av ch Edb RL :=
    let E' := ident:(E') in let R' := ident:(R') in lazymatch goal with DSTA : u8arr _ _ DST ?bs |- _ =>
      let SOK := fresh "SOK" in
      pose proof (u8arr_store_ok b0segs _ DST _ (dlen - av) _ DSTA ltac:(lia) eq_refl) as SOK;
      wstep; rewrite BzInv.le1_lit;
      let D := fresh "DSTB" in
      pose proof (u8arr_write b0segs _ DST _ (dlen - av) (Z_to_bv 8 ch) DSTA ltac:(lia)) as D;
      clear DSTA; store_done; try clear SOK; rename D into DSTA;
      lazymatch goal with DL : Z.of_nat (length bs) = _ |- _ =>
        let D2 := fresh "DLB" in
        pose proof DL as D2; rewrite <- (upd_length bs (Z.to_nat (dlen - av)) (Z_to_bv 8 ch)) in D2; clear DL; rename D2 into DL;
        unfold id in Edb;
        let r' := fresh "rest" in let E' := fresh "Edb" in let R' := fresh "RL" in
        cps_destruct (destc_snoc _ _ _ _ (Z.to_nat (dlen - av)) ch av Edb ltac:(rewrite length_map, length_rev; lia) RL ltac:(lia)) as (r' & E' & R');
        clear Edb RL; rename E' into Edb; rename R' into RL;
        let db := fresh "dbytes" in
        remember (upd bs (Z.to_nat (dlen - av)) (Z_to_bv 8 ch)) as db eqn:Xdb; clear Xdb;
        lazymatch type of Edb with ?x = ?y => change (id (x = y)) in Edb end
      end end.
  (* [comment removed for export] *)
  Ltac crc_load pclw crc ch :=
    let Hidx := fresh "Hidx" in
    pose proof (crc_idx_byte crc ch ltac:(lia) ltac:(lia)) as Hidx;
    brun_to pclw;
    lazymatch goal with CRC : u32arr _ ?mm 857056 crc_words |- _ =>
      let RD := fresh "RD" in
      pose proof (u32arr_read b0segs mm 857056 crc_words (Z.lxor (crc / 16777216) ch) _ _ CRC (crc_words_nth _ Hidx) ltac:(lia) eq_refl) as RD;
      wstep; clear RD end; clear Hidx.
  Ltac fix_optr av :=
    replace (Z_to_bv 64 (DST + (dlen - av) + 1)) with (Z_to_bv 64 (DST + (dlen - (av - 1)))) by (f_equal; lia).
  (* [comment removed for export] *)
  Ltac goHS IH crcw dbytes rest DSTA DL Edb RL FSL MU WM Hcrc :=
    enter_with (IH _ _ _ _ _ _ _ _ crcw _ _ dbytes rest);
    [ ccbv; st_eq
    | unfold DSgA; b0img; dvF_cbn; repeat match goal with |- _ /\ _ => split end; assumption
    | unfold B0F_bzd_fnr1.DESTc; ccbv; repeat match goal with |- _ /\ _ => split end; [exact DSTA| exact DL| exact Edb| exact RL]
    | unfold bzd_slots; exact FSL
    | ro_close | exact MU | exact WM
    | cinv_close | ccbv; exact Hcrc | tp_rel | ccbv; lia ].

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma fnr_G2 : forall f', (forall cl', HS f' cl') -> forall cl, G2S f' cl.
  Proof.
    intros f' IHH cl. unfold B0F_bzd_fnr1.G2S. intros until rest. intros DSm DE FSL ROm MU WM CI Hcrc Hlen Hnu Hf.
    unDS DSm. unRO ROm. cps_destruct DE as (DSTA & DL & Edb & RL). prep. unSH.
    cps_destruct CI as (Ccrc & Cch & Clen & Cnu & Ck0 & Ctp & Cav & Cout).
    destruct cl as [crc ch len nu k0 tp out av]. cbn [c_crc c_ch c_len c_nused c_k0 c_tPos c_out c_avail] in *. subst len.
    change (id (dbytes = map (Z_to_bv 8) (rev (s_out s0)) ++ map (Z_to_bv 8) (rev out) ++ rest)) in Edb.
    unfold DSgA in *. b0img. dvF_cbn_in HD. dvF_cbn_in MID. dvF_cbn_in SM. unfold bzd_slots in FSL.
    (* [comment removed for export] *)
    wstep. if_cases K1; zify_cond K1.
    2:{ rewrite G2_None by (ccbv; lia). wstep. exitK. }
    rewrite G2_Some by (ccbv; lia). ccbv.
    (* [comment removed for export] *)
    tt_load 0x8758c%Z tp. pose proof (Rtt tp) as Rw2. set (w2 := zget (d_tt d0) tp) in *. pose proof (div256_range w2 Rw2) as Dw2. rewrite ?(zx32_of_Z w2) by lia.
    (* [comment removed for export] *)
    wstep. wstep. wstep. wstep.
    wstep. if_cases K2; zify_cond K2.
    { (* [comment removed for export] *)
      mif_eq (nu + 1)%Z (sv_nblock (d_sv (o_d c)) + 1)%Z.
      goHS IHH crcw dbytes rest DSTA DL Edb RL FSL MU WM Hcrc. }
    mif_neq (nu + 1)%Z (sv_nblock (d_sv (o_d c)) + 1)%Z.
    (* [comment removed for export] *)
    wstep. wstep. pose proof (BzDOK.land255_byte w2) as CH2.
    wstep. if_cases K3; zify_cond K3.
    { mif_neq (Z.land w2 255) k0.
      goHS IHH crcw dbytes rest DSTA DL Edb RL FSL MU WM Hcrc. }
    mif_eq (Z.land w2 255) k0.
    (* [comment removed for export] *)
    wstep. if_cases K4; zify_cond K4.
    2:{ rewrite G3_None by (ccbv; first [lia | mlia]). wstep. exitK. }
    rewrite G3_Some by (ccbv; first [lia | mlia]). ccbv.
    tt_load 0x875ec%Z (w2 / 256)%Z. pose proof (Rtt (w2 / 256)%Z) as Rw3. set (w3 := zget (d_tt d0) (w2 / 256)) in *. pose proof (div256_range w3 Rw3) as Dw3. rewrite ?(zx32_of_Z w3) by lia.
    (* [comment removed for export] *)
    wstep. wstep. wstep. wstep.
    wstep. if_cases K5; zify_cond K5.
    { mif_eq (nu + 2)%Z (sv_nblock (d_sv (o_d c)) + 1)%Z.
      goHS IHH crcw dbytes rest DSTA DL Edb RL FSL MU WM Hcrc. }
    mif_neq (nu + 2)%Z (sv_nblock (d_sv (o_d c)) + 1)%Z.
    (* [comment removed for export] *)
    wstep. wstep. pose proof (BzDOK.land255_byte w3) as CH3.
    wstep. if_cases K6; zify_cond K6.
    { mif_neq (Z.land w3 255) k0.
      goHS IHH crcw dbytes rest DSTA DL Edb RL FSL MU WM Hcrc. }
    mif_eq (Z.land w3 255) k0.
    (* [comment removed for export] *)
    wstep. if_cases K7; zify_cond K7.
    2:{ rewrite G4_None by (ccbv; first [lia | mlia]). wstep. exitK. }
    rewrite G4_Some by (ccbv; first [lia | mlia]). ccbv.
    (* [comment removed for export] *)
    tt_load 0x8764c%Z (w3 / 256)%Z. pose proof (Rtt (w3 / 256)%Z) as Rw4. set (w4 := zget (d_tt d0) (w3 / 256)) in *. pose proof (div256_range w4 Rw4) as Dw4. rewrite ?(zx32_of_Z w4) by lia.
    (* [comment removed for export] *)
    wstep.
    (* [comment removed for export] *)
    wstep. if_cases K8; zify_cond K8.
    2:{ rewrite G5_None by (ccbv; first [lia | mlia]). wstep. exitK. }
    rewrite G5_Some by (ccbv; first [lia | mlia]). ccbv.
    (* [comment removed for export] *)
    tt_load 0x8768c%Z (w4 / 256)%Z. pose proof (Rtt (w4 / 256)%Z) as Rw5. set (w5 := zget (d_tt d0) (w4 / 256)) in *. pose proof (div256_range w5 Rw5) as Dw5.
    pose proof (BzDOK.land255_byte w4) as CH4. pose proof (BzDOK.land255_byte w5) as CH5.
    (* [comment removed for export] *)
    wstep. wstep. wstep. wstep.
    rewrite ?(sx32_mod32 w5), ?(sx32_land255 w5) by lia.
    wstep. (* [comment removed for export] *)
    goHS IHH crcw dbytes rest DSTA DL Edb RL FSL MU WM Hcrc.
  Time Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma fnr_X : forall f cl, GS f (c_write cl) -> XS f cl.
  Proof.
    intros f cl G. unfold B0F_bzd_fnr1.XS. intros until rest. intros DSm DE FSL ROm MU WM CI Hcrc Htp Hf.
    unDS DSm. unRO ROm. cps_destruct DE as (DSTA & DL & Edb & RL). prep. unSH.
    cps_destruct CI as (Ccrc & Cch & Clen & Cnu & Ck0 & Ctp & Cav & Cout).
    destruct cl as [crc ch len nu k0 tp out av]. cbn [c_crc c_ch c_len c_nused c_k0 c_tPos c_out c_avail] in *.
    change (id (dbytes = map (Z_to_bv 8) (rev (s_out s0)) ++ map (Z_to_bv 8) (rev out) ++ rest)) in Edb.
    unfold DSgA in *. b0img. dvF_cbn_in HD. dvF_cbn_in MID. dvF_cbn_in SM. unfold bzd_slots in FSL. ccbv_in G.
    rewrite K_H2_eq. ccbv.
    wstep. if_cases K0; zify_cond K0.
    - (* [comment removed for export] *)
      rewrite (proj2 (Z.eqb_eq av 0)) by lia.
      wstep. wstep. wstep. wstep.
      enter_with (fnr_W _ _ _ _ _ _ _ _ _ crcw tpw _ _ dbytes rest);
        [ ccbv; st_eq
        | unfold DSgA; b0img; dvF_cbn; repeat match goal with |- _ /\ _ => split end; assumption
        | unfold B0F_bzd_fnr1.DESTc; ccbv; repeat match goal with |- _ /\ _ => split end; [exact DSTA| exact DL| exact Edb| exact RL]
        | unfold bzd_slots; exact FSL
        | ro_close | exact MU | exact WM
        | unfold cinv; ccbv; lia | ccbv; exact Hcrc | ccbv; exact Htp ].
    - rewrite (proj2 (Z.eqb_neq av 0)) by lia.
      assert (AV1 : (1 <= av)%Z) by lia.
      pose proof (u8arr_bound _ _ _ _ DSTA) as DB.
      (* [comment removed for export] *)
      brun_to 0x87464%Z. ack_rd (DST + (dlen - av))%Z 1%Z. ack_merge.
      (* [comment removed for export] *)
      wstep. wstep. wstep. rewrite Hcrc. wstep. wstep. wstep.
      pose proof (crc_idx_byte crc ch ltac:(lia) ltac:(lia)) as CIR.
      (* [comment removed for export] *)
      dst_write av ch Edb RL.
      (* [comment removed for export] *)
      crc_load 0x874b0%Z crc ch. clear CIR.
      (* [comment removed for export] *)
      wstep. wstep. fix_optr av.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
        lazymatch goal with DSTA : u8arr _ _ DST ?db |- _ => lazymatch type of RL with Z.of_nat (length ?r) = _ =>
          pose proof (crc_step_rel crcw crc ch Hcrc ltac:(lia) ltac:(lia)) as Hcrc';
          unfold B0F_bzd_fnr1.GS in G;
          enter_with (G _ _ _ _ _ _ _ _ _ tpw mm db r);
          [ ccbv; st_eq
          | unfold DSgA; b0img; dvF_cbn; repeat match goal with |- _ /\ _ => split end; assumption
          | unfold B0F_bzd_fnr1.DESTc; ccbv; repeat match goal with |- _ /\ _ => split end; [exact DSTA| exact DL| exact Edb| exact RL]
          | unfold bzd_slots; exact FSL
          | ro_close | exact MU | exact WM
          | pose proof (crc_update_range crc ch ltac:(lia)); cinv_close | ccbv; exact Hcrc' | ccbv; exact Htp | ccbv; lia ]
        end end end.
  Time Qed.
End FNR.
End ACeilS1.
