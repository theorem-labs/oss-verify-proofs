(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.K5.Lib Require Import SFModel Arr SysStep.
From OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.K5.A08 Require Import ImageA.
From OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.K5.Lib Require Import FP ITree Nodes Decode.
From OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.K5.Lib Require Import StoreFast.
From OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.K5.Spec Require Import Prelim Monad PrintfModel.
From OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.K5.Spec Require PrintfFormats.
From OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.K5.A08 Require Import FX_lib F_memset F_memcpy F_fwritex F_pop_arg F_printf_iface F_printf_core.
From OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.K5.A08 Require Import F_printf_snsink F_sn_write F_towrite F_vfprintf F_vsnprintf.
From OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.K5.A08 Require Import F_pkit R_m2s I_consts I_qck F_achk.
From OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.K5.A08 Require Import I_pck I_pcbits I_pchead I_pcseg I_pcfmt I_vprintfw I_vfsnw I_pcgen I_vsngen F_vfprintf_sn2 F_vsnprintf2.
From OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.K5.Spec Require Import PrintfModel.
(* [comment removed for export] *)
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
From OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.K5.G3 Require Import Printf_sn2.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Definition PCLEPT (fmt : list Z) (args : list parg) (slots : list word) (A VA lo : Z) (m : mem) : Prop :=
  exists (t0 : list Z) (ds : list pitem),
    fmt = t0 ++ ptail ds ++ [0] /\ txt_ok t0 = true /\ Forall pitem_ok ds /\ (1 <= length (t0 ++ ptail ds))%nat
    /\ cstr_at m A (zb8 (t0 ++ ptail ds)) /\ A + Z.of_nat (length t0) + Z.of_nat (length (ptail ds)) + 1 <= lo
    /\ chk_ok m A (Z.of_nat (length t0) + Z.of_nat (length (ptail ds)) + 1)
    /\ pargs m (2^64) lo VA ds /\ VA + 8 * Z.of_nat (length ds) < 2^63
    /\ pctx m /\ pfcells m.

Section WithRIP.
Hypothesis RIP : rip_stmt.

Local Ltac tr_chk C MU := apply (chkr_munch _ _ _ _ _ C MU); intros ?x ?Hx; cbn [outside]; unfold SHADOW_LO, SHADOW_HI, kHighShadowEnd in *; lia.

Theorem ivfsn_lept2 : ivfsn_stmt2 PCLEPT.
Proof using RIP.
  unfold ivfsn_stmt2. intros until cap. cbv zeta.
  intros -> -> -> FH FR CKC DST BY HF P1 VAA AOK MODEL FPF CAP0 CAPN NH CAPD Hbufp ST LO GLO Q47 Q16 SSP MI FRM HA0 HA QF FVA VAHI FCK CKVA CKHI
    DLO GD HSH IC STKC FMTC ROD CHD DSH PC.
  destruct PC as (t0f & ds & EF & OK0 & OKD & L1 & CSA & ABL & CHKA & PA & VAH & PCX & PFC).
  set (q := bv_unsigned sp) in *.
  pose proof (bv_unsigned_in_range 64 sp) as Rq. unfold bv_modulus in Rq. change (2 ^ Z.of_N 64)%Z with (2^64)%Z in Rq.
  unfold IVF_DEPTH, GLOBALS_TOP, STATIC_SPLIT, kHighShadowEnd in *.
  pose proof (rw_cells_bound _ _ _ _ FH) as FB. cbn [cells_size snfile_head gfile_cells csize Nat.add] in FB.
  assert (ESP : sp = Z_to_bv 64 q) by (symmetry; apply Z_to_bv_bv_unsigned).
  (* [comment removed for export] *)
  eapply evt_cut.
  { rewrite ESP. eapply (ivfsn_walkA_gen RIP q Fp A VA lo t0f ds);
      first [exact ST | exact PCX | exact PFC | exact MI | lia | (unfold kHighShadowEnd; lia)
            | (split; [exact OK0|]; split; [exact OKD|]; split; [exact L1|]; split; [exact CSA|]; split; [exact ABL|]; split; [exact CHKA|];
               split; [apply (pargs_weaken ds m (2^64) q lo VA PA); lia|]; split; lia)]. }
  cbv beta. intros ms1 P. unfold ivfA_post in P.
  destruct P as (m1 & t0' & t1' & t2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & -> & MU1 & WM1 & MI1 & ST1 & FRf).
  assert (EU48 : bv_unsigned (Z_to_bv 64 (q + -48)) = q + -48) by (apply unsigned_lit; lia).
  (* [comment removed for export] *)
  assert (AOK1 : args_ok Fp (q + -48 - 352) 80 CK 16 D (Z.of_nat dn) m1 lo (q + -48) (q + -48 - VF_FRAME) slots args).
  { replace (q + -48 - 352) with (q - 400) by lia. replace (q + -48 - VF_FRAME) with (q - 416) by (unfold VF_FRAME; lia).
    eapply args_ok_vf; [exact AOK | lia | | unfold kHighShadowEnd; lia | unfold SHADOW_HI; lia].
    eapply munch_weaken; [| exact MU1]. unfold sub_fp; intros ?x ?Hx; cbn [outside] in *; lia. }
  assert (STK1 : forall p n, lo <= p -> p + n <= q + -48 -> chkr m1 p n).
  { intros p n' Hp1 Hp2. apply (chkr_munch _ m m1 p n' (STKC p n' Hp1 ltac:(lia)) MU1).
    intros ?x ?Hx; cbn [outside]; unfold SHADOW_LO, SHADOW_HI in *; lia. }
  assert (IC1 : ictx m1) by (apply (ictx_munch _ m m1 IC MU1 WM1); intros ?x ?Hx; cbn [in_rl ICR outside] in *; lia).
  assert (FMTC1 : chkr m1 A (zlength fmt)) by tr_chk FMTC MU1.
  assert (ROD1 : rod_chk m1).
  { destruct ROD as (R1 & R2 & R3). split; [| split]; [tr_chk R1 MU1 | tr_chk R2 MU1 | tr_chk R3 MU1]. }
  assert (CHD1 : chkr m1 D (Z.of_nat dn)) by tr_chk CHD MU1.
  destruct SSP as (SSP1 & SSP2). unfold got_ssp, ssp_guard in SSP1, SSP2. unfold va_area in VAA.
  assert (LZB : length (zb fmt) = length fmt) by (unfold zb; apply length_map).
  pose proof (u64s_length slots) as LU. unfold zlength in *.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => transport_after_call asegs m mm MU1 WM1 end.
  clear CSA CHKA PA PCX PFC STKC IC FMTC ROD CHD AOK.
  eapply evt_cut.
  { eapply (vfprintf_sn_proof2 RIP) with (Fp := Fp) (CK := CK) (D := D) (n := n) (bufp := bufp) (A := A) (VA := VA) (dn := dn) (junkd := junkd)
      (fmt := fmt) (slots := slots) (args := args) (lo := lo) (canary := canary) (r := r) (d := d) (o := o) (cap := cap);
      rewrite ?EU48; unfold VF_FRAME, PC_DEPTH, GLOBALS_TOP, STATIC_SPLIT, kHighShadowEnd, zlength.
    all: first [ reflexivity | exact FH | exact FR | exact CKC | exact DST | exact BY | exact HF | exact P1 | exact VAA | exact AOK1
               | exact MODEL | exact FPF | exact ST1 | split; [exact SSP1 | exact SSP2] | exact MI1 | exact FRM | exact IC1
               | exact STK1 | exact FMTC1 | exact ROD1 | exact CHD1 | exact DSH | lia ]. }
  cbv beta. intros ms2 P. unfold vfprintf_sn_post2 in P. rewrite ?EU48 in P.
  destruct P as (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & Ft & fc' & fjunk & rest2 & m2 & -> & MU2 & WM2 & MI2 & FRM2
                 & FOK & ST2 & SSP' & DST2 & CK2 & FJ2).
  pose proof (rw_cells_transport asegs _ _ _ _ _ FRf MU2 WM2 ltac:(cbn [disjoint_from cells_size csize Nat.add]; lia)) as FRf2.
  replace (ret_pc (Z_to_bv 64 0x511dc)) with (Z_to_bv 64 0x511dc) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
  (* [comment removed for export] *)
  eapply evt_mono.
  { eapply (ivfsn_walkB q VA lo); [exact ST2 | lia | lia | exact FRf2 | exact MI2]. }
  cbv beta. intros ms3 ((v0 & v1 & v2 & c1 & c2 & c3 & c4 & c5 & c6 & c7 & v3 & v4 & v5 & v6 & ->) & ST3).
  unfold vfprintf_sn_post2. rewrite <- ESP.
  exists v0, v1, v2, c1, c2, c3, c4, c5, c6, c7, v3, v4, v5, v6, Ft, fc', fjunk, rest2, m2.
  split; [reflexivity|].
  split. { apply (munch_trans _ m m1 m2).
           - eapply munch_weaken; [| exact MU1]. unfold sub_fp; intros ?x ?Hx; cbn [outside] in *; lia.
           - eapply munch_weaken; [| exact MU2]. unfold sub_fp; intros ?x ?Hx; cbn [outside] in *; lia. }
  split; [exact (wmono_trans _ _ _ _ WM1 WM2)|]. split; [exact MI2|]. split; [exact FRM2|]. split; [exact FOK|].
  split; [exact ST3|]. split; [exact SSP'|]. split; [exact DST2|]. split; [exact CK2| exact FJ2].
Qed.

End WithRIP.
