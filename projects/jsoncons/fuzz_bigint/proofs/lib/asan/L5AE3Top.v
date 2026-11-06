(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.jsoncons.fuzz_bigint.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare ShapeAlg SpinAlg HeapIface HeapIfaceA IcptIfaceA LibIface
     AsanAcct AxSymExec3 AxSymExec3Sound AsanPlanCore SegRun BigLinkBase BigLinkGlue L5Defs L5Kn L5KnA L5Core L5LazyA L5DefsA
     L5CoreA L5CoreSpecsA L5StepA L5CoreB L5ParseSpecsA L5OpmodSpecsA L5DivSpecsA L5UnwindSpecsA XIcptA XIcptAs0Kit L5AUnwK L5AUnwK2 L5AE1K L5AE2K L5AE3K L5AE2PP L5AE2Pad L5AE3P1 L5AE3P2 L5AE3P3 L5AE3P4 L5AE3P5 L5AE3P6 L5AE3P7 L5AE3P8 L5AE3P9 L5AE3P10 L5AE3P11 L5AE3PP L5AE3Pad L5AUnwK3 L5AUnwK4 L5DivInnerSpecsA L5AOpdel L5AE3S2.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_bigint.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Set Printing Width 100000. Set Printing Depth 100000.

Module L5AE3Top.
Import L5A. Import L5CA. Import L5CSA. Import L5SA. Import L5CB. Import L5AUK. Import L5AUK2.
Import L5AE3P1.L5AE3P1. Import L5AE3P2.L5AE3P2. Import L5AE3P3.L5AE3P3. Import L5AE3P4.L5AE3P4. Import L5AE3P5.L5AE3P5. Import L5AE3P6.L5AE3P6. Import L5AE3P7.L5AE3P7. Import L5AE3P8.L5AE3P8. Import L5AE3P9.L5AE3P9. Import L5AE3P10.L5AE3P10. Import L5AE3P11.L5AE3P11. Import L5AE3PP.L5AE3PP. Import L5AUK3. Import L5AUK4.
Section SCFG_1.
Context {SCFG_P : ScfgP}.
Local Ltac inl := apply L5K.in_b; vm_compute; reflexivity.

Section WithIface.
Variables (L : asan_layout) (ar : asan_run) (C : asan_statics_cells) (IL : icpt_layout) (HI : asan_iface).
Hypothesis LY : as0_layout L C.
Hypothesis ILY : as0_icpt_layout IL.
Hypothesis HIok : asan_iface_ok L ar C SCFG HI.
Hypothesis ICok : aicpt_ok L ar IL SCFG HI.
Hypothesis HFILL : XIAS0.fill_spec.
Hypothesis HCOPY : XIAS0.copy_spec.
Hypothesis HTLS : XIAS0.tls_spec.
Hypothesis UNWL : L5USA.as0_unw_layout L.

(* [comment removed for export] *)
Local Notation CALIGN := (cinv_aligned L ar C HI LY HIok UNWL _ _ _ _ _ _ _ _ _ _ _ _ _ _).
Local Notation CMALLOC := (cinv_malloc L ar C HI LY HIok UNWL _ _ _ _ _ _ _ _ _ _ _ _ _ _).
Local Notation CSTRLEN := (cinv_strlen L ar C IL HI LY ILY HIok ICok UNWL _ _ _ _ _ _ _ _ _ _ _ _ _ _).
Local Notation CMEMCPY := (cinv_memcpy_at L ar C HI LY HIok UNWL _ _ _ _ _ _ _ _).
Local Notation CSTRERROR := (cinv_strerror L ar C IL HI LY ILY HIok ICok UNWL _ _ _ _ _ _ _ _ _ _ _ _ _ _).
Local Notation CHNR := (cinv_hnr L ar C HI LY HIok UNWL _ _ _ _ _ _ _ _ _ _ _ _ _ _).
(* [comment removed for export] *)
Local Ltac ffeed P CI F tac := feed P ltac:(idtac; lazymatch goal with |- context [F] => first [ asm | assumption | rk | gmem | tac | fd_mem CI ] | |- _ => first [ asm | fdp CI ] end).
(* [comment removed for export] *)
Local Ltac flia := idtac; lazymatch goal with NUM : numf _, FN : numg _ |- _ =>
  first [ solve [clear - NUM FN; unfold numf in NUM; unfold numg in FN; lia]
        | match goal with D : (_ \/ _) |- _ => solve [clear - NUM FN D; unfold numf in NUM; unfold numg in FN; lia] end ] end.
(* [comment removed for export] *)
Local Ltac padfeed P CI tac := feed P ltac:(idtac; first [ rk | asm | assumption | apply BL.bvu_range | apply L5AUK.U_to | apply L5AUK.UR | (unfold SB in *; gmem) | (arith_goal; tac) | fd_mem CI ]).
(* [comment removed for export] *)
Local Ltac sd_calld := idtac; lazymatch goal with |- ccl _ _ _ _ => ccl_tac | |- _ => first [ nlia | dlia ] end.
(* [comment removed for export] *)
Local Notation XW := [(6357456, 4); (6360113, 6)].
Local Notation XWIMG := (L5AE1K.xw2_img L UNWL).

Theorem e3_chainA_ok : L5USA.e3_chainA_spec_of L ar HI (L5DIA.assert_throw_atA L ar).
Proof.
  unfold L5USA.e3_chainA_spec_of.
  intros fx R0 M0 R M model K LBT LB1 FF LK LKt cr A Sp SCR xo FR st ZT LFR G1 G2 G3 G4 G9 S32 XSP HH AM HK LKI STK HSCR SCR8 SH CRF KONT.
  unfold L5USA.ASSERT_THROW, L5USA.TOP_PAD, L5USA.OM1_RET in *. unfold L5USA.CHAIN_SCR in HSCR. unfold L5USA.GP in G3.
  rewrite (proj2 (proj2 UNWL)) in G4. unfold L5USA.TPV in G4.
  unfold L5USA.EXC23_SZ, L5USA.MSG3_SZ, L5USA.REF3_SZ in CRF.
  destruct ZT as (F1a & fl1a & F3a & fl3a & F1b & fl1b & F3b & fl3b & F1c & fl1c & F1d & fl1d & d1 & d2 & d3 & d4 & qx & bo & LB0 & lenX & w9 & w10 & xs & fbx & fd0N & fn0N & fnN & fdenN & w1
                  & fd0 & fn0 & fn & fden & v0 & v1 & v2 & v3 & nd0 & nn0 & nn & nd & bq & EFR & ELBT & ELB1 & ATR & a1 & a2 & a3 & a4 & a5 & a6 & a7 & a8 & a9 & a10 & a11 & a12 & a13 & z1 & z2 & z3 & z4 & z5 & z6 & z7 & z8 & z9 & z10 & z11 & z12 & z13 & n1 & n2 & n3 & n4 & n5 & n6 & n7 & n8 & n9 & n10 & n11 & n12 & n13 & m1 & m2 & m3 & m4 & m5 & m6 & m7 & m8 & m9 & m10 & m11 & m12 & m13 & N780 & DEN0N & NUM0N & NUMN & NUMNT & DENN & DENNT & q1 & q2 & q3 & q4 & q5 & q6 & q7 & q8 & q9 & q10 & q11 & ZQ & u1 & u2 & u3 & MW & DOS & o1 & o2 & o3 & o4 & o5 & o6 & o7 & o8 & o9 & o10 & o11 & DEN0 & NUM0 & NUMO & DENO & OMF & BQ & BQD & BX & SHd & SHc & SH3b & SH1b & SH3a & SH1a & FRLd & FRLc & FRL3b & FRL1b & FRL3a & FRL1a).
  subst FR LBT. cbn [L5USA.ff_e3_of map fst] in HH.
  (* [comment removed for export] *)
  assert (FRA : forall j : nat, (j < 13)%nat -> L5.u64_at RSEGS M (Sp - 1192 + 8 * Z.of_nat j)
                  (nth j [F1d; nz (S (xo + 8)); nz (Z.of_nat lenX); SB; F1c; S F1c; nz (xo + 8); nz xo; 2 ^ 64 - 1; F1c; Sp - 1088; Sp - 960; L5DSA.RESERVE_RET] 0)).
  { apply u64_at_nz in a12, a11, a7, a6. intros j Hj. do 13 (destruct j as [|j]; [cbn [nth]; gmem|]). exfalso. clear - Hj. lia. }
  assert (FRZ : forall j : nat, (j < 13)%nat -> L5.u64_at RSEGS M (Sp - 1064 + 8 * Z.of_nat j)
                  (nth j [F1c; F3b + 48; nz w9; nz xo; F1b + 32; nz xo; SB; F3b + 96; F3b + 32; S F3b; Sp - 960; Sp - 608; L5DSA.RESIZE_RET_G] 0)).
  { apply u64_at_nz in z11, z10, z8. intros j Hj. do 13 (destruct j as [|j]; [cbn [nth]; gmem|]). exfalso. clear - Hj. lia. }
  assert (FRN : forall j : nat, (j < 13)%nat -> L5.u64_at RSEGS M (Sp - 712 + 8 * Z.of_nat j)
                  (nth j [F3a; nz w10; nz w9; L5DSA.RETIRE_MAGIC; F1b; S F1b; F1b + 32; Sp - 504; nz xo; F1b; Sp - 608; Sp - 512; L5DSA.DIV_RET_N] 0)).
  { apply u64_at_nz in n12, n11, n5. intros j Hj. do 13 (destruct j as [|j]; [cbn [nth]; gmem|]). exfalso. clear - Hj. lia. }
  assert (FRQ : forall j : nat, (j < 11)%nat -> L5.u64_at RSEGS M (Sp - 600 + 8 * Z.of_nat j)
                  (nth j [F1b; F3a; nz (S xo); F1a + 32; F3a + 96; F3a + 32; nz xo; S F3a; nz xs; nz xo; L5DSA.DIVEQ_RET] 0)).
  { apply u64_at_nz in q9, q5, q3, q2. intros j Hj. do 11 (destruct j as [|j]; [cbn [nth]; gmem|]). exfalso. clear - Hj. lia. }
  assert (FRU : forall j : nat, (j < 3)%nat -> L5.u64_at RSEGS M (Sp - 472 + 8 * Z.of_nat j) (nth j [Sp - 448; Sp - 96; L5DSA.UNNORM_RET] 0)).
  { intros j Hj. do 3 (destruct j as [|j]; [cbn [nth]; gmem|]). exfalso. clear - Hj. lia. }
  assert (FRD : forall j : nat, (j < 13)%nat -> L5.u64_at RSEGS M (Sp - 200 + 8 * Z.of_nat j)
                  (nth j [L5DSA.U R0 27; L5DSA.U R0 26; L5DSA.U R0 25; L5DSA.RETIRE_MAGIC; F1a; F1a / 8 + SB; F1a + 32; nz bo; nz xo; F1a; Sp - 96; Sp; L5DSA.DIV_RET_O] 0)).
  { destruct DOS as (D104 & D112 & D120 & D128 & D136 & D144 & D152 & D160 & D168 & D176 & D184 & D192 & D200).
    apply u64_at_nz in D136, D144. intros j Hj. do 13 (destruct j as [|j]; [cbn [nth]; gmem|]). exfalso. clear - Hj. lia. }
  assert (U01 : L5DSA.U R0 1 = 581760). { unfold L5DSA.U. change (Z_to_bv 5 1) with (reg 1). rewrite <- r1, G1. apply L5.unsigned_lit. clear; lia. }
  assert (U09 : L5DSA.U R0 9 = Sp). { unfold L5DSA.U. change (Z_to_bv 5 9) with (reg 9). rewrite <- L5AE1K.r9, G9. apply L5.unsigned_lit. pose proof STK as (_ & X1 & X2 & X3 & _). clear - X1 X2 X3 HSCR. lia. }
  assert (FRO : forall j : nat, (j < 11)%nat -> L5.u64_at RSEGS M (Sp - 88 + 8 * Z.of_nat j)
                  (nth j [F1a; L5DSA.U R0 24; L5DSA.U R0 23; L5DSA.U R0 22; L5DSA.U R0 21; L5DSA.U R0 20; L5DSA.U R0 19; L5DSA.U R0 18; Sp; L5DSA.U R0 8; 581760] 0)).
  { destruct OMF as (O8 & O16 & O24 & O32 & O40 & O48 & O56 & O64 & O72 & O80 & O88). rewrite U01 in O8. rewrite U09 in O24.
    intros j Hj. do 11 (destruct j as [|j]; [cbn [nth]; gmem|]). exfalso. clear - Hj. lia. }
  clear a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 z1 z2 z3 z4 z5 z6 z7 z8 z9 z10 z11 z12 z13 n1 n2 n3 n4 n5 n6 n7 n8 n9 n10 n11 n12 n13 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 u1 u2 u3 DOS OMF U01 U09.
  (* [comment removed for export] *)
  clear m1 m6 m7 m9 m10 m11 m12 m13 N780 o1 o6 o7 o9 o10 o11.
  destruct DEN0N as (DEN0Nf & DEN0Nr & _ & DEN0Nt & _). cbn [L5.bo_fb L5.bo_st] in DEN0Nf, DEN0Nr, DEN0Nt.
  destruct NUM0N as (NUM0Nf & NUM0Nr & _ & NUM0Nt & NUM0Nc & NUM0Np & _). cbn [L5.bo_fb L5.bo_st] in NUM0Nf, NUM0Nr, NUM0Nt, NUM0Nc, NUM0Np.
  destruct MW as ((MWf & _) & _). cbn [L5.bo_fb] in MWf.
  destruct DEN0 as (DEN0f & DEN0r & _ & DEN0t & _). cbn [L5.bo_fb L5.bo_st] in DEN0f, DEN0r, DEN0t.
  destruct NUM0 as (NUM0f & NUM0r & _ & NUM0t & _). cbn [L5.bo_fb L5.bo_st] in NUM0f, NUM0r, NUM0t.
  destruct ATR as (Z2 & Z3 & Z4 & Z10 & Z8 & Z9 & Z18 & Z19 & Z20 & Z21 & Z22 & Z23 & Z24 & Z25 & Z26 & Z27).
  rewrite G3 in Z3. rewrite G4 in Z4.
  rewrite r2 in Z2. rewrite L5AE1K.r3 in Z3. rewrite r4 in Z4. rewrite L5AE1K.r8 in Z8. rewrite L5AE1K.r9 in Z9.
  destruct st as [gd fl av uid rnd canary hw]. destruct XSP as (XST & AVS). cbn [L5USA.xs_gd L5USA.xs_fl L5USA.xs_av L5USA.xs_uid L5USA.xs_rnd L5USA.xs_canary L5USA.xs_hw] in XST, AVS.
  destruct XST as (EC0 & EU0 & GD & FLG & SCN).
  destruct SCN as (TDL & MSG0 & (errv & ERR & ERRR) & CAN & AUXP & AV8 & AVLO & AVHI & AUXV & UIDR & RNDR & CANR & HWR & IC1 & IC2 & IC3).
  unfold L5USA.EH_CAUGHT in EC0. unfold L5USA.EH_UNCAUGHT in EU0. unfold L5USA.TD_LOCALE, L5USA.GLOBAL_LOCALE in TDL. unfold L5USA.LOCALE_MSGCAT in MSG0.
  unfold L5USA.ERRNO in ERR. unfold L5USA.CANARY in CAN. unfold L5USA.AUXVP in AUXP. unfold L5USA.SYSCAT_OBJ in IC3.
  destruct GD as (GD0 & GD1). unfold L5USA.SYSCAT_GUARD in GD0, GD1. change (6358000 + 1) with 6358001 in GD1.
  assert (FLX : L5.u8_at RSEGS M 6360113 (if fl then 1 else 0) /\ L5.u8_at RSEGS M 6360115 (if fl then 1 else 0) /\ L5.u8_at RSEGS M 6360117 (if fl then 1 else 0)
                /\ (fl = true -> L5.u8_at RSEGS M 6360114 0) /\ (fl = true -> L5.u8_at RSEGS M 6360116 0) /\ (fl = true -> L5.u8_at RSEGS M 6360118 0)).
  { unfold L5USA.uw_flags, L5USA.UW_FLAGS in FLG. destruct fl.
    - destruct FLG as (X0 & X1 & X2 & X3 & X4 & X5). repeat split; first [assumption | intros _; assumption].
    - destruct FLG as (X0 & X2 & X4). repeat split; first [assumption | intros X; discriminate X]. }
  clear FLG. destruct FLX as (FL0 & FL2 & FL4 & FL1 & FL3 & FL5).
  pose proof STK as (A16 & SLO & SHI & SPT & DSCR & DUP).
  assert (HS0 : 0 <= SCR) by (clear - HSCR; lia).
  assert (ALS : (Sp - 1216) mod 16 = 0) by (apply mod16_sub; [exact A16 | reflexivity]).
  assert (ALS8 : (Sp - 1216) mod 8 = 0) by (apply mod8_of_16; exact ALS).
  assert (SPR : 0 <= Sp - 1216 < 2 ^ 64 /\ 140735332552704 <= Sp - 1216 /\ Sp - 1216 <= 140737488355264) by (clear - SLO SHI SPT HSCR AVS AVHI; lia).
  destruct SPR as (SPR0 & SPLO & SPHI).
  pose proof (as0_layout2_of L C LY) as LY2.
  assert (HTP : hl_tp L = 6360328) by (rewrite (proj2 (proj2 UNWL)); reflexivity).
  (* [comment removed for export] *)
  assert (FNUM : (6500352 <= ar_fs ar /\ ar_fs ar + 11571200 <= ahl_ceil ar
                  /\ ar_fs ar <= F1d /\ F1d + 128 <= ar_fs ar + 11571200 /\ ar_fs ar <= F1c /\ F1c + 128 <= ar_fs ar + 11571200 /\ ar_fs ar <= F3b /\ F3b + 512 <= ar_fs ar + 11571200
                  /\ ar_fs ar <= F1b /\ F1b + 128 <= ar_fs ar + 11571200 /\ ar_fs ar <= F3a /\ F3a + 512 <= ar_fs ar + 11571200 /\ ar_fs ar <= F1a /\ F1a + 128 <= ar_fs ar + 11571200
                  /\ 0 <= F1d / 8 <= 2 ^ 44 /\ 0 <= F1c / 8 <= 2 ^ 44 /\ 0 <= F3b / 8 <= 2 ^ 44 /\ 0 <= F1b / 8 <= 2 ^ 44 /\ 0 <= F3a / 8 <= 2 ^ 44 /\ 0 <= F1a / 8 <= 2 ^ 44)
                 /\ (F1d mod 128 = 0 /\ F1c mod 128 = 0 /\ F3b mod 512 = 0 /\ F1b mod 128 = 0 /\ F3a mod 512 = 0 /\ F1a mod 128 = 0)
                 /\ (ar_fs ar + 11571200 <= 2147446784 \/ 2147446784 + 17592186048512 <= ar_fs ar)).
  { pose proof (aio_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as (_ & WF & FSAPP & FSCEIL & FSIMG & _). unfold L5DSA.ff_e3 in WF.
    pose proof (WF _ ltac:(left; reflexivity)) as (Wd1 & Wd2 & Wd3 & _). pose proof (WF _ ltac:(right; left; reflexivity)) as (Wc1 & Wc2 & Wc3 & _).
    pose proof (WF _ ltac:(right; right; left; reflexivity)) as (Wn1 & Wn2 & Wn3 & _). pose proof (WF _ ltac:(right; right; right; left; reflexivity)) as (Wq1 & Wq2 & Wq3 & _).
    pose proof (WF _ ltac:(right; right; right; right; left; reflexivity)) as (Wo1 & Wo2 & Wo3 & _). pose proof (WF _ ltac:(right; right; right; right; right; left; reflexivity)) as (Wm1 & Wm2 & Wm3 & _).
    cbn [ff_addr ff_class fst snd] in *. change (ff_bytes 3) with 512 in *. change (ff_bytes 1) with 128 in *.
    rewrite (aly_img_lo L C LY), (aly_img_hi L C LY) in FSIMG. unfold app_mem, BIGSHADOW_LO, BIGSHADOW_HI in FSAPP. unfold FS_BYTES in *.
    assert (DV : forall F, ar_fs ar <= F -> F <= ar_fs ar + 11571200 -> 0 <= F / 8 <= 2 ^ 44).
    { intros F H1 H2. split. apply Z.div_pos; [clear - H1 FSAPP; lia | clear; lia]. apply Z.div_le_upper_bound; [clear; lia | clear - H2 FSAPP; lia]. }
    pose proof (DV F1d Wd1 ltac:(clear - Wd2; lia)). pose proof (DV F1c Wc1 ltac:(clear - Wc2; lia)). pose proof (DV F3b Wn1 ltac:(clear - Wn2; lia)).
    pose proof (DV F1b Wq1 ltac:(clear - Wq2; lia)). pose proof (DV F3a Wo1 ltac:(clear - Wo2; lia)). pose proof (DV F1a Wm1 ltac:(clear - Wm2; lia)). clear DV.
    split. clear - Wd1 Wd2 Wc1 Wc2 Wn1 Wn2 Wq1 Wq2 Wo1 Wo2 Wm1 Wm2 FSAPP FSCEIL FSIMG H H0 H1 H2 H3 H4. lia.
    split. repeat split; assumption. clear - FSAPP. lia. }
  destruct FNUM as (FN & FAL & DJF). change (numg (6500352 <= ar_fs ar /\ ar_fs ar + 11571200 <= ahl_ceil ar
                  /\ ar_fs ar <= F1d /\ F1d + 128 <= ar_fs ar + 11571200 /\ ar_fs ar <= F1c /\ F1c + 128 <= ar_fs ar + 11571200 /\ ar_fs ar <= F3b /\ F3b + 512 <= ar_fs ar + 11571200
                  /\ ar_fs ar <= F1b /\ F1b + 128 <= ar_fs ar + 11571200 /\ ar_fs ar <= F3a /\ F3a + 512 <= ar_fs ar + 11571200 /\ ar_fs ar <= F1a /\ F1a + 128 <= ar_fs ar + 11571200
                  /\ 0 <= F1d / 8 <= 2 ^ 44 /\ 0 <= F1c / 8 <= 2 ^ 44 /\ 0 <= F3b / 8 <= 2 ^ 44 /\ 0 <= F1b / 8 <= 2 ^ 44 /\ 0 <= F3a / 8 <= 2 ^ 44 /\ 0 <= F1a / 8 <= 2 ^ 44)) in FN.
  assert (NUM : numf ((ahl_ceil ar + 4096 + SCR <= Sp /\ Sp <= ar_sptop ar /\ 140735340871680 <= ar_sptop ar <= 2 ^ 47 /\ 69632 <= SCR /\ 0 <= SCR)
                      /\ (0 <= Sp - 1216 < 2 ^ 64 /\ 140735332552704 <= Sp - 1216 /\ Sp - 1216 <= 140737488355264)
                      /\ (ar_sptop ar <= av /\ 2 ^ 40 <= av /\ av + 160 <= 2 ^ 47))).
  { unfold numf. clear - SLO SHI SPT HSCR HS0 SPR0 SPLO SPHI AVS AVLO AVHI. lia. }
  (* [comment removed for export] *)
  pose proof (cinv_init L ar HI M model A LB1 (L5DSA.ff_e3 FF Sp F1a F3a F1b F3b F1c F1d) Sp SCR XW [(d1, 64); (d2, 64); (d3, 64); (d4, 64)] LKt cr HH AM STK SH) as CI0.
  unfold L5DSA.ff_e3 in CI0.
  pose proof (acc_init L ar M model A LB1 Sp SCR XW ((F1c, 1, Sp - 1056) :: (F3b, 3, Sp - 928) :: (F1b, 1, Sp - 576) :: (F3a, 3, Sp - 416) :: (F1a, 1, Sp - 64) :: FF)) as ACC0.
  clear DSCR DUP.
  (* [comment removed for export] *)
  assert (E8 : bv_unsigned (getr R (reg 8)) = Sp - 1216 + 128). { rewrite Z8. rewrite L5.unsigned_lit. clear; lia. clear - SPR0 SPHI; lia. }
  assert (E9 : bv_unsigned (getr R (reg 9)) = Sp - 1216). { rewrite Z9. apply L5.unsigned_lit. exact SPR0. }
  pose proof (ue3a1_conc HFILL HCOPY HTLS fx R (mrestrict (ahid A model) M) (fun j => match j with 2%nat => Sp - 1216 | _ => 0 end)) as P. cbn beta iota in P.
  rewrite ?E8, ?E9 in P.
  piece_step CI0 XWIMG P (fun a => Sp - 1216 - 112 <= a < Sp - 1216 - 112 + 112) fx1 R1 M1 model1 CI1.
  (* [comment removed for export] *)
  destruct (L5OMA.acredit_for_take L cr 3 (144 + 48 + 66) 144 LY2 CRF ltac:(clear; lia) ltac:(clear; lia)) as (ACR1 & CRF1). change (3 - 1) with 2 in CRF1. change (144 + 48 + 66 - 144) with (48 + 66) in CRF1.
  apply (CALIGN fx1 R1 144 (Sp - 1216 - 48) 723952 K CI1 HK HS0); [ rk | rk | clear; lia | reflexivity | exact ACR1 | rk | split; [clear; lia | reflexivity] | rk | rewrite HTP; rk
    | apply mod16_sub; [exact ALS | reflexivity] | clear - HSCR; lia | clear; lia | ].
  intros fx2 R2 M2 model2 A2 u mR10 RP2 CI2 AG.
  carry M1 M2 AG sd_call. clear AG.
  remember (u + 128) as obj eqn:EOBJ.
  assert (InO : In (u, 144) ([(u, 144); (d1, 64); (d2, 64); (d3, 64); (d4, 64)] ++ LB1)) by (left; reflexivity).
  pose proof (cv_blk L ar C HI LY HIok M model A LB1 _ Sp SCR XW _ _ _ _ _ _ CI2 u 144 InO) as (BRo & _ & _).
  pose proof (aio_small_high _ _ _ _ _ HIok _ _ _ _ _ _ _ (proj1 CI2) (u, 144) InO ltac:(cbn [snd]; clear; lia)) as HIGH. cbn [fst] in HIGH. unfold BIGSHADOW_HI in HIGH.
  assert (OB16 : obj mod 16 = 0) by (rewrite EOBJ; apply mod16_add; [exact (proj1 (proj2 (proj2 BRo))) | reflexivity]).
  assert (OB8 : obj mod 8 = 0) by (apply mod8_of_16; exact OB16).
  assert (OBR : 0 <= obj < 2 ^ 64 /\ 17594333495424 <= obj <= 140737479966720 /\ obj + 16 <= ahl_ceil ar) by (clear - BRo HIGH EOBJ SPT; lia).
  destruct OBR as (OBR0 & OBR & OCEIL).
  (* [comment removed for export] *)
  pose proof (aio_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ (proj1 CI2)) as (WB2 & _). destruct (WB2 (u, 144) InO) as (_ & _ & _ & _ & _ & _ & DJU). cbn [fst snd] in DJU. unfold FS_BYTES in DJU. clear WB2.
  clear BRo HIGH InO.
  assert (NUM2 : numf ((ahl_ceil ar + 4096 + SCR <= Sp /\ Sp <= ar_sptop ar /\ 140735340871680 <= ar_sptop ar <= 2 ^ 47 /\ 69632 <= SCR /\ 0 <= SCR)
                      /\ (0 <= Sp - 1216 < 2 ^ 64 /\ 140735332552704 <= Sp - 1216 /\ Sp - 1216 <= 140737488355264)
                      /\ (ar_sptop ar <= av /\ 2 ^ 40 <= av /\ av + 160 <= 2 ^ 47)
                      /\ (obj = u + 128 /\ 0 <= obj < 2 ^ 64 /\ 17594333495424 <= obj <= 140737479966720 /\ obj + 16 <= ahl_ceil ar))).
  { unfold numf in *. clear - NUM EOBJ OBR0 OBR OCEIL. lia. }
  clear NUM. rename NUM2 into NUM.
  assert (R2_10 : getr R2 (reg 10) = Z_to_bv 64 (obj - 128)) by (rewrite mR10; f_equal; clear - EOBJ; lia). clear mR10.
  (* [comment removed for export] *)
  assert (Hk1 : In 1 [1; 2; 3]) by (left; reflexivity).
  pose proof CI2 as (HH2 & _).
  pose proof (L5DSA.frl_cell _ _ _ _ _ _ _ _ _ FRLd) as FLCd0. pose proof (L5DSA.frl_fs _ _ _ _ _ _ _ _ _ FRLd) as FLPd.
  destruct (flagptr_now L ar C HI LY HIok _ _ _ _ _ _ _ _ _ _ _ _ _ model2 F1d 1 _ _ fl1d HH HH2 (or_introl eq_refl) (or_introl eq_refl) Hk1 FLCd0) as [FLCd2 _].
  unfold SB in Z22, Z23, Z26.
  assert (SHDd0 : L5.defined M (F1d / 8 + SB) (ff_bytes 1 / 8)).
  { change (ff_bytes 1 / 8) with 16. destruct SHd as (S1 & S2 & S3 & S4 & S5). intros i Hi.
    destruct (Z_lt_dec i 4) as [LT0|GE0]; [apply (shrun_def M F1d 0 4 _ i S1); clear - Hi LT0; lia|].
    destruct (Z_lt_dec i 7) as [LT1|GE1]; [apply (shrun_def M F1d 4 3 _ i S2); clear - Hi LT1 GE0; lia|].
    destruct (Z_lt_dec i 8) as [LT2|GE2]; [apply (shrun_def M F1d 7 1 _ i S3); clear - Hi LT2 GE1; lia|].
    destruct (Z_lt_dec i 12) as [LT3|GE3]; [apply (shrun_def M F1d 8 4 _ i S4); clear - Hi LT3 GE2; lia|].
    apply (shrun_def M F1d 12 4 _ i S5); clear - Hi GE3; lia. }
  pose proof (frame_shadow_defined L ar C HI LY HIok M model A LB1 _ Sp SCR XW F1d 1 (Sp - 1184) _ _ _ _ _ _ CI2 Hk1 SHDd0) as SHDd2.
  destruct (cv_frame L ar C HI LY HIok M model A LB1 _ Sp SCR XW F1d 1 (Sp - 1184) _ _ _ _ _ _ CI2 Hk1 fl1d FLCd2 FLPd SHDd2) as (FDEFv & FWv & FSHWv & _ & _ & _ & _).
  change (ff_bytes 1) with 128 in *. change (128 / 8) with 16 in *. unfold SB in FSHWv.
  assert (FDN : ar_fs ar <= F1d /\ F1d + 128 <= ar_fs ar + 11571200) by (unfold numg in FN; clear - FN; lia).
  assert (FDA : F1d mod 128 = 0) by exact (proj1 FAL).
  assert (AL_Fd : aligned F1d 64). { unfold aligned. Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true). clear - FDA. lia. }
  assert (SHAP : obj / 8 + 2147450864 + 18 <= F1d / 8 + 2147450880 \/ F1d / 8 + 2147450880 + 16 <= obj / 8 + 2147450864).
  { clear - FDN FDA DJU EOBJ OB16. lia. }
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
  pose proof (ue3a2_mh_conc HFILL HCOPY HTLS fx2 R2 (mrestrict (ahid A2 model2) M2) (fun j => match j with 2%nat => Sp - 1216 | 10%nat => obj | 40%nat => F1d | _ => 0 end)) as P. cbn beta iota in P.
  feed P ltac:(idtac; lazymatch goal with
               | |- context [F1d] => first [ asm | assumption | rk | gmem | (unfold numf in NUM; unfold numg in FN; clear - NUM FN DJF DJU; lia) ]
               | |- _ => fdp CI2 end).
  destruct P as (fx3 & R3 & Mv & MG & _ & FZ & (MS & EX)).
  apply (cinv_piece_rebase L ar C HI LY HIok M model A LB1 Sp SCR XW XWIMG _ M model A F1d 1 (Sp - 1184) _ [(u, 144); (d1, 64); (d2, 64); (d3, 64); (d4, 64)] M2 model2 LKt _ A2 _ fx3 _ _ R3 _ Mv
           (fun a => Sp - 1216 - 2736 <= a < Sp - 1216 - 2736 + 2704 \/ obj - 128 <= a < obj - 128 + 144 \/ F1d / 8 + 2147450884 <= a < F1d / 8 + 2147450884 + 3)
           K ACC0 (sufl_refl L ar LB1 _) CI2 HS0 Hk1 MS MG).
  { intros a Ha Hna. apply FZ; [exact Ha | cbv beta in Hna; clear - Hna; lia ..]. }
  { intros a Wa. cbv beta in Wa. destruct Wa as [Wa|[Wa|Wa]].
    - left. left. nlia.
    - left. right. left. exists (u, 144). split. in_tac. cbn [fst snd]. nlia.
    - right. right. unfold SB. change (ff_bytes 1 / 8) with 16. clear - Wa. lia. }
  intros M3 model3 ACC3 CI3 AH3 VIS3 MG3 FRM3. subst Mv. clear MS MG FZ.
  repeat (lazymatch type of EX with _ /\ _ => let X := fresh "EX" in destruct EX as [X EX] end).
  pose proof (rb_agree L ar C HI LY HIok M model A LB1 _ Sp SCR XW F1d 1 (Sp - 1184) _ _ _ _ _ _ CI2 Hk1 M3 _
                (fun a => Sp - 1216 - 2736 <= a < Sp - 1216 - 2736 + 2704 \/ obj - 128 <= a < obj - 128 + 144) FRM3) as AG.
  specialize (AG ltac:(intros a Wa; cbv beta in Wa; destruct Wa as [Wa|[Wa|Wa]]; [left; left; exact Wa | left; right; exact Wa | right; right; unfold SB; change (ff_bytes 1 / 8) with 16; clear - Wa; lia])).
  cbv beta in AG.
  (* [comment removed for export] *)
  assert (KSH : keep (L5.u8_at RSEGS M3 (F1d / 8 + 2147450884) 0 /\ L5.u8_at RSEGS M3 (F1d / 8 + 2147450885) 0 /\ L5.u8_at RSEGS M3 (F1d / 8 + 2147450886) 0)).
  { unfold keep. repeat split;
      (apply (cu_fsh_u8 L ar C HI LY HIok M3 model3 A2 LB1 _ Sp SCR XW F1d 1 (Sp - 1184) _ _ _ _ _ _ CI3 Hk1);
       [ unfold SB; clear; lia | unfold SB; change (ff_bytes 1 / 8) with 16; clear; lia | unfold numg in FN; clear - FN; lia | unfold numg in FN; clear - FN; lia | assumption ]). }
  lift_cells CI3.
  carry M2 M3 AG ltac:(idtac; lazymatch goal with |- L5AUK.cvis _ _ _ _ _ => cvis_tac [(u, 144); (d1, 64); (d2, 64); (d3, 64); (d4, 64)] | |- _ => sd_piece end).
  assert (SHDd3 : L5.defined M3 (F1d / 8 + SB) 16) by (eapply L5.defined_grows; [exact MG3 | exact SHDd2]).
  clear AG FRM3 FDEFv FWv FSHWv SHDd2 FLCd2 HH2 SHAP MG3.
  (* [comment removed for export] *)
  pose proof CI3 as (HH3 & _).
  destruct (flagptr_now L ar C HI LY HIok _ _ _ _ _ _ _ _ _ _ _ _ _ model3 F1d 1 _ _ fl1d HH HH3 (or_introl eq_refl) (or_introl eq_refl) Hk1 FLCd0) as [FLCd3 _].
  destruct (cv_frame L ar C HI LY HIok M3 model3 A2 LB1 _ Sp SCR XW F1d 1 (Sp - 1184) _ _ _ _ _ _ CI3 Hk1 fl1d FLCd3 FLPd SHDd3) as (FDEFv & FWv & FSHWv & _ & _ & _ & _).
  change (ff_bytes 1) with 128 in *. change (128 / 8) with 16 in *. unfold SB in FSHWv.
  pose proof (ue3s1_conc HFILL HCOPY HTLS fx3 R3 (mrestrict (ahid A2 model3) M3) (fun j => match j with 2%nat => Sp - 1216 | 10%nat => obj | 40%nat => F1d | _ => 0 end)) as P. cbn beta iota in P.
  ffeed P CI3 F1d ltac:(unfold numf in NUM; unfold numg in FN; clear - NUM FN DJF DJU; lia).
  piece_step CI3 XWIMG P (fun a => Sp - 1216 - 128 <= a < Sp - 1216 - 128 + 128) fx4 R4 M4 model4 CI4.
  assert (E3_8 : bv_unsigned (getr R3 (reg 8)) = Sp - 1216 + 128). { apply (U_of R3 8). rk. unfold numf in NUM; clear - NUM; lia. }
  assert (E3_9 : bv_unsigned (getr R3 (reg 9)) = Sp - 1216). { apply (U_of R3 9). rk. unfold numf in NUM; clear - NUM; lia. }
  assert (E3_18 : bv_unsigned (getr R3 (reg 18)) = F1d). { apply (U_of R3 18). rk. unfold numg in FN; clear - FN; lia. }
  assert (E3_20 : bv_unsigned (getr R3 (reg 20)) = F1d + 32). { apply (U_of R3 20). rk. unfold numg in FN; clear - FN; lia. }
  assert (E3_21 : bv_unsigned (getr R3 (reg 21)) = obj). { apply (U_of R3 21). rk. unfold numf in NUM; clear - NUM; lia. }
  rewrite E3_8, E3_9, E3_18, E3_20, E3_21 in *. clear E3_8 E3_9 E3_18 E3_20 E3_21.
  clear FDEFv FWv FSHWv FLCd3 HH3.
  tidy CI4.
  exact (L5AE3S2.e3_s2 L ar C IL HI LY ILY HIok ICok HFILL HCOPY HTLS UNWL R0 R M model K LB1 FF LK LKt cr A Sp SCR xo gd fl av uid rnd canary hw F1a fl1a F3a fl3a F1b fl1b F3b fl3b F1c fl1c F1d fl1d d1 d2 d3 d4 qx bo LB0 lenX w9 w10 xs fbx fd0N fn0N fnN fdenN w1 fd0 fn0 fn fden v0 v1 v2 v3 nd0 nn0 nn nd M3 M4 errv R1 R2 A2 u obj R3 model3 fx4 R4 model4 bq ELB1 Z2 Z3 Z4 Z10 Z8 Z9 Z18 Z19 Z20 Z21 Z22 Z23 Z24 Z25 Z26 Z27 m2 m3 m4 m5 m8 DEN0Nf DEN0Nr DEN0Nt NUM0Nf NUM0Nr NUM0Nt NUM0Nc NUM0Np NUMN NUMNT DENN DENNT ZQ MWf o2 o3 o4 o5 o8 DEN0f DEN0r DEN0t NUM0f NUM0r NUM0t NUMO DENO BQ BQD BX SHd SHc SH3b SH1b SH3a SH1a FRL1a FRL3a FRL1b FRL3b FRLc FRLd LFR G1 G2 G3 G4 G9 S32 EC0 EU0 GD0 GD1 TDL MSG0 ERR ERRR CAN AUXP AV8 AVLO AVHI UIDR RNDR CANR HWR AVS HH AM HK LKI STK HSCR SCR8 SH CRF KONT FL0 FL2 FL4 A16 SLO SHI SPT HS0 ALS ALS8 SPR0 SPLO SPHI LY2 HTP FN FAL DJF ACC0 E8 E9 EX0 EX1 EX2 EX3 EX4 ACR1 CRF1 RP2 EOBJ OB16 OB8 OBR0 OBR OCEIL DJU NUM R2_10 Hk1 FLCd0 FLPd SHDd0 FDN FDA AL_Fd EX10 EX11 EX12 EX13 EX14 EX15 EX16 EX17 EX21 ACC3 KSH SHDd3 EX5 EX6 EX18 EX19 EX20 EX22 EX23 EX24 EX25 EX26 EX27 EX28 EX29 EX30 EX CI4 FL1 FL3 FL5 AUXV FRA FRZ FRN FRQ FRU FRD FRO IC1 IC2 IC3).
Qed.

End WithIface.
End SCFG_1.
End L5AE3Top.
