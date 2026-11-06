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
     L5CoreA L5CoreSpecsA L5StepA L5CoreB L5ParseSpecsA L5OpmodSpecsA L5DivSpecsA L5UnwindSpecsA XIcptA XIcptAs0Kit L5AUnwK L5AUnwK2 L5AE1K L5AE2K L5AE2P1 L5AE2P2 L5AE2P3 L5AE2P4 L5AE2P5 L5AE2P6 L5AE2PP L5AUnwK3 L5AE2S2.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_bigint.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Set Printing Width 100000. Set Printing Depth 100000.

Module L5AE2Top.
Import L5A. Import L5CA. Import L5CSA. Import L5SA. Import L5CB. Import L5AUK. Import L5AUK2.
Import L5AE2P1.L5AE2P1. Import L5AE2P2.L5AE2P2. Import L5AE2P3.L5AE2P3. Import L5AE2P4.L5AE2P4. Import L5AE2P5.L5AE2P5. Import L5AE2P6.L5AE2P6. Import L5AE2PP.L5AE2PP. Import L5AUK3.
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
Local Notation XW := [(6357456, 4); (6360113, 6)].
Local Notation XWIMG := (L5AE1K.xw2_img L UNWL).

Theorem e2_chainA_ok : L5USA.e2_chainA_spec L ar HI.
Proof.
  unfold L5USA.e2_chainA_spec.
  intros fx R0 M0 R M model K LB FF LK LKt cr A Sp SCR xo bo F1 fl1 F3 fl3 st ZT G1 G2 G3 G4 G9 S32 XSP HH AM HK LKI STK HSCR SCR8 SH CRF KONT.
  unfold L5USA.ZERO_THROW, L5USA.TOP_PAD, L5USA.OM1_RET in *. unfold L5USA.CHAIN_SCR in HSCR. unfold L5USA.GP in G3.
  rewrite (proj2 (proj2 UNWL)) in G4. unfold L5USA.TPV in G4.
  unfold L5USA.EXC23_SZ, L5USA.REF2_SZ in CRF.
  destruct ZT as (fden & v16 & v24 & ZR & OMF & DOS & C392 & C376 & C288 & C360 & C352 & C336 & C296 & BIGQ & BIGD & SHS).
  destruct ZR as (Z2 & Z3 & Z4 & Z10 & Z8 & Z9 & Z18 & Z19 & Z20 & Z21 & Z22 & Z23 & Z24 & Z25 & Z26 & Z27).
  rewrite G3 in Z3. rewrite G4 in Z4.
  (* [comment removed for export] *)
  assert (FRD : forall j : nat, (j < 13)%nat -> L5.u64_at RSEGS M (Sp - 200 + 8 * Z.of_nat j)
                  (nth j [L5DSA.U R0 27; L5DSA.U R0 26; L5DSA.U R0 25; L5DSA.RETIRE_MAGIC; F1; F1 / 8 + SB; F1 + 32; nz bo; nz xo; F1; Sp - 96; Sp; L5DSA.DIV_RET_O] 0)).
  { destruct DOS as (D104 & D112 & D120 & D128 & D136 & D144 & D152 & D160 & D168 & D176 & D184 & D192 & D200).
    apply u64_at_nz in D136, D144. intros j Hj. do 13 (destruct j as [|j]; [cbn [nth]; gmem|]). exfalso. clear - Hj. lia. }
  assert (U01 : L5DSA.U R0 1 = 581760). { unfold L5DSA.U. change (Z_to_bv 5 1) with (reg 1). rewrite <- r1, G1. apply L5.unsigned_lit. clear; lia. }
  assert (U09 : L5DSA.U R0 9 = Sp). { unfold L5DSA.U. change (Z_to_bv 5 9) with (reg 9). rewrite <- L5AE1K.r9, G9. apply L5.unsigned_lit. pose proof STK as (_ & X1 & X2 & X3 & _). clear - X1 X2 X3 HSCR. unfold L5USA.CHAIN_SCR in HSCR. lia. }
  assert (FRO : forall j : nat, (j < 11)%nat -> L5.u64_at RSEGS M (Sp - 88 + 8 * Z.of_nat j)
                  (nth j [F1; L5DSA.U R0 24; L5DSA.U R0 23; L5DSA.U R0 22; L5DSA.U R0 21; L5DSA.U R0 20; L5DSA.U R0 19; L5DSA.U R0 18; Sp; L5DSA.U R0 8; 581760] 0)).
  { destruct OMF as (O8 & O16 & O24 & O32 & O40 & O48 & O56 & O64 & O72 & O80 & O88). rewrite U01 in O8. rewrite U09 in O24.
    intros j Hj. do 11 (destruct j as [|j]; [cbn [nth]; gmem|]). exfalso. clear - Hj. lia. }
  clear OMF DOS.
  rewrite r2 in Z2. rewrite L5AE1K.r3 in Z3. rewrite r4 in Z4. rewrite L5AE1K.r8 in Z8. rewrite L5AE1K.r9 in Z9.
  assert (E8 : bv_unsigned (getr R (reg 8)) = Sp - 448 + 352). { rewrite Z8. rewrite L5.unsigned_lit. clear; lia. pose proof STK as (_ & X1 & X2 & X3 & _). clear - X1 X2 X3 HSCR. unfold L5USA.CHAIN_SCR in HSCR. lia. }
  assert (E9 : bv_unsigned (getr R (reg 9)) = Sp - 448). { rewrite Z9. apply L5.unsigned_lit. pose proof STK as (_ & X1 & X2 & X3 & _). clear - X1 X2 X3 HSCR. unfold L5USA.CHAIN_SCR in HSCR. lia. }
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
  assert (ALS : (Sp - 448) mod 16 = 0) by (apply mod16_sub; [exact A16 | reflexivity]).
  assert (ALS8 : (Sp - 448) mod 8 = 0) by (apply mod8_of_16; exact ALS).
  assert (SPR : 0 <= Sp - 448 < 2 ^ 64 /\ 140735332552704 <= Sp - 448 /\ Sp - 448 <= 140737488355264) by (clear - SLO SHI SPT HSCR AVS AVHI; lia).
  destruct SPR as (SPR0 & SPLO & SPHI).
  pose proof (as0_layout2_of L C LY) as LY2.
  assert (HTP : hl_tp L = 6360328) by (rewrite (proj2 (proj2 UNWL)); reflexivity).
  (* [comment removed for export] *)
  destruct SHS as (SH1a & SH1b & SH1c & SH1d & SH3a & SH3b & SH3c & SH3d & SH3e & SH3f & SH3g & SH3h & SH3i & SH3j & SH3k & SH3l & SH3m & SH3n & FRL3 & FRL1 & AHP0).
  assert (FNUM : (ar_fs ar <= F3 /\ F3 + 512 <= ar_fs ar + 11571200 /\ ar_fs ar <= F1 /\ F1 + 128 <= ar_fs ar + 11571200 /\ ar_fs ar <= fl1 < ar_fs ar + 11571200 /\ ar_fs ar <= fl3 < ar_fs ar + 11571200
                  /\ 6500352 <= ar_fs ar /\ ar_fs ar + 11571200 <= ahl_ceil ar /\ 0 <= F1 / 8 <= 2 ^ 44 /\ 0 <= F3 / 8 <= 2 ^ 44)
                 /\ (F3 mod 512 = 0 /\ F1 mod 128 = 0) /\ (ar_fs ar + 11571200 <= 2147446784 \/ 2147446784 + 17592186048512 <= ar_fs ar)).
  { pose proof (aio_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as (_ & WF & FSAPP & FSCEIL & FSIMG & _).
    pose proof (WF (F3, 3, Sp - 416) ltac:(left; reflexivity)) as (W31 & W32 & W33 & _). pose proof (WF (F1, 1, Sp - 64) ltac:(right; left; reflexivity)) as (W11 & W12 & W13 & _).
    cbn [ff_addr ff_class fst snd] in W31, W32, W33, W11, W12, W13. change (ff_bytes 3) with 512 in *. change (ff_bytes 1) with 128 in *.
    rewrite (aly_img_lo L C LY), (aly_img_hi L C LY) in FSIMG. unfold app_mem, BIGSHADOW_LO, BIGSHADOW_HI in FSAPP. unfold FS_BYTES in *.
    pose proof (L5DSA.frl_fs _ _ _ _ _ _ _ _ _ FRL3) as X3. pose proof (L5DSA.frl_fs _ _ _ _ _ _ _ _ _ FRL1) as X1. unfold FS_BYTES in X1, X3.
    assert (D1 : 0 <= F1 / 8 <= 2 ^ 44). { split. apply Z.div_pos; [clear - W11 FSAPP; lia | clear; lia]. apply Z.div_le_upper_bound; [clear; lia | clear - W12 FSAPP; lia]. }
    assert (D3 : 0 <= F3 / 8 <= 2 ^ 44). { split. apply Z.div_pos; [clear - W31 FSAPP; lia | clear; lia]. apply Z.div_le_upper_bound; [clear; lia | clear - W32 FSAPP; lia]. }
    split. clear - W31 W32 W11 W12 X1 X3 FSAPP FSCEIL FSIMG D1 D3. lia. split. split. exact W33. exact W13. clear - FSAPP. lia. }
  destruct FNUM as (FN & (F3A & F1A) & DJF). change (numg (ar_fs ar <= F3 /\ F3 + 512 <= ar_fs ar + 11571200 /\ ar_fs ar <= F1 /\ F1 + 128 <= ar_fs ar + 11571200 /\ ar_fs ar <= fl1 < ar_fs ar + 11571200 /\ ar_fs ar <= fl3 < ar_fs ar + 11571200
                  /\ 6500352 <= ar_fs ar /\ ar_fs ar + 11571200 <= ahl_ceil ar /\ 0 <= F1 / 8 <= 2 ^ 44 /\ 0 <= F3 / 8 <= 2 ^ 44)) in FN.
  assert (NUM : numf ((ahl_ceil ar + 4096 + SCR <= Sp /\ Sp <= ar_sptop ar /\ 140735340871680 <= ar_sptop ar <= 2 ^ 47 /\ 69632 <= SCR /\ 0 <= SCR)
                      /\ (0 <= Sp - 448 < 2 ^ 64 /\ 140735332552704 <= Sp - 448 /\ Sp - 448 <= 140737488355264)
                      /\ (ar_sptop ar <= av /\ 2 ^ 40 <= av /\ av + 160 <= 2 ^ 47))).
  { unfold numf. clear - SLO SHI SPT HSCR HS0 SPR0 SPLO SPHI AVS AVLO AVHI. lia. }
  (* [comment removed for export] *)
  pose proof (cinv_init L ar HI M model A LB (L5DSA.ff_e2 FF Sp F1 F3) Sp SCR XW [] LKt cr HH AM STK SH) as CI0.
  clear DSCR DUP.
  (* [comment removed for export] *)
  pose proof (ue2a1_conc HFILL HCOPY HTLS fx R (mrestrict (ahid A model) M) (fun j => match j with 2%nat => Sp - 448 | _ => 0 end)) as P. cbn beta iota in P.
  rewrite ?E8, ?E9 in P.
  piece_step CI0 XWIMG P (fun a => Sp - 448 - 112 <= a < Sp - 448 - 112 + 112) fx1 R1 M1 model1 CI1.
  (* [comment removed for export] *)
  destruct (L5OMA.acredit_for_take L cr 2 (144 + 37) 144 LY2 CRF ltac:(clear; lia) ltac:(clear; lia)) as (ACR1 & CRF1). change (2 - 1) with 1 in CRF1. change (144 + 37 - 144) with 37 in CRF1.
  apply (CALIGN fx1 R1 144 (Sp - 448 - 48) 723952 K CI1 HK HS0); [ rk | rk | clear; lia | reflexivity | exact ACR1 | rk | split; [clear; lia | reflexivity] | rk | rewrite HTP; rk
    | apply mod16_sub; [exact ALS | reflexivity] | clear - HSCR; lia | clear; lia | ].
  intros fx2 R2 M2 model2 A2 u mR10 RP2 CI2 AG.
  carry M1 M2 AG sd_call. clear AG.
  (* [comment removed for export] *)
  remember (u + 128) as obj eqn:EOBJ.
  assert (InO : In (u, 144) ([(u, 144)] ++ LB)) by (left; reflexivity).
  pose proof (cv_blk L ar C HI LY HIok M model A LB (L5DSA.ff_e2 FF Sp F1 F3) Sp SCR XW _ _ _ _ _ _ CI2 u 144 InO) as (BRo & _ & _).
  pose proof (aio_small_high _ _ _ _ _ HIok _ _ _ _ _ _ _ (proj1 CI2) (u, 144) InO ltac:(cbn [snd]; clear; lia)) as HIGH. cbn [fst] in HIGH. unfold BIGSHADOW_HI in HIGH.
  assert (OB16 : obj mod 16 = 0) by (rewrite EOBJ; apply mod16_add; [exact (proj1 (proj2 (proj2 BRo))) | reflexivity]).
  assert (OB8 : obj mod 8 = 0) by (apply mod8_of_16; exact OB16).
  assert (OBR : 0 <= obj < 2 ^ 64 /\ 17594333495424 <= obj <= 140737479966720 /\ obj + 16 <= ahl_ceil ar) by (clear - BRo HIGH EOBJ SPT; lia).
  destruct OBR as (OBR0 & OBR & OCEIL). clear BRo HIGH InO.
  assert (NUM2 : numf ((ahl_ceil ar + 4096 + SCR <= Sp /\ Sp <= ar_sptop ar /\ 140735340871680 <= ar_sptop ar <= 2 ^ 47 /\ 69632 <= SCR /\ 0 <= SCR)
                      /\ (0 <= Sp - 448 < 2 ^ 64 /\ 140735332552704 <= Sp - 448 /\ Sp - 448 <= 140737488355264)
                      /\ (ar_sptop ar <= av /\ 2 ^ 40 <= av /\ av + 160 <= 2 ^ 47)
                      /\ (obj = u + 128 /\ 0 <= obj < 2 ^ 64 /\ 17594333495424 <= obj <= 140737479966720 /\ obj + 16 <= ahl_ceil ar))).
  { unfold numf in *. clear - NUM EOBJ OBR0 OBR OCEIL. lia. }
  clear NUM. rename NUM2 into NUM.
  assert (R2_10 : getr R2 (reg 10) = Z_to_bv 64 (obj - 128)) by (rewrite mR10; f_equal; clear - EOBJ; lia). clear mR10.
  (* [comment removed for export] *)
  pose proof (ue2a2_mh_conc HFILL HCOPY HTLS fx2 R2 (mrestrict (ahid A2 model2) M2) (fun j => match j with 2%nat => Sp - 448 | 10%nat => obj | _ => 0 end)) as P. cbn beta iota in P.
  piece_step CI2 XWIMG P (fun a => Sp - 448 - 2736 <= a < Sp - 448 - 2736 + 2704 \/ obj - 128 <= a < obj - 128 + 144) fx3 R3 M3 model3 CI3.
  clear R2_10.
  (* [comment removed for export] *)
  match goal with H : L5KA.zeros_at M3 (obj - 128) 144 |- _ => pose proof (L5KA.zeros_at_sub M3 (obj - 128) 144 (obj - 72) 4 H ltac:(clear; lia) ltac:(clear; lia)) as Z72 end.
  (* [comment removed for export] *)
  assert (E10 : bv_unsigned (getr R3 (reg 10)) = obj). { apply (U_of R3 10). rk. unfold numf in NUM; clear - NUM; lia. }
  pose proof (ue2c1_conc HFILL HCOPY HTLS fx3 R3 (mrestrict (ahid A2 model3) M3) (fun j => match j with 2%nat => Sp - 448 | _ => 0 end)) as P. cbn beta iota in P.
  rewrite ?E10 in P.
  piece_step CI3 XWIMG P (fun a => Sp - 448 - 112 <= a < Sp - 448 - 112 + 112 \/ obj + 0 <= a < obj + 0 + 8) fx4 R4 M4 model4 CI4.
  assert (E3_8 : bv_unsigned (getr R3 (reg 8)) = Sp - 448 + 352). { apply (U_of R3 8). rk. unfold numf in NUM; clear - NUM; lia. }
  assert (E3_9 : bv_unsigned (getr R3 (reg 9)) = Sp - 448). { apply (U_of R3 9). rk. unfold numf in NUM; clear - NUM; lia. }
  assert (E3_19 : bv_unsigned (getr R3 (reg 19)) = obj). { apply (U_of R3 19). rk. unfold numf in NUM; clear - NUM; lia. }
  assert (E3_18 : bv_unsigned (getr R3 (reg 18)) = F3 / 8 + SB). { apply (U_of R3 18). rk. unfold SB; unfold numg in FN; clear - FN; lia. }
  rewrite E3_8, E3_9, E3_19, E3_18 in *. clear E3_8 E3_9 E3_19 E3_18.
  assert (R4_8 : getr R4 (reg 8) = Z_to_bv 64 obj) by (match goal with H : getr R4 (reg 8) = getr R3 (reg 10) |- _ => rewrite H end; rk).
  (* [comment removed for export] *)
  pose proof (cinv_num L ar HI M model A LB (L5DSA.ff_e2 FF Sp F1 F3) Sp SCR XW _ _ _ _ _ _ CI4) as (_ & SLO4 & SHI4 & SPT4).
  apply (CSTRLEN fx4 R4 142208 12 L5AE2K.zd_buf (Sp - 448 - 48) 728508 K CI4 HK HS0);
    [ rk | rk | split; [clear; lia | reflexivity] | rk | rewrite HTP; rk | apply mod16_sub; [exact ALS | reflexivity] | clear - HSCR; lia | clear; lia
    | clear; lia | change (Z.of_nat (length L5AE2K.zd_buf)) with 16; clear; lia | clear; lia
    | exact (L5AE2K.zd_rdn M4 IC1)
    | change (Z.of_nat (length L5AE2K.zd_buf)) with 16; reflexivity | reflexivity | | right; left; change (Z.of_nat (length L5AE2K.zd_buf)) with 16; clear; lia | exact IC1
    | apply (asrc_aacc L ar C IL HI ILY HIok ICok _ _ _ _ _ M4 _ 142208 13 (proj1 CI4)); right; right; left; exists 0x22b80, 13; split; [rewrite (aicl_globals IL ILY); in_tac | clear; lia]
    | apply app_rng_img; [clear - SPT4; lia | clear; lia | clear; lia] | ].
  { intros j Hj. change (Z.to_nat 12) with 12%nat in Hj. do 12 (destruct j as [|j]; [intros E; apply (f_equal bv_unsigned) in E; vm_compute in E; discriminate E|]). exfalso. clear - Hj. lia. }
  intros fx5 R5 M5 model5 sR5 RP5 CI5 AG.
  carry M4 M5 AG sd_call. clear AG SLO4 SHI4 SPT4.
  (* [comment removed for export] *)
  pose proof (ue2c2_conc HFILL HCOPY HTLS fx5 R5 (mrestrict (ahid A2 model5) M5) (fun j => match j with 2%nat => Sp - 448 | 10%nat => obj | _ => 0 end)) as P. cbn beta iota in P.
  piece_step CI5 XWIMG P (fun a => Sp - 448 - 128 <= a < Sp - 448 - 128 + 80) fx6 R6 M6 model6 CI6.
  destruct (L5OMA.acredit_for_take L (adebit L cr 144) 1 37 37 LY2 CRF1 ltac:(clear; lia) ltac:(clear; lia)) as (ACR2 & _).
  apply (CMALLOC fx6 R6 37 (Sp - 448 - 64) 856060 K CI6 HK HS0); [ rk | clear; lia | exact ACR2 | rk | split; [clear; lia | reflexivity] | rk | rewrite HTP; rk
    | apply mod16_sub; [exact ALS | reflexivity] | clear - HSCR; lia | clear; lia | ].
  intros fx7 R7 M7 model7 A7 ref mR7 RP7 CI7 AG.
  carry M6 M7 AG sd_call. clear AG.
  (* [comment removed for export] *)
  assert (InR : In (ref, 37) ([(ref, 37); (u, 144)] ++ LB)) by (left; reflexivity).
  pose proof (cv_blk L ar C HI LY HIok M model A LB (L5DSA.ff_e2 FF Sp F1 F3) Sp SCR XW _ _ _ _ _ _ CI7 ref 37 InR) as (BRr & _ & _).
  pose proof (aio_small_high _ _ _ _ _ HIok _ _ _ _ _ _ _ (proj1 CI7) (ref, 37) InR ltac:(cbn [snd]; clear; lia)) as HIGHr. cbn [fst] in HIGHr. unfold BIGSHADOW_HI in HIGHr.
  assert (APRT : ref + 37 <= u \/ u + 144 <= ref).
  { pose proof (aio_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ (proj1 CI7)) as (WB & _). destruct (WB (ref, 37) InR) as (_ & _ & _ & _ & BA & _). cbn [fst snd] in BA.
    cbn [app lb_remove fst] in BA. rewrite Z.eqb_refl in BA. specialize (BA (u, 144) ltac:(left; reflexivity)). cbn [fst snd] in BA. clear - BA; lia. }
  assert (RF16 : ref mod 16 = 0) by exact (proj1 (proj2 (proj2 BRr))).
  assert (NUM3 : numf ((ahl_ceil ar + 4096 + SCR <= Sp /\ Sp <= ar_sptop ar /\ 140735340871680 <= ar_sptop ar <= 2 ^ 47 /\ 69632 <= SCR /\ 0 <= SCR)
                      /\ (0 <= Sp - 448 < 2 ^ 64 /\ 140735332552704 <= Sp - 448 /\ Sp - 448 <= 140737488355264)
                      /\ (ar_sptop ar <= av /\ 2 ^ 40 <= av /\ av + 160 <= 2 ^ 47)
                      /\ (obj = u + 128 /\ 0 <= obj < 2 ^ 64 /\ 17594333495424 <= obj <= 140737479966720 /\ obj + 16 <= ahl_ceil ar)
                      /\ (17594333495296 <= ref /\ ref + 37 <= ahl_ceil ar /\ (ref + 37 <= u \/ u + 144 <= ref)))).
  { unfold numf in *. clear - NUM BRr HIGHr APRT. lia. }
  clear NUM. rename NUM3 into NUM. clear BRr HIGHr APRT InR.
  (* [comment removed for export] *)
  pose proof (ue2c3_conc HFILL HCOPY HTLS fx7 R7 (mrestrict (ahid A7 model7) M7) (fun j => match j with 2%nat => Sp - 448 | 10%nat => obj | 37%nat => ref | _ => 0 end)) as P. cbn beta iota in P.
  piece_step CI7 XWIMG P (fun a => Sp - 448 - 128 <= a < Sp - 448 - 128 + 64 \/ ref + 0 <= a < ref + 0 + 20) fx8 R8 M8 model8 CI8.
  apply (L5AE2S2.e2_s2 L ar C IL HI LY ILY HIok ICok HFILL HCOPY HTLS UNWL fx R0 M0 R M model K LB FF LK LKt cr A Sp SCR xo bo F1 fl1 F3 fl3 gd fl av uid rnd canary hw fden v16 v24 M1 M2 M3 M4 M5 M6 M7 M8 errv fx1 R1 model1 fx2 R2 model2 A2 u obj fx3 R3 model3 fx4 R4 model4 fx5 R5 model5 fx6 R6 model6 fx7 R7 model7 A7 ref fx8 R8 model8); assumption.
Qed.

End WithIface.
End SCFG_1.
End L5AE2Top.
