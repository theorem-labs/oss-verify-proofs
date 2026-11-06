(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.jsoncons.fuzz_bigint.images Require Import AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare ShapeAlg SpinAlg HeapIface HeapIfaceA IcptIfaceAB0 LibIface
     AsanAcct AxSymExec3 AxSymExec3Sound AsanPlanCore SegRun BigLinkBase BigLinkGlue L5Defs L5Kn L5KnA L5Core L5LazyA L5DefsAB0
     L5CoreAB0 L5CoreSpecsAB0 L5StepAB0 L5CoreBB0 L5ParseSpecsAB0 L5OpmodSpecsAB0 L5DivSpecsAB0 L5UnwindSpecsAB0 XIcptAB0 XIcptAs0KitB0 L5BUnwK L5BUnwK2 L5BE1K L5BE1P1 L5BE1P2 L5BE1P3 L5BE1P4 L5BE1P5 L5BE1S2.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_bigint.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Set Printing Width 100000. Set Printing Depth 100000.

Module L5BE1Top.
Import L5A. Import L5CA. Import L5CSA. Import L5SA. Import L5CB. Import L5AUK. Import L5AUK2.
Import L5BE1P1.L5BE1P1. Import L5BE1P2.L5BE1P2. Import L5BE1P3.L5BE1P3. Import L5BE1P4.L5BE1P4. Import L5BE1P5.L5BE1P5.
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
Local Notation XW := [(6360528, 4); (6363185, 6); (6361072, 8); (6363236, 4)].
Local Notation XWIMG := (L5BE1K.xw_img L UNWL).

Theorem e1_chainA_ok : L5USA.e1_chainA_spec L ar HI IL.
Proof.
  unfold L5USA.e1_chainA_spec.
  intros fx R M model K LB FF LK cr A Sp SCR s0v s2v st G2 G3 G4 G9 G18 S32 C8 C16 C24 C32 S0R S2R XSP HH AM HK STK HSCR SCR8 SH CRF KONT.
  unfold L5USA.STRCTOR_THROW, L5USA.E1_LANDING, L5USA.E1_RET in *. unfold L5USA.CHAIN_SCR in HSCR. unfold L5USA.GP in G3.
  rewrite (proj2 (proj2 UNWL)) in G4. unfold L5USA.TPV in G4.
  rewrite r2 in G2. rewrite L5BE1K.r3 in G3. rewrite r4 in G4. rewrite L5BE1K.r9 in G9. rewrite L5BE1K.r18 in G18.
  unfold L5USA.EXC1_SZ, L5USA.REF1_SZ in CRF.
  destruct st as [gd fl av uid rnd canary hw]. destruct XSP as (XST & AVS). cbn [L5USA.xs_gd L5USA.xs_fl L5USA.xs_av L5USA.xs_uid L5USA.xs_rnd L5USA.xs_canary L5USA.xs_hw] in XST, AVS.
  destruct XST as (EC0 & EU0 & GD & FLG & SCN).
  destruct SCN as (TDL & MSG0 & (errv & ERR & ERRR) & CAN & AUXP & AV8 & AVLO & AVHI & AUXV & UIDR & RNDR & CANR & HWR & IC1 & IC2 & IC3).
  unfold L5USA.EH_CAUGHT in EC0. unfold L5USA.EH_UNCAUGHT in EU0. unfold L5USA.TD_LOCALE, L5USA.GLOBAL_LOCALE in TDL. unfold L5USA.LOCALE_MSGCAT in MSG0.
  unfold L5USA.ERRNO in ERR. unfold L5USA.CANARY in CAN. unfold L5USA.AUXVP in AUXP. unfold L5USA.SYSCAT_OBJ in IC3.
  (* [comment removed for export] *)
  destruct GD as (GD0 & GD1). unfold L5USA.SYSCAT_GUARD in GD0, GD1. change (6361072 + 1) with 6361073 in GD1.
  assert (FLX : L5.u8_at RSEGS M 6363185 (if fl then 1 else 0) /\ L5.u8_at RSEGS M 6363187 (if fl then 1 else 0) /\ L5.u8_at RSEGS M 6363189 (if fl then 1 else 0)
                /\ (fl = true -> L5.u8_at RSEGS M 6363186 0) /\ (fl = true -> L5.u8_at RSEGS M 6363188 0) /\ (fl = true -> L5.u8_at RSEGS M 6363190 0)).
  { unfold L5USA.uw_flags, L5USA.UW_FLAGS in FLG. destruct fl.
    - destruct FLG as (F0 & F1 & F2 & F3 & F4 & F5). repeat split; first [assumption | intros _; assumption].
    - destruct FLG as (F0 & F2 & F4). repeat split; first [assumption | intros X; discriminate X]. }
  clear FLG. destruct FLX as (FL0 & FL2 & FL4 & FL1 & FL3 & FL5).
  pose proof STK as (A16 & SLO & SHI & SPT & DSCR & DUP).
  assert (HS0 : 0 <= SCR) by (clear - HSCR; lia).
  assert (ALS : (Sp - 32) mod 16 = 0) by (apply mod16_sub; [exact A16 | reflexivity]).
  assert (ALS8 : (Sp - 32) mod 8 = 0) by (apply mod8_of_16; exact ALS).
  assert (SPR : 0 <= Sp - 32 < 2 ^ 64 /\ 140735332552704 <= Sp - 32 /\ Sp - 32 <= 140737488355264) by (clear - SLO SHI SPT HSCR AVS AVHI; lia).
  destruct SPR as (SPR0 & SPLO & SPHI).
  pose proof (as0_layout2_of L C LY) as LY2.
  assert (HTP : hl_tp L = 6363400) by (rewrite (proj2 (proj2 UNWL)); reflexivity).
  assert (E9 : bv_unsigned (getr R (reg 9)) = 22). { rewrite G9. apply L5.unsigned_lit. clear; lia. }
  assert (NUM : numf ((ahl_ceil ar + 4096 + SCR <= Sp /\ Sp <= ar_sptop ar /\ 140735340871680 <= ar_sptop ar <= 2 ^ 47 /\ 69632 <= SCR /\ 0 <= SCR)
                      /\ (0 <= Sp - 32 < 2 ^ 64 /\ 140735332552704 <= Sp - 32 /\ Sp - 32 <= 140737488355264)
                      /\ (ar_sptop ar <= av /\ 2 ^ 40 <= av /\ av + 160 <= 2 ^ 47))).
  { unfold numf. clear - SLO SHI SPT HSCR HS0 SPR0 SPLO SPHI AVS AVLO AVHI. lia. }
  (* [comment removed for export] *)
  pose proof (cinv_init L ar HI M model A LB FF Sp SCR XW [] LK cr HH AM STK SH) as CI0.
  clear DSCR DUP.
  (* [comment removed for export] *)
  pose proof (ue1a1_conc HFILL HCOPY HTLS fx R (mrestrict (ahid A model) M) (fun j => match j with 2%nat => Sp - 32 | 40%nat => U R 10 | _ => 0 end)) as P. cbn beta iota in P.
  rewrite ?E9 in P.
  piece_step CI0 XWIMG P (fun a => Sp - 32 - 112 <= a < Sp - 32 - 112 + 112) fx1 R1 M1 model1 CI1.
  (* [comment removed for export] *)
  destruct (L5OMA.acredit_for_take L cr 2 (160 + 41) 160 LY2 CRF ltac:(clear; lia) ltac:(clear; lia)) as (ACR1 & CRF1). change (2 - 1) with 1 in CRF1. change (160 + 41 - 160) with 41 in CRF1.
  apply (CALIGN fx1 R1 160 (Sp - 32 - 48) 727044 K CI1 HK HS0); [ rk | rk | clear; lia | reflexivity | exact ACR1 | rk | split; [clear; lia | reflexivity] | rk | rewrite HTP; rk
    | apply mod16_sub; [exact ALS | reflexivity] | clear - HSCR; lia | clear; lia | ].
  intros fx2 R2 M2 model2 A2 u mR10 RP2 CI2 AG.
  carry M1 M2 AG sd_call. clear AG.
  (* [comment removed for export] *)
  remember (u + 128) as obj eqn:EOBJ.
  assert (InO : In (u, 160) ([(u, 160)] ++ LB)) by (left; reflexivity).
  pose proof (cv_blk L ar C HI LY HIok M model A LB FF Sp SCR XW _ _ _ _ _ _ CI2 u 160 InO) as (BRo & _ & _).
  pose proof (aio_small_high _ _ _ _ _ HIok _ _ _ _ _ _ _ (proj1 CI2) (u, 160) InO ltac:(cbn [snd]; clear; lia)) as HIGH. cbn [fst] in HIGH. unfold BIGSHADOW_HI in HIGH.
  assert (OB16 : obj mod 16 = 0) by (rewrite EOBJ; apply mod16_add; [exact (proj1 (proj2 (proj2 BRo))) | reflexivity]).
  assert (OB8 : obj mod 8 = 0) by (apply mod8_of_16; exact OB16).
  assert (OBR : 0 <= obj < 2 ^ 64 /\ 17594333495424 <= obj <= 140737479966720 /\ obj + 32 <= ahl_ceil ar) by (clear - BRo HIGH EOBJ SPT; lia).
  destruct OBR as (OBR0 & OBR & OCEIL). clear BRo HIGH InO.
  assert (NUM2 : numf ((ahl_ceil ar + 4096 + SCR <= Sp /\ Sp <= ar_sptop ar /\ 140735340871680 <= ar_sptop ar <= 2 ^ 47 /\ 69632 <= SCR /\ 0 <= SCR)
                      /\ (0 <= Sp - 32 < 2 ^ 64 /\ 140735332552704 <= Sp - 32 /\ Sp - 32 <= 140737488355264)
                      /\ (ar_sptop ar <= av /\ 2 ^ 40 <= av /\ av + 160 <= 2 ^ 47)
                      /\ (obj = u + 128 /\ 0 <= obj < 2 ^ 64 /\ 17594333495424 <= obj <= 140737479966720 /\ obj + 32 <= ahl_ceil ar))).
  { unfold numf in *. clear - NUM EOBJ OBR0 OBR OCEIL. lia. }
  clear NUM. rename NUM2 into NUM.
  assert (R2_10 : getr R2 (reg 10) = Z_to_bv 64 (obj - 128)) by (rewrite mR10; f_equal; clear - EOBJ; lia). clear mR10.
  (* [comment removed for export] *)
  pose proof (ue1a2_mh_conc HFILL HCOPY HTLS fx2 R2 (mrestrict (ahid A2 model2) M2) (fun j => match j with 2%nat => Sp - 32 | 10%nat => obj | 40%nat => U R 8 | _ => 0 end)) as P. cbn beta iota in P.
  piece_step CI2 XWIMG P (fun a => Sp - 32 - 2736 <= a < Sp - 32 - 2736 + 2704 \/ obj - 128 <= a < obj - 128 + 160) fx3 R3 M3 model3 CI3.
  clear R2_10.
  (* [comment removed for export] *)
  match goal with H : L5KA.zeros_at M3 (obj - 128) 160 |- _ => pose proof (L5KA.zeros_at_sub M3 (obj - 128) 160 (obj - 72) 4 H ltac:(clear; lia) ltac:(clear; lia)) as Z72 end.
  (* [comment removed for export] *)
  destruct gd; cbv iota in GD0, GD1.
  - pose proof (ue1g1_g1_conc HFILL HCOPY HTLS fx3 R3 (mrestrict (ahid A2 model3) M3) (fun j => match j with 2%nat => Sp - 32 | 10%nat => obj | 40%nat => U R3 10 | _ => 0 end)) as P. cbn beta iota in P.
    piece_step CI3 XWIMG P (fun a => Sp - 32 - 80 <= a < Sp - 32 - 80 + 80 \/ 6361072 <= a < 6361072 + 1 \/ 6361073 <= a < 6361073 + 1) fx4 R4 M4 model4 CI4.
    norm_ks R4 R3 KS4.
    apply (L5BE1S2.e1_s2 L ar C IL HI LY ILY HIok ICok HFILL HCOPY HTLS UNWL fx R M model K LB FF LK cr A Sp SCR s0v s2v true fl av uid rnd canary hw M1 M2 M3 M4 errv fx1 R1 model1 fx2 R2 model2 A2 u obj fx3 R3 model3 fx4 R4 model4); assumption.
  - pose proof (ue1g1_g0_conc HFILL HCOPY HTLS fx3 R3 (mrestrict (ahid A2 model3) M3) (fun j => match j with 2%nat => Sp - 32 | 10%nat => obj | 40%nat => U R3 10 | _ => 0 end)) as P. cbn beta iota in P.
    piece_step CI3 XWIMG P (fun a => Sp - 32 - 80 <= a < Sp - 32 - 80 + 80 \/ 6361072 <= a < 6361072 + 1 \/ 6361073 <= a < 6361073 + 1) fx4 R4 M4 model4 CI4.
    norm_ks R4 R3 KS4.
    apply (L5BE1S2.e1_s2 L ar C IL HI LY ILY HIok ICok HFILL HCOPY HTLS UNWL fx R M model K LB FF LK cr A Sp SCR s0v s2v false fl av uid rnd canary hw M1 M2 M3 M4 errv fx1 R1 model1 fx2 R2 model2 A2 u obj fx3 R3 model3 fx4 R4 model4); assumption.
Qed.

End WithIface.
End SCFG_1.
End L5BE1Top.
