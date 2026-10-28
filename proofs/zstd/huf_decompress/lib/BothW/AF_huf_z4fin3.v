(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith NArith List Lia Bool.

From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Spec Require Import FseNCount FuzzProducer HufPure_FseDecomp HufPure_HufX1 HufPure_HufX2.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Lib Require Import Tac Arr Bytes ZBridge Walk RunConst Image.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import DrvAgree FseWalkKit HufWalkKit2 HufWalkKit3.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require KXTac KXGoM.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Spec Require Import STree AsanCtrl AsanEmbed.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.LibA Require Import ExecF Shadow StepF.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.BothW Require Import BImg RtCells AProto ABase AMalloc_iface AProg_kit AHarness_iface.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.BothW Require Import AH_huf_iface AF_huf_dec_iface AF_huf_z4m AF_huf_z4f_defs AF_huf_z4kx AF_huf_z4kx2 AF_huf_z4fin AF_huf_z4fin2.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Startup_kit.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import RunDraw.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import FseWalkKitF.
Import ListNotations.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Notation zlen l := (Z.of_nat (length l)).

Section CANSEC1. Context {rc : runConstT}.
Section Z4FIN.
  Variable AI : AMallocIface.
  Notation CI := (aci AI).
  Variables (L : alayout) (RNG : footprint) (st : astate) (LB : list ablock).
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (FR : bvmap 5 word) (fc : bv 32) (m0 : amem).
  Variables (DST dcap SS DT mtl lo : Z) (src : list Z) (cbs : list byte) (pdt pb : aptr) (SBL SBH : Z) (cells : list deltX2).
  Notation SP := (bv_unsigned sp).
  Notation SPF := (SP + -528).
  Notation n := (zlen src).
  Notation seg := ((dcap + 3) / 4).
  Notation DTL := (DTABLE_BYTES mtl).
  Hypothesis AH : AHEAP AI L RNG st LB m0.
  Hypothesis HDT : In (HB pdt DT DTL) LB.
  Hypothesis HDB : In (HB pb DST dcap) LB.
  Hypothesis LOA : ATOP + 4096 <= lo.
  Hypothesis LOS : lo <= SP - HUF_DEC_STACK_A.
  Hypothesis SPT : SP + 16 < al_top L.
  Hypothesis SP16 : SP mod 16 = 0.
  Hypothesis TOK : x2_table_ok cells 11.
  Hypothesis ECB : cbs = firstn (Z.to_nat (4 * 2^11)) (x2_bytes' cells).
  Hypothesis LCB : zlen cbs = 8192.
  Hypothesis MTL : 11 <= mtl <= 12.
  Hypothesis DC : 0 < dcap < 2^32.
  Hypothesis SG : 3 * seg < dcap.
  Hypothesis NSM : 10 <= n < 2^26.
  Hypothesis SBB : SBL <= SS /\ SS + n <= SBH.
  Hypothesis SBA : ablk SBL SBH /\ SBL mod 8 = 0.
  Hypothesis BYS : Forall (fun c => 0 <= c < 256) src.
  Hypothesis DJ1 : KXGoM.apart DST dcap DT DTL.
  Hypothesis DJ2 : KXGoM.apart DST dcap SS n.
  Hypothesis UDT : unpoisoned m0 DT (DT + DTL).
  Hypothesis UDB : unpoisoned m0 DST (DST + dcap).
  Hypothesis USB : unpoisoned m0 SBL SBH.
  Hypothesis WSK : rng RNG lo (al_top L - lo).
  Hypothesis WIM : rng_aimg RNG.
  Hypothesis WDT : rng RNG DT DTL.
  Hypothesis WDB : rng RNG DST dcap.
  Hypothesis WSB : rng RNG SBL (SBH - SBL).
  Hypothesis WDTS : rng RNG (shad DT) (shlen (DTL + 7)).
  Hypothesis WDBS : rng RNG (shad DST) (shlen (dcap + 7)).
  Hypothesis WSBS : rng RNG (shad SBL) (shlen (SBH - SBL + 7)).

  Notation DW := [(lo, SP); (DST, DST + dcap)].
  Notation POST := (huf_dec_postA AI L RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc st LB DST dcap lo m0).
  Notation Z4M := (AF_huf_z4m.Z4M ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m0 DST dcap SS DT lo src cbs).
  Notation FRS := [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

  
  Notation KH pc mm k prev x1 x8 x9 x11 x12 x13 x18 x19 x20 x21 x22 x23 x24 x26 x28 x31 :=
    (MS (mkR x1 (Z_to_bv 64 SPF) gp tp (Z_to_bv 64 k) (Z_to_bv 64 seg) (Z_to_bv 64 64) x8 x9 (Z_to_bv 64 prev)
             x11 x12 x13 (Z_to_bv 64 (SP + -136)) (Z_to_bv 64 (SP + -256)) (Z_to_bv 64 AZ4_DBC) (Z_to_bv 64 8)
             x18 x19 x20 x21 x22 x23 x24 (Z_to_bv 64 0x20d84) x26 (Z_to_bv 64 2147450880) x28 (Z_to_bv 64 2) (Z_to_bv 64 4) x31)
        FR (Z_to_bv 64 pc) fc None mm (seg_rom bsegs)).


  Notation ZF l := (l AI L RNG st LB ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m0 DST dcap SS DT mtl lo src cbs pdt pb
                      SBL SBH cells AH HDT HDB LOA LOS SPT SP16 TOK ECB LCB MTL DC SG NSM SBB SBA BYS DJ1 DJ2 UDT UDB USB
                      WSK WIM WDT WDB WSB WDTS WDBS WSBS).

  Section STREAM.
  Variables (k SE OPk : Z) (w136 : word) (ws : list word).
  Hypothesis K4 : 0 <= k < 4.
  Hypothesis HSE : DST <= OPk <= SE.
  Hypothesis HSE2 : SE <= DST + dcap.
  Hypothesis WOP : nth_error ws (Z.to_nat (4 + k)) = Some (Z_to_bv 64 OPk).
  Notation Z4Mk mm := (Z4M mm w136 ws).

  
  Notation STA pc mm x1 x5 x6 x9 a0 a1 a2 a3 x21 x22 x24 x25 x27 x30 :=
    (MS (mkR x1 (Z_to_bv 64 SPF) gp tp x5 x6 (Z_to_bv 64 65) (Z_to_bv 64 (DT + 4)) x9 a0 a1 a2 a3
             (Z_to_bv 64 k) (Z_to_bv 64 (SPF + 264)) (Z_to_bv 64 (2^64 - 1 - (DT + 4))) (Z_to_bv 64 9)
             (Z_to_bv 64 (SPF + 176 + 8 * k)) (Z_to_bv 64 OPk) (Z_to_bv 64 SE) x21 x22 (Z_to_bv 64 0x7fff8000) x24 x25
             (Z_to_bv 64 0x20d53) x27 (Z_to_bv 64 2) (Z_to_bv 64 seg) x30 (Z_to_bv 64 64))
        FR (Z_to_bv 64 pc) fc None mm (seg_rom bsegs)).

  
  Hypothesis CONT : forall mm (x1 x5 x6 x9 a0 a1 a2 a3 x21 x22 x24 x25 x27 x30 : word),
    Z4M mm w136 (upd ws (Z.to_nat (4 + k)) (Z_to_bv 64 SE)) ->
    evtF bsegs RNG POST (STA 0x875d0 mm x1 x5 x6 x9 a0 a1 a2 a3 x21 x22 x24 x25 x27 x30).

  Notation ZS l := (ZF l k SE OPk w136 ws K4 HSE HSE2 WOP CONT).

  
  Lemma z4_st5 : forall (b : bool) flag, flag = 0 \/ flag = 1 -> Z.land (Z.b2z b) flag = if b then flag else 0.
Proof.
  intros b flag Hf. destruct b; destruct Hf as [-> | ->]; reflexivity.
Qed.

  
  Lemma z4f_join5 : forall p pt nb bits flag mm (x1 x5 x6 x9 x30 : word),
    Z4Mk mm -> OPk <= p <= SE -> 0 <= nb <= pt -> pt + 8 <= n -> 0 <= bits <= 64 ->
    (flag = 0 \/ (flag = 1 /\ bits <= 7)) ->
    (forall p' pt' bits' mm' (x1' x5' x6' x9' a1' a3' x30' : word),
       Z4Mk mm' -> p < p' <= SE -> 0 <= pt' -> pt' + 8 <= n -> 0 <= bits' <= 64 ->
       evtF bsegs RNG POST (STA 0x86c7c mm' x1' x5' x6' x9' (Z_to_bv 64 (SS + pt')) a1' (Z_to_bv 64 p') a3'
                                (Z_to_bv 64 SS) (Z_to_bv 64 (SS + 8)) (Z_to_bv 64 (SE - 9)) (Z_to_bv 64 SE) (Z_to_bv 64 bits') x30')) ->
    evtF bsegs RNG POST (STA 0x86cc8 mm x1 x5 x6 x9 (Z_to_bv 64 (SS + pt)) (Z_to_bv 64 flag) (Z_to_bv 64 p) (Z_to_bv 64 nb)
                             (Z_to_bv 64 SS) (Z_to_bv 64 (SS + 8)) (Z_to_bv 64 (SE - 9)) (Z_to_bv 64 SE) (Z_to_bv 64 bits) x30).
Proof using All.
  intros p pt nb bits flag mm x1 x5 x6 x9 x30 HZ HP HNB HPT HB HF K.
  pose proof (ZF z4f_frame_facts) as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8).
  pose proof (ZF z4f_blocks) as (BK1 & BK2 & BK3 & BK4 & BK5 & BK6 & BK7 & BK8 & BK9).
  assert (DP : 1 <= DST) by (unfold ablk, ABase.AIMG_HI, ABase.KLS in *; lia).
  pose proof (ZF z4f_ctx mm w136 ws HZ) as CTX.
  assert (R1 : rw_cells bsegs mm (SPF + 128) [C8 (Z_to_bv 64 (DT + 4))]) by (eapply z4f_slot112; exact HZ).
  zstep.
  assert (SSP : 1 <= SS) by (destruct SBB; unfold ablk, ABase.AIMG_HI, ABase.KLS in *; lia).
  assert (LA : Z.land (SS + pt) 18446744073709551615 = SS + pt).
  { change 18446744073709551615 with (Z.ones 64). rewrite Z.land_ones by lia. apply Z.mod_small. lia. }
  rewrite LA. replace (SS + pt - nb) with (SS + (pt - nb)) by lia.
  eapply (AF_huf_z4kx2.z4_R5 POST RNG mm FR fc); [exact CTX | lia | lia |].
  intros ra' s0' s1' a3' t1' t5'.
  do 6 zstep.
  rewrite z4_st5 by (destruct HF as [-> | (-> & _)]; [left | right]; reflexivity).
  change (Z_to_bv 64 (18446744073709551615 - (DT + 4))) with (Z_to_bv 64 (2^64 - 1 - (DT + 4))).
  assert (EX : (p <? SE - 9) = false \/ flag = 0 \/ ((p <? SE - 9) = true /\ flag = 1 /\ bits <= 7)).
  { destruct (p <? SE - 9); [destruct HF as [-> | (-> & BL)]; [right; left | right; right] | left]; auto. }
  destruct EX as [LT | [F0 | (GE & FL1 & BL)]].
  - rewrite LT. z4f_br.
    replace (SPF + 128) with (SP + -400) in R1 by lia. do 3 zstep.
    rewrite bv_ltu_Z, !Z_to_bv_unsigned. unfold bv_wrap, bv_modulus; change (Z.of_N 64) with 64.
    rewrite (Z.mod_small (SE - p)) by lia. rewrite (Z.mod_small 2) by lia.
    destruct (Z.ltb_spec (SE - p) 2) as [L2 | L2]; cbn [negb].
    + zstep.
      replace (SP + -264) with (SPF + 264) by lia. replace (SP + -352 + 8 * k) with (SPF + 176 + 8 * k) by lia.
      change (Z_to_bv 64 (18446744073709551615 - (DT + 4))) with (Z_to_bv 64 (2^64 - 1 - (DT + 4))).
      eapply (ZS z4f_last); [exact HZ | lia].
    + replace (SP + -264) with (SPF + 264) by lia. replace (SP + -352 + 8 * k) with (SPF + 176 + 8 * k) by lia.
      change (Z_to_bv 64 (18446744073709551615 - (DT + 4))) with (Z_to_bv 64 (2^64 - 1 - (DT + 4))).
      eapply (ZS z4f_ph2); [exact HZ | lia | intros _; exists (pt - nb); repeat split; lia].
  - subst flag. destruct (p <? SE - 9); z4f_br.
    + idtac.
      replace (SPF + 128) with (SP + -400) in R1 by lia. do 3 zstep.
      rewrite bv_ltu_Z, !Z_to_bv_unsigned. unfold bv_wrap, bv_modulus; change (Z.of_N 64) with 64.
      rewrite (Z.mod_small (SE - p)) by lia. rewrite (Z.mod_small 2) by lia.
      destruct (Z.ltb_spec (SE - p) 2) as [L2 | L2]; cbn [negb].
      * zstep.
        replace (SP + -264) with (SPF + 264) by lia. replace (SP + -352 + 8 * k) with (SPF + 176 + 8 * k) by lia.
        change (Z_to_bv 64 (18446744073709551615 - (DT + 4))) with (Z_to_bv 64 (2^64 - 1 - (DT + 4))).
        eapply (ZS z4f_last); [exact HZ | lia].
      * replace (SP + -264) with (SPF + 264) by lia. replace (SP + -352 + 8 * k) with (SPF + 176 + 8 * k) by lia.
        change (Z_to_bv 64 (18446744073709551615 - (DT + 4))) with (Z_to_bv 64 (2^64 - 1 - (DT + 4))).
        eapply (ZS z4f_ph2); [exact HZ | lia | intros _; exists (pt - nb); repeat split; lia].
    + idtac.
      replace (SPF + 128) with (SP + -400) in R1 by lia. do 3 zstep.
      rewrite bv_ltu_Z, !Z_to_bv_unsigned. unfold bv_wrap, bv_modulus; change (Z.of_N 64) with 64.
      rewrite (Z.mod_small (SE - p)) by lia. rewrite (Z.mod_small 2) by lia.
      destruct (Z.ltb_spec (SE - p) 2) as [L2 | L2]; cbn [negb].
      * zstep.
        replace (SP + -264) with (SPF + 264) by lia. replace (SP + -352 + 8 * k) with (SPF + 176 + 8 * k) by lia.
        change (Z_to_bv 64 (18446744073709551615 - (DT + 4))) with (Z_to_bv 64 (2^64 - 1 - (DT + 4))).
        eapply (ZS z4f_last); [exact HZ | lia].
      * replace (SP + -264) with (SPF + 264) by lia. replace (SP + -352 + 8 * k) with (SPF + 176 + 8 * k) by lia.
        change (Z_to_bv 64 (18446744073709551615 - (DT + 4))) with (Z_to_bv 64 (2^64 - 1 - (DT + 4))).
        eapply (ZS z4f_ph2); [exact HZ | lia | intros _; exists (pt - nb); repeat split; lia].
  - subst flag. rewrite GE. apply Z.ltb_lt in GE. z4f_br.
    eapply (AF_huf_z4kx.z4_D5 POST RNG mm FR fc); [exact CTX | lia | lia | lia |].
    intros mm' a1' a3'' s1'' t1'' t5'' nbs d MU' WM' MI' OB' NBS D.
    assert (HZ' : Z4Mk mm') by (eapply (ZF z4m_step_dst); eauto).
    zstep.
    rewrite bv_ltu_Z, !Z_to_bv_unsigned. unfold bv_wrap, bv_modulus; change (Z.of_N 64) with 64.
    rewrite (Z.mod_small (bits + nbs)) by lia. rewrite (Z.mod_small 65) by lia.
    rewrite (proj2 (Z.ltb_lt _ _)) by lia.
    replace (SP + -264) with (SPF + 264) by lia. replace (SP + -352 + 8 * k) with (SPF + 176 + 8 * k) by lia.
    change (Z_to_bv 64 (18446744073709551615 - (DT + 4))) with (Z_to_bv 64 (2^64 - 1 - (DT + 4))).
    apply (K (p + d) (pt - nb) (bits + nbs) mm'); [exact HZ' | lia | lia | lia | lia].
Qed.

  
  Lemma z4f_loop5 : forall (fuel : nat) p pt bits mm (x1 x5 x6 x9 a1 a3 x30 : word),
    Z4Mk mm -> OPk <= p <= SE -> SE - p < Z.of_nat fuel ->
    0 <= pt -> pt + 8 <= n -> 0 <= bits <= 64 ->
    evtF bsegs RNG POST (STA 0x86c7c mm x1 x5 x6 x9 (Z_to_bv 64 (SS + pt)) a1 (Z_to_bv 64 p) a3
                             (Z_to_bv 64 SS) (Z_to_bv 64 (SS + 8)) (Z_to_bv 64 (SE - 9)) (Z_to_bv 64 SE) (Z_to_bv 64 bits) x30).
Proof using All.
  intros fuel; induction fuel as [|fuel IH]; intros p pt bits mm x1 x5 x6 x9 a1 a3 x30 HZ HP HF HPT0 HPT HB; [lia|].
  pose proof (ZF z4f_frame_facts) as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8).
  pose proof (ZF z4f_blocks) as (BK1 & BK2 & BK3 & BK4 & BK5 & BK6 & BK7 & BK8 & BK9).
  assert (DP : 1 <= DST) by (unfold ablk, ABase.AIMG_HI, ABase.KLS in *; lia).
  assert (SSP : 1 <= SS) by (destruct SBB; unfold ablk, ABase.AIMG_HI, ABase.KLS in *; lia).
  assert (JK : forall p' pt' bits' mm' (x1' x5' x6' x9' a1' a3' x30' : word),
       Z4Mk mm' -> p < p' <= SE -> 0 <= pt' -> pt' + 8 <= n -> 0 <= bits' <= 64 ->
       evtF bsegs RNG POST (STA 0x86c7c mm' x1' x5' x6' x9' (Z_to_bv 64 (SS + pt')) a1' (Z_to_bv 64 p') a3'
                                (Z_to_bv 64 SS) (Z_to_bv 64 (SS + 8)) (Z_to_bv 64 (SE - 9)) (Z_to_bv 64 SE) (Z_to_bv 64 bits') x30')).
  { intros. eapply IH; eauto; lia. }
  destruct (Z_le_gt_dec 8 pt) as [P8 | P8].
  - assert (SW : bv_swrap 32 (Z.shiftr (bv_wrap 32 bits) 3) = bits / 8).
    { unfold bv_wrap, bv_modulus. change (Z.of_N 32) with 32. rewrite (Z.mod_small bits) by lia.
      rewrite Z.shiftr_div_pow2 by lia. change (2^3) with 8.
      unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus. change (Z.of_N 32) with 32.
      rewrite Z.mod_small by (split; [apply Z.add_nonneg_nonneg; [apply Z.div_pos|]|]; lia). lia. }
    zstep. z4f_br. zstep. rewrite SW.
    assert (B8 : 0 <= bits / 8 <= 8) by (split; [apply Z.div_pos | apply Z.div_le_upper_bound]; lia).
    zstep.
    rewrite bv_ltu_Z, !Z_to_bv_unsigned. unfold bv_wrap, bv_modulus; change (Z.of_N 64) with 64.
    rewrite (Z.mod_small (bits / 8)) by lia. rewrite (Z.mod_small (SS + pt)) by lia.
    rewrite (proj2 (Z.ltb_lt _ _)) by lia. cbn [negb].
    do 2 zstep.
    rewrite z4_land7 by lia.
    replace (SP + -264) with (SPF + 264) by lia. replace (SP + -352 + 8 * k) with (SPF + 176 + 8 * k) by lia.
    change (Z_to_bv 64 (18446744073709551615 - (DT + 4))) with (Z_to_bv 64 (2^64 - 1 - (DT + 4))).
    apply (z4f_join5 p pt (bits / 8) (bits mod 8) 1 mm); [exact HZ | lia | lia | lia | lia
      | right; split; [reflexivity | pose proof (Z.mod_pos_bound bits 8); lia] | exact JK].
  - destruct (Z.eq_dec pt 0) as [P0 | P0].
    + subst pt. zstep. z4f_br. zstep. z4f_br. zstep. zstep.
      rewrite bv_ltu_Z, !Z_to_bv_unsigned. unfold bv_wrap, bv_modulus; change (Z.of_N 64) with 64.
      rewrite (Z.mod_small (SE - p)) by lia. rewrite (Z.mod_small 2) by lia.
      destruct (Z.ltb_spec (SE - p) 2) as [L2 | L2]; cbn [negb].
      * replace (SP + -264) with (SPF + 264) by lia. replace (SP + -352 + 8 * k) with (SPF + 176 + 8 * k) by lia.
        change (Z_to_bv 64 (18446744073709551615 - (DT + 4))) with (Z_to_bv 64 (2^64 - 1 - (DT + 4))).
        eapply (ZS z4f_last); [exact HZ | lia].
      * replace (SP + -264) with (SPF + 264) by lia. replace (SP + -352 + 8 * k) with (SPF + 176 + 8 * k) by lia.
        change (Z_to_bv 64 (18446744073709551615 - (DT + 4))) with (Z_to_bv 64 (2^64 - 1 - (DT + 4))).
        eapply (ZS z4f_ph2); [exact HZ | lia | intros _; exists 0; repeat split; try (f_equal; lia); lia].
    + assert (SW : bv_swrap 32 (Z.shiftr (bv_wrap 32 bits) 3) = bits / 8).
      { unfold bv_wrap, bv_modulus. change (Z.of_N 32) with 32. rewrite (Z.mod_small bits) by lia.
        rewrite Z.shiftr_div_pow2 by lia. change (2^3) with 8.
        unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus. change (Z.of_N 32) with 32.
        rewrite Z.mod_small by (split; [apply Z.add_nonneg_nonneg; [apply Z.div_pos|]|]; lia). lia. }
      assert (B8 : 0 <= bits / 8 <= 8) by (split; [apply Z.div_pos | apply Z.div_le_upper_bound]; lia).
      zstep. z4f_br. zstep. z4f_br. zstep. rewrite SW.
      zstep.
      rewrite bv_ltu_Z, !Z_to_bv_unsigned. unfold bv_wrap, bv_modulus; change (Z.of_N 64) with 64.
      rewrite (Z.mod_small (bits / 8)) by lia. rewrite (Z.mod_small (SS + pt)) by lia.
      rewrite (proj2 (Z.ltb_lt _ _)) by (destruct SBB; unfold ablk, ABase.AIMG_HI, ABase.KLS in *; lia). cbn [negb].
      zstep.
      assert (SS8 : 8 <= SS) by (destruct SBB; unfold ablk, ABase.AIMG_HI, ABase.KLS in *; lia).
      destruct (Z_le_gt_dec (bits / 8) pt) as [NA | NB].
      * zstep.
        rewrite bv_ltu_Z, !Z_to_bv_unsigned. unfold bv_wrap, bv_modulus; change (Z.of_N 64) with 64.
        rewrite (Z.mod_small (SS + pt - bits / 8)) by lia. rewrite (Z.mod_small SS) by lia.
        rewrite (proj2 (Z.ltb_ge _ _)) by lia. cbn [negb].
        do 3 zstep.
        rewrite z4_land32 by lia.
        rewrite bv_ltu_Z, !Z_to_bv_unsigned. unfold bv_wrap, bv_modulus; change (Z.of_N 64) with 64.
        rewrite (Z.mod_small (bits / 8)) by lia. rewrite (Z.mod_small (SS + pt)) by lia.
        rewrite (proj2 (Z.ltb_lt _ _)) by lia. cbn [negb].
        do 4 zstep.
        rewrite (proj2 (Z.ltb_ge _ _)) by lia. change (Z.lxor (Z.b2z false) 1) with 1.
        rewrite Z.shiftl_mul_pow2 by lia. change (2^3) with 8.
        assert (L64 : Z.land (bits / 8 * 8) 18446744073709551615 = bits / 8 * 8)
          by (change 18446744073709551615 with (Z.ones 64); rewrite Z.land_ones by lia; apply Z.mod_small; lia).
        rewrite L64.
        pose proof (Z.mod_pos_bound bits 8 ltac:(lia)). pose proof (Z.div_mod bits 8 ltac:(lia)).
        assert (SWs : forall z, 0 <= z < 8 -> bv_swrap 32 z = z)
          by (intros z Hz; unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus; change (Z.of_N 32) with 32;
              rewrite Z.mod_small by lia; lia).
        rewrite (SWs (bits - bits / 8 * 8)) by lia. replace (bits - bits / 8 * 8) with (bits mod 8) by lia.
        zstep.
        replace (SP + -264) with (SPF + 264) by lia. replace (SP + -352 + 8 * k) with (SPF + 176 + 8 * k) by lia.
        change (Z_to_bv 64 (18446744073709551615 - (DT + 4))) with (Z_to_bv 64 (2^64 - 1 - (DT + 4))).
        apply (z4f_join5 p pt (bits / 8) (bits mod 8) 1 mm); [exact HZ | lia | lia | lia | lia
          | right; split; [reflexivity | lia] | exact JK].
      * zstep.
        rewrite bv_ltu_Z, !Z_to_bv_unsigned. unfold bv_wrap, bv_modulus; change (Z.of_N 64) with 64.
        rewrite (Z.mod_small (SS + pt - bits / 8)) by lia. rewrite (Z.mod_small SS) by lia.
        rewrite (proj2 (Z.ltb_lt _ _)) by lia. cbn [negb].
        do 4 zstep.
        replace (SS + pt - SS) with pt by lia. rewrite z4_land32 by lia.
        rewrite bv_ltu_Z, !Z_to_bv_unsigned. unfold bv_wrap, bv_modulus; change (Z.of_N 64) with 64.
        rewrite (Z.mod_small pt) by lia. rewrite (Z.mod_small (SS + pt)) by lia.
        rewrite (proj2 (Z.ltb_lt _ _)) by lia. cbn [negb].
        do 4 zstep.
        rewrite (proj2 (Z.ltb_lt _ _)) by lia. change (Z.lxor (Z.b2z true) 1) with 0.
        rewrite Z.shiftl_mul_pow2 by lia. change (2^3) with 8.
        assert (L64 : Z.land (pt * 8) 18446744073709551615 = pt * 8)
          by (change 18446744073709551615 with (Z.ones 64); rewrite Z.land_ones by lia; apply Z.mod_small; lia).
        rewrite L64.
        pose proof (Z.mod_pos_bound bits 8 ltac:(lia)). pose proof (Z.div_mod bits 8 ltac:(lia)).
        assert (SWs : forall z, 0 <= z <= 64 -> bv_swrap 32 z = z)
          by (intros z Hz; unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus; change (Z.of_N 32) with 32;
              rewrite Z.mod_small by lia; lia).
        rewrite (SWs (bits - pt * 8)) by lia.
        zstep.
        replace (SP + -264) with (SPF + 264) by lia. replace (SP + -352 + 8 * k) with (SPF + 176 + 8 * k) by lia.
        change (Z_to_bv 64 (18446744073709551615 - (DT + 4))) with (Z_to_bv 64 (2^64 - 1 - (DT + 4))).
        apply (z4f_join5 p pt pt (bits - pt * 8) 0 mm); [exact HZ | lia | lia | lia | lia | left; reflexivity
          | exact JK].
Qed.

  
  
  Lemma z4f_e5 : forall IP mm (x1 x5 x6 x9 a3 x27 x30 : word),
    Z4Mk mm -> SS <= IP -> IP + 8 <= SS + n -> bv_unsigned x27 <= 63 ->
    evtF bsegs RNG POST (STA 0x86c7c mm x1 x5 x6 x9 (Z_to_bv 64 IP) (Z_to_bv 64 (SE - OPk)) (Z_to_bv 64 OPk) a3
                             (Z_to_bv 64 SS) (Z_to_bv 64 (SS + 8)) (Z_to_bv 64 (SE - 9)) (Z_to_bv 64 SE) x27 x30).
Proof using All.
  intros IP mm x1 x5 x6 x9 a3 x27 x30 HZ HI1 HI2 B63.
  pose proof (bv_unsigned_in_range 64 x27) as X27.
  replace IP with (SS + (IP - SS)) by lia.
  rewrite <- (Z_to_bv_bv_unsigned x27).
  eapply (z4f_loop5 (S (Z.to_nat (SE - OPk)))); [exact HZ | lia | lia | lia | lia | lia].
Qed.

  End STREAM.

End Z4FIN.
End CANSEC1.
