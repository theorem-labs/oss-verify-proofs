(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import Tac Arr Bytes ZBridge ITree Nodes Decode SysStep Frame StoreFast.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Import Prelim Monad Fmt StdioCore Stdio PcapPrelim PcapTypes PcapPure Pcap Prog.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require FileCells__Musl. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require Printf_kit__Musl. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require AmoStep__Musl. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.FileCells__Musl.StrFun OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_kit__Musl.StartupKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.CellsExtra.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import ExecF ITreeA Shadow StepF SysStepF RunDraw.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require Import AImg ABase AMalloc_iface.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_memchr__S3. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_memchr__S3.SfKit.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require CkTac__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require MonadG GIA PcapRepA UnwKit. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require MonadGX__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require Pcap_ifaceA. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require FrameKit__A3P. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.CkTac__A3P.CkTac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadG OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.GIA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.PcapRepA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.UnwKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadGX__A3P.TracesA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.Pcap_ifaceA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.FrameKit__A3P.FrameKit.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Open Scope bv_scope.

(* [comment removed for export] *)
Definition np_shadow : list cell :=
  [C1 (Z_to_bv 8 18446744073709551601); C1 (Z_to_bv 8 18446744073709551601); C1 (Z_to_bv 8 18446744073709551601); C1 (Z_to_bv 8 18446744073709551601);
   C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0);
   C1 (Z_to_bv 8 18446744073709551602); C1 (Z_to_bv 8 18446744073709551602); C1 (Z_to_bv 8 18446744073709551602); C1 (Z_to_bv 8 18446744073709551602);
   C1 (Z_to_bv 8 18446744073709551602)].

(* [comment removed for export] *)
Record npk {hptr : Type} := mkNpk {
  k_self : hptr; k_f : hptr; k_sw : bool; k_vmaj : Z; k_vmin : Z; k_snap : Z; k_lt : Z; k_ltext : Z; k_hdr : pkthdr;
  k_hs : Z; k_lsw : lenswap_t; k_scl : sf_scale_t }.
Arguments npk : clear implicits.
(* [comment removed for export] *)
Definition pv {hptr : Type} (k : npk hptr) (bq : hptr) (bsz alloc : Z) (data eb : list Z) : PcapTypes.pcap hptr hptr :=
  mkPcap (k_self k) (k_f k) bsz alloc bq data (k_sw k) (k_vmaj k) (k_vmin k) (k_snap k) (k_lt k) (k_ltext k) 0 0 eb (k_hdr k)
         (PrivPcap (mkSf (k_hs k) (k_lsw k) (k_scl k))).

(* [comment removed for export] *)
Lemma le8_of_bytes : forall l : list byte, length l = 8%nat -> le8 (le_bytes_to_word l) = l.
Proof.
  intros l Hl. unfold le8, word_to_le_bytes, le_bytes_to_word. rewrite Z_to_bv_unsigned.
  change (bv_wrap 64 ?z) with (z mod 2^64)%Z. rewrite (Z_to_le_bytes_mod 8 _ 64) by (cbn; lia).
  rewrite <- Hl. apply Z_to_le_bytes_to_Z.
Qed.

Section CANSEC0. Context {rc : runConstT}.
(* [comment removed for export] *)
#[using="Type"] Lemma spill_words : forall m A l, rw_cells asegs m A [CB 120 l] ->
  exists w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 : word,
    rw_cells asegs m A [C8 w0; C8 w1; C8 w2; C8 w3; C8 w4; C8 w5; C8 w6; C8 w7; C8 w8; C8 w9; C8 w10; C8 w11; C8 w12; C8 w13; C8 w14].
Proof.
  intros m A l HC.
  apply (rw_cells_split_CB asegs _ _ [] 120 _ [] [8;8;8;8;8;8;8;8;8;8;8;8;8;8;8]%nat) in HC; [|reflexivity].
  cbn [mk_CB_cells app] in HC.
  repeat match type of HC with context [CB 8 ?t] => lazymatch t with firstn _ _ => idtac end; let j := fresh "jk" in set (j := t) in HC; clearbody j end.
  pose proof HC as [[WF _] _]. cbn [cells_wf cell_wf] in WF.
  destruct WF as (L0 & L1 & L2 & L3 & L4 & L5 & L6 & L7 & L8 & L9 & L10 & L11 & L12 & L13 & L14 & _).
  exists (le_bytes_to_word jk), (le_bytes_to_word jk0), (le_bytes_to_word jk1), (le_bytes_to_word jk2), (le_bytes_to_word jk3),
         (le_bytes_to_word jk4), (le_bytes_to_word jk5), (le_bytes_to_word jk6), (le_bytes_to_word jk7), (le_bytes_to_word jk8),
         (le_bytes_to_word jk9), (le_bytes_to_word jk10), (le_bytes_to_word jk11), (le_bytes_to_word jk12), (le_bytes_to_word jk13).
  eapply rw_cells_recell; [exact HC| cbn; repeat split|].
  cbn [cells_bytes cbytes]. rewrite !le8_of_bytes by assumption. reflexivity.
Qed.
End CANSEC0.

Section CANSEC1. Context {rc : runConstT} {tlsI : ABase.atlsT}.
Section NpDefs.
  Context {H hptr : Type} (HO : HeapOps H hptr) (FO : @FrameOps H hptr) (sites : stack_site -> Z).
  Variable GIOA : alayout -> footprint -> PState H hptr -> list (@cblock hptr) -> list (@cblock hptr) -> list fblock -> mem -> Prop.
  Variable TP : tparams.
  Variable fflagA : alayout -> fframe -> Z -> Z.

  (* [comment removed for export] *)
  Definition np_ctx (ra sp tp s0 : word) (L : alayout) (RNG : footprint) (CL FB : list (@cblock hptr)) (FL : list fblock) (trC : list Z)
      (lo HA DA Af SPA : Z) (f : hptr) (m : mem) : Prop :=
    (ATOP + 4096 <= lo)%Z /\ (lo + PCAP_L2_STACK <= bv_unsigned sp)%Z /\ (bv_unsigned sp + 16 < al_top L /\ al_top L <= 2^47)%Z
    /\ tp = Z_to_bv 64 ATP /\ (bv_unsigned sp mod 16 = 0)%Z
    /\ (rng RNG lo (al_top L - lo) /\ rng_aimg RNG /\ rng_aimg_sh RNG /\ rng_atls RNG)
    /\ ucallerA (depth_next_packet_op false) L m sp s0 ra trC /\ traces_next_packet_op TP false L (bv_unsigned ra) trC
    /\ nofr (frames_next_packet_op false) FL /\ In (f, Af, FILE_BLOCK) FB
    /\ cobjA RNG m FL CL HA 24 /\ cobjA RNG m FL CL DA 8 /\ (HA + 24 <= DA \/ DA + 8 <= HA)%Z
    /\ (HA mod 8 = 0)%Z /\ (DA mod 8 = 0)%Z
    /\ (bv_unsigned sp - 240 <= SPA <= bv_unsigned sp - 224)%Z /\ (SPA mod 32 = 0)%Z.

  (* [comment removed for export] *)
  Definition np_inv0 (ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (L : alayout) (RNG : footprint) (CL FB : list (@cblock hptr)) (FL : list fblock)
      (lo HA DA SPA Fb : Z) (o : option hptr) (m : mem)
      (RNGx : footprint) (sx : PState H hptr) (PB : list (@cblock hptr)) (dsh : list byte) (mm : mem) : Prop :=
    fp_le RNG RNGx /\ GIOA L RNGx sx (CL ++ PB) FB ((FF_NEXT_PACKET, Fb, 8192%Z) :: FL) mm /\ ps_outfile sx = o /\ mem_inv asegs mm
    /\ stk asegs mm lo SPA /\ stk asegs mm (SPA + 120) (bv_unsigned sp + -104)
    /\ rw_cells asegs mm (bv_unsigned sp + -104) [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]
    /\ agrees_on (fun a => client_keeps FL CL (bv_unsigned sp) a /\ outside [(HA, HA + 24); (DA, DA + 8)]%Z a) m mm
    /\ (exists (k0 k1 k2 : word) (fj : list byte),
          rw_cells asegs mm Fb [C8 k0; C8 k1; C8 k2; CB (Z.to_nat 8160) fj; C8 (Z_to_bv 64 (fflagA L FF_NEXT_PACKET Fb))])
    /\ rw_cells asegs mm (Z.shiftr Fb 3 + 2147450880) np_shadow
    /\ rw_cells asegs mm (Z.shiftr Fb 3 + 2147450892) [CB 512 dsh].
End NpDefs.

Section NpKeeps.
  Context {H hptr : Type} (FO : @FrameOps H hptr).
  Variable GIOA : alayout -> footprint -> PState H hptr -> list (@cblock hptr) -> list (@cblock hptr) -> list fblock -> mem -> Prop.
  Variable fflagA : alayout -> fframe -> Z -> Z.
  Hypothesis GL : gia_laws FO GIOA fflagA.

  (* [comment removed for export] *)
  #[using="tlsI FO fflagA GL"] Lemma keeps_not_PB : forall L RNG s (CLc PB FB : list (@cblock hptr)) FL FLc m SP a,
    GIOA L RNG s (CLc ++ PB) FB FL m -> incl FLc FL -> (ATOP <= SP)%Z -> client_keeps FLc CLc SP a -> ~ in_block PB a.
  Proof.
    intros L RNG s CLc PB FB FL FLc m SP a G IFL HSP K Hin.
    assert (HaB : in_block ((CLc ++ PB) ++ FB) a) by (apply in_block_app; left; apply in_block_app; right; exact Hin).
    destruct K as [K|[K|[K|K]]].
    - pose proof (gia_in_block_below _ _ _ GL _ _ _ _ _ _ _ a G HaB). lia.
    - apply in_block_In in K as (b & Hb & Hr). apply in_block_In in Hin as (b' & Hb' & Hr').
      pose proof (gl_apart _ _ _ GL _ _ _ _ _ _ _ G) as BA. apply blocks_apart_app_inv in BA as (BA & _ & _).
      apply blocks_apart_app_inv in BA as (_ & _ & BX). specialize (BX b b' Hb Hb'). unfold apart in BX. lia.
    - exact (gl_fr_apart _ _ _ GL _ _ _ _ _ _ _ a G (in_frames_incl _ _ _ IFL K) HaB).
    - pose proof (gia_in_frame_sh_band _ _ _ GL _ _ _ _ _ _ _ a G (in_frame_sh_incl _ _ _ IFL K)) as BD.
      apply in_block_In in HaB as (b & Hb & Hr). destruct (gl_block _ _ _ GL _ _ _ _ _ _ _ b G Hb) as ((BB & _) & _).
      exact (ablk_clear_band _ _ a BB ltac:(unfold KLS; lia) Hr).
  Qed.
End NpKeeps.
End CANSEC1.

(* [comment removed for export] *)
Ltac np_setup GL CTX INV :=
  pose proof CTX as (LO & BU & (SPT & TOP47) & TPE & ALN & (RSTK & RIMG & RISH & RTLS) & UC & TR & NF & HinF & OHA & ODA & DHD & HA8 & DA8 & SPAB & SPA32);
  pose proof INV as (FP & G & OF & MI & ST & STG & FR & AG & (k0 & k1 & k2 & fj & FRC) & SHC & SHD);
  unfold PCAP_L2_STACK in BU; unfold np_shadow in SHC;
  lazymatch type of ALN with (bv_unsigned ?sp mod 16 = 0)%Z => pose proof (bv_unsigned_in_range 64 sp) as RSP; unfold bv_modulus in RSP; cbn in RSP end;
  destruct (gl_frames _ _ _ GL _ _ _ _ _ _ _ G) as [FAll FND]; pose proof (Forall_inv FAll) as FRM; pose proof FRM as (FBAND' & FTOP' & F64 & _ & FRNG & FSRNG & _ & FSWR);
  cbn [fb_addr fb_size fst snd] in FBAND', FTOP', F64, FRNG, FSRNG, FSWR; clear FAll; change (Z.shiftr 8192 3) with 1024%Z in FSRNG, FSWR;
  pose proof (ablk_lin _ _ FBAND') as (_ & Fb0 & _ & _); (let bF := fresh "bF" in band_ind FBAND' bF);
  lazymatch type of G with ?GG _ _ _ (?CL ++ ?PB) _ ((FF_NEXT_PACKET, ?Fb, _) :: ?FL) _ =>
    assert (ICL : incl CL (CL ++ PB)) by (apply incl_appl, incl_refl);
    assert (IFL : incl FL ((FF_NEXT_PACKET, Fb, 8192%Z) :: FL)) by (apply incl_tl, incl_refl);
    assert (SHQ : (Fb = 8 * Z.shiftr Fb 3)%Z) by (rewrite Z.shiftr_div_pow2 by lia; change (2^3)%Z with 8%Z; Z.div_mod_to_equations; lia);
  pose proof (clocA_below _ _ _ GL _ _ _ _ _ _ _ _ _ G (clocA_incl _ _ _ _ _ _ (proj1 OHA) ICL IFL)) as (HALO & HAHI);
  pose proof (clocA_below _ _ _ GL _ _ _ _ _ _ _ _ _ G (clocA_incl _ _ _ _ _ _ (proj1 ODA) ICL IFL)) as (DALO & DAHI);
  pose proof (clocA_ablk _ _ _ GL _ _ _ _ _ _ _ _ _ G (clocA_incl _ _ _ _ _ _ (proj1 OHA) ICL IFL) ltac:(lia)) as HABAND;
  pose proof (clocA_ablk _ _ _ GL _ _ _ _ _ _ _ _ _ G (clocA_incl _ _ _ _ _ _ (proj1 ODA) ICL IFL) ltac:(lia)) as DABAND;
  pose proof HABAND as HABAND'; pose proof DABAND as DABAND';
  (let bH := fresh "bH" in band_ind HABAND bH); (let bD := fresh "bD" in band_ind DABAND bD);
  destruct (clocA_apart_frame _ _ _ GL _ _ _ _ _ _ _ _ _ _ G (clocA_incl _ _ _ _ _ _ (proj1 OHA) ICL (incl_refl _)) ltac:(lia)) as (kH & kHr & kH1 & kH2);
  destruct (clocA_apart_frame _ _ _ GL _ _ _ _ _ _ _ _ _ _ G (clocA_incl _ _ _ _ _ _ (proj1 ODA) ICL (incl_refl _)) ltac:(lia)) as (kD & kDr & kD1 & kD2);
  cbn [fb_addr fb_size fst snd] in kH1, kH2, kD1, kD2;
  pose proof (@Forall_cons (Z * Z) (fun iv : Z * Z => ablk (fst iv) (snd iv)) (_, _) _ HABAND'
                (@Forall_cons (Z * Z) (fun iv : Z * Z => ablk (fst iv) (snd iv)) (_, _) _ DABAND' (Forall_nil _))) as FXB;
  pose proof (keepsx_frame_sh _ _ _ GL _ _ _ _ _ _ _ _ _ _ _ _ _ G IFL AG FXB) as AGsh;
  pose proof (cobjA_keep _ _ _ GL _ _ _ _ _ _ _ _ _ _ _ _ _ OHA G ICL IFL AGsh ltac:(lia)) as OHAm;
  pose proof (cobjA_keep _ _ _ GL _ _ _ _ _ _ _ _ _ _ _ _ _ ODA G ICL IFL AGsh ltac:(lia)) as ODAm;
  pose proof OHAm as (_ & _ & _ & HAUNP & HARNG & HARSH & _); pose proof ODAm as (_ & _ & _ & DAUNP & DARNG & DARSH & _);
  rewrite HA8, Z.sub_0_r, Z.add_0_r in HARSH; rewrite DA8, Z.sub_0_r, Z.add_0_r in DARSH;
  apply (rng_fp_le _ _ _ _ FP) in RSTK; apply (rng_fp_le _ _ _ _ FP) in RIMG; apply (rng_fp_le _ _ _ _ FP) in RISH; apply (rng_fp_le _ _ _ _ FP) in RTLS;
  lazymatch type of RSTK with rng ?RNGx ?lo _ => lazymatch type of SPAB with (_ <= ?SPA <= bv_unsigned ?sp - _)%Z =>
    assert (RSPW : rng RNGx lo (bv_unsigned sp - lo)) by (eapply rng_sub'; [exact RSTK| lia]);
    assert (RSPA : rng RNGx SPA (bv_unsigned sp - SPA)) by (eapply rng_sub'; [exact RSTK| lia]) end end
  end.

(* [comment removed for export] *)
Ltac np_open PC :=
  pose proof PC as (Afx & HinFx & (Bx' & Ix & jx & padx & bsx & EPB & CELLS & PRIV & BUF & PFX & IFS & WF));
  unfold pv, pcap_blocks, psize, is_ng in EPB; cbn [pc_self pc_buffer pc_bufalloc pc_priv] in EPB;
  lazymatch type of EPB with _ :: (_, ?B0, _) :: _ = _ => (let E := fresh "EBX" in assert (E : Bx' = B0) by congruence; subst Bx') end; clear EPB;
  unfold pv in IFS; cbn [pc_priv ifaces_ok] in IFS; subst Ix;
  unfold pv, pcap_cells_gen, pc_pre, hdr_cells, pc_ops, np_entry, cleanup_entry, is_ng, PCAP_PRIV_OFF in CELLS;
  cbn [app pc_bufsize pc_break_loop pc_swapped pc_version_major pc_version_minor pc_snapshot pc_linktype pc_linktype_ext pc_tstamp_precision
       pc_header pc_priv pk_next_pcap pk_cleanup_sf PK] in CELLS;
  unfold pv, priv_cells, sf_cells, PCAP_PRIV_OFF in PRIV; cbn [pc_priv sf_hdrsize sf_lengths_swapped sf_scale_type] in PRIV;
  unfold pv in BUF, PFX; cbn [pc_bufalloc pc_bufdata] in BUF, PFX;
  pose proof WF as WF'; unfold pcap_wf, pv in WF';
  cbn [pc_snapshot pc_bufsize pc_bufalloc pc_bufdata pc_break_loop pc_tstamp_precision pc_version_major pc_version_minor
       pc_linktype pc_linktype_ext pc_header pc_priv sf_hdrsize] in WF';
  destruct WF' as (W1 & W2 & W3 & W4 & _ & _ & W7 & W8 & W9 & W10 & W11 & W12 & WHS & WBB); unfold INT_MAX in W1.

(* [comment removed for export] *)
Ltac np_blocks GL G OHA ODA IFL :=
  lazymatch type of G with ?GG _ _ _ (?CL ++ pcap_blocks (pv ?k ?bq ?bsz ?alloc ?data ?eb) ?P ?Bx 0%Z) ?FB ((FF_NEXT_PACKET, ?Fb, _) :: ?FL) _ =>
    assert (HinP : In (k_self k, P, 664%Z) ((CL ++ pcap_blocks (pv k bq bsz alloc data eb) P Bx 0%Z) ++ FB))
      by (apply in_or_app; left; apply in_or_app; right; left; reflexivity);
    assert (HinB : In (bq, Bx, alloc) ((CL ++ pcap_blocks (pv k bq bsz alloc data eb) P Bx 0%Z) ++ FB))
      by (apply in_or_app; left; apply in_or_app; right; right; left; reflexivity);
    assert (HinPB : In (k_self k, P, 664%Z) (pcap_blocks (pv k bq bsz alloc data eb) P Bx 0%Z)) by (left; reflexivity);
    assert (HinBB : In (bq, Bx, alloc) (pcap_blocks (pv k bq bsz alloc data eb) P Bx 0%Z)) by (right; left; reflexivity);
    pose proof (gl_block _ _ _ GL _ _ _ _ _ _ _ _ G HinP) as PBLK; pose proof PBLK as ((PBAND & _ & PTOP & P2) & P1 & PUNP & PRNG & PRSH & _);
    pose proof (gl_block _ _ _ GL _ _ _ _ _ _ _ _ G HinB) as BBLK; pose proof BBLK as ((BBAND & _ & BTOP & B2) & B1 & BUNP & BRNG & BRSH & _);
    cbn [cb_addr cb_size fst snd] in PBAND, PTOP, P2, P1, PUNP, PRNG, PRSH, BBAND, BTOP, B2, B1, BUNP, BRNG, BRSH;
    (let bP := fresh "bP" in band_ind PBAND bP); (let bB := fresh "bB" in band_ind BBAND bB);
    destruct (block_apart_frame _ _ _ GL _ _ _ _ _ _ _ _ _ G HinP (or_introl eq_refl) ltac:(cbn [cb_size snd]; lia)) as (kPF & kPFr & kPF1 & kPF2);
    destruct (block_apart_frame _ _ _ GL _ _ _ _ _ _ _ _ _ G HinB (or_introl eq_refl) ltac:(cbn [cb_size snd]; lia)) as (kBF & kBFr & kBF1 & kBF2);
    cbn [cb_addr cb_size fb_addr fb_size fst snd] in kPF1, kPF2, kBF1, kBF2;
    destruct (clocA_apart_block _ _ _ GL _ _ _ _ _ _ _ _ _ _ _ G (clocA_incl _ _ _ _ _ _ (proj1 OHA) (incl_refl _) IFL) HinPB ltac:(lia) ltac:(cbn [cb_size snd]; lia)) as (kHP & kHPr & kHP1 & kHP2);
    destruct (clocA_apart_block _ _ _ GL _ _ _ _ _ _ _ _ _ _ _ G (clocA_incl _ _ _ _ _ _ (proj1 ODA) (incl_refl _) IFL) HinPB ltac:(lia) ltac:(cbn [cb_size snd]; lia)) as (kDP & kDPr & kDP1 & kDP2);
    destruct (clocA_apart_block _ _ _ GL _ _ _ _ _ _ _ _ _ _ _ G (clocA_incl _ _ _ _ _ _ (proj1 OHA) (incl_refl _) IFL) HinBB ltac:(lia) ltac:(cbn [cb_size snd]; lia)) as (kHB & kHBr & kHB1 & kHB2);
    destruct (clocA_apart_block _ _ _ GL _ _ _ _ _ _ _ _ _ _ _ G (clocA_incl _ _ _ _ _ _ (proj1 ODA) (incl_refl _) IFL) HinBB ltac:(lia) ltac:(cbn [cb_size snd]; lia)) as (kDB & kDBr & kDB1 & kDB2);
    cbn [cb_addr cb_size fst snd] in kHP1, kHP2, kDP1, kDP2, kHB1, kHB2, kDB1, kDB2;
    pose proof (PB_apartA _ _ _ GL _ _ _ _ _ _ _ _ (pv k bq bsz alloc data eb) P Bx 0%Z G eq_refl) as [APB _];
    unfold pv, psize, is_ng in APB; cbn [pc_bufalloc pc_priv] in APB; unfold PCAP_SF_TOTAL in APB;
    (let kPB := fresh "kPB" in disj_ind APB kPB)
  end.

(* [comment removed for export] *)

Module TwB.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Tac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Arr OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Bytes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ZBridge OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ITree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Nodes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Decode OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.SysStep OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Frame OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.StoreFast.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Monad OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Fmt OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.StdioCore OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Stdio OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapPrelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapTypes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapPure OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Pcap OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prog.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.FileCells__Musl.StrFun OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_kit__Musl.StartupKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.CellsExtra.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.ExecF OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.ITreeA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.Shadow OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.StepF OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.SysStepF OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.RunDraw.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AMalloc_iface.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_memchr__S3.SfKit.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.CkTac__A3P.CkTac.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadG.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.GIA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.PcapRepA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.UnwKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadGX__A3P.TracesA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.Pcap_ifaceA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.FrameKit__A3P.FrameKit.TwB. Local Ltac Zify.zify_pre_hook ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB.twm_hook_1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Open Scope bv_scope.

(* [comment removed for export] *)
Definition np_shadow : list cell :=
  [C1 (Z_to_bv 8 18446744073709551601); C1 (Z_to_bv 8 18446744073709551601); C1 (Z_to_bv 8 18446744073709551601); C1 (Z_to_bv 8 18446744073709551601);
   C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0);
   C1 (Z_to_bv 8 18446744073709551602); C1 (Z_to_bv 8 18446744073709551602); C1 (Z_to_bv 8 18446744073709551602); C1 (Z_to_bv 8 18446744073709551602);
   C1 (Z_to_bv 8 18446744073709551602)].

(* [comment removed for export] *)
Record npk {hptr : Type} := mkNpk {
  k_self : hptr; k_f : hptr; k_sw : bool; k_vmaj : Z; k_vmin : Z; k_snap : Z; k_lt : Z; k_ltext : Z; k_hdr : pkthdr;
  k_hs : Z; k_lsw : lenswap_t; k_scl : sf_scale_t }.
Arguments npk : clear implicits.
(* [comment removed for export] *)
Definition pv {hptr : Type} (k : npk hptr) (bq : hptr) (bsz alloc : Z) (data eb : list Z) : PcapTypes.pcap hptr hptr :=
  mkPcap (k_self k) (k_f k) bsz alloc bq data (k_sw k) (k_vmaj k) (k_vmin k) (k_snap k) (k_lt k) (k_ltext k) 0 0 eb (k_hdr k)
         (PrivPcap (mkSf (k_hs k) (k_lsw k) (k_scl k))).

(* [comment removed for export] *)
Lemma le8_of_bytes : forall l : list byte, length l = 8%nat -> le8 (le_bytes_to_word l) = l.
Proof.
  intros l Hl. unfold le8, word_to_le_bytes, le_bytes_to_word. rewrite Z_to_bv_unsigned.
  change (bv_wrap 64 ?z) with (z mod 2^64)%Z. rewrite (Z_to_le_bytes_mod 8 _ 64) by (cbn; lia).
  rewrite <- Hl. apply Z_to_le_bytes_to_Z.
Qed.

Section CANSEC0. Context {rc : runConstT}.
(* [comment removed for export] *)
#[using="Type"] Lemma spill_words : forall m A l, rw_cells asegs m A [CB 120 l] ->
  exists w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 : word,
    rw_cells asegs m A [C8 w0; C8 w1; C8 w2; C8 w3; C8 w4; C8 w5; C8 w6; C8 w7; C8 w8; C8 w9; C8 w10; C8 w11; C8 w12; C8 w13; C8 w14].
Proof.
  intros m A l HC.
  apply (rw_cells_split_CB asegs _ _ [] 120 _ [] [8;8;8;8;8;8;8;8;8;8;8;8;8;8;8]%nat) in HC; [|reflexivity].
  cbn [mk_CB_cells app] in HC.
  repeat match type of HC with context [CB 8 ?t] => lazymatch t with firstn _ _ => idtac end; let j := fresh "jk" in set (j := t) in HC; clearbody j end.
  pose proof HC as [[WF _] _]. cbn [cells_wf cell_wf] in WF.
  destruct WF as (L0 & L1 & L2 & L3 & L4 & L5 & L6 & L7 & L8 & L9 & L10 & L11 & L12 & L13 & L14 & _).
  exists (le_bytes_to_word jk), (le_bytes_to_word jk0), (le_bytes_to_word jk1), (le_bytes_to_word jk2), (le_bytes_to_word jk3),
         (le_bytes_to_word jk4), (le_bytes_to_word jk5), (le_bytes_to_word jk6), (le_bytes_to_word jk7), (le_bytes_to_word jk8),
         (le_bytes_to_word jk9), (le_bytes_to_word jk10), (le_bytes_to_word jk11), (le_bytes_to_word jk12), (le_bytes_to_word jk13).
  eapply rw_cells_recell; [exact HC| cbn; repeat split|].
  cbn [cells_bytes cbytes]. rewrite !le8_of_bytes by assumption. reflexivity.
Qed.
End CANSEC0.

Section CANSEC1. Context {rc : runConstT} {tlsI : A3W.ABase.TwB.atlsT}.
Section NpDefs.
  Context {H hptr : Type} (HO : HeapOps H hptr) (FO : @FrameOps H hptr) (sites : stack_site -> Z).
  Variable GIOA : alayout -> footprint -> PState H hptr -> list (@cblock hptr) -> list (@cblock hptr) -> list fblock -> mem -> Prop.
  Variable TP : tparams.
  Variable fflagA : alayout -> fframe -> Z -> Z.

  (* [comment removed for export] *)
  Definition np_ctx (ra sp tp s0 : word) (L : alayout) (RNG : footprint) (CL FB : list (@cblock hptr)) (FL : list fblock) (trC : list Z)
      (lo HA DA Af SPA : Z) (f : hptr) (m : mem) : Prop :=
    (ATOP + 4096 <= lo)%Z /\ (lo + PCAP_L2_STACK <= bv_unsigned sp)%Z /\ (bv_unsigned sp + 16 < al_top L /\ al_top L <= 2^47)%Z
    /\ tp = Z_to_bv 64 ATP /\ (bv_unsigned sp mod 16 = 0)%Z
    /\ (rng RNG lo (al_top L - lo) /\ rng_aimg RNG /\ rng_aimg_sh RNG /\ rng_atls RNG)
    /\ ucallerA (depth_next_packet_op false) L m sp s0 ra trC /\ traces_next_packet_op TP false L (bv_unsigned ra) trC
    /\ nofr (frames_next_packet_op false) FL /\ In (f, Af, FILE_BLOCK) FB
    /\ cobjA RNG m FL CL HA 24 /\ cobjA RNG m FL CL DA 8 /\ (HA + 24 <= DA \/ DA + 8 <= HA)%Z
    /\ (HA mod 8 = 0)%Z /\ (DA mod 8 = 0)%Z
    /\ (bv_unsigned sp - 240 <= SPA <= bv_unsigned sp - 224)%Z /\ (SPA mod 32 = 0)%Z.

  (* [comment removed for export] *)
  Definition np_inv0 (ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (L : alayout) (RNG : footprint) (CL FB : list (@cblock hptr)) (FL : list fblock)
      (lo HA DA SPA Fb : Z) (o : option hptr) (m : mem)
      (RNGx : footprint) (sx : PState H hptr) (PB : list (@cblock hptr)) (dsh : list byte) (mm : mem) : Prop :=
    fp_le RNG RNGx /\ GIOA L RNGx sx (CL ++ PB) FB ((FF_NEXT_PACKET, Fb, 8192%Z) :: FL) mm /\ ps_outfile sx = o /\ mem_inv asegs mm
    /\ stk asegs mm lo SPA /\ stk asegs mm (SPA + 120) (bv_unsigned sp + -104)
    /\ rw_cells asegs mm (bv_unsigned sp + -104) [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]
    /\ agrees_on (fun a => client_keeps FL CL (bv_unsigned sp) a /\ outside [(HA, HA + 24); (DA, DA + 8)]%Z a) m mm
    /\ (exists (k0 k1 k2 : word) (fj : list byte),
          rw_cells asegs mm Fb [C8 k0; C8 k1; C8 k2; CB (Z.to_nat 8160) fj; C8 (Z_to_bv 64 (fflagA L FF_NEXT_PACKET Fb))])
    /\ rw_cells asegs mm (Z.shiftr Fb 3 + 2147450880) np_shadow
    /\ rw_cells asegs mm (Z.shiftr Fb 3 + 2147450892) [CB 512 dsh].
End NpDefs.

Section NpKeeps.
  Context {H hptr : Type} (FO : @FrameOps H hptr).
  Variable GIOA : alayout -> footprint -> PState H hptr -> list (@cblock hptr) -> list (@cblock hptr) -> list fblock -> mem -> Prop.
  Variable fflagA : alayout -> fframe -> Z -> Z.
  Hypothesis GL : gia_laws FO GIOA fflagA.

  (* [comment removed for export] *)
  #[using="tlsI FO fflagA GL"] Lemma keeps_not_PB : forall L RNG s (CLc PB FB : list (@cblock hptr)) FL FLc m SP a,
    GIOA L RNG s (CLc ++ PB) FB FL m -> incl FLc FL -> (ATOP <= SP)%Z -> client_keeps FLc CLc SP a -> ~ in_block PB a.
  Proof.
    intros L RNG s CLc PB FB FL FLc m SP a G IFL HSP K Hin.
    assert (HaB : in_block ((CLc ++ PB) ++ FB) a) by (apply in_block_app; left; apply in_block_app; right; exact Hin).
    destruct K as [K|[K|[K|K]]].
    - pose proof (gia_in_block_below _ _ _ GL _ _ _ _ _ _ _ a G HaB). lia.
    - apply in_block_In in K as (b & Hb & Hr). apply in_block_In in Hin as (b' & Hb' & Hr').
      pose proof (gl_apart _ _ _ GL _ _ _ _ _ _ _ G) as BA. apply blocks_apart_app_inv in BA as (BA & _ & _).
      apply blocks_apart_app_inv in BA as (_ & _ & BX). specialize (BX b b' Hb Hb'). unfold apart in BX. lia.
    - exact (gl_fr_apart _ _ _ GL _ _ _ _ _ _ _ a G (in_frames_incl _ _ _ IFL K) HaB).
    - pose proof (gia_in_frame_sh_band _ _ _ GL _ _ _ _ _ _ _ a G (in_frame_sh_incl _ _ _ IFL K)) as BD.
      apply in_block_In in HaB as (b & Hb & Hr). destruct (gl_block _ _ _ GL _ _ _ _ _ _ _ b G Hb) as ((BB & _) & _).
      exact (ablk_clear_band _ _ a BB ltac:(unfold KLS; lia) Hr).
  Qed.
End NpKeeps.
End CANSEC1.

(* [comment removed for export] *)
Ltac np_setup GL CTX INV :=
  pose proof CTX as (LO & BU & (SPT & TOP47) & TPE & ALN & (RSTK & RIMG & RISH & RTLS) & UC & TR & NF & HinF & OHA & ODA & DHD & HA8 & DA8 & SPAB & SPA32);
  pose proof INV as (FP & G & OF & MI & ST & STG & FR & AG & (k0 & k1 & k2 & fj & FRC) & SHC & SHD);
  unfold PCAP_L2_STACK in BU; unfold np_shadow in SHC;
  lazymatch type of ALN with (bv_unsigned ?sp mod 16 = 0)%Z => pose proof (bv_unsigned_in_range 64 sp) as RSP; unfold bv_modulus in RSP; cbn in RSP end;
  destruct (gl_frames _ _ _ GL _ _ _ _ _ _ _ G) as [FAll FND]; pose proof (Forall_inv FAll) as FRM; pose proof FRM as (FBAND' & FTOP' & F64 & _ & FRNG & FSRNG & _ & FSWR);
  cbn [fb_addr fb_size fst snd] in FBAND', FTOP', F64, FRNG, FSRNG, FSWR; clear FAll; change (Z.shiftr 8192 3) with 1024%Z in FSRNG, FSWR;
  pose proof (ablk_lin _ _ FBAND') as (_ & Fb0 & _ & _); (let bF := fresh "bF" in band_ind FBAND' bF);
  lazymatch type of G with ?GG _ _ _ (?CL ++ ?PB) _ ((FF_NEXT_PACKET, ?Fb, _) :: ?FL) _ =>
    assert (ICL : incl CL (CL ++ PB)) by (apply incl_appl, incl_refl);
    assert (IFL : incl FL ((FF_NEXT_PACKET, Fb, 8192%Z) :: FL)) by (apply incl_tl, incl_refl);
    assert (SHQ : (Fb = 8 * Z.shiftr Fb 3)%Z) by (rewrite Z.shiftr_div_pow2 by lia; change (2^3)%Z with 8%Z; Z.div_mod_to_equations; lia);
  pose proof (clocA_below _ _ _ GL _ _ _ _ _ _ _ _ _ G (clocA_incl _ _ _ _ _ _ (proj1 OHA) ICL IFL)) as (HALO & HAHI);
  pose proof (clocA_below _ _ _ GL _ _ _ _ _ _ _ _ _ G (clocA_incl _ _ _ _ _ _ (proj1 ODA) ICL IFL)) as (DALO & DAHI);
  pose proof (clocA_ablk _ _ _ GL _ _ _ _ _ _ _ _ _ G (clocA_incl _ _ _ _ _ _ (proj1 OHA) ICL IFL) ltac:(lia)) as HABAND;
  pose proof (clocA_ablk _ _ _ GL _ _ _ _ _ _ _ _ _ G (clocA_incl _ _ _ _ _ _ (proj1 ODA) ICL IFL) ltac:(lia)) as DABAND;
  pose proof HABAND as HABAND'; pose proof DABAND as DABAND';
  (let bH := fresh "bH" in band_ind HABAND bH); (let bD := fresh "bD" in band_ind DABAND bD);
  destruct (clocA_apart_frame _ _ _ GL _ _ _ _ _ _ _ _ _ _ G (clocA_incl _ _ _ _ _ _ (proj1 OHA) ICL (incl_refl _)) ltac:(lia)) as (kH & kHr & kH1 & kH2);
  destruct (clocA_apart_frame _ _ _ GL _ _ _ _ _ _ _ _ _ _ G (clocA_incl _ _ _ _ _ _ (proj1 ODA) ICL (incl_refl _)) ltac:(lia)) as (kD & kDr & kD1 & kD2);
  cbn [fb_addr fb_size fst snd] in kH1, kH2, kD1, kD2;
  pose proof (@Forall_cons (Z * Z) (fun iv : Z * Z => ablk (fst iv) (snd iv)) (_, _) _ HABAND'
                (@Forall_cons (Z * Z) (fun iv : Z * Z => ablk (fst iv) (snd iv)) (_, _) _ DABAND' (Forall_nil _))) as FXB;
  pose proof (keepsx_frame_sh _ _ _ GL _ _ _ _ _ _ _ _ _ _ _ _ _ G IFL AG FXB) as AGsh;
  pose proof (cobjA_keep _ _ _ GL _ _ _ _ _ _ _ _ _ _ _ _ _ OHA G ICL IFL AGsh ltac:(lia)) as OHAm;
  pose proof (cobjA_keep _ _ _ GL _ _ _ _ _ _ _ _ _ _ _ _ _ ODA G ICL IFL AGsh ltac:(lia)) as ODAm;
  pose proof OHAm as (_ & _ & _ & HAUNP & HARNG & HARSH & _); pose proof ODAm as (_ & _ & _ & DAUNP & DARNG & DARSH & _);
  rewrite HA8, Z.sub_0_r, Z.add_0_r in HARSH; rewrite DA8, Z.sub_0_r, Z.add_0_r in DARSH;
  apply (rng_fp_le _ _ _ _ FP) in RSTK; apply (rng_fp_le _ _ _ _ FP) in RIMG; apply (rng_fp_le _ _ _ _ FP) in RISH; apply (rng_fp_le _ _ _ _ FP) in RTLS;
  lazymatch type of RSTK with rng ?RNGx ?lo _ => lazymatch type of SPAB with (_ <= ?SPA <= bv_unsigned ?sp - _)%Z =>
    assert (RSPW : rng RNGx lo (bv_unsigned sp - lo)) by (eapply rng_sub'; [exact RSTK| lia]);
    assert (RSPA : rng RNGx SPA (bv_unsigned sp - SPA)) by (eapply rng_sub'; [exact RSTK| lia]) end end
  end.

(* [comment removed for export] *)
Ltac np_open PC :=
  pose proof PC as (Afx & HinFx & (Bx' & Ix & jx & padx & bsx & EPB & CELLS & PRIV & BUF & PFX & IFS & WF));
  unfold pv, pcap_blocks, psize, is_ng in EPB; cbn [pc_self pc_buffer pc_bufalloc pc_priv] in EPB;
  lazymatch type of EPB with _ :: (_, ?B0, _) :: _ = _ => (let E := fresh "EBX" in assert (E : Bx' = B0) by congruence; subst Bx') end; clear EPB;
  unfold pv in IFS; cbn [pc_priv ifaces_ok] in IFS; subst Ix;
  unfold pv, pcap_cells_gen, pc_pre, hdr_cells, pc_ops, np_entry, cleanup_entry, is_ng, PCAP_PRIV_OFF in CELLS;
  cbn [app pc_bufsize pc_break_loop pc_swapped pc_version_major pc_version_minor pc_snapshot pc_linktype pc_linktype_ext pc_tstamp_precision
       pc_header pc_priv pk_next_pcap pk_cleanup_sf PK] in CELLS;
  unfold pv, priv_cells, sf_cells, PCAP_PRIV_OFF in PRIV; cbn [pc_priv sf_hdrsize sf_lengths_swapped sf_scale_type] in PRIV;
  unfold pv in BUF, PFX; cbn [pc_bufalloc pc_bufdata] in BUF, PFX;
  pose proof WF as WF'; unfold pcap_wf, pv in WF';
  cbn [pc_snapshot pc_bufsize pc_bufalloc pc_bufdata pc_break_loop pc_tstamp_precision pc_version_major pc_version_minor
       pc_linktype pc_linktype_ext pc_header pc_priv sf_hdrsize] in WF';
  destruct WF' as (W1 & W2 & W3 & W4 & _ & _ & W7 & W8 & W9 & W10 & W11 & W12 & WHS & WBB); unfold INT_MAX in W1.

(* [comment removed for export] *)
Ltac np_blocks GL G OHA ODA IFL :=
  lazymatch type of G with ?GG _ _ _ (?CL ++ pcap_blocks (pv ?k ?bq ?bsz ?alloc ?data ?eb) ?P ?Bx 0%Z) ?FB ((FF_NEXT_PACKET, ?Fb, _) :: ?FL) _ =>
    assert (HinP : In (k_self k, P, 664%Z) ((CL ++ pcap_blocks (pv k bq bsz alloc data eb) P Bx 0%Z) ++ FB))
      by (apply in_or_app; left; apply in_or_app; right; left; reflexivity);
    assert (HinB : In (bq, Bx, alloc) ((CL ++ pcap_blocks (pv k bq bsz alloc data eb) P Bx 0%Z) ++ FB))
      by (apply in_or_app; left; apply in_or_app; right; right; left; reflexivity);
    assert (HinPB : In (k_self k, P, 664%Z) (pcap_blocks (pv k bq bsz alloc data eb) P Bx 0%Z)) by (left; reflexivity);
    assert (HinBB : In (bq, Bx, alloc) (pcap_blocks (pv k bq bsz alloc data eb) P Bx 0%Z)) by (right; left; reflexivity);
    pose proof (gl_block _ _ _ GL _ _ _ _ _ _ _ _ G HinP) as PBLK; pose proof PBLK as ((PBAND & _ & PTOP & P2) & P1 & PUNP & PRNG & PRSH & _);
    pose proof (gl_block _ _ _ GL _ _ _ _ _ _ _ _ G HinB) as BBLK; pose proof BBLK as ((BBAND & _ & BTOP & B2) & B1 & BUNP & BRNG & BRSH & _);
    cbn [cb_addr cb_size fst snd] in PBAND, PTOP, P2, P1, PUNP, PRNG, PRSH, BBAND, BTOP, B2, B1, BUNP, BRNG, BRSH;
    (let bP := fresh "bP" in band_ind PBAND bP); (let bB := fresh "bB" in band_ind BBAND bB);
    destruct (block_apart_frame _ _ _ GL _ _ _ _ _ _ _ _ _ G HinP (or_introl eq_refl) ltac:(cbn [cb_size snd]; lia)) as (kPF & kPFr & kPF1 & kPF2);
    destruct (block_apart_frame _ _ _ GL _ _ _ _ _ _ _ _ _ G HinB (or_introl eq_refl) ltac:(cbn [cb_size snd]; lia)) as (kBF & kBFr & kBF1 & kBF2);
    cbn [cb_addr cb_size fb_addr fb_size fst snd] in kPF1, kPF2, kBF1, kBF2;
    destruct (clocA_apart_block _ _ _ GL _ _ _ _ _ _ _ _ _ _ _ G (clocA_incl _ _ _ _ _ _ (proj1 OHA) (incl_refl _) IFL) HinPB ltac:(lia) ltac:(cbn [cb_size snd]; lia)) as (kHP & kHPr & kHP1 & kHP2);
    destruct (clocA_apart_block _ _ _ GL _ _ _ _ _ _ _ _ _ _ _ G (clocA_incl _ _ _ _ _ _ (proj1 ODA) (incl_refl _) IFL) HinPB ltac:(lia) ltac:(cbn [cb_size snd]; lia)) as (kDP & kDPr & kDP1 & kDP2);
    destruct (clocA_apart_block _ _ _ GL _ _ _ _ _ _ _ _ _ _ _ G (clocA_incl _ _ _ _ _ _ (proj1 OHA) (incl_refl _) IFL) HinBB ltac:(lia) ltac:(cbn [cb_size snd]; lia)) as (kHB & kHBr & kHB1 & kHB2);
    destruct (clocA_apart_block _ _ _ GL _ _ _ _ _ _ _ _ _ _ _ G (clocA_incl _ _ _ _ _ _ (proj1 ODA) (incl_refl _) IFL) HinBB ltac:(lia) ltac:(cbn [cb_size snd]; lia)) as (kDB & kDBr & kDB1 & kDB2);
    cbn [cb_addr cb_size fst snd] in kHP1, kHP2, kDP1, kDP2, kHB1, kHB2, kDB1, kDB2;
    pose proof (PB_apartA _ _ _ GL _ _ _ _ _ _ _ _ (pv k bq bsz alloc data eb) P Bx 0%Z G eq_refl) as [APB _];
    unfold pv, psize, is_ng in APB; cbn [pc_bufalloc pc_priv] in APB; unfold PCAP_SF_TOTAL in APB;
    (let kPB := fresh "kPB" in disj_ind APB kPB)
  end.
End TwB.
