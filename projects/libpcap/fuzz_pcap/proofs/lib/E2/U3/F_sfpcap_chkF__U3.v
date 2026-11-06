(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Lia.
(* [comment removed for export] *)
From Stdlib Require ZArith NArith List Lia Bool String.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require PropExec Tac Arr Bytes ZBridge ITree Nodes Decode SysStep MonadX Image ImgTgtUbsan.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Prelim Monad Fmt StdioCore Stdio PcapPrelim PcapTypes PcapPure Pcap Prog.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Adapter__Spec.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require AmoStep__Musl.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require Printf_kit__Musl.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require FmtFacts__S3.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_memchr__S3.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_memcpy GI.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require GIFacts__S3.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require PcapRep.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require Pcap_iface__S3.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_pcap_err__S3.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.U3 Require F_sfpcap_chkA.
From OSSVerify.libpcap.fuzz_pcap.images Require Ubsan.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Ceiling.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require LiaPin.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require SecDiet.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require KeepHyps.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_lock__S3.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_sfpcap_nextA.
From Stdlib Require Permutation.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Module F_sfpcap_chkF.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool String.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import PropExec Tac Arr Bytes ZBridge ITree Nodes Decode SysStep MonadX Image ImgTgtUbsan.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Prelim Monad Fmt StdioCore Stdio PcapPrelim PcapTypes PcapPure Pcap Prog. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Adapter__Spec. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Monad OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Fmt OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.StdioCore OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Stdio OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapPrelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapTypes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapPure OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Pcap OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prog OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Adapter__Spec.StartupModel.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require AmoStep__Musl. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require Printf_kit__Musl. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.STRW_tac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_kit__Musl.StartupKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.CellsExtra.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require FmtFacts__S3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_memchr__S3. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.FmtFacts__S3.FmtFacts OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_memchr__S3.SfKit.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_memcpy GI. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require GIFacts__S3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require PcapRep. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require Pcap_iface__S3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_pcap_err__S3. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_memcpy.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.GI.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.GIFacts__S3.GIFacts.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.GIFacts__S3.Ifaces.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.PcapRep.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Pcap_iface__S3.Pcap_iface.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Pcap_iface__S3.F_pcap_pure.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Pcap_iface__S3.F_pcap_small.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Pcap_iface__S3.F_pcap_next_ex.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_pcap_err__S3.F_pcap_open.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_pcap_err__S3.F_pcap_fopen.TwB. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.U3 Require Import F_sfpcap_chkA.
From OSSVerify.libpcap.fuzz_pcap.images Require Import Ubsan.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import Ceiling.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import LiaPin.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require SecDiet.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import KeepHyps.
(* [comment removed for export] *)
Local Ltac lia_e2w2_base := first [ zify_prune; zify_noeuclid; Z.euclidean_division_equations_cleanup; xlia zchecker
                                 | zify_prune; Zify.zify; xlia zchecker | Zify.zify; xlia zchecker ].
Local Ltac ceil_mentioned := lazymatch goal with | |- context [@alloc_ceiling _] => idtac | _ : context [@alloc_ceiling _] |- _ => idtac end.
(* [comment removed for export] *)
Local Ltac lia ::= clear_unpinned; try (ceil_ok; ceil_mentioned; ceil_facts); pinned_lia_core.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Open Scope bv_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Section WithCeil.
Context {CEILV : CEIL}.
Section ChkF.
  Context {H hptr : Type} (HO : HeapOps H hptr) (K : modkit H hptr) (sites : stack_site -> Z).
  Hypothesis HFL : heap_frame_law K.
  Hypothesis SFL : stdio_fp_law K.
  Hypothesis HPL : heap_perm_law K.
  Hypothesis MALLOC : malloc_stmt_o HO K.
  Hypothesis FREE : free_stmt_o HO K.

  #[local] Abbreviation chk_ctx := (F_sfpcap_chkA.chk_ctx K sites).
  #[local] Abbreviation chk_fail := (F_sfpcap_chkA.chk_fail K sites HFL SFL).
  #[local] Abbreviation pcells := (@F_sfpcap_chkA.pcells).
  #[local] Abbreviation blank_junk := (@F_sfpcap_chkA.blank_junk).
  #[local] Abbreviation z8 := (@F_sfpcap_chkA.z8).
  #[local] Abbreviation blocks2_apart := (F_sfpcap_chkA.blocks2_apart K).

  (* [comment removed for export] *)
  Definition chk_fill__stmt : Prop := forall (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
           (R : rctx) (s : PState H hptr) (CL FB : list cblock) (lo MG FA EB ERR : Z) (f : hptr) (magic : list Z) (m : mem)
           (ra' t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m3 : mem) (ps3 : PState H hptr) (q : hptr) (P : Z)
           (maj min n0 n1 n2 n3 l0 l1 l2 l3 mi : Z) (sw : bool) (mid e3 : list byte),
      chk_ctx sp tp R s CL FB lo MG FA EB ERR f magic m ->
      (mi = TCPDUMP_MAGIC \/ mi = KUZNETZOV_TCPDUMP_MAGIC \/ mi = NSEC_TCPDUMP_MAGIC) ->
      (0 <= maj < 2^16)%Z -> (0 <= min < 2^16)%Z ->
      (0 <= n0 < 256)%Z -> (0 <= n1 < 256)%Z -> (0 <= n2 < 256)%Z -> (0 <= n3 < 256)%Z ->
      (0 <= l0 < 256)%Z -> (0 <= l1 < 256)%Z -> (0 <= l2 < 256)%Z -> (0 <= l3 < 256)%Z -> l2 = 0%Z -> (l3 mod 4 = 0)%Z ->
      mem_inv usegs m3 -> stk usegs m3 lo (bv_unsigned sp + -96) ->
      agrees_on (fun a => client_keeps CL (bv_unsigned sp) a /\ ~ (EB <= a < EB + 256) /\ ~ (ERR <= a < ERR + 4))%Z m m3 ->
      GIo K R ps3 ((q, P, PCAP_SF_TOTAL) :: CL) FB m3 ->
      rw_cells usegs m3 P ([CB 16 (repeat (Z_to_bv 8 0) 16); C4 (Z_to_bv 64 (-1)); CB 28 (repeat (Z_to_bv 8 0) 28);
                            C8 (Z_to_bv 64 (P + PCAP_PRIV_OFF)); CB 128 (repeat (Z_to_bv 8 0) 128); C4 (Z_to_bv 64 (-1));
                            CB (Z.to_nat (PCAP_SF_TOTAL - 188)) (repeat (Z_to_bv 8 0) (Z.to_nat (PCAP_SF_TOTAL - 188)))]) ->
      rw_cells usegs m3 (bv_unsigned sp + -96) [C4 (Z_to_bv 64 (mi + (2^64 - 2^32)))] ->
      rw_cells usegs m3 (bv_unsigned sp + -92)
        [C2 (Z_to_bv 64 maj); C2 (Z_to_bv 64 min); CB 8 mid; C4 (Z_to_bv 64 (le4val n0 n1 n2 n3)); C4 (Z_to_bv 64 (le4val l0 l1 l2 l3))] ->
      rw_cells usegs m3 (bv_unsigned sp + -72) [C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
      rw_cells usegs m3 ERR [C4 z64] -> rw_cells usegs m3 MG (map (fun z => C1 (Z_to_bv 8 z)) magic) -> rw_cells usegs m3 EB [CB 256 e3] ->
      ps_outfile ps3 = ps_outfile s ->
      implM usegs (chk_fill_model MOps (prims HO fo_nop sites) q f 0 mi sw maj min (le4val n0 n1 n2 n3) (le4val l0 l1 l2 l3)) ps3
        (check_header_post K ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc R CL FB lo MG EB ERR magic f m (ps_outfile s))
        (MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -96)) gp tp t0 t1 t2 (Z_to_bv 64 ERR) (Z_to_bv 64 EB) (Z_to_bv 64 P) a1 a2 a3 a4 a5 a6 a7
                 z64 (Z_to_bv 64 min) (Z_to_bv 64 maj) (Z_to_bv 64 (mi + (2^64 - 2^32))) (Z_to_bv 64 (Z.b2z sw)) (Z_to_bv 64 (sxv l0 l1 l2 l3))
                 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x1570c) fc None m3 (seg_rom usegs)).
  Section Sz1.
  Variables ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc R s CL FB lo MG FA EB ERR f magic m ra' t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m3 ps3 q P maj min n0 n1 n2 n3 l0 l1 l2 l3 mi sw mid e3 : ltac2:(SecDiet.SzSec.tyM 'chk_fill__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra).
  Lemma chk_fill__body : ltac2:(SecDiet.SzSec.bodyP 'chk_fill__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof using FREE HFL HPL MALLOC SFL. pin_using (fun (FREE HFL HPL MALLOC SFL : unit) => tt).
 intros CTX MI3 Bmaj Bmin N0 N1 N2 N3 L0 L1 L2 L3 Z2 Z3 MI2 ST3 AG3 G3 CELLS0 FRA FRD FRS ERRc MG4 HEB3 OFX.
    destruct CTX as (G & LO & BU & SPM & TP & ALN & HinF & SITES & GL & GR & R1 & R2 & R3 & E1 & E2 & D1 & E4 & E8).
    pose proof (GIo_spw K _ _ _ _ _ G) as SPW. pose proof (bv_unsigned_in_range 64 sp) as RSP.
    assert (MIB : (2^31 <= mi < 2^32)%Z) by (unfold TCPDUMP_MAGIC, KUZNETZOV_TCPDUMP_MAGIC, NSEC_TCPDUMP_MAGIC in MI3; lia).
    pose proof (GIo_block_ok K _ _ _ _ _ _ G3 ltac:(left; reflexivity)) as (P1 & P2 & P3 & P4 & P5 & P6).
    cbn [cb_addr cb_size fst snd] in P1, P2, P3, P4, P5, P6. unfold PCAP_SF_TOTAL in P4, P5, P6.
    assert (P8 : (P mod 8 = 0)%Z) by (rewrite <- (Z.add_0_r P); apply aligned16_8; [exact P2| reflexivity]).
    pose proof (aligned16_8 P 648 P2 eq_refl) as P648.
    assert (CLB : forall a, in_block CL a -> (a < CEILZ)%Z).
    { intros a Ha. destruct (GIo_CLc_facts K R s CL [] FB m a ltac:(rewrite app_nil_r; exact G) Ha) as [Hc _]. exact (proj2 Hc). }
    assert (NB : forall a, in_block CL a -> ~ (P <= a < P + 664)%Z).
    { intros a Ha Hin. destruct (GIo_CLc_facts K R ps3 [(q, P, PCAP_SF_TOTAL)] CL FB m3 a G3
                 ltac:(unfold in_block; apply Exists_cons_hd; cbn [cb_addr cb_size fst snd]; unfold PCAP_SF_TOTAL; exact Hin)) as [_ Hn]. exact (Hn Ha). }
    apply F_sfpcap_chkA.blank_recell in CELLS0. rename CELLS0 into CELLS. unfold F_sfpcap_chkA.blank_cells, PCAP_PRIV_OFF in CELLS.
    (* [comment removed for export] *)
    unfold chk_fill_model. cbn [e_fenter e_fret fo_enter fo_ret fo_nop prims]. rewrite (land_ffff l0 l1 l2 l3) by lia.
    unfold PCAP_TSTAMP_PRECISION_MICRO. cbn [Z.eqb mo_bind mo_ret MOps e_fenter e_fret fo_enter fo_ret fo_nop prims e_malloc e_free prims].
    set (lt := linktype_to_dlt (l0 + 256 * l1)). set (snap := pcapint_adjust_snapshot lt (le4val n0 n1 n2 n3)).
    pose proof (linktype_to_dlt_range (l0 + 256 * l1) ltac:(lia)) as LTR. fold lt in LTR.
    pose proof (adjust_snapshot_range lt (le4val n0 n1 n2 n3) ltac:(unfold le4val; lia)) as SNR. fold snap in SNR. unfold INT_MAX in SNR.
    set (EXT := s32 (Z.land (le4val l0 l1 l2 l3) 4294901760)).
    pose proof (s32_range (Z.land (le4val l0 l1 l2 l3) 4294901760)) as EXR. fold EXT in EXR.
    set (POSTQ := check_header_post K ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc R CL FB lo MG EB ERR magic f m (ps_outfile s)).
    (* [comment removed for export] *)
    assert (K4OK : forall (ra6 t0' t1' t2' a2' a3' a4' a5' a6' a7' x2 x3 t3' t4' t5' t6' : word) (m6 : mem) (ps6 : PState H hptr)
                          (bq : hptr) (B BS HS SS : Z) (LS : lenswap_t) (SC : sf_scale_t) (bjunk e6 : list byte),
      (HS = 16 \/ HS = 24)%Z -> (1 <= SS <= 2147483647)%Z -> BS = (if 2048 <? SS then 2048 else SS)%Z ->
      mem_inv usegs m6 -> stk usegs m6 lo (bv_unsigned sp + -96) ->
      agrees_on (fun a => client_keeps CL (bv_unsigned sp) a /\ ~ (EB <= a < EB + 256) /\ ~ (ERR <= a < ERR + 4))%Z m m6 ->
      GIo K R ps6 ((bq, B, BS) :: (q, P, PCAP_SF_TOTAL) :: CL) FB m6 ->
      rw_cells usegs m6 B [CB (Z.to_nat BS) bjunk] ->
      rw_cells usegs m6 P (pcells P sw maj min lt EXT (C8 (Z_to_bv 64 88428)) (C4 (Z_to_bv 64 BS)) (C8 (Z_to_bv 64 B)) (C4 (Z_to_bv 64 SS))
                             (C8 (Z_to_bv 64 0)) (C8 (Z_to_bv 64 HS)) (C4 (Z_to_bv 64 (lenswap_code LS))) (C4 (Z_to_bv 64 (sfscale_code SC)))) ->
      rw_cells usegs m6 (bv_unsigned sp + -96) [C4 (Z_to_bv 64 (mi + (2^64 - 2^32)))] ->
      rw_cells usegs m6 (bv_unsigned sp + -92)
        [C2 (Z_to_bv 64 maj); C2 (Z_to_bv 64 min); CB 8 mid; C4 (Z_to_bv 64 (le4val n0 n1 n2 n3)); C4 (Z_to_bv 64 (le4val l0 l1 l2 l3))] ->
      rw_cells usegs m6 (bv_unsigned sp + -72) [C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
      rw_cells usegs m6 ERR [C4 z64] -> rw_cells usegs m6 MG (map (fun z => C1 (Z_to_bv 8 z)) magic) -> rw_cells usegs m6 EB [CB 256 e6] ->
      ps_outfile ps6 = ps_outfile s ->
      implM usegs (mret (CH_Ok (mkPcap q f BS BS bq [] sw maj min SS lt EXT 0 0 [] hdr0 (PrivPcap (mkSf HS LS SC))))) ps6 POSTQ
        (MS (mkR ra6 (Z_to_bv 64 (bv_unsigned sp + -96)) gp tp t0' t1' t2' (Z_to_bv 64 ERR) (Z_to_bv 64 EB) (Z_to_bv 64 P) (Z_to_bv 64 B) a2' a3' a4' a5' a6' a7'
                 x2 x3 (Z_to_bv 64 maj) (Z_to_bv 64 (mi + (2^64 - 2^32))) (Z_to_bv 64 P) (Z_to_bv 64 (sxv l0 l1 l2 l3))
                 s8 s9 s10 s11 t3' t4' t5' t6') F (Z_to_bv 64 0x15940) fc None m6 (seg_rom usegs))).
    { intros ra6 t0' t1' t2' a2' a3' a4' a5' a6' a7' x2 x3 t3' t4' t5' t6' m6 ps6 bq B BS HS SS LS SC bjunk e6 HHS HSS HBS MI6 ST6 AG6 G6 BUF CELLS6 FRA6 FRD6 FRS6 ERR6 MG6 HEB6 OF6.
      clear CELLS FRA FRD FRS ERRc MG4 HEB3 MI2 ST3 AG3.
      assert (BSR : (1 <= BS <= 2048)%Z) by (rewrite HBS; destruct (Z.ltb_spec 2048 SS); lia).
      pose proof (GIo_block_ok K _ _ _ _ _ _ G6 ltac:(left; reflexivity)) as (B1 & B2 & B3 & B4 & B5 & B6).
      cbn [cb_addr cb_size fst snd] in B1, B2, B3, B4, B5, B6.
      pose proof (GIo_got_pcap K _ _ _ _ _ G6) as GOT. unfold PK, GOT_PCAP_ADDR, GOT_INSTALL_BPF, GOT_BREAKLOOP in GOT; cbn [pk_oneshot pk_cleanup_sf] in GOT.
      assert (NB6 : forall a, in_block CL a -> ~ (P <= a < P + 664)%Z /\ ~ (B <= a < B + BS)%Z).
      { intros a Ha. split; intros Hin.
        - destruct (GIo_CLc_facts K R ps6 [(bq, B, BS); (q, P, PCAP_SF_TOTAL)] CL FB m6 a G6
                     ltac:(unfold in_block; apply Exists_cons_tl, Exists_cons_hd; cbn [cb_addr cb_size fst snd]; unfold PCAP_SF_TOTAL; lia)) as [_ Hn]. exact (Hn Ha).
        - destruct (GIo_CLc_facts K R ps6 [(bq, B, BS); (q, P, PCAP_SF_TOTAL)] CL FB m6 a G6
                     ltac:(unfold in_block; apply Exists_cons_hd; cbn [cb_addr cb_size fst snd]; lia)) as [_ Hn]. exact (Hn Ha). }
      pose proof (blocks2_apart _ _ _ _ _ _ _ _ _ _ _ G6 ltac:(lia) ltac:(unfold PCAP_SF_TOTAL; lia)) as BP. unfold PCAP_SF_TOTAL in BP.
      pose proof (munch_refl [(P, P + 664)]%Z m6) as MU6. pose proof (wmono_refl usegs m6) as WM6.
      hide HEB6. hide MG6. hide ERR6. hide BUF.
      unfold F_sfpcap_chkA.pcells in CELLS6.
      apply (implM_ret usegs).
      do 3 pstep. step. do 11 step.
      release_frame FRA6 ST6 (bv_unsigned sp + -92)%Z. release_frame FRD6 ST6 (bv_unsigned sp + -72)%Z. release_frame FRS6 ST6 (bv_unsigned sp).
      unhide HEB6. unhide MG6. unhide ERR6. unhide BUF.
      destruct magic as [|k0 [|k1 [|k2 [|k3 [|? ?]]]]]; try discriminate GL. cbn [map] in MG6.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
        assert (AGW : agrees_on (fun a => outside [(P, P + 664)]%Z a) m6 mm) by (eapply agrees_on_of_munch; [exact MU6 | exact WM6 | intros a _ Ho; exact Ho]);
        assert (HEB' : rw_cells usegs mm EB [CB 256 e6])
          by (eapply agrees_rw_cells; [exact AGW | exact HEB6 | intros a Ha; cbn [outside cells_size csize Nat.add] in *; unfold rc_lo in LO; (keep_hyps CEILV sp R lo EB ERR P n0 n1 n2 n3 l0 l1 l2 l3 k0 k1 k2 k3 B a LO BU E1 SPW P4 Ha; lia)]);
        assert (MG' : rw_cells usegs mm MG [CB 4 (map b8 [k0; k1; k2; k3])])
          by (eapply rw_cells_recell; [eapply agrees_rw_cells; [exact AGW | exact MG6 | intros a Ha; cbn [outside cells_size csize Nat.add] in *; unfold rc_lo in LO; (keep_hyps CEILV sp R lo MG EB ERR P n0 n1 n2 n3 l0 l1 l2 l3 k0 k1 k2 k3 B a LO BU R1 R2 SPW P4 Ha; lia)] | cbn; repeat split; exact Logic.I | reflexivity]);
        assert (ERR' : rw_cells usegs mm ERR [C4 z64])
          by (eapply agrees_rw_cells; [exact AGW | exact ERR6 | intros a Ha; cbn [outside cells_size csize Nat.add] in *; unfold rc_lo in LO; (keep_hyps CEILV sp R lo EB ERR P n0 n1 n2 n3 l0 l1 l2 l3 k0 k1 k2 k3 B a LO BU R1 SPW P4 Ha; lia)]);
        assert (BUF' : rw_cells usegs mm B [CB (Z.to_nat BS) bjunk])
          by (eapply agrees_rw_cells; [exact AGW | exact BUF | intros a Ha; cbn [outside cells_size csize Nat.add] in *; (keep_hyps CEILV sp R lo EB ERR P n0 n1 n2 n3 l0 l1 l2 l3 k0 k1 k2 k3 B BS a BP Ha; lia)]);
        assert (G' : GIo K R ps6 ((bq, B, BS) :: (q, P, PCAP_SF_TOTAL) :: CL) FB mm)
          by (eapply (GIo_client_frame K HFL SFL); [exact G6 | exact MU6 | exact WM6 |];
              apply Forall_cons; [right; unfold iv_in_block; apply Exists_cons_tl, Exists_cons_hd; cbn [cb_addr cb_size fst snd]; unfold PCAP_SF_TOTAL; (keep_hyps CEILV sp EB ERR P n0 n1 n2 n3 l0 l1 l2 l3 k0 k1 k2 k3 B; lia)| apply Forall_nil])
      end.
      apply evt_done. subst POSTQ. unfold check_header_post.
      lazymatch goal with |- context [MS _ _ _ _ _ ?mm _] => exists (Z_to_bv 64 P), mm, z64 end.
      split; [unfold hpost_regs; repeat (lazymatch goal with |- ex _ => eexists end); reflexivity|].
      split; [solve [assumption | congruence] |].
      split; [assumption|]. split; [assumption|].
      split. { eapply agrees_on_trans; [exact AG6|]. eapply agrees_on_weaken; [exact AGW|]. intros a [[Ha|Ha] _]; cbn [outside]; [unfold rc_lo in LO; lia|].
               split; [exact (proj1 (NB6 a Ha))| exact Logic.I]. }
      split; [exact MG'|]. split; [exact ERR'|].
      exists P, [(q, P, PCAP_SF_TOTAL); (bq, B, BS)].
      split; [reflexivity|].
      split. { eapply (GIo_perm K HPL); [exact G'|].
               eapply Permutation.Permutation_trans; [apply Permutation.Permutation_cons_append|]. cbn [app].
               replace (CL ++ [(q, P, PCAP_SF_TOTAL); (bq, B, BS)]) with ((CL ++ [(q, P, PCAP_SF_TOTAL)]) ++ [(bq, B, BS)])
                 by (first [now rewrite app_assoc | now rewrite <- app_assoc]).
               change ((q, P, PCAP_SF_TOTAL) :: CL ++ [(bq, B, BS)]) with (((q, P, PCAP_SF_TOTAL) :: CL) ++ [(bq, B, BS)]).
               apply Permutation.Permutation_app_tail. apply Permutation.Permutation_cons_append. }
      split; [| split; [reflexivity| exists e6; exact HEB']].
      exists z8, z8, z8. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
      exists B, 0%Z, blank_junk, [], bjunk.
      destruct (rw_cells_cut _ _ _ 33 CELLS6) as [CP CQ]. cbn [firstn skipn cells_size csize Nat.add] in CP, CQ.
      split; [unfold pcap_blocks, psize, is_ng; cbn [pc_priv pc_self pc_buffer pc_bufalloc]; reflexivity|].
      split. { unfold pcap_cells_gen, pc_pre, hdr_cells, pc_ops, np_entry, cleanup_entry, is_ng, PCAP_PRIV_OFF, PK, F_sfpcap_chkA.blank_junk.
               cbn [app pj_read_op pj_fd pj_a pj_b pj_c pj_d pj_e pj_f pj_g pj_h pj_breakloop pk_next_pcap pk_cleanup_sf
                    pc_priv pc_bufsize pc_break_loop pc_swapped pc_version_major pc_version_minor pc_snapshot pc_linktype pc_linktype_ext
                    pc_tstamp_precision pc_header h_sec h_usec h_caplen h_len hdr0].
               exact CP. }
      split. { unfold priv_cells, PCAP_PRIV_OFF. cbn [pc_priv sf_cells sf_hdrsize sf_lengths_swapped sf_scale_type].
               replace (P + 648)%Z with (P + Z.of_nat 648)%Z by lia. exact CQ. }
      split; [exact BUF'|]. split; [reflexivity|]. split; [reflexivity|].
      unfold pcap_wf. cbn [pc_snapshot pc_bufsize pc_bufalloc pc_bufdata pc_break_loop pc_tstamp_precision pc_version_major pc_version_minor
                            pc_linktype pc_linktype_ext pc_header pc_priv h_caplen h_len hdr0 sf_hdrsize length Z.of_nat].
      unfold INT_MAX. repeat split; try (keep_hyps CEILV sp EB ERR P n0 n1 n2 n3 l0 l1 l2 l3 k0 k1 k2 k3 B SS HSS BS BSR maj Bmaj min Bmin LTR EXR HS HHS; lia). }
    (* [comment removed for export] *)
    assert (K4FAIL : forall (ra6 t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' x2 x3 t3' t4' t5' t6' : word) (m6 : mem) (ps6 : PState H hptr) (e6 : list byte),
      mem_inv usegs m6 -> stk usegs m6 lo (bv_unsigned sp + -96) ->
      agrees_on (fun a => client_keeps CL (bv_unsigned sp) a /\ ~ (EB <= a < EB + 256) /\ ~ (ERR <= a < ERR + 4))%Z m m6 ->
      GIo K R ps6 ((q, P, PCAP_SF_TOTAL) :: CL) FB m6 ->
      rw_cells usegs m6 (bv_unsigned sp + -96) [C4 (Z_to_bv 64 (mi + (2^64 - 2^32)))] ->
      rw_cells usegs m6 (bv_unsigned sp + -92)
        [C2 (Z_to_bv 64 maj); C2 (Z_to_bv 64 min); CB 8 mid; C4 (Z_to_bv 64 (le4val n0 n1 n2 n3)); C4 (Z_to_bv 64 (le4val l0 l1 l2 l3))] ->
      rw_cells usegs m6 (bv_unsigned sp + -72) [C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
      rw_cells usegs m6 ERR [C4 z64] -> rw_cells usegs m6 MG (map (fun z => C1 (Z_to_bv 8 z)) magic) -> rw_cells usegs m6 EB [CB 256 e6] ->
      ps_outfile ps6 = ps_outfile s ->
      implM usegs (mbind (pfree HO q) (fun _ => mret (CH_Err Msg.out_of_memory))) ps6 POSTQ
        (MS (mkR ra6 (Z_to_bv 64 (bv_unsigned sp + -96)) gp tp t0' t1' t2' (Z_to_bv 64 ERR) (Z_to_bv 64 EB) (Z_to_bv 64 P) a1' a2' a3' a4' a5' a6' a7'
                 x2 x3 (Z_to_bv 64 maj) (Z_to_bv 64 (mi + (2^64 - 2^32))) (Z_to_bv 64 P) (Z_to_bv 64 (sxv l0 l1 l2 l3))
                 s8 s9 s10 s11 t3' t4' t5' t6') F (Z_to_bv 64 0x158ec) fc None m6 (seg_rom usegs))).
    { intros ra6 t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' x2 x3 t3' t4' t5' t6' m6 ps6 e6 MI6 ST6 AG6 G6 FRA6 FRD6 FRS6 ERR6 MG6 HEB6 OF6.
      clear CELLS FRA FRD FRS ERRc MG4 HEB3 MI2 ST3 AG3.
      pose proof (rw_cells_bound _ _ _ _ HEB6) as BEB. cbn [cells_size csize Nat.add] in BEB.
      assert (L6 : length e6 = 256%nat) by (destruct HEB6 as [[WF _] _]; cbn in WF; (keep_hyps CEILV sp R MG EB ERR P maj min n0 n1 n2 n3 l0 l1 l2 l3 mi e6 WF; tauto)).
      assert (HEB14 : rw_cells usegs m6 EB [CB 14 (firstn 14 e6); CB 242 (skipn 14 e6)]).
      { eapply rw_cells_recell; [exact HEB6 | cbn; rewrite length_firstn, length_skipn, L6; repeat split; reflexivity |].
        cbn [cells_bytes cbytes]. rewrite !app_nil_r. apply firstn_skipn. }
      destruct (rw_cells_cut _ _ _ 1 HEB14) as [HEBa HEBb]. clear HEB6 HEB14. cbn [firstn skipn cells_size csize Nat.add] in HEBa, HEBb.
      hide HEBb. hide MG6. hide ERR6.
      assert (LENM : length (map b8 Msg.out_of_memory ++ [Z_to_bv 8 0]) = 14%nat) by (vm_compute; reflexivity).
      pose proof (munch_refl [(EB, EB + 14)]%Z m6) as MU6. pose proof (wmono_refl usegs m6) as WM6.
      unfold implM. iprefix. do 6 step.
      call (memcpy_specZ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ EB 0x10df2%Z 14%Z (map b8 Msg.out_of_memory ++ [Z_to_bv 8 0]) (firstn 14 e6));
        [reflexivity | reflexivity | reflexivity
        | exact (ro_cells_bytes_at _ _ _ _ (ro_cells_image usegs m6 0x10df2 (map b8 Msg.out_of_memory ++ [Z_to_bv 8 0]) MI6 ltac:(vm_compute; reflexivity) ltac:((keep_hyps CEILV sp EB ERR magic P n0 n1 n2 n3 l0 l1 l2 l3 e6; lia)) ltac:(rewrite LENM; cbn; (keep_hyps CEILV sp EB ERR magic P n0 n1 n2 n3 l0 l1 l2 l3 e6; lia))))
        | rewrite LENM; reflexivity | (keep_hyps CEILV sp EB ERR magic P n0 n1 n2 n3 l0 l1 l2 l3 e6; lia) | exact HEBa | unfold rc_lo in LO; (keep_hyps CEILV sp R lo EB ERR magic P n0 n1 n2 n3 l0 l1 l2 l3 e6 LO BU E1 SPW; lia) | (keep_hyps CEILV sp EB ERR magic P n0 n1 n2 n3 l0 l1 l2 l3 e6 BEB; lia) | (keep_hyps CEILV sp EB ERR magic P n0 n1 n2 n3 l0 l1 l2 l3 e6; lia) | exact MI6 |].
      unhide HEBb. unhide MG6. unhide ERR6.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
        assert (AGW : agrees_on (fun a => outside [(EB, EB + 14)]%Z a) m6 mm) by (eapply agrees_on_of_munch; [exact MU6 | exact WM6 | intros a _ Ho; exact Ho]);
        assert (G7 : GIo K R ps6 ((q, P, PCAP_SF_TOTAL) :: CL) FB mm)
          by (eapply (GIo_client_frame K HFL SFL); [exact G6 | exact MU6 | exact WM6 |]; apply Forall_cons; [left; cbn [fst snd]; unfold rc_lo; (keep_hyps CEILV sp R lo EB ERR magic P n0 n1 n2 n3 l0 l1 l2 l3 e6 LO BU E1 E2; lia)| apply Forall_nil]);
        assert (HEB7 : rw_cells usegs mm EB [CB 14 (map b8 Msg.out_of_memory ++ [Z_to_bv 8 0]); CB 242 (skipn 14 e6)])
          by (eapply (rw_cells_uncut _ _ _ _ _ ltac:(eassumption));
              [eapply agrees_rw_cells; [exact AGW | exact HEBb | intros a Ha; cbn [outside cells_size csize Nat.add] in *; (keep_hyps CEILV sp EB ERR magic P n0 n1 n2 n3 l0 l1 l2 l3 e6 a Ha; lia)] | cbn; (keep_hyps CEILV sp R lo EB ERR magic P n0 n1 n2 n3 l0 l1 l2 l3 e6; lia)]);
        assert (MG7 : rw_cells usegs mm MG (map (fun z => C1 (Z_to_bv 8 z)) magic))
          by (eapply agrees_rw_cells; [exact AGW | exact MG6 | intros a Ha; rewrite cells_size_map_C1, GL in Ha; cbn [outside]; (keep_hyps CEILV sp R lo MG EB ERR magic P n0 n1 n2 n3 l0 l1 l2 l3 e6 a R2 D1 Ha; lia)]);
        assert (ERR7 : rw_cells usegs mm ERR [C4 z64])
          by (eapply agrees_rw_cells; [exact AGW | exact ERR6 | intros a Ha; cbn [outside cells_size csize Nat.add] in *; (keep_hyps CEILV sp R lo MG EB ERR magic P n0 n1 n2 n3 l0 l1 l2 l3 e6 a R2 D1 Ha; lia)]);
        assert (AG7 : agrees_on (fun a => client_keeps CL (bv_unsigned sp) a /\ ~ (EB <= a < EB + 256) /\ ~ (ERR <= a < ERR + 4))%Z m mm)
          by (eapply agrees_on_trans; [exact AG6|]; eapply agrees_on_weaken; [exact AGW|]; intros a [_ [Hn _]]; cbn [outside]; (keep_hyps CEILV sp EB ERR magic P n0 n1 n2 n3 l0 l1 l2 l3 e6 a Hn; lia))
      end.
      clear AGW HEBb MG6 ERR6 AG6 G6.
      do 2 step.
      (* [comment removed for export] *)
      name_sp sp (-96)%Z.
      apply evt_done. eapply (implM_bind usegs).
      { eapply (FREE _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ []); [| reflexivity].
        split; [exact G7|]. split; [rewrite Hsp; eassumption|]. split; [unfold rc_lo; lia|]. split; [unfold FREE_STACK; rewrite Hsp; lia|].
        split; [rewrite Hsp; lia|]. split; [assumption|]. split; [exact TP| rewrite Hsp; apply aln16_add; [exact ALN| reflexivity]]. }
      intros [] ps7 ms7 PO. cbv beta in PO. destruct PO as (av7 & m7 & E & OF7 & MI7 & ST7 & AGf & Gf).
      unfold hpost_regs in E. destruct_exs E. subst ms7. rewrite Hsp in *. unname_sp.
      replace (ret_pc (Z_to_bv 64 88332)) with (Z_to_bv 64 88332) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
      cbn [app] in AGf, Gf.
      lazymatch goal with |- context [MS _ _ _ _ _ ?mm (seg_rom usegs)] =>
      assert (KEEP : forall A cs, rw_cells usegs _ A cs -> (bv_unsigned sp + -96 <= A)%Z -> rw_cells usegs mm A cs)
        by (intros A cs HC HA; eapply agrees_rw_cells; [exact AGf | exact HC | intros a Ha; left; lia]) end.
      apply KEEP in HEB7; [|lia]. apply KEEP in MG7; [|lia]. apply KEEP in ERR7; [|lia].
      match goal with X1 : rw_cells usegs _ (bv_unsigned sp + -96)%Z _, X2 : rw_cells usegs _ (bv_unsigned sp + -92)%Z _, X3 : rw_cells usegs _ (bv_unsigned sp + -72)%Z _ |- _ =>
        apply KEEP in X1; [|lia]; apply KEEP in X2; [|lia]; apply KEEP in X3; [|lia];
        pose proof (rw_cells_uncut _ _ _ _ _ X1 X2 ltac:(cbn; lia)) as HC24 end.
      apply (implM_ret usegs). step.
      eapply chk_fail with (msg := Msg.out_of_memory);
        [ | exact MI7 | exact ST7 | | exact Gf | exact HC24 | reflexivity | assumption | exact ERR7 | exact MG7 | exact HEB7 | vm_compute; reflexivity
        | apply snprintf_ok; [vm_compute; reflexivity| constructor] | congruence ].
      { split; [exact G|]. repeat (split; [eassumption|]). eassumption. }
      eapply agrees_on_trans; [exact AG7|]. eapply agrees_on_weaken; [exact AGf|]. intros a [[Ha|Ha] _]; [left; lia| right; exact Ha]. }
    (* [comment removed for export] *)
    assert (PKEEP : forall m5, munch [(P, P + 664)]%Z m3 m5 -> wmono usegs m3 m5 ->
              GIo K R ps3 ((q, P, PCAP_SF_TOTAL) :: CL) FB m5
              /\ agrees_on (fun a => client_keeps CL (bv_unsigned sp) a /\ ~ (EB <= a < EB + 256) /\ ~ (ERR <= a < ERR + 4))%Z m m5
              /\ (forall A cs, rw_cells usegs m3 A cs -> (P + 664 <= A)%Z -> rw_cells usegs m5 A cs)
              /\ stk usegs m5 lo (bv_unsigned sp + -96)).
    { intros m5 MU WM.
      split; [eapply (GIo_client_frame K HFL SFL); [exact G3 | exact MU | exact WM |];
              apply Forall_cons; [right; unfold iv_in_block; apply Exists_cons_hd; cbn [cb_addr cb_size fst snd]; unfold PCAP_SF_TOTAL; lia| apply Forall_nil]|].
      split; [eapply agrees_on_trans; [exact AG3|]; eapply agrees_on_of_munch; [exact MU | exact WM |];
              intros a _ [[Ha|Ha] _]; cbn [outside]; [unfold rc_lo in LO; lia| split; [exact (NB a Ha)| exact Logic.I]]|].
      split. { intros A cs HC HA. eapply agrees_rw_cells; [eapply agrees_on_of_munch; [exact MU | exact WM | intros a _ Ho; exact Ho] | exact HC |].
               intros a Ha. cbn [outside]. lia. }
      eapply stk_transport_disjoint; [exact ST3 | exact MU | exact WM | cbn [disjoint_from]; unfold rc_lo in LO; lia]. }
    (* [comment removed for export] *)
    assert (K3A : forall (ra5 t0' t1' t2' a0' a2' a4' a5' a6' a7' x3 t3' t4' t5' t6' : word) (m5 : mem) (HS SS : Z) (LS : lenswap_t) (SC : sf_scale_t),
      (HS = 16 \/ HS = 24)%Z -> (2048 <= SS <= 2147483647)%Z ->
      mem_inv usegs m5 -> munch [(P, P + 664)]%Z m3 m5 -> wmono usegs m3 m5 ->
      rw_cells usegs m5 P (pcells P sw maj min lt EXT (C8 (Z_to_bv 64 88428)) (C4 (Z_to_bv 64 0)) (C8 (Z_to_bv 64 0)) (C4 (Z_to_bv 64 SS))
                             (C8 (Z_to_bv 64 0)) (C8 (Z_to_bv 64 HS)) (C4 (Z_to_bv 64 (lenswap_code LS))) (C4 (Z_to_bv 64 (sfscale_code SC)))) ->
      implM usegs (chk_buf_model MOps (prims HO fo_nop sites) q f 0 sw maj min lt EXT HS SS LS SC) ps3 POSTQ
        (MS (mkR ra5 (Z_to_bv 64 (bv_unsigned sp + -96)) gp tp t0' t1' t2' (Z_to_bv 64 ERR) (Z_to_bv 64 EB) a0' (Z_to_bv 64 2048) a2' (Z_to_bv 64 P) a4' a5' a6' a7'
                 z64 x3 (Z_to_bv 64 maj) (Z_to_bv 64 (mi + (2^64 - 2^32))) (Z_to_bv 64 P) (Z_to_bv 64 (sxv l0 l1 l2 l3))
                 s8 s9 s10 s11 t3' t4' t5' t6') F (Z_to_bv 64 0x158d0) fc None m5 (seg_rom usegs))).
    { intros ra5 t0' t1' t2' a0' a2' a4' a5' a6' a7' x3 t3' t4' t5' t6' m5 HS SS LS SC HHS HSS MI5 MU5 WM5 CELLS5.
      destruct (PKEEP m5 MU5 WM5) as (G5 & AG5 & _ & ST5).
      clear CELLS MI2.
      unfold chk_buf_model. cbn [e_fenter e_fret fo_enter fo_ret fo_nop prims]. replace (if 2048 <? SS then 2048 else SS)%Z with 2048%Z by (destruct (Z.ltb_spec 2048 SS); lia).
      cbn [mo_bind mo_ret MOps e_fenter e_fret fo_enter fo_ret fo_nop prims e_malloc e_free prims].
      unfold F_sfpcap_chkA.pcells in CELLS5.
      unfold implM. iprefix. step. pstep. step.
      destruct (PKEEP _ MU5 WM5) as (G5' & AG5' & KEEP5 & _). clear G5 AG5.
      pose proof (KEEP5 _ _ FRA ltac:(unfold rc_lo in LO; lia)) as FRA5. pose proof (KEEP5 _ _ FRD ltac:(unfold rc_lo in LO; lia)) as FRD5.
      pose proof (KEEP5 _ _ FRS ltac:(unfold rc_lo in LO; lia)) as FRS5. pose proof (KEEP5 _ _ ERRc ltac:(unfold rc_lo in LO; lia)) as ERR5.
      pose proof (KEEP5 _ _ MG4 ltac:(unfold rc_lo in LO; lia)) as MG5. pose proof (KEEP5 _ _ HEB3 ltac:(unfold rc_lo in LO; lia)) as HEB5.
      clear KEEP5.
      name_sp sp (-96)%Z.
      apply evt_done. eapply (implM_bind usegs).
      { eapply MALLOC; [| reflexivity | lia].
        split; [exact G5'|]. split; [rewrite Hsp; eassumption|]. split; [unfold rc_lo; lia|]. split; [unfold MALLOC_STACK; rewrite Hsp; lia|].
        split; [rewrite Hsp; lia|]. split; [assumption|]. split; [exact TP| rewrite Hsp; apply aln16_add; [exact ALN| reflexivity]]. }
      intros [bq|] ps6 ms6 PO; cbv beta iota in PO.
      - destruct PO as (av & m6 & E & OFm & MI6 & ST6 & AG6 & (B & bjunk & -> & G6 & BUF)).
        assert (OF6 : ps_outfile ps6 = ps_outfile s) by congruence.
        unfold hpost_regs in E. destruct_exs E. subst ms6. rewrite Hsp in *. unname_sp.
        replace (ret_pc (Z_to_bv 64 88284)) with (Z_to_bv 64 88284) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
        pose proof (GIo_block_ok K _ _ _ _ _ _ G6 ltac:(left; reflexivity)) as (B1 & _ & _ & B4 & _). cbn [cb_addr cb_size fst snd] in B1, B4.
        lazymatch type of AG6 with agrees_on _ ?ma _ =>
        assert (KEEP6 : forall A cs, rw_cells usegs ma A cs -> (bv_unsigned sp + -96 <= A \/ (P <= A /\ A + Z.of_nat (cells_size cs) <= P + 664))%Z -> rw_cells usegs m6 A cs) end.
        { intros A cs HC HA. eapply agrees_rw_cells; [exact AG6 | exact HC |]. intros a Ha. destruct HA as [HA|HA]; [left; lia| right].
          unfold in_block. apply Exists_cons_hd. cbn [cb_addr cb_size fst snd]. unfold PCAP_SF_TOTAL. lia. }
        apply KEEP6 in CELLS5; [|cbn [cells_size csize Nat.add]; lia]. apply KEEP6 in FRA5; [|lia]. apply KEEP6 in FRD5; [|lia]. apply KEEP6 in FRS5; [|lia].
        apply KEEP6 in ERR5; [|lia]. apply KEEP6 in MG5; [|lia]. apply KEEP6 in HEB5; [|lia].
        assert (AG06 : agrees_on (fun a => client_keeps CL (bv_unsigned sp) a /\ ~ (EB <= a < EB + 256) /\ ~ (ERR <= a < ERR + 4))%Z m m6).
        { eapply agrees_on_trans; [exact AG5'|]. eapply agrees_on_weaken; [exact AG6|]. intros a [[Ha|Ha] _]; [left; lia| right].
          unfold in_block. apply Exists_cons_tl. exact Ha. }
        clear KEEP6 AG6 AG5' G5'.
        pose proof (blocks2_apart _ _ _ _ _ _ _ _ _ _ _ G6 ltac:(lia) ltac:(unfold PCAP_SF_TOTAL; lia)) as BP. unfold PCAP_SF_TOTAL in BP.
        pose proof (munch_refl [(P, P + 664)]%Z m6) as MU6. pose proof (wmono_refl usegs m6) as WM6.
        hide BUF. unfold implM. iprefix. step. step. step. step. if_cases Kb; [ idtac | try (zify_cond Kb; exfalso; (keep_hyps CEILV sp EB ERR magic P n0 n1 n2 n3 l0 l1 l2 l3 B B1 Kb; lia)) ].
        unhide BUF.
        lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
          assert (AGW : agrees_on (fun a => outside [(P, P + 664)]%Z a) m6 mm) by (eapply agrees_on_of_munch; [exact MU6 | exact WM6 | intros a _ Ho; exact Ho]);
          apply (agrees_rw_cells _ _ _ _ _ AGW) in BUF; [| intros a Ha; cbn [outside cells_size csize Nat.add] in *; (keep_hyps CEILV sp R lo EB ERR magic P n0 n1 n2 n3 l0 l1 l2 l3 B a BP Ha; lia)];
          assert (G6' : GIo K R ps6 ((bq, B, _) :: (q, P, PCAP_SF_TOTAL) :: CL) FB mm)
            by (eapply (GIo_client_frame K HFL SFL); [exact G6 | exact MU6 | exact WM6 |];
                apply Forall_cons; [right; unfold iv_in_block; apply Exists_cons_tl, Exists_cons_hd; cbn [cb_addr cb_size fst snd]; unfold PCAP_SF_TOTAL; (keep_hyps CEILV sp EB ERR magic P n0 n1 n2 n3 l0 l1 l2 l3; lia)| apply Forall_nil]);
          assert (AG6' : agrees_on (fun a => client_keeps CL (bv_unsigned sp) a /\ ~ (EB <= a < EB + 256) /\ ~ (ERR <= a < ERR + 4))%Z m mm)
            by (eapply agrees_on_trans; [exact AG06|]; eapply agrees_on_weaken; [exact AGW|];
                intros a [[Ha|Ha] _]; cbn [outside]; [unfold rc_lo in LO; (keep_hyps CEILV sp R lo EB ERR magic P n0 n1 n2 n3 l0 l1 l2 l3 a LO BU SPW P4 Ha; lia)| split; [exact (NB a Ha)| exact Logic.I]])
        end.
        apply evt_done. eapply K4OK; try eassumption.
        { lia. }
        { destruct (Z.ltb_spec 2048 SS); lia. }
      - destruct PO as (av & m6 & E & OFm & MI6 & ST6 & AG6 & -> & G6 & EN6).
        assert (OF6 : ps_outfile ps6 = ps_outfile s) by congruence.
        unfold hpost_regs in E. destruct_exs E. subst ms6. rewrite Hsp in *. unname_sp.
        replace (ret_pc (Z_to_bv 64 88284)) with (Z_to_bv 64 88284) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
        lazymatch type of AG6 with agrees_on _ ?ma _ =>
        assert (KEEP6 : forall A cs, rw_cells usegs ma A cs -> (bv_unsigned sp + -96 <= A \/ (P <= A /\ A + Z.of_nat (cells_size cs) <= P + 664))%Z -> rw_cells usegs m6 A cs) end.
        { intros A cs HC HA. eapply agrees_rw_cells; [exact AG6 | exact HC |]. intros a Ha. destruct HA as [HA|HA]; [left; lia| right].
          unfold in_block. apply Exists_cons_hd. cbn [cb_addr cb_size fst snd]. unfold PCAP_SF_TOTAL. lia. }
        apply KEEP6 in CELLS5; [|cbn [cells_size csize Nat.add]; lia]. apply KEEP6 in FRA5; [|lia]. apply KEEP6 in FRD5; [|lia]. apply KEEP6 in FRS5; [|lia].
        apply KEEP6 in ERR5; [|lia]. apply KEEP6 in MG5; [|lia]. apply KEEP6 in HEB5; [|lia].
        assert (AG06 : agrees_on (fun a => client_keeps CL (bv_unsigned sp) a /\ ~ (EB <= a < EB + 256) /\ ~ (ERR <= a < ERR + 4))%Z m m6).
        { eapply agrees_on_trans; [exact AG5'|]. eapply agrees_on_weaken; [exact AG6|]. intros a [[Ha|Ha] _]; [left; lia| right].
          unfold in_block. apply Exists_cons_tl. exact Ha. }
        clear KEEP6 AG6 AG5' G5'.
        pose proof (munch_refl [(P, P + 664)]%Z m6) as MU6. pose proof (wmono_refl usegs m6) as WM6.
        unfold implM. iprefix. step. step. pstep. step.
        lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
          assert (AGW : agrees_on (fun a => outside [(P, P + 664)]%Z a) m6 mm) by (eapply agrees_on_of_munch; [exact MU6 | exact WM6 | intros a _ Ho; exact Ho]);
          assert (G6' : GIo K R ps6 ((q, P, PCAP_SF_TOTAL) :: CL) FB mm)
            by (eapply (GIo_client_frame K HFL SFL); [exact G6 | exact MU6 | exact WM6 |];
                apply Forall_cons; [right; unfold iv_in_block; apply Exists_cons_hd; cbn [cb_addr cb_size fst snd]; unfold PCAP_SF_TOTAL; lia| apply Forall_nil]);
          assert (AG6' : agrees_on (fun a => client_keeps CL (bv_unsigned sp) a /\ ~ (EB <= a < EB + 256) /\ ~ (ERR <= a < ERR + 4))%Z m mm)
            by (eapply agrees_on_trans; [exact AG06|]; eapply agrees_on_weaken; [exact AGW|];
                intros a [[Ha|Ha] _]; cbn [outside]; [unfold rc_lo in LO; lia| split; [exact (NB a Ha)| exact Logic.I]])
        end.
        apply evt_done. eapply K4FAIL; try eassumption. }
    (* [comment removed for export] *)
    assert (K3B : forall (ra5 t0' t1' t2' a1' a2' a4' a5' a6' a7' x3 t3' t4' t5' t6' : word) (m5 : mem) (HS SS : Z) (LS : lenswap_t) (SC : sf_scale_t),
      (HS = 16 \/ HS = 24)%Z -> (1 <= SS < 2048)%Z ->
      mem_inv usegs m5 -> munch [(P, P + 664)]%Z m3 m5 -> wmono usegs m3 m5 ->
      rw_cells usegs m5 P (pcells P sw maj min lt EXT (C8 (Z_to_bv 64 88428)) (C4 (Z_to_bv 64 0)) (C8 (Z_to_bv 64 0)) (C4 (Z_to_bv 64 SS))
                             (C8 (Z_to_bv 64 0)) (C8 (Z_to_bv 64 HS)) (C4 (Z_to_bv 64 (lenswap_code LS))) (C4 (Z_to_bv 64 (sfscale_code SC)))) ->
      implM usegs (chk_buf_model MOps (prims HO fo_nop sites) q f 0 sw maj min lt EXT HS SS LS SC) ps3 POSTQ
        (MS (mkR ra5 (Z_to_bv 64 (bv_unsigned sp + -96)) gp tp t0' t1' t2' (Z_to_bv 64 ERR) (Z_to_bv 64 EB) (Z_to_bv 64 SS) a1' a2' (Z_to_bv 64 P) a4' a5' a6' a7'
                 z64 x3 (Z_to_bv 64 maj) (Z_to_bv 64 (mi + (2^64 - 2^32))) (Z_to_bv 64 P) (Z_to_bv 64 (sxv l0 l1 l2 l3))
                 s8 s9 s10 s11 t3' t4' t5' t6') F (Z_to_bv 64 0x15928) fc None m5 (seg_rom usegs))).
    { intros ra5 t0' t1' t2' a1' a2' a4' a5' a6' a7' x3 t3' t4' t5' t6' m5 HS SS LS SC HHS HSS MI5 MU5 WM5 CELLS5.
      destruct (PKEEP m5 MU5 WM5) as (G5 & AG5 & _ & ST5).
      clear CELLS MI2.
      unfold chk_buf_model. cbn [e_fenter e_fret fo_enter fo_ret fo_nop prims]. replace (if 2048 <? SS then 2048 else SS)%Z with SS by (destruct (Z.ltb_spec 2048 SS); lia).
      cbn [mo_bind mo_ret MOps e_fenter e_fret fo_enter fo_ret fo_nop prims e_malloc e_free prims].
      unfold F_sfpcap_chkA.pcells in CELLS5.
      unfold implM. iprefix. step. step.
      destruct (PKEEP _ MU5 WM5) as (G5' & AG5' & KEEP5 & _). clear G5 AG5.
      pose proof (KEEP5 _ _ FRA ltac:(unfold rc_lo in LO; lia)) as FRA5. pose proof (KEEP5 _ _ FRD ltac:(unfold rc_lo in LO; lia)) as FRD5.
      pose proof (KEEP5 _ _ FRS ltac:(unfold rc_lo in LO; lia)) as FRS5. pose proof (KEEP5 _ _ ERRc ltac:(unfold rc_lo in LO; lia)) as ERR5.
      pose proof (KEEP5 _ _ MG4 ltac:(unfold rc_lo in LO; lia)) as MG5. pose proof (KEEP5 _ _ HEB3 ltac:(unfold rc_lo in LO; lia)) as HEB5.
      clear KEEP5.
      name_sp sp (-96)%Z.
      apply evt_done. eapply (implM_bind usegs).
      { eapply MALLOC; [| reflexivity | lia].
        split; [exact G5'|]. split; [rewrite Hsp; eassumption|]. split; [unfold rc_lo; lia|]. split; [unfold MALLOC_STACK; rewrite Hsp; lia|].
        split; [rewrite Hsp; lia|]. split; [assumption|]. split; [exact TP| rewrite Hsp; apply aln16_add; [exact ALN| reflexivity]]. }
      intros [bq|] ps6 ms6 PO; cbv beta iota in PO.
      - destruct PO as (av & m6 & E & OFm & MI6 & ST6 & AG6 & (B & bjunk & -> & G6 & BUF)).
        assert (OF6 : ps_outfile ps6 = ps_outfile s) by congruence.
        unfold hpost_regs in E. destruct_exs E. subst ms6. rewrite Hsp in *. unname_sp.
        replace (ret_pc (Z_to_bv 64 88368)) with (Z_to_bv 64 88368) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
        pose proof (GIo_block_ok K _ _ _ _ _ _ G6 ltac:(left; reflexivity)) as (B1 & _ & _ & B4 & _). cbn [cb_addr cb_size fst snd] in B1, B4.
        lazymatch type of AG6 with agrees_on _ ?ma _ =>
        assert (KEEP6 : forall A cs, rw_cells usegs ma A cs -> (bv_unsigned sp + -96 <= A \/ (P <= A /\ A + Z.of_nat (cells_size cs) <= P + 664))%Z -> rw_cells usegs m6 A cs) end.
        { intros A cs HC HA. eapply agrees_rw_cells; [exact AG6 | exact HC |]. intros a Ha. destruct HA as [HA|HA]; [left; lia| right].
          unfold in_block. apply Exists_cons_hd. cbn [cb_addr cb_size fst snd]. unfold PCAP_SF_TOTAL. lia. }
        apply KEEP6 in CELLS5; [|cbn [cells_size csize Nat.add]; lia]. apply KEEP6 in FRA5; [|lia]. apply KEEP6 in FRD5; [|lia]. apply KEEP6 in FRS5; [|lia].
        apply KEEP6 in ERR5; [|lia]. apply KEEP6 in MG5; [|lia]. apply KEEP6 in HEB5; [|lia].
        assert (AG06 : agrees_on (fun a => client_keeps CL (bv_unsigned sp) a /\ ~ (EB <= a < EB + 256) /\ ~ (ERR <= a < ERR + 4))%Z m m6).
        { eapply agrees_on_trans; [exact AG5'|]. eapply agrees_on_weaken; [exact AG6|]. intros a [[Ha|Ha] _]; [left; lia| right].
          unfold in_block. apply Exists_cons_tl. exact Ha. }
        clear KEEP6 AG6 AG5' G5'.
        pose proof (blocks2_apart _ _ _ _ _ _ _ _ _ _ _ G6 ltac:(lia) ltac:(unfold PCAP_SF_TOTAL; lia)) as BP. unfold PCAP_SF_TOTAL in BP.
        pose proof (munch_refl [(P, P + 664)]%Z m6) as MU6. pose proof (wmono_refl usegs m6) as WM6.
        hide BUF. unfold implM. iprefix. step. step. step. step. if_cases Kb; [ try (zify_cond Kb; exfalso; (keep_hyps CEILV sp EB ERR magic P n0 n1 n2 n3 l0 l1 l2 l3 B B1 Kb; lia)) | idtac ].
        unhide BUF.
        lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
          assert (AGW : agrees_on (fun a => outside [(P, P + 664)]%Z a) m6 mm) by (eapply agrees_on_of_munch; [exact MU6 | exact WM6 | intros a _ Ho; exact Ho]);
          apply (agrees_rw_cells _ _ _ _ _ AGW) in BUF; [| intros a Ha; cbn [outside cells_size csize Nat.add] in *; (keep_hyps CEILV sp R lo EB ERR magic P n0 n1 n2 n3 l0 l1 l2 l3 SS B a BP Ha; lia)];
          assert (G6' : GIo K R ps6 ((bq, B, _) :: (q, P, PCAP_SF_TOTAL) :: CL) FB mm)
            by (eapply (GIo_client_frame K HFL SFL); [exact G6 | exact MU6 | exact WM6 |];
                apply Forall_cons; [right; unfold iv_in_block; apply Exists_cons_tl, Exists_cons_hd; cbn [cb_addr cb_size fst snd]; unfold PCAP_SF_TOTAL; (keep_hyps CEILV sp EB ERR magic P n0 n1 n2 n3 l0 l1 l2 l3; lia)| apply Forall_nil]);
          assert (AG6' : agrees_on (fun a => client_keeps CL (bv_unsigned sp) a /\ ~ (EB <= a < EB + 256) /\ ~ (ERR <= a < ERR + 4))%Z m mm)
            by (eapply agrees_on_trans; [exact AG06|]; eapply agrees_on_weaken; [exact AGW|];
                intros a [[Ha|Ha] _]; cbn [outside]; [unfold rc_lo in LO; (keep_hyps CEILV sp R lo EB ERR magic P n0 n1 n2 n3 l0 l1 l2 l3 a LO BU SPW P4 Ha; lia)| split; [exact (NB a Ha)| exact Logic.I]])
        end.
        apply evt_done. eapply K4OK; try eassumption.
        { lia. }
        { destruct (Z.ltb_spec 2048 SS); lia. }
      - destruct PO as (av & m6 & E & OFm & MI6 & ST6 & AG6 & -> & G6 & EN6).
        assert (OF6 : ps_outfile ps6 = ps_outfile s) by congruence.
        unfold hpost_regs in E. destruct_exs E. subst ms6. rewrite Hsp in *. unname_sp.
        replace (ret_pc (Z_to_bv 64 88368)) with (Z_to_bv 64 88368) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
        lazymatch type of AG6 with agrees_on _ ?ma _ =>
        assert (KEEP6 : forall A cs, rw_cells usegs ma A cs -> (bv_unsigned sp + -96 <= A \/ (P <= A /\ A + Z.of_nat (cells_size cs) <= P + 664))%Z -> rw_cells usegs m6 A cs) end.
        { intros A cs HC HA. eapply agrees_rw_cells; [exact AG6 | exact HC |]. intros a Ha. destruct HA as [HA|HA]; [left; lia| right].
          unfold in_block. apply Exists_cons_hd. cbn [cb_addr cb_size fst snd]. unfold PCAP_SF_TOTAL. lia. }
        apply KEEP6 in CELLS5; [|cbn [cells_size csize Nat.add]; lia]. apply KEEP6 in FRA5; [|lia]. apply KEEP6 in FRD5; [|lia]. apply KEEP6 in FRS5; [|lia].
        apply KEEP6 in ERR5; [|lia]. apply KEEP6 in MG5; [|lia]. apply KEEP6 in HEB5; [|lia].
        assert (AG06 : agrees_on (fun a => client_keeps CL (bv_unsigned sp) a /\ ~ (EB <= a < EB + 256) /\ ~ (ERR <= a < ERR + 4))%Z m m6).
        { eapply agrees_on_trans; [exact AG5'|]. eapply agrees_on_weaken; [exact AG6|]. intros a [[Ha|Ha] _]; [left; lia| right].
          unfold in_block. apply Exists_cons_tl. exact Ha. }
        clear KEEP6 AG6 AG5' G5'.
        pose proof (munch_refl [(P, P + 664)]%Z m6) as MU6. pose proof (wmono_refl usegs m6) as WM6.
        unfold implM. iprefix. step. step. pstep. step.
        lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
          assert (AGW : agrees_on (fun a => outside [(P, P + 664)]%Z a) m6 mm) by (eapply agrees_on_of_munch; [exact MU6 | exact WM6 | intros a _ Ho; exact Ho]);
          assert (G6' : GIo K R ps6 ((q, P, PCAP_SF_TOTAL) :: CL) FB mm)
            by (eapply (GIo_client_frame K HFL SFL); [exact G6 | exact MU6 | exact WM6 |];
                apply Forall_cons; [right; unfold iv_in_block; apply Exists_cons_hd; cbn [cb_addr cb_size fst snd]; unfold PCAP_SF_TOTAL; lia| apply Forall_nil]);
          assert (AG6' : agrees_on (fun a => client_keeps CL (bv_unsigned sp) a /\ ~ (EB <= a < EB + 256) /\ ~ (ERR <= a < ERR + 4))%Z m mm)
            by (eapply agrees_on_trans; [exact AG06|]; eapply agrees_on_weaken; [exact AGW|];
                intros a [[Ha|Ha] _]; cbn [outside]; [unfold rc_lo in LO; lia| split; [exact (NB a Ha)| exact Logic.I]])
        end.
        apply evt_done. eapply K4FAIL; try eassumption. }
    (* [comment removed for export] *)
    assert (K2 : forall (ra5 t0' t1' t2' a4' a5' a6' a7' x3 t3' t4' t5' t6' : word) (m5 : mem) (LS : lenswap_t) (SC : sf_scale_t),
      mem_inv usegs m5 -> munch [(P, P + 664)]%Z m3 m5 -> wmono usegs m3 m5 ->
      rw_cells usegs m5 P (pcells P sw maj min lt EXT (C8 (Z_to_bv 64 88428)) (C4 (Z_to_bv 64 0)) (C8 (Z_to_bv 64 0)) (C4 (Z_to_bv 64 snap))
                             (C8 (Z_to_bv 64 0)) (C8 (Z_to_bv 64 0)) (C4 (Z_to_bv 64 0)) (C4 (Z_to_bv 64 (sfscale_code SC)))) ->
      implM usegs (chk_sf_model MOps (prims HO fo_nop sites) q f 0 mi sw maj min lt EXT snap LS SC) ps3 POSTQ
        (MS (mkR ra5 (Z_to_bv 64 (bv_unsigned sp + -96)) gp tp t0' t1' t2' (Z_to_bv 64 ERR) (Z_to_bv 64 EB) (Z_to_bv 64 snap) (Z_to_bv 64 (P + 648)) (Z_to_bv 64 (lenswap_code LS)) (Z_to_bv 64 P) a4' a5' a6' a7'
                 z64 x3 (Z_to_bv 64 maj) (Z_to_bv 64 (mi + (2^64 - 2^32))) (Z_to_bv 64 P) (Z_to_bv 64 (sxv l0 l1 l2 l3))
                 s8 s9 s10 s11 t3' t4' t5' t6') F (Z_to_bv 64 0x15874) fc None m5 (seg_rom usegs))).
    { intros ra5 t0' t1' t2' a4' a5' a6' a7' x3 t3' t4' t5' t6' m5 LS SC MI5 MU5 WM5 CELLS5.
      clear CELLS MI2. unfold chk_sf_model. cbn [e_fenter e_fret fo_enter fo_ret fo_nop prims]. unfold F_sfpcap_chkA.pcells in CELLS5.
      hide FRA. hide FRD. hide FRS. hide ERRc. hide MG4. hide HEB3.
      unfold implM. iprefix. pstep. step. step. step. rewrite (and7_aligned (P + 648)) by lia.
      destruct (Z.eq_dec mi KUZNETZOV_TCPDUMP_MAGIC) as [EK|NK].
      - (* [comment removed for export] *)
        subst mi. rewrite Z.eqb_refl.
        step. lit_branch. step. if_false. step. rewrite (sx32_small lt) by lia. do 2 step. pstep.
        destruct (Z.eq_dec lt 1) as [EL1|EL1].
        + replace (lt =? DLT_EN10MB) with true by (unfold DLT_EN10MB; symmetry; apply Z.eqb_eq; lia). cbv iota.
          step. if_cases Kd; [ try (zify_cond Kd; exfalso; (keep_hyps CEILV EL1 Kd; lia)) | idtac ]. do 2 step.
          destruct (Z.le_gt_cases snap 2147483633) as [S1|S1].
          * replace (snap <=? INT_MAX - 14) with true by (unfold INT_MAX; symmetry; apply Z.leb_le; lia). cbv iota.
            step. if_cases Ks; [ try (zify_cond Ks; rewrite ?signed_lit_small in Ks by (keep_hyps CEILV sp EB ERR magic P n0 n1 n2 n3 l0 l1 l2 l3 SNR; lia); exfalso; (keep_hyps CEILV sp EB ERR magic P n0 n1 n2 n3 l0 l1 l2 l3 S1 Ks; lia)) | idtac ].
            step. rewrite (addiw_small snap 14) by lia.
            step. do 2 step.
            destruct (Z.lt_ge_cases (snap + 14) 2048) as [S2|S2].
            -- step. if_cases Kt; [ idtac | try (zify_cond Kt; exfalso; (keep_hyps CEILV sp EB ERR magic P n0 n1 n2 n3 l0 l1 l2 l3 S2 Kt; lia)) ].
               apply evt_done. eapply K3B; [right; reflexivity | lia | assumption | exact MU5 | exact WM5 | exact CELLS5].
            -- step. if_cases Kt; [ try (zify_cond Kt; exfalso; (keep_hyps CEILV sp EB ERR magic P n0 n1 n2 n3 l0 l1 l2 l3 S2 Kt; lia)) | idtac ]. step.
               apply evt_done. eapply K3A; [right; reflexivity | lia | assumption | exact MU5 | exact WM5 | exact CELLS5].
          * replace (snap <=? INT_MAX - 14) with false by (unfold INT_MAX; symmetry; apply Z.leb_gt; lia). cbv iota.
            step. if_cases Ks; [ idtac | try (zify_cond Ks; rewrite ?signed_lit_small in Ks by (keep_hyps CEILV sp EB ERR magic P n0 n1 n2 n3 l0 l1 l2 l3 SNR; lia); exfalso; (keep_hyps CEILV sp EB ERR magic P n0 n1 n2 n3 l0 l1 l2 l3 S1 Ks; lia)) ].
            step. pstep. do 2 step. step. if_false. step.
            apply evt_done. eapply K3A; [right; reflexivity | unfold INT_MAX; lia | assumption | exact MU5 | exact WM5 | exact CELLS5].
        + replace (lt =? DLT_EN10MB) with false by (unfold DLT_EN10MB; symmetry; apply Z.eqb_neq; lia). cbv iota.
          step. if_cases Kd; [ idtac | try (zify_cond Kd; exfalso; (keep_hyps CEILV EL1 Kd; lia)) ]. do 2 step.
          destruct (Z.lt_ge_cases snap 2048) as [S2|S2].
          * step. if_cases Kt; [ idtac | try (zify_cond Kt; exfalso; (keep_hyps CEILV sp EB ERR magic P n0 n1 n2 n3 l0 l1 l2 l3 S2 Kt; lia)) ].
            apply evt_done. eapply K3B; [right; reflexivity | lia | assumption | exact MU5 | exact WM5 | exact CELLS5].
          * step. if_cases Kt; [ try (zify_cond Kt; exfalso; (keep_hyps CEILV sp EB ERR magic P n0 n1 n2 n3 l0 l1 l2 l3 S2 Kt; lia)) | idtac ].
            apply evt_done. eapply K3A; [right; reflexivity | lia | assumption | exact MU5 | exact WM5 | exact CELLS5].
      - replace (mi =? KUZNETZOV_TCPDUMP_MAGIC) with false by (symmetry; apply Z.eqb_neq; exact NK). cbv iota.
        unfold KUZNETZOV_TCPDUMP_MAGIC in NK.
        step. if_cases Km; [ idtac | try (zify_cond Km; exfalso; (keep_hyps CEILV sp R lo EB ERR magic P n0 n1 n2 n3 l0 l1 l2 l3 mi NK Km; lia)) ].
        step. if_false. step. pstep. do 2 step.
        destruct (Z.lt_ge_cases snap 2048) as [S2|S2].
        + step. if_cases Kt; [ try (zify_cond Kt; exfalso; (keep_hyps CEILV sp EB ERR magic P n0 n1 n2 n3 l0 l1 l2 l3 S2 Kt; lia)) | idtac ].
          apply evt_done. eapply K3B; [left; reflexivity | lia | assumption | exact MU5 | exact WM5 | exact CELLS5].
        + step. if_cases Kt; [ idtac | try (zify_cond Kt; exfalso; (keep_hyps CEILV sp EB ERR magic P n0 n1 n2 n3 l0 l1 l2 l3 S2 Kt; lia)) ].
          apply evt_done. eapply K3A; [left; reflexivity | lia | assumption | exact MU5 | exact WM5 | exact CELLS5]. }
    (* [comment removed for export] *)
    pose proof (munch_refl [(P, P + 664)]%Z m3) as MU3. pose proof (wmono_refl usegs m3) as WM3.
    hide HEB3. hide MG4. hide ERRc.
    unfold implM. iprefix.
    step. rewrite (and7_aligned P) by lia. step. if_false.
    pstep. pstep. pstep. step. step.
    rewrite (lt16_word l0 l1 l2 l3) by lia. do 3 step.
    (* [comment removed for export] *)
    eapply evt_cut.
    { eapply linktype_to_dlt_proof; [eassumption | reflexivity | lia]. }
    cbv beta. intros ms' PO. destruct PO as (y0 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & y8 & y9 & y10 & y11 & y12 & y13 & y14 & -> & ->).
    replace (ret_pc (Z_to_bv 64 87860)) with (Z_to_bv 64 87860) by (symmetry; apply ret_pc_even; [lia|reflexivity]). fold lt.
    do 3 step. rewrite (ltext_word l0 l1 l2 l3) by lia. fold EXT.
    rewrite (sx32_s32 (le4val n0 n1 n2 n3)) by (unfold le4val; lia).
    pstep. pstep. step.
    (* [comment removed for export] *)
    eapply evt_cut.
    { eapply adjust_snapshot_proof; [reflexivity | lia | reflexivity | unfold le4val; lia]. }
    cbv beta. intros ms' PO. destruct PO as (w0 & w1 & w2 & w3 & w4 & w5 & w6 & w7 & w8 & w9 & w10 & w11 & w12 & w13 & w14 & -> & ->).
    replace (ret_pc (Z_to_bv 64 87884)) with (Z_to_bv 64 87884) by (symmetry; apply ret_pc_even; [lia|reflexivity]). fold snap.
    do 8 pstep. step. if_false. step. if_false.
    (* [comment removed for export] *)
    step. if_false_by (eqz_false (P + 648) ltac:(lia)). step. rewrite (and7_aligned (P + 648)) by lia. step. if_false.
    step. step. step. step. rewrite (seqz_xor_lit (mi + (2^64 - 2^32)) 18446744072127396941) by lia.
    destruct (Z.eq_dec mi NSEC_TCPDUMP_MAGIC) as [EN|NN].
    - subst mi. rewrite Z.eqb_refl. replace (NSEC_TCPDUMP_MAGIC + (2 ^ 64 - 2 ^ 32) =? 18446744072127396941)%Z with true by (vm_compute; reflexivity). cbv iota.
      step. step. step. pstep.
      destruct (Z.eq_dec maj 543) as [M543|M543].
      + replace (maj =? 2) with false by (symmetry; apply Z.eqb_neq; lia). replace (maj =? 543) with true by (symmetry; apply Z.eqb_eq; lia). cbv iota.
        step. if_cases Kc; [ idtac | try (zify_cond Kc; exfalso; (keep_hyps CEILV M543 Kc; lia)) ].
        step. rewrite (and7_aligned (P + 648)) by lia. step. if_false. step. step.
        apply evt_done. eapply K2; [assumption | exact MU3 | exact WM3 | exact CELLS].
      + replace (maj =? 543) with false by (symmetry; apply Z.eqb_neq; lia).
        step. if_cases Kc; [ try (zify_cond Kc; exfalso; (keep_hyps CEILV M543 Kc; lia)) | idtac ]. step.
        destruct (Z.eq_dec maj 2) as [M2|M2].
        * replace (maj =? 2) with true by (symmetry; apply Z.eqb_eq; lia). cbv iota.
          step. if_cases Kc2; [ try (zify_cond Kc2; exfalso; (keep_hyps CEILV M2 Kc2; lia)) | idtac ].
          destruct (Z.lt_ge_cases 2 min) as [Mn|Mn].
          -- step. if_cases Kc3; [ idtac | try (zify_cond Kc3; exfalso; (keep_hyps CEILV sp EB ERR magic P min n0 n1 n2 n3 l0 l1 l2 l3 Mn Kc3; lia)) ].
             step. rewrite (and7_aligned (P + 648)) by lia. step. if_false. step. step. rewrite (seqz_lit (min + -3)) by lia.
             destruct (Z.eq_dec min 3) as [M3|M3].
             ++ replace (min <? 3) with false by (symmetry; apply Z.ltb_ge; lia). replace (min =? 3) with true by (symmetry; apply Z.eqb_eq; lia).
                replace (min + -3 =? 0)%Z with true by (symmetry; apply Z.eqb_eq; lia). cbv iota.
                step.
                apply evt_done. eapply K2; [assumption | exact MU3 | exact WM3 | exact CELLS].
             ++ replace (min <? 3) with false by (symmetry; apply Z.ltb_ge; lia). replace (min =? 3) with false by (symmetry; apply Z.eqb_neq; lia).
                replace (min + -3 =? 0)%Z with false by (symmetry; apply Z.eqb_neq; lia). cbv iota.
                step.
                apply evt_done. eapply K2; [assumption | exact MU3 | exact WM3 | exact CELLS].
          -- replace (min <? 3) with true by (symmetry; apply Z.ltb_lt; lia). cbv iota.
             step. if_cases Kc3; [ try (zify_cond Kc3; exfalso; (keep_hyps CEILV sp EB ERR magic P min n0 n1 n2 n3 l0 l1 l2 l3 Mn Kc3; lia)) | idtac ].
             step. rewrite (and7_aligned (P + 648)) by lia. step. if_false. step. step.
             apply evt_done. eapply K2; [assumption | exact MU3 | exact WM3 | exact CELLS].
        * replace (maj =? 2) with false by (symmetry; apply Z.eqb_neq; lia). cbv iota.
          step. if_cases Kc2; [ idtac | try (zify_cond Kc2; exfalso; (keep_hyps CEILV M2 Kc2; lia)) ].
          step. rewrite (and7_aligned (P + 648)) by lia. step. if_true.
          apply evt_done. eapply K2; [assumption | exact MU3 | exact WM3 | exact CELLS].
    - replace (mi =? NSEC_TCPDUMP_MAGIC) with false by (symmetry; apply Z.eqb_neq; exact NN). unfold NSEC_TCPDUMP_MAGIC in NN.
      replace (mi + (2 ^ 64 - 2 ^ 32) =? 18446744072127396941)%Z with false by (symmetry; apply Z.eqb_neq; lia). cbv iota.
      step. step. step. pstep.
      destruct (Z.eq_dec maj 543) as [M543|M543].
      + replace (maj =? 2) with false by (symmetry; apply Z.eqb_neq; lia). replace (maj =? 543) with true by (symmetry; apply Z.eqb_eq; lia). cbv iota.
        step. if_cases Kc; [ idtac | try (zify_cond Kc; exfalso; (keep_hyps CEILV M543 Kc; lia)) ].
        step. rewrite (and7_aligned (P + 648)) by lia. step. if_false. step. step.
        apply evt_done. eapply K2; [assumption | exact MU3 | exact WM3 | exact CELLS].
      + replace (maj =? 543) with false by (symmetry; apply Z.eqb_neq; lia).
        step. if_cases Kc; [ try (zify_cond Kc; exfalso; (keep_hyps CEILV M543 Kc; lia)) | idtac ]. step.
        destruct (Z.eq_dec maj 2) as [M2|M2].
        * replace (maj =? 2) with true by (symmetry; apply Z.eqb_eq; lia). cbv iota.
          step. if_cases Kc2; [ try (zify_cond Kc2; exfalso; (keep_hyps CEILV M2 Kc2; lia)) | idtac ].
          destruct (Z.lt_ge_cases 2 min) as [Mn|Mn].
          -- step. if_cases Kc3; [ idtac | try (zify_cond Kc3; exfalso; (keep_hyps CEILV sp EB ERR magic P min n0 n1 n2 n3 l0 l1 l2 l3 Mn Kc3; lia)) ].
             step. rewrite (and7_aligned (P + 648)) by lia. step. if_false. step. step. rewrite (seqz_lit (min + -3)) by lia.
             destruct (Z.eq_dec min 3) as [M3|M3].
             ++ replace (min <? 3) with false by (symmetry; apply Z.ltb_ge; lia). replace (min =? 3) with true by (symmetry; apply Z.eqb_eq; lia).
                replace (min + -3 =? 0)%Z with true by (symmetry; apply Z.eqb_eq; lia). cbv iota.
                step.
                apply evt_done. eapply K2; [assumption | exact MU3 | exact WM3 | exact CELLS].
             ++ replace (min <? 3) with false by (symmetry; apply Z.ltb_ge; lia). replace (min =? 3) with false by (symmetry; apply Z.eqb_neq; lia).
                replace (min + -3 =? 0)%Z with false by (symmetry; apply Z.eqb_neq; lia). cbv iota.
                step.
                apply evt_done. eapply K2; [assumption | exact MU3 | exact WM3 | exact CELLS].
          -- replace (min <? 3) with true by (symmetry; apply Z.ltb_lt; lia). cbv iota.
             step. if_cases Kc3; [ try (zify_cond Kc3; exfalso; (keep_hyps CEILV sp EB ERR magic P min n0 n1 n2 n3 l0 l1 l2 l3 Mn Kc3; lia)) | idtac ].
             step. rewrite (and7_aligned (P + 648)) by lia. step. if_false. step. step.
             apply evt_done. eapply K2; [assumption | exact MU3 | exact WM3 | exact CELLS].
        * replace (maj =? 2) with false by (symmetry; apply Z.eqb_neq; lia). cbv iota.
          step. if_cases Kc2; [ idtac | try (zify_cond Kc2; exfalso; (keep_hyps CEILV M2 Kc2; lia)) ].
          step. rewrite (and7_aligned (P + 648)) by lia. step. if_true.
          apply evt_done. eapply K2; [assumption | exact MU3 | exact WM3 | exact CELLS].
  Qed.
  End Sz1.
  Lemma chk_fill : ltac:(let t := eval cbv delta [chk_fill__stmt] in chk_fill__stmt in exact t).
  Proof using FREE HFL HPL MALLOC SFL. intros ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc R s CL FB lo MG FA EB ERR f magic m ra' t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m3 ps3 q P maj min n0 n1 n2 n3 l0 l1 l2 l3 mi sw mid e3. ltac2:(SecDiet.SzSec.closeP 'chk_fill__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.
End ChkF.

End WithCeil.
End F_sfpcap_chkF.

(* [comment removed for export] *)
Module F_sfpcap_nextA2.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool String.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import Tac Arr Bytes ZBridge ITree Nodes Decode SysStep MonadX Image ImgTgtUbsan.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Prelim Monad Fmt StdioCore Stdio PcapPrelim PcapTypes PcapPure Pcap Prog. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Adapter__Spec. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Monad OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Fmt OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.StdioCore OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Stdio OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapPrelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapTypes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapPure OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Pcap OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prog OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Adapter__Spec.StartupModel.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require AmoStep__Musl. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require Printf_kit__Musl. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.STRW_tac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_kit__Musl.StartupKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.CellsExtra.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require FmtFacts__S3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_memchr__S3. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.FmtFacts__S3.FmtFacts OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_memchr__S3.SfKit.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_memcpy GI. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require GIFacts__S3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require PcapRep. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require Pcap_iface__S3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_lock__S3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_pcap_err__S3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_sfpcap_nextA. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_memcpy.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.GI.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.GIFacts__S3.GIFacts.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.GIFacts__S3.Ifaces.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.PcapRep.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Pcap_iface__S3.Pcap_iface.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_lock__S3.Pcap_iface_pp.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Pcap_iface__S3.F_pcap_pure.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Pcap_iface__S3.F_pcap_small.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Pcap_iface__S3.F_pcap_next_ex.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_pcap_err__S3.F_pcap_open.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_pcap_err__S3.F_pcap_fopen.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_lock__S3.PP_kit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcap_nextA.TwB.
From OSSVerify.libpcap.fuzz_pcap.images Require Import Ubsan.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import Ceiling.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import LiaPin.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require SecDiet.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac natfold_term t :=
  match t with
  | context C[4136%nat] => let t1 := context C[Z.to_nat 4136] in natfold_term t1
  | _ => t
  end.
Local Ltac natfold_hyp H := let T := type of H in let U := natfold_term T in change U in H.
Local Ltac natfold_concl := lazymatch goal with |- ?G => let U := natfold_term G in change U end.
Local Ltac natfold_lits :=
  repeat match goal with
  | nfH : context [4136%nat] |- _ => natfold_hyp nfH
  end;
  lazymatch goal with
  | |- context [4136%nat] => natfold_concl
  | |- _ => idtac
  end.
(* [comment removed for export] *)
Local Ltac cl_lit_hyps :=
  repeat match goal with
  | H : context [cells_size ?cs] |- _ =>
      tryif (match goal with H' := _ |- _ => constr_eq H' H end) then fail else
      (sl_spine_closed cs;
       let n := eval cbv [cells_size csize Nat.add] in (cells_size cs) in
       change (cells_size cs) with n in H)
  end.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import KeepHyps.
(* [comment removed for export] *)
Local Ltac lia_e2w2_base := first [ zify_prune; zify_noeuclid; Z.euclidean_division_equations_cleanup; xlia zchecker
                                 | zify_prune; Zify.zify; xlia zchecker | Zify.zify; xlia zchecker ].
Local Ltac ceil_mentioned := lazymatch goal with | |- context [@alloc_ceiling _] => idtac | _ : context [@alloc_ceiling _] |- _ => idtac end.
(* [comment removed for export] *)
Local Ltac gio_ceil_fact :=
  match goal with
  | G : GIo _ _ _ _ _ _ |- _ => let H := fresh "CLO__" in pose proof (S3.PcapRep.TwB.GIo_ceil_lo _ _ _ _ _ _ G) as H; unfold rc_lo in H
  end.
(* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac lia ::= clear_unpinned; try gio_ceil_fact; try (ceil_ok; ceil_mentioned; ceil_facts); pinned_lia_core.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Open Scope bv_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
Section WithCeil.
Context {CEILV : CEIL}.
Lemma pfx_realloc : forall (bsx junk : list byte) (d : list Z) (M n : nat),
  firstn (length d) bsx = map b8 d -> (Nat.min n (length d) <= M)%nat -> (M <= length bsx)%nat ->
  firstn (length (firstn n d)) (firstn M bsx ++ junk) = map b8 (firstn n d).
Proof using Type. all: natfold_lits. pin_using tt.
  intros bsx junk d M n PFXd HM HL.
  rewrite length_firstn. rewrite firstn_app. rewrite firstn_firstn by lia.
  replace (Nat.min n (length d) - length (firstn M bsx))%nat with 0%nat by (rewrite length_firstn; lia). cbn [firstn]. rewrite app_nil_r.
  rewrite (Nat.min_l (Nat.min n (length d)) M) by lia.
  rewrite <- firstn_map, <- PFXd, firstn_firstn. reflexivity.
Qed.

Definition lor_ge_l__stmt : Prop := forall a b, (0 <= a)%Z -> (0 <= b)%Z -> (a <= Z.lor a b)%Z.
Section Sz2.
Variables a b : ltac2:(SecDiet.SzSec.tyM 'lor_ge_l__stmt "vv" @a).
Lemma lor_ge_l__body : ltac2:(SecDiet.SzSec.bodyP 'lor_ge_l__stmt "vv").
Proof using Type. all: natfold_lits. pin_using tt.
  intros Ha Hb.
  set (c := Z.land b (Z.lnot a)).
  assert (Hc : (0 <= c)%Z) by (subst c; apply Z.land_nonneg; left; lia).
  assert (D : Z.land a c = 0%Z).
  { subst c. rewrite Z.land_comm, <- Z.land_assoc. rewrite (Z.land_comm (Z.lnot a) a), Z.land_lnot_diag, Z.land_0_r. reflexivity. }
  assert (E : Z.lor a b = Z.lor a c).
  { apply Z.bits_inj'. intros n Hn. subst c. rewrite !Z.lor_spec, Z.land_spec, Z.lnot_spec by lia.
    destruct (Z.testbit a n), (Z.testbit b n); reflexivity. }
  rewrite E, <- Z.lxor_lor, <- Z.add_nocarry_lxor by exact D. lia.
Qed.
End Sz2.
Lemma lor_ge_l : ltac:(let t := eval cbv delta [lor_ge_l__stmt] in lor_ge_l__stmt in exact t).
Proof using Type. all: natfold_lits. intros a b. ltac2:(SecDiet.SzSec.closeP 'lor_ge_l__body "vv"). Qed.

Lemma zfirstn_length_le' : forall n (l : list Z), (length (zfirstn n l) <= Z.to_nat n)%nat.
Proof using Type. all: natfold_lits. pin_using tt. intros. unfold zfirstn. rewrite length_firstn. lia. Qed.

Lemma max_snaplen_le : forall d, (max_snaplen_for_dlt d <= 134217728)%Z.
Proof using Type. all: natfold_lits. pin_using tt. intros d. unfold max_snaplen_for_dlt, MAXIMUM_SNAPLEN. repeat match goal with |- context [Z.eqb ?a ?b] => destruct (Z.eqb a b) end; lia. Qed.


Section NpCtxA2.
  Context {H hptr : Type} (HO : HeapOps H hptr) (K : modkit H hptr) (sites : stack_site -> Z).
  Hypothesis HFL : heap_frame_law K.
  Hypothesis SFL : stdio_fp_law K.
  Hypothesis HPL : heap_perm_law K.
  Hypothesis HAL : heap_addr_law K HO.
  Hypothesis FREAD : fread_stmt_o HO K.
  Hypothesis FERROR : ferror_stmt_o HO K.
  Hypothesis FMT : fmt_errmsg_stmt K.
  Hypothesis SNPRINTF : snprintf_spec_stmt K.
  Hypothesis REALLOC : realloc_stmt_o HO K.
  Hypothesis PP : post_process_stmt.

  (* [comment removed for export] *)
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
  Variables (R : rctx) (CLc FB : list (cblock (hptr:=hptr))) (lo P HA DA B Af : Z) (m : mem) (o : option hptr).
  Variables (self buffer f : hptr) (bufsize bufalloc : Z) (bufdata : list Z) (swapped : bool)
            (vmaj vmin snapshot linktype ltext prec brk : Z) (errbuf : list Z) (header : pkthdr)
            (hdrsize : Z) (lsw : lenswap_t) (scl : sf_scale_t) (j : pcap_junk) (pad bs : list byte).
  Hypothesis LO : (usp0 R - 8388608 <= lo)%Z.
  Hypothesis BU : (lo + 81920 <= bv_unsigned sp)%Z.
  Hypothesis SPM : (bv_unsigned sp <= rc_spmain R)%Z.
  Hypothesis TP : tp = rc_tp R.
  Hypothesis ALN : (bv_unsigned sp mod 16 = 0)%Z.
  Hypothesis SITES : sites = sites_at (bv_unsigned sp + D_NEXT_PACKET).
  Hypothesis R1 : (bv_unsigned sp <= HA)%Z.
  Hypothesis R2 : (HA + 24 <= DA)%Z.
  Hypothesis R3 : (DA + 8 <= rc_spmain R)%Z.
  Hypothesis AH : (HA mod 8 = 0)%Z.
  Hypothesis AD : (DA mod 8 = 0)%Z.
  Hypothesis SPW : (140735340871680 <= usp0 R)%Z.
  Hypothesis SP47 : (usp0 R <= 2^47)%Z.
  Hypothesis HinF : In (f, Af, FILE_BLOCK) FB.
  Hypothesis P1 : (0 < P)%Z.  Hypothesis P2 : (P mod 16 = 0)%Z.  Hypothesis P4 : (P + 664 <= CEILZ)%Z.
  Hypothesis P5 : (P + 664 <= 65536 \/ 352256 <= P)%Z.  Hypothesis P6 : (P + 664 <= utp R - 200 \/ utp R - 200 + 4096 <= P)%Z.
  Hypothesis A1 : (0 < Af)%Z.  Hypothesis A4 : (Af + 1264 <= CEILZ)%Z.
  Hypothesis W1 : (1 <= snapshot <= INT_MAX)%Z.  Hypothesis W2 : (0 <= bufsize < 2^32)%Z.
  Hypothesis W5 : brk = 0%Z.  Hypothesis W6 : prec = 0%Z.
  Hypothesis W7 : (0 <= vmaj < 2^16)%Z.  Hypothesis W8 : (0 <= vmin < 2^16)%Z.
  Hypothesis W9 : (0 <= linktype < 2^31)%Z.  Hypothesis W10 : (-2^31 <= ltext < 2^31)%Z.
  Hypothesis WHS : (hdrsize = 16 \/ hdrsize = 24)%Z.
  Hypothesis PPLEN : forall lt sw hdr d, length (snd (pcapint_post_process lt sw hdr d)) = length d.
  Hypothesis PPSEC : forall lt sw hdr d, h_sec (fst (pcapint_post_process lt sw hdr d)) = h_sec hdr /\ h_usec (fst (pcapint_post_process lt sw hdr d)) = h_usec hdr.
  Hypothesis PPRNG : forall lt sw hdr d, (0 <= h_caplen hdr <= Z.of_nat (length d))%Z -> (0 <= h_len hdr < 2^32)%Z -> (Z.of_nat (length d) < 2^31)%Z ->
     (0 <= h_caplen (fst (pcapint_post_process lt sw hdr d)) < 2^32)%Z /\ (0 <= h_len (fst (pcapint_post_process lt sw hdr d)) < 2^32)%Z.

  Let POSTQ := next_packet_post K ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc R CLc FB lo P HA DA m o.

  (* [comment removed for export] *)
  #[local] Abbreviation pv := (S3.F_sfpcap_nextA.TwB.pv self f swapped vmaj vmin snapshot linktype ltext prec brk header hdrsize lsw scl).
  #[local] Abbreviation np_fail_tail := (S3.F_sfpcap_nextA.TwB.np_fail_tail K ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc R CLc FB lo P HA DA m o BU).
  #[local] Abbreviation np_ok_tail := (S3.F_sfpcap_nextA.TwB.np_ok_tail K ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc R CLc FB lo P HA DA m o BU).
  #[local] Abbreviation np_snp := (S3.F_sfpcap_nextA.TwB.np_snp K HFL SFL SNPRINTF ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc R CLc FB lo P HA DA m o LO BU SPM TP ALN R1 R2 AH AD SPW P1 P4 P5).
  #[local] Abbreviation np_fmt := (S3.F_sfpcap_nextA.TwB.np_fmt K FMT ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc R CLc FB lo P HA DA m o LO BU SPM TP ALN R1 R2 AH AD SPW P1 P2 P4).
  #[local] Abbreviation np_finish := (S3.F_sfpcap_nextA.TwB.np_finish K HFL SFL PP ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc R CLc FB lo P HA DA m o self f swapped vmaj vmin snapshot linktype ltext prec brk header hdrsize lsw scl
                               LO BU SPM R1 R2 R3 AH AD SPW SP47 P1 P5 P6 W9 PPLEN PPSEC PPRNG).
  #[local] Abbreviation np_CLc_facts := (S3.F_sfpcap_nextA.TwB.np_CLc_facts K R CLc FB).
  #[local] Abbreviation PCAPR_errbuf := (S3.F_sfpcap_nextA.TwB.PCAPR_errbuf K sp R lo P HA DA LO BU ALN R1 R2 AH AD SPW P1).

  Ltac norm_p :=
    unfold S3.F_sfpcap_nextA.TwB.pv in *; unfold pcap_blocks in *; unfold psize in *; unfold is_ng in *;
    cbn [pc_self pc_rfile pc_bufsize pc_bufalloc pc_buffer pc_bufdata pc_swapped pc_version_major pc_version_minor pc_snapshot pc_linktype
         pc_linktype_ext pc_tstamp_precision pc_break_loop pc_errbuf pc_header pc_priv priv_cells
         sf_hdrsize sf_lengths_swapped sf_scale_type ifaces_ok set_bufdata set_errbuf set_buffer] in *;
    unfold PCAP_SF_TOTAL, PCAP_PRIV_OFF in *.

  #[local] Abbreviation implM_pure_k := (@S3.F_sfpcap_nextA.TwB.implM_pure_k).
  #[local] Abbreviation p0 := (S3.F_sfpcap_nextA.TwB.p0 self buffer f bufsize bufalloc bufdata swapped vmaj vmin snapshot linktype ltext prec brk errbuf header hdrsize lsw scl).

  (* [comment removed for export] *)
  Definition np_nread__stmt : Prop := forall (ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' x2 x3 x4 x5 t3' t4' t5' t6' : word) (m5 : mem) (ps : PState H hptr)
           (bq : hptr) (Bx bsz alloc : Z) (data eb : list Z) (sec usec cap len : Z) (dw : cell) (fj : list byte),
      stk usegs m5 lo (bv_unsigned sp + -4208) ->
      rw_cells usegs m5 (bv_unsigned sp + -4208) [CB 4136 fj; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] -> mem_inv usegs m5 ->
      GIo K R ps (CLc ++ pcap_blocks (pv bq bsz alloc data eb) P Bx 0) FB m5 ->
      PCAPR (hptr:=hptr) P (pv bq bsz alloc data eb) (pcap_blocks (pv bq bsz alloc data eb) P Bx 0) FB m5 ->
      agrees_on (fun a => client_keeps CLc (bv_unsigned sp) a /\ ~ (HA <= a < HA + 24) /\ ~ (DA <= a < DA + 8))%Z m m5 ->
      rw_cells usegs m5 HA [C8 (Z_to_bv 64 sec); C8 (Z_to_bv 64 usec); C4 (Z_to_bv 64 cap); C4 (Z_to_bv 64 len)] -> rw_cells usegs m5 DA [dw] -> csize dw = 8%nat ->
      (0 <= cap <= bsz)%Z -> (cap <= snapshot)%Z -> (0 <= len < 2^32)%Z -> ps_outfile ps = o ->
      implM usegs (np_read_model MOps (prims HO fo_nop sites) f (pv bq bsz alloc data eb) (mkHdr sec usec cap len) cap) ps POSTQ
        (MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -4208)) gp tp t0' t1' t2' (Z_to_bv 64 P) (Z_to_bv 64 HA) a0' a1' a2' a3' a4' a5' a6' a7'
                 (Z_to_bv 64 DA) (Z_to_bv 64 Af) x2 x3 x4 x5 s8 s9 s10 s11 t3' t4' t5' t6') F (Z_to_bv 64 0x15d7c) fc None m5 (seg_rom usegs)).
  Section Sz5.
  Variables ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' x2 x3 x4 x5 t3' t4' t5' t6' m5 ps bq Bx bsz alloc data eb sec usec cap len dw fj : ltac2:(SecDiet.SzSec.tyM 'np_nread__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra').
  Lemma np_nread__body : ltac2:(SecDiet.SzSec.bodyP 'np_nread__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof using AD AH ALN BU FERROR FMT FREAD HAL HFL HinF LO P1 P2 P4 P5 P6 PP PPLEN PPRNG PPSEC R1 R2 R3 SFL SNPRINTF SP47 SPM SPW TP W1 W10 W5 W6 W7 W8 W9 WHS. all: natfold_lits. pin_using (fun (AD AH ALN BU FERROR FMT FREAD HAL HFL HinF LO P1 P2 P4 P5 P6 PP PPLEN PPRNG PPSEC R1 R2 R3 SFL SNPRINTF SP47 SPM SPW TP W1 W10 W5 W6 W7 W8 W9 WHS : unit) => tt).
 intros ST5 FR5 MI5 G5 PC5 AG5 HH HD Hd Hcap Hcs Hl32 OF5.
    pose proof (bv_unsigned_in_range 64 sp) as RSP.
    pose proof PC5 as PC5'.
    destruct PC5 as (Afx & Hin & (Bx' & Ix & jx' & padx & bsx' & EPB & CELLS & PRIV & BUF & PFX & IFS & WF)).
    norm_p. unfold sf_cells in PRIV. cbn [sf_hdrsize sf_lengths_swapped sf_scale_type] in PRIV.
    subst Ix. assert (EBX : Bx' = Bx) by congruence. subst Bx'. clear EPB.
    pose proof WF as (_ & W2' & W3 & W4 & _ & _ & _ & _ & _ & _ & _ & _ & _ & WBB). cbn [pc_bufsize pc_bufalloc pc_bufdata length] in W2', W3, W4, WBB.
    pose proof (GIo_PB_block K _ _ _ _ _ _ _ _ _ G5 ltac:(right; left; reflexivity)) as (K1 & K2 & K3 & K4 & K5 & K6).
    pose proof (GIo_PB_block K _ _ _ _ _ _ _ _ _ G5 ltac:(left; reflexivity)) as (L1 & L2 & L3 & L4 & L5 & L6).
    assert (BP' : (Bx + alloc <= P \/ P + 664 <= Bx)%Z).
    { pose proof (PB_apart K _ _ _ _ _ _ (pv bq bsz alloc data eb) P Bx 0 G5 eq_refl) as [APB _]. unfold S3.F_sfpcap_nextA.TwB.pv, psize, is_ng in APB. cbn [pc_bufalloc pc_priv] in APB. unfold PCAP_SF_TOTAL in APB. lia. }
    (* [comment removed for export] *)
    apply (rw_cells_split_CB usegs m5 _ [] (Z.to_nat alloc) _ [] [Z.to_nat cap; Z.to_nat alloc - Z.to_nat cap]%nat) in BUF; [| cbn; lia].
    cbn [mk_CB_cells app] in BUF.
    destruct (rw_cells_cut _ _ _ 1 BUF) as [BD BT]. clear BUF. (sl_lit_sizes_in BD; sl_lit_sizes_in BT; cbn [firstn skipn cells_size csize Nat.add] in BD, BT).
    unfold np_read_model, read_fail_msg, errmsg_for_errno. cbn [mo_bind mo_ret MOps e_fenter e_fret fo_enter fo_ret fo_nop prims e_fread e_ferror e_last_errno prims pc_buffer pc_linktype pc_swapped pc_bufdata set_bufdata set_errbuf
      pc_self pc_rfile pc_bufsize pc_bufalloc pc_version_major pc_version_minor pc_snapshot pc_linktype_ext pc_tstamp_precision pc_break_loop pc_errbuf pc_header pc_priv].
    (* [comment removed for export] *)
    pose proof CELLS as CELLSu.
    unfold pcap_cells, pcap_cells_gen, pc_pre, hdr_cells, pc_ops, np_entry, cleanup_entry, is_ng, PCAP_PRIV_OFF in CELLSu.
    cbn [app pc_bufsize pc_bufalloc pc_buffer pc_break_loop pc_swapped pc_version_major pc_version_minor pc_snapshot pc_linktype pc_linktype_ext pc_tstamp_precision pc_header pc_priv
         pk_next_pcap pk_cleanup_sf PK pc_rfile] in CELLSu.
    hide BT. hide PRIV. hide HD. hide CELLS.
    pose proof (munch_refl ([] : list (Z * Z)) m5) as MU. pose proof (wmono_refl usegs m5) as WM.
    unfold implM. iprefix.
    step. clear CELLSu. step. rewrite (zx32_lit cap) by lia. hide HH. do 3 step.
    name_sp sp (-4208)%Z.
    apply evt_done. eapply (implM_bind usegs).
    { apply implM_mget. cbn [eval_rdest fo_site fo_nop]. unfold blk_addr.
      rewrite (GIo_addr HO K HAL _ _ _ _ _ _ _ _ G5 ltac:(apply in_or_app; left; apply in_or_app; right; right; left; reflexivity)).
      rewrite Z.add_0_r.
      eapply FREAD; [| exact HinF | reflexivity | reflexivity | reflexivity | reflexivity | lia | exact BD | ].
      { split; [exact G5|]. split; [rewrite Hsp; exact ST5|]. split; [unfold rc_lo; lia|]. split; [unfold STDIO_STACK; rewrite Hsp; lia|].
        split; [rewrite Hsp; lia|]. split; [exact MI5|]. split; [exact TP| rewrite Hsp; apply aln16_add; [exact ALN| reflexivity]]. }
      left. intros a Ha. apply in_block_app. right. unfold in_block. apply Exists_cons_tl, Exists_cons_hd. cbn [cb_addr cb_size fst snd]. lia. }
    intros got ps6 ms6 PO. cbv beta in PO.
    destruct PO as (av & m6 & junk6 & E & OF6 & MI6 & ST6 & AG6 & G6 & -> & GOTL & GOTR & HD6).
    unfold hpost_regs in E. all: natfold_lits. destruct_exs E. subst ms6. rewrite Hsp in *. unname_sp.
    replace (ret_pc (Z_to_bv 64 89488)) with (Z_to_bv 64 89488) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
    unhide BT. unhide PRIV. unhide CELLS. unhide HH. unhide HD.
    assert (KEEP : forall A cs, rw_cells usegs m5 A cs ->
              ((bv_unsigned sp + -4208 <= A) \/ (P <= A /\ A + Z.of_nat (cells_size cs) <= P + 664) \/ (Bx + cap <= A /\ A + Z.of_nat (cells_size cs) <= Bx + alloc))%Z ->
              rw_cells usegs m6 A cs).
    { intros A cs HC HX. eapply agrees_rw_cells; [exact AG6 | exact HC |]. intros a Ha. destruct HX as [HX|[HX|HX]].
      - split; [left; lia| unfold rc_lo in LO; lia].
      - split; [| (keep_hyps CEILV sp R lo P HA DA Bx bsz alloc data cap dw A cs a Hcap WBB BP' HX Ha; lia)]. right. apply in_block_app. right. unfold in_block. apply Exists_cons_hd. cbn [cb_addr cb_size fst snd]. lia.
      - split; [| lia]. right. apply in_block_app. right. unfold in_block. apply Exists_cons_tl, Exists_cons_hd. cbn [cb_addr cb_size fst snd]. lia. }
    apply KEEP in FR5; [| left; lia]. apply KEEP in HH; [| left; lia]. apply KEEP in HD; [| left; lia].
    apply KEEP in CELLS; [| right; left; rewrite pcap_cells_gen_size by reflexivity; lia]. apply KEEP in PRIV; [| right; left; (sl_lit_sizes; cbn [cells_size csize Nat.add]); lia].
    apply KEEP in BT; [| right; right; (sl_lit_sizes; cbn [cells_size csize Nat.add]); lia]. clear KEEP.
    assert (AG06 : agrees_on (fun a => client_keeps CLc (bv_unsigned sp) a /\ ~ (HA <= a < HA + 24) /\ ~ (DA <= a < DA + 8))%Z m m6).
    { eapply agrees_on_trans; [exact AG5|]. eapply agrees_on_weaken; [exact AG6|]. intros a [[Ha|Ha] _]; [split; [left; lia| unfold rc_lo in LO; lia]|].
      destruct (np_CLc_facts _ _ _ _ G5 Ha) as [Hc Hnb]. split; [right; apply in_block_app; left; exact Ha|].
      intros Hin'. apply Hnb. unfold in_block. apply Exists_cons_tl, Exists_cons_hd. cbn [cb_addr cb_size fst snd]. lia. }
    clear AG6 MI5 ST5 G5 PC5' AG5 MU WM.
    hide BT. hide PRIV. hide CELLS. hide HD. hide HD6.
    pose proof (munch_refl ([] : list (Z * Z)) m6) as MU. pose proof (wmono_refl usegs m6) as WM.
    unfold implM. iprefix. step. rewrite (zx32_lit cap) by lia.
    destruct (Z.eq_dec (zlength got) cap) as [LEQ|LNE].
    - (* [comment removed for export] *)
      rewrite (proj2 (Z.eqb_eq _ _) LEQ). cbn [negb].
      step. if_cases Kq; try (zify_cond Kq; exfalso; unfold zlength in *; (keep_hyps CEILV R LEQ Kq; lia)).
      unhide BT. unhide PRIV. unhide CELLS. unhide HD. unhide HD6.
      assert (LG : length got = Z.to_nat cap) by (unfold zlength in LEQ; lia).
      pose proof (rw_cells_uncut _ _ _ _ _ HD6 BT ltac:((sl_lit_sizes; cbn [cells_size csize Nat.add]); lia)) as BUF6. cbn [app] in BUF6. merge_all BUF6.
      replace (length got + (Z.to_nat cap - length got + (Z.to_nat alloc - Z.to_nat cap + 0)))%nat with (Z.to_nat alloc) in BUF6 by lia.
      rewrite app_nil_r in BUF6.
      apply evt_done. eapply (np_finish _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (Z_to_bv 64 sec) (Z_to_bv 64 usec) m6 ps6 bq Bx bsz alloc got eb sec usec cap len dw fj);
        [exact ST6 | exact FR5 | exact MI6 | exact G6 | | exact AG06 | exact HH | exact HD | exact Hd | reflexivity | reflexivity | exact GOTR
        | unfold zlength in LEQ; lia | unfold zlength in LEQ; lia | exact Hl32 | congruence].
      exists Afx. split; [exact Hin|]. exists Bx, 0%Z, jx', padx, (map b8 got ++ junk6 ++ firstn (Z.to_nat alloc - Z.to_nat cap) (skipn (Z.to_nat cap) bsx')).
      split; [reflexivity|]. split; [exact CELLS|]. split; [unfold PCAP_PRIV_OFF; exact PRIV|]. split; [unfold S3.F_sfpcap_nextA.TwB.pv; cbn [pc_bufalloc]; exact BUF6|].
      split; [unfold S3.F_sfpcap_nextA.TwB.pv; cbn [pc_bufdata]; replace (length got) with (length (map b8 got)) by (apply length_map);
              rewrite firstn_app, firstn_all, Nat.sub_diag; cbn [firstn]; rewrite app_nil_r; reflexivity|].
      split; [reflexivity|].
      unfold pcap_wf, S3.F_sfpcap_nextA.TwB.pv in *. cbn [set_bufdata pc_snapshot pc_bufsize pc_bufalloc pc_bufdata pc_break_loop pc_tstamp_precision pc_version_major pc_version_minor
                                 pc_linktype pc_linktype_ext pc_header pc_priv sf_hdrsize] in *. rewrite LG. repeat split; try (keep_hyps CEILV sp R P HA DA snapshot Bx data cap dw got W1 bsz W2' alloc W3 lo Hcap WBB brk W5 prec W6 vmaj W7 vmin W8 linktype W9 ltext W10 header hdrsize WF WHS; lia); try tauto.
    - (* [comment removed for export] *)
      rewrite (proj2 (Z.eqb_neq _ _) LNE). cbn [negb].
      step. if_cases Kq; try (zify_cond Kq; exfalso; unfold zlength in *; (keep_hyps CEILV R LNE Kq; lia)).
      do 3 step.
      apply evt_done. apply (implM_bind_assoc usegs). name_sp sp (-4208)%Z. eapply (implM_bind usegs).
      { eapply FERROR; [| exact HinF | reflexivity].
        split; [exact G6|]. split; [rewrite Hsp; exact ST6|]. split; [unfold rc_lo; lia|]. split; [unfold STDIO_STACK; rewrite Hsp; lia|].
        split; [rewrite Hsp; lia|]. split; [exact MI6|]. split; [exact TP| rewrite Hsp; apply aln16_add; [exact ALN| reflexivity]]. }
      intros r ps7 ms7 PO. cbv beta in PO. destruct PO as (av7 & m7 & E & MI7 & ST7 & AG7 & G7 & -> & -> & ERRNO).
      unfold hpost_regs in E. all: natfold_lits. destruct_exs E. subst ms7. rewrite Hsp in *. unname_sp.
      replace (ret_pc (Z_to_bv 64 89608)) with (Z_to_bv 64 89608) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
      unhide BT. unhide PRIV. unhide CELLS. unhide HD. unhide HD6.
      assert (KEEP : forall A cs, rw_cells usegs m6 A cs ->
                ((bv_unsigned sp + -4208 <= A) \/ (P <= A /\ A + Z.of_nat (cells_size cs) <= P + 664) \/ (Bx <= A /\ A + Z.of_nat (cells_size cs) <= Bx + alloc))%Z ->
                rw_cells usegs m7 A cs).
      { intros A cs HC HX. eapply agrees_rw_cells; [exact AG7 | exact HC |]. intros a Ha. destruct HX as [HX|[HX|HX]]; [left; lia| right | right].
        - apply in_block_app. right. unfold in_block. apply Exists_cons_hd. cbn [cb_addr cb_size fst snd]. lia.
        - apply in_block_app. right. unfold in_block. apply Exists_cons_tl, Exists_cons_hd. cbn [cb_addr cb_size fst snd]. lia. }
      apply KEEP in FR5; [| left; lia]. apply KEEP in HH; [| left; lia]. apply KEEP in HD; [| left; lia].
      apply KEEP in CELLS; [| right; left; rewrite pcap_cells_gen_size by reflexivity; lia]. apply KEEP in PRIV; [| right; left; (sl_lit_sizes; cbn [cells_size csize Nat.add]); lia].
      apply KEEP in BT; [| right; right; (sl_lit_sizes; cbn [cells_size csize Nat.add]); lia]. apply KEEP in HD6; [| right; right; (sl_lit_sizes; cbn [cells_size csize Nat.add]); unfold zlength in GOTL; lia]. clear KEEP.
      assert (AG07 : agrees_on (fun a => client_keeps CLc (bv_unsigned sp) a /\ ~ (HA <= a < HA + 24) /\ ~ (DA <= a < DA + 8))%Z m m7).
      { eapply agrees_on_trans; [exact AG06|]. eapply agrees_on_weaken; [exact AG7|]. intros a [[Ha|Ha] _]; [left; lia| right; apply in_block_app; left; exact Ha]. }
      pose proof (rw_cells_uncut _ _ _ _ _ HD6 BT ltac:((sl_lit_sizes; cbn [cells_size csize Nat.add]); unfold zlength in GOTL; lia)) as BUF7. cbn [app] in BUF7. merge_all BUF7.
      replace (length got + (Z.to_nat cap - length got + (Z.to_nat alloc - Z.to_nat cap + 0)))%nat with (Z.to_nat alloc) in BUF7 by (unfold zlength in GOTL; lia).
      rewrite app_nil_r in BUF7.
      assert (PC7 : PCAPR (hptr:=hptr) P (pv bq bsz alloc got eb) [(self, P, 664%Z); (bq, Bx, alloc)] FB m7).
      { exists Afx. split; [exact Hin|]. exists Bx, 0%Z, jx', padx, (map b8 got ++ junk6 ++ firstn (Z.to_nat alloc - Z.to_nat cap) (skipn (Z.to_nat cap) bsx')).
        split; [reflexivity|]. split; [exact CELLS|]. split; [unfold PCAP_PRIV_OFF; exact PRIV|]. split; [unfold S3.F_sfpcap_nextA.TwB.pv; cbn [pc_bufalloc]; exact BUF7|].
        split; [unfold S3.F_sfpcap_nextA.TwB.pv; cbn [pc_bufdata]; replace (length got) with (length (map b8 got)) by (apply length_map);
                rewrite firstn_app, firstn_all, Nat.sub_diag; cbn [firstn]; rewrite app_nil_r; reflexivity|].
        split; [reflexivity|].
        unfold pcap_wf, S3.F_sfpcap_nextA.TwB.pv in *. cbn [set_bufdata pc_snapshot pc_bufsize pc_bufalloc pc_bufdata pc_break_loop pc_tstamp_precision pc_version_major pc_version_minor
                                   pc_linktype pc_linktype_ext pc_header pc_priv sf_hdrsize] in *. unfold zlength in GOTL. repeat split; try (keep_hyps CEILV sp R P HA DA snapshot Bx data dw got W1 bsz W2' alloc W3 lo cap Hcap WBB GOTL brk W5 prec W6 vmaj W7 vmin W8 linktype W9 ltext W10 header hdrsize WF WHS; lia); try tauto. }
      clear AG7 MU WM. hide BUF7. hide PRIV. hide CELLS. hide HD. hide HH.
      pose proof (munch_refl ([] : list (Z * Z)) m7) as MU. pose proof (wmono_refl usegs m7) as WM.
      destruct r.
      + (* [comment removed for export] *)
        destruct (ERRNO eq_refl) as [EN ER]. clear ERRNO. unfold utp in EN. rewrite <- TP in EN.
        pose proof (GIo_tls K _ _ _ _ _ G7) as [_ TB]. unfold tls_block_ok_u, utp in TB. rewrite <- TP in TB.
        eapply implM_pure_k; [reflexivity|]. cbn [fst snd].
        set (e := lc_errno (ps_libc ps6)) in *.
        assert (E4 : ((bv_unsigned tp + -164) mod 4 = 0)%Z).
        { destruct TB as (TBA & _). apply Z.mod_divide in TBA; [|lia]. destruct TBA as [q Hq]. apply Z.mod_divide; [lia|]. exists (q * 4 + 9)%Z. lia. }
        unfold implM. iprefix. cbn [Z.b2z]. step. if_false. do 5 step. if_false_by (eqz_false (bv_unsigned tp + -164) ltac:(clear - TB; lia)).
        step. rewrite (and3_aligned (bv_unsigned tp + -164)) by (clear - TB E4; lia). step. if_false.
        step. rewrite (sx32_s32 e) by lia. do 4 step.
        unhide BUF7. unhide PRIV. unhide CELLS. unhide HD. unhide HH.
        apply evt_done. eapply np_fmt; [exact ST7 | exact FR5 | exact MI7 | | lia |].
        { split; [exact G7|]. split; [exact PC7|]. split; [exact AG07|]. split; [exact HH|]. split; [reflexivity|]. split; [exact HD|]. split; [exact Hd| congruence]. }
        split; [|cbn; lia]. exact (ro_cells_bytes_at _ _ _ _ (ro_cells_image usegs m7 0x108d6 (map (fun c => Z_to_bv 8 (Z.of_nat (Ascii.nat_of_ascii c))) (list_ascii_of_string "error reading dump file"%string) ++ [Z_to_bv 8 0])
                                   MI7 ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(cbn; lia))).
      + (* [comment removed for export] *)
        eapply implM_pure_k; [reflexivity|]. cbn [fst snd].
        unfold implM. iprefix. cbn [Z.b2z]. step. if_true. step. rewrite (sextw_small cap) by lia. do 7 step.
        unhide BUF7. unhide PRIV. unhide CELLS. unhide HD. unhide HH.
        apply evt_done. unfold Msg.trunc_captured_u, PCAP_ERRBUF_SIZE.
        eapply np_snp; [exact ST7 | exact FR5 | exact MI7 | | | vm_compute; reflexivity | cbn; lia | | | vm_compute; reflexivity | apply args_ok_ints2].
        { split; [exact G7|]. split; [exact PC7|]. split; [exact AG07|]. split; [exact HH|]. split; [reflexivity|]. split; [exact HD|]. split; [exact Hd| congruence]. }
        { split; [|cbn; lia]. exact (ro_cells_bytes_at _ _ _ _ (ro_cells_image usegs m7 0x10c8d (map (fun c => Z_to_bv 8 (Z.of_nat (Ascii.nat_of_ascii c))) (list_ascii_of_string "truncated dump file; tried to read %u captured bytes, only got %zu"%string) ++ [Z_to_bv 8 0])
                                     MI7 ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(cbn; lia))). }
        { cbn [length firstn]. constructor; [reflexivity|]. constructor; [reflexivity| constructor]. }
        pose proof (snprintf_length 256 "truncated dump file; tried to read %u captured bytes, only got %zu"%string [AInt cap; AInt (zlength got)]) as LS.
        change (Z.to_nat (256 - 1)) with 255%nat in LS. exact LS.
  Qed.
  End Sz5.
  Lemma np_nread : ltac:(let t := eval cbv delta [np_nread__stmt] in np_nread__stmt in exact t).
  Proof using AD AH ALN BU FERROR FMT FREAD HAL HFL HinF LO P1 P2 P4 P5 P6 PP PPLEN PPRNG PPSEC R1 R2 R3 SFL SNPRINTF SP47 SPM SPW TP W1 W10 W5 W6 W7 W8 W9 WHS. all: natfold_lits. intros ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' x2 x3 x4 x5 t3' t4' t5' t6' m5 ps bq Bx bsz alloc data eb sec usec cap len dw fj. ltac2:(SecDiet.SzSec.closeP 'np_nread__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.

  (* [comment removed for export] *)
  Definition np_normal__stmt : Prop := forall (ra' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' x4 x5 t3' t4' t5' t6' : word) (m5 : mem) (ps : PState H hptr)
           (sec usec cap len : Z) (dw : cell) (fj : list byte),
      stk usegs m5 lo (bv_unsigned sp + -4208) ->
      rw_cells usegs m5 (bv_unsigned sp + -4208) [CB 4136 fj; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] -> mem_inv usegs m5 ->
      GIo K R ps (CLc ++ pcap_blocks p0 P B 0) FB m5 ->
      PCAPR (hptr:=hptr) P p0 (pcap_blocks p0 P B 0) FB m5 ->
      agrees_on (fun a => client_keeps CLc (bv_unsigned sp) a /\ ~ (HA <= a < HA + 24) /\ ~ (DA <= a < DA + 8))%Z m m5 ->
      rw_cells usegs m5 HA [C8 (Z_to_bv 64 sec); C8 (Z_to_bv 64 usec); C4 (Z_to_bv 64 cap); C4 (Z_to_bv 64 len)] -> rw_cells usegs m5 DA [dw] -> csize dw = 8%nat ->
      (0 <= cap <= snapshot)%Z -> (cap <= max_snaplen_for_dlt linktype)%Z -> (0 <= len < 2^32)%Z -> ps_outfile ps = o ->
      implM usegs (np_norm_model MOps (prims HO fo_nop sites) p0 (mkHdr sec usec cap len) cap) ps POSTQ
        (MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -4208)) gp tp t0' t1' t2' (Z_to_bv 64 P) (Z_to_bv 64 HA) (Z_to_bv 64 snapshot) a1' a2' a3' a4' a5' a6' a7'
                 (Z_to_bv 64 DA) (Z_to_bv 64 Af) (Z_to_bv 64 cap) (Z_to_bv 64 snapshot) x4 x5 s8 s9 s10 s11 t3' t4' t5' t6') F (Z_to_bv 64 0x15d20) fc None m5 (seg_rom usegs)).
  Section Sz6.
  Variables ra' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' x4 x5 t3' t4' t5' t6' m5 ps sec usec cap len dw fj : ltac2:(SecDiet.SzSec.tyM 'np_normal__stmt "vvvvvvvvvvvvvvvvvvvvvvvvv" @ra').
  Lemma np_normal__body : ltac2:(SecDiet.SzSec.bodyP 'np_normal__stmt "vvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof using AD AH ALN BU FERROR FMT FREAD HAL HFL HPL HinF LO P1 P2 P4 P5 P6 PP PPLEN PPRNG PPSEC R1 R2 R3 REALLOC SFL SNPRINTF SP47 SPM SPW TP W1 W10 W2 W5 W6 W7 W8 W9 WHS. all: natfold_lits. pin_using (fun (AD AH ALN BU FERROR FMT FREAD HAL HFL HPL HinF LO P1 P2 P4 P5 P6 PP PPLEN PPRNG PPSEC R1 R2 R3 REALLOC SFL SNPRINTF SP47 SPM SPW TP W1 W10 W2 W5 W6 W7 W8 W9 WHS : unit) => tt).
 intros ST5 FR5 MI5 G5 PC5 AG5 HH HD Hd Hcap Hcm Hl32 OF5.
    pose proof (bv_unsigned_in_range 64 sp) as RSP. pose proof (max_snaplen_range linktype) as MSR. pose proof W1 as W1'. unfold INT_MAX in MSR, W1'.
    pose proof PC5 as PC5'.
    destruct PC5 as (Afx & Hin & (Bx' & Ix & jx' & padx & bsx' & EPB & CELLS & PRIV & BUF & PFX & IFS & WF)).
    unfold S3.F_sfpcap_nextA.TwB.p0 in *. norm_p. unfold sf_cells in PRIV. cbn [sf_hdrsize sf_lengths_swapped sf_scale_type] in PRIV.
    subst Ix. assert (EBX : Bx' = B) by congruence. subst Bx'. clear EPB.
    pose proof WF as (_ & W2' & W3 & W4 & _ & _ & _ & _ & _ & _ & _ & _ & _ & WBB). cbn [pc_bufsize pc_bufalloc pc_bufdata length] in W2', W3, W4, WBB.
    pose proof (GIo_PB_block K _ _ _ _ _ _ _ _ _ G5 ltac:(right; left; reflexivity)) as (K1 & K2 & K3 & K4 & K5 & K6).
    pose proof (GIo_PB_block K _ _ _ _ _ _ _ _ _ G5 ltac:(left; reflexivity)) as (L1 & L2 & L3 & L4 & L5 & L6).
    assert (BP' : (B + bufalloc <= P \/ P + 664 <= B)%Z).
    { pose proof (PB_apart K _ _ _ _ _ _ (pv buffer bufsize bufalloc bufdata errbuf) P B 0 G5 eq_refl) as [APB _]. unfold S3.F_sfpcap_nextA.TwB.pv, psize, is_ng in APB. cbn [pc_bufalloc pc_priv] in APB. unfold PCAP_SF_TOTAL in APB. lia. }
    unfold pcap_cells_gen, pc_pre, hdr_cells, pc_ops, np_entry, cleanup_entry, is_ng, PCAP_PRIV_OFF in CELLS.
    cbn [app pc_bufsize pc_break_loop pc_swapped pc_version_major pc_version_minor pc_snapshot pc_linktype pc_linktype_ext pc_tstamp_precision pc_header pc_priv pk_next_pcap pk_cleanup_sf PK] in CELLS.
    unfold np_norm_model, grow_buffer. cbn [mo_bind mo_ret MOps e_fenter e_fret fo_enter fo_ret fo_nop prims e_realloc prims pc_bufsize pc_snapshot pc_rfile pc_buffer pc_bufdata
      pc_self pc_bufalloc pc_swapped pc_version_major pc_version_minor pc_linktype pc_linktype_ext pc_tstamp_precision pc_break_loop pc_errbuf pc_header pc_priv].
    hide BUF. hide PRIV. hide HH. hide HD.
    pose proof (munch_refl ([] : list (Z * Z)) m5) as MU. pose proof (wmono_refl usegs m5) as WM.
    unfold implM. iprefix. step. rewrite (sx32_small bufsize) by lia.
    destruct (Z.ltb_spec bufsize cap) as [GROW|NOGROW].
    - (* [comment removed for export] *)
      replace (bufsize <? cap) with true by (symmetry; apply Z.ltb_lt; lia).
      step. if_cases Kb; try (zify_cond Kb; exfalso; (keep_hyps CEILV sp R P HA DA B bufsize bufdata cap dw GROW Kb; lia)).
      (* [comment removed for export] *)
      step.
      pose proof (max_snaplen_le linktype) as MSL. assert (R0 : (0 <= cap - 1 < 2^27)%Z) by lia.
      step. step. rewrite (srliw_or (cap + -1) 1) by lia. pose proof (lor_shr_lt (cap + -1) 1 27 ltac:(lia) ltac:(lia) ltac:(lia)) as R1'.
      set (n1 := Z.lor (cap + -1) (Z.shiftr (cap + -1) 1)) in *.
      step. step. rewrite (srliw_or n1 2) by lia. pose proof (lor_shr_lt n1 2 27 ltac:(lia) ltac:(lia) R1') as R2'.
      set (n2 := Z.lor n1 (Z.shiftr n1 2)) in *.
      step. step. rewrite (srliw_or n2 4) by lia. pose proof (lor_shr_lt n2 4 27 ltac:(lia) ltac:(lia) R2') as R3'.
      set (n3 := Z.lor n2 (Z.shiftr n2 4)) in *.
      step. step. rewrite (srliw_or n3 8) by lia. pose proof (lor_shr_lt n3 8 27 ltac:(lia) ltac:(lia) R3') as R4'.
      set (n4 := Z.lor n3 (Z.shiftr n3 8)) in *.
      step. step. rewrite (srliw_or n4 16) by lia. pose proof (lor_shr_lt n4 16 27 ltac:(lia) ltac:(lia) R4') as R5'.
      set (n5 := Z.lor n4 (Z.shiftr n4 16)) in *.
      step. rewrite (addiw_small n5 1) by lia.
      assert (RU : roundup_pow2_u32 cap = (n5 + 1)%Z).
      { unfold roundup_pow2_u32, u32. rewrite (Z.mod_small (cap - 1)) by lia. replace (cap - 1)%Z with (cap + -1)%Z by lia.
        subst n1 n2 n3 n4 n5. rewrite Z.mod_small; [reflexivity| lia]. }
      rewrite RU.
      assert (GE : (cap <= n5 + 1)%Z).
      { pose proof (lor_ge_l (cap + -1) (Z.shiftr (cap + -1) 1) ltac:(lia) ltac:(apply Z.shiftr_nonneg; lia)) as G1. fold n1 in G1.
        pose proof (lor_ge_l n1 (Z.shiftr n1 2) ltac:(lia) ltac:(apply Z.shiftr_nonneg; lia)) as G2. fold n2 in G2.
        pose proof (lor_ge_l n2 (Z.shiftr n2 4) ltac:(lia) ltac:(apply Z.shiftr_nonneg; lia)) as G3. fold n3 in G3.
        pose proof (lor_ge_l n3 (Z.shiftr n3 8) ltac:(lia) ltac:(apply Z.shiftr_nonneg; lia)) as G4. fold n4 in G4.
        pose proof (lor_ge_l n4 (Z.shiftr n4 16) ltac:(lia) ltac:(apply Z.shiftr_nonneg; lia)) as G5'. fold n5 in G5'. lia. }
      clearbody n1 n2 n3 n4 n5.
      (* [comment removed for export] *)
      assert (K44 : forall (a1'' a2'' : word) (nb : Z) (mx : mem),
        nb = (if snapshot <? n5 + 1 then snapshot else n5 + 1)%Z -> mx = m5 ->
        evt usegs (fun ms' => impl usegs (at_node usegs) (npeek usegs)
            ((' (ok, p) <- (r <- prealloc HO buffer nb ;;
                            match r with
                            | Some b => mret (true, set_buffer b nb nb (zfirstn nb bufdata) (pv buffer bufsize bufalloc bufdata errbuf))
                            | None => mret (false, set_errbuf Msg.out_of_memory (pv buffer bufsize bufalloc bufdata errbuf))
                            end) ;;
              (if negb ok then mret ((-1)%Z, mkHdr sec usec cap len, p)
               else np_read_model MOps (prims HO fo_nop sites) f p (mkHdr sec usec cap len) cap)) ps)
            (epost (fun p => POSTQ p.1 p.2)) ms')
          (MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -4208)) gp tp t0' t1' t2' (Z_to_bv 64 P) (Z_to_bv 64 HA) (Z_to_bv 64 snapshot) a1'' a2'' a3' a4' a5' a6' a7'
                   (Z_to_bv 64 DA) (Z_to_bv 64 Af) (Z_to_bv 64 nb) (Z_to_bv 64 snapshot) x4 x5 s8 s9 s10 s11 t3' t4' t5' t6') F (Z_to_bv 64 0x15d60) fc None mx (seg_rom usegs))).
      2:{ step. if_cases Kc; zify_cond Kc.
          - replace (if snapshot <? n5 + 1 then snapshot else n5 + 1)%Z with (n5 + 1)%Z by (destruct (Z.ltb_spec snapshot (n5 + 1)); lia).
            apply (K44 _ _ (n5 + 1)%Z); [destruct (Z.ltb_spec snapshot (n5 + 1)); lia | reflexivity].
          - step. replace (if snapshot <? n5 + 1 then snapshot else n5 + 1)%Z with snapshot by (destruct (Z.ltb_spec snapshot (n5 + 1)); lia).
            apply (K44 _ _ snapshot); [destruct (Z.ltb_spec snapshot (n5 + 1)); lia | reflexivity]. }
      intros a1'' a2'' nb mx Hnb ->.
      assert (NB1 : (cap <= nb <= snapshot)%Z) by (rewrite Hnb; destruct (Z.ltb_spec snapshot (n5 + 1)); lia).
      assert (NB2 : (nb <= 2^27)%Z) by (rewrite Hnb; destruct (Z.ltb_spec snapshot (n5 + 1)); lia).
      clear Hnb.
      unhide BUF.
      step. do 2 step. rewrite (zext32_shifts_lit nb) by lia. step.
      (* [comment removed for export] *)
      apply evt_done. apply (implM_bind_assoc usegs). name_sp sp (-4208)%Z. eapply (implM_bind usegs).
      { replace (CLc ++ [(self, P, 664%Z); (buffer, B, bufalloc)]) with ((CLc ++ [(self, P, 664%Z)]) ++ (buffer, B, bufalloc) :: []) in G5
          by (rewrite <- app_assoc; reflexivity).
        eapply REALLOC; [| reflexivity | reflexivity | lia | exact BUF].
        split; [exact G5|]. split; [rewrite Hsp; exact ST5|]. split; [unfold rc_lo; lia|]. split; [unfold MALLOC_STACK; rewrite Hsp; lia|].
        split; [rewrite Hsp; lia|]. split; [exact MI5|]. split; [exact TP| rewrite Hsp; apply aln16_add; [exact ALN| reflexivity]]. }
      intros [bq'|] ps6 ms6 PO; cbv beta iota in PO.
      + destruct PO as (av & m6 & E & OFr & MI6 & ST6 & AG6 & (A' & junk6 & -> & G6 & NEW)).
        unfold hpost_regs in E. all: natfold_lits. destruct_exs E. subst ms6. rewrite Hsp in *. unname_sp.
        replace (ret_pc (Z_to_bv 64 89456)) with (Z_to_bv 64 89456) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
        rewrite app_nil_r in AG6, G6.
        pose proof (GIo_block_ok K _ _ _ _ _ _ G6 ltac:(left; reflexivity)) as (N1 & N2 & N3 & N4 & N5 & N6). cbn [cb_addr cb_size fst snd] in N1, N2, N3, N4, N5, N6.
        assert (LBS : length bsx' = Z.to_nat bufalloc) by (destruct BUF as [[WFB _] _]; cbn in WFB; exact (proj1 WFB)).
        unhide PRIV. unhide HH. unhide HD.
        assert (KEEP : forall A cs, rw_cells usegs m5 A cs -> ((bv_unsigned sp + -4208 <= A) \/ (P <= A /\ A + Z.of_nat (cells_size cs) <= P + 664))%Z -> rw_cells usegs m6 A cs).
        { intros A cs HC HX. eapply agrees_rw_cells; [exact AG6 | exact HC |]. intros a Ha. destruct HX as [HX|HX]; [left; lia| right].
          apply in_block_app. right. unfold in_block. apply Exists_cons_hd. cbn [cb_addr cb_size fst snd]. lia. }
        apply KEEP in FR5; [| left; lia]. apply KEEP in HH; [| left; lia]. apply KEEP in HD; [| left; lia].
        apply KEEP in CELLS; [| right; (sl_lit_sizes; cbn [cells_size csize Nat.add]); lia]. apply KEEP in PRIV; [| right; (sl_lit_sizes; cbn [cells_size csize Nat.add]); lia]. clear KEEP.
        assert (G6' : GIo K R ps6 (CLc ++ [(self, P, 664%Z); (bq', A', nb)]) FB m6).
        { eapply (GIo_perm K HPL); [exact G6|]. rewrite app_comm_cons. change ((self, P, 664%Z) :: [(bq', A', nb)]) with ([(self, P, 664%Z)] ++ [(bq', A', nb)]).
          rewrite app_assoc. apply Permutation.Permutation_cons_append. }
        assert (AG06 : agrees_on (fun a => client_keeps CLc (bv_unsigned sp) a /\ ~ (HA <= a < HA + 24) /\ ~ (DA <= a < DA + 8))%Z m m6).
        { eapply agrees_on_trans; [exact AG5|]. eapply agrees_on_weaken; [exact AG6|]. intros a [[Ha|Ha] _]; [left; lia| right; apply in_block_app; left; exact Ha]. }
        pose proof (PB_apart K _ _ _ _ _ _ (pv bq' nb nb (zfirstn nb bufdata) errbuf) P A' 0 G6' eq_refl) as [APB' _].
        unfold S3.F_sfpcap_nextA.TwB.pv, psize, is_ng in APB'. cbn [pc_bufalloc pc_priv] in APB'. unfold PCAP_SF_TOTAL in APB'.
        clear AG6 G6 ST5 MI5 AG5 PC5' G5 BUF MU WM.
        eapply (implM_retb usegs). cbv beta iota. cbn [negb set_buffer pc_self pc_rfile pc_swapped pc_version_major pc_version_minor pc_snapshot pc_linktype pc_linktype_ext
                                                    pc_tstamp_precision pc_break_loop pc_errbuf pc_header pc_priv].
        hide NEW. hide PRIV. hide HH. hide HD.
        pose proof (munch_refl [(P + 20, P + 32)]%Z m6) as MU. pose proof (wmono_refl usegs m6) as WM.
        unfold implM. iprefix. step. if_cases Kz; try (zify_cond Kz; exfalso; (keep_hyps CEILV sp R P HA DA B bufalloc bufdata dw bsx' A' N1 Kz; lia)).
        step. step.
        unhide NEW. unhide PRIV. unhide HH. unhide HD.
        lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
          assert (AGP : agrees_on (fun a => outside [(P + 20, P + 32)]%Z a) m6 mm) by (eapply agrees_on_of_munch; [exact MU | exact WM | intros a _ Ho; exact Ho]);
          rename mm into m6' end.
        apply (agrees_rw_cells _ _ _ _ _ AGP) in NEW; [| intros a Ha; (sl_lit_sizes_in Ha; sl_lit_sizes; cbn [outside cells_size csize Nat.add] in Ha |- *); clear - Ha APB' W1' W3; lia].
        apply (agrees_rw_cells _ _ _ _ _ AGP) in HH; [| intros a Ha; (sl_lit_sizes_in Ha; sl_lit_sizes; cbn [outside cells_size csize Nat.add] in Ha |- *); unfold rc_lo in LO; lia].
        apply (agrees_rw_cells _ _ _ _ _ AGP) in HD; [| intros a Ha; cbn [cells_size] in Ha; rewrite Hd in Ha; cbn [outside]; unfold rc_lo in LO; lia].
        apply (agrees_rw_cells _ _ _ _ _ AGP) in PRIV; [| intros a Ha; (sl_lit_sizes_in Ha; sl_lit_sizes; cbn [outside cells_size csize Nat.add] in Ha |- *); lia].
        assert (G6'' : GIo K R ps6 (CLc ++ [(self, P, 664%Z); (bq', A', nb)]) FB m6').
        { eapply (GIo_pcap_frame K HFL SFL); [exact G6' | exact MU | exact WM |].
          apply Forall_cons; [| apply Forall_nil]. right. unfold iv_in_block. apply Exists_cons_hd. cbn [cb_addr cb_size fst snd]. lia. }
        assert (AG06' : agrees_on (fun a => client_keeps CLc (bv_unsigned sp) a /\ ~ (HA <= a < HA + 24) /\ ~ (DA <= a < DA + 8))%Z m m6').
        { eapply agrees_on_trans; [exact AG06|]. eapply agrees_on_weaken; [exact AGP|]. intros a [[Ha|Ha] _]; cbn [outside]; [unfold rc_lo in LO; lia|].
          destruct (np_CLc_facts _ _ _ _ G6' Ha) as [Hc Hnb]. split; [| exact Logic.I]. intros Hin'. apply Hnb. unfold in_block. apply Exists_cons_hd. cbn [cb_addr cb_size fst snd]. lia. }
        merge_all NEW. replace (Z.to_nat (bufalloc `min` nb) + (Z.to_nat (nb - bufalloc `min` nb) + 0))%nat with (Z.to_nat nb) in NEW by (keep_hyps CEILV sp R lo P HA DA B bufalloc bufdata dw nb A' bsx' K3; lia). rewrite app_nil_r in NEW.
        apply evt_done. eapply (np_nread _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m6' ps6 bq' A' nb nb (zfirstn nb bufdata) errbuf sec usec cap len dw fj);
          [exact ST6 | exact FR5 | exact MI6 | exact G6'' | | exact AG06' | exact HH | exact HD | exact Hd | lia | lia | exact Hl32 | congruence].
        exists Afx. split; [exact Hin|]. exists A', 0%Z, jx', padx, (firstn (Z.to_nat (bufalloc `min` nb)) bsx' ++ junk6).
        split; [reflexivity|]. split; [exact CELLS|]. split; [unfold PCAP_PRIV_OFF; exact PRIV|]. split; [unfold S3.F_sfpcap_nextA.TwB.pv; cbn [pc_bufalloc]; exact NEW|].
        split; [unfold S3.F_sfpcap_nextA.TwB.pv, zfirstn; cbn [pc_bufdata]; apply pfx_realloc; [exact PFX | (keep_hyps CEILV sp R lo P HA DA B bufsize bufalloc bufdata snapshot cap dw nb A' bsx' W4; lia) | (keep_hyps CEILV sp R lo P HA DA B bufalloc bufdata dw nb A' bsx' LBS; lia)]|].
        split; [reflexivity|].
        unfold pcap_wf, S3.F_sfpcap_nextA.TwB.pv in *. cbn [pc_snapshot pc_bufsize pc_bufalloc pc_bufdata pc_break_loop pc_tstamp_precision pc_version_major pc_version_minor
                                   pc_linktype pc_linktype_ext pc_header pc_priv sf_hdrsize] in *.
        pose proof (zfirstn_length_le' nb bufdata) as ZL. unfold zfirstn. rewrite length_firstn. repeat split; try (keep_hyps CEILV sp R P HA DA B bufalloc bufdata snapshot dw nb A' bsx' W1 N3 NB2 lo brk W5 prec W6 vmaj W7 vmin W8 linktype W9 ltext W10 bufsize header hdrsize WF WHS; lia); try tauto.
      + (* [comment removed for export] *)
        destruct PO as (av & m6 & E & OFr & MI6 & ST6 & AG6 & -> & G6 & BUF6 & EN6).
        unfold hpost_regs in E. all: natfold_lits. destruct_exs E. subst ms6. rewrite Hsp in *. unname_sp.
        replace (ret_pc (Z_to_bv 64 89456)) with (Z_to_bv 64 89456) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
        rewrite app_nil_r in AG6.
        replace ((CLc ++ [(self, P, 664%Z)]) ++ [(buffer, B, bufalloc)]) with (CLc ++ [(self, P, 664%Z); (buffer, B, bufalloc)]) in G6 by (rewrite <- app_assoc; reflexivity).
        unhide PRIV. unhide HH. unhide HD.
        assert (KEEP : forall A cs, rw_cells usegs m5 A cs -> ((bv_unsigned sp + -4208 <= A) \/ (P <= A /\ A + Z.of_nat (cells_size cs) <= P + 664))%Z -> rw_cells usegs m6 A cs).
        { intros A cs HC HX. eapply agrees_rw_cells; [exact AG6 | exact HC |]. intros a Ha. destruct HX as [HX|HX]; [left; lia| right].
          apply in_block_app. right. unfold in_block. apply Exists_cons_hd. cbn [cb_addr cb_size fst snd]. lia. }
        apply KEEP in FR5; [| left; lia]. apply KEEP in HH; [| left; lia]. apply KEEP in HD; [| left; lia].
        apply KEEP in CELLS; [| right; (sl_lit_sizes; cbn [cells_size csize Nat.add]); lia]. apply KEEP in PRIV; [| right; (sl_lit_sizes; cbn [cells_size csize Nat.add]); lia]. clear KEEP.
        assert (AG06 : agrees_on (fun a => client_keeps CLc (bv_unsigned sp) a /\ ~ (HA <= a < HA + 24) /\ ~ (DA <= a < DA + 8))%Z m m6).
        { eapply agrees_on_trans; [exact AG5|]. eapply agrees_on_weaken; [exact AG6|]. intros a [[Ha|Ha] _]; [left; lia| right; apply in_block_app; left; exact Ha]. }
        assert (PC6 : PCAPR (hptr:=hptr) P (pv buffer bufsize bufalloc bufdata errbuf) [(self, P, 664%Z); (buffer, B, bufalloc)] FB m6).
        { exists Afx. split; [exact Hin|]. exists B, 0%Z, jx', padx, bsx'. split; [reflexivity|].
          split; [unfold S3.F_sfpcap_nextA.TwB.pv, pcap_cells, pcap_cells_gen, pc_pre, hdr_cells, pc_ops, np_entry, cleanup_entry, is_ng, PCAP_PRIV_OFF;
                  cbn [app pc_bufsize pc_break_loop pc_swapped pc_version_major pc_version_minor pc_snapshot pc_linktype pc_linktype_ext pc_tstamp_precision pc_header pc_priv pk_next_pcap pk_cleanup_sf PK]; exact CELLS|].
          split; [unfold PCAP_PRIV_OFF; exact PRIV|]. split; [exact BUF6|]. split; [exact PFX|]. split; [reflexivity| exact WF]. }
        clear AG6 ST5 MI5 AG5 PC5' G5 BUF MU WM.
        (* [comment removed for export] *)
        pose proof PC6 as (Afy & _ & (By & Iy & jy & pady & bsy & EPBy & CELLSy & _ & _ & _ & _ & _)).
        apply pcap_cells_split4 in CELLSy as (_ & CE & _ & _); [|reflexivity].
        apply (rw_cells_split_CB usegs m6 _ [] 304 _ [] [14; 242; 48]%nat) in CE; [|reflexivity]. cbn [mk_CB_cells app] in CE.
        destruct (rw_cells_cut _ _ _ 1 CE) as [CE1 CE']. (sl_lit_sizes_in CE1; sl_lit_sizes_in CE'; cbn [firstn skipn cells_size csize Nat.add] in CE1, CE').
        destruct (rw_cells_cut _ _ _ 1 CE') as [CE2 _]. clear CE CE'. (sl_lit_sizes_in CE2; cbn [firstn skipn cells_size csize Nat.add] in CE2).
        replace (P + 216 + Z.of_nat 14)%Z with (P + 230)%Z in CE2 by lia.
        eapply (implM_retb usegs). cbv beta iota. cbn [negb].
        assert (LENM : length (map b8 Msg.out_of_memory ++ [Z_to_bv 8 0]) = 14%nat) by (vm_compute; reflexivity).
        hide PRIV. hide HH. hide HD. hide CELLS. hide CE2. hide BUF6.
        pose proof (munch_refl [(P + 216, P + 216 + 14)]%Z m6) as MU. pose proof (wmono_refl usegs m6) as WM.
        unfold implM. iprefix. step. if_true. do 5 step.
        call (memcpy_specZ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (P + 216)%Z 0x10df2%Z 14%Z (map b8 Msg.out_of_memory ++ [Z_to_bv 8 0]) (firstn 14 (pj_g jy)));
          [reflexivity | reflexivity | reflexivity
          | exact (ro_cells_bytes_at _ _ _ _ (ro_cells_image usegs m6 0x10df2 (map b8 Msg.out_of_memory ++ [Z_to_bv 8 0]) MI6 ltac:(vm_compute; reflexivity) ltac:((keep_hyps CEILV sp R P HA DA B bufdata dw; lia)) ltac:(rewrite LENM; cbn; (keep_hyps CEILV sp R P HA DA B bufdata dw; lia))))
          | rewrite LENM; reflexivity | (keep_hyps CEILV sp R P HA DA B bufdata dw; lia) | exact CE1 | unfold rc_lo in LO; (keep_hyps CEILV sp R P HA DA B bufdata dw L5; lia) | (keep_hyps CEILV H hptr K sp R CLc FB lo P HA DA B self buffer bufalloc bufdata dw m6 ps6 L4; lia) | (keep_hyps CEILV sp R P HA DA B bufdata dw; lia) | exact MI6 |].
        unhide PRIV. unhide HH. unhide HD. unhide CELLS. unhide CE2. unhide BUF6.
        lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
          assert (AGW : agrees_on (fun a => outside [(P + 216, P + 216 + 14)]%Z a) m6 mm) by (eapply agrees_on_of_munch; [exact MU | exact WM | intros a _ Ho; exact Ho]);
          rename mm into m7 end.
        apply (agrees_rw_cells _ _ _ _ _ AGW) in HH; [| intros a Ha; (cl_lit_hyps; sl_lit_sizes; cbn [outside cells_size csize Nat.add] in *); unfold rc_lo in LO; lia].
        apply (agrees_rw_cells _ _ _ _ _ AGW) in HD; [| intros a Ha; (cl_lit_hyps; sl_lit_sizes; cbn [outside cells_size csize Nat.add] in *); unfold rc_lo in LO; lia].
        apply (agrees_rw_cells _ _ _ _ _ AGW) in CE2; [| intros a Ha; (cl_lit_hyps; sl_lit_sizes; cbn [outside cells_size csize Nat.add] in *); lia].
        assert (G7 : GIo K R ps6 (CLc ++ [(self, P, 664%Z); (buffer, B, bufalloc)]) FB m7).
        { eapply (GIo_pcap_frame K HFL SFL); [exact G6 | exact MU | exact WM |].
          apply Forall_cons; [| apply Forall_nil]. right. unfold iv_in_block. apply Exists_cons_hd. cbn [cb_addr cb_size fst snd]. lia. }
        assert (PC7 : PCAPR (hptr:=hptr) P (pv buffer bufsize bufalloc bufdata Msg.out_of_memory) [(self, P, 664%Z); (buffer, B, bufalloc)] FB m7).
        { lazymatch goal with PCm : rw_cells usegs m7 (P + 216)%Z _ |- _ =>
            pose proof (rw_cells_uncut _ _ _ _ _ PCm CE2 ltac:(cbn; lia)) as EB7 end.
          change (pv buffer bufsize bufalloc bufdata Msg.out_of_memory) with (set_errbuf Msg.out_of_memory (pv buffer bufsize bufalloc bufdata errbuf)).
          eapply (PCAPR_errbuf _ _ _ _ _ _ _ _ _ _ _ _ G6 PC6 AGW); [| exact EB7 | rewrite cells_size_app; cbn; lia].
          intros a Ha Hn. cbn [outside]. (keep_hyps CEILV sp R P HA DA B bufdata dw a Hn; lia). }
        assert (AG07 : agrees_on (fun a => client_keeps CLc (bv_unsigned sp) a /\ ~ (HA <= a < HA + 24) /\ ~ (DA <= a < DA + 8))%Z m m7).
        { eapply agrees_on_trans; [exact AG06|]. eapply agrees_on_weaken; [exact AGW|]. intros a [[Ha|Ha] _]; cbn [outside]; [unfold rc_lo in LO; lia|].
          destruct (np_CLc_facts _ _ _ _ G6 Ha) as [Hc Hnb]. split; [| exact Logic.I]. intros Hin'. apply Hnb. unfold in_block. apply Exists_cons_hd. cbn [cb_addr cb_size fst snd]. lia. }
        step. apply evt_done.
        eapply np_fail_tail; [eassumption | exact FR5 | eassumption | ].
        split; [exact G7|]. split; [unfold S3.F_sfpcap_nextA.TwB.pv in PC7; cbn [set_errbuf] ; exact PC7|]. split; [exact AG07|]. split; [exact HH|]. split; [reflexivity|]. split; [exact HD|]. split; [exact Hd| congruence].
    - (* [comment removed for export] *)
      apply evt_done. eapply (implM_retb usegs). cbv beta iota. cbn [negb].
      unfold implM. iprefix. step. if_cases Kb; try (zify_cond Kb; exfalso; (keep_hyps CEILV sp R P HA DA B bufsize bufdata cap dw NOGROW Kb; lia)).
      unhide BUF. unhide PRIV. unhide HH. unhide HD.
      apply evt_done. eapply (np_nread _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m5 ps buffer B bufsize bufalloc bufdata errbuf sec usec cap len dw fj);
        [exact ST5 | exact FR5 | exact MI5 | exact G5 | exact PC5' | exact AG5 | exact HH | exact HD | exact Hd | lia | lia | exact Hl32 | exact OF5].
  Qed.
  End Sz6.
  Lemma np_normal : ltac:(let t := eval cbv delta [np_normal__stmt] in np_normal__stmt in exact t).
  Proof using AD AH ALN BU FERROR FMT FREAD HAL HFL HPL HinF LO P1 P2 P4 P5 P6 PP PPLEN PPRNG PPSEC R1 R2 R3 REALLOC SFL SNPRINTF SP47 SPM SPW TP W1 W10 W2 W5 W6 W7 W8 W9 WHS. all: natfold_lits. intros ra' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' x4 x5 t3' t4' t5' t6' m5 ps sec usec cap len dw fj. ltac2:(SecDiet.SzSec.closeP 'np_normal__body "vvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.
End NpCtxA2.

End WithCeil.
End F_sfpcap_nextA2.

(* [comment removed for export] *)
Module F_sfpcapng_chkK.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool String Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import Tac Arr Bytes ZBridge ITree Nodes Decode SysStep MonadX Image ImgTgtUbsan.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Prelim Monad Fmt StdioCore Stdio PcapPrelim PcapTypes PcapPure Pcap Prog. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Adapter__Spec. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Monad OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Fmt OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.StdioCore OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Stdio OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapPrelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapTypes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapPure OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Pcap OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prog OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Adapter__Spec.StartupModel.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require Printf_kit__Musl. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require AmoStep__Musl. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_kit__Musl.StartupKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.CellsExtra.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require GI PcapRep. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.GI.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.PcapRep.TwB.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_memchr__S3. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_memchr__S3.SfKit.
From OSSVerify.libpcap.fuzz_pcap.images Require Import Ubsan.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import Ceiling.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import LiaPin.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac lia_e2w2_base := first [ zify_prune; zify_noeuclid; Z.euclidean_division_equations_cleanup; xlia zchecker
                                 | zify_prune; Zify.zify; xlia zchecker | Zify.zify; xlia zchecker ].
Local Ltac ceil_mentioned := lazymatch goal with | |- context [@alloc_ceiling _] => idtac | _ : context [@alloc_ceiling _] |- _ => idtac end.
(* [comment removed for export] *)
Local Ltac gio_ceil_fact :=
  match goal with
  | G : GIo _ _ _ _ _ _ |- _ => let H := fresh "CLO__" in pose proof (S3.PcapRep.TwB.GIo_ceil_lo _ _ _ _ _ _ G) as H; unfold rc_lo in H
  end.
(* [comment removed for export] *)
Local Ltac lia ::= clear_unpinned; try gio_ceil_fact; try (ceil_ok; ceil_mentioned; ceil_facts); pinned_lia_core.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Ltac msg_ok := vm_compute; repeat first [apply Forall_nil | apply Forall_cons; [split; reflexivity|]].

Section WithCeil.
Context {CEILV : CEIL}.
Lemma le4_le_bytes : forall x, 0 <= x < 2^32 -> le4 (Z_to_bv 64 x) = map b8 (le_bytes 4 x).
Proof using Type. pin_using tt.
  intros x Hx. unfold le_bytes. cbn [le_bytes_nat Z.to_nat Pos.to_nat Pos.iter_op Nat.add map].
  rewrite (le4_of_val _ (x mod 256) (x / 256 mod 256) (x / 256 / 256 mod 256) (x / 256 / 256 / 256 mod 256) 0);
    [reflexivity | | | | | lia |]; try (Z.div_mod_to_equations; lia).
  rewrite unsigned_lit by lia. Z.div_mod_to_equations. lia.
Qed.

Lemma le4_mod32 : forall x y, 0 <= x < 2^32 -> 0 <= y < 2^32 -> le4 (Z_to_bv 64 (x + 4294967296 * y)) = le4 (Z_to_bv 64 x).
Proof using Type. pin_using tt.
  intros x y Hx Hy. unfold le4. rewrite !unsigned_lit by lia.
  cbn [Z_to_le_bytes]. rewrite !Z.shiftr_shiftr, !Z.shiftr_div_pow2 by lia. cbn [Z.add Z.pow Z.pow_pos Pos.iter Z.mul].
  f_equal; [apply Z_to_bv8_mod; Z.div_mod_to_equations; lia|]. f_equal; [apply Z_to_bv8_mod; Z.div_mod_to_equations; lia|].
  f_equal; [apply Z_to_bv8_mod; Z.div_mod_to_equations; lia|]. f_equal. apply Z_to_bv8_mod. Z.div_mod_to_equations; lia.
Qed.

Lemma le_bytes_4_range : forall x, Forall (fun z => 0 <= z < 256) (le_bytes 4 x).
Proof using Type. pin_using tt.
  intros x. unfold le_bytes. cbn [le_bytes_nat Z.to_nat Pos.to_nat Pos.iter_op Nat.add].
  repeat constructor; Z.div_mod_to_equations; lia.
Qed.

Lemma length_le_bytes : forall k x, length (le_bytes k x) = Z.to_nat k.
Proof using Type. pin_using tt. intros k x. unfold le_bytes. generalize x. induction (Z.to_nat k) as [|n IH]; intros; cbn; [reflexivity| now rewrite IH]. Qed.

Lemma Z_to_bv_s32_inj : forall x y, 0 <= x < 2^32 -> 0 <= y < 2^32 -> Z_to_bv 64 (s32 x) = Z_to_bv 64 (s32 y) -> x = y.
Proof using Type. pin_using tt.
  intros x y Hx Hy E. apply (f_equal bv_unsigned) in E. rewrite !unsigned_lit_wrap in E. unfold s32 in E.
  Z.div_mod_to_equations. lia.
Qed.

Lemma eqb_s32 : forall x y, 0 <= x < 2^32 -> 0 <= y < 2^32 -> bv_eqb (Z_to_bv 64 (s32 x)) (Z_to_bv 64 (s32 y)) = (x =? y).
Proof using Type. pin_using tt.
  intros x y Hx Hy. destruct (Z.eqb_spec x y) as [->|NE]; [apply Z.eqb_refl|].
  unfold bv_eqb. apply Z.eqb_neq. intros E. apply NE. apply (Z_to_bv_s32_inj x y Hx Hy). apply bv_eq. exact E.
Qed.

Lemma swrap32_low : forall u x hi, u = x + 4294967296 * hi -> Z_to_bv 64 (bv_swrap 32 (u + 0)) = Z_to_bv 64 (s32 x).
Proof using Type. pin_using tt.
  intros u x hi ->. f_equal. unfold bv_swrap, bv_wrap, s32, bv_half_modulus, bv_modulus. cbn -[Z.add Z.sub Z.modulo Z.mul].
  Z.div_mod_to_equations. lia.
Qed.

Lemma firstn_len_app : forall {X} (l1 l2 : list X), firstn (length l1) (l1 ++ l2) = l1.
Proof using Type. pin_using tt. intros X l1 l2. rewrite firstn_app, Nat.sub_diag, firstn_all by lia. cbn. apply app_nil_r. Qed.

Lemma skipn_len_app : forall {X} (l1 l2 : list X), skipn (length l1) (l1 ++ l2) = l2.
Proof using Type. pin_using tt. intros X l1 l2. rewrite skipn_app, Nat.sub_diag, skipn_all by lia. reflexivity. Qed.

Lemma firstn_len_app' : forall {X} (l1 l2 : list X) n, n = length l1 -> firstn n (l1 ++ l2) = l1.
Proof using Type. pin_using tt. intros X l1 l2 n ->. apply firstn_len_app. Qed.

Definition out_of_image (A n : Z) : Prop := A + n <= 0x10000 \/ 0x56000 <= A.


Lemma zslice_at {A} (pre l post : list A) : zslice (Z.of_nat (length pre)) (Z.of_nat (length l)) (pre ++ l ++ post) = l.
Proof using Type. pin_using tt.
  unfold zslice, zfirstn, zskipn. rewrite !Nat2Z.id, skipn_app, skipn_all, Nat.sub_diag. unfold skipn. cbn.
  rewrite firstn_app, firstn_all, Nat.sub_diag by lia. cbn. apply app_nil_r.
Qed.

Lemma get_le16_at pre u0 u1 rest : get_le16 (pre ++ u0 :: u1 :: rest) (Z.of_nat (length pre)) = u0 + 256 * u1.
Proof using Type. pin_using tt.
  unfold get_le16. change (pre ++ u0 :: u1 :: rest) with (pre ++ [u0; u1] ++ rest). change 2 with (Z.of_nat (length [u0; u1])).
  rewrite zslice_at. cbn. lia.
Qed.

Lemma get_le16_at2 pre u0 u1 u2 u3 rest : get_le16 (pre ++ u0 :: u1 :: u2 :: u3 :: rest) (Z.of_nat (length pre) + 2) = u2 + 256 * u3.
Proof using Type. pin_using tt.
  replace (pre ++ u0 :: u1 :: u2 :: u3 :: rest) with ((pre ++ [u0; u1]) ++ u2 :: u3 :: rest) by (rewrite <- app_assoc; reflexivity).
  replace (Z.of_nat (length pre) + 2) with (Z.of_nat (length (pre ++ [u0; u1]))) by (rewrite length_app; cbn; lia). apply get_le16_at.
Qed.

Lemma swap2_at pre u0 u1 rest : swap_field 2 (Z.of_nat (length pre)) (pre ++ u0 :: u1 :: rest) = pre ++ u1 :: u0 :: rest.
Proof using Type. pin_using tt.
  unfold swap_field.
  replace (zslice (Z.of_nat (length pre)) 2 (pre ++ u0 :: u1 :: rest)) with [u0; u1] by (symmetry; exact (zslice_at pre [u0; u1] rest)).
  unfold buf_write_at, zfirstn, zskipn, zlength. cbn [rev app length].
  rewrite Nat2Z.id, firstn_app, Nat.sub_diag, firstn_all. cbn [firstn]. rewrite app_nil_r.
  replace (Z.to_nat (Z.of_nat (length pre) + Z.of_nat 2)) with (length pre + 2)%nat by lia.
  rewrite skipn_app, skipn_all2 by lia. replace (length pre + 2 - length pre)%nat with 2%nat by lia. reflexivity.
Qed.

Lemma swap2_at2 pre u0 u1 u2 u3 rest : swap_field 2 (Z.of_nat (length pre) + 2) (pre ++ u0 :: u1 :: u2 :: u3 :: rest) = pre ++ u0 :: u1 :: u3 :: u2 :: rest.
Proof using Type. pin_using tt.
  replace (pre ++ u0 :: u1 :: u2 :: u3 :: rest) with ((pre ++ [u0; u1]) ++ u2 :: u3 :: rest) by (rewrite <- app_assoc; reflexivity).
  replace (Z.of_nat (length pre) + 2) with (Z.of_nat (length (pre ++ [u0; u1]))) by (rewrite length_app; cbn; lia).
  rewrite swap2_at, <- app_assoc. reflexivity.
Qed.

Lemma pfx_decomp (pre mid post : list Z) (bs : list byte) :
  firstn (length (pre ++ mid ++ post)) bs = map b8 (pre ++ mid ++ post) ->
  exists bsr, bs = map b8 pre ++ map b8 mid ++ bsr /\ firstn (length post) bsr = map b8 post.
Proof using Type. pin_using tt.
  intros H. set (k := (length pre + length mid)%nat). exists (skipn k bs).
  assert (Hk : firstn k bs = map b8 pre ++ map b8 mid).
  { transitivity (firstn k (firstn (length (pre ++ mid ++ post)) bs)).
    - rewrite firstn_firstn. f_equal. rewrite !length_app. lia.
    - rewrite H, !map_app, app_assoc, firstn_app, firstn_all2 by (rewrite !length_app, !length_map; lia).
      rewrite length_app, !length_map. replace (k - (length pre + length mid))%nat with 0%nat by lia. cbn. apply app_nil_r. }
  split.
  - rewrite <- (firstn_skipn k bs) at 1. rewrite Hk, <- app_assoc. reflexivity.
  - rewrite firstn_skipn_comm. replace (k + length post)%nat with (length (pre ++ mid ++ post)) by (rewrite !length_app; lia).
    rewrite H, !map_app, app_assoc, skipn_app, skipn_all2 by (rewrite length_app, !length_map; lia).
    rewrite length_app, !length_map. replace (k - (length pre + length mid))%nat with 0%nat by lia. reflexivity.
Qed.

Lemma pfx_comp (pre mid post : list Z) (bsr : list byte) :
  firstn (length post) bsr = map b8 post ->
  firstn (length (pre ++ mid ++ post)) (map b8 pre ++ map b8 mid ++ bsr) = map b8 (pre ++ mid ++ post).
Proof using Type. pin_using tt.
  intros H. rewrite !length_app, !map_app.
  rewrite firstn_app, length_map, firstn_all2 by (rewrite length_map; lia). f_equal.
  rewrite firstn_app, length_map, firstn_all2 by (rewrite length_map; lia). f_equal.
  replace (length pre + (length mid + length post) - length pre - length mid)%nat with (length post) by lia. exact H.
Qed.

Lemma split_at8 (buf : list Z) (off : nat) : (off + 8 <= length buf)%nat ->
  exists pre v0 v1 v2 v3 v4 v5 v6 v7 post, buf = pre ++ v0 :: v1 :: v2 :: v3 :: v4 :: v5 :: v6 :: v7 :: post /\ length pre = off.
Proof using Type. pin_using tt.
  intros Hl. exists (firstn off buf).
  destruct (skipn off buf) as [|v0 [|v1 [|v2 [|v3 [|v4 [|v5 [|v6 [|v7 post]]]]]]]] eqn:E;
    try (apply (f_equal (@length Z)) in E; rewrite length_skipn in E; cbn in E; lia).
  exists v0, v1, v2, v3, v4, v5, v6, v7, post. split; [| apply firstn_length_le; lia]. rewrite <- E. symmetry. apply firstn_skipn.
Qed.

Lemma swap16_val a b : 0 <= a < 256 -> 0 <= b < 256 ->
  Z.lor ((a + 256 * b) * 2 ^ 8) ((a + 256 * b) / 2 ^ 8) = b + 256 * a + 65536 * b.
Proof using Type. pin_using tt.
  intros Ha Hb. replace ((a + 256 * b) / 2 ^ 8) with b by (Z.div_mod_to_equations; lia).
  rewrite lor_high_low by lia. lia.
Qed.

Lemma Z_to_bv64_mod x y : x mod 2^64 = y mod 2^64 -> Z_to_bv 64 x = Z_to_bv 64 y.
Proof using Type. pin_using tt. intros E. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. cbn [Z.of_N Z.pow_pos Pos.iter Z.mul]. cbn in E. exact E. Qed.
Lemma Z_to_bv64_drop x k : Z_to_bv 64 (x + k * 2^64) = Z_to_bv 64 x.
Proof using Type. pin_using tt. apply Z_to_bv64_mod. rewrite Z_mod_plus_full. reflexivity. Qed.

Lemma swap16_shl48 a b : 0 <= a < 256 -> 0 <= b < 256 ->
  Z_to_bv 64 (Z.shiftl (bv_unsigned (Z_to_bv 64 (a + 256 * b + 65536 * a))) 48) = Z_to_bv 64 ((a + 256 * b) * 2 ^ 48).
Proof using Type. pin_using tt.
  intros Ha Hb. rewrite unsigned_lit by lia. rewrite Z.shiftl_mul_pow2 by lia.
  replace ((a + 256 * b + 65536 * a) * 2 ^ 48) with ((a + 256 * b) * 2 ^ 48 + a * 2 ^ 64) by lia. apply Z_to_bv64_drop.
Qed.

Lemma shr48_of_shl48 x : 0 <= x < 65536 -> Z_to_bv 64 (Z.shiftr (bv_unsigned (Z_to_bv 64 (x * 2 ^ 48))) 48) = Z_to_bv 64 x.
Proof using Type. pin_using tt. intros Hx. rewrite unsigned_lit by lia. rewrite Z.shiftr_div_pow2, Z.div_mul by lia. reflexivity. Qed.

Lemma get_le32_at pre v0 v1 v2 v3 rest :
  get_le32 (pre ++ v0 :: v1 :: v2 :: v3 :: rest) (Z.of_nat (length pre)) = le4val v0 v1 v2 v3.
Proof using Type. pin_using tt.
  unfold get_le32. change (pre ++ v0 :: v1 :: v2 :: v3 :: rest) with (pre ++ [v0; v1; v2; v3] ++ rest).
  change 4%Z with (Z.of_nat (length [v0; v1; v2; v3])). rewrite zslice_at. cbn -[Z.add Z.mul]. unfold le4val. lia.
Qed.

End WithCeil.
End F_sfpcapng_chkK.
