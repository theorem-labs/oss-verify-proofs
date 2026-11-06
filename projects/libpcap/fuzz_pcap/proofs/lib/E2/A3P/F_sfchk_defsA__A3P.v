(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Lia.
(* [comment removed for export] *)
From Stdlib Require ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Tac Arr Bytes ZBridge ITree Nodes Decode SysStep Frame StoreFast.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Prelim Monad Fmt StdioCore Stdio PcapPrelim PcapTypes PcapPure Pcap Prog.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require FileCells__Musl.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require Printf_kit__Musl.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require AmoStep__Musl.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require ExecF ITreeA Shadow StepF SysStepF RunDraw.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AImg ABase AMalloc_iface.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_memchr__S3.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require CkTac__A3P.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require MonadG GIA PcapRepA UnwKit.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require MonadGX__A3P.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require Pcap_ifaceA.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require FrameKit__A3P.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require F_ngchk_defsA__A3P.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require SecDiet.
From Stdlib Require String.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Image.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require FmtFacts__S3.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require Pcap_iface_ngA Pcap_iface_ppA LibcKit.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require FmtKitA.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Module F_sfchk_defsA.
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
Definition chk_shadow : list cell :=
  [C1 (Z_to_bv 8 18446744073709551601); C1 (Z_to_bv 8 18446744073709551601); C1 (Z_to_bv 8 18446744073709551601); C1 (Z_to_bv 8 18446744073709551601);
   C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0);
   C1 (Z_to_bv 8 18446744073709551603); C1 (Z_to_bv 8 18446744073709551603); C1 (Z_to_bv 8 18446744073709551603); C1 (Z_to_bv 8 18446744073709551603);
   C1 (Z_to_bv 8 18446744073709551603); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)].

Section CANSEC1. Context {rc : runConstT} {tlsI : ABase.atlsT}.
Section ChkDefs.
  Context {H hptr : Type} (HO : HeapOps H hptr) (FO : @FrameOps H hptr) (sites : stack_site -> Z).
  Variable GIOA : alayout -> footprint -> PState H hptr -> list (@cblock hptr) -> list (@cblock hptr) -> list fblock -> mem -> Prop.
  Variable TP : tparams.
  Variable fflagA : alayout -> fframe -> Z -> Z.

  (* [comment removed for export] *)
  Definition chk_ctx (ra sp tp s0 : word) (L : alayout) (RNG : footprint) (CL FB : list (@cblock hptr)) (FL : list fblock) (trC : list Z)
      (lo MG FA EB ERR SPA Fb : Z) (f : hptr) (magic : list Z) (m : mem) : Prop :=
    (ATOP + 4096 <= lo)%Z /\ (lo + PCAP_L2_STACK <= bv_unsigned sp)%Z /\ (bv_unsigned sp + 16 < al_top L /\ al_top L <= 2^47)%Z
    /\ tp = Z_to_bv 64 ATP /\ (bv_unsigned sp mod 16 = 0)%Z
    /\ (rng RNG lo (al_top L - lo) /\ rng_aimg RNG /\ rng_aimg_sh RNG /\ rng_atls RNG)
    /\ ucallerA (depth_check_header false) L m sp s0 ra trC /\ traces_check_header TP false L (bv_unsigned ra) trC
    /\ nofr (frames_check_header false) FL /\ In (f, FA, FILE_BLOCK) FB
    /\ Forall (fun z => 0 <= z < 256)%Z magic /\ length magic = 4%nat
    /\ cobjA RNG m FL CL MG 4 /\ cobjA RNG m FL CL ERR 4 /\ (MG + 4 <= ERR \/ ERR + 4 <= MG)%Z
    /\ cobjA RNG m FL CL EB 256 /\ (EB + 256 <= ERR \/ ERR + 4 <= EB)%Z /\ (EB + 256 <= MG \/ MG + 4 <= EB)%Z
    /\ (ERR mod 4 = 0)%Z /\ (EB mod 8 = 0)%Z
    /\ (bv_unsigned sp - 208 <= SPA <= bv_unsigned sp - 192)%Z /\ (SPA mod 32 = 0)%Z.

  (* [comment removed for export] *)
  Definition chk_inv (ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (L : alayout) (RNG : footprint) (CL FB : list (@cblock hptr)) (FL : list fblock)
      (lo MG EB ERR SPA Fb : Z) (magic : list Z) (o : option hptr) (m : mem)
      (RNGx : footprint) (sx : PState H hptr) (PB : list (@cblock hptr)) (mm : mem) : Prop :=
    fp_le RNG RNGx /\ GIOA L RNGx sx (CL ++ PB) FB ((FF_CHECK_HEADER, Fb, 128%Z) :: FL) mm /\ ps_outfile sx = o /\ mem_inv asegs mm
    /\ stk asegs mm lo SPA /\ stk asegs mm (SPA + 88) (bv_unsigned sp + -104)
    /\ rw_cells asegs mm (bv_unsigned sp + -104) [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]
    /\ agrees_on (fun a => client_keeps FL CL (bv_unsigned sp) a /\ outside [(ERR, ERR + 4); (EB, EB + 256)]%Z a) m mm
    /\ rw_cells asegs mm MG (map (fun z => C1 (b8 z)) magic)
    /\ rw_cells asegs mm (Z.shiftr Fb 3 + 2147450880) chk_shadow.

  (* [comment removed for export] *)
  Definition chk_result (r : check_result) (av ew : word) (PB : list (@cblock hptr)) (EB : Z) (f : hptr) (mm : mem) : Prop :=
    match r with
    | CH_NotMe => av = Z_to_bv 64 0 /\ ew = Z_to_bv 64 0 /\ PB = [] /\ exists e, rw_cells asegs mm EB [CB 256 e]
    | CH_Err msg => av = Z_to_bv 64 0 /\ ew = Z_to_bv 64 1 /\ PB = []
        /\ (exists junk', rw_cells asegs mm EB [CB (length msg + 1) (map b8 msg ++ [Z_to_bv 8 0]); CB (255 - length msg) junk'])
        /\ (Z.of_nat (length msg) < 256)%Z /\ Forall (fun z => 0 < z < 256)%Z msg
    | CH_Ok p => exists P, av = Z_to_bv 64 P /\ pre_PCAPR (hptr:=hptr) P p PB mm /\ pc_rfile p = f /\ exists e, rw_cells asegs mm EB [CB 256 e]
    end.

  (* [comment removed for export] *)
  Definition chk_tail_stmt : Prop :=
    forall (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
           (L : alayout) (RNG : footprint) (s : PState H hptr) (CL FB : list (@cblock hptr)) (FL : list fblock) (trC : list Z)
           (lo MG FA EB ERR SPA Fb : Z) (f : hptr) (magic : list Z) (m : mem)
           (RNGx : footprint) (sx : PState H hptr) (mm : mem)
           (ra0 t0 t1 t2 a0 a1 a2 a3 a7 r18 r23 r26 t3 t4 t5 t6 : word)
           (j1 j2 j3 fjunk ej : list byte) (k0 k1 k2 : word) (mi : Z) (sw : bool),
      chk_ctx ra sp tp s0 L RNG CL FB FL trC lo MG FA EB ERR SPA Fb f magic m ->
      chk_inv ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 L RNG CL FB FL lo MG EB ERR SPA Fb magic (ps_outfile s) m RNGx sx [] mm ->
      (mi = TCPDUMP_MAGIC \/ mi = KUZNETZOV_TCPDUMP_MAGIC \/ mi = NSEC_TCPDUMP_MAGIC) ->
      length fjunk = 96%nat ->
      rw_cells asegs mm SPA [CB 32 j1; C8 z64; CB 16 j2; C8 (Z_to_bv 64 EB); CB 16 j3; C8 (Z_to_bv 64 Fb)] ->
      rw_cells asegs mm Fb [C8 k0; C8 k1; C8 k2; CB 96 fjunk; C8 (Z_to_bv 64 (fflagA L FF_CHECK_HEADER Fb))] ->
      rw_cells asegs mm ERR [C4 z64] -> rw_cells asegs mm EB [CB 256 ej] ->
      implMG RNGx (chk_rest MOps (prims HO FO sites) f 0 mi sw) sx
        (check_header_post GIOA ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG FL CL FB lo MG EB ERR magic f m (ps_outfile s))
        (MS (mkR ra0 (Z_to_bv 64 SPA) gp tp t0 t1 t2 sp (Z_to_bv 64 SPA) a0 a1 a2 a3 (Z_to_bv 64 (Z.b2z sw)) (Z_to_bv 64 Fb)
                 (Z_to_bv 64 (Z.shiftr ERR 3 + 2147450880)) a7 r18 (Z_to_bv 64 (Z.b2z (negb sw))) (Z_to_bv 64 ERR)
                 (Z_to_bv 64 (mi + (2^64 - 2^32))) (Z_to_bv 64 FA) r23 (Z_to_bv 64 (Z.shiftr Fb 3 + 2147450880)) (Z_to_bv 64 Fb) r26
                 (Z_to_bv 64 2147450880) t3 t4 t5 t6)
            F (Z_to_bv 64 0x877f4) fc None mm (seg_rom asegs)).

  (* [comment removed for export] *)
  Definition chk_hdr_stmt : Prop :=
    forall (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
           (L : alayout) (RNG : footprint) (s : PState H hptr) (CL FB : list (@cblock hptr)) (FL : list fblock) (trC : list Z)
           (lo MG FA EB ERR SPA Fb : Z) (f : hptr) (magic : list Z) (m : mem)
           (RNGx : footprint) (sx : PState H hptr) (mm : mem)
           (ra0 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 r18 r19 t3 t4 t5 t6 : word)
           (j1 j3 pre mid post ej : list byte) (k0 k1 k2 : word) (maj min n0 n1 n2 n3 l0 l1 l2 l3 mi : Z) (sw : bool),
      chk_ctx ra sp tp s0 L RNG CL FB FL trC lo MG FA EB ERR SPA Fb f magic m ->
      chk_inv ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 L RNG CL FB FL lo MG EB ERR SPA Fb magic (ps_outfile s) m RNGx sx [] mm ->
      (mi = TCPDUMP_MAGIC \/ mi = KUZNETZOV_TCPDUMP_MAGIC \/ mi = NSEC_TCPDUMP_MAGIC) ->
      (0 <= maj < 2^16)%Z -> (0 <= min < 2^16)%Z ->
      (0 <= n0 < 256)%Z -> (0 <= n1 < 256)%Z -> (0 <= n2 < 256)%Z -> (0 <= n3 < 256)%Z ->
      (0 <= l0 < 256)%Z -> (0 <= l1 < 256)%Z -> (0 <= l2 < 256)%Z -> (0 <= l3 < 256)%Z ->
      rw_cells asegs mm SPA [CB 24 j1; C8 (Z_to_bv 64 (Z.b2z sw)); C8 z64; C8 (Z_to_bv 64 (Z.shiftr ERR 3 + 2147450880));
                             C8 (Z_to_bv 64 Fb); C8 (Z_to_bv 64 EB); CB 16 j3; C8 (Z_to_bv 64 Fb)] ->
      rw_cells asegs mm Fb [C8 k0; C8 k1; C8 k2; CB 8 pre; C4 (Z_to_bv 64 (mi + (2^64 - 2^32)))] ->
      rw_cells asegs mm (Fb + 36)
        [C2 (Z_to_bv 64 maj); C2 (Z_to_bv 64 min); CB 8 mid; C4 (Z_to_bv 64 (le4val n0 n1 n2 n3)); C4 (Z_to_bv 64 (le4val l0 l1 l2 l3))] ->
      rw_cells asegs mm (Fb + 56) [CB 64 post; C8 (Z_to_bv 64 (fflagA L FF_CHECK_HEADER Fb))] ->
      rw_cells asegs mm ERR [C4 z64] -> rw_cells asegs mm EB [CB 256 ej] ->
      implMG RNGx (chk_rest2 MOps (prims HO FO sites) f 0 mi sw maj min (le4val n0 n1 n2 n3) (le4val l0 l1 l2 l3)) sx
        (check_header_post GIOA ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG FL CL FB lo MG EB ERR magic f m (ps_outfile s))
        (MS (mkR ra0 (Z_to_bv 64 SPA) gp tp t0 t1 t2 sp (Z_to_bv 64 SPA) a0 a1 a2 a3 a4 a5 a6 a7 r18 r19 (Z_to_bv 64 ERR)
                 (Z_to_bv 64 (mi + (2^64 - 2^32))) (Z_to_bv 64 FA) (Z_to_bv 64 (Fb + 32)) (Z_to_bv 64 (Z.shiftr Fb 3 + 2147450880)) (Z_to_bv 64 Fb)
                 (Z_to_bv 64 (Fb + 36)) (Z_to_bv 64 2147450880) t3 t4 t5 t6)
            F (Z_to_bv 64 0x878b4) fc None mm (seg_rom asegs)).

  (* [comment removed for export] *)
  Definition chk_fill_stmt : Prop :=
    forall (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
           (L : alayout) (RNG : footprint) (s : PState H hptr) (CL FB : list (@cblock hptr)) (FL : list fblock) (trC : list Z)
           (lo MG FA EB ERR SPA Fb : Z) (f : hptr) (magic : list Z) (m : mem)
           (RNGx : footprint) (sx : PState H hptr) (mm : mem)
           (ra0 t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 r18 t3 t4 t5 t6 : word)
           (j1 j3 pre mid post ej : list byte) (k0 k1 k2 : word) (q : hptr) (P : Z)
           (maj min n0 n1 n2 n3 l0 l1 l2 l3 mi : Z) (sw : bool),
      chk_ctx ra sp tp s0 L RNG CL FB FL trC lo MG FA EB ERR SPA Fb f magic m ->
      chk_inv ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 L RNG CL FB FL lo MG EB ERR SPA Fb magic (ps_outfile s) m RNGx sx [(q, P, PCAP_SF_TOTAL)] mm ->
      (mi = TCPDUMP_MAGIC \/ mi = KUZNETZOV_TCPDUMP_MAGIC \/ mi = NSEC_TCPDUMP_MAGIC) ->
      (0 <= maj < 2^16)%Z -> (0 <= min < 2^16)%Z ->
      (0 <= n0 < 256)%Z -> (0 <= n1 < 256)%Z -> (0 <= n2 < 256)%Z -> (0 <= n3 < 256)%Z ->
      (0 <= l0 < 256)%Z -> (0 <= l1 < 256)%Z -> (0 <= l2 < 256)%Z -> (0 <= l3 < 256)%Z -> l2 = 0%Z -> (l3 mod 4 = 0)%Z ->
      rw_cells asegs mm SPA [CB 24 j1; C8 (Z_to_bv 64 (Z.b2z sw)); C8 z64; C8 (Z_to_bv 64 (Z.shiftr ERR 3 + 2147450880));
                             C8 (Z_to_bv 64 Fb); C8 (Z_to_bv 64 EB); CB 16 j3; C8 (Z_to_bv 64 Fb)] ->
      rw_cells asegs mm Fb [C8 k0; C8 k1; C8 k2; CB 8 pre; C4 (Z_to_bv 64 (mi + (2^64 - 2^32)));
                            C2 (Z_to_bv 64 maj); C2 (Z_to_bv 64 min); CB 8 mid; C4 (Z_to_bv 64 (le4val n0 n1 n2 n3)); C4 (Z_to_bv 64 (le4val l0 l1 l2 l3));
                            CB 64 post; C8 (Z_to_bv 64 (fflagA L FF_CHECK_HEADER Fb))] ->
      rw_cells asegs mm P ([CB 16 (repeat (Z_to_bv 8 0) 16); C4 (Z_to_bv 64 (-1)); CB 28 (repeat (Z_to_bv 8 0) 28);
                            C8 (Z_to_bv 64 (P + PCAP_PRIV_OFF)); CB 128 (repeat (Z_to_bv 8 0) 128); C4 (Z_to_bv 64 (-1));
                            CB (Z.to_nat (PCAP_SF_TOTAL - 188)) (repeat (Z_to_bv 8 0) (Z.to_nat (PCAP_SF_TOTAL - 188)))]) ->
      rw_cells asegs mm ERR [C4 z64] -> rw_cells asegs mm EB [CB 256 ej] ->
      implMG RNGx (chk_fill_model MOps (prims HO FO sites) q f 0 mi sw maj min (le4val n0 n1 n2 n3) (le4val l0 l1 l2 l3)) sx
        (check_header_post GIOA ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG FL CL FB lo MG EB ERR magic f m (ps_outfile s))
        (MS (mkR ra0 (Z_to_bv 64 SPA) gp tp t0 t1 t2 sp (Z_to_bv 64 SPA) (Z_to_bv 64 P) a1 a2 a3 a4 a5 a6 a7 r18 (Z_to_bv 64 ERR) (Z_to_bv 64 ERR)
                 (Z_to_bv 64 (mi + (2^64 - 2^32))) (Z_to_bv 64 (sxv l0 l1 l2 l3)) (Z_to_bv 64 (Fb + 32)) (Z_to_bv 64 (Z.shiftr Fb 3 + 2147450880)) (Z_to_bv 64 Fb)
                 (Z_to_bv 64 maj) (Z_to_bv 64 2147450880) t3 t4 t5 t6)
            F (Z_to_bv 64 0x87b50) fc None mm (seg_rom asegs)).
End ChkDefs.

(* [comment removed for export] *)
Section KeepsCallee.
  Context {H hptr : Type} (FO : @FrameOps H hptr).
  Variable GIOA : alayout -> footprint -> PState H hptr -> list (@cblock hptr) -> list (@cblock hptr) -> list fblock -> mem -> Prop.
  Variable fflagA : alayout -> fframe -> Z -> Z.
  Hypothesis GL : gia_laws FO GIOA fflagA.

  #[using="Type"] Lemma client_keeps_up : forall (FL FL' : list fblock) (CL CL' : list (@cblock hptr)) SP SP' a,
    client_keeps FL CL SP a -> (SP' <= SP)%Z -> incl CL CL' -> incl FL FL' -> client_keeps FL' CL' SP' a.
  Proof.
    intros FL FL' CL CL' SP SP' a [K|[K|[K|K]]] HS IC IF.
    - left. lia.
    - right; left. apply in_block_In in K as (b & Hb & Hr). apply in_block_In. exists b. split; [apply IC; exact Hb| exact Hr].
    - right; right; left. eapply in_frames_incl; eassumption.
    - right; right; right. eapply in_frame_sh_incl; eassumption.
  Qed.

  #[using="tlsI FO fflagA GL"] Lemma keeps_callee : forall L RNGx sx (CLx FB : list (@cblock hptr)) fr FL m0 m1 m2 (CL : list (@cblock hptr)) SP SPA WX (Pn : Z -> Prop),
    GIOA L RNGx sx CLx FB (fr :: FL) m0 -> incl CL CLx -> (ATOP <= SPA)%Z -> (SPA <= SP)%Z ->
    agrees_on (fun a => client_keeps (fr :: FL) CLx SPA a /\ Pn a) m1 m2 ->
    (forall a, client_keeps FL CL SP a -> outside WX a -> ~ (fb_addr fr <= a < fb_addr fr + fb_size fr)%Z -> Pn a) ->
    agrees_on (fun a => client_keeps FL CL SP a /\ outside WX a) m1 m2.
  Proof.
    intros L RNGx sx CLx FB fr FL m0 m1 m2 CL SP SPA WX Pn G IC HA HS AG HP.
    eapply agrees_on_weaken; [exact AG|]. intros a (K & O). split.
    - eapply client_keeps_up; [exact K| exact HS| exact IC| apply incl_tl, incl_refl].
    - apply HP; [exact K| exact O|]. assert (HSP : (ATOP <= SP)%Z) by lia. exact (proj1 (keeps_not_own_frame _ _ _ GL _ _ _ _ _ _ _ _ _ _ a G IC HSP K)).
  Qed.

  #[using="Type"] Lemma keeps_callee0 : forall (CLx : list (@cblock hptr)) fr FL m1 m2 (CL : list (@cblock hptr)) SP SPA WX,
    incl CL CLx -> (SPA <= SP)%Z ->
    agrees_on (client_keeps (fr :: FL) CLx SPA) m1 m2 ->
    agrees_on (fun a => client_keeps FL CL SP a /\ outside WX a) m1 m2.
  Proof.
    intros CLx fr FL m1 m2 CL SP SPA WX IC HS AG.
    eapply agrees_on_weaken; [exact AG|]. intros a (K & O).
    eapply client_keeps_up; [exact K| exact HS| exact IC| apply incl_tl, incl_refl].
  Qed.
End KeepsCallee.
End CANSEC1.

(* [comment removed for export] *)
Ltac chk_setup GL CTX INV :=
  pose proof CTX as (LO & BU & (SPT & TOP47) & TPE & ALN & (RSTK & RIMG & RISH & RTLS) & UC & TR & NF & HinF & MGR & MGL & OMG & OERR & DME & OEB & DEE & DEM & ERR4 & EB8 & SPAB & SPA32);
  pose proof INV as (FP & G & OF & MI & ST & STG & FR & AG & MGc & SHC);
  unfold PCAP_L2_STACK in BU; unfold chk_shadow in SHC;
  lazymatch type of MGL with length ?magic = _ =>
    destruct magic as [|mg0 [|mg1 [|mg2 [|mg3 [|? ?]]]]]; try discriminate MGL; cbn [map] in MGc end;
  lazymatch type of ALN with (bv_unsigned ?sp mod 16 = 0)%Z => pose proof (bv_unsigned_in_range 64 sp) as RSP; unfold bv_modulus in RSP; cbn in RSP end;
  destruct (gl_frames _ _ _ GL _ _ _ _ _ _ _ G) as [FAll FND]; pose proof (Forall_inv FAll) as FRM; pose proof FRM as (FBAND' & FTOP' & F64 & _ & FRNG & FSRNG & _ & FSWR);
  cbn [fb_addr fb_size fst snd] in FBAND', FTOP', F64, FRNG, FSRNG, FSWR; clear FAll; change (Z.shiftr 128 3) with 16%Z in FSRNG, FSWR;
  pose proof (ablk_lin _ _ FBAND') as (_ & Fb0 & _ & _); (let bF := fresh "bF" in band_ind FBAND' bF);
  lazymatch type of G with ?GG _ _ _ (?CL ++ ?PB) _ ((FF_CHECK_HEADER, ?Fb, _) :: ?FL) _ =>
    assert (ICL : incl CL (CL ++ PB)) by (apply incl_appl, incl_refl);
    assert (IFL : incl FL ((FF_CHECK_HEADER, Fb, 128%Z) :: FL)) by (apply incl_tl, incl_refl);
  pose proof (clocA_below _ _ _ GL _ _ _ _ _ _ _ _ _ G (clocA_incl _ _ _ _ _ _ (proj1 OMG) ICL IFL)) as (MGLO & MGHI);
  pose proof (clocA_below _ _ _ GL _ _ _ _ _ _ _ _ _ G (clocA_incl _ _ _ _ _ _ (proj1 OERR) ICL IFL)) as (ERLO & ERHI);
  pose proof (clocA_below _ _ _ GL _ _ _ _ _ _ _ _ _ G (clocA_incl _ _ _ _ _ _ (proj1 OEB) ICL IFL)) as (EBLO & EBHI);
  pose proof (clocA_ablk _ _ _ GL _ _ _ _ _ _ _ _ _ G (clocA_incl _ _ _ _ _ _ (proj1 OMG) ICL IFL) ltac:(lia)) as MGBAND;
  pose proof (clocA_ablk _ _ _ GL _ _ _ _ _ _ _ _ _ G (clocA_incl _ _ _ _ _ _ (proj1 OERR) ICL IFL) ltac:(lia)) as ERBAND;
  pose proof (clocA_ablk _ _ _ GL _ _ _ _ _ _ _ _ _ G (clocA_incl _ _ _ _ _ _ (proj1 OEB) ICL IFL) ltac:(lia)) as EBBAND;
  pose proof MGBAND as MGBAND'; pose proof ERBAND as ERBAND'; pose proof EBBAND as EBBAND';
  (let bM := fresh "bM" in band_ind MGBAND bM); (let bE := fresh "bE" in band_ind ERBAND bE); (let bB := fresh "bB" in band_ind EBBAND bB);
  destruct (clocA_apart_frame _ _ _ GL _ _ _ _ _ _ _ _ _ _ G (clocA_incl _ _ _ _ _ _ (proj1 OMG) ICL (incl_refl _)) ltac:(lia)) as (kM & kMr & kM1 & kM2);
  destruct (clocA_apart_frame _ _ _ GL _ _ _ _ _ _ _ _ _ _ G (clocA_incl _ _ _ _ _ _ (proj1 OERR) ICL (incl_refl _)) ltac:(lia)) as (kE & kEr & kE1 & kE2);
  destruct (clocA_apart_frame _ _ _ GL _ _ _ _ _ _ _ _ _ _ G (clocA_incl _ _ _ _ _ _ (proj1 OEB) ICL (incl_refl _)) ltac:(lia)) as (kB & kBr & kB1 & kB2);
  cbn [fb_addr fb_size fst snd] in kM1, kM2, kE1, kE2, kB1, kB2;
  lazymatch type of FRNG with rng _ ?Fb _ =>
    assert (SHLO : (0x7fff8000 <= Z.shiftr Fb 3 + 2147450880 /\ Z.shiftr Fb 3 + 2147450880 + 16 <= 0x10007fff8000
                   /\ (Fb + 128 <= 0x7fff7000 \/ Z.shiftr Fb 3 + 2147450880 + 16 <= Fb))%Z)
      by (rewrite Z.shiftr_div_pow2 by lia; change (2^3)%Z with 8%Z; Z.div_mod_to_equations; lia) end;
  apply (rng_fp_le _ _ _ _ FP) in RSTK; apply (rng_fp_le _ _ _ _ FP) in RIMG; apply (rng_fp_le _ _ _ _ FP) in RISH; apply (rng_fp_le _ _ _ _ FP) in RTLS;
  lazymatch type of RSTK with rng ?RNGx ?lo _ => lazymatch type of SPAB with (_ <= ?SPA <= bv_unsigned ?sp - _)%Z =>
    assert (RSPW : rng RNGx lo (bv_unsigned sp - lo)) by (eapply rng_sub'; [exact RSTK| lia]);
    assert (RSPA : rng RNGx SPA (bv_unsigned sp - SPA)) by (eapply rng_sub'; [exact RSTK| lia]) end end
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
Definition chk_shadow : list cell :=
  [C1 (Z_to_bv 8 18446744073709551601); C1 (Z_to_bv 8 18446744073709551601); C1 (Z_to_bv 8 18446744073709551601); C1 (Z_to_bv 8 18446744073709551601);
   C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0);
   C1 (Z_to_bv 8 18446744073709551603); C1 (Z_to_bv 8 18446744073709551603); C1 (Z_to_bv 8 18446744073709551603); C1 (Z_to_bv 8 18446744073709551603);
   C1 (Z_to_bv 8 18446744073709551603); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)].

Section CANSEC1. Context {rc : runConstT} {tlsI : A3W.ABase.TwB.atlsT}.
Section ChkDefs.
  Context {H hptr : Type} (HO : HeapOps H hptr) (FO : @FrameOps H hptr) (sites : stack_site -> Z).
  Variable GIOA : alayout -> footprint -> PState H hptr -> list (@cblock hptr) -> list (@cblock hptr) -> list fblock -> mem -> Prop.
  Variable TP : tparams.
  Variable fflagA : alayout -> fframe -> Z -> Z.

  (* [comment removed for export] *)
  Definition chk_ctx (ra sp tp s0 : word) (L : alayout) (RNG : footprint) (CL FB : list (@cblock hptr)) (FL : list fblock) (trC : list Z)
      (lo MG FA EB ERR SPA Fb : Z) (f : hptr) (magic : list Z) (m : mem) : Prop :=
    (ATOP + 4096 <= lo)%Z /\ (lo + PCAP_L2_STACK <= bv_unsigned sp)%Z /\ (bv_unsigned sp + 16 < al_top L /\ al_top L <= 2^47)%Z
    /\ tp = Z_to_bv 64 ATP /\ (bv_unsigned sp mod 16 = 0)%Z
    /\ (rng RNG lo (al_top L - lo) /\ rng_aimg RNG /\ rng_aimg_sh RNG /\ rng_atls RNG)
    /\ ucallerA (depth_check_header false) L m sp s0 ra trC /\ traces_check_header TP false L (bv_unsigned ra) trC
    /\ nofr (frames_check_header false) FL /\ In (f, FA, FILE_BLOCK) FB
    /\ Forall (fun z => 0 <= z < 256)%Z magic /\ length magic = 4%nat
    /\ cobjA RNG m FL CL MG 4 /\ cobjA RNG m FL CL ERR 4 /\ (MG + 4 <= ERR \/ ERR + 4 <= MG)%Z
    /\ cobjA RNG m FL CL EB 256 /\ (EB + 256 <= ERR \/ ERR + 4 <= EB)%Z /\ (EB + 256 <= MG \/ MG + 4 <= EB)%Z
    /\ (ERR mod 4 = 0)%Z /\ (EB mod 8 = 0)%Z
    /\ (bv_unsigned sp - 208 <= SPA <= bv_unsigned sp - 192)%Z /\ (SPA mod 32 = 0)%Z.

  (* [comment removed for export] *)
  Definition chk_inv (ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (L : alayout) (RNG : footprint) (CL FB : list (@cblock hptr)) (FL : list fblock)
      (lo MG EB ERR SPA Fb : Z) (magic : list Z) (o : option hptr) (m : mem)
      (RNGx : footprint) (sx : PState H hptr) (PB : list (@cblock hptr)) (mm : mem) : Prop :=
    fp_le RNG RNGx /\ GIOA L RNGx sx (CL ++ PB) FB ((FF_CHECK_HEADER, Fb, 128%Z) :: FL) mm /\ ps_outfile sx = o /\ mem_inv asegs mm
    /\ stk asegs mm lo SPA /\ stk asegs mm (SPA + 88) (bv_unsigned sp + -104)
    /\ rw_cells asegs mm (bv_unsigned sp + -104) [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]
    /\ agrees_on (fun a => client_keeps FL CL (bv_unsigned sp) a /\ outside [(ERR, ERR + 4); (EB, EB + 256)]%Z a) m mm
    /\ rw_cells asegs mm MG (map (fun z => C1 (b8 z)) magic)
    /\ rw_cells asegs mm (Z.shiftr Fb 3 + 2147450880) chk_shadow.

  (* [comment removed for export] *)
  Definition chk_result (r : check_result) (av ew : word) (PB : list (@cblock hptr)) (EB : Z) (f : hptr) (mm : mem) : Prop :=
    match r with
    | CH_NotMe => av = Z_to_bv 64 0 /\ ew = Z_to_bv 64 0 /\ PB = [] /\ exists e, rw_cells asegs mm EB [CB 256 e]
    | CH_Err msg => av = Z_to_bv 64 0 /\ ew = Z_to_bv 64 1 /\ PB = []
        /\ (exists junk', rw_cells asegs mm EB [CB (length msg + 1) (map b8 msg ++ [Z_to_bv 8 0]); CB (255 - length msg) junk'])
        /\ (Z.of_nat (length msg) < 256)%Z /\ Forall (fun z => 0 < z < 256)%Z msg
    | CH_Ok p => exists P, av = Z_to_bv 64 P /\ pre_PCAPR (hptr:=hptr) P p PB mm /\ pc_rfile p = f /\ exists e, rw_cells asegs mm EB [CB 256 e]
    end.

  (* [comment removed for export] *)
  Definition chk_tail_stmt : Prop :=
    forall (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
           (L : alayout) (RNG : footprint) (s : PState H hptr) (CL FB : list (@cblock hptr)) (FL : list fblock) (trC : list Z)
           (lo MG FA EB ERR SPA Fb : Z) (f : hptr) (magic : list Z) (m : mem)
           (RNGx : footprint) (sx : PState H hptr) (mm : mem)
           (ra0 t0 t1 t2 a0 a1 a2 a3 a6 a7 r19 r20 r23 t3 t4 t5 t6 : word)
           (j1 j2 j3 fjunk ej : list byte) (k0 k1 k2 : word) (mi : Z) (sw : bool),
      chk_ctx ra sp tp s0 L RNG CL FB FL trC lo MG FA EB ERR SPA Fb f magic m ->
      chk_inv ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 L RNG CL FB FL lo MG EB ERR SPA Fb magic (ps_outfile s) m RNGx sx [] mm ->
      (mi = TCPDUMP_MAGIC \/ mi = KUZNETZOV_TCPDUMP_MAGIC \/ mi = NSEC_TCPDUMP_MAGIC) ->
      length fjunk = 96%nat ->
      rw_cells asegs mm SPA [CB 32 j1; C8 z64; CB 8 j2; C8 (Z_to_bv 64 EB); C8 (Z_to_bv 64 ERR); CB 16 j3; C8 (Z_to_bv 64 Fb)] ->
      rw_cells asegs mm Fb [C8 k0; C8 k1; C8 k2; CB 96 fjunk; C8 (Z_to_bv 64 (fflagA L FF_CHECK_HEADER Fb))] ->
      rw_cells asegs mm ERR [C4 z64] -> rw_cells asegs mm EB [CB 256 ej] ->
      implMG RNGx (chk_rest MOps (prims HO FO sites) f 0 mi sw) sx
        (check_header_post GIOA ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG FL CL FB lo MG EB ERR magic f m (ps_outfile s))
        (MS (mkR ra0 (Z_to_bv 64 SPA) gp tp t0 t1 t2 sp (Z_to_bv 64 SPA) a0 a1 a2 a3 (Z_to_bv 64 (Z.b2z sw))
                 (Z_to_bv 64 (Z.shiftr ERR 3 + 2147450880)) a6 a7 (Z_to_bv 64 (Z.b2z (negb sw))) r19 r20
                 (Z_to_bv 64 (mi + (2^64 - 2^32))) (Z_to_bv 64 FA) r23 (Z_to_bv 64 Fb) (Z_to_bv 64 (Z.shiftr Fb 3 + 2147450880)) (Z_to_bv 64 Fb)
                 (Z_to_bv 64 2147450880) t3 t4 t5 t6)
            F (Z_to_bv 64 0x87cb8) fc None mm (seg_rom asegs)).

  (* [comment removed for export] *)
  Definition chk_hdr_stmt : Prop :=
    forall (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
           (L : alayout) (RNG : footprint) (s : PState H hptr) (CL FB : list (@cblock hptr)) (FL : list fblock) (trC : list Z)
           (lo MG FA EB ERR SPA Fb : Z) (f : hptr) (magic : list Z) (m : mem)
           (RNGx : footprint) (sx : PState H hptr) (mm : mem)
           (ra0 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 r18 r24 t3 t4 t5 t6 : word)
           (j1 j3 pre mid post ej : list byte) (k0 k1 k2 : word) (maj min n0 n1 n2 n3 l0 l1 l2 l3 mi : Z) (sw : bool),
      chk_ctx ra sp tp s0 L RNG CL FB FL trC lo MG FA EB ERR SPA Fb f magic m ->
      chk_inv ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 L RNG CL FB FL lo MG EB ERR SPA Fb magic (ps_outfile s) m RNGx sx [] mm ->
      (mi = TCPDUMP_MAGIC \/ mi = KUZNETZOV_TCPDUMP_MAGIC \/ mi = NSEC_TCPDUMP_MAGIC) ->
      (0 <= maj < 2^16)%Z -> (0 <= min < 2^16)%Z ->
      (0 <= n0 < 256)%Z -> (0 <= n1 < 256)%Z -> (0 <= n2 < 256)%Z -> (0 <= n3 < 256)%Z ->
      (0 <= l0 < 256)%Z -> (0 <= l1 < 256)%Z -> (0 <= l2 < 256)%Z -> (0 <= l3 < 256)%Z ->
      rw_cells asegs mm SPA [CB 24 j1; C8 (Z_to_bv 64 (Z.b2z sw)); C8 z64; C8 (Z_to_bv 64 (Z.shiftr ERR 3 + 2147450880));
                             C8 (Z_to_bv 64 EB); C8 (Z_to_bv 64 ERR); CB 16 j3; C8 (Z_to_bv 64 Fb)] ->
      rw_cells asegs mm Fb [C8 k0; C8 k1; C8 k2; CB 8 pre; C4 (Z_to_bv 64 (mi + (2^64 - 2^32)))] ->
      rw_cells asegs mm (Fb + 36)
        [C2 (Z_to_bv 64 maj); C2 (Z_to_bv 64 min); CB 8 mid; C4 (Z_to_bv 64 (le4val n0 n1 n2 n3)); C4 (Z_to_bv 64 (le4val l0 l1 l2 l3))] ->
      rw_cells asegs mm (Fb + 56) [CB 64 post; C8 (Z_to_bv 64 (fflagA L FF_CHECK_HEADER Fb))] ->
      rw_cells asegs mm ERR [C4 z64] -> rw_cells asegs mm EB [CB 256 ej] ->
      implMG RNGx (chk_rest2 MOps (prims HO FO sites) f 0 mi sw maj min (le4val n0 n1 n2 n3) (le4val l0 l1 l2 l3)) sx
        (check_header_post GIOA ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG FL CL FB lo MG EB ERR magic f m (ps_outfile s))
        (MS (mkR ra0 (Z_to_bv 64 SPA) gp tp t0 t1 t2 sp (Z_to_bv 64 SPA) a0 a1 a2 a3 a4 a5 a6 a7 r18 (Z_to_bv 64 Fb) (Z_to_bv 64 (Fb + 36))
                 (Z_to_bv 64 (mi + (2^64 - 2^32))) (Z_to_bv 64 FA) (Z_to_bv 64 (Fb + 32)) r24 (Z_to_bv 64 (Z.shiftr Fb 3 + 2147450880)) (Z_to_bv 64 Fb)
                 (Z_to_bv 64 2147450880) t3 t4 t5 t6)
            F (Z_to_bv 64 0x87d78) fc None mm (seg_rom asegs)).

  (* [comment removed for export] *)
  Definition chk_fill_stmt : Prop :=
    forall (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
           (L : alayout) (RNG : footprint) (s : PState H hptr) (CL FB : list (@cblock hptr)) (FL : list fblock) (trC : list Z)
           (lo MG FA EB ERR SPA Fb : Z) (f : hptr) (magic : list Z) (m : mem)
           (RNGx : footprint) (sx : PState H hptr) (mm : mem)
           (ra0 t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word)
           (j1 j3 pre mid post ej : list byte) (k0 k1 k2 : word) (q : hptr) (P : Z)
           (maj min n0 n1 n2 n3 l0 l1 l2 l3 mi : Z) (sw : bool),
      chk_ctx ra sp tp s0 L RNG CL FB FL trC lo MG FA EB ERR SPA Fb f magic m ->
      chk_inv ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 L RNG CL FB FL lo MG EB ERR SPA Fb magic (ps_outfile s) m RNGx sx [(q, P, PCAP_SF_TOTAL)] mm ->
      (mi = TCPDUMP_MAGIC \/ mi = KUZNETZOV_TCPDUMP_MAGIC \/ mi = NSEC_TCPDUMP_MAGIC) ->
      (0 <= maj < 2^16)%Z -> (0 <= min < 2^16)%Z ->
      (0 <= n0 < 256)%Z -> (0 <= n1 < 256)%Z -> (0 <= n2 < 256)%Z -> (0 <= n3 < 256)%Z ->
      (0 <= l0 < 256)%Z -> (0 <= l1 < 256)%Z -> (0 <= l2 < 256)%Z -> (0 <= l3 < 256)%Z -> l2 = 0%Z -> (l3 mod 4 = 0)%Z ->
      rw_cells asegs mm SPA [CB 24 j1; C8 (Z_to_bv 64 (Z.b2z sw)); C8 z64; C8 (Z_to_bv 64 (Z.shiftr ERR 3 + 2147450880));
                             C8 (Z_to_bv 64 EB); C8 (Z_to_bv 64 ERR); CB 16 j3; C8 (Z_to_bv 64 Fb)] ->
      rw_cells asegs mm Fb [C8 k0; C8 k1; C8 k2; CB 8 pre; C4 (Z_to_bv 64 (mi + (2^64 - 2^32)));
                            C2 (Z_to_bv 64 maj); C2 (Z_to_bv 64 min); CB 8 mid; C4 (Z_to_bv 64 (le4val n0 n1 n2 n3)); C4 (Z_to_bv 64 (le4val l0 l1 l2 l3));
                            CB 64 post; C8 (Z_to_bv 64 (fflagA L FF_CHECK_HEADER Fb))] ->
      rw_cells asegs mm P ([CB 16 (repeat (Z_to_bv 8 0) 16); C4 (Z_to_bv 64 (-1)); CB 28 (repeat (Z_to_bv 8 0) 28);
                            C8 (Z_to_bv 64 (P + PCAP_PRIV_OFF)); CB 128 (repeat (Z_to_bv 8 0) 128); C4 (Z_to_bv 64 (-1));
                            CB (Z.to_nat (PCAP_SF_TOTAL - 188)) (repeat (Z_to_bv 8 0) (Z.to_nat (PCAP_SF_TOTAL - 188)))]) ->
      rw_cells asegs mm ERR [C4 z64] -> rw_cells asegs mm EB [CB 256 ej] ->
      implMG RNGx (chk_fill_model MOps (prims HO FO sites) q f 0 mi sw maj min (le4val n0 n1 n2 n3) (le4val l0 l1 l2 l3)) sx
        (check_header_post GIOA ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG FL CL FB lo MG EB ERR magic f m (ps_outfile s))
        (MS (mkR ra0 (Z_to_bv 64 SPA) gp tp t0 t1 t2 sp (Z_to_bv 64 SPA) (Z_to_bv 64 P) a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 ERR) (Z_to_bv 64 Fb) (Z_to_bv 64 (Fb + 36))
                 (Z_to_bv 64 (mi + (2^64 - 2^32))) (Z_to_bv 64 FA) (Z_to_bv 64 (Fb + 32)) (Z_to_bv 64 Fb) (Z_to_bv 64 (Z.shiftr Fb 3 + 2147450880)) (Z_to_bv 64 Fb)
                 (Z_to_bv 64 2147450880) t3 t4 t5 t6)
            F (Z_to_bv 64 0x88020) fc None mm (seg_rom asegs)).
End ChkDefs.

(* [comment removed for export] *)
Section KeepsCallee.
  Context {H hptr : Type} (FO : @FrameOps H hptr).
  Variable GIOA : alayout -> footprint -> PState H hptr -> list (@cblock hptr) -> list (@cblock hptr) -> list fblock -> mem -> Prop.
  Variable fflagA : alayout -> fframe -> Z -> Z.
  Hypothesis GL : gia_laws FO GIOA fflagA.

  #[using="Type"] Lemma client_keeps_up : forall (FL FL' : list fblock) (CL CL' : list (@cblock hptr)) SP SP' a,
    client_keeps FL CL SP a -> (SP' <= SP)%Z -> incl CL CL' -> incl FL FL' -> client_keeps FL' CL' SP' a.
  Proof.
    intros FL FL' CL CL' SP SP' a [K|[K|[K|K]]] HS IC IF.
    - left. lia.
    - right; left. apply in_block_In in K as (b & Hb & Hr). apply in_block_In. exists b. split; [apply IC; exact Hb| exact Hr].
    - right; right; left. eapply in_frames_incl; eassumption.
    - right; right; right. eapply in_frame_sh_incl; eassumption.
  Qed.

  #[using="tlsI FO fflagA GL"] Lemma keeps_callee : forall L RNGx sx (CLx FB : list (@cblock hptr)) fr FL m0 m1 m2 (CL : list (@cblock hptr)) SP SPA WX (Pn : Z -> Prop),
    GIOA L RNGx sx CLx FB (fr :: FL) m0 -> incl CL CLx -> (ATOP <= SPA)%Z -> (SPA <= SP)%Z ->
    agrees_on (fun a => client_keeps (fr :: FL) CLx SPA a /\ Pn a) m1 m2 ->
    (forall a, client_keeps FL CL SP a -> outside WX a -> ~ (fb_addr fr <= a < fb_addr fr + fb_size fr)%Z -> Pn a) ->
    agrees_on (fun a => client_keeps FL CL SP a /\ outside WX a) m1 m2.
  Proof.
    intros L RNGx sx CLx FB fr FL m0 m1 m2 CL SP SPA WX Pn G IC HA HS AG HP.
    eapply agrees_on_weaken; [exact AG|]. intros a (K & O). split.
    - eapply client_keeps_up; [exact K| exact HS| exact IC| apply incl_tl, incl_refl].
    - apply HP; [exact K| exact O|]. assert (HSP : (ATOP <= SP)%Z) by lia. exact (proj1 (keeps_not_own_frame _ _ _ GL _ _ _ _ _ _ _ _ _ _ a G IC HSP K)).
  Qed.

  #[using="Type"] Lemma keeps_callee0 : forall (CLx : list (@cblock hptr)) fr FL m1 m2 (CL : list (@cblock hptr)) SP SPA WX,
    incl CL CLx -> (SPA <= SP)%Z ->
    agrees_on (client_keeps (fr :: FL) CLx SPA) m1 m2 ->
    agrees_on (fun a => client_keeps FL CL SP a /\ outside WX a) m1 m2.
  Proof.
    intros CLx fr FL m1 m2 CL SP SPA WX IC HS AG.
    eapply agrees_on_weaken; [exact AG|]. intros a (K & O).
    eapply client_keeps_up; [exact K| exact HS| exact IC| apply incl_tl, incl_refl].
  Qed.
End KeepsCallee.
End CANSEC1.

(* [comment removed for export] *)
Ltac chk_setup GL CTX INV :=
  pose proof CTX as (LO & BU & (SPT & TOP47) & TPE & ALN & (RSTK & RIMG & RISH & RTLS) & UC & TR & NF & HinF & MGR & MGL & OMG & OERR & DME & OEB & DEE & DEM & ERR4 & EB8 & SPAB & SPA32);
  pose proof INV as (FP & G & OF & MI & ST & STG & FR & AG & MGc & SHC);
  unfold PCAP_L2_STACK in BU; unfold chk_shadow in SHC;
  lazymatch type of MGL with length ?magic = _ =>
    destruct magic as [|mg0 [|mg1 [|mg2 [|mg3 [|? ?]]]]]; try discriminate MGL; cbn [map] in MGc end;
  lazymatch type of ALN with (bv_unsigned ?sp mod 16 = 0)%Z => pose proof (bv_unsigned_in_range 64 sp) as RSP; unfold bv_modulus in RSP; cbn in RSP end;
  destruct (gl_frames _ _ _ GL _ _ _ _ _ _ _ G) as [FAll FND]; pose proof (Forall_inv FAll) as FRM; pose proof FRM as (FBAND' & FTOP' & F64 & _ & FRNG & FSRNG & _ & FSWR);
  cbn [fb_addr fb_size fst snd] in FBAND', FTOP', F64, FRNG, FSRNG, FSWR; clear FAll; change (Z.shiftr 128 3) with 16%Z in FSRNG, FSWR;
  pose proof (ablk_lin _ _ FBAND') as (_ & Fb0 & _ & _); (let bF := fresh "bF" in band_ind FBAND' bF);
  lazymatch type of G with ?GG _ _ _ (?CL ++ ?PB) _ ((FF_CHECK_HEADER, ?Fb, _) :: ?FL) _ =>
    assert (ICL : incl CL (CL ++ PB)) by (apply incl_appl, incl_refl);
    assert (IFL : incl FL ((FF_CHECK_HEADER, Fb, 128%Z) :: FL)) by (apply incl_tl, incl_refl);
  pose proof (clocA_below _ _ _ GL _ _ _ _ _ _ _ _ _ G (clocA_incl _ _ _ _ _ _ (proj1 OMG) ICL IFL)) as (MGLO & MGHI);
  pose proof (clocA_below _ _ _ GL _ _ _ _ _ _ _ _ _ G (clocA_incl _ _ _ _ _ _ (proj1 OERR) ICL IFL)) as (ERLO & ERHI);
  pose proof (clocA_below _ _ _ GL _ _ _ _ _ _ _ _ _ G (clocA_incl _ _ _ _ _ _ (proj1 OEB) ICL IFL)) as (EBLO & EBHI);
  pose proof (clocA_ablk _ _ _ GL _ _ _ _ _ _ _ _ _ G (clocA_incl _ _ _ _ _ _ (proj1 OMG) ICL IFL) ltac:(lia)) as MGBAND;
  pose proof (clocA_ablk _ _ _ GL _ _ _ _ _ _ _ _ _ G (clocA_incl _ _ _ _ _ _ (proj1 OERR) ICL IFL) ltac:(lia)) as ERBAND;
  pose proof (clocA_ablk _ _ _ GL _ _ _ _ _ _ _ _ _ G (clocA_incl _ _ _ _ _ _ (proj1 OEB) ICL IFL) ltac:(lia)) as EBBAND;
  pose proof MGBAND as MGBAND'; pose proof ERBAND as ERBAND'; pose proof EBBAND as EBBAND';
  (let bM := fresh "bM" in band_ind MGBAND bM); (let bE := fresh "bE" in band_ind ERBAND bE); (let bB := fresh "bB" in band_ind EBBAND bB);
  destruct (clocA_apart_frame _ _ _ GL _ _ _ _ _ _ _ _ _ _ G (clocA_incl _ _ _ _ _ _ (proj1 OMG) ICL (incl_refl _)) ltac:(lia)) as (kM & kMr & kM1 & kM2);
  destruct (clocA_apart_frame _ _ _ GL _ _ _ _ _ _ _ _ _ _ G (clocA_incl _ _ _ _ _ _ (proj1 OERR) ICL (incl_refl _)) ltac:(lia)) as (kE & kEr & kE1 & kE2);
  destruct (clocA_apart_frame _ _ _ GL _ _ _ _ _ _ _ _ _ _ G (clocA_incl _ _ _ _ _ _ (proj1 OEB) ICL (incl_refl _)) ltac:(lia)) as (kB & kBr & kB1 & kB2);
  cbn [fb_addr fb_size fst snd] in kM1, kM2, kE1, kE2, kB1, kB2;
  lazymatch type of FRNG with rng _ ?Fb _ =>
    assert (SHLO : (0x7fff8000 <= Z.shiftr Fb 3 + 2147450880 /\ Z.shiftr Fb 3 + 2147450880 + 16 <= 0x10007fff8000
                   /\ (Fb + 128 <= 0x7fff7000 \/ Z.shiftr Fb 3 + 2147450880 + 16 <= Fb))%Z)
      by (rewrite Z.shiftr_div_pow2 by lia; change (2^3)%Z with 8%Z; Z.div_mod_to_equations; lia) end;
  apply (rng_fp_le _ _ _ _ FP) in RSTK; apply (rng_fp_le _ _ _ _ FP) in RIMG; apply (rng_fp_le _ _ _ _ FP) in RISH; apply (rng_fp_le _ _ _ _ FP) in RTLS;
  lazymatch type of RSTK with rng ?RNGx ?lo _ => lazymatch type of SPAB with (_ <= ?SPA <= bv_unsigned ?sp - _)%Z =>
    assert (RSPW : rng RNGx lo (bv_unsigned sp - lo)) by (eapply rng_sub'; [exact RSTK| lia]);
    assert (RSPA : rng RNGx SPA (bv_unsigned sp - SPA)) by (eapply rng_sub'; [exact RSTK| lia]) end end
  end.
End TwB.
End F_sfchk_defsA.

(* [comment removed for export] *)
Module F_sfchk_exitA.
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
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require CkTac__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require MonadG GIA PcapRepA UnwKit. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require MonadGX__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require Pcap_ifaceA. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require FrameKit__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require F_ngchk_defsA__A3P. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.CkTac__A3P.CkTac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadG OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.GIA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.PcapRepA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.UnwKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadGX__A3P.TracesA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.Pcap_ifaceA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.FrameKit__A3P.FrameKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_ngchk_defsA__A3P.F_sfchk_epiA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_sfchk_defsA__A3P.F_sfchk_defsA.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require SecDiet.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Open Scope bv_scope.

Section CANSEC1. Context {rc : runConstT} {tlsI : ABase.atlsT}.
Section ChkExit.
  Context {H hptr : Type} (HO : HeapOps H hptr) (FO : @FrameOps H hptr) (sites : stack_site -> Z).
  Variable GIOA : alayout -> footprint -> PState H hptr -> list (@cblock hptr) -> list (@cblock hptr) -> list fblock -> mem -> Prop.
  Variable TP : tparams.
  Variable fflagA : alayout -> fframe -> Z -> Z.
  Hypothesis GL : gia_laws FO GIOA fflagA.
  Hypothesis FRET : fret_inline_law FO GIOA fflagA.

  Definition chk_exit__stmt : Prop := forall (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (L : alayout) (RNG : footprint) (CL FB : list (@cblock hptr)) (FL : list fblock) (trC : list Z)
      (lo MG FA EB ERR SPA Fb : Z) (f : hptr) (magic : list Z) (m : mem) (o : option hptr)
      (RNGx : footprint) (sx : PState H hptr) (PB : list (@cblock hptr)) (mm : mem)
      (ra0 sp0 t0 t1 t2 r9 av a1 a2 a3 a4 a6 a7 r18 r19 r20 r21 r22 r23 r26 r27 t3 t4 t5 t6 : word)
      (scs fcs : list cell) (k0 k1 k2 ew : word) (r : check_result),
    chk_ctx TP ra sp tp s0 L RNG CL FB FL trC lo MG FA EB ERR SPA Fb f magic m ->
    chk_inv GIOA ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 L RNG CL FB FL lo MG EB ERR SPA Fb magic o m RNGx sx PB mm ->
    rw_cells asegs mm SPA scs -> cells_size scs = 88%nat ->
    rw_cells asegs mm Fb ([C8 k0; C8 k1; C8 k2] ++ fcs ++ [C8 (Z_to_bv 64 (fflagA L FF_CHECK_HEADER Fb))]) -> cells_size fcs = 96%nat ->
    rw_cells asegs mm ERR [C4 ew] ->
    chk_result r av ew PB EB f mm ->
    implMG RNGx (fo_ret FO _ FF_CHECK_HEADER r) sx
      (check_header_post GIOA ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG FL CL FB lo MG EB ERR magic f m o)
      (MS (mkR ra0 sp0 gp tp t0 t1 t2 sp r9 av a1 a2 a3 a4 (Z_to_bv 64 Fb) a6 a7
               r18 r19 r20 r21 r22 r23 (Z_to_bv 64 (Z.shiftr Fb 3 + 2147450880)) (Z_to_bv 64 Fb) r26 r27 t3 t4 t5 t6)
          F (Z_to_bv 64 0x87a50) fc None mm (seg_rom asegs)).
  Section Sz1.
  Variables ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG CL FB FL trC lo MG FA EB ERR SPA Fb f magic m o RNGx sx PB mm ra0 sp0 t0 t1 t2 r9 av a1 a2 a3 a4 a6 a7 r18 r19 r20 r21 r22 r23 r26 r27 t3 t4 t5 t6 scs fcs k0 k1 k2 ew r : ltac2:(SecDiet.SzSec.tyM 'chk_exit__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra).
  Lemma chk_exit__body : ltac2:(SecDiet.SzSec.bodyP 'chk_exit__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof using GL FRET.
    intros CTX INV FRA Hscs FRC Hfcs ERRc RES.
    destruct CTX as (LO & BU & (SPT & TOP47) & TPE & ALN & (RSTK & RIMG & RISH & RTLS) & UC & TR & NF & HinF & MGR & MGL & OMG & OERR & DME & OEB & DEE & DEM & ERR4 & EB8 & SPAB & SPA32).
    destruct INV as (FP & G & OF & MI & ST & STG & FR & AG & MGc & SHC).
    unfold PCAP_L2_STACK in BU.
    destruct (rw_cells_forget _ _ _ _ FRA) as [jS FRA']. rewrite Hscs in FRA'. clear FRA.
    pose proof (rw_cells_merge asegs _ _ [C8 k0; C8 k1; C8 k2] fcs [C8 (Z_to_bv 64 (fflagA L FF_CHECK_HEADER Fb))] FRC) as FRCm.
    rewrite Hfcs in FRCm. cbn [app] in FRCm. clear FRC.
    unfold chk_shadow in SHC.
    apply (rng_fp_le _ _ _ _ FP) in RSTK.
    eapply implMG_mono.
    { eapply (chk_epi FO GIOA fflagA GL FRET ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNGx sx CL PB FB FL lo SPA Fb mm);
        [exact SPAB| exact SPA32| exact LO| lia| exact SPT| exact TOP47| exact G| exact MI| exact ST| exact STG| exact FRA'| exact FR| exact FRCm| exact SHC| exact RSTK]. }
    intros r' s3' RNG3 ms3 (-> & -> & PO). destruct_exs PO. destruct PO as (-> & MI7 & ST7 & AG7 & AGP7 & G7 & OF7).
    unfold check_header_post. split; [exact FP|].
    lazymatch goal with |- context [MS _ _ _ _ _ ?m7 _] => exists av, m7, ew end.
    split. { unfold hpost_regs. repeat (lazymatch goal with |- ex _ => eexists end). reflexivity. }
    split; [congruence|]. split; [exact MI7|]. split; [exact ST7|].
    split. { eapply agrees_on_trans; [eapply agrees_on_weaken; [exact AG|]; intros a (K & N1 & N2); split; [exact K|]; cbn [outside fst snd]; lia|].
             eapply agrees_on_weaken; [exact AG7|]. intros a (K & _); exact K. }
    destruct magic as [|mg0 [|mg1 [|mg2 [|mg3 [|? ?]]]]]; try discriminate MGL. cbn [map] in MGc |- *.
    split. { eapply rw_cells_recell; [eapply agrees_rw_cells; [exact AG7| exact MGc|]; intros a Ha; eapply clocA_keeps; [exact (proj1 OMG)| cbn [cells_size csize Nat.add] in Ha; lia]
                                    | cbn; repeat split; exact Logic.I | reflexivity]. }
    split. { eapply agrees_rw_cells; [exact AG7| exact ERRc|]. intros a Ha. eapply clocA_keeps; [exact (proj1 OERR)| cbn [cells_size csize Nat.add] in Ha; lia]. }
    assert (KEB : forall cs, rw_cells asegs mm EB cs -> cells_size cs = 256%nat -> rw_cells asegs x13 EB cs).
    { intros cs HC HS. eapply agrees_rw_cells; [exact AG7| exact HC|]. intros a Ha. eapply clocA_keeps; [exact (proj1 OEB)| rewrite HS in Ha; lia]. }
    destruct r as [| msg | p]; cbn [chk_result] in RES.
    - destruct RES as (-> & -> & -> & e & HEB). rewrite app_nil_r in G7.
      split; [reflexivity|]. split; [reflexivity|]. split; [exact G7|]. exists e. apply KEB; [exact HEB| reflexivity].
    - destruct RES as (-> & -> & -> & (junk' & HEB) & LEN & MSG). rewrite app_nil_r in G7.
      exists junk'. split; [reflexivity|]. split; [reflexivity|]. split; [exact G7|].
      split; [apply KEB; [exact HEB| cbn [cells_size csize Nat.add]; lia]|]. split; [exact LEN| exact MSG].
    - destruct RES as (P & -> & (rf & st & os & Lrf & Lst & Los & PG) & RF & e & HEB).
      exists P, PB. split; [reflexivity|]. split; [exact G7|].
      split. { exists rf, st, os. split; [exact Lrf|]. split; [exact Lst|]. split; [exact Los|].
               eapply PCAPRg_agree; [exact AGP7| intros a Ha; apply in_block_app; right; exact Ha| reflexivity| reflexivity| reflexivity| exact PG]. }
      split; [exact RF|]. exists e. apply KEB; [exact HEB| reflexivity].
  Qed.
  End Sz1.
  Lemma chk_exit : ltac:(let t := eval cbv delta [chk_exit__stmt] in chk_exit__stmt in exact t).
  Proof using GL FRET. intros ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG CL FB FL trC lo MG FA EB ERR SPA Fb f magic m o RNGx sx PB mm ra0 sp0 t0 t1 t2 r9 av a1 a2 a3 a4 a6 a7 r18 r19 r20 r21 r22 r23 r26 r27 t3 t4 t5 t6 scs fcs k0 k1 k2 ew r. ltac2:(SecDiet.SzSec.closeP 'chk_exit__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.
End ChkExit.
End CANSEC1.

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
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.CkTac__A3P.CkTac.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadG.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.GIA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.PcapRepA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.UnwKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadGX__A3P.TracesA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.Pcap_ifaceA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.FrameKit__A3P.FrameKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_ngchk_defsA__A3P.F_sfchk_epiA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_sfchk_defsA__A3P.F_sfchk_defsA.TwB.
(* [comment removed for export] *) Local Ltac Zify.zify_pre_hook ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB.twm_hook_1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Open Scope bv_scope.

Section CANSEC1. Context {rc : runConstT} {tlsI : A3W.ABase.TwB.atlsT}.
Section ChkExit.
  Context {H hptr : Type} (HO : HeapOps H hptr) (FO : @FrameOps H hptr) (sites : stack_site -> Z).
  Variable GIOA : alayout -> footprint -> PState H hptr -> list (@cblock hptr) -> list (@cblock hptr) -> list fblock -> mem -> Prop.
  Variable TP : tparams.
  Variable fflagA : alayout -> fframe -> Z -> Z.
  Hypothesis GL : gia_laws FO GIOA fflagA.
  Hypothesis FRET : fret_inline_law FO GIOA fflagA.

  Definition chk_exit__stmt : Prop := forall (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (L : alayout) (RNG : footprint) (CL FB : list (@cblock hptr)) (FL : list fblock) (trC : list Z)
      (lo MG FA EB ERR SPA Fb : Z) (f : hptr) (magic : list Z) (m : mem) (o : option hptr)
      (RNGx : footprint) (sx : PState H hptr) (PB : list (@cblock hptr)) (mm : mem)
      (ra0 sp0 t0 t1 t2 r9 av a1 a2 a3 a4 a5 a6 a7 r18 r19 r20 r21 r22 r23 r27 t3 t4 t5 t6 : word)
      (scs fcs : list cell) (k0 k1 k2 ew : word) (r : check_result),
    chk_ctx TP ra sp tp s0 L RNG CL FB FL trC lo MG FA EB ERR SPA Fb f magic m ->
    chk_inv GIOA ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 L RNG CL FB FL lo MG EB ERR SPA Fb magic o m RNGx sx PB mm ->
    rw_cells asegs mm SPA scs -> cells_size scs = 88%nat ->
    rw_cells asegs mm Fb ([C8 k0; C8 k1; C8 k2] ++ fcs ++ [C8 (Z_to_bv 64 (fflagA L FF_CHECK_HEADER Fb))]) -> cells_size fcs = 96%nat ->
    rw_cells asegs mm ERR [C4 ew] ->
    chk_result r av ew PB EB f mm ->
    implMG RNGx (fo_ret FO _ FF_CHECK_HEADER r) sx
      (check_header_post GIOA ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG FL CL FB lo MG EB ERR magic f m o)
      (MS (mkR ra0 sp0 gp tp t0 t1 t2 sp r9 av a1 a2 a3 a4 a5 a6 a7
               r18 r19 r20 r21 r22 r23 (Z_to_bv 64 Fb) (Z_to_bv 64 (Z.shiftr Fb 3 + 2147450880)) (Z_to_bv 64 Fb) r27 t3 t4 t5 t6)
          F (Z_to_bv 64 0x87f24) fc None mm (seg_rom asegs)).
  Section Sz1.
  Variables ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG CL FB FL trC lo MG FA EB ERR SPA Fb f magic m o RNGx sx PB mm ra0 sp0 t0 t1 t2 r9 av a1 a2 a3 a4 a5 a6 a7 r18 r19 r20 r21 r22 r23 r27 t3 t4 t5 t6 scs fcs k0 k1 k2 ew r : ltac2:(SecDiet.SzSec.tyM 'chk_exit__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra).
  Lemma chk_exit__body : ltac2:(SecDiet.SzSec.bodyP 'chk_exit__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof using GL FRET.
 intros CTX INV FRA Hscs FRC Hfcs ERRc RES.
    destruct CTX as (LO & BU & (SPT & TOP47) & TPE & ALN & (RSTK & RIMG & RISH & RTLS) & UC & TR & NF & HinF & MGR & MGL & OMG & OERR & DME & OEB & DEE & DEM & ERR4 & EB8 & SPAB & SPA32).
    destruct INV as (FP & G & OF & MI & ST & STG & FR & AG & MGc & SHC).
    unfold PCAP_L2_STACK in BU.
    destruct (rw_cells_forget _ _ _ _ FRA) as [jS FRA']. rewrite Hscs in FRA'. clear FRA.
    pose proof (rw_cells_merge asegs _ _ [C8 k0; C8 k1; C8 k2] fcs [C8 (Z_to_bv 64 (fflagA L FF_CHECK_HEADER Fb))] FRC) as FRCm.
    rewrite Hfcs in FRCm. cbn [app] in FRCm. clear FRC.
    unfold chk_shadow in SHC.
    apply (rng_fp_le _ _ _ _ FP) in RSTK.
    eapply implMG_mono.
    { eapply (chk_epi FO GIOA fflagA GL FRET ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNGx sx CL PB FB FL lo SPA Fb mm);
        [exact SPAB| exact SPA32| exact LO| lia| exact SPT| exact TOP47| exact G| exact MI| exact ST| exact STG| exact FRA'| exact FR| exact FRCm| exact SHC| exact RSTK]. }
    intros r' s3' RNG3 ms3 (-> & -> & PO). destruct_exs PO. destruct PO as (-> & MI7 & ST7 & AG7 & AGP7 & G7 & OF7).
    unfold check_header_post. split; [exact FP|].
    lazymatch goal with |- context [MS _ _ _ _ _ ?m7 _] => exists av, m7, ew end.
    split. { unfold hpost_regs. repeat (lazymatch goal with |- ex _ => eexists end). reflexivity. }
    split; [congruence|]. split; [exact MI7|]. split; [exact ST7|].
    split. { eapply agrees_on_trans; [eapply agrees_on_weaken; [exact AG|]; intros a (K & N1 & N2); split; [exact K|]; cbn [outside fst snd]; lia|].
             eapply agrees_on_weaken; [exact AG7|]. intros a (K & _); exact K. }
    destruct magic as [|mg0 [|mg1 [|mg2 [|mg3 [|? ?]]]]]; try discriminate MGL. cbn [map] in MGc |- *.
    split. { eapply rw_cells_recell; [eapply agrees_rw_cells; [exact AG7| exact MGc|]; intros a Ha; eapply clocA_keeps; [exact (proj1 OMG)| cbn [cells_size csize Nat.add] in Ha; lia]
                                    | cbn; repeat split; exact Logic.I | reflexivity]. }
    split. { eapply agrees_rw_cells; [exact AG7| exact ERRc|]. intros a Ha. eapply clocA_keeps; [exact (proj1 OERR)| cbn [cells_size csize Nat.add] in Ha; lia]. }
    assert (KEB : forall cs, rw_cells asegs mm EB cs -> cells_size cs = 256%nat -> rw_cells asegs x13 EB cs).
    { intros cs HC HS. eapply agrees_rw_cells; [exact AG7| exact HC|]. intros a Ha. eapply clocA_keeps; [exact (proj1 OEB)| rewrite HS in Ha; lia]. }
    destruct r as [| msg | p]; cbn [chk_result] in RES.
    - destruct RES as (-> & -> & -> & e & HEB). rewrite app_nil_r in G7.
      split; [reflexivity|]. split; [reflexivity|]. split; [exact G7|]. exists e. apply KEB; [exact HEB| reflexivity].
    - destruct RES as (-> & -> & -> & (junk' & HEB) & LEN & MSG). rewrite app_nil_r in G7.
      exists junk'. split; [reflexivity|]. split; [reflexivity|]. split; [exact G7|].
      split; [apply KEB; [exact HEB| cbn [cells_size csize Nat.add]; lia]|]. split; [exact LEN| exact MSG].
    - destruct RES as (P & -> & (rf & st & os & Lrf & Lst & Los & PG) & RF & e & HEB).
      exists P, PB. split; [reflexivity|]. split; [exact G7|].
      split. { exists rf, st, os. split; [exact Lrf|]. split; [exact Lst|]. split; [exact Los|].
               eapply PCAPRg_agree; [exact AGP7| intros a Ha; apply in_block_app; right; exact Ha| reflexivity| reflexivity| reflexivity| exact PG]. }
      split; [exact RF|]. exists e. apply KEB; [exact HEB| reflexivity].
  Qed.
  End Sz1.
  Lemma chk_exit : ltac:(let t := eval cbv delta [chk_exit__stmt] in chk_exit__stmt in exact t).
  Proof using GL FRET. intros ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG CL FB FL trC lo MG FA EB ERR SPA Fb f magic m o RNGx sx PB mm ra0 sp0 t0 t1 t2 r9 av a1 a2 a3 a4 a5 a6 a7 r18 r19 r20 r21 r22 r23 r27 t3 t4 t5 t6 scs fcs k0 k1 k2 ew r. ltac2:(SecDiet.SzSec.closeP 'chk_exit__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.
End ChkExit.
End CANSEC1.
End TwB.
End F_sfchk_exitA.

(* [comment removed for export] *)
Module F_ngnAA.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool String.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import Tac Arr Bytes ZBridge ITree Nodes Decode SysStep Frame StoreFast Image.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Import Prelim Monad Fmt StdioCore Stdio PcapPrelim PcapTypes PcapPure Pcap Prog.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require FileCells__Musl. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require Printf_kit__Musl. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require AmoStep__Musl. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.FileCells__Musl.StrFun OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_kit__Musl.StartupKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.CellsExtra.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require FmtFacts__S3. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.FmtFacts__S3.FmtFacts.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import ExecF ITreeA Shadow StepF SysStepF RunDraw.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require Import AImg ABase AMalloc_iface.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require CkTac__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require MonadG GIA PcapRepA UnwKit. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require MonadGX__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require Pcap_ifaceA Pcap_iface_ngA Pcap_iface_ppA LibcKit. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require FrameKit__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require FmtKitA. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require F_ngchk_defsA__A3P. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.CkTac__A3P.CkTac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadG OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.GIA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.PcapRepA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.UnwKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadGX__A3P.TracesA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.Pcap_ifaceA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.Pcap_iface_ngA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.Pcap_iface_ppA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.LibcKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.FrameKit__A3P.FrameKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.CkTac__A3P.PerfKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.FmtKitA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_ngchk_defsA__A3P.F_pcap_statsA.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Open Scope bv_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_chunks_extra m a bs n Hn Ha Hl ::= unp_store m a bs n Hn Ha Hl.
Local Ltac transport_call_extra segs W m m' MU WM ::= unp_call W m m' MU.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Ltac ienterG := lazymatch goal with |- implMG _ _ _ ?Q _ => let QQ := fresh "POSTQ" in set (QQ := Q) end; apply implMG_from_evtF.
Ltac hide H := lazymatch type of H with ?T => let X := fresh "AUX" in set (X := T) in H end.
Ltac unhide H := lazymatch type of H with ?X => subst X end.

Definition NGN_EPILOGUE_A : Z := 0x8d0f4.
Definition NGN_LOOP_A : Z := 0x8cc7c.

Section CANSEC1. Context {rc : runConstT} {tlsI : ABase.atlsT}.
Section NgnCtx.
  Context {H hptr : Type} (HO : HeapOps H hptr) (FO : @FrameOps H hptr) (sites : stack_site -> Z).
  Variable GIOA : alayout -> footprint -> PState H hptr -> list (@cblock hptr) -> list (@cblock hptr) -> list fblock -> mem -> Prop.
  Variable TP : tparams.
  Variable fflagA : alayout -> fframe -> Z -> Z.
  Hypothesis GL : gia_laws FO GIOA fflagA.

  (* [comment removed for export] *)
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
  Variables (L : alayout) (RNG : footprint) (CLc FB : list (@cblock hptr)) (FL : list fblock) (lo P HA DA Af : Z) (m : mem) (o : option hptr).
  Hypothesis LO : (ATOP + 4096 <= lo)%Z.
  Hypothesis BU : (lo + 57344 <= bv_unsigned sp)%Z.
  Hypothesis SPT : (bv_unsigned sp + 16 < al_top L /\ al_top L <= 2^47)%Z.
  Hypothesis RSTK : rng RNG lo (al_top L - lo).
  Hypothesis RIMG : rng_aimg RNG.
  Hypothesis RISH : rng_aimg_sh RNG.
  Hypothesis RTLS : rng_atls RNG.
  Hypothesis TPE : tp = Z_to_bv 64 ATP.
  Hypothesis ALN : (bv_unsigned sp mod 16 = 0)%Z.
  Hypothesis SNPRINTF : snprintf_spec_stmt GIOA.
  (* [comment removed for export] *)
  Hypothesis HALO : (0x603000 <= HA /\ HA + 24 <= ATOP)%Z.
  Hypothesis DALO : (0x603000 <= DA /\ DA + 8 <= ATOP)%Z.
  Hypothesis HAP : (HA + 24 <= P \/ P + 680 <= HA)%Z.
  Hypothesis DAP : (DA + 8 <= P \/ P + 680 <= DA)%Z.

  Let POSTQ := next_packet_post GIOA ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG FL CLc FB lo P HA DA m o.

  (* [comment removed for export] *)
  Definition ngn_frameA (ccs : list cell) : list cell :=
    [C8 (Z_to_bv 64 3); C8 (Z_to_bv 64 7); C8 (Z_to_bv 64 3); C8 (Z_to_bv 64 DA); C8 (Z_to_bv 64 (P + 648)); C8 (Z_to_bv 64 HA);
     C8 (Z_to_bv 64 (Z.shiftr (P + 96) 3 + 2147450880)); C8 (Z_to_bv 64 (P + 96)); C8 (Z_to_bv 64 439041101);
     C8 (Z_to_bv 64 (Z.shiftr (P + 100) 3 + 2147450880)); C8 (Z_to_bv 64 (P + 100)); C8 (Z_to_bv 64 65280)] ++ ccs ++
    [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

  (* [comment removed for export] *)
  #[using="rc L BU SPT RSTK"] Lemma ngn_epilogue :
    forall (ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 t3' t4' t5' t6' : word)
           (m5 : mem) (RNG5 : footprint) (ccs : list cell) (Q : machine_state -> Prop),
      fp_le RNG RNG5 ->
      stk asegs m5 lo (bv_unsigned sp + -224) ->
      rw_cells asegs m5 (bv_unsigned sp + -224) (ngn_frameA ccs) -> cells_size ccs = 24%nat -> mem_inv asegs m5 ->
      (forall t0'' t1'' t2'' a1'' a2'' a3'' a4'' a5'' a6'' a7'' t3'' t4'' t5'' t6'',
          stk asegs m5 lo (bv_unsigned sp) ->
          Q (MS (mkR ra sp gp tp t0'' t1'' t2'' s0 s1 x0 a1'' a2'' a3'' a4'' a5'' a6'' a7'' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3'' t4'' t5'' t6'')
                F (ret_pc ra) fc None m5 (seg_rom asegs))) ->
      evtF asegs RNG5 Q
        (MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -224)) gp tp t0' t1' t2' x0 x1 a0' a1' a2' a3' a4' a5' a6' a7'
                 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 t3' t4' t5' t6') F (Z_to_bv 64 NGN_EPILOGUE_A) fc None m5 (seg_rom asegs)).
  Proof.
    intros until Q. intros FP5 ST5 FR5 Hccs MI5 HQ.
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
    assert (RSPW : rng RNG5 lo (bv_unsigned sp - lo)) by (eapply rng_sub'; [exact (rng_fp_le _ _ _ _ FP5 RSTK)| lia]).
    pose proof (munch_refl ([] : list (Z * Z)) m5) as MU. pose proof (wmono_refl asegs m5) as WM.
    unfold ngn_frameA in FR5.
    apply rw_cells_app in FR5 as [FRJ FR5]. apply rw_cells_app in FR5 as [FRC FRS].
    cbn [cells_size csize Nat.add] in FRS, FRC. rewrite Hccs in FRS.
    replace (bv_unsigned sp + -224 + Z.of_nat 96 + Z.of_nat 24)%Z with (bv_unsigned sp + -104)%Z in FRS by lia.
    replace (bv_unsigned sp + -224 + Z.of_nat 96)%Z with (bv_unsigned sp + -128)%Z in FRC by lia.
    destruct (rw_cells_forget _ _ _ _ FRC) as [cj FRC']. clear FRC. rewrite Hccs in FRC'.
    unfold NGN_EPILOGUE_A. do 16 zstep.
    release_frame FRJ ST5 (bv_unsigned sp + -128)%Z. release_frame FRC' ST5 (bv_unsigned sp + -104)%Z. release_frame FRS ST5 (bv_unsigned sp).
    apply evtF_done. apply HQ. exact ST5.
  Qed.

  (* [comment removed for export] *)
  Definition ngn_final (m5 : mem) (RNG5 : footprint) (ps : PState H hptr) (PB' : list (@cblock hptr)) (p' : pcap hptr hptr) (hcs' : list cell) (dw : cell) : Prop :=
    fp_le RNG RNG5 /\ GIOA L RNG5 ps (CLc ++ PB') FB FL m5 /\ PCAPR (hptr:=hptr) P p' PB' FB m5
    /\ agrees_on (fun a => client_keeps FL CLc (bv_unsigned sp) a /\ ~ (HA <= a < HA + 24) /\ ~ (DA <= a < DA + 8))%Z m m5
    /\ rw_cells asegs m5 HA hcs' /\ cells_size hcs' = 24%nat /\ rw_cells asegs m5 DA [dw] /\ csize dw = 8%nat /\ ps_outfile ps = o.
  (* [comment removed for export] *)
  Definition ngn_finalC (m5 : mem) (RNG5 : footprint) (ps : PState H hptr) (PB' : list (@cblock hptr)) (p' : pcap hptr hptr) (hcs' : list cell) (dw : cell) : Prop :=
    fp_le RNG RNG5 /\ GIOA L RNG5 ps (CLc ++ PB') FB FL m5 /\ PCAPR_closable (hptr:=hptr) P p' PB' FB m5
    /\ agrees_on (fun a => client_keeps FL CLc (bv_unsigned sp) a /\ ~ (HA <= a < HA + 24) /\ ~ (DA <= a < DA + 8))%Z m m5
    /\ rw_cells asegs m5 HA hcs' /\ cells_size hcs' = 24%nat /\ rw_cells asegs m5 DA [dw] /\ csize dw = 8%nat /\ ps_outfile ps = o.

  #[using="Type"] Lemma ngn_final_C : forall m5 RNG5 ps PB' p' hcs' dw, ngn_final m5 RNG5 ps PB' p' hcs' dw -> ngn_finalC m5 RNG5 ps PB' p' hcs' dw.
  Proof. intros m5 RNG5 ps PB' p' hcs' dw (FP5 & G5 & PC5 & REST). split; [exact FP5|]. split; [exact G5|]. split; [apply PCAPR_closable_of; exact PC5| exact REST]. Qed.

  (* [comment removed for export] *)
  #[using="rc BU SPT RSTK"] Lemma ngn_ret_m1 :
    forall (ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 t3' t4' t5' t6' : word) (m5 : mem) (RNG5 : footprint) (ps : PState H hptr)
           (PB' : list (@cblock hptr)) (p' : pcap hptr hptr) (h : pkthdr) (hcs' : list cell) (dw : cell) (ccs : list cell),
      stk asegs m5 lo (bv_unsigned sp + -224) ->
      rw_cells asegs m5 (bv_unsigned sp + -224) (ngn_frameA ccs) -> cells_size ccs = 24%nat -> mem_inv asegs m5 ->
      ngn_finalC m5 RNG5 ps PB' p' hcs' dw ->
      implMG RNG5 (mret ((-1)%Z, h, p')) ps POSTQ
        (MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -224)) gp tp t0' t1' t2' (Z_to_bv 64 (-1)) x1 a0' a1' a2' a3' a4' a5' a6' a7'
                 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 t3' t4' t5' t6') F (Z_to_bv 64 NGN_EPILOGUE_A) fc None m5 (seg_rom asegs)).
  Proof.
    intros until ccs. intros ST5 FR5 Hccs MI5 (FP5 & G5 & PC5 & AG5 & HH & Hh & HD & Hd & OF).
    apply implMG_ret. eapply ngn_epilogue; [exact FP5 | exact ST5 | exact FR5 | exact Hccs | exact MI5 |].
    intros t0'' t1'' t2'' a1'' a2'' a3'' a4'' a5'' a6'' a7'' t3'' t4'' t5'' t6'' ST6.
    subst POSTQ. unfold next_packet_post. split; [exact FP5|]. exists (Z_to_bv 64 (-1)), m5, PB', dw.
    split; [unfold hpost_regs; repeat (lazymatch goal with |- ex _ => eexists end); reflexivity|].
    split; [exact OF|]. split; [exact MI5|]. split; [exact ST6|]. split; [exact AG5|]. split; [exact G5|].
    split; [intros X; exfalso; lia|]. split; [intros _; exact PC5|].
    split; [reflexivity|]. split; [lia|]. split; [intros X; lia|]. split; [intros _; exists hcs'; split; [exact Hh| exact HH]|].
    split; [exact HD| exact Hd].
  Qed.

  (* [comment removed for export] *)
  #[using="rc BU SPT RSTK"] Lemma ngn_ret_0 :
    forall (ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 t3' t4' t5' t6' : word) (m5 : mem) (RNG5 : footprint) (ps : PState H hptr)
           (PB' : list (@cblock hptr)) (p' : pcap hptr hptr) (h : pkthdr) (hcs' : list cell) (dw : cell) (ccs : list cell),
      stk asegs m5 lo (bv_unsigned sp + -224) ->
      rw_cells asegs m5 (bv_unsigned sp + -224) (ngn_frameA ccs) -> cells_size ccs = 24%nat -> mem_inv asegs m5 ->
      ngn_final m5 RNG5 ps PB' p' hcs' dw ->
      implMG RNG5 (mret (0%Z, h, p')) ps POSTQ
        (MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -224)) gp tp t0' t1' t2' (Z_to_bv 64 0) x1 a0' a1' a2' a3' a4' a5' a6' a7'
                 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 t3' t4' t5' t6') F (Z_to_bv 64 NGN_EPILOGUE_A) fc None m5 (seg_rom asegs)).
  Proof.
    intros until ccs. intros ST5 FR5 Hccs MI5 (FP5 & G5 & PC5 & AG5 & HH & Hh & HD & Hd & OF).
    apply implMG_ret. eapply ngn_epilogue; [exact FP5 | exact ST5 | exact FR5 | exact Hccs | exact MI5 |].
    intros t0'' t1'' t2'' a1'' a2'' a3'' a4'' a5'' a6'' a7'' t3'' t4'' t5'' t6'' ST6.
    subst POSTQ. unfold next_packet_post. split; [exact FP5|]. exists (Z_to_bv 64 0), m5, PB', dw.
    split; [unfold hpost_regs; repeat (lazymatch goal with |- ex _ => eexists end); reflexivity|].
    split; [exact OF|]. split; [exact MI5|]. split; [exact ST6|]. split; [exact AG5|]. split; [exact G5|].
    split; [intros _; exact PC5|]. split; [intros X; exfalso; lia|].
    split; [reflexivity|]. split; [lia|]. split; [intros X; lia|]. split; [intros _; exists hcs'; split; [exact Hh| exact HH]|].
    split; [exact HD| exact Hd].
  Qed.

  (* [comment removed for export] *)
  #[using="rc BU SPT RSTK"] Lemma ngn_ret_1 :
    forall (ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 t3' t4' t5' t6' : word) (m5 : mem) (RNG5 : footprint) (ps : PState H hptr)
           (PB' : list (@cblock hptr)) (p' : pcap hptr hptr) (h : pkthdr) (dw : cell) (ccs : list cell),
      stk asegs m5 lo (bv_unsigned sp + -224) ->
      rw_cells asegs m5 (bv_unsigned sp + -224) (ngn_frameA ccs) -> cells_size ccs = 24%nat -> mem_inv asegs m5 ->
      ngn_final m5 RNG5 ps PB' p' (hdr_cells h) dw -> (0 <= h_caplen h < 2^32)%Z -> (0 <= h_len h < 2^32)%Z ->
      implMG RNG5 (mret (1%Z, h, p')) ps POSTQ
        (MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -224)) gp tp t0' t1' t2' x0 x1 a0' a1' a2' a3' a4' a5' a6' a7'
                 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 t3' t4' t5' t6') F (Z_to_bv 64 0x8d8d0) fc None m5 (seg_rom asegs)).
  Proof.
    intros until ccs. intros ST5 FR5 Hccs MI5 (FP5 & G5 & PC5 & AG5 & HH & Hh & HD & Hd & OF) HC HL.
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
    apply implMG_ret. hide HH. hide HD. hide FR5.
    pose proof (munch_refl ([] : list (Z * Z)) m5) as MU. pose proof (wmono_refl asegs m5) as WM.
    do 2 zstep. unhide FR5. eapply ngn_epilogue; [exact FP5 | exact ST5 | exact FR5 | exact Hccs | exact MI5 |].
    intros t0'' t1'' t2'' a1'' a2'' a3'' a4'' a5'' a6'' a7'' t3'' t4'' t5'' t6'' ST6. unhide HH. unhide HD.
    subst POSTQ. unfold next_packet_post. split; [exact FP5|]. exists (Z_to_bv 64 1), m5, PB', dw.
    split; [unfold hpost_regs; repeat (lazymatch goal with |- ex _ => eexists end); reflexivity|].
    split; [exact OF|]. split; [exact MI5|]. split; [exact ST6|]. split; [exact AG5|]. split; [exact G5|].
    split; [intros _; exact PC5|]. split; [intros X; exfalso; lia|].
    split; [reflexivity|]. split; [lia|]. split; [intros _; split; [exact HH| split; [exact HC| exact HL]]|]. split; [intros X; exfalso; lia|].
    split; [exact HD| exact Hd].
  Qed.

  (* [comment removed for export] *)
  #[using="rc tlsI FO fflagA GL sp lo LO BU ALN"] Lemma PCAPRC_errbuf : forall Lx RNGx sx CLx FLx Px (p : pcap hptr hptr) PB FBx (mx mx' : mem) (Q : Z -> Prop) cs e,
    GIOA Lx RNGx sx (CLx ++ PB) FBx FLx mx -> PCAPR_closable (hptr:=hptr) Px p PB FBx mx -> agrees_on Q mx mx' ->
    (forall a, in_block PB a -> ~ (Px + 216 <= a < Px + 472)%Z -> Q a) ->
    rw_cells asegs mx' (Px + 216) cs -> cells_size cs = 256%nat ->
    PCAPR_closable (hptr:=hptr) Px (set_errbuf e p) PB FBx mx'.
  Proof.
    intros Lx RNGx sx CLx FLx Px p PB FBx mx mx' Q cs e G PC AG HQ HCS Hsz.
    destruct PC as (Afx & Hin & (Bx & I & jx & padx & bsx & EPB & CELLS & PRIV & BUF & PFX & IFS & WF)).
    pose proof (psize_pos p) as PS. pose proof (PB_apartA _ _ _ GL _ _ _ _ _ _ _ _ _ _ _ _ G EPB) as [APB API].
    assert (Q1 : forall a, (Px <= a < Px + psize p)%Z -> ~ (Px + 216 <= a < Px + 472)%Z -> Q a).
    { intros a Ha Hn. apply HQ; [|exact Hn]. rewrite EPB. unfold pcap_blocks, in_block. apply Exists_cons_hd. cbn [cb_addr cb_size fst snd]. exact Ha. }
    apply pcap_cells_split4 in CELLS as (CA & CE & CH & CO); [|reflexivity].
    apply (rw_cells_split_CB asegs mx _ [] 304 _ [] [256; 48]%nat) in CE; [|reflexivity]. cbn [mk_CB_cells app] in CE.
    destruct (rw_cells_cut _ _ _ 1 CE) as [_ CE2]. clear CE. cbn [firstn skipn cells_size csize Nat.add] in CE2.
    replace (Px + 216 + Z.of_nat 256)%Z with (Px + 472)%Z in CE2 by lia.
    apply (agrees_rw_cells _ _ _ _ _ AG) in CA; [| intros a Ha; rewrite (pc_pre_size p Px Bx (C8 (Z_to_bv 64 Afx)) jx eq_refl) in Ha; apply Q1; lia].
    apply (agrees_rw_cells _ _ _ _ _ AG) in CH; [| intros a Ha; cbn [cells_size csize hdr_cells Nat.add] in Ha; apply Q1; lia].
    apply (agrees_rw_cells _ _ _ _ _ AG) in CO; [| intros a Ha; cbn [cells_size csize pc_ops Nat.add] in Ha; apply Q1; lia].
    apply (agrees_rw_cells _ _ _ _ _ AG) in CE2; [| intros a Ha; cbn [cells_size csize Nat.add] in Ha; apply Q1; lia].
    pose proof (rw_cells_uncut _ _ _ _ _ HCS CE2 ltac:(rewrite Hsz; lia)) as CE'.
    pose proof WF as (_ & _ & W3 & _).
    destruct (pcap_aux_closable_agree p Px Bx I padx bsx mx mx' Q AG) as (BUF' & PRIV' & IFS');
      [ intros a Ha; apply HQ; [rewrite EPB; unfold pcap_blocks, in_block; apply Exists_cons_tl, Exists_cons_hd; cbn [cb_addr cb_size fst snd]; exact Ha| lia]
      | intros a Ha; apply Q1; unfold PCAP_PRIV_OFF in Ha; lia
      | intros sg q Hq a Ha; destruct (API sg q Hq) as [X1 X2]; apply HQ;
          [rewrite EPB; unfold pcap_blocks, in_block; rewrite Hq; do 2 apply Exists_cons_tl; apply Exists_cons_hd; cbn [cb_addr cb_size fst snd]; exact Ha| lia]
      | lia | exact BUF | exact PRIV | exact IFS |].
    exists Afx. split; [destruct p; exact Hin|].
    exists Bx, I, (set_pj_g (cells_bytes (cs ++ [CB 48 (firstn 48 (skipn 256 (pj_g jx)))])) jx), padx, bsx.
    split; [rewrite EPB; destruct p; reflexivity|].
    split. { pose proof (pcap_cells_join4 mx' Px p Bx (C8 (Z_to_bv 64 Afx)) (C8 (Z_to_bv 64 (pk_stats PK))) (C8 (Z_to_bv 64 (pk_oneshot PK))) jx _ (pc_header p)
                           eq_refl CA CE' ltac:(rewrite cells_size_app, Hsz; reflexivity) CH CO) as J.
             replace (set_header (pc_header p) p) with p in J by (destruct p; reflexivity).
             destruct p; cbn. exact J. }
    split; [destruct p; exact PRIV'|]. split; [destruct p; exact BUF'|]. split; [destruct p; exact PFX|].
    split; [destruct p; exact IFS'|]. destruct p; exact WF.
  Qed.

  (* [comment removed for export] *)
  #[using="FO fflagA GL LO BU SPT RSTK RIMG RISH RTLS TPE ALN SNPRINTF HALO DALO HAP DAP"] Lemma ngn_snp_call :
    forall (RA : Z) (t0' t1' t2' x0 a3' a4' a5' a6' a7' x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 t3' t4' t5' t6' : word) (m5 : mem) (RNG5 : footprint) (ps : PState H hptr)
           (PB' : list (@cblock hptr)) (p' : pcap hptr hptr) (hcs' : list cell) (dw : cell) (ccs : list cell)
           (FMTA : Z) (fs : string) (args : list farg) (Q : machine_state -> Prop),
      stk asegs m5 lo (bv_unsigned sp + -224) ->
      rw_cells asegs m5 (bv_unsigned sp + -224) (ngn_frameA ccs) -> cells_size ccs = 24%nat -> mem_inv asegs m5 ->
      ngn_finalC m5 RNG5 ps PB' p' hcs' dw -> is_ng p' = true ->
      fmt_at m5 FMTA fs -> fmt_ok fs args = true -> (length args <= 3)%nat ->
      Forall2 (farg_word true L RNG5 FL (CLc ++ PB') (bv_unsigned sp + -224) (P + 216) 256 m5) args (firstn (length args) [a3'; a4'; a5']) ->
      (0 <= RA < 2^64)%Z -> (RA mod 2 = 0)%Z ->
      (forall (m6 : mem) (t0'' t1'' t2'' a0'' a1'' a2'' a3'' a4'' a5'' a6'' a7'' t3'' t4'' t5'' t6'' : word),
          stk asegs m6 lo (bv_unsigned sp + -224) -> rw_cells asegs m6 (bv_unsigned sp + -224) (ngn_frameA ccs) -> mem_inv asegs m6 ->
          (forall e, ngn_finalC m6 RNG5 ps PB' (set_errbuf e p') hcs' dw) ->
          evtF asegs RNG5 Q (MS (mkR (Z_to_bv 64 RA) (Z_to_bv 64 (bv_unsigned sp + -224)) gp tp t0'' t1'' t2'' x0 x1 a0'' a1'' a2'' a3'' a4'' a5'' a6'' a7''
                           x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 t3'' t4'' t5'' t6'') F (Z_to_bv 64 RA) fc None m6 (seg_rom asegs))) ->
      evtF asegs RNG5 Q
        (MS (mkR (Z_to_bv 64 RA) (Z_to_bv 64 (bv_unsigned sp + -224)) gp tp t0' t1' t2' x0 x1
                 (Z_to_bv 64 (P + 216)) (Z_to_bv 64 256) (Z_to_bv 64 FMTA) a3' a4' a5' a6' a7'
                 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 t3' t4' t5' t6') F (Z_to_bv 64 SNPRINTF_ENTRY) fc None m5 (seg_rom asegs)).
  Proof.
    intros until Q. intros ST5 FR5 Hccs MI5 (FP5 & G5 & PC5 & AG5 & HH & Hh & HD & Hd & OF5) NG5 FMT5 FOK LA FW RA64 RAE HK.
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
    pose proof PC5 as (Afx & _ & (Bx & Ix & jx & padx & bsx & EPB & CELLS & _ & _ & _ & _ & WF)).
    assert (PS : psize p' = 680%Z) by (unfold psize; rewrite NG5; reflexivity).
    assert (HinP : In (pc_self p', P, psize p') ((CLc ++ PB') ++ FB)) by (apply in_or_app; left; apply in_or_app; right; rewrite EPB; left; reflexivity).
    pose proof (gl_block _ _ _ GL _ _ _ _ _ _ _ _ G5 HinP) as PBLK. pose proof PBLK as ((PBAND & P3 & PTOP & P2) & P1 & _).
    cbn [cb_addr cb_size fst snd] in PBAND, P3, PTOP, P2, P1. rewrite PS in *.
    apply pcap_cells_split4 in CELLS as (_ & CE & _ & _); [|reflexivity].
    apply (rw_cells_split_CB asegs m5 _ [] 304 _ [] [256; 48]%nat) in CE; [|reflexivity]. cbn [mk_CB_cells app] in CE.
    destruct (rw_cells_cut _ _ _ 1 CE) as [CE1 _]. clear CE. cbn [firstn skipn cells_size csize Nat.add] in CE1.
    pose proof (rng_fp_le _ _ _ _ FP5 RSTK) as RSTK5. pose proof (rng_fp_le _ _ _ _ FP5 RIMG) as RIMG5.
    pose proof (rng_fp_le _ _ _ _ FP5 RISH) as RISH5. pose proof (rng_fp_le _ _ _ _ FP5 RTLS) as RTLS5.
    name_sp sp (-224)%Z.
    eapply evtF_cut.
    { eapply SNPRINTF with (L := L) (s := ps) (CL := CLc ++ PB') (FB := FB) (FL := FL) (lo := lo) (DST := (P + 216)%Z) (n := 256%Z) (FMTA := FMTA) (fs := fs) (args := args)
                           (junk := firstn 256 (pj_g jx));
        [ split; [exact G5|]; split; [rewrite Hsp; exact ST5|]; split; [lia|]; split; [unfold STDIO_STACK; rewrite Hsp; lia|];
          split; [rewrite Hsp; lia|]; split; [exact MI5|]; split; [exact TPE|]; split; [rewrite Hsp; apply aln16_add; [exact ALN| reflexivity]|];
          split; [exact RSTK5|]; split; [exact RIMG5|]; split; [exact RISH5| exact RTLS5]
        | reflexivity | reflexivity | reflexivity | lia | exact FMT5 | exact FOK | exact LA | rewrite Hsp; exact FW | exact CE1
        | split; [left; exists (pc_self p', P, psize p'); split; [apply in_or_app; right; rewrite EPB; left; reflexivity| cbn [cb_addr cb_size fst snd]; lia]
                 | eapply blockA_aobj; [exact PBLK | cbn [cb_addr cb_size fst snd]; lia | cbn [cb_addr cb_size fst snd]; lia | lia]] ]. }
    cbv beta. intros ms' PO. destruct PO as (av & m6 & junk6 & E & MU6 & WM6 & MI6 & ST6 & -> & HEB6).
    unfold hpost_regs in E. destruct_exs E. subst ms'. rewrite Hsp in *. unname_sp.
    replace (ret_pc (Z_to_bv 64 RA)) with (Z_to_bv 64 RA) by (symmetry; apply ret_pc_even; [exact RA64| exact RAE]).
    unfold STDIO_STACK in MU6.
    assert (AGS : agrees_on (fun a => outside [(bv_unsigned sp + -224 - 16384, bv_unsigned sp + -224); (P + 216, P + 216 + 256)]%Z a) m5 m6)
      by (eapply agrees_on_of_munch; [exact MU6 | exact WM6 | intros a _ Ho; exact Ho]).
    apply (agrees_rw_cells _ _ _ _ _ AGS) in FR5; [| intros a Ha; unfold ngn_frameA in Ha; rewrite !cells_size_app in Ha; cbn [outside fst snd cells_size csize Nat.add] in *; rewrite Hccs in Ha; lia].
    apply (agrees_rw_cells _ _ _ _ _ AGS) in HH; [| intros a Ha; rewrite Hh in Ha; cbn [outside fst snd]; lia].
    apply (agrees_rw_cells _ _ _ _ _ AGS) in HD; [| intros a Ha; cbn [cells_size] in Ha; rewrite Hd in Ha; cbn [outside fst snd]; lia].
    assert (FW6 : Forall (pcap_iv FL PB') [(bv_unsigned sp + -224 - 16384, bv_unsigned sp + -224); (P + 216, P + 216 + 256)]%Z).
    { apply Forall_cons; [left; cbn [fst snd]; lia|]. apply Forall_cons; [|apply Forall_nil].
      right; left. rewrite EPB. unfold iv_in_block, pcap_blocks. apply Exists_cons_hd. cbn [cb_addr cb_size fst snd]. lia. }
    assert (G6 : GIOA L RNG5 ps (CLc ++ PB') FB FL m6) by (eapply (gl_frame _ _ _ GL); [exact G5 | exact MU6 | exact WM6 | exact FW6]).
    assert (PC6 : forall e, PCAPR_closable (hptr:=hptr) P (set_errbuf e p') PB' FB m6).
    { intros e. eapply (PCAPRC_errbuf _ _ _ _ _ _ _ _ _ _ _ _ _ _ G5 PC5 AGS); [| exact HEB6 | pose proof (snprintf_length_le 256 fs args ltac:(lia)); cbn [cells_size csize Nat.add]; lia].
      intros a Ha Hn. cbn [outside fst snd]. pose proof (gia_in_block_below _ _ _ GL _ _ _ _ _ _ _ a G5 ltac:(apply in_block_app; left; apply in_block_app; right; exact Ha)). lia. }
    assert (AG6 : agrees_on (fun a => client_keeps FL CLc (bv_unsigned sp) a /\ ~ (HA <= a < HA + 24) /\ ~ (DA <= a < DA + 8))%Z m m6).
    { eapply agrees_on_trans; [exact AG5|]. eapply agrees_on_weaken; [| intros a [K _]; exact K].
      eapply (gl_keeps _ _ _ GL _ _ _ _ _ _ FL []); [exact G5 | exact MU6 | exact WM6 | | lia].
      apply Forall_cons; [left; cbn [fst snd]; lia|]. apply Forall_cons; [|apply Forall_nil].
      right; left. rewrite EPB. unfold iv_in_block, pcap_blocks. apply Exists_cons_hd. cbn [cb_addr cb_size fst snd]. lia. }
    apply HK; [exact ST6 | exact FR5 | exact MI6 |].
    intros e. split; [exact FP5|]. split; [exact G6|]. split; [exact (PC6 e)|]. split; [exact AG6|]. split; [exact HH|]. split; [exact Hh|]. split; [exact HD|]. split; [exact Hd| exact OF5].
  Qed.

  (* [comment removed for export] *)
  #[using="FO fflagA GL LO BU SPT RSTK RIMG RISH RTLS TPE ALN SNPRINTF HALO DALO HAP DAP"] Lemma ngn_snp :
    forall (t0' t1' t2' a3' a4' a5' a6' a7' x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 t3' t4' t5' t6' : word) (m5 : mem) (RNG5 : footprint) (ps : PState H hptr)
           (PB' : list (@cblock hptr)) (p' : pcap hptr hptr) (h : pkthdr) (hcs' : list cell) (dw : cell) (ccs : list cell)
           (FMTA : Z) (fs : string) (args : list farg) (e : list Z),
      stk asegs m5 lo (bv_unsigned sp + -224) ->
      rw_cells asegs m5 (bv_unsigned sp + -224) (ngn_frameA ccs) -> cells_size ccs = 24%nat -> mem_inv asegs m5 ->
      ngn_finalC m5 RNG5 ps PB' p' hcs' dw -> is_ng p' = true ->
      fmt_at m5 FMTA fs -> fmt_ok fs args = true -> (length args <= 3)%nat ->
      Forall2 (farg_word true L RNG5 FL (CLc ++ PB') (bv_unsigned sp + -224) (P + 216) 256 m5) args (firstn (length args) [a3'; a4'; a5']) ->
      implMG RNG5 (mret ((-1)%Z, h, set_errbuf e p')) ps POSTQ
        (MS (mkR (Z_to_bv 64 NGN_EPILOGUE_A) (Z_to_bv 64 (bv_unsigned sp + -224)) gp tp t0' t1' t2' (Z_to_bv 64 (-1)) x1
                 (Z_to_bv 64 (P + 216)) (Z_to_bv 64 256) (Z_to_bv 64 FMTA) a3' a4' a5' a6' a7'
                 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 t3' t4' t5' t6') F (Z_to_bv 64 SNPRINTF_ENTRY) fc None m5 (seg_rom asegs)).
  Proof.
    intros until e. intros ST5 FR5 Hccs MI5 FIN NG5 FMT5 FOK LA FW.
    ienterG. unfold NGN_EPILOGUE_A.
    eapply ngn_snp_call; [exact ST5 | exact FR5 | exact Hccs | exact MI5 | exact FIN | exact NG5 | exact FMT5 | exact FOK | exact LA | exact FW | lia | reflexivity |].
    intros m6 t0'' t1'' t2'' a0'' a1'' a2'' a3'' a4'' a5'' a6'' a7'' t3'' t4'' t5'' t6'' ST6 FR6 MI6 FIN6.
    apply evtF_done. eapply ngn_ret_m1; [exact ST6 | exact FR6 | exact Hccs | exact MI6 | exact (FIN6 e)].
  Qed.

  (* [comment removed for export] *)
  #[using="rc tlsI FO fflagA GL LO BU SPT RSTK RIMG RISH ALN HALO DALO HAP DAP"] Lemma ngn_mcp :
    forall (ra' t0' t1' t2' a0' a3' a4' a5' a6' a7' x1 x2 x4 x5 x6 x7 x8 x9 x10 x11 t3' t4' t5' t6' : word) (m5 : mem) (RNG5 : footprint) (ps : PState H hptr)
           (PB' : list (@cblock hptr)) (p' : pcap hptr hptr) (h : pkthdr) (hcs' : list cell) (dw : cell) (ccs : list cell)
           (STR n : Z) (src : list byte) (e : list Z),
      stk asegs m5 lo (bv_unsigned sp + -224) ->
      rw_cells asegs m5 (bv_unsigned sp + -224) (ngn_frameA ccs) -> cells_size ccs = 24%nat -> mem_inv asegs m5 ->
      ngn_finalC m5 RNG5 ps PB' p' hcs' dw -> is_ng p' = true ->
      bytes_at asegs m5 STR src -> length src = Z.to_nat n -> (0 <= n <= 256)%Z -> In (STR, n) client_globals -> (STR + n <= 0x32000)%Z ->
      implMG RNG5 (mret ((-1)%Z, h, set_errbuf e p')) ps POSTQ
        (MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -224)) gp tp t0' t1' t2' (Z_to_bv 64 (-1)) x1
                 a0' (Z_to_bv 64 STR) (Z_to_bv 64 n) a3' a4' a5' a6' a7'
                 x2 (Z_to_bv 64 (P + 216)) x4 x5 x6 x7 x8 x9 x10 x11 t3' t4' t5' t6') F (Z_to_bv 64 0x8d0ac) fc None m5 (seg_rom asegs)).
  Proof.
    intros until e. intros ST5 FR5 Hccs MI5 (FP5 & G5 & PC5 & AG5 & HH & Hh & HD & Hd & OF5) NG5 SRC LEN Hn HG HSTR.
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
    pose proof PC5 as (Afx & _ & (Bx & Ix & jx & padx & bsx & EPB & CELLS & _ & _ & _ & _ & WF)).
    assert (PS : psize p' = 680%Z) by (unfold psize; rewrite NG5; reflexivity).
    assert (HinP : In (pc_self p', P, psize p') ((CLc ++ PB') ++ FB)) by (apply in_or_app; left; apply in_or_app; right; rewrite EPB; left; reflexivity).
    pose proof (gl_block _ _ _ GL _ _ _ _ _ _ _ _ G5 HinP) as PBLK. pose proof PBLK as ((PBAND & P3 & PTOP & P2) & P1 & _).
    cbn [cb_addr cb_size fst snd] in PBAND, P3, PTOP, P2, P1. rewrite PS in *.
    pose proof (gl_rt _ _ _ GL _ _ _ _ _ _ _ G5) as (RT5 & _).
    pose proof (ablk_lin _ _ PBAND) as (PIMG & _ & PATOP & _). unfold AIMG_HI in PIMG.
    pose proof (rng_fp_le _ _ _ _ FP5 RSTK) as RSTK5. pose proof (rng_fp_le _ _ _ _ FP5 RIMG) as RIMG5. pose proof (rng_fp_le _ _ _ _ FP5 RISH) as RISH5.
    assert (RSPW : rng RNG5 lo (bv_unsigned sp + -224 - lo)) by (eapply rng_sub'; [exact RSTK5| lia]).
    assert (RSPX : rng RNG5 lo (bv_unsigned sp - lo)) by (eapply rng_sub'; [exact RSTK5| lia]).
    pose proof (gia_global_mobjA _ _ _ GL _ _ _ _ _ _ _ _ _ G5 HG RIMG5 RISH5) as OSRC.
    apply pcap_cells_split4 in CELLS as (_ & CE & _ & _); [|reflexivity].
    apply (rw_cells_split_CB asegs m5 _ [] 304 _ [] [Z.to_nat n; 256 - Z.to_nat n; 48]%nat) in CE; [|cbn; lia]. cbn [mk_CB_cells app] in CE.
    destruct (rw_cells_cut _ _ _ 1 CE) as [CE1 CE23]. clear CE. cbn [firstn skipn cells_size csize Nat.add] in CE1, CE23.
    destruct (rw_cells_cut _ _ _ 1 CE23) as [CE2 _]. clear CE23. cbn [firstn skipn cells_size csize Nat.add] in CE2.
    ienterG. hide FR5. hide HH. hide HD. hide CE2.
    pose proof (munch_refl [(bv_unsigned sp + -224 - 2224, bv_unsigned sp + -224); (P + 216, P + 216 + n)]%Z m5) as MU. pose proof (wmono_refl asegs m5) as WM.
    zstep. zstep.
    name_sp sp (-224)%Z.
    eapply evtF_cut.
    { eapply (asan_memcpy_specZ RNG5 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m5 lo (P + 216)%Z STR n src (firstn (Z.to_nat n) (pj_g jx)));
        [ reflexivity | reflexivity | reflexivity | exact MI5 | rewrite Hsp; exact ST5 | rewrite Hsp; lia | lia | exact RT5 | exact SRC | exact LEN | lia | exact CE1
        | left; lia | exact OSRC
        | apply aobjA_mobjA; [eapply blockA_aobj; [exact PBLK | cbn [cb_addr cb_size fst snd]; lia | cbn [cb_addr cb_size fst snd]; lia | lia] | lia]
        | lia | lia | exact RIMG5 | rewrite Hsp; exact RSPW ]. }
    cbv beta. intros ms' PO. destruct PO as (y0 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & y8 & y9 & y10 & y11 & y12 & y13 & m6 & -> & MU6 & WM6 & MI6 & ST6 & HEB6 & _).
    rewrite Hsp in *. unname_sp.
    replace (ret_pc (Z_to_bv 64 577716)) with (Z_to_bv 64 577716) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
    unhide FR5. unhide HH. unhide HD. unhide CE2.
    assert (AGS : agrees_on (fun a => outside [(bv_unsigned sp + -224 - 2224, bv_unsigned sp + -224); (P + 216, P + 216 + n)]%Z a) m5 m6)
      by (eapply agrees_on_of_munch; [exact MU6 | exact WM6 | intros a _ Ho; exact Ho]).
    apply (agrees_rw_cells _ _ _ _ _ AGS) in FR5; [| intros a Ha; unfold ngn_frameA in Ha; rewrite !cells_size_app in Ha; cbn [outside fst snd cells_size csize Nat.add] in *; rewrite Hccs in Ha; lia].
    apply (agrees_rw_cells _ _ _ _ _ AGS) in HH; [| intros a Ha; rewrite Hh in Ha; cbn [outside fst snd]; lia].
    apply (agrees_rw_cells _ _ _ _ _ AGS) in HD; [| intros a Ha; cbn [cells_size] in Ha; rewrite Hd in Ha; cbn [outside fst snd]; lia].
    apply (agrees_rw_cells _ _ _ _ _ AGS) in CE2; [| intros a Ha; cbn [outside fst snd cells_size csize Nat.add] in *; lia].
    pose proof (rw_cells_uncut _ _ _ _ _ HEB6 CE2 ltac:(cbn [cells_size csize Nat.add]; lia)) as HEB. cbn [app] in HEB.
    assert (FW6 : Forall (pcap_iv FL PB') [(bv_unsigned sp + -224 - 2224, bv_unsigned sp + -224); (P + 216, P + 216 + n)]%Z).
    { apply Forall_cons; [left; cbn [fst snd]; lia|]. apply Forall_cons; [|apply Forall_nil].
      right; left. rewrite EPB. unfold iv_in_block, pcap_blocks. apply Exists_cons_hd. cbn [cb_addr cb_size fst snd]. lia. }
    assert (G6 : GIOA L RNG5 ps (CLc ++ PB') FB FL m6) by (eapply (gl_frame _ _ _ GL); [exact G5 | exact MU6 | exact WM6 | exact FW6]).
    assert (PC6 : PCAPR_closable (hptr:=hptr) P (set_errbuf e p') PB' FB m6).
    { eapply (PCAPRC_errbuf _ _ _ _ _ _ _ _ _ _ _ _ _ _ G5 PC5 AGS); [| exact HEB | cbn [cells_size csize Nat.add]; lia].
      intros a Ha Hna. cbn [outside fst snd]. pose proof (gia_in_block_below _ _ _ GL _ _ _ _ _ _ _ a G5 ltac:(apply in_block_app; left; apply in_block_app; right; exact Ha)). lia. }
    assert (AG6 : agrees_on (fun a => client_keeps FL CLc (bv_unsigned sp) a /\ ~ (HA <= a < HA + 24) /\ ~ (DA <= a < DA + 8))%Z m m6).
    { eapply agrees_on_trans; [exact AG5|]. eapply agrees_on_weaken; [| intros a [K _]; exact K].
      eapply (gl_keeps _ _ _ GL _ _ _ _ _ _ FL []); [exact G5 | exact MU6 | exact WM6 | | lia].
      apply Forall_cons; [left; cbn [fst snd]; lia|]. apply Forall_cons; [|apply Forall_nil].
      right; left. rewrite EPB. unfold iv_in_block, pcap_blocks. apply Exists_cons_hd. cbn [cb_addr cb_size fst snd]. lia. }
    clear MU WM. pose proof (munch_refl ([] : list (Z * Z)) m6) as MU. pose proof (wmono_refl asegs m6) as WM.
    hide FR5. hide HH. hide HD. hide HEB.
    zstep. unhide FR5. unhide HH. unhide HD.
    apply evtF_done. eapply ngn_ret_m1; [exact ST6 | exact FR5 | exact Hccs | exact MI6 |].
    split; [exact FP5|]. split; [exact G6|]. split; [exact PC6|]. split; [exact AG6|]. split; [exact HH|]. split; [exact Hh|]. split; [exact HD|]. split; [exact Hd| exact OF5].
  Qed.
End NgnCtx.
End CANSEC1.

(* [comment removed for export] *)

Module TwB.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Strings.String.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Tac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Arr OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Bytes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ZBridge OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ITree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Nodes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Decode OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.SysStep OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Frame OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.StoreFast OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Image.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Monad OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Fmt OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.StdioCore OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Stdio OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapPrelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapTypes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapPure OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Pcap OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prog.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.FileCells__Musl.StrFun OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_kit__Musl.StartupKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.CellsExtra.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.FmtFacts__S3.FmtFacts.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.ExecF OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.ITreeA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.Shadow OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.StepF OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.SysStepF OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.RunDraw.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AMalloc_iface.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.CkTac__A3P.CkTac.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadG.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.GIA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.PcapRepA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.UnwKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadGX__A3P.TracesA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.Pcap_ifaceA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.Pcap_iface_ngA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.Pcap_iface_ppA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.LibcKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.FrameKit__A3P.FrameKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.CkTac__A3P.PerfKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.FmtKitA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_ngchk_defsA__A3P.F_pcap_statsA.TwB. Local Ltac Zify.zify_pre_hook ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB.twm_hook_1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Open Scope bv_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_chunks_extra m a bs n Hn Ha Hl ::= unp_store m a bs n Hn Ha Hl.
Local Ltac transport_call_extra segs W m m' MU WM ::= unp_call W m m' MU.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Ltac ienterG := lazymatch goal with |- implMG _ _ _ ?Q _ => let QQ := fresh "POSTQ" in set (QQ := Q) end; apply implMG_from_evtF.
Ltac hide H := lazymatch type of H with ?T => let X := fresh "AUX" in set (X := T) in H end.
Ltac unhide H := lazymatch type of H with ?X => subst X end.

Definition NGN_EPILOGUE_A : Z := 0x8d9f4.
Definition NGN_LOOP_A : Z := 0x8ce28.

Section CANSEC1. Context {rc : runConstT} {tlsI : A3W.ABase.TwB.atlsT}.
Section NgnCtx.
  Context {H hptr : Type} (HO : HeapOps H hptr) (FO : @FrameOps H hptr) (sites : stack_site -> Z).
  Variable GIOA : alayout -> footprint -> PState H hptr -> list (@cblock hptr) -> list (@cblock hptr) -> list fblock -> mem -> Prop.
  Variable TP : tparams.
  Variable fflagA : alayout -> fframe -> Z -> Z.
  Hypothesis GL : gia_laws FO GIOA fflagA.

  (* [comment removed for export] *)
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
  Variables (L : alayout) (RNG : footprint) (CLc FB : list (@cblock hptr)) (FL : list fblock) (lo P HA DA Af : Z) (m : mem) (o : option hptr).
  Hypothesis LO : (ATOP + 4096 <= lo)%Z.
  Hypothesis BU : (lo + 57344 <= bv_unsigned sp)%Z.
  Hypothesis SPT : (bv_unsigned sp + 16 < al_top L /\ al_top L <= 2^47)%Z.
  Hypothesis RSTK : rng RNG lo (al_top L - lo).
  Hypothesis RIMG : rng_aimg RNG.
  Hypothesis RISH : rng_aimg_sh RNG.
  Hypothesis RTLS : rng_atls RNG.
  Hypothesis TPE : tp = Z_to_bv 64 ATP.
  Hypothesis ALN : (bv_unsigned sp mod 16 = 0)%Z.
  Hypothesis SNPRINTF : snprintf_spec_stmt GIOA.
  (* [comment removed for export] *)
  Hypothesis HALO : (0x604000 <= HA /\ HA + 24 <= ATOP)%Z.
  Hypothesis DALO : (0x604000 <= DA /\ DA + 8 <= ATOP)%Z.
  Hypothesis HAP : (HA + 24 <= P \/ P + 680 <= HA)%Z.
  Hypothesis DAP : (DA + 8 <= P \/ P + 680 <= DA)%Z.

  Let POSTQ := next_packet_post GIOA ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG FL CLc FB lo P HA DA m o.

  (* [comment removed for export] *)
  Definition ngn_frameA (ccs : list cell) : list cell :=
    [C8 (Z_to_bv 64 3); C8 (Z_to_bv 64 7); C8 (Z_to_bv 64 3); C8 (Z_to_bv 64 DA); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 (P + 648)); C8 (Z_to_bv 64 HA);
     C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 439041101); C8 (Z_to_bv 64 (P + 100));
     C8 (Z_to_bv 64 (Z.shiftr (P + 100) 3 + 2147450880)); C8 (Z_to_bv 64 (Z.shiftr (P + 96) 3 + 2147450880)); C8 (Z_to_bv 64 (P + 96)); C8 (Z_to_bv 64 65280)] ++ ccs ++
    [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

  (* [comment removed for export] *)
  #[using="rc L BU SPT RSTK"] Lemma ngn_epilogue :
    forall (ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 t3' t4' t5' t6' : word)
           (m5 : mem) (RNG5 : footprint) (ccs : list cell) (Q : machine_state -> Prop),
      fp_le RNG RNG5 ->
      stk asegs m5 lo (bv_unsigned sp + -240) ->
      rw_cells asegs m5 (bv_unsigned sp + -240) (ngn_frameA ccs) -> cells_size ccs = 24%nat -> mem_inv asegs m5 ->
      (forall t0'' t1'' t2'' a1'' a2'' a3'' a4'' a5'' a6'' a7'' t3'' t4'' t5'' t6'',
          stk asegs m5 lo (bv_unsigned sp) ->
          Q (MS (mkR ra sp gp tp t0'' t1'' t2'' s0 s1 x0 a1'' a2'' a3'' a4'' a5'' a6'' a7'' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3'' t4'' t5'' t6'')
                F (ret_pc ra) fc None m5 (seg_rom asegs))) ->
      evtF asegs RNG5 Q
        (MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -240)) gp tp t0' t1' t2' x0 x3 a0' a1' a2' a3' a4' a5' a6' a7'
                 x4 x5 x2 x1 x6 x7 x8 x9 x10 x11 t3' t4' t5' t6') F (Z_to_bv 64 NGN_EPILOGUE_A) fc None m5 (seg_rom asegs)).
  Proof.
    intros until Q. intros FP5 ST5 FR5 Hccs MI5 HQ.
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
    assert (RSPW : rng RNG5 lo (bv_unsigned sp - lo)) by (eapply rng_sub'; [exact (rng_fp_le _ _ _ _ FP5 RSTK)| lia]).
    pose proof (munch_refl ([] : list (Z * Z)) m5) as MU. pose proof (wmono_refl asegs m5) as WM.
    unfold ngn_frameA in FR5.
    apply rw_cells_app in FR5 as [FRJ FR5]. apply rw_cells_app in FR5 as [FRC FRS].
    cbn [cells_size csize Nat.add] in FRS, FRC. rewrite Hccs in FRS.
    replace (bv_unsigned sp + -240 + Z.of_nat 112 + Z.of_nat 24)%Z with (bv_unsigned sp + -104)%Z in FRS by lia.
    replace (bv_unsigned sp + -240 + Z.of_nat 112)%Z with (bv_unsigned sp + -128)%Z in FRC by lia.
    destruct (rw_cells_forget _ _ _ _ FRC) as [cj FRC']. clear FRC. rewrite Hccs in FRC'.
    unfold NGN_EPILOGUE_A. do 16 zstep.
    release_frame FRJ ST5 (bv_unsigned sp + -128)%Z. release_frame FRC' ST5 (bv_unsigned sp + -104)%Z. release_frame FRS ST5 (bv_unsigned sp).
    apply evtF_done. apply HQ. exact ST5.
  Qed.

  (* [comment removed for export] *)
  Definition ngn_final (m5 : mem) (RNG5 : footprint) (ps : PState H hptr) (PB' : list (@cblock hptr)) (p' : pcap hptr hptr) (hcs' : list cell) (dw : cell) : Prop :=
    fp_le RNG RNG5 /\ GIOA L RNG5 ps (CLc ++ PB') FB FL m5 /\ PCAPR (hptr:=hptr) P p' PB' FB m5
    /\ agrees_on (fun a => client_keeps FL CLc (bv_unsigned sp) a /\ ~ (HA <= a < HA + 24) /\ ~ (DA <= a < DA + 8))%Z m m5
    /\ rw_cells asegs m5 HA hcs' /\ cells_size hcs' = 24%nat /\ rw_cells asegs m5 DA [dw] /\ csize dw = 8%nat /\ ps_outfile ps = o.
  (* [comment removed for export] *)
  Definition ngn_finalC (m5 : mem) (RNG5 : footprint) (ps : PState H hptr) (PB' : list (@cblock hptr)) (p' : pcap hptr hptr) (hcs' : list cell) (dw : cell) : Prop :=
    fp_le RNG RNG5 /\ GIOA L RNG5 ps (CLc ++ PB') FB FL m5 /\ PCAPR_closable (hptr:=hptr) P p' PB' FB m5
    /\ agrees_on (fun a => client_keeps FL CLc (bv_unsigned sp) a /\ ~ (HA <= a < HA + 24) /\ ~ (DA <= a < DA + 8))%Z m m5
    /\ rw_cells asegs m5 HA hcs' /\ cells_size hcs' = 24%nat /\ rw_cells asegs m5 DA [dw] /\ csize dw = 8%nat /\ ps_outfile ps = o.

  #[using="Type"] Lemma ngn_final_C : forall m5 RNG5 ps PB' p' hcs' dw, ngn_final m5 RNG5 ps PB' p' hcs' dw -> ngn_finalC m5 RNG5 ps PB' p' hcs' dw.
  Proof. intros m5 RNG5 ps PB' p' hcs' dw (FP5 & G5 & PC5 & REST). split; [exact FP5|]. split; [exact G5|]. split; [apply PCAPR_closable_of; exact PC5| exact REST]. Qed.

  (* [comment removed for export] *)
  #[using="rc BU SPT RSTK"] Lemma ngn_ret_m1 :
    forall (ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 t3' t4' t5' t6' : word) (m5 : mem) (RNG5 : footprint) (ps : PState H hptr)
           (PB' : list (@cblock hptr)) (p' : pcap hptr hptr) (h : pkthdr) (hcs' : list cell) (dw : cell) (ccs : list cell),
      stk asegs m5 lo (bv_unsigned sp + -240) ->
      rw_cells asegs m5 (bv_unsigned sp + -240) (ngn_frameA ccs) -> cells_size ccs = 24%nat -> mem_inv asegs m5 ->
      ngn_finalC m5 RNG5 ps PB' p' hcs' dw ->
      implMG RNG5 (mret ((-1)%Z, h, p')) ps POSTQ
        (MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -240)) gp tp t0' t1' t2' (Z_to_bv 64 (-1)) x3 a0' a1' a2' a3' a4' a5' a6' a7'
                 x4 x5 x2 x1 x6 x7 x8 x9 x10 x11 t3' t4' t5' t6') F (Z_to_bv 64 NGN_EPILOGUE_A) fc None m5 (seg_rom asegs)).
  Proof.
    intros until ccs. intros ST5 FR5 Hccs MI5 (FP5 & G5 & PC5 & AG5 & HH & Hh & HD & Hd & OF).
    apply implMG_ret. eapply ngn_epilogue; [exact FP5 | exact ST5 | exact FR5 | exact Hccs | exact MI5 |].
    intros t0'' t1'' t2'' a1'' a2'' a3'' a4'' a5'' a6'' a7'' t3'' t4'' t5'' t6'' ST6.
    subst POSTQ. unfold next_packet_post. split; [exact FP5|]. exists (Z_to_bv 64 (-1)), m5, PB', dw.
    split; [unfold hpost_regs; repeat (lazymatch goal with |- ex _ => eexists end); reflexivity|].
    split; [exact OF|]. split; [exact MI5|]. split; [exact ST6|]. split; [exact AG5|]. split; [exact G5|].
    split; [intros X; exfalso; lia|]. split; [intros _; exact PC5|].
    split; [reflexivity|]. split; [lia|]. split; [intros X; lia|]. split; [intros _; exists hcs'; split; [exact Hh| exact HH]|].
    split; [exact HD| exact Hd].
  Qed.

  (* [comment removed for export] *)
  #[using="rc BU SPT RSTK"] Lemma ngn_ret_0 :
    forall (ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 t3' t4' t5' t6' : word) (m5 : mem) (RNG5 : footprint) (ps : PState H hptr)
           (PB' : list (@cblock hptr)) (p' : pcap hptr hptr) (h : pkthdr) (hcs' : list cell) (dw : cell) (ccs : list cell),
      stk asegs m5 lo (bv_unsigned sp + -240) ->
      rw_cells asegs m5 (bv_unsigned sp + -240) (ngn_frameA ccs) -> cells_size ccs = 24%nat -> mem_inv asegs m5 ->
      ngn_final m5 RNG5 ps PB' p' hcs' dw ->
      implMG RNG5 (mret (0%Z, h, p')) ps POSTQ
        (MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -240)) gp tp t0' t1' t2' (Z_to_bv 64 0) x3 a0' a1' a2' a3' a4' a5' a6' a7'
                 x4 x5 x2 x1 x6 x7 x8 x9 x10 x11 t3' t4' t5' t6') F (Z_to_bv 64 NGN_EPILOGUE_A) fc None m5 (seg_rom asegs)).
  Proof.
    intros until ccs. intros ST5 FR5 Hccs MI5 (FP5 & G5 & PC5 & AG5 & HH & Hh & HD & Hd & OF).
    apply implMG_ret. eapply ngn_epilogue; [exact FP5 | exact ST5 | exact FR5 | exact Hccs | exact MI5 |].
    intros t0'' t1'' t2'' a1'' a2'' a3'' a4'' a5'' a6'' a7'' t3'' t4'' t5'' t6'' ST6.
    subst POSTQ. unfold next_packet_post. split; [exact FP5|]. exists (Z_to_bv 64 0), m5, PB', dw.
    split; [unfold hpost_regs; repeat (lazymatch goal with |- ex _ => eexists end); reflexivity|].
    split; [exact OF|]. split; [exact MI5|]. split; [exact ST6|]. split; [exact AG5|]. split; [exact G5|].
    split; [intros _; exact PC5|]. split; [intros X; exfalso; lia|].
    split; [reflexivity|]. split; [lia|]. split; [intros X; lia|]. split; [intros _; exists hcs'; split; [exact Hh| exact HH]|].
    split; [exact HD| exact Hd].
  Qed.

  (* [comment removed for export] *)
  #[using="rc BU SPT RSTK"] Lemma ngn_ret_1 :
    forall (ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 t3' t4' t5' t6' : word) (m5 : mem) (RNG5 : footprint) (ps : PState H hptr)
           (PB' : list (@cblock hptr)) (p' : pcap hptr hptr) (h : pkthdr) (dw : cell) (ccs : list cell),
      stk asegs m5 lo (bv_unsigned sp + -240) ->
      rw_cells asegs m5 (bv_unsigned sp + -240) (ngn_frameA ccs) -> cells_size ccs = 24%nat -> mem_inv asegs m5 ->
      ngn_final m5 RNG5 ps PB' p' (hdr_cells h) dw -> (0 <= h_caplen h < 2^32)%Z -> (0 <= h_len h < 2^32)%Z ->
      implMG RNG5 (mret (1%Z, h, p')) ps POSTQ
        (MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -240)) gp tp t0' t1' t2' x0 x3 a0' a1' a2' a3' a4' a5' a6' a7'
                 x4 x5 x2 x1 x6 x7 x8 x9 x10 x11 t3' t4' t5' t6') F (Z_to_bv 64 0x8dc5c) fc None m5 (seg_rom asegs)).
  Proof.
    intros until ccs. intros ST5 FR5 Hccs MI5 (FP5 & G5 & PC5 & AG5 & HH & Hh & HD & Hd & OF) HC HL.
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
    apply implMG_ret. hide HH. hide HD. hide FR5.
    pose proof (munch_refl ([] : list (Z * Z)) m5) as MU. pose proof (wmono_refl asegs m5) as WM.
    do 2 zstep. unhide FR5. eapply ngn_epilogue; [exact FP5 | exact ST5 | exact FR5 | exact Hccs | exact MI5 |].
    intros t0'' t1'' t2'' a1'' a2'' a3'' a4'' a5'' a6'' a7'' t3'' t4'' t5'' t6'' ST6. unhide HH. unhide HD.
    subst POSTQ. unfold next_packet_post. split; [exact FP5|]. exists (Z_to_bv 64 1), m5, PB', dw.
    split; [unfold hpost_regs; repeat (lazymatch goal with |- ex _ => eexists end); reflexivity|].
    split; [exact OF|]. split; [exact MI5|]. split; [exact ST6|]. split; [exact AG5|]. split; [exact G5|].
    split; [intros _; exact PC5|]. split; [intros X; exfalso; lia|].
    split; [reflexivity|]. split; [lia|]. split; [intros _; split; [exact HH| split; [exact HC| exact HL]]|]. split; [intros X; exfalso; lia|].
    split; [exact HD| exact Hd].
  Qed.

  (* [comment removed for export] *)
  #[using="rc tlsI FO fflagA GL sp lo LO BU ALN"] Lemma PCAPRC_errbuf : forall Lx RNGx sx CLx FLx Px (p : pcap hptr hptr) PB FBx (mx mx' : mem) (Q : Z -> Prop) cs e,
    GIOA Lx RNGx sx (CLx ++ PB) FBx FLx mx -> PCAPR_closable (hptr:=hptr) Px p PB FBx mx -> agrees_on Q mx mx' ->
    (forall a, in_block PB a -> ~ (Px + 216 <= a < Px + 472)%Z -> Q a) ->
    rw_cells asegs mx' (Px + 216) cs -> cells_size cs = 256%nat ->
    PCAPR_closable (hptr:=hptr) Px (set_errbuf e p) PB FBx mx'.
  Proof.
    intros Lx RNGx sx CLx FLx Px p PB FBx mx mx' Q cs e G PC AG HQ HCS Hsz.
    destruct PC as (Afx & Hin & (Bx & I & jx & padx & bsx & EPB & CELLS & PRIV & BUF & PFX & IFS & WF)).
    pose proof (psize_pos p) as PS. pose proof (PB_apartA _ _ _ GL _ _ _ _ _ _ _ _ _ _ _ _ G EPB) as [APB API].
    assert (Q1 : forall a, (Px <= a < Px + psize p)%Z -> ~ (Px + 216 <= a < Px + 472)%Z -> Q a).
    { intros a Ha Hn. apply HQ; [|exact Hn]. rewrite EPB. unfold pcap_blocks, in_block. apply Exists_cons_hd. cbn [cb_addr cb_size fst snd]. exact Ha. }
    apply pcap_cells_split4 in CELLS as (CA & CE & CH & CO); [|reflexivity].
    apply (rw_cells_split_CB asegs mx _ [] 304 _ [] [256; 48]%nat) in CE; [|reflexivity]. cbn [mk_CB_cells app] in CE.
    destruct (rw_cells_cut _ _ _ 1 CE) as [_ CE2]. clear CE. cbn [firstn skipn cells_size csize Nat.add] in CE2.
    replace (Px + 216 + Z.of_nat 256)%Z with (Px + 472)%Z in CE2 by lia.
    apply (agrees_rw_cells _ _ _ _ _ AG) in CA; [| intros a Ha; rewrite (pc_pre_size p Px Bx (C8 (Z_to_bv 64 Afx)) jx eq_refl) in Ha; apply Q1; lia].
    apply (agrees_rw_cells _ _ _ _ _ AG) in CH; [| intros a Ha; cbn [cells_size csize hdr_cells Nat.add] in Ha; apply Q1; lia].
    apply (agrees_rw_cells _ _ _ _ _ AG) in CO; [| intros a Ha; cbn [cells_size csize pc_ops Nat.add] in Ha; apply Q1; lia].
    apply (agrees_rw_cells _ _ _ _ _ AG) in CE2; [| intros a Ha; cbn [cells_size csize Nat.add] in Ha; apply Q1; lia].
    pose proof (rw_cells_uncut _ _ _ _ _ HCS CE2 ltac:(rewrite Hsz; lia)) as CE'.
    pose proof WF as (_ & _ & W3 & _).
    destruct (pcap_aux_closable_agree p Px Bx I padx bsx mx mx' Q AG) as (BUF' & PRIV' & IFS');
      [ intros a Ha; apply HQ; [rewrite EPB; unfold pcap_blocks, in_block; apply Exists_cons_tl, Exists_cons_hd; cbn [cb_addr cb_size fst snd]; exact Ha| lia]
      | intros a Ha; apply Q1; unfold PCAP_PRIV_OFF in Ha; lia
      | intros sg q Hq a Ha; destruct (API sg q Hq) as [X1 X2]; apply HQ;
          [rewrite EPB; unfold pcap_blocks, in_block; rewrite Hq; do 2 apply Exists_cons_tl; apply Exists_cons_hd; cbn [cb_addr cb_size fst snd]; exact Ha| lia]
      | lia | exact BUF | exact PRIV | exact IFS |].
    exists Afx. split; [destruct p; exact Hin|].
    exists Bx, I, (set_pj_g (cells_bytes (cs ++ [CB 48 (firstn 48 (skipn 256 (pj_g jx)))])) jx), padx, bsx.
    split; [rewrite EPB; destruct p; reflexivity|].
    split. { pose proof (pcap_cells_join4 mx' Px p Bx (C8 (Z_to_bv 64 Afx)) (C8 (Z_to_bv 64 (pk_stats PK))) (C8 (Z_to_bv 64 (pk_oneshot PK))) jx _ (pc_header p)
                           eq_refl CA CE' ltac:(rewrite cells_size_app, Hsz; reflexivity) CH CO) as J.
             replace (set_header (pc_header p) p) with p in J by (destruct p; reflexivity).
             destruct p; cbn. exact J. }
    split; [destruct p; exact PRIV'|]. split; [destruct p; exact BUF'|]. split; [destruct p; exact PFX|].
    split; [destruct p; exact IFS'|]. destruct p; exact WF.
  Qed.

  (* [comment removed for export] *)
  #[using="FO fflagA GL LO BU SPT RSTK RIMG RISH RTLS TPE ALN SNPRINTF HALO DALO HAP DAP"] Lemma ngn_snp_call :
    forall (RA : Z) (t0' t1' t2' x0 a3' a4' a5' a6' a7' x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 t3' t4' t5' t6' : word) (m5 : mem) (RNG5 : footprint) (ps : PState H hptr)
           (PB' : list (@cblock hptr)) (p' : pcap hptr hptr) (hcs' : list cell) (dw : cell) (ccs : list cell)
           (FMTA : Z) (fs : string) (args : list farg) (Q : machine_state -> Prop),
      stk asegs m5 lo (bv_unsigned sp + -240) ->
      rw_cells asegs m5 (bv_unsigned sp + -240) (ngn_frameA ccs) -> cells_size ccs = 24%nat -> mem_inv asegs m5 ->
      ngn_finalC m5 RNG5 ps PB' p' hcs' dw -> is_ng p' = true ->
      fmt_at m5 FMTA fs -> fmt_ok fs args = true -> (length args <= 3)%nat ->
      Forall2 (farg_word true L RNG5 FL (CLc ++ PB') (bv_unsigned sp + -240) (P + 216) 256 m5) args (firstn (length args) [a3'; a4'; a5']) ->
      (0 <= RA < 2^64)%Z -> (RA mod 2 = 0)%Z ->
      (forall (m6 : mem) (t0'' t1'' t2'' a0'' a1'' a2'' a3'' a4'' a5'' a6'' a7'' t3'' t4'' t5'' t6'' : word),
          stk asegs m6 lo (bv_unsigned sp + -240) -> rw_cells asegs m6 (bv_unsigned sp + -240) (ngn_frameA ccs) -> mem_inv asegs m6 ->
          (forall e, ngn_finalC m6 RNG5 ps PB' (set_errbuf e p') hcs' dw) ->
          evtF asegs RNG5 Q (MS (mkR (Z_to_bv 64 RA) (Z_to_bv 64 (bv_unsigned sp + -240)) gp tp t0'' t1'' t2'' x0 x3 a0'' a1'' a2'' a3'' a4'' a5'' a6'' a7''
                           x4 x5 x2 x1 x6 x7 x8 x9 x10 x11 t3'' t4'' t5'' t6'') F (Z_to_bv 64 RA) fc None m6 (seg_rom asegs))) ->
      evtF asegs RNG5 Q
        (MS (mkR (Z_to_bv 64 RA) (Z_to_bv 64 (bv_unsigned sp + -240)) gp tp t0' t1' t2' x0 x3
                 (Z_to_bv 64 (P + 216)) (Z_to_bv 64 256) (Z_to_bv 64 FMTA) a3' a4' a5' a6' a7'
                 x4 x5 x2 x1 x6 x7 x8 x9 x10 x11 t3' t4' t5' t6') F (Z_to_bv 64 SNPRINTF_ENTRY) fc None m5 (seg_rom asegs)).
  Proof.
    intros until Q. intros ST5 FR5 Hccs MI5 (FP5 & G5 & PC5 & AG5 & HH & Hh & HD & Hd & OF5) NG5 FMT5 FOK LA FW RA64 RAE HK.
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
    pose proof PC5 as (Afx & _ & (Bx & Ix & jx & padx & bsx & EPB & CELLS & _ & _ & _ & _ & WF)).
    assert (PS : psize p' = 680%Z) by (unfold psize; rewrite NG5; reflexivity).
    assert (HinP : In (pc_self p', P, psize p') ((CLc ++ PB') ++ FB)) by (apply in_or_app; left; apply in_or_app; right; rewrite EPB; left; reflexivity).
    pose proof (gl_block _ _ _ GL _ _ _ _ _ _ _ _ G5 HinP) as PBLK. pose proof PBLK as ((PBAND & P3 & PTOP & P2) & P1 & _).
    cbn [cb_addr cb_size fst snd] in PBAND, P3, PTOP, P2, P1. rewrite PS in *.
    apply pcap_cells_split4 in CELLS as (_ & CE & _ & _); [|reflexivity].
    apply (rw_cells_split_CB asegs m5 _ [] 304 _ [] [256; 48]%nat) in CE; [|reflexivity]. cbn [mk_CB_cells app] in CE.
    destruct (rw_cells_cut _ _ _ 1 CE) as [CE1 _]. clear CE. cbn [firstn skipn cells_size csize Nat.add] in CE1.
    pose proof (rng_fp_le _ _ _ _ FP5 RSTK) as RSTK5. pose proof (rng_fp_le _ _ _ _ FP5 RIMG) as RIMG5.
    pose proof (rng_fp_le _ _ _ _ FP5 RISH) as RISH5. pose proof (rng_fp_le _ _ _ _ FP5 RTLS) as RTLS5.
    name_sp sp (-240)%Z.
    eapply evtF_cut.
    { eapply SNPRINTF with (L := L) (s := ps) (CL := CLc ++ PB') (FB := FB) (FL := FL) (lo := lo) (DST := (P + 216)%Z) (n := 256%Z) (FMTA := FMTA) (fs := fs) (args := args)
                           (junk := firstn 256 (pj_g jx));
        [ split; [exact G5|]; split; [rewrite Hsp; exact ST5|]; split; [lia|]; split; [unfold STDIO_STACK; rewrite Hsp; lia|];
          split; [rewrite Hsp; lia|]; split; [exact MI5|]; split; [exact TPE|]; split; [rewrite Hsp; apply aln16_add; [exact ALN| reflexivity]|];
          split; [exact RSTK5|]; split; [exact RIMG5|]; split; [exact RISH5| exact RTLS5]
        | reflexivity | reflexivity | reflexivity | lia | exact FMT5 | exact FOK | exact LA | rewrite Hsp; exact FW | exact CE1
        | split; [left; exists (pc_self p', P, psize p'); split; [apply in_or_app; right; rewrite EPB; left; reflexivity| cbn [cb_addr cb_size fst snd]; lia]
                 | eapply blockA_aobj; [exact PBLK | cbn [cb_addr cb_size fst snd]; lia | cbn [cb_addr cb_size fst snd]; lia | lia]] ]. }
    cbv beta. intros ms' PO. destruct PO as (av & m6 & junk6 & E & MU6 & WM6 & MI6 & ST6 & -> & HEB6).
    unfold hpost_regs in E. destruct_exs E. subst ms'. rewrite Hsp in *. unname_sp.
    replace (ret_pc (Z_to_bv 64 RA)) with (Z_to_bv 64 RA) by (symmetry; apply ret_pc_even; [exact RA64| exact RAE]).
    unfold STDIO_STACK in MU6.
    assert (AGS : agrees_on (fun a => outside [(bv_unsigned sp + -240 - 16384, bv_unsigned sp + -240); (P + 216, P + 216 + 256)]%Z a) m5 m6)
      by (eapply agrees_on_of_munch; [exact MU6 | exact WM6 | intros a _ Ho; exact Ho]).
    apply (agrees_rw_cells _ _ _ _ _ AGS) in FR5; [| intros a Ha; unfold ngn_frameA in Ha; rewrite !cells_size_app in Ha; cbn [outside fst snd cells_size csize Nat.add] in *; rewrite Hccs in Ha; lia].
    apply (agrees_rw_cells _ _ _ _ _ AGS) in HH; [| intros a Ha; rewrite Hh in Ha; cbn [outside fst snd]; lia].
    apply (agrees_rw_cells _ _ _ _ _ AGS) in HD; [| intros a Ha; cbn [cells_size] in Ha; rewrite Hd in Ha; cbn [outside fst snd]; lia].
    assert (FW6 : Forall (pcap_iv FL PB') [(bv_unsigned sp + -240 - 16384, bv_unsigned sp + -240); (P + 216, P + 216 + 256)]%Z).
    { apply Forall_cons; [left; cbn [fst snd]; lia|]. apply Forall_cons; [|apply Forall_nil].
      right; left. rewrite EPB. unfold iv_in_block, pcap_blocks. apply Exists_cons_hd. cbn [cb_addr cb_size fst snd]. lia. }
    assert (G6 : GIOA L RNG5 ps (CLc ++ PB') FB FL m6) by (eapply (gl_frame _ _ _ GL); [exact G5 | exact MU6 | exact WM6 | exact FW6]).
    assert (PC6 : forall e, PCAPR_closable (hptr:=hptr) P (set_errbuf e p') PB' FB m6).
    { intros e. eapply (PCAPRC_errbuf _ _ _ _ _ _ _ _ _ _ _ _ _ _ G5 PC5 AGS); [| exact HEB6 | pose proof (snprintf_length_le 256 fs args ltac:(lia)); cbn [cells_size csize Nat.add]; lia].
      intros a Ha Hn. cbn [outside fst snd]. pose proof (gia_in_block_below _ _ _ GL _ _ _ _ _ _ _ a G5 ltac:(apply in_block_app; left; apply in_block_app; right; exact Ha)). lia. }
    assert (AG6 : agrees_on (fun a => client_keeps FL CLc (bv_unsigned sp) a /\ ~ (HA <= a < HA + 24) /\ ~ (DA <= a < DA + 8))%Z m m6).
    { eapply agrees_on_trans; [exact AG5|]. eapply agrees_on_weaken; [| intros a [K _]; exact K].
      eapply (gl_keeps _ _ _ GL _ _ _ _ _ _ FL []); [exact G5 | exact MU6 | exact WM6 | | lia].
      apply Forall_cons; [left; cbn [fst snd]; lia|]. apply Forall_cons; [|apply Forall_nil].
      right; left. rewrite EPB. unfold iv_in_block, pcap_blocks. apply Exists_cons_hd. cbn [cb_addr cb_size fst snd]. lia. }
    apply HK; [exact ST6 | exact FR5 | exact MI6 |].
    intros e. split; [exact FP5|]. split; [exact G6|]. split; [exact (PC6 e)|]. split; [exact AG6|]. split; [exact HH|]. split; [exact Hh|]. split; [exact HD|]. split; [exact Hd| exact OF5].
  Qed.

  (* [comment removed for export] *)
  #[using="FO fflagA GL LO BU SPT RSTK RIMG RISH RTLS TPE ALN SNPRINTF HALO DALO HAP DAP"] Lemma ngn_snp :
    forall (t0' t1' t2' a3' a4' a5' a6' a7' x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 t3' t4' t5' t6' : word) (m5 : mem) (RNG5 : footprint) (ps : PState H hptr)
           (PB' : list (@cblock hptr)) (p' : pcap hptr hptr) (h : pkthdr) (hcs' : list cell) (dw : cell) (ccs : list cell)
           (FMTA : Z) (fs : string) (args : list farg) (e : list Z),
      stk asegs m5 lo (bv_unsigned sp + -240) ->
      rw_cells asegs m5 (bv_unsigned sp + -240) (ngn_frameA ccs) -> cells_size ccs = 24%nat -> mem_inv asegs m5 ->
      ngn_finalC m5 RNG5 ps PB' p' hcs' dw -> is_ng p' = true ->
      fmt_at m5 FMTA fs -> fmt_ok fs args = true -> (length args <= 3)%nat ->
      Forall2 (farg_word true L RNG5 FL (CLc ++ PB') (bv_unsigned sp + -240) (P + 216) 256 m5) args (firstn (length args) [a3'; a4'; a5']) ->
      implMG RNG5 (mret ((-1)%Z, h, set_errbuf e p')) ps POSTQ
        (MS (mkR (Z_to_bv 64 NGN_EPILOGUE_A) (Z_to_bv 64 (bv_unsigned sp + -240)) gp tp t0' t1' t2' (Z_to_bv 64 (-1)) x3
                 (Z_to_bv 64 (P + 216)) (Z_to_bv 64 256) (Z_to_bv 64 FMTA) a3' a4' a5' a6' a7'
                 x4 x5 x2 x1 x6 x7 x8 x9 x10 x11 t3' t4' t5' t6') F (Z_to_bv 64 SNPRINTF_ENTRY) fc None m5 (seg_rom asegs)).
  Proof.
    intros until e. intros ST5 FR5 Hccs MI5 FIN NG5 FMT5 FOK LA FW.
    ienterG. unfold NGN_EPILOGUE_A.
    eapply ngn_snp_call; [exact ST5 | exact FR5 | exact Hccs | exact MI5 | exact FIN | exact NG5 | exact FMT5 | exact FOK | exact LA | exact FW | lia | reflexivity |].
    intros m6 t0'' t1'' t2'' a0'' a1'' a2'' a3'' a4'' a5'' a6'' a7'' t3'' t4'' t5'' t6'' ST6 FR6 MI6 FIN6.
    apply evtF_done. eapply ngn_ret_m1; [exact ST6 | exact FR6 | exact Hccs | exact MI6 | exact (FIN6 e)].
  Qed.

  (* [comment removed for export] *)
  #[using="rc tlsI FO fflagA GL LO BU SPT RSTK RIMG RISH ALN HALO DALO HAP DAP"] Lemma ngn_mcp :
    forall (ra' t0' t1' t2' a0' a3' a4' a5' a6' a7' x1 x2 x4 x5 x6 x7 x8 x9 x10 x11 t3' t4' t5' t6' : word) (m5 : mem) (RNG5 : footprint) (ps : PState H hptr)
           (PB' : list (@cblock hptr)) (p' : pcap hptr hptr) (h : pkthdr) (hcs' : list cell) (dw : cell) (ccs : list cell)
           (STR n : Z) (src : list byte) (e : list Z),
      stk asegs m5 lo (bv_unsigned sp + -240) ->
      rw_cells asegs m5 (bv_unsigned sp + -240) (ngn_frameA ccs) -> cells_size ccs = 24%nat -> mem_inv asegs m5 ->
      ngn_finalC m5 RNG5 ps PB' p' hcs' dw -> is_ng p' = true ->
      bytes_at asegs m5 STR src -> length src = Z.to_nat n -> (0 <= n <= 256)%Z -> In (STR, n) client_globals -> (STR + n <= 0x32000)%Z ->
      implMG RNG5 (mret ((-1)%Z, h, set_errbuf e p')) ps POSTQ
        (MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -240)) gp tp t0' t1' t2' (Z_to_bv 64 (-1)) (Z_to_bv 64 (P + 216))
                 a0' (Z_to_bv 64 STR) (Z_to_bv 64 n) a3' a4' a5' a6' a7'
                 x4 x5 x2 x1 x6 x7 x8 x9 x10 x11 t3' t4' t5' t6') F (Z_to_bv 64 0x8d2a8) fc None m5 (seg_rom asegs)).
  Proof.
    intros until e. intros ST5 FR5 Hccs MI5 (FP5 & G5 & PC5 & AG5 & HH & Hh & HD & Hd & OF5) NG5 SRC LEN Hn HG HSTR.
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
    pose proof PC5 as (Afx & _ & (Bx & Ix & jx & padx & bsx & EPB & CELLS & _ & _ & _ & _ & WF)).
    assert (PS : psize p' = 680%Z) by (unfold psize; rewrite NG5; reflexivity).
    assert (HinP : In (pc_self p', P, psize p') ((CLc ++ PB') ++ FB)) by (apply in_or_app; left; apply in_or_app; right; rewrite EPB; left; reflexivity).
    pose proof (gl_block _ _ _ GL _ _ _ _ _ _ _ _ G5 HinP) as PBLK. pose proof PBLK as ((PBAND & P3 & PTOP & P2) & P1 & _).
    cbn [cb_addr cb_size fst snd] in PBAND, P3, PTOP, P2, P1. rewrite PS in *.
    pose proof (gl_rt _ _ _ GL _ _ _ _ _ _ _ G5) as (RT5 & _).
    pose proof (ablk_lin _ _ PBAND) as (PIMG & _ & PATOP & _). unfold AIMG_HI in PIMG.
    pose proof (rng_fp_le _ _ _ _ FP5 RSTK) as RSTK5. pose proof (rng_fp_le _ _ _ _ FP5 RIMG) as RIMG5. pose proof (rng_fp_le _ _ _ _ FP5 RISH) as RISH5.
    assert (RSPW : rng RNG5 lo (bv_unsigned sp + -240 - lo)) by (eapply rng_sub'; [exact RSTK5| lia]).
    assert (RSPX : rng RNG5 lo (bv_unsigned sp - lo)) by (eapply rng_sub'; [exact RSTK5| lia]).
    pose proof (gia_global_mobjA _ _ _ GL _ _ _ _ _ _ _ _ _ G5 HG RIMG5 RISH5) as OSRC.
    apply pcap_cells_split4 in CELLS as (_ & CE & _ & _); [|reflexivity].
    apply (rw_cells_split_CB asegs m5 _ [] 304 _ [] [Z.to_nat n; 256 - Z.to_nat n; 48]%nat) in CE; [|cbn; lia]. cbn [mk_CB_cells app] in CE.
    destruct (rw_cells_cut _ _ _ 1 CE) as [CE1 CE23]. clear CE. cbn [firstn skipn cells_size csize Nat.add] in CE1, CE23.
    destruct (rw_cells_cut _ _ _ 1 CE23) as [CE2 _]. clear CE23. cbn [firstn skipn cells_size csize Nat.add] in CE2.
    ienterG. hide FR5. hide HH. hide HD. hide CE2.
    pose proof (munch_refl [(bv_unsigned sp + -240 - 2224, bv_unsigned sp + -240); (P + 216, P + 216 + n)]%Z m5) as MU. pose proof (wmono_refl asegs m5) as WM.
    zstep. zstep.
    name_sp sp (-240)%Z.
    eapply evtF_cut.
    { eapply (asan_memcpy_specZ RNG5 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m5 lo (P + 216)%Z STR n src (firstn (Z.to_nat n) (pj_g jx)));
        [ reflexivity | reflexivity | reflexivity | exact MI5 | rewrite Hsp; exact ST5 | rewrite Hsp; lia | lia | exact RT5 | exact SRC | exact LEN | lia | exact CE1
        | left; lia | exact OSRC
        | apply aobjA_mobjA; [eapply blockA_aobj; [exact PBLK | cbn [cb_addr cb_size fst snd]; lia | cbn [cb_addr cb_size fst snd]; lia | lia] | lia]
        | lia | lia | exact RIMG5 | rewrite Hsp; exact RSPW ]. }
    cbv beta. intros ms' PO. destruct PO as (y0 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & y8 & y9 & y10 & y11 & y12 & y13 & m6 & -> & MU6 & WM6 & MI6 & ST6 & HEB6 & _).
    rewrite Hsp in *. unname_sp.
    replace (ret_pc (Z_to_bv 64 578224)) with (Z_to_bv 64 578224) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
    unhide FR5. unhide HH. unhide HD. unhide CE2.
    assert (AGS : agrees_on (fun a => outside [(bv_unsigned sp + -240 - 2224, bv_unsigned sp + -240); (P + 216, P + 216 + n)]%Z a) m5 m6)
      by (eapply agrees_on_of_munch; [exact MU6 | exact WM6 | intros a _ Ho; exact Ho]).
    apply (agrees_rw_cells _ _ _ _ _ AGS) in FR5; [| intros a Ha; unfold ngn_frameA in Ha; rewrite !cells_size_app in Ha; cbn [outside fst snd cells_size csize Nat.add] in *; rewrite Hccs in Ha; lia].
    apply (agrees_rw_cells _ _ _ _ _ AGS) in HH; [| intros a Ha; rewrite Hh in Ha; cbn [outside fst snd]; lia].
    apply (agrees_rw_cells _ _ _ _ _ AGS) in HD; [| intros a Ha; cbn [cells_size] in Ha; rewrite Hd in Ha; cbn [outside fst snd]; lia].
    apply (agrees_rw_cells _ _ _ _ _ AGS) in CE2; [| intros a Ha; cbn [outside fst snd cells_size csize Nat.add] in *; lia].
    pose proof (rw_cells_uncut _ _ _ _ _ HEB6 CE2 ltac:(cbn [cells_size csize Nat.add]; lia)) as HEB. cbn [app] in HEB.
    assert (FW6 : Forall (pcap_iv FL PB') [(bv_unsigned sp + -240 - 2224, bv_unsigned sp + -240); (P + 216, P + 216 + n)]%Z).
    { apply Forall_cons; [left; cbn [fst snd]; lia|]. apply Forall_cons; [|apply Forall_nil].
      right; left. rewrite EPB. unfold iv_in_block, pcap_blocks. apply Exists_cons_hd. cbn [cb_addr cb_size fst snd]. lia. }
    assert (G6 : GIOA L RNG5 ps (CLc ++ PB') FB FL m6) by (eapply (gl_frame _ _ _ GL); [exact G5 | exact MU6 | exact WM6 | exact FW6]).
    assert (PC6 : PCAPR_closable (hptr:=hptr) P (set_errbuf e p') PB' FB m6).
    { eapply (PCAPRC_errbuf _ _ _ _ _ _ _ _ _ _ _ _ _ _ G5 PC5 AGS); [| exact HEB | cbn [cells_size csize Nat.add]; lia].
      intros a Ha Hna. cbn [outside fst snd]. pose proof (gia_in_block_below _ _ _ GL _ _ _ _ _ _ _ a G5 ltac:(apply in_block_app; left; apply in_block_app; right; exact Ha)). lia. }
    assert (AG6 : agrees_on (fun a => client_keeps FL CLc (bv_unsigned sp) a /\ ~ (HA <= a < HA + 24) /\ ~ (DA <= a < DA + 8))%Z m m6).
    { eapply agrees_on_trans; [exact AG5|]. eapply agrees_on_weaken; [| intros a [K _]; exact K].
      eapply (gl_keeps _ _ _ GL _ _ _ _ _ _ FL []); [exact G5 | exact MU6 | exact WM6 | | lia].
      apply Forall_cons; [left; cbn [fst snd]; lia|]. apply Forall_cons; [|apply Forall_nil].
      right; left. rewrite EPB. unfold iv_in_block, pcap_blocks. apply Exists_cons_hd. cbn [cb_addr cb_size fst snd]. lia. }
    clear MU WM. pose proof (munch_refl ([] : list (Z * Z)) m6) as MU. pose proof (wmono_refl asegs m6) as WM.
    hide FR5. hide HH. hide HD. hide HEB.
    zstep. unhide FR5. unhide HH. unhide HD.
    apply evtF_done. eapply ngn_ret_m1; [exact ST6 | exact FR5 | exact Hccs | exact MI6 |].
    split; [exact FP5|]. split; [exact G6|]. split; [exact PC6|]. split; [exact AG6|]. split; [exact HH|]. split; [exact Hh|]. split; [exact HD|]. split; [exact Hd| exact OF5].
  Qed.
End NgnCtx.
End CANSEC1.
End TwB.
End F_ngnAA.
