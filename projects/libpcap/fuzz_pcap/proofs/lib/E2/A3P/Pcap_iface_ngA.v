(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool String.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Sem.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import Tac Arr Bytes ITree Nodes Decode SysStep.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Import Prelim Monad Fmt StdioCore Stdio PcapPrelim PcapTypes PcapPure Pcap Prog.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import ExecF ITreeA Shadow RunDraw.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require Import AImg ABase AMalloc_iface.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require MonadG GIA PcapRepA UnwKit. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require MonadGX__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require Pcap_ifaceA. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadG OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.GIA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.PcapRepA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.UnwKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadGX__A3P.TracesA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.Pcap_ifaceA.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

(* [comment removed for export] *)
Definition READ_BYTES_STACK : Z := PCAP_L1_STACK + 64.
Definition READ_BLOCK_STACK : Z := PCAP_L1_STACK + 96 + 4096.
Definition ADD_INTERFACE_STACK : Z := STDIO_STACK + 128.

Section NgIface.
  Context {rc : runConstT} {tlsI : ABase.atlsT}.
  Context {H hptr : Type} (HO : HeapOps H hptr) (FO : @FrameOps H hptr) (sites : stack_site -> Z).
  Variable GIOA : alayout -> footprint -> PState H hptr -> list (@cblock hptr) -> list (@cblock hptr) -> list fblock -> mem -> Prop.
  Variable TP : tparams.
  #[local] Abbreviation cblk := (@cblock hptr).
  #[local] Abbreviation PS := (PState H hptr).
  #[local] Abbreviation pcapT := (PcapTypes.pcap hptr hptr).
  #[local] Abbreviation PR := (prims HO FO sites).
  #[local] Abbreviation GIO := GIOA.
  #[local] Abbreviation SPOA := (std_pre_o GIOA).

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition read_bytes_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (L : alayout) (RNG : footprint) (FL : list fblock) (CL FB : list cblk) (lo D n EB : Z) (foe : bool) (ej : list byte) (m : mem) (o : option hptr) : (rb_status * list Z) -> PS -> footprint -> machine_state -> Prop :=
    fun r s' RNG' ms' => fp_le RNG RNG' /\ let '(st, got) := r in exists a0v m' junk',
      hpost_regs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0v m' ms'
      /\ ps_outfile s' = o /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp)
      /\ agrees_on (fun a => client_keeps FL CL (bv_unsigned sp) a /\ ~ (D <= a < D + n) /\ ~ (EB <= a < EB + 256)) m m'
      /\ GIO L RNG' s' CL FB FL m'
      /\ rw_cells asegs m' D [CB (length got) (map b8 got); CB (Z.to_nat n - length got) junk']
      /\ Forall (fun z => 0 <= z < 256) got /\ 0 <= zlength got <= n
      /\ match st with
         | RBS_Ok => a0v = Z_to_bv 64 1 /\ zlength got = n /\ rw_cells asegs m' EB [CB 256 ej]
         | RBS_Eof => a0v = Z_to_bv 64 0 /\ zlength got = 0 /\ foe = false /\ rw_cells asegs m' EB [CB 256 ej]
         | RBS_Err msg => exists junk'', a0v = Z_to_bv 64 (-1)
             /\ rw_cells asegs m' EB [CB (length msg + 1) (map b8 msg ++ [Z_to_bv 8 0]); CB (255 - length msg) junk''] /\ Z.of_nat (length msg) < 256
             /\ Forall (fun z => 0 < z < 256) msg
         end.

  Definition read_bytes_stmt : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (L : alayout) (RNG : footprint) (s : PS) (CL FB : list cblk) (FL : list fblock) (trC : list Z) (f : hptr) (Af D n EB lo : Z)
           (foe : bool) (dest : rdest hptr) (junk ej : list byte),
      SPOA L RNG sp tp s CL FB FL lo READ_BYTES_STACK m ->
      ucallerA depth_read_bytes L m sp s0 ra trC -> traces_read_bytes TP L (bv_unsigned ra) trC -> nofr frames_read_bytes FL -> In (f, Af, FILE_BLOCK) FB ->
      eval_rdest HO FO sites s dest = D ->
      a0 = Z_to_bv 64 Af -> a1 = Z_to_bv 64 D -> a2 = Z_to_bv 64 n -> a3 = Z_to_bv 64 (Z.b2z foe) -> a4 = Z_to_bv 64 EB ->
      0 <= n <= 2^30 ->
      rw_cells asegs m D [CB (Z.to_nat n) junk] -> cobjA RNG m FL CL D n ->
      rw_cells asegs m EB [CB 256 ej] -> cobjA RNG m FL CL EB 256 -> (D + n <= EB \/ EB + 256 <= D) ->
      EB mod 8 = 0 ->
      implMG RNG (read_bytes MOps (prims HO FO sites) f dest n foe) s
        (read_bytes_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG FL CL FB lo D n EB foe ej m (ps_outfile s))
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 READ_BYTES_ENTRY) fc None m (seg_rom asegs)).


  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition blk_handle (p : pcapT) (s : pcap_ng_sf) (P B : Z) (m : mem) : Prop :=
    rw_cells asegs m (P + 20) [C4 (Z_to_bv 64 (pc_bufsize p)); C8 (Z_to_bv 64 B)]
    /\ rw_cells asegs m (P + 48) [C8 (Z_to_bv 64 (P + PCAP_PRIV_OFF)); C4 (Z_to_bv 64 (Z.b2z (pc_swapped p)))]
    /\ rw_cells asegs m (P + 656) [C4 (Z_to_bv 64 (ng_max_blocksize s))]
    /\ 0 <= pc_bufsize p <= 2^30 /\ 0 <= ng_max_blocksize s <= 2^28 /\ 1 <= pc_bufalloc p < 2^32 /\ pc_bufsize p <= pc_bufalloc p.

  (* [comment removed for export] *)
  Definition same_meta (p' p : pcapT) : Prop :=
    pc_version_major p' = pc_version_major p /\ pc_version_minor p' = pc_version_minor p /\ pc_snapshot p' = pc_snapshot p
    /\ pc_linktype p' = pc_linktype p /\ pc_linktype_ext p' = pc_linktype_ext p /\ pc_tstamp_precision p' = pc_tstamp_precision p
    /\ pc_break_loop p' = pc_break_loop p /\ pc_errbuf p' = pc_errbuf p /\ pc_header p' = pc_header p.

  Definition read_block_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (L : alayout) (RNG : footprint) (FL : list fblock) (C1 C2 FB : list cblk) (lo P CUR EB : Z) (p : pcapT) (s : pcap_ng_sf) (ej : list byte) (m : mem) (o : option hptr)
      : block_result -> PS -> footprint -> machine_state -> Prop :=
    fun r s' RNG' ms' => fp_le RNG RNG' /\ exists a0v m' (p' : pcapT) B' bs',
      hpost_regs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0v m' ms'
      /\ ps_outfile s' = o /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp)
      /\ agrees_on (fun a => client_keeps FL (C1 ++ C2) (bv_unsigned sp) a /\ ~ (P + 24 <= a < P + 32)
                             /\ ~ (CUR <= a < CUR + 24) /\ ~ (EB <= a < EB + 256)) m m'
      /\ GIO L RNG' s' ((pc_buffer p', B', pc_bufalloc p') :: C1 ++ C2) FB FL m'
      /\ blk_handle p' s P B' m'
      /\ rw_cells asegs m' B' [CB (Z.to_nat (pc_bufalloc p')) bs'] /\ firstn (length (pc_bufdata p')) bs' = map b8 (pc_bufdata p')
      /\ Z.of_nat (length (pc_bufdata p')) <= pc_bufalloc p'
      /\ pc_priv p' = pc_priv p /\ pc_rfile p' = pc_rfile p /\ pc_self p' = pc_self p /\ pc_bufsize p' = pc_bufsize p /\ pc_swapped p' = pc_swapped p
      /\ same_meta p' p
      /\ match r with
         | RB_Ok c p'' => p'' = p' /\ a0v = Z_to_bv 64 1 /\ rw_cells asegs m' EB [CB 256 ej]
             /\ (exists cpad, rw_cells asegs m' CUR [C8 (Z_to_bv 64 (B' + 8)); C8 (Z_to_bv 64 (cur_remaining c)); C4 (Z_to_bv 64 (cur_block_type c)); CB 4 cpad])
             /\ cur_off c = 8 /\ 0 <= cur_remaining c /\ cur_remaining c + 12 <= pc_bufalloc p' /\ cur_remaining c + 12 <= 2^30 /\ 0 <= cur_block_type c < 2^32
             /\ Z.of_nat (length (pc_bufdata p')) = cur_remaining c + 12 /\ Forall (fun z => 0 <= z < 256) (pc_bufdata p')
         | RB_Eof p'' => p'' = p' /\ a0v = Z_to_bv 64 0 /\ rw_cells asegs m' EB [CB 256 ej]
             /\ (exists ccs', rw_cells asegs m' CUR ccs' /\ cells_size ccs' = 24%nat)
         | RB_Err msg p'' => p'' = p' /\ a0v = Z_to_bv 64 (-1)
             /\ (exists junk'', rw_cells asegs m' EB [CB (length msg + 1) (map b8 msg ++ [Z_to_bv 8 0]); CB (255 - length msg) junk''])
             /\ Z.of_nat (length msg) < 256 /\ Forall (fun z => 0 < z < 256) msg
             /\ (exists ccs', rw_cells asegs m' CUR ccs' /\ cells_size ccs' = 24%nat)
         end.

  Definition read_block_stmt : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (L : alayout) (RNG : footprint) (st : PS) (C1 C2 FB : list cblk) (FL : list fblock) (trC : list Z) (f : hptr) (Af P B CUR EB lo : Z)
           (p : pcapT) (s : pcap_ng_sf) (i : option hptr) (a_bhdr : rdest hptr) (bs ej : list byte) (ccs : list cell),
      SPOA L RNG sp tp st (C1 ++ (pc_buffer p, B, pc_bufalloc p) :: C2) FB FL lo READ_BLOCK_STACK m ->
      ucallerA depth_read_block L m sp s0 ra trC -> traces_read_block TP L (bv_unsigned ra) trC -> nofr frames_read_block FL ->
      In (f, Af, FILE_BLOCK) FB -> pc_rfile p = f -> pc_priv p = PrivNg s i ->
      In (pc_self p, P, PCAP_NG_SF_TOTAL) (C1 ++ C2) ->
      (exists site, a_bhdr = DStack site 0 /\ site_frameA site = Some (FF_READ_BLOCK, 32)) ->   (* [comment removed for export] *)
      a0 = Z_to_bv 64 Af -> a1 = Z_to_bv 64 P -> a2 = Z_to_bv 64 CUR -> a3 = Z_to_bv 64 EB ->
      blk_handle p s P B m -> rw_cells asegs m B [CB (Z.to_nat (pc_bufalloc p)) bs] ->
      firstn (length (pc_bufdata p)) bs = map b8 (pc_bufdata p) -> Z.of_nat (length (pc_bufdata p)) <= pc_bufalloc p ->
      rw_cells asegs m CUR ccs -> cells_size ccs = 24%nat -> (bv_unsigned sp <= CUR /\ CUR + 24 <= al_top L) -> CUR mod 8 = 0 ->
      rw_cells asegs m EB [CB 256 ej] ->
      ((cobjA RNG m FL (C1 ++ C2) EB 256 /\ (EB + 256 <= CUR \/ CUR + 24 <= EB) /\ (EB + 256 <= P \/ P + PCAP_NG_SF_TOTAL <= EB) /\ (EB + 256 <= B \/ B + pc_bufalloc p <= EB)) \/ (P + 216 = EB)) ->   (* [comment removed for export] *)
      EB mod 8 = 0 ->
      implMG RNG (read_block MOps (prims HO FO sites) a_bhdr p) st
        (read_block_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG FL C1 C2 FB lo P CUR EB p s ej m (ps_outfile st))
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 READ_BLOCK_ENTRY) fc None m (seg_rom asegs)).


  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition IBLK (i : option hptr) (I : Z) (s : pcap_ng_sf) : list cblk :=
    match i with Some q => [(q, I, 40 * ng_ifaces_size s)] | None => [] end.
  (* [comment removed for export] *)
  Definition cursor_cells (B : Z) (c : cursor) (cpad : list byte) : list cell :=
    [C8 (Z_to_bv 64 (B + cur_off c)); C8 (Z_to_bv 64 (cur_remaining c)); C4 (Z_to_bv 64 (cur_block_type c)); CB 4 cpad].

  (* [comment removed for export] *)
  Definition ng_ifaces_closable (s : pcap_ng_sf) (i : option hptr) (I : Z) (m : mem) : Prop :=
    match i with
    | None => I = 0
    | Some q => (exists junk, rw_cells asegs m I [CB (Z.to_nat (40 * ng_ifaces_size s)) junk]) /\ 1 <= ng_ifaces_size s < 2^26
    end.

  Definition add_interface_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (L : alayout) (RNG : footprint) (FL : list fblock) (C1 C2 FB : list cblk) (lo P B CUR EB : Z) (p : pcapT) (s : pcap_ng_sf) (c : cursor) (bs ej : list byte) (m : mem) (o : option hptr)
      : (bool * cursor * pcapT * list Z) -> PS -> footprint -> machine_state -> Prop :=
    fun r st' RNG' ms' => fp_le RNG RNG' /\ let '(ok, c', p', msg) := r in
      exists a0v m' (s' : pcap_ng_sf) (i' : option hptr) (I' : Z) (pad' : list byte) (bs' : list byte),
      hpost_regs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0v m' ms'
      /\ ps_outfile st' = o /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp)
      /\ agrees_on (fun a => client_keeps FL (C1 ++ C2) (bv_unsigned sp) a /\ ~ (P + PCAP_PRIV_OFF <= a < P + PCAP_NG_SF_TOTAL)
                             /\ ~ (CUR <= a < CUR + 24) /\ ~ (EB <= a < EB + 256) /\ ~ (B <= a < B + pc_bufalloc p)) m m'
      /\ p' = set_ng s' i' (set_bufdata (pc_bufdata p') p)
      /\ GIO L RNG' st' (IBLK i' I' s' ++ C1 ++ C2) FB FL m'
      /\ rw_cells asegs m' (P + PCAP_PRIV_OFF) (ng_cells s' I' pad')
      /\ ng_user_tsresol s' = ng_user_tsresol s /\ ng_max_blocksize s' = ng_max_blocksize s /\ 0 <= ng_ifcount s' < 2^32 /\ 0 <= ng_ifaces_size s' < 2^32
      /\ rw_cells asegs m' B [CB (Z.to_nat (pc_bufalloc p)) bs'] /\ firstn (length (pc_bufdata p')) bs' = map b8 (pc_bufdata p')
      /\ length (pc_bufdata p') = length (pc_bufdata p) /\ Forall (fun z => 0 <= z < 256) (pc_bufdata p')
      /\ a0v = Z_to_bv 64 (Z.b2z ok)
      /\ if ok then
           ifaces_ok p' I' m'
           /\ (exists cpad', rw_cells asegs m' CUR (cursor_cells B c' cpad'))
           /\ 0 <= cur_remaining c' /\ cur_off c <= cur_off c' /\ cur_off c' + cur_remaining c' <= cur_off c + cur_remaining c
           /\ cur_block_type c' = cur_block_type c
           /\ rw_cells asegs m' EB [CB 256 ej] /\ msg = []
         else
           ng_ifaces_closable s' i' I' m'
           /\ (exists ccs', rw_cells asegs m' CUR ccs' /\ cells_size ccs' = 24%nat)
           /\ (exists junk'', rw_cells asegs m' EB [CB (length msg + 1) (map b8 msg ++ [Z_to_bv 8 0]); CB (255 - length msg) junk''])
           /\ Z.of_nat (length msg) < 256 /\ Forall (fun z => 0 < z < 256) msg.

  (* [comment removed for export] *)
  Definition add_interface_stmt : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (L : alayout) (RNG : footprint) (st : PS) (C1 C2 FB : list cblk) (FL : list fblock) (trC : list Z) (P B I CUR EB lo idb_off : Z)
           (p : pcapT) (s : pcap_ng_sf) (i : option hptr) (c : cursor) (bs ej pad cpad : list byte),
      SPOA L RNG sp tp st (C1 ++ IBLK i I s ++ C2) FB FL lo ADD_INTERFACE_STACK m ->
      ucallerA depth_add_interface L m sp s0 ra trC -> traces_add_interface TP L (bv_unsigned ra) trC -> nofr frames_add_interface FL ->
      pc_priv p = PrivNg s i ->
      In (pc_self p, P, PCAP_NG_SF_TOTAL) (C1 ++ C2) -> In (pc_buffer p, B, pc_bufalloc p) (C1 ++ C2) ->
      P + PCAP_NG_SF_TOTAL <= B \/ B + pc_bufalloc p <= P ->
      a0 = Z_to_bv 64 P -> a1 = Z_to_bv 64 (B + idb_off) -> a2 = Z_to_bv 64 CUR -> a3 = Z_to_bv 64 EB ->
      rw_cells asegs m (P + 48) [C8 (Z_to_bv 64 (P + PCAP_PRIV_OFF)); C4 (Z_to_bv 64 (Z.b2z (pc_swapped p)))] ->
      rw_cells asegs m (P + PCAP_PRIV_OFF) (ng_cells s I pad) -> ifaces_ok p I m ->
      0 < ng_user_tsresol s < 2^64 -> 0 <= ng_max_blocksize s < 2^32 ->
      rw_cells asegs m B [CB (Z.to_nat (pc_bufalloc p)) bs] -> firstn (length (pc_bufdata p)) bs = map b8 (pc_bufdata p) ->
      Z.of_nat (length (pc_bufdata p)) <= pc_bufalloc p < 2^32 -> Forall (fun z => 0 <= z < 256) (pc_bufdata p) ->
      rw_cells asegs m CUR (cursor_cells B c cpad) -> (bv_unsigned sp <= CUR /\ CUR + 24 <= al_top L) -> CUR mod 8 = 0 ->
      0 <= idb_off -> idb_off mod 4 = 0 -> cur_off c = idb_off + 8 -> 0 <= cur_remaining c -> cur_off c + cur_remaining c <= Z.of_nat (length (pc_bufdata p)) ->
      0 <= cur_block_type c < 2^32 ->
      rw_cells asegs m EB [CB 256 ej] ->
      ((cobjA RNG m FL (C1 ++ C2) EB 256 /\ (EB + 256 <= CUR \/ CUR + 24 <= EB) /\ (EB + 256 <= P \/ P + PCAP_NG_SF_TOTAL <= EB) /\ (EB + 256 <= B \/ B + pc_bufalloc p <= EB)) \/ (P + 216 = EB)) ->   (* [comment removed for export] *)
      implMG RNG (add_interface MOps (prims HO FO sites) p idb_off c) st
        (add_interface_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG FL C1 C2 FB lo P B CUR EB p s c bs ej m (ps_outfile st))
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 ADD_INTERFACE_ENTRY) fc None m (seg_rom asegs)).
End NgIface.

(* [comment removed for export] *)

Module TwB.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Strings.String.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Sem.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Tac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Arr OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Bytes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ITree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Nodes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Decode OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.SysStep.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Monad OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Fmt OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.StdioCore OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Stdio OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapPrelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapTypes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapPure OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Pcap OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prog.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.ExecF OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.ITreeA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.Shadow OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.RunDraw.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AMalloc_iface.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadG.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.GIA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.PcapRepA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.UnwKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadGX__A3P.TracesA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.Pcap_ifaceA.TwB. Local Ltac Zify.zify_pre_hook ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB.twm_hook_1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

(* [comment removed for export] *)
Definition READ_BYTES_STACK : Z := PCAP_L1_STACK + 64.
Definition READ_BLOCK_STACK : Z := PCAP_L1_STACK + 96 + 4096.
Definition ADD_INTERFACE_STACK : Z := STDIO_STACK + 144.   (* [comment removed for export] *)

Section NgIface.
  Context {rc : runConstT} {tlsI : A3W.ABase.TwB.atlsT}.
  Context {H hptr : Type} (HO : HeapOps H hptr) (FO : @FrameOps H hptr) (sites : stack_site -> Z).
  Variable GIOA : alayout -> footprint -> PState H hptr -> list (@cblock hptr) -> list (@cblock hptr) -> list fblock -> mem -> Prop.
  Variable TP : tparams.
  #[local] Abbreviation cblk := (@cblock hptr).
  #[local] Abbreviation PS := (PState H hptr).
  #[local] Abbreviation pcapT := (PcapTypes.pcap hptr hptr).
  #[local] Abbreviation PR := (prims HO FO sites).
  #[local] Abbreviation GIO := GIOA.
  #[local] Abbreviation SPOA := (std_pre_o GIOA).

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition read_bytes_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (L : alayout) (RNG : footprint) (FL : list fblock) (CL FB : list cblk) (lo D n EB : Z) (foe : bool) (ej : list byte) (m : mem) (o : option hptr) : (rb_status * list Z) -> PS -> footprint -> machine_state -> Prop :=
    fun r s' RNG' ms' => fp_le RNG RNG' /\ let '(st, got) := r in exists a0v m' junk',
      hpost_regs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0v m' ms'
      /\ ps_outfile s' = o /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp)
      /\ agrees_on (fun a => client_keeps FL CL (bv_unsigned sp) a /\ ~ (D <= a < D + n) /\ ~ (EB <= a < EB + 256)) m m'
      /\ GIO L RNG' s' CL FB FL m'
      /\ rw_cells asegs m' D [CB (length got) (map b8 got); CB (Z.to_nat n - length got) junk']
      /\ Forall (fun z => 0 <= z < 256) got /\ 0 <= zlength got <= n
      /\ match st with
         | RBS_Ok => a0v = Z_to_bv 64 1 /\ zlength got = n /\ rw_cells asegs m' EB [CB 256 ej]
         | RBS_Eof => a0v = Z_to_bv 64 0 /\ zlength got = 0 /\ foe = false /\ rw_cells asegs m' EB [CB 256 ej]
         | RBS_Err msg => exists junk'', a0v = Z_to_bv 64 (-1)
             /\ rw_cells asegs m' EB [CB (length msg + 1) (map b8 msg ++ [Z_to_bv 8 0]); CB (255 - length msg) junk''] /\ Z.of_nat (length msg) < 256
             /\ Forall (fun z => 0 < z < 256) msg
         end.

  Definition read_bytes_stmt : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (L : alayout) (RNG : footprint) (s : PS) (CL FB : list cblk) (FL : list fblock) (trC : list Z) (f : hptr) (Af D n EB lo : Z)
           (foe : bool) (dest : rdest hptr) (junk ej : list byte),
      SPOA L RNG sp tp s CL FB FL lo READ_BYTES_STACK m ->
      ucallerA depth_read_bytes L m sp s0 ra trC -> traces_read_bytes TP L (bv_unsigned ra) trC -> nofr frames_read_bytes FL -> In (f, Af, FILE_BLOCK) FB ->
      eval_rdest HO FO sites s dest = D ->
      a0 = Z_to_bv 64 Af -> a1 = Z_to_bv 64 D -> a2 = Z_to_bv 64 n -> a3 = Z_to_bv 64 (Z.b2z foe) -> a4 = Z_to_bv 64 EB ->
      0 <= n <= 2^30 ->
      rw_cells asegs m D [CB (Z.to_nat n) junk] -> cobjA RNG m FL CL D n ->
      rw_cells asegs m EB [CB 256 ej] -> cobjA RNG m FL CL EB 256 -> (D + n <= EB \/ EB + 256 <= D) ->
      EB mod 8 = 0 ->
      implMG RNG (read_bytes MOps (prims HO FO sites) f dest n foe) s
        (read_bytes_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG FL CL FB lo D n EB foe ej m (ps_outfile s))
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 READ_BYTES_ENTRY) fc None m (seg_rom asegs)).


  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition blk_handle (p : pcapT) (s : pcap_ng_sf) (P B : Z) (m : mem) : Prop :=
    rw_cells asegs m (P + 20) [C4 (Z_to_bv 64 (pc_bufsize p)); C8 (Z_to_bv 64 B)]
    /\ rw_cells asegs m (P + 48) [C8 (Z_to_bv 64 (P + PCAP_PRIV_OFF)); C4 (Z_to_bv 64 (Z.b2z (pc_swapped p)))]
    /\ rw_cells asegs m (P + 656) [C4 (Z_to_bv 64 (ng_max_blocksize s))]
    /\ 0 <= pc_bufsize p <= 2^30 /\ 0 <= ng_max_blocksize s <= 2^28 /\ 1 <= pc_bufalloc p < 2^32 /\ pc_bufsize p <= pc_bufalloc p.

  (* [comment removed for export] *)
  Definition same_meta (p' p : pcapT) : Prop :=
    pc_version_major p' = pc_version_major p /\ pc_version_minor p' = pc_version_minor p /\ pc_snapshot p' = pc_snapshot p
    /\ pc_linktype p' = pc_linktype p /\ pc_linktype_ext p' = pc_linktype_ext p /\ pc_tstamp_precision p' = pc_tstamp_precision p
    /\ pc_break_loop p' = pc_break_loop p /\ pc_errbuf p' = pc_errbuf p /\ pc_header p' = pc_header p.

  Definition read_block_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (L : alayout) (RNG : footprint) (FL : list fblock) (C1 C2 FB : list cblk) (lo P CUR EB : Z) (p : pcapT) (s : pcap_ng_sf) (ej : list byte) (m : mem) (o : option hptr)
      : block_result -> PS -> footprint -> machine_state -> Prop :=
    fun r s' RNG' ms' => fp_le RNG RNG' /\ exists a0v m' (p' : pcapT) B' bs',
      hpost_regs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0v m' ms'
      /\ ps_outfile s' = o /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp)
      /\ agrees_on (fun a => client_keeps FL (C1 ++ C2) (bv_unsigned sp) a /\ ~ (P + 24 <= a < P + 32)
                             /\ ~ (CUR <= a < CUR + 24) /\ ~ (EB <= a < EB + 256)) m m'
      /\ GIO L RNG' s' ((pc_buffer p', B', pc_bufalloc p') :: C1 ++ C2) FB FL m'
      /\ blk_handle p' s P B' m'
      /\ rw_cells asegs m' B' [CB (Z.to_nat (pc_bufalloc p')) bs'] /\ firstn (length (pc_bufdata p')) bs' = map b8 (pc_bufdata p')
      /\ Z.of_nat (length (pc_bufdata p')) <= pc_bufalloc p'
      /\ pc_priv p' = pc_priv p /\ pc_rfile p' = pc_rfile p /\ pc_self p' = pc_self p /\ pc_bufsize p' = pc_bufsize p /\ pc_swapped p' = pc_swapped p
      /\ same_meta p' p
      /\ match r with
         | RB_Ok c p'' => p'' = p' /\ a0v = Z_to_bv 64 1 /\ rw_cells asegs m' EB [CB 256 ej]
             /\ (exists cpad, rw_cells asegs m' CUR [C8 (Z_to_bv 64 (B' + 8)); C8 (Z_to_bv 64 (cur_remaining c)); C4 (Z_to_bv 64 (cur_block_type c)); CB 4 cpad])
             /\ cur_off c = 8 /\ 0 <= cur_remaining c /\ cur_remaining c + 12 <= pc_bufalloc p' /\ cur_remaining c + 12 <= 2^30 /\ 0 <= cur_block_type c < 2^32
             /\ Z.of_nat (length (pc_bufdata p')) = cur_remaining c + 12 /\ Forall (fun z => 0 <= z < 256) (pc_bufdata p')
         | RB_Eof p'' => p'' = p' /\ a0v = Z_to_bv 64 0 /\ rw_cells asegs m' EB [CB 256 ej]
             /\ (exists ccs', rw_cells asegs m' CUR ccs' /\ cells_size ccs' = 24%nat)
         | RB_Err msg p'' => p'' = p' /\ a0v = Z_to_bv 64 (-1)
             /\ (exists junk'', rw_cells asegs m' EB [CB (length msg + 1) (map b8 msg ++ [Z_to_bv 8 0]); CB (255 - length msg) junk''])
             /\ Z.of_nat (length msg) < 256 /\ Forall (fun z => 0 < z < 256) msg
             /\ (exists ccs', rw_cells asegs m' CUR ccs' /\ cells_size ccs' = 24%nat)
         end.

  Definition read_block_stmt : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (L : alayout) (RNG : footprint) (st : PS) (C1 C2 FB : list cblk) (FL : list fblock) (trC : list Z) (f : hptr) (Af P B CUR EB lo : Z)
           (p : pcapT) (s : pcap_ng_sf) (i : option hptr) (a_bhdr : rdest hptr) (bs ej : list byte) (ccs : list cell),
      SPOA L RNG sp tp st (C1 ++ (pc_buffer p, B, pc_bufalloc p) :: C2) FB FL lo READ_BLOCK_STACK m ->
      ucallerA depth_read_block L m sp s0 ra trC -> traces_read_block TP L (bv_unsigned ra) trC -> nofr frames_read_block FL ->
      In (f, Af, FILE_BLOCK) FB -> pc_rfile p = f -> pc_priv p = PrivNg s i ->
      In (pc_self p, P, PCAP_NG_SF_TOTAL) (C1 ++ C2) ->
      (exists site, a_bhdr = DStack site 0 /\ site_frameA site = Some (FF_READ_BLOCK, 32)) ->   (* [comment removed for export] *)
      a0 = Z_to_bv 64 Af -> a1 = Z_to_bv 64 P -> a2 = Z_to_bv 64 CUR -> a3 = Z_to_bv 64 EB ->
      blk_handle p s P B m -> rw_cells asegs m B [CB (Z.to_nat (pc_bufalloc p)) bs] ->
      firstn (length (pc_bufdata p)) bs = map b8 (pc_bufdata p) -> Z.of_nat (length (pc_bufdata p)) <= pc_bufalloc p ->
      rw_cells asegs m CUR ccs -> cells_size ccs = 24%nat -> (bv_unsigned sp <= CUR /\ CUR + 24 <= al_top L) -> CUR mod 8 = 0 ->
      rw_cells asegs m EB [CB 256 ej] ->
      ((cobjA RNG m FL (C1 ++ C2) EB 256 /\ (EB + 256 <= CUR \/ CUR + 24 <= EB) /\ (EB + 256 <= P \/ P + PCAP_NG_SF_TOTAL <= EB) /\ (EB + 256 <= B \/ B + pc_bufalloc p <= EB)) \/ (P + 216 = EB)) ->   (* [comment removed for export] *)
      EB mod 8 = 0 ->
      implMG RNG (read_block MOps (prims HO FO sites) a_bhdr p) st
        (read_block_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG FL C1 C2 FB lo P CUR EB p s ej m (ps_outfile st))
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 READ_BLOCK_ENTRY) fc None m (seg_rom asegs)).


  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition IBLK (i : option hptr) (I : Z) (s : pcap_ng_sf) : list cblk :=
    match i with Some q => [(q, I, 40 * ng_ifaces_size s)] | None => [] end.
  (* [comment removed for export] *)
  Definition cursor_cells (B : Z) (c : cursor) (cpad : list byte) : list cell :=
    [C8 (Z_to_bv 64 (B + cur_off c)); C8 (Z_to_bv 64 (cur_remaining c)); C4 (Z_to_bv 64 (cur_block_type c)); CB 4 cpad].

  (* [comment removed for export] *)
  Definition ng_ifaces_closable (s : pcap_ng_sf) (i : option hptr) (I : Z) (m : mem) : Prop :=
    match i with
    | None => I = 0
    | Some q => (exists junk, rw_cells asegs m I [CB (Z.to_nat (40 * ng_ifaces_size s)) junk]) /\ 1 <= ng_ifaces_size s < 2^26
    end.

  Definition add_interface_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (L : alayout) (RNG : footprint) (FL : list fblock) (C1 C2 FB : list cblk) (lo P B CUR EB : Z) (p : pcapT) (s : pcap_ng_sf) (c : cursor) (bs ej : list byte) (m : mem) (o : option hptr)
      : (bool * cursor * pcapT * list Z) -> PS -> footprint -> machine_state -> Prop :=
    fun r st' RNG' ms' => fp_le RNG RNG' /\ let '(ok, c', p', msg) := r in
      exists a0v m' (s' : pcap_ng_sf) (i' : option hptr) (I' : Z) (pad' : list byte) (bs' : list byte),
      hpost_regs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0v m' ms'
      /\ ps_outfile st' = o /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp)
      /\ agrees_on (fun a => client_keeps FL (C1 ++ C2) (bv_unsigned sp) a /\ ~ (P + PCAP_PRIV_OFF <= a < P + PCAP_NG_SF_TOTAL)
                             /\ ~ (CUR <= a < CUR + 24) /\ ~ (EB <= a < EB + 256) /\ ~ (B <= a < B + pc_bufalloc p)) m m'
      /\ p' = set_ng s' i' (set_bufdata (pc_bufdata p') p)
      /\ GIO L RNG' st' (IBLK i' I' s' ++ C1 ++ C2) FB FL m'
      /\ rw_cells asegs m' (P + PCAP_PRIV_OFF) (ng_cells s' I' pad')
      /\ ng_user_tsresol s' = ng_user_tsresol s /\ ng_max_blocksize s' = ng_max_blocksize s /\ 0 <= ng_ifcount s' < 2^32 /\ 0 <= ng_ifaces_size s' < 2^32
      /\ rw_cells asegs m' B [CB (Z.to_nat (pc_bufalloc p)) bs'] /\ firstn (length (pc_bufdata p')) bs' = map b8 (pc_bufdata p')
      /\ length (pc_bufdata p') = length (pc_bufdata p) /\ Forall (fun z => 0 <= z < 256) (pc_bufdata p')
      /\ a0v = Z_to_bv 64 (Z.b2z ok)
      /\ if ok then
           ifaces_ok p' I' m'
           /\ (exists cpad', rw_cells asegs m' CUR (cursor_cells B c' cpad'))
           /\ 0 <= cur_remaining c' /\ cur_off c <= cur_off c' /\ cur_off c' + cur_remaining c' <= cur_off c + cur_remaining c
           /\ cur_block_type c' = cur_block_type c
           /\ rw_cells asegs m' EB [CB 256 ej] /\ msg = []
         else
           ng_ifaces_closable s' i' I' m'
           /\ (exists ccs', rw_cells asegs m' CUR ccs' /\ cells_size ccs' = 24%nat)
           /\ (exists junk'', rw_cells asegs m' EB [CB (length msg + 1) (map b8 msg ++ [Z_to_bv 8 0]); CB (255 - length msg) junk''])
           /\ Z.of_nat (length msg) < 256 /\ Forall (fun z => 0 < z < 256) msg.

  (* [comment removed for export] *)
  Definition add_interface_stmt : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (L : alayout) (RNG : footprint) (st : PS) (C1 C2 FB : list cblk) (FL : list fblock) (trC : list Z) (P B I CUR EB lo idb_off : Z)
           (p : pcapT) (s : pcap_ng_sf) (i : option hptr) (c : cursor) (bs ej pad cpad : list byte),
      SPOA L RNG sp tp st (C1 ++ IBLK i I s ++ C2) FB FL lo ADD_INTERFACE_STACK m ->
      ucallerA depth_add_interface L m sp s0 ra trC -> traces_add_interface TP L (bv_unsigned ra) trC -> nofr frames_add_interface FL ->
      pc_priv p = PrivNg s i ->
      In (pc_self p, P, PCAP_NG_SF_TOTAL) (C1 ++ C2) -> In (pc_buffer p, B, pc_bufalloc p) (C1 ++ C2) ->
      P + PCAP_NG_SF_TOTAL <= B \/ B + pc_bufalloc p <= P ->
      a0 = Z_to_bv 64 P -> a1 = Z_to_bv 64 (B + idb_off) -> a2 = Z_to_bv 64 CUR -> a3 = Z_to_bv 64 EB ->
      rw_cells asegs m (P + 48) [C8 (Z_to_bv 64 (P + PCAP_PRIV_OFF)); C4 (Z_to_bv 64 (Z.b2z (pc_swapped p)))] ->
      rw_cells asegs m (P + PCAP_PRIV_OFF) (ng_cells s I pad) -> ifaces_ok p I m ->
      0 < ng_user_tsresol s < 2^64 -> 0 <= ng_max_blocksize s < 2^32 ->
      rw_cells asegs m B [CB (Z.to_nat (pc_bufalloc p)) bs] -> firstn (length (pc_bufdata p)) bs = map b8 (pc_bufdata p) ->
      Z.of_nat (length (pc_bufdata p)) <= pc_bufalloc p < 2^32 -> Forall (fun z => 0 <= z < 256) (pc_bufdata p) ->
      rw_cells asegs m CUR (cursor_cells B c cpad) -> (bv_unsigned sp <= CUR /\ CUR + 24 <= al_top L) -> CUR mod 8 = 0 ->
      0 <= idb_off -> idb_off mod 4 = 0 -> cur_off c = idb_off + 8 -> 0 <= cur_remaining c -> cur_off c + cur_remaining c <= Z.of_nat (length (pc_bufdata p)) ->
      0 <= cur_block_type c < 2^32 ->
      rw_cells asegs m EB [CB 256 ej] ->
      ((cobjA RNG m FL (C1 ++ C2) EB 256 /\ (EB + 256 <= CUR \/ CUR + 24 <= EB) /\ (EB + 256 <= P \/ P + PCAP_NG_SF_TOTAL <= EB) /\ (EB + 256 <= B \/ B + pc_bufalloc p <= EB)) \/ (P + 216 = EB)) ->   (* [comment removed for export] *)
      implMG RNG (add_interface MOps (prims HO FO sites) p idb_off c) st
        (add_interface_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG FL C1 C2 FB lo P B CUR EB p s c bs ej m (ps_outfile st))
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 ADD_INTERFACE_ENTRY) fc None m (seg_rom asegs)).
End NgIface.
End TwB.
