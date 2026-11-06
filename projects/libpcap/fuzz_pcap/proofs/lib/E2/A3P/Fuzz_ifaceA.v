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
Definition FMT_FAILED_REMOVE : Z := 0x21160.  (* [comment removed for export] *)
Definition FMT_FAILED_OPEN   : Z := 0x211c0.  (* [comment removed for export] *)
Definition FMT_PACKET_LENGTH : Z := 0x210e0.  (* [comment removed for export] *)
Definition FMT_NUM_PACKETS   : Z := 0x21120.  (* [comment removed for export] *)
Definition FMT_COULDNT_OPEN  : Z := 0x210a0.  (* [comment removed for export] *)
Definition STR_DEVNULL : Z := 0x21040.        (* [comment removed for export] *)
Definition STR_W : Z := 0x21020.              (* [comment removed for export] *)
Definition STR_WB : Z := 0x211a0.             (* [comment removed for export] *)
Definition STR_TEMPLATE : Z := 0x21060.       (* [comment removed for export] *)

(* [comment removed for export] *)
Definition unlink_name_ok (name : list byte) : Prop :=
  Namei.path_has_slash name = false /\ name <> Uapi.dot_path /\ name <> Namei.dotdot_path /\ (length name <= Uapi.NAME_MAX)%nat.

Section FuzzIfaces.
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
  Definition fwrite_stmt_o : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (L : alayout) (RNG : footprint) (s : PS) (CL FB : list cblk) (FL : list fblock) (f : hptr) (Af SRC lo : Z) (src : list byte),
      SPOA L RNG sp tp s CL FB FL lo STDIO_STACK m -> In (f, Af, FILE_BLOCK) FB ->
      a0 = Z_to_bv 64 SRC -> a1 = Z_to_bv 64 1 -> a2 = Z_to_bv 64 (Z.of_nat (length src)) -> a3 = Z_to_bv 64 Af ->
      bytes_at asegs m SRC src -> ((src = [] /\ 0x10040 <= SRC /\ SRC <= 0x602fc0) \/ cobjA RNG m FL CL SRC (Z.of_nat (length src))) ->   (* [comment removed for export] *)
      (* [comment removed for export] *)
      (forall fs, files_lookup (ho_eqb HO) (lc_files (ps_libc s)) f = Some fs ->
                  zlength (f_wbuf fs) + Z.of_nat (length src) <= 2^26) ->
      implMG RNG (s_fwrite HO f (map bv_unsigned src)) s
        (fun r s' RNG' ms' => fp_le RNG RNG' /\ exists a0v m', hpost_regs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0v m' ms'
           /\ ps_outfile s' = ps_outfile s /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp) /\ agrees_on (client_keeps FL CL (bv_unsigned sp)) m m'
           /\ GIO L RNG' s' CL FB FL m' /\ a0v = Z_to_bv 64 r /\ 0 <= r <= Z.of_nat (length src))
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 FWRITE_ENTRY) fc None m (seg_rom asegs)).

  (* [comment removed for export] *)
  Definition remove_stmt_o : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (L : alayout) (RNG : footprint) (s : PS) (CL FB : list cblk) (FL : list fblock) (lo NAME : Z) (name : list byte),
      SPOA L RNG sp tp s CL FB FL lo STDIO_STACK m -> a0 = Z_to_bv 64 NAME ->
      bytes_at asegs m NAME (name ++ [Z_to_bv 8 0]) -> ~ In (Z_to_bv 8 0) name -> (1 <= length name <= 4095)%nat ->
      cobjA RNG m FL CL NAME (Z.of_nat (length name) + 1) -> unlink_name_ok name ->
      implMG RNG (s_remove (map bv_unsigned name)) s
        (fun r s' RNG' ms' => fp_le RNG RNG' /\ exists a0v m', hpost_regs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0v m' ms'
           /\ ps_outfile s' = ps_outfile s /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp) /\ agrees_on (client_keeps FL CL (bv_unsigned sp)) m m'
           /\ GIO L RNG' s' CL FB FL m' /\ a0v = Z_to_bv 64 r
           /\ (r = 0 \/ (r = -1 /\ rw_cells asegs m' (ATP + -164) [C4 (Z_to_bv 64 (lc_errno (ps_libc s')))]
                               /\ 0 <= lc_errno (ps_libc s') < 2^31)))
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 REMOVE_ENTRY) fc None m (seg_rom asegs)).

  (* [comment removed for export] *)
  Definition unlink_stmt_o : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (L : alayout) (RNG : footprint) (s : PS) (CL FB : list cblk) (FL : list fblock) (lo NAME : Z) (name : list byte),
      SPOA L RNG sp tp s CL FB FL lo STDIO_STACK m -> a0 = Z_to_bv 64 NAME ->
      bytes_at asegs m NAME (name ++ [Z_to_bv 8 0]) -> ~ In (Z_to_bv 8 0) name -> (1 <= length name <= 4095)%nat ->
      cobjA RNG m FL CL NAME (Z.of_nat (length name) + 1) -> unlink_name_ok name ->
      implMG RNG (s_unlink (map bv_unsigned name)) s
        (fun r s' RNG' ms' => fp_le RNG RNG' /\ exists a0v m', hpost_regs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0v m' ms'
           /\ ps_outfile s' = ps_outfile s /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp) /\ agrees_on (client_keeps FL CL (bv_unsigned sp)) m m'
           /\ GIO L RNG' s' CL FB FL m' /\ a0v = Z_to_bv 64 r /\ (r = 0 \/ r = -1))
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 UNLINK_ENTRY) fc None m (seg_rom asegs)).

  (* [comment removed for export] *)
  Definition close_stmt_o : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (L : alayout) (RNG : footprint) (s : PS) (CL FB : list cblk) (FL : list fblock) (lo fd : Z),
      SPOA L RNG sp tp s CL FB FL lo STDIO_STACK m -> a0 = Z_to_bv 64 fd -> 3 <= fd < 2^31 ->
      implMG RNG (s_close fd) s
        (fun _ s' RNG' ms' => fp_le RNG RNG' /\ exists a0v m', hpost_regs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0v m' ms'
           /\ ps_outfile s' = ps_outfile s /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp) /\ agrees_on (client_keeps FL CL (bv_unsigned sp)) m m'
           /\ GIO L RNG' s' CL FB FL m')
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 CLOSE_ENTRY) fc None m (seg_rom asegs)).

  (* [comment removed for export] *)
  Definition mkstemp_stmt_o : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (L : alayout) (RNG : footprint) (s : PS) (CL FB : list cblk) (FL : list fblock) (lo NAME : Z) (n : nat) (tmpl buf : list byte),
      SPOA L RNG sp tp s CL FB FL lo STDIO_STACK m -> a0 = Z_to_bv 64 NAME ->
      rw_cells asegs m NAME [CB n buf] -> firstn (length tmpl + 1) buf = tmpl ++ [Z_to_bv 8 0] ->
      ~ In (Z_to_bv 8 0) tmpl -> tmpl = map b8 TEMPLATE ->   (* [comment removed for export] *)
      (length tmpl + 9 <= n)%nat -> (n <= 4096)%nat ->   (* [comment removed for export] *)
      cobjA RNG m FL CL NAME (Z.of_nat n) ->
      implMG RNG (s_mkstemp (map bv_unsigned tmpl)) s
        (fun r s' RNG' ms' => fp_le RNG RNG' /\ exists a0v m' buf', hpost_regs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0v m' ms'
           /\ ps_outfile s' = ps_outfile s /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp)
           /\ agrees_on (fun a => client_keeps FL CL (bv_unsigned sp) a /\ ~ (NAME <= a < NAME + Z.of_nat n)) m m'
           /\ GIO L RNG' s' CL FB FL m'
           /\ a0v = Z_to_bv 64 (snd r) /\ (snd r = -1 \/ 3 <= snd r < 2^31)
           /\ rw_cells asegs m' NAME [CB n buf'] /\ firstn (length (fst r) + 1) buf' = map b8 (fst r) ++ [Z_to_bv 8 0]
           /\ Forall (fun z => 0 < z < 256) (fst r) /\ (length (fst r) <= length tmpl)%nat
           /\ (0 <= snd r -> Namei.path_has_slash (map b8 (fst r)) = false /\ map b8 (fst r) <> Uapi.dot_path /\ map b8 (fst r) <> Namei.dotdot_path))
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 MKSTEMP_ENTRY) fc None m (seg_rom asegs)).

  (* [comment removed for export] *)
  Definition printf_d_stmt_o (FMT : Z) (mk : Z -> list (list Z)) : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (L : alayout) (RNG : footprint) (s : PS) (CL FB : list cblk) (FL : list fblock) (lo v : Z),
      SPOA L RNG sp tp s CL FB FL lo STDIO_STACK m -> a0 = Z_to_bv 64 FMT -> a1 = Z_to_bv 64 v -> 0 <= v < 2^31 ->
      implMG RNG (s_printf (mk v)) s
        (fun _ s' RNG' ms' => fp_le RNG RNG' /\ exists a0v m', hpost_regs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0v m' ms'
           /\ ps_outfile s' = ps_outfile s /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp) /\ agrees_on (client_keeps FL CL (bv_unsigned sp)) m m'
           /\ GIO L RNG' s' CL FB FL m')
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 PRINTF_ENTRY) fc None m (seg_rom asegs)).

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition FUZZ_ONE_ENTRY : Z := 0x845c0.
  Definition FUZZ_STACK : Z := PCAP_L4_STACK + 0x1000.     (* [comment removed for export] *)
  Definition fuzz_one_stmt : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (L : alayout) (RNG : footprint) (s : PS) (CL FB : list cblk) (trC : list Z) (lo D : Z) (data : list byte),
      SPOA L RNG sp tp s CL FB [] lo FUZZ_STACK m ->
      ucallerA depth_fuzz_one L m sp s0 ra trC -> traces_fuzz_one TP L (bv_unsigned ra) trC ->
      a0 = Z_to_bv 64 D -> a1 = Z_to_bv 64 (Z.of_nat (length data)) ->
      bytes_at asegs m D data -> ((data = [] /\ 0x10040 <= D /\ D <= 0x602fc0) \/ cobjA RNG m [] CL D (Z.of_nat (length data))) -> Z.of_nat (length data) < 2^26 ->     (* [comment removed for export] *)
      implMG RNG (harness_call HO FO sites (map bv_unsigned data)) s
        (fun r s' RNG' ms' => fp_le RNG RNG' /\ exists t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m' FB',
           ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 r) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                    F (ret_pc ra) fc None m' (seg_rom asegs)
           /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp) /\ agrees_on (client_keeps [] CL (bv_unsigned sp)) m m'
           /\ GIO L RNG' s' CL FB' [] m' /\ r = 0)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 FUZZ_ONE_ENTRY) fc None m (seg_rom asegs)).
End FuzzIfaces.

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
Definition FMT_FAILED_REMOVE : Z := 0x21160.  (* [comment removed for export] *)
Definition FMT_FAILED_OPEN   : Z := 0x211c0.  (* [comment removed for export] *)
Definition FMT_PACKET_LENGTH : Z := 0x210e0.  (* [comment removed for export] *)
Definition FMT_NUM_PACKETS   : Z := 0x21120.  (* [comment removed for export] *)
Definition FMT_COULDNT_OPEN  : Z := 0x210a0.  (* [comment removed for export] *)
Definition STR_DEVNULL : Z := 0x21040.        (* [comment removed for export] *)
Definition STR_W : Z := 0x21020.              (* [comment removed for export] *)
Definition STR_WB : Z := 0x211a0.             (* [comment removed for export] *)
Definition STR_TEMPLATE : Z := 0x21060.       (* [comment removed for export] *)

(* [comment removed for export] *)
Definition unlink_name_ok (name : list byte) : Prop :=
  Namei.path_has_slash name = false /\ name <> Uapi.dot_path /\ name <> Namei.dotdot_path /\ (length name <= Uapi.NAME_MAX)%nat.

Section FuzzIfaces.
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
  Definition fwrite_stmt_o : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (L : alayout) (RNG : footprint) (s : PS) (CL FB : list cblk) (FL : list fblock) (f : hptr) (Af SRC lo : Z) (src : list byte),
      SPOA L RNG sp tp s CL FB FL lo STDIO_STACK m -> In (f, Af, FILE_BLOCK) FB ->
      a0 = Z_to_bv 64 SRC -> a1 = Z_to_bv 64 1 -> a2 = Z_to_bv 64 (Z.of_nat (length src)) -> a3 = Z_to_bv 64 Af ->
      bytes_at asegs m SRC src -> ((src = [] /\ 0x10040 <= SRC /\ SRC <= 0x603fc0) \/ cobjA RNG m FL CL SRC (Z.of_nat (length src))) ->   (* [comment removed for export] *)
      (* [comment removed for export] *)
      (forall fs, files_lookup (ho_eqb HO) (lc_files (ps_libc s)) f = Some fs ->
                  zlength (f_wbuf fs) + Z.of_nat (length src) <= 2^26) ->
      implMG RNG (s_fwrite HO f (map bv_unsigned src)) s
        (fun r s' RNG' ms' => fp_le RNG RNG' /\ exists a0v m', hpost_regs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0v m' ms'
           /\ ps_outfile s' = ps_outfile s /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp) /\ agrees_on (client_keeps FL CL (bv_unsigned sp)) m m'
           /\ GIO L RNG' s' CL FB FL m' /\ a0v = Z_to_bv 64 r /\ 0 <= r <= Z.of_nat (length src))
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 FWRITE_ENTRY) fc None m (seg_rom asegs)).

  (* [comment removed for export] *)
  Definition remove_stmt_o : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (L : alayout) (RNG : footprint) (s : PS) (CL FB : list cblk) (FL : list fblock) (lo NAME : Z) (name : list byte),
      SPOA L RNG sp tp s CL FB FL lo STDIO_STACK m -> a0 = Z_to_bv 64 NAME ->
      bytes_at asegs m NAME (name ++ [Z_to_bv 8 0]) -> ~ In (Z_to_bv 8 0) name -> (1 <= length name <= 4095)%nat ->
      cobjA RNG m FL CL NAME (Z.of_nat (length name) + 1) -> unlink_name_ok name ->
      implMG RNG (s_remove (map bv_unsigned name)) s
        (fun r s' RNG' ms' => fp_le RNG RNG' /\ exists a0v m', hpost_regs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0v m' ms'
           /\ ps_outfile s' = ps_outfile s /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp) /\ agrees_on (client_keeps FL CL (bv_unsigned sp)) m m'
           /\ GIO L RNG' s' CL FB FL m' /\ a0v = Z_to_bv 64 r
           /\ (r = 0 \/ (r = -1 /\ rw_cells asegs m' (ATP + -164) [C4 (Z_to_bv 64 (lc_errno (ps_libc s')))]
                               /\ 0 <= lc_errno (ps_libc s') < 2^31)))
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 REMOVE_ENTRY) fc None m (seg_rom asegs)).

  (* [comment removed for export] *)
  Definition unlink_stmt_o : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (L : alayout) (RNG : footprint) (s : PS) (CL FB : list cblk) (FL : list fblock) (lo NAME : Z) (name : list byte),
      SPOA L RNG sp tp s CL FB FL lo STDIO_STACK m -> a0 = Z_to_bv 64 NAME ->
      bytes_at asegs m NAME (name ++ [Z_to_bv 8 0]) -> ~ In (Z_to_bv 8 0) name -> (1 <= length name <= 4095)%nat ->
      cobjA RNG m FL CL NAME (Z.of_nat (length name) + 1) -> unlink_name_ok name ->
      implMG RNG (s_unlink (map bv_unsigned name)) s
        (fun r s' RNG' ms' => fp_le RNG RNG' /\ exists a0v m', hpost_regs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0v m' ms'
           /\ ps_outfile s' = ps_outfile s /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp) /\ agrees_on (client_keeps FL CL (bv_unsigned sp)) m m'
           /\ GIO L RNG' s' CL FB FL m' /\ a0v = Z_to_bv 64 r /\ (r = 0 \/ r = -1))
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 UNLINK_ENTRY) fc None m (seg_rom asegs)).

  (* [comment removed for export] *)
  Definition close_stmt_o : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (L : alayout) (RNG : footprint) (s : PS) (CL FB : list cblk) (FL : list fblock) (lo fd : Z),
      SPOA L RNG sp tp s CL FB FL lo STDIO_STACK m -> a0 = Z_to_bv 64 fd -> 3 <= fd < 2^31 ->
      implMG RNG (s_close fd) s
        (fun _ s' RNG' ms' => fp_le RNG RNG' /\ exists a0v m', hpost_regs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0v m' ms'
           /\ ps_outfile s' = ps_outfile s /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp) /\ agrees_on (client_keeps FL CL (bv_unsigned sp)) m m'
           /\ GIO L RNG' s' CL FB FL m')
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 CLOSE_ENTRY) fc None m (seg_rom asegs)).

  (* [comment removed for export] *)
  Definition mkstemp_stmt_o : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (L : alayout) (RNG : footprint) (s : PS) (CL FB : list cblk) (FL : list fblock) (lo NAME : Z) (n : nat) (tmpl buf : list byte),
      SPOA L RNG sp tp s CL FB FL lo STDIO_STACK m -> a0 = Z_to_bv 64 NAME ->
      rw_cells asegs m NAME [CB n buf] -> firstn (length tmpl + 1) buf = tmpl ++ [Z_to_bv 8 0] ->
      ~ In (Z_to_bv 8 0) tmpl -> tmpl = map b8 TEMPLATE ->   (* [comment removed for export] *)
      (length tmpl + 9 <= n)%nat -> (n <= 4096)%nat ->   (* [comment removed for export] *)
      cobjA RNG m FL CL NAME (Z.of_nat n) ->
      implMG RNG (s_mkstemp (map bv_unsigned tmpl)) s
        (fun r s' RNG' ms' => fp_le RNG RNG' /\ exists a0v m' buf', hpost_regs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0v m' ms'
           /\ ps_outfile s' = ps_outfile s /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp)
           /\ agrees_on (fun a => client_keeps FL CL (bv_unsigned sp) a /\ ~ (NAME <= a < NAME + Z.of_nat n)) m m'
           /\ GIO L RNG' s' CL FB FL m'
           /\ a0v = Z_to_bv 64 (snd r) /\ (snd r = -1 \/ 3 <= snd r < 2^31)
           /\ rw_cells asegs m' NAME [CB n buf'] /\ firstn (length (fst r) + 1) buf' = map b8 (fst r) ++ [Z_to_bv 8 0]
           /\ Forall (fun z => 0 < z < 256) (fst r) /\ (length (fst r) <= length tmpl)%nat
           /\ (0 <= snd r -> Namei.path_has_slash (map b8 (fst r)) = false /\ map b8 (fst r) <> Uapi.dot_path /\ map b8 (fst r) <> Namei.dotdot_path))
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 MKSTEMP_ENTRY) fc None m (seg_rom asegs)).

  (* [comment removed for export] *)
  Definition printf_d_stmt_o (FMT : Z) (mk : Z -> list (list Z)) : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (L : alayout) (RNG : footprint) (s : PS) (CL FB : list cblk) (FL : list fblock) (lo v : Z),
      SPOA L RNG sp tp s CL FB FL lo STDIO_STACK m -> a0 = Z_to_bv 64 FMT -> a1 = Z_to_bv 64 v -> 0 <= v < 2^31 ->
      implMG RNG (s_printf (mk v)) s
        (fun _ s' RNG' ms' => fp_le RNG RNG' /\ exists a0v m', hpost_regs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0v m' ms'
           /\ ps_outfile s' = ps_outfile s /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp) /\ agrees_on (client_keeps FL CL (bv_unsigned sp)) m m'
           /\ GIO L RNG' s' CL FB FL m')
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 PRINTF_ENTRY) fc None m (seg_rom asegs)).

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition FUZZ_ONE_ENTRY : Z := 0x84628.
  Definition FUZZ_STACK : Z := PCAP_L4_STACK + 0x1000.     (* [comment removed for export] *)
  Definition fuzz_one_stmt : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (L : alayout) (RNG : footprint) (s : PS) (CL FB : list cblk) (trC : list Z) (lo D : Z) (data : list byte),
      SPOA L RNG sp tp s CL FB [] lo FUZZ_STACK m ->
      ucallerA depth_fuzz_one L m sp s0 ra trC -> traces_fuzz_one TP L (bv_unsigned ra) trC ->
      a0 = Z_to_bv 64 D -> a1 = Z_to_bv 64 (Z.of_nat (length data)) ->
      bytes_at asegs m D data -> ((data = [] /\ 0x10040 <= D /\ D <= 0x603fc0) \/ cobjA RNG m [] CL D (Z.of_nat (length data))) -> Z.of_nat (length data) < 2^26 ->     (* [comment removed for export] *)
      implMG RNG (harness_call HO FO sites (map bv_unsigned data)) s
        (fun r s' RNG' ms' => fp_le RNG RNG' /\ exists t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m' FB',
           ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 r) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                    F (ret_pc ra) fc None m' (seg_rom asegs)
           /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp) /\ agrees_on (client_keeps [] CL (bv_unsigned sp)) m m'
           /\ GIO L RNG' s' CL FB' [] m' /\ r = 0)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 FUZZ_ONE_ENTRY) fc None m (seg_rom asegs)).
End FuzzIfaces.
End TwB.
