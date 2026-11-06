(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Lia.
(* [comment removed for export] *)
From Stdlib Require ZArith NArith List Lia Bool String.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Prelude Sem.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Tac Arr Bytes ITree Nodes Decode SysStep ImgSrc3.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Prelim Monad Fmt StdioCore Stdio PcapPrelim PcapTypes PcapPure Pcap Prog.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require InitMem.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require Printf_kit__Musl.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require FileCells__Musl.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require GI.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require GIFacts__S3.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require PcapRep.
From OSSVerify.libpcap.fuzz_pcap.images Require Plain.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Ceiling.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require LiaPin.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require ImgTgtUbsan.
From OSSVerify.libpcap.fuzz_pcap.images Require Ubsan.
From LinuxProcessSemantics.Riscv Require Instr Decode DecodeC Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Image.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require SecDiet.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require MonadX.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require AmoStep__Musl.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_memcpy.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Adapter__Spec.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Module Pcap_iface.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool String.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Sem.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import Tac Arr Bytes ITree Nodes Decode SysStep ImgSrc3.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Import Prelim Monad Fmt StdioCore Stdio PcapPrelim PcapTypes PcapPure Pcap Prog.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require InitMem. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require Printf_kit__Musl. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require FileCells__Musl. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.InitMem OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_kit__Musl.StartupKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.FileCells__Musl.FileCells.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require GI. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require GIFacts__S3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require PcapRep. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.GI OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.GIFacts__S3.Ifaces OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.PcapRep.
From OSSVerify.libpcap.fuzz_pcap.images Require Import Plain.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import Ceiling.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import LiaPin.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac lia_e2w2_base := first [ zify_prune; zify_noeuclid; Z.euclidean_division_equations_cleanup; xlia zchecker
                                 | zify_prune; Zify.zify; xlia zchecker | Zify.zify; xlia zchecker ].
Local Ltac ceil_mentioned := lazymatch goal with | |- context [@alloc_ceiling _] => idtac | _ : context [@alloc_ceiling _] |- _ => idtac end.
(* [comment removed for export] *)
Local Ltac lia ::= clear_unpinned; try (ceil_ok; ceil_mentioned; ceil_facts); pinned_lia_core.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section WithCeil.
Context {CEILV : CEIL}.
Definition CALLOC_ENTRY : Z := 0x18654.
Definition REALLOC_ENTRY : Z := 0x1a138.
Definition FOPEN_ENTRY : Z := 0x1b08c.
Definition FCLOSE_ENTRY : Z := 0x1ab54.
Definition FREAD_ENTRY : Z := 0x1b5e8.
Definition FERROR_ENTRY : Z := 0x1ac20.
Definition FILENO_ENTRY : Z := 0x1b020.
Definition VSNPRINTF_ENTRY : Z := 0x2056c.
Definition SNPRINTF_ENTRY : Z := 0x1baac.
Definition STRERROR_R_ENTRY : Z := 0x20f74.
Definition STRLEN_ENTRY : Z := 0x2100c.
Definition MEMCPY_ENTRY : Z := 0x207e0.
Definition ERRNO_LOCATION_ENTRY : Z := 0x181bc.
Definition STDIN_FILE : Z := 0x23750.          (* [comment removed for export] *)
Definition GOT_STDIN : Z := 0x225f0.           (* [comment removed for export] *)
Definition STR_RB : Z := 0x108ab.              (* [comment removed for export] *)
Definition STR_PERCENT_S : Z := 0x107e7.       (* [comment removed for export] *)
Definition STR_STATS_NA : Z := 0x10e78.        (* [comment removed for export] *)

(* [comment removed for export] *)
Definition PCAP_L0_STACK : Z := 0x11000.   (* [comment removed for export] *)
Definition PCAP_L1_STACK : Z := 0x12000.   (* [comment removed for export] *)
Definition PCAP_L1B_STACK : Z := 0x13000.  (* [comment removed for export] *)
Definition PCAP_L2_STACK : Z := 0x14000.   (* [comment removed for export] *)
Definition PCAP_L3_STACK : Z := 0x16000.   (* [comment removed for export] *)
Definition PCAP_L4_STACK : Z := 0x18000.   (* [comment removed for export] *)

(* [comment removed for export] *)
Definition FUZZ_FRAME : Z := 4432.

(* [comment removed for export] *)
Definition sites_at (spB : Z) (site : stack_site) : Z :=
  match site with
  | SiteMagic => spB - 92                 (* [comment removed for export] *)
  | SitePcapHdrRest => spB - 196          (* [comment removed for export] *)
  | SiteSfHdr => spB - 208                (* [comment removed for export] *)
  | SiteDiscardBuf => spB - 4304          (* [comment removed for export] *)
  | SiteNgTotalLength => spB - 188        (* [comment removed for export] *)
  | SiteNgByteOrderMagic => spB - 192     (* [comment removed for export] *)
  | SiteBhdrCheckHeader => spB - 320      (* [comment removed for export] *)
  | SiteBhdrNextPacket => spB - 368       (* [comment removed for export] *)
  | SiteReadStage => 0x23989              (* [comment removed for export] *)
  end.
(* [comment removed for export] *)
Definition open_name_ok (wr : bool) (name : list byte) : Prop :=
  if wr then (Namei.path_has_slash name = false \/ name = Uapi.devnull_path)
  else (Namei.path_has_slash name = false /\ Fs.path_eqb name Namei.dotdot_path = false).

(* [comment removed for export] *)
Definition D_NEXT_EX : Z := 0.        Definition D_OFFLINE_READ : Z := 32.     Definition D_NEXT_PACKET : Z := 112.
Definition D_OPEN_OFFLINE : Z := 0.   Definition D_FOPEN_OFFLINE : Z := 48.    Definition D_CHECK_HEADER : Z := 96.
Definition D_READ_BLOCK_CH : Z := 224. Definition D_READ_BLOCK_NP : Z := 272.

Section Ifaces.
  Context {H hptr : Type} (HO : HeapOps H hptr) (K : modkit H hptr) (sites : stack_site -> Z).
  #[local] Abbreviation cblk := (@cblock hptr).
  #[local] Abbreviation PS := (PState H hptr).
  #[local] Abbreviation pcapT := (PcapTypes.pcap hptr hptr).
  #[local] Abbreviation PR := (prims HO fo_nop sites).
  #[local] Abbreviation GIO := (GIo K).
  #[local] Abbreviation SPO := (std_pre_o K).
  #[local] Abbreviation PCR := (@PCAPR hptr).
  #[local] Abbreviation PCRC := (@PCAPR_closable hptr).

  (* [comment removed for export] *)
  Definition client_range (R : rctx) (CL : list cblk) (SP A n : Z) : Prop :=
    (forall a, A <= a < A + n -> in_block CL a) \/ (SP <= A /\ A + n <= rc_spmain R).

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition hpost_regs (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (a0v : word) (m' : mem) (ms' : machine_state) : Prop :=
    exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6,
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0v a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (ret_pc ra) fc None m' (seg_rom ssegs).

  (* [comment removed for export] *)
  Definition enomem_at (R : rctx) (s' : PS) (m' : mem) : Prop :=
    lc_errno (ps_libc s') = 12 /\ rw_cells ssegs m' (utp R + -164) [C4 (Z_to_bv 64 12)].

  Definition malloc_stmt_o : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (R : rctx) (s : PS) (CL FB : list cblk) (lo n : Z),
      SPO sp tp R s CL FB lo MALLOC_STACK m -> a0 = Z_to_bv 64 n -> 0 <= n < 2^32 ->
      implM ssegs (pmalloc HO n) s
        (fun r s' ms' => exists a0v m', hpost_regs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0v m' ms'
           /\ ps_outfile s' = ps_outfile s /\ mem_inv ssegs m' /\ stk ssegs m' lo (bv_unsigned sp) /\ agrees_on (client_keeps CL (bv_unsigned sp)) m m'
           /\ match r with
              | None => a0v = Z_to_bv 64 0 /\ GIO R s' CL FB m' /\ enomem_at R s' m'
              | Some q => exists A junk, a0v = Z_to_bv 64 A /\ GIO R s' ((q, A, n) :: CL) FB m'
                          /\ rw_cells ssegs m' A [CB (Z.to_nat n) junk]
              end)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 MALLOC_ENTRY) fc None m (seg_rom ssegs)).

  (* [comment removed for export] *)
  Definition calloc_stmt_o : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (R : rctx) (s : PS) (CL FB : list cblk) (lo cnt sz : Z),
      SPO sp tp R s CL FB lo MALLOC_STACK m -> a0 = Z_to_bv 64 cnt -> a1 = Z_to_bv 64 sz -> 0 <= cnt < 2^32 -> 0 <= sz < 2^32 -> cnt * sz <= 3260 ->
      implM ssegs (pcalloc HO cnt sz) s
        (fun r s' ms' => exists a0v m', hpost_regs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0v m' ms'
           /\ ps_outfile s' = ps_outfile s /\ mem_inv ssegs m' /\ stk ssegs m' lo (bv_unsigned sp) /\ agrees_on (client_keeps CL (bv_unsigned sp)) m m'
           /\ match r with
              | None => a0v = Z_to_bv 64 0 /\ GIO R s' CL FB m' /\ enomem_at R s' m'
              | Some q => exists A, a0v = Z_to_bv 64 A /\ GIO R s' ((q, A, cnt * sz) :: CL) FB m'
                          /\ rw_cells ssegs m' A [CB (Z.to_nat (cnt * sz)) (repeat (Z_to_bv 8 0) (Z.to_nat (cnt * sz)))]
              end)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 CALLOC_ENTRY) fc None m (seg_rom ssegs)).

  (* [comment removed for export] *)
  Definition realloc_stmt_o : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (R : rctx) (s : PS) (C1 C2 FB : list cblk) (q : hptr) (A sz lo n : Z) (bs : list byte),
      SPO sp tp R s (C1 ++ (q, A, sz) :: C2) FB lo MALLOC_STACK m -> a0 = Z_to_bv 64 A -> a1 = Z_to_bv 64 n -> 0 <= n < 2^32 ->
      rw_cells ssegs m A [CB (Z.to_nat sz) bs] ->
      implM ssegs (prealloc HO q n) s
        (fun r s' ms' => exists a0v m', hpost_regs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0v m' ms'
           /\ ps_outfile s' = ps_outfile s /\ mem_inv ssegs m' /\ stk ssegs m' lo (bv_unsigned sp) /\ agrees_on (client_keeps (C1 ++ C2) (bv_unsigned sp)) m m'
           /\ match r with
              | None => a0v = Z_to_bv 64 0 /\ GIO R s' (C1 ++ (q, A, sz) :: C2) FB m' /\ rw_cells ssegs m' A [CB (Z.to_nat sz) bs] /\ enomem_at R s' m'
              | Some q' => exists A' junk, a0v = Z_to_bv 64 A' /\ GIO R s' ((q', A', n) :: C1 ++ C2) FB m'
                          /\ rw_cells ssegs m' A' [CB (Z.to_nat (Z.min sz n)) (firstn (Z.to_nat (Z.min sz n)) bs); CB (Z.to_nat (n - Z.min sz n)) junk]
              end)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 REALLOC_ENTRY) fc None m (seg_rom ssegs)).

  Definition free_stmt_o : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (R : rctx) (s : PS) (C1 C2 FB : list cblk) (q : hptr) (A n lo : Z),
      SPO sp tp R s (C1 ++ (q, A, n) :: C2) FB lo FREE_STACK m -> a0 = Z_to_bv 64 A ->
      implM ssegs (pfree HO q) s
        (fun _ s' ms' => exists a0v m', hpost_regs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0v m' ms'
           /\ ps_outfile s' = ps_outfile s /\ mem_inv ssegs m' /\ stk ssegs m' lo (bv_unsigned sp) /\ agrees_on (client_keeps (C1 ++ C2) (bv_unsigned sp)) m m'
           /\ GIO R s' (C1 ++ C2) FB m')
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 FREE_ENTRY) fc None m (seg_rom ssegs)).

  (* [comment removed for export] *)

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition mode_ok (wr : bool) (md : list byte) : Prop :=
    if wr then (md = [Z_to_bv 8 119] \/ md = [Z_to_bv 8 119; Z_to_bv 8 98])     (* [comment removed for export] *)
    else (md = [Z_to_bv 8 114] \/ md = [Z_to_bv 8 114; Z_to_bv 8 98]).          (* [comment removed for export] *)

  (* [comment removed for export] *)
  Definition mode_lit (wr : bool) (MODE : Z) (md : list byte) : Prop :=
    if wr then (MODE = 0x10da2 /\ md = [Z_to_bv 8 119]) \/ (MODE = 0x10427 /\ md = [Z_to_bv 8 119; Z_to_bv 8 98])   (* [comment removed for export] *)
    else (MODE = STR_RB /\ md = [Z_to_bv 8 114; Z_to_bv 8 98]).                                                  (* [comment removed for export] *)

  (* [comment removed for export] *)
  Definition fopen_stmt_o : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (R : rctx) (s : PS) (CL FB : list cblk) (lo NAME MODE : Z) (name md : list byte) (wr : bool),
      SPO sp tp R s CL FB lo STDIO_STACK m -> a0 = Z_to_bv 64 NAME -> a1 = Z_to_bv 64 MODE ->
      bytes_at ssegs m NAME (name ++ [Z_to_bv 8 0]) -> ~ In (Z_to_bv 8 0) name -> (1 <= length name <= 4095)%nat ->
      open_name_ok wr name ->   (* [comment removed for export] *)
      (client_range R CL (bv_unsigned sp) NAME (Z.of_nat (length name) + 1) \/ (0x10000 <= NAME /\ NAME + Z.of_nat (length name) + 1 <= 0x13000)) ->
      bytes_at ssegs m MODE (md ++ [Z_to_bv 8 0]) -> mode_lit wr MODE md ->
      implM ssegs (s_fopen HO (map bv_unsigned name) wr) s
        (fun r s' ms' => exists a0v m', hpost_regs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0v m' ms'
           /\ ps_outfile s' = ps_outfile s /\ mem_inv ssegs m' /\ stk ssegs m' lo (bv_unsigned sp) /\ agrees_on (client_keeps CL (bv_unsigned sp)) m m'
           /\ match r with
              | None => a0v = Z_to_bv 64 0 /\ GIO R s' CL FB m'
                        /\ rw_cells ssegs m' (utp R + -164) [C4 (Z_to_bv 64 (lc_errno (ps_libc s')))]   (* [comment removed for export] *)
                        /\ 0 <= lc_errno (ps_libc s') < 2^31
              | Some f => exists Af, a0v = Z_to_bv 64 Af /\ GIO R s' CL ((f, Af, FILE_BLOCK) :: FB) m'
              end)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 FOPEN_ENTRY) fc None m (seg_rom ssegs)).

  (* [comment removed for export] *)
  Definition fclose_stmt_o : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (R : rctx) (s : PS) (CL F1 F2 : list cblk) (f : hptr) (Af lo : Z),
      SPO sp tp R s CL (F1 ++ (f, Af, FILE_BLOCK) :: F2) lo STDIO_STACK m -> a0 = Z_to_bv 64 Af -> ps_outfile s <> Some f ->
      implM ssegs (s_fclose HO f) s
        (fun _ s' ms' => exists a0v m', hpost_regs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0v m' ms'
           /\ ps_outfile s' = ps_outfile s /\ mem_inv ssegs m' /\ stk ssegs m' lo (bv_unsigned sp) /\ agrees_on (client_keeps CL (bv_unsigned sp)) m m'
           /\ GIO R s' CL (F1 ++ F2) m')
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 FCLOSE_ENTRY) fc None m (seg_rom ssegs)).

  (* [comment removed for export] *)
  Definition fread_stmt_o : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (R : rctx) (s : PS) (CL FB : list cblk) (f : hptr) (Af D n lo : Z) (junk : list byte),
      SPO sp tp R s CL FB lo STDIO_STACK m -> In (f, Af, FILE_BLOCK) FB ->
      a0 = Z_to_bv 64 D -> a1 = Z_to_bv 64 1 -> a2 = Z_to_bv 64 n -> a3 = Z_to_bv 64 Af -> 0 <= n <= 2^30 ->
      rw_cells ssegs m D [CB (Z.to_nat n) junk] -> client_range R CL (bv_unsigned sp) D n ->
      implM ssegs (s_fread HO f D n) s
        (fun got s' ms' => exists a0v m' junk', hpost_regs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0v m' ms'
           /\ ps_outfile s' = ps_outfile s /\ mem_inv ssegs m' /\ stk ssegs m' lo (bv_unsigned sp)
           /\ agrees_on (fun a => client_keeps CL (bv_unsigned sp) a /\ ~ (D <= a < D + n)) m m'
           /\ GIO R s' CL FB m'
           /\ a0v = Z_to_bv 64 (zlength got) /\ 0 <= zlength got <= n /\ Forall (fun z => 0 <= z < 256) got
           /\ rw_cells ssegs m' D [CB (length got) (map b8 got); CB (Z.to_nat n - length got) junk'])
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 FREAD_ENTRY) fc None m (seg_rom ssegs)).

  (* [comment removed for export] *)
  Definition ferror_stmt_o : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (R : rctx) (s : PS) (CL FB : list cblk) (f : hptr) (Af lo : Z),
      SPO sp tp R s CL FB lo STDIO_STACK m -> In (f, Af, FILE_BLOCK) FB -> a0 = Z_to_bv 64 Af ->
      implM ssegs (s_ferror HO f) s
        (fun r s' ms' => exists a0v m', hpost_regs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0v m' ms'
           /\ mem_inv ssegs m' /\ stk ssegs m' lo (bv_unsigned sp) /\ agrees_on (client_keeps CL (bv_unsigned sp)) m m'
           /\ GIO R s' CL FB m' /\ s' = s /\ a0v = Z_to_bv 64 (Z.b2z r)
           (* [comment removed for export] *)
           /\ (r = true -> rw_cells ssegs m' (utp R + -164) [C4 (Z_to_bv 64 (lc_errno (ps_libc s')))] /\ 0 <= lc_errno (ps_libc s') < 2^31))
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 FERROR_ENTRY) fc None m (seg_rom ssegs)).

  Definition fileno_stmt_o : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (R : rctx) (s : PS) (CL FB : list cblk) (f : hptr) (Af lo : Z),
      SPO sp tp R s CL FB lo STDIO_STACK m -> In (f, Af, FILE_BLOCK) FB -> a0 = Z_to_bv 64 Af ->
      implM ssegs (s_fileno HO f) s
        (fun r s' ms' => exists a0v m', hpost_regs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0v m' ms'
           /\ mem_inv ssegs m' /\ stk ssegs m' lo (bv_unsigned sp) /\ agrees_on (client_keeps CL (bv_unsigned sp)) m m'
           /\ GIO R s' CL FB m' /\ s' = s /\ a0v = Z_to_bv 64 r /\ 0 <= r < 2^31)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 FILENO_ENTRY) fc None m (seg_rom ssegs)).

  (* [comment removed for export] *)
  Definition fprintf_dd_stmt_o (FMT : Z) (mk : Z -> Z -> list (list Z)) : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (R : rctx) (s : PS) (CL FB : list cblk) (f : hptr) (Af lo v1 v2 : Z),
      SPO sp tp R s CL FB lo STDIO_STACK m -> In (f, Af, FILE_BLOCK) FB ->
      a0 = Z_to_bv 64 Af -> a1 = Z_to_bv 64 FMT -> a2 = sx32 (Z_to_bv 64 v1) -> a3 = sx32 (Z_to_bv 64 v2) -> 0 <= v1 < 2^32 -> 0 <= v2 < 2^32 ->
      implM ssegs (s_fprintf HO f (mk v1 v2)) s
        (fun _ s' ms' => exists a0v m', hpost_regs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0v m' ms'
           /\ ps_outfile s' = ps_outfile s /\ mem_inv ssegs m' /\ stk ssegs m' lo (bv_unsigned sp) /\ agrees_on (client_keeps CL (bv_unsigned sp)) m m'
           /\ GIO R s' CL FB m')
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 FPRINTF_ENTRY) fc None m (seg_rom ssegs)).

  Definition fprintf_s_stmt_o (FMT : Z) (mk : list Z -> list (list Z)) : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (R : rctx) (s : PS) (CL FB : list cblk) (f : hptr) (Af lo P : Z) (str slack : list byte),
      SPO sp tp R s CL FB lo STDIO_STACK m -> In (f, Af, FILE_BLOCK) FB ->
      a0 = Z_to_bv 64 Af -> a1 = Z_to_bv 64 FMT -> a2 = Z_to_bv 64 P ->
      bytes_at ssegs m P (str ++ Z_to_bv 8 0 :: slack) -> ~ In (Z_to_bv 8 0) str -> Z.of_nat (length str) < 2^24 ->
      (- (P + Z.of_nat (length str) + 1)) mod 8 <= Z.of_nat (length slack) ->   (* [comment removed for export] *)
      client_range R CL (bv_unsigned sp) P (Z.of_nat (length str) + 1) ->
      implM ssegs (s_fprintf HO f (mk (map bv_unsigned str))) s
        (fun _ s' ms' => exists a0v m', hpost_regs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0v m' ms'
           /\ ps_outfile s' = ps_outfile s /\ mem_inv ssegs m' /\ stk ssegs m' lo (bv_unsigned sp) /\ agrees_on (client_keeps CL (bv_unsigned sp)) m m'
           /\ GIO R s' CL FB m')
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 FPRINTF_ENTRY) fc None m (seg_rom ssegs)).

  (* [comment removed for export] *)
  Definition fmt_at (m : mem) (FMTA : Z) (fs : string) : Prop :=
    bytes_at ssegs m FMTA (map (fun c => Z_to_bv 8 (Z.of_nat (Ascii.nat_of_ascii c))) (String.list_ascii_of_string fs) ++ [Z_to_bv 8 0])
    /\ 0x10000 <= FMTA /\ FMTA + Z.of_nat (String.length fs) + 1 <= 0x13000.

  (* [comment removed for export] *)
  Definition conv_ok (c : conv) (a : farg) : bool :=
    match c, a with
    | Cs, AStr _ => true
    | Cd, AInt _ => true | Cu, AInt _ => true | Czu, AInt _ => true | C08x, AInt _ => true
    | _, _ => false
    end.
  Fixpoint items_ok (its : list fitem) (args : list farg) : bool :=
    match its with
    | [] => match args with [] => true | _ => false end
    | FLit l :: its' => forallb (fun c => negb (c =? 0) && negb (c =? 37)) l && items_ok its' args
    | FConv c :: its' => match args with a :: args' => conv_ok c a && items_ok its' args' | [] => false end
    | FBad _ :: _ => false
    end.
  Definition fmt_ok (fs : string) (args : list farg) : bool :=
    items_ok (fmt fs) args && (Z.of_nat (String.length fs) <? 4096).

  (* [comment removed for export] *)
  Definition farg_word (R : rctx) (CL : list cblk) (SP D dn : Z) (m : mem) (a : farg) (w : word) : Prop :=
    match a with
    | AInt z => w = Z_to_bv 64 z
    | AStr cs => exists P bs slack, w = Z_to_bv 64 P /\ bytes_at ssegs m P (bs ++ Z_to_bv 8 0 :: slack) /\ ~ In (Z_to_bv 8 0) bs
                 /\ cs = map bv_unsigned bs /\ Z.of_nat (length bs) < 2^24
                 /\ (- (P + Z.of_nat (length bs) + 1)) mod 8 <= Z.of_nat (length slack)
                 /\ (P + Z.of_nat (length bs) + 1 + Z.of_nat (length slack) <= D \/ D + dn <= P)
                 /\ (client_range R CL SP P (Z.of_nat (length bs) + 1)
                     \/ ((0x10000 <= P /\ P + Z.of_nat (length bs) + 1 <= 0x13000)
                         \/ (utp R - 200 <= P /\ P + Z.of_nat (length bs) + 1 + Z.of_nat (length slack) <= utp R - 200 + 4096)))
    end.

  (* [comment removed for export] *)
  Definition snprintf_spec_stmt : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (R : rctx) (s : PS) (CL FB : list cblk) (lo DST n FMTA : Z) (fs : string) (args : list farg) (junk : list byte),
      SPO sp tp R s CL FB lo STDIO_STACK m ->
      a0 = Z_to_bv 64 DST -> a1 = Z_to_bv 64 n -> a2 = Z_to_bv 64 FMTA -> 1 <= n < 2^31 -> fmt_at m FMTA fs -> fmt_ok fs args = true ->
      (length args <= 3)%nat -> Forall2 (farg_word R CL (bv_unsigned sp) DST n m) args (firstn (length args) [a3; a4; a5]) ->
      rw_cells ssegs m DST [CB (Z.to_nat n) junk] -> client_range R CL (bv_unsigned sp) DST n ->
      evt ssegs (fun ms' => exists a0v m' junk', hpost_regs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0v m' ms'
           /\ munch [(bv_unsigned sp - STDIO_STACK, bv_unsigned sp); (DST, DST + n)] m m' /\ wmono ssegs m m' /\ mem_inv ssegs m'
           /\ stk ssegs m' lo (bv_unsigned sp)
           /\ a0v = Z_to_bv 64 (snprintf_ret (fmt fs) args)
           /\ rw_cells ssegs m' DST [CB (length (Fmt.snprintf n fs args) + 1) (map b8 (Fmt.snprintf n fs args) ++ [Z_to_bv 8 0]);
                                   CB (Z.to_nat n - length (Fmt.snprintf n fs args) - 1) junk'])
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 SNPRINTF_ENTRY) fc None m (seg_rom ssegs)).

  (* [comment removed for export] *)
  Definition vsnprintf_spec_stmt : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (R : rctx) (s : PS) (CL FB : list cblk) (lo DST n FMTA AP : Z) (fs : string) (args : list farg)
           (ws : list word) (junk : list byte),
      SPO sp tp R s CL FB lo STDIO_STACK m ->
      a0 = Z_to_bv 64 DST -> a1 = Z_to_bv 64 n -> a2 = Z_to_bv 64 FMTA -> a3 = Z_to_bv 64 AP -> 1 <= n < 2^31 -> fmt_at m FMTA fs -> fmt_ok fs args = true ->
      length ws = length args -> Forall2 (farg_word R CL (bv_unsigned sp) DST n m) args ws ->
      rw_cells ssegs m AP (map C8 ws) -> bv_unsigned sp <= AP -> AP + 8 * Z.of_nat (length ws) <= rc_spmain R ->
      (AP + 8 * Z.of_nat (length ws) <= DST \/ DST + n <= AP) ->
      rw_cells ssegs m DST [CB (Z.to_nat n) junk] -> client_range R CL (bv_unsigned sp) DST n ->
      evt ssegs (fun ms' => exists a0v m' junk', hpost_regs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0v m' ms'
           /\ munch [(bv_unsigned sp - STDIO_STACK, bv_unsigned sp); (DST, DST + n)] m m' /\ wmono ssegs m m' /\ mem_inv ssegs m'
           /\ stk ssegs m' lo (bv_unsigned sp)
           /\ a0v = Z_to_bv 64 (snprintf_ret (fmt fs) args)
           /\ rw_cells ssegs m' DST [CB (length (Fmt.snprintf n fs args) + 1) (map b8 (Fmt.snprintf n fs args) ++ [Z_to_bv 8 0]);
                                   CB (Z.to_nat n - length (Fmt.snprintf n fs args) - 1) junk'])
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 VSNPRINTF_ENTRY) fc None m (seg_rom ssegs)).

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition leaf_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (v : word) (m : mem) : machine_state -> Prop :=
    fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6,
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (ret_pc ra) fc None m (seg_rom ssegs)
      /\ a0 = v.

  (* [comment removed for export] *)
  Definition linktype_to_dlt_stmt : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (lt : Z),
      mem_inv ssegs m -> a0 = Z_to_bv 64 lt -> 0 <= lt < 2^32 ->
      evt ssegs (leaf_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (Z_to_bv 64 (linktype_to_dlt lt)) m)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 LINKTYPE_TO_DLT_ENTRY) fc None m (seg_rom ssegs)).

  (* [comment removed for export] *)
  Definition max_snaplen_stmt : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (dlt : Z),
      a0 = Z_to_bv 64 dlt -> 0 <= dlt < 2^64 ->
      evt ssegs (leaf_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (Z_to_bv 64 (max_snaplen_for_dlt dlt)) m)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 MAX_SNAPLEN_ENTRY) fc None m (seg_rom ssegs)).

  (* [comment removed for export] *)
  Definition adjust_snapshot_stmt : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (lt snaplen : Z),
      a0 = Z_to_bv 64 lt -> 0 <= lt < 2^31 -> a1 = Z_to_bv 64 (s32 snaplen) -> 0 <= snaplen < 2^32 ->
      evt ssegs (leaf_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (Z_to_bv 64 (pcapint_adjust_snapshot lt snaplen)) m)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 PCAP_ADJUST_SNAPSHOT_ENTRY) fc None m (seg_rom ssegs)).

  (* [comment removed for export] *)
  Definition oneshot_stmt : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (U HD PKT SRC : Z) (pd w0 w1 w2 o0 o1 o2 : word) (pkc : cell),
      a0 = Z_to_bv 64 U -> a1 = Z_to_bv 64 SRC ->
      rw_cells ssegs m U [C8 (Z_to_bv 64 HD); C8 (Z_to_bv 64 PKT); C8 pd] ->
      rw_cells ssegs m SRC [C8 w0; C8 w1; C8 w2] ->
      rw_cells ssegs m HD [C8 o0; C8 o1; C8 o2] ->
      rw_cells ssegs m PKT [pkc] -> csize pkc = 8%nat ->
      (HD + 24 <= U \/ U + 24 <= HD) -> (HD + 24 <= SRC \/ SRC + 24 <= HD) -> (HD + 24 <= PKT \/ PKT + 8 <= HD) ->
      (PKT + 8 <= U \/ U + 24 <= PKT) -> (PKT + 8 <= SRC \/ SRC + 24 <= PKT) ->
      mem_inv ssegs m ->
      0 < U -> U mod 8 = 0 -> 0 < PKT -> PKT mod 8 = 0 ->      (* [comment removed for export] *)
      evt ssegs (fun ms' => exists t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m',
          ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                   F (ret_pc ra) fc None m' (seg_rom ssegs)
          /\ munch [(HD, HD + 24); (PKT, PKT + 8)] m m' /\ wmono ssegs m m' /\ mem_inv ssegs m'
          /\ rw_cells ssegs m' U [C8 (Z_to_bv 64 HD); C8 (Z_to_bv 64 PKT); C8 pd]
          /\ rw_cells ssegs m' SRC [C8 w0; C8 w1; C8 w2]
          /\ rw_cells ssegs m' HD [C8 w0; C8 w1; C8 w2]
          /\ rw_cells ssegs m' PKT [C8 a2])
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 (pk_oneshot PK)) fc None m (seg_rom ssegs)).

  (* [comment removed for export] *)
  Definition pcap_strerror_stmt : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (R : rctx) (s : PS) (CL FB : list cblk) (lo e : Z),
      SPO sp tp R s CL FB lo PCAP_L0_STACK m ->
      a0 = Z_to_bv 64 (s32 e) -> -2^31 <= e < 2^31 ->
      evt ssegs (fun ms' => exists t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m' rest,
          ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 tp a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                   F (ret_pc ra) fc None m' (seg_rom ssegs)
          /\ mem_inv ssegs m' /\ stk ssegs m' lo (bv_unsigned sp) /\ agrees_on (client_keeps CL (bv_unsigned sp)) m m'
          /\ GIO R s CL FB m'
          /\ rw_cells ssegs m' (bv_unsigned tp) [CB (length (Fmt.strerror e) + 1) (map b8 (Fmt.strerror e) ++ [Z_to_bv 8 0]);
                                                CB (255 - length (Fmt.strerror e)) rest])
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 PCAP_STRERROR_ENTRY) fc None m (seg_rom ssegs)).

  (* [comment removed for export] *)
  Definition fmt_errmsg_stmt : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (R : rctx) (s : PS) (CL FB : list cblk) (lo EB FMTA e : Z) (fs : string) (args : list farg)
           (junk : list byte),
      SPO sp tp R s CL FB lo PCAP_L1_STACK m ->
      a0 = Z_to_bv 64 EB -> a1 = Z_to_bv 64 256 -> a2 = Z_to_bv 64 (s32 e) -> -2^31 <= e < 2^31 -> a3 = Z_to_bv 64 FMTA ->
      fmt_at m FMTA fs -> fmt_ok fs args = true -> (length args <= 1)%nat -> Forall2 (farg_word R CL (bv_unsigned sp) EB 256 m) args (firstn (length args) [a4]) ->
      rw_cells ssegs m EB [CB 256 junk] -> client_range R CL (bv_unsigned sp) EB 256 -> EB mod 8 = 0 ->
      evt ssegs (fun ms' => exists t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m' junk',
          ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                   F (ret_pc ra) fc None m' (seg_rom ssegs)
          /\ mem_inv ssegs m' /\ stk ssegs m' lo (bv_unsigned sp)
          /\ agrees_on (fun a => client_keeps CL (bv_unsigned sp) a /\ ~ (EB <= a < EB + 256)) m m'
          /\ GIO R s CL FB m'
          /\ rw_cells ssegs m' EB [CB (length (fmt_errmsg fs args e) + 1) (map b8 (fmt_errmsg fs args e) ++ [Z_to_bv 8 0]);
                                  CB (255 - length (fmt_errmsg fs args e)) junk'])
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 PCAP_FMT_ERRMSG_ENTRY) fc None m (seg_rom ssegs)).

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition pcap_post {A} (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (R : rctx) (CLc : list cblk) (lo : Z) (m : mem)
      (X : A -> PS -> word -> mem -> list cblk -> list cblk -> Prop) : A -> PS -> machine_state -> Prop :=
    fun r s' ms' => exists a0v m' PB' FB', hpost_regs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0v m' ms'
      /\ mem_inv ssegs m' /\ stk ssegs m' lo (bv_unsigned sp) /\ agrees_on (client_keeps CLc (bv_unsigned sp)) m m'
      /\ GIO R s' (CLc ++ PB') FB' m' /\ X r s' a0v m' PB' FB'.

  (* [comment removed for export] *)
  Definition pcap_stats_stmt : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (R : rctx) (s : PS) (CLc PB FB : list cblk) (lo P : Z) (p : pcapT),
      SPO sp tp R s (CLc ++ PB) FB lo PCAP_L1_STACK m -> PCRC P p PB FB m -> a0 = Z_to_bv 64 P ->
      implM ssegs (Pcap.pcap_stats MOps p) s
        (pcap_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc R CLc lo m
           (fun r s' a0v m' PB' FB' => PB' = PB /\ FB' = FB /\ s' = s /\ a0v = Z_to_bv 64 (fst r) /\ fst r = -1 /\ PCRC P (snd r) PB FB m'))
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 PCAP_STATS_ENTRY) fc None m (seg_rom ssegs)).

  (* [comment removed for export] *)
  Definition next_packet_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (R : rctx) (CLc : list cblk) (FB : list cblk) (lo P HA DA : Z) (m : mem) (o : option hptr) : (Z * pkthdr * pcapT) -> PS -> machine_state -> Prop :=
    fun r s' ms' => let '(st, h, p') := r in
      exists a0v m' PB' (dw : cell), hpost_regs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0v m' ms'
      /\ ps_outfile s' = o /\ mem_inv ssegs m' /\ stk ssegs m' lo (bv_unsigned sp)
      /\ agrees_on (fun a => client_keeps CLc (bv_unsigned sp) a /\ ~ (HA <= a < HA + 24) /\ ~ (DA <= a < DA + 8)) m m'
      /\ GIO R s' (CLc ++ PB') FB m' /\ (st <> -1 -> PCR P p' PB' FB m') /\ (st = -1 -> PCRC P p' PB' FB m')
      /\ a0v = Z_to_bv 64 st /\ (st = 1 \/ st = 0 \/ st = -1)
      /\ (st = 1 -> rw_cells ssegs m' HA (hdr_cells h) /\ 0 <= h_caplen h < 2^32 /\ 0 <= h_len h < 2^32)
      /\ (st <> 1 -> exists hcs', cells_size hcs' = 24%nat /\ rw_cells ssegs m' HA hcs')
      /\ rw_cells ssegs m' DA [dw] /\ csize dw = 8%nat.

  Definition next_packet_op_stmt_for (ng : bool) : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (R : rctx) (s : PS) (CLc PB FB : list cblk) (lo P HA DA : Z) (p : pcapT) (fuel : nat)
           (hcs : list cell) (dc : cell),
      SPO sp tp R s (CLc ++ PB) FB lo PCAP_L2_STACK m -> PCR P p PB FB m -> is_ng p = ng ->
      sites = sites_at (bv_unsigned sp + D_NEXT_PACKET) ->
      a0 = Z_to_bv 64 P -> a1 = Z_to_bv 64 HA -> a2 = Z_to_bv 64 DA ->
      rw_cells ssegs m HA hcs -> cells_size hcs = 24%nat -> rw_cells ssegs m DA [dc] -> csize dc = 8%nat ->
      bv_unsigned sp <= HA -> HA + 24 <= DA -> DA + 8 <= rc_spmain R -> HA mod 8 = 0 -> DA mod 8 = 0 ->
      implM ssegs (next_packet_op MOps PR fuel p) s
        (next_packet_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc R CLc FB lo P HA DA m (ps_outfile s))
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 (np_entry p)) fc None m (seg_rom ssegs)).
  Definition pcap_next_packet_stmt : Prop := next_packet_op_stmt_for false.
  Definition pcap_ng_next_packet_stmt : Prop := next_packet_op_stmt_for true.

  (* [comment removed for export] *)
  Definition offline_read_stmt : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (R : rctx) (s : PS) (CLc PB FB : list cblk) (lo P U PKT : Z) (p : pcapT) (fuel : nat)
           (pd : word) (pkc : cell),
      SPO sp tp R s (CLc ++ PB) FB lo PCAP_L3_STACK m -> PCR P p PB FB m ->
      sites = sites_at (bv_unsigned sp + D_OFFLINE_READ) ->
      a0 = Z_to_bv 64 P -> a1 = Z_to_bv 64 1 -> a2 = Z_to_bv 64 (pk_oneshot PK) -> a3 = Z_to_bv 64 U ->
      rw_cells ssegs m U [C8 (Z_to_bv 64 (P + PCAP_HDR_OFF)); C8 (Z_to_bv 64 PKT); C8 pd] -> rw_cells ssegs m PKT [pkc] -> csize pkc = 8%nat ->
      bv_unsigned sp <= U -> U + 24 <= rc_spmain R -> bv_unsigned sp <= PKT -> PKT + 8 <= rc_spmain R -> (U + 24 <= PKT \/ PKT + 8 <= U) ->
      U mod 8 = 0 -> PKT mod 8 = 0 ->
      implM ssegs (pcapint_offline_read_1 MOps PR fuel p) s
        (fun r s' ms' => let '(st, p') := r in
           exists a0v m' PB' (pk' : cell), hpost_regs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0v m' ms'
           /\ ps_outfile s' = ps_outfile s /\ mem_inv ssegs m' /\ stk ssegs m' lo (bv_unsigned sp)
           /\ agrees_on (fun a => client_keeps CLc (bv_unsigned sp) a /\ ~ (PKT <= a < PKT + 8)) m m'
           /\ GIO R s' (CLc ++ PB') FB m' /\ (st <> -1 -> PCR P p' PB' FB m') /\ (st = -1 -> PCRC P p' PB' FB m')
           /\ a0v = Z_to_bv 64 st /\ (st = 1 \/ st = 0 \/ st = -1)
           /\ rw_cells ssegs m' U [C8 (Z_to_bv 64 (P + PCAP_HDR_OFF)); C8 (Z_to_bv 64 PKT); C8 pd]
           /\ rw_cells ssegs m' PKT [pk'] /\ csize pk' = 8%nat)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 PCAP_OFFLINE_READ_ENTRY) fc None m (seg_rom ssegs)).

  (* [comment removed for export] *)
  Definition pcap_next_ex_stmt : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (R : rctx) (s : PS) (CLc PB FB : list cblk) (lo P HP PKT : Z) (p : pcapT) (fuel : nat)
           (hc pkc : cell),
      SPO sp tp R s (CLc ++ PB) FB lo PCAP_L4_STACK m -> PCR P p PB FB m ->
      sites = sites_at (bv_unsigned sp + D_NEXT_EX) ->
      a0 = Z_to_bv 64 P -> a1 = Z_to_bv 64 HP -> a2 = Z_to_bv 64 PKT ->
      rw_cells ssegs m HP [hc] -> csize hc = 8%nat -> rw_cells ssegs m PKT [pkc] -> csize pkc = 8%nat ->
      bv_unsigned sp <= HP -> HP + 8 <= rc_spmain R -> bv_unsigned sp <= PKT -> PKT + 8 <= rc_spmain R -> (HP + 8 <= PKT \/ PKT + 8 <= HP) ->
      HP mod 8 = 0 -> PKT mod 8 = 0 ->
      implM ssegs (Pcap.pcap_next_ex MOps PR fuel p) s
        (fun r s' ms' => let '(st, p') := r in
           exists a0v m' PB' (pk' : cell), hpost_regs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0v m' ms'
           /\ ps_outfile s' = ps_outfile s /\ mem_inv ssegs m' /\ stk ssegs m' lo (bv_unsigned sp)
           /\ agrees_on (fun a => client_keeps CLc (bv_unsigned sp) a /\ ~ (HP <= a < HP + 8) /\ ~ (PKT <= a < PKT + 8)) m m'
           /\ GIO R s' (CLc ++ PB') FB m' /\ (st <> -1 -> PCR P p' PB' FB m') /\ (st = -1 -> PCRC P p' PB' FB m')
           /\ a0v = Z_to_bv 64 st /\ (st = 1 \/ st = -2 \/ st = -1)
           /\ rw_cells ssegs m' HP [C8 (Z_to_bv 64 (P + PCAP_HDR_OFF))]
           /\ rw_cells ssegs m' PKT [pk'] /\ csize pk' = 8%nat)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 PCAP_NEXT_EX_ENTRY) fc None m (seg_rom ssegs)).

  (* [comment removed for export] *)
  Definition cleanup_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (R : rctx) (CLc FB1 FB2 : list cblk) (lo P B Af : Z) (p : pcapT) (m : mem) (o : option hptr) : unit -> PS -> machine_state -> Prop :=
    fun _ s' ms' => exists a0v m' j', hpost_regs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0v m' ms'
      /\ ps_outfile s' = o /\ mem_inv ssegs m' /\ stk ssegs m' lo (bv_unsigned sp) /\ agrees_on (client_keeps CLc (bv_unsigned sp)) m m'
      /\ GIO R s' (CLc ++ [(pc_self p, P, psize p)]) (FB1 ++ FB2) m'
      /\ rw_cells ssegs m' P (pcap_cells p P B Af j').

  Definition sf_cleanup_stmt : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (R : rctx) (s : PS) (CLc FB1 FB2 : list cblk) (lo P B Af : Z) (p : pcapT) (j : pcap_junk),
      SPO sp tp R s (CLc ++ [(pc_self p, P, psize p); (pc_buffer p, B, pc_bufalloc p)]) (FB1 ++ (pc_rfile p, Af, FILE_BLOCK) :: FB2) lo PCAP_L3_STACK m ->
      rw_cells ssegs m P (pcap_cells p P B Af j) -> a0 = Z_to_bv 64 P -> ps_outfile s <> Some (pc_rfile p) ->
      implM ssegs (Pcap.pcapint_sf_cleanup MOps PR p) s
        (cleanup_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc R CLc FB1 FB2 lo P B Af p m (ps_outfile s))
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 (pk_cleanup_sf PK)) fc None m (seg_rom ssegs)).

  (* [comment removed for export] *)
  Definition ng_cleanup_stmt : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (R : rctx) (s : PS) (CLc PB FB : list cblk) (lo P : Z) (p : pcapT),
      SPO sp tp R s (CLc ++ PB) FB lo PCAP_L3_STACK m -> PCRC P p PB FB m -> is_ng p = true ->
      a0 = Z_to_bv 64 P -> ps_outfile s <> Some (pc_rfile p) ->
      implM ssegs (Pcap.pcap_ng_cleanup MOps PR p) s
        (fun u s' ms' => exists B Af FB1 FB2, FB = FB1 ++ (pc_rfile p, Af, FILE_BLOCK) :: FB2
           /\ cleanup_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc R CLc FB1 FB2 lo P B Af p m (ps_outfile s) u s' ms')
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 (pk_cleanup_ng PK)) fc None m (seg_rom ssegs)).

  (* [comment removed for export] *)
  Definition pcap_close_stmt : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (R : rctx) (s : PS) (CLc PB FB : list cblk) (lo P : Z) (p : pcapT),
      SPO sp tp R s (CLc ++ PB) FB lo PCAP_L4_STACK m -> PCRC P p PB FB m -> a0 = Z_to_bv 64 P -> ps_outfile s <> Some (pc_rfile p) ->
      implM ssegs (Pcap.pcap_close MOps PR p) s
        (pcap_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc R CLc lo m
           (fun _ s' a0v m' PB' FB' => ps_outfile s' = ps_outfile s /\ PB' = [] /\ exists F1 F2 Af, FB = F1 ++ (pc_rfile p, Af, FILE_BLOCK) :: F2 /\ FB' = F1 ++ F2))
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 PCAP_CLOSE_ENTRY) fc None m (seg_rom ssegs)).

  (* [comment removed for export] *)
  Definition open_common_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (R : rctx) (CL FB : list cblk) (lo EB total : Z) (ej : list byte) (m : mem) (o : option hptr) : ((list Z) + hptr) -> PS -> machine_state -> Prop :=
    fun r s' ms' => exists a0v m', hpost_regs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0v m' ms'
      /\ ps_outfile s' = o /\ mem_inv ssegs m' /\ stk ssegs m' lo (bv_unsigned sp)
      /\ agrees_on (fun a => client_keeps CL (bv_unsigned sp) a /\ ~ (EB <= a < EB + 256)) m m'
      /\ match r with
         | inl msg => exists junk', a0v = Z_to_bv 64 0 /\ GIO R s' CL FB m'
             /\ rw_cells ssegs m' EB [CB (length msg + 1) (map b8 msg ++ [Z_to_bv 8 0]); CB (255 - length msg) junk']
             /\ Z.of_nat (length msg) < 256 /\ Forall (fun z => 0 < z < 256) msg
         | inr q => exists P, a0v = Z_to_bv 64 P /\ GIO R s' ((q, P, total) :: CL) FB m'
             /\ rw_cells ssegs m' P ([CB 16 (repeat (Z_to_bv 8 0) 16); C4 (Z_to_bv 64 (-1)); CB 28 (repeat (Z_to_bv 8 0) 28);
                                     C8 (Z_to_bv 64 (P + PCAP_PRIV_OFF)); CB 128 (repeat (Z_to_bv 8 0) 128); C4 (Z_to_bv 64 (-1));
                                     CB (Z.to_nat (total - 188)) (repeat (Z_to_bv 8 0) (Z.to_nat (total - 188)))])
             /\ rw_cells ssegs m' EB [CB 256 ej]
         end.
  Definition open_offline_common_stmt : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (R : rctx) (s : PS) (CL FB : list cblk) (lo EB total : Z) (ej : list byte),
      SPO sp tp R s CL FB lo PCAP_L1B_STACK m ->
      a0 = Z_to_bv 64 EB -> a1 = Z_to_bv 64 total -> a2 = Z_to_bv 64 PCAP_PRIV_OFF -> (total = PCAP_SF_TOTAL \/ total = PCAP_NG_SF_TOTAL) ->
      rw_cells ssegs m EB [CB 256 ej] -> client_range R CL (bv_unsigned sp) EB 256 -> EB mod 8 = 0 ->
      implM ssegs (Pcap.pcapint_open_offline_common MOps PR total) s
        (open_common_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc R CL FB lo EB total ej m (ps_outfile s))
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 PCAP_OPEN_OFFLINE_COMMON_ENTRY) fc None m (seg_rom ssegs)).

  (* [comment removed for export] *)
  Definition check_header_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (R : rctx) (CL FB : list cblk) (lo MG EB ERR : Z) (magic : list Z) (f : hptr) (m : mem) (o : option hptr) : check_result -> PS -> machine_state -> Prop :=
    fun r s' ms' => exists a0v m' errw, hpost_regs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0v m' ms'
      /\ ps_outfile s' = o /\ mem_inv ssegs m' /\ stk ssegs m' lo (bv_unsigned sp)
      /\ agrees_on (fun a => client_keeps CL (bv_unsigned sp) a /\ ~ (EB <= a < EB + 256) /\ ~ (ERR <= a < ERR + 4)) m m'
      /\ rw_cells ssegs m' MG [CB 4 (map b8 magic)] /\ rw_cells ssegs m' ERR [C4 errw]
      /\ match r with
         | CH_NotMe => a0v = Z_to_bv 64 0 /\ errw = Z_to_bv 64 0 /\ GIO R s' CL FB m' /\ exists e, rw_cells ssegs m' EB [CB 256 e]
         | CH_Err msg => exists junk', a0v = Z_to_bv 64 0 /\ errw = Z_to_bv 64 1 /\ GIO R s' CL FB m'
             /\ rw_cells ssegs m' EB [CB (length msg + 1) (map b8 msg ++ [Z_to_bv 8 0]); CB (255 - length msg) junk'] /\ Z.of_nat (length msg) < 256
             /\ Forall (fun z => 0 < z < 256) msg
         | CH_Ok p => exists P PB, a0v = Z_to_bv 64 P /\ GIO R s' (CL ++ PB) FB m' /\ pre_PCAPR (hptr:=hptr) P p PB m' /\ pc_rfile p = f
             /\ (exists e, rw_cells ssegs m' EB [CB 256 e])
         end.

  (* [comment removed for export] *)
  Definition check_header_stmt_for (ng : bool) : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (R : rctx) (s : PS) (CL FB : list cblk) (lo MG FA EB ERR : Z) (f : hptr)
           (magic : list Z) (ej : list byte) (ec : cell) (fuel : nat),
      SPO sp tp R s CL FB lo PCAP_L2_STACK m -> In (f, FA, FILE_BLOCK) FB ->
      sites = sites_at (bv_unsigned sp + D_CHECK_HEADER) ->
      a0 = Z_to_bv 64 MG -> a1 = Z_to_bv 64 FA -> a2 = Z_to_bv 64 0 (* [comment removed for export] *) -> a3 = Z_to_bv 64 EB -> a4 = Z_to_bv 64 ERR ->
      rw_cells ssegs m MG [CB 4 (map b8 magic)] -> Forall (fun z => 0 <= z < 256) magic -> length magic = 4%nat ->
      rw_cells ssegs m EB [CB 256 ej] -> rw_cells ssegs m ERR [ec] -> csize ec = 4%nat ->
      bv_unsigned sp <= ERR -> ERR + 4 <= MG -> MG + 4 <= rc_spmain R ->            (* [comment removed for export] *)
      bv_unsigned sp <= EB -> EB + 256 <= rc_spmain R -> (EB + 256 <= ERR \/ MG + 4 <= EB) -> ERR mod 4 = 0 -> EB mod 8 = 0 ->
      implM ssegs ((if ng then Pcap.pcap_ng_check_header MOps PR fuel else Pcap.pcap_check_header MOps PR) magic f 0) s
        (check_header_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc R CL FB lo MG EB ERR magic f m (ps_outfile s))
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 (if ng then PCAP_NG_CHECK_HEADER_ENTRY else PCAP_CHECK_HEADER_ENTRY)) fc None m (seg_rom ssegs)).
  Definition pcap_check_header_stmt : Prop := check_header_stmt_for false.      (* [comment removed for export] *)
  Definition pcap_ng_check_header_stmt : Prop := check_header_stmt_for true.    (* [comment removed for export] *)

  (* [comment removed for export] *)
  Definition open_result_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (R : rctx) (CL : list cblk) (lo EB : Z) (m : mem) (o : option hptr)
      (keepFB : list cblk -> Prop)   (* [comment removed for export] *)
      (okFB : list cblk -> pcapT -> Prop)
      : ((list Z) + pcapT) -> PS -> machine_state -> Prop :=
    fun r s' ms' => exists a0v m' FB', hpost_regs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0v m' ms'
      /\ ps_outfile s' = o /\ mem_inv ssegs m' /\ stk ssegs m' lo (bv_unsigned sp)
      /\ agrees_on (fun a => client_keeps CL (bv_unsigned sp) a /\ ~ (EB <= a < EB + 256)) m m'
      /\ match r with
         | inl msg => exists junk', a0v = Z_to_bv 64 0 /\ keepFB FB' /\ GIO R s' CL FB' m'
             /\ rw_cells ssegs m' EB [CB (length msg + 1) (map b8 msg ++ [Z_to_bv 8 0]); CB (255 - length msg) junk'] /\ Z.of_nat (length msg) < 256
             /\ Forall (fun z => 0 < z < 256) msg
         | inr p => exists P PB, a0v = Z_to_bv 64 P /\ okFB FB' p /\ GIO R s' (CL ++ PB) FB' m' /\ PCR P p PB FB' m'
             /\ (exists e, rw_cells ssegs m' EB [CB 256 e])
         end.

  Definition fopen_offline_stmt : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (R : rctx) (s : PS) (CL FB : list cblk) (lo FA EB : Z) (f : hptr) (ej : list byte) (fuel : nat),
      SPO sp tp R s CL FB lo PCAP_L3_STACK m -> In (f, FA, FILE_BLOCK) FB ->
      sites = sites_at (bv_unsigned sp + D_FOPEN_OFFLINE) ->
      a0 = Z_to_bv 64 FA -> a1 = Z_to_bv 64 0 -> a2 = Z_to_bv 64 EB ->
      rw_cells ssegs m EB [CB 256 ej] -> bv_unsigned sp <= EB -> EB + 256 <= rc_spmain R -> EB mod 8 = 0 ->
      implM ssegs (Pcap.pcap_fopen_offline_with_tstamp_precision MOps PR fuel f 0) s
        (open_result_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc R CL lo EB m (ps_outfile s)
           (fun FB' => FB' = FB) (fun FB' p => FB' = FB /\ pc_rfile p = f))
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 PCAP_FOPEN_OFFLINE_WTP_ENTRY) fc None m (seg_rom ssegs)).

  (* [comment removed for export] *)
  Definition open_offline_stmt_at (ENTRY : Z) (a_err : word -> word -> word) : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (R : rctx) (s : PS) (CL FB : list cblk) (lo NAME EB : Z) (name slack ej : list byte) (fuel : nat),
      SPO sp tp R s CL FB lo PCAP_L4_STACK m ->
      sites = sites_at (bv_unsigned sp + D_OPEN_OFFLINE) ->
      a0 = Z_to_bv 64 NAME -> a_err a1 a2 = Z_to_bv 64 EB -> (ENTRY = PCAP_OPEN_OFFLINE_WTP_ENTRY -> a1 = Z_to_bv 64 0) ->
      bytes_at ssegs m NAME (name ++ Z_to_bv 8 0 :: slack) -> ~ In (Z_to_bv 8 0) name -> (1 <= length name <= 4095)%nat ->
      nth_error name 0 <> Some (Z_to_bv 8 45) ->
      open_name_ok false name ->   (* [comment removed for export] *)
      (- (NAME + Z.of_nat (length name) + 1)) mod 8 <= Z.of_nat (length slack) ->
      bv_unsigned sp <= NAME -> NAME + Z.of_nat (length name) + 1 + Z.of_nat (length slack) <= rc_spmain R ->
      rw_cells ssegs m EB [CB 256 ej] -> bv_unsigned sp <= EB -> EB + 256 <= rc_spmain R -> EB mod 8 = 0 ->
      (NAME + Z.of_nat (length name) + 1 + Z.of_nat (length slack) <= EB \/ EB + 256 <= NAME) ->
      implM ssegs (Pcap.pcap_open_offline MOps PR fuel (map bv_unsigned name)) s
        (open_result_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc R CL lo EB m (ps_outfile s)
           (fun FB' => FB' = FB) (fun FB' p => exists FA, FB' = (pc_rfile p, FA, FILE_BLOCK) :: FB))
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 ENTRY) fc None m (seg_rom ssegs)).
  Definition pcap_open_offline_stmt : Prop := open_offline_stmt_at PCAP_OPEN_OFFLINE_ENTRY (fun a1 _ => a1).
  Definition pcap_open_offline_wtp_stmt : Prop := open_offline_stmt_at PCAP_OPEN_OFFLINE_WTP_ENTRY (fun _ a2 => a2).

  (* [comment removed for export] *)
End Ifaces.

End WithCeil.

(* [comment removed for export] *)
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require ImgTgtUbsan.
From OSSVerify.libpcap.fuzz_pcap.images Require Ubsan.
Module TwB.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Strings.String.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Sem.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Tac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Arr OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Bytes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ITree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Nodes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Decode OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.SysStep OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ImgTgtUbsan.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Monad OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Fmt OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.StdioCore OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Stdio OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapPrelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapTypes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapPure OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Pcap OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prog.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.InitMem OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_kit__Musl.StartupKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.FileCells__Musl.FileCells.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.GI.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.GIFacts__S3.Ifaces.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.PcapRep.TwB.
Import OSSVerify.libpcap.fuzz_pcap.images.Ubsan.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Ceiling.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.LiaPin.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac lia_e2w2_base := first [ zify_prune; zify_noeuclid; Z.euclidean_division_equations_cleanup; xlia zchecker
                                 | zify_prune; Zify.zify; xlia zchecker | Zify.zify; xlia zchecker ].
Local Ltac ceil_mentioned := lazymatch goal with | |- context [@alloc_ceiling _] => idtac | _ : context [@alloc_ceiling _] |- _ => idtac end.
(* [comment removed for export] *)
Local Ltac lia ::= clear_unpinned; try (ceil_ok; ceil_mentioned; ceil_facts); pinned_lia_core.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section WithCeil.
Context {CEILV : CEIL}.
Definition CALLOC_ENTRY : Z := 0x18e14.
Definition REALLOC_ENTRY : Z := 0x1a8f8.
Definition FOPEN_ENTRY : Z := 0x1b84c.
Definition FCLOSE_ENTRY : Z := 0x1b314.
Definition FREAD_ENTRY : Z := 0x1bda8.
Definition FERROR_ENTRY : Z := 0x1b3e0.
Definition FILENO_ENTRY : Z := 0x1b7e0.
Definition VSNPRINTF_ENTRY : Z := 0x20d2c.
Definition SNPRINTF_ENTRY : Z := 0x1c26c.
Definition STRERROR_R_ENTRY : Z := 0x21734.
Definition STRLEN_ENTRY : Z := 0x217cc.
Definition MEMCPY_ENTRY : Z := 0x20fa0.
Definition ERRNO_LOCATION_ENTRY : Z := 0x1897c.
Definition STDIN_FILE : Z := 0x23f10.          (* [comment removed for export] *)
Definition GOT_STDIN : Z := 0x22db0.           (* [comment removed for export] *)
Definition STR_RB : Z := 0x108ab.              (* [comment removed for export] *)
Definition STR_PERCENT_S : Z := 0x107e7.       (* [comment removed for export] *)
Definition STR_STATS_NA : Z := 0x10e78.        (* [comment removed for export] *)

(* [comment removed for export] *)
Definition PCAP_L0_STACK : Z := 0x11000.   (* [comment removed for export] *)
Definition PCAP_L1_STACK : Z := 0x12000.   (* [comment removed for export] *)
Definition PCAP_L1B_STACK : Z := 0x13000.  (* [comment removed for export] *)
Definition PCAP_L2_STACK : Z := 0x14000.   (* [comment removed for export] *)
Definition PCAP_L3_STACK : Z := 0x16000.   (* [comment removed for export] *)
Definition PCAP_L4_STACK : Z := 0x18000.   (* [comment removed for export] *)

(* [comment removed for export] *)
Definition FUZZ_FRAME : Z := 4432.

(* [comment removed for export] *)
Definition sites_at (spB : Z) (site : stack_site) : Z :=
  match site with
  | SiteMagic => spB - 92                 (* [comment removed for export] *)
  | SitePcapHdrRest => spB - 188          (* [comment removed for export] *)
  | SiteSfHdr => spB - 208                (* [comment removed for export] *)
  | SiteDiscardBuf => spB - 4304          (* [comment removed for export] *)
  | SiteNgTotalLength => spB - 188        (* [comment removed for export] *)
  | SiteNgByteOrderMagic => spB - 192     (* [comment removed for export] *)
  | SiteBhdrCheckHeader => spB - 320      (* [comment removed for export] *)
  | SiteBhdrNextPacket => spB - 368       (* [comment removed for export] *)
  | SiteReadStage => 0x24149              (* [comment removed for export] *)
  end.
(* [comment removed for export] *)
Definition open_name_ok (wr : bool) (name : list byte) : Prop :=
  if wr then (Namei.path_has_slash name = false \/ name = Uapi.devnull_path)
  else (Namei.path_has_slash name = false /\ Fs.path_eqb name Namei.dotdot_path = false).

(* [comment removed for export] *)
Definition D_NEXT_EX : Z := 0.        Definition D_OFFLINE_READ : Z := 32.     Definition D_NEXT_PACKET : Z := 112.
Definition D_OPEN_OFFLINE : Z := 0.   Definition D_FOPEN_OFFLINE : Z := 48.    Definition D_CHECK_HEADER : Z := 96.
Definition D_READ_BLOCK_CH : Z := 224. Definition D_READ_BLOCK_NP : Z := 272.

Section Ifaces.
  Context {H hptr : Type} (HO : HeapOps H hptr) (K : modkit H hptr) (sites : stack_site -> Z).
  #[local] Abbreviation cblk := (@cblock hptr).
  #[local] Abbreviation PS := (PState H hptr).
  #[local] Abbreviation pcapT := (PcapTypes.pcap hptr hptr).
  #[local] Abbreviation PR := (prims HO fo_nop sites).
  #[local] Abbreviation GIO := (GIo K).
  #[local] Abbreviation SPO := (std_pre_o K).
  #[local] Abbreviation PCR := (@PCAPR hptr).
  #[local] Abbreviation PCRC := (@PCAPR_closable hptr).

  (* [comment removed for export] *)
  Definition client_range (R : rctx) (CL : list cblk) (SP A n : Z) : Prop :=
    (forall a, A <= a < A + n -> in_block CL a) \/ (SP <= A /\ A + n <= rc_spmain R).

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition hpost_regs (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (a0v : word) (m' : mem) (ms' : machine_state) : Prop :=
    exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6,
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0v a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (ret_pc ra) fc None m' (seg_rom usegs).

  (* [comment removed for export] *)
  Definition enomem_at (R : rctx) (s' : PS) (m' : mem) : Prop :=
    lc_errno (ps_libc s') = 12 /\ rw_cells usegs m' (utp R + -164) [C4 (Z_to_bv 64 12)].

  Definition malloc_stmt_o : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (R : rctx) (s : PS) (CL FB : list cblk) (lo n : Z),
      SPO sp tp R s CL FB lo MALLOC_STACK m -> a0 = Z_to_bv 64 n -> 0 <= n < 2^32 ->
      implM usegs (pmalloc HO n) s
        (fun r s' ms' => exists a0v m', hpost_regs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0v m' ms'
           /\ ps_outfile s' = ps_outfile s /\ mem_inv usegs m' /\ stk usegs m' lo (bv_unsigned sp) /\ agrees_on (client_keeps CL (bv_unsigned sp)) m m'
           /\ match r with
              | None => a0v = Z_to_bv 64 0 /\ GIO R s' CL FB m' /\ enomem_at R s' m'
              | Some q => exists A junk, a0v = Z_to_bv 64 A /\ GIO R s' ((q, A, n) :: CL) FB m'
                          /\ rw_cells usegs m' A [CB (Z.to_nat n) junk]
              end)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 MALLOC_ENTRY) fc None m (seg_rom usegs)).

  (* [comment removed for export] *)
  Definition calloc_stmt_o : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (R : rctx) (s : PS) (CL FB : list cblk) (lo cnt sz : Z),
      SPO sp tp R s CL FB lo MALLOC_STACK m -> a0 = Z_to_bv 64 cnt -> a1 = Z_to_bv 64 sz -> 0 <= cnt < 2^32 -> 0 <= sz < 2^32 -> cnt * sz <= 3260 ->
      implM usegs (pcalloc HO cnt sz) s
        (fun r s' ms' => exists a0v m', hpost_regs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0v m' ms'
           /\ ps_outfile s' = ps_outfile s /\ mem_inv usegs m' /\ stk usegs m' lo (bv_unsigned sp) /\ agrees_on (client_keeps CL (bv_unsigned sp)) m m'
           /\ match r with
              | None => a0v = Z_to_bv 64 0 /\ GIO R s' CL FB m' /\ enomem_at R s' m'
              | Some q => exists A, a0v = Z_to_bv 64 A /\ GIO R s' ((q, A, cnt * sz) :: CL) FB m'
                          /\ rw_cells usegs m' A [CB (Z.to_nat (cnt * sz)) (repeat (Z_to_bv 8 0) (Z.to_nat (cnt * sz)))]
              end)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 CALLOC_ENTRY) fc None m (seg_rom usegs)).

  (* [comment removed for export] *)
  Definition realloc_stmt_o : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (R : rctx) (s : PS) (C1 C2 FB : list cblk) (q : hptr) (A sz lo n : Z) (bs : list byte),
      SPO sp tp R s (C1 ++ (q, A, sz) :: C2) FB lo MALLOC_STACK m -> a0 = Z_to_bv 64 A -> a1 = Z_to_bv 64 n -> 0 <= n < 2^32 ->
      rw_cells usegs m A [CB (Z.to_nat sz) bs] ->
      implM usegs (prealloc HO q n) s
        (fun r s' ms' => exists a0v m', hpost_regs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0v m' ms'
           /\ ps_outfile s' = ps_outfile s /\ mem_inv usegs m' /\ stk usegs m' lo (bv_unsigned sp) /\ agrees_on (client_keeps (C1 ++ C2) (bv_unsigned sp)) m m'
           /\ match r with
              | None => a0v = Z_to_bv 64 0 /\ GIO R s' (C1 ++ (q, A, sz) :: C2) FB m' /\ rw_cells usegs m' A [CB (Z.to_nat sz) bs] /\ enomem_at R s' m'
              | Some q' => exists A' junk, a0v = Z_to_bv 64 A' /\ GIO R s' ((q', A', n) :: C1 ++ C2) FB m'
                          /\ rw_cells usegs m' A' [CB (Z.to_nat (Z.min sz n)) (firstn (Z.to_nat (Z.min sz n)) bs); CB (Z.to_nat (n - Z.min sz n)) junk]
              end)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 REALLOC_ENTRY) fc None m (seg_rom usegs)).

  Definition free_stmt_o : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (R : rctx) (s : PS) (C1 C2 FB : list cblk) (q : hptr) (A n lo : Z),
      SPO sp tp R s (C1 ++ (q, A, n) :: C2) FB lo FREE_STACK m -> a0 = Z_to_bv 64 A ->
      implM usegs (pfree HO q) s
        (fun _ s' ms' => exists a0v m', hpost_regs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0v m' ms'
           /\ ps_outfile s' = ps_outfile s /\ mem_inv usegs m' /\ stk usegs m' lo (bv_unsigned sp) /\ agrees_on (client_keeps (C1 ++ C2) (bv_unsigned sp)) m m'
           /\ GIO R s' (C1 ++ C2) FB m')
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 FREE_ENTRY) fc None m (seg_rom usegs)).

  (* [comment removed for export] *)

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition mode_ok (wr : bool) (md : list byte) : Prop :=
    if wr then (md = [Z_to_bv 8 119] \/ md = [Z_to_bv 8 119; Z_to_bv 8 98])     (* [comment removed for export] *)
    else (md = [Z_to_bv 8 114] \/ md = [Z_to_bv 8 114; Z_to_bv 8 98]).          (* [comment removed for export] *)

  (* [comment removed for export] *)
  Definition mode_lit (wr : bool) (MODE : Z) (md : list byte) : Prop :=
    if wr then (MODE = 0x10da2 /\ md = [Z_to_bv 8 119]) \/ (MODE = 0x10427 /\ md = [Z_to_bv 8 119; Z_to_bv 8 98])   (* [comment removed for export] *)
    else (MODE = STR_RB /\ md = [Z_to_bv 8 114; Z_to_bv 8 98]).                                                  (* [comment removed for export] *)

  (* [comment removed for export] *)
  Definition fopen_stmt_o : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (R : rctx) (s : PS) (CL FB : list cblk) (lo NAME MODE : Z) (name md : list byte) (wr : bool),
      SPO sp tp R s CL FB lo STDIO_STACK m -> a0 = Z_to_bv 64 NAME -> a1 = Z_to_bv 64 MODE ->
      bytes_at usegs m NAME (name ++ [Z_to_bv 8 0]) -> ~ In (Z_to_bv 8 0) name -> (1 <= length name <= 4095)%nat ->
      open_name_ok wr name ->   (* [comment removed for export] *)
      (client_range R CL (bv_unsigned sp) NAME (Z.of_nat (length name) + 1) \/ (0x10000 <= NAME /\ NAME + Z.of_nat (length name) + 1 <= 0x13000)) ->
      bytes_at usegs m MODE (md ++ [Z_to_bv 8 0]) -> mode_lit wr MODE md ->
      implM usegs (s_fopen HO (map bv_unsigned name) wr) s
        (fun r s' ms' => exists a0v m', hpost_regs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0v m' ms'
           /\ ps_outfile s' = ps_outfile s /\ mem_inv usegs m' /\ stk usegs m' lo (bv_unsigned sp) /\ agrees_on (client_keeps CL (bv_unsigned sp)) m m'
           /\ match r with
              | None => a0v = Z_to_bv 64 0 /\ GIO R s' CL FB m'
                        /\ rw_cells usegs m' (utp R + -164) [C4 (Z_to_bv 64 (lc_errno (ps_libc s')))]   (* [comment removed for export] *)
                        /\ 0 <= lc_errno (ps_libc s') < 2^31
              | Some f => exists Af, a0v = Z_to_bv 64 Af /\ GIO R s' CL ((f, Af, FILE_BLOCK) :: FB) m'
              end)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 FOPEN_ENTRY) fc None m (seg_rom usegs)).

  (* [comment removed for export] *)
  Definition fclose_stmt_o : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (R : rctx) (s : PS) (CL F1 F2 : list cblk) (f : hptr) (Af lo : Z),
      SPO sp tp R s CL (F1 ++ (f, Af, FILE_BLOCK) :: F2) lo STDIO_STACK m -> a0 = Z_to_bv 64 Af -> ps_outfile s <> Some f ->
      implM usegs (s_fclose HO f) s
        (fun _ s' ms' => exists a0v m', hpost_regs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0v m' ms'
           /\ ps_outfile s' = ps_outfile s /\ mem_inv usegs m' /\ stk usegs m' lo (bv_unsigned sp) /\ agrees_on (client_keeps CL (bv_unsigned sp)) m m'
           /\ GIO R s' CL (F1 ++ F2) m')
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 FCLOSE_ENTRY) fc None m (seg_rom usegs)).

  (* [comment removed for export] *)
  Definition fread_stmt_o : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (R : rctx) (s : PS) (CL FB : list cblk) (f : hptr) (Af D n lo : Z) (junk : list byte),
      SPO sp tp R s CL FB lo STDIO_STACK m -> In (f, Af, FILE_BLOCK) FB ->
      a0 = Z_to_bv 64 D -> a1 = Z_to_bv 64 1 -> a2 = Z_to_bv 64 n -> a3 = Z_to_bv 64 Af -> 0 <= n <= 2^30 ->
      rw_cells usegs m D [CB (Z.to_nat n) junk] -> client_range R CL (bv_unsigned sp) D n ->
      implM usegs (s_fread HO f D n) s
        (fun got s' ms' => exists a0v m' junk', hpost_regs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0v m' ms'
           /\ ps_outfile s' = ps_outfile s /\ mem_inv usegs m' /\ stk usegs m' lo (bv_unsigned sp)
           /\ agrees_on (fun a => client_keeps CL (bv_unsigned sp) a /\ ~ (D <= a < D + n)) m m'
           /\ GIO R s' CL FB m'
           /\ a0v = Z_to_bv 64 (zlength got) /\ 0 <= zlength got <= n /\ Forall (fun z => 0 <= z < 256) got
           /\ rw_cells usegs m' D [CB (length got) (map b8 got); CB (Z.to_nat n - length got) junk'])
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 FREAD_ENTRY) fc None m (seg_rom usegs)).

  (* [comment removed for export] *)
  Definition ferror_stmt_o : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (R : rctx) (s : PS) (CL FB : list cblk) (f : hptr) (Af lo : Z),
      SPO sp tp R s CL FB lo STDIO_STACK m -> In (f, Af, FILE_BLOCK) FB -> a0 = Z_to_bv 64 Af ->
      implM usegs (s_ferror HO f) s
        (fun r s' ms' => exists a0v m', hpost_regs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0v m' ms'
           /\ mem_inv usegs m' /\ stk usegs m' lo (bv_unsigned sp) /\ agrees_on (client_keeps CL (bv_unsigned sp)) m m'
           /\ GIO R s' CL FB m' /\ s' = s /\ a0v = Z_to_bv 64 (Z.b2z r)
           (* [comment removed for export] *)
           /\ (r = true -> rw_cells usegs m' (utp R + -164) [C4 (Z_to_bv 64 (lc_errno (ps_libc s')))] /\ 0 <= lc_errno (ps_libc s') < 2^31))
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 FERROR_ENTRY) fc None m (seg_rom usegs)).

  Definition fileno_stmt_o : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (R : rctx) (s : PS) (CL FB : list cblk) (f : hptr) (Af lo : Z),
      SPO sp tp R s CL FB lo STDIO_STACK m -> In (f, Af, FILE_BLOCK) FB -> a0 = Z_to_bv 64 Af ->
      implM usegs (s_fileno HO f) s
        (fun r s' ms' => exists a0v m', hpost_regs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0v m' ms'
           /\ mem_inv usegs m' /\ stk usegs m' lo (bv_unsigned sp) /\ agrees_on (client_keeps CL (bv_unsigned sp)) m m'
           /\ GIO R s' CL FB m' /\ s' = s /\ a0v = Z_to_bv 64 r /\ 0 <= r < 2^31)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 FILENO_ENTRY) fc None m (seg_rom usegs)).

  (* [comment removed for export] *)
  Definition fprintf_dd_stmt_o (FMT : Z) (mk : Z -> Z -> list (list Z)) : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (R : rctx) (s : PS) (CL FB : list cblk) (f : hptr) (Af lo v1 v2 : Z),
      SPO sp tp R s CL FB lo STDIO_STACK m -> In (f, Af, FILE_BLOCK) FB ->
      a0 = Z_to_bv 64 Af -> a1 = Z_to_bv 64 FMT -> a2 = sx32 (Z_to_bv 64 v1) -> a3 = sx32 (Z_to_bv 64 v2) -> 0 <= v1 < 2^32 -> 0 <= v2 < 2^32 ->
      implM usegs (s_fprintf HO f (mk v1 v2)) s
        (fun _ s' ms' => exists a0v m', hpost_regs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0v m' ms'
           /\ ps_outfile s' = ps_outfile s /\ mem_inv usegs m' /\ stk usegs m' lo (bv_unsigned sp) /\ agrees_on (client_keeps CL (bv_unsigned sp)) m m'
           /\ GIO R s' CL FB m')
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 FPRINTF_ENTRY) fc None m (seg_rom usegs)).

  Definition fprintf_s_stmt_o (FMT : Z) (mk : list Z -> list (list Z)) : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (R : rctx) (s : PS) (CL FB : list cblk) (f : hptr) (Af lo P : Z) (str slack : list byte),
      SPO sp tp R s CL FB lo STDIO_STACK m -> In (f, Af, FILE_BLOCK) FB ->
      a0 = Z_to_bv 64 Af -> a1 = Z_to_bv 64 FMT -> a2 = Z_to_bv 64 P ->
      bytes_at usegs m P (str ++ Z_to_bv 8 0 :: slack) -> ~ In (Z_to_bv 8 0) str -> Z.of_nat (length str) < 2^24 ->
      (- (P + Z.of_nat (length str) + 1)) mod 8 <= Z.of_nat (length slack) ->   (* [comment removed for export] *)
      client_range R CL (bv_unsigned sp) P (Z.of_nat (length str) + 1) ->
      implM usegs (s_fprintf HO f (mk (map bv_unsigned str))) s
        (fun _ s' ms' => exists a0v m', hpost_regs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0v m' ms'
           /\ ps_outfile s' = ps_outfile s /\ mem_inv usegs m' /\ stk usegs m' lo (bv_unsigned sp) /\ agrees_on (client_keeps CL (bv_unsigned sp)) m m'
           /\ GIO R s' CL FB m')
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 FPRINTF_ENTRY) fc None m (seg_rom usegs)).

  (* [comment removed for export] *)
  Definition fmt_at (m : mem) (FMTA : Z) (fs : string) : Prop :=
    bytes_at usegs m FMTA (map (fun c => Z_to_bv 8 (Z.of_nat (Ascii.nat_of_ascii c))) (String.list_ascii_of_string fs) ++ [Z_to_bv 8 0])
    /\ 0x10000 <= FMTA /\ FMTA + Z.of_nat (String.length fs) + 1 <= 0x13000.

  (* [comment removed for export] *)
  Definition conv_ok (c : conv) (a : farg) : bool :=
    match c, a with
    | Cs, AStr _ => true
    | Cd, AInt _ => true | Cu, AInt _ => true | Czu, AInt _ => true | C08x, AInt _ => true
    | _, _ => false
    end.
  Fixpoint items_ok (its : list fitem) (args : list farg) : bool :=
    match its with
    | [] => match args with [] => true | _ => false end
    | FLit l :: its' => forallb (fun c => negb (c =? 0) && negb (c =? 37)) l && items_ok its' args
    | FConv c :: its' => match args with a :: args' => conv_ok c a && items_ok its' args' | [] => false end
    | FBad _ :: _ => false
    end.
  Definition fmt_ok (fs : string) (args : list farg) : bool :=
    items_ok (fmt fs) args && (Z.of_nat (String.length fs) <? 4096).

  (* [comment removed for export] *)
  Definition farg_word (R : rctx) (CL : list cblk) (SP D dn : Z) (m : mem) (a : farg) (w : word) : Prop :=
    match a with
    | AInt z => w = Z_to_bv 64 z
    | AStr cs => exists P bs slack, w = Z_to_bv 64 P /\ bytes_at usegs m P (bs ++ Z_to_bv 8 0 :: slack) /\ ~ In (Z_to_bv 8 0) bs
                 /\ cs = map bv_unsigned bs /\ Z.of_nat (length bs) < 2^24
                 /\ (- (P + Z.of_nat (length bs) + 1)) mod 8 <= Z.of_nat (length slack)
                 /\ (P + Z.of_nat (length bs) + 1 + Z.of_nat (length slack) <= D \/ D + dn <= P)
                 /\ (client_range R CL SP P (Z.of_nat (length bs) + 1)
                     \/ ((0x10000 <= P /\ P + Z.of_nat (length bs) + 1 <= 0x13000)
                         \/ (utp R - 200 <= P /\ P + Z.of_nat (length bs) + 1 + Z.of_nat (length slack) <= utp R - 200 + 4096)))
    end.

  (* [comment removed for export] *)
  Definition snprintf_spec_stmt : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (R : rctx) (s : PS) (CL FB : list cblk) (lo DST n FMTA : Z) (fs : string) (args : list farg) (junk : list byte),
      SPO sp tp R s CL FB lo STDIO_STACK m ->
      a0 = Z_to_bv 64 DST -> a1 = Z_to_bv 64 n -> a2 = Z_to_bv 64 FMTA -> 1 <= n < 2^31 -> fmt_at m FMTA fs -> fmt_ok fs args = true ->
      (length args <= 3)%nat -> Forall2 (farg_word R CL (bv_unsigned sp) DST n m) args (firstn (length args) [a3; a4; a5]) ->
      rw_cells usegs m DST [CB (Z.to_nat n) junk] -> client_range R CL (bv_unsigned sp) DST n ->
      evt usegs (fun ms' => exists a0v m' junk', hpost_regs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0v m' ms'
           /\ munch [(bv_unsigned sp - STDIO_STACK, bv_unsigned sp); (DST, DST + n)] m m' /\ wmono usegs m m' /\ mem_inv usegs m'
           /\ stk usegs m' lo (bv_unsigned sp)
           /\ a0v = Z_to_bv 64 (snprintf_ret (fmt fs) args)
           /\ rw_cells usegs m' DST [CB (length (Fmt.snprintf n fs args) + 1) (map b8 (Fmt.snprintf n fs args) ++ [Z_to_bv 8 0]);
                                   CB (Z.to_nat n - length (Fmt.snprintf n fs args) - 1) junk'])
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 SNPRINTF_ENTRY) fc None m (seg_rom usegs)).

  (* [comment removed for export] *)
  Definition vsnprintf_spec_stmt : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (R : rctx) (s : PS) (CL FB : list cblk) (lo DST n FMTA AP : Z) (fs : string) (args : list farg)
           (ws : list word) (junk : list byte),
      SPO sp tp R s CL FB lo STDIO_STACK m ->
      a0 = Z_to_bv 64 DST -> a1 = Z_to_bv 64 n -> a2 = Z_to_bv 64 FMTA -> a3 = Z_to_bv 64 AP -> 1 <= n < 2^31 -> fmt_at m FMTA fs -> fmt_ok fs args = true ->
      length ws = length args -> Forall2 (farg_word R CL (bv_unsigned sp) DST n m) args ws ->
      rw_cells usegs m AP (map C8 ws) -> bv_unsigned sp <= AP -> AP + 8 * Z.of_nat (length ws) <= rc_spmain R ->
      (AP + 8 * Z.of_nat (length ws) <= DST \/ DST + n <= AP) ->
      rw_cells usegs m DST [CB (Z.to_nat n) junk] -> client_range R CL (bv_unsigned sp) DST n ->
      evt usegs (fun ms' => exists a0v m' junk', hpost_regs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0v m' ms'
           /\ munch [(bv_unsigned sp - STDIO_STACK, bv_unsigned sp); (DST, DST + n)] m m' /\ wmono usegs m m' /\ mem_inv usegs m'
           /\ stk usegs m' lo (bv_unsigned sp)
           /\ a0v = Z_to_bv 64 (snprintf_ret (fmt fs) args)
           /\ rw_cells usegs m' DST [CB (length (Fmt.snprintf n fs args) + 1) (map b8 (Fmt.snprintf n fs args) ++ [Z_to_bv 8 0]);
                                   CB (Z.to_nat n - length (Fmt.snprintf n fs args) - 1) junk'])
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 VSNPRINTF_ENTRY) fc None m (seg_rom usegs)).

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition leaf_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (v : word) (m : mem) : machine_state -> Prop :=
    fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6,
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (ret_pc ra) fc None m (seg_rom usegs)
      /\ a0 = v.

  (* [comment removed for export] *)
  Definition linktype_to_dlt_stmt : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (lt : Z),
      mem_inv usegs m -> a0 = Z_to_bv 64 lt -> 0 <= lt < 2^32 ->
      evt usegs (leaf_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (Z_to_bv 64 (linktype_to_dlt lt)) m)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 LINKTYPE_TO_DLT_ENTRY) fc None m (seg_rom usegs)).

  (* [comment removed for export] *)
  Definition max_snaplen_stmt : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (dlt : Z),
      a0 = Z_to_bv 64 dlt -> 0 <= dlt < 2^64 ->
      evt usegs (leaf_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (Z_to_bv 64 (max_snaplen_for_dlt dlt)) m)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 MAX_SNAPLEN_ENTRY) fc None m (seg_rom usegs)).

  (* [comment removed for export] *)
  Definition adjust_snapshot_stmt : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (lt snaplen : Z),
      a0 = Z_to_bv 64 lt -> 0 <= lt < 2^31 -> a1 = Z_to_bv 64 (s32 snaplen) -> 0 <= snaplen < 2^32 ->
      evt usegs (leaf_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (Z_to_bv 64 (pcapint_adjust_snapshot lt snaplen)) m)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 PCAP_ADJUST_SNAPSHOT_ENTRY) fc None m (seg_rom usegs)).

  (* [comment removed for export] *)
  Definition oneshot_stmt : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (U HD PKT SRC : Z) (pd w0 w1 w2 o0 o1 o2 : word) (pkc : cell),
      a0 = Z_to_bv 64 U -> a1 = Z_to_bv 64 SRC ->
      rw_cells usegs m U [C8 (Z_to_bv 64 HD); C8 (Z_to_bv 64 PKT); C8 pd] ->
      rw_cells usegs m SRC [C8 w0; C8 w1; C8 w2] ->
      rw_cells usegs m HD [C8 o0; C8 o1; C8 o2] ->
      rw_cells usegs m PKT [pkc] -> csize pkc = 8%nat ->
      (HD + 24 <= U \/ U + 24 <= HD) -> (HD + 24 <= SRC \/ SRC + 24 <= HD) -> (HD + 24 <= PKT \/ PKT + 8 <= HD) ->
      (PKT + 8 <= U \/ U + 24 <= PKT) -> (PKT + 8 <= SRC \/ SRC + 24 <= PKT) ->
      mem_inv usegs m ->
      0 < U -> U mod 8 = 0 -> 0 < PKT -> PKT mod 8 = 0 ->      (* [comment removed for export] *)
      evt usegs (fun ms' => exists t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m',
          ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                   F (ret_pc ra) fc None m' (seg_rom usegs)
          /\ munch [(HD, HD + 24); (PKT, PKT + 8)] m m' /\ wmono usegs m m' /\ mem_inv usegs m'
          /\ rw_cells usegs m' U [C8 (Z_to_bv 64 HD); C8 (Z_to_bv 64 PKT); C8 pd]
          /\ rw_cells usegs m' SRC [C8 w0; C8 w1; C8 w2]
          /\ rw_cells usegs m' HD [C8 w0; C8 w1; C8 w2]
          /\ rw_cells usegs m' PKT [C8 a2])
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 (pk_oneshot PK)) fc None m (seg_rom usegs)).

  (* [comment removed for export] *)
  Definition pcap_strerror_stmt : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (R : rctx) (s : PS) (CL FB : list cblk) (lo e : Z),
      SPO sp tp R s CL FB lo PCAP_L0_STACK m ->
      a0 = Z_to_bv 64 (s32 e) -> -2^31 <= e < 2^31 ->
      evt usegs (fun ms' => exists t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m' rest,
          ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 tp a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                   F (ret_pc ra) fc None m' (seg_rom usegs)
          /\ mem_inv usegs m' /\ stk usegs m' lo (bv_unsigned sp) /\ agrees_on (client_keeps CL (bv_unsigned sp)) m m'
          /\ GIO R s CL FB m'
          /\ rw_cells usegs m' (bv_unsigned tp) [CB (length (Fmt.strerror e) + 1) (map b8 (Fmt.strerror e) ++ [Z_to_bv 8 0]);
                                                CB (255 - length (Fmt.strerror e)) rest])
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 PCAP_STRERROR_ENTRY) fc None m (seg_rom usegs)).

  (* [comment removed for export] *)
  Definition fmt_errmsg_stmt : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (R : rctx) (s : PS) (CL FB : list cblk) (lo EB FMTA e : Z) (fs : string) (args : list farg)
           (junk : list byte),
      SPO sp tp R s CL FB lo PCAP_L1_STACK m ->
      a0 = Z_to_bv 64 EB -> a1 = Z_to_bv 64 256 -> a2 = Z_to_bv 64 (s32 e) -> -2^31 <= e < 2^31 -> a3 = Z_to_bv 64 FMTA ->
      fmt_at m FMTA fs -> fmt_ok fs args = true -> (length args <= 1)%nat -> Forall2 (farg_word R CL (bv_unsigned sp) EB 256 m) args (firstn (length args) [a4]) ->
      rw_cells usegs m EB [CB 256 junk] -> client_range R CL (bv_unsigned sp) EB 256 -> EB mod 8 = 0 ->
      evt usegs (fun ms' => exists t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m' junk',
          ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                   F (ret_pc ra) fc None m' (seg_rom usegs)
          /\ mem_inv usegs m' /\ stk usegs m' lo (bv_unsigned sp)
          /\ agrees_on (fun a => client_keeps CL (bv_unsigned sp) a /\ ~ (EB <= a < EB + 256)) m m'
          /\ GIO R s CL FB m'
          /\ rw_cells usegs m' EB [CB (length (fmt_errmsg fs args e) + 1) (map b8 (fmt_errmsg fs args e) ++ [Z_to_bv 8 0]);
                                  CB (255 - length (fmt_errmsg fs args e)) junk'])
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 PCAP_FMT_ERRMSG_ENTRY) fc None m (seg_rom usegs)).

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition pcap_post {A} (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (R : rctx) (CLc : list cblk) (lo : Z) (m : mem)
      (X : A -> PS -> word -> mem -> list cblk -> list cblk -> Prop) : A -> PS -> machine_state -> Prop :=
    fun r s' ms' => exists a0v m' PB' FB', hpost_regs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0v m' ms'
      /\ mem_inv usegs m' /\ stk usegs m' lo (bv_unsigned sp) /\ agrees_on (client_keeps CLc (bv_unsigned sp)) m m'
      /\ GIO R s' (CLc ++ PB') FB' m' /\ X r s' a0v m' PB' FB'.

  (* [comment removed for export] *)
  Definition pcap_stats_stmt : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (R : rctx) (s : PS) (CLc PB FB : list cblk) (lo P : Z) (p : pcapT),
      SPO sp tp R s (CLc ++ PB) FB lo PCAP_L1_STACK m -> PCRC P p PB FB m -> a0 = Z_to_bv 64 P ->
      implM usegs (Pcap.pcap_stats MOps p) s
        (pcap_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc R CLc lo m
           (fun r s' a0v m' PB' FB' => PB' = PB /\ FB' = FB /\ s' = s /\ a0v = Z_to_bv 64 (fst r) /\ fst r = -1 /\ PCRC P (snd r) PB FB m'))
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 PCAP_STATS_ENTRY) fc None m (seg_rom usegs)).

  (* [comment removed for export] *)
  Definition next_packet_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (R : rctx) (CLc : list cblk) (FB : list cblk) (lo P HA DA : Z) (m : mem) (o : option hptr) : (Z * pkthdr * pcapT) -> PS -> machine_state -> Prop :=
    fun r s' ms' => let '(st, h, p') := r in
      exists a0v m' PB' (dw : cell), hpost_regs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0v m' ms'
      /\ ps_outfile s' = o /\ mem_inv usegs m' /\ stk usegs m' lo (bv_unsigned sp)
      /\ agrees_on (fun a => client_keeps CLc (bv_unsigned sp) a /\ ~ (HA <= a < HA + 24) /\ ~ (DA <= a < DA + 8)) m m'
      /\ GIO R s' (CLc ++ PB') FB m' /\ (st <> -1 -> PCR P p' PB' FB m') /\ (st = -1 -> PCRC P p' PB' FB m')
      /\ a0v = Z_to_bv 64 st /\ (st = 1 \/ st = 0 \/ st = -1)
      /\ (st = 1 -> rw_cells usegs m' HA (hdr_cells h) /\ 0 <= h_caplen h < 2^32 /\ 0 <= h_len h < 2^32)
      /\ (st <> 1 -> exists hcs', cells_size hcs' = 24%nat /\ rw_cells usegs m' HA hcs')
      /\ rw_cells usegs m' DA [dw] /\ csize dw = 8%nat.

  Definition next_packet_op_stmt_for (ng : bool) : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (R : rctx) (s : PS) (CLc PB FB : list cblk) (lo P HA DA : Z) (p : pcapT) (fuel : nat)
           (hcs : list cell) (dc : cell),
      SPO sp tp R s (CLc ++ PB) FB lo PCAP_L2_STACK m -> PCR P p PB FB m -> is_ng p = ng ->
      sites = sites_at (bv_unsigned sp + D_NEXT_PACKET) ->
      a0 = Z_to_bv 64 P -> a1 = Z_to_bv 64 HA -> a2 = Z_to_bv 64 DA ->
      rw_cells usegs m HA hcs -> cells_size hcs = 24%nat -> rw_cells usegs m DA [dc] -> csize dc = 8%nat ->
      bv_unsigned sp <= HA -> HA + 24 <= DA -> DA + 8 <= rc_spmain R -> HA mod 8 = 0 -> DA mod 8 = 0 ->
      implM usegs (next_packet_op MOps PR fuel p) s
        (next_packet_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc R CLc FB lo P HA DA m (ps_outfile s))
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 (np_entry p)) fc None m (seg_rom usegs)).
  Definition pcap_next_packet_stmt : Prop := next_packet_op_stmt_for false.
  Definition pcap_ng_next_packet_stmt : Prop := next_packet_op_stmt_for true.

  (* [comment removed for export] *)
  Definition offline_read_stmt : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (R : rctx) (s : PS) (CLc PB FB : list cblk) (lo P U PKT : Z) (p : pcapT) (fuel : nat)
           (pd : word) (pkc : cell),
      SPO sp tp R s (CLc ++ PB) FB lo PCAP_L3_STACK m -> PCR P p PB FB m ->
      sites = sites_at (bv_unsigned sp + D_OFFLINE_READ) ->
      a0 = Z_to_bv 64 P -> a1 = Z_to_bv 64 1 -> a2 = Z_to_bv 64 (pk_oneshot PK) -> a3 = Z_to_bv 64 U ->
      rw_cells usegs m U [C8 (Z_to_bv 64 (P + PCAP_HDR_OFF)); C8 (Z_to_bv 64 PKT); C8 pd] -> rw_cells usegs m PKT [pkc] -> csize pkc = 8%nat ->
      bv_unsigned sp <= U -> U + 24 <= rc_spmain R -> bv_unsigned sp <= PKT -> PKT + 8 <= rc_spmain R -> (U + 24 <= PKT \/ PKT + 8 <= U) ->
      U mod 8 = 0 -> PKT mod 8 = 0 ->
      implM usegs (pcapint_offline_read_1 MOps PR fuel p) s
        (fun r s' ms' => let '(st, p') := r in
           exists a0v m' PB' (pk' : cell), hpost_regs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0v m' ms'
           /\ ps_outfile s' = ps_outfile s /\ mem_inv usegs m' /\ stk usegs m' lo (bv_unsigned sp)
           /\ agrees_on (fun a => client_keeps CLc (bv_unsigned sp) a /\ ~ (PKT <= a < PKT + 8)) m m'
           /\ GIO R s' (CLc ++ PB') FB m' /\ (st <> -1 -> PCR P p' PB' FB m') /\ (st = -1 -> PCRC P p' PB' FB m')
           /\ a0v = Z_to_bv 64 st /\ (st = 1 \/ st = 0 \/ st = -1)
           /\ rw_cells usegs m' U [C8 (Z_to_bv 64 (P + PCAP_HDR_OFF)); C8 (Z_to_bv 64 PKT); C8 pd]
           /\ rw_cells usegs m' PKT [pk'] /\ csize pk' = 8%nat)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 PCAP_OFFLINE_READ_ENTRY) fc None m (seg_rom usegs)).

  (* [comment removed for export] *)
  Definition pcap_next_ex_stmt : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (R : rctx) (s : PS) (CLc PB FB : list cblk) (lo P HP PKT : Z) (p : pcapT) (fuel : nat)
           (hc pkc : cell),
      SPO sp tp R s (CLc ++ PB) FB lo PCAP_L4_STACK m -> PCR P p PB FB m ->
      sites = sites_at (bv_unsigned sp + D_NEXT_EX) ->
      a0 = Z_to_bv 64 P -> a1 = Z_to_bv 64 HP -> a2 = Z_to_bv 64 PKT ->
      rw_cells usegs m HP [hc] -> csize hc = 8%nat -> rw_cells usegs m PKT [pkc] -> csize pkc = 8%nat ->
      bv_unsigned sp <= HP -> HP + 8 <= rc_spmain R -> bv_unsigned sp <= PKT -> PKT + 8 <= rc_spmain R -> (HP + 8 <= PKT \/ PKT + 8 <= HP) ->
      HP mod 8 = 0 -> PKT mod 8 = 0 ->
      implM usegs (Pcap.pcap_next_ex MOps PR fuel p) s
        (fun r s' ms' => let '(st, p') := r in
           exists a0v m' PB' (pk' : cell), hpost_regs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0v m' ms'
           /\ ps_outfile s' = ps_outfile s /\ mem_inv usegs m' /\ stk usegs m' lo (bv_unsigned sp)
           /\ agrees_on (fun a => client_keeps CLc (bv_unsigned sp) a /\ ~ (HP <= a < HP + 8) /\ ~ (PKT <= a < PKT + 8)) m m'
           /\ GIO R s' (CLc ++ PB') FB m' /\ (st <> -1 -> PCR P p' PB' FB m') /\ (st = -1 -> PCRC P p' PB' FB m')
           /\ a0v = Z_to_bv 64 st /\ (st = 1 \/ st = -2 \/ st = -1)
           /\ rw_cells usegs m' HP [C8 (Z_to_bv 64 (P + PCAP_HDR_OFF))]
           /\ rw_cells usegs m' PKT [pk'] /\ csize pk' = 8%nat)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 PCAP_NEXT_EX_ENTRY) fc None m (seg_rom usegs)).

  (* [comment removed for export] *)
  Definition cleanup_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (R : rctx) (CLc FB1 FB2 : list cblk) (lo P B Af : Z) (p : pcapT) (m : mem) (o : option hptr) : unit -> PS -> machine_state -> Prop :=
    fun _ s' ms' => exists a0v m' j', hpost_regs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0v m' ms'
      /\ ps_outfile s' = o /\ mem_inv usegs m' /\ stk usegs m' lo (bv_unsigned sp) /\ agrees_on (client_keeps CLc (bv_unsigned sp)) m m'
      /\ GIO R s' (CLc ++ [(pc_self p, P, psize p)]) (FB1 ++ FB2) m'
      /\ rw_cells usegs m' P (pcap_cells p P B Af j').

  Definition sf_cleanup_stmt : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (R : rctx) (s : PS) (CLc FB1 FB2 : list cblk) (lo P B Af : Z) (p : pcapT) (j : pcap_junk),
      SPO sp tp R s (CLc ++ [(pc_self p, P, psize p); (pc_buffer p, B, pc_bufalloc p)]) (FB1 ++ (pc_rfile p, Af, FILE_BLOCK) :: FB2) lo PCAP_L3_STACK m ->
      rw_cells usegs m P (pcap_cells p P B Af j) -> a0 = Z_to_bv 64 P -> ps_outfile s <> Some (pc_rfile p) ->
      implM usegs (Pcap.pcapint_sf_cleanup MOps PR p) s
        (cleanup_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc R CLc FB1 FB2 lo P B Af p m (ps_outfile s))
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 (pk_cleanup_sf PK)) fc None m (seg_rom usegs)).

  (* [comment removed for export] *)
  Definition ng_cleanup_stmt : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (R : rctx) (s : PS) (CLc PB FB : list cblk) (lo P : Z) (p : pcapT),
      SPO sp tp R s (CLc ++ PB) FB lo PCAP_L3_STACK m -> PCRC P p PB FB m -> is_ng p = true ->
      a0 = Z_to_bv 64 P -> ps_outfile s <> Some (pc_rfile p) ->
      implM usegs (Pcap.pcap_ng_cleanup MOps PR p) s
        (fun u s' ms' => exists B Af FB1 FB2, FB = FB1 ++ (pc_rfile p, Af, FILE_BLOCK) :: FB2
           /\ cleanup_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc R CLc FB1 FB2 lo P B Af p m (ps_outfile s) u s' ms')
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 (pk_cleanup_ng PK)) fc None m (seg_rom usegs)).

  (* [comment removed for export] *)
  Definition pcap_close_stmt : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (R : rctx) (s : PS) (CLc PB FB : list cblk) (lo P : Z) (p : pcapT),
      SPO sp tp R s (CLc ++ PB) FB lo PCAP_L4_STACK m -> PCRC P p PB FB m -> a0 = Z_to_bv 64 P -> ps_outfile s <> Some (pc_rfile p) ->
      implM usegs (Pcap.pcap_close MOps PR p) s
        (pcap_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc R CLc lo m
           (fun _ s' a0v m' PB' FB' => ps_outfile s' = ps_outfile s /\ PB' = [] /\ exists F1 F2 Af, FB = F1 ++ (pc_rfile p, Af, FILE_BLOCK) :: F2 /\ FB' = F1 ++ F2))
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 PCAP_CLOSE_ENTRY) fc None m (seg_rom usegs)).

  (* [comment removed for export] *)
  Definition open_common_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (R : rctx) (CL FB : list cblk) (lo EB total : Z) (ej : list byte) (m : mem) (o : option hptr) : ((list Z) + hptr) -> PS -> machine_state -> Prop :=
    fun r s' ms' => exists a0v m', hpost_regs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0v m' ms'
      /\ ps_outfile s' = o /\ mem_inv usegs m' /\ stk usegs m' lo (bv_unsigned sp)
      /\ agrees_on (fun a => client_keeps CL (bv_unsigned sp) a /\ ~ (EB <= a < EB + 256)) m m'
      /\ match r with
         | inl msg => exists junk', a0v = Z_to_bv 64 0 /\ GIO R s' CL FB m'
             /\ rw_cells usegs m' EB [CB (length msg + 1) (map b8 msg ++ [Z_to_bv 8 0]); CB (255 - length msg) junk']
             /\ Z.of_nat (length msg) < 256 /\ Forall (fun z => 0 < z < 256) msg
         | inr q => exists P, a0v = Z_to_bv 64 P /\ GIO R s' ((q, P, total) :: CL) FB m'
             /\ rw_cells usegs m' P ([CB 16 (repeat (Z_to_bv 8 0) 16); C4 (Z_to_bv 64 (-1)); CB 28 (repeat (Z_to_bv 8 0) 28);
                                     C8 (Z_to_bv 64 (P + PCAP_PRIV_OFF)); CB 128 (repeat (Z_to_bv 8 0) 128); C4 (Z_to_bv 64 (-1));
                                     CB (Z.to_nat (total - 188)) (repeat (Z_to_bv 8 0) (Z.to_nat (total - 188)))])
             /\ rw_cells usegs m' EB [CB 256 ej]
         end.
  Definition open_offline_common_stmt : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (R : rctx) (s : PS) (CL FB : list cblk) (lo EB total : Z) (ej : list byte),
      SPO sp tp R s CL FB lo PCAP_L1B_STACK m ->
      a0 = Z_to_bv 64 EB -> a1 = Z_to_bv 64 total -> a2 = Z_to_bv 64 PCAP_PRIV_OFF -> (total = PCAP_SF_TOTAL \/ total = PCAP_NG_SF_TOTAL) ->
      rw_cells usegs m EB [CB 256 ej] -> client_range R CL (bv_unsigned sp) EB 256 -> EB mod 8 = 0 ->
      implM usegs (Pcap.pcapint_open_offline_common MOps PR total) s
        (open_common_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc R CL FB lo EB total ej m (ps_outfile s))
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 PCAP_OPEN_OFFLINE_COMMON_ENTRY) fc None m (seg_rom usegs)).

  (* [comment removed for export] *)
  Definition check_header_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (R : rctx) (CL FB : list cblk) (lo MG EB ERR : Z) (magic : list Z) (f : hptr) (m : mem) (o : option hptr) : check_result -> PS -> machine_state -> Prop :=
    fun r s' ms' => exists a0v m' errw, hpost_regs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0v m' ms'
      /\ ps_outfile s' = o /\ mem_inv usegs m' /\ stk usegs m' lo (bv_unsigned sp)
      /\ agrees_on (fun a => client_keeps CL (bv_unsigned sp) a /\ ~ (EB <= a < EB + 256) /\ ~ (ERR <= a < ERR + 4)) m m'
      /\ rw_cells usegs m' MG [CB 4 (map b8 magic)] /\ rw_cells usegs m' ERR [C4 errw]
      /\ match r with
         | CH_NotMe => a0v = Z_to_bv 64 0 /\ errw = Z_to_bv 64 0 /\ GIO R s' CL FB m' /\ exists e, rw_cells usegs m' EB [CB 256 e]
         | CH_Err msg => exists junk', a0v = Z_to_bv 64 0 /\ errw = Z_to_bv 64 1 /\ GIO R s' CL FB m'
             /\ rw_cells usegs m' EB [CB (length msg + 1) (map b8 msg ++ [Z_to_bv 8 0]); CB (255 - length msg) junk'] /\ Z.of_nat (length msg) < 256
             /\ Forall (fun z => 0 < z < 256) msg
         | CH_Ok p => exists P PB, a0v = Z_to_bv 64 P /\ GIO R s' (CL ++ PB) FB m' /\ pre_PCAPR (hptr:=hptr) P p PB m' /\ pc_rfile p = f
             /\ (exists e, rw_cells usegs m' EB [CB 256 e])
         end.

  (* [comment removed for export] *)
  Definition check_header_stmt_for (ng : bool) : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (R : rctx) (s : PS) (CL FB : list cblk) (lo MG FA EB ERR : Z) (f : hptr)
           (magic : list Z) (ej : list byte) (ec : cell) (fuel : nat),
      SPO sp tp R s CL FB lo PCAP_L2_STACK m -> In (f, FA, FILE_BLOCK) FB ->
      sites = sites_at (bv_unsigned sp + D_CHECK_HEADER) ->
      a0 = Z_to_bv 64 MG -> a1 = Z_to_bv 64 FA -> a2 = Z_to_bv 64 0 (* [comment removed for export] *) -> a3 = Z_to_bv 64 EB -> a4 = Z_to_bv 64 ERR ->
      rw_cells usegs m MG [CB 4 (map b8 magic)] -> Forall (fun z => 0 <= z < 256) magic -> length magic = 4%nat ->
      rw_cells usegs m EB [CB 256 ej] -> rw_cells usegs m ERR [ec] -> csize ec = 4%nat ->
      bv_unsigned sp <= ERR -> ERR + 4 <= MG -> MG + 4 <= rc_spmain R ->            (* [comment removed for export] *)
      bv_unsigned sp <= EB -> EB + 256 <= rc_spmain R -> (EB + 256 <= ERR \/ MG + 4 <= EB) -> ERR mod 4 = 0 -> EB mod 8 = 0 ->
      implM usegs ((if ng then Pcap.pcap_ng_check_header MOps PR fuel else Pcap.pcap_check_header MOps PR) magic f 0) s
        (check_header_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc R CL FB lo MG EB ERR magic f m (ps_outfile s))
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 (if ng then PCAP_NG_CHECK_HEADER_ENTRY else PCAP_CHECK_HEADER_ENTRY)) fc None m (seg_rom usegs)).
  Definition pcap_check_header_stmt : Prop := check_header_stmt_for false.      (* [comment removed for export] *)
  Definition pcap_ng_check_header_stmt : Prop := check_header_stmt_for true.    (* [comment removed for export] *)

  (* [comment removed for export] *)
  Definition open_result_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (R : rctx) (CL : list cblk) (lo EB : Z) (m : mem) (o : option hptr)
      (keepFB : list cblk -> Prop)   (* [comment removed for export] *)
      (okFB : list cblk -> pcapT -> Prop)
      : ((list Z) + pcapT) -> PS -> machine_state -> Prop :=
    fun r s' ms' => exists a0v m' FB', hpost_regs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0v m' ms'
      /\ ps_outfile s' = o /\ mem_inv usegs m' /\ stk usegs m' lo (bv_unsigned sp)
      /\ agrees_on (fun a => client_keeps CL (bv_unsigned sp) a /\ ~ (EB <= a < EB + 256)) m m'
      /\ match r with
         | inl msg => exists junk', a0v = Z_to_bv 64 0 /\ keepFB FB' /\ GIO R s' CL FB' m'
             /\ rw_cells usegs m' EB [CB (length msg + 1) (map b8 msg ++ [Z_to_bv 8 0]); CB (255 - length msg) junk'] /\ Z.of_nat (length msg) < 256
             /\ Forall (fun z => 0 < z < 256) msg
         | inr p => exists P PB, a0v = Z_to_bv 64 P /\ okFB FB' p /\ GIO R s' (CL ++ PB) FB' m' /\ PCR P p PB FB' m'
             /\ (exists e, rw_cells usegs m' EB [CB 256 e])
         end.

  Definition fopen_offline_stmt : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (R : rctx) (s : PS) (CL FB : list cblk) (lo FA EB : Z) (f : hptr) (ej : list byte) (fuel : nat),
      SPO sp tp R s CL FB lo PCAP_L3_STACK m -> In (f, FA, FILE_BLOCK) FB ->
      sites = sites_at (bv_unsigned sp + D_FOPEN_OFFLINE) ->
      a0 = Z_to_bv 64 FA -> a1 = Z_to_bv 64 0 -> a2 = Z_to_bv 64 EB ->
      rw_cells usegs m EB [CB 256 ej] -> bv_unsigned sp <= EB -> EB + 256 <= rc_spmain R -> EB mod 8 = 0 ->
      implM usegs (Pcap.pcap_fopen_offline_with_tstamp_precision MOps PR fuel f 0) s
        (open_result_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc R CL lo EB m (ps_outfile s)
           (fun FB' => FB' = FB) (fun FB' p => FB' = FB /\ pc_rfile p = f))
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 PCAP_FOPEN_OFFLINE_WTP_ENTRY) fc None m (seg_rom usegs)).

  (* [comment removed for export] *)
  Definition open_offline_stmt_at (ENTRY : Z) (a_err : word -> word -> word) : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (R : rctx) (s : PS) (CL FB : list cblk) (lo NAME EB : Z) (name slack ej : list byte) (fuel : nat),
      SPO sp tp R s CL FB lo PCAP_L4_STACK m ->
      sites = sites_at (bv_unsigned sp + D_OPEN_OFFLINE) ->
      a0 = Z_to_bv 64 NAME -> a_err a1 a2 = Z_to_bv 64 EB -> (ENTRY = PCAP_OPEN_OFFLINE_WTP_ENTRY -> a1 = Z_to_bv 64 0) ->
      bytes_at usegs m NAME (name ++ Z_to_bv 8 0 :: slack) -> ~ In (Z_to_bv 8 0) name -> (1 <= length name <= 4095)%nat ->
      nth_error name 0 <> Some (Z_to_bv 8 45) ->
      open_name_ok false name ->   (* [comment removed for export] *)
      (- (NAME + Z.of_nat (length name) + 1)) mod 8 <= Z.of_nat (length slack) ->
      bv_unsigned sp <= NAME -> NAME + Z.of_nat (length name) + 1 + Z.of_nat (length slack) <= rc_spmain R ->
      rw_cells usegs m EB [CB 256 ej] -> bv_unsigned sp <= EB -> EB + 256 <= rc_spmain R -> EB mod 8 = 0 ->
      (NAME + Z.of_nat (length name) + 1 + Z.of_nat (length slack) <= EB \/ EB + 256 <= NAME) ->
      implM usegs (Pcap.pcap_open_offline MOps PR fuel (map bv_unsigned name)) s
        (open_result_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc R CL lo EB m (ps_outfile s)
           (fun FB' => FB' = FB) (fun FB' p => exists FA, FB' = (pc_rfile p, FA, FILE_BLOCK) :: FB))
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 ENTRY) fc None m (seg_rom usegs)).
  Definition pcap_open_offline_stmt : Prop := open_offline_stmt_at PCAP_OPEN_OFFLINE_ENTRY (fun a1 _ => a1).
  Definition pcap_open_offline_wtp_stmt : Prop := open_offline_stmt_at PCAP_OPEN_OFFLINE_WTP_ENTRY (fun _ a2 => a2).

  (* [comment removed for export] *)
End Ifaces.

End WithCeil.
End TwB.
End Pcap_iface.

(* [comment removed for export] *)
Module F_pcap_pure.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import Tac Bytes Image ITree Nodes SysStep ImgSrc3.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Import Prelim PcapPrelim PcapTypes PcapPure.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require Printf_kit__Musl. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_kit__Musl.StartupKit.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require PcapRep. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.PcapRep OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Pcap_iface__S3.Pcap_iface.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import Ceiling.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import LiaPin.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require SecDiet.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac lia_e2w2_base := first [ zify_prune; zify_noeuclid; Z.euclidean_division_equations_cleanup; xlia zchecker
                                 | zify_prune; Zify.zify; xlia zchecker | Zify.zify; xlia zchecker ].
Local Ltac ceil_mentioned := lazymatch goal with | |- context [@alloc_ceiling _] => idtac | _ : context [@alloc_ceiling _] |- _ => idtac end.
(* [comment removed for export] *)
Local Ltac lia ::= clear_unpinned; try (ceil_ok; ceil_mentioned; ceil_facts); pinned_lia_core.
Import ListNotations.
Open Scope bv_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section WithCeil.
Context {CEILV : CEIL}.
Definition max_snaplen_proof__stmt : Prop := max_snaplen_stmt.
Section Sz1.
Variables ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m dlt : ltac2:(SecDiet.SzSec.tyM 'max_snaplen_proof__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra).
Lemma max_snaplen_proof__body : ltac2:(SecDiet.SzSec.bodyP 'max_snaplen_proof__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
Proof using Type. pin_using tt.
 intros -> Hdlt.
  do 2 step. if_cases K; zify_cond K; rewrite ?unsigned_lit in K by lia.
  { do 2 step. finish. unfold max_snaplen_for_dlt, DLT_DBUS. subst dlt. reflexivity. }
  do 2 step. if_cases K2; zify_cond K2; rewrite ?unsigned_lit in K2 by lia.
  { do 2 step. finish. unfold max_snaplen_for_dlt, DLT_DBUS, DLT_USBPCAP, DLT_EBHSCR. subst dlt. reflexivity. }
  do 2 step. if_cases K3; zify_cond K3; rewrite ?unsigned_lit in K3 by lia.
  { do 2 step. finish. unfold max_snaplen_for_dlt, DLT_DBUS, DLT_USBPCAP, DLT_EBHSCR, MAXIMUM_SNAPLEN.
    rewrite (proj2 (Z.eqb_neq _ _) K), (proj2 (Z.eqb_neq _ _) K3), (proj2 (Z.eqb_neq _ _) K2). reflexivity. }
  do 2 step. finish. unfold max_snaplen_for_dlt, DLT_DBUS, DLT_USBPCAP, DLT_EBHSCR.
  rewrite (proj2 (Z.eqb_neq _ _) K), (proj2 (Z.eqb_neq _ _) K2), K3. reflexivity.
Qed.
End Sz1.
Theorem max_snaplen_proof : ltac:(let t := eval cbv delta [max_snaplen_proof__stmt] in max_snaplen_proof__stmt in exact t).
Proof using Type. red. intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m dlt. ltac2:(SecDiet.SzSec.closeP 'max_snaplen_proof__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma s32_cases : forall z, (0 <= z < 2^32)%Z ->
  (0 <= z < 2^31 /\ s32 z = z)%Z \/ (2^31 <= z < 2^32 /\ s32 z = z - 2^32)%Z.
Proof using Type. pin_using tt.
  intros z Hz. unfold s32.
  destruct (Z_lt_ge_dec z (2^31)).
  - left. split; [lia|]. rewrite Z.mod_small by lia. lia.
  - right. split; [lia|]. replace (z + 2^31)%Z with ((z - 2^31) + 1 * 2^32)%Z by lia.
    rewrite Z.mod_add by lia. rewrite Z.mod_small by lia. lia.
Qed.

Definition adjust_snapshot_proof__stmt : Prop := adjust_snapshot_stmt.
Section Sz3.
Variables ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lt snaplen : ltac2:(SecDiet.SzSec.tyM 'adjust_snapshot_proof__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra).
Lemma adjust_snapshot_proof__body : ltac2:(SecDiet.SzSec.bodyP 'adjust_snapshot_proof__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
Proof using Type. pin_using tt.
 intros -> Hlt -> Hsn. unfold PCAP_ADJUST_SNAPSHOT_ENTRY.
  destruct (s32_cases snaplen Hsn) as [[R1 E]|[R1 E]]; rewrite E.
  - (* [comment removed for export] *)
    step. if_cases K; zify_cond K; rewrite ?unsigned_lit in * by lia.
    + (* [comment removed for export] *)
      assert (snaplen = 0%Z).
      { apply andb_false_iff in K. destruct K as [K|K]; [apply Z.ltb_ge in K| apply Z.ltb_ge in K]; lia. }
      subst snaplen.
      step. eapply evt_mono; [eapply max_snaplen_proof; [reflexivity| lia]|].
      cbv beta. intros ms' PO. unfold leaf_post in *. destruct_exs PO. destruct PO as [-> ->].
      repeat (lazymatch goal with |- ex _ => eexists end). split; [reflexivity|]. reflexivity.
    + do 2 step. finish. unfold pcapint_adjust_snapshot, INT_MAX.
      replace (snaplen =? 0)%Z with false by (symmetry; apply Z.eqb_neq; lia).
      replace (2 ^ 31 - 1 <? snaplen)%Z with false by (symmetry; apply Z.ltb_ge; lia). reflexivity.
  - (* [comment removed for export] *)
    assert (U : bv_unsigned (Z_to_bv 64 (snaplen - 2 ^ 32)) = (2^64 + (snaplen - 2^32))%Z).
    { rewrite unsigned_lit_wrap. replace (snaplen - 2^32)%Z with ((2^64 + (snaplen - 2^32)) + (-1) * 2^64)%Z at 1 by lia.
      rewrite Z.mod_add by lia. apply Z.mod_small. lia. }
    step. if_cases K; zify_cond K; rewrite ?U, ?unsigned_lit_wrap in *.
    + step. eapply evt_mono; [eapply max_snaplen_proof; [reflexivity| lia]|].
      cbv beta. intros ms' PO. unfold leaf_post in *. destruct_exs PO. destruct PO as [-> ->].
      repeat (lazymatch goal with |- ex _ => eexists end). split; [reflexivity|].
      unfold pcapint_adjust_snapshot, INT_MAX. replace (2 ^ 31 - 1 <? snaplen)%Z with true by (symmetry; apply Z.ltb_lt; lia).
      rewrite orb_true_r. reflexivity.
    + exfalso.
      assert (EM : ((snaplen - 4294967296) mod 18446744073709551616 = 18446744073709551616 + (snaplen - 4294967296))%Z).
      { replace (snaplen - 4294967296)%Z with ((18446744073709551616 + (snaplen - 4294967296)) + (-1) * 18446744073709551616)%Z at 1 by lia.
        rewrite Z.mod_add by lia. apply Z.mod_small. lia. }
      rewrite EM in *. lia.
Qed.
End Sz3.
Theorem adjust_snapshot_proof : ltac:(let t := eval cbv delta [adjust_snapshot_proof__stmt] in adjust_snapshot_proof__stmt in exact t).
Proof using Type. red. intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lt snaplen. ltac2:(SecDiet.SzSec.closeP 'adjust_snapshot_proof__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition lt_tab : list byte := [11; 0; 0; 0; 12; 0; 0; 0; 15; 0; 0; 0; 16; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 19; 0; 0; 0].

Lemma swrap32_range_neg : forall x, (-2^31 <= x < 0)%Z -> bv_unsigned (Z_to_bv 64 (bv_swrap 32 x)) = (2^64 + x)%Z.
Proof using Type. pin_using tt.
  intros x Hx. rewrite swrap32_small by lia. rewrite unsigned_lit_wrap.
  replace x with ((2^64 + x) + (-1) * 2^64)%Z at 1 by lia. rewrite Z.mod_add by lia. apply Z.mod_small. lia.
Qed.

Lemma swrap32_mid : forall x, (2^31 <= x < 2^32 + 2^31)%Z -> bv_swrap 32 x = (x - 2^32)%Z.
Proof using Type. pin_using tt.
  intros x Hx. unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus.
  change (2 ^ Z.of_N 32)%Z with (2^32)%Z. change (2 ^ 32 `div` 2)%Z with (2^31)%Z.
  replace (x + 2^31)%Z with ((x + 2^31 - 2^32) + 1 * 2^32)%Z by lia. rewrite Z.mod_add by lia. rewrite Z.mod_small by lia. lia.
Qed.

(* [comment removed for export] *)
Definition lt_out_of_table__stmt : Prop := forall lt, (11 <= lt < 2^32)%Z -> (lt < 100 \/ 107 <= lt)%Z ->
  bv_ltu (Z_to_bv 64 6) (Z_to_bv 64 (bv_swrap 32 (lt + -100))) = true.
Section Sz6.
Variables lt : ltac2:(SecDiet.SzSec.tyM 'lt_out_of_table__stmt "v" @lt).
Lemma lt_out_of_table__body : ltac2:(SecDiet.SzSec.bodyP 'lt_out_of_table__stmt "v").
Proof using Type. pin_using tt.
  intros H1 H2.
 unfold bv_ltu. rewrite (unsigned_lit 6) by lia. apply Z.ltb_lt.
  destruct (Z_lt_ge_dec lt 100).
  - rewrite swrap32_range_neg by lia. lia.
  - destruct (Z_lt_ge_dec lt (2^31 + 100)).
    + rewrite swrap32_small by lia. rewrite unsigned_lit by lia. lia.
    + rewrite swrap32_mid by lia. rewrite unsigned_lit_wrap.
      replace (lt + -100 - 2^32)%Z with ((2^64 + (lt - 100 - 2^32)) + (-1) * 2^64)%Z by lia.
      rewrite Z.mod_add by lia. rewrite Z.mod_small by lia. lia.
Qed.
End Sz6.
Lemma lt_out_of_table : ltac:(let t := eval cbv delta [lt_out_of_table__stmt] in lt_out_of_table__stmt in exact t).
Proof using Type. intros lt. ltac2:(SecDiet.SzSec.closeP 'lt_out_of_table__body "v"). Qed.

Definition linktype_to_dlt_proof__stmt : Prop := linktype_to_dlt_stmt.
Section Sz7.
Variables ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lt : ltac2:(SecDiet.SzSec.tyM 'linktype_to_dlt_proof__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra).
Lemma linktype_to_dlt_proof__body : ltac2:(SecDiet.SzSec.bodyP 'linktype_to_dlt_proof__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
Proof using Type. pin_using tt.
  intros MI -> Hlt.
 unfold LINKTYPE_TO_DLT_ENTRY.
  assert (TAB : ro_cells ssegs m 0x11194 [CB 28 lt_tab]).
  { apply (ro_cells_image ssegs m); [exact MI | vm_compute; reflexivity | lia | cbn; lia]. }
  assert (CASES : (lt < 11 \/ (11 <= lt /\ (lt < 100 \/ 107 <= lt))
                   \/ lt = 100 \/ lt = 101 \/ lt = 102 \/ lt = 103 \/ lt = 104 \/ lt = 105 \/ lt = 106)%Z) by lia.
  destruct CASES as [C|[C|[->|[->|[->|[->|[->|[->| ->]]]]]]]].
  - (* [comment removed for export] *)
    step. step. if_cases K; zify_cond K; rewrite ?unsigned_lit in * by lia; [|exfalso; lia].
    step. finish. unfold linktype_to_dlt.
    rewrite !(proj2 (Z.eqb_neq _ _)) by lia. reflexivity.
  - (* [comment removed for export] *)
    step. step. if_cases K; zify_cond K; rewrite ?unsigned_lit in * by lia; [exfalso; lia|].
    step. step. step. rewrite (unsigned_lit lt) by lia. if_true_by (lt_out_of_table lt ltac:(lia) ltac:(lia)).
    step. finish. unfold linktype_to_dlt. rewrite !(proj2 (Z.eqb_neq _ _)) by lia. reflexivity.
  - do 15 astep. finish. vm_compute. reflexivity.
  - do 15 astep. finish. vm_compute. reflexivity.
  - do 15 astep. finish. vm_compute. reflexivity.
  - do 15 astep. finish. vm_compute. reflexivity.
  - do 10 astep. finish. reflexivity.
  - do 10 astep. finish. reflexivity.
  - do 15 astep. finish. vm_compute. reflexivity.
Qed.
End Sz7.
Theorem linktype_to_dlt_proof : ltac:(let t := eval cbv delta [linktype_to_dlt_proof__stmt] in linktype_to_dlt_proof__stmt in exact t).
Proof using Type. red. intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lt. ltac2:(SecDiet.SzSec.closeP 'linktype_to_dlt_proof__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.

End WithCeil.

(* [comment removed for export] *)
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require ImgTgtUbsan.
Module TwB.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Tac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Bytes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Image OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ITree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Nodes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.SysStep OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ImgTgtUbsan.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapPrelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapTypes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapPure.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_kit__Musl.StartupKit.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.PcapRep.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Pcap_iface__S3.Pcap_iface.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Ceiling.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.LiaPin.
(* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac lia_e2w2_base := first [ zify_prune; zify_noeuclid; Z.euclidean_division_equations_cleanup; xlia zchecker
                                 | zify_prune; Zify.zify; xlia zchecker | Zify.zify; xlia zchecker ].
Local Ltac ceil_mentioned := lazymatch goal with | |- context [@alloc_ceiling _] => idtac | _ : context [@alloc_ceiling _] |- _ => idtac end.
(* [comment removed for export] *)
Local Ltac lia ::= clear_unpinned; try (ceil_ok; ceil_mentioned; ceil_facts); pinned_lia_core.
Import ListNotations.
Open Scope bv_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section WithCeil.
Context {CEILV : CEIL}.
Definition max_snaplen_proof__stmt : Prop := max_snaplen_stmt.
Section Sz1.
Variables ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m dlt : ltac2:(SecDiet.SzSec.tyM 'max_snaplen_proof__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra).
Lemma max_snaplen_proof__body : ltac2:(SecDiet.SzSec.bodyP 'max_snaplen_proof__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
Proof using Type. pin_using tt.
 intros -> Hdlt.
  do 2 step. if_cases K; zify_cond K; rewrite ?unsigned_lit in K by lia.
  { do 2 step. finish. unfold max_snaplen_for_dlt, DLT_DBUS. subst dlt. reflexivity. }
  do 2 step. if_cases K2; zify_cond K2; rewrite ?unsigned_lit in K2 by lia.
  { do 2 step. finish. unfold max_snaplen_for_dlt, DLT_DBUS, DLT_USBPCAP, DLT_EBHSCR. subst dlt. reflexivity. }
  do 2 step. if_cases K3; zify_cond K3; rewrite ?unsigned_lit in K3 by lia.
  { do 2 step. finish. unfold max_snaplen_for_dlt, DLT_DBUS, DLT_USBPCAP, DLT_EBHSCR, MAXIMUM_SNAPLEN.
    rewrite (proj2 (Z.eqb_neq _ _) K), (proj2 (Z.eqb_neq _ _) K3), (proj2 (Z.eqb_neq _ _) K2). reflexivity. }
  do 2 step. finish. unfold max_snaplen_for_dlt, DLT_DBUS, DLT_USBPCAP, DLT_EBHSCR.
  rewrite (proj2 (Z.eqb_neq _ _) K), (proj2 (Z.eqb_neq _ _) K2), K3. reflexivity.
Qed.
End Sz1.
Theorem max_snaplen_proof : ltac:(let t := eval cbv delta [max_snaplen_proof__stmt] in max_snaplen_proof__stmt in exact t).
Proof using Type. red. intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m dlt. ltac2:(SecDiet.SzSec.closeP 'max_snaplen_proof__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma s32_cases : forall z, (0 <= z < 2^32)%Z ->
  (0 <= z < 2^31 /\ s32 z = z)%Z \/ (2^31 <= z < 2^32 /\ s32 z = z - 2^32)%Z.
Proof using Type. pin_using tt.
  intros z Hz. unfold s32.
  destruct (Z_lt_ge_dec z (2^31)).
  - left. split; [lia|]. rewrite Z.mod_small by lia. lia.
  - right. split; [lia|]. replace (z + 2^31)%Z with ((z - 2^31) + 1 * 2^32)%Z by lia.
    rewrite Z.mod_add by lia. rewrite Z.mod_small by lia. lia.
Qed.

Definition adjust_snapshot_proof__stmt : Prop := adjust_snapshot_stmt.
Section Sz3.
Variables ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lt snaplen : ltac2:(SecDiet.SzSec.tyM 'adjust_snapshot_proof__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra).
Lemma adjust_snapshot_proof__body : ltac2:(SecDiet.SzSec.bodyP 'adjust_snapshot_proof__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
Proof using Type. pin_using tt.
 intros -> Hlt -> Hsn. unfold PCAP_ADJUST_SNAPSHOT_ENTRY.
  destruct (s32_cases snaplen Hsn) as [[R1 E]|[R1 E]]; rewrite E.
  - (* [comment removed for export] *)
    step. if_cases K; zify_cond K; rewrite ?unsigned_lit in * by lia.
    + (* [comment removed for export] *)
      assert (snaplen = 0%Z).
      { apply andb_false_iff in K. destruct K as [K|K]; [apply Z.ltb_ge in K| apply Z.ltb_ge in K]; lia. }
      subst snaplen.
      step. eapply evt_mono; [eapply max_snaplen_proof; [reflexivity| lia]|].
      cbv beta. intros ms' PO. unfold leaf_post in *. destruct_exs PO. destruct PO as [-> ->].
      repeat (lazymatch goal with |- ex _ => eexists end). split; [reflexivity|]. reflexivity.
    + do 2 step. finish. unfold pcapint_adjust_snapshot, INT_MAX.
      replace (snaplen =? 0)%Z with false by (symmetry; apply Z.eqb_neq; lia).
      replace (2 ^ 31 - 1 <? snaplen)%Z with false by (symmetry; apply Z.ltb_ge; lia). reflexivity.
  - (* [comment removed for export] *)
    assert (U : bv_unsigned (Z_to_bv 64 (snaplen - 2 ^ 32)) = (2^64 + (snaplen - 2^32))%Z).
    { rewrite unsigned_lit_wrap. replace (snaplen - 2^32)%Z with ((2^64 + (snaplen - 2^32)) + (-1) * 2^64)%Z at 1 by lia.
      rewrite Z.mod_add by lia. apply Z.mod_small. lia. }
    step. if_cases K; zify_cond K; rewrite ?U, ?unsigned_lit_wrap in *.
    + step. eapply evt_mono; [eapply max_snaplen_proof; [reflexivity| lia]|].
      cbv beta. intros ms' PO. unfold leaf_post in *. destruct_exs PO. destruct PO as [-> ->].
      repeat (lazymatch goal with |- ex _ => eexists end). split; [reflexivity|].
      unfold pcapint_adjust_snapshot, INT_MAX. replace (2 ^ 31 - 1 <? snaplen)%Z with true by (symmetry; apply Z.ltb_lt; lia).
      rewrite orb_true_r. reflexivity.
    + exfalso.
      assert (EM : ((snaplen - 4294967296) mod 18446744073709551616 = 18446744073709551616 + (snaplen - 4294967296))%Z).
      { replace (snaplen - 4294967296)%Z with ((18446744073709551616 + (snaplen - 4294967296)) + (-1) * 18446744073709551616)%Z at 1 by lia.
        rewrite Z.mod_add by lia. apply Z.mod_small. lia. }
      rewrite EM in *. lia.
Qed.
End Sz3.
Theorem adjust_snapshot_proof : ltac:(let t := eval cbv delta [adjust_snapshot_proof__stmt] in adjust_snapshot_proof__stmt in exact t).
Proof using Type. red. intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lt snaplen. ltac2:(SecDiet.SzSec.closeP 'adjust_snapshot_proof__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition lt_tab : list byte := [11; 0; 0; 0; 12; 0; 0; 0; 15; 0; 0; 0; 16; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 19; 0; 0; 0].

Lemma swrap32_range_neg : forall x, (-2^31 <= x < 0)%Z -> bv_unsigned (Z_to_bv 64 (bv_swrap 32 x)) = (2^64 + x)%Z.
Proof using Type. pin_using tt.
  intros x Hx. rewrite swrap32_small by lia. rewrite unsigned_lit_wrap.
  replace x with ((2^64 + x) + (-1) * 2^64)%Z at 1 by lia. rewrite Z.mod_add by lia. apply Z.mod_small. lia.
Qed.

Lemma swrap32_mid : forall x, (2^31 <= x < 2^32 + 2^31)%Z -> bv_swrap 32 x = (x - 2^32)%Z.
Proof using Type. pin_using tt.
  intros x Hx. unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus.
  change (2 ^ Z.of_N 32)%Z with (2^32)%Z. change (2 ^ 32 `div` 2)%Z with (2^31)%Z.
  replace (x + 2^31)%Z with ((x + 2^31 - 2^32) + 1 * 2^32)%Z by lia. rewrite Z.mod_add by lia. rewrite Z.mod_small by lia. lia.
Qed.

(* [comment removed for export] *)
Definition lt_out_of_table__stmt : Prop := forall lt, (11 <= lt < 2^32)%Z -> (lt < 100 \/ 107 <= lt)%Z ->
  bv_ltu (Z_to_bv 64 6) (Z_to_bv 64 (bv_swrap 32 (lt + -100))) = true.
Section Sz6.
Variables lt : ltac2:(SecDiet.SzSec.tyM 'lt_out_of_table__stmt "v" @lt).
Lemma lt_out_of_table__body : ltac2:(SecDiet.SzSec.bodyP 'lt_out_of_table__stmt "v").
Proof using Type. pin_using tt.
  intros H1 H2.
 unfold bv_ltu. rewrite (unsigned_lit 6) by lia. apply Z.ltb_lt.
  destruct (Z_lt_ge_dec lt 100).
  - rewrite swrap32_range_neg by lia. lia.
  - destruct (Z_lt_ge_dec lt (2^31 + 100)).
    + rewrite swrap32_small by lia. rewrite unsigned_lit by lia. lia.
    + rewrite swrap32_mid by lia. rewrite unsigned_lit_wrap.
      replace (lt + -100 - 2^32)%Z with ((2^64 + (lt - 100 - 2^32)) + (-1) * 2^64)%Z by lia.
      rewrite Z.mod_add by lia. rewrite Z.mod_small by lia. lia.
Qed.
End Sz6.
Lemma lt_out_of_table : ltac:(let t := eval cbv delta [lt_out_of_table__stmt] in lt_out_of_table__stmt in exact t).
Proof using Type. intros lt. ltac2:(SecDiet.SzSec.closeP 'lt_out_of_table__body "v"). Qed.

Definition linktype_to_dlt_proof__stmt : Prop := linktype_to_dlt_stmt.
Section Sz7.
Variables ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lt : ltac2:(SecDiet.SzSec.tyM 'linktype_to_dlt_proof__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra).
Lemma linktype_to_dlt_proof__body : ltac2:(SecDiet.SzSec.bodyP 'linktype_to_dlt_proof__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
Proof using Type. pin_using tt.
 intros MI -> Hlt. unfold LINKTYPE_TO_DLT_ENTRY.
  assert (TAB : ro_cells usegs m 0x11194 [CB 28 lt_tab]).
  { apply (ro_cells_image usegs m); [exact MI | vm_compute; reflexivity | lia | cbn; lia]. }
  assert (CASES : (lt < 11 \/ (11 <= lt /\ (lt < 100 \/ 107 <= lt))
                   \/ lt = 100 \/ lt = 101 \/ lt = 102 \/ lt = 103 \/ lt = 104 \/ lt = 105 \/ lt = 106)%Z) by lia.
  destruct CASES as [C|[C|[->|[->|[->|[->|[->|[->| ->]]]]]]]].
  - (* [comment removed for export] *)
    step. step. if_cases K; zify_cond K; rewrite ?unsigned_lit in * by lia; [|exfalso; lia].
    step. finish. unfold linktype_to_dlt.
    rewrite !(proj2 (Z.eqb_neq _ _)) by lia. reflexivity.
  - (* [comment removed for export] *)
    step. step. if_cases K; zify_cond K; rewrite ?unsigned_lit in * by lia; [exfalso; lia|].
    step. step. step. rewrite (unsigned_lit lt) by lia. if_true_by (lt_out_of_table lt ltac:(lia) ltac:(lia)).
    step. finish. unfold linktype_to_dlt. rewrite !(proj2 (Z.eqb_neq _ _)) by lia. reflexivity.
  - do 15 astep. finish. vm_compute. reflexivity.
  - do 15 astep. finish. vm_compute. reflexivity.
  - do 15 astep. finish. vm_compute. reflexivity.
  - do 15 astep. finish. vm_compute. reflexivity.
  - do 10 astep. finish. reflexivity.
  - do 10 astep. finish. reflexivity.
  - do 15 astep. finish. vm_compute. reflexivity.
Qed.
End Sz7.
Theorem linktype_to_dlt_proof : ltac:(let t := eval cbv delta [linktype_to_dlt_proof__stmt] in linktype_to_dlt_proof__stmt in exact t).
Proof using Type. red. intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lt. ltac2:(SecDiet.SzSec.closeP 'linktype_to_dlt_proof__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.

End WithCeil.
End TwB.
End F_pcap_pure.

(* [comment removed for export] *)
Module F_pcap_small.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import Tac Arr Bytes ITree Nodes Decode SysStep MonadX Image ImgSrc3.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Import Prelim Monad Fmt StdioCore Stdio PcapPrelim PcapTypes PcapPure Pcap Prog.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require Printf_kit__Musl. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require AmoStep__Musl. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_kit__Musl.StartupKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.CellsExtra.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_memcpy GI. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require GIFacts__S3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require PcapRep. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_memcpy OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.GI OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.GIFacts__S3.Ifaces OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.PcapRep OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Pcap_iface__S3.Pcap_iface.
From OSSVerify.libpcap.fuzz_pcap.images Require Import Plain.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import Ceiling.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import LiaPin.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require SecDiet.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac lia_e2w2_base := first [ zify_prune; zify_noeuclid; Z.euclidean_division_equations_cleanup; xlia zchecker
                                 | zify_prune; Zify.zify; xlia zchecker | Zify.zify; xlia zchecker ].
Local Ltac ceil_mentioned := lazymatch goal with | |- context [@alloc_ceiling _] => idtac | _ : context [@alloc_ceiling _] |- _ => idtac end.
(* [comment removed for export] *)
Local Ltac lia ::= clear_unpinned; try (ceil_ok; ceil_mentioned; ceil_facts); pinned_lia_core.
Import ListNotations.
Import ITree.Exc.
Open Scope bv_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section WithCeil.
Context {CEILV : CEIL}.
Lemma free_null_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte),
  a0 = Z_to_bv 64 0 ->
  evt ssegs (fun ms' => ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                F (ret_pc ra) fc None m (seg_rom ssegs))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 FREE_ENTRY) fc None m (seg_rom ssegs)).
Proof using Type. pin_using tt. intros until m. intros ->. unfold FREE_ENTRY. step. step. if_true. step. apply evt_done. reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition oneshot_proof__stmt : Prop := oneshot_stmt.
Section Sz2.
Variables ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m U HD PKT SRC pd w0 w1 w2 o0 o1 o2 pkc : ltac2:(SecDiet.SzSec.tyM 'oneshot_proof__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra).
Lemma oneshot_proof__body : ltac2:(SecDiet.SzSec.bodyP 'oneshot_proof__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
Proof using Type. pin_using tt.
 intros -> -> HU HS HH HP0 Hpk D1 D2 D3 D4 D5 MI _ _ _ _. unfold PK, pk_oneshot.
  destruct (rw_cells_forget _ _ _ _ HP0) as [pj HP]. clear HP0. cbn [cells_size] in HP. rewrite Hpk in HP. change (8 + 0)%nat with 8%nat in HP.
  pose proof (rw_cells_bound _ _ _ _ HU) as BU. pose proof (rw_cells_bound _ _ _ _ HS) as BS.
  pose proof (rw_cells_bound _ _ _ _ HH) as BH. pose proof (rw_cells_bound _ _ _ _ HP) as BP.
  cbn [cells_size csize Nat.add] in BU, BS, BH, BP.
  pose proof (munch_refl [(HD, HD + 24); (PKT, PKT + 8)]%Z m) as MU. pose proof (wmono_refl ssegs m) as WM.
  do 10 step. finish.
Qed.
End Sz2.
Theorem oneshot_proof : ltac:(let t := eval cbv delta [oneshot_proof__stmt] in oneshot_proof__stmt in exact t).
Proof using Type. red. intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m U HD PKT SRC pd w0 w1 w2 o0 o1 o2 pkc. ltac2:(SecDiet.SzSec.closeP 'oneshot_proof__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition stats_msg : list byte := [83; 116; 97; 116; 105; 115; 116; 105; 99; 115; 32; 97; 114; 101; 110; 39; 116; 32; 97; 118; 97; 105; 108; 97; 98; 108; 101; 32; 102; 114; 111; 109; 32; 115; 97; 118; 101; 102; 105; 108; 101; 115; 0].

Definition memcpy_specZ__stmt : Prop := forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (Dst Src n : Z) (src junk : list byte),
  a0 = Z_to_bv 64 Dst -> a1 = Z_to_bv 64 Src -> a2 = Z_to_bv 64 n ->
  bytes_at ssegs m Src src -> length src = Z.to_nat n -> (0 <= n)%Z ->
  rw_cells ssegs m Dst [CB (Z.to_nat n) junk] ->
  (Src + n <= Dst \/ Dst + n <= Src)%Z -> (Dst < 2^64)%Z -> (Src < 2^64)%Z ->
  mem_inv ssegs m ->
  evt ssegs (fun ms' => exists t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m',
      ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0 a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
               F (ret_pc ra) fc None m' (seg_rom ssegs)
      /\ munch [(Dst, Dst + n)]%Z m m' /\ wmono ssegs m m' /\ mem_inv ssegs m'
      /\ rw_cells ssegs m' Dst [CB (Z.to_nat n) src] /\ bytes_at ssegs m' Src src)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x207e0) fc None m (seg_rom ssegs)).
Section Sz3.
Variables ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m Dst Src n src junk : ltac2:(SecDiet.SzSec.tyM 'memcpy_specZ__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra).
Lemma memcpy_specZ__body : ltac2:(SecDiet.SzSec.bodyP 'memcpy_specZ__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
Proof using Type. pin_using tt.
 intros -> -> -> SRC LEN Hn DST SEP HD HS MI.
  pose proof (bytes_at_bound _ _ _ _ SRC) as B1. pose proof (rw_cells_bound _ _ _ _ DST) as B2. cbn [cells_size csize Nat.add] in B2.
  rewrite Nat.add_0_r, Z2Nat.id in B2 by lia. rewrite LEN, Z2Nat.id in B1 by lia.
  assert (E0 : bv_unsigned (Z_to_bv 64 Dst) = Dst) by (apply unsigned_lit; lia).
  assert (E1 : bv_unsigned (Z_to_bv 64 Src) = Src) by (apply unsigned_lit; lia).
  assert (E2 : bv_unsigned (Z_to_bv 64 n) = n) by (apply unsigned_lit; lia).
  eapply evt_mono; [eapply memcpy_spec; rewrite ?E0, ?E1, ?E2; try eassumption|].
  cbv beta. intros ms' PO. unfold memcpy_post in PO. rewrite ?E0, ?E1, ?E2 in PO. exact PO.
Qed.
End Sz3.
Lemma memcpy_specZ : ltac:(let t := eval cbv delta [memcpy_specZ__stmt] in memcpy_specZ__stmt in exact t).
Proof using Type. intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m Dst Src n src junk. ltac2:(SecDiet.SzSec.closeP 'memcpy_specZ__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.
Section Stats.
  Context {H hptr : Type} (HO : HeapOps H hptr) (K : modkit H hptr) (sites : stack_site -> Z).
  Hypothesis HFL : heap_frame_law K.
  Hypothesis SFL : stdio_fp_law K.

(* [comment removed for export] *)
Lemma pcap_aux_closable_agree : forall (p : pcap hptr hptr) P B I pad bs m m' (Q : Z -> Prop),
  agrees_on Q m m' ->
  (forall a, B <= a < B + pc_bufalloc p -> Q a)%Z ->
  (forall a, P + PCAP_PRIV_OFF <= a < P + psize p -> Q a)%Z ->
  (forall sg q, pc_priv p = PrivNg sg (Some q) -> forall a, I <= a < I + 40 * ng_ifaces_size sg -> Q a)%Z ->
  (0 <= pc_bufalloc p)%Z ->
  rw_cells ssegs m B [CB (Z.to_nat (pc_bufalloc p)) bs] -> rw_cells ssegs m (P + PCAP_PRIV_OFF) (priv_cells p I pad) -> ifaces_closable p I m ->
  rw_cells ssegs m' B [CB (Z.to_nat (pc_bufalloc p)) bs] /\ rw_cells ssegs m' (P + PCAP_PRIV_OFF) (priv_cells p I pad) /\ ifaces_closable p I m'.
Proof using CEILV. pin_using (fun (CEILV : unit) => tt).
  intros p P B I pad bs m m' Q AG HB HP HI Hba BUF PRIV IFS. split; [|split].
  - eapply agrees_rw_cells; [exact AG|exact BUF|]. intros a Ha. apply HB. cbn [cells_size csize] in Ha. lia.
  - eapply agrees_rw_cells; [exact AG|exact PRIV|]. intros a Ha. apply HP. pose proof (priv_cells_psize _ _ _ _ _ PRIV). lia.
  - eapply ifaces_closable_agree; eassumption.
Qed.

Definition pcap_stats_proof__stmt : Prop := pcap_stats_stmt K.
Section Sz5.
Variables ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m R s CLc PB FB lo P p : ltac2:(SecDiet.SzSec.tyM 'pcap_stats_proof__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra).
Lemma pcap_stats_proof__body : ltac2:(SecDiet.SzSec.bodyP 'pcap_stats_proof__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
Proof using HFL SFL. pin_using (fun (HFL SFL : unit) => tt).
  intros PRE PC ->.
  destruct PRE as (G & ST & LO & BU & SPM & MI & TP & ALN).
  destruct PC as (Af & HinF & (B & I & j & pad & bs & EPB & CELLS & PRIV & BUF & PFX & IFS & WF)).
  pose proof (GIo_PB_block K _ _ _ _ _ _ _ _ _ G ltac:(rewrite EPB; left; reflexivity)) as (P1 & P2 & P3 & P4 & P5 & P6).
  pose proof (GIo_PB_block K _ _ _ _ _ _ _ _ _ G ltac:(rewrite EPB; right; left; reflexivity)) as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6).
  pose proof WF as (W1 & W2 & W3 & W4 & W5 & W6 & W7 & W8 & W9 & W10 & W11 & W12 & W13).
  pose proof (PB_apart K _ _ _ _ _ _ _ _ _ _ G EPB) as [APB API].
  pose proof (psize_pos p) as PS. pose proof (GIo_spw K _ _ _ _ _ G) as SPW. unfold rc_lo in LO. unfold PCAP_L1_STACK in BU.
  pose proof (bv_unsigned_in_range 64 sp) as RSP.
  (* [comment removed for export] *)
  set (AUXB := rw_cells ssegs m B [CB (Z.to_nat (pc_bufalloc p)) bs]) in BUF.
  set (AUXP := rw_cells ssegs m (P + PCAP_PRIV_OFF) (priv_cells p I pad)) in PRIV.
  set (AUXI := ifaces_ok p I m) in IFS.
  (* [comment removed for export] *)
  unfold Pcap.pcap_stats. cbn [mo_ret MOps e_fenter e_fret fo_enter fo_ret fo_nop prims]. apply (implM_ret ssegs).
  unfold PCAP_STATS_ENTRY.
  (* [comment removed for export] *)
  assert (MSG : ro_cells ssegs m 0x10e78 [CB 43 stats_msg]).
  { apply (ro_cells_image ssegs m); [exact MI | vm_compute; reflexivity | lia | cbn; lia]. }
  (* [comment removed for export] *)
  apply pcap_cells_split4 in CELLS as (CA & CE & CH & CO); [|reflexivity].
  unfold pc_ops, PK, pk_stats, pk_oneshot in CO. unfold pc_pre in CA. unfold hdr_cells in CH. unfold PCAP_PRIV_OFF in CA.
  apply (rw_cells_split_CB ssegs m _ [] 304 _ [] [43; 261]%nat) in CE; [|reflexivity]. cbn [mk_CB_cells app] in CE.
  destruct (rw_cells_cut _ _ _ 1 CE) as [CB1 CB2]. clear CE. cbn [firstn skipn cells_size csize Nat.add] in CB1, CB2.
  replace (P + 216 + Z.of_nat 43)%Z with (P + 259)%Z in CB2 by lia.
  pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp); (P + 216, P + 216 + 43)]%Z m) as MU. pose proof (wmono_refl ssegs m) as WM.
  step. step.
  replace (ret_pc (Z_to_bv 64 83508)) with (Z_to_bv 64 83508) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
  carve_frame 16%nat ST.
  do 7 step.
  call (memcpy_specZ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (P + 216)%Z 0x10e78%Z 43%Z stats_msg (firstn 43 (pj_g j)));
    [reflexivity | reflexivity | reflexivity | exact (ro_cells_bytes_at _ _ _ _ MSG) | reflexivity | lia | exact CB1 | lia | lia | lia | assumption |].
  do 4 step.
  release_frame FR ST (bv_unsigned sp).
  (* [comment removed for export] *)
  set (W := [(bv_unsigned sp - 16, bv_unsigned sp); (P + 216, P + 216 + 43)]%Z) in *.
  assert (FW : Forall (fun iv => (rc_lo R <= fst iv /\ snd iv <= bv_unsigned sp) \/ iv_in_block PB iv)%Z W).
  { subst W. constructor; [left; cbn [fst snd]; unfold rc_lo; lia|]. constructor; [|constructor].
    right. rewrite EPB. unfold iv_in_block, pcap_blocks. apply Exists_cons_hd. cbn [cb_addr cb_size fst snd]. lia. }
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    assert (AG : agrees_on (fun a => outside W a) m mm) by (eapply agrees_on_of_munch; [exact MU | exact WM | intros a _ Ho; exact Ho]);
    destruct (pcap_aux_closable_agree p P B I pad bs m mm _ AG) as (BUF' & PRIV' & IFS');
      [ | | | lia | exact BUF | exact PRIV | exact IFS |]
  end.
  { intros a Ha. subst W. cbn [outside]. unfold rc_lo in LO. lia. }
  { intros a Ha. subst W. cbn [outside]. unfold PCAP_PRIV_OFF in Ha. unfold rc_lo in LO. lia. }
  { intros sg q Hq a Ha. subst W. cbn [outside]. destruct (API sg q Hq) as [X1 X2].
    pose proof (GIo_PB_block K _ _ _ _ _ _ _ _ _ G ltac:(rewrite EPB; unfold pcap_blocks; rewrite Hq; right; right; left; reflexivity)) as (I1 & I2 & I3 & I4 & I5 & I6).
    unfold rc_lo in LO. lia. }
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    apply evt_done; unfold pcap_post; exists (Z_to_bv 64 (-1)), mm, PB, FB end.
  split. { unfold hpost_regs. repeat (lazymatch goal with |- ex _ => eexists end). reflexivity. }
  split; [assumption|]. split; [assumption|].
  split. { eapply (keeps_of_pcap_writes K); [exact G | exact MU | exact WM | exact FW | unfold rc_lo; lia]. }
  split. { eapply (GIo_pcap_frame K HFL SFL); [exact G | exact MU | exact WM |].
           apply Forall_impl with (2 := FW). intros iv [Hs|Hb]; [left; unfold rc_lo in *; lia| right; exact Hb]. }
  split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
  (* [comment removed for export] *)
  cbn [fst snd]. exists Af. split; [exact HinF|].
  exists B, I. eexists. exists pad, bs.
  split; [exact EPB|]. split.
  { lazymatch goal with HPC : rw_cells _ ?mm (P + 216)%Z _ |- rw_cells _ _ _ _ =>
      pose proof (rw_cells_uncut _ _ _ _ _ HPC CB2 ltac:(cbn; lia)) as CE';
      pose proof (pcap_cells_join4 mm P p B (C8 (Z_to_bv 64 Af)) (C8 (Z_to_bv 64 (pk_stats PK))) (C8 (Z_to_bv 64 (pk_oneshot PK))) j _ (pc_header p)
                    eq_refl CA CE' eq_refl CH CO) as J end.
    replace (set_header (pc_header p) p) with p in J by (destruct p; reflexivity). exact J. }
  split; [exact PRIV'|]. split; [exact BUF'|]. split; [exact PFX|]. split; [exact IFS'|]. exact WF.
Qed.
End Sz5.
Theorem pcap_stats_proof : ltac:(let t := eval cbv delta [pcap_stats_proof__stmt] in pcap_stats_proof__stmt in exact t).
Proof using HFL SFL. red. intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m R s CLc PB FB lo P p. ltac2:(SecDiet.SzSec.closeP 'pcap_stats_proof__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.
End Stats.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section Freecode.
  Context {hptr : Type}.

  Definition pcap_freecode_spec__stmt : Prop := forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
      (F : bvmap 5 word) fc (m : mem) (lo P B : Z) (p : PcapTypes.pcap hptr hptr) (rf : cell) (j : pcap_junk),
    stk ssegs m lo (bv_unsigned sp) -> (lo + 16 <= bv_unsigned sp)%Z -> (alloc_ceiling <= lo)%Z -> mem_inv ssegs m ->
    a0 = Z_to_bv 64 (P + 200) -> csize rf = 8%nat -> (0 < P)%Z -> (P + 216 <= alloc_ceiling)%Z -> (P mod 16 = 0)%Z ->
    rw_cells ssegs m P (pc_pre p P B rf j) ->
    evt ssegs (fun ms' => exists t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m' f',
        ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                 F (ret_pc ra) fc None m' (seg_rom ssegs)
        /\ munch [(bv_unsigned sp - 16, bv_unsigned sp); (P + 200, P + 204)]%Z m m' /\ wmono ssegs m m' /\ mem_inv ssegs m'
        /\ stk ssegs m' lo (bv_unsigned sp)
        /\ rw_cells ssegs m' P (pc_pre p P B rf (set_pj_f f' j)))   (* [comment removed for export] *)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 PCAP_FREECODE_ENTRY) fc None m (seg_rom ssegs)).
  Section Sz6.
  Variables ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo P B p rf j : ltac2:(SecDiet.SzSec.tyM 'pcap_freecode_spec__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra).
  Lemma pcap_freecode_spec__body : ltac2:(SecDiet.SzSec.bodyP 'pcap_freecode_spec__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof using Type. pin_using tt.
    intros ST BU LO MI -> Hrf HP0 HP _ CA.
    pose proof (bv_unsigned_in_range 64 sp) as RSP.
    unfold PCAP_FREECODE_ENTRY. unfold pc_pre, PCAP_PRIV_OFF in CA.
    destruct rf as [rv|rv|rv|rb|rn rbs]; try discriminate Hrf; [|cbn in Hrf; subst rn].
    all: pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp); (P + 200, P + 204)]%Z m) as MU; pose proof (wmono_refl ssegs m) as WM.
    all: carve_frame 16%nat ST.
    all: do 7 step; if_true; do 4 step.
    all: release_frame FR ST (bv_unsigned sp).
    all: lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      lazymatch goal with CH : rw_cells _ mm ?PP ?cs, jj : pcap_junk |- _ =>
        let pre := eval cbn [firstn] in (firstn 21 cs) in
        pose proof (rw_cells_merge ssegs mm PP pre [CB 40 (firstn 40 (pj_f jj)); C4 (Z_to_bv 64 0); CB 4 (skipn 44 (pj_f jj))] [C8 (Z_to_bv 64 0)] CH) as CH';
        cbn [app cells_size csize cells_bytes cbytes Nat.add] in CH';
        apply evt_done; do 16 eexists; exists (firstn 40 (pj_f jj) ++ (le4 (Z_to_bv 64 0) ++ (skipn 44 (pj_f jj) ++ [])))
      end end.
    all: split; [reflexivity|]; split; [assumption|]; split; [assumption|]; split; [assumption|]; split; [assumption|].
    all: exact CH'.
  Qed.
  End Sz6.
  Lemma pcap_freecode_spec : ltac:(let t := eval cbv delta [pcap_freecode_spec__stmt] in pcap_freecode_spec__stmt in exact t).
  Proof using Type. intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo P B p rf j. ltac2:(SecDiet.SzSec.closeP 'pcap_freecode_spec__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.
End Freecode.

End WithCeil.

(* [comment removed for export] *)
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require ImgTgtUbsan.
From OSSVerify.libpcap.fuzz_pcap.images Require Ubsan.
Module TwB.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Tac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Arr OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Bytes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ITree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Nodes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Decode OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.SysStep OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.MonadX OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Image OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ImgTgtUbsan.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Monad OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Fmt OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.StdioCore OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Stdio OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapPrelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapTypes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapPure OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Pcap OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prog.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_kit__Musl.StartupKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.CellsExtra.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_memcpy.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.GI.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.GIFacts__S3.Ifaces.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.PcapRep.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Pcap_iface__S3.Pcap_iface.TwB.
Import OSSVerify.libpcap.fuzz_pcap.images.Ubsan.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Ceiling.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.LiaPin.
(* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac lia_e2w2_base := first [ zify_prune; zify_noeuclid; Z.euclidean_division_equations_cleanup; xlia zchecker
                                 | zify_prune; Zify.zify; xlia zchecker | Zify.zify; xlia zchecker ].
Local Ltac ceil_mentioned := lazymatch goal with | |- context [@alloc_ceiling _] => idtac | _ : context [@alloc_ceiling _] |- _ => idtac end.
(* [comment removed for export] *)
Local Ltac lia ::= clear_unpinned; try (ceil_ok; ceil_mentioned; ceil_facts); pinned_lia_core.
Import ListNotations.
Import ITree.Exc.
Open Scope bv_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section WithCeil.
Context {CEILV : CEIL}.
Lemma free_null_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte),
  a0 = Z_to_bv 64 0 ->
  evt usegs (fun ms' => ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                F (ret_pc ra) fc None m (seg_rom usegs))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 FREE_ENTRY) fc None m (seg_rom usegs)).
Proof using Type. pin_using tt. intros until m. intros ->. unfold FREE_ENTRY. step. step. if_true. step. apply evt_done. reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition oneshot_proof__stmt : Prop := oneshot_stmt.
Section Sz2.
Variables ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m U HD PKT SRC pd w0 w1 w2 o0 o1 o2 pkc : ltac2:(SecDiet.SzSec.tyM 'oneshot_proof__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra).
Lemma oneshot_proof__body : ltac2:(SecDiet.SzSec.bodyP 'oneshot_proof__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
Proof using Type. pin_using tt.
 intros -> -> HU HS HH HP0 Hpk D1 D2 D3 D4 D5 MI U0 AU K0 AK. unfold PK, pk_oneshot.
  destruct (rw_cells_forget _ _ _ _ HP0) as [pj HP]. clear HP0. cbn [cells_size] in HP. rewrite Hpk in HP. change (8 + 0)%nat with 8%nat in HP.
  pose proof (rw_cells_bound _ _ _ _ HU) as BU. pose proof (rw_cells_bound _ _ _ _ HS) as BS.
  pose proof (rw_cells_bound _ _ _ _ HH) as BH. pose proof (rw_cells_bound _ _ _ _ HP) as BP.
  cbn [cells_size csize Nat.add] in BU, BS, BH, BP.
  pose proof (munch_refl [(HD, HD + 24); (PKT, PKT + 8)]%Z m) as MU. pose proof (wmono_refl usegs m) as WM.
  step. if_false_by (eqz_false U ltac:(lia)). step. rewrite (and7_aligned U) by lia. step. if_false.
  do 9 step. if_false_by (eqz_false PKT ltac:(lia)). step. rewrite (and7_aligned PKT) by lia. step. if_false.
  do 2 step. finish.
Qed.
End Sz2.
Theorem oneshot_proof : ltac:(let t := eval cbv delta [oneshot_proof__stmt] in oneshot_proof__stmt in exact t).
Proof using Type. red. intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m U HD PKT SRC pd w0 w1 w2 o0 o1 o2 pkc. ltac2:(SecDiet.SzSec.closeP 'oneshot_proof__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition stats_msg : list byte := [83; 116; 97; 116; 105; 115; 116; 105; 99; 115; 32; 97; 114; 101; 110; 39; 116; 32; 97; 118; 97; 105; 108; 97; 98; 108; 101; 32; 102; 114; 111; 109; 32; 115; 97; 118; 101; 102; 105; 108; 101; 115; 0].

Definition memcpy_specZ__stmt : Prop := forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (Dst Src n : Z) (src junk : list byte),
  a0 = Z_to_bv 64 Dst -> a1 = Z_to_bv 64 Src -> a2 = Z_to_bv 64 n ->
  bytes_at usegs m Src src -> length src = Z.to_nat n -> (0 <= n)%Z ->
  rw_cells usegs m Dst [CB (Z.to_nat n) junk] ->
  (Src + n <= Dst \/ Dst + n <= Src)%Z -> (Dst < 2^64)%Z -> (Src < 2^64)%Z ->
  mem_inv usegs m ->
  evt usegs (fun ms' => exists t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m',
      ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0 a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
               F (ret_pc ra) fc None m' (seg_rom usegs)
      /\ munch [(Dst, Dst + n)]%Z m m' /\ wmono usegs m m' /\ mem_inv usegs m'
      /\ rw_cells usegs m' Dst [CB (Z.to_nat n) src] /\ bytes_at usegs m' Src src)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x20fa0) fc None m (seg_rom usegs)).
Section Sz3.
Variables ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m Dst Src n src junk : ltac2:(SecDiet.SzSec.tyM 'memcpy_specZ__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra).
Lemma memcpy_specZ__body : ltac2:(SecDiet.SzSec.bodyP 'memcpy_specZ__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
Proof using Type. pin_using tt.
 intros -> -> -> SRC LEN Hn DST SEP HD HS MI.
  pose proof (bytes_at_bound _ _ _ _ SRC) as B1. pose proof (rw_cells_bound _ _ _ _ DST) as B2. cbn [cells_size csize Nat.add] in B2.
  rewrite Nat.add_0_r, Z2Nat.id in B2 by lia. rewrite LEN, Z2Nat.id in B1 by lia.
  assert (E0 : bv_unsigned (Z_to_bv 64 Dst) = Dst) by (apply unsigned_lit; lia).
  assert (E1 : bv_unsigned (Z_to_bv 64 Src) = Src) by (apply unsigned_lit; lia).
  assert (E2 : bv_unsigned (Z_to_bv 64 n) = n) by (apply unsigned_lit; lia).
  eapply evt_mono; [eapply memcpy_spec; rewrite ?E0, ?E1, ?E2; try eassumption|].
  cbv beta. intros ms' PO. unfold memcpy_post in PO. rewrite ?E0, ?E1, ?E2 in PO. exact PO.
Qed.
End Sz3.
Lemma memcpy_specZ : ltac:(let t := eval cbv delta [memcpy_specZ__stmt] in memcpy_specZ__stmt in exact t).
Proof using Type. intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m Dst Src n src junk. ltac2:(SecDiet.SzSec.closeP 'memcpy_specZ__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.
Section Stats.
  Context {H hptr : Type} (HO : HeapOps H hptr) (K : modkit H hptr) (sites : stack_site -> Z).
  Hypothesis HFL : heap_frame_law K.
  Hypothesis SFL : stdio_fp_law K.

(* [comment removed for export] *)
Lemma pcap_aux_closable_agree : forall (p : pcap hptr hptr) P B I pad bs m m' (Q : Z -> Prop),
  agrees_on Q m m' ->
  (forall a, B <= a < B + pc_bufalloc p -> Q a)%Z ->
  (forall a, P + PCAP_PRIV_OFF <= a < P + psize p -> Q a)%Z ->
  (forall sg q, pc_priv p = PrivNg sg (Some q) -> forall a, I <= a < I + 40 * ng_ifaces_size sg -> Q a)%Z ->
  (0 <= pc_bufalloc p)%Z ->
  rw_cells usegs m B [CB (Z.to_nat (pc_bufalloc p)) bs] -> rw_cells usegs m (P + PCAP_PRIV_OFF) (priv_cells p I pad) -> ifaces_closable p I m ->
  rw_cells usegs m' B [CB (Z.to_nat (pc_bufalloc p)) bs] /\ rw_cells usegs m' (P + PCAP_PRIV_OFF) (priv_cells p I pad) /\ ifaces_closable p I m'.
Proof using CEILV. pin_using (fun (CEILV : unit) => tt).
  intros p P B I pad bs m m' Q AG HB HP HI Hba BUF PRIV IFS. split; [|split].
  - eapply agrees_rw_cells; [exact AG|exact BUF|]. intros a Ha. apply HB. cbn [cells_size csize] in Ha. lia.
  - eapply agrees_rw_cells; [exact AG|exact PRIV|]. intros a Ha. apply HP. pose proof (priv_cells_psize _ _ _ _ _ PRIV). lia.
  - eapply ifaces_closable_agree; eassumption.
Qed.

Definition pcap_stats_proof__stmt : Prop := pcap_stats_stmt K.
Section Sz5.
Variables ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m R s CLc PB FB lo P p : ltac2:(SecDiet.SzSec.tyM 'pcap_stats_proof__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra).
Lemma pcap_stats_proof__body : ltac2:(SecDiet.SzSec.bodyP 'pcap_stats_proof__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
Proof using HFL SFL. pin_using (fun (HFL SFL : unit) => tt).
 intros PRE PC ->.
  destruct PRE as (G & ST & LO & BU & SPM & MI & TP & ALN).
  destruct PC as (Af & HinF & (B & I & j & pad & bs & EPB & CELLS & PRIV & BUF & PFX & IFS & WF)).
  pose proof (GIo_PB_block K _ _ _ _ _ _ _ _ _ G ltac:(rewrite EPB; left; reflexivity)) as (P1 & P2 & P3 & P4 & P5 & P6).
  pose proof (GIo_PB_block K _ _ _ _ _ _ _ _ _ G ltac:(rewrite EPB; right; left; reflexivity)) as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6).
  pose proof WF as (W1 & W2 & W3 & W4 & W5 & W6 & W7 & W8 & W9 & W10 & W11 & W12 & W13).
  pose proof (PB_apart K _ _ _ _ _ _ _ _ _ _ G EPB) as [APB API].
  pose proof (psize_pos p) as PS. pose proof (GIo_spw K _ _ _ _ _ G) as SPW. unfold rc_lo in LO. unfold PCAP_L1_STACK in BU.
  pose proof (bv_unsigned_in_range 64 sp) as RSP.
  (* [comment removed for export] *)
  set (AUXB := rw_cells usegs m B [CB (Z.to_nat (pc_bufalloc p)) bs]) in BUF.
  set (AUXP := rw_cells usegs m (P + PCAP_PRIV_OFF) (priv_cells p I pad)) in PRIV.
  set (AUXI := ifaces_ok p I m) in IFS.
  (* [comment removed for export] *)
  unfold Pcap.pcap_stats. cbn [mo_ret MOps e_fenter e_fret fo_enter fo_ret fo_nop prims]. apply (implM_ret usegs).
  unfold PCAP_STATS_ENTRY.
  (* [comment removed for export] *)
  assert (MSG : ro_cells usegs m 0x10e78 [CB 43 stats_msg]).
  { apply (ro_cells_image usegs m); [exact MI | vm_compute; reflexivity | lia | cbn; lia]. }
  (* [comment removed for export] *)
  apply pcap_cells_split4 in CELLS as (CA & CE & CH & CO); [|reflexivity].
  unfold pc_ops, PK, pk_stats, pk_oneshot in CO. unfold pc_pre in CA. unfold hdr_cells in CH. unfold PCAP_PRIV_OFF in CA.
  apply (rw_cells_split_CB usegs m _ [] 304 _ [] [43; 261]%nat) in CE; [|reflexivity]. cbn [mk_CB_cells app] in CE.
  destruct (rw_cells_cut _ _ _ 1 CE) as [CB1 CB2]. clear CE. cbn [firstn skipn cells_size csize Nat.add] in CB1, CB2.
  replace (P + 216 + Z.of_nat 43)%Z with (P + 259)%Z in CB2 by lia.
  pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp); (P + 216, P + 216 + 43)]%Z m) as MU. pose proof (wmono_refl usegs m) as WM.
  assert (P8 : (P mod 8 = 0)%Z) by (rewrite <- (Z.add_0_r P); apply aligned16_8; [exact P2| reflexivity]).
  step. if_false_by (eqz_false P ltac:(lia)). step. rewrite (and7_aligned P) by lia. step. if_false. step. step.
  replace (ret_pc (Z_to_bv 64 83804)) with (Z_to_bv 64 83804) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
  step. if_false_by (eqz_false P ltac:(lia)). step. rewrite (and7_aligned P) by lia. step. if_false.
  carve_frame 16%nat ST.
  do 7 step.
  call (memcpy_specZ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (P + 216)%Z 0x10e78%Z 43%Z stats_msg (firstn 43 (pj_g j)));
    [reflexivity | reflexivity | reflexivity | exact (ro_cells_bytes_at _ _ _ _ MSG) | reflexivity | lia | exact CB1 | lia | lia | lia | assumption |].
  do 4 step.
  release_frame FR ST (bv_unsigned sp).
  (* [comment removed for export] *)
  set (W := [(bv_unsigned sp - 16, bv_unsigned sp); (P + 216, P + 216 + 43)]%Z) in *.
  assert (FW : Forall (fun iv => (rc_lo R <= fst iv /\ snd iv <= bv_unsigned sp) \/ iv_in_block PB iv)%Z W).
  { subst W. constructor; [left; cbn [fst snd]; unfold rc_lo; lia|]. constructor; [|constructor].
    right. rewrite EPB. unfold iv_in_block, pcap_blocks. apply Exists_cons_hd. cbn [cb_addr cb_size fst snd]. lia. }
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    assert (AG : agrees_on (fun a => outside W a) m mm) by (eapply agrees_on_of_munch; [exact MU | exact WM | intros a _ Ho; exact Ho]);
    destruct (pcap_aux_closable_agree p P B I pad bs m mm _ AG) as (BUF' & PRIV' & IFS');
      [ | | | lia | exact BUF | exact PRIV | exact IFS |]
  end.
  { intros a Ha. subst W. cbn [outside]. unfold rc_lo in LO. lia. }
  { intros a Ha. subst W. cbn [outside]. unfold PCAP_PRIV_OFF in Ha. unfold rc_lo in LO. lia. }
  { intros sg q Hq a Ha. subst W. cbn [outside]. destruct (API sg q Hq) as [X1 X2].
    pose proof (GIo_PB_block K _ _ _ _ _ _ _ _ _ G ltac:(rewrite EPB; unfold pcap_blocks; rewrite Hq; right; right; left; reflexivity)) as (I1 & I2 & I3 & I4 & I5 & I6).
    unfold rc_lo in LO. lia. }
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    apply evt_done; unfold pcap_post; exists (Z_to_bv 64 (-1)), mm, PB, FB end.
  split. { unfold hpost_regs. repeat (lazymatch goal with |- ex _ => eexists end). reflexivity. }
  split; [assumption|]. split; [assumption|].
  split. { eapply (keeps_of_pcap_writes K); [exact G | exact MU | exact WM | exact FW | unfold rc_lo; lia]. }
  split. { eapply (GIo_pcap_frame K HFL SFL); [exact G | exact MU | exact WM |].
           apply Forall_impl with (2 := FW). intros iv [Hs|Hb]; [left; unfold rc_lo in *; lia| right; exact Hb]. }
  split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
  (* [comment removed for export] *)
  cbn [fst snd]. exists Af. split; [exact HinF|].
  exists B, I. eexists. exists pad, bs.
  split; [exact EPB|]. split.
  { lazymatch goal with HPC : rw_cells _ ?mm (P + 216)%Z _ |- rw_cells _ _ _ _ =>
      pose proof (rw_cells_uncut _ _ _ _ _ HPC CB2 ltac:(cbn; lia)) as CE';
      pose proof (pcap_cells_join4 mm P p B (C8 (Z_to_bv 64 Af)) (C8 (Z_to_bv 64 (pk_stats PK))) (C8 (Z_to_bv 64 (pk_oneshot PK))) j _ (pc_header p)
                    eq_refl CA CE' eq_refl CH CO) as J end.
    replace (set_header (pc_header p) p) with p in J by (destruct p; reflexivity). exact J. }
  split; [exact PRIV'|]. split; [exact BUF'|]. split; [exact PFX|]. split; [exact IFS'|]. exact WF.
Qed.
End Sz5.
Theorem pcap_stats_proof : ltac:(let t := eval cbv delta [pcap_stats_proof__stmt] in pcap_stats_proof__stmt in exact t).
Proof using HFL SFL. red. intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m R s CLc PB FB lo P p. ltac2:(SecDiet.SzSec.closeP 'pcap_stats_proof__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.
End Stats.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section Freecode.
  Context {hptr : Type}.

  Definition pcap_freecode_spec__stmt : Prop := forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
      (F : bvmap 5 word) fc (m : mem) (lo P B : Z) (p : PcapTypes.pcap hptr hptr) (rf : cell) (j : pcap_junk),
    stk usegs m lo (bv_unsigned sp) -> (lo + 16 <= bv_unsigned sp)%Z -> (alloc_ceiling <= lo)%Z -> mem_inv usegs m ->
    a0 = Z_to_bv 64 (P + 200) -> csize rf = 8%nat -> (0 < P)%Z -> (P + 216 <= alloc_ceiling)%Z -> (P mod 16 = 0)%Z ->
    rw_cells usegs m P (pc_pre p P B rf j) ->
    evt usegs (fun ms' => exists t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m' f',
        ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                 F (ret_pc ra) fc None m' (seg_rom usegs)
        /\ munch [(bv_unsigned sp - 16, bv_unsigned sp); (P + 200, P + 204)]%Z m m' /\ wmono usegs m m' /\ mem_inv usegs m'
        /\ stk usegs m' lo (bv_unsigned sp)
        /\ rw_cells usegs m' P (pc_pre p P B rf (set_pj_f f' j)))   (* [comment removed for export] *)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 PCAP_FREECODE_ENTRY) fc None m (seg_rom usegs)).
  Section Sz6.
  Variables ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo P B p rf j : ltac2:(SecDiet.SzSec.tyM 'pcap_freecode_spec__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra).
  Lemma pcap_freecode_spec__body : ltac2:(SecDiet.SzSec.bodyP 'pcap_freecode_spec__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof using Type. pin_using tt.
 intros ST BU LO MI -> Hrf HP0 HP HP16 CA.
    assert (P8 : ((P + 200) mod 8 = 0)%Z) by (apply aligned16_8; [exact HP16| reflexivity]).
    pose proof (bv_unsigned_in_range 64 sp) as RSP.
    unfold PCAP_FREECODE_ENTRY. unfold pc_pre, PCAP_PRIV_OFF in CA.
    destruct rf as [rv|rv|rv|rb|rn rbs]; try discriminate Hrf; [|cbn in Hrf; subst rn].
    all: pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp); (P + 200, P + 204)]%Z m) as MU; pose proof (wmono_refl usegs m) as WM.
    all: carve_frame 16%nat ST.
    all: do 4 step; if_false_by (eqz_false (P + 200) ltac:(lia)); do 2 step; rewrite (and7_aligned (P + 200)) by lia; step; if_false; do 3 step; if_true; do 4 step.
    all: release_frame FR ST (bv_unsigned sp).
    all: lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      lazymatch goal with CH : rw_cells _ mm ?PP ?cs, jj : pcap_junk |- _ =>
        let pre := eval cbn [firstn] in (firstn 21 cs) in
        pose proof (rw_cells_merge usegs mm PP pre [CB 40 (firstn 40 (pj_f jj)); C4 (Z_to_bv 64 0); CB 4 (skipn 44 (pj_f jj))] [C8 (Z_to_bv 64 0)] CH) as CH';
        cbn [app cells_size csize cells_bytes cbytes Nat.add] in CH';
        apply evt_done; do 16 eexists; exists (firstn 40 (pj_f jj) ++ (le4 (Z_to_bv 64 0) ++ (skipn 44 (pj_f jj) ++ [])))
      end end.
    all: split; [reflexivity|]; split; [assumption|]; split; [assumption|]; split; [assumption|]; split; [assumption|].
    all: exact CH'.
  Qed.
  End Sz6.
  Lemma pcap_freecode_spec : ltac:(let t := eval cbv delta [pcap_freecode_spec__stmt] in pcap_freecode_spec__stmt in exact t).
  Proof using Type. intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo P B p rf j. ltac2:(SecDiet.SzSec.closeP 'pcap_freecode_spec__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.
End Freecode.

End WithCeil.
End TwB.
End F_pcap_small.

(* [comment removed for export] *)
Module F_pcap_next_ex.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import Tac Arr Bytes ITree Nodes Decode SysStep MonadX Image ImgSrc3.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Import Prelim Monad Fmt StdioCore Stdio PcapPrelim PcapTypes PcapPure Pcap Prog.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require Printf_kit__Musl. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require AmoStep__Musl. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_kit__Musl.StartupKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.CellsExtra.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require GI PcapRep. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.GI OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.PcapRep OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Pcap_iface__S3.Pcap_iface OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Pcap_iface__S3.F_pcap_small.
From OSSVerify.libpcap.fuzz_pcap.images Require Import Plain.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import Ceiling.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import LiaPin.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require SecDiet.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
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

(* [comment removed for export] *)
Ltac hide H := lazymatch type of H with ?T => let X := fresh "AUX" in set (X := T) in H end.
Ltac unhide H := lazymatch type of H with ?X => subst X end.
(* [comment removed for export] *)
Ltac ienter := lazymatch goal with |- implM _ _ _ ?Q _ => let QQ := fresh "POSTQ" in set (QQ := Q) end; unfold implM; iprefix.

Section WithCeil.
Context {CEILV : CEIL}.
Section NextEx.
  Context {H hptr : Type} (HO : HeapOps H hptr) (K : modkit H hptr) (sites : stack_site -> Z).
  Hypothesis HFL : heap_frame_law K.
  Hypothesis SFL : stdio_fp_law K.
  (* [comment removed for export] *)
  Hypothesis NP_PCAP : pcap_next_packet_stmt HO K sites.
  Hypothesis NP_NG : pcap_ng_next_packet_stmt HO K sites.

  Lemma next_packet_op_any : forall ng, next_packet_op_stmt_for HO K sites ng.
  Proof using NP_NG NP_PCAP. pin_using (fun (NP_NG NP_PCAP : unit) => tt). intros [|]; [exact NP_NG | exact NP_PCAP]. Qed.

  Definition offline_read_proof__stmt : Prop := offline_read_stmt HO K sites.
  Section Sz2.
  Variables ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m R s CLc PB FB lo P U PKT p fuel pd pkc : ltac2:(SecDiet.SzSec.tyM 'offline_read_proof__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra).
  Lemma offline_read_proof__body : ltac2:(SecDiet.SzSec.bodyP 'offline_read_proof__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof using HFL NP_NG NP_PCAP SFL. pin_using (fun (HFL NP_NG NP_PCAP SFL : unit) => tt).
    intros PRE PC SITES -> -> -> -> HU HPK Hpk U1 U2 K1 K2 D1 AU AK.
    destruct PRE as (G & ST & LO & BU & SPM & MI & TP & ALN).
    pose proof PC as (Af & HinF & (B & I & j & pad & bs & EPB & CELLS & PRIV & BUF & PFX & IFS & WF)).
    pose proof WF as (W1 & W2 & W3 & W4 & W5 & W6 & W7 & W8 & W9 & W10 & W11 & W12 & W13).
    pose proof (GIo_PB_block K _ _ _ _ _ _ _ _ _ G ltac:(rewrite EPB; left; reflexivity)) as (P1 & P2 & P3 & P4 & P5 & P6).
    pose proof (psize_pos p) as PS. pose proof (GIo_spw K _ _ _ _ _ G) as SPW. unfold rc_lo in LO. unfold PCAP_L3_STACK in BU.
    pose proof (bv_unsigned_in_range 64 sp) as RSP.
    destruct (rw_cells_forget _ _ _ _ HPK) as [pkj HP]. clear HPK. cbn [cells_size] in HP. rewrite Hpk in HP. change (8 + 0)%nat with 8%nat in HP.
    (* [comment removed for export] *)
    apply pcap_cells_split4 in CELLS as (CA & CE & CH & CO); [|reflexivity].
    hide BUF. hide PRIV. hide IFS. hide CE. hide CH. hide CO.
    unfold pc_pre, PCAP_PRIV_OFF in CA. rewrite W5 in CA.
    (* [comment removed for export] *)
    unfold pcapint_offline_read_1. rewrite W5. cbn [Z.eqb negb]. cbn [mo_bind mo_ret MOps e_fenter e_fret fo_enter fo_ret fo_nop prims].
    unfold PCAP_OFFLINE_READ_ENTRY.
    pose proof (munch_refl [(bv_unsigned sp - 80, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl ssegs m) as WM.
    ienter.
    carve_frame 80%nat ST.
    do 12 step. if_true. do 2 step. if_true. do 7 step.
    replace (ret_pc (Z_to_bv 64 (np_entry p))) with (Z_to_bv 64 (np_entry p))
      by (unfold np_entry, PK; cbn [pk_next_ng pk_next_pcap]; destruct (is_ng p); (symmetry; apply ret_pc_even; [lia|reflexivity])).
    (* [comment removed for export] *)
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      assert (FW : Forall (pcap_iv R PB) [(bv_unsigned sp + -80, bv_unsigned sp)]%Z)
        by (apply Forall_cons; [left; cbn [fst snd]; unfold rc_lo; lia| apply Forall_nil]);
      assert (G0 : GIo K R s (CLc ++ PB) FB mm) by (eapply (GIo_pcap_frame K HFL SFL); [exact G | exact MU | exact WM | exact FW]);
      assert (AG0 : agrees_on (fun a => outside [(bv_unsigned sp + -80, bv_unsigned sp)]%Z a) m mm)
        by (eapply agrees_on_of_munch; [exact MU | exact WM | intros a _ Ho; exact Ho]);
      assert (PC0 : PCAPR P p PB FB mm)
        by (eapply PCAPR_agree; [exact AG0 | intros a Ha; pose proof (in_PB_below K _ _ _ _ _ _ _ G Ha); cbn [outside]; unfold rc_lo in *; lia | exact PC])
    end.
    clear CA CE CH CO PRIV BUF IFS AUX AUX0 AUX1 AUX2 AUX3 AUX4.
    (* [comment removed for export] *)
    apply (rw_cells_split_CB ssegs _ _ [] 32 _ _ [24; 8]%nat) in FR; [|reflexivity]. cbn [mk_CB_cells app] in FR.
    destruct (rw_cells_cut _ _ _ 1 FR) as [FRH FR']. clear FR. cbn [firstn skipn cells_size csize Nat.add] in FRH, FR'.
    destruct (rw_cells_cut _ _ _ 1 FR') as [FRD FRS]. clear FR'. cbn [firstn skipn cells_size csize Nat.add] in FRD, FRS.
    replace (bv_unsigned sp + -80 + Z.of_nat 24 + Z.of_nat 8)%Z with (bv_unsigned sp + -48)%Z in FRS by lia.
    replace (bv_unsigned sp + -80 + Z.of_nat 24)%Z with (bv_unsigned sp + -56)%Z in FRD by lia.
    name_sp sp (-80)%Z.
    apply evt_done. eapply (implM_bind ssegs).
    { eapply (next_packet_op_any (is_ng p));
        [ split; [exact G0|]; split; [rewrite Hsp; exact ST|]; split; [unfold rc_lo; lia|]; split; [unfold PCAP_L2_STACK; rewrite Hsp; lia|];
          split; [rewrite Hsp; lia|]; split; [assumption|]; split; [exact TP| first [exact ALN | rewrite Hsp; apply aln16_add; [exact ALN| reflexivity]]]
        | exact PC0 | reflexivity | rewrite SITES, Hsp; unfold D_OFFLINE_READ, D_NEXT_PACKET; f_equal; lia
        | reflexivity | exact Esp | reflexivity | exact FRH | reflexivity | exact FRD | reflexivity | rewrite Hsp; lia | lia | lia
        | apply aligned16_8; [exact ALN| reflexivity] | apply aligned16_8; [exact ALN| reflexivity] ]. }
    intros [[st h] p'] s' ms' PO. unfold next_packet_post in PO. destruct_exs PO.
    destruct PO as (E & OF1 & MI1 & ST1 & AG1 & G1 & PC1 & PCC1 & -> & Hst & HH1 & HH0 & HD1 & Hdw).
    unfold hpost_regs in E. destruct_exs E. subst ms'. rewrite Hsp in *. unname_sp.
    rename x0 into m2. rename x1 into PB1.
    destruct (rw_cells_forget _ _ _ _ HD1) as [dwj HD]. clear HD1. cbn [cells_size] in HD. rewrite Hdw in HD. change (8 + 0)%nat with 8%nat in HD. clear x2 Hdw.
    replace (ret_pc (Z_to_bv 64 83312)) with (Z_to_bv 64 83312) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
    (* [comment removed for export] *)
    assert (KEEP : forall A cs, rw_cells ssegs m1 A cs -> (bv_unsigned sp + -48 <= A)%Z -> rw_cells ssegs m2 A cs).
    { intros A cs HC HA. eapply agrees_rw_cells; [exact AG1 | exact HC | intros a Ha; split; [left; lia| lia]]. }
    apply KEEP in FRS; [|lia]. apply KEEP in HU; [|lia]. apply KEEP in HP; [|lia]. clear KEEP.
    assert (AGa : agrees_on (client_keeps CLc (bv_unsigned sp)) m m1).
    { eapply (keeps_of_pcap_writes K); [exact G | exact MU | exact WM | | unfold rc_lo; lia].
      apply Forall_cons; [left; cbn [fst snd]; unfold rc_lo; lia| apply Forall_nil]. }
    assert (AGab : agrees_on (fun a => client_keeps CLc (bv_unsigned sp) a /\ ~ (PKT <= a < PKT + 8))%Z m m2).
    { eapply agrees_on_trans; [eapply agrees_on_weaken; [exact AGa| intros a [Ha _]; exact Ha] |].
      eapply agrees_on_weaken; [exact AG1|]. intros a [[Ha|Ha] Hn]; [split; [left; lia| lia]|].
      destruct (GIo_CLc_facts K _ _ _ _ _ _ _ G Ha) as [Hc _]. unfold rc_lo in LO. split; [right; exact Ha| lia]. }
    clear MU WM AG0 G0 PC0 MI.
    unfold PCAP_HDR_OFF in HU.
    destruct Hst as [-> | [-> | ->]].
    - (* [comment removed for export] *)
      specialize (PC1 ltac:(lia)). clear PCC1.
      (* [comment removed for export] *)
      pose proof PC1 as (Af1 & HinF1 & (B1 & I1 & j1 & pad1 & bs1 & EPB1 & CELLS1 & PRIV1 & BUF1 & PFX1 & IFS1 & WF1)).
      pose proof (GIo_PB_block K _ _ _ _ _ _ _ _ _ G1 ltac:(rewrite EPB1; left; reflexivity)) as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6).
      pose proof (psize_pos p') as PS1.
      apply pcap_cells_split4 in CELLS1 as (CA1 & CE1 & CH1 & CO1); [|reflexivity].
      unfold pc_pre, PCAP_PRIV_OFF in CA1.
      destruct (HH1 eq_refl) as (HDR & Hcap & Hlen). clear HH0 HH1.
      apply hdr_cells_to_3 in HDR. apply hdr_cells_to_3 in CH1. unfold hdr3 in HDR, CH1.
      hide BUF1. hide PRIV1. hide IFS1. hide CE1. hide CO1.
      pose proof (munch_refl [(P + 520, P + 544); (PKT, PKT + 8)]%Z m2) as MU2. pose proof (wmono_refl ssegs m2) as WM2.
      cbn [Z.ltb Z.eqb]. apply (implM_ret ssegs).
      step. if_false. step. if_false. step. step. if_true. do 4 step.
      replace (ret_pc (Z_to_bv 64 (pk_oneshot PK))) with (Z_to_bv 64 (pk_oneshot PK)) by (symmetry; apply ret_pc_even; [cbn; lia|reflexivity]).
      call (oneshot_proof _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ U (P + 520)%Z PKT (bv_unsigned sp + -80)%Z pd _ _ _ _ _ _ (CB 8 pkj));
        [reflexivity | reflexivity | exact HU | exact HDR | exact CH1 | exact HP | reflexivity
        | unfold rc_lo in LO; lia | unfold rc_lo in LO; lia | unfold rc_lo in LO; lia | lia | lia | assumption
        | unfold rc_lo in LO; lia | exact AU | unfold rc_lo in LO; lia | exact AK |].
      do 2 step. if_true. do 9 step.
      release_frame HDR ST1 (bv_unsigned sp + -56)%Z. release_frame HD ST1 (bv_unsigned sp + -48)%Z. release_frame FRS ST1 (bv_unsigned sp).
      (* [comment removed for export] *)
      pose proof (PB_apart K _ _ _ _ _ _ _ _ _ _ G1 EPB1) as [APB1 API1].
      pose proof (GIo_PB_block K _ _ _ _ _ _ _ _ _ G1 ltac:(rewrite EPB1; right; left; reflexivity)) as (R1 & R2 & R3 & R4 & R5 & R6).
      pose proof WF1 as (_ & _ & W3' & _).
      set (FP2 := [(P + 520, P + 544); (PKT, PKT + 8)]%Z) in *.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
        assert (AG2 : agrees_on (fun a => outside FP2 a) m2 mm) by (eapply agrees_on_of_munch; [exact MU2 | exact WM2 | intros a _ Ho; exact Ho]);
        unhide CE1; unhide CO1; unhide BUF1; unhide PRIV1; unhide IFS1;
        destruct (pcap_aux_agree p' P B1 I1 pad1 bs1 m2 mm _ AG2) as (BUF' & PRIV' & IFS'); [ | | | lia | exact BUF1 | exact PRIV1 | exact IFS1 |]
      end.
      { intros a Ha. subst FP2. cbn [outside]. unfold rc_lo in LO. lia. }
      { intros a Ha. subst FP2. cbn [outside]. unfold PCAP_PRIV_OFF in Ha. unfold rc_lo in LO. lia. }
      { intros sg q Hq a Ha. subst FP2. cbn [outside]. destruct (API1 sg q Hq) as [X1 X2].
        pose proof (GIo_PB_block K _ _ _ _ _ _ _ _ _ G1 ltac:(rewrite EPB1; unfold pcap_blocks; rewrite Hq; right; right; left; reflexivity)) as (I1' & I2 & I3 & I4 & I5 & I6).
        unfold rc_lo in LO. clear - Ha X1 PS1 K1 I4 SPW LO BU. lia. }
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
        assert (CE' : rw_cells ssegs mm (P + 216) [CB 304 (pj_g j1)]) by (eapply agrees_rw_cells; [exact AG2 | exact CE1 | intros a Ha; subst FP2; cbn [outside cells_size csize Nat.add] in *; unfold rc_lo in LO; lia]);
        assert (CO' : rw_cells ssegs mm (P + 544) (pc_ops p' (C8 (Z_to_bv 64 (pk_stats PK))) (C8 (Z_to_bv 64 (pk_oneshot PK))) j1))
          by (eapply agrees_rw_cells; [exact AG2 | exact CO1 | intros a Ha; subst FP2; cbn [outside cells_size csize Nat.add pc_ops] in *; unfold rc_lo in LO; lia]);
        lazymatch goal with HPC : rw_cells _ mm (P + 520)%Z _ |- _ =>
          pose proof (pcap_cells_join4 mm P p' B1 (C8 (Z_to_bv 64 Af1)) (C8 (Z_to_bv 64 (pk_stats PK))) (C8 (Z_to_bv 64 (pk_oneshot PK))) j1 _ h
                        eq_refl CA1 CE' eq_refl (hdr_cells_of_3 _ _ h HPC) CO') as J end;
        assert (FW2 : Forall (pcap_iv R PB1) FP2)
          by (subst FP2; apply Forall_cons; [right; rewrite EPB1; unfold iv_in_block, pcap_blocks; apply Exists_cons_hd; cbn [cb_addr cb_size fst snd]; lia|];
              apply Forall_cons; [left; cbn [fst snd]; unfold rc_lo; lia| apply Forall_nil]);
        apply evt_done; subst POSTQ; cbv beta iota;
        lazymatch goal with PO : rw_cells _ mm PKT [C8 ?v] |- _ => exists (Z_to_bv 64 1), mm, PB1, (C8 v) end
      end.
      split. { unfold hpost_regs. repeat (lazymatch goal with |- ex _ => eexists end). reflexivity. }
      split; [exact OF1|]. split; [assumption|]. split; [assumption|].
      split. { eapply agrees_on_trans; [exact AGab|]. eapply agrees_on_weaken; [exact AG2|]. intros a [[Ha|Ha] Hn]; subst FP2; cbn [outside].
               - unfold rc_lo in LO. lia.
               - destruct (GIo_CLc_facts K _ _ _ _ _ _ _ G1 Ha) as [Hc Hnb]. split; [|lia].
                 intros Hin. apply Hnb. rewrite EPB1. unfold pcap_blocks, in_block. apply Exists_cons_hd. cbn [cb_addr cb_size fst snd]. lia. }
      split. { eapply (GIo_pcap_frame K HFL SFL); [exact G1 | exact MU2 | exact WM2 | exact FW2]. }
      split. { intros _. eapply PCAPR_intro_set_header; [exact HinF1 | exact EPB1 | exact J | exact PRIV' | exact BUF' | exact PFX1 | exact IFS' | exact WF1 | exact Hcap | exact Hlen]. }
      split. { intros X. exfalso. lia. }
      split; [reflexivity|]. split; [left; reflexivity|]. split; [assumption|]. split; [assumption| reflexivity].
    - (* [comment removed for export] *)
      destruct (HH0 ltac:(lia)) as (hcs' & Hsz & HDR0). clear HH0 HH1.
      destruct (rw_cells_forget _ _ _ _ HDR0) as [hj HDR]. clear HDR0. rewrite Hsz in HDR.
      cbn [Z.ltb Z.eqb]. apply (implM_ret ssegs).
      step. if_false. step. if_true. do 9 step.
      release_frame HDR ST1 (bv_unsigned sp + -56)%Z. release_frame HD ST1 (bv_unsigned sp + -48)%Z. release_frame FRS ST1 (bv_unsigned sp).
      apply evt_done; subst POSTQ; cbv beta iota. exists (Z_to_bv 64 0), m2, PB1, (CB 8 pkj).
      split. { unfold hpost_regs. repeat (lazymatch goal with |- ex _ => eexists end). reflexivity. }
      split; [exact OF1|]. split; [assumption|]. split; [assumption|]. split; [exact AGab|]. split; [exact G1|].
      split; [intros _; exact (PC1 ltac:(lia))|]. split; [intros X; exfalso; lia|].
      split; [reflexivity|]. split; [right; left; reflexivity|]. split; [assumption|]. split; [assumption| reflexivity].
    - (* [comment removed for export] *)
      destruct (HH0 ltac:(lia)) as (hcs' & Hsz & HDR0). clear HH0 HH1.
      destruct (rw_cells_forget _ _ _ _ HDR0) as [hj HDR]. clear HDR0. rewrite Hsz in HDR.
      cbn [Z.ltb Z.eqb]. apply (implM_ret ssegs).
      step. if_true. do 11 step.
      release_frame HDR ST1 (bv_unsigned sp + -56)%Z. release_frame HD ST1 (bv_unsigned sp + -48)%Z. release_frame FRS ST1 (bv_unsigned sp).
      apply evt_done; subst POSTQ; cbv beta iota. exists (Z_to_bv 64 (-1)), m2, PB1, (CB 8 pkj).
      split. { unfold hpost_regs. repeat (lazymatch goal with |- ex _ => eexists end). reflexivity. }
      split; [exact OF1|]. split; [assumption|]. split; [assumption|]. split; [exact AGab|]. split; [exact G1|].
      split; [intros X; exfalso; lia|]. split; [intros _; exact (PCC1 eq_refl)|].
      split; [reflexivity|]. split; [right; right; reflexivity|]. split; [assumption|]. split; [assumption| reflexivity].
  Qed.
  End Sz2.
  Theorem offline_read_proof : ltac:(let t := eval cbv delta [offline_read_proof__stmt] in offline_read_proof__stmt in exact t).
  Proof using HFL NP_NG NP_PCAP SFL. red. intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m R s CLc PB FB lo P U PKT p fuel pd pkc. ltac2:(SecDiet.SzSec.closeP 'offline_read_proof__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.


  Definition next_ex_proof__stmt : Prop := pcap_next_ex_stmt HO K sites.
  Section Sz3.
  Variables ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m R s CLc PB FB lo P HP PKT p fuel hc pkc : ltac2:(SecDiet.SzSec.tyM 'next_ex_proof__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra).
  Lemma next_ex_proof__body : ltac2:(SecDiet.SzSec.bodyP 'next_ex_proof__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof using HFL NP_NG NP_PCAP SFL. pin_using (fun (HFL NP_NG NP_PCAP SFL : unit) => tt).
    intros PRE PC SITES -> -> -> HHP Hhc HPK Hpk U1 U2 K1 K2 D1 AH AK.
    destruct PRE as (G & ST & LO & BU & SPM & MI & TP & ALN).
    pose proof PC as (Af & HinF & (B & I & j & pad & bs & EPB & CELLS & PRIV & BUF & PFX & IFS & WF)).
    pose proof (GIo_PB_block K _ _ _ _ _ _ _ _ _ G ltac:(rewrite EPB; left; reflexivity)) as (P1 & P2 & P3 & P4 & P5 & P6).
    pose proof (GIo_block_ok K _ _ _ _ _ _ G ltac:(apply in_or_app; right; exact HinF)) as (A1 & _ & _ & A4 & _).
    cbn [cb_addr cb_size fst snd] in A1, A4. unfold FILE_BLOCK in A4.
    pose proof (psize_pos p) as PS. pose proof (GIo_spw K _ _ _ _ _ G) as SPW. unfold rc_lo in LO. unfold PCAP_L4_STACK in BU.
    pose proof (bv_unsigned_in_range 64 sp) as RSP.
    destruct (rw_cells_forget _ _ _ _ HPK) as [pkj HPc]. clear HPK. cbn [cells_size] in HPc. rewrite Hpk in HPc. change (8 + 0)%nat with 8%nat in HPc.
    destruct (rw_cells_forget _ _ _ _ HHP) as [hcj HH]. clear HHP. cbn [cells_size] in HH. rewrite Hhc in HH. change (8 + 0)%nat with 8%nat in HH.
    apply pcap_cells_split4 in CELLS as (CA & CE & CH & CO); [|reflexivity].
    hide BUF. hide PRIV. hide IFS. hide CE. hide CH.
    unfold pc_pre, PCAP_PRIV_OFF in CA. unfold pc_ops in CO.
    unfold Pcap.pcap_next_ex. cbn [mo_bind mo_ret MOps e_fenter e_fret fo_enter fo_ret fo_nop prims]. unfold PCAP_NEXT_EX_ENTRY.
    pose proof (munch_refl [(bv_unsigned sp - 32, bv_unsigned sp); (HP, HP + 8)]%Z m) as MU. pose proof (wmono_refl ssegs m) as WM.
    ienter.
    carve_frame 32%nat ST.
    do 9 step. if_false_by (eqz_false Af ltac:(lia)). do 4 step.
    (* [comment removed for export] *)
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      assert (FW : Forall (pcap_iv R PB) [(bv_unsigned sp + -32, bv_unsigned sp); (HP, HP + 8)]%Z)
        by (apply Forall_cons; [left; cbn [fst snd]; unfold rc_lo; lia|]; apply Forall_cons; [left; cbn [fst snd]; unfold rc_lo; lia| apply Forall_nil]);
      assert (G0 : GIo K R s (CLc ++ PB) FB mm) by (eapply (GIo_pcap_frame K HFL SFL); [exact G | exact MU | exact WM | exact FW]);
      assert (AG0 : agrees_on (fun a => outside [(bv_unsigned sp + -32, bv_unsigned sp); (HP, HP + 8)]%Z a) m mm)
        by (eapply agrees_on_of_munch; [exact MU | exact WM | intros a _ Ho; exact Ho]);
      assert (PC0 : PCAPR P p PB FB mm)
        by (eapply PCAPR_agree; [exact AG0 | intros a Ha; pose proof (in_PB_below K _ _ _ _ _ _ _ G Ha); cbn [outside]; unfold rc_lo in *; lia | exact PC])
    end.
    clear CA CE CH CO PRIV BUF IFS AUX AUX0 AUX1 AUX2 AUX3.
    destruct (rw_cells_cut _ _ _ 3 FR) as [FRU FRS]. clear FR. cbn [firstn skipn cells_size csize Nat.add] in FRU, FRS.
    replace (bv_unsigned sp + -32 + Z.of_nat 24)%Z with (bv_unsigned sp + -8)%Z in FRS by lia.
    name_sp sp (-32)%Z.
    apply evt_done. eapply (implM_bind ssegs).
    { eapply offline_read_proof;
        [ split; [exact G0|]; split; [rewrite Hsp; exact ST|]; split; [unfold rc_lo; lia|]; split; [unfold PCAP_L3_STACK; rewrite Hsp; lia|];
          split; [rewrite Hsp; lia|]; split; [assumption|]; split; [exact TP| first [exact ALN | rewrite Hsp; apply aln16_add; [exact ALN| reflexivity]]]
        | exact PC0 | rewrite SITES, Hsp; unfold D_OFFLINE_READ, D_NEXT_EX; f_equal; lia
        | reflexivity | reflexivity | reflexivity | exact Esp | exact FRU | exact HPc | reflexivity
        | rewrite Hsp; lia | lia | rewrite Hsp; lia | lia | lia
        | apply aln16_add with (k := (-32)%Z) in ALN; [|reflexivity]; apply Z.mod_divide in ALN; [|lia]; apply Z.mod_divide; [lia|]; destruct ALN as [q Hq]; exists (q * 2)%Z; lia
        | exact AK ]. }
    intros [st p'] s' ms' PO. cbv beta iota in PO. destruct_exs PO.
    destruct PO as (E & OF1 & MI1 & ST1 & AG1 & G1 & PC1 & PCC1 & -> & Hst & HU1 & HP1 & Hpk1).
    unfold hpost_regs in E. destruct_exs E. subst ms'. rewrite Hsp in *. unname_sp.
    rename x0 into m2. rename x1 into PB1. rename x2 into pk'.
    replace (ret_pc (Z_to_bv 64 83696)) with (Z_to_bv 64 83696) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
    rename m0 into m1.
    assert (KEEP : forall A cs, rw_cells ssegs m1 A cs -> (bv_unsigned sp + -8 <= A)%Z -> (A + Z.of_nat (cells_size cs) <= PKT \/ PKT + 8 <= A)%Z -> rw_cells ssegs m2 A cs).
    { intros A cs HC HA HD. eapply agrees_rw_cells; [exact AG1 | exact HC | intros a Ha; split; [left; lia| lia]]. }
    apply KEEP in FRS; [|lia|cbn [cells_size csize Nat.add]; lia]. apply KEEP in HH; [|lia|cbn [cells_size csize Nat.add]; lia]. clear KEEP.
    assert (AGab : agrees_on (fun a => client_keeps CLc (bv_unsigned sp) a /\ ~ (HP <= a < HP + 8) /\ ~ (PKT <= a < PKT + 8))%Z m m2).
    { eapply agrees_on_trans.
      - eapply agrees_on_weaken; [exact AG0|]. intros a [[Ha|Ha] [Hn1 Hn2]]; cbn [outside]; [lia|].
        destruct (GIo_CLc_facts K _ _ _ _ _ _ _ G Ha) as [Hc _]. unfold rc_lo in LO. lia.
      - eapply agrees_on_weaken; [exact AG1|]. intros a [[Ha|Ha] [Hn1 Hn2]]; [split; [left; lia| lia]|].
        split; [right; exact Ha| exact Hn2]. }
    apply (implM_ret ssegs).
    destruct Hst as [-> | [-> | ->]].
    - step. if_true. do 3 step.
      release_frame HU1 ST1 (bv_unsigned sp + -8)%Z. release_frame FRS ST1 (bv_unsigned sp).
      apply evt_done; subst POSTQ; cbv beta iota. exists (Z_to_bv 64 1), m2, PB1, pk'.
      split. { unfold hpost_regs. repeat (lazymatch goal with |- ex _ => eexists end). reflexivity. }
      split; [exact OF1|]. split; [assumption|]. split; [assumption|]. split; [exact AGab|]. split; [exact G1|].
      split. { cbn [Z.eqb]. intros _; exact (PC1 ltac:(lia)). } split. { cbn [Z.eqb]. intros X; exfalso; lia. }
      split; [reflexivity|]. split; [left; reflexivity|]. split; [exact HH|]. split; [exact HP1| exact Hpk1].
    - step. if_false. do 4 step.
      release_frame HU1 ST1 (bv_unsigned sp + -8)%Z. release_frame FRS ST1 (bv_unsigned sp).
      apply evt_done; subst POSTQ; cbv beta iota. exists (Z_to_bv 64 (-2)), m2, PB1, pk'.
      split. { unfold hpost_regs. repeat (lazymatch goal with |- ex _ => eexists end). reflexivity. }
      split; [exact OF1|]. split; [assumption|]. split; [assumption|]. split; [exact AGab|]. split; [exact G1|].
      split. { cbn [Z.eqb]. intros _; exact (PC1 ltac:(lia)). } split. { cbn [Z.eqb]. intros X; exfalso; lia. }
      split; [reflexivity|]. split; [right; left; reflexivity|]. split; [exact HH|]. split; [exact HP1| exact Hpk1].
    - step. if_true. do 3 step.
      release_frame HU1 ST1 (bv_unsigned sp + -8)%Z. release_frame FRS ST1 (bv_unsigned sp).
      apply evt_done; subst POSTQ; cbv beta iota. exists (Z_to_bv 64 (-1)), m2, PB1, pk'.
      split. { unfold hpost_regs. repeat (lazymatch goal with |- ex _ => eexists end). reflexivity. }
      split; [exact OF1|]. split; [assumption|]. split; [assumption|]. split; [exact AGab|]. split; [exact G1|].
      split. { cbn [Z.eqb]. intros X; exfalso; lia. } split. { cbn [Z.eqb]. intros _; exact (PCC1 eq_refl). }
      split; [reflexivity|]. split; [right; right; reflexivity|]. split; [exact HH|]. split; [exact HP1| exact Hpk1].
  Qed.
  End Sz3.
  Theorem next_ex_proof : ltac:(let t := eval cbv delta [next_ex_proof__stmt] in next_ex_proof__stmt in exact t).
  Proof using HFL NP_NG NP_PCAP SFL. red. intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m R s CLc PB FB lo P HP PKT p fuel hc pkc. ltac2:(SecDiet.SzSec.closeP 'next_ex_proof__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.
End NextEx.

End WithCeil.

(* [comment removed for export] *)
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require ImgTgtUbsan.
From OSSVerify.libpcap.fuzz_pcap.images Require Ubsan.
Module TwB.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Tac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Arr OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Bytes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ITree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Nodes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Decode OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.SysStep OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.MonadX OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Image OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ImgTgtUbsan.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Monad OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Fmt OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.StdioCore OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Stdio OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapPrelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapTypes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapPure OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Pcap OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prog.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_kit__Musl.StartupKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.CellsExtra.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.GI.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.PcapRep.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Pcap_iface__S3.Pcap_iface.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Pcap_iface__S3.F_pcap_small.TwB.
Import OSSVerify.libpcap.fuzz_pcap.images.Ubsan.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Ceiling.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.LiaPin.
(* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
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

(* [comment removed for export] *)
Ltac hide H := lazymatch type of H with ?T => let X := fresh "AUX" in set (X := T) in H end.
Ltac unhide H := lazymatch type of H with ?X => subst X end.
(* [comment removed for export] *)
Ltac ienter := lazymatch goal with |- implM _ _ _ ?Q _ => let QQ := fresh "POSTQ" in set (QQ := Q) end; unfold implM; iprefix.

Section WithCeil.
Context {CEILV : CEIL}.
Section NextEx.
  Context {H hptr : Type} (HO : HeapOps H hptr) (K : modkit H hptr) (sites : stack_site -> Z).
  Hypothesis HFL : heap_frame_law K.
  Hypothesis SFL : stdio_fp_law K.
  (* [comment removed for export] *)
  Hypothesis NP_PCAP : pcap_next_packet_stmt HO K sites.
  Hypothesis NP_NG : pcap_ng_next_packet_stmt HO K sites.

  Lemma next_packet_op_any : forall ng, next_packet_op_stmt_for HO K sites ng.
  Proof using NP_NG NP_PCAP. pin_using (fun (NP_NG NP_PCAP : unit) => tt). intros [|]; [exact NP_NG | exact NP_PCAP]. Qed.

  Definition offline_read_proof__stmt : Prop := offline_read_stmt HO K sites.
  Section Sz2.
  Variables ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m R s CLc PB FB lo P U PKT p fuel pd pkc : ltac2:(SecDiet.SzSec.tyM 'offline_read_proof__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra).
  Lemma offline_read_proof__body : ltac2:(SecDiet.SzSec.bodyP 'offline_read_proof__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof using HFL NP_NG NP_PCAP SFL. pin_using (fun (HFL NP_NG NP_PCAP SFL : unit) => tt).
 intros PRE PC SITES -> -> -> -> HU HPK Hpk U1 U2 K1 K2 D1 AU AK.
    destruct PRE as (G & ST & LO & BU & SPM & MI & TP & ALN).
    pose proof PC as (Af & HinF & (B & I & j & pad & bs & EPB & CELLS & PRIV & BUF & PFX & IFS & WF)).
    pose proof WF as (W1 & W2 & W3 & W4 & W5 & W6 & W7 & W8 & W9 & W10 & W11 & W12 & W13).
    pose proof (GIo_PB_block K _ _ _ _ _ _ _ _ _ G ltac:(rewrite EPB; left; reflexivity)) as (P1 & P2 & P3 & P4 & P5 & P6).
    pose proof (psize_pos p) as PS. pose proof (GIo_spw K _ _ _ _ _ G) as SPW. unfold rc_lo in LO. unfold PCAP_L3_STACK in BU.
    pose proof (bv_unsigned_in_range 64 sp) as RSP.
    destruct (rw_cells_forget _ _ _ _ HPK) as [pkj HP]. clear HPK. cbn [cells_size] in HP. rewrite Hpk in HP. change (8 + 0)%nat with 8%nat in HP.
    (* [comment removed for export] *)
    apply pcap_cells_split4 in CELLS as (CA & CE & CH & CO); [|reflexivity].
    hide BUF. hide PRIV. hide IFS. hide CE. hide CH. hide CO.
    unfold pc_pre, PCAP_PRIV_OFF in CA. rewrite W5 in CA.
    (* [comment removed for export] *)
    unfold pcapint_offline_read_1. rewrite W5. cbn [Z.eqb negb]. cbn [mo_bind mo_ret MOps e_fenter e_fret fo_enter fo_ret fo_nop prims].
    unfold PCAP_OFFLINE_READ_ENTRY.
    pose proof (munch_refl [(bv_unsigned sp - 80, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl usegs m) as WM.
    ienter.
    carve_frame 80%nat ST.
    assert (P8 : (P mod 8 = 0)%Z) by (rewrite <- (Z.add_0_r P); apply aligned16_8; [exact P2| reflexivity]).
    do 12 step. if_true. step. if_false_by (eqz_false P ltac:(lia)). step. rewrite (and7_aligned P) by lia. step. if_false.
    do 2 step. if_true. do 7 step.
    replace (ret_pc (Z_to_bv 64 (np_entry p))) with (Z_to_bv 64 (np_entry p))
      by (unfold np_entry, PK; cbn [pk_next_ng pk_next_pcap]; destruct (is_ng p); (symmetry; apply ret_pc_even; [lia|reflexivity])).
    (* [comment removed for export] *)
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      assert (FW : Forall (pcap_iv R PB) [(bv_unsigned sp + -80, bv_unsigned sp)]%Z)
        by (apply Forall_cons; [left; cbn [fst snd]; unfold rc_lo; lia| apply Forall_nil]);
      assert (G0 : GIo K R s (CLc ++ PB) FB mm) by (eapply (GIo_pcap_frame K HFL SFL); [exact G | exact MU | exact WM | exact FW]);
      assert (AG0 : agrees_on (fun a => outside [(bv_unsigned sp + -80, bv_unsigned sp)]%Z a) m mm)
        by (eapply agrees_on_of_munch; [exact MU | exact WM | intros a _ Ho; exact Ho]);
      assert (PC0 : PCAPR P p PB FB mm)
        by (eapply PCAPR_agree; [exact AG0 | intros a Ha; pose proof (in_PB_below K _ _ _ _ _ _ _ G Ha); cbn [outside]; unfold rc_lo in *; lia | exact PC])
    end.
    clear CA CE CH CO PRIV BUF IFS AUX AUX0 AUX1 AUX2 AUX3 AUX4.
    (* [comment removed for export] *)
    apply (rw_cells_split_CB usegs _ _ [] 32 _ _ [24; 8]%nat) in FR; [|reflexivity]. cbn [mk_CB_cells app] in FR.
    destruct (rw_cells_cut _ _ _ 1 FR) as [FRH FR']. clear FR. cbn [firstn skipn cells_size csize Nat.add] in FRH, FR'.
    destruct (rw_cells_cut _ _ _ 1 FR') as [FRD FRS]. clear FR'. cbn [firstn skipn cells_size csize Nat.add] in FRD, FRS.
    replace (bv_unsigned sp + -80 + Z.of_nat 24 + Z.of_nat 8)%Z with (bv_unsigned sp + -48)%Z in FRS by lia.
    replace (bv_unsigned sp + -80 + Z.of_nat 24)%Z with (bv_unsigned sp + -56)%Z in FRD by lia.
    name_sp sp (-80)%Z.
    apply evt_done. eapply (implM_bind usegs).
    { eapply (next_packet_op_any (is_ng p));
        [ split; [exact G0|]; split; [rewrite Hsp; exact ST|]; split; [unfold rc_lo; lia|]; split; [unfold PCAP_L2_STACK; rewrite Hsp; lia|];
          split; [rewrite Hsp; lia|]; split; [assumption|]; split; [exact TP| first [exact ALN | rewrite Hsp; apply aln16_add; [exact ALN| reflexivity]]]
        | exact PC0 | reflexivity | rewrite SITES, Hsp; unfold D_OFFLINE_READ, D_NEXT_PACKET; f_equal; lia
        | reflexivity | exact Esp | reflexivity | exact FRH | reflexivity | exact FRD | reflexivity | rewrite Hsp; lia | lia | lia
        | apply aligned16_8; [exact ALN| reflexivity] | apply aligned16_8; [exact ALN| reflexivity] ]. }
    intros [[st h] p'] s' ms' PO. unfold next_packet_post in PO. destruct_exs PO.
    destruct PO as (E & OF1 & MI1 & ST1 & AG1 & G1 & PC1 & PCC1 & -> & Hst & HH1 & HH0 & HD1 & Hdw).
    unfold hpost_regs in E. destruct_exs E. subst ms'. rewrite Hsp in *. unname_sp.
    rename x0 into m2. rename x1 into PB1.
    destruct (rw_cells_forget _ _ _ _ HD1) as [dwj HD]. clear HD1. cbn [cells_size] in HD. rewrite Hdw in HD. change (8 + 0)%nat with 8%nat in HD. clear x2 Hdw.
    replace (ret_pc (Z_to_bv 64 83520)) with (Z_to_bv 64 83520) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
    (* [comment removed for export] *)
    assert (KEEP : forall A cs, rw_cells usegs m1 A cs -> (bv_unsigned sp + -48 <= A)%Z -> rw_cells usegs m2 A cs).
    { intros A cs HC HA. eapply agrees_rw_cells; [exact AG1 | exact HC | intros a Ha; split; [left; lia| lia]]. }
    apply KEEP in FRS; [|lia]. apply KEEP in HU; [|lia]. apply KEEP in HP; [|lia]. clear KEEP.
    assert (AGa : agrees_on (client_keeps CLc (bv_unsigned sp)) m m1).
    { eapply (keeps_of_pcap_writes K); [exact G | exact MU | exact WM | | unfold rc_lo; lia].
      apply Forall_cons; [left; cbn [fst snd]; unfold rc_lo; lia| apply Forall_nil]. }
    assert (AGab : agrees_on (fun a => client_keeps CLc (bv_unsigned sp) a /\ ~ (PKT <= a < PKT + 8))%Z m m2).
    { eapply agrees_on_trans; [eapply agrees_on_weaken; [exact AGa| intros a [Ha _]; exact Ha] |].
      eapply agrees_on_weaken; [exact AG1|]. intros a [[Ha|Ha] Hn]; [split; [left; lia| lia]|].
      destruct (GIo_CLc_facts K _ _ _ _ _ _ _ G Ha) as [Hc _]. unfold rc_lo in LO. split; [right; exact Ha| lia]. }
    clear MU WM AG0 G0 PC0 MI.
    unfold PCAP_HDR_OFF in HU.
    destruct Hst as [-> | [-> | ->]].
    - (* [comment removed for export] *)
      specialize (PC1 ltac:(lia)). clear PCC1.
      (* [comment removed for export] *)
      pose proof PC1 as (Af1 & HinF1 & (B1 & I1 & j1 & pad1 & bs1 & EPB1 & CELLS1 & PRIV1 & BUF1 & PFX1 & IFS1 & WF1)).
      pose proof (GIo_PB_block K _ _ _ _ _ _ _ _ _ G1 ltac:(rewrite EPB1; left; reflexivity)) as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6).
      pose proof (psize_pos p') as PS1.
      apply pcap_cells_split4 in CELLS1 as (CA1 & CE1 & CH1 & CO1); [|reflexivity].
      unfold pc_pre, PCAP_PRIV_OFF in CA1.
      destruct (HH1 eq_refl) as (HDR & Hcap & Hlen). clear HH0 HH1.
      apply hdr_cells_to_3 in HDR. apply hdr_cells_to_3 in CH1. unfold hdr3 in HDR, CH1.
      hide BUF1. hide PRIV1. hide IFS1. hide CE1. hide CO1.
      pose proof (munch_refl [(P + 520, P + 544); (PKT, PKT + 8)]%Z m2) as MU2. pose proof (wmono_refl usegs m2) as WM2.
      cbn [Z.ltb Z.eqb]. apply (implM_ret usegs).
      step. if_false. step. if_false. step. step. if_true. do 4 step.
      replace (ret_pc (Z_to_bv 64 (pk_oneshot PK))) with (Z_to_bv 64 (pk_oneshot PK)) by (symmetry; apply ret_pc_even; [cbn; lia|reflexivity]).
      call (oneshot_proof _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ U (P + 520)%Z PKT (bv_unsigned sp + -80)%Z pd _ _ _ _ _ _ (CB 8 pkj));
        [reflexivity | reflexivity | exact HU | exact HDR | exact CH1 | exact HP | reflexivity
        | unfold rc_lo in LO; lia | unfold rc_lo in LO; lia | unfold rc_lo in LO; lia | lia | lia | assumption
        | unfold rc_lo in LO; lia | exact AU | unfold rc_lo in LO; lia | exact AK |].
      step. step. if_false. step. step. if_false. do 10 step.
      release_frame HDR ST1 (bv_unsigned sp + -56)%Z. release_frame HD ST1 (bv_unsigned sp + -48)%Z. release_frame FRS ST1 (bv_unsigned sp).
      (* [comment removed for export] *)
      pose proof (PB_apart K _ _ _ _ _ _ _ _ _ _ G1 EPB1) as [APB1 API1].
      pose proof (GIo_PB_block K _ _ _ _ _ _ _ _ _ G1 ltac:(rewrite EPB1; right; left; reflexivity)) as (R1 & R2 & R3 & R4 & R5 & R6).
      pose proof WF1 as (_ & _ & W3' & _).
      set (FP2 := [(P + 520, P + 544); (PKT, PKT + 8)]%Z) in *.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
        assert (AG2 : agrees_on (fun a => outside FP2 a) m2 mm) by (eapply agrees_on_of_munch; [exact MU2 | exact WM2 | intros a _ Ho; exact Ho]);
        unhide CE1; unhide CO1; unhide BUF1; unhide PRIV1; unhide IFS1;
        destruct (pcap_aux_agree p' P B1 I1 pad1 bs1 m2 mm _ AG2) as (BUF' & PRIV' & IFS'); [ | | | lia | exact BUF1 | exact PRIV1 | exact IFS1 |]
      end.
      { intros a Ha. subst FP2. cbn [outside]. unfold rc_lo in LO. lia. }
      { intros a Ha. subst FP2. cbn [outside]. unfold PCAP_PRIV_OFF in Ha. unfold rc_lo in LO. lia. }
      { intros sg q Hq a Ha. subst FP2. cbn [outside]. destruct (API1 sg q Hq) as [X1 X2].
        pose proof (GIo_PB_block K _ _ _ _ _ _ _ _ _ G1 ltac:(rewrite EPB1; unfold pcap_blocks; rewrite Hq; right; right; left; reflexivity)) as (I1' & I2 & I3 & I4 & I5 & I6).
        unfold rc_lo in LO. clear - Ha X1 PS1 K1 I4 SPW LO BU. lia. }
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
        assert (CE' : rw_cells usegs mm (P + 216) [CB 304 (pj_g j1)]) by (eapply agrees_rw_cells; [exact AG2 | exact CE1 | intros a Ha; subst FP2; cbn [outside cells_size csize Nat.add] in *; unfold rc_lo in LO; lia]);
        assert (CO' : rw_cells usegs mm (P + 544) (pc_ops p' (C8 (Z_to_bv 64 (pk_stats PK))) (C8 (Z_to_bv 64 (pk_oneshot PK))) j1))
          by (eapply agrees_rw_cells; [exact AG2 | exact CO1 | intros a Ha; subst FP2; cbn [outside cells_size csize Nat.add pc_ops] in *; unfold rc_lo in LO; lia]);
        lazymatch goal with HPC : rw_cells _ mm (P + 520)%Z _ |- _ =>
          pose proof (pcap_cells_join4 mm P p' B1 (C8 (Z_to_bv 64 Af1)) (C8 (Z_to_bv 64 (pk_stats PK))) (C8 (Z_to_bv 64 (pk_oneshot PK))) j1 _ h
                        eq_refl CA1 CE' eq_refl (hdr_cells_of_3 _ _ h HPC) CO') as J end;
        assert (FW2 : Forall (pcap_iv R PB1) FP2)
          by (subst FP2; apply Forall_cons; [right; rewrite EPB1; unfold iv_in_block, pcap_blocks; apply Exists_cons_hd; cbn [cb_addr cb_size fst snd]; lia|];
              apply Forall_cons; [left; cbn [fst snd]; unfold rc_lo; lia| apply Forall_nil]);
        apply evt_done; subst POSTQ; cbv beta iota;
        lazymatch goal with PO : rw_cells _ mm PKT [C8 ?v] |- _ => exists (Z_to_bv 64 1), mm, PB1, (C8 v) end
      end.
      split. { unfold hpost_regs. repeat (lazymatch goal with |- ex _ => eexists end). reflexivity. }
      split; [exact OF1|]. split; [assumption|]. split; [assumption|].
      split. { eapply agrees_on_trans; [exact AGab|]. eapply agrees_on_weaken; [exact AG2|]. intros a [[Ha|Ha] Hn]; subst FP2; cbn [outside].
               - unfold rc_lo in LO. lia.
               - destruct (GIo_CLc_facts K _ _ _ _ _ _ _ G1 Ha) as [Hc Hnb]. split; [|lia].
                 intros Hin. apply Hnb. rewrite EPB1. unfold pcap_blocks, in_block. apply Exists_cons_hd. cbn [cb_addr cb_size fst snd]. lia. }
      split. { eapply (GIo_pcap_frame K HFL SFL); [exact G1 | exact MU2 | exact WM2 | exact FW2]. }
      split. { intros _. eapply PCAPR_intro_set_header; [exact HinF1 | exact EPB1 | exact J | exact PRIV' | exact BUF' | exact PFX1 | exact IFS' | exact WF1 | exact Hcap | exact Hlen]. }
      split. { intros X. exfalso. lia. }
      split; [reflexivity|]. split; [left; reflexivity|]. split; [assumption|]. split; [assumption| reflexivity].
    - (* [comment removed for export] *)
      destruct (HH0 ltac:(lia)) as (hcs' & Hsz & HDR0). clear HH0 HH1.
      destruct (rw_cells_forget _ _ _ _ HDR0) as [hj HDR]. clear HDR0. rewrite Hsz in HDR.
      cbn [Z.ltb Z.eqb]. apply (implM_ret usegs).
      step. if_false. step. if_true. do 11 step.
      release_frame HDR ST1 (bv_unsigned sp + -56)%Z. release_frame HD ST1 (bv_unsigned sp + -48)%Z. release_frame FRS ST1 (bv_unsigned sp).
      apply evt_done; subst POSTQ; cbv beta iota. exists (Z_to_bv 64 0), m2, PB1, (CB 8 pkj).
      split. { unfold hpost_regs. repeat (lazymatch goal with |- ex _ => eexists end). reflexivity. }
      split; [exact OF1|]. split; [assumption|]. split; [assumption|]. split; [exact AGab|]. split; [exact G1|].
      split; [intros _; exact (PC1 ltac:(lia))|]. split; [intros X; exfalso; lia|].
      split; [reflexivity|]. split; [right; left; reflexivity|]. split; [assumption|]. split; [assumption| reflexivity].
    - (* [comment removed for export] *)
      destruct (HH0 ltac:(lia)) as (hcs' & Hsz & HDR0). clear HH0 HH1.
      destruct (rw_cells_forget _ _ _ _ HDR0) as [hj HDR]. clear HDR0. rewrite Hsz in HDR.
      cbn [Z.ltb Z.eqb]. apply (implM_ret usegs).
      step. if_true. do 9 step.
      release_frame HDR ST1 (bv_unsigned sp + -56)%Z. release_frame HD ST1 (bv_unsigned sp + -48)%Z. release_frame FRS ST1 (bv_unsigned sp).
      apply evt_done; subst POSTQ; cbv beta iota. exists (Z_to_bv 64 (-1)), m2, PB1, (CB 8 pkj).
      split. { unfold hpost_regs. repeat (lazymatch goal with |- ex _ => eexists end). reflexivity. }
      split; [exact OF1|]. split; [assumption|]. split; [assumption|]. split; [exact AGab|]. split; [exact G1|].
      split; [intros X; exfalso; lia|]. split; [intros _; exact (PCC1 eq_refl)|].
      split; [reflexivity|]. split; [right; right; reflexivity|]. split; [assumption|]. split; [assumption| reflexivity].
  Qed.
  End Sz2.
  Theorem offline_read_proof : ltac:(let t := eval cbv delta [offline_read_proof__stmt] in offline_read_proof__stmt in exact t).
  Proof using HFL NP_NG NP_PCAP SFL. red. intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m R s CLc PB FB lo P U PKT p fuel pd pkc. ltac2:(SecDiet.SzSec.closeP 'offline_read_proof__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.


  Definition next_ex_proof__stmt : Prop := pcap_next_ex_stmt HO K sites.
  Section Sz3.
  Variables ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m R s CLc PB FB lo P HP PKT p fuel hc pkc : ltac2:(SecDiet.SzSec.tyM 'next_ex_proof__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra).
  Lemma next_ex_proof__body : ltac2:(SecDiet.SzSec.bodyP 'next_ex_proof__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof using HFL NP_NG NP_PCAP SFL. pin_using (fun (HFL NP_NG NP_PCAP SFL : unit) => tt).
 intros PRE PC SITES -> -> -> HHP Hhc HPK Hpk U1 U2 K1 K2 D1 AH AK.
    destruct PRE as (G & ST & LO & BU & SPM & MI & TP & ALN).
    pose proof PC as (Af & HinF & (B & I & j & pad & bs & EPB & CELLS & PRIV & BUF & PFX & IFS & WF)).
    pose proof (GIo_PB_block K _ _ _ _ _ _ _ _ _ G ltac:(rewrite EPB; left; reflexivity)) as (P1 & P2 & P3 & P4 & P5 & P6).
    pose proof (GIo_block_ok K _ _ _ _ _ _ G ltac:(apply in_or_app; right; exact HinF)) as (A1 & _ & _ & A4 & _).
    cbn [cb_addr cb_size fst snd] in A1, A4. unfold FILE_BLOCK in A4.
    pose proof (psize_pos p) as PS. pose proof (GIo_spw K _ _ _ _ _ G) as SPW. unfold rc_lo in LO. unfold PCAP_L4_STACK in BU.
    pose proof (bv_unsigned_in_range 64 sp) as RSP.
    destruct (rw_cells_forget _ _ _ _ HPK) as [pkj HPc]. clear HPK. cbn [cells_size] in HPc. rewrite Hpk in HPc. change (8 + 0)%nat with 8%nat in HPc.
    destruct (rw_cells_forget _ _ _ _ HHP) as [hcj HH]. clear HHP. cbn [cells_size] in HH. rewrite Hhc in HH. change (8 + 0)%nat with 8%nat in HH.
    apply pcap_cells_split4 in CELLS as (CA & CE & CH & CO); [|reflexivity].
    hide BUF. hide PRIV. hide IFS. hide CE. hide CH.
    unfold pc_pre, PCAP_PRIV_OFF in CA. unfold pc_ops in CO.
    unfold Pcap.pcap_next_ex. cbn [mo_bind mo_ret MOps e_fenter e_fret fo_enter fo_ret fo_nop prims]. unfold PCAP_NEXT_EX_ENTRY.
    pose proof (munch_refl [(bv_unsigned sp - 32, bv_unsigned sp); (HP, HP + 8)]%Z m) as MU. pose proof (wmono_refl usegs m) as WM.
    ienter.
    carve_frame 32%nat ST.
    assert (P8 : (P mod 8 = 0)%Z) by (rewrite <- (Z.add_0_r P); apply aligned16_8; [exact P2| reflexivity]).
    do 3 step. if_false_by (eqz_false P ltac:(lia)). step. rewrite (and7_aligned P) by lia. step. if_false.
    assert (HPB : (0 < HP < 2^64)%Z).
    { pose proof (bv_unsigned_in_range 64 (rc_sp0 R)) as X. unfold bv_modulus in X. cbn in X.
      pose proof U2 as U2'. pose proof SPW as SPW'. unfold rc_spmain, usp0 in U2'. unfold usp0 in SPW'. lia. }
    do 5 step. if_false_by (eqz_false HP HPB). step. rewrite (and7_aligned HP ltac:(lia) AH). step. if_false.
    do 3 step. if_false_by (eqz_false Af ltac:(lia)). do 4 step.
    (* [comment removed for export] *)
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      assert (FW : Forall (pcap_iv R PB) [(bv_unsigned sp + -32, bv_unsigned sp); (HP, HP + 8)]%Z)
        by (apply Forall_cons; [left; cbn [fst snd]; unfold rc_lo; lia|]; apply Forall_cons; [left; cbn [fst snd]; unfold rc_lo; lia| apply Forall_nil]);
      assert (G0 : GIo K R s (CLc ++ PB) FB mm) by (eapply (GIo_pcap_frame K HFL SFL); [exact G | exact MU | exact WM | exact FW]);
      assert (AG0 : agrees_on (fun a => outside [(bv_unsigned sp + -32, bv_unsigned sp); (HP, HP + 8)]%Z a) m mm)
        by (eapply agrees_on_of_munch; [exact MU | exact WM | intros a _ Ho; exact Ho]);
      assert (PC0 : PCAPR P p PB FB mm)
        by (eapply PCAPR_agree; [exact AG0 | intros a Ha; pose proof (in_PB_below K _ _ _ _ _ _ _ G Ha); cbn [outside]; unfold rc_lo in *; lia | exact PC])
    end.
    clear CA CE CH CO PRIV BUF IFS AUX AUX0 AUX1 AUX2 AUX3.
    destruct (rw_cells_cut _ _ _ 3 FR) as [FRU FRS]. clear FR. cbn [firstn skipn cells_size csize Nat.add] in FRU, FRS.
    replace (bv_unsigned sp + -32 + Z.of_nat 24)%Z with (bv_unsigned sp + -8)%Z in FRS by lia.
    name_sp sp (-32)%Z.
    apply evt_done. eapply (implM_bind usegs).
    { eapply offline_read_proof;
        [ split; [exact G0|]; split; [rewrite Hsp; exact ST|]; split; [unfold rc_lo; lia|]; split; [unfold PCAP_L3_STACK; rewrite Hsp; lia|];
          split; [rewrite Hsp; lia|]; split; [assumption|]; split; [exact TP| first [exact ALN | rewrite Hsp; apply aln16_add; [exact ALN| reflexivity]]]
        | exact PC0 | rewrite SITES, Hsp; unfold D_OFFLINE_READ, D_NEXT_EX; f_equal; lia
        | reflexivity | reflexivity | reflexivity | exact Esp | exact FRU | exact HPc | reflexivity
        | rewrite Hsp; lia | lia | rewrite Hsp; lia | lia | lia
        | apply aln16_add with (k := (-32)%Z) in ALN; [|reflexivity]; apply Z.mod_divide in ALN; [|lia]; apply Z.mod_divide; [lia|]; destruct ALN as [q Hq]; exists (q * 2)%Z; lia
        | exact AK ]. }
    intros [st p'] s' ms' PO. cbv beta iota in PO. destruct_exs PO.
    destruct PO as (E & OF1 & MI1 & ST1 & AG1 & G1 & PC1 & PCC1 & -> & Hst & HU1 & HP1 & Hpk1).
    unfold hpost_regs in E. destruct_exs E. subst ms'. rewrite Hsp in *. unname_sp.
    rename x0 into m2. rename x1 into PB1. rename x2 into pk'.
    replace (ret_pc (Z_to_bv 64 84076)) with (Z_to_bv 64 84076) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
    rename m0 into m1.
    assert (KEEP : forall A cs, rw_cells usegs m1 A cs -> (bv_unsigned sp + -8 <= A)%Z -> (A + Z.of_nat (cells_size cs) <= PKT \/ PKT + 8 <= A)%Z -> rw_cells usegs m2 A cs).
    { intros A cs HC HA HD. eapply agrees_rw_cells; [exact AG1 | exact HC | intros a Ha; split; [left; lia| lia]]. }
    apply KEEP in FRS; [|lia|cbn [cells_size csize Nat.add]; lia]. apply KEEP in HH; [|lia|cbn [cells_size csize Nat.add]; lia]. clear KEEP.
    assert (AGab : agrees_on (fun a => client_keeps CLc (bv_unsigned sp) a /\ ~ (HP <= a < HP + 8) /\ ~ (PKT <= a < PKT + 8))%Z m m2).
    { eapply agrees_on_trans.
      - eapply agrees_on_weaken; [exact AG0|]. intros a [[Ha|Ha] [Hn1 Hn2]]; cbn [outside]; [lia|].
        destruct (GIo_CLc_facts K _ _ _ _ _ _ _ G Ha) as [Hc _]. unfold rc_lo in LO. lia.
      - eapply agrees_on_weaken; [exact AG1|]. intros a [[Ha|Ha] [Hn1 Hn2]]; [split; [left; lia| lia]|].
        split; [right; exact Ha| exact Hn2]. }
    apply (implM_ret usegs).
    destruct Hst as [-> | [-> | ->]].
    - step. if_true. do 3 step.
      release_frame HU1 ST1 (bv_unsigned sp + -8)%Z. release_frame FRS ST1 (bv_unsigned sp).
      apply evt_done; subst POSTQ; cbv beta iota. exists (Z_to_bv 64 1), m2, PB1, pk'.
      split. { unfold hpost_regs. repeat (lazymatch goal with |- ex _ => eexists end). reflexivity. }
      split; [exact OF1|]. split; [assumption|]. split; [assumption|]. split; [exact AGab|]. split; [exact G1|].
      split. { cbn [Z.eqb]. intros _; exact (PC1 ltac:(lia)). } split. { cbn [Z.eqb]. intros X; exfalso; lia. }
      split; [reflexivity|]. split; [left; reflexivity|]. split; [exact HH|]. split; [exact HP1| exact Hpk1].
    - step. if_false. do 4 step.
      release_frame HU1 ST1 (bv_unsigned sp + -8)%Z. release_frame FRS ST1 (bv_unsigned sp).
      apply evt_done; subst POSTQ; cbv beta iota. exists (Z_to_bv 64 (-2)), m2, PB1, pk'.
      split. { unfold hpost_regs. repeat (lazymatch goal with |- ex _ => eexists end). reflexivity. }
      split; [exact OF1|]. split; [assumption|]. split; [assumption|]. split; [exact AGab|]. split; [exact G1|].
      split. { cbn [Z.eqb]. intros _; exact (PC1 ltac:(lia)). } split. { cbn [Z.eqb]. intros X; exfalso; lia. }
      split; [reflexivity|]. split; [right; left; reflexivity|]. split; [exact HH|]. split; [exact HP1| exact Hpk1].
    - step. if_true. do 3 step.
      release_frame HU1 ST1 (bv_unsigned sp + -8)%Z. release_frame FRS ST1 (bv_unsigned sp).
      apply evt_done; subst POSTQ; cbv beta iota. exists (Z_to_bv 64 (-1)), m2, PB1, pk'.
      split. { unfold hpost_regs. repeat (lazymatch goal with |- ex _ => eexists end). reflexivity. }
      split; [exact OF1|]. split; [assumption|]. split; [assumption|]. split; [exact AGab|]. split; [exact G1|].
      split. { cbn [Z.eqb]. intros X; exfalso; lia. } split. { cbn [Z.eqb]. intros _; exact (PCC1 eq_refl). }
      split; [reflexivity|]. split; [right; right; reflexivity|]. split; [exact HH|]. split; [exact HP1| exact Hpk1].
  Qed.
  End Sz3.
  Theorem next_ex_proof : ltac:(let t := eval cbv delta [next_ex_proof__stmt] in next_ex_proof__stmt in exact t).
  Proof using HFL NP_NG NP_PCAP SFL. red. intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m R s CLc PB FB lo P HP PKT p fuel hc pkc. ltac2:(SecDiet.SzSec.closeP 'next_ex_proof__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.
End NextEx.

End WithCeil.
End TwB.
End F_pcap_next_ex.

(* [comment removed for export] *)
Module Fuzz_iface.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Sem.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import Tac Arr Bytes ITree Nodes Decode SysStep ImgSrc3.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Import Prelim Monad Fmt StdioCore Stdio PcapPrelim PcapTypes PcapPure Pcap Prog.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require GI. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require GIFacts__S3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require PcapRep. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.GI OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.GIFacts__S3.GIFacts OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.GIFacts__S3.Ifaces OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.PcapRep OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Pcap_iface__S3.Pcap_iface.
From OSSVerify.libpcap.fuzz_pcap.images Require Import Plain.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import Ceiling.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import LiaPin.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac lia_e2w2_base := first [ zify_prune; zify_noeuclid; Z.euclidean_division_equations_cleanup; xlia zchecker
                                 | zify_prune; Zify.zify; xlia zchecker | Zify.zify; xlia zchecker ].
Local Ltac ceil_mentioned := lazymatch goal with | |- context [@alloc_ceiling _] => idtac | _ : context [@alloc_ceiling _] |- _ => idtac end.
(* [comment removed for export] *)
Local Ltac lia ::= clear_unpinned; try (ceil_ok; ceil_mentioned; ceil_facts); pinned_lia_core.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

Notation mem := (word -> option byte).

(* [comment removed for export] *)
Section WithCeil.
Context {CEILV : CEIL}.
Definition FWRITE_ENTRY  : Z := 0x1b85c.
Definition REMOVE_ENTRY  : Z := 0x1ba5c.
Definition UNLINK_ENTRY  : Z := 0x2151c.
Definition CLOSE_ENTRY   : Z := 0x21488.
Definition MKSTEMP_ENTRY : Z := 0x17b18.      (* [comment removed for export] *)
Definition PRINTF_ENTRY  : Z := 0x1b9e4.
(* [comment removed for export] *)
Definition FMT_FAILED_REMOVE : Z := 0x10a93.  (* [comment removed for export] *)
Definition FMT_FAILED_OPEN   : Z := 0x104be.  (* [comment removed for export] *)
Definition FMT_PACKET_LENGTH : Z := 0x10e20.  (* [comment removed for export] *)
Definition FMT_COULDNT_OPEN  : Z := 0x10705.  (* [comment removed for export] *)
Definition STR_DEVNULL : Z := 0x10e6e.        (* [comment removed for export] *)
Definition STR_W : Z := 0x10da2.              (* [comment removed for export] *)
Definition STR_WB : Z := 0x10427.             (* [comment removed for export] *)
Definition STR_TEMPLATE : Z := 0x1075d.       (* [comment removed for export] *)
Definition OUTFILE_ADDR : Z := 0x339c0.       (* [comment removed for export] *)

(* [comment removed for export] *)
Definition unlink_name_ok (name : list byte) : Prop :=
  Namei.path_has_slash name = false /\ name <> Uapi.dot_path /\ name <> Namei.dotdot_path /\ (length name <= Uapi.NAME_MAX)%nat.

Section FuzzIfaces.
  Context {H hptr : Type} (HO : HeapOps H hptr) (K : modkit H hptr).
  #[local] Abbreviation cblk := (@cblock hptr).
  #[local] Abbreviation PS := (PState H hptr).
  #[local] Abbreviation GIO := (GIo K).
  #[local] Abbreviation SPO := (std_pre_o K).

  (* [comment removed for export] *)
  Definition fwrite_stmt_o : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (R : rctx) (s : PS) (CL FB : list cblk) (f : hptr) (Af SRC lo : Z) (src : list byte),
      SPO sp tp R s CL FB lo STDIO_STACK m -> In (f, Af, FILE_BLOCK) FB ->
      a0 = Z_to_bv 64 SRC -> a1 = Z_to_bv 64 1 -> a2 = Z_to_bv 64 (Z.of_nat (length src)) -> a3 = Z_to_bv 64 Af ->
      bytes_at ssegs m SRC src -> client_range R CL (bv_unsigned sp) SRC (Z.of_nat (length src)) ->
      (* [comment removed for export] *)
      (forall fs, files_lookup (ho_eqb HO) (lc_files (ps_libc s)) f = Some fs ->
                  zlength (f_wbuf fs) + Z.of_nat (length src) <= 2^26) ->
      implM ssegs (s_fwrite HO f (map bv_unsigned src)) s
        (fun r s' ms' => exists a0v m', hpost_regs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0v m' ms'
           /\ ps_outfile s' = ps_outfile s /\ mem_inv ssegs m' /\ stk ssegs m' lo (bv_unsigned sp) /\ agrees_on (client_keeps CL (bv_unsigned sp)) m m'
           /\ GIO R s' CL FB m' /\ a0v = Z_to_bv 64 r /\ 0 <= r <= Z.of_nat (length src))
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 FWRITE_ENTRY) fc None m (seg_rom ssegs)).

  (* [comment removed for export] *)
  Definition remove_stmt_o : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (R : rctx) (s : PS) (CL FB : list cblk) (lo NAME : Z) (name : list byte),
      SPO sp tp R s CL FB lo STDIO_STACK m -> a0 = Z_to_bv 64 NAME ->
      bytes_at ssegs m NAME (name ++ [Z_to_bv 8 0]) -> ~ In (Z_to_bv 8 0) name -> (1 <= length name <= 4095)%nat ->
      client_range R CL (bv_unsigned sp) NAME (Z.of_nat (length name) + 1) -> unlink_name_ok name ->
      implM ssegs (s_remove (map bv_unsigned name)) s
        (fun r s' ms' => exists a0v m', hpost_regs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0v m' ms'
           /\ ps_outfile s' = ps_outfile s /\ mem_inv ssegs m' /\ stk ssegs m' lo (bv_unsigned sp) /\ agrees_on (client_keeps CL (bv_unsigned sp)) m m'
           /\ GIO R s' CL FB m' /\ a0v = Z_to_bv 64 r
           /\ (r = 0 \/ (r = -1 /\ rw_cells ssegs m' (utp R + -164) [C4 (Z_to_bv 64 (lc_errno (ps_libc s')))]
                               /\ 0 <= lc_errno (ps_libc s') < 2^31)))
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 REMOVE_ENTRY) fc None m (seg_rom ssegs)).

  (* [comment removed for export] *)
  Definition unlink_stmt_o : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (R : rctx) (s : PS) (CL FB : list cblk) (lo NAME : Z) (name : list byte),
      SPO sp tp R s CL FB lo STDIO_STACK m -> a0 = Z_to_bv 64 NAME ->
      bytes_at ssegs m NAME (name ++ [Z_to_bv 8 0]) -> ~ In (Z_to_bv 8 0) name -> (1 <= length name <= 4095)%nat ->
      client_range R CL (bv_unsigned sp) NAME (Z.of_nat (length name) + 1) -> unlink_name_ok name ->
      implM ssegs (s_unlink (map bv_unsigned name)) s
        (fun r s' ms' => exists a0v m', hpost_regs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0v m' ms'
           /\ ps_outfile s' = ps_outfile s /\ mem_inv ssegs m' /\ stk ssegs m' lo (bv_unsigned sp) /\ agrees_on (client_keeps CL (bv_unsigned sp)) m m'
           /\ GIO R s' CL FB m' /\ a0v = Z_to_bv 64 r /\ (r = 0 \/ r = -1))
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 UNLINK_ENTRY) fc None m (seg_rom ssegs)).

  (* [comment removed for export] *)
  Definition close_stmt_o : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (R : rctx) (s : PS) (CL FB : list cblk) (lo fd : Z),
      SPO sp tp R s CL FB lo STDIO_STACK m -> a0 = Z_to_bv 64 fd -> 3 <= fd < 2^31 ->
      implM ssegs (s_close fd) s
        (fun _ s' ms' => exists a0v m', hpost_regs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0v m' ms'
           /\ ps_outfile s' = ps_outfile s /\ mem_inv ssegs m' /\ stk ssegs m' lo (bv_unsigned sp) /\ agrees_on (client_keeps CL (bv_unsigned sp)) m m'
           /\ GIO R s' CL FB m')
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 CLOSE_ENTRY) fc None m (seg_rom ssegs)).

  (* [comment removed for export] *)
  Definition mkstemp_stmt_o : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (R : rctx) (s : PS) (CL FB : list cblk) (lo NAME : Z) (n : nat) (tmpl buf : list byte),
      SPO sp tp R s CL FB lo STDIO_STACK m -> a0 = Z_to_bv 64 NAME ->
      rw_cells ssegs m NAME [CB n buf] -> firstn (length tmpl + 1) buf = tmpl ++ [Z_to_bv 8 0] ->
      ~ In (Z_to_bv 8 0) tmpl -> tmpl = map b8 TEMPLATE ->   (* [comment removed for export] *)
      (length tmpl + 9 <= n)%nat -> (n <= 4096)%nat ->   (* [comment removed for export] *)
      client_range R CL (bv_unsigned sp) NAME (Z.of_nat n) ->
      implM ssegs (s_mkstemp (map bv_unsigned tmpl)) s
        (fun r s' ms' => exists a0v m' buf', hpost_regs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0v m' ms'
           /\ ps_outfile s' = ps_outfile s /\ mem_inv ssegs m' /\ stk ssegs m' lo (bv_unsigned sp)
           /\ agrees_on (fun a => client_keeps CL (bv_unsigned sp) a /\ ~ (NAME <= a < NAME + Z.of_nat n)) m m'
           /\ GIO R s' CL FB m'
           /\ a0v = Z_to_bv 64 (snd r) /\ (snd r = -1 \/ 3 <= snd r < 2^31)
           /\ rw_cells ssegs m' NAME [CB n buf'] /\ firstn (length (fst r) + 1) buf' = map b8 (fst r) ++ [Z_to_bv 8 0]
           /\ Forall (fun z => 0 < z < 256) (fst r) /\ (length (fst r) <= length tmpl)%nat
           /\ (0 <= snd r -> Namei.path_has_slash (map b8 (fst r)) = false /\ map b8 (fst r) <> Uapi.dot_path /\ map b8 (fst r) <> Namei.dotdot_path))
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 MKSTEMP_ENTRY) fc None m (seg_rom ssegs)).

  (* [comment removed for export] *)
  Definition printf_d_stmt_o (FMT : Z) (mk : Z -> list (list Z)) : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (R : rctx) (s : PS) (CL FB : list cblk) (lo v : Z),
      SPO sp tp R s CL FB lo STDIO_STACK m -> a0 = Z_to_bv 64 FMT -> a1 = Z_to_bv 64 v -> 0 <= v < 2^31 ->
      implM ssegs (s_printf (mk v)) s
        (fun _ s' ms' => exists a0v m', hpost_regs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0v m' ms'
           /\ ps_outfile s' = ps_outfile s /\ mem_inv ssegs m' /\ stk ssegs m' lo (bv_unsigned sp) /\ agrees_on (client_keeps CL (bv_unsigned sp)) m m'
           /\ GIO R s' CL FB m')
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 PRINTF_ENTRY) fc None m (seg_rom ssegs)).
End FuzzIfaces.

End WithCeil.

(* [comment removed for export] *)
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require ImgTgtUbsan.
From OSSVerify.libpcap.fuzz_pcap.images Require Ubsan.
Module TwB.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Sem.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Tac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Arr OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Bytes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ITree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Nodes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Decode OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.SysStep OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ImgTgtUbsan.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Monad OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Fmt OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.StdioCore OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Stdio OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapPrelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapTypes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapPure OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Pcap OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prog.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.GI.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.GIFacts__S3.GIFacts.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.GIFacts__S3.Ifaces.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.PcapRep.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Pcap_iface__S3.Pcap_iface.TwB.
Import OSSVerify.libpcap.fuzz_pcap.images.Ubsan.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Ceiling.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.LiaPin.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac lia_e2w2_base := first [ zify_prune; zify_noeuclid; Z.euclidean_division_equations_cleanup; xlia zchecker
                                 | zify_prune; Zify.zify; xlia zchecker | Zify.zify; xlia zchecker ].
Local Ltac ceil_mentioned := lazymatch goal with | |- context [@alloc_ceiling _] => idtac | _ : context [@alloc_ceiling _] |- _ => idtac end.
(* [comment removed for export] *)
Local Ltac lia ::= clear_unpinned; try (ceil_ok; ceil_mentioned; ceil_facts); pinned_lia_core.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

Notation mem := (word -> option byte).

(* [comment removed for export] *)
Section WithCeil.
Context {CEILV : CEIL}.
Definition FWRITE_ENTRY  : Z := 0x1c01c.
Definition REMOVE_ENTRY  : Z := 0x1c21c.
Definition UNLINK_ENTRY  : Z := 0x21cdc.
Definition CLOSE_ENTRY   : Z := 0x21c48.
Definition MKSTEMP_ENTRY : Z := 0x182d8.      (* [comment removed for export] *)
Definition PRINTF_ENTRY  : Z := 0x1c1a4.
(* [comment removed for export] *)
Definition FMT_FAILED_REMOVE : Z := 0x10a93.  (* [comment removed for export] *)
Definition FMT_FAILED_OPEN   : Z := 0x104be.  (* [comment removed for export] *)
Definition FMT_PACKET_LENGTH : Z := 0x10e20.  (* [comment removed for export] *)
Definition FMT_COULDNT_OPEN  : Z := 0x10705.  (* [comment removed for export] *)
Definition STR_DEVNULL : Z := 0x10e6e.        (* [comment removed for export] *)
Definition STR_W : Z := 0x10da2.              (* [comment removed for export] *)
Definition STR_WB : Z := 0x10427.             (* [comment removed for export] *)
Definition STR_TEMPLATE : Z := 0x1075d.       (* [comment removed for export] *)
Definition OUTFILE_ADDR : Z := 0x34180.       (* [comment removed for export] *)

(* [comment removed for export] *)
Definition unlink_name_ok (name : list byte) : Prop :=
  Namei.path_has_slash name = false /\ name <> Uapi.dot_path /\ name <> Namei.dotdot_path /\ (length name <= Uapi.NAME_MAX)%nat.

Section FuzzIfaces.
  Context {H hptr : Type} (HO : HeapOps H hptr) (K : modkit H hptr).
  #[local] Abbreviation cblk := (@cblock hptr).
  #[local] Abbreviation PS := (PState H hptr).
  #[local] Abbreviation GIO := (GIo K).
  #[local] Abbreviation SPO := (std_pre_o K).

  (* [comment removed for export] *)
  Definition fwrite_stmt_o : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (R : rctx) (s : PS) (CL FB : list cblk) (f : hptr) (Af SRC lo : Z) (src : list byte),
      SPO sp tp R s CL FB lo STDIO_STACK m -> In (f, Af, FILE_BLOCK) FB ->
      a0 = Z_to_bv 64 SRC -> a1 = Z_to_bv 64 1 -> a2 = Z_to_bv 64 (Z.of_nat (length src)) -> a3 = Z_to_bv 64 Af ->
      bytes_at usegs m SRC src -> client_range R CL (bv_unsigned sp) SRC (Z.of_nat (length src)) ->
      (* [comment removed for export] *)
      (forall fs, files_lookup (ho_eqb HO) (lc_files (ps_libc s)) f = Some fs ->
                  zlength (f_wbuf fs) + Z.of_nat (length src) <= 2^26) ->
      implM usegs (s_fwrite HO f (map bv_unsigned src)) s
        (fun r s' ms' => exists a0v m', hpost_regs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0v m' ms'
           /\ ps_outfile s' = ps_outfile s /\ mem_inv usegs m' /\ stk usegs m' lo (bv_unsigned sp) /\ agrees_on (client_keeps CL (bv_unsigned sp)) m m'
           /\ GIO R s' CL FB m' /\ a0v = Z_to_bv 64 r /\ 0 <= r <= Z.of_nat (length src))
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 FWRITE_ENTRY) fc None m (seg_rom usegs)).

  (* [comment removed for export] *)
  Definition remove_stmt_o : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (R : rctx) (s : PS) (CL FB : list cblk) (lo NAME : Z) (name : list byte),
      SPO sp tp R s CL FB lo STDIO_STACK m -> a0 = Z_to_bv 64 NAME ->
      bytes_at usegs m NAME (name ++ [Z_to_bv 8 0]) -> ~ In (Z_to_bv 8 0) name -> (1 <= length name <= 4095)%nat ->
      client_range R CL (bv_unsigned sp) NAME (Z.of_nat (length name) + 1) -> unlink_name_ok name ->
      implM usegs (s_remove (map bv_unsigned name)) s
        (fun r s' ms' => exists a0v m', hpost_regs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0v m' ms'
           /\ ps_outfile s' = ps_outfile s /\ mem_inv usegs m' /\ stk usegs m' lo (bv_unsigned sp) /\ agrees_on (client_keeps CL (bv_unsigned sp)) m m'
           /\ GIO R s' CL FB m' /\ a0v = Z_to_bv 64 r
           /\ (r = 0 \/ (r = -1 /\ rw_cells usegs m' (utp R + -164) [C4 (Z_to_bv 64 (lc_errno (ps_libc s')))]
                               /\ 0 <= lc_errno (ps_libc s') < 2^31)))
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 REMOVE_ENTRY) fc None m (seg_rom usegs)).

  (* [comment removed for export] *)
  Definition unlink_stmt_o : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (R : rctx) (s : PS) (CL FB : list cblk) (lo NAME : Z) (name : list byte),
      SPO sp tp R s CL FB lo STDIO_STACK m -> a0 = Z_to_bv 64 NAME ->
      bytes_at usegs m NAME (name ++ [Z_to_bv 8 0]) -> ~ In (Z_to_bv 8 0) name -> (1 <= length name <= 4095)%nat ->
      client_range R CL (bv_unsigned sp) NAME (Z.of_nat (length name) + 1) -> unlink_name_ok name ->
      implM usegs (s_unlink (map bv_unsigned name)) s
        (fun r s' ms' => exists a0v m', hpost_regs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0v m' ms'
           /\ ps_outfile s' = ps_outfile s /\ mem_inv usegs m' /\ stk usegs m' lo (bv_unsigned sp) /\ agrees_on (client_keeps CL (bv_unsigned sp)) m m'
           /\ GIO R s' CL FB m' /\ a0v = Z_to_bv 64 r /\ (r = 0 \/ r = -1))
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 UNLINK_ENTRY) fc None m (seg_rom usegs)).

  (* [comment removed for export] *)
  Definition close_stmt_o : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (R : rctx) (s : PS) (CL FB : list cblk) (lo fd : Z),
      SPO sp tp R s CL FB lo STDIO_STACK m -> a0 = Z_to_bv 64 fd -> 3 <= fd < 2^31 ->
      implM usegs (s_close fd) s
        (fun _ s' ms' => exists a0v m', hpost_regs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0v m' ms'
           /\ ps_outfile s' = ps_outfile s /\ mem_inv usegs m' /\ stk usegs m' lo (bv_unsigned sp) /\ agrees_on (client_keeps CL (bv_unsigned sp)) m m'
           /\ GIO R s' CL FB m')
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 CLOSE_ENTRY) fc None m (seg_rom usegs)).

  (* [comment removed for export] *)
  Definition mkstemp_stmt_o : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (R : rctx) (s : PS) (CL FB : list cblk) (lo NAME : Z) (n : nat) (tmpl buf : list byte),
      SPO sp tp R s CL FB lo STDIO_STACK m -> a0 = Z_to_bv 64 NAME ->
      rw_cells usegs m NAME [CB n buf] -> firstn (length tmpl + 1) buf = tmpl ++ [Z_to_bv 8 0] ->
      ~ In (Z_to_bv 8 0) tmpl -> tmpl = map b8 TEMPLATE ->   (* [comment removed for export] *)
      (length tmpl + 9 <= n)%nat -> (n <= 4096)%nat ->   (* [comment removed for export] *)
      client_range R CL (bv_unsigned sp) NAME (Z.of_nat n) ->
      implM usegs (s_mkstemp (map bv_unsigned tmpl)) s
        (fun r s' ms' => exists a0v m' buf', hpost_regs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0v m' ms'
           /\ ps_outfile s' = ps_outfile s /\ mem_inv usegs m' /\ stk usegs m' lo (bv_unsigned sp)
           /\ agrees_on (fun a => client_keeps CL (bv_unsigned sp) a /\ ~ (NAME <= a < NAME + Z.of_nat n)) m m'
           /\ GIO R s' CL FB m'
           /\ a0v = Z_to_bv 64 (snd r) /\ (snd r = -1 \/ 3 <= snd r < 2^31)
           /\ rw_cells usegs m' NAME [CB n buf'] /\ firstn (length (fst r) + 1) buf' = map b8 (fst r) ++ [Z_to_bv 8 0]
           /\ Forall (fun z => 0 < z < 256) (fst r) /\ (length (fst r) <= length tmpl)%nat
           /\ (0 <= snd r -> Namei.path_has_slash (map b8 (fst r)) = false /\ map b8 (fst r) <> Uapi.dot_path /\ map b8 (fst r) <> Namei.dotdot_path))
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 MKSTEMP_ENTRY) fc None m (seg_rom usegs)).

  (* [comment removed for export] *)
  Definition printf_d_stmt_o (FMT : Z) (mk : Z -> list (list Z)) : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (R : rctx) (s : PS) (CL FB : list cblk) (lo v : Z),
      SPO sp tp R s CL FB lo STDIO_STACK m -> a0 = Z_to_bv 64 FMT -> a1 = Z_to_bv 64 v -> 0 <= v < 2^31 ->
      implM usegs (s_printf (mk v)) s
        (fun _ s' ms' => exists a0v m', hpost_regs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0v m' ms'
           /\ ps_outfile s' = ps_outfile s /\ mem_inv usegs m' /\ stk usegs m' lo (bv_unsigned sp) /\ agrees_on (client_keeps CL (bv_unsigned sp)) m m'
           /\ GIO R s' CL FB m')
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 PRINTF_ENTRY) fc None m (seg_rom usegs)).
End FuzzIfaces.

End WithCeil.
End TwB.
End Fuzz_iface.

(* [comment removed for export] *)
Module Pcap_iface_ng.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool String.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Run.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import Tac Arr Bytes ITree Nodes Decode SysStep MonadX Image ImgSrc3.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Prelim Monad Fmt StdioCore Stdio PcapPrelim PcapTypes PcapPure Pcap Prog. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Adapter__Spec. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Monad OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Fmt OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.StdioCore OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Stdio OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapPrelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapTypes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapPure OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Pcap OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prog OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Adapter__Spec.StartupModel.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require Printf_kit__Musl. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require AmoStep__Musl. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_kit__Musl.StartupKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.CellsExtra.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require GI. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require GIFacts__S3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require PcapRep. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.GI OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.GIFacts__S3.Ifaces OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.PcapRep OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Pcap_iface__S3.Pcap_iface.
From OSSVerify.libpcap.fuzz_pcap.images Require Import Plain.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import Ceiling.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import LiaPin.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac lia ::= pinned_lia.
Import ListNotations.
Open Scope Z_scope.

Section WithCeil.
Context {CEILV : CEIL}.
Definition READ_BYTES_ENTRY : Z := 0x16b48.
(* [comment removed for export] *)
Definition READ_BYTES_STACK : Z := PCAP_L1_STACK + 64.
Definition READ_BLOCK_ENTRY : Z := 0x16c20.
Definition READ_BLOCK_STACK : Z := PCAP_L1_STACK + 96.
Definition ADD_INTERFACE_ENTRY : Z := 0x16f44.
(* [comment removed for export] *)
Definition ADD_INTERFACE_STACK : Z := MALLOC_STACK + 112.

Section NgIface.
  Context {H hptr : Type} (HO : HeapOps H hptr) (K : modkit H hptr) (sites : stack_site -> Z).
  #[local] Notation cblk := (@cblock hptr).
  #[local] Notation PS := (PState H hptr).
  #[local] Notation pcapT := (PcapTypes.pcap hptr hptr).

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition read_bytes_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (R : rctx) (CL FB : list cblk) (lo D n EB : Z) (foe : bool) (ej : list byte) (m : mem) (o : option hptr) : (rb_status * list Z) -> PS -> machine_state -> Prop :=
    fun r s' ms' => let '(st, got) := r in exists a0v m' junk',
      hpost_regs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0v m' ms'
      /\ ps_outfile s' = o /\ mem_inv ssegs m' /\ stk ssegs m' lo (bv_unsigned sp)
      /\ agrees_on (fun a => client_keeps CL (bv_unsigned sp) a /\ ~ (D <= a < D + n) /\ ~ (EB <= a < EB + 256)) m m'
      /\ GIo K R s' CL FB m'
      /\ rw_cells ssegs m' D [CB (length got) (map b8 got); CB (Z.to_nat n - length got) junk']
      /\ Forall (fun z => 0 <= z < 256) got /\ 0 <= zlength got <= n
      /\ match st with
         | RBS_Ok => a0v = Z_to_bv 64 1 /\ zlength got = n /\ rw_cells ssegs m' EB [CB 256 ej]
         | RBS_Eof => a0v = Z_to_bv 64 0 /\ zlength got = 0 /\ foe = false /\ rw_cells ssegs m' EB [CB 256 ej]
         | RBS_Err msg => exists junk'', a0v = Z_to_bv 64 (-1)
             /\ rw_cells ssegs m' EB [CB (length msg + 1) (map b8 msg ++ [Z_to_bv 8 0]); CB (255 - length msg) junk''] /\ Z.of_nat (length msg) < 256
             /\ Forall (fun z => 0 < z < 256) msg
         end.

  Definition read_bytes_stmt : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (R : rctx) (s : PS) (CL FB : list cblk) (f : hptr) (Af D n EB lo : Z)
           (foe : bool) (dest : rdest hptr) (junk ej : list byte),
      std_pre_o K sp tp R s CL FB lo READ_BYTES_STACK m -> In (f, Af, FILE_BLOCK) FB ->
      eval_rdest HO fo_nop sites s dest = D ->
      a0 = Z_to_bv 64 Af -> a1 = Z_to_bv 64 D -> a2 = Z_to_bv 64 n -> a3 = Z_to_bv 64 (Z.b2z foe) -> a4 = Z_to_bv 64 EB ->
      0 <= n <= 2^30 ->
      rw_cells ssegs m D [CB (Z.to_nat n) junk] -> client_range R CL (bv_unsigned sp) D n ->
      rw_cells ssegs m EB [CB 256 ej] -> ((bv_unsigned sp <= EB /\ EB + 256 <= rc_spmain R) \/ iv_in_block CL (EB, EB + 256)) -> (D + n <= EB \/ EB + 256 <= D) ->
      EB mod 8 = 0 ->
      implM ssegs (read_bytes MOps (prims HO fo_nop sites) f dest n foe) s
        (read_bytes_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc R CL FB lo D n EB foe ej m (ps_outfile s))
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 READ_BYTES_ENTRY) fc None m (seg_rom ssegs)).


  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition blk_handle (p : pcapT) (s : pcap_ng_sf) (P B : Z) (m : mem) : Prop :=
    rw_cells ssegs m (P + 20) [C4 (Z_to_bv 64 (pc_bufsize p)); C8 (Z_to_bv 64 B)]
    /\ rw_cells ssegs m (P + 48) [C8 (Z_to_bv 64 (P + PCAP_PRIV_OFF)); C4 (Z_to_bv 64 (Z.b2z (pc_swapped p)))]
    /\ rw_cells ssegs m (P + 656) [C4 (Z_to_bv 64 (ng_max_blocksize s))]
    /\ 0 <= pc_bufsize p <= 2^30 /\ 0 <= ng_max_blocksize s <= 2^30 /\ 0 <= pc_bufalloc p < 2^32 /\ pc_bufsize p <= pc_bufalloc p.

  (* [comment removed for export] *)
  Definition same_meta (p' p : pcapT) : Prop :=
    pc_version_major p' = pc_version_major p /\ pc_version_minor p' = pc_version_minor p /\ pc_snapshot p' = pc_snapshot p
    /\ pc_linktype p' = pc_linktype p /\ pc_linktype_ext p' = pc_linktype_ext p /\ pc_tstamp_precision p' = pc_tstamp_precision p
    /\ pc_break_loop p' = pc_break_loop p /\ pc_errbuf p' = pc_errbuf p /\ pc_header p' = pc_header p.

  Definition read_block_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (R : rctx) (C1 C2 FB : list cblk) (lo P CUR EB : Z) (p : pcapT) (s : pcap_ng_sf) (ej : list byte) (m : mem) (o : option hptr)
      : block_result -> PS -> machine_state -> Prop :=
    fun r s' ms' => exists a0v m' (p' : pcapT) B' bs',
      hpost_regs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0v m' ms'
      /\ ps_outfile s' = o /\ mem_inv ssegs m' /\ stk ssegs m' lo (bv_unsigned sp)
      /\ agrees_on (fun a => client_keeps (C1 ++ C2) (bv_unsigned sp) a /\ ~ (P + 24 <= a < P + 32)
                             /\ ~ (CUR <= a < CUR + 24) /\ ~ (EB <= a < EB + 256)) m m'
      /\ GIo K R s' ((pc_buffer p', B', pc_bufalloc p') :: C1 ++ C2) FB m'
      /\ blk_handle p' s P B' m'
      /\ rw_cells ssegs m' B' [CB (Z.to_nat (pc_bufalloc p')) bs'] /\ firstn (length (pc_bufdata p')) bs' = map b8 (pc_bufdata p')
      /\ Z.of_nat (length (pc_bufdata p')) <= pc_bufalloc p'
      /\ pc_priv p' = pc_priv p /\ pc_rfile p' = pc_rfile p /\ pc_self p' = pc_self p /\ pc_bufsize p' = pc_bufsize p /\ pc_swapped p' = pc_swapped p
      /\ same_meta p' p
      /\ match r with
         | RB_Ok c p'' => p'' = p' /\ a0v = Z_to_bv 64 1 /\ rw_cells ssegs m' EB [CB 256 ej]
             /\ (exists cpad, rw_cells ssegs m' CUR [C8 (Z_to_bv 64 (B' + 8)); C8 (Z_to_bv 64 (cur_remaining c)); C4 (Z_to_bv 64 (cur_block_type c)); CB 4 cpad])
             /\ cur_off c = 8 /\ 0 <= cur_remaining c /\ cur_remaining c + 12 <= pc_bufalloc p' /\ cur_remaining c + 12 <= 2^30 /\ 0 <= cur_block_type c < 2^32
             /\ Z.of_nat (length (pc_bufdata p')) = cur_remaining c + 12 /\ Forall (fun z => 0 <= z < 256) (pc_bufdata p')
         | RB_Eof p'' => p'' = p' /\ a0v = Z_to_bv 64 0 /\ rw_cells ssegs m' EB [CB 256 ej]
             /\ (exists ccs', rw_cells ssegs m' CUR ccs' /\ cells_size ccs' = 24%nat)
         | RB_Err msg p'' => p'' = p' /\ a0v = Z_to_bv 64 (-1)
             /\ (exists junk'', rw_cells ssegs m' EB [CB (length msg + 1) (map b8 msg ++ [Z_to_bv 8 0]); CB (255 - length msg) junk''])
             /\ Z.of_nat (length msg) < 256 /\ Forall (fun z => 0 < z < 256) msg
             /\ (exists ccs', rw_cells ssegs m' CUR ccs' /\ cells_size ccs' = 24%nat)
         end.

  Definition read_block_stmt : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (R : rctx) (st : PS) (C1 C2 FB : list cblk) (f : hptr) (Af P B CUR EB lo : Z)
           (p : pcapT) (s : pcap_ng_sf) (i : option hptr) (a_bhdr : rdest hptr) (bs ej : list byte) (ccs : list cell),
      std_pre_o K sp tp R st (C1 ++ (pc_buffer p, B, pc_bufalloc p) :: C2) FB lo READ_BLOCK_STACK m ->
      In (f, Af, FILE_BLOCK) FB -> pc_rfile p = f -> pc_priv p = PrivNg s i ->
      In (pc_self p, P, PCAP_NG_SF_TOTAL) (C1 ++ C2) ->
      (forall st', eval_rdest HO fo_nop sites st' a_bhdr = bv_unsigned sp - 96) ->
      a0 = Z_to_bv 64 Af -> a1 = Z_to_bv 64 P -> a2 = Z_to_bv 64 CUR -> a3 = Z_to_bv 64 EB ->
      blk_handle p s P B m -> rw_cells ssegs m B [CB (Z.to_nat (pc_bufalloc p)) bs] ->
      firstn (length (pc_bufdata p)) bs = map b8 (pc_bufdata p) -> Z.of_nat (length (pc_bufdata p)) <= pc_bufalloc p ->
      rw_cells ssegs m CUR ccs -> cells_size ccs = 24%nat -> bv_unsigned sp <= CUR -> CUR + 24 <= rc_spmain R -> CUR mod 8 = 0 ->
      rw_cells ssegs m EB [CB 256 ej] ->
      ((bv_unsigned sp <= EB /\ EB + 256 <= rc_spmain R /\ (EB + 256 <= CUR \/ CUR + 24 <= EB)) \/ (P + 216 = EB)) ->
      EB mod 8 = 0 ->
      implM ssegs (read_block MOps (prims HO fo_nop sites) a_bhdr p) st
        (read_block_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc R C1 C2 FB lo P CUR EB p s ej m (ps_outfile st))
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 READ_BLOCK_ENTRY) fc None m (seg_rom ssegs)).


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
    | Some q => (exists junk, rw_cells ssegs m I [CB (Z.to_nat (40 * ng_ifaces_size s)) junk]) /\ 1 <= ng_ifaces_size s < 2^26
    end.

  Definition add_interface_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (R : rctx) (C1 C2 FB : list cblk) (lo P B CUR EB : Z) (p : pcapT) (s : pcap_ng_sf) (c : cursor) (bs ej : list byte) (m : mem) (o : option hptr)
      : (bool * cursor * pcapT * list Z) -> PS -> machine_state -> Prop :=
    fun r st' ms' => let '(ok, c', p', msg) := r in
      exists a0v m' (s' : pcap_ng_sf) (i' : option hptr) (I' : Z) (pad' : list byte) (bs' : list byte),
      hpost_regs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0v m' ms'
      /\ ps_outfile st' = o /\ mem_inv ssegs m' /\ stk ssegs m' lo (bv_unsigned sp)
      /\ agrees_on (fun a => client_keeps (C1 ++ C2) (bv_unsigned sp) a /\ ~ (P + PCAP_PRIV_OFF <= a < P + PCAP_NG_SF_TOTAL)
                             /\ ~ (CUR <= a < CUR + 24) /\ ~ (EB <= a < EB + 256) /\ ~ (B <= a < B + pc_bufalloc p)) m m'
      /\ p' = set_ng s' i' (set_bufdata (pc_bufdata p') p)
      /\ GIo K R st' (IBLK i' I' s' ++ C1 ++ C2) FB m'
      /\ rw_cells ssegs m' (P + PCAP_PRIV_OFF) (ng_cells s' I' pad')
      /\ ng_user_tsresol s' = ng_user_tsresol s /\ ng_max_blocksize s' = ng_max_blocksize s /\ 0 <= ng_ifcount s' < 2^32 /\ 0 <= ng_ifaces_size s' < 2^32
      /\ rw_cells ssegs m' B [CB (Z.to_nat (pc_bufalloc p)) bs'] /\ firstn (length (pc_bufdata p')) bs' = map b8 (pc_bufdata p')
      /\ length (pc_bufdata p') = length (pc_bufdata p) /\ Forall (fun z => 0 <= z < 256) (pc_bufdata p')
      /\ a0v = Z_to_bv 64 (Z.b2z ok)
      /\ if ok then
           ifaces_ok p' I' m'
           /\ (exists cpad', rw_cells ssegs m' CUR (cursor_cells B c' cpad'))
           /\ 0 <= cur_remaining c' /\ cur_off c <= cur_off c' /\ cur_off c' + cur_remaining c' <= cur_off c + cur_remaining c
           /\ cur_block_type c' = cur_block_type c
           /\ rw_cells ssegs m' EB [CB 256 ej] /\ msg = []
         else
           ng_ifaces_closable s' i' I' m'
           /\ (exists ccs', rw_cells ssegs m' CUR ccs' /\ cells_size ccs' = 24%nat)
           /\ (exists junk'', rw_cells ssegs m' EB [CB (length msg + 1) (map b8 msg ++ [Z_to_bv 8 0]); CB (255 - length msg) junk''])
           /\ Z.of_nat (length msg) < 256 /\ Forall (fun z => 0 < z < 256) msg.

  (* [comment removed for export] *)
  Definition add_interface_stmt : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (R : rctx) (st : PS) (C1 C2 FB : list cblk) (P B I CUR EB lo idb_off : Z)
           (p : pcapT) (s : pcap_ng_sf) (i : option hptr) (c : cursor) (bs ej pad cpad : list byte),
      std_pre_o K sp tp R st (C1 ++ IBLK i I s ++ C2) FB lo ADD_INTERFACE_STACK m ->
      pc_priv p = PrivNg s i ->
      In (pc_self p, P, PCAP_NG_SF_TOTAL) (C1 ++ C2) -> In (pc_buffer p, B, pc_bufalloc p) (C1 ++ C2) ->
      P + PCAP_NG_SF_TOTAL <= B \/ B + pc_bufalloc p <= P ->
      a0 = Z_to_bv 64 P -> a1 = Z_to_bv 64 (B + idb_off) -> a2 = Z_to_bv 64 CUR -> a3 = Z_to_bv 64 EB ->
      rw_cells ssegs m (P + 48) [C8 (Z_to_bv 64 (P + PCAP_PRIV_OFF)); C4 (Z_to_bv 64 (Z.b2z (pc_swapped p)))] ->
      rw_cells ssegs m (P + PCAP_PRIV_OFF) (ng_cells s I pad) -> ifaces_ok p I m ->
      0 < ng_user_tsresol s < 2^64 -> 0 <= ng_max_blocksize s < 2^32 ->
      rw_cells ssegs m B [CB (Z.to_nat (pc_bufalloc p)) bs] -> firstn (length (pc_bufdata p)) bs = map b8 (pc_bufdata p) ->
      Z.of_nat (length (pc_bufdata p)) <= pc_bufalloc p < 2^32 -> Forall (fun z => 0 <= z < 256) (pc_bufdata p) ->
      rw_cells ssegs m CUR (cursor_cells B c cpad) -> bv_unsigned sp <= CUR -> CUR + 24 <= rc_spmain R -> CUR mod 8 = 0 ->
      0 <= idb_off -> cur_off c = idb_off + 8 -> 0 <= cur_remaining c -> cur_off c + cur_remaining c <= Z.of_nat (length (pc_bufdata p)) ->
      0 <= cur_block_type c < 2^32 ->
      rw_cells ssegs m EB [CB 256 ej] ->
      ((bv_unsigned sp <= EB /\ EB + 256 <= rc_spmain R /\ (EB + 256 <= CUR \/ CUR + 24 <= EB)) \/ (P + 216 = EB)) ->
      implM ssegs (add_interface MOps (prims HO fo_nop sites) p idb_off c) st
        (add_interface_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc R C1 C2 FB lo P B CUR EB p s c bs ej m (ps_outfile st))
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 ADD_INTERFACE_ENTRY) fc None m (seg_rom ssegs)).
End NgIface.

End WithCeil.

(* [comment removed for export] *)
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require ImgTgtUbsan.
From OSSVerify.libpcap.fuzz_pcap.images Require Ubsan.
Module TwB.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Strings.String.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Tac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Arr OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Bytes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ITree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Nodes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Decode OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.SysStep OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.MonadX OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Image OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ImgTgtUbsan.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Monad OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Fmt OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.StdioCore OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Stdio OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapPrelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapTypes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapPure OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Pcap OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prog OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Adapter__Spec.StartupModel.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_kit__Musl.StartupKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.CellsExtra.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.GI.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.GIFacts__S3.Ifaces.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.PcapRep.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Pcap_iface__S3.Pcap_iface.TwB.
Import OSSVerify.libpcap.fuzz_pcap.images.Ubsan.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Ceiling.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.LiaPin.
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

Section WithCeil.
Context {CEILV : CEIL}.
Definition READ_BYTES_ENTRY : Z := 0x1703c.
(* [comment removed for export] *)
Definition READ_BYTES_STACK : Z := PCAP_L1_STACK + 64.
Definition READ_BLOCK_ENTRY : Z := 0x17124.
Definition READ_BLOCK_STACK : Z := PCAP_L1_STACK + 96.
Definition ADD_INTERFACE_ENTRY : Z := 0x17524.
(* [comment removed for export] *)
Definition ADD_INTERFACE_STACK : Z := MALLOC_STACK + 112.

Section NgIface.
  Context {H hptr : Type} (HO : HeapOps H hptr) (K : modkit H hptr) (sites : stack_site -> Z).
  #[local] Notation cblk := (@cblock hptr).
  #[local] Notation PS := (PState H hptr).
  #[local] Notation pcapT := (PcapTypes.pcap hptr hptr).

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition read_bytes_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (R : rctx) (CL FB : list cblk) (lo D n EB : Z) (foe : bool) (ej : list byte) (m : mem) (o : option hptr) : (rb_status * list Z) -> PS -> machine_state -> Prop :=
    fun r s' ms' => let '(st, got) := r in exists a0v m' junk',
      hpost_regs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0v m' ms'
      /\ ps_outfile s' = o /\ mem_inv usegs m' /\ stk usegs m' lo (bv_unsigned sp)
      /\ agrees_on (fun a => client_keeps CL (bv_unsigned sp) a /\ ~ (D <= a < D + n) /\ ~ (EB <= a < EB + 256)) m m'
      /\ GIo K R s' CL FB m'
      /\ rw_cells usegs m' D [CB (length got) (map b8 got); CB (Z.to_nat n - length got) junk']
      /\ Forall (fun z => 0 <= z < 256) got /\ 0 <= zlength got <= n
      /\ match st with
         | RBS_Ok => a0v = Z_to_bv 64 1 /\ zlength got = n /\ rw_cells usegs m' EB [CB 256 ej]
         | RBS_Eof => a0v = Z_to_bv 64 0 /\ zlength got = 0 /\ foe = false /\ rw_cells usegs m' EB [CB 256 ej]
         | RBS_Err msg => exists junk'', a0v = Z_to_bv 64 (-1)
             /\ rw_cells usegs m' EB [CB (length msg + 1) (map b8 msg ++ [Z_to_bv 8 0]); CB (255 - length msg) junk''] /\ Z.of_nat (length msg) < 256
             /\ Forall (fun z => 0 < z < 256) msg
         end.

  Definition read_bytes_stmt : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (R : rctx) (s : PS) (CL FB : list cblk) (f : hptr) (Af D n EB lo : Z)
           (foe : bool) (dest : rdest hptr) (junk ej : list byte),
      std_pre_o K sp tp R s CL FB lo READ_BYTES_STACK m -> In (f, Af, FILE_BLOCK) FB ->
      eval_rdest HO fo_nop sites s dest = D ->
      a0 = Z_to_bv 64 Af -> a1 = Z_to_bv 64 D -> a2 = Z_to_bv 64 n -> a3 = Z_to_bv 64 (Z.b2z foe) -> a4 = Z_to_bv 64 EB ->
      0 <= n <= 2^30 ->
      rw_cells usegs m D [CB (Z.to_nat n) junk] -> client_range R CL (bv_unsigned sp) D n ->
      rw_cells usegs m EB [CB 256 ej] -> ((bv_unsigned sp <= EB /\ EB + 256 <= rc_spmain R) \/ iv_in_block CL (EB, EB + 256)) -> (D + n <= EB \/ EB + 256 <= D) ->
      EB mod 8 = 0 ->
      implM usegs (read_bytes MOps (prims HO fo_nop sites) f dest n foe) s
        (read_bytes_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc R CL FB lo D n EB foe ej m (ps_outfile s))
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 READ_BYTES_ENTRY) fc None m (seg_rom usegs)).


  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition blk_handle (p : pcapT) (s : pcap_ng_sf) (P B : Z) (m : mem) : Prop :=
    rw_cells usegs m (P + 20) [C4 (Z_to_bv 64 (pc_bufsize p)); C8 (Z_to_bv 64 B)]
    /\ rw_cells usegs m (P + 48) [C8 (Z_to_bv 64 (P + PCAP_PRIV_OFF)); C4 (Z_to_bv 64 (Z.b2z (pc_swapped p)))]
    /\ rw_cells usegs m (P + 656) [C4 (Z_to_bv 64 (ng_max_blocksize s))]
    /\ 0 <= pc_bufsize p <= 2^30 /\ 0 <= ng_max_blocksize s <= 2^30 /\ 0 <= pc_bufalloc p < 2^32 /\ pc_bufsize p <= pc_bufalloc p.

  (* [comment removed for export] *)
  Definition same_meta (p' p : pcapT) : Prop :=
    pc_version_major p' = pc_version_major p /\ pc_version_minor p' = pc_version_minor p /\ pc_snapshot p' = pc_snapshot p
    /\ pc_linktype p' = pc_linktype p /\ pc_linktype_ext p' = pc_linktype_ext p /\ pc_tstamp_precision p' = pc_tstamp_precision p
    /\ pc_break_loop p' = pc_break_loop p /\ pc_errbuf p' = pc_errbuf p /\ pc_header p' = pc_header p.

  Definition read_block_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (R : rctx) (C1 C2 FB : list cblk) (lo P CUR EB : Z) (p : pcapT) (s : pcap_ng_sf) (ej : list byte) (m : mem) (o : option hptr)
      : block_result -> PS -> machine_state -> Prop :=
    fun r s' ms' => exists a0v m' (p' : pcapT) B' bs',
      hpost_regs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0v m' ms'
      /\ ps_outfile s' = o /\ mem_inv usegs m' /\ stk usegs m' lo (bv_unsigned sp)
      /\ agrees_on (fun a => client_keeps (C1 ++ C2) (bv_unsigned sp) a /\ ~ (P + 24 <= a < P + 32)
                             /\ ~ (CUR <= a < CUR + 24) /\ ~ (EB <= a < EB + 256)) m m'
      /\ GIo K R s' ((pc_buffer p', B', pc_bufalloc p') :: C1 ++ C2) FB m'
      /\ blk_handle p' s P B' m'
      /\ rw_cells usegs m' B' [CB (Z.to_nat (pc_bufalloc p')) bs'] /\ firstn (length (pc_bufdata p')) bs' = map b8 (pc_bufdata p')
      /\ Z.of_nat (length (pc_bufdata p')) <= pc_bufalloc p'
      /\ pc_priv p' = pc_priv p /\ pc_rfile p' = pc_rfile p /\ pc_self p' = pc_self p /\ pc_bufsize p' = pc_bufsize p /\ pc_swapped p' = pc_swapped p
      /\ same_meta p' p
      /\ match r with
         | RB_Ok c p'' => p'' = p' /\ a0v = Z_to_bv 64 1 /\ rw_cells usegs m' EB [CB 256 ej]
             /\ (exists cpad, rw_cells usegs m' CUR [C8 (Z_to_bv 64 (B' + 8)); C8 (Z_to_bv 64 (cur_remaining c)); C4 (Z_to_bv 64 (cur_block_type c)); CB 4 cpad])
             /\ cur_off c = 8 /\ 0 <= cur_remaining c /\ cur_remaining c + 12 <= pc_bufalloc p' /\ cur_remaining c + 12 <= 2^30 /\ 0 <= cur_block_type c < 2^32
             /\ Z.of_nat (length (pc_bufdata p')) = cur_remaining c + 12 /\ Forall (fun z => 0 <= z < 256) (pc_bufdata p')
         | RB_Eof p'' => p'' = p' /\ a0v = Z_to_bv 64 0 /\ rw_cells usegs m' EB [CB 256 ej]
             /\ (exists ccs', rw_cells usegs m' CUR ccs' /\ cells_size ccs' = 24%nat)
         | RB_Err msg p'' => p'' = p' /\ a0v = Z_to_bv 64 (-1)
             /\ (exists junk'', rw_cells usegs m' EB [CB (length msg + 1) (map b8 msg ++ [Z_to_bv 8 0]); CB (255 - length msg) junk''])
             /\ Z.of_nat (length msg) < 256 /\ Forall (fun z => 0 < z < 256) msg
             /\ (exists ccs', rw_cells usegs m' CUR ccs' /\ cells_size ccs' = 24%nat)
         end.

  Definition read_block_stmt : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (R : rctx) (st : PS) (C1 C2 FB : list cblk) (f : hptr) (Af P B CUR EB lo : Z)
           (p : pcapT) (s : pcap_ng_sf) (i : option hptr) (a_bhdr : rdest hptr) (bs ej : list byte) (ccs : list cell),
      std_pre_o K sp tp R st (C1 ++ (pc_buffer p, B, pc_bufalloc p) :: C2) FB lo READ_BLOCK_STACK m ->
      In (f, Af, FILE_BLOCK) FB -> pc_rfile p = f -> pc_priv p = PrivNg s i ->
      In (pc_self p, P, PCAP_NG_SF_TOTAL) (C1 ++ C2) ->
      (forall st', eval_rdest HO fo_nop sites st' a_bhdr = bv_unsigned sp - 96) ->
      a0 = Z_to_bv 64 Af -> a1 = Z_to_bv 64 P -> a2 = Z_to_bv 64 CUR -> a3 = Z_to_bv 64 EB ->
      blk_handle p s P B m -> rw_cells usegs m B [CB (Z.to_nat (pc_bufalloc p)) bs] ->
      firstn (length (pc_bufdata p)) bs = map b8 (pc_bufdata p) -> Z.of_nat (length (pc_bufdata p)) <= pc_bufalloc p ->
      rw_cells usegs m CUR ccs -> cells_size ccs = 24%nat -> bv_unsigned sp <= CUR -> CUR + 24 <= rc_spmain R -> CUR mod 8 = 0 ->
      rw_cells usegs m EB [CB 256 ej] ->
      ((bv_unsigned sp <= EB /\ EB + 256 <= rc_spmain R /\ (EB + 256 <= CUR \/ CUR + 24 <= EB)) \/ (P + 216 = EB)) ->
      EB mod 8 = 0 ->
      implM usegs (read_block MOps (prims HO fo_nop sites) a_bhdr p) st
        (read_block_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc R C1 C2 FB lo P CUR EB p s ej m (ps_outfile st))
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 READ_BLOCK_ENTRY) fc None m (seg_rom usegs)).


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
    | Some q => (exists junk, rw_cells usegs m I [CB (Z.to_nat (40 * ng_ifaces_size s)) junk]) /\ 1 <= ng_ifaces_size s < 2^26
    end.

  Definition add_interface_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (R : rctx) (C1 C2 FB : list cblk) (lo P B CUR EB : Z) (p : pcapT) (s : pcap_ng_sf) (c : cursor) (bs ej : list byte) (m : mem) (o : option hptr)
      : (bool * cursor * pcapT * list Z) -> PS -> machine_state -> Prop :=
    fun r st' ms' => let '(ok, c', p', msg) := r in
      exists a0v m' (s' : pcap_ng_sf) (i' : option hptr) (I' : Z) (pad' : list byte) (bs' : list byte),
      hpost_regs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0v m' ms'
      /\ ps_outfile st' = o /\ mem_inv usegs m' /\ stk usegs m' lo (bv_unsigned sp)
      /\ agrees_on (fun a => client_keeps (C1 ++ C2) (bv_unsigned sp) a /\ ~ (P + PCAP_PRIV_OFF <= a < P + PCAP_NG_SF_TOTAL)
                             /\ ~ (CUR <= a < CUR + 24) /\ ~ (EB <= a < EB + 256) /\ ~ (B <= a < B + pc_bufalloc p)) m m'
      /\ p' = set_ng s' i' (set_bufdata (pc_bufdata p') p)
      /\ GIo K R st' (IBLK i' I' s' ++ C1 ++ C2) FB m'
      /\ rw_cells usegs m' (P + PCAP_PRIV_OFF) (ng_cells s' I' pad')
      /\ ng_user_tsresol s' = ng_user_tsresol s /\ ng_max_blocksize s' = ng_max_blocksize s /\ 0 <= ng_ifcount s' < 2^32 /\ 0 <= ng_ifaces_size s' < 2^32
      /\ rw_cells usegs m' B [CB (Z.to_nat (pc_bufalloc p)) bs'] /\ firstn (length (pc_bufdata p')) bs' = map b8 (pc_bufdata p')
      /\ length (pc_bufdata p') = length (pc_bufdata p) /\ Forall (fun z => 0 <= z < 256) (pc_bufdata p')
      /\ a0v = Z_to_bv 64 (Z.b2z ok)
      /\ if ok then
           ifaces_ok p' I' m'
           /\ (exists cpad', rw_cells usegs m' CUR (cursor_cells B c' cpad'))
           /\ 0 <= cur_remaining c' /\ cur_off c <= cur_off c' /\ cur_off c' + cur_remaining c' <= cur_off c + cur_remaining c
           /\ cur_block_type c' = cur_block_type c
           /\ rw_cells usegs m' EB [CB 256 ej] /\ msg = []
         else
           ng_ifaces_closable s' i' I' m'
           /\ (exists ccs', rw_cells usegs m' CUR ccs' /\ cells_size ccs' = 24%nat)
           /\ (exists junk'', rw_cells usegs m' EB [CB (length msg + 1) (map b8 msg ++ [Z_to_bv 8 0]); CB (255 - length msg) junk''])
           /\ Z.of_nat (length msg) < 256 /\ Forall (fun z => 0 < z < 256) msg.

  (* [comment removed for export] *)
  Definition add_interface_stmt : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (R : rctx) (st : PS) (C1 C2 FB : list cblk) (P B I CUR EB lo idb_off : Z)
           (p : pcapT) (s : pcap_ng_sf) (i : option hptr) (c : cursor) (bs ej pad cpad : list byte),
      std_pre_o K sp tp R st (C1 ++ IBLK i I s ++ C2) FB lo ADD_INTERFACE_STACK m ->
      pc_priv p = PrivNg s i ->
      In (pc_self p, P, PCAP_NG_SF_TOTAL) (C1 ++ C2) -> In (pc_buffer p, B, pc_bufalloc p) (C1 ++ C2) ->
      P + PCAP_NG_SF_TOTAL <= B \/ B + pc_bufalloc p <= P ->
      a0 = Z_to_bv 64 P -> a1 = Z_to_bv 64 (B + idb_off) -> a2 = Z_to_bv 64 CUR -> a3 = Z_to_bv 64 EB ->
      rw_cells usegs m (P + 48) [C8 (Z_to_bv 64 (P + PCAP_PRIV_OFF)); C4 (Z_to_bv 64 (Z.b2z (pc_swapped p)))] ->
      rw_cells usegs m (P + PCAP_PRIV_OFF) (ng_cells s I pad) -> ifaces_ok p I m ->
      0 < ng_user_tsresol s < 2^64 -> 0 <= ng_max_blocksize s < 2^32 ->
      rw_cells usegs m B [CB (Z.to_nat (pc_bufalloc p)) bs] -> firstn (length (pc_bufdata p)) bs = map b8 (pc_bufdata p) ->
      Z.of_nat (length (pc_bufdata p)) <= pc_bufalloc p < 2^32 -> Forall (fun z => 0 <= z < 256) (pc_bufdata p) ->
      rw_cells usegs m CUR (cursor_cells B c cpad) -> bv_unsigned sp <= CUR -> CUR + 24 <= rc_spmain R -> CUR mod 8 = 0 ->
      0 <= idb_off -> idb_off mod 4 = 0 -> cur_off c = idb_off + 8 -> 0 <= cur_remaining c -> cur_off c + cur_remaining c <= Z.of_nat (length (pc_bufdata p)) ->
      0 <= cur_block_type c < 2^32 ->
      rw_cells usegs m EB [CB 256 ej] ->
      ((bv_unsigned sp <= EB /\ EB + 256 <= rc_spmain R /\ (EB + 256 <= CUR \/ CUR + 24 <= EB)) \/ (P + 216 = EB)) ->
      implM usegs (add_interface MOps (prims HO fo_nop sites) p idb_off c) st
        (add_interface_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc R C1 C2 FB lo P B CUR EB p s c bs ej m (ps_outfile st))
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 ADD_INTERFACE_ENTRY) fc None m (seg_rom usegs)).
End NgIface.

End WithCeil.
End TwB.
End Pcap_iface_ng.
