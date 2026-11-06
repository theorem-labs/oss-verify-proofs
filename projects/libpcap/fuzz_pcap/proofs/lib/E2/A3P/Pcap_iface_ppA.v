(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Sem.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import Tac Arr Bytes.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Import Prelim PcapPrelim PcapTypes PcapPure.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import ExecF ITreeA Shadow RunDraw.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require Import AImg ABase.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require Import GIA PcapRepA Pcap_ifaceA.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Definition zbytes (d : list Z) : list byte := map (Z_to_bv 8) d.
Definition zarr (m : mem) (A : Z) (d : list Z) : Prop :=
  bytes_at asegs m A (zbytes d) /\ wr_at asegs m A (Z.of_nat (length d)) /\ Forall (fun x => 0 <= x < 256) d.

(* [comment removed for export] *)
Definition pkthdr_cells (ws wu : word) (h : pkthdr) : list cell :=
  [C8 ws; C8 wu; C4 (Z_to_bv 64 (h_caplen h)); C4 (Z_to_bv 64 (h_len h))].

Definition PP_ENTRY : Z := PCAP_POST_PROCESS_ENTRY.
Definition PP_FRAME : Z := 48.   (* [comment removed for export] *)

Section CANSEC1. Context {rc : runConstT} {tlsI : ABase.atlsT}.
Definition post_process_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (HA DA : Z) (ws wu : word) (linktype : Z) (swapped : bool) (hdr : pkthdr) (d : list Z) (lo : Z) (m : mem)
    : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch [(bv_unsigned sp - PP_FRAME, bv_unsigned sp); (HA + 20, HA + 24); (DA, DA + h_caplen hdr)] m m'
    /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo (bv_unsigned sp)
    /\ rw_cells asegs m' HA (pkthdr_cells ws wu (fst (pcapint_post_process linktype swapped hdr d)))
    /\ zarr m' DA (snd (pcapint_post_process linktype swapped hdr d)).

Definition post_process_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem) (RNG : footprint)
         (HA DA : Z) (ws wu : word) (linktype : Z) (swapped : bool) (hdr : pkthdr) (d : list Z) (lo : Z),
    stk asegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - PP_FRAME -> ATOP + 4096 <= lo ->
    rw_cells asegs m HA (pkthdr_cells ws wu hdr) ->
    zarr m DA d ->
    mem_inv asegs m -> artcells m ->
    a0 = Z_to_bv 64 linktype -> a1 = Z_to_bv 64 (Z.b2z swapped) -> a2 = Z_to_bv 64 HA -> a3 = Z_to_bv 64 DA ->
    0 <= linktype < 2^31 ->
    0 <= h_caplen hdr <= Z.of_nat (length d) -> Z.of_nat (length d) < 2^31 -> 0 <= h_len hdr < 2^32 ->
    (* [comment removed for export] *)
    aobjA RNG m HA 24 -> aobjA RNG m DA (Z.of_nat (length d)) ->
    HA + 24 <= ATOP -> DA + Z.of_nat (length d) <= ATOP ->
    (HA + 24 <= DA \/ DA + Z.of_nat (length d) <= HA) ->
    HA mod 8 = 0 -> DA mod 4 = 0 ->     (* [comment removed for export] *)
    rng RNG lo (bv_unsigned sp - lo) -> rng_aimg RNG -> rng_aimg_sh RNG ->
    evtF asegs RNG (post_process_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc HA DA ws wu linktype swapped hdr d lo m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 PP_ENTRY) fc None m (seg_rom asegs)).
End CANSEC1.

(* [comment removed for export] *)

Module TwB.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Sem.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Tac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Arr OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Bytes.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapPrelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapTypes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapPure.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.ExecF OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.ITreeA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.Shadow OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.RunDraw.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.GIA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.PcapRepA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.Pcap_ifaceA.TwB. Local Ltac Zify.zify_pre_hook ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB.twm_hook_1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Definition zbytes (d : list Z) : list byte := map (Z_to_bv 8) d.
Definition zarr (m : mem) (A : Z) (d : list Z) : Prop :=
  bytes_at asegs m A (zbytes d) /\ wr_at asegs m A (Z.of_nat (length d)) /\ Forall (fun x => 0 <= x < 256) d.

(* [comment removed for export] *)
Definition pkthdr_cells (ws wu : word) (h : pkthdr) : list cell :=
  [C8 ws; C8 wu; C4 (Z_to_bv 64 (h_caplen h)); C4 (Z_to_bv 64 (h_len h))].

Definition PP_ENTRY : Z := PCAP_POST_PROCESS_ENTRY.
Definition PP_FRAME : Z := 64.   (* [comment removed for export] *)

Section CANSEC1. Context {rc : runConstT} {tlsI : A3W.ABase.TwB.atlsT}.
Definition post_process_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (HA DA : Z) (ws wu : word) (linktype : Z) (swapped : bool) (hdr : pkthdr) (d : list Z) (lo : Z) (m : mem)
    : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch [(bv_unsigned sp - PP_FRAME, bv_unsigned sp); (HA + 20, HA + 24); (DA, DA + h_caplen hdr)] m m'
    /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo (bv_unsigned sp)
    /\ rw_cells asegs m' HA (pkthdr_cells ws wu (fst (pcapint_post_process linktype swapped hdr d)))
    /\ zarr m' DA (snd (pcapint_post_process linktype swapped hdr d)).

Definition post_process_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem) (RNG : footprint)
         (HA DA : Z) (ws wu : word) (linktype : Z) (swapped : bool) (hdr : pkthdr) (d : list Z) (lo : Z),
    stk asegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - PP_FRAME -> ATOP + 4096 <= lo ->
    rw_cells asegs m HA (pkthdr_cells ws wu hdr) ->
    zarr m DA d ->
    mem_inv asegs m -> artcells m ->
    a0 = Z_to_bv 64 linktype -> a1 = Z_to_bv 64 (Z.b2z swapped) -> a2 = Z_to_bv 64 HA -> a3 = Z_to_bv 64 DA ->
    0 <= linktype < 2^31 ->
    0 <= h_caplen hdr <= Z.of_nat (length d) -> Z.of_nat (length d) < 2^31 -> 0 <= h_len hdr < 2^32 ->
    (* [comment removed for export] *)
    aobjA RNG m HA 24 -> aobjA RNG m DA (Z.of_nat (length d)) ->
    HA + 24 <= ATOP -> DA + Z.of_nat (length d) <= ATOP ->
    (HA + 24 <= DA \/ DA + Z.of_nat (length d) <= HA) ->
    HA mod 8 = 0 -> DA mod 4 = 0 ->     (* [comment removed for export] *)
    rng RNG lo (bv_unsigned sp - lo) -> rng_aimg RNG -> rng_aimg_sh RNG ->
    evtF asegs RNG (post_process_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc HA DA ws wu linktype swapped hdr d lo m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 PP_ENTRY) fc None m (seg_rom asegs)).
End CANSEC1.
End TwB.
