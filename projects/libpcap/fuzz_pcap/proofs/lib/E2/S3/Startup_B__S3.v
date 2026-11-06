(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Lia.
(* [comment removed for export] *)
From Stdlib Require ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType StackLayout State Specs Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Tac Arr Bytes ITree Nodes Decode SysStep RegsEquiv ImgSrc3.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Monad.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Adapter__Spec.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require FileCells__Musl.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require AmoStep__Musl.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require InitMem.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require Printf_kit__Musl.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_memchr__S3.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_memcpy.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_memmove__S3.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require LiaPin.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require SecDiet.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require ImgTgtUbsan.
From OSSVerify.libpcap.fuzz_pcap.images Require Plain.
From OSSVerify.libpcap.fuzz_pcap.images Require Ubsan.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require ZBridge MonadX.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Prelim Fmt StdioCore Stdio PcapPrelim PcapTypes PcapPure Pcap.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Prog.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require Exit__S3.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_atexit GI.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require GIFacts__S3.
From Stdlib Require String.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Image.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require FmtFacts__S3.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require PcapRep.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require Pcap_iface__S3.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_lock__S3.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_sfpcapng_blkA__S3.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_ngnextA.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Ceiling.
From LinuxProcessSemantics.EquivalenceDefinition Require Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Fs.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require PropExec MState Mem Cells Exec Step Frame.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Kernel Require Fork.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require StartupFacts.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib Require TopLevel.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Top Require EntryCeil.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Module Startup_B.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import Tac Arr Bytes ITree Nodes Decode SysStep RegsEquiv ImgSrc3.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Monad. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Adapter__Spec. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Monad OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Adapter__Spec.StartupModel.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require FileCells__Musl. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require AmoStep__Musl. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require InitMem. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require Printf_kit__Musl. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.FileCells__Musl.StrFun OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.STRW_tac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.InitMem OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_kit__Musl.StartupKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.EntryRnd.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_memchr__S3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_memcpy. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_memmove__S3. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_memchr__S3.F_memset OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_memcpy OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_memmove__S3.Startup_A.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import LiaPin.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require SecDiet.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac lia ::= pinned_lia.
Import ListNotations.
Open Scope bv_scope.
Import ITree.Exc.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section WithCeil.
Context {CEILV : CEIL}.
Definition memsetZ_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (A n c : Z) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1' a2' a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 A) a1' a2' a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom ssegs)
    /\ munch [(A, A + n)]%Z m m' /\ wmono ssegs m m' /\ mem_inv ssegs m'
    /\ rw_cells ssegs m' A [CB (Z.to_nat n) (repeat (Z_to_bv 8 c) (Z.to_nat n))].

Definition memset_specZ__stmt : Prop := forall (A n c : Z) ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (junk : list byte),
  rw_cells ssegs m A [CB (Z.to_nat n) junk] ->
  mem_inv ssegs m ->
  a0 = Z_to_bv 64 A -> a1 = Z_to_bv 64 c -> a2 = Z_to_bv 64 n ->
  (0 <= c < 256)%Z -> (0 <= n < 2^64)%Z -> (A < 2^64)%Z ->
  evt ssegs (memsetZ_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc A n c m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x20d60) fc None m (seg_rom ssegs)).
Section Sz1.
Variables A n c ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m junk : ltac2:(SecDiet.SzSec.tyM 'memset_specZ__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @A).
Lemma memset_specZ__body : ltac2:(SecDiet.SzSec.bodyP 'memset_specZ__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
Proof using CEILV. pin_using (fun (CEILV : unit) => tt). ceil_facts.
  intros DST MI -> -> -> Hc Hn Hl.
  pose proof (rw_cells_bound _ _ _ _ DST) as B. cbn [cells_size csize Nat.add] in B.
  assert (EA : bv_unsigned (Z_to_bv 64 A) = A) by (apply unsigned_lit; lia).
  assert (En : bv_unsigned (Z_to_bv 64 n) = n) by (apply unsigned_lit; lia).
  assert (Ec : (bv_unsigned (Z_to_bv 64 c) mod 256 = c)%Z) by (rewrite unsigned_lit by lia; apply Z.mod_small; lia).
  eapply evt_mono. { eapply memset_spec; [|exact MI]. rewrite EA, En. exact DST. }
  intros ms' PO. unfold memset_post in PO. rewrite EA, En, Ec in PO. exact PO.
Qed.
End Sz1.
Lemma memset_specZ : ltac:(let t := eval cbv delta [memset_specZ__stmt] in memset_specZ__stmt in exact t).
Proof using CEILV. intros A n c ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m junk. ltac2:(SecDiet.SzSec.closeP 'memset_specZ__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.

Definition memcpyZ_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (A S n : Z) (src : list byte) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1' a2' a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 A) a1' a2' a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom ssegs)
    /\ munch [(A, A + n)]%Z m m' /\ wmono ssegs m m' /\ mem_inv ssegs m'
    /\ rw_cells ssegs m' A [CB (Z.to_nat n) src]
    /\ bytes_at ssegs m' S src.

Definition memcpy_specZ__stmt : Prop := forall (A S n : Z) ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (src junk : list byte),
  bytes_at ssegs m S src ->
  length src = Z.to_nat n ->
  rw_cells ssegs m A [CB (Z.to_nat n) junk] ->
  (S + n <= A \/ A + n <= S)%Z ->
  mem_inv ssegs m ->
  a0 = Z_to_bv 64 A -> a1 = Z_to_bv 64 S -> a2 = Z_to_bv 64 n ->
  (0 <= n < 2^64)%Z -> (A < 2^64)%Z -> (S < 2^64)%Z ->
  evt ssegs (memcpyZ_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc A S n src m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x207e0) fc None m (seg_rom ssegs)).
Section Sz2.
Variables A S n ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m src junk : ltac2:(SecDiet.SzSec.tyM 'memcpy_specZ__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @A).
Lemma memcpy_specZ__body : ltac2:(SecDiet.SzSec.bodyP 'memcpy_specZ__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
Proof using CEILV. pin_using (fun (CEILV : unit) => tt). ceil_facts.
  intros SRC LEN DST SEP MI -> -> -> Hn HA HS.
  pose proof (rw_cells_bound _ _ _ _ DST) as B. cbn [cells_size csize Nat.add] in B.
  pose proof (bytes_at_bound _ _ _ _ SRC) as B2.
  assert (EA : bv_unsigned (Z_to_bv 64 A) = A) by (apply unsigned_lit; lia).
  assert (ES : bv_unsigned (Z_to_bv 64 S) = S) by (apply unsigned_lit; lia).
  assert (En : bv_unsigned (Z_to_bv 64 n) = n) by (apply unsigned_lit; lia).
  eapply evt_mono. { eapply memcpy_spec; [| | | | exact MI]; rewrite ?EA, ?ES, ?En; [exact SRC | exact LEN | exact DST | lia]. }
  intros ms' PO. unfold memcpy_post in PO. rewrite EA, ES, En in PO. exact PO.
Qed.
End Sz2.
Lemma memcpy_specZ : ltac:(let t := eval cbv delta [memcpy_specZ__stmt] in memcpy_specZ__stmt in exact t).
Proof using CEILV. intros A S n ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m src junk. ltac2:(SecDiet.SzSec.closeP 'memcpy_specZ__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
End WithCeil.

Notation GOT_SSP := 0x22620%Z (only parsing).
Notation GUARD := 0x53d08%Z (only parsing).

Section WithCeil.
Context {CEILV : CEIL}.
Definition init_ssp_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (lo R tb : Z) (rnd : EntryDraw) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x10 : word) (tls : list byte) (x12 x13 : word) (m : word -> option byte)
    : machine_state -> Prop :=   (* [comment removed for export] *)
  fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
                 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom ssegs)
    /\ munch [(bv_unsigned sp - 16, bv_unsigned sp); (GUARD, 0x53d10); (tb + 184, tb + 192)]%Z m m'
    /\ wmono ssegs m m' /\ mem_inv ssegs m'
    /\ stk ssegs m' lo (bv_unsigned sp)
    /\ rw_cells ssegs m' GUARD [C8 (ssp_canary rnd)]
    /\ rw_cells ssegs m' GOT_SSP [C8 (Z_to_bv 64 GUARD)]
    /\ rw_cells ssegs m' tb (tls_cells x0 x1 x2 x3 x4 x5 x6 x7 x8 (ssp_canary rnd) x10 tls x12 x13)
    /\ bytes_at ssegs m' R (at_random_lo rnd).

Definition init_ssp_spec__stmt : Prop := forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (lo R tb : Z) (rnd : EntryDraw) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 : word) (tls : list byte) (x12 x13 : word)
    (junk : list byte),
  stk ssegs m lo (bv_unsigned sp) ->
  bytes_at ssegs m R (at_random_lo rnd) ->      (* [comment removed for export] *)
  rw_cells ssegs m GUARD [CB 8 junk] ->
  rw_cells ssegs m GOT_SSP [C8 (Z_to_bv 64 GUARD)] ->
  rw_cells ssegs m tb (tls_cells x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 tls x12 x13) ->
  mem_inv ssegs m ->
  tp = Z_to_bv 64 (tb + 200) -> a0 = Z_to_bv 64 R ->
  (lo <= bv_unsigned sp - 16)%Z -> (alloc_ceiling <= lo)%Z -> (bv_unsigned sp <= R)%Z -> tls_block_ok tb ->
  evt ssegs (init_ssp_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo R tb rnd x0 x1 x2 x3 x4 x5 x6 x7 x8 x10 tls x12 x13 m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x184d0) fc None m (seg_rom ssegs)).
Section Sz3.
Variables ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo R tb rnd x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 tls x12 x13 junk : ltac2:(SecDiet.SzSec.tyM 'init_ssp_spec__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra).
Lemma init_ssp_spec__body : ltac2:(SecDiet.SzSec.bodyP 'init_ssp_spec__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
Proof using Type. pin_using tt. ceil_facts.
  intros ST RND GU GG TLS MI -> -> LO LOLO SPR TB.
  unfold tls_cells in TLS. destruct TB as (TBA & TB0 & TBC & TBI).
  pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp); (GUARD, 0x53d10); (tb + 184, tb + 192)]%Z m) as MU.
  pose proof (wmono_refl ssegs m) as WM.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  pose proof (bytes_at_bound _ _ _ _ RND) as RB. rewrite length_at_random_lo in RB.
  carve_frame 16%nat ST.
  lstep. lstep. lstep. if_cases K; zify_cond K; [exfalso; lia|]. clear K.
  do 4 lstep.
  lstep. call (memcpy_specZ GUARD R 8); [exact RND | apply length_at_random_lo | exact GU | lia | exact MI | reflexivity | reflexivity | reflexivity | lia | lia | lia |].
  rename PC into GU. clear RND. rename POST into RND. change (Z.to_nat 8) with 8%nat in GU. try rename MI0 into MI.
  lstep. lstep. lstep. lstep.
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  apply (rw_cells_recast ssegs _ _ _ [C8 (ssp_canary rnd)]) in GU;
    [| cbn; repeat split; exact I
     | cbn [cells_bytes cbytes app]; rewrite app_nil_r, le8_ssp_canary; reflexivity
     | reflexivity].
  lstep. lstep. lstep.
  do 2 lstep. release_frame FR ST (bv_unsigned sp). lstep.
  unfold init_ssp_post, tls_cells. sys_finish.
Qed.
End Sz3.
Lemma init_ssp_spec : ltac:(let t := eval cbv delta [init_ssp_spec__stmt] in init_ssp_spec__stmt in exact t).
Proof using Type. intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo R tb rnd x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 tls x12 x13 junk. ltac2:(SecDiet.SzSec.closeP 'init_ssp_spec__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition auxv20 (uid hw rnd : word) : list word :=
  [Z_to_bv 64 3; Z_to_bv 64 0x10040; Z_to_bv 64 4; Z_to_bv 64 56; Z_to_bv 64 5; Z_to_bv 64 11;
   Z_to_bv 64 16; hw; Z_to_bv 64 6; Z_to_bv 64 4096; Z_to_bv 64 11; uid; Z_to_bv 64 12; uid; Z_to_bv 64 23; z64;
   Z_to_bv 64 25; rnd; z64; z64].
End WithCeil.


Notation ENVIRON := 0x339c8%Z (only parsing).   (* [comment removed for export] *)
Notation PROGNAME := 0x53d18%Z (only parsing).  (* [comment removed for export] *)
Notation HWCAP := 0x53d90%Z (only parsing).     (* [comment removed for export] *)
Notation GOT3 := 0x225f8%Z (only parsing).      (* [comment removed for export] *)

(* [comment removed for export] *)
Section WithCeil.
Context {CEILV : CEIL}.
Lemma envp_count_loop : forall (ws : list word) (Q : machine_state -> Prop)
    ra sp gp tp t0 t1 t2 s0 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (A : Z) (rest : list byte),
  Forall (fun w : word => bv_unsigned w <> 0%Z) ws ->
  bytes_at ssegs m A (u64s ws ++ le8 z64 ++ rest) ->
  evt ssegs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 (Z_to_bv 64 (A + 8 * (Z.of_nat (length ws) + 1))) z64 a1 a2 a3 a4 a5
                    a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (Z_to_bv 64 0x17c30) fc None m (seg_rom ssegs)) ->
  evt ssegs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 (Z_to_bv 64 A) a0 a1 a2 a3 a4 a5
                    a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (Z_to_bv 64 0x17c24) fc None m (seg_rom ssegs)).
Proof using CEILV. pin_using (fun (CEILV : unit) => tt). ceil_facts.
  induction ws as [|w ws IH]; intros until rest; intros NZ B HQ.
  - cbn [u64s app] in B.
    pose proof (bytes_at_bound _ _ _ _ B) as BB. rewrite app_length, length_le8 in BB.
    pose proof (rd_u64 ssegs m A z64 rest (Z_to_bv 64 A) B eq_refl) as RD.
    zstep. clear RD. zstep. zstep.
    cbn [length Z.of_nat] in HQ. exact_evt HQ.
  - cbn [u64s app] in B. rewrite <- app_assoc in B.
    pose proof (bytes_at_bound _ _ _ _ B) as BB. rewrite !app_length, !length_le8 in BB.
    apply Forall_cons_iff in NZ. destruct NZ as [NZw NZ].
    pose proof (rd_u64 ssegs m A w _ (Z_to_bv 64 A) B eq_refl) as RD.
    zstep. clear RD. zstep. zstep. if_true.
    apply bytes_at_app in B. destruct B as [_ B]. rewrite length_le8 in B.
    eapply (IH Q); [exact NZ | exact B |].
    cbn [length] in HQ. exact_evt HQ.
Qed.

Section InitLibc.
  Context {St : Type} (set_tls : Z -> St -> St).
  Variables (ra sp gp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo : Z)
            (E : Z) (eps : list word) (uid hw : word) (rnd : EntryDraw) (R : Z) (P : Z) (str : list byte)
            (pn0 pnf0 hw0 env0 : word) (gjunk : list byte) (s : St).
  Notation W := [(bv_unsigned sp - 448, bv_unsigned sp); (ENVIRON, 0x339d0); (0x53aa8, 0x53ad8);
                 (GUARD, 0x53d10); (PROGNAME, 0x53d28); (LIBC, 0x53d60); (HWCAP, 0x53d98)]%Z.
  Notation AUXV := (E + 8 * (Z.of_nat (length eps) + 1))%Z.

  Definition init_libc_post : unit -> St -> machine_state -> Prop :=
    fun _ s' ms' => exists (tb t : Z) t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' pg m',
      (tls_block_ok tb /\ (0 < t < 4194304)%Z /\ s' = set_tls tb s)
      /\ ms' = MS (mkR ra sp gp (Z_to_bv 64 (tb + 200)) t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7'
                   s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
               F (ret_pc ra) fc None m' (seg_rom ssegs)
      /\ munch ((tb, tb + 4096)%Z :: W) m m' /\ wmono ssegs m m' /\ mem_inv ssegs m'
      /\ stk ssegs m' lo (bv_unsigned sp)
      /\ rw_cells ssegs m' tb (tls_cells (Z_to_bv 64 tb) (Z_to_bv 64 tb) (Z_to_bv 64 tb) z64 (Z_to_bv 64 t) z64 (Z_to_bv 64 2)
                                      (Z_to_bv 64 (tb + 120)) (Z_to_bv 64 0x53d60) (ssp_canary rnd) (Z_to_bv 64 (tb + 464))
                                      (repeat (Z_to_bv 8 0) 256) (Z_to_bv 64 1) (Z_to_bv 64 (tb + 2248)))
      /\ rw_cells ssegs m' LIBC (libc_cells (Z_to_bv 8 1) (Z_to_bv 8 0) (Z_to_bv 8 0) (Z_to_bv 8 0) z64 (Z_to_bv 64 AUXV)
                                   (Z_to_bv 64 0x53aa8) (Z_to_bv 64 480) (Z_to_bv 64 8) (Z_to_bv 64 1) (Z_to_bv 64 4096)
                                   (repeat (Z_to_bv 8 0) 48))
      /\ rw_cells ssegs m' TLL (tll_cells z64 z64 (Z_to_bv 64 TLS_IMAGE) z64 (Z_to_bv 64 0x100) (Z_to_bv 64 8) z64)
      /\ rw_cells ssegs m' SYSINFO [C8 z64]
      /\ rw_cells ssegs m' PROGNAME [C8 pg; C8 (Z_to_bv 64 P)]
      /\ rw_cells ssegs m' HWCAP [C8 hw]   (* [comment removed for export] *)
      /\ rw_cells ssegs m' ENVIRON [C8 (Z_to_bv 64 E)]
      /\ rw_cells ssegs m' DEFSTACK [C4 (Z_to_bv 64 0x20000)]
      /\ rw_cells ssegs m' GUARD [C8 (ssp_canary rnd)]
      /\ rw_cells ssegs m' GOT3 [C8 (Z_to_bv 64 ENVIRON); C8 (Z_to_bv 64 0x53d20); C8 (Z_to_bv 64 PROGNAME)]
      /\ rw_cells ssegs m' GOT_SSP [C8 (Z_to_bv 64 GUARD)]
      /\ rw_cells ssegs m' GOT_DYNAMIC [C8 z64]
      /\ bytes_at ssegs m' E (u64s eps ++ le8 z64 ++ u64s (auxv20 uid hw (Z_to_bv 64 R)))
      /\ bytes_at ssegs m' P (str ++ [Z_to_bv 8 0])
      /\ bytes_at ssegs m' R (at_random_lo rnd).

  Hypothesis EPS : Forall (fun w : word => bv_unsigned w <> 0%Z) eps.
  Hypothesis NONUL : Forall (fun b : byte => bv_unsigned b <> 0%Z) str.
  Hypothesis LO : (lo <= bv_unsigned sp - 448)%Z.
  Hypothesis LOLO : (alloc_ceiling <= lo)%Z.
  Hypothesis SPE : (bv_unsigned sp <= E)%Z.
  Hypothesis SPP : (bv_unsigned sp <= P)%Z.
  Hypothesis SPR : (bv_unsigned sp <= R)%Z.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition pn_post (x5 x6 x7 x9 x11 x14 x15 x16 x17 x28 x29 x30 x31 : word) (m0 : word -> option byte) : machine_state -> Prop :=
    fun ms' => exists pg m',
    ms' = MS (mkR (Z_to_bv 64 0x17c18) (Z_to_bv 64 (bv_unsigned sp + -384)) gp x11 (* [comment removed for export] *) x5 x6 x7
                  (Z_to_bv 64 P) x9 (Z_to_bv 64 PROGNAME) (Z_to_bv 64 (P + Z.of_nat (length str) + 1)) (Z_to_bv 64 47) z64 x14 x15 x16 x17
                  (Z_to_bv 64 LIBC) s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
             F (Z_to_bv 64 0x17cf4) fc None m' (seg_rom ssegs)
    /\ munch [(PROGNAME, 0x53d20)]%Z m0 m' /\ wmono ssegs m0 m' /\ mem_inv ssegs m'
    /\ rw_cells ssegs m' PROGNAME [C8 pg; C8 (Z_to_bv 64 P)].

  Lemma pn_loop : forall (k : nat) (j : Z) (m0 mm : word -> option byte) x5 x6 x7 x9 x11 x13 x14 x15 x16 x17 x28 x29 x30 x31 pg,
    (Z.of_nat k = Z.of_nat (length str) + 1 - j)%Z -> (1 <= j)%Z ->
    munch [(PROGNAME, 0x53d20)]%Z m0 mm -> wmono ssegs m0 mm -> mem_inv ssegs mm ->
    bytes_at ssegs mm P (str ++ [Z_to_bv 8 0]) ->
    rw_cells ssegs mm PROGNAME [C8 pg; C8 (Z_to_bv 64 P)] ->
    evt ssegs (pn_post x5 x6 x7 x9 x11 x14 x15 x16 x17 x28 x29 x30 x31 m0)
      (MS (mkR (Z_to_bv 64 0x17c18) (Z_to_bv 64 (bv_unsigned sp + -384)) gp x11 x5 x6 x7
               (Z_to_bv 64 P) x9 (Z_to_bv 64 PROGNAME) (Z_to_bv 64 (P + j)) (Z_to_bv 64 47) x13 x14 x15 x16 x17
               (Z_to_bv 64 LIBC) s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
          F (Z_to_bv 64 0x17ce8) fc None mm (seg_rom ssegs)).
  Proof using LO LOLO NONUL SPP. pin_using (fun (LO LOLO NONUL SPP : unit) => tt). ceil_facts.
    induction k as [|k IH]; intros j m0 mm x5 x6 x7 x9 x11 x13 x14 x15 x16 x17 x28 x29 x30 x31 pg Hk Hj MU WM MI STR G2.
    - pose proof (bytes_at_bound _ _ _ _ STR) as BB. rewrite app_length in BB. cbn [length] in BB.
      assert (Hn : nth_error (str ++ [Z_to_bv 8 0]) (Z.to_nat (j - 1)) = Some (Z_to_bv 8 0)).
      { rewrite nth_error_app2 by lia. replace (Z.to_nat (j - 1) - length str)%nat with 0%nat by lia. reflexivity. }
      pose proof (u8ro_read ssegs mm P _ (j - 1) _ (Z_to_bv 64 (P + j + -1)) STR Hn ltac:(lia) ltac:(unfold wa; f_equal; lia)) as RD.
      zstep. clear RD. zstep. if_false. zstep. if_false.
      replace (Z_to_bv 64 (P + j)) with (Z_to_bv 64 (P + Z.of_nat (length str) + 1)) by (f_equal; lia).
      unfold pn_post. finish2. all: eassumption.
    - pose proof (bytes_at_bound _ _ _ _ STR) as BB. rewrite app_length in BB. cbn [length] in BB.
      destruct (nth_error str (Z.to_nat (j - 1))) as [b|] eqn:Hb; [| apply nth_error_None in Hb; lia].
      assert (Hn : nth_error (str ++ [Z_to_bv 8 0]) (Z.to_nat (j - 1)) = Some b) by (rewrite nth_error_app1 by lia; exact Hb).
      pose proof (proj1 (Forall_forall _ _) NONUL b (nth_error_In _ _ Hb)) as NZb. cbn in NZb.
      pose proof (bv_unsigned_in_range 8 b) as Rb. unfold bv_modulus in Rb. cbn in Rb.
      pose proof (u8ro_read ssegs mm P _ (j - 1) _ (Z_to_bv 64 (P + j + -1)) STR Hn ltac:(lia) ltac:(unfold wa; f_equal; lia)) as RD.
      zstep. clear RD. zstep. if_cases K.
      + (* [comment removed for export] *) lstep. zstep.
        replace (P + j + 1)%Z with (P + (j + 1))%Z by lia.
        eapply (IH (j + 1)%Z); try eassumption; lia.
      + zstep. if_cases K0; zify_cond K0; [| exfalso; lia]. zstep.
        replace (P + j + 1)%Z with (P + (j + 1))%Z by lia.
        eapply (IH (j + 1)%Z); try eassumption; lia.
  Qed.

  (* [comment removed for export] *)
  Ltac scan_it AUXB vi ki :=
    lstep; if_false; ldaux AUXB vi; lstep; lstep;
    (try lazymatch goal with |- context [Z_to_bv 64 (bv_unsigned ?spv + -336 + ?c)] =>
      let off := eval vm_compute in (-336 + c)%Z in
      replace (Z_to_bv 64 (bv_unsigned spv + -336 + c)) with (Z_to_bv 64 (bv_unsigned spv + off)) by (f_equal; lia)
    end);
    (try lazymatch goal with |- context [Z_to_bv 64 (?c + (bv_unsigned ?spv + -336))] =>
      let off := eval vm_compute in (c + -336)%Z in
      replace (Z_to_bv 64 (c + (bv_unsigned spv + -336))) with (Z_to_bv 64 (bv_unsigned spv + off)) by (f_equal; lia)
    end);
    lstep; lstep; ldaux AUXB ki; lstep; astep.

  Definition init_libc_spec__stmt : Prop := forall tp a0 a1,
    stk ssegs m lo (bv_unsigned sp) ->
    bytes_at ssegs m E (u64s eps ++ le8 z64 ++ u64s (auxv20 uid hw (Z_to_bv 64 R))) ->
    bytes_at ssegs m P (str ++ [Z_to_bv 8 0]) ->
    bytes_at ssegs m R (at_random_lo rnd) ->
    rw_cells ssegs m PROGNAME [C8 pn0; C8 pnf0] ->
    rw_cells ssegs m HWCAP [C8 hw0] ->
    rw_cells ssegs m ENVIRON [C8 env0] ->
    rw_cells ssegs m SYSINFO [C8 z64] ->
    rw_cells ssegs m LIBC (libc_cells (Z_to_bv 8 0) (Z_to_bv 8 0) (Z_to_bv 8 0) (Z_to_bv 8 0) z64 z64 z64 z64 z64 z64 z64 (repeat (Z_to_bv 8 0) 48)) ->
    rw_cells ssegs m TLL (tll_cells z64 z64 z64 z64 z64 z64 z64) ->
    rw_cells ssegs m DEFSTACK [C4 (Z_to_bv 64 0x20000)] ->
    rw_cells ssegs m GUARD [CB 8 gjunk] ->
    rw_cells ssegs m GOT3 [C8 (Z_to_bv 64 ENVIRON); C8 (Z_to_bv 64 0x53d20); C8 (Z_to_bv 64 PROGNAME)] ->
    rw_cells ssegs m GOT_SSP [C8 (Z_to_bv 64 GUARD)] ->
    rw_cells ssegs m GOT_DYNAMIC [C8 z64] ->
    rw_cells ssegs m 0x339d0 [CB 4096 (repeat (Z_to_bv 8 0) 4096)] ->
    mem_inv ssegs m ->
    a0 = Z_to_bv 64 E -> a1 = Z_to_bv 64 P ->
    implM ssegs (startup_model set_tls 0x339d0) s init_libc_post
         (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (Z_to_bv 64 0x17bec) fc None m (seg_rom ssegs)).
  Section Sz6.
  Variables tp a0 a1 : ltac2:(SecDiet.SzSec.tyM 'init_libc_spec__stmt "vvv" @tp).
  Lemma init_libc_spec__body : ltac2:(SecDiet.SzSec.bodyP 'init_libc_spec__stmt "vvv").
  Proof using EPS LO LOLO NONUL SPE SPP SPR. pin_using (fun (EPS LO LOLO NONUL SPE SPP SPR : unit) => tt). ceil_facts.
    intros ST ENV STR RND G2 HW ENVC SI LC MT DS GU GOT3 GG GD ZT MI -> ->.
    unfold libc_cells, tll_cells in *.
    pose proof (munch_refl W m) as MU. pose proof (wmono_refl ssegs m) as WM.
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
    pose proof (bytes_at_bound _ _ _ _ ENV) as EB. rewrite !app_length, !u64s_length, length_le8 in EB. cbn [length auxv20] in EB.
    pose proof (bytes_at_bound _ _ _ _ STR) as PB. rewrite app_length in PB. cbn [length] in PB.
    pose proof (bytes_at_bound _ _ _ _ RND) as RB. rewrite length_at_random_lo in RB.
    unfold implM. iprefix.
    carve_frame 384%nat ST.
    do 10 lstep.
    (* [comment removed for export] *)
    apply (rw_cells_split_CB ssegs _ _ [] 352 _ _ [48; 304]%nat) in FR; [|reflexivity]. cbn [mk_CB_cells app] in FR.
    apply (proj1 (rw_cells_app _ _ _ [_] _)) in FR. destruct FR as [FRlo FR]. cbn [cells_size csize Nat.add] in FR.
    apply (proj1 (rw_cells_app _ _ _ [_] _)) in FR. destruct FR as [AUX FRhi]. cbn [cells_size csize Nat.add] in FRhi.
    change (Z.of_nat 48) with 48%Z in *. change (Z.of_nat 304) with 304%Z in *.
    replace (bv_unsigned sp + -384 + 48)%Z with (bv_unsigned sp + -336)%Z in AUX by lia.
    replace (bv_unsigned sp + -384 + 48 + 304)%Z with (bv_unsigned sp + -32)%Z in FRhi by lia.
    lstep. call (memset_specZ (bv_unsigned sp + -336) 304 0); [exact AUX | exact MI | reflexivity | reflexivity | reflexivity | lia | lia | lia |].
    rename POST into AUX. change (Z.to_nat 304) with 304%nat in AUX. try rename MI0 into MI.
    apply (rw_cells_recast ssegs _ _ _ (repeat (C8 z64) 38)) in AUX;
      [| cbn; repeat split; exact I | vm_compute; reflexivity | reflexivity]. cbn [repeat] in AUX.
    (* [comment removed for export] *)
    lstep. lstep. lstep.
    eapply (envp_count_loop eps); [exact EPS | exact ENV |].
    (* [comment removed for export] *)
    lstep. lstep. lstep.
    pose proof ENV as AUXB. apply bytes_at_app in AUXB. destruct AUXB as [_ AUXB].
    apply bytes_at_app in AUXB. destruct AUXB as [_ AUXB]. rewrite u64s_length, length_le8 in AUXB.
    replace (E + Z.of_nat (8 * length eps) + Z.of_nat 8)%Z with AUXV in AUXB by lia.
    ldaux AUXB 0%nat. lstep. if_false. lstep. lstep. lstep. lstep.
    (* [comment removed for export] *)
    scan_it AUXB 1%nat 2%nat. scan_it AUXB 3%nat 4%nat. scan_it AUXB 5%nat 6%nat. scan_it AUXB 7%nat 8%nat.
    scan_it AUXB 9%nat 10%nat. scan_it AUXB 11%nat 12%nat. scan_it AUXB 13%nat 14%nat. scan_it AUXB 15%nat 16%nat.
    scan_it AUXB 17%nat 18%nat.
    (* [comment removed for export] *)
    steps_to 0x17ca8%Z.
    astep. if_cases K; zify_cond K; [|exfalso; lia]. clear K.
    astep. if_cases K; zify_cond K; [|exfalso; lia]. clear K.
    (* [comment removed for export] *)
    steps_to 0x17ce8%Z.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      call (pn_loop (length str) 1 mm mm); [lia | lia | apply munch_refl | apply wmono_refl | exact MI | exact STR | exact G2 | ] end.
    rename POST into G2. try rename MI0 into MI.
    (* [comment removed for export] *)
    apply (proj1 (rw_cells_app _ _ _ [_;_;_] _)) in AUX. destruct AUX as [AUXa AUX].
    apply (proj1 (rw_cells_app _ _ _ [_;_;_] _)) in AUX. destruct AUX as [AUX3 AUXb].
    cbn [cells_size csize Nat.add] in AUX3, AUXb. change (Z.of_nat 24) with 24%Z in *.
    replace (bv_unsigned sp + -336 + 24 + 24)%Z with (bv_unsigned sp + -288)%Z in AUXb by lia.
    lstep. lstep.
    name_sp sp (-384)%Z.
    icallM (init_tls_spec set_tls _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
               lo (bv_unsigned sp + -336)%Z _ _ _ _ _ _ _ _ _ _ s).
    all: lazymatch goal with
         | |- forall _, _ => ipostT ssegs; unname_sp
         | |- _ => unname_sp; fastfirst (first [ noevar_assumption | hyp_by_addr | reflexivity | lia ])
         end.
    (* [comment removed for export] *)
    repeat match goal with
           | H1 : rw_cells _ ?mm ?A ?cs, H2 : rw_cells _ ?mm ?A ?cs |- _ => clear H2
           end.
    unfold tls_cells, libc_cells, tll_cells in *.
    match goal with H : stk _ _ _ _ |- _ => rename H into ST end.
    (* [comment removed for export] *)
    lstep. lstep.
    lazymatch goal with TB : tls_block_ok ?tb |- _ =>
      call_sp (init_ssp_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ lo R tb rnd) end.
    all: lazymatch goal with
         | |- evt _ _ _ => idtac
         | |- tls_block_ok _ => assumption
         | |- ?g => fastfirst (first [ noevar_assumption | hyp_by_addr | reflexivity | lia ])
         end.
    match goal with H : stk _ _ _ _ |- _ => rename H into ST end.
    (* [comment removed for export] *)
    do 3 lstep. if_false. lstep. lstep. lstep. if_false. lstep. lstep. if_true.
    do 5 lstep.
    join2 FRlo AUXa. join2 FRlo AUX3. join2 FRlo AUXb. join2 FRlo FRhi.
    release_frame FRlo ST (bv_unsigned sp).
    lstep.
    apply evt_done. unfold init_libc_post.
    lazymatch goal with TB : tls_block_ok ?tb, Ht : (0 < ?t < 4194304)%Z |- _ => exists tb, t end.
    repeat (lazymatch goal with |- ex _ => eexists end).
    split. { split; [assumption|]. split; [assumption|]. assumption. }
    split. { cbv delta [mkR]. reflexivity. }
    repeat match goal with |- _ /\ _ => split end; fastfirst (first [hyp_by_addr | assumption | lia]).
  Qed.
  End Sz6.
  Lemma init_libc_spec : ltac:(let t := eval cbv delta [init_libc_spec__stmt] in init_libc_spec__stmt in exact t).
  Proof using EPS LO LOLO NONUL SPE SPP SPR. intros tp a0 a1. ltac2:(SecDiet.SzSec.closeP 'init_libc_spec__body "vvv"). Qed.
End InitLibc.

End WithCeil.

(* [comment removed for export] *)
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require ImgTgtUbsan.
Module TwB.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Tac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Arr OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Bytes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ITree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Nodes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Decode OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.SysStep OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.RegsEquiv OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ImgTgtUbsan.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Monad OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Adapter__Spec.StartupModel.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.FileCells__Musl.StrFun OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.STRW_tac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.InitMem OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_kit__Musl.StartupKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.EntryRnd.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_memchr__S3.F_memset.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_memcpy.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_memmove__S3.Startup_A.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.LiaPin.
(* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac lia ::= pinned_lia.
Import ListNotations.
Open Scope bv_scope.
Import ITree.Exc.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section WithCeil.
Context {CEILV : CEIL}.
Definition memsetZ_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (A n c : Z) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1' a2' a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 A) a1' a2' a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom usegs)
    /\ munch [(A, A + n)]%Z m m' /\ wmono usegs m m' /\ mem_inv usegs m'
    /\ rw_cells usegs m' A [CB (Z.to_nat n) (repeat (Z_to_bv 8 c) (Z.to_nat n))].

Definition memset_specZ__stmt : Prop := forall (A n c : Z) ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (junk : list byte),
  rw_cells usegs m A [CB (Z.to_nat n) junk] ->
  mem_inv usegs m ->
  a0 = Z_to_bv 64 A -> a1 = Z_to_bv 64 c -> a2 = Z_to_bv 64 n ->
  (0 <= c < 256)%Z -> (0 <= n < 2^64)%Z -> (A < 2^64)%Z ->
  evt usegs (memsetZ_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc A n c m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x21520) fc None m (seg_rom usegs)).
Section Sz1.
Variables A n c ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m junk : ltac2:(SecDiet.SzSec.tyM 'memset_specZ__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @A).
Lemma memset_specZ__body : ltac2:(SecDiet.SzSec.bodyP 'memset_specZ__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
Proof using CEILV. pin_using (fun (CEILV : unit) => tt). ceil_facts.
 intros DST MI -> -> -> Hc Hn Hl.
  pose proof (rw_cells_bound _ _ _ _ DST) as B. cbn [cells_size csize Nat.add] in B.
  assert (EA : bv_unsigned (Z_to_bv 64 A) = A) by (apply unsigned_lit; lia).
  assert (En : bv_unsigned (Z_to_bv 64 n) = n) by (apply unsigned_lit; lia).
  assert (Ec : (bv_unsigned (Z_to_bv 64 c) mod 256 = c)%Z) by (rewrite unsigned_lit by lia; apply Z.mod_small; lia).
  eapply evt_mono. { eapply memset_spec; [|exact MI]. rewrite EA, En. exact DST. }
  intros ms' PO. unfold memset_post in PO. rewrite EA, En, Ec in PO. exact PO.
Qed.
End Sz1.
Lemma memset_specZ : ltac:(let t := eval cbv delta [memset_specZ__stmt] in memset_specZ__stmt in exact t).
Proof using CEILV. intros A n c ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m junk. ltac2:(SecDiet.SzSec.closeP 'memset_specZ__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.

Definition memcpyZ_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (A S n : Z) (src : list byte) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1' a2' a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 A) a1' a2' a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom usegs)
    /\ munch [(A, A + n)]%Z m m' /\ wmono usegs m m' /\ mem_inv usegs m'
    /\ rw_cells usegs m' A [CB (Z.to_nat n) src]
    /\ bytes_at usegs m' S src.

Definition memcpy_specZ__stmt : Prop := forall (A S n : Z) ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (src junk : list byte),
  bytes_at usegs m S src ->
  length src = Z.to_nat n ->
  rw_cells usegs m A [CB (Z.to_nat n) junk] ->
  (S + n <= A \/ A + n <= S)%Z ->
  mem_inv usegs m ->
  a0 = Z_to_bv 64 A -> a1 = Z_to_bv 64 S -> a2 = Z_to_bv 64 n ->
  (0 <= n < 2^64)%Z -> (A < 2^64)%Z -> (S < 2^64)%Z ->
  evt usegs (memcpyZ_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc A S n src m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x20fa0) fc None m (seg_rom usegs)).
Section Sz2.
Variables A S n ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m src junk : ltac2:(SecDiet.SzSec.tyM 'memcpy_specZ__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @A).
Lemma memcpy_specZ__body : ltac2:(SecDiet.SzSec.bodyP 'memcpy_specZ__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
Proof using CEILV. pin_using (fun (CEILV : unit) => tt). ceil_facts.
 intros SRC LEN DST SEP MI -> -> -> Hn HA HS.
  pose proof (rw_cells_bound _ _ _ _ DST) as B. cbn [cells_size csize Nat.add] in B.
  pose proof (bytes_at_bound _ _ _ _ SRC) as B2.
  assert (EA : bv_unsigned (Z_to_bv 64 A) = A) by (apply unsigned_lit; lia).
  assert (ES : bv_unsigned (Z_to_bv 64 S) = S) by (apply unsigned_lit; lia).
  assert (En : bv_unsigned (Z_to_bv 64 n) = n) by (apply unsigned_lit; lia).
  eapply evt_mono. { eapply memcpy_spec; [| | | | exact MI]; rewrite ?EA, ?ES, ?En; [exact SRC | exact LEN | exact DST | lia]. }
  intros ms' PO. unfold memcpy_post in PO. rewrite EA, ES, En in PO. exact PO.
Qed.
End Sz2.
Lemma memcpy_specZ : ltac:(let t := eval cbv delta [memcpy_specZ__stmt] in memcpy_specZ__stmt in exact t).
Proof using CEILV. intros A S n ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m src junk. ltac2:(SecDiet.SzSec.closeP 'memcpy_specZ__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
End WithCeil.

Notation GOT_SSP := 0x22de0%Z (only parsing).
Notation GUARD := 0x544c8%Z (only parsing).

Section WithCeil.
Context {CEILV : CEIL}.
Definition init_ssp_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (lo R tb : Z) (rnd : EntryDraw) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x10 : word) (tls : list byte) (x12 x13 : word) (m : word -> option byte)
    : machine_state -> Prop :=   (* [comment removed for export] *)
  fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
                 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom usegs)
    /\ munch [(bv_unsigned sp - 16, bv_unsigned sp); (GUARD, 0x544d0); (tb + 184, tb + 192)]%Z m m'
    /\ wmono usegs m m' /\ mem_inv usegs m'
    /\ stk usegs m' lo (bv_unsigned sp)
    /\ rw_cells usegs m' GUARD [C8 (ssp_canary rnd)]
    /\ rw_cells usegs m' GOT_SSP [C8 (Z_to_bv 64 GUARD)]
    /\ rw_cells usegs m' tb (tls_cells x0 x1 x2 x3 x4 x5 x6 x7 x8 (ssp_canary rnd) x10 tls x12 x13)
    /\ bytes_at usegs m' R (at_random_lo rnd).

Definition init_ssp_spec__stmt : Prop := forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (lo R tb : Z) (rnd : EntryDraw) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 : word) (tls : list byte) (x12 x13 : word)
    (junk : list byte),
  stk usegs m lo (bv_unsigned sp) ->
  bytes_at usegs m R (at_random_lo rnd) ->      (* [comment removed for export] *)
  rw_cells usegs m GUARD [CB 8 junk] ->
  rw_cells usegs m GOT_SSP [C8 (Z_to_bv 64 GUARD)] ->
  rw_cells usegs m tb (tls_cells x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 tls x12 x13) ->
  mem_inv usegs m ->
  tp = Z_to_bv 64 (tb + 200) -> a0 = Z_to_bv 64 R ->
  (lo <= bv_unsigned sp - 16)%Z -> (alloc_ceiling <= lo)%Z -> (bv_unsigned sp <= R)%Z -> tls_block_ok_u tb ->
  evt usegs (init_ssp_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo R tb rnd x0 x1 x2 x3 x4 x5 x6 x7 x8 x10 tls x12 x13 m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x18c90) fc None m (seg_rom usegs)).
Section Sz3.
Variables ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo R tb rnd x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 tls x12 x13 junk : ltac2:(SecDiet.SzSec.tyM 'init_ssp_spec__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra).
Lemma init_ssp_spec__body : ltac2:(SecDiet.SzSec.bodyP 'init_ssp_spec__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
Proof using Type. pin_using tt. ceil_facts.
 intros ST RND GU GG TLS MI -> -> LO LOLO SPR TB.
  unfold tls_cells in TLS. destruct TB as (TBA & TB0 & TBC & TBI).
  pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp); (GUARD, 0x544d0); (tb + 184, tb + 192)]%Z m) as MU.
  pose proof (wmono_refl usegs m) as WM.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  pose proof (bytes_at_bound _ _ _ _ RND) as RB. rewrite length_at_random_lo in RB.
  carve_frame 16%nat ST.
  lstep. lstep. lstep. if_cases K; zify_cond K; [exfalso; lia|]. clear K.
  do 4 lstep.
  lstep. call (memcpy_specZ GUARD R 8); [exact RND | apply length_at_random_lo | exact GU | lia | exact MI | reflexivity | reflexivity | reflexivity | lia | lia | lia |].
  rename PC into GU. clear RND. rename POST into RND. change (Z.to_nat 8) with 8%nat in GU. try rename MI0 into MI.
  lstep. lstep. lstep. lstep.
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  apply (rw_cells_recast usegs _ _ _ [C8 (ssp_canary rnd)]) in GU;
    [| cbn; repeat split; exact I
     | cbn [cells_bytes cbytes app]; rewrite app_nil_r, le8_ssp_canary; reflexivity
     | reflexivity].
  lstep. lstep. lstep.
  do 2 lstep. release_frame FR ST (bv_unsigned sp). lstep.
  unfold init_ssp_post, tls_cells. sys_finish.
Qed.
End Sz3.
Lemma init_ssp_spec : ltac:(let t := eval cbv delta [init_ssp_spec__stmt] in init_ssp_spec__stmt in exact t).
Proof using Type. intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo R tb rnd x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 tls x12 x13 junk. ltac2:(SecDiet.SzSec.closeP 'init_ssp_spec__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition auxv20 (uid hw rnd : word) : list word :=
  [Z_to_bv 64 3; Z_to_bv 64 0x10040; Z_to_bv 64 4; Z_to_bv 64 56; Z_to_bv 64 5; Z_to_bv 64 11;
   Z_to_bv 64 16; hw; Z_to_bv 64 6; Z_to_bv 64 4096; Z_to_bv 64 11; uid; Z_to_bv 64 12; uid; Z_to_bv 64 23; z64;
   Z_to_bv 64 25; rnd; z64; z64].
End WithCeil.


Notation ENVIRON := 0x34188%Z (only parsing).   (* [comment removed for export] *)
Notation PROGNAME := 0x544d8%Z (only parsing).  (* [comment removed for export] *)
Notation HWCAP := 0x54550%Z (only parsing).     (* [comment removed for export] *)
Notation GOT3 := 0x22db8%Z (only parsing).      (* [comment removed for export] *)

(* [comment removed for export] *)
Section WithCeil.
Context {CEILV : CEIL}.
Lemma envp_count_loop : forall (ws : list word) (Q : machine_state -> Prop)
    ra sp gp tp t0 t1 t2 s0 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (A : Z) (rest : list byte),
  Forall (fun w : word => bv_unsigned w <> 0%Z) ws ->
  bytes_at usegs m A (u64s ws ++ le8 z64 ++ rest) ->
  evt usegs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 (Z_to_bv 64 (A + 8 * (Z.of_nat (length ws) + 1))) z64 a1 a2 a3 a4 a5
                    a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (Z_to_bv 64 0x183f0) fc None m (seg_rom usegs)) ->
  evt usegs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 (Z_to_bv 64 A) a0 a1 a2 a3 a4 a5
                    a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (Z_to_bv 64 0x183e4) fc None m (seg_rom usegs)).
Proof using CEILV. pin_using (fun (CEILV : unit) => tt). ceil_facts.
  induction ws as [|w ws IH]; intros until rest; intros NZ B HQ.
  - cbn [u64s app] in B.
    pose proof (bytes_at_bound _ _ _ _ B) as BB. rewrite app_length, length_le8 in BB.
    pose proof (rd_u64 usegs m A z64 rest (Z_to_bv 64 A) B eq_refl) as RD.
    zstep. clear RD. zstep. zstep.
    cbn [length Z.of_nat] in HQ. exact_evt HQ.
  - cbn [u64s app] in B. rewrite <- app_assoc in B.
    pose proof (bytes_at_bound _ _ _ _ B) as BB. rewrite !app_length, !length_le8 in BB.
    apply Forall_cons_iff in NZ. destruct NZ as [NZw NZ].
    pose proof (rd_u64 usegs m A w _ (Z_to_bv 64 A) B eq_refl) as RD.
    zstep. clear RD. zstep. zstep. if_true.
    apply bytes_at_app in B. destruct B as [_ B]. rewrite length_le8 in B.
    eapply (IH Q); [exact NZ | exact B |].
    cbn [length] in HQ. exact_evt HQ.
Qed.

Section InitLibc.
  Context {St : Type} (set_tls : Z -> St -> St).
  Variables (ra sp gp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo : Z)
            (E : Z) (eps : list word) (uid hw : word) (rnd : EntryDraw) (R : Z) (P : Z) (str : list byte)
            (pn0 pnf0 hw0 env0 : word) (gjunk : list byte) (s : St).
  Notation W := [(bv_unsigned sp - 448, bv_unsigned sp); (ENVIRON, 0x34190); (0x54268, 0x54298);
                 (GUARD, 0x544d0); (PROGNAME, 0x544e8); (LIBC, 0x54520); (HWCAP, 0x54558)]%Z.
  Notation AUXV := (E + 8 * (Z.of_nat (length eps) + 1))%Z.

  Definition init_libc_post : unit -> St -> machine_state -> Prop :=
    fun _ s' ms' => exists (tb t : Z) t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' pg m',
      (tls_block_ok_u tb /\ (0 < t < 4194304)%Z /\ s' = set_tls tb s)
      /\ ms' = MS (mkR ra sp gp (Z_to_bv 64 (tb + 200)) t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7'
                   s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
               F (ret_pc ra) fc None m' (seg_rom usegs)
      /\ munch ((tb, tb + 4096)%Z :: W) m m' /\ wmono usegs m m' /\ mem_inv usegs m'
      /\ stk usegs m' lo (bv_unsigned sp)
      /\ rw_cells usegs m' tb (tls_cells (Z_to_bv 64 tb) (Z_to_bv 64 tb) (Z_to_bv 64 tb) z64 (Z_to_bv 64 t) z64 (Z_to_bv 64 2)
                                      (Z_to_bv 64 (tb + 120)) (Z_to_bv 64 0x54520) (ssp_canary rnd) (Z_to_bv 64 (tb + 464))
                                      (repeat (Z_to_bv 8 0) 256) (Z_to_bv 64 1) (Z_to_bv 64 (tb + 2248)))
      /\ rw_cells usegs m' LIBC (libc_cells (Z_to_bv 8 1) (Z_to_bv 8 0) (Z_to_bv 8 0) (Z_to_bv 8 0) z64 (Z_to_bv 64 AUXV)
                                   (Z_to_bv 64 0x54268) (Z_to_bv 64 480) (Z_to_bv 64 8) (Z_to_bv 64 1) (Z_to_bv 64 4096)
                                   (repeat (Z_to_bv 8 0) 48))
      /\ rw_cells usegs m' TLL (tll_cells z64 z64 (Z_to_bv 64 TLS_IMAGE) z64 (Z_to_bv 64 0x100) (Z_to_bv 64 8) z64)
      /\ rw_cells usegs m' SYSINFO [C8 z64]
      /\ rw_cells usegs m' PROGNAME [C8 pg; C8 (Z_to_bv 64 P)]
      /\ rw_cells usegs m' HWCAP [C8 hw]   (* [comment removed for export] *)
      /\ rw_cells usegs m' ENVIRON [C8 (Z_to_bv 64 E)]
      /\ rw_cells usegs m' DEFSTACK [C4 (Z_to_bv 64 0x20000)]
      /\ rw_cells usegs m' GUARD [C8 (ssp_canary rnd)]
      /\ rw_cells usegs m' GOT3 [C8 (Z_to_bv 64 ENVIRON); C8 (Z_to_bv 64 0x544e0); C8 (Z_to_bv 64 PROGNAME)]
      /\ rw_cells usegs m' GOT_SSP [C8 (Z_to_bv 64 GUARD)]
      /\ rw_cells usegs m' GOT_DYNAMIC [C8 z64]
      /\ bytes_at usegs m' E (u64s eps ++ le8 z64 ++ u64s (auxv20 uid hw (Z_to_bv 64 R)))
      /\ bytes_at usegs m' P (str ++ [Z_to_bv 8 0])
      /\ bytes_at usegs m' R (at_random_lo rnd).

  Hypothesis EPS : Forall (fun w : word => bv_unsigned w <> 0%Z) eps.
  Hypothesis NONUL : Forall (fun b : byte => bv_unsigned b <> 0%Z) str.
  Hypothesis LO : (lo <= bv_unsigned sp - 448)%Z.
  Hypothesis LOLO : (alloc_ceiling <= lo)%Z.
  Hypothesis SPE : (bv_unsigned sp <= E)%Z.
  Hypothesis SPP : (bv_unsigned sp <= P)%Z.
  Hypothesis SPR : (bv_unsigned sp <= R)%Z.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition pn_post (x5 x6 x7 x9 x11 x14 x15 x16 x17 x28 x29 x30 x31 : word) (m0 : word -> option byte) : machine_state -> Prop :=
    fun ms' => exists pg m',
    ms' = MS (mkR (Z_to_bv 64 0x183d8) (Z_to_bv 64 (bv_unsigned sp + -384)) gp x11 (* [comment removed for export] *) x5 x6 x7
                  (Z_to_bv 64 P) x9 (Z_to_bv 64 PROGNAME) (Z_to_bv 64 (P + Z.of_nat (length str) + 1)) (Z_to_bv 64 47) z64 x14 x15 x16 x17
                  (Z_to_bv 64 LIBC) s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
             F (Z_to_bv 64 0x184b4) fc None m' (seg_rom usegs)
    /\ munch [(PROGNAME, 0x544e0)]%Z m0 m' /\ wmono usegs m0 m' /\ mem_inv usegs m'
    /\ rw_cells usegs m' PROGNAME [C8 pg; C8 (Z_to_bv 64 P)].

  Lemma pn_loop : forall (k : nat) (j : Z) (m0 mm : word -> option byte) x5 x6 x7 x9 x11 x13 x14 x15 x16 x17 x28 x29 x30 x31 pg,
    (Z.of_nat k = Z.of_nat (length str) + 1 - j)%Z -> (1 <= j)%Z ->
    munch [(PROGNAME, 0x544e0)]%Z m0 mm -> wmono usegs m0 mm -> mem_inv usegs mm ->
    bytes_at usegs mm P (str ++ [Z_to_bv 8 0]) ->
    rw_cells usegs mm PROGNAME [C8 pg; C8 (Z_to_bv 64 P)] ->
    evt usegs (pn_post x5 x6 x7 x9 x11 x14 x15 x16 x17 x28 x29 x30 x31 m0)
      (MS (mkR (Z_to_bv 64 0x183d8) (Z_to_bv 64 (bv_unsigned sp + -384)) gp x11 x5 x6 x7
               (Z_to_bv 64 P) x9 (Z_to_bv 64 PROGNAME) (Z_to_bv 64 (P + j)) (Z_to_bv 64 47) x13 x14 x15 x16 x17
               (Z_to_bv 64 LIBC) s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
          F (Z_to_bv 64 0x184a8) fc None mm (seg_rom usegs)).
  Proof using LO LOLO NONUL SPP. pin_using (fun (LO LOLO NONUL SPP : unit) => tt). ceil_facts.
    induction k as [|k IH]; intros j m0 mm x5 x6 x7 x9 x11 x13 x14 x15 x16 x17 x28 x29 x30 x31 pg Hk Hj MU WM MI STR G2.
    - pose proof (bytes_at_bound _ _ _ _ STR) as BB. rewrite app_length in BB. cbn [length] in BB.
      assert (Hn : nth_error (str ++ [Z_to_bv 8 0]) (Z.to_nat (j - 1)) = Some (Z_to_bv 8 0)).
      { rewrite nth_error_app2 by lia. replace (Z.to_nat (j - 1) - length str)%nat with 0%nat by lia. reflexivity. }
      pose proof (u8ro_read usegs mm P _ (j - 1) _ (Z_to_bv 64 (P + j + -1)) STR Hn ltac:(lia) ltac:(unfold wa; f_equal; lia)) as RD.
      zstep. clear RD. zstep. if_false. zstep. if_false.
      replace (Z_to_bv 64 (P + j)) with (Z_to_bv 64 (P + Z.of_nat (length str) + 1)) by (f_equal; lia).
      unfold pn_post. finish2. all: eassumption.
    - pose proof (bytes_at_bound _ _ _ _ STR) as BB. rewrite app_length in BB. cbn [length] in BB.
      destruct (nth_error str (Z.to_nat (j - 1))) as [b|] eqn:Hb; [| apply nth_error_None in Hb; lia].
      assert (Hn : nth_error (str ++ [Z_to_bv 8 0]) (Z.to_nat (j - 1)) = Some b) by (rewrite nth_error_app1 by lia; exact Hb).
      pose proof (proj1 (Forall_forall _ _) NONUL b (nth_error_In _ _ Hb)) as NZb. cbn in NZb.
      pose proof (bv_unsigned_in_range 8 b) as Rb. unfold bv_modulus in Rb. cbn in Rb.
      pose proof (u8ro_read usegs mm P _ (j - 1) _ (Z_to_bv 64 (P + j + -1)) STR Hn ltac:(lia) ltac:(unfold wa; f_equal; lia)) as RD.
      zstep. clear RD. zstep. if_cases K.
      + (* [comment removed for export] *) lstep. zstep.
        replace (P + j + 1)%Z with (P + (j + 1))%Z by lia.
        eapply (IH (j + 1)%Z); try eassumption; lia.
      + zstep. if_cases K0; zify_cond K0; [| exfalso; lia]. zstep.
        replace (P + j + 1)%Z with (P + (j + 1))%Z by lia.
        eapply (IH (j + 1)%Z); try eassumption; lia.
  Qed.

  (* [comment removed for export] *)
  Ltac scan_it AUXB vi ki :=
    lstep; if_false; ldaux AUXB vi; lstep; lstep;
    (try lazymatch goal with |- context [Z_to_bv 64 (bv_unsigned ?spv + -336 + ?c)] =>
      let off := eval vm_compute in (-336 + c)%Z in
      replace (Z_to_bv 64 (bv_unsigned spv + -336 + c)) with (Z_to_bv 64 (bv_unsigned spv + off)) by (f_equal; lia)
    end);
    (try lazymatch goal with |- context [Z_to_bv 64 (?c + (bv_unsigned ?spv + -336))] =>
      let off := eval vm_compute in (c + -336)%Z in
      replace (Z_to_bv 64 (c + (bv_unsigned spv + -336))) with (Z_to_bv 64 (bv_unsigned spv + off)) by (f_equal; lia)
    end);
    lstep; lstep; ldaux AUXB ki; lstep; astep.

  Definition init_libc_spec__stmt : Prop := forall tp a0 a1,
    stk usegs m lo (bv_unsigned sp) ->
    bytes_at usegs m E (u64s eps ++ le8 z64 ++ u64s (auxv20 uid hw (Z_to_bv 64 R))) ->
    bytes_at usegs m P (str ++ [Z_to_bv 8 0]) ->
    bytes_at usegs m R (at_random_lo rnd) ->
    rw_cells usegs m PROGNAME [C8 pn0; C8 pnf0] ->
    rw_cells usegs m HWCAP [C8 hw0] ->
    rw_cells usegs m ENVIRON [C8 env0] ->
    rw_cells usegs m SYSINFO [C8 z64] ->
    rw_cells usegs m LIBC (libc_cells (Z_to_bv 8 0) (Z_to_bv 8 0) (Z_to_bv 8 0) (Z_to_bv 8 0) z64 z64 z64 z64 z64 z64 z64 (repeat (Z_to_bv 8 0) 48)) ->
    rw_cells usegs m TLL (tll_cells z64 z64 z64 z64 z64 z64 z64) ->
    rw_cells usegs m DEFSTACK [C4 (Z_to_bv 64 0x20000)] ->
    rw_cells usegs m GUARD [CB 8 gjunk] ->
    rw_cells usegs m GOT3 [C8 (Z_to_bv 64 ENVIRON); C8 (Z_to_bv 64 0x544e0); C8 (Z_to_bv 64 PROGNAME)] ->
    rw_cells usegs m GOT_SSP [C8 (Z_to_bv 64 GUARD)] ->
    rw_cells usegs m GOT_DYNAMIC [C8 z64] ->
    rw_cells usegs m 0x34190 [CB 4096 (repeat (Z_to_bv 8 0) 4096)] ->
    mem_inv usegs m ->
    a0 = Z_to_bv 64 E -> a1 = Z_to_bv 64 P ->
    implM usegs (startup_model set_tls 0x34190) s init_libc_post
         (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (Z_to_bv 64 0x183ac) fc None m (seg_rom usegs)).
  Section Sz6.
  Variables tp a0 a1 : ltac2:(SecDiet.SzSec.tyM 'init_libc_spec__stmt "vvv" @tp).
  Lemma init_libc_spec__body : ltac2:(SecDiet.SzSec.bodyP 'init_libc_spec__stmt "vvv").
  Proof using EPS LO LOLO NONUL SPE SPP SPR. pin_using (fun (EPS LO LOLO NONUL SPE SPP SPR : unit) => tt). ceil_facts.
    intros ST ENV STR RND G2 HW ENVC SI LC MT DS GU GOT3 GG GD ZT MI -> ->.
    unfold libc_cells, tll_cells in *.
    pose proof (munch_refl W m) as MU. pose proof (wmono_refl usegs m) as WM.
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
    pose proof (bytes_at_bound _ _ _ _ ENV) as EB. rewrite !app_length, !u64s_length, length_le8 in EB. cbn [length auxv20] in EB.
    pose proof (bytes_at_bound _ _ _ _ STR) as PB. rewrite app_length in PB. cbn [length] in PB.
    pose proof (bytes_at_bound _ _ _ _ RND) as RB. rewrite length_at_random_lo in RB.
    unfold implM. iprefix.
    carve_frame 384%nat ST.
    do 10 lstep.
    (* [comment removed for export] *)
    apply (rw_cells_split_CB usegs _ _ [] 352 _ _ [48; 304]%nat) in FR; [|reflexivity]. cbn [mk_CB_cells app] in FR.
    apply (proj1 (rw_cells_app _ _ _ [_] _)) in FR. destruct FR as [FRlo FR]. cbn [cells_size csize Nat.add] in FR.
    apply (proj1 (rw_cells_app _ _ _ [_] _)) in FR. destruct FR as [AUX FRhi]. cbn [cells_size csize Nat.add] in FRhi.
    change (Z.of_nat 48) with 48%Z in *. change (Z.of_nat 304) with 304%Z in *.
    replace (bv_unsigned sp + -384 + 48)%Z with (bv_unsigned sp + -336)%Z in AUX by lia.
    replace (bv_unsigned sp + -384 + 48 + 304)%Z with (bv_unsigned sp + -32)%Z in FRhi by lia.
    lstep. call (memset_specZ (bv_unsigned sp + -336) 304 0); [exact AUX | exact MI | reflexivity | reflexivity | reflexivity | lia | lia | lia |].
    rename POST into AUX. change (Z.to_nat 304) with 304%nat in AUX. try rename MI0 into MI.
    apply (rw_cells_recast usegs _ _ _ (repeat (C8 z64) 38)) in AUX;
      [| cbn; repeat split; exact I | vm_compute; reflexivity | reflexivity]. cbn [repeat] in AUX.
    (* [comment removed for export] *)
    lstep. lstep. lstep.
    eapply (envp_count_loop eps); [exact EPS | exact ENV |].
    (* [comment removed for export] *)
    lstep. lstep. lstep.
    pose proof ENV as AUXB. apply bytes_at_app in AUXB. destruct AUXB as [_ AUXB].
    apply bytes_at_app in AUXB. destruct AUXB as [_ AUXB]. rewrite u64s_length, length_le8 in AUXB.
    replace (E + Z.of_nat (8 * length eps) + Z.of_nat 8)%Z with AUXV in AUXB by lia.
    ldaux AUXB 0%nat. lstep. if_false. lstep. lstep. lstep. lstep.
    (* [comment removed for export] *)
    scan_it AUXB 1%nat 2%nat. scan_it AUXB 3%nat 4%nat. scan_it AUXB 5%nat 6%nat. scan_it AUXB 7%nat 8%nat.
    scan_it AUXB 9%nat 10%nat. scan_it AUXB 11%nat 12%nat. scan_it AUXB 13%nat 14%nat. scan_it AUXB 15%nat 16%nat.
    scan_it AUXB 17%nat 18%nat.
    (* [comment removed for export] *)
    steps_to 0x18468%Z.
    astep. if_cases K; zify_cond K; [|exfalso; lia]. clear K.
    astep. if_cases K; zify_cond K; [|exfalso; lia]. clear K.
    (* [comment removed for export] *)
    steps_to 0x184a8%Z.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      call (pn_loop (length str) 1 mm mm); [lia | lia | apply munch_refl | apply wmono_refl | exact MI | exact STR | exact G2 | ] end.
    rename POST into G2. try rename MI0 into MI.
    (* [comment removed for export] *)
    apply (proj1 (rw_cells_app _ _ _ [_;_;_] _)) in AUX. destruct AUX as [AUXa AUX].
    apply (proj1 (rw_cells_app _ _ _ [_;_;_] _)) in AUX. destruct AUX as [AUX3 AUXb].
    cbn [cells_size csize Nat.add] in AUX3, AUXb. change (Z.of_nat 24) with 24%Z in *.
    replace (bv_unsigned sp + -336 + 24 + 24)%Z with (bv_unsigned sp + -288)%Z in AUXb by lia.
    lstep. lstep.
    name_sp sp (-384)%Z.
    icallM (init_tls_spec set_tls _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
               lo (bv_unsigned sp + -336)%Z _ _ _ _ _ _ _ _ _ _ s).
    all: lazymatch goal with
         | |- forall _, _ => ipostT usegs; unname_sp
         | |- _ => unname_sp; fastfirst (first [ noevar_assumption | hyp_by_addr | reflexivity | lia ])
         end.
    (* [comment removed for export] *)
    repeat match goal with
           | H1 : rw_cells _ ?mm ?A ?cs, H2 : rw_cells _ ?mm ?A ?cs |- _ => clear H2
           end.
    unfold tls_cells, libc_cells, tll_cells in *.
    match goal with H : stk _ _ _ _ |- _ => rename H into ST end.
    (* [comment removed for export] *)
    lstep. lstep.
    lazymatch goal with TB : tls_block_ok_u ?tb |- _ =>
      call_sp (init_ssp_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ lo R tb rnd) end.
    all: lazymatch goal with
         | |- evt _ _ _ => idtac
         | |- tls_block_ok_u _ => assumption
         | |- ?g => fastfirst (first [ noevar_assumption | hyp_by_addr | reflexivity | lia ])
         end.
    match goal with H : stk _ _ _ _ |- _ => rename H into ST end.
    (* [comment removed for export] *)
    do 3 lstep. if_false. lstep. lstep. lstep. if_false. lstep. lstep. if_true.
    do 5 lstep.
    join2 FRlo AUXa. join2 FRlo AUX3. join2 FRlo AUXb. join2 FRlo FRhi.
    release_frame FRlo ST (bv_unsigned sp).
    lstep.
    apply evt_done. unfold init_libc_post.
    lazymatch goal with TB : tls_block_ok_u ?tb, Ht : (0 < ?t < 4194304)%Z |- _ => exists tb, t end.
    repeat (lazymatch goal with |- ex _ => eexists end).
    split. { split; [assumption|]. split; [assumption|]. assumption. }
    split. { cbv delta [mkR]. reflexivity. }
    repeat match goal with |- _ /\ _ => split end; fastfirst (first [hyp_by_addr | assumption | lia]).
  Qed.
  End Sz6.
  Lemma init_libc_spec : ltac:(let t := eval cbv delta [init_libc_spec__stmt] in init_libc_spec__stmt in exact t).
  Proof using EPS LO LOLO NONUL SPE SPP SPR. intros tp a0 a1. ltac2:(SecDiet.SzSec.closeP 'init_libc_spec__body "vvv"). Qed.
End InitLibc.

End WithCeil.
End TwB.
End Startup_B.

(* [comment removed for export] *)
Module Startup.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import Tac Arr Bytes ITree Nodes Decode SysStep RegsEquiv ImgSrc3.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Monad. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Adapter__Spec. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Monad OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Adapter__Spec.StartupModel.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require FileCells__Musl. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require AmoStep__Musl. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require InitMem. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require Printf_kit__Musl. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.FileCells__Musl.StrFun OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.STRW_tac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.InitMem OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_kit__Musl.StartupKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.EntryRnd.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_memchr__S3. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_memchr__S3.F_memset OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Startup_B__S3.Startup_B.
From OSSVerify.libpcap.fuzz_pcap.images Require Import Plain.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import LiaPin.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac lia ::= pinned_lia.
Import ListNotations.
Open Scope bv_scope.
Import ITree.Exc.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Notation ph := Plain.M.phdrs.
Notation MAIN := 0x13b10%Z (only parsing).
Notation RA_MAIN := 0x17f08%Z (only parsing).   (* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section WithCeil.
Context {CEILV : CEIL}.
Section AtMain.
  Variables (sp0 : word) (argv envp : list (list byte)) (uid hw : word) (rnd : EntryDraw).   (* [comment removed for export] *)
  Notation usp0 := (bv_unsigned sp0).

  (* [comment removed for export] *)
  Definition crt_written : list (Z * Z) :=
    [(0x23940, 0x23941);   (* [comment removed for export] *)
     (0x339c8, 0x339d0);   (* [comment removed for export] *)
     (0x53aa8, 0x53ad8);   (* [comment removed for export] *)
     (0x53d08, 0x53d10);   (* [comment removed for export] *)
     (0x53d18, 0x53d60);   (* [comment removed for export] *)
     (0x53d90, 0x53d98);   (* [comment removed for export] *)
     (0x339d0, 0x349d0)]%Z.

  (* [comment removed for export] *)
  Definition at_main (tp : word) : machine_state -> Prop :=
    fun ms' => exists (t0 t1 t2 a3 a4 a5 a6 a7 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
                      (t P0 : Z) (pg : word) (m' : word -> option byte),
    ms' = MS (mkR (Z_to_bv 64 RA_MAIN) (Z_to_bv 64 (usp0 + -48)) (Z_to_bv 64 0x10800) tp
                 t0 t1 t2 (Z_to_bv 64 (usp0 + 8)) (Z_to_bv 64 (argc argv))
                 (Z_to_bv 64 (argc argv)) (Z_to_bv 64 (usp0 + 8)) (Z_to_bv 64 (envp_addr sp0 argv)) a3 a4 a5 a6 a7
                 (Z_to_bv 64 MAIN) (Z_to_bv 64 (envp_addr sp0 argv)) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             bvmap_empty (Z_to_bv 64 MAIN) (Z_to_bv 32 0) None m' (seg_rom ssegs)
    /\ mem_inv ssegs m'
    /\ stk ssegs m' (usp0 - 8388608) (usp0 + -48)
    (* [comment removed for export] *)
    /\ tls_block_ok (bv_unsigned tp - 200)
    (* [comment removed for export] *)
    /\ rw_cells ssegs m' (bv_unsigned tp + -200)
         [C8 (Z_to_bv 64 (bv_unsigned tp - 200)); C8 (Z_to_bv 64 (bv_unsigned tp - 200)); C8 (Z_to_bv 64 (bv_unsigned tp - 200)); C8 z64; C4 (Z_to_bv 64 t)]
    (* [comment removed for export] *)
    /\ rw_cells ssegs m' (bv_unsigned tp + -164) [C4 z64]
    (* [comment removed for export] *)
    /\ rw_cells ssegs m' (bv_unsigned tp + -160)
         [C4 (Z_to_bv 64 2); CB 76 (repeat (Z_to_bv 8 0) 76); C8 (Z_to_bv 64 (bv_unsigned tp - 80));
          CB 24 (repeat (Z_to_bv 8 0) 24); C8 (Z_to_bv 64 0x53d60); CB 24 (repeat (Z_to_bv 8 0) 24)]
    (* [comment removed for export] *)
    /\ rw_cells ssegs m' (bv_unsigned tp + -16) [C8 (ssp_canary rnd)]
    (* [comment removed for export] *)
    /\ rw_cells ssegs m' (bv_unsigned tp + -8) [C8 (Z_to_bv 64 (bv_unsigned tp + 264))]
    (* [comment removed for export] *)
    /\ rw_cells ssegs m' (bv_unsigned tp) [CB 256 (repeat (Z_to_bv 8 0) 256)]
    (* [comment removed for export] *)
    /\ rw_cells ssegs m' (bv_unsigned tp + 256)
         [CB 8 (repeat (Z_to_bv 8 0) 8); C8 (Z_to_bv 64 1); C8 (Z_to_bv 64 (bv_unsigned tp + 2048)); CB 3616 (repeat (Z_to_bv 8 0) 3616)]
    (* [comment removed for export] *)
    /\ rw_cells ssegs m' 0x53d28 (libc_cells (Z_to_bv 8 1) (Z_to_bv 8 0) (Z_to_bv 8 0) (Z_to_bv 8 0) z64
                                   (Z_to_bv 64 (auxv_addr sp0 argv envp)) (Z_to_bv 64 0x53aa8) (Z_to_bv 64 480)
                                   (Z_to_bv 64 8) (Z_to_bv 64 1) (Z_to_bv 64 4096) (repeat (Z_to_bv 8 0) 48))
    (* [comment removed for export] *)
    /\ rw_cells ssegs m' 0x53aa0 (tll_cells z64 z64 (Z_to_bv 64 0x2154c) z64 (Z_to_bv 64 0x100) (Z_to_bv 64 8) z64)
    (* [comment removed for export] *)
    /\ rw_cells ssegs m' 0x53d10 [C8 z64]
    /\ rw_cells ssegs m' 0x53d18 [C8 pg; C8 (Z_to_bv 64 P0)]
    /\ rw_cells ssegs m' 0x53d90 [C8 hw]                 (* [comment removed for export] *)
    /\ rw_cells ssegs m' 0x339c8 [C8 (Z_to_bv 64 (envp_addr sp0 argv))]
    /\ rw_cells ssegs m' 0x23930 [C4 (Z_to_bv 64 0x20000)]
    /\ rw_cells ssegs m' 0x53d08 [C8 (ssp_canary rnd)]   (* [comment removed for export] *)
    (* [comment removed for export] *)
    /\ rw_cells ssegs m' 0x22580 [C8 z64]
    /\ rw_cells ssegs m' 0x22588 [C8 (Z_to_bv 64 MAIN); C8 (Z_to_bv 64 0x17be8); C8 (Z_to_bv 64 0x1840c); C8 z64]
    /\ rw_cells ssegs m' 0x225a8 [C8 (Z_to_bv 64 0x18340); C8 z64]
    /\ rw_cells ssegs m' 0x225f8 [C8 (Z_to_bv 64 0x339c8); C8 (Z_to_bv 64 0x53d20); C8 (Z_to_bv 64 0x53d18)]
    /\ rw_cells ssegs m' 0x22610 [C8 (Z_to_bv 64 0x22558); C8 (Z_to_bv 64 0x22550)]
    /\ rw_cells ssegs m' 0x22620 [C8 (Z_to_bv 64 0x53d08)]
    /\ rw_cells ssegs m' 0x22628 [C8 (Z_to_bv 64 0x22560); C8 (Z_to_bv 64 0x22558)]
    (* [comment removed for export] *)
    /\ rw_cells ssegs m' 0x22550 [C8 (Z_to_bv 64 0x13a0c)]
    /\ rw_cells ssegs m' 0x22558 [C8 (Z_to_bv 64 0x13a80)]
    (* [comment removed for export] *)
    /\ rw_cells ssegs m' 0x23638 [C8 (Z_to_bv 64 0x23638)]
    /\ rw_cells ssegs m' 0x23940 [C1 (Z_to_bv 8 1)]
    /\ rw_cells ssegs m' 0x23988 [C1 (Z_to_bv 8 0)]
    (* [comment removed for export] *)
    /\ rw_cells ssegs m' 0x53d00 [C4 z64]
    /\ rw_cells ssegs m' 0x53ae0 [C1 (Z_to_bv 8 0); CB 3 (repeat (Z_to_bv 8 0) 3); C4 z64; C4 z64; CB 4 (repeat (Z_to_bv 8 0) 4); C8 z64]
    (* [comment removed for export] *)
    /\ bytes_at ssegs m' usp0 (build_stack_bytes ph sp0 argv envp uid hw rnd)
    /\ wr_at ssegs m' usp0 (Z.of_nat (length (build_stack_bytes ph sp0 argv envp uid hw rnd)))
    /\ nth_error (argv_ptrs sp0 argv envp) 0 = Some (Z_to_bv 64 P0)
    (* [comment removed for export] *)
    /\ (forall a : word, (0x22000 <= bv_unsigned a < 0x55000)%Z -> outside crt_written (bv_unsigned a) -> m' a = None)
    /\ (0 < t < 4194304)%Z
    (* [comment removed for export] *)
    /\ (alloc_ceiling <= usp0 - 8388608)%Z.
End AtMain.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section Proof.
  Context {St : Type} (set_tls : Z -> St -> St).
  Variables (sp0 : word) (argv envp : list (list byte)) (uid hw : word) (rnd : EntryDraw).   (* [comment removed for export] *)
  Hypothesis VSP : valid_sp sp0.
  Hypothesis VARGV : valid_argv argv.
  Hypothesis VENVP : valid_envp envp.
  Hypothesis FITS : entry_stack_fits sp0 argv envp.
  (* [comment removed for export] *)
  Hypothesis CLO : (alloc_ceiling <= bv_unsigned sp0 - 8388608)%Z.
  Notation usp0 := (bv_unsigned sp0).
  Notation img := (build_stack_bytes ph sp0 argv envp uid hw rnd).
  Notation esi := (entry_stack_image ph sp0 argv envp uid hw rnd).   (* [comment removed for export] *)

  Lemma img_len_bound : (Z.of_nat (length img) <= 2500000)%Z.
  Proof using CEILV VARGV VENVP. pin_using (fun (CEILV VARGV VENVP : unit) => tt). ceil_facts.
    rewrite build_stack_bytes_length. destruct VARGV as (A1 & A2 & _). destruct VENVP as (E1 & E2 & _).
    pose proof (raw_len_nonneg ph sp0 argv envp uid hw rnd). unfold raw_len, struct_size, argc, envc in *. lia.
  Qed.

  Lemma sp_facts : (stack_max_size <= usp0)%Z /\ (usp0 + Z.of_nat (length esi) <= 2^64)%Z /\
                   (usp0 mod 16 = 0)%Z /\ (0x7fff80000000 <= usp0 <= 0x800000000000)%Z /\
                   (usp0 + Z.of_nat (length img) <= 0x800000000000)%Z.
  Proof using CEILV FITS VSP. pin_using (fun (CEILV FITS VSP : unit) => tt). ceil_facts.
    destruct (entry_bounds ph sp0 argv envp uid hw rnd VSP FITS) as [A B].
    pose proof (bsb_le_esi ph sp0 argv envp uid hw rnd) as C.
    destruct VSP as (L & H & M). unfold sp_window_lo, sp_window_hi, stack_max_size in *. lia.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition startup_post (s : St) : unit -> St -> machine_state -> Prop :=
    fun _ s' ms' => exists tp : word, s' = set_tls (bv_unsigned tp - 200)%Z s /\ at_main sp0 argv envp uid hw rnd tp ms'.

  Theorem startup_spec : forall s : St,
    implM ssegs (startup_model set_tls 0x339d0) s (startup_post s)
          (init_ms ssegs Plain.M.init_pc ph sp0 rnd argv envp uid hw).
  Proof using CLO FITS VARGV VENVP VSP. pin_using (fun (CLO FITS VARGV VENVP VSP : unit) => tt). ceil_facts.
    intros s.
    destruct sp_facts as (SPLO & IMGHI & SP16 & SPW & IMGTOP).
    pose proof img_len_bound as IL.
    unfold init_ms, mkR_init. change (Z.of_N Plain.M.init_pc) with 0x139c4%Z.
    set (m := wrap_mem ph sp0 argv envp uid hw rnd).
    assert (NONE : forall a : word, (bv_unsigned a < 0x55000)%Z -> m a = None).
    { intros a Ha. apply init_none. unfold stack_max_size. lia. }
    pose proof (init_stk ssegs ph sp0 argv envp uid hw rnd SPLO) as ST. fold m in ST.
    change stack_max_size with 8388608%Z in ST.
    pose proof (init_mem_inv' ssegs ph sp0 argv envp uid hw rnd SPLO IMGHI ltac:(change (segs_top ssegs) with 0x55000%Z; unfold stack_max_size; lia)) as MI.
    fold m in MI.
    pose proof (init_block_bytes ssegs ph sp0 argv envp uid hw rnd SPLO IMGHI) as IMG. fold m in IMG.   (* [comment removed for export] *)
    pose proof (init_wr ssegs ph sp0 argv envp uid hw rnd SPLO IMGHI) as WR. fold m in WR. rewrite <- (build_stack_bytes_length ph sp0 argv envp uid hw rnd) in WR.
    destruct (init_pieces ssegs ph sp0 argv envp uid hw rnd SPLO IMGHI) as (ARGC & ARGV & ENVP & AUXW & _ & _ & RNDB). fold m in ARGC, ARGV, ENVP, AUXW, RNDB.
    (* [comment removed for export] *)
    destruct VARGV as (VA1 & VA2 & VA3 & VA4 & _).   (* [comment removed for export] *)
    assert (Harg0 : exists arg0, nth_error argv 0 = Some arg0).
    { destruct argv as [|a ?]; [cbn in VA1; lia | exists a; reflexivity]. }
    destruct Harg0 as [arg0 Harg0].
    destruct (init_argv_string ssegs ph sp0 argv envp uid hw rnd SPLO IMGHI 0 arg0 Harg0) as (P0 & HP0 & P0LO & P0HI & STR).
    fold m in STR.
    pose proof (proj1 (Forall_forall _ _) VA4 arg0 (nth_error_In _ _ Harg0)) as NONUL0. cbn beta in NONUL0.
    assert (NONUL : Forall (fun b : byte => bv_unsigned b <> 0%Z) arg0).
    { apply Forall_forall. intros b Hb E0. apply NONUL0. replace (Z_to_bv 8 0) with b; [exact Hb|]. apply bv_eq. rewrite E0. reflexivity. }
    assert (EPS : Forall (fun w : word => bv_unsigned w <> 0%Z) (envp_ptrs sp0 argv envp)).
    { apply Forall_forall. intros w Hw. destruct (In_nth_error _ _ Hw) as [i Hi].
      pose proof (envp_ptr_bounds ph sp0 argv envp uid hw rnd IMGHI i w Hi).
      pose proof (raw_len_nonneg ph sp0 argv envp uid hw rnd). unfold env_base, str_base, struct_size in *. lia. }
    (* [comment removed for export] *)
    assert (RND : bytes_at ssegs m (rnd_addr sp0 argv envp) (at_random_lo rnd)).   (* [comment removed for export] *)
    { rewrite at_random_split in RNDB. apply bytes_at_app in RNDB. exact (proj1 RNDB). }
    assert (RLO : (usp0 <= rnd_addr sp0 argv envp)%Z).
    { pose proof (raw_len_nonneg ph sp0 argv envp uid hw rnd). unfold rnd_addr, raw_len. lia. }
    (* [comment removed for export] *)
    rimg_chunk ssegs NONE m 0x53d18%Z [C8 z64; C8 z64] G2.
    rimg_chunk ssegs NONE m 0x53d90%Z [C8 z64] HW.
    rimg_chunk ssegs NONE m 0x339c8%Z [C8 z64] ENVC.
    rimg_chunk ssegs NONE m 0x53d10%Z [C8 z64] SI.
    rimg_chunk ssegs NONE m 0x53d28%Z (libc_cells (Z_to_bv 8 0) (Z_to_bv 8 0) (Z_to_bv 8 0) (Z_to_bv 8 0) z64 z64 z64 z64 z64 z64 z64 (repeat (Z_to_bv 8 0) 48)) LC.
    rimg_chunk ssegs NONE m 0x53aa0%Z (tll_cells z64 z64 z64 z64 z64 z64 z64) MT.
    rimg_chunk ssegs NONE m 0x23930%Z [C4 (Z_to_bv 64 0x20000)] DS.
    rimg_chunk ssegs NONE m 0x53d08%Z [CB 8 (repeat (Z_to_bv 8 0) 8)] GU.
    rimg_chunk ssegs NONE m 0x225f8%Z [C8 (Z_to_bv 64 0x339c8); C8 (Z_to_bv 64 0x53d20); C8 (Z_to_bv 64 0x53d18)] G3.
    rimg_chunk ssegs NONE m 0x22620%Z [C8 (Z_to_bv 64 0x53d08)] GG.
    rimg_chunk ssegs NONE m 0x22580%Z [C8 z64] GD.
    rimg_chunk ssegs NONE m 0x22588%Z [C8 (Z_to_bv 64 MAIN); C8 (Z_to_bv 64 0x17be8); C8 (Z_to_bv 64 0x1840c); C8 z64] GOT0.
    rimg_chunk ssegs NONE m 0x22610%Z [C8 (Z_to_bv 64 0x22558); C8 (Z_to_bv 64 0x22550)] GIN.
    rimg_chunk ssegs NONE m 0x22550%Z [C8 (Z_to_bv 64 0x13a0c)] INA.
    rimg_chunk ssegs NONE m 0x23940%Z [C1 (Z_to_bv 8 0)] INI.
    rimg_chunk ssegs NONE m 0x339d0%Z [CB 4096 (repeat (Z_to_bv 8 0) 4096)] ZT.
    unfold libc_cells, tll_cells in LC, MT.
    assert (HC : argc argv = Z.of_nat (length argv)) by reflexivity.
    assert (HE : envc envp = Z.of_nat (length envp)) by reflexivity.
    assert (P0GE : (usp0 + 184 <= P0)%Z).   (* [comment removed for export] *)
    { pose proof (raw_len_nonneg ph sp0 argv envp uid hw rnd). unfold str_base, struct_size in P0LO. lia. }
    pose proof (munch_refl [(usp0 - 8388608, usp0); (0x23940, 0x23941); (0x339c8, 0x339d0); (0x53aa8, 0x53ad8);
                            (0x53d08, 0x53d10); (0x53d18, 0x53d60); (0x53d90, 0x53d98); (0x339d0, 0x349d0)]%Z m) as MU.
    pose proof (wmono_refl ssegs m) as WM.
    clearbody m.
    (* [comment removed for export] *)
    change (id (bytes_at ssegs m usp0 img)) in IMG. change (id (wr_at ssegs m usp0 (Z.of_nat (length img)))) in WR.
    unfold implM. iprefix.
    (* [comment removed for export] *)
    do 7 lstep.
    (* [comment removed for export] *)
    pose proof (bytes_at_read ssegs m usp0 _ 0 4 ARGC ltac:(lia) ltac:(rewrite length_le8; lia)) as RD.
    change (firstn 4 (skipn (Z.to_nat 0) (le8 (Z_to_bv 64 (argc argv))))) with (le4 (Z_to_bv 64 (argc argv))) in RD.
    let a := cur_mem_addr in replace (wa (usp0 + 0)) with a in RD by (unfold wa; rewrite Z.add_0_r; try reflexivity; symmetry; apply Z_to_bv_bv_unsigned).
    lstep. clear RD.
    replace (Z_to_bv 64 (Z.land usp0 18446744073709551600)) with sp0.
    2:{ change 18446744073709551600%Z with (2^64 - 2^4)%Z. rewrite land_align_down by lia.
        change (2^4)%Z with 16%Z. rewrite SP16, Z.sub_0_r. symmetry. apply Z_to_bv_bv_unsigned. }
    replace (sx32 (Z_to_bv 64 (argc argv))) with (Z_to_bv 64 (argc argv)).
    2:{ unfold sx32. f_equal. unfold argc. rewrite unsigned_lit by lia. symmetry. apply swrap32_small. lia. }
    steps_to 0x17e64%Z.
    (* [comment removed for export] *)
    carve_frame 32%nat ST.
    do 8 lstep.
    (* [comment removed for export] *)
    pose proof (rd_u64s_g ssegs _ (usp0 + 8) _ 0 _ (Z_to_bv 64 (usp0 + 8)) ARGV ltac:(rewrite nth_error_app1 by (rewrite argv_ptrs_length; lia); exact HP0) ltac:(unfold wa; f_equal; lia)) as RD.
    lstep. clear RD ARGV.
    do 3 lstep.
    replace (Z_to_bv 64 (usp0 + 8 + Z.shiftl (argc argv) 3 + 8)) with (Z_to_bv 64 (envp_addr sp0 argv))
      by (unfold envp_addr; f_equal; rewrite Z.shiftl_mul_pow2 by lia; lia).
    (* [comment removed for export] *)
    assert (ENV : bytes_at ssegs m1 (envp_addr sp0 argv)
                    (u64s (envp_ptrs sp0 argv envp) ++ le8 z64 ++ u64s (auxv20 uid hw (Z_to_bv 64 (rnd_addr sp0 argv envp))))).
    { rewrite u64s_app in ENVP. cbn [u64s] in ENVP. rewrite app_nil_r in ENVP.
      apply bytes_at_app in ENVP. destruct ENVP as [E1 E2]. rewrite u64s_length, envp_ptrs_length in E2.
      unfold envp_addr. apply bytes_at_app. split; [exact E1|]. apply bytes_at_app. split.
      - rewrite u64s_length, envp_ptrs_length. exact E2.
      - rewrite u64s_length, envp_ptrs_length, length_le8.
        replace (usp0 + 8 * (argc argv + 2) + Z.of_nat (8 * length envp) + Z.of_nat 8)%Z
          with (usp0 + 8 * (argc argv + envc envp + 3))%Z by lia.
        exact AUXW. }
    clear ENVP AUXW ARGC RNDB.
    lstep. name_sp sp0 (-32)%Z.
    icallM (init_libc_spec set_tls _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (usp0 - 8388608)%Z
              (envp_addr sp0 argv) (envp_ptrs sp0 argv envp) uid hw rnd (rnd_addr sp0 argv envp) P0 arg0 _ _ _ _ _ s).
    all: lazymatch goal with
         | |- forall _, _ => ipostT ssegs; unname_sp
         | |- Forall _ _ => first [exact EPS | exact NONUL]
         | |- _ => unname_sp; fastfirst (first [ noevar_assumption | hyp_by_addr | reflexivity | unfold envp_addr; lia ])
         end.
    (* [comment removed for export] *)
    repeat match goal with
           | H : bytes_at _ _ _ (u64s _ ++ _) |- _ => clear H
           | H : bytes_at _ _ P0 _ |- _ => clear H
           | H : bytes_at _ _ (rnd_addr _ _ _) _ |- _ => clear H
           end.
    repeat match goal with H1 : rw_cells _ ?mm ?A ?cs, H2 : rw_cells _ ?mm ?A ?cs |- _ => clear H2 end.
    clear EPS NONUL NONUL0 VA2 VA3 VA4 RLO P0HI.
    unfold tls_cells, libc_cells, tll_cells in *.
    match goal with H : stk _ _ _ _ |- _ => rename H into ST end.
    rewrite envp_ptrs_length in *.
    replace (envp_addr sp0 argv + 8 * (Z.of_nat (length envp) + 1))%Z with (auxv_addr sp0 argv envp) in *
      by (unfold auxv_addr, envp_addr, envc; lia).
    (* [comment removed for export] *)
    steps_to 0x17ec0%Z. release_frame FR ST (bv_unsigned sp0). astep.
    (* [comment removed for export] *)
    carve_frame 48%nat ST. steps_to 0x17e18%Z.
    (* [comment removed for export] *)
    carve_frame 32%nat ST. steps_to 0x13a0c%Z.
    (* [comment removed for export] *)
    carve_frame 16%nat ST. steps_to 0x13a28%Z. try change (zxb (Z_to_bv 8 0)) with (Z_to_bv 64 0).
    steps_to 0x13a7c%Z. release_frame FR1 ST (usp0 + -80)%Z. astep.
    steps_to 0x17e60%Z. release_frame FR0 ST (usp0 + -48)%Z. astep.
    (* [comment removed for export] *)
    steps_to 0x13b10%Z.
    replace (Z_to_bv 64 (usp0 + 8 + Z.shiftl (argc argv) 3 + 8)) with (Z_to_bv 64 (envp_addr sp0 argv))
      by (unfold envp_addr; f_equal; rewrite Z.shiftl_mul_pow2 by lia; lia).
    (* [comment removed for export] *)
    unfold id in IMG, WR.
    lazymatch type of MU with munch ?W m ?mf =>
      apply (bytes_at_transport ssegs W m mf usp0 img) in IMG; [| exact MU | cbn [disjoint_from]; lia];
      apply (wr_at_transport ssegs m mf) in WR; [| exact WM] end.
    (* [comment removed for export] *)
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mf _) =>
      assert (NONE' : forall a : word, (0x22000 <= bv_unsigned a < 0x55000)%Z ->
                outside [(0x23940, 0x23941); (0x339c8, 0x339d0); (0x53aa8, 0x53ad8);
                         (0x53d08, 0x53d10); (0x53d18, 0x53d60); (0x53d90, 0x53d98); (0x339d0, 0x349d0)]%Z (bv_unsigned a) -> mf a = None)
        by (intros a Ha Ho; rewrite (MU a); [apply NONE; lia | cbn [outside] in Ho |- *; lia]);
      rimg_chunk ssegs NONE' mf 0x225a8%Z [C8 (Z_to_bv 64 0x18340); C8 z64] GCX;
      rimg_chunk ssegs NONE' mf 0x22628%Z [C8 (Z_to_bv 64 0x22560); C8 (Z_to_bv 64 0x22558)] GFI;
      rimg_chunk ssegs NONE' mf 0x22558%Z [C8 (Z_to_bv 64 0x13a80)] FIA;
      rimg_chunk ssegs NONE' mf 0x23638%Z [C8 (Z_to_bv 64 0x23638)] DSO;
      rimg_chunk ssegs NONE' mf 0x23988%Z [C1 (Z_to_bv 8 0)] FIN;
      rimg_chunk ssegs NONE' mf 0x53d00%Z [C4 z64] EXL;
      rimg_chunk ssegs NONE' mf 0x53ae0%Z [C1 (Z_to_bv 8 0); CB 3 (repeat (Z_to_bv 8 0) 3); C4 z64; C4 z64; CB 4 (repeat (Z_to_bv 8 0) 4); C8 z64] ATX
    end.
    (* [comment removed for export] *)
    lazymatch goal with TB : tls_block_ok ?tb, TLS : rw_cells _ _ ?tb _ |- _ =>
      rename TLS into TLS0;
      remember (Z_to_bv 64 (tb + 200)) as tpw eqn:Etpw;
      assert (Eu : bv_unsigned tpw = (tb + 200)%Z) by (subst tpw; apply unsigned_lit; lia);
      apply (proj1 (rw_cells_app _ _ _ [_;_;_;_;_] _)) in TLS0; destruct TLS0 as [TDH TLS0];
      apply (proj1 (rw_cells_app _ _ _ [_] _)) in TLS0; destruct TLS0 as [ERR TLS0];
      apply (proj1 (rw_cells_app _ _ _ [_;_;_;_;_;_] _)) in TLS0; destruct TLS0 as [TDM TLS0];
      apply (proj1 (rw_cells_app _ _ _ [_] _)) in TLS0; destruct TLS0 as [CAN TLS0];
      apply (proj1 (rw_cells_app _ _ _ [_] _)) in TLS0; destruct TLS0 as [DTVP TLS0];
      apply (proj1 (rw_cells_app _ _ _ [_] _)) in TLS0; destruct TLS0 as [TLSA DTV];
      cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in ERR, TDM, CAN, DTVP, TLSA, DTV;
      match type of TDH with rw_cells _ _ ?A _ => replace A with (bv_unsigned tpw + -200)%Z in TDH by lia end;
      match type of ERR with rw_cells _ _ ?A _ => replace A with (bv_unsigned tpw + -164)%Z in ERR by lia end;
      match type of TDM with rw_cells _ _ ?A _ => replace A with (bv_unsigned tpw + -160)%Z in TDM by lia end;
      match type of CAN with rw_cells _ _ ?A _ => replace A with (bv_unsigned tpw + -16)%Z in CAN by lia end;
      match type of DTVP with rw_cells _ _ ?A _ => replace A with (bv_unsigned tpw + -8)%Z in DTVP by lia end;
      match type of TLSA with rw_cells _ _ ?A _ => replace A with (bv_unsigned tpw) in TLSA by lia end;
      match type of DTV with rw_cells _ _ ?A _ => replace A with (bv_unsigned tpw + 256)%Z in DTV by lia end;
      replace (tb + 120)%Z with (bv_unsigned tpw - 80)%Z in TDM by lia;
      replace (tb + 464)%Z with (bv_unsigned tpw + 264)%Z in DTVP by lia;
      replace (tb + 2248)%Z with (bv_unsigned tpw + 2048)%Z in DTV by lia;
      assert (Etb : tb = (bv_unsigned tpw - 200)%Z) by lia;
      clear Etpw Eu; rewrite Etb in *; clear Etb
    end.
    apply evt_done. unfold startup_post, at_main. exists tpw. split; [assumption|].
    (* [comment removed for export] *)
    let z := fresh "sblz" in pose (z := repeat (Z_to_bv 8 0) 3616); change (repeat (Z_to_bv 8 0) 3616) with z.
    let x := fresh "sbl" in pose (x := 3616%nat); change 3616%nat with x.
    let z := fresh "sblz" in pose (z := repeat (Z_to_bv 8 0) 256); change (repeat (Z_to_bv 8 0) 256) with z.
    repeat (lazymatch goal with |- ex _ => eexists end).
    split; [cbv delta [mkR]; reflexivity|].
    repeat match goal with |- _ /\ _ => split end.
    all: lazymatch goal with
         | |- nth_error _ _ = _ => exact HP0
         | |- wr_at _ _ _ _ => exact WR
         | |- forall _, _ => intros a Ha Hout; rewrite (MU a); [apply NONE; lia|];
                              unfold crt_written in Hout; cbn [outside] in Hout |- *; lia
         | |- _ => fastfirst (first [ noevar_assumption |hyp_by_addr | assumption | lia])
         end.
  Qed.
End Proof.

End WithCeil.

(* [comment removed for export] *)
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require ImgTgtUbsan.
From OSSVerify.libpcap.fuzz_pcap.images Require Ubsan.
Module TwB.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Tac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Arr OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Bytes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ITree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Nodes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Decode OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.SysStep OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.RegsEquiv OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ImgTgtUbsan.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Monad OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Adapter__Spec.StartupModel.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.FileCells__Musl.StrFun OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.STRW_tac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.InitMem OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_kit__Musl.StartupKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.EntryRnd.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_memchr__S3.F_memset.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Startup_B__S3.Startup_B.TwB.
Import OSSVerify.libpcap.fuzz_pcap.images.Ubsan.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.LiaPin.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac lia ::= pinned_lia.
Import ListNotations.
Open Scope bv_scope.
Import ITree.Exc.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Notation ph := Ubsan.M.phdrs.
Notation MAIN := 0x13b84%Z (only parsing).
Notation RA_MAIN := 0x186c8%Z (only parsing).   (* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section WithCeil.
Context {CEILV : CEIL}.
Section AtMain.
  Variables (sp0 : word) (argv envp : list (list byte)) (uid hw : word) (rnd : EntryDraw).   (* [comment removed for export] *)
  Notation usp0 := (bv_unsigned sp0).

  (* [comment removed for export] *)
  Definition crt_written : list (Z * Z) :=
    [(0x24100, 0x24101);   (* [comment removed for export] *)
     (0x34188, 0x34190);   (* [comment removed for export] *)
     (0x54268, 0x54298);   (* [comment removed for export] *)
     (0x544c8, 0x544d0);   (* [comment removed for export] *)
     (0x544d8, 0x54520);   (* [comment removed for export] *)
     (0x54550, 0x54558);   (* [comment removed for export] *)
     (0x34190, 0x35190)]%Z.

  (* [comment removed for export] *)
  Definition at_main (tp : word) : machine_state -> Prop :=
    fun ms' => exists (t0 t1 t2 a3 a4 a5 a6 a7 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
                      (t P0 : Z) (pg : word) (m' : word -> option byte),
    ms' = MS (mkR (Z_to_bv 64 RA_MAIN) (Z_to_bv 64 (usp0 + -48)) (Z_to_bv 64 0x10800) tp
                 t0 t1 t2 (Z_to_bv 64 (usp0 + 8)) (Z_to_bv 64 (argc argv))
                 (Z_to_bv 64 (argc argv)) (Z_to_bv 64 (usp0 + 8)) (Z_to_bv 64 (envp_addr sp0 argv)) a3 a4 a5 a6 a7
                 (Z_to_bv 64 MAIN) (Z_to_bv 64 (envp_addr sp0 argv)) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             bvmap_empty (Z_to_bv 64 MAIN) (Z_to_bv 32 0) None m' (seg_rom usegs)
    /\ mem_inv usegs m'
    /\ stk usegs m' (usp0 - 8388608) (usp0 + -48)
    (* [comment removed for export] *)
    /\ tls_block_ok_u (bv_unsigned tp - 200)
    (* [comment removed for export] *)
    /\ rw_cells usegs m' (bv_unsigned tp + -200)
         [C8 (Z_to_bv 64 (bv_unsigned tp - 200)); C8 (Z_to_bv 64 (bv_unsigned tp - 200)); C8 (Z_to_bv 64 (bv_unsigned tp - 200)); C8 z64; C4 (Z_to_bv 64 t)]
    (* [comment removed for export] *)
    /\ rw_cells usegs m' (bv_unsigned tp + -164) [C4 z64]
    (* [comment removed for export] *)
    /\ rw_cells usegs m' (bv_unsigned tp + -160)
         [C4 (Z_to_bv 64 2); CB 76 (repeat (Z_to_bv 8 0) 76); C8 (Z_to_bv 64 (bv_unsigned tp - 80));
          CB 24 (repeat (Z_to_bv 8 0) 24); C8 (Z_to_bv 64 0x54520); CB 24 (repeat (Z_to_bv 8 0) 24)]
    (* [comment removed for export] *)
    /\ rw_cells usegs m' (bv_unsigned tp + -16) [C8 (ssp_canary rnd)]
    (* [comment removed for export] *)
    /\ rw_cells usegs m' (bv_unsigned tp + -8) [C8 (Z_to_bv 64 (bv_unsigned tp + 264))]
    (* [comment removed for export] *)
    /\ rw_cells usegs m' (bv_unsigned tp) [CB 256 (repeat (Z_to_bv 8 0) 256)]
    (* [comment removed for export] *)
    /\ rw_cells usegs m' (bv_unsigned tp + 256)
         [CB 8 (repeat (Z_to_bv 8 0) 8); C8 (Z_to_bv 64 1); C8 (Z_to_bv 64 (bv_unsigned tp + 2048)); CB 3616 (repeat (Z_to_bv 8 0) 3616)]
    (* [comment removed for export] *)
    /\ rw_cells usegs m' 0x544e8 (libc_cells (Z_to_bv 8 1) (Z_to_bv 8 0) (Z_to_bv 8 0) (Z_to_bv 8 0) z64
                                   (Z_to_bv 64 (auxv_addr sp0 argv envp)) (Z_to_bv 64 0x54268) (Z_to_bv 64 480)
                                   (Z_to_bv 64 8) (Z_to_bv 64 1) (Z_to_bv 64 4096) (repeat (Z_to_bv 8 0) 48))
    (* [comment removed for export] *)
    /\ rw_cells usegs m' 0x54260 (tll_cells z64 z64 (Z_to_bv 64 0x21d0c) z64 (Z_to_bv 64 0x100) (Z_to_bv 64 8) z64)
    (* [comment removed for export] *)
    /\ rw_cells usegs m' 0x544d0 [C8 z64]
    /\ rw_cells usegs m' 0x544d8 [C8 pg; C8 (Z_to_bv 64 P0)]
    /\ rw_cells usegs m' 0x54550 [C8 hw]                 (* [comment removed for export] *)
    /\ rw_cells usegs m' 0x34188 [C8 (Z_to_bv 64 (envp_addr sp0 argv))]
    /\ rw_cells usegs m' 0x240f0 [C4 (Z_to_bv 64 0x20000)]
    /\ rw_cells usegs m' 0x544c8 [C8 (ssp_canary rnd)]   (* [comment removed for export] *)
    (* [comment removed for export] *)
    /\ rw_cells usegs m' 0x22d40 [C8 z64]
    /\ rw_cells usegs m' 0x22d48 [C8 (Z_to_bv 64 MAIN); C8 (Z_to_bv 64 0x183a8); C8 (Z_to_bv 64 0x18bcc); C8 z64]
    /\ rw_cells usegs m' 0x22d68 [C8 (Z_to_bv 64 0x18b00); C8 z64]
    /\ rw_cells usegs m' 0x22db8 [C8 (Z_to_bv 64 0x34188); C8 (Z_to_bv 64 0x544e0); C8 (Z_to_bv 64 0x544d8)]
    /\ rw_cells usegs m' 0x22dd0 [C8 (Z_to_bv 64 0x22d18); C8 (Z_to_bv 64 0x22d10)]
    /\ rw_cells usegs m' 0x22de0 [C8 (Z_to_bv 64 0x544c8)]
    /\ rw_cells usegs m' 0x22de8 [C8 (Z_to_bv 64 0x22d20); C8 (Z_to_bv 64 0x22d18)]
    (* [comment removed for export] *)
    /\ rw_cells usegs m' 0x22d10 [C8 (Z_to_bv 64 0x13a80)]
    /\ rw_cells usegs m' 0x22d18 [C8 (Z_to_bv 64 0x13af4)]
    (* [comment removed for export] *)
    /\ rw_cells usegs m' 0x23df8 [C8 (Z_to_bv 64 0x23df8)]
    /\ rw_cells usegs m' 0x24100 [C1 (Z_to_bv 8 1)]
    /\ rw_cells usegs m' 0x24148 [C1 (Z_to_bv 8 0)]
    (* [comment removed for export] *)
    /\ rw_cells usegs m' 0x544c0 [C4 z64]
    /\ rw_cells usegs m' 0x542a0 [C1 (Z_to_bv 8 0); CB 3 (repeat (Z_to_bv 8 0) 3); C4 z64; C4 z64; CB 4 (repeat (Z_to_bv 8 0) 4); C8 z64]
    (* [comment removed for export] *)
    /\ bytes_at usegs m' usp0 (build_stack_bytes ph sp0 argv envp uid hw rnd)
    /\ wr_at usegs m' usp0 (Z.of_nat (length (build_stack_bytes ph sp0 argv envp uid hw rnd)))
    /\ nth_error (argv_ptrs sp0 argv envp) 0 = Some (Z_to_bv 64 P0)
    (* [comment removed for export] *)
    /\ (forall a : word, (0x22000 <= bv_unsigned a < 0x56000)%Z -> outside crt_written (bv_unsigned a) -> m' a = None)
    /\ (0 < t < 4194304)%Z
    (* [comment removed for export] *)
    /\ (alloc_ceiling <= usp0 - 8388608)%Z.
End AtMain.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section Proof.
  Context {St : Type} (set_tls : Z -> St -> St).
  Variables (sp0 : word) (argv envp : list (list byte)) (uid hw : word) (rnd : EntryDraw).   (* [comment removed for export] *)
  Hypothesis VSP : valid_sp sp0.
  Hypothesis VARGV : valid_argv argv.
  Hypothesis VENVP : valid_envp envp.
  Hypothesis FITS : entry_stack_fits sp0 argv envp.
  (* [comment removed for export] *)
  Hypothesis CLO : (alloc_ceiling <= bv_unsigned sp0 - 8388608)%Z.
  Notation usp0 := (bv_unsigned sp0).
  Notation img := (build_stack_bytes ph sp0 argv envp uid hw rnd).
  Notation esi := (entry_stack_image ph sp0 argv envp uid hw rnd).   (* [comment removed for export] *)

  Lemma img_len_bound : (Z.of_nat (length img) <= 2500000)%Z.
  Proof using CEILV VARGV VENVP. pin_using (fun (CEILV VARGV VENVP : unit) => tt). ceil_facts.
    rewrite build_stack_bytes_length. destruct VARGV as (A1 & A2 & _). destruct VENVP as (E1 & E2 & _).
    pose proof (raw_len_nonneg ph sp0 argv envp uid hw rnd). unfold raw_len, struct_size, argc, envc in *. lia.
  Qed.

  Lemma sp_facts : (stack_max_size <= usp0)%Z /\ (usp0 + Z.of_nat (length esi) <= 2^64)%Z /\
                   (usp0 mod 16 = 0)%Z /\ (0x7fff80000000 <= usp0 <= 0x800000000000)%Z /\
                   (usp0 + Z.of_nat (length img) <= 0x800000000000)%Z.
  Proof using CEILV FITS VSP. pin_using (fun (CEILV FITS VSP : unit) => tt). ceil_facts.
    destruct (entry_bounds ph sp0 argv envp uid hw rnd VSP FITS) as [A B].
    pose proof (bsb_le_esi ph sp0 argv envp uid hw rnd) as C.
    destruct VSP as (L & H & M). unfold sp_window_lo, sp_window_hi, stack_max_size in *. lia.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition startup_post (s : St) : unit -> St -> machine_state -> Prop :=
    fun _ s' ms' => exists tp : word, s' = set_tls (bv_unsigned tp - 200)%Z s /\ at_main sp0 argv envp uid hw rnd tp ms'.

  Theorem startup_spec : forall s : St,
    implM usegs (startup_model set_tls 0x34190) s (startup_post s)
          (init_ms usegs Ubsan.M.init_pc ph sp0 rnd argv envp uid hw).
  Proof using CLO FITS VARGV VENVP VSP. pin_using (fun (CLO FITS VARGV VENVP VSP : unit) => tt). ceil_facts.
    intros s.
    destruct sp_facts as (SPLO & IMGHI & SP16 & SPW & IMGTOP).
    pose proof img_len_bound as IL.
    unfold init_ms, mkR_init. change (Z.of_N Ubsan.M.init_pc) with 0x13a38%Z.
    set (m := wrap_mem ph sp0 argv envp uid hw rnd).
    assert (NONE : forall a : word, (bv_unsigned a < 0x56000)%Z -> m a = None).
    { intros a Ha. apply init_none. unfold stack_max_size. lia. }
    pose proof (init_stk usegs ph sp0 argv envp uid hw rnd SPLO) as ST. fold m in ST.
    change stack_max_size with 8388608%Z in ST.
    pose proof (init_mem_inv' usegs ph sp0 argv envp uid hw rnd SPLO IMGHI ltac:(change (segs_top usegs) with 0x56000%Z; unfold stack_max_size; lia)) as MI.
    fold m in MI.
    pose proof (init_block_bytes usegs ph sp0 argv envp uid hw rnd SPLO IMGHI) as IMG. fold m in IMG.   (* [comment removed for export] *)
    pose proof (init_wr usegs ph sp0 argv envp uid hw rnd SPLO IMGHI) as WR. fold m in WR. rewrite <- (build_stack_bytes_length ph sp0 argv envp uid hw rnd) in WR.
    destruct (init_pieces usegs ph sp0 argv envp uid hw rnd SPLO IMGHI) as (ARGC & ARGV & ENVP & AUXW & _ & _ & RNDB). fold m in ARGC, ARGV, ENVP, AUXW, RNDB.
    (* [comment removed for export] *)
    destruct VARGV as (VA1 & VA2 & VA3 & VA4 & _).   (* [comment removed for export] *)
    assert (Harg0 : exists arg0, nth_error argv 0 = Some arg0).
    { destruct argv as [|a ?]; [cbn in VA1; lia | exists a; reflexivity]. }
    destruct Harg0 as [arg0 Harg0].
    destruct (init_argv_string usegs ph sp0 argv envp uid hw rnd SPLO IMGHI 0 arg0 Harg0) as (P0 & HP0 & P0LO & P0HI & STR).
    fold m in STR.
    pose proof (proj1 (Forall_forall _ _) VA4 arg0 (nth_error_In _ _ Harg0)) as NONUL0. cbn beta in NONUL0.
    assert (NONUL : Forall (fun b : byte => bv_unsigned b <> 0%Z) arg0).
    { apply Forall_forall. intros b Hb E0. apply NONUL0. replace (Z_to_bv 8 0) with b; [exact Hb|]. apply bv_eq. rewrite E0. reflexivity. }
    assert (EPS : Forall (fun w : word => bv_unsigned w <> 0%Z) (envp_ptrs sp0 argv envp)).
    { apply Forall_forall. intros w Hw. destruct (In_nth_error _ _ Hw) as [i Hi].
      pose proof (envp_ptr_bounds ph sp0 argv envp uid hw rnd IMGHI i w Hi).
      pose proof (raw_len_nonneg ph sp0 argv envp uid hw rnd). unfold env_base, str_base, struct_size in *. lia. }
    (* [comment removed for export] *)
    assert (RND : bytes_at usegs m (rnd_addr sp0 argv envp) (at_random_lo rnd)).   (* [comment removed for export] *)
    { rewrite at_random_split in RNDB. apply bytes_at_app in RNDB. exact (proj1 RNDB). }
    assert (RLO : (usp0 <= rnd_addr sp0 argv envp)%Z).
    { pose proof (raw_len_nonneg ph sp0 argv envp uid hw rnd). unfold rnd_addr, raw_len. lia. }
    (* [comment removed for export] *)
    rimg_chunk usegs NONE m 0x544d8%Z [C8 z64; C8 z64] G2.
    rimg_chunk usegs NONE m 0x54550%Z [C8 z64] HW.
    rimg_chunk usegs NONE m 0x34188%Z [C8 z64] ENVC.
    rimg_chunk usegs NONE m 0x544d0%Z [C8 z64] SI.
    rimg_chunk usegs NONE m 0x544e8%Z (libc_cells (Z_to_bv 8 0) (Z_to_bv 8 0) (Z_to_bv 8 0) (Z_to_bv 8 0) z64 z64 z64 z64 z64 z64 z64 (repeat (Z_to_bv 8 0) 48)) LC.
    rimg_chunk usegs NONE m 0x54260%Z (tll_cells z64 z64 z64 z64 z64 z64 z64) MT.
    rimg_chunk usegs NONE m 0x240f0%Z [C4 (Z_to_bv 64 0x20000)] DS.
    rimg_chunk usegs NONE m 0x544c8%Z [CB 8 (repeat (Z_to_bv 8 0) 8)] GU.
    rimg_chunk usegs NONE m 0x22db8%Z [C8 (Z_to_bv 64 0x34188); C8 (Z_to_bv 64 0x544e0); C8 (Z_to_bv 64 0x544d8)] G3.
    rimg_chunk usegs NONE m 0x22de0%Z [C8 (Z_to_bv 64 0x544c8)] GG.
    rimg_chunk usegs NONE m 0x22d40%Z [C8 z64] GD.
    rimg_chunk usegs NONE m 0x22d48%Z [C8 (Z_to_bv 64 MAIN); C8 (Z_to_bv 64 0x183a8); C8 (Z_to_bv 64 0x18bcc); C8 z64] GOT0.
    rimg_chunk usegs NONE m 0x22dd0%Z [C8 (Z_to_bv 64 0x22d18); C8 (Z_to_bv 64 0x22d10)] GIN.
    rimg_chunk usegs NONE m 0x22d10%Z [C8 (Z_to_bv 64 0x13a80)] INA.
    rimg_chunk usegs NONE m 0x24100%Z [C1 (Z_to_bv 8 0)] INI.
    rimg_chunk usegs NONE m 0x34190%Z [CB 4096 (repeat (Z_to_bv 8 0) 4096)] ZT.
    unfold libc_cells, tll_cells in LC, MT.
    assert (HC : argc argv = Z.of_nat (length argv)) by reflexivity.
    assert (HE : envc envp = Z.of_nat (length envp)) by reflexivity.
    assert (P0GE : (usp0 + 184 <= P0)%Z).   (* [comment removed for export] *)
    { pose proof (raw_len_nonneg ph sp0 argv envp uid hw rnd). unfold str_base, struct_size in P0LO. lia. }
    pose proof (munch_refl [(usp0 - 8388608, usp0); (0x24100, 0x24101); (0x34188, 0x34190); (0x54268, 0x54298);
                            (0x544c8, 0x544d0); (0x544d8, 0x54520); (0x54550, 0x54558); (0x34190, 0x35190)]%Z m) as MU.
    pose proof (wmono_refl usegs m) as WM.
    clearbody m.
    (* [comment removed for export] *)
    change (id (bytes_at usegs m usp0 img)) in IMG. change (id (wr_at usegs m usp0 (Z.of_nat (length img)))) in WR.
    unfold implM. iprefix.
    (* [comment removed for export] *)
    do 7 lstep.
    (* [comment removed for export] *)
    pose proof (bytes_at_read usegs m usp0 _ 0 4 ARGC ltac:(lia) ltac:(rewrite length_le8; lia)) as RD.
    change (firstn 4 (skipn (Z.to_nat 0) (le8 (Z_to_bv 64 (argc argv))))) with (le4 (Z_to_bv 64 (argc argv))) in RD.
    let a := cur_mem_addr in replace (wa (usp0 + 0)) with a in RD by (unfold wa; rewrite Z.add_0_r; try reflexivity; symmetry; apply Z_to_bv_bv_unsigned).
    lstep. clear RD.
    replace (Z_to_bv 64 (Z.land usp0 18446744073709551600)) with sp0.
    2:{ change 18446744073709551600%Z with (2^64 - 2^4)%Z. rewrite land_align_down by lia.
        change (2^4)%Z with 16%Z. rewrite SP16, Z.sub_0_r. symmetry. apply Z_to_bv_bv_unsigned. }
    replace (sx32 (Z_to_bv 64 (argc argv))) with (Z_to_bv 64 (argc argv)).
    2:{ unfold sx32. f_equal. unfold argc. rewrite unsigned_lit by lia. symmetry. apply swrap32_small. lia. }
    steps_to 0x18624%Z.
    (* [comment removed for export] *)
    carve_frame 32%nat ST.
    do 8 lstep.
    (* [comment removed for export] *)
    pose proof (rd_u64s_g usegs _ (usp0 + 8) _ 0 _ (Z_to_bv 64 (usp0 + 8)) ARGV ltac:(rewrite nth_error_app1 by (rewrite argv_ptrs_length; lia); exact HP0) ltac:(unfold wa; f_equal; lia)) as RD.
    lstep. clear RD ARGV.
    do 3 lstep.
    replace (Z_to_bv 64 (usp0 + 8 + Z.shiftl (argc argv) 3 + 8)) with (Z_to_bv 64 (envp_addr sp0 argv))
      by (unfold envp_addr; f_equal; rewrite Z.shiftl_mul_pow2 by lia; lia).
    (* [comment removed for export] *)
    assert (ENV : bytes_at usegs m1 (envp_addr sp0 argv)
                    (u64s (envp_ptrs sp0 argv envp) ++ le8 z64 ++ u64s (auxv20 uid hw (Z_to_bv 64 (rnd_addr sp0 argv envp))))).
    { rewrite u64s_app in ENVP. cbn [u64s] in ENVP. rewrite app_nil_r in ENVP.
      apply bytes_at_app in ENVP. destruct ENVP as [E1 E2]. rewrite u64s_length, envp_ptrs_length in E2.
      unfold envp_addr. apply bytes_at_app. split; [exact E1|]. apply bytes_at_app. split.
      - rewrite u64s_length, envp_ptrs_length. exact E2.
      - rewrite u64s_length, envp_ptrs_length, length_le8.
        replace (usp0 + 8 * (argc argv + 2) + Z.of_nat (8 * length envp) + Z.of_nat 8)%Z
          with (usp0 + 8 * (argc argv + envc envp + 3))%Z by lia.
        exact AUXW. }
    clear ENVP AUXW ARGC RNDB.
    lstep. name_sp sp0 (-32)%Z.
    icallM (init_libc_spec set_tls _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (usp0 - 8388608)%Z
              (envp_addr sp0 argv) (envp_ptrs sp0 argv envp) uid hw rnd (rnd_addr sp0 argv envp) P0 arg0 _ _ _ _ _ s).
    all: lazymatch goal with
         | |- forall _, _ => ipostT usegs; unname_sp
         | |- Forall _ _ => first [exact EPS | exact NONUL]
         | |- _ => unname_sp; fastfirst (first [ noevar_assumption | hyp_by_addr | reflexivity | unfold envp_addr; lia ])
         end.
    (* [comment removed for export] *)
    repeat match goal with
           | H : bytes_at _ _ _ (u64s _ ++ _) |- _ => clear H
           | H : bytes_at _ _ P0 _ |- _ => clear H
           | H : bytes_at _ _ (rnd_addr _ _ _) _ |- _ => clear H
           end.
    repeat match goal with H1 : rw_cells _ ?mm ?A ?cs, H2 : rw_cells _ ?mm ?A ?cs |- _ => clear H2 end.
    clear EPS NONUL NONUL0 VA2 VA3 VA4 RLO P0HI.
    unfold tls_cells, libc_cells, tll_cells in *.
    match goal with H : stk _ _ _ _ |- _ => rename H into ST end.
    rewrite envp_ptrs_length in *.
    replace (envp_addr sp0 argv + 8 * (Z.of_nat (length envp) + 1))%Z with (auxv_addr sp0 argv envp) in *
      by (unfold auxv_addr, envp_addr, envc; lia).
    (* [comment removed for export] *)
    steps_to 0x18680%Z. release_frame FR ST (bv_unsigned sp0). astep.
    (* [comment removed for export] *)
    carve_frame 48%nat ST. steps_to 0x185d8%Z.
    (* [comment removed for export] *)
    carve_frame 32%nat ST. steps_to 0x13a80%Z.
    (* [comment removed for export] *)
    carve_frame 16%nat ST. steps_to 0x13a9c%Z. try change (zxb (Z_to_bv 8 0)) with (Z_to_bv 64 0).
    steps_to 0x13af0%Z. release_frame FR1 ST (usp0 + -80)%Z. astep.
    steps_to 0x18620%Z. release_frame FR0 ST (usp0 + -48)%Z. astep.
    (* [comment removed for export] *)
    steps_to 0x13b84%Z.
    replace (Z_to_bv 64 (usp0 + 8 + Z.shiftl (argc argv) 3 + 8)) with (Z_to_bv 64 (envp_addr sp0 argv))
      by (unfold envp_addr; f_equal; rewrite Z.shiftl_mul_pow2 by lia; lia).
    (* [comment removed for export] *)
    unfold id in IMG, WR.
    lazymatch type of MU with munch ?W m ?mf =>
      apply (bytes_at_transport usegs W m mf usp0 img) in IMG; [| exact MU | cbn [disjoint_from]; lia];
      apply (wr_at_transport usegs m mf) in WR; [| exact WM] end.
    (* [comment removed for export] *)
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mf _) =>
      assert (NONE' : forall a : word, (0x22000 <= bv_unsigned a < 0x56000)%Z ->
                outside [(0x24100, 0x24101); (0x34188, 0x34190); (0x54268, 0x54298);
                         (0x544c8, 0x544d0); (0x544d8, 0x54520); (0x54550, 0x54558); (0x34190, 0x35190)]%Z (bv_unsigned a) -> mf a = None)
        by (intros a Ha Ho; rewrite (MU a); [apply NONE; lia | cbn [outside] in Ho |- *; lia]);
      rimg_chunk usegs NONE' mf 0x22d68%Z [C8 (Z_to_bv 64 0x18b00); C8 z64] GCX;
      rimg_chunk usegs NONE' mf 0x22de8%Z [C8 (Z_to_bv 64 0x22d20); C8 (Z_to_bv 64 0x22d18)] GFI;
      rimg_chunk usegs NONE' mf 0x22d18%Z [C8 (Z_to_bv 64 0x13af4)] FIA;
      rimg_chunk usegs NONE' mf 0x23df8%Z [C8 (Z_to_bv 64 0x23df8)] DSO;
      rimg_chunk usegs NONE' mf 0x24148%Z [C1 (Z_to_bv 8 0)] FIN;
      rimg_chunk usegs NONE' mf 0x544c0%Z [C4 z64] EXL;
      rimg_chunk usegs NONE' mf 0x542a0%Z [C1 (Z_to_bv 8 0); CB 3 (repeat (Z_to_bv 8 0) 3); C4 z64; C4 z64; CB 4 (repeat (Z_to_bv 8 0) 4); C8 z64] ATX
    end.
    (* [comment removed for export] *)
    lazymatch goal with TB : tls_block_ok_u ?tb, TLS : rw_cells _ _ ?tb _ |- _ =>
      rename TLS into TLS0;
      remember (Z_to_bv 64 (tb + 200)) as tpw eqn:Etpw;
      assert (Eu : bv_unsigned tpw = (tb + 200)%Z) by (subst tpw; apply unsigned_lit; lia);
      apply (proj1 (rw_cells_app _ _ _ [_;_;_;_;_] _)) in TLS0; destruct TLS0 as [TDH TLS0];
      apply (proj1 (rw_cells_app _ _ _ [_] _)) in TLS0; destruct TLS0 as [ERR TLS0];
      apply (proj1 (rw_cells_app _ _ _ [_;_;_;_;_;_] _)) in TLS0; destruct TLS0 as [TDM TLS0];
      apply (proj1 (rw_cells_app _ _ _ [_] _)) in TLS0; destruct TLS0 as [CAN TLS0];
      apply (proj1 (rw_cells_app _ _ _ [_] _)) in TLS0; destruct TLS0 as [DTVP TLS0];
      apply (proj1 (rw_cells_app _ _ _ [_] _)) in TLS0; destruct TLS0 as [TLSA DTV];
      cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in ERR, TDM, CAN, DTVP, TLSA, DTV;
      match type of TDH with rw_cells _ _ ?A _ => replace A with (bv_unsigned tpw + -200)%Z in TDH by lia end;
      match type of ERR with rw_cells _ _ ?A _ => replace A with (bv_unsigned tpw + -164)%Z in ERR by lia end;
      match type of TDM with rw_cells _ _ ?A _ => replace A with (bv_unsigned tpw + -160)%Z in TDM by lia end;
      match type of CAN with rw_cells _ _ ?A _ => replace A with (bv_unsigned tpw + -16)%Z in CAN by lia end;
      match type of DTVP with rw_cells _ _ ?A _ => replace A with (bv_unsigned tpw + -8)%Z in DTVP by lia end;
      match type of TLSA with rw_cells _ _ ?A _ => replace A with (bv_unsigned tpw) in TLSA by lia end;
      match type of DTV with rw_cells _ _ ?A _ => replace A with (bv_unsigned tpw + 256)%Z in DTV by lia end;
      replace (tb + 120)%Z with (bv_unsigned tpw - 80)%Z in TDM by lia;
      replace (tb + 464)%Z with (bv_unsigned tpw + 264)%Z in DTVP by lia;
      replace (tb + 2248)%Z with (bv_unsigned tpw + 2048)%Z in DTV by lia;
      assert (Etb : tb = (bv_unsigned tpw - 200)%Z) by lia;
      clear Etpw Eu; rewrite Etb in *; clear Etb
    end.
    apply evt_done. unfold startup_post, at_main. exists tpw. split; [assumption|].
    (* [comment removed for export] *)
    let z := fresh "sblz" in pose (z := repeat (Z_to_bv 8 0) 3616); change (repeat (Z_to_bv 8 0) 3616) with z.
    let x := fresh "sbl" in pose (x := 3616%nat); change 3616%nat with x.
    let z := fresh "sblz" in pose (z := repeat (Z_to_bv 8 0) 256); change (repeat (Z_to_bv 8 0) 256) with z.
    repeat (lazymatch goal with |- ex _ => eexists end).
    split; [cbv delta [mkR]; reflexivity|].
    repeat match goal with |- _ /\ _ => split end.
    all: lazymatch goal with
         | |- nth_error _ _ = _ => exact HP0
         | |- wr_at _ _ _ _ => exact WR
         | |- forall _, _ => intros a Ha Hout; rewrite (MU a); [apply NONE; lia|];
                              unfold crt_written in Hout; cbn [outside] in Hout |- *; lia
         | |- _ => fastfirst (first [ noevar_assumption |hyp_by_addr | assumption | lia])
         end.
  Qed.
End Proof.

End WithCeil.
End TwB.
End Startup.

(* [comment removed for export] *)
Module F_target_run.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import Tac Arr Bytes ZBridge ITree Nodes Decode SysStep RegsEquiv MonadX ImgSrc3.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Prelim Monad Fmt StdioCore Stdio PcapPrelim PcapTypes PcapPure Pcap. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Adapter__Spec. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Prog. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Monad OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Fmt OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.StdioCore OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Stdio OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapPrelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapTypes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapPure OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Pcap OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Adapter__Spec.Driver OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Adapter__Spec.Adapter OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prog OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Adapter__Spec.StartupModel.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require FileCells__Musl. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require AmoStep__Musl. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require InitMem. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require Printf_kit__Musl. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.FileCells__Musl.StrFun OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.STRW_tac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.InitMem OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_kit__Musl.StartupKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.FileCells__Musl.FileCells OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.CellsExtra.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_memcpy. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require Exit__S3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_atexit GI. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require GIFacts__S3. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_memcpy OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Startup_B__S3.Startup_B OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Startup_B__S3.Startup OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Exit__S3.Exit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_atexit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.GI OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.GIFacts__S3.GIFacts OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.GIFacts__S3.Ifaces.
From OSSVerify.libpcap.fuzz_pcap.images Require Import Plain.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import LiaPin.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require SecDiet.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac lia ::= pinned_lia.
Import ListNotations.
Open Scope bv_scope.
Import ITree.Exc.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
Section WithCeil.
Context {CEILV : CEIL}.
Definition reg_post (sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (lo : Z) (cb : bool) (pad j1 j2 : list byte) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m',
      ms' = MS (mkR ra' sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
               F (Z_to_bv 64 0x13e28) fc None m' (seg_rom ssegs)
      /\ munch [(0x33990%Z, 0x33995%Z); (0x53ae0%Z, 0x53d00%Z); ((bv_unsigned sp - 48)%Z, bv_unsigned sp)] m m'
      /\ wmono ssegs m m' /\ mem_inv ssegs m' /\ stk ssegs m' lo (bv_unsigned sp)
      /\ rw_cells ssegs m' 0x33990 [C1 (bool8 true); CB 3 pad; C1 (bool8 cb)]
      /\ rw_cells ssegs m' 0x53ae0 (atexit_cells (Z_to_bv 8 0) (repeat (Z_to_bv 8 0) 3) (atx_slot true) (repeat (Z_to_bv 8 0) 4) (atx_head true))
      /\ rw_cells ssegs m' 0x53af8 (builtin_cells (Z_to_bv 64 0x18408) j1 (Z_to_bv 64 0x13f38) j2).

Lemma reg_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (lo : Z) (reg cb : bool) (pad : list byte) (f0 g0 : word) (j1 j2 : list byte)
    (cdt thr sec : byte) (tm1 auxv th ts ta tc ps : word) (loc : list byte),
  stk ssegs m lo (bv_unsigned sp) ->
  rw_cells ssegs m 0x33990 [C1 (bool8 reg); CB 3 pad; C1 (bool8 cb)] ->
  rw_cells ssegs m 0x53ae0 (atexit_cells (Z_to_bv 8 0) (repeat (Z_to_bv 8 0) 3) (atx_slot reg) (repeat (Z_to_bv 8 0) 4) (atx_head reg)) ->
  rw_cells ssegs m 0x53af8 (builtin_cells f0 j1 g0 j2) ->
  (reg = true -> f0 = Z_to_bv 64 0x18408 /\ g0 = Z_to_bv 64 0x13f38) ->
  rw_cells ssegs m 0x53d28 (libc_cells cdt thr sec (Z_to_bv 8 0) tm1 auxv th ts ta tc ps loc) ->      (* [comment removed for export] *)
  rw_cells ssegs m 0x225c0 [C8 (Z_to_bv 64 0)] ->                                                   (* [comment removed for export] *)
  mem_inv ssegs m -> (lo <= bv_unsigned sp - 48)%Z -> (alloc_ceiling <= lo)%Z ->
  a1 = Z_to_bv 64 (bv_unsigned (bool8 reg)) -> s4 = Z_to_bv 64 0x33990 ->
  evt ssegs (reg_post sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo cb pad j1 j2 m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x13e24) fc None m (seg_rom ssegs)).
Proof using CEILV. pin_using (fun (CEILV : unit) => tt). ceil_facts.
  intros until loc. intros ST FL ATX BLT REG LC GLI MI LO LOLO -> ->.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  pose proof (munch_refl [(0x33990%Z, 0x33995%Z); (0x53ae0%Z, 0x53d00%Z); ((bv_unsigned sp - 48)%Z, bv_unsigned sp)] m) as MU.
  pose proof (wmono_refl ssegs m) as WM.
  destruct reg; cbn [bool8 atx_slot atx_head] in *.
  - (* [comment removed for export] *)
    destruct (REG eq_refl) as [-> ->]. clear REG.
    lstep. if_false.
    unfold reg_post, atexit_cells, builtin_cells in *. cbn [bool8 atx_slot atx_head]. finish.
  - (* [comment removed for export] *)
    clear REG.
    lstep. if_true. lstep. lstep. lstep. lstep. lstep.
    unfold atexit_cells, builtin_cells in ATX, BLT.
    call atexit_spec; [exact ST | exact LC | exact ATX | exact BLT | exact MI | lia | exact LOLO |].
    lstep. if_true. lstep. lstep. lstep. if_true.
    unfold reg_post, atexit_cells, builtin_cells in *. cbn [bool8 atx_slot atx_head]. finish.
Qed.

Lemma free_null_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte),
  a0 = Z_to_bv 64 0 ->
  evt ssegs (fun ms' => ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                F (ret_pc ra) fc None m (seg_rom ssegs))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x1878c) fc None m (seg_rom ssegs)).
Proof using CEILV. pin_using (fun (CEILV : unit) => tt). ceil_facts.
  intros until m. intros ->.
  step. step. if_true. step. apply evt_done. reflexivity.
Qed.

(* [comment removed for export] *)
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
Proof using CEILV. pin_using (fun (CEILV : unit) => tt). ceil_facts.
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
Proof using CEILV. intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m Dst Src n src junk. ltac2:(SecDiet.SzSec.closeP 'memcpy_specZ__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.

(* [comment removed for export] *)
Lemma ranges_apart : forall S D n, (0 < n)%Z ->
  (forall a, S <= a < S + n -> ~ (D <= a < D + n))%Z -> (S + n <= D \/ D + n <= S)%Z.
Proof using CEILV. pin_using (fun (CEILV : unit) => tt). ceil_facts.
  intros S D n Hn H.
  destruct (Z_lt_le_dec S (D + n)); [|right; lia]. destruct (Z_lt_le_dec D (S + n)); [|left; lia].
  exfalso. destruct (Z_le_gt_dec D S).
  - apply (H S); lia.
  - apply (H D); lia.
Qed.

Lemma land3_range : forall c, (0 <= Z.land c 3 <= 3)%Z.
Proof using CEILV. pin_using (fun (CEILV : unit) => tt). ceil_facts. intros c. change 3%Z with (2^2 - 1)%Z. rewrite zb_land_mask by lia. pose proof (Z.mod_pos_bound c (2^2) ltac:(lia)). lia. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma target_alloc_init_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte),
  evt ssegs (fun ms' => ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                F (ret_pc ra) fc None m (seg_rom ssegs))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x13dd4) fc None m (seg_rom ssegs)).
Proof using CEILV. pin_using (fun (CEILV : unit) => tt). ceil_facts. intros. step. apply evt_done. reflexivity. Qed.

Lemma target_alloc_count_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte),
  evt ssegs (fun ms' => ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                F (ret_pc ra) fc None m (seg_rom ssegs))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x13dd8) fc None m (seg_rom ssegs)).
Proof using CEILV. pin_using (fun (CEILV : unit) => tt). ceil_facts. intros. step. step. apply evt_done. reflexivity. Qed.

Lemma eqz_cond_false : forall z, (0 < z < 2^64)%Z -> bv_eqb (Z_to_bv 64 z) z64 = false.
Proof using CEILV. pin_using (fun (CEILV : unit) => tt). ceil_facts. intros z Hz. unfold bv_eqb. rewrite !unsigned_lit by lia. apply Z.eqb_neq. lia. Qed.

Lemma nez_cond : forall z, (0 < z < 2^64)%Z -> negb (bv_eqb (Z_to_bv 64 z) z64) = true.
Proof using CEILV. pin_using (fun (CEILV : unit) => tt). ceil_facts. intros z Hz. unfold bv_eqb. rewrite !unsigned_lit by lia. apply Bool.negb_true_iff. apply Z.eqb_neq. lia. Qed.

Section TargetRun.
  Context {H hptr : Type} (HO : HeapOps H hptr) (K : modkit H hptr) (sites_of : Z -> stack_site -> Z) (sites : stack_site -> Z).
  Hypothesis HFL : heap_frame_law K.
  Hypothesis SFL : stdio_fp_law K.
  Hypothesis HCB : heap_cb_law K.
  Hypothesis SCB : stdio_cb_law K.
  Hypothesis MALLOC : malloc_stmt HO K.
  Hypothesis FREE : free_stmt HO K.
  Hypothesis FUZZ : fuzz_one_stmt HO K sites_of sites.
  Hypothesis VPR : vprintf_d_stmt K.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Ltac aln_fin := fastfirst (first [ noevar_assumption |lia | Z.div_mod_to_equations; lia]).
  Ltac aln :=
    fastfirst (first [ noevar_assumption | assumption
          | (match goal with H : bv_unsigned ?x = _ |- (bv_unsigned ?x mod 16 = 0)%Z => rewrite H end; aln_fin)
          | (rewrite unsigned_lit by lia; aln_fin)
          | aln_fin ]).

  Definition emit_printf_spec__stmt : Prop := forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (R : rctx) (s : PState H hptr) (CL : list cblock) (lo v : Z),
    GI K R s CL m -> stk ssegs m lo (bv_unsigned sp) -> (rc_lo R <= lo)%Z -> (lo + 80 + STDIO_STACK <= bv_unsigned sp)%Z ->
    (bv_unsigned sp <= rc_spmain R)%Z -> mem_inv ssegs m -> tp = rc_tp R ->
    a1 = Z_to_bv 64 v -> (- 2^31 <= v < 2^31)%Z -> (bv_unsigned sp mod 16 = 0)%Z ->
    implM ssegs (@emit_d (PState H hptr) hptr ps_libc set_libc v) s
      (out_post K ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc R CL lo m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x13f68) fc None m (seg_rom ssegs)).
  Section Sz10.
  Variables ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m R s CL lo v : ltac2:(SecDiet.SzSec.tyM 'emit_printf_spec__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra).
  Lemma emit_printf_spec__body : ltac2:(SecDiet.SzSec.bodyP 'emit_printf_spec__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof using HFL SFL VPR. pin_using (fun (HFL SFL VPR : unit) => tt). ceil_facts.
    intros G ST LOLO BUD SPM MI Etp Ea1 Hv ALN.
    unfold STDIO_STACK in BUD.
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
    pose proof (GI_spw K _ _ _ _ G) as SPW. pose proof (GI_ceil_lo K _ _ _ _ G) as CLO__. unfold rc_lo in CLO__. unfold rc_lo in LOLO. unfold rc_spmain in SPM.
    pose proof (munch_refl [(bv_unsigned sp - 80, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl ssegs m) as WM.
    subst a1 tp.
    unfold implM. iprefix.
    carve_frame 80%nat ST.
    steps_to 0x20550%Z.
    (* [comment removed for export] *)
    assert (G1 : GI K R s CL m0).
    { eapply (GI_client_frame K HFL SFL); [exact G | exact MU | exact WM |].
      constructor; [left; cbn [fst snd]; unfold rc_lo, rc_spmain; lia | constructor]. }
    assert (AG0 : agrees_on (client_keeps CL (bv_unsigned sp)) m m0).
    { eapply (keeps_of_munch K); [exact G | exact MU | exact WM | | lia]. constructor; [left; cbn [fst snd]; lia| constructor]. }
    clear MU WM.
    (* [comment removed for export] *)
    apply (proj1 (rw_cells_app ssegs m0 _ [_; _; _] _)) in FR as [FR1 FR2]. cbn [cells_size csize Nat.add] in FR2.
    apply (rw_cells_merge ssegs m0 _ [C8 (Z_to_bv 64 v)] [C8 a2; C8 a3; C8 a4; C8 a5; C8 a6; C8 a7] []) in FR2.
    cbn [cells_size csize cells_bytes cbytes Nat.add app] in FR2.
    replace (bv_unsigned sp + -80 + Z.of_nat 24)%Z with (bv_unsigned sp + -56)%Z in FR2 by lia.
    name_sp sp (-80)%Z.
    apply evt_done. unfold emit_d. eapply implM_post_evt.
    { eapply VPR.
      { split; [exact G1|]. split; [rewrite Hsp; exact ST|]. split; [unfold rc_lo; lia|]. split; [unfold STDIO_STACK; lia|].
        split; [unfold rc_spmain; lia|]. split; [exact MI|]. split; [reflexivity| aln]. }
      all: fastfirst (first [ noevar_assumption |reflexivity | exact Hv | exact FR2 | unfold rc_spmain; lia]). }
    intros [] s' ms' PO. unfold out_post in PO. destruct_exs PO. destruct PO as (-> & MI' & ST' & AG & G'). clear MI. rename MI' into MI.
    replace (ret_pc (Z_to_bv 64 81828)) with (Z_to_bv 64 81828) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
    apply (keeps_rw_cells_stack CL _ _ _ _ _ AG) in FR1; [|lia].
    apply (keeps_rw_cells_stack CL _ _ _ _ _ AG) in FR2; [|lia].
    unname_sp.
    lstep. lstep. lstep.
    release_frame FR1 ST' (bv_unsigned sp + -56)%Z. release_frame FR2 ST' (bv_unsigned sp).
    finish.
    eapply keeps_trans; [exact AG0 | exact AG | lia | intros a Ha; exact Ha].
  Qed.
  End Sz10.
  Lemma emit_printf_spec : ltac:(let t := eval cbv delta [emit_printf_spec__stmt] in emit_printf_spec__stmt in exact t).
  Proof using HFL SFL VPR. intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m R s CL lo v. ltac2:(SecDiet.SzSec.closeP 'emit_printf_spec__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.

  (* [comment removed for export] *)
  Definition loop_post (spi gp tp s0 s1 s2 s4 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (R : rctx) (CL : list cblock) (lo : Z) (bad : bool) (m : mem) : bool -> PState H hptr -> machine_state -> Prop :=
    fun bad' s' ms' => exists ra' t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 s3' m',
      ms' = MS (mkR ra' spi gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3' s4 (Z_to_bv 64 0) (Z_to_bv 64 (Z.b2z bad)) s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (Z_to_bv 64 0x13ed0) fc None m' (seg_rom ssegs)
      /\ bad' = bad /\ mem_inv ssegs m' /\ stk ssegs m' lo (bv_unsigned spi)
      /\ agrees_on (client_keeps CL (bv_unsigned spi)) m m' /\ GI K R s' CL m'.

  (* [comment removed for export] *)
  Ltac tr_hide H := lazymatch type of H with ?T => let X := fresh "AUX" in pose (X := T); change T with X in H end.
  Ltac tr_unhide H := lazymatch type of H with ?X => subst X end.

  Lemma set_cb_back : forall (R : rctx) b, rc_cb R = false -> set_cb (set_cb R b) false = R.
  Proof using Type. pin_using tt. intros [] b Hb. cbn in Hb. subst. reflexivity. Qed.

  Lemma loop_spec : forall (n : nat) (ra spi gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (R : rctx) (s : PState H hptr) (CL : list cblock) (lo D : Z) (data : list byte) (bad : bool),
    (1 <= n <= 4)%nat ->
    GI K R s CL m -> rc_cb R = false ->
    stk ssegs m lo (bv_unsigned spi) -> (rc_lo R <= lo)%Z -> (lo + FUZZ_STACK <= bv_unsigned spi)%Z ->
    (lo + 80 + STDIO_STACK <= bv_unsigned spi)%Z -> (bv_unsigned spi <= rc_spmain R)%Z -> mem_inv ssegs m -> tp = rc_tp R ->
    s0 = Z_to_bv 64 (Z.of_nat (length data)) -> s1 = Z_to_bv 64 D -> s5 = Z_to_bv 64 (Z.of_nat n) -> s4 = Z_to_bv 64 0x33990 ->
    s6 = Z_to_bv 64 (Z.b2z bad) -> s7 = Z_to_bv 64 (-2) ->
    bytes_at ssegs m D data ->
    (forall a, D <= a < D + Z.of_nat (length data) -> in_block CL a)%Z ->
    (Z.of_nat (length data) < 2^26)%Z ->
    (bv_unsigned spi mod 16 = 0)%Z -> sites = sites_of (bv_unsigned spi) ->
    implM ssegs (call_loop (@emit_d (PState H hptr) hptr ps_libc set_libc) (harness_call HO fo_nop sites) n (map bv_unsigned data) bad) s
      (loop_post spi gp tp s0 s1 s2 s4 s7 s8 s9 s10 s11 F fc R CL lo bad m)
      (MS (mkR ra spi gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x13e98) fc None m (seg_rom ssegs)).
  Proof using FUZZ HFL SFL HCB SCB VPR. pin_using (fun (FUZZ HFL SFL HCB SCB VPR : unit) => tt). ceil_facts.
    induction n as [|n IH]; [intros; lia|].
    intros until bad. intros Hn G Hcb ST LOLO BUDF BUDS SPM MI Etp Es0 Es1 Es5 Es4 Es6 Es7 SRC HK HD ALN SITES.
    unfold FUZZ_STACK in BUDF. unfold STDIO_STACK in BUDS.
    pose proof (bv_unsigned_in_range 64 spi) as RSP. unfold bv_modulus in RSP. cbn in RSP.
    pose proof (GI_spw K _ _ _ _ G) as SPW. pose proof (GI_ceil_lo K _ _ _ _ G) as CLO__. unfold rc_lo in CLO__. unfold rc_lo in LOLO. unfold rc_spmain in SPM.
    pose proof (bytes_at_bound _ _ _ _ SRC) as DB.
    subst s0 s1 s5 s4 s6 s7 tp.
    cbn [call_loop].
    (* [comment removed for export] *)
    destruct (GI_atx K _ _ _ _ G) as (reg & pad & f0 & g0 & j1 & j2 & FL & ATXc & BLT & REG). rewrite Hcb in FL. cbn [bool8] in FL.
    pose proof (munch_refl [(0x33990, 0x33995); (0x53ae0, 0x53d00)]%Z m) as MU. pose proof (wmono_refl ssegs m) as WM.
    unfold atexit_cells, builtin_cells in ATXc, BLT.
    tr_hide SRC.
    unfold implM. iprefix. lstep. lstep.
    tr_unhide SRC.
    lazymatch type of MU with munch _ _ ?mb =>
      assert (G1 : GI K (set_cb R true) s CL mb);
      [ eapply (GI_atx_frame K HFL SFL HCB SCB); [exact G | exact MU | exact WM | constructor |];
        exists reg, pad, f0, g0, j1, j2; split; [exact FL|]; split; [exact ATXc|]; split; [exact BLT| exact REG]
      | assert (AG0 : agrees_on (client_keeps CL (bv_unsigned spi)) m mb);
        [ eapply (keeps_of_munch K); [exact G | exact MU | exact WM | | lia];
          constructor; [right; cbn [fst snd]; lia | constructor; [right; cbn [fst snd]; lia | constructor]] | ] ]
    end.
    apply (agrees_bytes_at _ _ _ _ _ AG0) in SRC; [| intros a Ha; right; apply HK; exact Ha].
    clear MU WM G FL ATXc BLT REG.
    lstep. lstep. lstep.
    apply evt_done. eapply (implM_bind ssegs).
    { eapply (FUZZ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (set_cb R true));
        [ | exact SITES | reflexivity | reflexivity | exact SRC | exact HK | exact HD].
      unfold std_pre. change (rc_lo (set_cb R true)) with (rc_lo R). change (rc_spmain (set_cb R true)) with (rc_spmain R). change (rc_tp (set_cb R true)) with (rc_tp R).
      split; [exact G1|]. split; [exact ST|]. split; [unfold rc_lo; lia|]. split; [unfold FUZZ_STACK; lia|].
      split; [unfold rc_spmain; lia|]. split; [exact MI|]. split; [reflexivity| aln]. }
    intros rc' s' ms' PO. unfold fuzz_post in PO. destruct_exs PO. destruct PO as (-> & MI1 & ST1 & AG1 & G1' & ->).
    clear MI G1. cbn [fst snd].
    replace (ret_pc (Z_to_bv 64 0x13eac)) with (Z_to_bv 64 0x13eac) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
    (* [comment removed for export] *)
    clear reg pad f0 g0 j1 j2.
    destruct (GI_atx K _ _ _ _ G1') as (reg & pad & f0 & g0 & j1 & j2 & FL & ATXc & BLT & REG). cbn [set_cb rc_cb bool8] in FL.
    unfold atexit_cells, builtin_cells in ATXc, BLT.
    lazymatch goal with |- implM _ _ _ _ (MS _ _ _ _ _ ?m1 _) =>
      pose proof (munch_refl [(0x33990, 0x33995); (0x53ae0, 0x53d00)]%Z m1) as MU; pose proof (wmono_refl ssegs m1) as WM end.
    unfold implM. iprefix. lstep. lstep.
    lazymatch type of MU with munch _ ?ma ?mb =>
      assert (G2 : GI K R s' CL mb);
      [ rewrite <- (set_cb_back R true Hcb) at 1;
        eapply (GI_atx_frame K HFL SFL HCB SCB); [exact G1' | exact MU | exact WM | constructor |];
        exists reg, pad, f0, g0, j1, j2; split; [exact FL|]; split; [exact ATXc|]; split; [exact BLT| exact REG]
      | assert (AG2 : agrees_on (client_keeps CL (bv_unsigned spi)) ma mb);
        [ eapply (keeps_of_munch K); [exact G1' | exact MU | exact WM | | lia];
          constructor; [right; cbn [fst snd]; lia | constructor; [right; cbn [fst snd]; lia | constructor]] | ] ]
    end.
    clear MU WM G1' FL ATXc BLT REG.
    lstep. lstep.
    apply evt_done. eapply (implM_bind ssegs).
    { eapply (emit_printf_spec _ spi); [exact G2 | eassumption | unfold rc_lo; lia | unfold STDIO_STACK; lia | unfold rc_spmain; lia | eassumption | reflexivity | reflexivity | lia | aln]. }
    intros [] s'' ms'' PO. unfold out_post in PO. destruct_exs PO. destruct PO as (-> & MI3 & ST3 & AG3 & G3).
    cbn [fst snd].
    replace (ret_pc (Z_to_bv 64 0x13ebc)) with (Z_to_bv 64 0x13ebc) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
    rewrite bad_rc_step0.
    unfold implM. iprefix. lstep. lstep. if_true. lstep.
    replace (bv_swrap 32 (Z.of_nat (S n) + -1)) with (Z.of_nat n) by (rewrite bv_swrap_small; [lia| change (bv_half_modulus 32) with 2147483648%Z; lia]).
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mz _) =>
      assert (AGall : agrees_on (client_keeps CL (bv_unsigned spi)) m mz) end.
    { eapply keeps_trans; [exact AG0 | eapply keeps_trans; [exact AG1 | eapply keeps_trans; [exact AG2 | exact AG3 | lia | intros a Ha; exact Ha] | lia | intros a Ha; exact Ha] | lia | intros a Ha; exact Ha]. }
    destruct (Nat.eq_dec n 0) as [->|Hn0].
    - change (Z.of_nat 0) with 0%Z. astep. apply evt_done. apply (implM_ret ssegs). apply evt_done.
      unfold loop_post. repeat (lazymatch goal with |- ex _ => eexists end).
      split; [cbv delta [mkR]; reflexivity|]. split; [reflexivity|]. split; [exact MI3|]. split; [exact ST3|]. split; [exact AGall|exact G3].
    - lstep. if_true_by (nez_cond (Z.of_nat n) ltac:(lia)).
      apply evt_done. eapply (implM_mono ssegs).
      + eapply IH; [lia | exact G3 | exact Hcb | exact ST3 | unfold rc_lo; lia | unfold FUZZ_STACK; lia | unfold STDIO_STACK; lia
                   | unfold rc_spmain; lia | exact MI3 | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | | exact HK | exact HD | aln | exact SITES].
        eapply agrees_bytes_at; [exact AG3 | eapply agrees_bytes_at; [exact AG2 | eapply agrees_bytes_at; [exact AG1 | exact SRC |] |] |]; intros a Ha; right; apply HK; exact Ha.
      + cbv beta. intros b2 s2' ms2 PO. unfold loop_post in *. destruct_exs PO. destruct PO as (-> & -> & MI4 & ST4 & AG4 & G4).
        repeat (lazymatch goal with |- ex _ => eexists end).
        split; [reflexivity|]. split; [reflexivity|]. split; [exact MI4|]. split; [exact ST4|]. split; [|exact G4].
        eapply keeps_trans; [exact AGall | exact AG4 | lia | intros a Ha; exact Ha].
  Qed.

  (* [comment removed for export] *)
  Definition tr_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (R : rctx) (CL : list cblock) (lo SP : Z) (m : mem) : Z -> PState H hptr -> machine_state -> Prop :=
    fun r s' ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 r) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (ret_pc ra) fc None m' (seg_rom ssegs)
      /\ mem_inv ssegs m' /\ stk ssegs m' lo (bv_unsigned sp)
      /\ agrees_on (client_keeps CL SP) m m'
      /\ GI K R s' CL m' /\ (0 <= r <= 2)%Z.

  Lemma rest_spec : forall (k : nat) (o : option hptr)
      (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (cra cs0 cs1 cs2 cs3 cs4 cs5 cs6 cs7 : word) (junk : list byte)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (R : rctx) (s : PState H hptr) (CL : list cblock) (lo D : Z) (data : list byte),
    (1 <= k <= 4)%nat ->
    GI K R s (match o with Some q => (q, D, Z.of_nat (length data)) :: CL | None => CL end) m -> rc_cb R = false ->
    stk ssegs m lo (bv_unsigned sp + -80) -> (rc_lo R <= lo)%Z -> (lo + FUZZ_STACK + 80 + STDIO_STACK <= bv_unsigned sp)%Z ->
    (bv_unsigned sp <= rc_spmain R)%Z -> mem_inv ssegs m -> tp = rc_tp R ->
    s0 = Z_to_bv 64 (Z.of_nat (length data)) -> s1 = Z_to_bv 64 D -> s5 = Z_to_bv 64 (Z.of_nat k) -> s4 = Z_to_bv 64 0x33990 ->
    s2 = match o with Some _ => Z_to_bv 64 D | None => Z_to_bv 64 0 end ->
    bytes_at ssegs m D data ->
    (forall a, D <= a < D + Z.of_nat (length data) ->
               in_block (match o with Some q => (q, D, Z.of_nat (length data)) :: CL | None => CL end) a)%Z ->
    (Z.of_nat (length data) < 2^26)%Z ->
    rw_cells ssegs m (bv_unsigned sp + -80) [CB 8 junk; C8 cs7; C8 cs6; C8 cs5; C8 cs4; C8 cs3; C8 cs2; C8 cs1; C8 cs0; C8 cra] ->
    (bv_unsigned sp mod 16 = 0)%Z -> sites = sites_of (bv_unsigned sp + -80) ->
    implM ssegs (bad <- call_loop (@emit_d (PState H hptr) hptr ps_libc set_libc) (harness_call HO fo_nop sites) k (map bv_unsigned data) false ;;
                 match o with Some q => pfree HO q | None => mret tt end ;;;
                 mret (if bad then 78 else 0)%Z) s
      (tr_post cra sp gp tp cs0 cs1 cs2 cs3 cs4 cs5 cs6 cs7 s8 s9 s10 s11 F fc R CL lo (bv_unsigned sp + -80) m)
      (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -80)) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x13e90) fc None m (seg_rom ssegs)).
  Proof using FREE FUZZ HFL SFL HCB SCB VPR. pin_using (fun (FREE FUZZ HFL SFL HCB SCB VPR : unit) => tt). ceil_facts.
    intros until data. intros Hk G Hcb ST LOLO BUD SPM MI Etp Es0 Es1 Es5 Es4 Es2 SRC HK HD FR ALN SITES.
    unfold FUZZ_STACK, STDIO_STACK in BUD.
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
    pose proof (GI_spw K _ _ _ _ G) as SPW. pose proof (GI_ceil_lo K _ _ _ _ G) as CLO__. unfold rc_lo in CLO__. unfold rc_lo in LOLO. unfold rc_spmain in SPM.
    pose proof (bytes_at_bound _ _ _ _ SRC) as DB.
    subst s0 s1 s5 s4 tp.
    (* [comment removed for export] *)
    unfold implM. iprefix. lstep. lstep.
    name_sp sp (-80)%Z.
    apply evt_done.
    eapply (implM_bind ssegs).
    { eapply (loop_spec k) with (bad := false);
        [exact Hk | exact G | exact Hcb | rewrite Hsp; exact ST | unfold rc_lo; lia | unfold FUZZ_STACK; lia | unfold STDIO_STACK; lia
        | unfold rc_spmain; lia | exact MI | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | exact SRC | exact HK | exact HD | aln | rewrite Hsp; exact SITES]. }
    intros bad' s' ms' PO. unfold loop_post in PO. destruct_exs PO. destruct PO as (-> & -> & MI1 & ST1 & AG1 & G1). clear MI.
    apply (keeps_rw_cells_stack _ _ _ _ _ _ AG1) in FR; [|lia].
    unname_sp.
    unfold implM. iprefix. lstep. lstep.
    destruct o as [q|]; subst s2.
    - (* [comment removed for export] *)
      name_sp sp (-80)%Z.
      apply evt_done. eapply (implM_bind ssegs).
      { eapply FREE with (C1 := []); [| reflexivity].
        split; [exact G1|]. split; [rewrite Hsp; exact ST1|]. split; [unfold rc_lo; lia|]. split; [unfold FREE_STACK; lia|].
        split; [unfold rc_spmain; lia|]. split; [exact MI1|]. split; [reflexivity| aln]. }
      intros [] s'' ms'' PO. unfold free_post in PO. destruct_exs PO. destruct PO as (-> & MI2 & ST2 & AG2 & G2). clear MI1.
      cbn [app] in AG2, G2.
      replace (ret_pc (Z_to_bv 64 0x13ed8)) with (Z_to_bv 64 0x13ed8) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
      apply (keeps_rw_cells_stack _ _ _ _ _ _ AG2) in FR; [|lia].
      unname_sp.
      unfold implM. iprefix. do 3 lstep.
      do 11 lstep.
      apply evt_done. apply (implM_ret ssegs). apply evt_done.
      release_frame FR ST2 (bv_unsigned sp).
      unfold tr_post. repeat (lazymatch goal with |- ex _ => eexists end).
      split; [cbv delta [mkR]; reflexivity|]. split; [exact MI2|]. split; [exact ST2|]. split; [|split; [exact G2| lia]].
      eapply keeps_trans; [ | exact AG2 | lia | intros a Ha; exact Ha].
      eapply client_keeps_weaken; [exact AG1 | lia | intros a Ha; apply in_block_cons; exact Ha].
    - (* [comment removed for export] *)
      eapply evt_cut; [eapply free_null_spec; reflexivity|]. cbv beta. intros ms' ->.
      replace (ret_pc (Z_to_bv 64 0x13ed8)) with (Z_to_bv 64 0x13ed8) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
      do 3 lstep.
      do 11 lstep.
      apply evt_done. apply (implM_ret_bind ssegs). apply (implM_ret ssegs). apply evt_done.
      release_frame FR ST1 (bv_unsigned sp).
      unfold tr_post. repeat (lazymatch goal with |- ex _ => eexists end).
      split; [cbv delta [mkR]; reflexivity|]. split; [exact MI1|]. split; [exact ST1|]. split; [exact AG1|split; [exact G1| lia]].
  Qed.

  (* [comment removed for export] *)
  Definition tr_rest (k : nat) (pl : list Z) : M (PState H hptr) Z :=
    owned <- (if (length pl =? 0)%nat then mret (Some None)
              else q <- pmalloc HO (zlength pl) ;;
                   mret (match q with None => None | Some q' => Some (Some q') end)) ;;
    match owned with
    | None => mret 2%Z
    | Some o =>
        bad <- call_loop (@emit_d (PState H hptr) hptr ps_libc set_libc) (harness_call HO fo_nop sites) k pl false ;;
        (match o with Some q => pfree HO q | None => mret tt end) ;;;
        mret (if bad then 78 else 0)%Z
    end.

  (* [comment removed for export] *)
  Lemma path_empty : forall (k : nat)
      (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (cra cs0 cs1 cs2 cs3 cs4 cs5 cs6 cs7 : word) (junk : list byte)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (R : rctx) (s : PState H hptr) (CL : list cblock) (lo : Z),
    (1 <= k <= 4)%nat ->
    GI K R s CL m -> rc_cb R = false ->
    stk ssegs m lo (bv_unsigned sp + -80) -> (rc_lo R <= lo)%Z -> (lo + FUZZ_STACK + 80 + STDIO_STACK <= bv_unsigned sp)%Z ->
    (bv_unsigned sp <= rc_spmain R)%Z -> mem_inv ssegs m -> tp = rc_tp R ->
    s0 = Z_to_bv 64 0 -> s5 = Z_to_bv 64 (Z.of_nat k) -> s4 = Z_to_bv 64 0x33990 ->
    rw_cells ssegs m (bv_unsigned sp + -80) [CB 8 junk; C8 cs7; C8 cs6; C8 cs5; C8 cs4; C8 cs3; C8 cs2; C8 cs1; C8 cs0; C8 cra] ->
    (bv_unsigned sp mod 16 = 0)%Z -> sites = sites_of (bv_unsigned sp + -80) ->
    implM ssegs (tr_rest k []) s
      (tr_post cra sp gp tp cs0 cs1 cs2 cs3 cs4 cs5 cs6 cs7 s8 s9 s10 s11 F fc R CL lo (bv_unsigned sp + -80) m)
      (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -80)) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x13e88) fc None m (seg_rom ssegs)).
  Proof using FREE FUZZ HFL SFL HCB SCB VPR. pin_using (fun (FREE FUZZ HFL SFL HCB SCB VPR : unit) => tt). ceil_facts.
    intros until lo. intros Hk G Hcb ST LOLO BUD SPM MI Etp Es0 Es5 Es4 FR ALN SITES.
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
    pose proof (GI_spw K _ _ _ _ G) as SPW. pose proof (GI_ceil_lo K _ _ _ _ G) as CLO__. unfold rc_lo in CLO__. pose proof LOLO as LOLO'. unfold rc_lo in LOLO'. unfold FUZZ_STACK, STDIO_STACK in BUD.
    subst s0 s5 s4 tp.
    unfold tr_rest. cbn [length Nat.eqb]. apply (implM_ret_bind ssegs). cbv beta iota.
    unfold implM. iprefix. lstep. lstep.
    apply evt_done. eapply rest_spec with (o := None) (data := @nil byte); try reflexivity;
      [exact Hk | exact G | exact Hcb | exact ST | exact LOLO | unfold FUZZ_STACK, STDIO_STACK; lia | exact SPM | exact MI
      | apply bytes_at_nil; lia | intros a Ha; cbn in Ha; lia | exact FR | aln | exact SITES].
  Qed.

  (* [comment removed for export] *)
  Lemma path_alloc : forall (k : nat)
      (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (cra cs0 cs1 cs2 cs3 cs4 cs5 cs6 cs7 : word) (junk : list byte)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (R : rctx) (s : PState H hptr) (CL : list cblock) (lo P : Z) (src : list byte),
    (1 <= k <= 4)%nat ->
    GI K R s CL m -> rc_cb R = false ->
    stk ssegs m lo (bv_unsigned sp + -80) -> (rc_lo R <= lo)%Z -> (lo + FUZZ_STACK + 80 + STDIO_STACK <= bv_unsigned sp)%Z ->
    (bv_unsigned sp <= rc_spmain R)%Z -> mem_inv ssegs m -> tp = rc_tp R ->
    s0 = Z_to_bv 64 (Z.of_nat (length src)) -> s1 = Z_to_bv 64 P -> s5 = Z_to_bv 64 (Z.of_nat k) -> s4 = Z_to_bv 64 0x33990 ->
    (0 < length src)%nat -> (Z.of_nat (length src) < 2^26)%Z ->
    bytes_at ssegs m P src -> (forall a, P <= a < P + Z.of_nat (length src) -> in_block CL a)%Z ->
    rw_cells ssegs m (bv_unsigned sp + -80) [CB 8 junk; C8 cs7; C8 cs6; C8 cs5; C8 cs4; C8 cs3; C8 cs2; C8 cs1; C8 cs0; C8 cra] ->
    (bv_unsigned sp mod 16 = 0)%Z -> sites = sites_of (bv_unsigned sp + -80) ->
    implM ssegs (tr_rest k (map bv_unsigned src)) s
      (tr_post cra sp gp tp cs0 cs1 cs2 cs3 cs4 cs5 cs6 cs7 s8 s9 s10 s11 F fc R CL lo (bv_unsigned sp + -80) m)
      (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -80)) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x13e3c) fc None m (seg_rom ssegs)).
  Proof using FREE FUZZ HFL MALLOC SFL HCB SCB VPR. pin_using (fun (FREE FUZZ HFL MALLOC SFL HCB SCB VPR : unit) => tt). ceil_facts.
    intros until src. intros Hk G Hcb ST LOLO BUD SPM MI Etp Es0 Es1 Es5 Es4 HP0 HP32 SRC HINP FR ALN SITES.
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
    pose proof (GI_spw K _ _ _ _ G) as SPW. pose proof (GI_ceil_lo K _ _ _ _ G) as CLO__. unfold rc_lo in CLO__. pose proof LOLO as LOLO'. unfold rc_lo in LOLO'. unfold FUZZ_STACK, STDIO_STACK in BUD.
    pose proof SPM as SPM'. unfold rc_spmain in SPM'.
    destruct (client_range_bounds K _ _ _ _ P (Z.of_nat (length src)) G HINP ltac:(lia)) as (P0 & PHI & PI & PT).
    subst s0 s1 s5 s4 tp.
    set (n := Z.of_nat (length src)) in *.
    unfold tr_rest. rewrite length_map. replace (length src =? 0)%nat with false by (symmetry; apply Nat.eqb_neq; lia).
    unfold zlength. rewrite length_map. fold n.
    apply (implM_bind_assoc ssegs).
    unfold implM. iprefix. lstep. lstep.
    name_sp sp (-80)%Z.
    apply evt_done. eapply (implM_bind ssegs).
    { eapply MALLOC; [| reflexivity | lia].
      split; [exact G|]. split; [rewrite Hsp; exact ST|]. split; [exact LOLO|]. split; [unfold MALLOC_STACK; lia|].
      split; [unfold rc_spmain; lia|]. split; [exact MI|]. split; [reflexivity| aln]. }
    intros r s' ms' PO. unfold malloc_post in PO. destruct_exs PO. destruct PO as (-> & MI1 & ST1 & AG1 & CASES). clear MI.
    replace (ret_pc (Z_to_bv 64 0x13e44)) with (Z_to_bv 64 0x13e44) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
    apply (keeps_rw_cells_stack _ _ _ _ _ _ AG1) in FR; [|lia].
    apply (keeps_bytes_at_block _ _ _ _ _ _ AG1) in SRC; [|exact HINP].
    unname_sp.
    destruct r as [q|].
    - destruct CASES as (A' & junk' & -> & G1 & BLK & BOK & HADDR).
      pose proof BOK as BOK'. unfold block_ok in BOK'. cbn [cb_addr cb_size fst snd] in BOK'. destruct BOK' as (B1 & B2 & B3 & B4 & B5 & B6).
      assert (SEP : (P + n <= A' \/ A' + n <= P)%Z).
      { apply ranges_apart; [lia|]. intros a Ha Hin.
        destruct (GI_blocks K _ _ _ _ G1) as [_ [AP _]].
        pose proof (HINP a Ha) as Hb. unfold in_block in Hb. apply Exists_exists in Hb as (b & Hb & Hr).
        pose proof (proj1 (Forall_forall _ _) AP _ Hb) as X. unfold apart in X. cbn [cb_addr cb_size fst snd] in X. lia. }
      apply (implM_ret_bind ssegs). cbv beta iota.
      unfold implM. iprefix. lstep. if_false_by (eqz_cond_false A' ltac:(lia)).
      lstep. lstep. lstep. lstep.
      match goal with |- evt _ _ (MS _ _ _ _ _ ?m1 _) =>
        pose proof (munch_refl [(A', A' + n)]%Z m1) as MU2; pose proof (wmono_refl ssegs m1) as WM2 end.
      call (memcpy_specZ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ A' P n src junk');
        [reflexivity | reflexivity | reflexivity | exact SRC | subst n; lia | lia | exact BLK | exact SEP | lia | lia | exact MI1 |].
      rename PC into DST. clear POST.
      lazymatch type of MU2 with munch _ ?ma ?mb =>
        assert (G2 : GI K R s' ((q, A', n) :: CL) mb);
        [ eapply (GI_client_frame K HFL SFL); [exact G1 | exact MU2 | exact WM2 |];
          constructor; [| constructor]; right; unfold iv_in_block; apply Exists_cons_hd; cbn [cb_addr cb_size fst snd]; lia
        | assert (AG2 : agrees_on (client_keeps CL (bv_unsigned sp + -80)) ma mb);
          [ eapply (keeps_of_block_write K); [exact G1 | exact MU2 | exact WM2 | lia] | ] ];
        assert (DATA : bytes_at ssegs mb A' src);
        [ destruct DST as [[Hwf HB] Hwr]; cbn [cells_bytes cbytes] in HB; rewrite app_nil_r in HB; exact HB | ]
      end.
      clear MU2 WM2.
      lstep. lstep.
      apply evt_done. eapply (implM_mono ssegs).
      + eapply rest_spec with (o := Some q) (data := src) (lo := lo); try reflexivity;
          [exact Hk | exact G2 | exact Hcb | exact ST1 | exact LOLO | unfold FUZZ_STACK, STDIO_STACK; lia | exact SPM | exact MI
          | exact DATA | intros a Ha; unfold in_block; apply Exists_cons_hd; cbn [cb_addr cb_size fst snd]; lia
          | subst n; lia | exact FR | aln | exact SITES].
      + cbv beta. intros r2 s2' ms2 PO. unfold tr_post in *. destruct_exs PO. destruct PO as (-> & MI3 & ST3 & AG3 & G3 & Hr).
        repeat (lazymatch goal with |- ex _ => eexists end).
        split; [reflexivity|]. split; [exact MI3|]. split; [exact ST3|]. split; [|split; [exact G3| exact Hr]].
        eapply keeps_trans; [exact AG1 | eapply keeps_trans; [exact AG2 | exact AG3 | lia | intros a Ha; exact Ha] | lia | intros a Ha; exact Ha].
    - (* [comment removed for export] *)
      destruct CASES as [-> G1].
      apply (implM_ret_bind ssegs). cbv beta iota.
      unfold implM. iprefix. astep. lstep. lstep.
      do 11 lstep.
      apply evt_done. apply (implM_ret ssegs). apply evt_done.
      release_frame FR ST1 (bv_unsigned sp).
      unfold tr_post. repeat (lazymatch goal with |- ex _ => eexists end).
      split; [cbv delta [mkR]; reflexivity|]. split; [exact MI1|]. split; [exact ST1|]. split; [exact AG1|split; [exact G1| lia]].
  Qed.

  Theorem target_run_proof : target_run_stmt HO K sites_of sites.
  Proof using FREE FUZZ HFL MALLOC SFL HCB SCB VPR. pin_using (fun (FREE FUZZ HFL MALLOC SFL HCB SCB VPR : unit) => tt). ceil_facts.
    unfold target_run_stmt.
    intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m R s CL lo A L content.
    intros (G & ST & LOLO & BUD & SPM & MI & Etp & ALN) Hcb SITES SRC HL0 HL6 HLEN HINB Ea0 Ea1 Ea2 Ea3.
    pose proof BUD as BUD'. unfold TARGET_RUN_STACK, FUZZ_STACK, STDIO_STACK in BUD'.
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
    pose proof (bytes_at_bound _ _ _ _ SRC) as SB.
    pose proof (GI_spw K _ _ _ _ G) as SPW. pose proof (GI_ceil_lo K _ _ _ _ G) as CLO__. unfold rc_lo in CLO__. pose proof LOLO as LOLO'. unfold rc_lo in LOLO'. pose proof SPM as SPM'. unfold rc_spmain in SPM'.
    destruct (client_range_bounds K _ _ _ _ A (Z.of_nat (length content)) G HINB ltac:(lia)) as (SRC0 & SRCHI & SRCI & SRCT).
    (* [comment removed for export] *)
    assert (exists b0 b1 b2 rest, content = b0 :: b1 :: b2 :: rest) as (b0 & b1 & b2 & rest & EC).
    { destruct content as [|x0 [|x1 [|x2 r]]]; [cbn in HL6; lia..|]. repeat eexists. }
    unfold TARGET_RUN_ENTRY. unfold run, target_run.
    set (pl := skipn (Z.to_nat (6 + L)) (map bv_unsigned content)).
    set (cfg := firstn (Z.to_nat L) (skipn 2 (map bv_unsigned content))).
    set (k := Z.to_nat (1 + Z.land (match cfg with [] => 0 | b :: _ => b end) 3)).
    set (plen := (Z.of_nat (length content) - 6 - L)%Z) in *.
    set (src := skipn (Z.to_nat (6 + L)) content).
    assert (Epl : pl = map bv_unsigned src). { subst pl src. rewrite skipn_map. reflexivity. }
    assert (Hsrc : length src = Z.to_nat plen). { subst src plen. rewrite length_skipn. lia. }
    assert (SRCp : bytes_at ssegs m (A + 6 + L) src).
    { subst src. pose proof SRC as SRC2. rewrite <- (firstn_skipn (Z.to_nat (6 + L)) content) in SRC2. apply bytes_at_app in SRC2 as [_ S2].
      rewrite length_firstn in S2. replace (A + Z.of_nat (Nat.min (Z.to_nat (6 + L)) (length content)))%Z with (A + 6 + L)%Z in S2 by lia. exact S2. }
    assert (HINP : forall a, (A + 6 + L <= a < A + 6 + L + Z.of_nat (length src))%Z -> in_block CL a).
    { intros a Ha. apply HINB. lia. }
    assert (Hk : (1 <= k <= 4)%nat). { subst k. pose proof (land3_range (match cfg with [] => 0 | b :: _ => b end)). lia. }
    change (Z.to_nat (1 + Z.land (match cfg with [] => 0 | b :: _ => b end) 3)) with k.
    rewrite Epl.
    subst a0 a1 a2 a3 tp.
    (* [comment removed for export] *)
    destruct (GI_atx K _ _ _ _ G) as (reg & pad & f0 & g0 & j1 & j2 & FL & ATXc & BLT & REG). rewrite Hcb in FL.
    destruct (GI_core K _ _ _ _ G) as (_ & _ & (LC & _) & _ & _ & _).
    destruct (GI_initflag K _ _ _ _ G) as [_ GLI].
    unfold atexit_cells, builtin_cells in ATXc, BLT. unfold libc_cells in LC.
    pose proof (munch_refl [(0x33990, 0x33995); (0x53ae0, 0x53d00); (bv_unsigned sp - 128, bv_unsigned sp)]%Z m) as MU.
    pose proof (wmono_refl ssegs m) as WM.
    unfold implM. iprefix.
    carve_frame 80%nat ST.
    do 17 lstep.
    call_sp reg_spec; [exact ST | exact FL | exact ATXc | exact BLT | exact REG | exact LC | exact GLI | exact MI | lia | lia | reflexivity | reflexivity |].
    rename MI0 into MI.
    lazymatch goal with H : stk ssegs _ lo _ |- _ => rename H into ST end.
    (* [comment removed for export] *)
    lazymatch type of MU with munch _ _ ?mb =>
      assert (G1 : GI K R s CL mb);
      [ rewrite <- (set_cb_same R); rewrite Hcb;
        eapply (GI_atx_frame K HFL SFL HCB SCB); [exact G | exact MU | exact WM | constructor; [left; cbn [fst snd]; unfold rc_lo, rc_spmain; lia | constructor] |];
        exists true, pad; do 4 eexists; split; [eassumption|]; split; [eassumption|]; split; [eassumption| intros _; split; reflexivity]
      | assert (AG0 : agrees_on (client_keeps CL (bv_unsigned sp)) m mb);
        [ eapply (keeps_of_munch K); [exact G | exact MU | exact WM | | lia];
          constructor; [right; cbn [fst snd]; lia | constructor; [right; cbn [fst snd]; lia | constructor; [left; cbn [fst snd]; lia | constructor]]] | ] ]
    end.
    clear MU WM.
    (* [comment removed for export] *)
    assert (TAIL : forall r s' ms' m1, agrees_on (client_keeps CL (bv_unsigned sp)) m m1 ->
              tr_post ra sp gp (rc_tp R) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc R CL lo (bv_unsigned sp + -80) m1 r s' ms' ->
              target_run_post K ra sp gp (rc_tp R) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc R CL lo m r s' ms').
    { intros r s' ms' m1 AGa PO. unfold tr_post in PO. destruct_exs PO. destruct PO as (-> & MIf & STf & AGf & Gf & Hr).
      unfold target_run_post. repeat (lazymatch goal with |- ex _ => eexists end).
      split; [reflexivity|]. split; [exact MIf|]. split; [exact STf|]. split; [| split; [exact Gf| exact Hr]].
      eapply keeps_trans; [exact AGa | exact AGf | lia | intros a Ha; exact Ha]. }
    lstep.
    destruct (Z.eq_dec L 0) as [EL|NL].
    - (* [comment removed for export] *)
      assert (Ek : k = 1%nat). { subst k cfg. rewrite EL. reflexivity. }
      replace (Z_to_bv 64 L) with z64 by (rewrite EL; reflexivity). if_true. lstep. lstep.
      destruct (Z.eq_dec plen 0) as [EP|NP].
      + replace (Z_to_bv 64 plen) with z64 by (rewrite EP; reflexivity). if_false.
        assert (Esrc : src = []). { destruct src; [reflexivity| rewrite EP in Hsrc; cbn in Hsrc; lia]. }
        rewrite Esrc. apply evt_done. eapply (implM_mono ssegs).
        * eapply path_empty with (lo := lo); [exact Hk | exact G1 | exact Hcb | exact ST | exact LOLO | unfold FUZZ_STACK, STDIO_STACK; lia | exact SPM | exact MI | reflexivity
            | reflexivity | rewrite Ek; reflexivity | reflexivity | exact FR | aln | exact SITES].
        * intros r s' ms'. apply TAIL. exact AG0.
      + if_true_by (nez_cond plen ltac:(lia)).
        apply evt_done. eapply (implM_mono ssegs).
        * eapply path_alloc with (lo := lo) (P := (A + 6 + L)%Z); [exact Hk | exact G1 | exact Hcb | exact ST | exact LOLO | unfold FUZZ_STACK, STDIO_STACK; lia | exact SPM | exact MI | reflexivity
            | f_equal; lia | reflexivity | rewrite Ek; reflexivity | reflexivity | lia | lia | exact SRCp | exact HINP | exact FR | aln | exact SITES].
        * intros r s' ms'. apply TAIL. exact AG0.
    - (* [comment removed for export] *)
      assert (Ek : (Z.of_nat k = Z.land (bv_unsigned b2) 3 + 1)%Z).
      { subst k cfg. rewrite EC. replace (Z.to_nat L) with (S (Z.to_nat (L - 1))) by lia. cbn [map skipn firstn].
        pose proof (land3_range (bv_unsigned b2)). lia. }
      if_false_by (eqz_cond_false L ltac:(lia)).
      pose proof SRC as SRC3. rewrite EC in SRC3.
      pose proof (bytes_at_read ssegs _ A _ 2 1 SRC3 ltac:(lia) ltac:(cbn; lia)) as HR. clear SRC3.
      change (Z.to_nat 2) with 2%nat in HR. cbn [firstn skipn] in HR.
      lstep. lstep. lstep. lstep.
      destruct (Z.eq_dec plen 0) as [EP|NP].
      + replace (Z_to_bv 64 plen) with z64 by (rewrite EP; reflexivity). if_true.
        assert (Esrc : src = []). { destruct src; [reflexivity| rewrite EP in Hsrc; cbn in Hsrc; lia]. }
        rewrite Esrc. apply evt_done. eapply (implM_mono ssegs).
        * eapply path_empty with (lo := lo); [exact Hk | exact G1 | exact Hcb | exact ST | exact LOLO | unfold FUZZ_STACK, STDIO_STACK; lia | exact SPM | exact MI | reflexivity
            | reflexivity | f_equal; lia | reflexivity | exact FR | aln | exact SITES].
        * intros r s' ms'. apply TAIL. exact AG0.
      + if_false_by (eqz_cond_false plen ltac:(lia)).
        apply evt_done. eapply (implM_mono ssegs).
        * eapply path_alloc with (lo := lo) (P := (A + 6 + L)%Z); [exact Hk | exact G1 | exact Hcb | exact ST | exact LOLO | unfold FUZZ_STACK, STDIO_STACK; lia | exact SPM | exact MI | reflexivity
            | f_equal; lia | reflexivity | f_equal; lia | reflexivity | lia | lia | exact SRCp | exact HINP | exact FR | aln | exact SITES].
        * intros r s' ms'. apply TAIL. exact AG0.
  Qed.
End TargetRun.

End WithCeil.

(* [comment removed for export] *)
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require ImgTgtUbsan.
From OSSVerify.libpcap.fuzz_pcap.images Require Ubsan.
Module TwB.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Tac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Arr OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Bytes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ZBridge OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ITree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Nodes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Decode OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.SysStep OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.RegsEquiv OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.MonadX OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ImgTgtUbsan.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Monad OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Fmt OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.StdioCore OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Stdio OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapPrelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapTypes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapPure OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Pcap OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Adapter__Spec.Driver OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Adapter__Spec.Adapter OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prog OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Adapter__Spec.StartupModel.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.FileCells__Musl.StrFun OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.STRW_tac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.InitMem OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_kit__Musl.StartupKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.FileCells__Musl.FileCells OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.CellsExtra.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_memcpy.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Startup_B__S3.Startup_B.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Startup_B__S3.Startup.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Exit__S3.Exit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_atexit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.GI.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.GIFacts__S3.GIFacts.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.GIFacts__S3.Ifaces.TwB.
Import OSSVerify.libpcap.fuzz_pcap.images.Ubsan.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.LiaPin.
(* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac lia ::= pinned_lia.
Import ListNotations.
Open Scope bv_scope.
Import ITree.Exc.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
Section WithCeil.
Context {CEILV : CEIL}.
Definition reg_post (sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (lo : Z) (cb : bool) (pad j1 j2 : list byte) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m',
      ms' = MS (mkR ra' sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
               F (Z_to_bv 64 0x13e9c) fc None m' (seg_rom usegs)
      /\ munch [(0x34150%Z, 0x34155%Z); (0x542a0%Z, 0x544c0%Z); ((bv_unsigned sp - 48)%Z, bv_unsigned sp)] m m'
      /\ wmono usegs m m' /\ mem_inv usegs m' /\ stk usegs m' lo (bv_unsigned sp)
      /\ rw_cells usegs m' 0x34150 [C1 (bool8 true); CB 3 pad; C1 (bool8 cb)]
      /\ rw_cells usegs m' 0x542a0 (atexit_cells (Z_to_bv 8 0) (repeat (Z_to_bv 8 0) 3) (atx_slot true) (repeat (Z_to_bv 8 0) 4) (atx_head true))
      /\ rw_cells usegs m' 0x542b8 (builtin_cells (Z_to_bv 64 0x18bc8) j1 (Z_to_bv 64 0x13fac) j2).

Lemma reg_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (lo : Z) (reg cb : bool) (pad : list byte) (f0 g0 : word) (j1 j2 : list byte)
    (cdt thr sec : byte) (tm1 auxv th ts ta tc ps : word) (loc : list byte),
  stk usegs m lo (bv_unsigned sp) ->
  rw_cells usegs m 0x34150 [C1 (bool8 reg); CB 3 pad; C1 (bool8 cb)] ->
  rw_cells usegs m 0x542a0 (atexit_cells (Z_to_bv 8 0) (repeat (Z_to_bv 8 0) 3) (atx_slot reg) (repeat (Z_to_bv 8 0) 4) (atx_head reg)) ->
  rw_cells usegs m 0x542b8 (builtin_cells f0 j1 g0 j2) ->
  (reg = true -> f0 = Z_to_bv 64 0x18bc8 /\ g0 = Z_to_bv 64 0x13fac) ->
  rw_cells usegs m 0x544e8 (libc_cells cdt thr sec (Z_to_bv 8 0) tm1 auxv th ts ta tc ps loc) ->      (* [comment removed for export] *)
  rw_cells usegs m 0x22d80 [C8 (Z_to_bv 64 0)] ->                                                   (* [comment removed for export] *)
  mem_inv usegs m -> (lo <= bv_unsigned sp - 48)%Z -> (alloc_ceiling <= lo)%Z ->
  a1 = Z_to_bv 64 (bv_unsigned (bool8 reg)) -> s4 = Z_to_bv 64 0x34150 ->
  evt usegs (reg_post sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo cb pad j1 j2 m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x13e98) fc None m (seg_rom usegs)).
Proof using CEILV. pin_using (fun (CEILV : unit) => tt). ceil_facts.
  intros until loc. intros ST FL ATX BLT REG LC GLI MI LO LOLO -> ->.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  pose proof (munch_refl [(0x34150%Z, 0x34155%Z); (0x542a0%Z, 0x544c0%Z); ((bv_unsigned sp - 48)%Z, bv_unsigned sp)] m) as MU.
  pose proof (wmono_refl usegs m) as WM.
  destruct reg; cbn [bool8 atx_slot atx_head] in *.
  - (* [comment removed for export] *)
    destruct (REG eq_refl) as [-> ->]. clear REG.
    lstep. if_false.
    unfold reg_post, atexit_cells, builtin_cells in *. cbn [bool8 atx_slot atx_head]. finish.
  - (* [comment removed for export] *)
    clear REG.
    lstep. if_true. lstep. lstep. lstep. lstep. lstep.
    unfold atexit_cells, builtin_cells in ATX, BLT.
    call atexit_spec; [exact ST | exact LC | exact ATX | exact BLT | exact MI | lia | exact LOLO |].
    lstep. if_true. lstep. lstep. lstep. if_true.
    unfold reg_post, atexit_cells, builtin_cells in *. cbn [bool8 atx_slot atx_head]. finish.
Qed.

Lemma free_null_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte),
  a0 = Z_to_bv 64 0 ->
  evt usegs (fun ms' => ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                F (ret_pc ra) fc None m (seg_rom usegs))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x18f4c) fc None m (seg_rom usegs)).
Proof using CEILV. pin_using (fun (CEILV : unit) => tt). ceil_facts.
  intros until m. intros ->.
  step. step. if_true. step. apply evt_done. reflexivity.
Qed.

(* [comment removed for export] *)
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
Proof using CEILV. pin_using (fun (CEILV : unit) => tt). ceil_facts.
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
Proof using CEILV. intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m Dst Src n src junk. ltac2:(SecDiet.SzSec.closeP 'memcpy_specZ__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.

(* [comment removed for export] *)
Lemma ranges_apart : forall S D n, (0 < n)%Z ->
  (forall a, S <= a < S + n -> ~ (D <= a < D + n))%Z -> (S + n <= D \/ D + n <= S)%Z.
Proof using CEILV. pin_using (fun (CEILV : unit) => tt). ceil_facts.
  intros S D n Hn H.
  destruct (Z_lt_le_dec S (D + n)); [|right; lia]. destruct (Z_lt_le_dec D (S + n)); [|left; lia].
  exfalso. destruct (Z_le_gt_dec D S).
  - apply (H S); lia.
  - apply (H D); lia.
Qed.

Lemma land3_range : forall c, (0 <= Z.land c 3 <= 3)%Z.
Proof using CEILV. pin_using (fun (CEILV : unit) => tt). ceil_facts. intros c. change 3%Z with (2^2 - 1)%Z. rewrite zb_land_mask by lia. pose proof (Z.mod_pos_bound c (2^2) ltac:(lia)). lia. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma target_alloc_init_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte),
  evt usegs (fun ms' => ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                F (ret_pc ra) fc None m (seg_rom usegs))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x13e48) fc None m (seg_rom usegs)).
Proof using CEILV. pin_using (fun (CEILV : unit) => tt). ceil_facts. intros. step. apply evt_done. reflexivity. Qed.

Lemma target_alloc_count_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte),
  evt usegs (fun ms' => ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                F (ret_pc ra) fc None m (seg_rom usegs))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x13e4c) fc None m (seg_rom usegs)).
Proof using CEILV. pin_using (fun (CEILV : unit) => tt). ceil_facts. intros. step. step. apply evt_done. reflexivity. Qed.

Lemma eqz_cond_false : forall z, (0 < z < 2^64)%Z -> bv_eqb (Z_to_bv 64 z) z64 = false.
Proof using CEILV. pin_using (fun (CEILV : unit) => tt). ceil_facts. intros z Hz. unfold bv_eqb. rewrite !unsigned_lit by lia. apply Z.eqb_neq. lia. Qed.

Lemma nez_cond : forall z, (0 < z < 2^64)%Z -> negb (bv_eqb (Z_to_bv 64 z) z64) = true.
Proof using CEILV. pin_using (fun (CEILV : unit) => tt). ceil_facts. intros z Hz. unfold bv_eqb. rewrite !unsigned_lit by lia. apply Bool.negb_true_iff. apply Z.eqb_neq. lia. Qed.

Section TargetRun.
  Context {H hptr : Type} (HO : HeapOps H hptr) (K : modkit H hptr) (sites_of : Z -> stack_site -> Z) (sites : stack_site -> Z).
  Hypothesis HFL : heap_frame_law K.
  Hypothesis SFL : stdio_fp_law K.
  Hypothesis HCB : heap_cb_law K.
  Hypothesis SCB : stdio_cb_law K.
  Hypothesis MALLOC : malloc_stmt HO K.
  Hypothesis FREE : free_stmt HO K.
  Hypothesis FUZZ : fuzz_one_stmt HO K sites_of sites.
  Hypothesis VPR : vprintf_d_stmt K.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Ltac aln_fin := fastfirst (first [ noevar_assumption |lia | Z.div_mod_to_equations; lia]).
  Ltac aln :=
    fastfirst (first [ noevar_assumption | assumption
          | (match goal with H : bv_unsigned ?x = _ |- (bv_unsigned ?x mod 16 = 0)%Z => rewrite H end; aln_fin)
          | (rewrite unsigned_lit by lia; aln_fin)
          | aln_fin ]).

  Definition emit_printf_spec__stmt : Prop := forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (R : rctx) (s : PState H hptr) (CL : list cblock) (lo v : Z),
    GI K R s CL m -> stk usegs m lo (bv_unsigned sp) -> (rc_lo R <= lo)%Z -> (lo + 80 + STDIO_STACK <= bv_unsigned sp)%Z ->
    (bv_unsigned sp <= rc_spmain R)%Z -> mem_inv usegs m -> tp = rc_tp R ->
    a1 = Z_to_bv 64 v -> (- 2^31 <= v < 2^31)%Z -> (bv_unsigned sp mod 16 = 0)%Z ->
    implM usegs (@emit_d (PState H hptr) hptr ps_libc set_libc v) s
      (out_post K ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc R CL lo m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x13fdc) fc None m (seg_rom usegs)).
  Section Sz10.
  Variables ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m R s CL lo v : ltac2:(SecDiet.SzSec.tyM 'emit_printf_spec__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra).
  Lemma emit_printf_spec__body : ltac2:(SecDiet.SzSec.bodyP 'emit_printf_spec__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof using HFL SFL VPR. pin_using (fun (HFL SFL VPR : unit) => tt). ceil_facts.
    intros G ST LOLO BUD SPM MI Etp Ea1 Hv ALN.
    unfold STDIO_STACK in BUD.
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
    pose proof (GI_spw K _ _ _ _ G) as SPW. pose proof (GI_ceil_lo K _ _ _ _ G) as CLO__. unfold rc_lo in CLO__. unfold rc_lo in LOLO. unfold rc_spmain in SPM.
    pose proof (munch_refl [(bv_unsigned sp - 80, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl usegs m) as WM.
    subst a1 tp.
    unfold implM. iprefix.
    carve_frame 80%nat ST.
    steps_to 0x20d10%Z.
    (* [comment removed for export] *)
    assert (G1 : GI K R s CL m0).
    { eapply (GI_client_frame K HFL SFL); [exact G | exact MU | exact WM |].
      constructor; [left; cbn [fst snd]; unfold rc_lo, rc_spmain; lia | constructor]. }
    assert (AG0 : agrees_on (client_keeps CL (bv_unsigned sp)) m m0).
    { eapply (keeps_of_munch K); [exact G | exact MU | exact WM | | lia]. constructor; [left; cbn [fst snd]; lia| constructor]. }
    clear MU WM.
    (* [comment removed for export] *)
    apply (proj1 (rw_cells_app usegs m0 _ [_; _; _] _)) in FR as [FR1 FR2]. cbn [cells_size csize Nat.add] in FR2.
    apply (rw_cells_merge usegs m0 _ [C8 (Z_to_bv 64 v)] [C8 a2; C8 a3; C8 a4; C8 a5; C8 a6; C8 a7] []) in FR2.
    cbn [cells_size csize cells_bytes cbytes Nat.add app] in FR2.
    replace (bv_unsigned sp + -80 + Z.of_nat 24)%Z with (bv_unsigned sp + -56)%Z in FR2 by lia.
    name_sp sp (-80)%Z.
    apply evt_done. unfold emit_d. eapply implM_post_evt.
    { eapply VPR.
      { split; [exact G1|]. split; [rewrite Hsp; exact ST|]. split; [unfold rc_lo; lia|]. split; [unfold STDIO_STACK; lia|].
        split; [unfold rc_spmain; lia|]. split; [exact MI|]. split; [reflexivity| aln]. }
      all: fastfirst (first [ noevar_assumption |reflexivity | exact Hv | exact FR2 | unfold rc_spmain; lia]). }
    intros [] s' ms' PO. unfold out_post in PO. destruct_exs PO. destruct PO as (-> & MI' & ST' & AG & G'). clear MI. rename MI' into MI.
    replace (ret_pc (Z_to_bv 64 81944)) with (Z_to_bv 64 81944) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
    apply (keeps_rw_cells_stack CL _ _ _ _ _ AG) in FR1; [|lia].
    apply (keeps_rw_cells_stack CL _ _ _ _ _ AG) in FR2; [|lia].
    unname_sp.
    lstep. lstep. lstep.
    release_frame FR1 ST' (bv_unsigned sp + -56)%Z. release_frame FR2 ST' (bv_unsigned sp).
    finish.
    eapply keeps_trans; [exact AG0 | exact AG | lia | intros a Ha; exact Ha].
  Qed.
  End Sz10.
  Lemma emit_printf_spec : ltac:(let t := eval cbv delta [emit_printf_spec__stmt] in emit_printf_spec__stmt in exact t).
  Proof using HFL SFL VPR. intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m R s CL lo v. ltac2:(SecDiet.SzSec.closeP 'emit_printf_spec__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.

  (* [comment removed for export] *)
  Definition loop_post (spi gp tp s0 s1 s2 s4 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (R : rctx) (CL : list cblock) (lo : Z) (bad : bool) (m : mem) : bool -> PState H hptr -> machine_state -> Prop :=
    fun bad' s' ms' => exists ra' t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 s3' m',
      ms' = MS (mkR ra' spi gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3' s4 (Z_to_bv 64 0) (Z_to_bv 64 (Z.b2z bad)) s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (Z_to_bv 64 0x13f44) fc None m' (seg_rom usegs)
      /\ bad' = bad /\ mem_inv usegs m' /\ stk usegs m' lo (bv_unsigned spi)
      /\ agrees_on (client_keeps CL (bv_unsigned spi)) m m' /\ GI K R s' CL m'.

  (* [comment removed for export] *)
  Ltac tr_hide H := lazymatch type of H with ?T => let X := fresh "AUX" in pose (X := T); change T with X in H end.
  Ltac tr_unhide H := lazymatch type of H with ?X => subst X end.

  Lemma set_cb_back : forall (R : rctx) b, rc_cb R = false -> set_cb (set_cb R b) false = R.
  Proof using Type. pin_using tt. intros [] b Hb. cbn in Hb. subst. reflexivity. Qed.

  Lemma loop_spec : forall (n : nat) (ra spi gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (R : rctx) (s : PState H hptr) (CL : list cblock) (lo D : Z) (data : list byte) (bad : bool),
    (1 <= n <= 4)%nat ->
    GI K R s CL m -> rc_cb R = false ->
    stk usegs m lo (bv_unsigned spi) -> (rc_lo R <= lo)%Z -> (lo + FUZZ_STACK <= bv_unsigned spi)%Z ->
    (lo + 80 + STDIO_STACK <= bv_unsigned spi)%Z -> (bv_unsigned spi <= rc_spmain R)%Z -> mem_inv usegs m -> tp = rc_tp R ->
    s0 = Z_to_bv 64 (Z.of_nat (length data)) -> s1 = Z_to_bv 64 D -> s5 = Z_to_bv 64 (Z.of_nat n) -> s4 = Z_to_bv 64 0x34150 ->
    s6 = Z_to_bv 64 (Z.b2z bad) -> s7 = Z_to_bv 64 (-2) ->
    bytes_at usegs m D data ->
    (forall a, D <= a < D + Z.of_nat (length data) -> in_block CL a)%Z ->
    (Z.of_nat (length data) < 2^26)%Z ->
    (bv_unsigned spi mod 16 = 0)%Z -> sites = sites_of (bv_unsigned spi) ->
    implM usegs (call_loop (@emit_d (PState H hptr) hptr ps_libc set_libc) (harness_call HO fo_nop sites) n (map bv_unsigned data) bad) s
      (loop_post spi gp tp s0 s1 s2 s4 s7 s8 s9 s10 s11 F fc R CL lo bad m)
      (MS (mkR ra spi gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x13f0c) fc None m (seg_rom usegs)).
  Proof using FUZZ HFL SFL HCB SCB VPR. pin_using (fun (FUZZ HFL SFL HCB SCB VPR : unit) => tt). ceil_facts.
    induction n as [|n IH]; [intros; lia|].
    intros until bad. intros Hn G Hcb ST LOLO BUDF BUDS SPM MI Etp Es0 Es1 Es5 Es4 Es6 Es7 SRC HK HD ALN SITES.
    unfold FUZZ_STACK in BUDF. unfold STDIO_STACK in BUDS.
    pose proof (bv_unsigned_in_range 64 spi) as RSP. unfold bv_modulus in RSP. cbn in RSP.
    pose proof (GI_spw K _ _ _ _ G) as SPW. pose proof (GI_ceil_lo K _ _ _ _ G) as CLO__. unfold rc_lo in CLO__. unfold rc_lo in LOLO. unfold rc_spmain in SPM.
    pose proof (bytes_at_bound _ _ _ _ SRC) as DB.
    subst s0 s1 s5 s4 s6 s7 tp.
    cbn [call_loop].
    (* [comment removed for export] *)
    destruct (GI_atx K _ _ _ _ G) as (reg & pad & f0 & g0 & j1 & j2 & FL & ATXc & BLT & REG). rewrite Hcb in FL. cbn [bool8] in FL.
    pose proof (munch_refl [(0x34150, 0x34155); (0x542a0, 0x544c0)]%Z m) as MU. pose proof (wmono_refl usegs m) as WM.
    unfold atexit_cells, builtin_cells in ATXc, BLT.
    tr_hide SRC.
    unfold implM. iprefix. lstep. lstep.
    tr_unhide SRC.
    lazymatch type of MU with munch _ _ ?mb =>
      assert (G1 : GI K (set_cb R true) s CL mb);
      [ eapply (GI_atx_frame K HFL SFL HCB SCB); [exact G | exact MU | exact WM | constructor |];
        exists reg, pad, f0, g0, j1, j2; split; [exact FL|]; split; [exact ATXc|]; split; [exact BLT| exact REG]
      | assert (AG0 : agrees_on (client_keeps CL (bv_unsigned spi)) m mb);
        [ eapply (keeps_of_munch K); [exact G | exact MU | exact WM | | lia];
          constructor; [right; cbn [fst snd]; lia | constructor; [right; cbn [fst snd]; lia | constructor]] | ] ]
    end.
    apply (agrees_bytes_at _ _ _ _ _ AG0) in SRC; [| intros a Ha; right; apply HK; exact Ha].
    clear MU WM G FL ATXc BLT REG.
    lstep. lstep. lstep.
    apply evt_done. eapply (implM_bind usegs).
    { eapply (FUZZ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (set_cb R true));
        [ | exact SITES | reflexivity | reflexivity | exact SRC | exact HK | exact HD].
      unfold std_pre. change (rc_lo (set_cb R true)) with (rc_lo R). change (rc_spmain (set_cb R true)) with (rc_spmain R). change (rc_tp (set_cb R true)) with (rc_tp R).
      split; [exact G1|]. split; [exact ST|]. split; [unfold rc_lo; lia|]. split; [unfold FUZZ_STACK; lia|].
      split; [unfold rc_spmain; lia|]. split; [exact MI|]. split; [reflexivity| aln]. }
    intros rc' s' ms' PO. unfold fuzz_post in PO. destruct_exs PO. destruct PO as (-> & MI1 & ST1 & AG1 & G1' & ->).
    clear MI G1. cbn [fst snd].
    replace (ret_pc (Z_to_bv 64 0x13f20)) with (Z_to_bv 64 0x13f20) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
    (* [comment removed for export] *)
    clear reg pad f0 g0 j1 j2.
    destruct (GI_atx K _ _ _ _ G1') as (reg & pad & f0 & g0 & j1 & j2 & FL & ATXc & BLT & REG). cbn [set_cb rc_cb bool8] in FL.
    unfold atexit_cells, builtin_cells in ATXc, BLT.
    lazymatch goal with |- implM _ _ _ _ (MS _ _ _ _ _ ?m1 _) =>
      pose proof (munch_refl [(0x34150, 0x34155); (0x542a0, 0x544c0)]%Z m1) as MU; pose proof (wmono_refl usegs m1) as WM end.
    unfold implM. iprefix. lstep. lstep.
    lazymatch type of MU with munch _ ?ma ?mb =>
      assert (G2 : GI K R s' CL mb);
      [ rewrite <- (set_cb_back R true Hcb) at 1;
        eapply (GI_atx_frame K HFL SFL HCB SCB); [exact G1' | exact MU | exact WM | constructor |];
        exists reg, pad, f0, g0, j1, j2; split; [exact FL|]; split; [exact ATXc|]; split; [exact BLT| exact REG]
      | assert (AG2 : agrees_on (client_keeps CL (bv_unsigned spi)) ma mb);
        [ eapply (keeps_of_munch K); [exact G1' | exact MU | exact WM | | lia];
          constructor; [right; cbn [fst snd]; lia | constructor; [right; cbn [fst snd]; lia | constructor]] | ] ]
    end.
    clear MU WM G1' FL ATXc BLT REG.
    lstep. lstep.
    apply evt_done. eapply (implM_bind usegs).
    { eapply (emit_printf_spec _ spi); [exact G2 | eassumption | unfold rc_lo; lia | unfold STDIO_STACK; lia | unfold rc_spmain; lia | eassumption | reflexivity | reflexivity | lia | aln]. }
    intros [] s'' ms'' PO. unfold out_post in PO. destruct_exs PO. destruct PO as (-> & MI3 & ST3 & AG3 & G3).
    cbn [fst snd].
    replace (ret_pc (Z_to_bv 64 0x13f30)) with (Z_to_bv 64 0x13f30) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
    rewrite bad_rc_step0.
    unfold implM. iprefix. lstep. lstep. if_true. lstep.
    replace (bv_swrap 32 (Z.of_nat (S n) + -1)) with (Z.of_nat n) by (rewrite bv_swrap_small; [lia| change (bv_half_modulus 32) with 2147483648%Z; lia]).
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mz _) =>
      assert (AGall : agrees_on (client_keeps CL (bv_unsigned spi)) m mz) end.
    { eapply keeps_trans; [exact AG0 | eapply keeps_trans; [exact AG1 | eapply keeps_trans; [exact AG2 | exact AG3 | lia | intros a Ha; exact Ha] | lia | intros a Ha; exact Ha] | lia | intros a Ha; exact Ha]. }
    destruct (Nat.eq_dec n 0) as [->|Hn0].
    - change (Z.of_nat 0) with 0%Z. astep. apply evt_done. apply (implM_ret usegs). apply evt_done.
      unfold loop_post. repeat (lazymatch goal with |- ex _ => eexists end).
      split; [cbv delta [mkR]; reflexivity|]. split; [reflexivity|]. split; [exact MI3|]. split; [exact ST3|]. split; [exact AGall|exact G3].
    - lstep. if_true_by (nez_cond (Z.of_nat n) ltac:(lia)).
      apply evt_done. eapply (implM_mono usegs).
      + eapply IH; [lia | exact G3 | exact Hcb | exact ST3 | unfold rc_lo; lia | unfold FUZZ_STACK; lia | unfold STDIO_STACK; lia
                   | unfold rc_spmain; lia | exact MI3 | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | | exact HK | exact HD | aln | exact SITES].
        eapply agrees_bytes_at; [exact AG3 | eapply agrees_bytes_at; [exact AG2 | eapply agrees_bytes_at; [exact AG1 | exact SRC |] |] |]; intros a Ha; right; apply HK; exact Ha.
      + cbv beta. intros b2 s2' ms2 PO. unfold loop_post in *. destruct_exs PO. destruct PO as (-> & -> & MI4 & ST4 & AG4 & G4).
        repeat (lazymatch goal with |- ex _ => eexists end).
        split; [reflexivity|]. split; [reflexivity|]. split; [exact MI4|]. split; [exact ST4|]. split; [|exact G4].
        eapply keeps_trans; [exact AGall | exact AG4 | lia | intros a Ha; exact Ha].
  Qed.

  (* [comment removed for export] *)
  Definition tr_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (R : rctx) (CL : list cblock) (lo SP : Z) (m : mem) : Z -> PState H hptr -> machine_state -> Prop :=
    fun r s' ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 r) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (ret_pc ra) fc None m' (seg_rom usegs)
      /\ mem_inv usegs m' /\ stk usegs m' lo (bv_unsigned sp)
      /\ agrees_on (client_keeps CL SP) m m'
      /\ GI K R s' CL m' /\ (0 <= r <= 2)%Z.

  Lemma rest_spec : forall (k : nat) (o : option hptr)
      (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (cra cs0 cs1 cs2 cs3 cs4 cs5 cs6 cs7 : word) (junk : list byte)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (R : rctx) (s : PState H hptr) (CL : list cblock) (lo D : Z) (data : list byte),
    (1 <= k <= 4)%nat ->
    GI K R s (match o with Some q => (q, D, Z.of_nat (length data)) :: CL | None => CL end) m -> rc_cb R = false ->
    stk usegs m lo (bv_unsigned sp + -80) -> (rc_lo R <= lo)%Z -> (lo + FUZZ_STACK + 80 + STDIO_STACK <= bv_unsigned sp)%Z ->
    (bv_unsigned sp <= rc_spmain R)%Z -> mem_inv usegs m -> tp = rc_tp R ->
    s0 = Z_to_bv 64 (Z.of_nat (length data)) -> s1 = Z_to_bv 64 D -> s5 = Z_to_bv 64 (Z.of_nat k) -> s4 = Z_to_bv 64 0x34150 ->
    s2 = match o with Some _ => Z_to_bv 64 D | None => Z_to_bv 64 0 end ->
    bytes_at usegs m D data ->
    (forall a, D <= a < D + Z.of_nat (length data) ->
               in_block (match o with Some q => (q, D, Z.of_nat (length data)) :: CL | None => CL end) a)%Z ->
    (Z.of_nat (length data) < 2^26)%Z ->
    rw_cells usegs m (bv_unsigned sp + -80) [CB 8 junk; C8 cs7; C8 cs6; C8 cs5; C8 cs4; C8 cs3; C8 cs2; C8 cs1; C8 cs0; C8 cra] ->
    (bv_unsigned sp mod 16 = 0)%Z -> sites = sites_of (bv_unsigned sp + -80) ->
    implM usegs (bad <- call_loop (@emit_d (PState H hptr) hptr ps_libc set_libc) (harness_call HO fo_nop sites) k (map bv_unsigned data) false ;;
                 match o with Some q => pfree HO q | None => mret tt end ;;;
                 mret (if bad then 78 else 0)%Z) s
      (tr_post cra sp gp tp cs0 cs1 cs2 cs3 cs4 cs5 cs6 cs7 s8 s9 s10 s11 F fc R CL lo (bv_unsigned sp + -80) m)
      (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -80)) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x13f04) fc None m (seg_rom usegs)).
  Proof using FREE FUZZ HFL SFL HCB SCB VPR. pin_using (fun (FREE FUZZ HFL SFL HCB SCB VPR : unit) => tt). ceil_facts.
    intros until data. intros Hk G Hcb ST LOLO BUD SPM MI Etp Es0 Es1 Es5 Es4 Es2 SRC HK HD FR ALN SITES.
    unfold FUZZ_STACK, STDIO_STACK in BUD.
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
    pose proof (GI_spw K _ _ _ _ G) as SPW. pose proof (GI_ceil_lo K _ _ _ _ G) as CLO__. unfold rc_lo in CLO__. unfold rc_lo in LOLO. unfold rc_spmain in SPM.
    pose proof (bytes_at_bound _ _ _ _ SRC) as DB.
    subst s0 s1 s5 s4 tp.
    (* [comment removed for export] *)
    unfold implM. iprefix. lstep. lstep.
    name_sp sp (-80)%Z.
    apply evt_done.
    eapply (implM_bind usegs).
    { eapply (loop_spec k) with (bad := false);
        [exact Hk | exact G | exact Hcb | rewrite Hsp; exact ST | unfold rc_lo; lia | unfold FUZZ_STACK; lia | unfold STDIO_STACK; lia
        | unfold rc_spmain; lia | exact MI | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | exact SRC | exact HK | exact HD | aln | rewrite Hsp; exact SITES]. }
    intros bad' s' ms' PO. unfold loop_post in PO. destruct_exs PO. destruct PO as (-> & -> & MI1 & ST1 & AG1 & G1). clear MI.
    apply (keeps_rw_cells_stack _ _ _ _ _ _ AG1) in FR; [|lia].
    unname_sp.
    unfold implM. iprefix. lstep. lstep.
    destruct o as [q|]; subst s2.
    - (* [comment removed for export] *)
      name_sp sp (-80)%Z.
      apply evt_done. eapply (implM_bind usegs).
      { eapply FREE with (C1 := []); [| reflexivity].
        split; [exact G1|]. split; [rewrite Hsp; exact ST1|]. split; [unfold rc_lo; lia|]. split; [unfold FREE_STACK; lia|].
        split; [unfold rc_spmain; lia|]. split; [exact MI1|]. split; [reflexivity| aln]. }
      intros [] s'' ms'' PO. unfold free_post in PO. destruct_exs PO. destruct PO as (-> & MI2 & ST2 & AG2 & G2). clear MI1.
      cbn [app] in AG2, G2.
      replace (ret_pc (Z_to_bv 64 0x13f4c)) with (Z_to_bv 64 0x13f4c) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
      apply (keeps_rw_cells_stack _ _ _ _ _ _ AG2) in FR; [|lia].
      unname_sp.
      unfold implM. iprefix. do 3 lstep.
      do 11 lstep.
      apply evt_done. apply (implM_ret usegs). apply evt_done.
      release_frame FR ST2 (bv_unsigned sp).
      unfold tr_post. repeat (lazymatch goal with |- ex _ => eexists end).
      split; [cbv delta [mkR]; reflexivity|]. split; [exact MI2|]. split; [exact ST2|]. split; [|split; [exact G2| lia]].
      eapply keeps_trans; [ | exact AG2 | lia | intros a Ha; exact Ha].
      eapply client_keeps_weaken; [exact AG1 | lia | intros a Ha; apply in_block_cons; exact Ha].
    - (* [comment removed for export] *)
      eapply evt_cut; [eapply free_null_spec; reflexivity|]. cbv beta. intros ms' ->.
      replace (ret_pc (Z_to_bv 64 0x13f4c)) with (Z_to_bv 64 0x13f4c) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
      do 3 lstep.
      do 11 lstep.
      apply evt_done. apply (implM_ret_bind usegs). apply (implM_ret usegs). apply evt_done.
      release_frame FR ST1 (bv_unsigned sp).
      unfold tr_post. repeat (lazymatch goal with |- ex _ => eexists end).
      split; [cbv delta [mkR]; reflexivity|]. split; [exact MI1|]. split; [exact ST1|]. split; [exact AG1|split; [exact G1| lia]].
  Qed.

  (* [comment removed for export] *)
  Definition tr_rest (k : nat) (pl : list Z) : M (PState H hptr) Z :=
    owned <- (if (length pl =? 0)%nat then mret (Some None)
              else q <- pmalloc HO (zlength pl) ;;
                   mret (match q with None => None | Some q' => Some (Some q') end)) ;;
    match owned with
    | None => mret 2%Z
    | Some o =>
        bad <- call_loop (@emit_d (PState H hptr) hptr ps_libc set_libc) (harness_call HO fo_nop sites) k pl false ;;
        (match o with Some q => pfree HO q | None => mret tt end) ;;;
        mret (if bad then 78 else 0)%Z
    end.

  (* [comment removed for export] *)
  Lemma path_empty : forall (k : nat)
      (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (cra cs0 cs1 cs2 cs3 cs4 cs5 cs6 cs7 : word) (junk : list byte)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (R : rctx) (s : PState H hptr) (CL : list cblock) (lo : Z),
    (1 <= k <= 4)%nat ->
    GI K R s CL m -> rc_cb R = false ->
    stk usegs m lo (bv_unsigned sp + -80) -> (rc_lo R <= lo)%Z -> (lo + FUZZ_STACK + 80 + STDIO_STACK <= bv_unsigned sp)%Z ->
    (bv_unsigned sp <= rc_spmain R)%Z -> mem_inv usegs m -> tp = rc_tp R ->
    s0 = Z_to_bv 64 0 -> s5 = Z_to_bv 64 (Z.of_nat k) -> s4 = Z_to_bv 64 0x34150 ->
    rw_cells usegs m (bv_unsigned sp + -80) [CB 8 junk; C8 cs7; C8 cs6; C8 cs5; C8 cs4; C8 cs3; C8 cs2; C8 cs1; C8 cs0; C8 cra] ->
    (bv_unsigned sp mod 16 = 0)%Z -> sites = sites_of (bv_unsigned sp + -80) ->
    implM usegs (tr_rest k []) s
      (tr_post cra sp gp tp cs0 cs1 cs2 cs3 cs4 cs5 cs6 cs7 s8 s9 s10 s11 F fc R CL lo (bv_unsigned sp + -80) m)
      (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -80)) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x13efc) fc None m (seg_rom usegs)).
  Proof using FREE FUZZ HFL SFL HCB SCB VPR. pin_using (fun (FREE FUZZ HFL SFL HCB SCB VPR : unit) => tt). ceil_facts.
    intros until lo. intros Hk G Hcb ST LOLO BUD SPM MI Etp Es0 Es5 Es4 FR ALN SITES.
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
    pose proof (GI_spw K _ _ _ _ G) as SPW. pose proof (GI_ceil_lo K _ _ _ _ G) as CLO__. unfold rc_lo in CLO__. pose proof LOLO as LOLO'. unfold rc_lo in LOLO'. unfold FUZZ_STACK, STDIO_STACK in BUD.
    subst s0 s5 s4 tp.
    unfold tr_rest. cbn [length Nat.eqb]. apply (implM_ret_bind usegs). cbv beta iota.
    unfold implM. iprefix. lstep. lstep.
    apply evt_done. eapply rest_spec with (o := None) (data := @nil byte); try reflexivity;
      [exact Hk | exact G | exact Hcb | exact ST | exact LOLO | unfold FUZZ_STACK, STDIO_STACK; lia | exact SPM | exact MI
      | apply bytes_at_nil; lia | intros a Ha; cbn in Ha; lia | exact FR | aln | exact SITES].
  Qed.

  (* [comment removed for export] *)
  Lemma path_alloc : forall (k : nat)
      (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (cra cs0 cs1 cs2 cs3 cs4 cs5 cs6 cs7 : word) (junk : list byte)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (R : rctx) (s : PState H hptr) (CL : list cblock) (lo P : Z) (src : list byte),
    (1 <= k <= 4)%nat ->
    GI K R s CL m -> rc_cb R = false ->
    stk usegs m lo (bv_unsigned sp + -80) -> (rc_lo R <= lo)%Z -> (lo + FUZZ_STACK + 80 + STDIO_STACK <= bv_unsigned sp)%Z ->
    (bv_unsigned sp <= rc_spmain R)%Z -> mem_inv usegs m -> tp = rc_tp R ->
    s0 = Z_to_bv 64 (Z.of_nat (length src)) -> s1 = Z_to_bv 64 P -> s5 = Z_to_bv 64 (Z.of_nat k) -> s4 = Z_to_bv 64 0x34150 ->
    (0 < length src)%nat -> (Z.of_nat (length src) < 2^26)%Z ->
    bytes_at usegs m P src -> (forall a, P <= a < P + Z.of_nat (length src) -> in_block CL a)%Z ->
    rw_cells usegs m (bv_unsigned sp + -80) [CB 8 junk; C8 cs7; C8 cs6; C8 cs5; C8 cs4; C8 cs3; C8 cs2; C8 cs1; C8 cs0; C8 cra] ->
    (bv_unsigned sp mod 16 = 0)%Z -> sites = sites_of (bv_unsigned sp + -80) ->
    implM usegs (tr_rest k (map bv_unsigned src)) s
      (tr_post cra sp gp tp cs0 cs1 cs2 cs3 cs4 cs5 cs6 cs7 s8 s9 s10 s11 F fc R CL lo (bv_unsigned sp + -80) m)
      (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -80)) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x13eb0) fc None m (seg_rom usegs)).
  Proof using FREE FUZZ HFL MALLOC SFL HCB SCB VPR. pin_using (fun (FREE FUZZ HFL MALLOC SFL HCB SCB VPR : unit) => tt). ceil_facts.
    intros until src. intros Hk G Hcb ST LOLO BUD SPM MI Etp Es0 Es1 Es5 Es4 HP0 HP32 SRC HINP FR ALN SITES.
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
    pose proof (GI_spw K _ _ _ _ G) as SPW. pose proof (GI_ceil_lo K _ _ _ _ G) as CLO__. unfold rc_lo in CLO__. pose proof LOLO as LOLO'. unfold rc_lo in LOLO'. unfold FUZZ_STACK, STDIO_STACK in BUD.
    pose proof SPM as SPM'. unfold rc_spmain in SPM'.
    destruct (client_range_bounds K _ _ _ _ P (Z.of_nat (length src)) G HINP ltac:(lia)) as (P0 & PHI & PI & PT).
    subst s0 s1 s5 s4 tp.
    set (n := Z.of_nat (length src)) in *.
    unfold tr_rest. rewrite length_map. replace (length src =? 0)%nat with false by (symmetry; apply Nat.eqb_neq; lia).
    unfold zlength. rewrite length_map. fold n.
    apply (implM_bind_assoc usegs).
    unfold implM. iprefix. lstep. lstep.
    name_sp sp (-80)%Z.
    apply evt_done. eapply (implM_bind usegs).
    { eapply MALLOC; [| reflexivity | lia].
      split; [exact G|]. split; [rewrite Hsp; exact ST|]. split; [exact LOLO|]. split; [unfold MALLOC_STACK; lia|].
      split; [unfold rc_spmain; lia|]. split; [exact MI|]. split; [reflexivity| aln]. }
    intros r s' ms' PO. unfold malloc_post in PO. destruct_exs PO. destruct PO as (-> & MI1 & ST1 & AG1 & CASES). clear MI.
    replace (ret_pc (Z_to_bv 64 0x13eb8)) with (Z_to_bv 64 0x13eb8) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
    apply (keeps_rw_cells_stack _ _ _ _ _ _ AG1) in FR; [|lia].
    apply (keeps_bytes_at_block _ _ _ _ _ _ AG1) in SRC; [|exact HINP].
    unname_sp.
    destruct r as [q|].
    - destruct CASES as (A' & junk' & -> & G1 & BLK & BOK & HADDR).
      pose proof BOK as BOK'. unfold block_ok in BOK'. cbn [cb_addr cb_size fst snd] in BOK'. destruct BOK' as (B1 & B2 & B3 & B4 & B5 & B6).
      assert (SEP : (P + n <= A' \/ A' + n <= P)%Z).
      { apply ranges_apart; [lia|]. intros a Ha Hin.
        destruct (GI_blocks K _ _ _ _ G1) as [_ [AP _]].
        pose proof (HINP a Ha) as Hb. unfold in_block in Hb. apply Exists_exists in Hb as (b & Hb & Hr).
        pose proof (proj1 (Forall_forall _ _) AP _ Hb) as X. unfold apart in X. cbn [cb_addr cb_size fst snd] in X. lia. }
      apply (implM_ret_bind usegs). cbv beta iota.
      unfold implM. iprefix. lstep. if_false_by (eqz_cond_false A' ltac:(lia)).
      lstep. lstep. lstep. lstep.
      match goal with |- evt _ _ (MS _ _ _ _ _ ?m1 _) =>
        pose proof (munch_refl [(A', A' + n)]%Z m1) as MU2; pose proof (wmono_refl usegs m1) as WM2 end.
      call (memcpy_specZ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ A' P n src junk');
        [reflexivity | reflexivity | reflexivity | exact SRC | subst n; lia | lia | exact BLK | exact SEP | lia | lia | exact MI1 |].
      rename PC into DST. clear POST.
      lazymatch type of MU2 with munch _ ?ma ?mb =>
        assert (G2 : GI K R s' ((q, A', n) :: CL) mb);
        [ eapply (GI_client_frame K HFL SFL); [exact G1 | exact MU2 | exact WM2 |];
          constructor; [| constructor]; right; unfold iv_in_block; apply Exists_cons_hd; cbn [cb_addr cb_size fst snd]; lia
        | assert (AG2 : agrees_on (client_keeps CL (bv_unsigned sp + -80)) ma mb);
          [ eapply (keeps_of_block_write K); [exact G1 | exact MU2 | exact WM2 | lia] | ] ];
        assert (DATA : bytes_at usegs mb A' src);
        [ destruct DST as [[Hwf HB] Hwr]; cbn [cells_bytes cbytes] in HB; rewrite app_nil_r in HB; exact HB | ]
      end.
      clear MU2 WM2.
      lstep. lstep.
      apply evt_done. eapply (implM_mono usegs).
      + eapply rest_spec with (o := Some q) (data := src) (lo := lo); try reflexivity;
          [exact Hk | exact G2 | exact Hcb | exact ST1 | exact LOLO | unfold FUZZ_STACK, STDIO_STACK; lia | exact SPM | exact MI
          | exact DATA | intros a Ha; unfold in_block; apply Exists_cons_hd; cbn [cb_addr cb_size fst snd]; lia
          | subst n; lia | exact FR | aln | exact SITES].
      + cbv beta. intros r2 s2' ms2 PO. unfold tr_post in *. destruct_exs PO. destruct PO as (-> & MI3 & ST3 & AG3 & G3 & Hr).
        repeat (lazymatch goal with |- ex _ => eexists end).
        split; [reflexivity|]. split; [exact MI3|]. split; [exact ST3|]. split; [|split; [exact G3| exact Hr]].
        eapply keeps_trans; [exact AG1 | eapply keeps_trans; [exact AG2 | exact AG3 | lia | intros a Ha; exact Ha] | lia | intros a Ha; exact Ha].
    - (* [comment removed for export] *)
      destruct CASES as [-> G1].
      apply (implM_ret_bind usegs). cbv beta iota.
      unfold implM. iprefix. astep. lstep. lstep.
      do 11 lstep.
      apply evt_done. apply (implM_ret usegs). apply evt_done.
      release_frame FR ST1 (bv_unsigned sp).
      unfold tr_post. repeat (lazymatch goal with |- ex _ => eexists end).
      split; [cbv delta [mkR]; reflexivity|]. split; [exact MI1|]. split; [exact ST1|]. split; [exact AG1|split; [exact G1| lia]].
  Qed.

  Theorem target_run_proof : target_run_stmt HO K sites_of sites.
  Proof using FREE FUZZ HFL MALLOC SFL HCB SCB VPR. pin_using (fun (FREE FUZZ HFL MALLOC SFL HCB SCB VPR : unit) => tt). ceil_facts.
    unfold target_run_stmt.
    intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m R s CL lo A L content.
    intros (G & ST & LOLO & BUD & SPM & MI & Etp & ALN) Hcb SITES SRC HL0 HL6 HLEN HINB Ea0 Ea1 Ea2 Ea3.
    pose proof BUD as BUD'. unfold TARGET_RUN_STACK, FUZZ_STACK, STDIO_STACK in BUD'.
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
    pose proof (bytes_at_bound _ _ _ _ SRC) as SB.
    pose proof (GI_spw K _ _ _ _ G) as SPW. pose proof (GI_ceil_lo K _ _ _ _ G) as CLO__. unfold rc_lo in CLO__. pose proof LOLO as LOLO'. unfold rc_lo in LOLO'. pose proof SPM as SPM'. unfold rc_spmain in SPM'.
    destruct (client_range_bounds K _ _ _ _ A (Z.of_nat (length content)) G HINB ltac:(lia)) as (SRC0 & SRCHI & SRCI & SRCT).
    (* [comment removed for export] *)
    assert (exists b0 b1 b2 rest, content = b0 :: b1 :: b2 :: rest) as (b0 & b1 & b2 & rest & EC).
    { destruct content as [|x0 [|x1 [|x2 r]]]; [cbn in HL6; lia..|]. repeat eexists. }
    unfold TARGET_RUN_ENTRY. unfold run, target_run.
    set (pl := skipn (Z.to_nat (6 + L)) (map bv_unsigned content)).
    set (cfg := firstn (Z.to_nat L) (skipn 2 (map bv_unsigned content))).
    set (k := Z.to_nat (1 + Z.land (match cfg with [] => 0 | b :: _ => b end) 3)).
    set (plen := (Z.of_nat (length content) - 6 - L)%Z) in *.
    set (src := skipn (Z.to_nat (6 + L)) content).
    assert (Epl : pl = map bv_unsigned src). { subst pl src. rewrite skipn_map. reflexivity. }
    assert (Hsrc : length src = Z.to_nat plen). { subst src plen. rewrite length_skipn. lia. }
    assert (SRCp : bytes_at usegs m (A + 6 + L) src).
    { subst src. pose proof SRC as SRC2. rewrite <- (firstn_skipn (Z.to_nat (6 + L)) content) in SRC2. apply bytes_at_app in SRC2 as [_ S2].
      rewrite length_firstn in S2. replace (A + Z.of_nat (Nat.min (Z.to_nat (6 + L)) (length content)))%Z with (A + 6 + L)%Z in S2 by lia. exact S2. }
    assert (HINP : forall a, (A + 6 + L <= a < A + 6 + L + Z.of_nat (length src))%Z -> in_block CL a).
    { intros a Ha. apply HINB. lia. }
    assert (Hk : (1 <= k <= 4)%nat). { subst k. pose proof (land3_range (match cfg with [] => 0 | b :: _ => b end)). lia. }
    change (Z.to_nat (1 + Z.land (match cfg with [] => 0 | b :: _ => b end) 3)) with k.
    rewrite Epl.
    subst a0 a1 a2 a3 tp.
    (* [comment removed for export] *)
    destruct (GI_atx K _ _ _ _ G) as (reg & pad & f0 & g0 & j1 & j2 & FL & ATXc & BLT & REG). rewrite Hcb in FL.
    destruct (GI_core K _ _ _ _ G) as (_ & _ & (LC & _) & _ & _ & _).
    destruct (GI_initflag K _ _ _ _ G) as [_ GLI].
    unfold atexit_cells, builtin_cells in ATXc, BLT. unfold libc_cells in LC.
    pose proof (munch_refl [(0x34150, 0x34155); (0x542a0, 0x544c0); (bv_unsigned sp - 128, bv_unsigned sp)]%Z m) as MU.
    pose proof (wmono_refl usegs m) as WM.
    unfold implM. iprefix.
    carve_frame 80%nat ST.
    do 17 lstep.
    call_sp reg_spec; [exact ST | exact FL | exact ATXc | exact BLT | exact REG | exact LC | exact GLI | exact MI | lia | lia | reflexivity | reflexivity |].
    rename MI0 into MI.
    lazymatch goal with H : stk usegs _ lo _ |- _ => rename H into ST end.
    (* [comment removed for export] *)
    lazymatch type of MU with munch _ _ ?mb =>
      assert (G1 : GI K R s CL mb);
      [ rewrite <- (set_cb_same R); rewrite Hcb;
        eapply (GI_atx_frame K HFL SFL HCB SCB); [exact G | exact MU | exact WM | constructor; [left; cbn [fst snd]; unfold rc_lo, rc_spmain; lia | constructor] |];
        exists true, pad; do 4 eexists; split; [eassumption|]; split; [eassumption|]; split; [eassumption| intros _; split; reflexivity]
      | assert (AG0 : agrees_on (client_keeps CL (bv_unsigned sp)) m mb);
        [ eapply (keeps_of_munch K); [exact G | exact MU | exact WM | | lia];
          constructor; [right; cbn [fst snd]; lia | constructor; [right; cbn [fst snd]; lia | constructor; [left; cbn [fst snd]; lia | constructor]]] | ] ]
    end.
    clear MU WM.
    (* [comment removed for export] *)
    assert (TAIL : forall r s' ms' m1, agrees_on (client_keeps CL (bv_unsigned sp)) m m1 ->
              tr_post ra sp gp (rc_tp R) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc R CL lo (bv_unsigned sp + -80) m1 r s' ms' ->
              target_run_post K ra sp gp (rc_tp R) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc R CL lo m r s' ms').
    { intros r s' ms' m1 AGa PO. unfold tr_post in PO. destruct_exs PO. destruct PO as (-> & MIf & STf & AGf & Gf & Hr).
      unfold target_run_post. repeat (lazymatch goal with |- ex _ => eexists end).
      split; [reflexivity|]. split; [exact MIf|]. split; [exact STf|]. split; [| split; [exact Gf| exact Hr]].
      eapply keeps_trans; [exact AGa | exact AGf | lia | intros a Ha; exact Ha]. }
    lstep.
    destruct (Z.eq_dec L 0) as [EL|NL].
    - (* [comment removed for export] *)
      assert (Ek : k = 1%nat). { subst k cfg. rewrite EL. reflexivity. }
      replace (Z_to_bv 64 L) with z64 by (rewrite EL; reflexivity). if_true. lstep. lstep.
      destruct (Z.eq_dec plen 0) as [EP|NP].
      + replace (Z_to_bv 64 plen) with z64 by (rewrite EP; reflexivity). if_false.
        assert (Esrc : src = []). { destruct src; [reflexivity| rewrite EP in Hsrc; cbn in Hsrc; lia]. }
        rewrite Esrc. apply evt_done. eapply (implM_mono usegs).
        * eapply path_empty with (lo := lo); [exact Hk | exact G1 | exact Hcb | exact ST | exact LOLO | unfold FUZZ_STACK, STDIO_STACK; lia | exact SPM | exact MI | reflexivity
            | reflexivity | rewrite Ek; reflexivity | reflexivity | exact FR | aln | exact SITES].
        * intros r s' ms'. apply TAIL. exact AG0.
      + if_true_by (nez_cond plen ltac:(lia)).
        apply evt_done. eapply (implM_mono usegs).
        * eapply path_alloc with (lo := lo) (P := (A + 6 + L)%Z); [exact Hk | exact G1 | exact Hcb | exact ST | exact LOLO | unfold FUZZ_STACK, STDIO_STACK; lia | exact SPM | exact MI | reflexivity
            | f_equal; lia | reflexivity | rewrite Ek; reflexivity | reflexivity | lia | lia | exact SRCp | exact HINP | exact FR | aln | exact SITES].
        * intros r s' ms'. apply TAIL. exact AG0.
    - (* [comment removed for export] *)
      assert (Ek : (Z.of_nat k = Z.land (bv_unsigned b2) 3 + 1)%Z).
      { subst k cfg. rewrite EC. replace (Z.to_nat L) with (S (Z.to_nat (L - 1))) by lia. cbn [map skipn firstn].
        pose proof (land3_range (bv_unsigned b2)). lia. }
      if_false_by (eqz_cond_false L ltac:(lia)).
      pose proof SRC as SRC3. rewrite EC in SRC3.
      pose proof (bytes_at_read usegs _ A _ 2 1 SRC3 ltac:(lia) ltac:(cbn; lia)) as HR. clear SRC3.
      change (Z.to_nat 2) with 2%nat in HR. cbn [firstn skipn] in HR.
      lstep. lstep. lstep. lstep.
      destruct (Z.eq_dec plen 0) as [EP|NP].
      + replace (Z_to_bv 64 plen) with z64 by (rewrite EP; reflexivity). if_true.
        assert (Esrc : src = []). { destruct src; [reflexivity| rewrite EP in Hsrc; cbn in Hsrc; lia]. }
        rewrite Esrc. apply evt_done. eapply (implM_mono usegs).
        * eapply path_empty with (lo := lo); [exact Hk | exact G1 | exact Hcb | exact ST | exact LOLO | unfold FUZZ_STACK, STDIO_STACK; lia | exact SPM | exact MI | reflexivity
            | reflexivity | f_equal; lia | reflexivity | exact FR | aln | exact SITES].
        * intros r s' ms'. apply TAIL. exact AG0.
      + if_false_by (eqz_cond_false plen ltac:(lia)).
        apply evt_done. eapply (implM_mono usegs).
        * eapply path_alloc with (lo := lo) (P := (A + 6 + L)%Z); [exact Hk | exact G1 | exact Hcb | exact ST | exact LOLO | unfold FUZZ_STACK, STDIO_STACK; lia | exact SPM | exact MI | reflexivity
            | f_equal; lia | reflexivity | f_equal; lia | reflexivity | lia | lia | exact SRCp | exact HINP | exact FR | aln | exact SITES].
        * intros r s' ms'. apply TAIL. exact AG0.
  Qed.
End TargetRun.

End WithCeil.
End TwB.
End F_target_run.

(* [comment removed for export] *)
Module Ifaces47.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Sem.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import Tac Arr Bytes ITree Nodes Decode SysStep ImgSrc3.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Prelim Monad Fmt StdioCore Stdio PcapPrelim PcapTypes PcapPure Pcap. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Adapter__Spec. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Prog. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Monad OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Fmt OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.StdioCore OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Stdio OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapPrelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapTypes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapPure OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Pcap OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Adapter__Spec.Driver OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Adapter__Spec.Adapter OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prog.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require InitMem. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require Printf_kit__Musl. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require FileCells__Musl. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.InitMem OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_kit__Musl.StartupKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.FileCells__Musl.FileCells.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require Exit__S3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require GI. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require GIFacts__S3. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Startup_B__S3.Startup OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Exit__S3.Exit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.GI OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.GIFacts__S3.Ifaces.
From OSSVerify.libpcap.fuzz_pcap.images Require Import Plain.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import LiaPin.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac lia ::= pinned_lia.
Import ListNotations.
Open Scope Z_scope.

Section WithCeil.
Context {CEILV : CEIL}.
Section Ifaces47.
  Context {H hptr : Type} (K : modkit H hptr).
  Notation cblk := (@cblock hptr).
  Notation PS := (PState H hptr).

  Definition eprintf_s_stmt47 (FMT : Z) (mk : list Z -> list (list Z)) : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (R : rctx) (s : PS) (CL : list cblk) (lo P : Z) (str slack : list byte),
      std_pre K sp tp R s CL lo STDIO_STACK m ->
      a0 = Z_to_bv 64 STDERR_FILE -> a1 = Z_to_bv 64 FMT -> a2 = Z_to_bv 64 P ->
      bytes_at ssegs m P (str ++ Z_to_bv 8 0 :: slack) -> ~ In (Z_to_bv 8 0) str -> Z.of_nat (length str) < 2^24 ->
      (- (P + Z.of_nat (length str) + 1)) mod 8 <= Z.of_nat (length slack) ->   (* [comment removed for export] *)
      (forall a, P <= a < P + Z.of_nat (length str) + 1 -> client_keeps CL (bv_unsigned sp) a) ->
      P + Z.of_nat (length str) + 1 <= 2^47 ->                                   (* [comment removed for export] *)
      implM ssegs (@eprintf PS hptr ps_libc set_libc (mk (map bv_unsigned str))) s
        (out_post K ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc R CL lo m)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 FPRINTF_ENTRY) fc None m (seg_rom ssegs)).

  (* [comment removed for export] *)
  Lemma eprintf_s_stmt47_of : forall FMT mk, eprintf_s_stmt K FMT mk -> eprintf_s_stmt47 FMT mk.
  Proof using Type. pin_using tt. intros FMT mk HS. unfold eprintf_s_stmt47. intros. eapply HS; eassumption. Qed.
End Ifaces47.
End WithCeil.

(* [comment removed for export] *)
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require ImgTgtUbsan.
From OSSVerify.libpcap.fuzz_pcap.images Require Ubsan.
Module TwB.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Sem.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Tac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Arr OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Bytes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ITree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Nodes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Decode OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.SysStep OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ImgTgtUbsan.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Monad OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Fmt OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.StdioCore OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Stdio OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapPrelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapTypes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapPure OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Pcap OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Adapter__Spec.Driver OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Adapter__Spec.Adapter OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prog.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.InitMem OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_kit__Musl.StartupKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.FileCells__Musl.FileCells.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Startup_B__S3.Startup.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Exit__S3.Exit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.GI.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.GIFacts__S3.Ifaces.TwB.
Import OSSVerify.libpcap.fuzz_pcap.images.Ubsan.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.LiaPin.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac lia ::= pinned_lia.
Import ListNotations.
Open Scope Z_scope.

Section WithCeil.
Context {CEILV : CEIL}.
Section Ifaces47.
  Context {H hptr : Type} (K : modkit H hptr).
  Notation cblk := (@cblock hptr).
  Notation PS := (PState H hptr).

  Definition eprintf_s_stmt47 (FMT : Z) (mk : list Z -> list (list Z)) : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (R : rctx) (s : PS) (CL : list cblk) (lo P : Z) (str slack : list byte),
      std_pre K sp tp R s CL lo STDIO_STACK m ->
      a0 = Z_to_bv 64 STDERR_FILE -> a1 = Z_to_bv 64 FMT -> a2 = Z_to_bv 64 P ->
      bytes_at usegs m P (str ++ Z_to_bv 8 0 :: slack) -> ~ In (Z_to_bv 8 0) str -> Z.of_nat (length str) < 2^24 ->
      (- (P + Z.of_nat (length str) + 1)) mod 8 <= Z.of_nat (length slack) ->   (* [comment removed for export] *)
      (forall a, P <= a < P + Z.of_nat (length str) + 1 -> client_keeps CL (bv_unsigned sp) a) ->
      P + Z.of_nat (length str) + 1 <= 2^47 ->                                   (* [comment removed for export] *)
      implM usegs (@eprintf PS hptr ps_libc set_libc (mk (map bv_unsigned str))) s
        (out_post K ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc R CL lo m)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 FPRINTF_ENTRY) fc None m (seg_rom usegs)).

  (* [comment removed for export] *)
  Lemma eprintf_s_stmt47_of : forall FMT mk, eprintf_s_stmt K FMT mk -> eprintf_s_stmt47 FMT mk.
  Proof using Type. pin_using tt. intros FMT mk HS. unfold eprintf_s_stmt47. intros. eapply HS; eassumption. Qed.
End Ifaces47.
End WithCeil.
End TwB.
End Ifaces47.

(* [comment removed for export] *)
Module F_ngnextB.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool String.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import Tac Arr Bytes ZBridge ITree Nodes Decode SysStep MonadX Image ImgSrc3.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Prelim Monad Fmt StdioCore Stdio PcapPrelim PcapTypes PcapPure Pcap Prog. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Adapter__Spec. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Monad OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Fmt OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.StdioCore OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Stdio OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapPrelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapTypes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapPure OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Pcap OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prog OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Adapter__Spec.StartupModel.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require AmoStep__Musl. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require Printf_kit__Musl. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.STRW_tac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_kit__Musl.StartupKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.CellsExtra.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require FmtFacts__S3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require GI PcapRep. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require Pcap_iface__S3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_lock__S3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_memchr__S3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_sfpcapng_blkA__S3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_ngnextA. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.FmtFacts__S3.FmtFacts OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.GI OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.PcapRep OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Pcap_iface__S3.Pcap_iface OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_lock__S3.Pcap_iface_pp OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Pcap_iface__S3.Pcap_iface_ng OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_memchr__S3.SfKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcapng_blkA__S3.SfNgKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.FmtFacts__S3.PPFacts OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_lock__S3.PP_kit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_ngnextA.
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
Local Ltac gio_ceil_fact :=
  match goal with
  | G : GIo _ _ _ _ _ _ |- _ => let H := fresh "CLO__" in pose proof (PcapRep.GIo_ceil_lo _ _ _ _ _ _ G) as H; unfold rc_lo in H
  end.
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
Lemma pfx_split : forall (data : list Z) (bs : list byte) (k : nat),
  firstn (length data) bs = map b8 data -> (k <= length data)%nat ->
  firstn k bs = map b8 (firstn k data) /\ firstn (length data - k) (skipn k bs) = map b8 (skipn k data).
Proof using Type. pin_using tt.
  intros data bs k PFX Hk. split.
  - rewrite <- firstn_map. rewrite <- PFX. rewrite firstn_firstn. f_equal. lia.
  - rewrite <- skipn_map. rewrite <- PFX. rewrite skipn_firstn_comm. reflexivity.
Qed.

Lemma bytes_wr_rw_cells : forall mx A l, bytes_at ssegs mx A l -> wr_at ssegs mx A (Z.of_nat (length l)) -> rw_cells ssegs mx A [CB (length l) l].
Proof using Type. pin_using tt. intros mx A l HB HW. split; [split; [cbn; split; [reflexivity| exact Logic.I] | cbn [cells_bytes cbytes]; rewrite app_nil_r; exact HB] | cbn [cells_size csize Nat.add]; rewrite Nat.add_0_r; exact HW]. Qed.

Section NgnCtx.
  Context {H hptr : Type} (HO : HeapOps H hptr) (K : modkit H hptr) (sites : stack_site -> Z).
  Hypothesis HFL : heap_frame_law K.
  Hypothesis SFL : stdio_fp_law K.
  Hypothesis HPL : heap_perm_law K.
  Hypothesis HAL : heap_addr_law K HO.
  Hypothesis SNPRINTF : snprintf_spec_stmt K.
  Hypothesis PP : post_process_stmt.
  Hypothesis ADJ : adjust_snapshot_stmt.
  Hypothesis RBLK : read_block_stmt HO K sites.
  Hypothesis ADDIF : add_interface_stmt HO K sites.

  (* [comment removed for export] *)
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
  Variables (R : rctx) (CLc FB : list (cblock (hptr:=hptr))) (lo P HA DA Af : Z) (m : mem) (o : option hptr).
  Variables (self f : hptr) (bufsize : Z) (swapped : bool) (vmaj vmin snapshot linktype ltext prec brk : Z) (header : pkthdr).
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
  Hypothesis P1 : (0 < P)%Z.  Hypothesis P2 : (P mod 16 = 0)%Z.  Hypothesis P4 : (P + 680 <= CEILZ)%Z.
  Hypothesis P5 : (P + 680 <= 65536 \/ 348160 <= P)%Z.  Hypothesis P6 : (P + 680 <= utp R - 200 \/ utp R - 200 + 4096 <= P)%Z.
  Hypothesis A1 : (0 < Af)%Z.  Hypothesis A4 : (Af + 1264 <= CEILZ)%Z.
  Hypothesis W1 : (1 <= snapshot <= INT_MAX)%Z.  Hypothesis W2 : (0 <= bufsize <= 2^30)%Z.
  Hypothesis W5 : brk = 0%Z.  Hypothesis W6 : prec = 0%Z.
  Hypothesis W7 : (0 <= vmaj < 2^16)%Z.  Hypothesis W8 : (0 <= vmin < 2^16)%Z.
  Hypothesis W9 : (0 <= linktype < 2^31)%Z.  Hypothesis W10 : (-2^31 <= ltext < 2^31)%Z.

  Let POSTQ := next_packet_post K ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc R CLc FB lo P HA DA m o.

  (* [comment removed for export] *)
  #[local] Abbreviation pv := (F_ngnextA.pv self f bufsize swapped vmaj vmin snapshot linktype ltext prec brk header).
  #[local] Abbreviation ngn_frame := (F_ngnextA.ngn_frame ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 P HA DA).
  #[local] Abbreviation ngn_final := (F_ngnextA.ngn_final K sp R CLc FB P HA DA m o).
  #[local] Abbreviation ngn_finalC := (F_ngnextA.ngn_finalC K sp R CLc FB P HA DA m o).
  #[local] Abbreviation ngn_final_C := (F_ngnextA.ngn_final_C K sp R CLc FB P HA DA m o).
  #[local] Abbreviation ngn_ret_m1 := (F_ngnextA.ngn_ret_m1 K ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc R CLc FB lo P HA DA m o BU).
  #[local] Abbreviation ngn_ret_0 := (F_ngnextA.ngn_ret_0 K ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc R CLc FB lo P HA DA m o BU).
  #[local] Abbreviation ngn_ret_1 := (F_ngnextA.ngn_ret_1 K ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc R CLc FB lo P HA DA m o BU).
  #[local] Abbreviation ngn_CLc_facts := (F_ngnextA.ngn_CLc_facts K R CLc FB).
  #[local] Abbreviation ngn_snp_call := (F_ngnextA.ngn_snp_call K HFL SFL SNPRINTF ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc R CLc FB lo P HA DA m o LO BU SPM TP ALN R1 R2 AH AD SPW P1 P4 P5).
  #[local] Abbreviation ngn_snp := (F_ngnextA.ngn_snp K HFL SFL SNPRINTF ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc R CLc FB lo P HA DA m o LO BU SPM TP ALN R1 R2 AH AD SPW P1 P4 P5).
  #[local] Abbreviation ngn_mcp := (F_ngnextA.ngn_mcp K HFL SFL ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc R CLc FB lo P HA DA m o LO BU ALN R1 R2 AH AD SPW P1 P4 P5 P6).
  #[local] Abbreviation PCAPRC_errbuf := (F_ngnextA.PCAPRC_errbuf K sp R lo P HA DA LO BU ALN R1 R2 AH AD SPW P1).

  Ltac norm_g :=
    unfold F_ngnextA.pv; unfold pcap_blocks; unfold psize; unfold is_ng;
    cbn [pc_self pc_rfile pc_bufsize pc_bufalloc pc_buffer pc_bufdata pc_swapped pc_version_major pc_version_minor pc_snapshot pc_linktype
         pc_linktype_ext pc_tstamp_precision pc_break_loop pc_errbuf pc_header pc_priv priv_cells ng_of ng_ifaces_ptr_of
         set_bufdata set_errbuf set_buffer set_ng set_priv];
    unfold PCAP_NG_SF_TOTAL, PCAP_PRIV_OFF.
  Ltac norm_p :=
    unfold F_ngnextA.pv in *; unfold pcap_blocks in *; unfold psize in *; unfold is_ng in *;
    cbn [pc_self pc_rfile pc_bufsize pc_bufalloc pc_buffer pc_bufdata pc_swapped pc_version_major pc_version_minor pc_snapshot pc_linktype
         pc_linktype_ext pc_tstamp_precision pc_break_loop pc_errbuf pc_header pc_priv priv_cells ng_of ng_ifaces_ptr_of
         set_bufdata set_errbuf set_buffer set_ng set_priv] in *;
    unfold PCAP_NG_SF_TOTAL, PCAP_PRIV_OFF in *.

  (* [comment removed for export] *)
  Definition ngn_pp__stmt : Prop := forall (ra' t0' t1' t2' x0 x1 a0' a1' a2' a3' a4' a6' a7' x2 x3 x5 x6 x7 x8 x9 x10 x11 t4' t5' t6' ws wu : word) (m5 : mem) (ps : PState H hptr)
           (bq : hptr) (Bq Ix alloc doff : Z) (data eb : list Z) (sx : pcap_ng_sf) (ix : option hptr) (sec usec cap len : Z) (dw : cell) (dj : list byte) (ccs : list cell),
      stk ssegs m5 lo (bv_unsigned sp + -160) ->
      rw_cells ssegs m5 (bv_unsigned sp + -160) (ngn_frame dj ccs) -> cells_size ccs = 24%nat -> mem_inv ssegs m5 ->
      GIo K R ps (CLc ++ pcap_blocks (pv bq alloc data eb sx ix) P Bq Ix) FB m5 ->
      PCAPR (hptr:=hptr) P (pv bq alloc data eb sx ix) (pcap_blocks (pv bq alloc data eb sx ix) P Bq Ix) FB m5 ->
      agrees_on (fun a => client_keeps CLc (bv_unsigned sp) a /\ ~ (HA <= a < HA + 24) /\ ~ (DA <= a < DA + 8))%Z m m5 ->
      rw_cells ssegs m5 HA [C8 ws; C8 wu; C4 (Z_to_bv 64 cap); C4 (Z_to_bv 64 len)] -> rw_cells ssegs m5 DA [dw] -> csize dw = 8%nat ->
      ws = Z_to_bv 64 sec -> wu = Z_to_bv 64 usec -> Forall (fun x => 0 <= x < 256)%Z data ->
      (0 <= doff <= Z.of_nat (length data))%Z -> (doff mod 4 = 0)%Z ->
      (0 <= cap <= Z.of_nat (length data) - doff)%Z -> (Z.of_nat (length data) < 2^31)%Z -> (0 <= len < 2^32)%Z -> ps_outfile ps = o ->
      implM ssegs (let '(hdr, d) := pcapint_post_process linktype swapped (mkHdr sec usec cap len) (zskipn doff data) in
                   mret (1%Z, hdr, set_bufdata (zfirstn doff data ++ d) (pv bq alloc data eb sx ix))) ps POSTQ
        (MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -160)) gp tp t0' t1' t2' x0 x1 a0' a1' a2' a3' a4' (Z_to_bv 64 (Bq + doff)) a6' a7'
                 x2 x3 (Z_to_bv 64 P) x5 x6 x7 x8 x9 x10 x11 (Z_to_bv 64 HA) t4' t5' t6') F (Z_to_bv 64 0x17ac4) fc None m5 (seg_rom ssegs)).
  Section Sz3.
  Variables ra' t0' t1' t2' x0 x1 a0' a1' a2' a3' a4' a6' a7' x2 x3 x5 x6 x7 x8 x9 x10 x11 t4' t5' t6' ws wu m5 ps bq Bq Ix alloc doff data eb sx ix sec usec cap len dw dj ccs : ltac2:(SecDiet.SzSec.tyM 'ngn_pp__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra').
  Lemma ngn_pp__body : ltac2:(SecDiet.SzSec.bodyP 'ngn_pp__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof using AD AH BU HFL LO P1 P2 P4 P5 P6 PP R1 R2 R3 SFL SP47 SPM SPW W1 W10 W2 W5 W6 W7 W8 W9. pin_using (fun (AD AH BU HFL LO P1 P2 P4 P5 P6 PP R1 R2 R3 SFL SP47 SPM SPW W1 W10 W2 W5 W6 W7 W8 W9 : unit) => tt).
    intros ST5 FR5 Hccs MI5 G5 PC5 AG5 HH HD Hd -> -> DRNG Hdoff Hd4 Hcap Hl31 Hlen OF5.
    pose proof (bv_unsigned_in_range 64 sp) as RSP.
    destruct PC5 as (Afx & Hin & (Bx' & Ix' & jx' & padx & bsx' & EPB & CELLS & PRIV & BUF & PFX & IFS & WF)).
    rewrite EPB in G5.
    pose proof (PB_apart K _ _ _ _ _ _ _ _ _ _ G5 eq_refl) as [APB API].
    pose proof (GIo_PB_block K _ _ _ _ _ _ _ _ _ G5 ltac:(right; left; reflexivity)) as (K1 & K2 & K3 & K4 & K5 & K6).
    norm_p.
    assert (EBX : Bx' = Bq) by congruence. subst Bx'. clear EPB.
    pose proof WF as (W1' & W2' & W3 & W4 & _ & _ & _ & _ & _ & _ & _ & _ & (UT & WMB & WIC & WIS) & WBB). cbn [pc_bufsize pc_bufalloc pc_bufdata length] in W3, W4, WBB.
    unfold pcap_cells_gen, pc_pre, hdr_cells, pc_ops, np_entry, cleanup_entry, is_ng, PCAP_PRIV_OFF in CELLS.
    cbn [app pc_bufsize pc_break_loop pc_swapped pc_version_major pc_version_minor pc_snapshot pc_linktype pc_linktype_ext pc_tstamp_precision pc_header pc_priv pk_next_ng pk_cleanup_ng PK] in CELLS.
    destruct (rw_cells_forget _ _ _ _ HD) as [dwj HD']. clear HD. cbn [cells_size] in HD'. rewrite Hd in HD'. change (8 + 0)%nat with 8%nat in HD'.
    (* [comment removed for export] *)
    apply (rw_cells_split_CB ssegs m5 _ [] (Z.to_nat alloc) _ [] [Z.to_nat doff; length data - Z.to_nat doff; Z.to_nat alloc - length data]%nat) in BUF; [| cbn; lia].
    cbn [mk_CB_cells app] in BUF.
    destruct (pfx_split data bsx' (Z.to_nat doff) PFX ltac:(lia)) as [E0 E1]. rewrite E0, E1 in BUF.
    destruct (rw_cells_cut _ _ _ 1 BUF) as [BD0 BUF']. cbn [firstn skipn cells_size csize Nat.add] in BD0, BUF'.
    destruct (rw_cells_cut _ _ _ 1 BUF') as [BD BT]. clear BUF BUF'. cbn [firstn skipn cells_size csize Nat.add] in BD, BT.
    replace (Bq + Z.of_nat (Z.to_nat doff + 0))%Z with (Bq + doff)%Z in BD, BT by lia.
    replace (Bq + doff + Z.of_nat (length data - Z.to_nat doff + 0))%Z with (Bq + Z.of_nat (length data))%Z in BT by lia.
    pose proof FR5 as FRJ. unfold F_ngnextA.ngn_frame in FRJ. apply rw_cells_app in FRJ as [FRJ _]. 
    hide BD0. hide BD. hide BT. hide PRIV. hide IFS. hide HH. hide FR5.
    pose proof (munch_refl [(DA, DA + 8)]%Z m5) as MU. pose proof (wmono_refl ssegs m5) as WM.
    unfold implM. iprefix.
    step. rewrite (sx32_small (Z.b2z swapped)) by (destruct swapped; cbn; lia).
    step. rewrite (sx32_small linktype) by lia.
    step. step. step. step. step.
    unhide BD0. unhide BD. unhide BT. unhide PRIV. unhide IFS. unhide HH. unhide FR5. clear FRJ.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      assert (AGD : agrees_on (fun a => outside [(DA, DA + 8)]%Z a) m5 mm) by (eapply agrees_on_of_munch; [exact MU | exact WM | intros a _ Ho; exact Ho]);
      rename mm into m5' end.
    assert (T0 : forall A cs, rw_cells ssegs m5 A cs -> (A + Z.of_nat (cells_size cs) <= DA \/ DA + 8 <= A)%Z -> rw_cells ssegs m5' A cs).
    { intros A cs HC HA'. eapply agrees_rw_cells; [exact AGD | exact HC | intros a Ha; cbn [outside]; lia]. }
    apply T0 in BD0; [| cbn [cells_size csize Nat.add]; unfold rc_lo in LO; lia].
    apply T0 in BD; [| cbn [cells_size csize Nat.add]; unfold rc_lo in LO; lia].
    apply T0 in BT; [| cbn [cells_size csize Nat.add]; unfold rc_lo in LO; lia].
    apply T0 in PRIV; [| cbn [cells_size csize Nat.add ng_cells]; unfold rc_lo in LO; lia].
    apply T0 in HH; [| cbn [cells_size csize Nat.add]; lia].
    apply T0 in FR5; [| unfold F_ngnextA.ngn_frame; rewrite !cells_size_app; cbn [cells_size csize Nat.add]; rewrite Hccs; lia].
    assert (IFS' : ifaces_ok (pv bq alloc data eb sx ix) Ix' m5').
    { eapply ifaces_ok_agree; [exact AGD| | exact IFS]. intros sg q Hq a Ha. cbn [outside].
      cbn [pc_priv] in Hq. injection Hq as Esx Eix. subst sg ix.
      pose proof (GIo_PB_block K _ _ _ _ _ _ _ _ _ G5 ltac:(unfold pcap_blocks; cbn [pc_priv]; right; right; left; reflexivity)) as (I1 & I2 & I3 & I4 & I5 & I6).
      unfold rc_lo in LO. lia. }
    clear IFS T0.
    rename ST5 into ST5'.
    assert (G5' : GIo K R ps (CLc ++ pcap_blocks (pv bq alloc data eb sx ix) P Bq Ix') FB m5').
    { eapply (GIo_pcap_frame K HFL SFL); [exact G5 | exact MU | exact WM |]. apply Forall_cons; [left; cbn [fst snd]; unfold rc_lo; lia| apply Forall_nil]. }
    assert (AG5' : agrees_on (fun a => client_keeps CLc (bv_unsigned sp) a /\ ~ (HA <= a < HA + 24) /\ ~ (DA <= a < DA + 8))%Z m m5').
    { eapply agrees_on_trans; [exact AG5|]. eapply agrees_on_weaken; [exact AGD|]. intros a [_ [_ Hn]]; cbn [outside]; lia. }
    lazymatch goal with |- context [mem_inv ssegs m5'] => idtac | _ => idtac end.
    assert (MI5' : mem_inv ssegs m5') by assumption.
    clear MU WM AGD G5 AG5.
    assert (ZA : zarr m5' (Bq + doff) (zskipn doff data)).
    { unfold zskipn. split; [| split; [| apply Forall_range_skipn; exact DRNG]].
      - pose proof (rw_cells_bytes_at _ _ _ _ BD) as X. cbn [cells_bytes cbytes] in X. rewrite app_nil_r in X. exact X.
      - eapply rw_cells_wr_at; [exact BD|]. cbn [cells_size csize Nat.add]. rewrite length_skipn. lia. }
    change (rw_cells ssegs m5' HA (pkthdr_cells (Z_to_bv 64 sec) (Z_to_bv 64 usec) (mkHdr sec usec cap len))) in HH.
    assert (LD : Z.of_nat (length (zskipn doff data)) = (Z.of_nat (length data) - doff)%Z) by (unfold zskipn; rewrite length_skipn; lia).
    name_sp sp (-160)%Z.
    eapply evt_cut.
    { eapply PP; [rewrite Hsp; exact ST5' | unfold PP_FRAME; rewrite Hsp; lia | exact HH | exact ZA | exact MI5' | reflexivity | reflexivity | reflexivity | reflexivity
                 | lia | cbn [h_caplen]; lia | lia | cbn [h_len]; lia | left; rewrite Hsp; lia | right; unfold rc_lo in LO; lia | unfold PP_FRAME; rewrite Hsp; unfold rc_lo in LO; lia
                 | exact AH | clear -K2 Hd4; Z.div_mod_to_equations; lia | unfold rc_spmain in R3; lia | lia | unfold rc_lo in LO; lia | lia ]. }
    cbv beta. intros ms' PO. destruct PO as (y0 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & y8 & y9 & y10 & y11 & y12 & y13 & y14 & m6 & -> & MU6 & WM6 & MI6 & ST6 & HH6 & ZA6).
    rewrite Hsp in *. unname_sp.
    replace (ret_pc (Z_to_bv 64 96992)) with (Z_to_bv 64 96992) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
    cbn [h_caplen] in MU6. unfold PP_FRAME in MU6.
    set (hdr' := fst (pcapint_post_process linktype swapped (mkHdr sec usec cap len) (zskipn doff data))) in *.
    set (d' := snd (pcapint_post_process linktype swapped (mkHdr sec usec cap len) (zskipn doff data))) in *.
    pose proof (pp_length linktype swapped (mkHdr sec usec cap len) (zskipn doff data)) as LEN'. fold d' in LEN'.
    pose proof (pp_sec linktype swapped (mkHdr sec usec cap len) (zskipn doff data)) as [SEC' USEC']. fold hdr' in SEC', USEC'. cbn [h_sec h_usec] in SEC', USEC'.
    pose proof (pp_range linktype swapped (mkHdr sec usec cap len) (zskipn doff data) ltac:(cbn [h_caplen]; lia) ltac:(cbn [h_len]; lia) ltac:(lia)) as [RC' RL']. fold hdr' in RC', RL'.
    assert (AGS : agrees_on (fun a => outside [(bv_unsigned sp + -160 - 32, bv_unsigned sp + -160); (HA + 20, HA + 24); (Bq + doff, Bq + doff + cap)]%Z a) m5' m6)
      by (eapply agrees_on_of_munch; [exact MU6 | exact WM6 | intros a _ Ho; exact Ho]).
    apply (agrees_rw_cells _ _ _ _ _ AGS) in FR5; [| intros a Ha; unfold F_ngnextA.ngn_frame in Ha; rewrite !cells_size_app in Ha; cbn [outside cells_size csize Nat.add] in *; rewrite Hccs in Ha; unfold rc_lo in LO; lia].
    apply (agrees_rw_cells _ _ _ _ _ AGS) in HD'; [| intros a Ha; cbn [outside cells_size csize Nat.add] in *; unfold rc_lo in LO; lia].
    apply (agrees_rw_cells _ _ _ _ _ AGS) in CELLS; [| intros a Ha; cbn [outside cells_size csize Nat.add] in *; unfold rc_lo in LO; lia].
    apply (agrees_rw_cells _ _ _ _ _ AGS) in PRIV; [| intros a Ha; cbn [outside cells_size csize Nat.add ng_cells] in *; unfold rc_lo in LO; lia].
    apply (agrees_rw_cells _ _ _ _ _ AGS) in BT; [| intros a Ha; cbn [outside cells_size csize Nat.add] in *; unfold rc_lo in LO; lia].
    apply (agrees_rw_cells _ _ _ _ _ AGS) in BD0; [| intros a Ha; cbn [outside cells_size csize Nat.add] in *; unfold rc_lo in LO; lia].
    assert (IFS6 : ifaces_ok (pv bq alloc data eb sx ix) Ix' m6).
    { eapply ifaces_ok_agree; [exact AGS| | exact IFS']. intros sg q Hq a Ha. cbn [outside]. pose proof (API sg q Hq) as [X1 X2].
      cbn [pc_priv] in Hq. injection Hq as Esx Eix. subst sg ix.
      pose proof (GIo_PB_block K _ _ _ _ _ _ _ _ _ G5' ltac:(unfold pcap_blocks; cbn [pc_priv]; right; right; left; reflexivity)) as (I1 & I2 & I3 & I4 & I5 & I6).
      cbn [pc_bufalloc] in X2. unfold rc_lo in LO. lia. }
    (* [comment removed for export] *)
    destruct ZA6 as (ZB & ZW & ZR).
    pose proof (bytes_wr_rw_cells _ _ _ ZB ltac:(rewrite zbytes_length; exact ZW)) as BD6. rewrite zbytes_length in BD6.
    pose proof (rw_cells_uncut _ _ _ _ _ BD6 BT ltac:(cbn [cells_size csize Nat.add]; rewrite LEN'; unfold zskipn; rewrite length_skipn; lia)) as BDT. cbn [app] in BDT.
    pose proof (rw_cells_uncut _ _ _ _ _ BD0 BDT ltac:(cbn [cells_size csize Nat.add]; lia)) as BUF6. cbn [app] in BUF6.
    merge_all BUF6.
    replace (Z.to_nat doff + (length d' + (Z.to_nat alloc - length data + 0)))%nat with (Z.to_nat alloc) in BUF6 by (rewrite LEN'; unfold zskipn; rewrite length_skipn; lia).
    rewrite app_nil_r in BUF6.
    rewrite (surjective_pairing (pcapint_post_process linktype swapped _ _)). fold hdr' d'.
    cbn [set_bufdata pc_self pc_rfile pc_bufsize pc_bufalloc pc_buffer pc_swapped pc_version_major pc_version_minor pc_snapshot pc_linktype pc_linktype_ext pc_tstamp_precision pc_break_loop pc_errbuf pc_header pc_priv].
    assert (G6 : GIo K R ps (CLc ++ pcap_blocks (pv bq alloc data eb sx ix) P Bq Ix') FB m6).
    { eapply (GIo_pcap_frame K HFL SFL); [exact G5' | exact MU6 | exact WM6 |].
      apply Forall_cons; [left; cbn [fst snd]; unfold rc_lo; lia|]. apply Forall_cons; [left; cbn [fst snd]; unfold rc_lo, rc_spmain in *; lia|].
      apply Forall_cons; [| apply Forall_nil]. right. unfold iv_in_block, pcap_blocks. apply Exists_cons_tl, Exists_cons_hd. cbn [cb_addr cb_size fst snd pc_buffer pc_bufalloc F_ngnextA.pv]. lia. }
    apply evt_done. eapply (ngn_ret_1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m6 ps (pcap_blocks (pv bq alloc data eb sx ix) P Bq Ix')
                             (pv bq alloc (zfirstn doff data ++ d') eb sx ix) hdr'); [exact ST6 | exact FR5 | exact Hccs | exact MI6 | | exact RC' | exact RL'].
    unfold F_ngnextA.ngn_final. norm_p.
    split; [exact G6|]. split.
    { exists Afx. split; [exact Hin|]. exists Bq, Ix', jx', padx, (map b8 (firstn (Z.to_nat doff) data) ++ zbytes d' ++ firstn (Z.to_nat alloc - length data) (skipn (length data - Z.to_nat doff) (skipn (Z.to_nat doff) bsx'))).
      norm_g.
      split; [reflexivity|]. split; [exact CELLS|]. split; [exact PRIV|]. split; [rewrite <- app_assoc in BUF6 || idtac; exact BUF6|].
      split. { unfold zfirstn. rewrite length_app, length_firstn, map_app.
               replace (Nat.min (Z.to_nat doff) (length data) + length d')%nat with (length (map b8 (firstn (Z.to_nat doff) data) ++ zbytes d')) by (rewrite length_app, length_map, length_firstn, zbytes_length; lia).
               rewrite app_assoc, firstn_app, firstn_all, Nat.sub_diag. cbn [firstn]. rewrite app_nil_r. reflexivity. }
      split; [exact IFS6|].
      unfold pcap_wf in *. cbn [pc_snapshot pc_bufsize pc_bufalloc pc_bufdata pc_break_loop pc_tstamp_precision pc_version_major pc_version_minor pc_linktype pc_linktype_ext pc_header pc_priv] in *.
      unfold zfirstn. rewrite length_app, length_firstn, LEN'.
      repeat split; try lia; try tauto. all: unfold zskipn; rewrite ?length_skipn; lia. }
    split. { eapply agrees_on_trans; [exact AG5'|]. eapply agrees_on_weaken; [exact AGS|]. intros a [[Ha|Ha] [Hn1 Hn2]]; cbn [outside]; [unfold rc_lo in LO; lia|].
             destruct (ngn_CLc_facts _ _ _ _ G5' Ha) as [Hc Hnb]. unfold rc_lo in LO. split; [lia|]. split; [lia|]. split; [| exact Logic.I].
             intros Hin'. apply Hnb. unfold pcap_blocks, in_block. apply Exists_cons_tl, Exists_cons_hd. cbn [cb_addr cb_size fst snd pc_buffer pc_bufalloc]. lia. }
    split. { unfold hdr_cells. rewrite SEC', USEC'. exact HH6. }
    split; [reflexivity|]. split; [exact HD'|]. split; [reflexivity| exact OF5].
  Qed.
  End Sz3.
  Lemma ngn_pp : ltac:(let t := eval cbv delta [ngn_pp__stmt] in ngn_pp__stmt in exact t).
  Proof using AD AH BU HFL LO P1 P2 P4 P5 P6 PP R1 R2 R3 SFL SP47 SPM SPW W1 W10 W2 W5 W6 W7 W8 W9. intros ra' t0' t1' t2' x0 x1 a0' a1' a2' a3' a4' a6' a7' x2 x3 x5 x6 x7 x8 x9 x10 x11 t4' t5' t6' ws wu m5 ps bq Bq Ix alloc doff data eb sx ix sec usec cap len dw dj ccs. ltac2:(SecDiet.SzSec.closeP 'ngn_pp__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.

  (* [comment removed for export] *)
  Definition ngn_tsK (fd : ng_found) (p : pcap hptr hptr) : M (PState H hptr) (Z * pkthdr * pcap hptr hptr) :=
    let ng := ng_of p in
    let interface_id := f_interface_id fd in
    let ifc := nth_slot (ng_ifaces ng) (ng_ifcount ng) interface_id in
    let t := f_t fd in
    let sec := u64 (t / if_tsresol ifc + if_tsoffset ifc) in
    let frac := t mod if_tsresol ifc in
    let frac := match if_scale_type ifc with
                | NG_PASS_THROUGH => frac
                | SCALE_UP_DEC => u64 (frac * if_scale_factor ifc)
                | SCALE_UP_BIN => u64 (frac * ng_user_tsresol ng) / if_tsresol ifc
                | SCALE_DOWN_DEC => frac / if_scale_factor ifc
                | SCALE_DOWN_BIN => u64 (frac * ng_user_tsresol ng) / if_tsresol ifc
                end in
    let hdr := mkHdr (s64 sec) (s32 frac) (f_caplen fd) (f_len fd) in
    match get_from_block_data (f_cursor fd) (f_caplen fd) with
    | inl m => mret ((-1)%Z, hdr, set_errbuf m p)
    | inr (doff, _) =>
      let '(hdr, d) := pcapint_post_process (pc_linktype p) (pc_swapped p) hdr (zskipn doff (pc_bufdata p)) in
      mret (1%Z, hdr, set_bufdata (zfirstn doff (pc_bufdata p) ++ d) p)
    end.
  Definition ngn_foundK (fd : ng_found) (p : pcap hptr hptr) : M (PState H hptr) (Z * pkthdr * pcap hptr hptr) :=
    let ng := ng_of p in
    let interface_id := f_interface_id fd in
    if ng_ifcount ng <=? interface_id
    then mret ((-1)%Z, hdr0, set_errbuf (Msg.no_idb_for_interface interface_id) p)
    else if pc_snapshot p <? f_caplen fd
    then mret ((-1)%Z, hdr0, set_errbuf (Msg.invalid_caplen_snaplen (f_caplen fd) (pc_snapshot p)) p)
    else ngn_tsK fd p.
  Lemma ngn_next_packet_eq : forall fuel (p : pcap hptr hptr),
    pcap_ng_next_packet MOps (prims HO fo_nop sites) fuel p
    = mbind (ng_scan_blocks MOps (prims HO fo_nop sites) fuel p) (fun rp => let '(r, p) := rp in
        match r with inl st => mret (st, hdr0, p) | inr fd => ngn_foundK fd p end).
  Proof using Type. pin_using tt. intros. reflexivity. Qed.

End NgnCtx.

End WithCeil.

(* [comment removed for export] *)
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require ImgTgtUbsan.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_memchr__S3.
From OSSVerify.libpcap.fuzz_pcap.images Require Ubsan.
Module TwB.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Strings.String.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Tac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Arr OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Bytes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ZBridge OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ITree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Nodes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Decode OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.SysStep OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.MonadX OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Image OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ImgTgtUbsan.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Monad OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Fmt OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.StdioCore OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Stdio OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapPrelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapTypes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapPure OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Pcap OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prog OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Adapter__Spec.StartupModel.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.STRW_tac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_kit__Musl.StartupKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.CellsExtra.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.FmtFacts__S3.FmtFacts OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_memchr__S3.SfKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_memchr__S3.NpArith OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.FmtFacts__S3.PPFacts.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.GI.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.PcapRep.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Pcap_iface__S3.Pcap_iface.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_lock__S3.Pcap_iface_pp.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Pcap_iface__S3.Pcap_iface_ng.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcapng_blkA__S3.SfNgKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_lock__S3.PP_kit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_ngnextA.TwB.
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
Local Ltac gio_ceil_fact :=
  match goal with
  | G : GIo _ _ _ _ _ _ |- _ => let H := fresh "CLO__" in pose proof (S3.PcapRep.TwB.GIo_ceil_lo _ _ _ _ _ _ G) as H; unfold rc_lo in H
  end.
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
Lemma pfx_split : forall (data : list Z) (bs : list byte) (k : nat),
  firstn (length data) bs = map b8 data -> (k <= length data)%nat ->
  firstn k bs = map b8 (firstn k data) /\ firstn (length data - k) (skipn k bs) = map b8 (skipn k data).
Proof using Type. pin_using tt.
  intros data bs k PFX Hk. split.
  - rewrite <- firstn_map. rewrite <- PFX. rewrite firstn_firstn. f_equal. lia.
  - rewrite <- skipn_map. rewrite <- PFX. rewrite skipn_firstn_comm. reflexivity.
Qed.

Lemma bytes_wr_rw_cells : forall mx A l, bytes_at usegs mx A l -> wr_at usegs mx A (Z.of_nat (length l)) -> rw_cells usegs mx A [CB (length l) l].
Proof using Type. pin_using tt. intros mx A l HB HW. split; [split; [cbn; split; [reflexivity| exact Logic.I] | cbn [cells_bytes cbytes]; rewrite app_nil_r; exact HB] | cbn [cells_size csize Nat.add]; rewrite Nat.add_0_r; exact HW]. Qed.

Section NgnCtx.
  Context {H hptr : Type} (HO : HeapOps H hptr) (K : modkit H hptr) (sites : stack_site -> Z).
  Hypothesis HFL : heap_frame_law K.
  Hypothesis SFL : stdio_fp_law K.
  Hypothesis HPL : heap_perm_law K.
  Hypothesis HAL : heap_addr_law K HO.
  Hypothesis SNPRINTF : snprintf_spec_stmt K.
  Hypothesis PP : post_process_stmt.
  Hypothesis ADJ : adjust_snapshot_stmt.
  Hypothesis RBLK : read_block_stmt HO K sites.
  Hypothesis ADDIF : add_interface_stmt HO K sites.

  (* [comment removed for export] *)
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
  Variables (R : rctx) (CLc FB : list (cblock (hptr:=hptr))) (lo P HA DA Af : Z) (m : mem) (o : option hptr).
  Variables (self f : hptr) (bufsize : Z) (swapped : bool) (vmaj vmin snapshot linktype ltext prec brk : Z) (header : pkthdr).
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
  Hypothesis P1 : (0 < P)%Z.  Hypothesis P2 : (P mod 16 = 0)%Z.  Hypothesis P4 : (P + 680 <= CEILZ)%Z.
  Hypothesis P5 : (P + 680 <= 65536 \/ 352256 <= P)%Z.  Hypothesis P6 : (P + 680 <= utp R - 200 \/ utp R - 200 + 4096 <= P)%Z.
  Hypothesis A1 : (0 < Af)%Z.  Hypothesis A4 : (Af + 1264 <= CEILZ)%Z.
  Hypothesis W1 : (1 <= snapshot <= INT_MAX)%Z.  Hypothesis W2 : (0 <= bufsize <= 2^30)%Z.
  Hypothesis W5 : brk = 0%Z.  Hypothesis W6 : prec = 0%Z.
  Hypothesis W7 : (0 <= vmaj < 2^16)%Z.  Hypothesis W8 : (0 <= vmin < 2^16)%Z.
  Hypothesis W9 : (0 <= linktype < 2^31)%Z.  Hypothesis W10 : (-2^31 <= ltext < 2^31)%Z.

  Let POSTQ := next_packet_post K ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc R CLc FB lo P HA DA m o.

  (* [comment removed for export] *)
  #[local] Abbreviation pv := (S3.F_ngnextA.TwB.pv self f bufsize swapped vmaj vmin snapshot linktype ltext prec brk header).
  #[local] Abbreviation ngn_frame := (S3.F_ngnextA.TwB.ngn_frame ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 P HA DA).
  #[local] Abbreviation ngn_final := (S3.F_ngnextA.TwB.ngn_final K sp R CLc FB P HA DA m o).
  #[local] Abbreviation ngn_finalC := (S3.F_ngnextA.TwB.ngn_finalC K sp R CLc FB P HA DA m o).
  #[local] Abbreviation ngn_final_C := (S3.F_ngnextA.TwB.ngn_final_C K sp R CLc FB P HA DA m o).
  #[local] Abbreviation ngn_ret_m1 := (S3.F_ngnextA.TwB.ngn_ret_m1 K ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc R CLc FB lo P HA DA m o BU).
  #[local] Abbreviation ngn_ret_0 := (S3.F_ngnextA.TwB.ngn_ret_0 K ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc R CLc FB lo P HA DA m o BU).
  #[local] Abbreviation ngn_ret_1 := (S3.F_ngnextA.TwB.ngn_ret_1 K ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc R CLc FB lo P HA DA m o BU).
  #[local] Abbreviation ngn_CLc_facts := (S3.F_ngnextA.TwB.ngn_CLc_facts K R CLc FB).
  #[local] Abbreviation ngn_snp_call := (S3.F_ngnextA.TwB.ngn_snp_call K HFL SFL SNPRINTF ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc R CLc FB lo P HA DA m o LO BU SPM TP ALN R1 R2 AH AD SPW P1 P4 P5).
  #[local] Abbreviation ngn_snp := (S3.F_ngnextA.TwB.ngn_snp K HFL SFL SNPRINTF ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc R CLc FB lo P HA DA m o LO BU SPM TP ALN R1 R2 AH AD SPW P1 P4 P5).
  #[local] Abbreviation ngn_mcp := (S3.F_ngnextA.TwB.ngn_mcp K HFL SFL ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc R CLc FB lo P HA DA m o LO BU ALN R1 R2 AH AD SPW P1 P4 P5 P6).
  #[local] Abbreviation PCAPRC_errbuf := (S3.F_ngnextA.TwB.PCAPRC_errbuf K sp R lo P HA DA LO BU ALN R1 R2 AH AD SPW P1).

  Ltac norm_g :=
    unfold S3.F_ngnextA.TwB.pv; unfold pcap_blocks; unfold psize; unfold is_ng;
    cbn [pc_self pc_rfile pc_bufsize pc_bufalloc pc_buffer pc_bufdata pc_swapped pc_version_major pc_version_minor pc_snapshot pc_linktype
         pc_linktype_ext pc_tstamp_precision pc_break_loop pc_errbuf pc_header pc_priv priv_cells ng_of ng_ifaces_ptr_of
         set_bufdata set_errbuf set_buffer set_ng set_priv];
    unfold PCAP_NG_SF_TOTAL, PCAP_PRIV_OFF.
  Ltac norm_p :=
    unfold S3.F_ngnextA.TwB.pv in *; unfold pcap_blocks in *; unfold psize in *; unfold is_ng in *;
    cbn [pc_self pc_rfile pc_bufsize pc_bufalloc pc_buffer pc_bufdata pc_swapped pc_version_major pc_version_minor pc_snapshot pc_linktype
         pc_linktype_ext pc_tstamp_precision pc_break_loop pc_errbuf pc_header pc_priv priv_cells ng_of ng_ifaces_ptr_of
         set_bufdata set_errbuf set_buffer set_ng set_priv] in *;
    unfold PCAP_NG_SF_TOTAL, PCAP_PRIV_OFF in *.

  (* [comment removed for export] *)
  Definition ngn_pp__stmt : Prop := forall (ra' t0' t1' t2' x0 x1 a0' a1' a2' a3' a4' a6' a7' x2 x3 x5 x6 x7 x8 x9 x10 x11 t3' t4' t5' t6' ws wu : word) (m5 : mem) (ps : PState H hptr)
           (bq : hptr) (Bq Ix alloc doff : Z) (data eb : list Z) (sx : pcap_ng_sf) (ix : option hptr) (sec usec cap len : Z) (dw : cell) (dj : list byte) (ccs : list cell),
      stk usegs m5 lo (bv_unsigned sp + -160) ->
      rw_cells usegs m5 (bv_unsigned sp + -160) (ngn_frame dj ccs) -> cells_size ccs = 24%nat -> mem_inv usegs m5 ->
      GIo K R ps (CLc ++ pcap_blocks (pv bq alloc data eb sx ix) P Bq Ix) FB m5 ->
      PCAPR (hptr:=hptr) P (pv bq alloc data eb sx ix) (pcap_blocks (pv bq alloc data eb sx ix) P Bq Ix) FB m5 ->
      agrees_on (fun a => client_keeps CLc (bv_unsigned sp) a /\ ~ (HA <= a < HA + 24) /\ ~ (DA <= a < DA + 8))%Z m m5 ->
      rw_cells usegs m5 HA [C8 ws; C8 wu; C4 (Z_to_bv 64 cap); C4 (Z_to_bv 64 len)] -> rw_cells usegs m5 DA [dw] -> csize dw = 8%nat ->
      ws = Z_to_bv 64 sec -> wu = Z_to_bv 64 usec -> Forall (fun x => 0 <= x < 256)%Z data ->
      (0 <= doff <= Z.of_nat (length data))%Z -> (doff mod 4 = 0)%Z ->
      (0 <= cap <= Z.of_nat (length data) - doff)%Z -> (Z.of_nat (length data) < 2^31)%Z -> (0 <= len < 2^32)%Z -> ps_outfile ps = o ->
      implM usegs (let '(hdr, d) := pcapint_post_process linktype swapped (mkHdr sec usec cap len) (zskipn doff data) in
                   mret (1%Z, hdr, set_bufdata (zfirstn doff data ++ d) (pv bq alloc data eb sx ix))) ps POSTQ
        (MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -160)) gp tp t0' t1' t2' x0 x1 a0' a1' a2' a3' a4' (Z_to_bv 64 (Bq + doff)) a6' a7'
                 x2 (Z_to_bv 64 P) x3 x5 x6 x7 x8 x9 x10 x11 t3' t4' t5' t6') F (Z_to_bv 64 0x1824c) fc None m5 (seg_rom usegs)).
  Section Sz3.
  Variables ra' t0' t1' t2' x0 x1 a0' a1' a2' a3' a4' a6' a7' x2 x3 x5 x6 x7 x8 x9 x10 x11 t3' t4' t5' t6' ws wu m5 ps bq Bq Ix alloc doff data eb sx ix sec usec cap len dw dj ccs : ltac2:(SecDiet.SzSec.tyM 'ngn_pp__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra').
  Lemma ngn_pp__body : ltac2:(SecDiet.SzSec.bodyP 'ngn_pp__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof using AD AH BU HFL LO P1 P2 P4 P5 P6 PP R1 R2 R3 SFL SP47 SPM SPW W1 W10 W2 W5 W6 W7 W8 W9. pin_using (fun (AD AH BU HFL LO P1 P2 P4 P5 P6 PP R1 R2 R3 SFL SP47 SPM SPW W1 W10 W2 W5 W6 W7 W8 W9 : unit) => tt).
 intros ST5 FR5 Hccs MI5 G5 PC5 AG5 HH HD Hd -> -> DRNG Hdoff Hd4 Hcap Hl31 Hlen OF5.
    pose proof (bv_unsigned_in_range 64 sp) as RSP.
    destruct PC5 as (Afx & Hin & (Bx' & Ix' & jx' & padx & bsx' & EPB & CELLS & PRIV & BUF & PFX & IFS & WF)).
    rewrite EPB in G5.
    pose proof (PB_apart K _ _ _ _ _ _ _ _ _ _ G5 eq_refl) as [APB API].
    pose proof (GIo_PB_block K _ _ _ _ _ _ _ _ _ G5 ltac:(right; left; reflexivity)) as (K1 & K2 & K3 & K4 & K5 & K6).
    norm_p.
    assert (EBX : Bx' = Bq) by congruence. subst Bx'. clear EPB.
    pose proof WF as (W1' & W2' & W3 & W4 & _ & _ & _ & _ & _ & _ & _ & _ & (UT & WMB & WIC & WIS) & WBB). cbn [pc_bufsize pc_bufalloc pc_bufdata length] in W3, W4, WBB.
    unfold pcap_cells_gen, pc_pre, hdr_cells, pc_ops, np_entry, cleanup_entry, is_ng, PCAP_PRIV_OFF in CELLS.
    cbn [app pc_bufsize pc_break_loop pc_swapped pc_version_major pc_version_minor pc_snapshot pc_linktype pc_linktype_ext pc_tstamp_precision pc_header pc_priv pk_next_ng pk_cleanup_ng PK] in CELLS.
    destruct (rw_cells_forget _ _ _ _ HD) as [dwj HD']. clear HD. cbn [cells_size] in HD'. rewrite Hd in HD'. change (8 + 0)%nat with 8%nat in HD'.
    (* [comment removed for export] *)
    apply (rw_cells_split_CB usegs m5 _ [] (Z.to_nat alloc) _ [] [Z.to_nat doff; length data - Z.to_nat doff; Z.to_nat alloc - length data]%nat) in BUF; [| cbn; lia].
    cbn [mk_CB_cells app] in BUF.
    destruct (pfx_split data bsx' (Z.to_nat doff) PFX ltac:(lia)) as [E0 E1]. rewrite E0, E1 in BUF.
    destruct (rw_cells_cut _ _ _ 1 BUF) as [BD0 BUF']. cbn [firstn skipn cells_size csize Nat.add] in BD0, BUF'.
    destruct (rw_cells_cut _ _ _ 1 BUF') as [BD BT]. clear BUF BUF'. cbn [firstn skipn cells_size csize Nat.add] in BD, BT.
    replace (Bq + Z.of_nat (Z.to_nat doff + 0))%Z with (Bq + doff)%Z in BD, BT by lia.
    replace (Bq + doff + Z.of_nat (length data - Z.to_nat doff + 0))%Z with (Bq + Z.of_nat (length data))%Z in BT by lia.
    pose proof FR5 as FRJ. unfold S3.F_ngnextA.TwB.ngn_frame in FRJ. apply rw_cells_app in FRJ as [FRJ _]. 
    hide BD0. hide BD. hide BT. hide PRIV. hide IFS. hide HH. hide FR5.
    pose proof (munch_refl [(DA, DA + 8)]%Z m5) as MU. pose proof (wmono_refl usegs m5) as WM.
    unfold implM. iprefix.
    step. step. if_false_by (eqz_false DA ltac:(gio_ceil_fact; clear -CLO__ R1 R2 R3 BU LO SPW SP47; unfold rc_spmain in *; lia)).
    step. step. rewrite (and7_aligned DA) by (gio_ceil_fact; clear -CLO__ AD R1 R2 R3 BU LO SPW SP47; unfold rc_spmain in *; lia). step. if_false.
    step. step.
    step. if_false_by (eqz_false (Bq + doff) ltac:(clear - K1 K4 Hdoff W4; lia)).
    step. rewrite (sx32_small (Z.b2z swapped)) by (destruct swapped; cbn; lia).
    step. rewrite (sx32_small linktype) by lia.
    step. step. step.
    unhide BD0. unhide BD. unhide BT. unhide PRIV. unhide IFS. unhide HH. unhide FR5. clear FRJ.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      assert (AGD : agrees_on (fun a => outside [(DA, DA + 8)]%Z a) m5 mm) by (eapply agrees_on_of_munch; [exact MU | exact WM | intros a _ Ho; exact Ho]);
      rename mm into m5' end.
    assert (T0 : forall A cs, rw_cells usegs m5 A cs -> (A + Z.of_nat (cells_size cs) <= DA \/ DA + 8 <= A)%Z -> rw_cells usegs m5' A cs).
    { intros A cs HC HA'. eapply agrees_rw_cells; [exact AGD | exact HC | intros a Ha; cbn [outside]; lia]. }
    apply T0 in BD0; [| cbn [cells_size csize Nat.add]; unfold rc_lo in LO; lia].
    apply T0 in BD; [| cbn [cells_size csize Nat.add]; unfold rc_lo in LO; lia].
    apply T0 in BT; [| cbn [cells_size csize Nat.add]; unfold rc_lo in LO; lia].
    apply T0 in PRIV; [| cbn [cells_size csize Nat.add ng_cells]; unfold rc_lo in LO; lia].
    apply T0 in HH; [| cbn [cells_size csize Nat.add]; lia].
    apply T0 in FR5; [| unfold S3.F_ngnextA.TwB.ngn_frame; rewrite !cells_size_app; cbn [cells_size csize Nat.add]; rewrite Hccs; lia].
    assert (IFS' : ifaces_ok (pv bq alloc data eb sx ix) Ix' m5').
    { eapply ifaces_ok_agree; [exact AGD| | exact IFS]. intros sg q Hq a Ha. cbn [outside].
      cbn [pc_priv] in Hq. injection Hq as Esx Eix. subst sg ix.
      pose proof (GIo_PB_block K _ _ _ _ _ _ _ _ _ G5 ltac:(unfold pcap_blocks; cbn [pc_priv]; right; right; left; reflexivity)) as (I1 & I2 & I3 & I4 & I5 & I6).
      unfold rc_lo in LO. lia. }
    clear IFS T0.
    rename ST5 into ST5'.
    assert (G5' : GIo K R ps (CLc ++ pcap_blocks (pv bq alloc data eb sx ix) P Bq Ix') FB m5').
    { eapply (GIo_pcap_frame K HFL SFL); [exact G5 | exact MU | exact WM |]. apply Forall_cons; [left; cbn [fst snd]; unfold rc_lo; lia| apply Forall_nil]. }
    assert (AG5' : agrees_on (fun a => client_keeps CLc (bv_unsigned sp) a /\ ~ (HA <= a < HA + 24) /\ ~ (DA <= a < DA + 8))%Z m m5').
    { eapply agrees_on_trans; [exact AG5|]. eapply agrees_on_weaken; [exact AGD|]. intros a [_ [_ Hn]]; cbn [outside]; lia. }
    lazymatch goal with |- context [mem_inv usegs m5'] => idtac | _ => idtac end.
    assert (MI5' : mem_inv usegs m5') by assumption.
    clear MU WM AGD G5 AG5.
    assert (ZA : zarr m5' (Bq + doff) (zskipn doff data)).
    { unfold zskipn. split; [| split; [| apply Forall_range_skipn; exact DRNG]].
      - pose proof (rw_cells_bytes_at _ _ _ _ BD) as X. cbn [cells_bytes cbytes] in X. rewrite app_nil_r in X. exact X.
      - eapply rw_cells_wr_at; [exact BD|]. cbn [cells_size csize Nat.add]. rewrite length_skipn. lia. }
    change (rw_cells usegs m5' HA (pkthdr_cells (Z_to_bv 64 sec) (Z_to_bv 64 usec) (mkHdr sec usec cap len))) in HH.
    assert (LD : Z.of_nat (length (zskipn doff data)) = (Z.of_nat (length data) - doff)%Z) by (unfold zskipn; rewrite length_skipn; lia).
    name_sp sp (-160)%Z.
    eapply evt_cut.
    { eapply PP; [rewrite Hsp; exact ST5' | unfold PP_FRAME; rewrite Hsp; lia | exact HH | exact ZA | exact MI5' | reflexivity | reflexivity | reflexivity | reflexivity
                 | lia | cbn [h_caplen]; lia | lia | cbn [h_len]; lia | left; rewrite Hsp; lia | right; unfold rc_lo in LO; lia | unfold PP_FRAME; rewrite Hsp; unfold rc_lo in LO; lia
                 | exact AH | clear -K2 Hd4; Z.div_mod_to_equations; lia | unfold rc_spmain in R3; lia | lia | unfold rc_lo in LO; lia | lia ]. }
    cbv beta. intros ms' PO. destruct PO as (y0 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & y8 & y9 & y10 & y11 & y12 & y13 & y14 & m6 & -> & MU6 & WM6 & MI6 & ST6 & HH6 & ZA6).
    rewrite Hsp in *. unname_sp.
    replace (ret_pc (Z_to_bv 64 0x18280)) with (Z_to_bv 64 0x18280) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
    cbn [h_caplen] in MU6. unfold PP_FRAME in MU6.
    set (hdr' := fst (pcapint_post_process linktype swapped (mkHdr sec usec cap len) (zskipn doff data))) in *.
    set (d' := snd (pcapint_post_process linktype swapped (mkHdr sec usec cap len) (zskipn doff data))) in *.
    pose proof (pp_length linktype swapped (mkHdr sec usec cap len) (zskipn doff data)) as LEN'. fold d' in LEN'.
    pose proof (pp_sec linktype swapped (mkHdr sec usec cap len) (zskipn doff data)) as [SEC' USEC']. fold hdr' in SEC', USEC'. cbn [h_sec h_usec] in SEC', USEC'.
    pose proof (pp_range linktype swapped (mkHdr sec usec cap len) (zskipn doff data) ltac:(cbn [h_caplen]; lia) ltac:(cbn [h_len]; lia) ltac:(lia)) as [RC' RL']. fold hdr' in RC', RL'.
    assert (AGS : agrees_on (fun a => outside [(bv_unsigned sp + -160 - 32, bv_unsigned sp + -160); (HA + 20, HA + 24); (Bq + doff, Bq + doff + cap)]%Z a) m5' m6)
      by (eapply agrees_on_of_munch; [exact MU6 | exact WM6 | intros a _ Ho; exact Ho]).
    apply (agrees_rw_cells _ _ _ _ _ AGS) in FR5; [| intros a Ha; unfold S3.F_ngnextA.TwB.ngn_frame in Ha; rewrite !cells_size_app in Ha; cbn [outside cells_size csize Nat.add] in *; rewrite Hccs in Ha; unfold rc_lo in LO; lia].
    apply (agrees_rw_cells _ _ _ _ _ AGS) in HD'; [| intros a Ha; cbn [outside cells_size csize Nat.add] in *; unfold rc_lo in LO; lia].
    apply (agrees_rw_cells _ _ _ _ _ AGS) in CELLS; [| intros a Ha; cbn [outside cells_size csize Nat.add] in *; unfold rc_lo in LO; lia].
    apply (agrees_rw_cells _ _ _ _ _ AGS) in PRIV; [| intros a Ha; cbn [outside cells_size csize Nat.add ng_cells] in *; unfold rc_lo in LO; lia].
    apply (agrees_rw_cells _ _ _ _ _ AGS) in BT; [| intros a Ha; cbn [outside cells_size csize Nat.add] in *; unfold rc_lo in LO; lia].
    apply (agrees_rw_cells _ _ _ _ _ AGS) in BD0; [| intros a Ha; cbn [outside cells_size csize Nat.add] in *; unfold rc_lo in LO; lia].
    assert (IFS6 : ifaces_ok (pv bq alloc data eb sx ix) Ix' m6).
    { eapply ifaces_ok_agree; [exact AGS| | exact IFS']. intros sg q Hq a Ha. cbn [outside]. pose proof (API sg q Hq) as [X1 X2].
      cbn [pc_priv] in Hq. injection Hq as Esx Eix. subst sg ix.
      pose proof (GIo_PB_block K _ _ _ _ _ _ _ _ _ G5' ltac:(unfold pcap_blocks; cbn [pc_priv]; right; right; left; reflexivity)) as (I1 & I2 & I3 & I4 & I5 & I6).
      cbn [pc_bufalloc] in X2. unfold rc_lo in LO. lia. }
    (* [comment removed for export] *)
    destruct ZA6 as (ZB & ZW & ZR).
    pose proof (bytes_wr_rw_cells _ _ _ ZB ltac:(rewrite zbytes_length; exact ZW)) as BD6. rewrite zbytes_length in BD6.
    pose proof (rw_cells_uncut _ _ _ _ _ BD6 BT ltac:(cbn [cells_size csize Nat.add]; rewrite LEN'; unfold zskipn; rewrite length_skipn; lia)) as BDT. cbn [app] in BDT.
    pose proof (rw_cells_uncut _ _ _ _ _ BD0 BDT ltac:(cbn [cells_size csize Nat.add]; lia)) as BUF6. cbn [app] in BUF6.
    merge_all BUF6.
    replace (Z.to_nat doff + (length d' + (Z.to_nat alloc - length data + 0)))%nat with (Z.to_nat alloc) in BUF6 by (rewrite LEN'; unfold zskipn; rewrite length_skipn; lia).
    rewrite app_nil_r in BUF6.
    rewrite (surjective_pairing (pcapint_post_process linktype swapped _ _)). fold hdr' d'.
    cbn [set_bufdata pc_self pc_rfile pc_bufsize pc_bufalloc pc_buffer pc_swapped pc_version_major pc_version_minor pc_snapshot pc_linktype pc_linktype_ext pc_tstamp_precision pc_break_loop pc_errbuf pc_header pc_priv].
    assert (G6 : GIo K R ps (CLc ++ pcap_blocks (pv bq alloc data eb sx ix) P Bq Ix') FB m6).
    { eapply (GIo_pcap_frame K HFL SFL); [exact G5' | exact MU6 | exact WM6 |].
      apply Forall_cons; [left; cbn [fst snd]; unfold rc_lo; lia|]. apply Forall_cons; [left; cbn [fst snd]; unfold rc_lo, rc_spmain in *; lia|].
      apply Forall_cons; [| apply Forall_nil]. right. unfold iv_in_block, pcap_blocks. apply Exists_cons_tl, Exists_cons_hd. cbn [cb_addr cb_size fst snd pc_buffer pc_bufalloc S3.F_ngnextA.TwB.pv]. lia. }
    apply evt_done. eapply (ngn_ret_1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m6 ps (pcap_blocks (pv bq alloc data eb sx ix) P Bq Ix')
                             (pv bq alloc (zfirstn doff data ++ d') eb sx ix) hdr'); [exact ST6 | exact FR5 | exact Hccs | exact MI6 | | exact RC' | exact RL'].
    unfold S3.F_ngnextA.TwB.ngn_final. norm_p.
    split; [exact G6|]. split.
    { exists Afx. split; [exact Hin|]. exists Bq, Ix', jx', padx, (map b8 (firstn (Z.to_nat doff) data) ++ zbytes d' ++ firstn (Z.to_nat alloc - length data) (skipn (length data - Z.to_nat doff) (skipn (Z.to_nat doff) bsx'))).
      norm_g.
      split; [reflexivity|]. split; [exact CELLS|]. split; [exact PRIV|]. split; [rewrite <- app_assoc in BUF6 || idtac; exact BUF6|].
      split. { unfold zfirstn. rewrite length_app, length_firstn, map_app.
               replace (Nat.min (Z.to_nat doff) (length data) + length d')%nat with (length (map b8 (firstn (Z.to_nat doff) data) ++ zbytes d')) by (rewrite length_app, length_map, length_firstn, zbytes_length; lia).
               rewrite app_assoc, firstn_app, firstn_all, Nat.sub_diag. cbn [firstn]. rewrite app_nil_r. reflexivity. }
      split; [exact IFS6|].
      unfold pcap_wf in *. cbn [pc_snapshot pc_bufsize pc_bufalloc pc_bufdata pc_break_loop pc_tstamp_precision pc_version_major pc_version_minor pc_linktype pc_linktype_ext pc_header pc_priv] in *.
      unfold zfirstn. rewrite length_app, length_firstn, LEN'.
      repeat split; try lia; try tauto. all: unfold zskipn; rewrite ?length_skipn; lia. }
    split. { eapply agrees_on_trans; [exact AG5'|]. eapply agrees_on_weaken; [exact AGS|]. intros a [[Ha|Ha] [Hn1 Hn2]]; cbn [outside]; [unfold rc_lo in LO; lia|].
             destruct (ngn_CLc_facts _ _ _ _ G5' Ha) as [Hc Hnb]. unfold rc_lo in LO. split; [lia|]. split; [lia|]. split; [| exact Logic.I].
             intros Hin'. apply Hnb. unfold pcap_blocks, in_block. apply Exists_cons_tl, Exists_cons_hd. cbn [cb_addr cb_size fst snd pc_buffer pc_bufalloc]. lia. }
    split. { unfold hdr_cells. rewrite SEC', USEC'. exact HH6. }
    split; [reflexivity|]. split; [exact HD'|]. split; [reflexivity| exact OF5].
  Qed.
  End Sz3.
  Lemma ngn_pp : ltac:(let t := eval cbv delta [ngn_pp__stmt] in ngn_pp__stmt in exact t).
  Proof using AD AH BU HFL LO P1 P2 P4 P5 P6 PP R1 R2 R3 SFL SP47 SPM SPW W1 W10 W2 W5 W6 W7 W8 W9. intros ra' t0' t1' t2' x0 x1 a0' a1' a2' a3' a4' a6' a7' x2 x3 x5 x6 x7 x8 x9 x10 x11 t3' t4' t5' t6' ws wu m5 ps bq Bq Ix alloc doff data eb sx ix sec usec cap len dw dj ccs. ltac2:(SecDiet.SzSec.closeP 'ngn_pp__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.

  (* [comment removed for export] *)
  Definition ngn_tsK (fd : ng_found) (p : pcap hptr hptr) : M (PState H hptr) (Z * pkthdr * pcap hptr hptr) :=
    let ng := ng_of p in
    let interface_id := f_interface_id fd in
    let ifc := nth_slot (ng_ifaces ng) (ng_ifcount ng) interface_id in
    let t := f_t fd in
    let sec := u64 (t / if_tsresol ifc + if_tsoffset ifc) in
    let frac := t mod if_tsresol ifc in
    let frac := match if_scale_type ifc with
                | NG_PASS_THROUGH => frac
                | SCALE_UP_DEC => u64 (frac * if_scale_factor ifc)
                | SCALE_UP_BIN => u64 (frac * ng_user_tsresol ng) / if_tsresol ifc
                | SCALE_DOWN_DEC => frac / if_scale_factor ifc
                | SCALE_DOWN_BIN => u64 (frac * ng_user_tsresol ng) / if_tsresol ifc
                end in
    let hdr := mkHdr (s64 sec) (s32 frac) (f_caplen fd) (f_len fd) in
    match get_from_block_data (f_cursor fd) (f_caplen fd) with
    | inl m => mret ((-1)%Z, hdr, set_errbuf m p)
    | inr (doff, _) =>
      let '(hdr, d) := pcapint_post_process (pc_linktype p) (pc_swapped p) hdr (zskipn doff (pc_bufdata p)) in
      mret (1%Z, hdr, set_bufdata (zfirstn doff (pc_bufdata p) ++ d) p)
    end.
  Definition ngn_foundK (fd : ng_found) (p : pcap hptr hptr) : M (PState H hptr) (Z * pkthdr * pcap hptr hptr) :=
    let ng := ng_of p in
    let interface_id := f_interface_id fd in
    if ng_ifcount ng <=? interface_id
    then mret ((-1)%Z, hdr0, set_errbuf (Msg.no_idb_for_interface interface_id) p)
    else if pc_snapshot p <? f_caplen fd
    then mret ((-1)%Z, hdr0, set_errbuf (Msg.invalid_caplen_snaplen (f_caplen fd) (pc_snapshot p)) p)
    else ngn_tsK fd p.
  Lemma ngn_next_packet_eq : forall fuel (p : pcap hptr hptr),
    pcap_ng_next_packet MOps (prims HO fo_nop sites) fuel p
    = mbind (ng_scan_blocks MOps (prims HO fo_nop sites) fuel p) (fun rp => let '(r, p) := rp in
        match r with inl st => mret (st, hdr0, p) | inr fd => ngn_foundK fd p end).
  Proof using Type. pin_using tt. intros. reflexivity. Qed.

End NgnCtx.

End WithCeil.
End TwB.
End F_ngnextB.

(* [comment removed for export] *)
Module F_ngnextT.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool String.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import Tac Arr Bytes ZBridge ITree Nodes Decode SysStep MonadX Image ImgSrc3.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Prelim Monad Fmt StdioCore Stdio PcapPrelim PcapTypes PcapPure Pcap Prog. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Adapter__Spec. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Monad OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Fmt OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.StdioCore OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Stdio OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapPrelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapTypes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapPure OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Pcap OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prog OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Adapter__Spec.StartupModel.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require AmoStep__Musl. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require Printf_kit__Musl. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.STRW_tac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_kit__Musl.StartupKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.CellsExtra.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require FmtFacts__S3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require GI PcapRep. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require Pcap_iface__S3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_lock__S3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_memchr__S3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_sfpcapng_blkA__S3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_ngnextA. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.FmtFacts__S3.FmtFacts OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.GI OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.PcapRep OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Pcap_iface__S3.Pcap_iface OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_lock__S3.Pcap_iface_pp OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Pcap_iface__S3.Pcap_iface_ng OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_memchr__S3.SfKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcapng_blkA__S3.SfNgKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.FmtFacts__S3.PPFacts OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_lock__S3.PP_kit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_ngnextA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Startup_B__S3.F_ngnextB.
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
Local Ltac gio_ceil_fact :=
  match goal with
  | G : GIo _ _ _ _ _ _ |- _ => let H := fresh "CLO__" in pose proof (PcapRep.GIo_ceil_lo _ _ _ _ _ _ G) as H; unfold rc_lo in H
  end.
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
Definition ifs_cells_slot__stmt : Prop := forall m I ifs js rest k,
  rw_cells ssegs m I (ifs_cells ifs js ++ rest) -> length js = length ifs -> (k < length ifs)%nat ->
  rw_cells ssegs m (I + 40 * Z.of_nat k) (if_cells (nth k ifs ngif0) (nth k js (mkIJ [] [] (Z_to_bv 64 0)))).
Section Sz1.
Variables m I : ltac2:(SecDiet.SzSec.tyM 'ifs_cells_slot__stmt "vvk" @m).
Lemma ifs_cells_slot__body : ltac2:(SecDiet.SzSec.bodyP 'ifs_cells_slot__stmt "vvk").
Proof using Type. pin_using tt.
  intros ifs.
 revert m I. induction ifs as [|i ifs IH]; intros m I js rest k HC Hl Hk; [cbn in Hk; lia|].
  destruct js as [|j js]; [cbn in Hl; lia|]. cbn [ifs_cells] in HC. rewrite <- app_assoc in HC.
  apply rw_cells_app in HC as [H1 H2]. rewrite if_cells_size in H2.
  destruct k as [|k].
  - cbn [nth]. replace (I + 40 * Z.of_nat 0)%Z with I by lia. exact H1.
  - cbn [nth]. replace (I + 40 * Z.of_nat (S k))%Z with (I + Z.of_nat 40 + 40 * Z.of_nat k)%Z by lia.
    apply (IH _ _ js rest k H2); cbn [length] in *; lia.
Qed.
End Sz1.
Lemma ifs_cells_slot : ltac:(let t := eval cbv delta [ifs_cells_slot__stmt] in ifs_cells_slot__stmt in exact t).
Proof using Type. intros m I ifs. ltac2:(SecDiet.SzSec.closeP 'ifs_cells_slot__body "vvk"). Qed.

(* [comment removed for export] *)
Lemma mulhu_40 : forall (iw : word) (id : Z), (bv_unsigned iw mod 2^32 = id)%Z ->
  Z_to_bv 64 (Z.shiftr (bv_unsigned (Z_to_bv 64 (Z.shiftl (bv_unsigned iw) 32)) * 171798691840) 64) = Z_to_bv 64 (40 * id).
Proof using Type. pin_using tt.
  intros iw id Hid. pose proof (bv_unsigned_in_range 64 iw) as R. change (bv_modulus 64) with (2^64)%Z in R.
  rewrite Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia. rewrite unsigned_lit_wrap.
  replace ((bv_unsigned iw * 2 ^ 32) mod 2 ^ 64)%Z with (id * 2^32)%Z by (rewrite <- Hid; Z.div_mod_to_equations; nia).
  f_equal. replace (id * 2 ^ 32 * 171798691840)%Z with ((40 * id) * 2^64)%Z by lia. rewrite Z.div_mul by lia. reflexivity.
Qed.

Lemma divu_lit : forall a b, (0 <= a < 2^64)%Z -> (0 < b < 2^64)%Z -> mul_div M_DIVU (Z_to_bv 64 a) (Z_to_bv 64 b) = Z_to_bv 64 (a / b).
Proof using Type. pin_using tt.
  intros a b Ha Hb. unfold mul_div. rewrite (unsigned_lit b) by lia. replace (b =? 0)%Z with false by (symmetry; apply Z.eqb_neq; lia).
  apply bv_eq. rewrite bv_divu_unsigned. rewrite (unsigned_lit a), (unsigned_lit b) by lia.
  rewrite unsigned_lit; [reflexivity|]. split; [apply Z.div_pos; lia|]. apply Z.div_lt_upper_bound; [lia|]. nia.
Qed.

Lemma zbv64_eq : forall a b, (a mod 2^64 = b mod 2^64)%Z -> Z_to_bv 64 a = Z_to_bv 64 b.
Proof using Type. pin_using tt. intros a b E. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64)%Z with (2^64)%Z. exact E. Qed.

Lemma swrap32_s32 : forall x, bv_swrap 32 x = s32 x.
Proof using Type. pin_using tt. intros x. unfold bv_swrap, s32, bv_wrap, bv_half_modulus, bv_modulus. change (2 ^ Z.of_N 32)%Z with (2^32)%Z. change (2 ^ (Z.of_N 32 - 1))%Z with (2^31)%Z. reflexivity. Qed.

Lemma divu_lit_mod : forall a b, (0 <= a)%Z -> (0 < b < 2^64)%Z -> mul_div M_DIVU (Z_to_bv 64 a) (Z_to_bv 64 b) = Z_to_bv 64 ((a mod 2^64) / b).
Proof using Type. pin_using tt.
  intros a b Ha Hb. rewrite (zbv64_eq a (a mod 2^64)) by (rewrite Z.mod_mod by lia; reflexivity).
  apply divu_lit; [| exact Hb]. Z.div_mod_to_equations. lia.
Qed.

Lemma frac_word : forall t b, (0 <= t < 2^64)%Z -> (0 < b < 2^64)%Z ->
  Z_to_bv 64 (bv_unsigned (Z_to_bv 64 t) - bv_unsigned (Z_to_bv 64 (bv_unsigned (Z_to_bv 64 (t / b)) * bv_unsigned (Z_to_bv 64 b))))
  = Z_to_bv 64 (t mod b).
Proof using Type. pin_using tt.
  intros t b Ht Hb.
  assert (Q : (0 <= t / b <= t)%Z) by (split; [apply Z.div_pos; lia| apply Z.div_le_upper_bound || idtac; Z.div_mod_to_equations; nia]).
  assert (QB : (0 <= t / b * b <= t)%Z) by (Z.div_mod_to_equations; nia).
  rewrite (unsigned_lit t), (unsigned_lit (t / b)), (unsigned_lit b) by lia. rewrite unsigned_lit by lia.
  f_equal. Z.div_mod_to_equations. nia.
Qed.

Lemma sec_word_eq : forall off q, Z_to_bv 64 (off + q) = Z_to_bv 64 (s64 (u64 (q + off))).
Proof using Type. pin_using tt. intros. apply zbv64_eq. unfold s64, u64. Z.div_mod_to_equations. lia. Qed.

Lemma usec_word_eq : forall x, (0 <= x < 2^64)%Z -> Z_to_bv 64 (bv_swrap 32 (bv_unsigned (Z_to_bv 64 x))) = Z_to_bv 64 (s32 x).
Proof using Type. pin_using tt. intros x Hx. rewrite unsigned_lit by lia. rewrite swrap32_s32. reflexivity. Qed.

Lemma mul_word_u64 : forall a b, (0 <= a < 2^64)%Z -> (0 <= b < 2^64)%Z ->
  Z_to_bv 64 (bv_unsigned (Z_to_bv 64 a) * bv_unsigned (Z_to_bv 64 b)) = Z_to_bv 64 (u64 (b * a)).
Proof using Type. pin_using tt. intros a b Ha Hb. rewrite !unsigned_lit by lia. apply zbv64_eq. unfold u64. rewrite Z.mod_mod by lia. f_equal. lia. Qed.

Lemma u64_range : forall x, (0 <= u64 x < 2^64)%Z.
Proof using Type. pin_using tt. intros. unfold u64. apply Z.mod_pos_bound. lia. Qed.
Lemma div_range64 : forall a b, (0 <= a < 2^64)%Z -> (0 < b)%Z -> (0 <= a / b < 2^64)%Z.
Proof using Type. pin_using tt.
  intros a b Ha Hb. split; [apply Z.div_pos; lia|].
  apply Z.div_lt_upper_bound; [lia|]. assert (1 * 2^64 <= b * 2^64)%Z by (apply Z.mul_le_mono_nonneg_r; lia). lia.
Qed.
Lemma mod_range64 : forall a b, (0 < b < 2^64)%Z -> (0 <= a mod b < 2^64)%Z.
Proof using Type. pin_using tt. intros a b Hb. pose proof (Z.mod_pos_bound a b ltac:(lia)). lia. Qed.

(* [comment removed for export] *)
Definition sxu (v : Z) : Z := if v <? 2^31 then v else v + 2^64 - 2^32.
Lemma sxu_mono : forall a b, (0 <= a < 2^32)%Z -> (0 <= b < 2^32)%Z -> (sxu a < sxu b <-> a < b)%Z.
Proof using Type. pin_using tt. intros a b Ha Hb. unfold sxu. destruct (Z.ltb_spec a (2^31)); destruct (Z.ltb_spec b (2^31)); lia. Qed.
Lemma unsigned_sextw : forall (w : word), bv_unsigned (Z_to_bv 64 (bv_swrap 32 (bv_unsigned w + 0))) = sxu (bv_unsigned w mod 2^32).
Proof using Type. pin_using tt. intros w. rewrite Z.add_0_r. rewrite unsigned_swrap32. reflexivity. Qed.
Lemma sextw_mod : forall (x : Z), ((bv_swrap 32 (x + 0)) mod 18446744073709551616 = sxu (x mod 2^32))%Z.
Proof using Type. pin_using tt. intros x. rewrite Z.add_0_r. change 18446744073709551616%Z with (2^64)%Z. rewrite <- (unsigned_lit_wrap (bv_swrap 32 x)). rewrite unsigned_swrap32. reflexivity. Qed.
Lemma unsigned_sx32' : forall x, (0 <= x < 2^32)%Z -> bv_unsigned (sx32 (Z_to_bv 64 x)) = sxu x.
Proof using Type. pin_using tt. intros x Hx. rewrite OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_lock__S3.PP_kit.unsigned_sx32 by lia. reflexivity. Qed.
Lemma sxu_range : forall v, (0 <= v < 2^32)%Z -> (0 <= sxu v < 2^64)%Z /\ (v < 2^31 -> sxu v = v)%Z /\ (2^31 <= v -> 2^64 - 2^31 <= sxu v)%Z.
Proof using Type. pin_using tt. intros v Hv. unfold sxu. destruct (Z.ltb_spec v (2^31)); lia. Qed.

Section NgnCtx.
  Context {H hptr : Type} (HO : HeapOps H hptr) (K : modkit H hptr) (sites : stack_site -> Z).
  Hypothesis HFL : heap_frame_law K.
  Hypothesis SFL : stdio_fp_law K.
  Hypothesis HPL : heap_perm_law K.
  Hypothesis HAL : heap_addr_law K HO.
  Hypothesis SNPRINTF : snprintf_spec_stmt K.
  Hypothesis PP : post_process_stmt.
  Hypothesis ADJ : adjust_snapshot_stmt.
  Hypothesis RBLK : read_block_stmt HO K sites.
  Hypothesis ADDIF : add_interface_stmt HO K sites.

  (* [comment removed for export] *)
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
  Variables (R : rctx) (CLc FB : list (cblock (hptr:=hptr))) (lo P HA DA Af : Z) (m : mem) (o : option hptr).
  Variables (self f : hptr) (bufsize : Z) (swapped : bool) (vmaj vmin snapshot linktype ltext prec brk : Z) (header : pkthdr).
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
  Hypothesis P1 : (0 < P)%Z.  Hypothesis P2 : (P mod 16 = 0)%Z.  Hypothesis P4 : (P + 680 <= CEILZ)%Z.
  Hypothesis P5 : (P + 680 <= 65536 \/ 348160 <= P)%Z.  Hypothesis P6 : (P + 680 <= utp R - 200 \/ utp R - 200 + 4096 <= P)%Z.
  Hypothesis A1 : (0 < Af)%Z.  Hypothesis A4 : (Af + 1264 <= CEILZ)%Z.
  Hypothesis W1 : (1 <= snapshot <= INT_MAX)%Z.  Hypothesis W2 : (0 <= bufsize <= 2^30)%Z.
  Hypothesis W5 : brk = 0%Z.  Hypothesis W6 : prec = 0%Z.
  Hypothesis W7 : (0 <= vmaj < 2^16)%Z.  Hypothesis W8 : (0 <= vmin < 2^16)%Z.
  Hypothesis W9 : (0 <= linktype < 2^31)%Z.  Hypothesis W10 : (-2^31 <= ltext < 2^31)%Z.

  Let POSTQ := next_packet_post K ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc R CLc FB lo P HA DA m o.
  (* [comment removed for export] *)
  #[local] Abbreviation pv := (F_ngnextA.pv self f bufsize swapped vmaj vmin snapshot linktype ltext prec brk header).
  #[local] Abbreviation ngn_frame := (F_ngnextA.ngn_frame ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 P HA DA).
  #[local] Abbreviation ngn_final := (F_ngnextA.ngn_final K sp R CLc FB P HA DA m o).
  #[local] Abbreviation ngn_finalC := (F_ngnextA.ngn_finalC K sp R CLc FB P HA DA m o).
  #[local] Abbreviation ngn_final_C := (F_ngnextA.ngn_final_C K sp R CLc FB P HA DA m o).
  #[local] Abbreviation ngn_ret_m1 := (F_ngnextA.ngn_ret_m1 K ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc R CLc FB lo P HA DA m o BU).
  #[local] Abbreviation ngn_ret_0 := (F_ngnextA.ngn_ret_0 K ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc R CLc FB lo P HA DA m o BU).
  #[local] Abbreviation ngn_ret_1 := (F_ngnextA.ngn_ret_1 K ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc R CLc FB lo P HA DA m o BU).
  #[local] Abbreviation ngn_CLc_facts := (F_ngnextA.ngn_CLc_facts K R CLc FB).
  #[local] Abbreviation ngn_snp_call := (F_ngnextA.ngn_snp_call K HFL SFL SNPRINTF ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc R CLc FB lo P HA DA m o LO BU SPM TP ALN R1 R2 AH AD SPW P1 P4 P5).
  #[local] Abbreviation ngn_snp := (F_ngnextA.ngn_snp K HFL SFL SNPRINTF ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc R CLc FB lo P HA DA m o LO BU SPM TP ALN R1 R2 AH AD SPW P1 P4 P5).
  #[local] Abbreviation ngn_mcp := (F_ngnextA.ngn_mcp K HFL SFL ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc R CLc FB lo P HA DA m o LO BU ALN R1 R2 AH AD SPW P1 P4 P5 P6).
  #[local] Abbreviation PCAPRC_errbuf := (F_ngnextA.PCAPRC_errbuf K sp R lo P HA DA LO BU ALN R1 R2 AH AD SPW P1).

  Ltac norm_g :=
    unfold F_ngnextA.pv; unfold pcap_blocks; unfold psize; unfold is_ng;
    cbn [pc_self pc_rfile pc_bufsize pc_bufalloc pc_buffer pc_bufdata pc_swapped pc_version_major pc_version_minor pc_snapshot pc_linktype
         pc_linktype_ext pc_tstamp_precision pc_break_loop pc_errbuf pc_header pc_priv priv_cells ng_of ng_ifaces_ptr_of
         set_bufdata set_errbuf set_buffer set_ng set_priv];
    unfold PCAP_NG_SF_TOTAL, PCAP_PRIV_OFF.
  Ltac norm_p :=
    unfold F_ngnextA.pv in *; unfold pcap_blocks in *; unfold psize in *; unfold is_ng in *;
    cbn [pc_self pc_rfile pc_bufsize pc_bufalloc pc_buffer pc_bufdata pc_swapped pc_version_major pc_version_minor pc_snapshot pc_linktype
         pc_linktype_ext pc_tstamp_precision pc_break_loop pc_errbuf pc_header pc_priv priv_cells ng_of ng_ifaces_ptr_of
         set_bufdata set_errbuf set_buffer set_ng set_priv] in *;
    unfold PCAP_NG_SF_TOTAL, PCAP_PRIV_OFF in *.

  #[local] Abbreviation ngn_pp := (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Startup_B__S3.F_ngnextB.ngn_pp K HFL SFL PP ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc R CLc FB lo P HA DA m o self f bufsize swapped vmaj vmin snapshot linktype ltext prec brk header LO BU SPM R1 R2 R3 AH AD SPW SP47 P1 P2 P4 P5 P6 W1 W2 W5 W6 W7 W8 W9 W10).

  (* [comment removed for export] *)
  Definition ngn_ts2__stmt : Prop := forall (ra' t0' t1' t2' a6' a7' x2 x3 x5 x6 x7 x8 x9 x10 x11 t4' t5' t6' cw ws wf : word) (hj1 hj2 : list byte) (m5 : mem) (ps : PState H hptr)
           (bq : hptr) (Bq Ix alloc doff rem : Z) (data eb : list Z) (sx : pcap_ng_sf) (ix : option hptr) (sec usec cap len bt : Z) (dw : cell) (dj : list byte) (ccs : list cell),
      stk ssegs m5 lo (bv_unsigned sp + -160) ->
      rw_cells ssegs m5 (bv_unsigned sp + -160) (ngn_frame dj ccs) -> cells_size ccs = 24%nat -> mem_inv ssegs m5 ->
      GIo K R ps (CLc ++ pcap_blocks (pv bq alloc data eb sx ix) P Bq Ix) FB m5 ->
      PCAPR (hptr:=hptr) P (pv bq alloc data eb sx ix) (pcap_blocks (pv bq alloc data eb sx ix) P Bq Ix) FB m5 ->
      agrees_on (fun a => client_keeps CLc (bv_unsigned sp) a /\ ~ (HA <= a < HA + 24) /\ ~ (DA <= a < DA + 8))%Z m m5 ->
      rw_cells ssegs m5 HA [CB 8 hj1; CB 8 hj2; C4 (Z_to_bv 64 cap); C4 (Z_to_bv 64 len)] -> rw_cells ssegs m5 DA [dw] -> csize dw = 8%nat ->
      (bv_unsigned cw mod 2^32 = cap)%Z -> ws = Z_to_bv 64 sec -> Z_to_bv 64 (bv_swrap 32 (bv_unsigned wf)) = Z_to_bv 64 usec ->
      Forall (fun x => 0 <= x < 256)%Z data -> (0 <= doff)%Z -> (doff mod 4 = 0)%Z -> (0 <= rem)%Z -> (doff + rem <= Z.of_nat (length data))%Z ->
      (Z.of_nat (length data) < 2^31)%Z -> (0 <= len < 2^32)%Z -> (0 <= bt < 2^32)%Z -> ps_outfile ps = o ->
      implM ssegs (match get_from_block_data (mkCursor doff rem bt) cap with
                   | inl e => mret ((-1)%Z, mkHdr sec usec cap len, set_errbuf e (pv bq alloc data eb sx ix))
                   | inr (doff', _) =>
                     let '(hdr, d) := pcapint_post_process linktype swapped (mkHdr sec usec cap len) (zskipn doff' data) in
                     mret (1%Z, hdr, set_bufdata (zfirstn doff' data ++ d) (pv bq alloc data eb sx ix))
                   end) ps POSTQ
        (MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -160)) gp tp t0' t1' t2' (Z_to_bv 64 (-1)) (Z_to_bv 64 (P + 216))
                 (Z_to_bv 64 rem) ws cw (Z_to_bv 64 (s32 bt)) wf (Z_to_bv 64 (Bq + doff)) a6' a7'
                 x2 x3 (Z_to_bv 64 P) x5 x6 x7 x8 x9 x10 x11 (Z_to_bv 64 HA) t4' t5' t6') F (Z_to_bv 64 0x17a8c) fc None m5 (seg_rom ssegs)).
  Section Sz19.
  Variables ra' t0' t1' t2' a6' a7' x2 x3 x5 x6 x7 x8 x9 x10 x11 t4' t5' t6' cw ws wf hj1 hj2 m5 ps bq Bq Ix alloc doff rem data eb sx ix sec usec cap len bt dw dj ccs : ltac2:(SecDiet.SzSec.tyM 'ngn_ts2__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra').
  Lemma ngn_ts2__body : ltac2:(SecDiet.SzSec.bodyP 'ngn_ts2__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof using AD AH ALN BU HFL LO P1 P2 P4 P5 P6 PP R1 R2 R3 SFL SNPRINTF SP47 SPM SPW TP W1 W10 W2 W5 W6 W7 W8 W9. pin_using (fun (AD AH ALN BU HFL LO P1 P2 P4 P5 P6 PP R1 R2 R3 SFL SNPRINTF SP47 SPM SPW TP W1 W10 W2 W5 W6 W7 W8 W9 : unit) => tt).
    intros ST5 FR5 Hccs MI5 G5 PC5 AG5 HH HD Hd Hcw -> Hwf DRNG Hdoff Hd4 Hrem Hdr Hl31 Hlen Hbt OF5.
    pose proof (bv_unsigned_in_range 64 sp) as RSP.
    pose proof (bv_unsigned_in_range 64 cw) as RCW. change (bv_modulus 64) with (2^64)%Z in RCW.
    assert (CAP : (0 <= cap < 2^32)%Z) by (rewrite <- Hcw; Z.div_mod_to_equations; lia).
    pose proof PC5 as (Afx & Hin & (Bx' & Ix' & jx' & padx & bsx' & EPB & CELLS & PRIV & BUF & PFX & IFS & WF)).
    pose proof G5 as G5e. rewrite EPB in G5e.
    pose proof (GIo_PB_block K _ _ _ _ _ _ _ _ _ G5e ltac:(right; left; reflexivity)) as (K1 & K2 & K3 & K4 & K5 & K6).
    unfold F_ngnextA.pv, pcap_blocks, psize, is_ng in EPB, K1, K2, K3, K4, K5, K6. cbn [pc_self pc_buffer pc_bufalloc pc_priv] in EPB, K1, K2, K3, K4, K5, K6.
    assert (EBX : Bx' = Bq) by congruence. subst Bx'. clear EPB G5e CELLS PRIV BUF PFX IFS WF.
    pose proof FR5 as FRJ. unfold F_ngnextA.ngn_frame in FRJ. apply rw_cells_app in FRJ as [FRJ _].
    hide FR5. hide HD.
    pose proof (munch_refl [(HA, HA + 16)]%Z m5) as MU. pose proof (wmono_refl ssegs m5) as WM.
    unfold implM. iprefix.
    step. rewrite ?Z.add_0_r. rewrite Hwf.
    step. step.
    replace (Z_to_bv 64 (Z.shiftr (bv_unsigned (Z_to_bv 64 (Z.shiftl (bv_unsigned cw) 32))) 32)) with (Z_to_bv 64 cap).
    2:{ rewrite Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia. rewrite unsigned_lit_wrap. rewrite <- Hcw. f_equal. Z.div_mod_to_equations. nia. }
    step. step.
    unfold get_from_block_data. cbn [cur_remaining cur_off cur_block_type].
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      assert (AGD : agrees_on (fun a => outside [(HA, HA + 16)]%Z a) m5 mm) by (eapply agrees_on_of_munch; [exact MU | exact WM | intros a _ Ho; exact Ho]);
      assert (G5' : GIo K R ps (CLc ++ pcap_blocks (pv bq alloc data eb sx ix) P Bq Ix) FB mm)
        by (eapply (GIo_pcap_frame K HFL SFL); [exact G5 | exact MU | exact WM |]; apply Forall_cons; [left; cbn [fst snd]; unfold rc_lo, rc_spmain in *; lia| apply Forall_nil]);
      rename mm into m5' end.
    unhide FR5. unhide HD.
    apply (agrees_rw_cells _ _ _ _ _ AGD) in FR5; [| intros a Ha; unfold F_ngnextA.ngn_frame in Ha; rewrite !cells_size_app in Ha; cbn [outside cells_size csize Nat.add] in *; rewrite Hccs in Ha; lia].
    apply (agrees_rw_cells _ _ _ _ _ AGD) in HD; [| intros a Ha; cbn [outside cells_size csize Nat.add] in *; rewrite Hd in Ha; lia].
    assert (PC5' : PCAPR (hptr:=hptr) P (pv bq alloc data eb sx ix) (pcap_blocks (pv bq alloc data eb sx ix) P Bq Ix) FB m5').
    { eapply PCAPR_agree; [exact AGD| | exact PC5]. intros a Ha. cbn [outside]. pose proof (in_PB_below K _ _ _ _ _ _ _ G5 Ha). unfold rc_lo in LO. lia. }
    assert (AG5' : agrees_on (fun a => client_keeps CLc (bv_unsigned sp) a /\ ~ (HA <= a < HA + 24) /\ ~ (DA <= a < DA + 8))%Z m m5').
    { eapply agrees_on_trans; [exact AG5|]. eapply agrees_on_weaken; [exact AGD|]. intros a [_ [Hn _]]; cbn [outside]; lia. }
    assert (MI5' : mem_inv ssegs m5') by assumption. assert (ST5' : stk ssegs m5' lo (bv_unsigned sp + -160)) by assumption.
    clear AGD G5 AG5 PC5 FRJ.
    hide FR5. hide HD. step. unhide FR5. unhide HD. clear MU WM.
    if_cases BR; zify_cond BR.
    - (* [comment removed for export] *)
      rewrite ?unsigned_lit in BR by lia.
      replace (rem <? cap) with false by (symmetry; apply Z.ltb_ge; lia). cbv iota. cbv beta.
      apply evt_done. eapply ngn_pp; [exact ST5' | exact FR5 | exact Hccs | exact MI5' | exact G5' | exact PC5' | exact AG5' | exact HH | exact HD | exact Hd
                                      | reflexivity | reflexivity | exact DRNG | lia | exact Hd4 | lia | exact Hl31 | exact Hlen | exact OF5].
    - (* [comment removed for export] *)
      rewrite ?unsigned_lit in BR by lia.
      replace (rem <? cap) with true by (symmetry; apply Z.ltb_lt; lia). cbv iota.
      pose proof (munch_refl ([] : list (Z * Z)) m5') as MU. pose proof (wmono_refl ssegs m5') as WM.
      hide FR5. hide HD. hide HH.
      step. step. step. step. step.
      unhide FR5. unhide HD. unhide HH.
      assert (MSG : fmt_at m5' NGN_FMT_TOO_SHORT "block of type %u in pcapng dump file is too short"%string)
        by (apply fmt_at_intro; [exact MI5' | vm_compute; reflexivity | unfold NGN_FMT_TOO_SHORT; lia | unfold NGN_FMT_TOO_SHORT; cbn; lia]).
      unfold NGN_FMT_TOO_SHORT in MSG.
      eapply (ngn_snp_call 0x17ab8) with (m5 := m5') (ps := ps) (p' := pv bq alloc data eb sx ix) (dw := dw) (dj := dj) (ccs := ccs) (args := [AInt (s32 bt)]);
        [exact ST5' | exact FR5 | exact Hccs | exact MI5' | | exact MSG | reflexivity | cbn; lia | cbn; apply Forall2_cons; [reflexivity| apply Forall2_nil] | lia | reflexivity |].
      { split; [exact G5'|]. split; [apply PCAPR_closable_of; exact PC5'|]. split; [exact AG5'|]. split; [exact HH|]. split; [reflexivity|].
        split; [exact HD|]. split; [exact Hd| exact OF5]. }
      intros m6 t0'' t1'' t2'' a0'' a1'' a2'' a3'' a4'' a5'' a6'' a7'' t3'' t4'' t5'' t6'' ST6 FR6 MI6 FIN6.
      destruct (FIN6 (Msg.block_too_short bt)) as (G6 & PC6 & AG6 & HH6 & Hh6 & HD6 & Hd6 & OF6).
      destruct (rw_cells_forget _ _ _ _ HD6) as [dwj HD6']. clear HD6. cbn [cells_size] in HD6'. rewrite Hd6 in HD6'. change (8 + 0)%nat with 8%nat in HD6'.
      pose proof FR6 as FRJ. unfold F_ngnextA.ngn_frame in FRJ. apply rw_cells_app in FRJ as [FRJ _].
      clear MU WM. pose proof (munch_refl [(DA, DA + 8)]%Z m6) as MU. pose proof (wmono_refl ssegs m6) as WM.
      hide FR6. hide HH6.
      step. pstep. step.
      unhide FR6. unhide HH6.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
        assert (AGD : agrees_on (fun a => outside [(DA, DA + 8)]%Z a) m6 mm) by (eapply agrees_on_of_munch; [exact MU | exact WM | intros a _ Ho; exact Ho]);
        assert (G7 : GIo K R ps (CLc ++ pcap_blocks (pv bq alloc data eb sx ix) P Bq Ix) FB mm)
          by (eapply (GIo_pcap_frame K HFL SFL); [exact G6 | exact MU | exact WM |]; apply Forall_cons; [left; cbn [fst snd]; unfold rc_lo, rc_spmain in *; lia| apply Forall_nil]);
        rename mm into m7 end.
      apply (agrees_rw_cells _ _ _ _ _ AGD) in FR6; [| intros a Ha; unfold F_ngnextA.ngn_frame in Ha; rewrite !cells_size_app in Ha; cbn [outside cells_size csize Nat.add] in *; rewrite Hccs in Ha; lia].
      apply (agrees_rw_cells _ _ _ _ _ AGD) in HH6; [| intros a Ha; cbn [outside cells_size csize Nat.add] in *; rewrite ?Hh6 in Ha; lia].
      apply evt_done. eapply ngn_ret_m1; [assumption | exact FR6 | exact Hccs | assumption |].
      split; [exact G7|]. split.
      { eapply PCAPR_closable_agree; [exact AGD| | exact PC6]. intros a Ha. cbn [outside]. pose proof (in_PB_below K _ _ _ _ _ _ _ G6 Ha). unfold rc_lo in LO. lia. }
      split. { eapply agrees_on_trans; [exact AG6|]. eapply agrees_on_weaken; [exact AGD|]. intros a [_ [_ Hn]]; cbn [outside]; lia. }
      split; [exact HH6|]. split; [exact Hh6|]. split; [eassumption| split; [reflexivity| exact OF6]].
  Qed.
  End Sz19.
  Lemma ngn_ts2 : ltac:(let t := eval cbv delta [ngn_ts2__stmt] in ngn_ts2__stmt in exact t).
  Proof using AD AH ALN BU HFL LO P1 P2 P4 P5 P6 PP R1 R2 R3 SFL SNPRINTF SP47 SPM SPW TP W1 W10 W2 W5 W6 W7 W8 W9. intros ra' t0' t1' t2' a6' a7' x2 x3 x5 x6 x7 x8 x9 x10 x11 t4' t5' t6' cw ws wf hj1 hj2 m5 ps bq Bq Ix alloc doff rem data eb sx ix sec usec cap len bt dw dj ccs. ltac2:(SecDiet.SzSec.closeP 'ngn_ts2__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.

  (* [comment removed for export] *)
  Definition ngn_ts__stmt : Prop := forall (ra' t0' t1' t2' a4' a6' x2 x3 x5 x6 x7 x8 x9 x10 x11 t4' t5' t6' iw cw : word) (hj1 hj2 : list byte) (m5 : mem) (ps : PState H hptr)
           (bq : hptr) (Bq Ix alloc doff rem : Z) (data eb : list Z) (sx : pcap_ng_sf) (ix : option hptr) (id t cap len bt : Z) (dw : cell) (dj : list byte) (ccs : list cell),
      stk ssegs m5 lo (bv_unsigned sp + -160) ->
      rw_cells ssegs m5 (bv_unsigned sp + -160) (ngn_frame dj ccs) -> cells_size ccs = 24%nat -> mem_inv ssegs m5 ->
      GIo K R ps (CLc ++ pcap_blocks (pv bq alloc data eb sx ix) P Bq Ix) FB m5 ->
      PCAPR (hptr:=hptr) P (pv bq alloc data eb sx ix) (pcap_blocks (pv bq alloc data eb sx ix) P Bq Ix) FB m5 ->
      agrees_on (fun a => client_keeps CLc (bv_unsigned sp) a /\ ~ (HA <= a < HA + 24) /\ ~ (DA <= a < DA + 8))%Z m m5 ->
      rw_cells ssegs m5 HA [CB 8 hj1; CB 8 hj2; C4 (Z_to_bv 64 cap); C4 (Z_to_bv 64 len)] -> rw_cells ssegs m5 DA [dw] -> csize dw = 8%nat ->
      (bv_unsigned iw mod 2^32 = id)%Z -> (bv_unsigned cw mod 2^32 = cap)%Z -> (0 <= id < ng_ifcount sx)%Z -> (0 <= t < 2^64)%Z ->
      Forall (fun x => 0 <= x < 256)%Z data -> (0 <= doff)%Z -> (doff mod 4 = 0)%Z -> (0 <= rem)%Z -> (doff + rem <= Z.of_nat (length data))%Z ->
      (Z.of_nat (length data) < 2^31)%Z -> (0 <= len < 2^32)%Z -> (0 <= bt < 2^32)%Z -> ps_outfile ps = o ->
      implM ssegs (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Startup_B__S3.F_ngnextB.ngn_tsK (mkFound id t cap len (mkCursor doff rem bt)) (pv bq alloc data eb sx ix)) ps POSTQ
        (MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -160)) gp tp t0' t1' t2' (Z_to_bv 64 (-1)) (Z_to_bv 64 (P + 216))
                 (Z_to_bv 64 rem) iw cw (Z_to_bv 64 (s32 bt)) a4' (Z_to_bv 64 (Bq + doff)) a6' (Z_to_bv 64 t)
                 x2 x3 (Z_to_bv 64 P) x5 x6 x7 x8 x9 x10 x11 (Z_to_bv 64 HA) t4' t5' t6') F (Z_to_bv 64 0x17a04) fc None m5 (seg_rom ssegs)).
  Section Sz20.
  Variables ra' t0' t1' t2' a4' a6' x2 x3 x5 x6 x7 x8 x9 x10 x11 t4' t5' t6' iw cw hj1 hj2 m5 ps bq Bq Ix alloc doff rem data eb sx ix id t cap len bt dw dj ccs : ltac2:(SecDiet.SzSec.tyM 'ngn_ts__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra').
  Lemma ngn_ts__body : ltac2:(SecDiet.SzSec.bodyP 'ngn_ts__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof using AD AH ALN BU HFL LO P1 P2 P4 P5 P6 PP R1 R2 R3 SFL SNPRINTF SP47 SPM SPW TP W1 W10 W2 W5 W6 W7 W8 W9. pin_using (fun (AD AH ALN BU HFL LO P1 P2 P4 P5 P6 PP R1 R2 R3 SFL SNPRINTF SP47 SPM SPW TP W1 W10 W2 W5 W6 W7 W8 W9 : unit) => tt).
    intros ST5 FR5 Hccs MI5 G5 PC5 AG5 HH HD Hd Hiw Hcw Hid Ht DRNG Hdoff Hd4 Hrem Hdr Hl31 Hlen Hbt OF5.
    pose proof (bv_unsigned_in_range 64 sp) as RSP.
    pose proof PC5 as (Afx & Hin & (Bx' & Ix' & jx' & padx & bsx' & EPB & CELLS & PRIV & BUF & PFX & IFS & WF)).
    pose proof G5 as G5e. rewrite EPB in G5e.
    pose proof (PB_apart K _ _ _ _ _ _ _ _ _ _ G5e eq_refl) as [APB API].
    pose proof WF as (_ & _ & W3 & W4 & _ & _ & _ & _ & _ & _ & _ & _ & WNG & WBB).
    unfold F_ngnextA.pv, pcap_blocks, psize, is_ng in EPB, API, WNG. cbn [pc_self pc_buffer pc_bufalloc pc_priv] in EPB, API, WNG.
    destruct WNG as (UT & WMB & WIC & WIS).
    assert (EBX : Bx' = Bq) by congruence. subst Bx'.
    (* [comment removed for export] *)
    unfold ifaces_ok, F_ngnextA.pv in IFS. cbn [pc_priv] in IFS.
    destruct ix as [q|]; [| destruct IFS as (_ & _ & IC0 & _); exfalso; clear -IC0 Hid; lia].
    destruct IFS as (js & tail & Ljs & HIF & EIC & ICS & ISZ & IWF).
    pose proof (GIo_PB_block K _ _ _ _ _ _ _ _ _ G5e ltac:(right; right; left; reflexivity)) as (I1 & I2 & I3 & I4 & I5 & I6).
    set (k := Z.to_nat id).
    assert (Hk : (k < length (ng_ifaces sx))%nat) by (subst k; clear -Hid EIC; lia).
    pose proof (ifs_cells_slot _ _ _ _ _ k HIF ltac:(rewrite length_rev; exact Ljs) ltac:(rewrite length_rev; exact Hk)) as SLOT.
    replace (Ix' + 40 * Z.of_nat k)%Z with (Ix' + 40 * id)%Z in SLOT by (subst k; lia).
    rewrite (rev_nth (ng_ifaces sx) ngif0 Hk) in SLOT.
    set (ifc := nth (length (ng_ifaces sx) - S k) (ng_ifaces sx) ngif0) in SLOT.
    set (jfc := nth k (rev js) (mkIJ [] [] (Z_to_bv 64 0))) in SLOT.
    assert (EIFC : nth_slot (ng_ifaces sx) (ng_ifcount sx) id = ifc).
    { unfold nth_slot. subst ifc. f_equal. rewrite EIC. subst k. clear -Hid. lia. }
    assert (WFC : if_wf ifc).
    { apply (proj1 (List.Forall_forall _ _) IWF). subst ifc. apply nth_In. clear -Hk. lia. }
    destruct WFC as [TSR SFR].
    pose proof (rw_cells_bound _ _ _ _ HIF) as IB. rewrite cells_size_app, ifs_cells_size in IB by (rewrite length_rev; exact Ljs). cbn [cells_size csize Nat.add] in IB. rewrite length_rev in IB.
    assert (SLB : (Ix' <= Ix' + 40 * id /\ Ix' + 40 * id + 40 <= Ix' + 40 * ng_ifaces_size sx)%Z) by (clear -Hid EIC ICS; nia).
    clearbody ifc jfc. clear HIF.
    unfold if_cells in SLOT.
    (* [comment removed for export] *)
    unfold OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Startup_B__S3.F_ngnextB.ngn_tsK. cbn [f_interface_id f_t f_caplen f_len f_cursor ng_of pc_priv pc_linktype pc_swapped pc_bufdata F_ngnextA.pv]. rewrite EIFC.
    unfold priv_cells, F_ngnextA.pv in PRIV. cbn [pc_priv] in PRIV. unfold ng_cells, PCAP_PRIV_OFF in PRIV.
    pose proof FR5 as FRJ. unfold F_ngnextA.ngn_frame in FRJ. apply rw_cells_app in FRJ as [FRJ _].
    hide FR5. hide BUF. hide CELLS. hide HD. hide HH.
    pose proof (munch_refl ([] : list (Z * Z)) m5) as MU. pose proof (wmono_refl ssegs m5) as WM.
    unfold implM. iprefix.
    step. step. step. step. step. step. rewrite (mulhu_40 iw id Hiw).
    step. step. step. step. rewrite (sx32_small (ngscale_code (if_scale_type ifc))) by (destruct (if_scale_type ifc); cbn; lia).
    step. rewrite (divu_lit t (if_tsresol ifc)) by lia.
    step. step. step. step. rewrite (frac_word t (if_tsresol ifc)) by lia.
    assert (FR : (0 <= t mod if_tsresol ifc < if_tsresol ifc)%Z) by (apply Z.mod_pos_bound; lia).
    unhide FR5. unhide BUF. unhide CELLS. unhide HD. unhide HH.
    (* [comment removed for export] *)
    assert (TAIL : forall (a6'' a7'' t1'' t2'' : word) (fr : Z), (0 <= fr < 2^64)%Z ->
      evt ssegs (fun ms' => impl ssegs (at_node ssegs) (npeek ssegs)
        ((match get_from_block_data (mkCursor doff rem bt) cap with
          | inl e => mret ((-1)%Z, mkHdr (s64 (u64 (t / if_tsresol ifc + if_tsoffset ifc))) (s32 fr) cap len, set_errbuf e (pv bq alloc data eb sx (Some q)))
          | inr (doff', _) =>
            let '(hdr, d) := pcapint_post_process linktype swapped (mkHdr (s64 (u64 (t / if_tsresol ifc + if_tsoffset ifc))) (s32 fr) cap len) (zskipn doff' data) in
            mret (1%Z, hdr, set_bufdata (zfirstn doff' data ++ d) (pv bq alloc data eb sx (Some q)))
          end) ps) (epost (fun p : Z * pkthdr * pcap hptr hptr * PState H hptr => POSTQ p.1 p.2)) ms')
        (MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -160)) gp tp (Z_to_bv 64 (Ix' + 40 * id)) t1'' t2'' (Z_to_bv 64 (-1)) (Z_to_bv 64 (P + 216))
                 (Z_to_bv 64 rem) (Z_to_bv 64 (if_tsoffset ifc + t / if_tsresol ifc)) cw (Z_to_bv 64 (s32 bt)) (Z_to_bv 64 fr) (Z_to_bv 64 (Bq + doff)) a6'' a7''
                 x2 x3 (Z_to_bv 64 P) x5 x6 x7 x8 x9 x10 x11 (Z_to_bv 64 HA) t4' t5' t6') F (Z_to_bv 64 0x17a8c) fc None m5 (seg_rom ssegs))).
    { intros a6'' a7'' t1'' t2'' fr Hfr. apply evt_done.
      eapply ngn_ts2; [exact ST5 | exact FR5 | exact Hccs | exact MI5 | exact G5 | exact PC5 | exact AG5 | exact HH | exact HD | exact Hd | exact Hcw
                      | apply sec_word_eq | apply usec_word_eq; exact Hfr | exact DRNG | exact Hdoff | exact Hd4 | exact Hrem | exact Hdr | exact Hl31 | exact Hlen | exact Hbt | exact OF5]. }
    hide FR5. hide BUF. hide CELLS. hide HD. hide HH.
    pose proof (mod_range64 t (if_tsresol ifc) TSR) as FR64.
    destruct (if_scale_type ifc) eqn:EST; try rewrite EST in SLOT; try rewrite EST in SFR; cbn [ngscale_code is_dec] in SLOT, SFR |- *.
    - (* [comment removed for export] *)
      step. if_false. step. step. if_false. step. step. if_true. apply (TAIL _ _ _ _ (t mod if_tsresol ifc)). exact FR64.
    - (* [comment removed for export] *)
      pose proof (SFR eq_refl) as SF.
      step. if_false. step. step. if_true. step. step. rewrite (mul_word_u64 (if_scale_factor ifc) (t mod if_tsresol ifc)) by lia.
      apply (TAIL _ _ _ _ (u64 (t mod if_tsresol ifc * if_scale_factor ifc))). apply u64_range.
    - (* [comment removed for export] *)
      pose proof (SFR eq_refl) as SF.
      step. if_false. step. step. if_false. step. step. if_false. step. step. rewrite (divu_lit (t mod if_tsresol ifc) (if_scale_factor ifc)) by lia. step.
      apply (TAIL _ _ _ _ (t mod if_tsresol ifc / if_scale_factor ifc)). apply div_range64; [exact FR64| lia].
    - (* [comment removed for export] *)
      pose proof (u64_range (t mod if_tsresol ifc * ng_user_tsresol sx)) as UR.
      step. if_true. step. step. if_true. step. step. step. rewrite (mul_word_u64 (ng_user_tsresol sx) (t mod if_tsresol ifc)) by lia.
      step. rewrite (divu_lit (u64 (t mod if_tsresol ifc * ng_user_tsresol sx)) (if_tsresol ifc)) by lia. step.
      apply (TAIL _ _ _ _ (u64 (t mod if_tsresol ifc * ng_user_tsresol sx) / if_tsresol ifc)). apply div_range64; [exact UR| lia].
    - (* [comment removed for export] *)
      pose proof (u64_range (t mod if_tsresol ifc * ng_user_tsresol sx)) as UR.
      step. if_true. step. step. if_false. step. step. if_false. step. step. step. rewrite (mul_word_u64 (ng_user_tsresol sx) (t mod if_tsresol ifc)) by lia.
      step. rewrite (divu_lit (u64 (t mod if_tsresol ifc * ng_user_tsresol sx)) (if_tsresol ifc)) by lia. step.
      apply (TAIL _ _ _ _ (u64 (t mod if_tsresol ifc * ng_user_tsresol sx) / if_tsresol ifc)). apply div_range64; [exact UR| lia].
  Qed.
  End Sz20.
  Lemma ngn_ts : ltac:(let t := eval cbv delta [ngn_ts__stmt] in ngn_ts__stmt in exact t).
  Proof using AD AH ALN BU HFL LO P1 P2 P4 P5 P6 PP R1 R2 R3 SFL SNPRINTF SP47 SPM SPW TP W1 W10 W2 W5 W6 W7 W8 W9. intros ra' t0' t1' t2' a4' a6' x2 x3 x5 x6 x7 x8 x9 x10 x11 t4' t5' t6' iw cw hj1 hj2 m5 ps bq Bq Ix alloc doff rem data eb sx ix id t cap len bt dw dj ccs. ltac2:(SecDiet.SzSec.closeP 'ngn_ts__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.

  (* [comment removed for export] *)
  Definition ngn_found__stmt : Prop := forall (ra' t0' t1' t2' a4' a6' x2 x3 x5 x6 x7 x8 x9 x10 x11 t4' t5' t6' iw cw : word) (hj1 hj2 : list byte) (m5 : mem) (ps : PState H hptr)
           (bq : hptr) (Bq Ix alloc doff rem : Z) (data eb : list Z) (sx : pcap_ng_sf) (ix : option hptr) (id t cap len bt : Z) (dw : cell) (dj : list byte) (ccs : list cell),
      stk ssegs m5 lo (bv_unsigned sp + -160) ->
      rw_cells ssegs m5 (bv_unsigned sp + -160) (ngn_frame dj ccs) -> cells_size ccs = 24%nat -> mem_inv ssegs m5 ->
      GIo K R ps (CLc ++ pcap_blocks (pv bq alloc data eb sx ix) P Bq Ix) FB m5 ->
      PCAPR (hptr:=hptr) P (pv bq alloc data eb sx ix) (pcap_blocks (pv bq alloc data eb sx ix) P Bq Ix) FB m5 ->
      agrees_on (fun a => client_keeps CLc (bv_unsigned sp) a /\ ~ (HA <= a < HA + 24) /\ ~ (DA <= a < DA + 8))%Z m m5 ->
      rw_cells ssegs m5 HA [CB 8 hj1; CB 8 hj2; C4 (Z_to_bv 64 cap); C4 (Z_to_bv 64 len)] -> rw_cells ssegs m5 DA [dw] -> csize dw = 8%nat ->
      (bv_unsigned iw mod 2^32 = id)%Z -> (bv_unsigned cw mod 2^32 = cap)%Z -> (0 <= t < 2^64)%Z ->
      Forall (fun x => 0 <= x < 256)%Z data -> (0 <= doff)%Z -> (doff mod 4 = 0)%Z -> (0 <= rem)%Z -> (doff + rem <= Z.of_nat (length data))%Z ->
      (Z.of_nat (length data) < 2^31)%Z -> (0 <= len < 2^32)%Z -> (0 <= bt < 2^32)%Z -> ps_outfile ps = o ->
      implM ssegs (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Startup_B__S3.F_ngnextB.ngn_foundK (mkFound id t cap len (mkCursor doff rem bt)) (pv bq alloc data eb sx ix)) ps POSTQ
        (MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -160)) gp tp t0' t1' t2' (Z_to_bv 64 (-1)) (Z_to_bv 64 (P + 216))
                 (Z_to_bv 64 rem) iw cw (Z_to_bv 64 (s32 bt)) a4' (Z_to_bv 64 (Bq + doff)) a6' (Z_to_bv 64 t)
                 x2 x3 (Z_to_bv 64 P) x5 x6 x7 x8 x9 x10 x11 (Z_to_bv 64 HA) t4' t5' t6') F (Z_to_bv 64 0x179b4) fc None m5 (seg_rom ssegs)).
  Section Sz21.
  Variables ra' t0' t1' t2' a4' a6' x2 x3 x5 x6 x7 x8 x9 x10 x11 t4' t5' t6' iw cw hj1 hj2 m5 ps bq Bq Ix alloc doff rem data eb sx ix id t cap len bt dw dj ccs : ltac2:(SecDiet.SzSec.tyM 'ngn_found__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra').
  Lemma ngn_found__body : ltac2:(SecDiet.SzSec.bodyP 'ngn_found__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof using AD AH ALN BU HFL LO P1 P2 P4 P5 P6 PP R1 R2 R3 SFL SNPRINTF SP47 SPM SPW TP W1 W10 W2 W5 W6 W7 W8 W9. pin_using (fun (AD AH ALN BU HFL LO P1 P2 P4 P5 P6 PP R1 R2 R3 SFL SNPRINTF SP47 SPM SPW TP W1 W10 W2 W5 W6 W7 W8 W9 : unit) => tt).
    intros ST5 FR5 Hccs MI5 G5 PC5 AG5 HH HD Hd Hiw Hcw Ht DRNG Hdoff Hd4 Hrem Hdr Hl31 Hlen Hbt OF5.
    pose proof (bv_unsigned_in_range 64 sp) as RSP.
    pose proof (bv_unsigned_in_range 64 iw) as RIW. change (bv_modulus 64) with (2^64)%Z in RIW.
    pose proof (bv_unsigned_in_range 64 cw) as RCW. change (bv_modulus 64) with (2^64)%Z in RCW.
    assert (IDR : (0 <= id < 2^32)%Z) by (rewrite <- Hiw; apply Z.mod_pos_bound; lia).
    assert (CAP : (0 <= cap < 2^32)%Z) by (rewrite <- Hcw; apply Z.mod_pos_bound; lia).
    pose proof PC5 as (Afx & Hin & (Bx' & Ix' & jx' & padx & bsx' & EPB & CELLS & PRIV & BUF & PFX & IFS & WF)).
    pose proof WF as (_ & _ & W3 & W4 & _ & _ & _ & _ & _ & _ & _ & _ & WNG & WBB).
    unfold F_ngnextA.pv in WNG. cbn [pc_priv] in WNG. destruct WNG as (UT & WMB & WIC & WIS).
    (* [comment removed for export] *)
    unfold OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Startup_B__S3.F_ngnextB.ngn_foundK. cbn [f_interface_id f_caplen ng_of pc_priv pc_snapshot F_ngnextA.pv].
    unfold pcap_cells_gen, pc_pre, hdr_cells, pc_ops, np_entry, cleanup_entry, is_ng, PCAP_PRIV_OFF, F_ngnextA.pv in CELLS.
    cbn [app pc_bufsize pc_break_loop pc_swapped pc_version_major pc_version_minor pc_snapshot pc_linktype pc_linktype_ext pc_tstamp_precision pc_header pc_priv pk_next_ng pk_cleanup_ng PK] in CELLS.
    unfold priv_cells, F_ngnextA.pv in PRIV. cbn [pc_priv] in PRIV. unfold ng_cells, PCAP_PRIV_OFF in PRIV.
    pose proof FR5 as FRJ. unfold F_ngnextA.ngn_frame in FRJ. apply rw_cells_app in FRJ as [FRJ _].
    hide FR5. hide BUF. hide HD. hide HH. hide IFS.
    pose proof (munch_refl ([] : list (Z * Z)) m5) as MU. pose proof (wmono_refl ssegs m5) as WM.
    unfold implM. iprefix.
    step. step. step. step.
    if_cases BR; zify_cond BR.
    - (* [comment removed for export] *)
      rewrite sextw_mod, Hiw, (unsigned_sx32' (ng_ifcount sx)) in BR by lia.
      assert (LE : (ng_ifcount sx <= id)%Z) by (pose proof (sxu_mono id (ng_ifcount sx) IDR WIC); lia).
      replace (ng_ifcount sx <=? id) with true by (symmetry; apply Z.leb_le; exact LE). cbv iota.
      step. step. step. step. step. step. step.
      unhide FR5. unhide HD. unhide HH. unhide IFS.
      assert (MSG : fmt_at m5 NGN_FMT_NOIDB "a packet arrived on interface %u, but there's no Interface Description Block for that interface"%string)
        by (apply fmt_at_intro; [exact MI5 | vm_compute; reflexivity | unfold NGN_FMT_NOIDB; lia | unfold NGN_FMT_NOIDB; cbn; lia]).
      unfold NGN_FMT_NOIDB in MSG.
      apply evt_done. eapply ngn_snp with (args := [AInt (bv_swrap 32 (bv_unsigned iw + 0))]);
        [exact ST5 | exact FR5 | exact Hccs | exact MI5 | | exact MSG | reflexivity | cbn; lia | cbn; apply Forall2_cons; [reflexivity| apply Forall2_nil]].
      split; [exact G5|]. split; [apply PCAPR_closable_of; exact PC5|]. split; [exact AG5|]. split; [exact HH|]. split; [reflexivity|].
      split; [exact HD|]. split; [exact Hd| exact OF5].
    - rewrite sextw_mod, Hiw, (unsigned_sx32' (ng_ifcount sx)) in BR by lia.
      assert (LT : (id < ng_ifcount sx)%Z) by (pose proof (sxu_mono id (ng_ifcount sx) IDR WIC); lia).
      replace (ng_ifcount sx <=? id) with false by (symmetry; apply Z.leb_gt; exact LT). cbv iota.
      unfold INT_MAX in W1.
      step. rewrite (sx32_small snapshot) by lia. step. step.
      if_cases BR2; zify_cond BR2.
      + (* [comment removed for export] *)
        rewrite sextw_mod, Hcw, ?(unsigned_lit snapshot) in BR2 by lia.
        pose proof (sxu_range cap CAP) as (SX1 & SX2 & SX3).
        assert (LE : (cap <= snapshot)%Z) by (destruct (Z_lt_dec cap (2^31)); [rewrite SX2 in BR2 by lia; lia| exfalso; specialize (SX3 ltac:(lia)); lia]).
        replace (snapshot <? cap) with false by (symmetry; apply Z.ltb_ge; exact LE). cbv iota.
        unhide FR5. unhide BUF. unhide HD. unhide HH. unhide IFS.
        apply evt_done. eapply ngn_ts; [exact ST5 | exact FR5 | exact Hccs | exact MI5 | exact G5 | exact PC5 | exact AG5 | exact HH | exact HD | exact Hd
                                      | exact Hiw | exact Hcw | lia | exact Ht | exact DRNG | exact Hdoff | exact Hd4 | exact Hrem | exact Hdr | exact Hl31 | exact Hlen | exact Hbt | exact OF5].
      + (* [comment removed for export] *)
        rewrite sextw_mod, Hcw, ?(unsigned_lit snapshot) in BR2 by lia.
        pose proof (sxu_range cap CAP) as (SX1 & SX2 & SX3).
        assert (LT2 : (snapshot < cap)%Z) by (destruct (Z_lt_dec cap (2^31)); [rewrite SX2 in BR2 by lia; lia| lia]).
        replace (snapshot <? cap) with true by (symmetry; apply Z.ltb_lt; exact LT2). cbv iota.
        step. step. step. step. step. step.
        unhide FR5. unhide HD. unhide HH. unhide IFS.
        assert (MSG : fmt_at m5 NGN_FMT_CAPLEN "invalid packet capture length %u, bigger than snaplen of %d"%string)
          by (apply fmt_at_intro; [exact MI5 | vm_compute; reflexivity | unfold NGN_FMT_CAPLEN; lia | unfold NGN_FMT_CAPLEN; cbn; lia]).
        unfold NGN_FMT_CAPLEN in MSG.
        eapply (ngn_snp_call 0x179e8) with (m5 := m5) (ps := ps) (p' := pv bq alloc data eb sx ix) (dw := dw) (dj := dj) (ccs := ccs)
                                            (args := [AInt (bv_swrap 32 (bv_unsigned cw + 0)); AInt snapshot]);
          [exact ST5 | exact FR5 | exact Hccs | exact MI5 | | exact MSG | reflexivity | cbn; lia | cbn; apply Forall2_cons; [reflexivity| apply Forall2_cons; [reflexivity| apply Forall2_nil]] | lia | reflexivity |].
        { split; [exact G5|]. split; [apply PCAPR_closable_of; exact PC5|]. split; [exact AG5|]. split; [exact HH|]. split; [reflexivity|].
          split; [exact HD|]. split; [exact Hd| exact OF5]. }
        intros m6 t0'' t1'' t2'' a0'' a1'' a2'' a3'' a4'' a5'' a6'' a7'' t3'' t4'' t5'' t6'' ST6 FR6 MI6 FIN6.
        pose proof (FIN6 (Msg.invalid_caplen_snaplen cap snapshot)) as FIN.
        pose proof FIN as (G6 & PC6 & AG6 & HH6 & Hh6 & HD6 & Hd6 & OF6).
        clear MU WM. pose proof (munch_refl ([] : list (Z * Z)) m6) as MU. pose proof (wmono_refl ssegs m6) as WM.
        hide FR6. hide HH6. hide HD6. step. unhide FR6. unhide HH6. unhide HD6.
        apply evt_done. eapply ngn_ret_m1; [exact ST6 | exact FR6 | exact Hccs | exact MI6 | exact FIN].
  Qed.
  End Sz21.
  Lemma ngn_found : ltac:(let t := eval cbv delta [ngn_found__stmt] in ngn_found__stmt in exact t).
  Proof using AD AH ALN BU HFL LO P1 P2 P4 P5 P6 PP R1 R2 R3 SFL SNPRINTF SP47 SPM SPW TP W1 W10 W2 W5 W6 W7 W8 W9. intros ra' t0' t1' t2' a4' a6' x2 x3 x5 x6 x7 x8 x9 x10 x11 t4' t5' t6' iw cw hj1 hj2 m5 ps bq Bq Ix alloc doff rem data eb sx ix id t cap len bt dw dj ccs. ltac2:(SecDiet.SzSec.closeP 'ngn_found__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.

End NgnCtx.

End WithCeil.

(* [comment removed for export] *)
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require ImgTgtUbsan.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_memchr__S3.
From OSSVerify.libpcap.fuzz_pcap.images Require Ubsan.
Module TwB.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Strings.String.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Tac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Arr OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Bytes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ZBridge OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ITree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Nodes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Decode OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.SysStep OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.MonadX OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Image OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ImgTgtUbsan.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Monad OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Fmt OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.StdioCore OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Stdio OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapPrelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapTypes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapPure OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Pcap OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prog OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Adapter__Spec.StartupModel.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.STRW_tac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_kit__Musl.StartupKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.CellsExtra.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.FmtFacts__S3.FmtFacts OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_memchr__S3.SfKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_memchr__S3.NpArith OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.FmtFacts__S3.PPFacts.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.GI.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.PcapRep.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Pcap_iface__S3.Pcap_iface.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_lock__S3.Pcap_iface_pp.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Pcap_iface__S3.Pcap_iface_ng.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcapng_blkA__S3.SfNgKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_lock__S3.PP_kit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_ngnextA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Startup_B__S3.F_ngnextB.TwB.
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
Local Ltac gio_ceil_fact :=
  match goal with
  | G : GIo _ _ _ _ _ _ |- _ => let H := fresh "CLO__" in pose proof (S3.PcapRep.TwB.GIo_ceil_lo _ _ _ _ _ _ G) as H; unfold rc_lo in H
  end.
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
Definition ifs_cells_slot__stmt : Prop := forall m I ifs js rest k,
  rw_cells usegs m I (ifs_cells ifs js ++ rest) -> length js = length ifs -> (k < length ifs)%nat ->
  rw_cells usegs m (I + 40 * Z.of_nat k) (if_cells (nth k ifs ngif0) (nth k js (mkIJ [] [] (Z_to_bv 64 0)))).
Section Sz1.
Variables m I : ltac2:(SecDiet.SzSec.tyM 'ifs_cells_slot__stmt "vvk" @m).
Lemma ifs_cells_slot__body : ltac2:(SecDiet.SzSec.bodyP 'ifs_cells_slot__stmt "vvk").
Proof using Type. pin_using tt.
  intros ifs.
 revert m I. induction ifs as [|i ifs IH]; intros m I js rest k HC Hl Hk; [cbn in Hk; lia|].
  destruct js as [|j js]; [cbn in Hl; lia|]. cbn [ifs_cells] in HC. rewrite <- app_assoc in HC.
  apply rw_cells_app in HC as [H1 H2]. rewrite if_cells_size in H2.
  destruct k as [|k].
  - cbn [nth]. replace (I + 40 * Z.of_nat 0)%Z with I by lia. exact H1.
  - cbn [nth]. replace (I + 40 * Z.of_nat (S k))%Z with (I + Z.of_nat 40 + 40 * Z.of_nat k)%Z by lia.
    apply (IH _ _ js rest k H2); cbn [length] in *; lia.
Qed.
End Sz1.
Lemma ifs_cells_slot : ltac:(let t := eval cbv delta [ifs_cells_slot__stmt] in ifs_cells_slot__stmt in exact t).
Proof using Type. intros m I ifs. ltac2:(SecDiet.SzSec.closeP 'ifs_cells_slot__body "vvk"). Qed.

(* [comment removed for export] *)
Lemma mulhu_40 : forall (iw : word) (id : Z), (bv_unsigned iw mod 2^32 = id)%Z ->
  Z_to_bv 64 (Z.shiftr (bv_unsigned (Z_to_bv 64 (Z.shiftl (bv_unsigned iw) 32)) * 171798691840) 64) = Z_to_bv 64 (40 * id).
Proof using Type. pin_using tt.
  intros iw id Hid. pose proof (bv_unsigned_in_range 64 iw) as R. change (bv_modulus 64) with (2^64)%Z in R.
  rewrite Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia. rewrite unsigned_lit_wrap.
  replace ((bv_unsigned iw * 2 ^ 32) mod 2 ^ 64)%Z with (id * 2^32)%Z by (rewrite <- Hid; Z.div_mod_to_equations; nia).
  f_equal. replace (id * 2 ^ 32 * 171798691840)%Z with ((40 * id) * 2^64)%Z by lia. rewrite Z.div_mul by lia. reflexivity.
Qed.

Lemma divu_lit : forall a b, (0 <= a < 2^64)%Z -> (0 < b < 2^64)%Z -> mul_div M_DIVU (Z_to_bv 64 a) (Z_to_bv 64 b) = Z_to_bv 64 (a / b).
Proof using Type. pin_using tt.
  intros a b Ha Hb. unfold mul_div. rewrite (unsigned_lit b) by lia. replace (b =? 0)%Z with false by (symmetry; apply Z.eqb_neq; lia).
  apply bv_eq. rewrite bv_divu_unsigned. rewrite (unsigned_lit a), (unsigned_lit b) by lia.
  rewrite unsigned_lit; [reflexivity|]. split; [apply Z.div_pos; lia|]. apply Z.div_lt_upper_bound; [lia|]. nia.
Qed.

Lemma zbv64_eq : forall a b, (a mod 2^64 = b mod 2^64)%Z -> Z_to_bv 64 a = Z_to_bv 64 b.
Proof using Type. pin_using tt. intros a b E. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64)%Z with (2^64)%Z. exact E. Qed.

Lemma swrap32_s32 : forall x, bv_swrap 32 x = s32 x.
Proof using Type. pin_using tt. intros x. unfold bv_swrap, s32, bv_wrap, bv_half_modulus, bv_modulus. change (2 ^ Z.of_N 32)%Z with (2^32)%Z. change (2 ^ (Z.of_N 32 - 1))%Z with (2^31)%Z. reflexivity. Qed.

Lemma divu_lit_mod : forall a b, (0 <= a)%Z -> (0 < b < 2^64)%Z -> mul_div M_DIVU (Z_to_bv 64 a) (Z_to_bv 64 b) = Z_to_bv 64 ((a mod 2^64) / b).
Proof using Type. pin_using tt.
  intros a b Ha Hb. rewrite (zbv64_eq a (a mod 2^64)) by (rewrite Z.mod_mod by lia; reflexivity).
  apply divu_lit; [| exact Hb]. Z.div_mod_to_equations. lia.
Qed.

Lemma frac_word : forall t b, (0 <= t < 2^64)%Z -> (0 < b < 2^64)%Z ->
  Z_to_bv 64 (bv_unsigned (Z_to_bv 64 t) - bv_unsigned (Z_to_bv 64 (bv_unsigned (Z_to_bv 64 (t / b)) * bv_unsigned (Z_to_bv 64 b))))
  = Z_to_bv 64 (t mod b).
Proof using Type. pin_using tt.
  intros t b Ht Hb.
  assert (Q : (0 <= t / b <= t)%Z) by (split; [apply Z.div_pos; lia| apply Z.div_le_upper_bound || idtac; Z.div_mod_to_equations; nia]).
  assert (QB : (0 <= t / b * b <= t)%Z) by (Z.div_mod_to_equations; nia).
  rewrite (unsigned_lit t), (unsigned_lit (t / b)), (unsigned_lit b) by lia. rewrite unsigned_lit by lia.
  f_equal. Z.div_mod_to_equations. nia.
Qed.

Lemma sec_word_eq : forall off q, Z_to_bv 64 (off + q) = Z_to_bv 64 (s64 (u64 (q + off))).
Proof using Type. pin_using tt. intros. apply zbv64_eq. unfold s64, u64. Z.div_mod_to_equations. lia. Qed.

Lemma usec_word_eq : forall x, (0 <= x < 2^64)%Z -> Z_to_bv 64 (bv_swrap 32 (bv_unsigned (Z_to_bv 64 x))) = Z_to_bv 64 (s32 x).
Proof using Type. pin_using tt. intros x Hx. rewrite unsigned_lit by lia. rewrite swrap32_s32. reflexivity. Qed.

Lemma mul_word_u64 : forall a b, (0 <= a < 2^64)%Z -> (0 <= b < 2^64)%Z ->
  Z_to_bv 64 (bv_unsigned (Z_to_bv 64 a) * bv_unsigned (Z_to_bv 64 b)) = Z_to_bv 64 (u64 (b * a)).
Proof using Type. pin_using tt. intros a b Ha Hb. rewrite !unsigned_lit by lia. apply zbv64_eq. unfold u64. rewrite Z.mod_mod by lia. f_equal. lia. Qed.

Lemma u64_range : forall x, (0 <= u64 x < 2^64)%Z.
Proof using Type. pin_using tt. intros. unfold u64. apply Z.mod_pos_bound. lia. Qed.
Lemma div_range64 : forall a b, (0 <= a < 2^64)%Z -> (0 < b)%Z -> (0 <= a / b < 2^64)%Z.
Proof using Type. pin_using tt.
  intros a b Ha Hb. split; [apply Z.div_pos; lia|].
  apply Z.div_lt_upper_bound; [lia|]. assert (1 * 2^64 <= b * 2^64)%Z by (apply Z.mul_le_mono_nonneg_r; lia). lia.
Qed.
Lemma mod_range64 : forall a b, (0 < b < 2^64)%Z -> (0 <= a mod b < 2^64)%Z.
Proof using Type. pin_using tt. intros a b Hb. pose proof (Z.mod_pos_bound a b ltac:(lia)). lia. Qed.

(* [comment removed for export] *)
Definition sxu (v : Z) : Z := if v <? 2^31 then v else v + 2^64 - 2^32.
Lemma sxu_mono : forall a b, (0 <= a < 2^32)%Z -> (0 <= b < 2^32)%Z -> (sxu a < sxu b <-> a < b)%Z.
Proof using Type. pin_using tt. intros a b Ha Hb. unfold sxu. destruct (Z.ltb_spec a (2^31)); destruct (Z.ltb_spec b (2^31)); lia. Qed.
Lemma unsigned_sextw : forall (w : word), bv_unsigned (Z_to_bv 64 (bv_swrap 32 (bv_unsigned w + 0))) = sxu (bv_unsigned w mod 2^32).
Proof using Type. pin_using tt. intros w. rewrite Z.add_0_r. rewrite unsigned_swrap32. reflexivity. Qed.
Lemma sextw_mod : forall (x : Z), ((bv_swrap 32 (x + 0)) mod 18446744073709551616 = sxu (x mod 2^32))%Z.
Proof using Type. pin_using tt. intros x. rewrite Z.add_0_r. change 18446744073709551616%Z with (2^64)%Z. rewrite <- (unsigned_lit_wrap (bv_swrap 32 x)). rewrite unsigned_swrap32. reflexivity. Qed.
Lemma unsigned_sx32' : forall x, (0 <= x < 2^32)%Z -> bv_unsigned (sx32 (Z_to_bv 64 x)) = sxu x.
Proof using Type. pin_using tt. intros x Hx. rewrite OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_lock__S3.PP_kit.TwB.unsigned_sx32 by lia. reflexivity. Qed.
Lemma sxu_range : forall v, (0 <= v < 2^32)%Z -> (0 <= sxu v < 2^64)%Z /\ (v < 2^31 -> sxu v = v)%Z /\ (2^31 <= v -> 2^64 - 2^31 <= sxu v)%Z.
Proof using Type. pin_using tt. intros v Hv. unfold sxu. destruct (Z.ltb_spec v (2^31)); lia. Qed.

Section NgnCtx.
  Context {H hptr : Type} (HO : HeapOps H hptr) (K : modkit H hptr) (sites : stack_site -> Z).
  Hypothesis HFL : heap_frame_law K.
  Hypothesis SFL : stdio_fp_law K.
  Hypothesis HPL : heap_perm_law K.
  Hypothesis HAL : heap_addr_law K HO.
  Hypothesis SNPRINTF : snprintf_spec_stmt K.
  Hypothesis PP : post_process_stmt.
  Hypothesis ADJ : adjust_snapshot_stmt.
  Hypothesis RBLK : read_block_stmt HO K sites.
  Hypothesis ADDIF : add_interface_stmt HO K sites.

  (* [comment removed for export] *)
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
  Variables (R : rctx) (CLc FB : list (cblock (hptr:=hptr))) (lo P HA DA Af : Z) (m : mem) (o : option hptr).
  Variables (self f : hptr) (bufsize : Z) (swapped : bool) (vmaj vmin snapshot linktype ltext prec brk : Z) (header : pkthdr).
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
  Hypothesis P1 : (0 < P)%Z.  Hypothesis P2 : (P mod 16 = 0)%Z.  Hypothesis P4 : (P + 680 <= CEILZ)%Z.
  Hypothesis P5 : (P + 680 <= 65536 \/ 352256 <= P)%Z.  Hypothesis P6 : (P + 680 <= utp R - 200 \/ utp R - 200 + 4096 <= P)%Z.
  Hypothesis A1 : (0 < Af)%Z.  Hypothesis A4 : (Af + 1264 <= CEILZ)%Z.
  Hypothesis W1 : (1 <= snapshot <= INT_MAX)%Z.  Hypothesis W2 : (0 <= bufsize <= 2^30)%Z.
  Hypothesis W5 : brk = 0%Z.  Hypothesis W6 : prec = 0%Z.
  Hypothesis W7 : (0 <= vmaj < 2^16)%Z.  Hypothesis W8 : (0 <= vmin < 2^16)%Z.
  Hypothesis W9 : (0 <= linktype < 2^31)%Z.  Hypothesis W10 : (-2^31 <= ltext < 2^31)%Z.

  Let POSTQ := next_packet_post K ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc R CLc FB lo P HA DA m o.
  (* [comment removed for export] *)
  #[local] Abbreviation pv := (S3.F_ngnextA.TwB.pv self f bufsize swapped vmaj vmin snapshot linktype ltext prec brk header).
  #[local] Abbreviation ngn_frame := (S3.F_ngnextA.TwB.ngn_frame ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 P HA DA).
  #[local] Abbreviation ngn_final := (S3.F_ngnextA.TwB.ngn_final K sp R CLc FB P HA DA m o).
  #[local] Abbreviation ngn_finalC := (S3.F_ngnextA.TwB.ngn_finalC K sp R CLc FB P HA DA m o).
  #[local] Abbreviation ngn_final_C := (S3.F_ngnextA.TwB.ngn_final_C K sp R CLc FB P HA DA m o).
  #[local] Abbreviation ngn_ret_m1 := (S3.F_ngnextA.TwB.ngn_ret_m1 K ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc R CLc FB lo P HA DA m o BU).
  #[local] Abbreviation ngn_ret_0 := (S3.F_ngnextA.TwB.ngn_ret_0 K ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc R CLc FB lo P HA DA m o BU).
  #[local] Abbreviation ngn_ret_1 := (S3.F_ngnextA.TwB.ngn_ret_1 K ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc R CLc FB lo P HA DA m o BU).
  #[local] Abbreviation ngn_CLc_facts := (S3.F_ngnextA.TwB.ngn_CLc_facts K R CLc FB).
  #[local] Abbreviation ngn_snp_call := (S3.F_ngnextA.TwB.ngn_snp_call K HFL SFL SNPRINTF ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc R CLc FB lo P HA DA m o LO BU SPM TP ALN R1 R2 AH AD SPW P1 P4 P5).
  #[local] Abbreviation ngn_snp := (S3.F_ngnextA.TwB.ngn_snp K HFL SFL SNPRINTF ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc R CLc FB lo P HA DA m o LO BU SPM TP ALN R1 R2 AH AD SPW P1 P4 P5).
  #[local] Abbreviation ngn_mcp := (S3.F_ngnextA.TwB.ngn_mcp K HFL SFL ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc R CLc FB lo P HA DA m o LO BU ALN R1 R2 AH AD SPW P1 P4 P5 P6).
  #[local] Abbreviation PCAPRC_errbuf := (S3.F_ngnextA.TwB.PCAPRC_errbuf K sp R lo P HA DA LO BU ALN R1 R2 AH AD SPW P1).

  Ltac norm_g :=
    unfold S3.F_ngnextA.TwB.pv; unfold pcap_blocks; unfold psize; unfold is_ng;
    cbn [pc_self pc_rfile pc_bufsize pc_bufalloc pc_buffer pc_bufdata pc_swapped pc_version_major pc_version_minor pc_snapshot pc_linktype
         pc_linktype_ext pc_tstamp_precision pc_break_loop pc_errbuf pc_header pc_priv priv_cells ng_of ng_ifaces_ptr_of
         set_bufdata set_errbuf set_buffer set_ng set_priv];
    unfold PCAP_NG_SF_TOTAL, PCAP_PRIV_OFF.
  Ltac norm_p :=
    unfold S3.F_ngnextA.TwB.pv in *; unfold pcap_blocks in *; unfold psize in *; unfold is_ng in *;
    cbn [pc_self pc_rfile pc_bufsize pc_bufalloc pc_buffer pc_bufdata pc_swapped pc_version_major pc_version_minor pc_snapshot pc_linktype
         pc_linktype_ext pc_tstamp_precision pc_break_loop pc_errbuf pc_header pc_priv priv_cells ng_of ng_ifaces_ptr_of
         set_bufdata set_errbuf set_buffer set_ng set_priv] in *;
    unfold PCAP_NG_SF_TOTAL, PCAP_PRIV_OFF in *.

  #[local] Abbreviation ngn_pp := (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Startup_B__S3.F_ngnextB.TwB.ngn_pp K HFL SFL PP ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc R CLc FB lo P HA DA m o self f bufsize swapped vmaj vmin snapshot linktype ltext prec brk header LO BU SPM R1 R2 R3 AH AD SPW SP47 P1 P2 P4 P5 P6 W1 W2 W5 W6 W7 W8 W9 W10).

  (* [comment removed for export] *)
  Lemma lxor_ones64 : forall a, (0 <= a < 2^64)%Z -> Z.lxor a 18446744073709551615 = (18446744073709551615 - a)%Z.
  Proof using DA HA P sp. pin_using (fun (DA HA P sp : unit) => tt).
    intros a Ha. change 18446744073709551615%Z with (Z.ones 64).
    destruct (Z.eq_dec a 0) as [->|Hnz]; [reflexivity|].
    rewrite <- Z.ldiff_ones_l_low; [| lia | apply Z.log2_lt_pow2; lia].
    symmetry. apply Z.sub_nocarry_ldiff. rewrite Z.ldiff_ones_r by lia. rewrite Z.shiftr_eq_0; [reflexivity| lia |].
    apply Z.log2_lt_pow2; lia.
  Qed.

  (* [comment removed for export] *)
  Definition ngn_nodata__stmt : Prop := forall (ra' t0' t1' t2' x1 a0' a1' a2' a3' a4' a6' a7' x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 t3' t4' t5' t6' : word) (m5 : mem) (ps : PState H hptr)
           (PB' : list (cblock (hptr:=hptr))) (p' : pcap hptr hptr) (h : pkthdr) (hcs' : list cell) (dw : cell) (dj : list byte) (ccs : list cell),
      stk usegs m5 lo (bv_unsigned sp + -160) ->
      rw_cells usegs m5 (bv_unsigned sp + -160) (ngn_frame dj ccs) -> cells_size ccs = 24%nat -> mem_inv usegs m5 ->
      ngn_finalC m5 ps PB' p' hcs' dw ->
      implM usegs (mret ((-1)%Z, h, p')) ps POSTQ
        (MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -160)) gp tp t0' t1' t2' (Z_to_bv 64 (-1)) x1 a0' a1' a2' a3' a4' (Z_to_bv 64 0) a6' a7'
                 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 t3' t4' t5' t6') F (Z_to_bv 64 0x1824c) fc None m5 (seg_rom usegs)).
  Section Sz20.
  Variables ra' t0' t1' t2' x1 a0' a1' a2' a3' a4' a6' a7' x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 t3' t4' t5' t6' m5 ps PB' p' h hcs' dw dj ccs : ltac2:(SecDiet.SzSec.tyM 'ngn_nodata__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra').
  Lemma ngn_nodata__body : ltac2:(SecDiet.SzSec.bodyP 'ngn_nodata__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof using AD BU HFL LO P1 R1 R2 R3 SFL SP47 SPW. pin_using (fun (AD BU HFL LO P1 R1 R2 R3 SFL SP47 SPW : unit) => tt).
 intros ST5 FR5 Hccs MI5 (G5 & PC5 & AG5 & HH & Hh & HD & Hd & OF5).
    pose proof (bv_unsigned_in_range 64 sp) as RSP.
    destruct (rw_cells_forget _ _ _ _ HD) as [dwj HD']. clear HD. cbn [cells_size] in HD'. rewrite Hd in HD'. change (8 + 0)%nat with 8%nat in HD'.
    pose proof FR5 as FRJ. unfold S3.F_ngnextA.TwB.ngn_frame in FRJ. apply rw_cells_app in FRJ as [FRJ _].
    hide FR5. hide HH.
    pose proof (munch_refl [(DA, DA + 8)]%Z m5) as MU. pose proof (wmono_refl usegs m5) as WM.
    unfold implM. iprefix.
    step. step. if_false_by (eqz_false DA ltac:(gio_ceil_fact; clear -CLO__ R1 R2 R3 BU LO SPW SP47; unfold rc_spmain in *; lia)).
    step. step. rewrite (and7_aligned DA) by (gio_ceil_fact; clear -CLO__ AD R1 R2 R3 BU LO SPW SP47; unfold rc_spmain in *; lia). step. if_false.
    step. pstep. step. if_true.
    unhide FR5. unhide HH. clear FRJ.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      assert (AGD : agrees_on (fun a => outside [(DA, DA + 8)]%Z a) m5 mm) by (eapply agrees_on_of_munch; [exact MU | exact WM | intros a _ Ho; exact Ho]);
      assert (G6 : GIo K R ps (CLc ++ PB') FB mm)
        by (eapply (GIo_pcap_frame K HFL SFL); [exact G5 | exact MU | exact WM |]; apply Forall_cons; [left; cbn [fst snd]; unfold rc_lo, rc_spmain in *; clear - R1 R2 R3 LO BU SPM; lia| apply Forall_nil]);
      rename mm into m6 end.
    apply (agrees_rw_cells _ _ _ _ _ AGD) in FR5; [| intros a Ha; unfold S3.F_ngnextA.TwB.ngn_frame in Ha; rewrite !cells_size_app in Ha; cbn [outside cells_size csize Nat.add] in Ha |- *; rewrite Hccs in Ha; clear - Ha R1 R2; lia].
    apply (agrees_rw_cells _ _ _ _ _ AGD) in HH; [| intros a Ha; cbn [outside]; rewrite Hh in Ha; clear - Ha R2; lia].
    unfold NGN_EPILOGUE in *.
    apply evt_done. eapply ngn_ret_m1; [assumption | exact FR5 | exact Hccs | assumption |].
    split; [exact G6|]. split.
    { eapply PCAPR_closable_agree; [exact AGD| | exact PC5]. intros a Ha. cbn [outside]. pose proof (in_PB_below K _ _ _ _ _ _ _ G5 Ha). gio_ceil_fact; clear -CLO__ H0 R1 R2 LO BU SPW. lia. }
    split. { eapply agrees_on_trans; [exact AG5|]. eapply agrees_on_weaken; [exact AGD|]. intros a [_ [_ Hn]]; cbn [outside]; clear - Hn; lia. }
    split; [exact HH|]. split; [exact Hh|]. split; [eassumption| split; [reflexivity| exact OF5]].
  Qed.
  End Sz20.
  Lemma ngn_nodata : ltac:(let t := eval cbv delta [ngn_nodata__stmt] in ngn_nodata__stmt in exact t).
  Proof using AD BU HFL LO P1 R1 R2 R3 SFL SP47 SPW. intros ra' t0' t1' t2' x1 a0' a1' a2' a3' a4' a6' a7' x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 t3' t4' t5' t6' m5 ps PB' p' h hcs' dw dj ccs. ltac2:(SecDiet.SzSec.closeP 'ngn_nodata__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.
  (* [comment removed for export] *)
  Definition ngn_ts2__stmt : Prop := forall (ra' t0' t1' t2' a4' a7' x2 x4 x5 x6 x7 x8 x9 x10 x11 t3' t4' t5' t6' cw ws wu : word) (hj1 hj2 : list byte) (m5 : mem) (ps : PState H hptr)
           (bq : hptr) (Bq Ix alloc doff rem : Z) (data eb : list Z) (sx : pcap_ng_sf) (ix : option hptr) (sec usec cap len bt : Z) (dw : cell) (dj : list byte) (cv1 cv2 cv3 : word) (cpad : list byte),
      stk usegs m5 lo (bv_unsigned sp + -160) ->
      rw_cells usegs m5 (bv_unsigned sp + -160) (ngn_frame dj [C8 cv1; C8 cv2; C4 cv3; CB 4 cpad]) -> mem_inv usegs m5 ->
      GIo K R ps (CLc ++ pcap_blocks (pv bq alloc data eb sx ix) P Bq Ix) FB m5 ->
      PCAPR (hptr:=hptr) P (pv bq alloc data eb sx ix) (pcap_blocks (pv bq alloc data eb sx ix) P Bq Ix) FB m5 ->
      agrees_on (fun a => client_keeps CLc (bv_unsigned sp) a /\ ~ (HA <= a < HA + 24) /\ ~ (DA <= a < DA + 8))%Z m m5 ->
      rw_cells usegs m5 HA [CB 8 hj1; CB 8 hj2; C4 (Z_to_bv 64 cap); C4 (Z_to_bv 64 len)] -> rw_cells usegs m5 DA [dw] -> csize dw = 8%nat ->
      (bv_unsigned cw mod 2^32 = cap)%Z -> ws = Z_to_bv 64 sec -> wu = Z_to_bv 64 usec ->
      Forall (fun x => 0 <= x < 256)%Z data -> (0 <= doff)%Z -> (doff mod 4 = 0)%Z -> (0 <= rem)%Z -> (doff + rem <= Z.of_nat (length data))%Z ->
      (Z.of_nat (length data) < 2^31)%Z -> (0 <= len < 2^32)%Z -> (0 <= bt < 2^32)%Z -> ps_outfile ps = o ->
      implM usegs (match get_from_block_data (mkCursor doff rem bt) cap with
                   | inl e => mret ((-1)%Z, mkHdr sec usec cap len, set_errbuf e (pv bq alloc data eb sx ix))
                   | inr (doff', _) =>
                     let '(hdr, d) := pcapint_post_process linktype swapped (mkHdr sec usec cap len) (zskipn doff' data) in
                     mret (1%Z, hdr, set_bufdata (zfirstn doff' data ++ d) (pv bq alloc data eb sx ix))
                   end) ps POSTQ
        (MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -160)) gp tp t0' t1' t2' (Z_to_bv 64 (-1)) (Z_to_bv 64 (P + 216))
                 (Z_to_bv 64 rem) cw ws (Z_to_bv 64 (s32 bt)) a4' (Z_to_bv 64 (Bq + doff)) wu a7'
                 x2 (Z_to_bv 64 P) x4 x5 x6 x7 x8 x9 x10 x11 t3' t4' t5' t6') F (Z_to_bv 64 0x18200) fc None m5 (seg_rom usegs)).
  Section Sz21.
  Variables ra' t0' t1' t2' a4' a7' x2 x4 x5 x6 x7 x8 x9 x10 x11 t3' t4' t5' t6' cw ws wu hj1 hj2 m5 ps bq Bq Ix alloc doff rem data eb sx ix sec usec cap len bt dw dj cv1 cv2 cv3 cpad : ltac2:(SecDiet.SzSec.tyM 'ngn_ts2__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra').
  Lemma ngn_ts2__body : ltac2:(SecDiet.SzSec.bodyP 'ngn_ts2__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof using AD AH ALN BU HFL LO P1 P2 P4 P5 P6 PP R1 R2 R3 SFL SNPRINTF SP47 SPM SPW TP W1 W10 W2 W5 W6 W7 W8 W9. pin_using (fun (AD AH ALN BU HFL LO P1 P2 P4 P5 P6 PP R1 R2 R3 SFL SNPRINTF SP47 SPM SPW TP W1 W10 W2 W5 W6 W7 W8 W9 : unit) => tt).
 intros ST5 FR5 MI5 G5 PC5 AG5 HH HD Hd Hcw -> -> DRNG Hdoff Hd4 Hrem Hdr Hl31 Hlen Hbt OF5.
    pose proof (bv_unsigned_in_range 64 sp) as RSP.
    pose proof (bv_unsigned_in_range 64 cw) as RCW. change (bv_modulus 64) with (2^64)%Z in RCW.
    assert (CAP : (0 <= cap < 2^32)%Z) by (rewrite <- Hcw; Z.div_mod_to_equations; lia).
    pose proof PC5 as (Afx & Hin & (Bx' & Ix' & jx' & padx & bsx' & EPB & CELLS & PRIV & BUF & PFX & IFS & WF)).
    pose proof G5 as G5e. rewrite EPB in G5e.
    pose proof (GIo_PB_block K _ _ _ _ _ _ _ _ _ G5e ltac:(right; left; reflexivity)) as (K1 & K2 & K3 & K4 & K5 & K6).
    pose proof WF as (_ & _ & W3 & W4 & _).
    unfold S3.F_ngnextA.TwB.pv, pcap_blocks, psize, is_ng in EPB, K1, K2, K3, K4, K5, K6. cbn [pc_self pc_buffer pc_bufalloc pc_priv] in EPB, K1, K2, K3, K4, K5, K6.
    unfold S3.F_ngnextA.TwB.pv in W3, W4. cbn [pc_bufalloc pc_bufdata] in W3, W4.
    assert (EBX : Bx' = Bq) by congruence. subst Bx'. clear EPB G5e CELLS PRIV BUF PFX IFS WF.
    pose proof FR5 as FRJ. unfold S3.F_ngnextA.TwB.ngn_frame in FRJ. cbn [app] in FRJ.
    hide FR5. hide HD.
    pose proof (munch_refl [(HA, HA + 16); (bv_unsigned sp + -160 + 32, bv_unsigned sp + -160 + 48)]%Z m5) as MU. pose proof (wmono_refl usegs m5) as WM.
    unfold implM. iprefix.
    step. step.
    replace (Z_to_bv 64 (Z.shiftr (bv_unsigned (Z_to_bv 64 (Z.shiftl (bv_unsigned cw) 32))) 32)) with (Z_to_bv 64 cap).
    2:{ rewrite Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia. rewrite unsigned_lit_wrap. rewrite <- Hcw. f_equal. Z.div_mod_to_equations. nia. }
    step. step. step.
    unfold get_from_block_data. cbn [cur_remaining cur_off cur_block_type].
    step. if_cases BR; zify_cond BR; rewrite ?unsigned_lit in BR by lia.
    - (* [comment removed for export] *)
      replace (rem <? cap) with false by (symmetry; apply Z.ltb_ge; lia). cbv iota. cbv beta.
      step. rewrite (unsigned_lit (Bq + doff)) by (clear - K1 K4 Hdoff Hdr Hrem W4; lia). rewrite (lxor_ones64 (Bq + doff)) by (clear - K1 K4 Hdoff Hdr Hrem W4; lia).
      step. if_cases BW; zify_cond BW; [exfalso; rewrite ?unsigned_lit in BW by (clear - K1 K4 Hdoff Hdr Hrem W4 CAP; lia); clear - BW K1 K4 Hdoff Hdr Hrem W4 CAP BR; lia|].
      step. step. step. step.
      unhide FR5. unhide HD. clear FR5.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
        assert (AGD : agrees_on (fun a => outside [(HA, HA + 16); (bv_unsigned sp + -160 + 32, bv_unsigned sp + -160 + 48)]%Z a) m5 mm) by (eapply agrees_on_of_munch; [exact MU | exact WM | intros a _ Ho; exact Ho]);
        assert (G5' : GIo K R ps (CLc ++ pcap_blocks (pv bq alloc data eb sx ix) P Bq Ix) FB mm)
          by (eapply (GIo_pcap_frame K HFL SFL); [exact G5 | exact MU | exact WM |]; apply Forall_cons; [left; cbn [fst snd]; unfold rc_lo, rc_spmain in *; clear - R1 R2 R3 LO BU SPM; lia|];
              apply Forall_cons; [left; cbn [fst snd]; unfold rc_lo, rc_spmain in *; clear - LO BU SPM; lia| apply Forall_nil]);
        rename mm into m5' end.
      apply (agrees_rw_cells _ _ _ _ _ AGD) in HD; [| intros a Ha; cbn [outside cells_size csize Nat.add] in Ha |- *; rewrite Hd in Ha; clear - Ha R1 R2; lia].
      assert (PC5' : PCAPR (hptr:=hptr) P (pv bq alloc data eb sx ix) (pcap_blocks (pv bq alloc data eb sx ix) P Bq Ix) FB m5').
      { eapply PCAPR_agree; [exact AGD| | exact PC5]. intros a Ha. cbn [outside]. pose proof (in_PB_below K _ _ _ _ _ _ _ G5 Ha). gio_ceil_fact; clear -CLO__ H0 R1 LO BU SPW. lia. }
      assert (AG5' : agrees_on (fun a => client_keeps CLc (bv_unsigned sp) a /\ ~ (HA <= a < HA + 24) /\ ~ (DA <= a < DA + 8))%Z m m5').
      { eapply agrees_on_trans; [exact AG5|]. eapply agrees_on_weaken; [exact AGD|]. intros a [Hc [Hn _]]; cbn [outside]. split; [clear - Hn; lia|]. split; [| exact Logic.I].
        destruct Hc as [Hc|Hc]; [clear - Hc; lia|]. destruct (ngn_CLc_facts _ _ _ _ G5 Hc) as [Hx _]. gio_ceil_fact; clear -CLO__ Hx LO BU SPW. lia. }
      lazymatch goal with FRX : rw_cells usegs m5' (bv_unsigned sp + -160) (_ :: _ :: _ :: _ :: ?c1 :: ?c2 :: ?c3 :: ?c4 :: _) |- _ =>
        assert (FR6 : rw_cells usegs m5' (bv_unsigned sp + -160) (S3.F_ngnextA.TwB.ngn_frame ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 P HA DA dj [c1; c2; c3; c4])) by exact FRX;
        assert (Hccs' : cells_size [c1; c2; c3; c4] = 24%nat) by reflexivity end.
      lazymatch goal with HHX : rw_cells usegs m5' HA _ |- _ => rename HHX into HH' end.
      apply evt_done. eapply ngn_pp; [assumption | exact FR6 | exact Hccs' | assumption | exact G5' | exact PC5' | exact AG5' | exact HH' | exact HD | exact Hd
                                      | reflexivity | reflexivity | exact DRNG | lia | exact Hd4 | lia | exact Hl31 | exact Hlen | exact OF5].
    - (* [comment removed for export] *)
      replace (rem <? cap) with true by (symmetry; apply Z.ltb_lt; lia). cbv iota.
      step. step. step. step. step.
      unhide FR5. unhide HD.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
        assert (AGD : agrees_on (fun a => outside [(HA, HA + 16); (bv_unsigned sp + -160 + 32, bv_unsigned sp + -160 + 48)]%Z a) m5 mm) by (eapply agrees_on_of_munch; [exact MU | exact WM | intros a _ Ho; exact Ho]);
        assert (G5' : GIo K R ps (CLc ++ pcap_blocks (pv bq alloc data eb sx ix) P Bq Ix) FB mm)
          by (eapply (GIo_pcap_frame K HFL SFL); [exact G5 | exact MU | exact WM |]; apply Forall_cons; [left; cbn [fst snd]; unfold rc_lo, rc_spmain in *; clear - R1 R2 R3 LO BU SPM; lia|];
              apply Forall_cons; [left; cbn [fst snd]; unfold rc_lo, rc_spmain in *; clear - LO BU SPM; lia| apply Forall_nil]);
        rename mm into m5' end.
      clear FR5.
      lazymatch goal with FRX : rw_cells usegs m5' (bv_unsigned sp + -160) (_ :: _ :: _ :: _ :: _ :: _) |- _ =>
        assert (FR5 : rw_cells usegs m5' (bv_unsigned sp + -160) (S3.F_ngnextA.TwB.ngn_frame ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 P HA DA dj [C8 cv1; C8 cv2; C4 cv3; CB 4 cpad])) by exact FRX; clear FRX end.
      apply (agrees_rw_cells _ _ _ _ _ AGD) in HD; [| intros a Ha; cbn [outside cells_size csize Nat.add] in Ha |- *; rewrite Hd in Ha; clear - Ha R1 R2; lia].
      assert (PC5' : PCAPR (hptr:=hptr) P (pv bq alloc data eb sx ix) (pcap_blocks (pv bq alloc data eb sx ix) P Bq Ix) FB m5').
      { eapply PCAPR_agree; [exact AGD| | exact PC5]. intros a Ha. cbn [outside]. pose proof (in_PB_below K _ _ _ _ _ _ _ G5 Ha). gio_ceil_fact; clear -CLO__ H0 R1 LO BU SPW. lia. }
      assert (AG5' : agrees_on (fun a => client_keeps CLc (bv_unsigned sp) a /\ ~ (HA <= a < HA + 24) /\ ~ (DA <= a < DA + 8))%Z m m5').
      { eapply agrees_on_trans; [exact AG5|]. eapply agrees_on_weaken; [exact AGD|]. intros a [Hc [Hn _]]; cbn [outside]. split; [clear - Hn; lia|]. split; [| exact Logic.I].
        destruct Hc as [Hc|Hc]; [clear - Hc; lia|]. destruct (ngn_CLc_facts _ _ _ _ G5 Hc) as [Hx _]. gio_ceil_fact; clear -CLO__ Hx LO BU SPW. lia. }
      lazymatch goal with HHX : rw_cells usegs m5' HA _ |- _ => rename HHX into HH' end.
      assert (MI5' : mem_inv usegs m5') by assumption. assert (ST5' : stk usegs m5' lo (bv_unsigned sp + -160)) by assumption.
      clear MU WM AGD G5 AG5 PC5.
      assert (MSG : fmt_at m5' NGN_FMT_TOO_SHORT "block of type %u in pcapng dump file is too short"%string)
        by (apply fmt_at_intro; [exact MI5' | vm_compute; reflexivity | unfold NGN_FMT_TOO_SHORT; lia | unfold NGN_FMT_TOO_SHORT; cbn; lia]).
      unfold NGN_FMT_TOO_SHORT in MSG.
      eapply (ngn_snp_call 0x1822c) with (m5 := m5') (ps := ps) (p' := pv bq alloc data eb sx ix) (dw := dw) (dj := dj) (args := [AInt (s32 bt)]);
        [exact ST5' | exact FR5 | reflexivity | exact MI5' | | exact MSG | reflexivity | cbn; lia | cbn; apply Forall2_cons; [reflexivity| apply Forall2_nil] | lia | reflexivity |].
      { split; [exact G5'|]. split; [apply PCAPR_closable_of; exact PC5'|]. split; [exact AG5'|]. split; [exact HH'|]. split; [reflexivity|].
        split; [exact HD|]. split; [exact Hd| exact OF5]. }
      intros m6 t0'' t1'' t2'' a0'' a1'' a2'' a3'' a4'' a5'' a6'' a7'' t3'' t4'' t5'' t6'' ST6 FR6 MI6 FIN6.
      pose proof (munch_refl ([] : list (Z * Z)) m6) as MU. pose proof (wmono_refl usegs m6) as WM.
      hide FR6. step. step. unhide FR6.
      apply evt_done. eapply ngn_nodata; [exact ST6 | exact FR6 | reflexivity | exact MI6 | exact (FIN6 (Msg.block_too_short bt))].
  Qed.
  End Sz21.
  Lemma ngn_ts2 : ltac:(let t := eval cbv delta [ngn_ts2__stmt] in ngn_ts2__stmt in exact t).
  Proof using AD AH ALN BU HFL LO P1 P2 P4 P5 P6 PP R1 R2 R3 SFL SNPRINTF SP47 SPM SPW TP W1 W10 W2 W5 W6 W7 W8 W9. intros ra' t0' t1' t2' a4' a7' x2 x4 x5 x6 x7 x8 x9 x10 x11 t3' t4' t5' t6' cw ws wu hj1 hj2 m5 ps bq Bq Ix alloc doff rem data eb sx ix sec usec cap len bt dw dj cv1 cv2 cv3 cpad. ltac2:(SecDiet.SzSec.closeP 'ngn_ts2__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.
  (* [comment removed for export] *)
  Lemma snez_pos' : forall x, (0 < x < 2^64)%Z -> v_sltu z64 (Z_to_bv 64 x) = Z_to_bv 64 1.
  Proof using Type. pin_using tt.
    intros x Hx. rewrite v_sltu_b2z. change (bv_unsigned z64) with 0%Z. rewrite (unsigned_lit x) by (clear -Hx; lia).
    destruct (Z.ltb_spec 0 x); [reflexivity| exfalso; clear -Hx H0; lia].
  Qed.
  Lemma seqz_pos' : forall x, (0 < x < 2^64)%Z -> v_sltiu (Z_to_bv 64 x) 1 = Z_to_bv 64 0.
  Proof using Type. pin_using tt.
    intros x Hx. unfold v_sltiu. rewrite (unsigned_lit x) by (clear -Hx; lia). change (bv_wrap 64 1) with 1%Z.
    destruct (Z.ltb_spec x 1); [exfalso; clear -Hx H0; lia| reflexivity].
  Qed.

  (* [comment removed for export] *)
  Definition ngn_ts__stmt : Prop := forall (ra' t0' t1' t2' a4' a6' x2 x4 x5 x6 x7 x8 x9 x10 x11 t3' t4' t5' t6' iw cw : word) (hj1 hj2 : list byte) (m5 : mem) (ps : PState H hptr)
           (bq : hptr) (Bq Ix alloc doff rem : Z) (data eb : list Z) (sx : pcap_ng_sf) (ix : option hptr) (id t cap len bt : Z) (dw : cell) (dj : list byte)
           (cv1 cv2 cv3 : word) (cpad : list byte),
      stk usegs m5 lo (bv_unsigned sp + -160) ->
      rw_cells usegs m5 (bv_unsigned sp + -160) (ngn_frame dj [C8 cv1; C8 cv2; C4 cv3; CB 4 cpad]) -> mem_inv usegs m5 ->
      GIo K R ps (CLc ++ pcap_blocks (pv bq alloc data eb sx ix) P Bq Ix) FB m5 ->
      PCAPR (hptr:=hptr) P (pv bq alloc data eb sx ix) (pcap_blocks (pv bq alloc data eb sx ix) P Bq Ix) FB m5 ->
      agrees_on (fun a => client_keeps CLc (bv_unsigned sp) a /\ ~ (HA <= a < HA + 24) /\ ~ (DA <= a < DA + 8))%Z m m5 ->
      rw_cells usegs m5 HA [CB 8 hj1; CB 8 hj2; C4 (Z_to_bv 64 cap); C4 (Z_to_bv 64 len)] -> rw_cells usegs m5 DA [dw] -> csize dw = 8%nat ->
      (bv_unsigned iw mod 2^32 = id)%Z -> (bv_unsigned cw mod 2^32 = cap)%Z -> (0 <= id < ng_ifcount sx)%Z -> (0 <= t < 2^64)%Z ->
      Forall (fun x => 0 <= x < 256)%Z data -> (0 <= doff)%Z -> (doff mod 4 = 0)%Z -> (0 <= rem)%Z -> (doff + rem <= Z.of_nat (length data))%Z ->
      (Z.of_nat (length data) < 2^31)%Z -> (0 <= len < 2^32)%Z -> (0 <= bt < 2^32)%Z -> ps_outfile ps = o ->
      implM usegs (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Startup_B__S3.F_ngnextB.TwB.ngn_tsK (mkFound id t cap len (mkCursor doff rem bt)) (pv bq alloc data eb sx ix)) ps POSTQ
        (MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -160)) gp tp t0' t1' t2' (Z_to_bv 64 (-1)) (Z_to_bv 64 (P + 216))
                 (Z_to_bv 64 rem) cw iw (Z_to_bv 64 (s32 bt)) a4' (Z_to_bv 64 (Bq + doff)) a6' (Z_to_bv 64 t)
                 x2 (Z_to_bv 64 P) x4 x5 x6 x7 x8 x9 x10 x11 t3' t4' t5' t6') F (Z_to_bv 64 0x1814c) fc None m5 (seg_rom usegs)).
  Section Sz24.
  Variables ra' t0' t1' t2' a4' a6' x2 x4 x5 x6 x7 x8 x9 x10 x11 t3' t4' t5' t6' iw cw hj1 hj2 m5 ps bq Bq Ix alloc doff rem data eb sx ix id t cap len bt dw dj cv1 cv2 cv3 cpad : ltac2:(SecDiet.SzSec.tyM 'ngn_ts__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra').
  Lemma ngn_ts__body : ltac2:(SecDiet.SzSec.bodyP 'ngn_ts__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof using AD AH ALN BU HFL LO P1 P2 P4 P5 P6 PP R1 R2 R3 SFL SNPRINTF SP47 SPM SPW TP W1 W10 W2 W5 W6 W7 W8 W9. pin_using (fun (AD AH ALN BU HFL LO P1 P2 P4 P5 P6 PP R1 R2 R3 SFL SNPRINTF SP47 SPM SPW TP W1 W10 W2 W5 W6 W7 W8 W9 : unit) => tt).
 intros ST5 FR5 MI5 G5 PC5 AG5 HH HD Hd Hiw Hcw Hid Ht DRNG Hdoff Hd4 Hrem Hdr Hl31 Hlen Hbt OF5.
    pose proof (bv_unsigned_in_range 64 sp) as RSP.
    pose proof PC5 as (Afx & Hin & (Bx' & Ix' & jx' & padx & bsx' & EPB & CELLS & PRIV & BUF & PFX & IFS & WF)).
    pose proof G5 as G5e. rewrite EPB in G5e.
    pose proof (PB_apart K _ _ _ _ _ _ _ _ _ _ G5e eq_refl) as [APB API].
    pose proof WF as (_ & _ & W3 & W4 & _ & _ & _ & _ & _ & _ & _ & _ & WNG & WBB).
    unfold S3.F_ngnextA.TwB.pv, pcap_blocks, psize, is_ng in EPB, API, WNG. cbn [pc_self pc_buffer pc_bufalloc pc_priv] in EPB, API, WNG.
    destruct WNG as (UT & WMB & WIC & WIS).
    assert (EBX : Bx' = Bq) by congruence. subst Bx'.
    (* [comment removed for export] *)
    unfold ifaces_ok, S3.F_ngnextA.TwB.pv in IFS. cbn [pc_priv] in IFS.
    destruct ix as [q|]; [| destruct IFS as (_ & _ & IC0 & _); exfalso; clear -IC0 Hid; lia].
    destruct IFS as (js & tail & Ljs & HIF & EIC & ICS & ISZ & IWF).
    pose proof (GIo_PB_block K _ _ _ _ _ _ _ _ _ G5e ltac:(right; right; left; reflexivity)) as (I1 & I2 & I3 & I4 & I5 & I6).
    set (k := Z.to_nat id).
    assert (Hk : (k < length (ng_ifaces sx))%nat) by (subst k; clear -Hid EIC; lia).
    pose proof (ifs_cells_slot _ _ _ _ _ k HIF ltac:(rewrite length_rev; exact Ljs) ltac:(rewrite length_rev; exact Hk)) as SLOT.
    replace (Ix' + 40 * Z.of_nat k)%Z with (Ix' + 40 * id)%Z in SLOT by (subst k; lia).
    rewrite (rev_nth (ng_ifaces sx) ngif0 Hk) in SLOT.
    set (ifc := nth (length (ng_ifaces sx) - S k) (ng_ifaces sx) ngif0) in SLOT.
    set (jfc := nth k (rev js) (mkIJ [] [] (Z_to_bv 64 0))) in SLOT.
    assert (EIFC : nth_slot (ng_ifaces sx) (ng_ifcount sx) id = ifc).
    { unfold nth_slot. subst ifc. f_equal. rewrite EIC. subst k. clear -Hid. lia. }
    assert (WFC : if_wf ifc).
    { apply (proj1 (List.Forall_forall _ _) IWF). subst ifc. apply nth_In. clear -Hk. lia. }
    destruct WFC as [TSR SFR].
    pose proof (rw_cells_bound _ _ _ _ HIF) as IB. rewrite cells_size_app, ifs_cells_size in IB by (rewrite length_rev; exact Ljs). cbn [cells_size csize Nat.add] in IB. rewrite length_rev in IB.
    assert (SLB : (Ix' <= Ix' + 40 * id /\ Ix' + 40 * id + 40 <= Ix' + 40 * ng_ifaces_size sx)%Z) by (clear -Hid EIC ICS; nia).
    assert (SLA : ((Ix' + 40 * id) mod 8 = 0)%Z) by (clear -I2 Hid; Z.div_mod_to_equations; lia).
    clearbody ifc jfc. clear HIF.
    unfold if_cells in SLOT.
    (* [comment removed for export] *)
    unfold OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Startup_B__S3.F_ngnextB.TwB.ngn_tsK. cbn [f_interface_id f_t f_caplen f_len f_cursor ng_of pc_priv pc_linktype pc_swapped pc_bufdata S3.F_ngnextA.TwB.pv]. rewrite EIFC.
    unfold priv_cells, S3.F_ngnextA.TwB.pv in PRIV. cbn [pc_priv] in PRIV. unfold ng_cells, PCAP_PRIV_OFF in PRIV.
    pose proof FR5 as FRJ. unfold S3.F_ngnextA.TwB.ngn_frame in FRJ. apply rw_cells_app in FRJ as [FRJ _].
    hide FR5. hide BUF. hide CELLS. hide HD. hide HH.
    pose proof (munch_refl ([] : list (Z * Z)) m5) as MU. pose proof (wmono_refl usegs m5) as WM.
    unfold implM. iprefix.
    step. step. step. step. step. step. rewrite (mulhu_40 iw id Hiw).
    step.
    step. if_cases Kc; [zify_cond Kc; exfalso; rewrite ?unsigned_lit in Kc by (clear -I1 I3 I4 SLB; lia); clear -Kc I1 I3 I4 SLB; lia|]. clear Kc.
    step. rewrite (snez_pos' Ix') by (clear -I1 I3 I4; lia).
    step. rewrite (seqz_pos' (Ix' + 40 * id)) by (clear -I1 I3 I4 SLB; lia).
    step. change (Z.lxor (bv_unsigned (Z_to_bv 64 1)) 0) with 1%Z.
    step. if_false.
    step. if_false_by (eqz_false Ix' ltac:(clear -I1 I3 I4; lia)).
    step. rewrite (and7_aligned (Ix' + 40 * id)) by (clear -I1 I3 I4 SLB SLA; lia). step. if_false.
    step. step. if_false_by (eqz_false (if_tsresol ifc) ltac:(clear -TSR; lia)).
    step. rewrite (divu_lit t (if_tsresol ifc)) by (clear -Ht TSR; lia).
    step. rewrite (sx32_small (ngscale_code (if_scale_type ifc))) by (destruct (if_scale_type ifc); cbn; lia).
    step. step. step. step. rewrite (frac_word t (if_tsresol ifc)) by (clear -Ht TSR; lia).
    assert (FR : (0 <= t mod if_tsresol ifc < if_tsresol ifc)%Z) by (apply Z.mod_pos_bound; lia).
    unhide FR5. unhide BUF. unhide CELLS. unhide HD. unhide HH.
    (* [comment removed for export] *)
    assert (TAIL : forall (a7'' t1'' t2'' t3'' : word) (fr : Z), (0 <= fr < 2^64)%Z ->
      evt usegs (fun ms' => impl usegs (at_node usegs) (npeek usegs)
        ((match get_from_block_data (mkCursor doff rem bt) cap with
          | inl e => mret ((-1)%Z, mkHdr (s64 (u64 (t / if_tsresol ifc + if_tsoffset ifc))) (s32 fr) cap len, set_errbuf e (pv bq alloc data eb sx (Some q)))
          | inr (doff', _) =>
            let '(hdr, d) := pcapint_post_process linktype swapped (mkHdr (s64 (u64 (t / if_tsresol ifc + if_tsoffset ifc))) (s32 fr) cap len) (zskipn doff' data) in
            mret (1%Z, hdr, set_bufdata (zfirstn doff' data ++ d) (pv bq alloc data eb sx (Some q)))
          end) ps) (epost (fun p : Z * pkthdr * pcap hptr hptr * PState H hptr => POSTQ p.1 p.2)) ms')
        (MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -160)) gp tp (Z_to_bv 64 (Ix' + 40 * id)) t1'' t2'' (Z_to_bv 64 (-1)) (Z_to_bv 64 (P + 216))
                 (Z_to_bv 64 rem) cw (Z_to_bv 64 (t / if_tsresol ifc)) (Z_to_bv 64 (s32 bt)) (Z_to_bv 64 (if_tsoffset ifc)) (Z_to_bv 64 (Bq + doff)) (Z_to_bv 64 fr) a7''
                 x2 (Z_to_bv 64 P) x4 x5 x6 x7 x8 x9 x10 x11 t3'' t4' t5' t6') F (Z_to_bv 64 0x181f8) fc None m5 (seg_rom usegs))).
    { intros a7'' t1'' t2'' t3'' fr Hfr.
      hide FR5. hide BUF. hide CELLS. hide HD. hide HH.
      step. step.
      unhide FR5. unhide BUF. unhide CELLS. unhide HD. unhide HH.
      apply evt_done.
      eapply ngn_ts2; [exact ST5 | exact FR5 | exact MI5 | exact G5 | exact PC5 | exact AG5 | exact HH | exact HD | exact Hd | exact Hcw
                      | apply sec_word_eq | rewrite Z.add_0_r; apply usec_word_eq; exact Hfr | exact DRNG | exact Hdoff | exact Hd4 | exact Hrem | exact Hdr | exact Hl31 | exact Hlen | exact Hbt | exact OF5]. }
    hide FR5. hide BUF. hide CELLS. hide HD. hide HH.
    pose proof (mod_range64 t (if_tsresol ifc) TSR) as FR64.
    destruct (if_scale_type ifc) eqn:EST; try rewrite EST in SLOT; try rewrite EST in SFR; cbn [ngscale_code is_dec] in SLOT, SFR |- *.
    - (* [comment removed for export] *)
      step. if_false. step. step. if_false. step. step. if_true. apply (TAIL _ _ _ _ (t mod if_tsresol ifc)). exact FR64.
    - (* [comment removed for export] *)
      pose proof (SFR eq_refl) as SF.
      step. if_false. step. step. if_true. step. step. rewrite (mul_word_u64 (if_scale_factor ifc) (t mod if_tsresol ifc)) by lia.
      apply (TAIL _ _ _ _ (u64 (t mod if_tsresol ifc * if_scale_factor ifc))). apply u64_range.
    - (* [comment removed for export] *)
      pose proof (SFR eq_refl) as SF.
      step. if_false. step. step. if_false. step. step. if_false. step. step. if_false_by (eqz_false (if_scale_factor ifc) ltac:(clear -SF; lia)).
      step. rewrite (divu_lit (t mod if_tsresol ifc) (if_scale_factor ifc)) by lia. step.
      apply (TAIL _ _ _ _ (t mod if_tsresol ifc / if_scale_factor ifc)). apply div_range64; [exact FR64| lia].
    - (* [comment removed for export] *)
      pose proof (u64_range (t mod if_tsresol ifc * ng_user_tsresol sx)) as UR.
      step. if_true. step. step. if_true. step. step. step. rewrite (mul_word_u64 (ng_user_tsresol sx) (t mod if_tsresol ifc)) by lia.
      step. rewrite (divu_lit (u64 (t mod if_tsresol ifc * ng_user_tsresol sx)) (if_tsresol ifc)) by lia. step.
      apply (TAIL _ _ _ _ (u64 (t mod if_tsresol ifc * ng_user_tsresol sx) / if_tsresol ifc)). apply div_range64; [exact UR| lia].
    - (* [comment removed for export] *)
      pose proof (u64_range (t mod if_tsresol ifc * ng_user_tsresol sx)) as UR.
      step. if_true. step. step. if_false. step. step. if_false. step. step. step. rewrite (mul_word_u64 (ng_user_tsresol sx) (t mod if_tsresol ifc)) by lia.
      step. rewrite (divu_lit (u64 (t mod if_tsresol ifc * ng_user_tsresol sx)) (if_tsresol ifc)) by lia. step.
      apply (TAIL _ _ _ _ (u64 (t mod if_tsresol ifc * ng_user_tsresol sx) / if_tsresol ifc)). apply div_range64; [exact UR| lia].
  Qed.
  End Sz24.
  Lemma ngn_ts : ltac:(let t := eval cbv delta [ngn_ts__stmt] in ngn_ts__stmt in exact t).
  Proof using AD AH ALN BU HFL LO P1 P2 P4 P5 P6 PP R1 R2 R3 SFL SNPRINTF SP47 SPM SPW TP W1 W10 W2 W5 W6 W7 W8 W9. intros ra' t0' t1' t2' a4' a6' x2 x4 x5 x6 x7 x8 x9 x10 x11 t3' t4' t5' t6' iw cw hj1 hj2 m5 ps bq Bq Ix alloc doff rem data eb sx ix id t cap len bt dw dj cv1 cv2 cv3 cpad. ltac2:(SecDiet.SzSec.closeP 'ngn_ts__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.

  (* [comment removed for export] *)
  Definition ngn_found__stmt : Prop := forall (ra' t0' t1' t2' a4' a6' x2 x4 x5 x6 x7 x8 x9 x10 x11 t3' t4' t5' t6' iw cw : word) (hj1 hj2 : list byte) (m5 : mem) (ps : PState H hptr)
           (bq : hptr) (Bq Ix alloc doff rem : Z) (data eb : list Z) (sx : pcap_ng_sf) (ix : option hptr) (id t cap len bt : Z) (dw : cell) (dj : list byte)
           (cv1 cv2 cv3 : word) (cpad : list byte),
      stk usegs m5 lo (bv_unsigned sp + -160) ->
      rw_cells usegs m5 (bv_unsigned sp + -160) (ngn_frame dj [C8 cv1; C8 cv2; C4 cv3; CB 4 cpad]) -> mem_inv usegs m5 ->
      GIo K R ps (CLc ++ pcap_blocks (pv bq alloc data eb sx ix) P Bq Ix) FB m5 ->
      PCAPR (hptr:=hptr) P (pv bq alloc data eb sx ix) (pcap_blocks (pv bq alloc data eb sx ix) P Bq Ix) FB m5 ->
      agrees_on (fun a => client_keeps CLc (bv_unsigned sp) a /\ ~ (HA <= a < HA + 24) /\ ~ (DA <= a < DA + 8))%Z m m5 ->
      rw_cells usegs m5 HA [CB 8 hj1; CB 8 hj2; C4 (Z_to_bv 64 cap); C4 (Z_to_bv 64 len)] -> rw_cells usegs m5 DA [dw] -> csize dw = 8%nat ->
      (bv_unsigned iw mod 2^32 = id)%Z -> (bv_unsigned cw mod 2^32 = cap)%Z -> (0 <= t < 2^64)%Z ->
      Forall (fun x => 0 <= x < 256)%Z data -> (0 <= doff)%Z -> (doff mod 4 = 0)%Z -> (0 <= rem)%Z -> (doff + rem <= Z.of_nat (length data))%Z ->
      (Z.of_nat (length data) < 2^31)%Z -> (0 <= len < 2^32)%Z -> (0 <= bt < 2^32)%Z -> ps_outfile ps = o ->
      implM usegs (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Startup_B__S3.F_ngnextB.TwB.ngn_foundK (mkFound id t cap len (mkCursor doff rem bt)) (pv bq alloc data eb sx ix)) ps POSTQ
        (MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -160)) gp tp t0' t1' t2' (Z_to_bv 64 (-1)) (Z_to_bv 64 (P + 216))
                 (Z_to_bv 64 rem) cw iw (Z_to_bv 64 (s32 bt)) a4' (Z_to_bv 64 (Bq + doff)) a6' (Z_to_bv 64 t)
                 x2 (Z_to_bv 64 P) x4 x5 x6 x7 x8 x9 x10 x11 t3' t4' t5' t6') F (Z_to_bv 64 0x180e0) fc None m5 (seg_rom usegs)).
  Section Sz25.
  Variables ra' t0' t1' t2' a4' a6' x2 x4 x5 x6 x7 x8 x9 x10 x11 t3' t4' t5' t6' iw cw hj1 hj2 m5 ps bq Bq Ix alloc doff rem data eb sx ix id t cap len bt dw dj cv1 cv2 cv3 cpad : ltac2:(SecDiet.SzSec.tyM 'ngn_found__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra').
  Lemma ngn_found__body : ltac2:(SecDiet.SzSec.bodyP 'ngn_found__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof using AD AH ALN BU HFL LO P1 P2 P4 P5 P6 PP R1 R2 R3 SFL SNPRINTF SP47 SPM SPW TP W1 W10 W2 W5 W6 W7 W8 W9. pin_using (fun (AD AH ALN BU HFL LO P1 P2 P4 P5 P6 PP R1 R2 R3 SFL SNPRINTF SP47 SPM SPW TP W1 W10 W2 W5 W6 W7 W8 W9 : unit) => tt).
 intros ST5 FR5 MI5 G5 PC5 AG5 HH HD Hd Hiw Hcw Ht DRNG Hdoff Hd4 Hrem Hdr Hl31 Hlen Hbt OF5.
    pose proof (bv_unsigned_in_range 64 sp) as RSP.
    pose proof (bv_unsigned_in_range 64 iw) as RIW. change (bv_modulus 64) with (2^64)%Z in RIW.
    pose proof (bv_unsigned_in_range 64 cw) as RCW. change (bv_modulus 64) with (2^64)%Z in RCW.
    assert (IDR : (0 <= id < 2^32)%Z) by (rewrite <- Hiw; apply Z.mod_pos_bound; lia).
    assert (CAP : (0 <= cap < 2^32)%Z) by (rewrite <- Hcw; apply Z.mod_pos_bound; lia).
    pose proof PC5 as (Afx & Hin & (Bx' & Ix' & jx' & padx & bsx' & EPB & CELLS & PRIV & BUF & PFX & IFS & WF)).
    pose proof WF as (_ & _ & W3 & W4 & _ & _ & _ & _ & _ & _ & _ & _ & WNG & WBB).
    unfold S3.F_ngnextA.TwB.pv in WNG. cbn [pc_priv] in WNG. destruct WNG as (UT & WMB & WIC & WIS).
    (* [comment removed for export] *)
    unfold OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Startup_B__S3.F_ngnextB.TwB.ngn_foundK. cbn [f_interface_id f_caplen ng_of pc_priv pc_snapshot S3.F_ngnextA.TwB.pv].
    unfold pcap_cells_gen, pc_pre, hdr_cells, pc_ops, np_entry, cleanup_entry, is_ng, PCAP_PRIV_OFF, S3.F_ngnextA.TwB.pv in CELLS.
    cbn [app pc_bufsize pc_break_loop pc_swapped pc_version_major pc_version_minor pc_snapshot pc_linktype pc_linktype_ext pc_tstamp_precision pc_header pc_priv pk_next_ng pk_cleanup_ng PK] in CELLS.
    unfold priv_cells, S3.F_ngnextA.TwB.pv in PRIV. cbn [pc_priv] in PRIV. unfold ng_cells, PCAP_PRIV_OFF in PRIV.
    pose proof FR5 as FRJ. unfold S3.F_ngnextA.TwB.ngn_frame in FRJ. apply rw_cells_app in FRJ as [FRJ _].
    hide FR5. hide BUF. hide HD. hide HH. hide IFS.
    pose proof (munch_refl ([] : list (Z * Z)) m5) as MU. pose proof (wmono_refl usegs m5) as WM.
    unfold implM. iprefix.
    step. step. if_false_by (eqz_false (P + 648) ltac:(clear -P1 P4; lia)).
    step. step. if_false.
    step. step. step. step.
    if_cases BR; zify_cond BR.
    - (* [comment removed for export] *)
      rewrite sextw_mod, Hiw, (unsigned_sx32' (ng_ifcount sx)) in BR by lia.
      assert (LE : (ng_ifcount sx <= id)%Z) by (pose proof (sxu_mono id (ng_ifcount sx) IDR WIC); lia).
      replace (ng_ifcount sx <=? id) with true by (symmetry; apply Z.leb_le; exact LE). cbv iota.
      step. step. step. step. step. step. step.
      unhide FR5. unhide HD. unhide HH. unhide IFS.
      assert (MSG : fmt_at m5 NGN_FMT_NOIDB "a packet arrived on interface %u, but there's no Interface Description Block for that interface"%string)
        by (apply fmt_at_intro; [exact MI5 | vm_compute; reflexivity | unfold NGN_FMT_NOIDB; lia | unfold NGN_FMT_NOIDB; cbn; lia]).
      unfold NGN_FMT_NOIDB in MSG. unfold NGN_EPILOGUE in *.
      apply evt_done. eapply ngn_snp with (args := [AInt (bv_swrap 32 (bv_unsigned iw + 0))]);
        [exact ST5 | exact FR5 | reflexivity | exact MI5 | | exact MSG | reflexivity | cbn; lia | cbn; apply Forall2_cons; [reflexivity| apply Forall2_nil]].
      split; [exact G5|]. split; [apply PCAPR_closable_of; exact PC5|]. split; [exact AG5|]. split; [exact HH|]. split; [reflexivity|].
      split; [exact HD|]. split; [exact Hd| exact OF5].
    - rewrite sextw_mod, Hiw, (unsigned_sx32' (ng_ifcount sx)) in BR by lia.
      assert (LT : (id < ng_ifcount sx)%Z) by (pose proof (sxu_mono id (ng_ifcount sx) IDR WIC); lia).
      replace (ng_ifcount sx <=? id) with false by (symmetry; apply Z.leb_gt; exact LT). cbv iota.
      unfold INT_MAX in W1.
      step. step. rewrite (and7_aligned HA) by (gio_ceil_fact; clear -CLO__ AH R1 R2 R3 BU LO SPW SP47; unfold rc_spmain in *; lia). step. if_false.
      step. rewrite (sx32_small snapshot) by lia. step. step.
      if_cases BR2; zify_cond BR2.
      + (* [comment removed for export] *)
        rewrite sextw_mod, Hcw, ?(unsigned_lit snapshot) in BR2 by lia.
        pose proof (sxu_range cap CAP) as (SX1 & SX2 & SX3).
        assert (LE : (cap <= snapshot)%Z) by (destruct (Z_lt_dec cap (2^31)); [rewrite SX2 in BR2 by lia; lia| exfalso; specialize (SX3 ltac:(lia)); lia]).
        replace (snapshot <? cap) with false by (symmetry; apply Z.ltb_ge; exact LE). cbv iota.
        unhide FR5. unhide BUF. unhide HD. unhide HH. unhide IFS.
        apply evt_done. eapply ngn_ts; [exact ST5 | exact FR5 | exact MI5 | exact G5 | exact PC5 | exact AG5 | exact HH | exact HD | exact Hd
                                      | exact Hiw | exact Hcw | lia | exact Ht | exact DRNG | exact Hdoff | exact Hd4 | exact Hrem | exact Hdr | exact Hl31 | exact Hlen | exact Hbt | exact OF5].
      + (* [comment removed for export] *)
        rewrite sextw_mod, Hcw, ?(unsigned_lit snapshot) in BR2 by lia.
        pose proof (sxu_range cap CAP) as (SX1 & SX2 & SX3).
        assert (LT2 : (snapshot < cap)%Z) by (destruct (Z_lt_dec cap (2^31)); [rewrite SX2 in BR2 by lia; lia| lia]).
        replace (snapshot <? cap) with true by (symmetry; apply Z.ltb_lt; exact LT2). cbv iota.
        step. step. step. step. step. step.
        unhide FR5. unhide HD. unhide HH. unhide IFS.
        assert (MSG : fmt_at m5 NGN_FMT_CAPLEN "invalid packet capture length %u, bigger than snaplen of %d"%string)
          by (apply fmt_at_intro; [exact MI5 | vm_compute; reflexivity | unfold NGN_FMT_CAPLEN; lia | unfold NGN_FMT_CAPLEN; cbn; lia]).
        unfold NGN_FMT_CAPLEN in MSG.
        eapply (ngn_snp_call 0x18130) with (m5 := m5) (ps := ps) (p' := pv bq alloc data eb sx ix) (dw := dw) (dj := dj)
                                            (args := [AInt (bv_swrap 32 (bv_unsigned cw + 0)); AInt snapshot]);
          [exact ST5 | exact FR5 | reflexivity | exact MI5 | | exact MSG | reflexivity | cbn; lia | cbn; apply Forall2_cons; [reflexivity| apply Forall2_cons; [reflexivity| apply Forall2_nil]] | lia | reflexivity |].
        { split; [exact G5|]. split; [apply PCAPR_closable_of; exact PC5|]. split; [exact AG5|]. split; [exact HH|]. split; [reflexivity|].
          split; [exact HD|]. split; [exact Hd| exact OF5]. }
        intros m6 t0'' t1'' t2'' a0'' a1'' a2'' a3'' a4'' a5'' a6'' a7'' t3'' t4'' t5'' t6'' ST6 FR6 MI6 FIN6.
        pose proof (FIN6 (Msg.invalid_caplen_snaplen cap snapshot)) as FIN.
        pose proof FIN as (G6 & PC6 & AG6 & HH6 & Hh6 & HD6 & Hd6 & OF6).
        clear MU WM. pose proof (munch_refl ([] : list (Z * Z)) m6) as MU. pose proof (wmono_refl usegs m6) as WM.
        hide FR6. hide HH6. hide HD6. step. unhide FR6. unhide HH6. unhide HD6.
        unfold NGN_EPILOGUE in *.
        apply evt_done. eapply ngn_ret_m1; [exact ST6 | exact FR6 | reflexivity | exact MI6 | exact FIN].
  Qed.
  End Sz25.
  Lemma ngn_found : ltac:(let t := eval cbv delta [ngn_found__stmt] in ngn_found__stmt in exact t).
  Proof using AD AH ALN BU HFL LO P1 P2 P4 P5 P6 PP R1 R2 R3 SFL SNPRINTF SP47 SPM SPW TP W1 W10 W2 W5 W6 W7 W8 W9. intros ra' t0' t1' t2' a4' a6' x2 x4 x5 x6 x7 x8 x9 x10 x11 t3' t4' t5' t6' iw cw hj1 hj2 m5 ps bq Bq Ix alloc doff rem data eb sx ix id t cap len bt dw dj cv1 cv2 cv3 cpad. ltac2:(SecDiet.SzSec.closeP 'ngn_found__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.
End NgnCtx.

End WithCeil.
End TwB.
End F_ngnextT.

(* [comment removed for export] *)
Module Vsn_iface.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool String.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Sem.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import Tac Arr Bytes ITree Nodes Decode SysStep ImgSrc3.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Import Prelim Monad Fmt StdioCore Stdio PcapPrelim PcapTypes PcapPure Pcap Prog.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require InitMem. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require Printf_kit__Musl. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require FileCells__Musl. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.InitMem OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_kit__Musl.StartupKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.FileCells__Musl.FileCells.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require Exit__S3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require GI. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require GIFacts__S3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require PcapRep. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require Pcap_iface__S3. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Startup_B__S3.Startup OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Exit__S3.Exit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.GI OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.GIFacts__S3.GIFacts OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.GIFacts__S3.Ifaces OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.PcapRep OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Pcap_iface__S3.Pcap_iface.
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

Section WithCeil.
Context {CEILV : CEIL}.
Section Ifaces.
  Context {H hptr : Type} (HO : HeapOps H hptr) (K : modkit H hptr).
  #[local] Abbreviation cblk := (@cblock hptr).
  #[local] Abbreviation PS := (PState H hptr).
  #[local] Abbreviation SPO := (std_pre_o K).

  (* [comment removed for export] *)
  Definition vsnprintf_spec4_stmt : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (R : rctx) (s : PS) (CL FB : list cblk) (lo DST n FMTA AP : Z) (fs : string) (args : list farg)
           (ws : list word) (junk : list byte),
      SPO sp tp R s CL FB lo STDIO_STACK m ->
      a0 = Z_to_bv 64 DST -> a1 = Z_to_bv 64 n -> a2 = Z_to_bv 64 FMTA -> a3 = Z_to_bv 64 AP -> 1 <= n < 2^31 -> fmt_at m FMTA fs -> fmt_ok fs args = true ->
      length ws = length args -> (length args <= 4)%nat -> Forall2 (farg_word R CL (bv_unsigned sp) DST n m) args ws ->
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
End Ifaces.

End WithCeil.

(* [comment removed for export] *)
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require ImgTgtUbsan.
Module TwB.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Strings.String.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Sem.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Tac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Arr OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Bytes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ITree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Nodes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Decode OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.SysStep OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ImgTgtUbsan.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Monad OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Fmt OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.StdioCore OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Stdio OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapPrelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapTypes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapPure OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Pcap OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prog.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.InitMem OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_kit__Musl.StartupKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.FileCells__Musl.FileCells.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Startup_B__S3.Startup.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Exit__S3.Exit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.GI.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.GIFacts__S3.GIFacts.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.GIFacts__S3.Ifaces.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.PcapRep.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Pcap_iface__S3.Pcap_iface.TwB.
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

Section WithCeil.
Context {CEILV : CEIL}.
Section Ifaces.
  Context {H hptr : Type} (HO : HeapOps H hptr) (K : modkit H hptr).
  #[local] Abbreviation cblk := (@cblock hptr).
  #[local] Abbreviation PS := (PState H hptr).
  #[local] Abbreviation SPO := (std_pre_o K).

  (* [comment removed for export] *)
  Definition vsnprintf_spec4_stmt : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (R : rctx) (s : PS) (CL FB : list cblk) (lo DST n FMTA AP : Z) (fs : string) (args : list farg)
           (ws : list word) (junk : list byte),
      SPO sp tp R s CL FB lo STDIO_STACK m ->
      a0 = Z_to_bv 64 DST -> a1 = Z_to_bv 64 n -> a2 = Z_to_bv 64 FMTA -> a3 = Z_to_bv 64 AP -> 1 <= n < 2^31 -> fmt_at m FMTA fs -> fmt_ok fs args = true ->
      length ws = length args -> (length args <= 4)%nat -> Forall2 (farg_word R CL (bv_unsigned sp) DST n m) args ws ->
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
End Ifaces.

End WithCeil.
End TwB.
End Vsn_iface.

(* [comment removed for export] *)
Module Compose.
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Sem.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import PropExec MState Mem Cells Exec Step Frame Tac ITree Nodes Decode RegsEquiv ImgSrc3.
From OSSVerify.libpcap.fuzz_pcap.images Require Import Plain.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Kernel Require Import Fork.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Monad. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Adapter__Spec. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require StartupFacts. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Monad OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Adapter__Spec.StartupModel OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.StartupFacts.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require Printf_kit__Musl. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_kit__Musl.StartupKit.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require Exit__S3. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Startup_B__S3.Startup OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Exit__S3.Exit.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib Require Import TopLevel.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Top Require Import EntryCeil.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import LiaPin.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac lia ::= pinned_lia.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Open Scope mspec_scope.

Section WithCeil.
Context {CEILV : CEIL}.
Section Compose.
  Context {St : Type}.
  Variables (set_tls : Z -> St -> St).
  (* [comment removed for export] *)
  Variables (main : ExecEntry -> ProcInput -> M St Z) (stdio_exit_model : M St unit).
  (* [comment removed for export] *)
  Variable SX : St -> word -> (word -> option byte) -> Prop.
  Variable stdio_exit_frame : Z.
  Hypothesis stdio_exit_frame_nonneg : 0 <= stdio_exit_frame.
  Hypothesis SX_frame : forall s tp m m',
    SX s tp m -> munch exit_footprint m m' -> wmono ssegs m m' -> SX s tp m'.
  Hypothesis STDIO_EXIT : stdio_exit_stmt stdio_exit_model SX stdio_exit_frame.
  (* [comment removed for export] *)
  Variable P0 : St -> Prop.
  (* [comment removed for export] *)
  Variable EN_OK : ExecEntry -> Prop.
  Hypothesis EN_CLO : forall en, EN_OK en -> (alloc_ceiling <= bv_unsigned (en_sp en) - 8388608)%Z.

  (* [comment removed for export] *)
  Definition main_stmt : Prop :=
    forall (en : ExecEntry) (inp : ProcInput) (tp : word) (s : St) (ms : machine_state),
      P0 s -> EN_OK en ->
      valid_entry (mkImage ssegs Plain.M.init_pc Plain.M.phdrs) en inp -> valid_input inp ->
      at_main (en_sp en) (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp) (en_draw en) tp ms ->   (* [comment removed for export] *)
      implM ssegs (main en inp) (set_tls (bv_unsigned tp - 200) s)
            (fun code s' ms' => at_exit SX stdio_exit_frame code s' ms') ms.
  Hypothesis MAIN : main_stmt.

  Definition prog (en : ExecEntry) (inp : ProcInput) : M St Empty_set :=
    startup_model set_tls 0x339d0 ;;;
    code <- main en inp ;;
    exit_model stdio_exit_model code.

  Definition prog_tree (en : ExecEntry) (inp : ProcInput) (s0 : St) : itree node (exc unit) :=
    ebind (prog en inp s0) (fun p => match fst p : Empty_set with end).

  Theorem prog_impl_from_main : forall (s0 : St) (en : ExecEntry) (inp : ProcInput),
      P0 s0 ->
      valid_entry (mkImage ssegs Plain.M.init_pc Plain.M.phdrs) en inp ->
      valid_input inp ->
      EN_OK en ->      (* [comment removed for export] *)
      impl ssegs (at_node ssegs) (npeek ssegs) (prog_tree en inp s0) (epost (fun (_ : unit) (_ : machine_state) => True))
           (ms0 ssegs Plain.M.init_pc Plain.M.phdrs en inp).
  Proof using EN_CLO MAIN STDIO_EXIT SX_frame stdio_exit_frame_nonneg. pin_using (fun (EN_CLO MAIN STDIO_EXIT SX_frame stdio_exit_frame_nonneg : unit) => tt). ceil_facts.
    intros s0 en inp HP0 VE VI ENOK. pose proof (EN_CLO en ENOK) as CLO.
    pose proof VE as VE'. pose proof VI as VI'.
    apply (valid_entry_sv48 _ _ _ (valid_input_sv48 inp VI)) in VE.   (* [comment removed for export] *)
    destruct en as [sp0 brk mb rnd].
    destruct VE as (VSP & _ & _ & FITS). destruct VI as (VARGV & VENVP & _).
    destruct inp as [argv envp fs sin uid gid groups net nofile sigmask hw abterm vasz]; cbn [en_sp en_draw in_argv in_envp in_uid in_hwcap] in *.
    unfold ms0. cbn [en_sp en_draw in_argv in_envp in_uid in_hwcap].
    unfold prog_tree.
    eapply (impl_ebind _ _ _ _ _ _ (fun (_ : Empty_set * St) (_ : machine_state) => True)).
    2:{ intros [v ?] ms' _. destruct v. }
    unfold prog. unfold Monad.mbind at 1.
    eapply (impl_ebind _ _ _ _ _ _ (fun (p : unit * St) ms' => startup_post set_tls sp0 argv envp uid hw rnd s0 (fst p) (snd p) ms')).
    - pose proof (startup_spec set_tls sp0 argv envp uid hw rnd VSP VARGV VENVP FITS CLO s0) as SU.
      unfold implM in SU. eapply impl_epost_mono; [exact SU|]. intros [[] s'] ms' H. exact H.
    - intros [[] s] ms' SP. cbn [fst snd] in SP. unfold startup_post in SP. destruct SP as (tp & -> & AM).
      cbn [fst snd].
      lazymatch goal with |- impl _ _ _ (mbind ?mn _ _) _ _ =>
        change (implM ssegs (mbind mn (fun code => exit_model stdio_exit_model code))
                  (set_tls (bv_unsigned tp - 200) s0) (fun _ _ _ => True) ms') end.
      eapply (implM_bind ssegs).
      + exact (MAIN _ _ tp s0 ms' HP0 ENOK VE' VI' AM).
      + intros code s' ms'' AE. cbn in AE. eapply (exit_spec stdio_exit_model SX stdio_exit_frame); try eassumption.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  (* [comment removed for export] *)
  Lemma floor_free_ssegs : floor_free ssegs.
  Proof using CEILV. pin_using (fun (CEILV : unit) => tt). ceil_facts. vm_compute. reflexivity. Qed.

  (* The thread descriptor window lies in the image's writable segment. *)
  Lemma tls_in_image_ssegs : tls_in_image ssegs 0x339d0.
  Proof using Type.
    apply (tls_in_image_intro ssegs 0x339d0 0x23000 0x32000); [lia | vm_compute; do 3 right; left; reflexivity | lia | unfold TLS_MAPLEN; lia].
  Qed.
End Compose.

End WithCeil.

(* [comment removed for export] *)
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require ImgTgtUbsan.
From OSSVerify.libpcap.fuzz_pcap.images Require Ubsan.
Module TwB.
(* [comment removed for export] *)
(* [comment removed for export] *)

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.EquivalenceDefinition.Equivalence.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Sem.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.PropExec OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.MState OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Mem OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Cells OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Exec OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Step OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Frame OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Tac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ITree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Nodes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Decode OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.RegsEquiv OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ImgTgtUbsan.
Import OSSVerify.libpcap.fuzz_pcap.images.Ubsan.
Import LinuxProcessSemantics.LinuxProcessSem.Sys.Kernel.Fork.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Monad OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Adapter__Spec.StartupModel OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.StartupFacts.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_kit__Musl.StartupKit.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Startup_B__S3.Startup.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Exit__S3.Exit.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.TopLevel.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Top.EntryCeil.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.LiaPin.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac lia ::= pinned_lia.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Open Scope mspec_scope.

Section WithCeil.
Context {CEILV : CEIL}.
Section Compose.
  Context {St : Type}.
  Variables (set_tls : Z -> St -> St).
  (* [comment removed for export] *)
  Variables (main : ExecEntry -> ProcInput -> M St Z) (stdio_exit_model : M St unit).
  (* [comment removed for export] *)
  Variable SX : St -> word -> (word -> option byte) -> Prop.
  Variable stdio_exit_frame : Z.
  Hypothesis stdio_exit_frame_nonneg : 0 <= stdio_exit_frame.
  Hypothesis SX_frame : forall s tp m m',
    SX s tp m -> munch exit_footprint m m' -> wmono usegs m m' -> SX s tp m'.
  Hypothesis STDIO_EXIT : stdio_exit_stmt stdio_exit_model SX stdio_exit_frame.
  (* [comment removed for export] *)
  Variable P0 : St -> Prop.
  (* [comment removed for export] *)
  Variable EN_OK : ExecEntry -> Prop.
  Hypothesis EN_CLO : forall en, EN_OK en -> (alloc_ceiling <= bv_unsigned (en_sp en) - 8388608)%Z.

  (* [comment removed for export] *)
  Definition main_stmt : Prop :=
    forall (en : ExecEntry) (inp : ProcInput) (tp : word) (s : St) (ms : machine_state),
      P0 s -> EN_OK en ->
      valid_entry (mkImage usegs Ubsan.M.init_pc Ubsan.M.phdrs) en inp -> valid_input inp ->
      at_main (en_sp en) (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp) (en_draw en) tp ms ->   (* [comment removed for export] *)
      implM usegs (main en inp) (set_tls (bv_unsigned tp - 200) s)
            (fun code s' ms' => at_exit SX stdio_exit_frame code s' ms') ms.
  Hypothesis MAIN : main_stmt.

  Definition prog (en : ExecEntry) (inp : ProcInput) : M St Empty_set :=
    startup_model set_tls 0x34190 ;;;
    code <- main en inp ;;
    exit_model stdio_exit_model code.

  Definition prog_tree (en : ExecEntry) (inp : ProcInput) (s0 : St) : itree node (exc unit) :=
    ebind (prog en inp s0) (fun p => match fst p : Empty_set with end).

  Theorem prog_impl_from_main : forall (s0 : St) (en : ExecEntry) (inp : ProcInput),
      P0 s0 ->
      valid_entry (mkImage usegs Ubsan.M.init_pc Ubsan.M.phdrs) en inp ->
      valid_input inp ->
      EN_OK en ->      (* [comment removed for export] *)
      impl usegs (at_node usegs) (npeek usegs) (prog_tree en inp s0) (epost (fun (_ : unit) (_ : machine_state) => True))
           (ms0 usegs Ubsan.M.init_pc Ubsan.M.phdrs en inp).
  Proof using EN_CLO MAIN STDIO_EXIT SX_frame stdio_exit_frame_nonneg. pin_using (fun (EN_CLO MAIN STDIO_EXIT SX_frame stdio_exit_frame_nonneg : unit) => tt). ceil_facts.
    intros s0 en inp HP0 VE VI ENOK. pose proof (EN_CLO en ENOK) as CLO.
    pose proof VE as VE'. pose proof VI as VI'.
    apply (valid_entry_sv48 _ _ _ (valid_input_sv48 inp VI)) in VE.   (* [comment removed for export] *)
    destruct en as [sp0 brk mb rnd].
    destruct VE as (VSP & _ & _ & FITS). destruct VI as (VARGV & VENVP & _).
    destruct inp as [argv envp fs sin uid gid groups net nofile sigmask hw abterm vasz]; cbn [en_sp en_draw in_argv in_envp in_uid in_hwcap] in *.
    unfold ms0. cbn [en_sp en_draw in_argv in_envp in_uid in_hwcap].
    unfold prog_tree.
    eapply (impl_ebind _ _ _ _ _ _ (fun (_ : Empty_set * St) (_ : machine_state) => True)).
    2:{ intros [v ?] ms' _. destruct v. }
    unfold prog. unfold Monad.mbind at 1.
    eapply (impl_ebind _ _ _ _ _ _ (fun (p : unit * St) ms' => startup_post set_tls sp0 argv envp uid hw rnd s0 (fst p) (snd p) ms')).
    - pose proof (startup_spec set_tls sp0 argv envp uid hw rnd VSP VARGV VENVP FITS CLO s0) as SU.
      unfold implM in SU. eapply impl_epost_mono; [exact SU|]. intros [[] s'] ms' H. exact H.
    - intros [[] s] ms' SP. cbn [fst snd] in SP. unfold startup_post in SP. destruct SP as (tp & -> & AM).
      cbn [fst snd].
      lazymatch goal with |- impl _ _ _ (mbind ?mn _ _) _ _ =>
        change (implM usegs (mbind mn (fun code => exit_model stdio_exit_model code))
                  (set_tls (bv_unsigned tp - 200) s0) (fun _ _ _ => True) ms') end.
      eapply (implM_bind usegs).
      + exact (MAIN _ _ tp s0 ms' HP0 ENOK VE' VI' AM).
      + intros code s' ms'' AE. cbn in AE. eapply (exit_spec stdio_exit_model SX stdio_exit_frame); try eassumption.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  (* [comment removed for export] *)
  Lemma floor_free_usegs : floor_free usegs.
  Proof using CEILV. pin_using (fun (CEILV : unit) => tt). ceil_facts. vm_compute. reflexivity. Qed.

  (* The thread descriptor window lies in the image's writable segment. *)
  Lemma tls_in_image_usegs : tls_in_image usegs 0x34190.
  Proof using Type.
    apply (tls_in_image_intro usegs 0x34190 0x23000 0x33000); [lia | vm_compute; do 3 right; left; reflexivity | lia | unfold TLS_MAPLEN; lia].
  Qed.
End Compose.

End WithCeil.
End TwB.
End Compose.
