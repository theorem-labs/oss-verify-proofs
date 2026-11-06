(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Lia.
(* [comment removed for export] *)
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require AllocBridge__Spec.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require TlsBase.
From Stdlib Require ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Tac ITree Nodes SysStep Decode.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require ImgSrc3.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require F_mm_syscalls.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_lock__S3.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require RMallocRep__S3.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require MSecret.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require LiaPin.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require SecDiet.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require ImgTgtUbsan.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require TlsBaseU.
From stdpp Require gmap.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Image ZBridge Arr.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require SFModel.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require MallocTree.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require MallocKit_A2__MA.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require STree Malloc.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require KInv__Spec.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require MI_Realloc2__Spec.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require F_malloc_free__MA.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require MallocBlocks__MA.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require MallocFacts_A__MA.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require F_am_F__MA.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require MallocCtrl.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require RF_am_A__S3.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require RF_get_meta__S3.
From LinuxProcessSemantics.LinuxProcessSem Require Fs.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require KStep__Spec.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require RF_malloc_entry__S3.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Monad.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require Malloc_fp F_malloc_bigw.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require RMallocKit_A.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require RF_enframe.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require RF_free_K__S3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Module RF_mm_syscalls.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require AllocBridge__Spec. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.AllocBridge__Spec.AllocBridge.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require Import TlsBase.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import Tac ITree Nodes SysStep Decode.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import ImgSrc3.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require Import F_mm_syscalls.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_lock__S3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require RMallocRep__S3. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_lock__S3.F_syscalls OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RMallocRep__S3.RMallocRep.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require Import MSecret.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import LiaPin.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require SecDiet.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac lia ::= pinned_lia.
Import ListNotations.
Open Scope bv_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
(* [comment removed for export] *)
Section WithCeil.
Context {CEILV : CEIL} {MSECV : MSEC}.
Section PORT.
Context {PState : Type} {AS : AllocSt PState} {TB : TlsBase}.
Let TLSFACTS := the_tb_facts (TB:=TB).

Local Unset Keyed Unification.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma dec_mmap_err_enomem len avoid rsp e : dec_mmap len avoid rsp = Some (MmErr e) -> e = ENOMEM.
Proof using MSECV. pin_using (fun (MSECV : unit) => tt). ceil_facts. msec_facts.
  unfold dec_mmap. destruct (core rsp) as [[[[r ws] zs] us]|]; [|discriminate].
  destruct ws; [|discriminate]. destruct zs as [|[a n] [|? ?]]; destruct us; try discriminate.
  - destruct (mm_errno_of r) eqn:E; [|discriminate]. intros H. inversion H; subst. exact (proj2 (mm_errno_of_Some _ _ E)).
  - destruct (bv_eqb a r && bv_eqb n _ && mmap_addr_ok len avoid (bv_unsigned r)); discriminate.
Qed.
Lemma dec_mmap_none_err_enomem len avoid rsp e : dec_mmap_none len avoid rsp = Some (MmErr e) -> e = ENOMEM.
Proof using MSECV. pin_using (fun (MSECV : unit) => tt). ceil_facts. msec_facts.
  unfold dec_mmap_none. destruct (core rsp) as [[[[r ws] zs] us]|]; [|discriminate].
  destruct ws; [|discriminate]. destruct zs; [|discriminate]. destruct us as [|[a n] [|? ?]]; try discriminate.
  - destruct (mm_errno_of r) eqn:E; [|discriminate]. intros H. inversion H; subst. exact (proj2 (mm_errno_of_Some _ _ E)).
  - destruct (bv_eqb a r && bv_eqb n _ && mmap_addr_ok len avoid (bv_unsigned r)); discriminate.
Qed.
Lemma dec_munmap_err_enomem A L rsp e : dec_munmap A L rsp = Some (RgErr e) -> e = ENOMEM.
Proof using CEILV MSECV. pin_using (fun (CEILV MSECV : unit) => tt). ceil_facts. msec_facts.
  unfold dec_munmap. destruct (core rsp) as [[[[r ws] zs] us]|]; [|discriminate].
  destruct ws; [|discriminate]. destruct zs; [|discriminate]. destruct us as [|[a n] [|? ?]]; try discriminate.
  - destruct (mm_errno_of r) eqn:E. { intros H. inversion H; subst. exact (proj2 (mm_errno_of_Some _ _ E)). }
    destruct (bv_unsigned r =? 0)%Z; [|discriminate]. intros H; inversion H.
  - destruct ((bv_unsigned r =? 0)%Z && bv_eqb a _ && bv_eqb n _); [|discriminate]. intros H; inversion H.
Qed.
Lemma dec_mprotect_err_enomem A L rsp e : dec_mprotect A L rsp = Some (RgErr e) -> e = ENOMEM.
Proof using CEILV MSECV. pin_using (fun (CEILV MSECV : unit) => tt). ceil_facts. msec_facts.
  unfold dec_mprotect. destruct (core rsp) as [[[[r ws] zs] us]|]; [|discriminate].
  destruct ws; [|discriminate]. destruct zs as [|[a n] [|? ?]]; destruct us; try discriminate.
  - destruct (mm_errno_of r) eqn:E. { intros H. inversion H; subst. exact (proj2 (mm_errno_of_Some _ _ E)). }
    destruct (bv_unsigned r =? 0)%Z; [|discriminate]. intros H; inversion H.
  - destruct ((bv_unsigned r =? 0)%Z && bv_eqb a _ && bv_eqb n _); [|discriminate]. intros H; inversion H.
Qed.

(* [comment removed for export] *)
Lemma rg_err_range (P : Z -> Prop) (a : range_ans) :
  match a with RgErr e => (1 <= e <= 4095)%Z /\ P e | RgDone _ => True end ->
  match a with RgErr e => (1 <= e <= 4095)%Z | RgDone _ => True end.
Proof using MSECV TLSFACTS. pin_using (fun (MSECV TLSFACTS : unit) => tt). ceil_facts. msec_facts. destruct a; tauto. Qed.

Definition rmunmap_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (A L : Z) (errv : word) (lo : Z) (m : word -> option byte) (a : range_ans) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (munmap_ret a) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom ssegs)
    /\ munch [(bv_unsigned sp - 48, bv_unsigned sp); (errno_addr tp, errno_addr tp + 4); (A, A + mmap_len L)]%Z m m'
    /\ (match a with RgDone true => True | _ => wmono ssegs m m' end)
    /\ mem_inv ssegs m'
    /\ stk ssegs m' lo (bv_unsigned sp)
    /\ rw_cells ssegs m' (errno_addr tp) [C4 (rg_errno a errv)]
    /\ match a with RgErr e => (1 <= e <= 4095)%Z /\ e = ENOMEM | _ => True end.

Definition rmunmap_spec__stmt : Prop := forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
    (A L : Z) (errv : word) (lo : Z),
  stk ssegs m lo (bv_unsigned sp) ->
  rw_cells ssegs m (errno_addr tp) [C4 errv] ->
  mem_inv ssegs m ->
  a0 = Z_to_bv 64 A -> a1 = Z_to_bv 64 L ->
  (0 < A)%Z -> (A + mmap_len L <= 2^64)%Z -> (0 < L < 2^64)%Z ->
  (lo <= bv_unsigned sp - 48)%Z ->
  (errno_addr tp + 4 <= bv_unsigned sp - 48 \/ bv_unsigned sp <= errno_addr tp)%Z ->
  (A + mmap_len L <= lo \/ bv_unsigned sp <= A)%Z ->
  (A + mmap_len L <= errno_addr tp \/ errno_addr tp + 4 <= A)%Z ->
  (164 <= bv_unsigned tp)%Z ->
  impl ssegs (at_node ssegs) (npeek ssegs) (enode (NMunmap A L) (dec_munmap A L))
       (epost (rmunmap_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc A L errv lo m))
       (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
           F (Z_to_bv 64 rmunmap_entry) fc None m (seg_rom ssegs)).
Section Sz1.
Variables ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m A L errv lo : ltac2:(SecDiet.SzSec.tyM 'rmunmap_spec__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra).
Lemma rmunmap_spec__body : ltac2:(SecDiet.SzSec.bodyP 'rmunmap_spec__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
Proof using MSECV TLSFACTS. pin_using (fun (MSECV TLSFACTS : unit) => tt). ceil_facts. msec_facts.
  intros ST ERR MI -> -> A0 AL L0 LO SEP1 SEP2 SEP3 TP.
  pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp); (errno_addr tp, errno_addr tp + 4); (A, A + mmap_len L)]%Z m) as MU.
  pose proof (wmono_refl ssegs m) as WM.
  pose proof (mmap_len_ge L) as ML.
  unfold rmunmap_entry. apply impl_enode.
  carve_frame 32%nat ST.
  do 6 step. (* [comment removed for export] *)
  step. step. (* [comment removed for export] *)
  do 3 step. (* [comment removed for export] *)
  step_ecall.
  split. { at_node_solve. }
  intros rsp ans Hdec. pose proof (dec_munmap_Some _ _ _ _ Hdec) as D.
  destruct ans as [e|[|]].
  - pose proof (dec_munmap_err_enomem _ _ _ _ Hdec) as HE. clear Hdec. destruct D as [-> He]. unfold efferr, eff0. sys_nret.
    step. call_sp sysret_spec; [exact ST | exact ERR | exact MI | lia | lia | lia | ]. rename PC into ST; rename POST into ERR.
    unfold sysret_val, sysret_errno in *. rewrite errno_of_errno_ret in * by lia.
    step. step. step. step. step. step. release_frame FR ST (bv_unsigned sp).
    unfold rmunmap_post, munmap_ret, rg_errno. finish; lia.
  - rewrite D. sys_nret.
    step. call_sp sysret_spec; [exact ST | exact ERR | exact MI | lia | lia | lia | ]. rename PC into ST; rename POST into ERR.
    unfold sysret_val, sysret_errno in *. rewrite errno_of_lit in * by lia.
    step. try rewrite sextw_small by lia. step. step. step. step. step. release_frame FR ST (bv_unsigned sp).
    unfold rmunmap_post, munmap_ret, rg_errno. finish; exact I.
  - rewrite D. unfold eff0. sys_nret.
    step. call_sp sysret_spec; [exact ST | exact ERR | exact MI | lia | lia | lia | ]. rename PC into ST; rename POST into ERR.
    unfold sysret_val, sysret_errno in *. rewrite errno_of_lit in * by lia.
    step. try rewrite sextw_small by lia. step. step. step. step. step. release_frame FR ST (bv_unsigned sp).
    unfold rmunmap_post, munmap_ret, rg_errno. finish; exact I.
Qed.
End Sz1.
Lemma rmunmap_spec : ltac:(let t := eval cbv delta [rmunmap_spec__stmt] in rmunmap_spec__stmt in exact t).
Proof using MSECV TLSFACTS. intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m A L errv lo. ltac2:(SecDiet.SzSec.closeP 'rmunmap_spec__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.

Lemma rmprotect_args : forall A L, (A mod 4096 = 0)%Z -> (L mod 4096 = 0)%Z -> (0 <= A)%Z -> (0 <= L)%Z -> (A + L + 4096 <= 2^64)%Z ->
  Z_to_bv 64 (Z.land 18446744073709547520 (bv_unsigned (Z_to_bv 64 A))) = Z_to_bv 64 A
  /\ Z_to_bv 64 (bv_unsigned (Z_to_bv 64 (Z.land (bv_unsigned (Z_to_bv 64 (A + L + 4095))) 18446744073709547520))
                 - bv_unsigned (Z_to_bv 64 (Z.land 18446744073709547520 (bv_unsigned (Z_to_bv 64 A))))) = Z_to_bv 64 L.
Proof using MSECV TLSFACTS. pin_using (fun (MSECV TLSFACTS : unit) => tt). ceil_facts. msec_facts.
  intros A L HA HL A0 L0 B. rewrite (Z.land_comm 18446744073709547520).
  rewrite (unsigned_lit A), (unsigned_lit (A + L + 4095)) by lia. rewrite !land_m4096 by lia.
  assert (E1 : (A - A mod 4096 = A)%Z) by lia.
  assert (E2 : ((A + L + 4095) - (A + L + 4095) mod 4096 = A + L)%Z) by (Z.div_mod_to_equations; lia).
  rewrite E1, E2. rewrite !unsigned_lit by lia. split; [reflexivity|]. f_equal. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition rmprotect_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (A L : Z) (errv : word) (lo : Z) (m : word -> option byte) (a : range_ans) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (munmap_ret a) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom ssegs)
    /\ munch [(bv_unsigned sp - 32, bv_unsigned sp); (errno_addr tp, errno_addr tp + 4); (A, A + L)]%Z m m'
    /\ wmono ssegs m m' /\ mem_inv ssegs m'
    /\ stk ssegs m' lo (bv_unsigned sp)
    /\ rw_cells ssegs m' (errno_addr tp) [C4 (rg_errno a errv)]
    /\ rw_cells ssegs m' RPAGE_SIZE [C8 (Z_to_bv 64 4096)]
    /\ match a with
       | RgErr e => (1 <= e <= 4095)%Z /\ e = ENOMEM
       | RgDone true => rw_cells ssegs m' A [CB (Z.to_nat L) (repeat (Z_to_bv 8 0) (Z.to_nat L))]
       | RgDone false => True
       end.

Definition rmprotect_spec__stmt : Prop := forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
    (A L P : Z) (errv : word) (lo : Z),
  stk ssegs m lo (bv_unsigned sp) ->
  rw_cells ssegs m (errno_addr tp) [C4 errv] ->
  rw_cells ssegs m RPAGE_SIZE [C8 (Z_to_bv 64 4096)] ->
  mem_inv ssegs m ->
  a0 = Z_to_bv 64 A -> a1 = Z_to_bv 64 L -> a2 = Z_to_bv 64 P ->
  (A mod 4096 = 0)%Z -> (L mod 4096 = 0)%Z -> (0 < A)%Z -> (0 < L)%Z -> (A + L + 4096 <= 2^64)%Z -> (0 <= P < 2^64)%Z ->
  (lo <= bv_unsigned sp - 32)%Z ->
  (errno_addr tp + 4 <= bv_unsigned sp - 32 \/ bv_unsigned sp <= errno_addr tp)%Z ->
  (A + L <= lo \/ bv_unsigned sp <= A)%Z ->
  (A + L <= errno_addr tp \/ errno_addr tp + 4 <= A)%Z ->
  (A + L <= 0x10000 \/ 0x55000 <= A)%Z ->
  (0x55000 <= lo)%Z -> (errno_addr tp + 4 <= RPAGE_SIZE \/ RPAGE_SIZE + 8 <= errno_addr tp)%Z ->
  (164 <= bv_unsigned tp)%Z ->
  impl ssegs (at_node ssegs) (npeek ssegs) (enode (NMprotect A L P) (dec_mprotect A L))
       (epost (rmprotect_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc A L errv lo m))
       (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
           F (Z_to_bv 64 rmprotect_entry) fc None m (seg_rom ssegs)).
Section Sz3.
Variables ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m A L P errv lo : ltac2:(SecDiet.SzSec.tyM 'rmprotect_spec__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra).
Lemma rmprotect_spec__body : ltac2:(SecDiet.SzSec.bodyP 'rmprotect_spec__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
Proof using MSECV TLSFACTS. pin_using (fun (MSECV TLSFACTS : unit) => tt). ceil_facts. msec_facts.
  intros ST ERR PG MI -> -> -> AA LA A0 L0 AL PR LO SEP1 SEP2 SEP3 SEP4 SLO SEP5 TP.
  pose proof (munch_refl [(bv_unsigned sp - 32, bv_unsigned sp); (errno_addr tp, errno_addr tp + 4); (A, A + L)]%Z m) as MU.
  pose proof (wmono_refl ssegs m) as WM.
  unfold rmprotect_entry, RPAGE_SIZE in *. apply impl_enode.
  carve_frame 16%nat ST.
  step. step. step. step.
  do 7 step.
  destruct (rmprotect_args A L AA LA ltac:(lia) ltac:(lia) AL) as [E1 E2]. rewrite E2, E1.
  step. step_ecall.
  split. { at_node_solve. }
  intros rsp ans Hdec. pose proof (dec_mprotect_Some _ _ _ _ Hdec) as D.
  rewrite (mmap_len_aligned L LA) in D.
  destruct ans as [e|[|]].
  - pose proof (dec_mprotect_err_enomem _ _ _ _ Hdec) as HE. clear Hdec. destruct D as [-> He]. unfold efferr, eff0. sys_nret.
    step. call_sp sysret_spec; [exact ST | exact ERR | exact MI | lia | lia | lia | ]. rename PC into ST; rename POST into ERR.
    unfold sysret_val, sysret_errno in *. rewrite errno_of_errno_ret in * by lia.
    step. step. step. step. release_frame FR ST (bv_unsigned sp).
    unfold rmprotect_post, munmap_ret, rg_errno. finish; lia.
  - rewrite D.
    assert (ROF : forall x : word, (A <= bv_unsigned x < A + L)%Z -> ro_addr ssegs x = false) by (intros x Hx; apply ref_ro_addr_false; lia).
    sys_nret. lazymatch goal with H : mem_inv _ _ |- _ => rename H into MI end.
    step. call_sp sysret_spec; [exact ST | exact ERR | exact MI | lia | lia | lia | ]. rename PC into ST; rename POST into ERR.
    unfold sysret_val, sysret_errno in *. rewrite errno_of_lit in * by lia.
    step. try rewrite sextw_small by lia. step. step. step. release_frame FR ST (bv_unsigned sp).
    unfold rmprotect_post, munmap_ret, rg_errno. finish.
  - rewrite D. unfold eff0. sys_nret.
    step. call_sp sysret_spec; [exact ST | exact ERR | exact MI | lia | lia | lia | ]. rename PC into ST; rename POST into ERR.
    unfold sysret_val, sysret_errno in *. rewrite errno_of_lit in * by lia.
    step. try rewrite sextw_small by lia. step. step. step. release_frame FR ST (bv_unsigned sp).
    unfold rmprotect_post, munmap_ret, rg_errno. finish; exact I.
Qed.
End Sz3.
Lemma rmprotect_spec : ltac:(let t := eval cbv delta [rmprotect_spec__stmt] in rmprotect_spec__stmt in exact t).
Proof using MSECV TLSFACTS. intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m A L P errv lo. ltac2:(SecDiet.SzSec.closeP 'rmprotect_spec__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.

Lemma land_ones64 y : (0 <= y < 2^64)%Z -> Z.land y 18446744073709551615 = y.
Proof using MSECV TB. pin_using (fun (MSECV TB : unit) => tt). ceil_facts. msec_facts. intros. change 18446744073709551615%Z with (Z.ones 64). rewrite Z.land_ones by lia. apply Z.mod_small. lia. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition rmmap_anon_post (isnone : bool) (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (len : Z) (avoid : list (Z * Z)) (errv : word) (lo : Z) (m : word -> option byte) (a : mmap_ans)
    : machine_state -> Prop :=
  fun ms' =>
    match a with
    | MmErr e => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
        ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (-1)) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                 F (ret_pc ra) fc None m' (seg_rom ssegs)
        /\ munch [(bv_unsigned sp - 80, bv_unsigned sp); (errno_addr tp, errno_addr tp + 4)]%Z m m'
        /\ wmono ssegs m m' /\ mem_inv ssegs m'
        /\ stk ssegs m' lo (bv_unsigned sp)
        /\ rw_cells ssegs m' (errno_addr tp) [C4 (Z_to_bv 64 (mmap_fix_errno e))]
        /\ (1 <= e <= 4095)%Z /\ e = ENOMEM
    | MmOk x => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m2,
        ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 x) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                 F (ret_pc ra) fc None (mmap_raw isnone x len m2) (seg_rom ssegs)
        /\ munch [(bv_unsigned sp - 80, bv_unsigned sp)]%Z m m2
        /\ wmono ssegs m m2 /\ mem_inv ssegs m2
        /\ stk ssegs (mmap_raw isnone x len m2) lo (bv_unsigned sp)
        /\ rw_cells ssegs m2 (errno_addr tp) [C4 errv]
        /\ mmap_addr_ok len avoid x = true
    end.

Definition rmmap_anon_spec__stmt : Prop := forall (isnone : bool) ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
    (len : Z) (avoid : list (Z * Z)) (errv : word) (lo : Z),
  let prot := (if isnone then 0 else 3)%Z in
  stk ssegs m lo (bv_unsigned sp) ->
  rw_cells ssegs m (errno_addr tp) [C4 errv] ->
  mem_inv ssegs m ->
  a0 = Z_to_bv 64 0 -> a1 = Z_to_bv 64 len -> a2 = Z_to_bv 64 prot -> a3 = Z_to_bv 64 34 ->
  a4 = Z_to_bv 64 (-1) -> a5 = Z_to_bv 64 0 ->
  (0 < len <= 2^62)%Z ->
  (lo <= bv_unsigned sp - 80)%Z -> (alloc_ceiling <= lo)%Z ->
  (errno_addr tp + 4 <= bv_unsigned sp - 80 \/ bv_unsigned sp <= errno_addr tp)%Z ->
  (164 <= bv_unsigned tp)%Z ->
  impl ssegs (at_node ssegs) (npeek ssegs) (enode (NMmap 0 len prot 34) (if isnone then dec_mmap_none len avoid else dec_mmap len avoid))
       (epost (rmmap_anon_post isnone ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc len avoid errv lo m))
       (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
           F (Z_to_bv 64 rmmap_entry) fc None m (seg_rom ssegs)).
Section Sz4.
Variables isnone ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m len avoid errv lo : ltac2:(SecDiet.SzSec.tyM 'rmmap_anon_spec__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @isnone).
Lemma rmmap_anon_spec__body : ltac2:(SecDiet.SzSec.bodyP 'rmmap_anon_spec__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
Proof using MSECV TLSFACTS. pin_using (fun (MSECV TLSFACTS : unit) => tt). ceil_facts. msec_facts.
  intros prot ST ERR MI -> -> -> -> -> -> LEN LO CEIL SEP1 TP.
  pose proof (munch_refl [(bv_unsigned sp - 80, bv_unsigned sp); (errno_addr tp, errno_addr tp + 4)]%Z m) as MU.
  pose proof (munch_refl [(bv_unsigned sp - 80, bv_unsigned sp)]%Z m) as MU1.
  pose proof (wmono_refl ssegs m) as WM.
  ceil_facts.
  assert (PR : (0 <= prot < 4)%Z) by (destruct isnone; subst prot; lia). clearbody prot.
  unfold rmmap_entry. apply impl_enode.
  carve_frame 64%nat ST.
  do 8 step.
  step. step. if_cases K0; zify_cond K0. 2:{ exfalso. rewrite ?unsigned_lit in K0 by lia. lia. } clear K0.
  step. step. step. if_cases K1; zify_cond K1. 2:{ exfalso. rewrite ?unsigned_lit in K1 by lia. lia. } clear K1.
  step. step. if_cases K2; zify_cond K2. { exfalso. rewrite ?unsigned_lit in K2 by lia. lia. } clear K2.
  step. step.
  step. step. step_ecall.
  split. { at_node_solve. }
  intros rsp ans Hdec.
  assert (D : match ans with
              | MmErr e => (rsp = efferr e /\ (1 <= e <= 4095)%Z) /\ e = ENOMEM
              | MmOk a => rsp = (if isnone then mkEffectU (Z_to_bv 64 a) [] [] [(wa a, Z_to_bv 64 (mmap_len len))] [] []
                                 else mkEffect (Z_to_bv 64 a) [] [(wa a, Z_to_bv 64 (mmap_len len))])
                          /\ mmap_addr_ok len avoid a = true
              end).
  { destruct isnone; [pose proof (dec_mmap_none_Some _ _ _ _ Hdec) as D | pose proof (dec_mmap_Some _ _ _ _ Hdec) as D];
      destruct ans; try exact D; (split; [exact D|]); [exact (dec_mmap_none_err_enomem _ _ _ _ Hdec)| exact (dec_mmap_err_enomem _ _ _ _ Hdec)]. }
  clear Hdec. destruct ans as [e|x].
  - clear MU1. destruct D as [[-> He] HE]. unfold efferr, eff0. sys_nret.
    step. step. step.
    rewrite unsigned_errno_ret, zb_lxor_ones, Z.lor_0_l by lia.
    if_cases K; zify_cond K.
    + (* [comment removed for export] *)
      step. call_sp sysret_spec; [exact ST | exact ERR | exact MI | lia | lia | lia | ]. rename PC into ST; rename POST into ERR.
      unfold sysret_val, sysret_errno in *. rewrite errno_of_errno_ret in * by lia.
      do 10 step. release_frame FR ST (bv_unsigned sp).
      unfold rmmap_anon_post, mmap_fix_errno. replace (e =? 1)%Z with false by (symmetry; apply Z.eqb_neq; lia).
      finish; lia.
    + (* [comment removed for export] *)
      rewrite ?unsigned_lit in K by lia.
      step. step. step. step.
      replace (Z_to_bv 64 18446744073709551604) with (errno_ret 12) by (apply bv_eq; reflexivity).
      step. call_sp sysret_spec; [exact ST | exact ERR | exact MI | lia | lia | lia | ]. rename PC into ST; rename POST into ERR.
      unfold sysret_val, sysret_errno in *. rewrite errno_of_errno_ret in * by lia.
      do 10 step. release_frame FR ST (bv_unsigned sp).
      unfold rmmap_anon_post, mmap_fix_errno. replace (e =? 1)%Z with true by (symmetry; apply Z.eqb_eq; lia).
      finish; lia.
  - clear MU. destruct D as [-> Hok]. pose proof (mmap_addr_ok_true _ _ _ Hok) as ((XA & X0 & XC) & XAV).
    ceil_facts. pose proof (mmap_len_ge len) as ML.
    lazymatch goal with |- context [nret (MSsvc _ _ _ _ _ _ ?mc _) _] => rename mc into m2 end || idtac.
    destruct isnone; sys_nret_raw.
    all: lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
           set (m' := mm);
           assert (Hza : (0 <= x < 2^64)%Z) by lia; assert (Hzn : (0 <= mmap_len len < 2^64)%Z) by lia;
           assert (Hzan : (x + mmap_len len <= 2^64)%Z) by lia
         end.
    1: pose proof (rw_cells_unmaps_other ssegs _ x (mmap_len len) Hza Hzn Hzan _ _ FR ltac:(cbn; lia)) as FR';
       pose proof (stk_unmaps_other ssegs _ x (mmap_len len) Hza Hzn Hzan _ _ ST ltac:(lia)) as ST'.
    2: pose proof (rw_cells_zeros_other ssegs _ x (mmap_len len) Hza Hzn Hzan _ _ FR ltac:(cbn; lia)) as FR';
       pose proof (stk_zeros ssegs _ x (mmap_len len) Hza Hzn Hzan _ _ ST) as ST'.
    all: fold m' in FR', ST'; clear FR; rename ST into ST0.
    all: step; step; step.
    all: rewrite zb_lxor_ones, Z.lor_0_l by (rewrite ?unsigned_lit by lia; lia); rewrite ?unsigned_lit by lia.
    all: if_cases K; zify_cond K; rewrite ?land_ones64 in K by lia; [| exfalso; lia].
    (* [comment removed for export] *)
    all: step; step; step; step; if_cases K1; zify_cond K1; [| exfalso; rewrite ?unsigned_lit in K1 by lia; lia]; step.
    (* [comment removed for export] *)
    all: do 9 step; release_frame FR' ST' (bv_unsigned sp); step.
    all: apply evt_done; unfold rmmap_anon_post, mmap_raw; cbv iota.
    all: do 14 eexists; eexists; split; [subst m'; reflexivity|].
    all: split; [exact MU1|]; split; [exact WM|]; split; [exact MI|]; split; [exact ST'|]; split; [exact ERR| exact Hok].
Qed.
End Sz4.
Lemma rmmap_anon_spec : ltac:(let t := eval cbv delta [rmmap_anon_spec__stmt] in rmmap_anon_spec__stmt in exact t).
Proof using MSECV TLSFACTS. intros isnone ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m len avoid errv lo. ltac2:(SecDiet.SzSec.closeP 'rmmap_anon_spec__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition rmmap_fixed_post {X} (R : X -> word -> bool -> Prop)
    (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (A L : Z) (errv : word) (lo : Z) (m : word -> option byte) (a : X) : machine_state -> Prop :=
  fun ms' => exists (r : word) (u : bool) t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    R a r u /\
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (sysret_val r) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom ssegs)
    /\ munch [(bv_unsigned sp - 80, bv_unsigned sp); (errno_addr tp, errno_addr tp + 4); (A, A + mmap_len L)]%Z m m'
    /\ (u = false -> wmono ssegs m m')
    /\ mem_inv ssegs m'
    /\ stk ssegs m' lo (bv_unsigned sp)
    /\ rw_cells ssegs m' (errno_addr tp) [C4 (sysret_errno r errv)].

Lemma rmmap_fixed_spec : forall {X} (dec : resp -> option X) (R : X -> word -> bool -> Prop)
    ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
    (A L P : Z) (errv : word) (lo : Z),
  (forall rsp a, dec rsp = Some a -> exists r u, R a r u /\ rsp = fixed_shape A L r u) ->
  stk ssegs m lo (bv_unsigned sp) ->
  rw_cells ssegs m (errno_addr tp) [C4 errv] ->
  mem_inv ssegs m ->
  a0 = Z_to_bv 64 A -> a1 = Z_to_bv 64 L -> a2 = Z_to_bv 64 P -> a3 = Z_to_bv 64 50 ->
  a4 = Z_to_bv 64 (-1) -> a5 = Z_to_bv 64 0 ->
  (0 < A)%Z -> (0 < L <= 2^62)%Z -> (A + mmap_len L < 2^64)%Z -> (0 <= P < 4)%Z ->
  (lo <= bv_unsigned sp - 80)%Z ->
  (errno_addr tp + 4 <= bv_unsigned sp - 80 \/ bv_unsigned sp <= errno_addr tp)%Z ->
  (A + mmap_len L <= lo \/ bv_unsigned sp <= A)%Z ->
  (A + mmap_len L <= errno_addr tp \/ errno_addr tp + 4 <= A)%Z ->
  (164 <= bv_unsigned tp)%Z ->
  impl ssegs (at_node ssegs) (npeek ssegs) (enode (NMmap A L P 50) dec)
       (epost (rmmap_fixed_post R ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc A L errv lo m))
       (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
           F (Z_to_bv 64 rmmap_entry) fc None m (seg_rom ssegs)).
Proof using MSECV TLSFACTS. pin_using (fun (MSECV TLSFACTS : unit) => tt). ceil_facts. msec_facts.
  intros until lo. intros DEC ST ERR MI -> -> -> -> -> -> A0 LEN AL PR LO SEP1 SEP2 SEP3 TP.
  pose proof (munch_refl [(bv_unsigned sp - 80, bv_unsigned sp); (errno_addr tp, errno_addr tp + 4); (A, A + mmap_len L)]%Z m) as MU.
  pose proof (wmono_refl ssegs m) as WM.
  pose proof (mmap_len_ge L) as ML.
  unfold rmmap_entry. apply impl_enode.
  carve_frame 64%nat ST.
  do 8 step.
  step. step. if_cases K0; zify_cond K0. 2:{ exfalso. rewrite ?unsigned_lit in K0 by lia. lia. } clear K0.
  step. step. step. if_cases K1; zify_cond K1. 2:{ exfalso. rewrite ?unsigned_lit in K1 by lia. lia. } clear K1.
  step. step. if_cases K2; zify_cond K2. 2:{ exfalso. rewrite ?unsigned_lit in K2 by lia. lia. } clear K2.
  (* [comment removed for export] *)
  set (z0 := Z_to_bv 64 0). set (zm1 := Z_to_bv 64 (-1)). set (z50 := Z_to_bv 64 50).
  set (zA := Z_to_bv 64 A). set (zL := Z_to_bv 64 L). set (zP := Z_to_bv 64 P).
  do 6 step. step. step. do 6 step. step.
  subst z0 zm1 z50 zA zL zP.
  step. step. step_ecall.
  split. { at_node_solve. }
  intros rsp ans Hdec. destruct (DEC rsp ans Hdec) as (r & u & HR & ->). clear Hdec.
  pose proof (bv_unsigned_in_range 64 r) as RR. change (bv_modulus 64) with (2^64)%Z in RR.
  destruct u; unfold fixed_shape; cbv iota.
  all: sys_nret.
  all: step; step; step.
  all: if_cases K; zify_cond K; [| exfalso; apply Z.lor_eq_0_iff in K; lia ].
  all: step; call_sp sysret_spec; [exact ST | exact ERR | exact MI | lia | lia | lia |]; rename PC into ST; rename POST into ERR.
  all: do 10 step; release_frame FR ST (bv_unsigned sp).
  all: unfold rmmap_fixed_post; apply evt_done; exists r; eexists; do 15 eexists; split; [exact HR|]; split; [reflexivity|].
  all: split; [ eapply munch_weaken; [|exact MU]; intros y; cbn; lia |].
  all: split; [ first [intros; discriminate | intros _; assumption] |].
  all: split; [lazymatch goal with H : mem_inv ssegs ?mm |- mem_inv ssegs ?mm => exact H end|].
  all: split; [lazymatch goal with H : stk ssegs ?mm ?a ?b |- stk ssegs ?mm _ _ => exact H end|].
  all: lazymatch goal with H : rw_cells ssegs ?mm ?a ?c |- rw_cells ssegs ?mm _ _ => exact H end.
Qed.

End PORT.

End WithCeil.

(* [comment removed for export] *)
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require ImgTgtUbsan.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require TlsBaseU.
Module TwB.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.AllocBridge__Spec.AllocBridge.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.TlsBaseU.
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Tac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ITree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Nodes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.SysStep OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Decode.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ImgTgtUbsan.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.F_mm_syscalls.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_lock__S3.F_syscalls.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RMallocRep__S3.RMallocRep.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MSecret.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.LiaPin.
(* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac lia ::= pinned_lia.
Import ListNotations.
Open Scope bv_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
(* [comment removed for export] *)
Section WithCeil.
Context {CEILV : CEIL} {MSECV : MSEC}.
Section PORT.
Context {PState : Type} {AS : AllocSt PState} {TB : TlsBase}.
Let TLSFACTS := the_tb_facts (TB:=TB).

Local Unset Keyed Unification.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma dec_mmap_err_enomem len avoid rsp e : dec_mmap len avoid rsp = Some (MmErr e) -> e = ENOMEM.
Proof using MSECV. pin_using (fun (MSECV : unit) => tt). ceil_facts. msec_facts.
  unfold dec_mmap. destruct (core rsp) as [[[[r ws] zs] us]|]; [|discriminate].
  destruct ws; [|discriminate]. destruct zs as [|[a n] [|? ?]]; destruct us; try discriminate.
  - destruct (mm_errno_of r) eqn:E; [|discriminate]. intros H. inversion H; subst. exact (proj2 (mm_errno_of_Some _ _ E)).
  - destruct (bv_eqb a r && bv_eqb n _ && mmap_addr_ok len avoid (bv_unsigned r)); discriminate.
Qed.
Lemma dec_mmap_none_err_enomem len avoid rsp e : dec_mmap_none len avoid rsp = Some (MmErr e) -> e = ENOMEM.
Proof using MSECV. pin_using (fun (MSECV : unit) => tt). ceil_facts. msec_facts.
  unfold dec_mmap_none. destruct (core rsp) as [[[[r ws] zs] us]|]; [|discriminate].
  destruct ws; [|discriminate]. destruct zs; [|discriminate]. destruct us as [|[a n] [|? ?]]; try discriminate.
  - destruct (mm_errno_of r) eqn:E; [|discriminate]. intros H. inversion H; subst. exact (proj2 (mm_errno_of_Some _ _ E)).
  - destruct (bv_eqb a r && bv_eqb n _ && mmap_addr_ok len avoid (bv_unsigned r)); discriminate.
Qed.
Lemma dec_munmap_err_enomem A L rsp e : dec_munmap A L rsp = Some (RgErr e) -> e = ENOMEM.
Proof using CEILV MSECV. pin_using (fun (CEILV MSECV : unit) => tt). ceil_facts. msec_facts.
  unfold dec_munmap. destruct (core rsp) as [[[[r ws] zs] us]|]; [|discriminate].
  destruct ws; [|discriminate]. destruct zs; [|discriminate]. destruct us as [|[a n] [|? ?]]; try discriminate.
  - destruct (mm_errno_of r) eqn:E. { intros H. inversion H; subst. exact (proj2 (mm_errno_of_Some _ _ E)). }
    destruct (bv_unsigned r =? 0)%Z; [|discriminate]. intros H; inversion H.
  - destruct ((bv_unsigned r =? 0)%Z && bv_eqb a _ && bv_eqb n _); [|discriminate]. intros H; inversion H.
Qed.
Lemma dec_mprotect_err_enomem A L rsp e : dec_mprotect A L rsp = Some (RgErr e) -> e = ENOMEM.
Proof using CEILV MSECV. pin_using (fun (CEILV MSECV : unit) => tt). ceil_facts. msec_facts.
  unfold dec_mprotect. destruct (core rsp) as [[[[r ws] zs] us]|]; [|discriminate].
  destruct ws; [|discriminate]. destruct zs as [|[a n] [|? ?]]; destruct us; try discriminate.
  - destruct (mm_errno_of r) eqn:E. { intros H. inversion H; subst. exact (proj2 (mm_errno_of_Some _ _ E)). }
    destruct (bv_unsigned r =? 0)%Z; [|discriminate]. intros H; inversion H.
  - destruct ((bv_unsigned r =? 0)%Z && bv_eqb a _ && bv_eqb n _); [|discriminate]. intros H; inversion H.
Qed.

(* [comment removed for export] *)
Lemma rg_err_range (P : Z -> Prop) (a : range_ans) :
  match a with RgErr e => (1 <= e <= 4095)%Z /\ P e | RgDone _ => True end ->
  match a with RgErr e => (1 <= e <= 4095)%Z | RgDone _ => True end.
Proof using MSECV TLSFACTS. pin_using (fun (MSECV TLSFACTS : unit) => tt). ceil_facts. msec_facts. destruct a; tauto. Qed.

Definition rmunmap_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (A L : Z) (errv : word) (lo : Z) (m : word -> option byte) (a : range_ans) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (munmap_ret a) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom usegs)
    /\ munch [(bv_unsigned sp - 48, bv_unsigned sp); (errno_addr tp, errno_addr tp + 4); (A, A + mmap_len L)]%Z m m'
    /\ (match a with RgDone true => True | _ => wmono usegs m m' end)
    /\ mem_inv usegs m'
    /\ stk usegs m' lo (bv_unsigned sp)
    /\ rw_cells usegs m' (errno_addr tp) [C4 (rg_errno a errv)]
    /\ match a with RgErr e => (1 <= e <= 4095)%Z /\ e = ENOMEM | _ => True end.

Definition rmunmap_spec__stmt : Prop := forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
    (A L : Z) (errv : word) (lo : Z),
  stk usegs m lo (bv_unsigned sp) ->
  rw_cells usegs m (errno_addr tp) [C4 errv] ->
  mem_inv usegs m ->
  a0 = Z_to_bv 64 A -> a1 = Z_to_bv 64 L ->
  (0 < A)%Z -> (A + mmap_len L <= 2^64)%Z -> (0 < L < 2^64)%Z ->
  (lo <= bv_unsigned sp - 48)%Z ->
  (errno_addr tp + 4 <= bv_unsigned sp - 48 \/ bv_unsigned sp <= errno_addr tp)%Z ->
  (A + mmap_len L <= lo \/ bv_unsigned sp <= A)%Z ->
  (A + mmap_len L <= errno_addr tp \/ errno_addr tp + 4 <= A)%Z ->
  (164 <= bv_unsigned tp)%Z ->
  impl usegs (at_node usegs) (npeek usegs) (enode (NMunmap A L) (dec_munmap A L))
       (epost (rmunmap_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc A L errv lo m))
       (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
           F (Z_to_bv 64 rmunmap_entry) fc None m (seg_rom usegs)).
Section Sz1.
Variables ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m A L errv lo : ltac2:(SecDiet.SzSec.tyM 'rmunmap_spec__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra).
Lemma rmunmap_spec__body : ltac2:(SecDiet.SzSec.bodyP 'rmunmap_spec__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
Proof using MSECV TLSFACTS. pin_using (fun (MSECV TLSFACTS : unit) => tt). ceil_facts. msec_facts.
 intros ST ERR MI -> -> A0 AL L0 LO SEP1 SEP2 SEP3 TP.
  pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp); (errno_addr tp, errno_addr tp + 4); (A, A + mmap_len L)]%Z m) as MU.
  pose proof (wmono_refl usegs m) as WM.
  pose proof (mmap_len_ge L) as ML.
  unfold rmunmap_entry. apply impl_enode.
  carve_frame 32%nat ST.
  do 6 step. (* [comment removed for export] *)
  step. step. (* [comment removed for export] *)
  do 3 step. (* [comment removed for export] *)
  step_ecall.
  split. { at_node_solve. }
  intros rsp ans Hdec. pose proof (dec_munmap_Some _ _ _ _ Hdec) as D.
  destruct ans as [e|[|]].
  - pose proof (dec_munmap_err_enomem _ _ _ _ Hdec) as HE. clear Hdec. destruct D as [-> He]. unfold efferr, eff0. sys_nret.
    step. call_sp sysret_spec; [exact ST | exact ERR | exact MI | lia | lia | lia | ]. rename PC into ST; rename POST into ERR.
    unfold sysret_val, sysret_errno in *. rewrite errno_of_errno_ret in * by lia.
    step. step. step. step. step. step. release_frame FR ST (bv_unsigned sp).
    unfold rmunmap_post, munmap_ret, rg_errno. finish; lia.
  - rewrite D. sys_nret.
    step. call_sp sysret_spec; [exact ST | exact ERR | exact MI | lia | lia | lia | ]. rename PC into ST; rename POST into ERR.
    unfold sysret_val, sysret_errno in *. rewrite errno_of_lit in * by lia.
    step. try rewrite sextw_small by lia. step. step. step. step. step. release_frame FR ST (bv_unsigned sp).
    unfold rmunmap_post, munmap_ret, rg_errno. finish; exact I.
  - rewrite D. unfold eff0. sys_nret.
    step. call_sp sysret_spec; [exact ST | exact ERR | exact MI | lia | lia | lia | ]. rename PC into ST; rename POST into ERR.
    unfold sysret_val, sysret_errno in *. rewrite errno_of_lit in * by lia.
    step. try rewrite sextw_small by lia. step. step. step. step. step. release_frame FR ST (bv_unsigned sp).
    unfold rmunmap_post, munmap_ret, rg_errno. finish; exact I.
Qed.
End Sz1.
Lemma rmunmap_spec : ltac:(let t := eval cbv delta [rmunmap_spec__stmt] in rmunmap_spec__stmt in exact t).
Proof using MSECV TLSFACTS. intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m A L errv lo. ltac2:(SecDiet.SzSec.closeP 'rmunmap_spec__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.

Lemma rmprotect_args : forall A L, (A mod 4096 = 0)%Z -> (L mod 4096 = 0)%Z -> (0 <= A)%Z -> (0 <= L)%Z -> (A + L + 4096 <= 2^64)%Z ->
  Z_to_bv 64 (Z.land 18446744073709547520 (bv_unsigned (Z_to_bv 64 A))) = Z_to_bv 64 A
  /\ Z_to_bv 64 (bv_unsigned (Z_to_bv 64 (Z.land (bv_unsigned (Z_to_bv 64 (A + L + 4095))) 18446744073709547520))
                 - bv_unsigned (Z_to_bv 64 (Z.land 18446744073709547520 (bv_unsigned (Z_to_bv 64 A))))) = Z_to_bv 64 L.
Proof using MSECV TLSFACTS. pin_using (fun (MSECV TLSFACTS : unit) => tt). ceil_facts. msec_facts.
  intros A L HA HL A0 L0 B. rewrite (Z.land_comm 18446744073709547520).
  rewrite (unsigned_lit A), (unsigned_lit (A + L + 4095)) by lia. rewrite !land_m4096 by lia.
  assert (E1 : (A - A mod 4096 = A)%Z) by lia.
  assert (E2 : ((A + L + 4095) - (A + L + 4095) mod 4096 = A + L)%Z) by (Z.div_mod_to_equations; lia).
  rewrite E1, E2. rewrite !unsigned_lit by lia. split; [reflexivity|]. f_equal. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition rmprotect_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (A L : Z) (errv : word) (lo : Z) (m : word -> option byte) (a : range_ans) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (munmap_ret a) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom usegs)
    /\ munch [(bv_unsigned sp - 32, bv_unsigned sp); (errno_addr tp, errno_addr tp + 4); (A, A + L)]%Z m m'
    /\ wmono usegs m m' /\ mem_inv usegs m'
    /\ stk usegs m' lo (bv_unsigned sp)
    /\ rw_cells usegs m' (errno_addr tp) [C4 (rg_errno a errv)]
    /\ rw_cells usegs m' RPAGE_SIZE [C8 (Z_to_bv 64 4096)]
    /\ match a with
       | RgErr e => (1 <= e <= 4095)%Z /\ e = ENOMEM
       | RgDone true => rw_cells usegs m' A [CB (Z.to_nat L) (repeat (Z_to_bv 8 0) (Z.to_nat L))]
       | RgDone false => True
       end.

Definition rmprotect_spec__stmt : Prop := forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
    (A L P : Z) (errv : word) (lo : Z),
  stk usegs m lo (bv_unsigned sp) ->
  rw_cells usegs m (errno_addr tp) [C4 errv] ->
  rw_cells usegs m RPAGE_SIZE [C8 (Z_to_bv 64 4096)] ->
  mem_inv usegs m ->
  a0 = Z_to_bv 64 A -> a1 = Z_to_bv 64 L -> a2 = Z_to_bv 64 P ->
  (A mod 4096 = 0)%Z -> (L mod 4096 = 0)%Z -> (0 < A)%Z -> (0 < L)%Z -> (A + L + 4096 <= 2^64)%Z -> (0 <= P < 2^64)%Z ->
  (lo <= bv_unsigned sp - 32)%Z ->
  (errno_addr tp + 4 <= bv_unsigned sp - 32 \/ bv_unsigned sp <= errno_addr tp)%Z ->
  (A + L <= lo \/ bv_unsigned sp <= A)%Z ->
  (A + L <= errno_addr tp \/ errno_addr tp + 4 <= A)%Z ->
  (A + L <= 0x10000 \/ 0x56000 <= A)%Z ->
  (0x56000 <= lo)%Z -> (errno_addr tp + 4 <= RPAGE_SIZE \/ RPAGE_SIZE + 8 <= errno_addr tp)%Z ->
  (164 <= bv_unsigned tp)%Z ->
  impl usegs (at_node usegs) (npeek usegs) (enode (NMprotect A L P) (dec_mprotect A L))
       (epost (rmprotect_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc A L errv lo m))
       (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
           F (Z_to_bv 64 rmprotect_entry) fc None m (seg_rom usegs)).
Section Sz3.
Variables ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m A L P errv lo : ltac2:(SecDiet.SzSec.tyM 'rmprotect_spec__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra).
Lemma rmprotect_spec__body : ltac2:(SecDiet.SzSec.bodyP 'rmprotect_spec__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
Proof using MSECV TLSFACTS. pin_using (fun (MSECV TLSFACTS : unit) => tt). ceil_facts. msec_facts.
 intros ST ERR PG MI -> -> -> AA LA A0 L0 AL PR LO SEP1 SEP2 SEP3 SEP4 SLO SEP5 TP.
  pose proof (munch_refl [(bv_unsigned sp - 32, bv_unsigned sp); (errno_addr tp, errno_addr tp + 4); (A, A + L)]%Z m) as MU.
  pose proof (wmono_refl usegs m) as WM.
  unfold rmprotect_entry, RPAGE_SIZE in *. apply impl_enode.
  carve_frame 16%nat ST.
  step. step. step. step.
  do 7 step.
  destruct (rmprotect_args A L AA LA ltac:(lia) ltac:(lia) AL) as [E1 E2]. rewrite E2, E1.
  step. step_ecall.
  split. { at_node_solve. }
  intros rsp ans Hdec. pose proof (dec_mprotect_Some _ _ _ _ Hdec) as D.
  rewrite (mmap_len_aligned L LA) in D.
  destruct ans as [e|[|]].
  - pose proof (dec_mprotect_err_enomem _ _ _ _ Hdec) as HE. clear Hdec. destruct D as [-> He]. unfold efferr, eff0. sys_nret.
    step. call_sp sysret_spec; [exact ST | exact ERR | exact MI | lia | lia | lia | ]. rename PC into ST; rename POST into ERR.
    unfold sysret_val, sysret_errno in *. rewrite errno_of_errno_ret in * by lia.
    step. step. step. step. release_frame FR ST (bv_unsigned sp).
    unfold rmprotect_post, munmap_ret, rg_errno. finish; lia.
  - rewrite D.
    assert (ROF : forall x : word, (A <= bv_unsigned x < A + L)%Z -> ro_addr usegs x = false) by (intros x Hx; apply ref_ro_addr_false; lia).
    sys_nret. lazymatch goal with H : mem_inv _ _ |- _ => rename H into MI end.
    step. call_sp sysret_spec; [exact ST | exact ERR | exact MI | lia | lia | lia | ]. rename PC into ST; rename POST into ERR.
    unfold sysret_val, sysret_errno in *. rewrite errno_of_lit in * by lia.
    step. try rewrite sextw_small by lia. step. step. step. release_frame FR ST (bv_unsigned sp).
    unfold rmprotect_post, munmap_ret, rg_errno. finish.
  - rewrite D. unfold eff0. sys_nret.
    step. call_sp sysret_spec; [exact ST | exact ERR | exact MI | lia | lia | lia | ]. rename PC into ST; rename POST into ERR.
    unfold sysret_val, sysret_errno in *. rewrite errno_of_lit in * by lia.
    step. try rewrite sextw_small by lia. step. step. step. release_frame FR ST (bv_unsigned sp).
    unfold rmprotect_post, munmap_ret, rg_errno. finish; exact I.
Qed.
End Sz3.
Lemma rmprotect_spec : ltac:(let t := eval cbv delta [rmprotect_spec__stmt] in rmprotect_spec__stmt in exact t).
Proof using MSECV TLSFACTS. intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m A L P errv lo. ltac2:(SecDiet.SzSec.closeP 'rmprotect_spec__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.

Lemma land_ones64 y : (0 <= y < 2^64)%Z -> Z.land y 18446744073709551615 = y.
Proof using MSECV TB. pin_using (fun (MSECV TB : unit) => tt). ceil_facts. msec_facts. intros. change 18446744073709551615%Z with (Z.ones 64). rewrite Z.land_ones by lia. apply Z.mod_small. lia. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition rmmap_anon_post (isnone : bool) (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (len : Z) (avoid : list (Z * Z)) (errv : word) (lo : Z) (m : word -> option byte) (a : mmap_ans)
    : machine_state -> Prop :=
  fun ms' =>
    match a with
    | MmErr e => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
        ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (-1)) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                 F (ret_pc ra) fc None m' (seg_rom usegs)
        /\ munch [(bv_unsigned sp - 80, bv_unsigned sp); (errno_addr tp, errno_addr tp + 4)]%Z m m'
        /\ wmono usegs m m' /\ mem_inv usegs m'
        /\ stk usegs m' lo (bv_unsigned sp)
        /\ rw_cells usegs m' (errno_addr tp) [C4 (Z_to_bv 64 (mmap_fix_errno e))]
        /\ (1 <= e <= 4095)%Z /\ e = ENOMEM
    | MmOk x => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m2,
        ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 x) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                 F (ret_pc ra) fc None (mmap_raw isnone x len m2) (seg_rom usegs)
        /\ munch [(bv_unsigned sp - 80, bv_unsigned sp)]%Z m m2
        /\ wmono usegs m m2 /\ mem_inv usegs m2
        /\ stk usegs (mmap_raw isnone x len m2) lo (bv_unsigned sp)
        /\ rw_cells usegs m2 (errno_addr tp) [C4 errv]
        /\ mmap_addr_ok len avoid x = true
    end.

Definition rmmap_anon_spec__stmt : Prop := forall (isnone : bool) ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
    (len : Z) (avoid : list (Z * Z)) (errv : word) (lo : Z),
  let prot := (if isnone then 0 else 3)%Z in
  stk usegs m lo (bv_unsigned sp) ->
  rw_cells usegs m (errno_addr tp) [C4 errv] ->
  mem_inv usegs m ->
  a0 = Z_to_bv 64 0 -> a1 = Z_to_bv 64 len -> a2 = Z_to_bv 64 prot -> a3 = Z_to_bv 64 34 ->
  a4 = Z_to_bv 64 (-1) -> a5 = Z_to_bv 64 0 ->
  (0 < len <= 2^62)%Z ->
  (lo <= bv_unsigned sp - 80)%Z -> (alloc_ceiling <= lo)%Z ->
  (errno_addr tp + 4 <= bv_unsigned sp - 80 \/ bv_unsigned sp <= errno_addr tp)%Z ->
  (164 <= bv_unsigned tp)%Z ->
  impl usegs (at_node usegs) (npeek usegs) (enode (NMmap 0 len prot 34) (if isnone then dec_mmap_none len avoid else dec_mmap len avoid))
       (epost (rmmap_anon_post isnone ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc len avoid errv lo m))
       (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
           F (Z_to_bv 64 rmmap_entry) fc None m (seg_rom usegs)).
Section Sz4.
Variables isnone ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m len avoid errv lo : ltac2:(SecDiet.SzSec.tyM 'rmmap_anon_spec__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @isnone).
Lemma rmmap_anon_spec__body : ltac2:(SecDiet.SzSec.bodyP 'rmmap_anon_spec__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
Proof using MSECV TLSFACTS. pin_using (fun (MSECV TLSFACTS : unit) => tt). ceil_facts. msec_facts.
 intros prot ST ERR MI -> -> -> -> -> -> LEN LO CEIL SEP1 TP.
  pose proof (munch_refl [(bv_unsigned sp - 80, bv_unsigned sp); (errno_addr tp, errno_addr tp + 4)]%Z m) as MU.
  pose proof (munch_refl [(bv_unsigned sp - 80, bv_unsigned sp)]%Z m) as MU1.
  pose proof (wmono_refl usegs m) as WM.
  ceil_facts.
  assert (PR : (0 <= prot < 4)%Z) by (destruct isnone; subst prot; lia). clearbody prot.
  unfold rmmap_entry. apply impl_enode.
  carve_frame 64%nat ST.
  do 8 step.
  step. step. if_cases K0; zify_cond K0. 2:{ exfalso. rewrite ?unsigned_lit in K0 by lia. lia. } clear K0.
  step. step. step. if_cases K1; zify_cond K1. 2:{ exfalso. rewrite ?unsigned_lit in K1 by lia. lia. } clear K1.
  step. step. if_cases K2; zify_cond K2. { exfalso. rewrite ?unsigned_lit in K2 by lia. lia. } clear K2.
  step. step.
  step. step. step_ecall.
  split. { at_node_solve. }
  intros rsp ans Hdec.
  assert (D : match ans with
              | MmErr e => (rsp = efferr e /\ (1 <= e <= 4095)%Z) /\ e = ENOMEM
              | MmOk a => rsp = (if isnone then mkEffectU (Z_to_bv 64 a) [] [] [(wa a, Z_to_bv 64 (mmap_len len))] [] []
                                 else mkEffect (Z_to_bv 64 a) [] [(wa a, Z_to_bv 64 (mmap_len len))])
                          /\ mmap_addr_ok len avoid a = true
              end).
  { destruct isnone; [pose proof (dec_mmap_none_Some _ _ _ _ Hdec) as D | pose proof (dec_mmap_Some _ _ _ _ Hdec) as D];
      destruct ans; try exact D; (split; [exact D|]); [exact (dec_mmap_none_err_enomem _ _ _ _ Hdec)| exact (dec_mmap_err_enomem _ _ _ _ Hdec)]. }
  clear Hdec. destruct ans as [e|x].
  - clear MU1. destruct D as [[-> He] HE]. unfold efferr, eff0. sys_nret.
    step. step. step.
    rewrite unsigned_errno_ret, zb_lxor_ones, Z.lor_0_l by lia.
    if_cases K; zify_cond K.
    + (* [comment removed for export] *)
      step. call_sp sysret_spec; [exact ST | exact ERR | exact MI | lia | lia | lia | ]. rename PC into ST; rename POST into ERR.
      unfold sysret_val, sysret_errno in *. rewrite errno_of_errno_ret in * by lia.
      do 10 step. release_frame FR ST (bv_unsigned sp).
      unfold rmmap_anon_post, mmap_fix_errno. replace (e =? 1)%Z with false by (symmetry; apply Z.eqb_neq; lia).
      finish; lia.
    + (* [comment removed for export] *)
      rewrite ?unsigned_lit in K by lia.
      step. step. step. step.
      replace (Z_to_bv 64 18446744073709551604) with (errno_ret 12) by (apply bv_eq; reflexivity).
      step. call_sp sysret_spec; [exact ST | exact ERR | exact MI | lia | lia | lia | ]. rename PC into ST; rename POST into ERR.
      unfold sysret_val, sysret_errno in *. rewrite errno_of_errno_ret in * by lia.
      do 10 step. release_frame FR ST (bv_unsigned sp).
      unfold rmmap_anon_post, mmap_fix_errno. replace (e =? 1)%Z with true by (symmetry; apply Z.eqb_eq; lia).
      finish; lia.
  - clear MU. destruct D as [-> Hok]. pose proof (mmap_addr_ok_true _ _ _ Hok) as ((XA & X0 & XC) & XAV).
    ceil_facts. pose proof (mmap_len_ge len) as ML.
    lazymatch goal with |- context [nret (MSsvc _ _ _ _ _ _ ?mc _) _] => rename mc into m2 end || idtac.
    destruct isnone; sys_nret_raw.
    all: lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
           set (m' := mm);
           assert (Hza : (0 <= x < 2^64)%Z) by lia; assert (Hzn : (0 <= mmap_len len < 2^64)%Z) by lia;
           assert (Hzan : (x + mmap_len len <= 2^64)%Z) by lia
         end.
    1: pose proof (rw_cells_unmaps_other usegs _ x (mmap_len len) Hza Hzn Hzan _ _ FR ltac:(cbn; lia)) as FR';
       pose proof (stk_unmaps_other usegs _ x (mmap_len len) Hza Hzn Hzan _ _ ST ltac:(lia)) as ST'.
    2: pose proof (rw_cells_zeros_other usegs _ x (mmap_len len) Hza Hzn Hzan _ _ FR ltac:(cbn; lia)) as FR';
       pose proof (stk_zeros usegs _ x (mmap_len len) Hza Hzn Hzan _ _ ST) as ST'.
    all: fold m' in FR', ST'; clear FR; rename ST into ST0.
    all: step; step; step.
    all: rewrite zb_lxor_ones, Z.lor_0_l by (rewrite ?unsigned_lit by lia; lia); rewrite ?unsigned_lit by lia.
    all: if_cases K; zify_cond K; rewrite ?land_ones64 in K by lia; [| exfalso; lia].
    (* [comment removed for export] *)
    all: step; step; step; step; if_cases K1; zify_cond K1; [| exfalso; rewrite ?unsigned_lit in K1 by lia; lia]; step.
    (* [comment removed for export] *)
    all: do 9 step; release_frame FR' ST' (bv_unsigned sp); step.
    all: apply evt_done; unfold rmmap_anon_post, mmap_raw; cbv iota.
    all: do 14 eexists; eexists; split; [subst m'; reflexivity|].
    all: split; [exact MU1|]; split; [exact WM|]; split; [exact MI|]; split; [exact ST'|]; split; [exact ERR| exact Hok].
Qed.
End Sz4.
Lemma rmmap_anon_spec : ltac:(let t := eval cbv delta [rmmap_anon_spec__stmt] in rmmap_anon_spec__stmt in exact t).
Proof using MSECV TLSFACTS. intros isnone ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m len avoid errv lo. ltac2:(SecDiet.SzSec.closeP 'rmmap_anon_spec__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition rmmap_fixed_post {X} (R : X -> word -> bool -> Prop)
    (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (A L : Z) (errv : word) (lo : Z) (m : word -> option byte) (a : X) : machine_state -> Prop :=
  fun ms' => exists (r : word) (u : bool) t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    R a r u /\
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (sysret_val r) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom usegs)
    /\ munch [(bv_unsigned sp - 80, bv_unsigned sp); (errno_addr tp, errno_addr tp + 4); (A, A + mmap_len L)]%Z m m'
    /\ (u = false -> wmono usegs m m')
    /\ mem_inv usegs m'
    /\ stk usegs m' lo (bv_unsigned sp)
    /\ rw_cells usegs m' (errno_addr tp) [C4 (sysret_errno r errv)].

Lemma rmmap_fixed_spec : forall {X} (dec : resp -> option X) (R : X -> word -> bool -> Prop)
    ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
    (A L P : Z) (errv : word) (lo : Z),
  (forall rsp a, dec rsp = Some a -> exists r u, R a r u /\ rsp = fixed_shape A L r u) ->
  stk usegs m lo (bv_unsigned sp) ->
  rw_cells usegs m (errno_addr tp) [C4 errv] ->
  mem_inv usegs m ->
  a0 = Z_to_bv 64 A -> a1 = Z_to_bv 64 L -> a2 = Z_to_bv 64 P -> a3 = Z_to_bv 64 50 ->
  a4 = Z_to_bv 64 (-1) -> a5 = Z_to_bv 64 0 ->
  (0 < A)%Z -> (0 < L <= 2^62)%Z -> (A + mmap_len L < 2^64)%Z -> (0 <= P < 4)%Z ->
  (lo <= bv_unsigned sp - 80)%Z ->
  (errno_addr tp + 4 <= bv_unsigned sp - 80 \/ bv_unsigned sp <= errno_addr tp)%Z ->
  (A + mmap_len L <= lo \/ bv_unsigned sp <= A)%Z ->
  (A + mmap_len L <= errno_addr tp \/ errno_addr tp + 4 <= A)%Z ->
  (164 <= bv_unsigned tp)%Z ->
  impl usegs (at_node usegs) (npeek usegs) (enode (NMmap A L P 50) dec)
       (epost (rmmap_fixed_post R ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc A L errv lo m))
       (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
           F (Z_to_bv 64 rmmap_entry) fc None m (seg_rom usegs)).
Proof using MSECV TLSFACTS. pin_using (fun (MSECV TLSFACTS : unit) => tt). ceil_facts. msec_facts.
  intros until lo. intros DEC ST ERR MI -> -> -> -> -> -> A0 LEN AL PR LO SEP1 SEP2 SEP3 TP.
  pose proof (munch_refl [(bv_unsigned sp - 80, bv_unsigned sp); (errno_addr tp, errno_addr tp + 4); (A, A + mmap_len L)]%Z m) as MU.
  pose proof (wmono_refl usegs m) as WM.
  pose proof (mmap_len_ge L) as ML.
  unfold rmmap_entry. apply impl_enode.
  carve_frame 64%nat ST.
  do 8 step.
  step. step. if_cases K0; zify_cond K0. 2:{ exfalso. rewrite ?unsigned_lit in K0 by lia. lia. } clear K0.
  step. step. step. if_cases K1; zify_cond K1. 2:{ exfalso. rewrite ?unsigned_lit in K1 by lia. lia. } clear K1.
  step. step. if_cases K2; zify_cond K2. 2:{ exfalso. rewrite ?unsigned_lit in K2 by lia. lia. } clear K2.
  (* [comment removed for export] *)
  set (z0 := Z_to_bv 64 0). set (zm1 := Z_to_bv 64 (-1)). set (z50 := Z_to_bv 64 50).
  set (zA := Z_to_bv 64 A). set (zL := Z_to_bv 64 L). set (zP := Z_to_bv 64 P).
  do 6 step. step. step. do 6 step. step.
  subst z0 zm1 z50 zA zL zP.
  step. step. step_ecall.
  split. { at_node_solve. }
  intros rsp ans Hdec. destruct (DEC rsp ans Hdec) as (r & u & HR & ->). clear Hdec.
  pose proof (bv_unsigned_in_range 64 r) as RR. change (bv_modulus 64) with (2^64)%Z in RR.
  destruct u; unfold fixed_shape; cbv iota.
  all: sys_nret.
  all: step; step; step.
  all: if_cases K; zify_cond K; [| exfalso; apply Z.lor_eq_0_iff in K; lia ].
  all: step; call_sp sysret_spec; [exact ST | exact ERR | exact MI | lia | lia | lia |]; rename PC into ST; rename POST into ERR.
  all: do 10 step; release_frame FR ST (bv_unsigned sp).
  all: unfold rmmap_fixed_post; apply evt_done; exists r; eexists; do 15 eexists; split; [exact HR|]; split; [reflexivity|].
  all: split; [ eapply munch_weaken; [|exact MU]; intros y; cbn; lia |].
  all: split; [ first [intros; discriminate | intros _; assumption] |].
  all: split; [lazymatch goal with H : mem_inv usegs ?mm |- mem_inv usegs ?mm => exact H end|].
  all: split; [lazymatch goal with H : stk usegs ?mm ?a ?b |- stk usegs ?mm _ _ => exact H end|].
  all: lazymatch goal with H : rw_cells usegs ?mm ?a ?c |- rw_cells usegs ?mm _ _ => exact H end.
Qed.

End PORT.

End WithCeil.
End TwB.
End RF_mm_syscalls.

(* [comment removed for export] *)
Module RF_mremap.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require AllocBridge__Spec. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.AllocBridge__Spec.AllocBridge.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require Import TlsBase.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import Tac ITree Nodes SysStep Decode.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import ImgSrc3.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require AllocBridge__Spec. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.AllocBridge__Spec.KArith.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require Import F_mm_syscalls.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_lock__S3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require RMallocRep__S3. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_lock__S3.F_syscalls OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RMallocRep__S3.RMallocRep.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require Import MSecret.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import LiaPin.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require SecDiet.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac lia ::= pinned_lia.
Import ListNotations.
Open Scope bv_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Section WithCeil.
Context {CEILV : CEIL} {MSECV : MSEC}.
Definition rmremap_entry : Z := 0x1a6b4.

(* [comment removed for export] *)
Definition mremap_mem (old on nn : Z) (x : mremap_ans) (m : word -> option byte) : word -> option byte :=
  match x with
  | MrErr _ => m
  | MrSame => if (nn <? on)%Z then apply_unmaps m [(Z_to_bv 64 (old + nn), Z_to_bv 64 (on - nn))]
              else apply_zeros m [(Z_to_bv 64 (old + on), Z_to_bv 64 (nn - on))]
  | MrMoved a => apply_copy m (apply_zeros (apply_unmaps m [(Z_to_bv 64 old, Z_to_bv 64 on)]) [(Z_to_bv 64 (a + on), Z_to_bv 64 (nn - on))])
                            (mkCopy (Z_to_bv 64 old) (Z_to_bv 64 a) (Z_to_bv 64 on))
  end.

Definition mremap_ret (old : Z) (x : mremap_ans) : word :=
  match x with MrErr _ => Z_to_bv 64 (-1) | MrSame => Z_to_bv 64 old | MrMoved a => Z_to_bv 64 a end.

Section PORT.
Context {PState : Type} {AS : AllocSt PState} {TB : TlsBase}.
Let TLSFACTS := the_tb_facts (TB:=TB).
Local Unset Keyed Unification.

(* [comment removed for export] *)
Definition img_clear (b on nn : Z) : Prop := (nn <= on \/ b + nn <= 0x10000 \/ 0x55000 <= b)%Z.

(* [comment removed for export] *)
Definition rmremap_facts (old on nn : Z) (avoid : list (Z * Z)) (x : mremap_ans) : Prop :=
  match x with
  | MrErr e => (1 <= e <= 4095)%Z
  | MrSame => (on < nn -> old + nn <= alloc_ceiling /\ avoids old nn avoid = true)%Z
  | MrMoved a => (on < nn)%Z /\ mmap_addr_ok nn avoid a = true /\ (0 <= a < 2^64)%Z /\ a <> old
  end.

Definition rmremap_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (old on nn : Z) (avoid : list (Z * Z)) (errv : word) (lo : Z) (m : word -> option byte) (x : mremap_ans) : machine_state -> Prop :=
  fun ms' => rmremap_facts old on nn avoid x /\ (
    match x with MrErr _ => True | MrSame => img_clear old on nn | MrMoved a => img_clear a on nn end ->
    exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m2,
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (mremap_ret old x) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None (mremap_mem old on nn x m2) (seg_rom ssegs)
    /\ mem_inv ssegs (mremap_mem old on nn x m2) /\ stk ssegs (mremap_mem old on nn x m2) lo (bv_unsigned sp)
    /\ match x with
       | MrErr e => munch [(bv_unsigned sp - 112, bv_unsigned sp); (errno_addr tp, errno_addr tp + 4)]%Z m m2 /\ wmono ssegs m m2
                    /\ rw_cells ssegs m2 (errno_addr tp) [C4 (Z_to_bv 64 e)] /\ (1 <= e <= 4095)%Z
       | MrSame => munch [(bv_unsigned sp - 112, bv_unsigned sp)]%Z m m2 /\ wmono ssegs m m2 /\ mem_inv ssegs m2 /\ rw_cells ssegs m2 (errno_addr tp) [C4 errv]
                   /\ (on < nn -> old + nn <= alloc_ceiling /\ avoids old nn (avoid) = true)%Z
       | MrMoved a => munch [(bv_unsigned sp - 112, bv_unsigned sp)]%Z m m2 /\ wmono ssegs m m2 /\ mem_inv ssegs m2 /\ rw_cells ssegs m2 (errno_addr tp) [C4 errv]
                      /\ (on < nn)%Z /\ mmap_addr_ok nn avoid a = true /\ (0 <= a < 2^64)%Z /\ a <> old
       end).

Definition rmremap_spec__stmt : Prop := forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
    (old on nn : Z) (avoid : list (Z * Z)) (errv : word) (lo : Z),
  stk ssegs m lo (bv_unsigned sp) ->
  rw_cells ssegs m (errno_addr tp) [C4 errv] ->
  rw_cells ssegs m RGOT_SSP [C8 (wz RSSP_GUARD)] -> rw_cells ssegs m RSSP_GUARD [C8 mcanary] ->
  mem_inv ssegs m ->
  a0 = Z_to_bv 64 old -> a1 = Z_to_bv 64 on -> a2 = Z_to_bv 64 nn -> a3 = Z_to_bv 64 Uapi.MREMAP_MAYMOVE ->
  (0 < old)%Z -> (old mod 4096 = 0)%Z -> (0 < on)%Z -> (on mod 4096 = 0)%Z -> (0 < nn < 2^62)%Z -> (nn mod 4096 = 0)%Z -> on <> nn ->
  (old + on <= alloc_ceiling)%Z -> (old + on <= 0x10000 \/ 0x55000 <= old)%Z ->
  (lo <= bv_unsigned sp - 112)%Z -> (alloc_ceiling <= lo)%Z ->
  (errno_addr tp + 4 <= bv_unsigned sp - 112 \/ bv_unsigned sp <= errno_addr tp)%Z ->
  (164 <= bv_unsigned tp)%Z ->
  (0x339d0 <= errno_addr tp /\ errno_addr tp + 4 <= 0x53aa0)%Z ->
  impl ssegs (at_node ssegs) (npeek ssegs) (enode (NMremap old on nn) (dec_mremap old on nn avoid avoid))
       (epost (rmremap_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc old on nn avoid errv lo m))
       (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
           F (Z_to_bv 64 rmremap_entry) fc None m (seg_rom ssegs)).
Section Sz1.
Variables ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m old on nn avoid errv lo : ltac2:(SecDiet.SzSec.tyM 'rmremap_spec__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra).
Lemma rmremap_spec__body : ltac2:(SecDiet.SzSec.bodyP 'rmremap_spec__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
Proof using TLSFACTS. pin_using (fun (TLSFACTS : unit) => tt). ceil_facts. msec_facts.
  intros ST ERR GOT GUARD MI -> -> -> -> O0 OAL ON0 ONAL NN NNAL NE OC OIMG LO CEIL SEP1 TP SEP2.
  pose proof (munch_refl [(bv_unsigned sp - 112, bv_unsigned sp); (errno_addr tp, errno_addr tp + 4)]%Z m) as MU.
  pose proof (munch_refl [(bv_unsigned sp - 112, bv_unsigned sp)]%Z m) as MU1.
  pose proof (wmono_refl ssegs m) as WM.
  pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64)%Z in SPR.
  ceil_facts.
  unfold rmremap_entry, RGOT_SSP, RSSP_GUARD in *. unfold wz in GOT, GUARD. change Uapi.MREMAP_MAYMOVE with 1%Z.
  apply impl_enode.
  carve_frame 96%nat ST.
  do 7 step. (* [comment removed for export] *)
  step. step. (* [comment removed for export] *)
  do 4 step. (* [comment removed for export] *)
  step. (* [comment removed for export] *)
  step. step. step. (* [comment removed for export] *)
  (* [comment removed for export] *)
  step. if_cases K0; zify_cond K0. 2:{ exfalso. revert K0. clear -NN. intros K0. lia. }
  clear K0.
  step. step. if_cases K1; zify_cond K1. 2:{ exfalso. revert K1. clear. intros K1. cbn in K1. lia. }
  clear K1.
  step. step_ecall.
  split. { at_node_solve. }
  intros rsp ans Hdec.
  pose proof (dec_mremap_Some old on nn avoid avoid rsp ans Hdec) as D. cbv zeta in D.
  rewrite !mmap_len_of_aligned in D by lia.
  (* [comment removed for export] *)
  assert (OKTAIL : forall (v : Z) (m2 mm : word -> option byte) (x : mremap_ans),
    mm = mremap_mem old on nn x m2 ->
    (0 <= v)%Z -> (v + 4096 <= alloc_ceiling)%Z -> mremap_ret old x = Z_to_bv 64 v ->
    mem_inv ssegs mm -> stk ssegs mm lo (bv_unsigned sp + -96) ->
    rw_cells ssegs mm (bv_unsigned sp + -96) [CB 8 (firstn 8 (firstn 16 (firstn 24 (firstn 32 (firstn 40 (firstn 48 (firstn 56 junk))))))); C8 mcanary;
       C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra; C8 a4; C8 a5; C8 a6; C8 a7] ->
    rw_cells ssegs mm 343304 [C8 mcanary] ->
    match x with
    | MrErr e => False
    | MrSame => munch [(bv_unsigned sp - 112, bv_unsigned sp)]%Z m m2 /\ wmono ssegs m m2 /\ mem_inv ssegs m2 /\ rw_cells ssegs m2 (errno_addr tp) [C4 errv]
                /\ (on < nn -> old + nn <= alloc_ceiling /\ avoids old nn (avoid) = true)%Z
    | MrMoved a => munch [(bv_unsigned sp - 112, bv_unsigned sp)]%Z m m2 /\ wmono ssegs m m2 /\ mem_inv ssegs m2 /\ rw_cells ssegs m2 (errno_addr tp) [C4 errv]
                   /\ (on < nn)%Z /\ mmap_addr_ok nn avoid a = true /\ (0 <= a < 2^64)%Z /\ a <> old
    end ->
    evt ssegs (rmremap_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc old on nn avoid errv lo m x)
      (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -96)) gp tp (Z_to_bv 64 141008) t1 t2 (Z_to_bv 64 (-1)) (Z_to_bv 64 343304)
                (Z_to_bv 64 v) (Z_to_bv 64 on) (Z_to_bv 64 nn) (Z_to_bv 64 1) (Z_to_bv 64 0) (Z_to_bv 64 9223372036854775807) a6 (Z_to_bv 64 216)
                s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x1a74c) fc None mm (seg_rom ssegs))).
  { intros v m2 mm x Emm V0 VC Ev MIm STm FRm GUARDm SIDE. ceil_facts.
    (* [comment removed for export] *)
    step. step. step. step. if_cases K1; zify_cond K1. 2:{ exfalso. rewrite ?unsigned_lit in K1 by lia. lia. }
    step.
    (* [comment removed for export] *)
    step. step. step. step. if_cases K2; zify_cond K2. { exfalso. apply K2. reflexivity. }
    do 9 step. release_frame FRm STm (bv_unsigned sp).
    apply evt_done. unfold rmremap_post. split.
    { unfold rmremap_facts. destruct x; [destruct SIDE| exact (proj2 (proj2 (proj2 (proj2 SIDE))))| exact (proj2 (proj2 (proj2 (proj2 SIDE))))]. }
    intros _. do 14 eexists. exists m2. rewrite <- Ev, <- Emm. split; [reflexivity|].
    split; [exact MIm|]. split; [exact STm|]. destruct x; [destruct SIDE| exact SIDE| exact SIDE]. }
  pose proof FR as FR0. pose proof ST as ST0.
  destruct ans as [e| |a].
  - (* [comment removed for export] *)
    clear MU1 OKTAIL. destruct D as [-> He]. unfold efferr, eff0. sys_nret.
    step. call_sp sysret_spec; [exact ST | exact ERR | exact MI | lia | lia | lia | ]. rename PC into ST; rename POST into ERR.
    unfold sysret_val, sysret_errno in *. rewrite errno_of_errno_ret in * by lia.
    (* [comment removed for export] *)
    step. step. step. step. if_cases K2; zify_cond K2. { exfalso. apply K2. reflexivity. }
    do 9 step. release_frame FR ST (bv_unsigned sp).
    apply evt_done. unfold rmremap_post, mremap_ret, mremap_mem. split; [exact He|]. intros _. do 14 eexists. eexists. split; [reflexivity|].
    split; [assumption|]. split; [exact ST|]. split; [exact MU|]. split; [exact WM|]. split; [exact ERR| exact He].
  - (* [comment removed for export] *)
    clear MU.
    destruct D as [[EQ _]|[[SH ->]|[GR (CE & AVS & ->)]]]; [exfalso; lia| |].
    + (* [comment removed for export] *)
      rewrite nret_MSsvc, ?mkR_set_a0. simp_regs.
      lazymatch goal with |- evt _ _ (MS _ _ (Z_to_bv 64 ?p + Z_to_bv 64 4) _ _ _ _) =>
        let p' := eval vm_compute in (p + 4)%Z in replace (Z_to_bv 64 p + Z_to_bv 64 4 : word) with (Z_to_bv 64 p' : word) by (rewrite lit_add_lit; reflexivity) end.
      rewrite apply_mem_unmaps.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (apply_unmaps ?mX _) _) =>
        assert (Hza : (0 <= old + nn < 2^64)%Z) by lia; assert (Hzn : (0 <= on - nn < 2^64)%Z) by lia;
        assert (Hzan : (old + nn + (on - nn) <= 2^64)%Z) by lia;
        pose proof (rw_cells_unmaps_other ssegs mX (old + nn) (on - nn) Hza Hzn Hzan _ _ FR ltac:(cbn [cells_size csize Nat.add]; lia)) as FRm;
        pose proof (rw_cells_unmaps_other ssegs mX (old + nn) (on - nn) Hza Hzn Hzan _ _ GUARD) as GUARDm;
        specialize (GUARDm ltac:(cbn [cells_size csize Nat.add]; clear -O0 NN ON0 SH OIMG; lia));
        pose proof (stk_unmaps_other ssegs mX (old + nn) (on - nn) Hza Hzn Hzan _ _ ST ltac:(lia)) as STm;
        pose proof (mem_inv_unmaps ssegs mX (old + nn) (on - nn) Hza Hzn Hzan MI) as MIm;
        apply (OKTAIL old mX _ MrSame); [unfold mremap_mem; rewrite (proj2 (Z.ltb_lt nn on)) by lia; reflexivity
          | lia| ceil_facts; lia| reflexivity| exact MIm| exact STm| exact FRm| exact GUARDm|]
      end.
      split; [exact MU1|]. split; [exact WM|]. split; [exact MI|]. split; [exact ERR|]. intros; exfalso; lia.
    + (* [comment removed for export] *)
      rewrite nret_MSsvc, ?mkR_set_a0. simp_regs.
      lazymatch goal with |- evt _ _ (MS _ _ (Z_to_bv 64 ?p + Z_to_bv 64 4) _ _ _ _) =>
        let p' := eval vm_compute in (p + 4)%Z in replace (Z_to_bv 64 p + Z_to_bv 64 4 : word) with (Z_to_bv 64 p' : word) by (rewrite lit_add_lit; reflexivity) end.
      rewrite apply_mem_zeros.
      (* [comment removed for export] *)
      destruct (Z.le_gt_cases 0x55000 old) as [HI|LOW].
      2: destruct (Z.le_gt_cases (old + nn) 0x10000) as [LOWOK|BAD].
      3:{ apply evt_done. unfold rmremap_post. split; [intros _; split; [exact CE| exact AVS]|]. intros IC. exfalso. unfold img_clear in IC. lia. }
      all: lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (apply_zeros ?mX _) _) =>
        assert (Hza : (0 <= old + on < 2^64)%Z) by lia; assert (Hzn : (0 <= nn - on < 2^64)%Z) by lia;
        assert (Hzan : (old + on + (nn - on) <= 2^64)%Z) by (ceil_facts; lia);
        pose proof (rw_cells_zeros_other ssegs mX (old + on) (nn - on) Hza Hzn Hzan _ _ FR ltac:(ceil_facts; cbn [cells_size csize Nat.add]; lia)) as FRm;
        pose proof (rw_cells_zeros_other ssegs mX (old + on) (nn - on) Hza Hzn Hzan _ _ GUARD ltac:(cbn [cells_size csize Nat.add]; lia)) as GUARDm;
        pose proof (stk_zeros ssegs mX (old + on) (nn - on) Hza Hzn Hzan _ _ ST) as STm;
        pose proof (mem_inv_zeros ssegs mX (old + on) (nn - on) Hza Hzn Hzan MI ltac:(intros x Hx; apply ref_ro_addr_false; lia)) as MIm;
        apply (OKTAIL old mX _ MrSame); [unfold mremap_mem; rewrite (proj2 (Z.ltb_ge nn on)) by lia; reflexivity
          | lia| ceil_facts; lia| reflexivity| exact MIm| exact STm| exact FRm| exact GUARDm|]
      end.
      all: split; [exact MU1|]; split; [exact WM|]; split; [exact MI|]; split; [exact ERR|]; intros _; split; [exact CE| exact AVS].
  - (* [comment removed for export] *)
    clear MU. destruct D as (GR & AOK & AR & ANE & ->).
    pose proof (mmap_addr_ok_true _ _ _ AOK) as ((AAL & A0 & AC) & _). rewrite mmap_len_of_aligned in AC by lia. ceil_facts.
    rewrite nret_MSsvc_copies, ?mkR_set_a0. simp_regs.
    lazymatch goal with |- evt _ _ (MS _ _ (Z_to_bv 64 ?p + Z_to_bv 64 4) _ _ _ _) =>
      let p' := eval vm_compute in (p + 4)%Z in replace (Z_to_bv 64 p + Z_to_bv 64 4 : word) with (Z_to_bv 64 p' : word) by (rewrite lit_add_lit; reflexivity) end.
    rewrite apply_mem_mremap_move.
    destruct (Z.le_gt_cases 0x55000 a) as [HI|LOW].
    2: destruct (Z.le_gt_cases (a + nn) 0x10000) as [LOWOK|BAD].
    3:{ apply evt_done. unfold rmremap_post. split; [unfold rmremap_facts; split; [exact GR|]; split; [exact AOK|]; split; [exact AR|]; intros E; apply ANE; rewrite E; reflexivity|].
        intros IC. exfalso. unfold img_clear in IC. lia. }
    all: lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (apply_copy ?mX ?mZ ?c) _) =>
      assert (Hold : (0 <= old < 2^64)%Z) by lia; assert (Holdn : (old + on <= 2^64)%Z) by lia;
      assert (Hdst : (0 <= a < 2^64)%Z) by lia; assert (Hdstn : (a + nn < 2^64)%Z) by lia;
      assert (Hon : (0 <= on < 2^64)%Z) by lia; assert (Hnn : (on <= nn < 2^64)%Z) by lia;
      pose proof (mremap_move_mem_inv ssegs mX old on a nn Hold Holdn Hdst Hdstn Hon Hnn MI ltac:(intros x Hx; apply ref_ro_addr_false; lia)) as MIm;
      assert (Hza : (0 <= a + on < 2^64)%Z) by lia; assert (Hzn : (0 <= nn - on < 2^64)%Z) by lia; assert (Hzan : (a + on + (nn - on) <= 2^64)%Z) by lia;
      assert (Hua : (0 <= old < 2^64)%Z) by lia; assert (Hun : (0 <= on < 2^64)%Z) by lia; assert (Huan : (old + on <= 2^64)%Z) by lia;
      pose proof (rw_cells_unmaps_other ssegs mX old on Hua Hun Huan _ _ FR ltac:(cbn [cells_size csize Nat.add]; lia)) as FR1;
      pose proof (rw_cells_zeros_other ssegs _ (a + on) (nn - on) Hza Hzn Hzan _ _ FR1 ltac:(cbn [cells_size csize Nat.add]; lia)) as FR2;
      pose proof (rw_cells_copy_other ssegs mX _ old a on Hua Hdst Hun _ _ FR2 ltac:(cbn [cells_size csize Nat.add]; lia)) as FRm;
      pose proof (rw_cells_unmaps_other ssegs mX old on Hua Hun Huan _ _ GUARD ltac:(cbn [cells_size csize Nat.add]; lia)) as GU1;
      pose proof (rw_cells_zeros_other ssegs _ (a + on) (nn - on) Hza Hzn Hzan _ _ GU1 ltac:(cbn [cells_size csize Nat.add]; lia)) as GU2;
      pose proof (rw_cells_copy_other ssegs mX _ old a on Hua Hdst Hun _ _ GU2 ltac:(cbn [cells_size csize Nat.add]; lia)) as GUARDm;
      pose proof (stk_unmaps_other ssegs mX old on Hua Hun Huan _ _ ST ltac:(lia)) as ST1;
      pose proof (stk_zeros ssegs _ (a + on) (nn - on) Hza Hzn Hzan _ _ ST1) as ST2;
      pose proof (stk_copy_other ssegs mX _ old a on Hua Hdst Hun _ _ ST2 ltac:(lia)) as STm;
      apply (OKTAIL a mX _ (MrMoved a)); [reflexivity| lia| ceil_facts; lia| reflexivity| exact MIm| exact STm| exact FRm| exact GUARDm|]
    end.
    all: split; [exact MU1|]; split; [exact WM|]; split; [exact MI|]; split; [exact ERR|]; split; [exact GR|]; split; [exact AOK|]; split; [exact AR|].
    all: intros E; apply ANE; rewrite E; reflexivity.
Qed.
End Sz1.
Lemma rmremap_spec : ltac:(let t := eval cbv delta [rmremap_spec__stmt] in rmremap_spec__stmt in exact t).
Proof using TLSFACTS. intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m old on nn avoid errv lo. ltac2:(SecDiet.SzSec.closeP 'rmremap_spec__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.
End PORT.

End WithCeil.

(* [comment removed for export] *)
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require ImgTgtUbsan.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require TlsBaseU.
Module TwB.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.AllocBridge__Spec.AllocBridge.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.TlsBaseU.
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Tac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ITree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Nodes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.SysStep OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Decode.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ImgTgtUbsan.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.AllocBridge__Spec.KArith.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.F_mm_syscalls.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_lock__S3.F_syscalls.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RMallocRep__S3.RMallocRep.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MSecret.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.LiaPin.
(* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac lia ::= pinned_lia.
Import ListNotations.
Open Scope bv_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Section WithCeil.
Context {CEILV : CEIL} {MSECV : MSEC}.
Definition rmremap_entry : Z := 0x1ae74.

(* [comment removed for export] *)
Definition mremap_mem (old on nn : Z) (x : mremap_ans) (m : word -> option byte) : word -> option byte :=
  match x with
  | MrErr _ => m
  | MrSame => if (nn <? on)%Z then apply_unmaps m [(Z_to_bv 64 (old + nn), Z_to_bv 64 (on - nn))]
              else apply_zeros m [(Z_to_bv 64 (old + on), Z_to_bv 64 (nn - on))]
  | MrMoved a => apply_copy m (apply_zeros (apply_unmaps m [(Z_to_bv 64 old, Z_to_bv 64 on)]) [(Z_to_bv 64 (a + on), Z_to_bv 64 (nn - on))])
                            (mkCopy (Z_to_bv 64 old) (Z_to_bv 64 a) (Z_to_bv 64 on))
  end.

Definition mremap_ret (old : Z) (x : mremap_ans) : word :=
  match x with MrErr _ => Z_to_bv 64 (-1) | MrSame => Z_to_bv 64 old | MrMoved a => Z_to_bv 64 a end.

Section PORT.
Context {PState : Type} {AS : AllocSt PState} {TB : TlsBase}.
Let TLSFACTS := the_tb_facts (TB:=TB).
Local Unset Keyed Unification.

(* [comment removed for export] *)
Definition img_clear (b on nn : Z) : Prop := (nn <= on \/ b + nn <= 0x10000 \/ 0x56000 <= b)%Z.

(* [comment removed for export] *)
Definition rmremap_facts (old on nn : Z) (avoid : list (Z * Z)) (x : mremap_ans) : Prop :=
  match x with
  | MrErr e => (1 <= e <= 4095)%Z
  | MrSame => (on < nn -> old + nn <= alloc_ceiling /\ avoids old nn avoid = true)%Z
  | MrMoved a => (on < nn)%Z /\ mmap_addr_ok nn avoid a = true /\ (0 <= a < 2^64)%Z /\ a <> old
  end.

Definition rmremap_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (old on nn : Z) (avoid : list (Z * Z)) (errv : word) (lo : Z) (m : word -> option byte) (x : mremap_ans) : machine_state -> Prop :=
  fun ms' => rmremap_facts old on nn avoid x /\ (
    match x with MrErr _ => True | MrSame => img_clear old on nn | MrMoved a => img_clear a on nn end ->
    exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m2,
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (mremap_ret old x) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None (mremap_mem old on nn x m2) (seg_rom usegs)
    /\ mem_inv usegs (mremap_mem old on nn x m2) /\ stk usegs (mremap_mem old on nn x m2) lo (bv_unsigned sp)
    /\ match x with
       | MrErr e => munch [(bv_unsigned sp - 112, bv_unsigned sp); (errno_addr tp, errno_addr tp + 4)]%Z m m2 /\ wmono usegs m m2
                    /\ rw_cells usegs m2 (errno_addr tp) [C4 (Z_to_bv 64 e)] /\ (1 <= e <= 4095)%Z
       | MrSame => munch [(bv_unsigned sp - 112, bv_unsigned sp)]%Z m m2 /\ wmono usegs m m2 /\ mem_inv usegs m2 /\ rw_cells usegs m2 (errno_addr tp) [C4 errv]
                   /\ (on < nn -> old + nn <= alloc_ceiling /\ avoids old nn (avoid) = true)%Z
       | MrMoved a => munch [(bv_unsigned sp - 112, bv_unsigned sp)]%Z m m2 /\ wmono usegs m m2 /\ mem_inv usegs m2 /\ rw_cells usegs m2 (errno_addr tp) [C4 errv]
                      /\ (on < nn)%Z /\ mmap_addr_ok nn avoid a = true /\ (0 <= a < 2^64)%Z /\ a <> old
       end).

Definition rmremap_spec__stmt : Prop := forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
    (old on nn : Z) (avoid : list (Z * Z)) (errv : word) (lo : Z),
  stk usegs m lo (bv_unsigned sp) ->
  rw_cells usegs m (errno_addr tp) [C4 errv] ->
  rw_cells usegs m RGOT_SSP [C8 (wz RSSP_GUARD)] -> rw_cells usegs m RSSP_GUARD [C8 mcanary] ->
  mem_inv usegs m ->
  a0 = Z_to_bv 64 old -> a1 = Z_to_bv 64 on -> a2 = Z_to_bv 64 nn -> a3 = Z_to_bv 64 Uapi.MREMAP_MAYMOVE ->
  (0 < old)%Z -> (old mod 4096 = 0)%Z -> (0 < on)%Z -> (on mod 4096 = 0)%Z -> (0 < nn < 2^62)%Z -> (nn mod 4096 = 0)%Z -> on <> nn ->
  (old + on <= alloc_ceiling)%Z -> (old + on <= 0x10000 \/ 0x56000 <= old)%Z ->
  (lo <= bv_unsigned sp - 112)%Z -> (alloc_ceiling <= lo)%Z ->
  (errno_addr tp + 4 <= bv_unsigned sp - 112 \/ bv_unsigned sp <= errno_addr tp)%Z ->
  (164 <= bv_unsigned tp)%Z ->
  (0x34190 <= errno_addr tp /\ errno_addr tp + 4 <= 0x54260)%Z ->
  impl usegs (at_node usegs) (npeek usegs) (enode (NMremap old on nn) (dec_mremap old on nn avoid avoid))
       (epost (rmremap_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc old on nn avoid errv lo m))
       (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
           F (Z_to_bv 64 rmremap_entry) fc None m (seg_rom usegs)).
Section Sz1.
Variables ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m old on nn avoid errv lo : ltac2:(SecDiet.SzSec.tyM 'rmremap_spec__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra).
Lemma rmremap_spec__body : ltac2:(SecDiet.SzSec.bodyP 'rmremap_spec__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
Proof using TLSFACTS. pin_using (fun (TLSFACTS : unit) => tt). ceil_facts. msec_facts.
 intros ST ERR GOT GUARD MI -> -> -> -> O0 OAL ON0 ONAL NN NNAL NE OC OIMG LO CEIL SEP1 TP SEP2.
  pose proof (munch_refl [(bv_unsigned sp - 112, bv_unsigned sp); (errno_addr tp, errno_addr tp + 4)]%Z m) as MU.
  pose proof (munch_refl [(bv_unsigned sp - 112, bv_unsigned sp)]%Z m) as MU1.
  pose proof (wmono_refl usegs m) as WM.
  pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64)%Z in SPR.
  ceil_facts.
  unfold rmremap_entry, RGOT_SSP, RSSP_GUARD in *. unfold wz in GOT, GUARD. change Uapi.MREMAP_MAYMOVE with 1%Z.
  apply impl_enode.
  carve_frame 96%nat ST.
  do 7 step. (* [comment removed for export] *)
  step. step. (* [comment removed for export] *)
  do 4 step. (* [comment removed for export] *)
  step. (* [comment removed for export] *)
  step. step. step. (* [comment removed for export] *)
  (* [comment removed for export] *)
  step. if_cases K0; zify_cond K0. 2:{ exfalso. revert K0. clear -NN. intros K0. lia. }
  clear K0.
  step. step. if_cases K1; zify_cond K1. 2:{ exfalso. revert K1. clear. intros K1. cbn in K1. lia. }
  clear K1.
  step. step_ecall.
  split. { at_node_solve. }
  intros rsp ans Hdec.
  pose proof (dec_mremap_Some old on nn avoid avoid rsp ans Hdec) as D. cbv zeta in D.
  rewrite !mmap_len_of_aligned in D by lia.
  (* [comment removed for export] *)
  assert (OKTAIL : forall (v : Z) (m2 mm : word -> option byte) (x : mremap_ans),
    mm = mremap_mem old on nn x m2 ->
    (0 <= v)%Z -> (v + 4096 <= alloc_ceiling)%Z -> mremap_ret old x = Z_to_bv 64 v ->
    mem_inv usegs mm -> stk usegs mm lo (bv_unsigned sp + -96) ->
    rw_cells usegs mm (bv_unsigned sp + -96) [CB 8 (firstn 8 (firstn 16 (firstn 24 (firstn 32 (firstn 40 (firstn 48 (firstn 56 junk))))))); C8 mcanary;
       C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra; C8 a4; C8 a5; C8 a6; C8 a7] ->
    rw_cells usegs mm 345288 [C8 mcanary] ->
    match x with
    | MrErr e => False
    | MrSame => munch [(bv_unsigned sp - 112, bv_unsigned sp)]%Z m m2 /\ wmono usegs m m2 /\ mem_inv usegs m2 /\ rw_cells usegs m2 (errno_addr tp) [C4 errv]
                /\ (on < nn -> old + nn <= alloc_ceiling /\ avoids old nn (avoid) = true)%Z
    | MrMoved a => munch [(bv_unsigned sp - 112, bv_unsigned sp)]%Z m m2 /\ wmono usegs m m2 /\ mem_inv usegs m2 /\ rw_cells usegs m2 (errno_addr tp) [C4 errv]
                   /\ (on < nn)%Z /\ mmap_addr_ok nn avoid a = true /\ (0 <= a < 2^64)%Z /\ a <> old
    end ->
    evt usegs (rmremap_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc old on nn avoid errv lo m x)
      (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -96)) gp tp (Z_to_bv 64 142992) t1 t2 (Z_to_bv 64 (-1)) (Z_to_bv 64 345288)
                (Z_to_bv 64 v) (Z_to_bv 64 on) (Z_to_bv 64 nn) (Z_to_bv 64 1) (Z_to_bv 64 0) (Z_to_bv 64 9223372036854775807) a6 (Z_to_bv 64 216)
                s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x1af0c) fc None mm (seg_rom usegs))).
  { intros v m2 mm x Emm V0 VC Ev MIm STm FRm GUARDm SIDE. ceil_facts.
    (* [comment removed for export] *)
    step. step. step. step. if_cases K1; zify_cond K1. 2:{ exfalso. rewrite ?unsigned_lit in K1 by lia. lia. }
    step.
    (* [comment removed for export] *)
    step. step. step. step. if_cases K2; zify_cond K2. { exfalso. apply K2. reflexivity. }
    do 9 step. release_frame FRm STm (bv_unsigned sp).
    apply evt_done. unfold rmremap_post. split.
    { unfold rmremap_facts. destruct x; [destruct SIDE| exact (proj2 (proj2 (proj2 (proj2 SIDE))))| exact (proj2 (proj2 (proj2 (proj2 SIDE))))]. }
    intros _. do 14 eexists. exists m2. rewrite <- Ev, <- Emm. split; [reflexivity|].
    split; [exact MIm|]. split; [exact STm|]. destruct x; [destruct SIDE| exact SIDE| exact SIDE]. }
  pose proof FR as FR0. pose proof ST as ST0.
  destruct ans as [e| |a].
  - (* [comment removed for export] *)
    clear MU1 OKTAIL. destruct D as [-> He]. unfold efferr, eff0. sys_nret.
    step. call_sp sysret_spec; [exact ST | exact ERR | exact MI | lia | lia | lia | ]. rename PC into ST; rename POST into ERR.
    unfold sysret_val, sysret_errno in *. rewrite errno_of_errno_ret in * by lia.
    (* [comment removed for export] *)
    step. step. step. step. if_cases K2; zify_cond K2. { exfalso. apply K2. reflexivity. }
    do 9 step. release_frame FR ST (bv_unsigned sp).
    apply evt_done. unfold rmremap_post, mremap_ret, mremap_mem. split; [exact He|]. intros _. do 14 eexists. eexists. split; [reflexivity|].
    split; [assumption|]. split; [exact ST|]. split; [exact MU|]. split; [exact WM|]. split; [exact ERR| exact He].
  - (* [comment removed for export] *)
    clear MU.
    destruct D as [[EQ _]|[[SH ->]|[GR (CE & AVS & ->)]]]; [exfalso; lia| |].
    + (* [comment removed for export] *)
      rewrite nret_MSsvc, ?mkR_set_a0. simp_regs.
      lazymatch goal with |- evt _ _ (MS _ _ (Z_to_bv 64 ?p + Z_to_bv 64 4) _ _ _ _) =>
        let p' := eval vm_compute in (p + 4)%Z in replace (Z_to_bv 64 p + Z_to_bv 64 4 : word) with (Z_to_bv 64 p' : word) by (rewrite lit_add_lit; reflexivity) end.
      rewrite apply_mem_unmaps.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (apply_unmaps ?mX _) _) =>
        assert (Hza : (0 <= old + nn < 2^64)%Z) by lia; assert (Hzn : (0 <= on - nn < 2^64)%Z) by lia;
        assert (Hzan : (old + nn + (on - nn) <= 2^64)%Z) by lia;
        pose proof (rw_cells_unmaps_other usegs mX (old + nn) (on - nn) Hza Hzn Hzan _ _ FR ltac:(cbn [cells_size csize Nat.add]; lia)) as FRm;
        pose proof (rw_cells_unmaps_other usegs mX (old + nn) (on - nn) Hza Hzn Hzan _ _ GUARD) as GUARDm;
        specialize (GUARDm ltac:(cbn [cells_size csize Nat.add]; clear -O0 NN ON0 SH OIMG; lia));
        pose proof (stk_unmaps_other usegs mX (old + nn) (on - nn) Hza Hzn Hzan _ _ ST ltac:(lia)) as STm;
        pose proof (mem_inv_unmaps usegs mX (old + nn) (on - nn) Hza Hzn Hzan MI) as MIm;
        apply (OKTAIL old mX _ MrSame); [unfold mremap_mem; rewrite (proj2 (Z.ltb_lt nn on)) by lia; reflexivity
          | lia| ceil_facts; lia| reflexivity| exact MIm| exact STm| exact FRm| exact GUARDm|]
      end.
      split; [exact MU1|]. split; [exact WM|]. split; [exact MI|]. split; [exact ERR|]. intros; exfalso; lia.
    + (* [comment removed for export] *)
      rewrite nret_MSsvc, ?mkR_set_a0. simp_regs.
      lazymatch goal with |- evt _ _ (MS _ _ (Z_to_bv 64 ?p + Z_to_bv 64 4) _ _ _ _) =>
        let p' := eval vm_compute in (p + 4)%Z in replace (Z_to_bv 64 p + Z_to_bv 64 4 : word) with (Z_to_bv 64 p' : word) by (rewrite lit_add_lit; reflexivity) end.
      rewrite apply_mem_zeros.
      (* [comment removed for export] *)
      destruct (Z.le_gt_cases 0x56000 old) as [HI|LOW].
      2: destruct (Z.le_gt_cases (old + nn) 0x10000) as [LOWOK|BAD].
      3:{ apply evt_done. unfold rmremap_post. split; [intros _; split; [exact CE| exact AVS]|]. intros IC. exfalso. unfold img_clear in IC. lia. }
      all: lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (apply_zeros ?mX _) _) =>
        assert (Hza : (0 <= old + on < 2^64)%Z) by lia; assert (Hzn : (0 <= nn - on < 2^64)%Z) by lia;
        assert (Hzan : (old + on + (nn - on) <= 2^64)%Z) by (ceil_facts; lia);
        pose proof (rw_cells_zeros_other usegs mX (old + on) (nn - on) Hza Hzn Hzan _ _ FR ltac:(ceil_facts; cbn [cells_size csize Nat.add]; lia)) as FRm;
        pose proof (rw_cells_zeros_other usegs mX (old + on) (nn - on) Hza Hzn Hzan _ _ GUARD ltac:(cbn [cells_size csize Nat.add]; lia)) as GUARDm;
        pose proof (stk_zeros usegs mX (old + on) (nn - on) Hza Hzn Hzan _ _ ST) as STm;
        pose proof (mem_inv_zeros usegs mX (old + on) (nn - on) Hza Hzn Hzan MI ltac:(intros x Hx; apply ref_ro_addr_false; lia)) as MIm;
        apply (OKTAIL old mX _ MrSame); [unfold mremap_mem; rewrite (proj2 (Z.ltb_ge nn on)) by lia; reflexivity
          | lia| ceil_facts; lia| reflexivity| exact MIm| exact STm| exact FRm| exact GUARDm|]
      end.
      all: split; [exact MU1|]; split; [exact WM|]; split; [exact MI|]; split; [exact ERR|]; intros _; split; [exact CE| exact AVS].
  - (* [comment removed for export] *)
    clear MU. destruct D as (GR & AOK & AR & ANE & ->).
    pose proof (mmap_addr_ok_true _ _ _ AOK) as ((AAL & A0 & AC) & _). rewrite mmap_len_of_aligned in AC by lia. ceil_facts.
    rewrite nret_MSsvc_copies, ?mkR_set_a0. simp_regs.
    lazymatch goal with |- evt _ _ (MS _ _ (Z_to_bv 64 ?p + Z_to_bv 64 4) _ _ _ _) =>
      let p' := eval vm_compute in (p + 4)%Z in replace (Z_to_bv 64 p + Z_to_bv 64 4 : word) with (Z_to_bv 64 p' : word) by (rewrite lit_add_lit; reflexivity) end.
    rewrite apply_mem_mremap_move.
    destruct (Z.le_gt_cases 0x56000 a) as [HI|LOW].
    2: destruct (Z.le_gt_cases (a + nn) 0x10000) as [LOWOK|BAD].
    3:{ apply evt_done. unfold rmremap_post. split; [unfold rmremap_facts; split; [exact GR|]; split; [exact AOK|]; split; [exact AR|]; intros E; apply ANE; rewrite E; reflexivity|].
        intros IC. exfalso. unfold img_clear in IC. lia. }
    all: lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (apply_copy ?mX ?mZ ?c) _) =>
      assert (Hold : (0 <= old < 2^64)%Z) by lia; assert (Holdn : (old + on <= 2^64)%Z) by lia;
      assert (Hdst : (0 <= a < 2^64)%Z) by lia; assert (Hdstn : (a + nn < 2^64)%Z) by lia;
      assert (Hon : (0 <= on < 2^64)%Z) by lia; assert (Hnn : (on <= nn < 2^64)%Z) by lia;
      pose proof (mremap_move_mem_inv usegs mX old on a nn Hold Holdn Hdst Hdstn Hon Hnn MI ltac:(intros x Hx; apply ref_ro_addr_false; lia)) as MIm;
      assert (Hza : (0 <= a + on < 2^64)%Z) by lia; assert (Hzn : (0 <= nn - on < 2^64)%Z) by lia; assert (Hzan : (a + on + (nn - on) <= 2^64)%Z) by lia;
      assert (Hua : (0 <= old < 2^64)%Z) by lia; assert (Hun : (0 <= on < 2^64)%Z) by lia; assert (Huan : (old + on <= 2^64)%Z) by lia;
      pose proof (rw_cells_unmaps_other usegs mX old on Hua Hun Huan _ _ FR ltac:(cbn [cells_size csize Nat.add]; lia)) as FR1;
      pose proof (rw_cells_zeros_other usegs _ (a + on) (nn - on) Hza Hzn Hzan _ _ FR1 ltac:(cbn [cells_size csize Nat.add]; lia)) as FR2;
      pose proof (rw_cells_copy_other usegs mX _ old a on Hua Hdst Hun _ _ FR2 ltac:(cbn [cells_size csize Nat.add]; lia)) as FRm;
      pose proof (rw_cells_unmaps_other usegs mX old on Hua Hun Huan _ _ GUARD ltac:(cbn [cells_size csize Nat.add]; lia)) as GU1;
      pose proof (rw_cells_zeros_other usegs _ (a + on) (nn - on) Hza Hzn Hzan _ _ GU1 ltac:(cbn [cells_size csize Nat.add]; lia)) as GU2;
      pose proof (rw_cells_copy_other usegs mX _ old a on Hua Hdst Hun _ _ GU2 ltac:(cbn [cells_size csize Nat.add]; lia)) as GUARDm;
      pose proof (stk_unmaps_other usegs mX old on Hua Hun Huan _ _ ST ltac:(lia)) as ST1;
      pose proof (stk_zeros usegs _ (a + on) (nn - on) Hza Hzn Hzan _ _ ST1) as ST2;
      pose proof (stk_copy_other usegs mX _ old a on Hua Hdst Hun _ _ ST2 ltac:(lia)) as STm;
      apply (OKTAIL a mX _ (MrMoved a)); [reflexivity| lia| ceil_facts; lia| reflexivity| exact MIm| exact STm| exact FRm| exact GUARDm|]
    end.
    all: split; [exact MU1|]; split; [exact WM|]; split; [exact MI|]; split; [exact ERR|]; split; [exact GR|]; split; [exact AOK|]; split; [exact AR|].
    all: intros E; apply ANE; rewrite E; reflexivity.
Qed.
End Sz1.
Lemma rmremap_spec : ltac:(let t := eval cbv delta [rmremap_spec__stmt] in rmremap_spec__stmt in exact t).
Proof using TLSFACTS. intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m old on nn avoid errv lo. ltac2:(SecDiet.SzSec.closeP 'rmremap_spec__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.
End PORT.

End WithCeil.
End TwB.
End RF_mremap.

(* [comment removed for export] *)
Module RF_realloc63M.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require AllocBridge__Spec. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.AllocBridge__Spec.AllocBridge.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require Import TlsBase.
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import Tac Image ZBridge SysStep Arr ITree Nodes Decode.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require Import SFModel.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import ImgSrc3.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require MallocTree. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require MallocKit_A2__MA. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocTree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocKit_A2__MA.MallocKit_A2.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require RMallocRep__S3. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RMallocRep__S3.RMallocRep OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RMallocRep__S3.RMallocTree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RF_mm_syscalls__S3.RF_mremap.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require STree Malloc. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require KInv__Spec. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.STree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Malloc OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.KInv__Spec.MallocRe.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require MI_Realloc2__Spec.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require Import MSecret.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import LiaPin.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac lia ::= pinned_lia.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
(* [comment removed for export] *)

Section WithCeil.
Context {CEILV : CEIL} {MSECV : MSEC}.
Lemma is_err_neg_errno e : 1 <= e <= 4095 -> is_err (neg_errno e) = true.
Proof using CEILV MSECV. pin_using (fun (CEILV MSECV : unit) => tt). ceil_facts. msec_facts. intros He. unfold is_err, neg_errno, TWO64. apply Z.ltb_lt. lia. Qed.

(* [comment removed for export] *)
Lemma mremap_ok_cases st rid old oldlen needed z :
  mremap_answer_ok st rid old oldlen needed z = true -> is_err z = false ->
  (z = old /\ (needed <= oldlen \/ (old + needed <= alloc_ceiling /\ ranges_free (live_ranges_wo st rid) (old + oldlen) (needed - oldlen) = true)))
  \/ (z <> old /\ 0 < z /\ z mod 4096 = 0 /\ z + needed <= alloc_ceiling /\ ranges_free (live_ranges st) z needed = true).
Proof using MSECV. pin_using (fun (MSECV : unit) => tt). ceil_facts. msec_facts.
  intros OK ERR. unfold mremap_answer_ok in OK. rewrite (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_Realloc2__Spec.MI_Realloc3.is_err_false_not_errno z ERR) in OK. cbn [orb] in OK.
  apply Bool.orb_true_iff in OK. destruct OK as [OK|OK].
  - apply andb_prop in OK as [Ez OK]. apply Z.eqb_eq in Ez. left. split; [exact Ez|].
    apply Bool.orb_true_iff in OK. destruct OK as [LE|OK]; [left; apply Z.leb_le in LE; exact LE|].
    apply andb_prop in OK as [CE RF]. apply Z.leb_le in CE. right. split; [exact CE| exact RF].
  - apply andb_prop in OK as [OK RFz]. apply andb_prop in OK as [OK CE]. apply andb_prop in OK as [OK AL]. apply andb_prop in OK as [NEz POS].
    apply Z.ltb_lt in POS. apply Z.eqb_eq in AL. apply Z.leb_le in CE. apply Bool.negb_true_iff in NEz. apply Z.eqb_neq in NEz.
    right. unfold PGSZ in AL. repeat split; assumption.
Qed.

(* [comment removed for export] *)
Lemma ranges_free_app_pos l a n k :
  (forall b kk, In (b, kk) l -> 0 < kk) -> 0 <= n -> 0 <= k ->
  ranges_free l a n = true -> ranges_free l (a + n) k = true -> ranges_free l a (n + k) = true.
Proof using CEILV MSECV. pin_using (fun (CEILV MSECV : unit) => tt). ceil_facts. msec_facts.
  intros POS Hn Hk H1 H2. apply ranges_free_intro. intros b kk HI.
  pose proof (ranges_free_In _ _ _ _ _ H1 HI) as D1. pose proof (ranges_free_In _ _ _ _ _ H2 HI) as D2. pose proof (POS _ _ HI). lia.
Qed.

Section PORT.
Context {TB : TlsBase}.

Lemma ref_reserved_pos : forall b kk, In (b, kk) ref_reserved -> 0 < kk.
Proof using MSECV. pin_using (fun (MSECV : unit) => tt). ceil_facts. msec_facts.
  intros b kk HI. unfold ref_reserved in HI. cbn in HI.
  destruct HI as [E|[E|[E|[E|[E|[]]]]]]; inversion E; subst; lia.
Qed.

Lemma rpres_except_of_eq (C : Z -> Prop) (m m' : mem) :
  (forall a, 0 <= a < 2^64 -> ~ C a -> m' (wa a) = m (wa a)) -> rpres_except C m m'.
Proof using CEILV MSECV. pin_using (fun (CEILV MSECV : unit) => tt). ceil_facts. msec_facts.
  intros H a Ha Hc. pose proof (H a Ha Hc) as E. split; [exact E|]. unfold wview. rewrite E. tauto.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma mremap_mem_facts (m2 : mem) (old on nn : Z) (x : mremap_ans) (nb : Z) :
  0 < old -> 0 < on -> 0 < nn -> old + on <= alloc_ceiling -> 0 < nb -> nb + nn <= alloc_ceiling ->
  match x with
  | MrErr _ => False
  | MrSame => nb = old
  | MrMoved a => nb = a /\ on < nn /\ (old + on <= a \/ a + nn <= old)
  end ->
  let mA := mremap_mem old on nn x m2 in
     (forall a, 0 <= a < 2^64 -> (a < old \/ old + on <= a) -> (a < nb \/ nb + nn <= a) -> mA (wa a) = m2 (wa a))
  /\ (forall o, 0 <= o < Z.min on nn -> mA (wa (nb + o)) = m2 (wa (old + o)))
  /\ (forall o, on <= o < nn -> mA (wa (nb + o)) = Some (Z_to_bv 8 0)).
Proof using MSECV. pin_using (fun (MSECV : unit) => tt). ceil_facts. msec_facts.
  intros O0 ON0 NN0 OC NB0 NC HX. ceil_facts. cbv zeta.
  destruct x as [e| |na]; [destruct HX| |]; cbn [mremap_mem].
  - subst nb. destruct (Z.ltb_spec0 nn on) as [LT|GE].
    + (* [comment removed for export] *)
      change (Z_to_bv 64 (old + nn)) with (wa (old + nn)).
      split; [| split].
      * intros a Ha H1 H2. apply (unmaps_outside m2 (old + nn) (on - nn)); try lia. rewrite wa_unsigned by lia. lia.
      * intros o Ho. apply (unmaps_outside m2 (old + nn) (on - nn)); try lia. rewrite wa_unsigned by lia. lia.
      * intros o Ho. exfalso. lia.
    + (* [comment removed for export] *)
      change (Z_to_bv 64 (old + on)) with (wa (old + on)).
      split; [| split].
      * intros a Ha H1 H2. apply (zeros_outside m2 (old + on) (nn - on)); try lia. rewrite wa_unsigned by lia. lia.
      * intros o Ho. apply (zeros_outside m2 (old + on) (nn - on)); try lia. rewrite wa_unsigned by lia. lia.
      * intros o Ho. apply (zeros_inside m2 (old + on) (nn - on)); try lia. rewrite wa_unsigned by lia. lia.
  - destruct HX as (-> & LT & DIS).
    change (Z_to_bv 64 old) with (wa old). change (Z_to_bv 64 na) with (wa na). change (Z_to_bv 64 (na + on)) with (wa (na + on)).
    split; [| split].
    + intros a Ha H1 H2. apply (mremap_move_outside m2 old on na nn); try lia; rewrite wa_unsigned by lia; lia.
    + intros o Ho. rewrite (mremap_move_copied m2 old on na nn); try lia; rewrite ?wa_unsigned by lia; [| lia].
      f_equal. f_equal. lia.
    + intros o Ho. apply (mremap_move_tail m2 old on na nn); try lia. rewrite wa_unsigned by lia. lia.
Qed.

Lemma mremap_mem_wr_at (m2 : mem) (old on nn : Z) (x : mremap_ans) (nb : Z) :
  0 < old -> 0 < on -> 0 < nn -> old + on <= alloc_ceiling -> 0 < nb -> nb + nn <= alloc_ceiling ->
  match x with
  | MrErr _ => False
  | MrSame => nb = old
  | MrMoved a => nb = a /\ on < nn /\ (old + on <= a \/ a + nn <= old)
  end ->
  (old + on <= 0x10000 \/ 0x55000 <= old) -> (nb + nn <= 0x10000 \/ 0x55000 <= nb) ->
  wr_at ssegs m2 old on ->
  wr_at ssegs (mremap_mem old on nn x m2) nb nn.
Proof using MSECV. pin_using (fun (MSECV : unit) => tt). ceil_facts. msec_facts.
  intros O0 ON0 NN0 OC NB0 NC HX OI NI WR.
  destruct (mremap_mem_facts m2 old on nn x nb O0 ON0 NN0 OC NB0 NC HX) as (OUT & PRE & TL).
  ceil_facts. destruct WR as (_ & _ & WR).
  split; [lia|]. split; [lia|]. intros i Hi.
  rewrite ref_wview_overlay by (rewrite wa_unsigned by lia; lia).
  destruct (Z_lt_dec i on) as [LT|GE].
  - rewrite PRE by lia. specialize (WR i ltac:(lia)). rewrite ref_wview_overlay in WR by (rewrite wa_unsigned by lia; lia). exact WR.
  - rewrite TL by lia. discriminate.
Qed.

End PORT.

End WithCeil.

(* [comment removed for export] *)
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require ImgTgtUbsan.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require TlsBaseU.
Module TwB.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.AllocBridge__Spec.AllocBridge.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.TlsBaseU.
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Tac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Image OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ZBridge OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.SysStep OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Arr OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ITree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Nodes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Decode.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.SFModel.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ImgTgtUbsan.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocTree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocKit_A2__MA.MallocKit_A2.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RMallocRep__S3.RMallocRep.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RMallocRep__S3.RMallocTree.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RF_mm_syscalls__S3.RF_mremap.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.STree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Malloc OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.KInv__Spec.MallocRe.
(* [comment removed for export] *)
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MSecret.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.LiaPin.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac lia ::= pinned_lia.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
(* [comment removed for export] *)

Section WithCeil.
Context {CEILV : CEIL} {MSECV : MSEC}.
Lemma is_err_neg_errno e : 1 <= e <= 4095 -> is_err (neg_errno e) = true.
Proof using CEILV MSECV. pin_using (fun (CEILV MSECV : unit) => tt). ceil_facts. msec_facts. intros He. unfold is_err, neg_errno, TWO64. apply Z.ltb_lt. lia. Qed.

(* [comment removed for export] *)
Lemma mremap_ok_cases st rid old oldlen needed z :
  mremap_answer_ok st rid old oldlen needed z = true -> is_err z = false ->
  (z = old /\ (needed <= oldlen \/ (old + needed <= alloc_ceiling /\ ranges_free (live_ranges_wo st rid) (old + oldlen) (needed - oldlen) = true)))
  \/ (z <> old /\ 0 < z /\ z mod 4096 = 0 /\ z + needed <= alloc_ceiling /\ ranges_free (live_ranges st) z needed = true).
Proof using MSECV. pin_using (fun (MSECV : unit) => tt). ceil_facts. msec_facts.
  intros OK ERR. unfold mremap_answer_ok in OK. rewrite (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_Realloc2__Spec.MI_Realloc3.is_err_false_not_errno z ERR) in OK. cbn [orb] in OK.
  apply Bool.orb_true_iff in OK. destruct OK as [OK|OK].
  - apply andb_prop in OK as [Ez OK]. apply Z.eqb_eq in Ez. left. split; [exact Ez|].
    apply Bool.orb_true_iff in OK. destruct OK as [LE|OK]; [left; apply Z.leb_le in LE; exact LE|].
    apply andb_prop in OK as [CE RF]. apply Z.leb_le in CE. right. split; [exact CE| exact RF].
  - apply andb_prop in OK as [OK RFz]. apply andb_prop in OK as [OK CE]. apply andb_prop in OK as [OK AL]. apply andb_prop in OK as [NEz POS].
    apply Z.ltb_lt in POS. apply Z.eqb_eq in AL. apply Z.leb_le in CE. apply Bool.negb_true_iff in NEz. apply Z.eqb_neq in NEz.
    right. unfold PGSZ in AL. repeat split; assumption.
Qed.

(* [comment removed for export] *)
Lemma ranges_free_app_pos l a n k :
  (forall b kk, In (b, kk) l -> 0 < kk) -> 0 <= n -> 0 <= k ->
  ranges_free l a n = true -> ranges_free l (a + n) k = true -> ranges_free l a (n + k) = true.
Proof using CEILV MSECV. pin_using (fun (CEILV MSECV : unit) => tt). ceil_facts. msec_facts.
  intros POS Hn Hk H1 H2. apply ranges_free_intro. intros b kk HI.
  pose proof (ranges_free_In _ _ _ _ _ H1 HI) as D1. pose proof (ranges_free_In _ _ _ _ _ H2 HI) as D2. pose proof (POS _ _ HI). lia.
Qed.

Section PORT.
Context {TB : TlsBase}.

Lemma ref_reserved_pos : forall b kk, In (b, kk) ref_reserved -> 0 < kk.
Proof using MSECV. pin_using (fun (MSECV : unit) => tt). ceil_facts. msec_facts.
  intros b kk HI. unfold ref_reserved in HI. cbn in HI.
  destruct HI as [E|[E|[E|[E|[E|[]]]]]]; inversion E; subst; lia.
Qed.

Lemma rpres_except_of_eq (C : Z -> Prop) (m m' : mem) :
  (forall a, 0 <= a < 2^64 -> ~ C a -> m' (wa a) = m (wa a)) -> rpres_except C m m'.
Proof using CEILV MSECV. pin_using (fun (CEILV MSECV : unit) => tt). ceil_facts. msec_facts.
  intros H a Ha Hc. pose proof (H a Ha Hc) as E. split; [exact E|]. unfold wview. rewrite E. tauto.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma mremap_mem_facts (m2 : mem) (old on nn : Z) (x : mremap_ans) (nb : Z) :
  0 < old -> 0 < on -> 0 < nn -> old + on <= alloc_ceiling -> 0 < nb -> nb + nn <= alloc_ceiling ->
  match x with
  | MrErr _ => False
  | MrSame => nb = old
  | MrMoved a => nb = a /\ on < nn /\ (old + on <= a \/ a + nn <= old)
  end ->
  let mA := mremap_mem old on nn x m2 in
     (forall a, 0 <= a < 2^64 -> (a < old \/ old + on <= a) -> (a < nb \/ nb + nn <= a) -> mA (wa a) = m2 (wa a))
  /\ (forall o, 0 <= o < Z.min on nn -> mA (wa (nb + o)) = m2 (wa (old + o)))
  /\ (forall o, on <= o < nn -> mA (wa (nb + o)) = Some (Z_to_bv 8 0)).
Proof using MSECV. pin_using (fun (MSECV : unit) => tt). ceil_facts. msec_facts.
  intros O0 ON0 NN0 OC NB0 NC HX. ceil_facts. cbv zeta.
  destruct x as [e| |na]; [destruct HX| |]; cbn [mremap_mem].
  - subst nb. destruct (Z.ltb_spec0 nn on) as [LT|GE].
    + (* [comment removed for export] *)
      change (Z_to_bv 64 (old + nn)) with (wa (old + nn)).
      split; [| split].
      * intros a Ha H1 H2. apply (unmaps_outside m2 (old + nn) (on - nn)); try lia. rewrite wa_unsigned by lia. lia.
      * intros o Ho. apply (unmaps_outside m2 (old + nn) (on - nn)); try lia. rewrite wa_unsigned by lia. lia.
      * intros o Ho. exfalso. lia.
    + (* [comment removed for export] *)
      change (Z_to_bv 64 (old + on)) with (wa (old + on)).
      split; [| split].
      * intros a Ha H1 H2. apply (zeros_outside m2 (old + on) (nn - on)); try lia. rewrite wa_unsigned by lia. lia.
      * intros o Ho. apply (zeros_outside m2 (old + on) (nn - on)); try lia. rewrite wa_unsigned by lia. lia.
      * intros o Ho. apply (zeros_inside m2 (old + on) (nn - on)); try lia. rewrite wa_unsigned by lia. lia.
  - destruct HX as (-> & LT & DIS).
    change (Z_to_bv 64 old) with (wa old). change (Z_to_bv 64 na) with (wa na). change (Z_to_bv 64 (na + on)) with (wa (na + on)).
    split; [| split].
    + intros a Ha H1 H2. apply (mremap_move_outside m2 old on na nn); try lia; rewrite wa_unsigned by lia; lia.
    + intros o Ho. rewrite (mremap_move_copied m2 old on na nn); try lia; rewrite ?wa_unsigned by lia; [| lia].
      f_equal. f_equal. lia.
    + intros o Ho. apply (mremap_move_tail m2 old on na nn); try lia. rewrite wa_unsigned by lia. lia.
Qed.

Lemma mremap_mem_wr_at (m2 : mem) (old on nn : Z) (x : mremap_ans) (nb : Z) :
  0 < old -> 0 < on -> 0 < nn -> old + on <= alloc_ceiling -> 0 < nb -> nb + nn <= alloc_ceiling ->
  match x with
  | MrErr _ => False
  | MrSame => nb = old
  | MrMoved a => nb = a /\ on < nn /\ (old + on <= a \/ a + nn <= old)
  end ->
  (old + on <= 0x10000 \/ 0x56000 <= old) -> (nb + nn <= 0x10000 \/ 0x56000 <= nb) ->
  wr_at usegs m2 old on ->
  wr_at usegs (mremap_mem old on nn x m2) nb nn.
Proof using MSECV. pin_using (fun (MSECV : unit) => tt). ceil_facts. msec_facts.
  intros O0 ON0 NN0 OC NB0 NC HX OI NI WR.
  destruct (mremap_mem_facts m2 old on nn x nb O0 ON0 NN0 OC NB0 NC HX) as (OUT & PRE & TL).
  ceil_facts. destruct WR as (_ & _ & WR).
  split; [lia|]. split; [lia|]. intros i Hi.
  rewrite ref_wview_overlay by (rewrite wa_unsigned by lia; lia).
  destruct (Z_lt_dec i on) as [LT|GE].
  - rewrite PRE by lia. specialize (WR i ltac:(lia)). rewrite ref_wview_overlay in WR by (rewrite wa_unsigned by lia; lia). exact WR.
  - rewrite TL by lia. discriminate.
Qed.

End PORT.

End WithCeil.
End TwB.
End RF_realloc63M.

(* [comment removed for export] *)
Module RF_am_F.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require AllocBridge__Spec. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.AllocBridge__Spec.AllocBridge.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require Import TlsBase.
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import Tac Image ZBridge SysStep  Arr ITree Nodes Decode.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require Import SFModel.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import ImgSrc3.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require F_malloc_free__MA. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require MallocTree. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require MallocBlocks__MA. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require MallocFacts_A__MA. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require F_am_F__MA. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.F_malloc_free__MA.F_malloc_free OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocTree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocBlocks__MA.MallocModel_B OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocBlocks__MA.F_ntf_A OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocBlocks__MA.F_ntf_B OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocBlocks__MA.MallocKit_B OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocBlocks__MA.MallocKit_B3 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocFacts_A__MA.F_am_A OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocFacts_A__MA.F_am_K OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocFacts_A__MA.F_am_C OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.F_am_F__MA.F_am_F.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require STree Malloc MallocCtrl. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require AllocBridge__Spec. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require MI_Realloc2__Spec. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.STree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Malloc OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MallocCtrl OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.AllocBridge__Spec.AllocBridge OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_Realloc2__Spec.ProgFull.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require RMallocRep__S3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require RF_am_A__S3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require RF_get_meta__S3. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RMallocRep__S3.RMallocRep OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RMallocRep__S3.RMallocTree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RMallocRep__S3.RMallocKit_B OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RMallocRep__S3.RMallocKit_B3 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RF_mm_syscalls__S3.RF_mm_syscalls OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RMallocRep__S3.RF_ntf_A OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RF_am_A__S3.RF_am_A OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RF_get_meta__S3.RF_am_K OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RF_am_A__S3.RF_am_C.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require Import MSecret.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import LiaPin.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac lia ::= pinned_lia.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
Section WithCeil.
Context {CEILV : CEIL} {MSECV : MSEC}.
Section PORT.
Context {PState : Type} {AS : AllocSt PState} {TB : TlsBase}.
Let TLSFACTS := the_tb_facts (TB:=TB).

Lemma ram_disp_fin : forall (sp gp tp t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 x1 : word) F fc
    (m : word -> option byte) (st : mstate) (p : aptr) (r : region),
  rmrep st m -> c_avail_meta_area_count (ctx st) <> 0 -> 0 <= c_avail_meta_area_count (ctx st) < 2^64 ->
  c_avail_meta_areas (ctx st) = Some p -> (s_regions st) !! (fst p) = Some r -> pgal (snd p) -> 0 <= snd p -> snd p + 4096 <= round_up_pg (r_len r) ->
  evt ssegs (fun ms' => ms' = MS (mkR x1 sp gp tp t0 t1 t2 (Z_to_bv 64 4096) (Z_to_bv 64 (conc st p)) (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7
                                   (Z_to_bv 64 RSSP_GUARD) (Z_to_bv 64 RMLOCK) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x1922c) fc None m (seg_rom ssegs))
      (MS (mkR x1 sp gp tp t0 t1 t2 (Z_to_bv 64 4096) s1 a0 a1 a2 a3 a4 a5 a6 a7
               (Z_to_bv 64 RSSP_GUARD) (Z_to_bv 64 RMLOCK) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x1908c) fc None m (seg_rom ssegs)).
Proof using Type. pin_using tt. ceil_facts. msec_facts.
  intros until r. intros MR CNT CR AMA Hr SAL S0 S1.
  pose proof MR as (WF & (C1 & _) & _). unfold ctx_head_cells in C1. rewrite AMA in C1.
  unfold pw in C1. cbn [oconc] in C1. unfold wz in C1.
  pose proof WF as (_ & WR & _). destruct (WR _ _ Hr) as (RB0 & RBAL & RL0 & RBC & _). ceil_facts.
  pose proof (conc_region' st p r Hr) as Cp. pose proof (round_up_pg_ge (r_len r)) as RU.
  assert (AL : Z.land (conc st p) 4095 = 0).
  { rewrite Cp. unfold pgal in SAL. change 4095 with (Z.ones 12). rewrite Z.land_ones by lia. change (2 ^ 12) with 4096.
    clear - RBAL SAL S0 RB0. Z.div_mod_to_equations. lia. }
  assert (AL' : Z.land 4095 (conc st p) = 0) by (rewrite Z.land_comm; exact AL).
  assert (PB : 0 <= conc st p < 2^64) by lia.
  clear RBAL RU RBC RL0 WR.
  unfold RCTX, RMLOCK, RSSP_GUARD in *.
  (* [comment removed for export] *)
  st1. st1.
  assert (CF : negb (bv_eqb (Z_to_bv 64 (c_avail_meta_area_count (ctx st))) (Z_to_bv 64 0)) = true)
    by (unfold bv_eqb; rewrite !unsigned_lit by lia; apply Bool.negb_true_iff; apply Z.eqb_neq; exact CNT).
  rewrite CF.
  (* [comment removed for export] *)
  st1. apply Bool.negb_true_iff in CF. rewrite CF. clear CF.
  st1. st1.
  (* [comment removed for export] *)
  st1. st1. rewrite ?AL, ?AL'. st1.
  change (bv_eqb (Z_to_bv 64 0) (Z_to_bv 64 0)) with true. cbv iota.
  apply evt_done. reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma ram_to_mprotect : forall (sp gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 x1 : word) F fc
    (m : word -> option byte) (P : Z),
  evt ssegs (fun ms' => ms' = MS (mkR (Z_to_bv 64 0x1923c) sp gp tp t0 t1 t2 (Z_to_bv 64 4096) (Z_to_bv 64 P)
                                   (Z_to_bv 64 P) (Z_to_bv 64 4096) (Z_to_bv 64 3) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                F (Z_to_bv 64 rmprotect_entry) fc None m (seg_rom ssegs))
      (MS (mkR x1 sp gp tp t0 t1 t2 (Z_to_bv 64 4096) (Z_to_bv 64 P) a0 a1 a2 a3 a4 a5 a6 a7
               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x1922c) fc None m (seg_rom ssegs)).
Proof using CEILV MSECV. pin_using (fun (CEILV MSECV : unit) => tt). ceil_facts. msec_facts.
  intros.
  (* [comment removed for export] *)
  st1. st1. st1. st1.
  apply evt_done. unfold rmprotect_entry. reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma ram_mp_ok0 : forall (sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 x1 : word) F fc
    (m : word -> option byte),
  evt ssegs (fun ms' => ms' = MS (mkR x1 sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7
                                   s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x1919c) fc None m (seg_rom ssegs))
      (MS (mkR x1 sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7
               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x1923c) fc None m (seg_rom ssegs)).
Proof using CEILV MSECV. pin_using (fun (CEILV MSECV : unit) => tt). ceil_facts. msec_facts.
  intros.
  st1. rewrite bv_eqb_refl. cbv iota.
  apply evt_done. reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma ram_mp_fail : forall (sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 x1 raw s0o s1o s2o s3o s4o : word) F fc
    (m0 m : word -> option byte) (junk : list byte) (lo e : Z) (st : mstate),
  rmrep st m -> mem_inv ssegs m -> tp = Z_to_bv 64 RATP ->
  rw_cells ssegs m (errno_addr tp) [C4 (Z_to_bv 64 e)] -> 1 <= e <= 4095 -> e <> 38 ->
  rpres_except (ram_fp st lo (bv_unsigned sp)) m0 m -> wmono ssegs m0 m ->
  rw_cells ssegs m (bv_unsigned sp + -64) (ram_frame junk s4o s3o s2o s1o s0o raw) ->
  stk ssegs m lo (bv_unsigned sp + -64) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - 64 ->
  evt ssegs (fun ms' => ram_ret_post raw sp gp tp s0o s1o s2o s3o s4o s5 s6 s7 s8 s9 s10 s11 F fc lo st m0 st (Z_to_bv 64 0) ms'
                        /\ rw_cells ssegs (ms_mem ms') (errno_addr tp) [C4 (Z_to_bv 64 e)])
      (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (-1)) a1 a2 a3 a4 a5 a6 a7
               (Z_to_bv 64 RSSP_GUARD) (Z_to_bv 64 RMLOCK) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x1923c) fc None m (seg_rom ssegs)).
Proof using Type. pin_using tt. ceil_facts. msec_facts.
  intros until st. intros MR MI TP ERR ER E38 PE0 WM0 FR ST LO LOLE.
  pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  pose proof (munch_refl [(bv_unsigned sp - 64, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl ssegs m) as WM.
  pose proof MR as (_ & _ & (_ & _ & _ & _ & GUARD) & _).
  (* [comment removed for export] *)
  pose proof (rerrno_addr tp TP) as ETP. assert (TPR : bv_unsigned tp = RATP) by (rewrite TP; apply RATP_unsigned). pose proof the_tb_facts as TBF.
  change (Z_to_bv 64 e) with (wz e) in ERR.
  unfold RCTX, RMLOCK, RSSP_GUARD, ram_frame in *; ceil_facts.
  (* [comment removed for export] *)
  st1. change (bv_eqb (Z_to_bv 64 (-1)) (Z_to_bv 64 0)) with false. cbv iota.
  (* [comment removed for export] *)
  st1. st1. st1. st1.
  (* [comment removed for export] *)
  st1. rewrite sx32_wz by lia. st1. st1.
  assert (CF : bv_eqb (wz e) (Z_to_bv 64 38) = false)
    by (unfold bv_eqb, wz; rewrite !unsigned_lit by lia; apply Z.eqb_neq; exact E38).
  rewrite CF; clear CF.
  (* [comment removed for export] *)
  st1. st1. st1. st1. st1. if_cases K; zify_cond K. { exfalso. apply K. reflexivity. }
  (* [comment removed for export] *)
  st1. st1. st1. st1. st1. st1. st1. st1.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) => assert (MRX : rmrep st mX) end.
  { eapply rmrep_transport_high; [exact MR| exact MU| exact WM|]. intros l h [E|[]]; inversion E; subst; ceil_facts; lia. }
  release_frame FR ST (bv_unsigned sp).
  apply evt_done. split.
  - unfold ram_ret_post. do 15 eexists. split; [reflexivity|].
    split.
    { eapply rpres_except_trans; [exact PE0|].
      apply (rpres_except_of_munch_cov (ram_fp st lo (bv_unsigned sp))) in MU; [exact MU|exact WM|].
      cbn [ivs_covered]. split; [|exact I]. intros x Hx. apply ram_fp_stack. lia. }
    split; [eapply wmono_trans; [exact WM0| exact WM]|]. split; [assumption|]. split; [exact ST|]. exact MRX.
  - cbn [ms_mem]. change (wz e) with (Z_to_bv 64 e) in ERR. exact ERR.
Qed.

End PORT.

End WithCeil.

(* [comment removed for export] *)
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require ImgTgtUbsan SecDiet.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require TlsBaseU.
Module TwB.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.AllocBridge__Spec.AllocBridge.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.TlsBaseU.
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Tac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Image OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ZBridge OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.SysStep OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Arr OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ITree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Nodes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Decode.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.SFModel.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ImgTgtUbsan.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.F_malloc_free__MA.F_malloc_free OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocTree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocBlocks__MA.MallocModel_B OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocBlocks__MA.F_ntf_A OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocBlocks__MA.F_ntf_B OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocBlocks__MA.MallocKit_B OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocBlocks__MA.MallocKit_B3 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocFacts_A__MA.F_am_A OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocFacts_A__MA.F_am_K OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocFacts_A__MA.F_am_C OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.F_am_F__MA.F_am_F.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.STree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Malloc OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MallocCtrl OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.AllocBridge__Spec.AllocBridge OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_Realloc2__Spec.ProgFull.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RMallocRep__S3.RMallocRep.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RMallocRep__S3.RMallocTree.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RMallocRep__S3.RMallocKit_B.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RMallocRep__S3.RMallocKit_B3.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RF_mm_syscalls__S3.RF_mm_syscalls.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RMallocRep__S3.RF_ntf_A.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RF_am_A__S3.RF_am_A.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RF_get_meta__S3.RF_am_K.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RF_am_A__S3.RF_am_C.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MSecret.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.LiaPin.
(* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac lia ::= pinned_lia.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
Section WithCeil.
Context {CEILV : CEIL} {MSECV : MSEC}.
Section PORT.
Context {PState : Type} {AS : AllocSt PState} {TB : TlsBase}.
Let TLSFACTS := the_tb_facts (TB:=TB).

Definition ram_disp_fin__stmt : Prop := forall (sp gp tp t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 x1 : word) F fc
    (m : word -> option byte) (st : mstate) (p : aptr) (r : region),
  rmrep st m -> c_avail_meta_area_count (ctx st) <> 0 -> 0 <= c_avail_meta_area_count (ctx st) < 2^64 ->
  c_avail_meta_areas (ctx st) = Some p -> (s_regions st) !! (fst p) = Some r -> pgal (snd p) -> 0 <= snd p -> snd p + 4096 <= round_up_pg (r_len r) ->
  evt usegs (fun ms' => ms' = MS (mkR x1 sp gp tp t0 t1 t2 (Z_to_bv 64 4096) (Z_to_bv 64 (conc st p)) (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7
                                   (Z_to_bv 64 RSSP_GUARD) (Z_to_bv 64 RMLOCK) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x199ec) fc None m (seg_rom usegs))
      (MS (mkR x1 sp gp tp t0 t1 t2 (Z_to_bv 64 4096) s1 a0 a1 a2 a3 a4 a5 a6 a7
               (Z_to_bv 64 RSSP_GUARD) (Z_to_bv 64 RMLOCK) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x1984c) fc None m (seg_rom usegs)).
Section Sz1.
Variables sp gp tp t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 x1 F fc m st p r : ltac2:(SecDiet.SzSec.tyM 'ram_disp_fin__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @sp).
Lemma ram_disp_fin__body : ltac2:(SecDiet.SzSec.bodyP 'ram_disp_fin__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
Proof using Type. pin_using tt. ceil_facts. msec_facts.
 intros MR CNT CR AMA Hr SAL S0 S1.
  pose proof MR as (WF & (C1 & _) & _). unfold ctx_head_cells in C1. rewrite AMA in C1.
  unfold pw in C1. cbn [oconc] in C1. unfold wz in C1.
  pose proof WF as (_ & WR & _). destruct (WR _ _ Hr) as (RB0 & RBAL & RL0 & RBC & _). ceil_facts.
  pose proof (conc_region' st p r Hr) as Cp. pose proof (round_up_pg_ge (r_len r)) as RU.
  assert (AL : Z.land (conc st p) 4095 = 0).
  { rewrite Cp. unfold pgal in SAL. change 4095 with (Z.ones 12). rewrite Z.land_ones by lia. change (2 ^ 12) with 4096.
    clear - RBAL SAL S0 RB0. Z.div_mod_to_equations. lia. }
  assert (AL' : Z.land 4095 (conc st p) = 0) by (rewrite Z.land_comm; exact AL).
  assert (PB : 0 <= conc st p < 2^64) by lia.
  clear RBAL RU RBC RL0 WR.
  unfold RCTX, RMLOCK, RSSP_GUARD in *.
  (* [comment removed for export] *)
  st1. st1.
  assert (CF : negb (bv_eqb (Z_to_bv 64 (c_avail_meta_area_count (ctx st))) (Z_to_bv 64 0)) = true)
    by (unfold bv_eqb; rewrite !unsigned_lit by lia; apply Bool.negb_true_iff; apply Z.eqb_neq; exact CNT).
  rewrite CF.
  (* [comment removed for export] *)
  st1. apply Bool.negb_true_iff in CF. rewrite CF. clear CF.
  st1. st1.
  (* [comment removed for export] *)
  st1. st1. rewrite ?AL, ?AL'. st1.
  change (bv_eqb (Z_to_bv 64 0) (Z_to_bv 64 0)) with true. cbv iota.
  apply evt_done. reflexivity.
Qed.
End Sz1.
Lemma ram_disp_fin : ltac:(let t := eval cbv delta [ram_disp_fin__stmt] in ram_disp_fin__stmt in exact t).
Proof using Type. intros sp gp tp t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 x1 F fc m st p r. ltac2:(SecDiet.SzSec.closeP 'ram_disp_fin__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma ram_to_mprotect : forall (sp gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 x1 : word) F fc
    (m : word -> option byte) (P : Z),
  evt usegs (fun ms' => ms' = MS (mkR (Z_to_bv 64 0x199fc) sp gp tp t0 t1 t2 (Z_to_bv 64 4096) (Z_to_bv 64 P)
                                   (Z_to_bv 64 P) (Z_to_bv 64 4096) (Z_to_bv 64 3) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                F (Z_to_bv 64 rmprotect_entry) fc None m (seg_rom usegs))
      (MS (mkR x1 sp gp tp t0 t1 t2 (Z_to_bv 64 4096) (Z_to_bv 64 P) a0 a1 a2 a3 a4 a5 a6 a7
               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x199ec) fc None m (seg_rom usegs)).
Proof using CEILV MSECV. pin_using (fun (CEILV MSECV : unit) => tt). ceil_facts. msec_facts.
  intros.
  (* [comment removed for export] *)
  st1. st1. st1. st1.
  apply evt_done. unfold rmprotect_entry. reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma ram_mp_ok0 : forall (sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 x1 : word) F fc
    (m : word -> option byte),
  evt usegs (fun ms' => ms' = MS (mkR x1 sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7
                                   s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x1995c) fc None m (seg_rom usegs))
      (MS (mkR x1 sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7
               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x199fc) fc None m (seg_rom usegs)).
Proof using CEILV MSECV. pin_using (fun (CEILV MSECV : unit) => tt). ceil_facts. msec_facts.
  intros.
  st1. rewrite bv_eqb_refl. cbv iota.
  apply evt_done. reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition ram_mp_fail__stmt : Prop := forall (sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 x1 raw s0o s1o s2o s3o s4o : word) F fc
    (m0 m : word -> option byte) (junk : list byte) (lo e : Z) (st : mstate),
  rmrep st m -> mem_inv usegs m -> tp = Z_to_bv 64 RATP ->
  rw_cells usegs m (errno_addr tp) [C4 (Z_to_bv 64 e)] -> 1 <= e <= 4095 -> e <> 38 ->
  rpres_except (ram_fp st lo (bv_unsigned sp)) m0 m -> wmono usegs m0 m ->
  rw_cells usegs m (bv_unsigned sp + -64) (ram_frame junk s4o s3o s2o s1o s0o raw) ->
  stk usegs m lo (bv_unsigned sp + -64) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - 64 ->
  evt usegs (fun ms' => ram_ret_post raw sp gp tp s0o s1o s2o s3o s4o s5 s6 s7 s8 s9 s10 s11 F fc lo st m0 st (Z_to_bv 64 0) ms'
                        /\ rw_cells usegs (ms_mem ms') (errno_addr tp) [C4 (Z_to_bv 64 e)])
      (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (-1)) a1 a2 a3 a4 a5 a6 a7
               (Z_to_bv 64 RSSP_GUARD) (Z_to_bv 64 RMLOCK) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x199fc) fc None m (seg_rom usegs)).
Section Sz4.
Variables sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 x1 raw s0o s1o s2o s3o s4o F fc m0 m junk lo e st : ltac2:(SecDiet.SzSec.tyM 'ram_mp_fail__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @sp).
Lemma ram_mp_fail__body : ltac2:(SecDiet.SzSec.bodyP 'ram_mp_fail__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
Proof using Type. pin_using tt. ceil_facts. msec_facts.
 intros MR MI TP ERR ER E38 PE0 WM0 FR ST LO LOLE.
  pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  pose proof (munch_refl [(bv_unsigned sp - 64, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl usegs m) as WM.
  pose proof MR as (_ & _ & (_ & _ & _ & _ & GUARD) & _).
  (* [comment removed for export] *)
  pose proof (rerrno_addr tp TP) as ETP. assert (TPR : bv_unsigned tp = RATP) by (rewrite TP; apply RATP_unsigned). pose proof the_tb_facts as TBF.
  change (Z_to_bv 64 e) with (wz e) in ERR.
  unfold RCTX, RMLOCK, RSSP_GUARD, ram_frame in *; ceil_facts.
  (* [comment removed for export] *)
  st1. change (bv_eqb (Z_to_bv 64 (-1)) (Z_to_bv 64 0)) with false. cbv iota.
  (* [comment removed for export] *)
  st1. st1. st1. st1.
  (* [comment removed for export] *)
  st1. rewrite sx32_wz by lia. st1. st1.
  assert (CF : bv_eqb (wz e) (Z_to_bv 64 38) = false)
    by (unfold bv_eqb, wz; rewrite !unsigned_lit by lia; apply Z.eqb_neq; exact E38).
  rewrite CF; clear CF.
  (* [comment removed for export] *)
  st1. st1. st1. st1. st1. if_cases K; zify_cond K. { exfalso. apply K. reflexivity. }
  (* [comment removed for export] *)
  st1. st1. st1. st1. st1. st1. st1. st1.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) => assert (MRX : rmrep st mX) end.
  { eapply rmrep_transport_high; [exact MR| exact MU| exact WM|]. intros l h [E|[]]; inversion E; subst; ceil_facts; lia. }
  release_frame FR ST (bv_unsigned sp).
  apply evt_done. split.
  - unfold ram_ret_post. do 15 eexists. split; [reflexivity|].
    split.
    { eapply rpres_except_trans; [exact PE0|].
      apply (rpres_except_of_munch_cov (ram_fp st lo (bv_unsigned sp))) in MU; [exact MU|exact WM|].
      cbn [ivs_covered]. split; [|exact I]. intros x Hx. apply ram_fp_stack. lia. }
    split; [eapply wmono_trans; [exact WM0| exact WM]|]. split; [assumption|]. split; [exact ST|]. exact MRX.
  - cbn [ms_mem]. change (wz e) with (Z_to_bv 64 e) in ERR. exact ERR.
Qed.
End Sz4.
Lemma ram_mp_fail : ltac:(let t := eval cbv delta [ram_mp_fail__stmt] in ram_mp_fail__stmt in exact t).
Proof using Type. intros sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 x1 raw s0o s1o s2o s3o s4o F fc m0 m junk lo e st. ltac2:(SecDiet.SzSec.closeP 'ram_mp_fail__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.

End PORT.

End WithCeil.
End TwB.
End RF_am_F.

(* [comment removed for export] *)
Module RF_am_G.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require AllocBridge__Spec. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.AllocBridge__Spec.AllocBridge.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require Import TlsBase.
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import Tac Image ZBridge SysStep  Arr ITree Nodes Decode.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require Import SFModel.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import ImgSrc3.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require F_malloc_free__MA. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require MallocTree. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require MallocBlocks__MA. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require MallocFacts_A__MA. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require F_am_F__MA. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.F_malloc_free__MA.F_malloc_free OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocTree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocBlocks__MA.MallocModel_B OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocBlocks__MA.F_ntf_A OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocBlocks__MA.F_ntf_B OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocBlocks__MA.MallocKit_B OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocBlocks__MA.MallocKit_B3 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocFacts_A__MA.F_am_A OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocFacts_A__MA.F_am_K OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocFacts_A__MA.F_am_C OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.F_am_F__MA.F_am_G.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require STree Malloc MallocCtrl. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require AllocBridge__Spec. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require MI_Realloc2__Spec. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.STree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Malloc OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MallocCtrl OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.AllocBridge__Spec.AllocBridge OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_Realloc2__Spec.ProgFull.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require RMallocRep__S3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require RF_am_A__S3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require RF_get_meta__S3. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RMallocRep__S3.RMallocRep OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RMallocRep__S3.RMallocTree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RMallocRep__S3.RMallocKit_B OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RMallocRep__S3.RMallocKit_B3 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RF_mm_syscalls__S3.RF_mm_syscalls OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RMallocRep__S3.RF_ntf_A OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RF_am_A__S3.RF_am_A OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RF_get_meta__S3.RF_am_K OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RF_am_A__S3.RF_am_C.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require Import MSecret.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import LiaPin.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac lia ::= pinned_lia.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section WithCeil.
Context {CEILV : CEIL} {MSECV : MSEC}.
Section PORT.
Context {PState : Type} {AS : AllocSt PState} {TB : TlsBase}.
Let TLSFACTS := the_tb_facts (TB:=TB).

Lemma ram_disp_dead : forall (sp gp tp t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 x1 : word) F fc
    (m : word -> option byte) (st : mstate),
  rmrep st m -> c_avail_meta_area_count (ctx st) = 0 -> c_brk (ctx st) = BrkDead ->
  evt ssegs (fun ms' => ms' = MS (mkR x1 sp gp tp t0 t1 t2 (Z_to_bv 64 4096) (Z_to_bv 64 (2^64 - 1)) (Z_to_bv 64 0) (Z_to_bv 64 (-1)) a2 a3 a4 a5 a6 a7
                                   (Z_to_bv 64 RSSP_GUARD) (Z_to_bv 64 RMLOCK) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x1913c) fc None m (seg_rom ssegs))
      (MS (mkR x1 sp gp tp t0 t1 t2 (Z_to_bv 64 4096) s1 a0 a1 a2 a3 a4 a5 a6 a7
               (Z_to_bv 64 RSSP_GUARD) (Z_to_bv 64 RMLOCK) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x1908c) fc None m (seg_rom ssegs)).
Proof using Type. pin_using tt. ceil_facts. msec_facts.
  intros until st. intros MR CNT BRK.
  pose proof MR as (WF & (C1 & _ & _ & _ & _ & C6) & _). unfold ctx_head_cells in C1. rewrite CNT in C1.
  unfold ctx_tail_cells, brk_word in C6. rewrite BRK in C6.
  unfold pw in C1. cbn [oconc] in C1. unfold wz in C1, C6.
  unfold RCTX, RMLOCK, RSSP_GUARD in *. change (343456 + 912) with 344368 in C6.
  (* [comment removed for export] *)
  st1. st1. rewrite bv_eqb_refl. cbn [negb]. cbv iota.
  (* [comment removed for export] *)
  st1. st1. st1.
  change (bv_eqb (Z_to_bv 64 (2 ^ 64 - 1)) (Z_to_bv 64 (-1))) with true. cbv iota.
  (* [comment removed for export] *)
  st1. rewrite bv_eqb_refl. cbv iota.
  apply evt_done. reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma ram_to_mmap : forall (sp gp tp t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 x1 : word) F fc
    (m : word -> option byte) (st : mstate),
  rmrep st m -> 0 <= c_meta_alloc_shift (ctx st) <= 40 ->
  let n := Z.shiftl 2 (c_meta_alloc_shift (ctx st)) in
  evt ssegs (fun ms' => ms' = MS (mkR (Z_to_bv 64 0x19168) sp gp tp t0 t1 t2 (Z_to_bv 64 4096) (Z_to_bv 64 n)
                                   (Z_to_bv 64 0) (Z_to_bv 64 (n * 4096)) (Z_to_bv 64 0) (Z_to_bv 64 34) (Z_to_bv 64 (-1)) (Z_to_bv 64 0) a6 a7
                                   (Z_to_bv 64 RSSP_GUARD) (Z_to_bv 64 RMLOCK) (Z_to_bv 64 (-1)) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                F (Z_to_bv 64 rmmap_entry) fc None m (seg_rom ssegs))
      (MS (mkR x1 sp gp tp t0 t1 t2 (Z_to_bv 64 4096) s1 a0 a1 a2 a3 a4 a5 a6 a7
               (Z_to_bv 64 RSSP_GUARD) (Z_to_bv 64 RMLOCK) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x1913c) fc None m (seg_rom ssegs)).
Proof using Type. pin_using tt. ceil_facts. msec_facts.
  intros until st. intros MR SH n.
  pose proof MR as (WF & (C1 & _) & _). unfold ctx_head_cells in C1. unfold pw in C1. cbn [oconc] in C1. unfold wz in C1.
  unfold RCTX, RMLOCK, RSSP_GUARD in *.
  (* [comment removed for export] *)
  st1. st1. st1.
  rewrite (Z.mod_small (c_meta_alloc_shift (ctx st)) 64) by lia.
  assert (NR : 0 < Z.shiftl 2 (c_meta_alloc_shift (ctx st)) <= 2^41).
  { rewrite Z.shiftl_mul_pow2 by lia. split; [apply Z.mul_pos_pos; [lia| apply Z.pow_pos_nonneg; lia]|].
    change (2^41) with (2 * 2^40). apply Z.mul_le_mono_nonneg_l; [lia|]. apply Z.pow_le_mono_r; lia. }
  (* [comment removed for export] *)
  st1. st1. st1. st1. st1. st1. st1. st1.
  apply evt_done. unfold rmmap_entry. subst n. reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma ram_mm_fail : forall (sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 x1 raw s0o s1o s2o s3o s4o : word) F fc
    (m0 m : word -> option byte) (junk : list byte) (lo : Z) (st : mstate),
  rmrep st m -> mem_inv ssegs m ->
  rpres_except (ram_fp st lo (bv_unsigned sp)) m0 m -> wmono ssegs m0 m ->
  rw_cells ssegs m (bv_unsigned sp + -64) (ram_frame junk s4o s3o s2o s1o s0o raw) ->
  stk ssegs m lo (bv_unsigned sp + -64) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - 64 ->
  evt ssegs (ram_ret_post raw sp gp tp s0o s1o s2o s3o s4o s5 s6 s7 s8 s9 s10 s11 F fc lo st m0 st (Z_to_bv 64 0))
      (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (-1)) a1 a2 a3 a4 a5 a6 a7
               (Z_to_bv 64 RSSP_GUARD) (Z_to_bv 64 RMLOCK) (Z_to_bv 64 (-1)) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x19168) fc None m (seg_rom ssegs)).
Proof using Type. pin_using tt. ceil_facts. msec_facts.
  intros until st. intros MR MI PE0 WM0 FR ST LO LOLE.
  pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  pose proof (munch_refl [(bv_unsigned sp - 64, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl ssegs m) as WM.
  pose proof MR as (_ & _ & (_ & _ & _ & _ & GUARD) & _).
  unfold RCTX, RMLOCK, RSSP_GUARD, ram_frame in *; ceil_facts.
  (* [comment removed for export] *)
  st1. rewrite bv_eqb_refl. cbv iota. st1. st1. st1. st1. st1. if_cases K; zify_cond K. { exfalso. apply K. reflexivity. }
  (* [comment removed for export] *)
  st1. st1. st1. st1. st1. st1. st1. st1.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) => assert (MRX : rmrep st mX) end.
  { eapply rmrep_transport_high; [exact MR| exact MU| exact WM|]. intros l h [E|[]]; inversion E; subst; ceil_facts; lia. }
  release_frame FR ST (bv_unsigned sp).
  apply evt_done. unfold ram_ret_post. do 15 eexists. split; [reflexivity|].
  split.
  { eapply rpres_except_trans; [exact PE0|].
    apply (rpres_except_of_munch_cov (ram_fp st lo (bv_unsigned sp))) in MU; [exact MU|exact WM|].
    cbn [ivs_covered]. split; [|exact I]. intros x Hx. apply ram_fp_stack. lia. }
  split; [eapply wmono_trans; [exact WM0| exact WM]|]. split; [assumption|]. split; [exact ST|]. exact MRX.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma ram_mm_ok : forall (sp gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 x1 raw s0o s1o s2o s3o s4o : word) F fc
    (m0 m : word -> option byte) (junk : list byte) (lo x n : Z) (st0 st : mstate) (rid : N) (r : region),
  rmrep st m -> mem_inv ssegs m -> (forall a, ram_fp st0 lo (bv_unsigned sp) a -> ram_fp st lo (bv_unsigned sp) a) ->
  (s_regions st) !! rid = Some r -> r_base r = x -> x mod 4096 = 0 -> 0 < x -> x + 8192 <= alloc_ceiling -> 1 <= n < 2^62 ->
  0 <= c_meta_alloc_shift (ctx st) < 2^62 ->
  rpres_except (ram_fp st0 lo (bv_unsigned sp)) m0 m -> wmono ssegs m0 m ->
  rw_cells ssegs m (bv_unsigned sp + -64) (ram_frame junk s4o s3o s2o s1o s0o raw) ->
  stk ssegs m lo (bv_unsigned sp + -64) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - 64 ->
  evt ssegs (fun ms' => exists m',
        ms' = MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp t0 t1 t2 (Z_to_bv 64 4096) (Z_to_bv 64 (x + 4096)) (Z_to_bv 64 0)
                      (Z_to_bv 64 (c_meta_alloc_shift (ctx st) + 1)) (Z_to_bv 64 (n - 1)) a3 a4 a5 a6 a7
                      (Z_to_bv 64 RSSP_GUARD) (Z_to_bv 64 RMLOCK) (Z_to_bv 64 (-1)) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x1922c) fc None m' (seg_rom ssegs)
        /\ rpres_except (ram_fp st lo (bv_unsigned sp)) m0 m' /\ wmono ssegs m0 m' /\ mem_inv ssegs m'
        /\ rw_cells ssegs m' (bv_unsigned sp + -64) (ram_frame junk s4o s3o s2o s1o s0o raw)
        /\ stk ssegs m' lo (bv_unsigned sp + -64)
        /\ rmrep (mm_ok_st st rid n) m')
      (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp t0 t1 t2 (Z_to_bv 64 4096) (Z_to_bv 64 n) (Z_to_bv 64 x) a1 a2 a3 a4 a5 a6 a7
               (Z_to_bv 64 RSSP_GUARD) (Z_to_bv 64 RMLOCK) (Z_to_bv 64 (-1)) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x19168) fc None m (seg_rom ssegs)).
Proof using Type. pin_using tt. ceil_facts. msec_facts.
  intros until r. intros MR MI FP0 Hr RB XAL X0 XC NR SH PE0 WM0 FR ST LO LOLE.
  pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  pose proof (munch_refl [(bv_unsigned sp - 64, bv_unsigned sp); (RCTX, RCTX + 928)]%Z m) as MU. pose proof (wmono_refl ssegs m) as WM.
  pose proof MR as (WF & (C1 & _) & _). unfold ctx_head_cells in C1. unfold pw in C1. cbn [oconc] in C1. unfold wz in C1.
  assert (AL : Z.land (x + 4096) 4095 = 0).
  { change 4095 with (Z.ones 12). rewrite Z.land_ones by lia. change (2 ^ 12) with 4096. clear - XAL X0. Z.div_mod_to_equations. lia. }
  assert (AL' : Z.land 4095 (x + 4096) = 0) by (rewrite Z.land_comm; exact AL).
  change (x mod 4096 = 0) with (pgal x) in XAL.
  unfold RCTX, RMLOCK, RSSP_GUARD, ram_frame in *; ceil_facts.
  (* [comment removed for export] *)
  st1.
  assert (CF : bv_eqb (Z_to_bv 64 x) (Z_to_bv 64 (-1)) = false)
    by (unfold bv_eqb; rewrite (unsigned_lit x) by lia; change (bv_unsigned (Z_to_bv 64 (-1))) with (2^64 - 1)%Z; apply Z.eqb_neq; lia).
  rewrite CF; clear CF.
  (* [comment removed for export] *)
  st1. st1. st1. st1. st1. st1.
  replace ((n + -1) * 1) with (n - 1) by lia.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
    pose proof (munch_refl [(RCTX + 40, RCTX + 56); (RCTX + 72, RCTX + 80)]%Z mX) as MUc; pose proof (wmono_refl ssegs mX) as WMc end.
  unfold RCTX in MUc.
  (* [comment removed for export] *)
  st1. st1. st1.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) => assert (MR2 : rmrep (mm_ok_st st rid n) mX) end.
  { eapply (rmrep_ctx_frameW st _ _ _ _ MR MUc WMc); try reflexivity.
    - intros lo' hi' [E|[E|[]]]; inversion E; subst; unfold RCTX; lia.
    - left. unfold ctx_head_cells, RCTX. cbn [ctx mm_ok_st upd_ctx s_ctx set_meta_alloc_shift set_avail_meta_area_count set_avail_meta_areas c_secret c_init_done c_mmap_counter c_free_meta_head c_avail_meta
            c_avail_meta_count c_avail_meta_area_count c_meta_alloc_shift c_meta_area_head c_meta_area_tail c_avail_meta_areas].
      change (pw (mm_ok_st st rid n) ?q) with (pw st q). unfold pw. cbn [oconc]. change (conc (mm_ok_st st rid n) ?q) with (conc st q).
      rewrite (conc_region' st (rid, 4096) r Hr). cbn [snd]. rewrite RB. unfold wz.
      lazymatch goal with H : rw_cells ssegs ?mX 343456 _ |- _ => exact H end.
    - right. split; [reflexivity|]. intros lo' hi' [E|[E|[]]]; inversion E; subst; unfold RCTX; lia.
    - right. split; [reflexivity|]. intros lo' hi' [E|[E|[]]]; inversion E; subst; unfold RCTX; lia.
    - right. split; [reflexivity|]. intros lo' hi' [E|[E|[]]]; inversion E; subst; unfold RCTX; lia.
    - right. split; [reflexivity|]. intros lo' hi' [E|[E|[]]]; inversion E; subst; unfold RCTX; lia.
    - right. split; [reflexivity|]. intros lo' hi' [E|[E|[]]]; inversion E; subst; unfold RCTX; lia. }
  clear MUc WMc.
  (* [comment removed for export] *)
  st1. st1. rewrite ?AL, ?AL'. st1. rewrite bv_eqb_refl. cbv iota.
  apply evt_done. eexists. split; [reflexivity|].
  split.
  { eapply rpres_except_trans; [eapply rpres_except_mono; [exact PE0| exact FP0]|].
    apply (rpres_except_of_munch_cov (ram_fp st lo (bv_unsigned sp))) in MU; [exact MU|exact WM|].
    cbn [ivs_covered]. split; [|split; [|exact I]].
    - intros y Hy. apply ram_fp_stack. lia.
    - intros y Hy. apply ram_fp_ctx. unfold RCTX. lia. }
  split; [first [exact WM0 | eapply wmono_trans; [exact WM0| exact WM]]|]. split; [assumption|]. split; [exact FR|]. split; [exact ST|]. exact MR2.
Qed.

End PORT.

End WithCeil.

(* [comment removed for export] *)
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require ImgTgtUbsan SecDiet.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require TlsBaseU.
Module TwB.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.AllocBridge__Spec.AllocBridge.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.TlsBaseU.
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Tac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Image OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ZBridge OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.SysStep OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Arr OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ITree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Nodes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Decode.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.SFModel.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ImgTgtUbsan.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.F_malloc_free__MA.F_malloc_free OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocTree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocBlocks__MA.MallocModel_B OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocBlocks__MA.F_ntf_A OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocBlocks__MA.F_ntf_B OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocBlocks__MA.MallocKit_B OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocBlocks__MA.MallocKit_B3 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocFacts_A__MA.F_am_A OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocFacts_A__MA.F_am_K OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocFacts_A__MA.F_am_C OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.F_am_F__MA.F_am_G.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.STree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Malloc OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MallocCtrl OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.AllocBridge__Spec.AllocBridge OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_Realloc2__Spec.ProgFull.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RMallocRep__S3.RMallocRep.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RMallocRep__S3.RMallocTree.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RMallocRep__S3.RMallocKit_B.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RMallocRep__S3.RMallocKit_B3.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RF_mm_syscalls__S3.RF_mm_syscalls.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RMallocRep__S3.RF_ntf_A.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RF_am_A__S3.RF_am_A.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RF_get_meta__S3.RF_am_K.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RF_am_A__S3.RF_am_C.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MSecret.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.LiaPin.
(* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac lia ::= pinned_lia.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section WithCeil.
Context {CEILV : CEIL} {MSECV : MSEC}.
Section PORT.
Context {PState : Type} {AS : AllocSt PState} {TB : TlsBase}.
Let TLSFACTS := the_tb_facts (TB:=TB).

Definition ram_disp_dead__stmt : Prop := forall (sp gp tp t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 x1 : word) F fc
    (m : word -> option byte) (st : mstate),
  rmrep st m -> c_avail_meta_area_count (ctx st) = 0 -> c_brk (ctx st) = BrkDead ->
  evt usegs (fun ms' => ms' = MS (mkR x1 sp gp tp t0 t1 t2 (Z_to_bv 64 4096) (Z_to_bv 64 (2^64 - 1)) (Z_to_bv 64 0) (Z_to_bv 64 (-1)) a2 a3 a4 a5 a6 a7
                                   (Z_to_bv 64 RSSP_GUARD) (Z_to_bv 64 RMLOCK) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x198fc) fc None m (seg_rom usegs))
      (MS (mkR x1 sp gp tp t0 t1 t2 (Z_to_bv 64 4096) s1 a0 a1 a2 a3 a4 a5 a6 a7
               (Z_to_bv 64 RSSP_GUARD) (Z_to_bv 64 RMLOCK) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x1984c) fc None m (seg_rom usegs)).
Section Sz1.
Variables sp gp tp t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 x1 F fc m st : ltac2:(SecDiet.SzSec.tyM 'ram_disp_dead__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @sp).
Lemma ram_disp_dead__body : ltac2:(SecDiet.SzSec.bodyP 'ram_disp_dead__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
Proof using Type. pin_using tt. ceil_facts. msec_facts.
 intros MR CNT BRK.
  pose proof MR as (WF & (C1 & _ & _ & _ & _ & C6) & _). unfold ctx_head_cells in C1. rewrite CNT in C1.
  unfold ctx_tail_cells, brk_word in C6. rewrite BRK in C6.
  unfold pw in C1. cbn [oconc] in C1. unfold wz in C1, C6.
  unfold RCTX, RMLOCK, RSSP_GUARD in *. change (345440 + 912) with 346352 in C6.
  (* [comment removed for export] *)
  st1. st1. rewrite bv_eqb_refl. cbn [negb]. cbv iota.
  (* [comment removed for export] *)
  st1. st1. st1.
  change (bv_eqb (Z_to_bv 64 (2 ^ 64 - 1)) (Z_to_bv 64 (-1))) with true. cbv iota.
  (* [comment removed for export] *)
  st1. rewrite bv_eqb_refl. cbv iota.
  apply evt_done. reflexivity.
Qed.
End Sz1.
Lemma ram_disp_dead : ltac:(let t := eval cbv delta [ram_disp_dead__stmt] in ram_disp_dead__stmt in exact t).
Proof using Type. intros sp gp tp t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 x1 F fc m st. ltac2:(SecDiet.SzSec.closeP 'ram_disp_dead__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition ram_to_mmap__stmt : Prop := forall (sp gp tp t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 x1 : word) F fc
    (m : word -> option byte) (st : mstate),
  rmrep st m -> 0 <= c_meta_alloc_shift (ctx st) <= 40 ->
  let n := Z.shiftl 2 (c_meta_alloc_shift (ctx st)) in
  evt usegs (fun ms' => ms' = MS (mkR (Z_to_bv 64 0x19928) sp gp tp t0 t1 t2 (Z_to_bv 64 4096) (Z_to_bv 64 n)
                                   (Z_to_bv 64 0) (Z_to_bv 64 (n * 4096)) (Z_to_bv 64 0) (Z_to_bv 64 34) (Z_to_bv 64 (-1)) (Z_to_bv 64 0) a6 a7
                                   (Z_to_bv 64 RSSP_GUARD) (Z_to_bv 64 RMLOCK) (Z_to_bv 64 (-1)) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                F (Z_to_bv 64 rmmap_entry) fc None m (seg_rom usegs))
      (MS (mkR x1 sp gp tp t0 t1 t2 (Z_to_bv 64 4096) s1 a0 a1 a2 a3 a4 a5 a6 a7
               (Z_to_bv 64 RSSP_GUARD) (Z_to_bv 64 RMLOCK) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x198fc) fc None m (seg_rom usegs)).
Section Sz2.
Variables sp gp tp t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 x1 F fc m st : ltac2:(SecDiet.SzSec.tyM 'ram_to_mmap__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @sp).
Lemma ram_to_mmap__body : ltac2:(SecDiet.SzSec.bodyP 'ram_to_mmap__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
Proof using Type. pin_using tt. ceil_facts. msec_facts.
 intros MR SH n.
  pose proof MR as (WF & (C1 & _) & _). unfold ctx_head_cells in C1. unfold pw in C1. cbn [oconc] in C1. unfold wz in C1.
  unfold RCTX, RMLOCK, RSSP_GUARD in *.
  (* [comment removed for export] *)
  st1. st1. st1.
  rewrite (Z.mod_small (c_meta_alloc_shift (ctx st)) 64) by lia.
  assert (NR : 0 < Z.shiftl 2 (c_meta_alloc_shift (ctx st)) <= 2^41).
  { rewrite Z.shiftl_mul_pow2 by lia. split; [apply Z.mul_pos_pos; [lia| apply Z.pow_pos_nonneg; lia]|].
    change (2^41) with (2 * 2^40). apply Z.mul_le_mono_nonneg_l; [lia|]. apply Z.pow_le_mono_r; lia. }
  (* [comment removed for export] *)
  st1. st1. st1. st1. st1. st1. st1. st1.
  apply evt_done. unfold rmmap_entry. subst n. reflexivity.
Qed.
End Sz2.
Lemma ram_to_mmap : ltac:(let t := eval cbv delta [ram_to_mmap__stmt] in ram_to_mmap__stmt in exact t).
Proof using Type. intros sp gp tp t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 x1 F fc m st. ltac2:(SecDiet.SzSec.closeP 'ram_to_mmap__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition ram_mm_fail__stmt : Prop := forall (sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 x1 raw s0o s1o s2o s3o s4o : word) F fc
    (m0 m : word -> option byte) (junk : list byte) (lo : Z) (st : mstate),
  rmrep st m -> mem_inv usegs m ->
  rpres_except (ram_fp st lo (bv_unsigned sp)) m0 m -> wmono usegs m0 m ->
  rw_cells usegs m (bv_unsigned sp + -64) (ram_frame junk s4o s3o s2o s1o s0o raw) ->
  stk usegs m lo (bv_unsigned sp + -64) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - 64 ->
  evt usegs (ram_ret_post raw sp gp tp s0o s1o s2o s3o s4o s5 s6 s7 s8 s9 s10 s11 F fc lo st m0 st (Z_to_bv 64 0))
      (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (-1)) a1 a2 a3 a4 a5 a6 a7
               (Z_to_bv 64 RSSP_GUARD) (Z_to_bv 64 RMLOCK) (Z_to_bv 64 (-1)) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x19928) fc None m (seg_rom usegs)).
Section Sz3.
Variables sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 x1 raw s0o s1o s2o s3o s4o F fc m0 m junk lo st : ltac2:(SecDiet.SzSec.tyM 'ram_mm_fail__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @sp).
Lemma ram_mm_fail__body : ltac2:(SecDiet.SzSec.bodyP 'ram_mm_fail__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
Proof using Type. pin_using tt. ceil_facts. msec_facts.
 intros MR MI PE0 WM0 FR ST LO LOLE.
  pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  pose proof (munch_refl [(bv_unsigned sp - 64, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl usegs m) as WM.
  pose proof MR as (_ & _ & (_ & _ & _ & _ & GUARD) & _).
  unfold RCTX, RMLOCK, RSSP_GUARD, ram_frame in *; ceil_facts.
  (* [comment removed for export] *)
  st1. rewrite bv_eqb_refl. cbv iota. st1. st1. st1. st1. st1. if_cases K; zify_cond K. { exfalso. apply K. reflexivity. }
  (* [comment removed for export] *)
  st1. st1. st1. st1. st1. st1. st1. st1.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) => assert (MRX : rmrep st mX) end.
  { eapply rmrep_transport_high; [exact MR| exact MU| exact WM|]. intros l h [E|[]]; inversion E; subst; ceil_facts; lia. }
  release_frame FR ST (bv_unsigned sp).
  apply evt_done. unfold ram_ret_post. do 15 eexists. split; [reflexivity|].
  split.
  { eapply rpres_except_trans; [exact PE0|].
    apply (rpres_except_of_munch_cov (ram_fp st lo (bv_unsigned sp))) in MU; [exact MU|exact WM|].
    cbn [ivs_covered]. split; [|exact I]. intros x Hx. apply ram_fp_stack. lia. }
  split; [eapply wmono_trans; [exact WM0| exact WM]|]. split; [assumption|]. split; [exact ST|]. exact MRX.
Qed.
End Sz3.
Lemma ram_mm_fail : ltac:(let t := eval cbv delta [ram_mm_fail__stmt] in ram_mm_fail__stmt in exact t).
Proof using Type. intros sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 x1 raw s0o s1o s2o s3o s4o F fc m0 m junk lo st. ltac2:(SecDiet.SzSec.closeP 'ram_mm_fail__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition ram_mm_ok__stmt : Prop := forall (sp gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 x1 raw s0o s1o s2o s3o s4o : word) F fc
    (m0 m : word -> option byte) (junk : list byte) (lo x n : Z) (st0 st : mstate) (rid : N) (r : region),
  rmrep st m -> mem_inv usegs m -> (forall a, ram_fp st0 lo (bv_unsigned sp) a -> ram_fp st lo (bv_unsigned sp) a) ->
  (s_regions st) !! rid = Some r -> r_base r = x -> x mod 4096 = 0 -> 0 < x -> x + 8192 <= alloc_ceiling -> 1 <= n < 2^62 ->
  0 <= c_meta_alloc_shift (ctx st) < 2^62 ->
  rpres_except (ram_fp st0 lo (bv_unsigned sp)) m0 m -> wmono usegs m0 m ->
  rw_cells usegs m (bv_unsigned sp + -64) (ram_frame junk s4o s3o s2o s1o s0o raw) ->
  stk usegs m lo (bv_unsigned sp + -64) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - 64 ->
  evt usegs (fun ms' => exists m',
        ms' = MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp t0 t1 t2 (Z_to_bv 64 4096) (Z_to_bv 64 (x + 4096)) (Z_to_bv 64 0)
                      (Z_to_bv 64 (c_meta_alloc_shift (ctx st) + 1)) (Z_to_bv 64 (n - 1)) a3 a4 a5 a6 a7
                      (Z_to_bv 64 RSSP_GUARD) (Z_to_bv 64 RMLOCK) (Z_to_bv 64 (-1)) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x199ec) fc None m' (seg_rom usegs)
        /\ rpres_except (ram_fp st lo (bv_unsigned sp)) m0 m' /\ wmono usegs m0 m' /\ mem_inv usegs m'
        /\ rw_cells usegs m' (bv_unsigned sp + -64) (ram_frame junk s4o s3o s2o s1o s0o raw)
        /\ stk usegs m' lo (bv_unsigned sp + -64)
        /\ rmrep (mm_ok_st st rid n) m')
      (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp t0 t1 t2 (Z_to_bv 64 4096) (Z_to_bv 64 n) (Z_to_bv 64 x) a1 a2 a3 a4 a5 a6 a7
               (Z_to_bv 64 RSSP_GUARD) (Z_to_bv 64 RMLOCK) (Z_to_bv 64 (-1)) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x19928) fc None m (seg_rom usegs)).
Section Sz4.
Variables sp gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 x1 raw s0o s1o s2o s3o s4o F fc m0 m junk lo x n st0 st rid r : ltac2:(SecDiet.SzSec.tyM 'ram_mm_ok__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @sp).
Lemma ram_mm_ok__body : ltac2:(SecDiet.SzSec.bodyP 'ram_mm_ok__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
Proof using Type. pin_using tt. ceil_facts. msec_facts.
 intros MR MI FP0 Hr RB XAL X0 XC NR SH PE0 WM0 FR ST LO LOLE.
  pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  pose proof (munch_refl [(bv_unsigned sp - 64, bv_unsigned sp); (RCTX, RCTX + 928)]%Z m) as MU. pose proof (wmono_refl usegs m) as WM.
  pose proof MR as (WF & (C1 & _) & _). unfold ctx_head_cells in C1. unfold pw in C1. cbn [oconc] in C1. unfold wz in C1.
  assert (AL : Z.land (x + 4096) 4095 = 0).
  { change 4095 with (Z.ones 12). rewrite Z.land_ones by lia. change (2 ^ 12) with 4096. clear - XAL X0. Z.div_mod_to_equations. lia. }
  assert (AL' : Z.land 4095 (x + 4096) = 0) by (rewrite Z.land_comm; exact AL).
  change (x mod 4096 = 0) with (pgal x) in XAL.
  unfold RCTX, RMLOCK, RSSP_GUARD, ram_frame in *; ceil_facts.
  (* [comment removed for export] *)
  st1.
  assert (CF : bv_eqb (Z_to_bv 64 x) (Z_to_bv 64 (-1)) = false)
    by (unfold bv_eqb; rewrite (unsigned_lit x) by lia; change (bv_unsigned (Z_to_bv 64 (-1))) with (2^64 - 1)%Z; apply Z.eqb_neq; lia).
  rewrite CF; clear CF.
  (* [comment removed for export] *)
  st1. st1. st1. st1. st1. st1.
  replace ((n + -1) * 1) with (n - 1) by lia.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
    pose proof (munch_refl [(RCTX + 40, RCTX + 56); (RCTX + 72, RCTX + 80)]%Z mX) as MUc; pose proof (wmono_refl usegs mX) as WMc end.
  unfold RCTX in MUc.
  (* [comment removed for export] *)
  st1. st1. st1.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) => assert (MR2 : rmrep (mm_ok_st st rid n) mX) end.
  { eapply (rmrep_ctx_frameW st _ _ _ _ MR MUc WMc); try reflexivity.
    - intros lo' hi' [E|[E|[]]]; inversion E; subst; unfold RCTX; lia.
    - left. unfold ctx_head_cells, RCTX. cbn [ctx mm_ok_st upd_ctx s_ctx set_meta_alloc_shift set_avail_meta_area_count set_avail_meta_areas c_secret c_init_done c_mmap_counter c_free_meta_head c_avail_meta
            c_avail_meta_count c_avail_meta_area_count c_meta_alloc_shift c_meta_area_head c_meta_area_tail c_avail_meta_areas].
      change (pw (mm_ok_st st rid n) ?q) with (pw st q). unfold pw. cbn [oconc]. change (conc (mm_ok_st st rid n) ?q) with (conc st q).
      rewrite (conc_region' st (rid, 4096) r Hr). cbn [snd]. rewrite RB. unfold wz.
      lazymatch goal with H : rw_cells usegs ?mX 345440 _ |- _ => exact H end.
    - right. split; [reflexivity|]. intros lo' hi' [E|[E|[]]]; inversion E; subst; unfold RCTX; lia.
    - right. split; [reflexivity|]. intros lo' hi' [E|[E|[]]]; inversion E; subst; unfold RCTX; lia.
    - right. split; [reflexivity|]. intros lo' hi' [E|[E|[]]]; inversion E; subst; unfold RCTX; lia.
    - right. split; [reflexivity|]. intros lo' hi' [E|[E|[]]]; inversion E; subst; unfold RCTX; lia.
    - right. split; [reflexivity|]. intros lo' hi' [E|[E|[]]]; inversion E; subst; unfold RCTX; lia. }
  clear MUc WMc.
  (* [comment removed for export] *)
  st1. st1. rewrite ?AL, ?AL'. st1. rewrite bv_eqb_refl. cbv iota.
  apply evt_done. eexists. split; [reflexivity|].
  split.
  { eapply rpres_except_trans; [eapply rpres_except_mono; [exact PE0| exact FP0]|].
    apply (rpres_except_of_munch_cov (ram_fp st lo (bv_unsigned sp))) in MU; [exact MU|exact WM|].
    cbn [ivs_covered]. split; [|split; [|exact I]].
    - intros y Hy. apply ram_fp_stack. lia.
    - intros y Hy. apply ram_fp_ctx. unfold RCTX. lia. }
  split; [first [exact WM0 | eapply wmono_trans; [exact WM0| exact WM]]|]. split; [assumption|]. split; [exact FR|]. split; [exact ST|]. exact MR2.
Qed.
End Sz4.
Lemma ram_mm_ok : ltac:(let t := eval cbv delta [ram_mm_ok__stmt] in ram_mm_ok__stmt in exact t).
Proof using Type. intros sp gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 x1 raw s0o s1o s2o s3o s4o F fc m0 m junk lo x n st0 st rid r. ltac2:(SecDiet.SzSec.closeP 'ram_mm_ok__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.

End PORT.

End WithCeil.
End TwB.
End RF_am_G.

(* [comment removed for export] *)
Module RF_am_H.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require AllocBridge__Spec. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.AllocBridge__Spec.AllocBridge.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require Import TlsBase.
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run Fs.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import Tac Image ZBridge SysStep  Arr ITree Nodes Decode.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require Import SFModel.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import ImgSrc3.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require F_malloc_free__MA. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require MallocTree. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require MallocBlocks__MA. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require MallocFacts_A__MA. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require F_am_F__MA. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.F_malloc_free__MA.F_malloc_free OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocTree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocBlocks__MA.MallocModel_B OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocBlocks__MA.F_ntf_A OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocBlocks__MA.F_ntf_B OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocBlocks__MA.MallocKit_B OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocBlocks__MA.MallocKit_B3 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocFacts_A__MA.F_am_A OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocFacts_A__MA.F_am_K OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocFacts_A__MA.F_am_C OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.F_am_F__MA.F_am_F OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.F_am_F__MA.F_am_G OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.F_am_F__MA.F_am_H.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require STree Malloc MallocCtrl. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require AllocBridge__Spec. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require MI_Realloc2__Spec. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.STree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Malloc OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MallocCtrl OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.AllocBridge__Spec.AllocBridge OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_Realloc2__Spec.ProgFull.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require KStep__Spec.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require RMallocRep__S3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require RF_am_A__S3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require RF_get_meta__S3. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RMallocRep__S3.RMallocRep OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RMallocRep__S3.RMallocTree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RMallocRep__S3.RMallocKit_B OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RMallocRep__S3.RMallocKit_B3 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RF_mm_syscalls__S3.RF_mm_syscalls OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RMallocRep__S3.RF_ntf_A OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RF_am_A__S3.RF_am_A OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RF_get_meta__S3.RF_am_K OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RF_am_A__S3.RF_am_C OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RF_mm_syscalls__S3.RF_am_F OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RF_mm_syscalls__S3.RF_am_G.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require Import MSecret.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import LiaPin.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac lia ::= pinned_lia.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section WithCeil.
Context {CEILV : CEIL} {MSECV : MSEC}.
Section PORT.
Context {PState : Type} {AS : AllocSt PState} {TB : TlsBase}.
Let TLSFACTS := the_tb_facts (TB:=TB).

Lemma ram_disp_untried : forall (sp gp tp t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 x1 : word) F fc
    (m : word -> option byte) (st : mstate),
  rmrep st m -> c_avail_meta_area_count (ctx st) = 0 -> c_brk (ctx st) = BrkUntried ->
  evt ssegs (fun ms' => ms' = MS (mkR x1 sp gp tp t0 t1 t2 (Z_to_bv 64 4096) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 4095) a2 a3 a4 a5 a6 (Z_to_bv 64 214)
                                   (Z_to_bv 64 RSSP_GUARD) (Z_to_bv 64 RMLOCK) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x190c8) fc None m (seg_rom ssegs))
      (MS (mkR x1 sp gp tp t0 t1 t2 (Z_to_bv 64 4096) s1 a0 a1 a2 a3 a4 a5 a6 a7
               (Z_to_bv 64 RSSP_GUARD) (Z_to_bv 64 RMLOCK) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x1908c) fc None m (seg_rom ssegs)).
Proof using Type. pin_using tt. ceil_facts. msec_facts.
  intros until st. intros MR CNT BRK.
  pose proof MR as (WF & (C1 & _ & _ & _ & _ & C6) & _). unfold ctx_head_cells in C1. rewrite CNT in C1.
  unfold ctx_tail_cells, brk_word in C6. rewrite BRK in C6.
  unfold pw in C1. cbn [oconc] in C1. unfold wz in C1, C6.
  unfold RCTX, RMLOCK, RSSP_GUARD in *. change (343456 + 912) with 344368 in C6.
  (* [comment removed for export] *)
  st1. st1. rewrite bv_eqb_refl. cbn [negb]. cbv iota.
  (* [comment removed for export] *)
  st1. st1. st1.
  change (bv_eqb (Z_to_bv 64 0) (Z_to_bv 64 (-1))) with false. cbv iota.
  st1. rewrite bv_eqb_refl. cbv iota.
  st1. st1. st1.
  apply evt_done. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma ram_disp_live : forall (sp gp tp t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 x1 : word) F fc
    (m : word -> option byte) (st : mstate) (rid : N) (off : Z),
  rmrep st m -> c_avail_meta_area_count (ctx st) = 0 -> c_brk (ctx st) = BrkLive rid off ->
  0 < conc st (rid, off) -> conc st (rid, off) + 4096 < 2^64 ->
  evt ssegs (fun ms' => ms' = MS (mkR x1 sp gp tp t0 t1 t2 (Z_to_bv 64 4096) (Z_to_bv 64 (conc st (rid, off) + 4096))
                                   (Z_to_bv 64 (conc st (rid, off) + 4096)) (Z_to_bv 64 (-1)) a2 a3 a4 a5 a6 (Z_to_bv 64 214)
                                   (Z_to_bv 64 RSSP_GUARD) (Z_to_bv 64 RMLOCK) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                             F (Z_to_bv 64 0x190b0) fc None m (seg_rom ssegs))
      (MS (mkR x1 sp gp tp t0 t1 t2 (Z_to_bv 64 4096) s1 a0 a1 a2 a3 a4 a5 a6 a7
               (Z_to_bv 64 RSSP_GUARD) (Z_to_bv 64 RMLOCK) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x1908c) fc None m (seg_rom ssegs)).
Proof using Type. pin_using tt. ceil_facts. msec_facts.
  intros until off. intros MR CNT BRK C0 C1b.
  pose proof MR as (WF & (C1 & _ & _ & _ & _ & C6) & _). unfold ctx_head_cells in C1. rewrite CNT in C1.
  unfold ctx_tail_cells, brk_word in C6. rewrite BRK in C6.
  unfold pw in C1. cbn [oconc] in C1. unfold wz in C1, C6.
  unfold RCTX, RMLOCK, RSSP_GUARD in *. change (343456 + 912) with 344368 in C6.
  (* [comment removed for export] *)
  st1. st1. rewrite bv_eqb_refl. cbn [negb]. cbv iota.
  (* [comment removed for export] *)
  st1. st1. st1.
  assert (CF : bv_eqb (Z_to_bv 64 (conc st (rid, off))) (Z_to_bv 64 (-1)) = false)
    by (unfold bv_eqb; rewrite (unsigned_lit (conc st (rid, off))) by lia; change (bv_unsigned (Z_to_bv 64 (-1))) with (2^64 - 1)%Z; apply Z.eqb_neq; lia).
  rewrite CF; clear CF.
  st1.
  assert (CF : bv_eqb (Z_to_bv 64 (conc st (rid, off))) (Z_to_bv 64 0) = false)
    by (unfold bv_eqb; rewrite !unsigned_lit by lia; apply Z.eqb_neq; lia).
  rewrite CF; clear CF.
  st1. st1. st1.
  apply evt_done. reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section BRKNODES.
Variables (x1 sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
          (m : word -> option byte).

Definition rbrk_regs (a0 : word) : _ :=
  mkR x1 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 (Z_to_bv 64 214) s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6.

(* [comment removed for export] *)
Lemma ram_brk0_node :
  impl ssegs (at_node ssegs) (npeek ssegs) (enode (NBrk 0) dec_brk0)
       (epost (fun r ms' => ms' = MS (rbrk_regs (Z_to_bv 64 r)) F (Z_to_bv 64 0x190cc) fc None m (seg_rom ssegs) /\ 0 <= r < 2^64))
       (MS (rbrk_regs (Z_to_bv 64 0)) F (Z_to_bv 64 0x190c8) fc None m (seg_rom ssegs)).
Proof using CEILV MSECV. pin_using (fun (CEILV MSECV : unit) => tt). ceil_facts. msec_facts.
  unfold rbrk_regs. apply impl_enode. step_ecall. split. { at_node_solve. }
  intros rsp r Hdec. apply dec_brk0_Some in Hdec. destruct Hdec as [-> Hr]. unfold eff0.
  rewrite nret_MSsvc, mkR_set_a0, apply_mem_none, lit_add_lit. replace (0x190c8 + 4)%Z with 0x190cc%Z by reflexivity.
  apply evt_done. split; [reflexivity| exact Hr].
Qed.

(* [comment removed for export] *)
Lemma ram_brk_node_at (pc : Z) :
  (pc = 0x190b0 \/ pc = 0x190ec) -> forall cur req, req <> 0 ->
  impl ssegs (at_node ssegs) (npeek ssegs) (enode (NBrk req) (dec_brk cur req))
       (epost (fun a ms' => ms' = MS (rbrk_regs (Z_to_bv 64 (brk_res cur req a))) F (Z_to_bv 64 (pc + 4)) fc None (brk_mem m cur req a) (seg_rom ssegs)))
       (MS (rbrk_regs (Z_to_bv 64 req)) F (Z_to_bv 64 pc) fc None m (seg_rom ssegs)).
Proof using CEILV MSECV. pin_using (fun (CEILV MSECV : unit) => tt). ceil_facts. msec_facts.
  intros Hpc cur req NZ. unfold rbrk_regs.
  destruct Hpc as [-> | ->]; (apply impl_enode; step_ecall; split; [at_node_solve|]);
    intros rsp a Hdec; apply dec_brk_Some in Hdec; (destruct a; rewrite Hdec; unfold eff0, brk_res, brk_mem, zeros_of;
      rewrite nret_MSsvc, mkR_set_a0, lit_add_lit;
      [ destruct (brk_new_pages cur req) as [[lo n]|]; [rewrite apply_mem_zeros | rewrite apply_mem_none]
      | rewrite apply_mem_none ];
      apply evt_done; reflexivity).
Qed.
End BRKNODES.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma ram_bu_mid : forall (sp gp tp t0 t1 t2 a2 a3 a4 a5 a6 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 x1 : word) (q0 : byte) (q1 : list byte) (q2 : word) F fc
    (m : word -> option byte) (cur : Z),
  0 < cur < 2^64 -> cur mod 4096 = 0 ->
  rw_cells ssegs m (RCTX + 912) [C1 q0; CB 7 q1; C8 q2] -> mem_inv ssegs m ->
  evt ssegs (fun ms' => exists a2' m',
        ms' = MS (mkR x1 sp gp tp t0 t1 t2 (Z_to_bv 64 4096) (Z_to_bv 64 (cur + 8192)) (Z_to_bv 64 (cur + 8192)) (Z_to_bv 64 0) a2' a3 a4 a5 a6 (Z_to_bv 64 214)
                      (Z_to_bv 64 RSSP_GUARD) (Z_to_bv 64 RMLOCK) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                 F (Z_to_bv 64 0x190ec) fc None m' (seg_rom ssegs)
        /\ munch [(RCTX + 920, RCTX + 928)]%Z m m' /\ wmono ssegs m m' /\ mem_inv ssegs m'
        /\ rw_cells ssegs m' (RCTX + 912) [C1 q0; CB 7 q1; C8 (Z_to_bv 64 cur)])
      (MS (mkR x1 sp gp tp t0 t1 t2 (Z_to_bv 64 4096) (Z_to_bv 64 0) (Z_to_bv 64 cur) (Z_to_bv 64 4095) a2 a3 a4 a5 a6 (Z_to_bv 64 214)
               (Z_to_bv 64 RSSP_GUARD) (Z_to_bv 64 RMLOCK) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x190cc) fc None m (seg_rom ssegs)).
Proof using MSECV TB. pin_using (fun (MSECV TB : unit) => tt). ceil_facts. msec_facts.
  intros until cur. intros CR CAL TC MI.
  pose proof (munch_refl [(RCTX + 920, RCTX + 928)]%Z m) as MU. pose proof (wmono_refl ssegs m) as WM.
  pose proof (land_neg_aligned cur CR CAL) as AL.
  assert (AL' : Z.land 4095 (bv_unsigned (Z_to_bv 64 (0 + - cur))) = 0) by (rewrite Z.land_comm; exact AL).
  change (cur mod 4096 = 0) with (pgal cur) in CAL.
  unfold RCTX, RMLOCK, RSSP_GUARD in *. change (343456 + 912) with 344368 in TC. change (343456 + 920) with 344376 in MU. change (343456 + 928) with 344384 in MU.
  (* [comment removed for export] *)
  st1. st1. rewrite ?AL, ?AL'. st1. st1.
  replace (0 + cur) with cur by lia.
  (* [comment removed for export] *)
  st1. st1. st1. st1.
  replace (8192 + cur) with (cur + 8192) by lia.
  apply evt_done. do 2 eexists. split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [assumption|]. exact TC.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma ram_bu_ok : forall (sp gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 x1 : word) (q0 : byte) (q1 : list byte) F fc
    (m : word -> option byte) (cur : Z),
  0 < cur -> cur + 8192 < 2^64 ->
  rw_cells ssegs m (RCTX + 912) [C1 q0; CB 7 q1; C8 (Z_to_bv 64 cur)] ->
  evt ssegs (fun ms' => ms' = MS (mkR (Z_to_bv 64 0x19110) sp gp tp t0 t1 t2 (Z_to_bv 64 4096) (Z_to_bv 64 (cur + 8192))
                                   (Z_to_bv 64 cur) (Z_to_bv 64 4096) (Z_to_bv 64 0) (Z_to_bv 64 50) (Z_to_bv 64 (-1)) (Z_to_bv 64 0) a6 (Z_to_bv 64 214)
                                   (Z_to_bv 64 RSSP_GUARD) (Z_to_bv 64 RMLOCK) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                F (Z_to_bv 64 rmmap_entry) fc None m (seg_rom ssegs))
      (MS (mkR x1 sp gp tp t0 t1 t2 (Z_to_bv 64 4096) (Z_to_bv 64 (cur + 8192)) (Z_to_bv 64 (cur + 8192)) a1 a2 a3 a4 a5 a6 (Z_to_bv 64 214)
               (Z_to_bv 64 RSSP_GUARD) (Z_to_bv 64 RMLOCK) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x190f0) fc None m (seg_rom ssegs)).
Proof using CEILV MSECV. pin_using (fun (CEILV MSECV : unit) => tt). ceil_facts. msec_facts.
  intros until cur. intros C0 C1b TC.
  unfold RCTX, RMLOCK, RSSP_GUARD in *. change (343456 + 912) with 344368 in TC.
  (* [comment removed for export] *)
  st1. rewrite bv_eqb_refl. cbn [negb]. cbv iota.
  st1. st1. st1. st1. st1. st1. st1.
  apply evt_done. unfold rmmap_entry. reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma ram_b_store : forall (sp gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 x1 : word)
    (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 : word) (q0 : byte) (q1 : list byte) (q2 : word) F fc (m : word -> option byte) (nw : Z),
  0 <= nw < 2^64 ->
  rw_cells ssegs m RCTX [C8 w0; C4 w1; C4 w2; C8 w3; C8 w4; C8 w5; C8 w6; C8 w7; C8 w8; C8 w9; C8 w10] ->
  rw_cells ssegs m (RCTX + 912) [C1 q0; CB 7 q1; C8 q2] -> mem_inv ssegs m ->
  evt ssegs (fun ms' => exists m',
        ms' = MS (mkR x1 sp gp tp t0 t1 t2 (Z_to_bv 64 1) (Z_to_bv 64 (nw - 4096)) a0 a1 a2 a3 a4 a5 a6 a7
                      (Z_to_bv 64 RSSP_GUARD) (Z_to_bv 64 RMLOCK) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                 F (Z_to_bv 64 0x1919c) fc None m' (seg_rom ssegs)
        /\ munch [(RCTX + 40, RCTX + 48); (RCTX + 920, RCTX + 928)]%Z m m' /\ wmono ssegs m m' /\ mem_inv ssegs m'
        /\ rw_cells ssegs m' RCTX [C8 w0; C4 w1; C4 w2; C8 w3; C8 w4; C8 w5; C8 (Z_to_bv 64 1); C8 w7; C8 w8; C8 w9; C8 w10]
        /\ rw_cells ssegs m' (RCTX + 912) [C1 q0; CB 7 q1; C8 (Z_to_bv 64 nw)])
      (MS (mkR x1 sp gp tp t0 t1 t2 (Z_to_bv 64 4096) (Z_to_bv 64 nw) a0 a1 a2 a3 a4 a5 a6 a7
               (Z_to_bv 64 RSSP_GUARD) (Z_to_bv 64 RMLOCK) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x19110) fc None m (seg_rom ssegs)).
Proof using MSECV TB. pin_using (fun (MSECV TB : unit) => tt). ceil_facts. msec_facts.
  intros until nw. intros NW HC TC MI.
  pose proof (munch_refl [(RCTX + 40, RCTX + 48); (RCTX + 920, RCTX + 928)]%Z m) as MU. pose proof (wmono_refl ssegs m) as WM.
  unfold RCTX, RMLOCK, RSSP_GUARD in *. change (343456 + 912) with 344368 in TC.
  change (343456 + 40) with 343496 in MU. change (343456 + 48) with 343504 in MU. change (343456 + 920) with 344376 in MU. change (343456 + 928) with 344384 in MU.
  (* [comment removed for export] *)
  st1. st1. rewrite ?(unsigned_lit nw) by lia. replace (nw + - (4096)) with (nw - 4096) by lia. st1. change (Z.shiftr 4096 12) with 1. st1. st1.
  apply evt_done. eexists. split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact HC| exact TC].
Qed.

(* [comment removed for export] *)
Lemma ram_bl_ok : forall (sp gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 x1 : word)
    (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 : word) (q0 : byte) (q1 : list byte) (q2 : word) F fc (m : word -> option byte) (nw : Z),
  0 <= nw < 2^64 ->
  rw_cells ssegs m RCTX [C8 w0; C4 w1; C4 w2; C8 w3; C8 w4; C8 w5; C8 w6; C8 w7; C8 w8; C8 w9; C8 w10] ->
  rw_cells ssegs m (RCTX + 912) [C1 q0; CB 7 q1; C8 q2] -> mem_inv ssegs m ->
  evt ssegs (fun ms' => exists m',
        ms' = MS (mkR x1 sp gp tp t0 t1 t2 (Z_to_bv 64 1) (Z_to_bv 64 (nw - 4096)) (Z_to_bv 64 nw) a1 a2 a3 a4 a5 a6 a7
                      (Z_to_bv 64 RSSP_GUARD) (Z_to_bv 64 RMLOCK) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                 F (Z_to_bv 64 0x1919c) fc None m' (seg_rom ssegs)
        /\ munch [(RCTX + 40, RCTX + 48); (RCTX + 920, RCTX + 928)]%Z m m' /\ wmono ssegs m m' /\ mem_inv ssegs m'
        /\ rw_cells ssegs m' RCTX [C8 w0; C4 w1; C4 w2; C8 w3; C8 w4; C8 w5; C8 (Z_to_bv 64 1); C8 w7; C8 w8; C8 w9; C8 w10]
        /\ rw_cells ssegs m' (RCTX + 912) [C1 q0; CB 7 q1; C8 (Z_to_bv 64 nw)])
      (MS (mkR x1 sp gp tp t0 t1 t2 (Z_to_bv 64 4096) (Z_to_bv 64 nw) (Z_to_bv 64 nw) a1 a2 a3 a4 a5 a6 a7
               (Z_to_bv 64 RSSP_GUARD) (Z_to_bv 64 RMLOCK) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x190b4) fc None m (seg_rom ssegs)).
Proof using MSECV TB. pin_using (fun (MSECV TB : unit) => tt). ceil_facts. msec_facts.
  intros until nw. intros NW HC TC MI.
  (* [comment removed for export] *)
  st1. rewrite bv_eqb_refl. cbv iota.
  eapply (ram_b_store sp gp tp t0 t1 t2 _ a1 a2 a3 a4 a5 a6 a7 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 x1 w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 q0 q1 q2 F fc m nw NW HC TC MI).
Qed.

(* [comment removed for export] *)
Lemma ram_brk_dead : forall (sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 x1 : word)
    (q0 : byte) (q1 : list byte) (q2 : word) F fc (m0 m : word -> option byte) (st : mstate),
  rmrep st m0 -> munch [(RCTX + 920, RCTX + 928)]%Z m0 m -> wmono ssegs m0 m ->
  c_avail_meta_area_count (ctx st) = 0 ->
  rw_cells ssegs m (RCTX + 912) [C1 q0; CB 7 q1; C8 q2] -> q0 = b8 (c_seq (ctx st)) -> q1 = zeros 7 -> mem_inv ssegs m ->
  evt ssegs (fun ms' => exists m',
        ms' = MS (mkR x1 sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) (Z_to_bv 64 (-1)) a2 a3 a4 a5 a6 a7
                      (Z_to_bv 64 RSSP_GUARD) (Z_to_bv 64 RMLOCK) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x1913c) fc None m' (seg_rom ssegs)
        /\ munch [(RCTX + 920, RCTX + 928)]%Z m m' /\ wmono ssegs m m' /\ mem_inv ssegs m'
        /\ rmrep (upd_ctx (set_brk BrkDead) st) m')
      (MS (mkR x1 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
               (Z_to_bv 64 RSSP_GUARD) (Z_to_bv 64 RMLOCK) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x19124) fc None m (seg_rom ssegs)).
Proof using Type. pin_using tt. ceil_facts. msec_facts.
  intros until st. intros MR MU0 WM0 CNT TC -> -> MI.
  pose proof MR as (WF & (C1 & _) & _). unfold ctx_head_cells in C1. rewrite CNT in C1. unfold pw in C1. cbn [oconc] in C1. unfold wz in C1.
  lazymatch type of C1 with rw_cells _ _ _ ?cs =>
    assert (C1' : rw_cells ssegs m RCTX cs)
      by (eapply OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RMallocRep__S3.RMallocKit_B.rrw_cells_agree; [exact C1| | exact WM0]; cbn [cells_size csize Nat.add]; intros y Hy; apply MU0;
          rewrite wa_unsigned by (unfold RCTX in *; lia); unfold RCTX in *; cbn; lia) end.
  clear C1.
  pose proof (munch_refl [(RCTX + 920, RCTX + 928)]%Z m) as MU. pose proof (wmono_refl ssegs m) as WM.
  unfold RCTX, RMLOCK, RSSP_GUARD in *. change (343456 + 912) with 344368 in TC.
  change (343456 + 920) with 344376 in MU, MU0. change (343456 + 928) with 344384 in MU, MU0.
  (* [comment removed for export] *)
  st1. st1. st1. st1. rewrite bv_eqb_refl. cbv iota.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) => assert (MR' : rmrep (upd_ctx (set_brk BrkDead) st) mX) end.
  { eapply (rmrep_ctx_frameW st _ m0 _ [(RCTX + 920, RCTX + 928)]%Z MR); try reflexivity.
    - unfold RCTX. first [exact MU0 | eapply munch_trans; [exact MU0| exact MU]].
    - first [exact WM0 | eapply wmono_trans; [exact WM0| exact WM]].
    - intros lo' hi' [E|[]]; inversion E; subst; unfold RCTX; lia.
    - right. split; [reflexivity|]. intros lo' hi' [E|[]]; inversion E; subst; unfold RCTX; lia.
    - right. split; [reflexivity|]. intros lo' hi' [E|[]]; inversion E; subst; unfold RCTX; lia.
    - right. split; [reflexivity|]. intros lo' hi' [E|[]]; inversion E; subst; unfold RCTX; lia.
    - right. split; [reflexivity|]. intros lo' hi' [E|[]]; inversion E; subst; unfold RCTX; lia.
    - right. split; [reflexivity|]. intros lo' hi' [E|[]]; inversion E; subst; unfold RCTX; lia.
    - left. unfold ctx_tail_cells, brk_word, RCTX. cbn [ctx upd_ctx s_ctx set_brk c_brk c_seq]. change (343456 + 912) with 344368.
      replace (wz (2 ^ 64 - 1)) with (Z_to_bv 64 (-1)) by (apply Z_to_bv_eqm; reflexivity).
      lazymatch goal with H : rw_cells ssegs ?mX 344368 _ |- _ => exact H end. }
  apply evt_done. eexists. split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [assumption|]. exact MR'.
Qed.

(* [comment removed for export] *)
Lemma ram_bl_fail : forall (sp gp tp t0 t1 t2 a2 a3 a4 a5 a6 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 x1 : word)
    F fc (m : word -> option byte) (st : mstate) (old : Z),
  rmrep st m -> c_avail_meta_area_count (ctx st) = 0 -> 0 < old -> old + 4096 < 2^64 -> mem_inv ssegs m ->
  evt ssegs (fun ms' => exists m',
        ms' = MS (mkR x1 sp gp tp t0 t1 t2 (Z_to_bv 64 4096) (Z_to_bv 64 (old + 4096)) (Z_to_bv 64 0) (Z_to_bv 64 (-1)) a2 a3 a4 a5 a6 (Z_to_bv 64 214)
                      (Z_to_bv 64 RSSP_GUARD) (Z_to_bv 64 RMLOCK) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x1913c) fc None m' (seg_rom ssegs)
        /\ munch [(RCTX + 920, RCTX + 928)]%Z m m' /\ wmono ssegs m m' /\ mem_inv ssegs m'
        /\ rmrep (upd_ctx (set_brk BrkDead) st) m')
      (MS (mkR x1 sp gp tp t0 t1 t2 (Z_to_bv 64 4096) (Z_to_bv 64 (old + 4096)) (Z_to_bv 64 old) (Z_to_bv 64 (-1)) a2 a3 a4 a5 a6 (Z_to_bv 64 214)
               (Z_to_bv 64 RSSP_GUARD) (Z_to_bv 64 RMLOCK) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x190b4) fc None m (seg_rom ssegs)).
Proof using Type. pin_using tt. ceil_facts. msec_facts.
  intros until old. intros MR CNT O0 O1 MI.
  pose proof MR as (WF & (_ & _ & _ & _ & _ & C6) & _). unfold ctx_tail_cells in C6.
  (* [comment removed for export] *)
  st1.
  assert (CF : bv_eqb (Z_to_bv 64 old) (Z_to_bv 64 (old + 4096)) = false) by (unfold bv_eqb; rewrite !unsigned_lit by lia; apply Z.eqb_neq; lia).
  rewrite CF; clear CF.
  st1.
  eapply (ram_brk_dead sp gp tp t0 t1 t2 _ _ _ _ a2 a3 a4 a5 a6 _ s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 x1 _ _ _ F fc m m st MR (munch_refl _ m) (wmono_refl ssegs m) CNT C6 eq_refl eq_refl MI).
Qed.

(* [comment removed for export] *)
Lemma ram_bu_fail : forall (sp gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 x1 : word)
    (q0 : byte) (q1 : list byte) F fc (m0 m : word -> option byte) (st : mstate) (cur : Z),
  rmrep st m0 -> munch [(RCTX + 920, RCTX + 928)]%Z m0 m -> wmono ssegs m0 m ->
  c_avail_meta_area_count (ctx st) = 0 -> 0 < cur -> cur < 2^64 ->
  rw_cells ssegs m (RCTX + 912) [C1 q0; CB 7 q1; C8 (Z_to_bv 64 cur)] -> q0 = b8 (c_seq (ctx st)) -> q1 = zeros 7 -> mem_inv ssegs m ->
  evt ssegs (fun ms' => exists m',
        ms' = MS (mkR x1 sp gp tp t0 t1 t2 (Z_to_bv 64 4096) (Z_to_bv 64 (cur + 8192)) (Z_to_bv 64 0) (Z_to_bv 64 (-1)) a2 a3 a4 a5 a6 (Z_to_bv 64 214)
                      (Z_to_bv 64 RSSP_GUARD) (Z_to_bv 64 RMLOCK) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x1913c) fc None m' (seg_rom ssegs)
        /\ munch [(RCTX + 920, RCTX + 928)]%Z m m' /\ wmono ssegs m m' /\ mem_inv ssegs m'
        /\ rmrep (upd_ctx (set_brk BrkDead) st) m')
      (MS (mkR x1 sp gp tp t0 t1 t2 (Z_to_bv 64 4096) (Z_to_bv 64 (cur + 8192)) (Z_to_bv 64 cur) a1 a2 a3 a4 a5 a6 (Z_to_bv 64 214)
               (Z_to_bv 64 RSSP_GUARD) (Z_to_bv 64 RMLOCK) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x190f0) fc None m (seg_rom ssegs)).
Proof using Type. pin_using tt. ceil_facts. msec_facts.
  intros until cur. intros MR MU0 WM0 CNT C0 C1b TC -> -> MI.
  (* [comment removed for export] *)
  st1.
  assert (CF : negb (bv_eqb (Z_to_bv 64 cur) (Z_to_bv 64 (cur + 8192))) = true).
  { apply Bool.negb_true_iff. unfold bv_eqb. rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2^64).
    apply Z.eqb_neq. rewrite (Z.mod_small cur) by lia. Z.div_mod_to_equations. lia. }
  rewrite CF; clear CF.
  eapply (ram_brk_dead sp gp tp t0 t1 t2 _ _ _ _ a2 a3 a4 a5 a6 _ s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 x1 _ _ _ F fc m0 m st MR MU0 WM0 CNT TC eq_refl eq_refl MI).
Qed.

End PORT.

End WithCeil.

(* [comment removed for export] *)
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require ImgTgtUbsan.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require TlsBaseU.
Module TwB.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.AllocBridge__Spec.AllocBridge.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.TlsBaseU.
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run LinuxProcessSemantics.LinuxProcessSem.Fs.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Tac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Image OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ZBridge OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.SysStep OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Arr OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ITree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Nodes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Decode.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.SFModel.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ImgTgtUbsan.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.F_malloc_free__MA.F_malloc_free OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocTree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocBlocks__MA.MallocModel_B OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocBlocks__MA.F_ntf_A OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocBlocks__MA.F_ntf_B OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocBlocks__MA.MallocKit_B OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocBlocks__MA.MallocKit_B3 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocFacts_A__MA.F_am_A OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocFacts_A__MA.F_am_K OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocFacts_A__MA.F_am_C OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.F_am_F__MA.F_am_F OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.F_am_F__MA.F_am_G OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.F_am_F__MA.F_am_H.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.STree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Malloc OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MallocCtrl OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.AllocBridge__Spec.AllocBridge OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_Realloc2__Spec.ProgFull.
(* [comment removed for export] *)
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RMallocRep__S3.RMallocRep.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RMallocRep__S3.RMallocTree.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RMallocRep__S3.RMallocKit_B.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RMallocRep__S3.RMallocKit_B3.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RF_mm_syscalls__S3.RF_mm_syscalls.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RMallocRep__S3.RF_ntf_A.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RF_am_A__S3.RF_am_A.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RF_get_meta__S3.RF_am_K.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RF_am_A__S3.RF_am_C.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RF_mm_syscalls__S3.RF_am_F.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RF_mm_syscalls__S3.RF_am_G.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MSecret.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.LiaPin.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac lia ::= pinned_lia.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section WithCeil.
Context {CEILV : CEIL} {MSECV : MSEC}.
Section PORT.
Context {PState : Type} {AS : AllocSt PState} {TB : TlsBase}.
Let TLSFACTS := the_tb_facts (TB:=TB).

Lemma ram_disp_untried : forall (sp gp tp t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 x1 : word) F fc
    (m : word -> option byte) (st : mstate),
  rmrep st m -> c_avail_meta_area_count (ctx st) = 0 -> c_brk (ctx st) = BrkUntried ->
  evt usegs (fun ms' => ms' = MS (mkR x1 sp gp tp t0 t1 t2 (Z_to_bv 64 4096) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 4095) a2 a3 a4 a5 a6 (Z_to_bv 64 214)
                                   (Z_to_bv 64 RSSP_GUARD) (Z_to_bv 64 RMLOCK) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x19888) fc None m (seg_rom usegs))
      (MS (mkR x1 sp gp tp t0 t1 t2 (Z_to_bv 64 4096) s1 a0 a1 a2 a3 a4 a5 a6 a7
               (Z_to_bv 64 RSSP_GUARD) (Z_to_bv 64 RMLOCK) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x1984c) fc None m (seg_rom usegs)).
Proof using Type. pin_using tt. ceil_facts. msec_facts.
  intros until st. intros MR CNT BRK.
  pose proof MR as (WF & (C1 & _ & _ & _ & _ & C6) & _). unfold ctx_head_cells in C1. rewrite CNT in C1.
  unfold ctx_tail_cells, brk_word in C6. rewrite BRK in C6.
  unfold pw in C1. cbn [oconc] in C1. unfold wz in C1, C6.
  unfold RCTX, RMLOCK, RSSP_GUARD in *. change (345440 + 912) with 346352 in C6.
  (* [comment removed for export] *)
  st1. st1. rewrite bv_eqb_refl. cbn [negb]. cbv iota.
  (* [comment removed for export] *)
  st1. st1. st1.
  change (bv_eqb (Z_to_bv 64 0) (Z_to_bv 64 (-1))) with false. cbv iota.
  st1. rewrite bv_eqb_refl. cbv iota.
  st1. st1. st1.
  apply evt_done. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma ram_disp_live : forall (sp gp tp t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 x1 : word) F fc
    (m : word -> option byte) (st : mstate) (rid : N) (off : Z),
  rmrep st m -> c_avail_meta_area_count (ctx st) = 0 -> c_brk (ctx st) = BrkLive rid off ->
  0 < conc st (rid, off) -> conc st (rid, off) + 4096 < 2^64 ->
  evt usegs (fun ms' => ms' = MS (mkR x1 sp gp tp t0 t1 t2 (Z_to_bv 64 4096) (Z_to_bv 64 (conc st (rid, off) + 4096))
                                   (Z_to_bv 64 (conc st (rid, off) + 4096)) (Z_to_bv 64 (-1)) a2 a3 a4 a5 a6 (Z_to_bv 64 214)
                                   (Z_to_bv 64 RSSP_GUARD) (Z_to_bv 64 RMLOCK) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                             F (Z_to_bv 64 0x19870) fc None m (seg_rom usegs))
      (MS (mkR x1 sp gp tp t0 t1 t2 (Z_to_bv 64 4096) s1 a0 a1 a2 a3 a4 a5 a6 a7
               (Z_to_bv 64 RSSP_GUARD) (Z_to_bv 64 RMLOCK) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x1984c) fc None m (seg_rom usegs)).
Proof using Type. pin_using tt. ceil_facts. msec_facts.
  intros until off. intros MR CNT BRK C0 C1b.
  pose proof MR as (WF & (C1 & _ & _ & _ & _ & C6) & _). unfold ctx_head_cells in C1. rewrite CNT in C1.
  unfold ctx_tail_cells, brk_word in C6. rewrite BRK in C6.
  unfold pw in C1. cbn [oconc] in C1. unfold wz in C1, C6.
  unfold RCTX, RMLOCK, RSSP_GUARD in *. change (345440 + 912) with 346352 in C6.
  (* [comment removed for export] *)
  st1. st1. rewrite bv_eqb_refl. cbn [negb]. cbv iota.
  (* [comment removed for export] *)
  st1. st1. st1.
  assert (CF : bv_eqb (Z_to_bv 64 (conc st (rid, off))) (Z_to_bv 64 (-1)) = false)
    by (unfold bv_eqb; rewrite (unsigned_lit (conc st (rid, off))) by lia; change (bv_unsigned (Z_to_bv 64 (-1))) with (2^64 - 1)%Z; apply Z.eqb_neq; lia).
  rewrite CF; clear CF.
  st1.
  assert (CF : bv_eqb (Z_to_bv 64 (conc st (rid, off))) (Z_to_bv 64 0) = false)
    by (unfold bv_eqb; rewrite !unsigned_lit by lia; apply Z.eqb_neq; lia).
  rewrite CF; clear CF.
  st1. st1. st1.
  apply evt_done. reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section BRKNODES.
Variables (x1 sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
          (m : word -> option byte).

Definition rbrk_regs (a0 : word) : _ :=
  mkR x1 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 (Z_to_bv 64 214) s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6.

(* [comment removed for export] *)
Lemma ram_brk0_node :
  impl usegs (at_node usegs) (npeek usegs) (enode (NBrk 0) dec_brk0)
       (epost (fun r ms' => ms' = MS (rbrk_regs (Z_to_bv 64 r)) F (Z_to_bv 64 0x1988c) fc None m (seg_rom usegs) /\ 0 <= r < 2^64))
       (MS (rbrk_regs (Z_to_bv 64 0)) F (Z_to_bv 64 0x19888) fc None m (seg_rom usegs)).
Proof using CEILV MSECV. pin_using (fun (CEILV MSECV : unit) => tt). ceil_facts. msec_facts.
  unfold rbrk_regs. apply impl_enode. step_ecall. split. { at_node_solve. }
  intros rsp r Hdec. apply dec_brk0_Some in Hdec. destruct Hdec as [-> Hr]. unfold eff0.
  rewrite nret_MSsvc, mkR_set_a0, apply_mem_none, lit_add_lit. replace (0x19888 + 4)%Z with 0x1988c%Z by reflexivity.
  apply evt_done. split; [reflexivity| exact Hr].
Qed.

(* [comment removed for export] *)
Lemma ram_brk_node_at (pc : Z) :
  (pc = 0x19870 \/ pc = 0x198ac) -> forall cur req, req <> 0 ->
  impl usegs (at_node usegs) (npeek usegs) (enode (NBrk req) (dec_brk cur req))
       (epost (fun a ms' => ms' = MS (rbrk_regs (Z_to_bv 64 (brk_res cur req a))) F (Z_to_bv 64 (pc + 4)) fc None (brk_mem m cur req a) (seg_rom usegs)))
       (MS (rbrk_regs (Z_to_bv 64 req)) F (Z_to_bv 64 pc) fc None m (seg_rom usegs)).
Proof using CEILV MSECV. pin_using (fun (CEILV MSECV : unit) => tt). ceil_facts. msec_facts.
  intros Hpc cur req NZ. unfold rbrk_regs.
  destruct Hpc as [-> | ->]; (apply impl_enode; step_ecall; split; [at_node_solve|]);
    intros rsp a Hdec; apply dec_brk_Some in Hdec; (destruct a; rewrite Hdec; unfold eff0, brk_res, brk_mem, zeros_of;
      rewrite nret_MSsvc, mkR_set_a0, lit_add_lit;
      [ destruct (brk_new_pages cur req) as [[lo n]|]; [rewrite apply_mem_zeros | rewrite apply_mem_none]
      | rewrite apply_mem_none ];
      apply evt_done; reflexivity).
Qed.
End BRKNODES.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma ram_bu_mid : forall (sp gp tp t0 t1 t2 a2 a3 a4 a5 a6 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 x1 : word) (q0 : byte) (q1 : list byte) (q2 : word) F fc
    (m : word -> option byte) (cur : Z),
  0 < cur < 2^64 -> cur mod 4096 = 0 ->
  rw_cells usegs m (RCTX + 912) [C1 q0; CB 7 q1; C8 q2] -> mem_inv usegs m ->
  evt usegs (fun ms' => exists a2' m',
        ms' = MS (mkR x1 sp gp tp t0 t1 t2 (Z_to_bv 64 4096) (Z_to_bv 64 (cur + 8192)) (Z_to_bv 64 (cur + 8192)) (Z_to_bv 64 0) a2' a3 a4 a5 a6 (Z_to_bv 64 214)
                      (Z_to_bv 64 RSSP_GUARD) (Z_to_bv 64 RMLOCK) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                 F (Z_to_bv 64 0x198ac) fc None m' (seg_rom usegs)
        /\ munch [(RCTX + 920, RCTX + 928)]%Z m m' /\ wmono usegs m m' /\ mem_inv usegs m'
        /\ rw_cells usegs m' (RCTX + 912) [C1 q0; CB 7 q1; C8 (Z_to_bv 64 cur)])
      (MS (mkR x1 sp gp tp t0 t1 t2 (Z_to_bv 64 4096) (Z_to_bv 64 0) (Z_to_bv 64 cur) (Z_to_bv 64 4095) a2 a3 a4 a5 a6 (Z_to_bv 64 214)
               (Z_to_bv 64 RSSP_GUARD) (Z_to_bv 64 RMLOCK) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x1988c) fc None m (seg_rom usegs)).
Proof using MSECV TB. pin_using (fun (MSECV TB : unit) => tt). ceil_facts. msec_facts.
  intros until cur. intros CR CAL TC MI.
  pose proof (munch_refl [(RCTX + 920, RCTX + 928)]%Z m) as MU. pose proof (wmono_refl usegs m) as WM.
  pose proof (land_neg_aligned cur CR CAL) as AL.
  assert (AL' : Z.land 4095 (bv_unsigned (Z_to_bv 64 (0 + - cur))) = 0) by (rewrite Z.land_comm; exact AL).
  change (cur mod 4096 = 0) with (pgal cur) in CAL.
  unfold RCTX, RMLOCK, RSSP_GUARD in *. change (345440 + 912) with 346352 in TC. change (345440 + 920) with 346360 in MU. change (345440 + 928) with 346368 in MU.
  (* [comment removed for export] *)
  st1. st1. rewrite ?AL, ?AL'. st1. st1.
  replace (0 + cur) with cur by lia.
  (* [comment removed for export] *)
  st1. st1. st1. st1.
  replace (8192 + cur) with (cur + 8192) by lia.
  apply evt_done. do 2 eexists. split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [assumption|]. exact TC.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma ram_bu_ok : forall (sp gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 x1 : word) (q0 : byte) (q1 : list byte) F fc
    (m : word -> option byte) (cur : Z),
  0 < cur -> cur + 8192 < 2^64 ->
  rw_cells usegs m (RCTX + 912) [C1 q0; CB 7 q1; C8 (Z_to_bv 64 cur)] ->
  evt usegs (fun ms' => ms' = MS (mkR (Z_to_bv 64 0x198d0) sp gp tp t0 t1 t2 (Z_to_bv 64 4096) (Z_to_bv 64 (cur + 8192))
                                   (Z_to_bv 64 cur) (Z_to_bv 64 4096) (Z_to_bv 64 0) (Z_to_bv 64 50) (Z_to_bv 64 (-1)) (Z_to_bv 64 0) a6 (Z_to_bv 64 214)
                                   (Z_to_bv 64 RSSP_GUARD) (Z_to_bv 64 RMLOCK) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                F (Z_to_bv 64 rmmap_entry) fc None m (seg_rom usegs))
      (MS (mkR x1 sp gp tp t0 t1 t2 (Z_to_bv 64 4096) (Z_to_bv 64 (cur + 8192)) (Z_to_bv 64 (cur + 8192)) a1 a2 a3 a4 a5 a6 (Z_to_bv 64 214)
               (Z_to_bv 64 RSSP_GUARD) (Z_to_bv 64 RMLOCK) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x198b0) fc None m (seg_rom usegs)).
Proof using CEILV MSECV. pin_using (fun (CEILV MSECV : unit) => tt). ceil_facts. msec_facts.
  intros until cur. intros C0 C1b TC.
  unfold RCTX, RMLOCK, RSSP_GUARD in *. change (345440 + 912) with 346352 in TC.
  (* [comment removed for export] *)
  st1. rewrite bv_eqb_refl. cbn [negb]. cbv iota.
  st1. st1. st1. st1. st1. st1. st1.
  apply evt_done. unfold rmmap_entry. reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma ram_b_store : forall (sp gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 x1 : word)
    (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 : word) (q0 : byte) (q1 : list byte) (q2 : word) F fc (m : word -> option byte) (nw : Z),
  0 <= nw < 2^64 ->
  rw_cells usegs m RCTX [C8 w0; C4 w1; C4 w2; C8 w3; C8 w4; C8 w5; C8 w6; C8 w7; C8 w8; C8 w9; C8 w10] ->
  rw_cells usegs m (RCTX + 912) [C1 q0; CB 7 q1; C8 q2] -> mem_inv usegs m ->
  evt usegs (fun ms' => exists m',
        ms' = MS (mkR x1 sp gp tp t0 t1 t2 (Z_to_bv 64 1) (Z_to_bv 64 (nw - 4096)) a0 a1 a2 a3 a4 a5 a6 a7
                      (Z_to_bv 64 RSSP_GUARD) (Z_to_bv 64 RMLOCK) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                 F (Z_to_bv 64 0x1995c) fc None m' (seg_rom usegs)
        /\ munch [(RCTX + 40, RCTX + 48); (RCTX + 920, RCTX + 928)]%Z m m' /\ wmono usegs m m' /\ mem_inv usegs m'
        /\ rw_cells usegs m' RCTX [C8 w0; C4 w1; C4 w2; C8 w3; C8 w4; C8 w5; C8 (Z_to_bv 64 1); C8 w7; C8 w8; C8 w9; C8 w10]
        /\ rw_cells usegs m' (RCTX + 912) [C1 q0; CB 7 q1; C8 (Z_to_bv 64 nw)])
      (MS (mkR x1 sp gp tp t0 t1 t2 (Z_to_bv 64 4096) (Z_to_bv 64 nw) a0 a1 a2 a3 a4 a5 a6 a7
               (Z_to_bv 64 RSSP_GUARD) (Z_to_bv 64 RMLOCK) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x198d0) fc None m (seg_rom usegs)).
Proof using MSECV TB. pin_using (fun (MSECV TB : unit) => tt). ceil_facts. msec_facts.
  intros until nw. intros NW HC TC MI.
  pose proof (munch_refl [(RCTX + 40, RCTX + 48); (RCTX + 920, RCTX + 928)]%Z m) as MU. pose proof (wmono_refl usegs m) as WM.
  unfold RCTX, RMLOCK, RSSP_GUARD in *. change (345440 + 912) with 346352 in TC.
  change (345440 + 40) with 345480 in MU. change (345440 + 48) with 345488 in MU. change (345440 + 920) with 346360 in MU. change (345440 + 928) with 346368 in MU.
  (* [comment removed for export] *)
  st1. st1. rewrite ?(unsigned_lit nw) by lia. replace (nw + - (4096)) with (nw - 4096) by lia. st1. change (Z.shiftr 4096 12) with 1. st1. st1.
  apply evt_done. eexists. split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact HC| exact TC].
Qed.

(* [comment removed for export] *)
Lemma ram_bl_ok : forall (sp gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 x1 : word)
    (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 : word) (q0 : byte) (q1 : list byte) (q2 : word) F fc (m : word -> option byte) (nw : Z),
  0 <= nw < 2^64 ->
  rw_cells usegs m RCTX [C8 w0; C4 w1; C4 w2; C8 w3; C8 w4; C8 w5; C8 w6; C8 w7; C8 w8; C8 w9; C8 w10] ->
  rw_cells usegs m (RCTX + 912) [C1 q0; CB 7 q1; C8 q2] -> mem_inv usegs m ->
  evt usegs (fun ms' => exists m',
        ms' = MS (mkR x1 sp gp tp t0 t1 t2 (Z_to_bv 64 1) (Z_to_bv 64 (nw - 4096)) (Z_to_bv 64 nw) a1 a2 a3 a4 a5 a6 a7
                      (Z_to_bv 64 RSSP_GUARD) (Z_to_bv 64 RMLOCK) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                 F (Z_to_bv 64 0x1995c) fc None m' (seg_rom usegs)
        /\ munch [(RCTX + 40, RCTX + 48); (RCTX + 920, RCTX + 928)]%Z m m' /\ wmono usegs m m' /\ mem_inv usegs m'
        /\ rw_cells usegs m' RCTX [C8 w0; C4 w1; C4 w2; C8 w3; C8 w4; C8 w5; C8 (Z_to_bv 64 1); C8 w7; C8 w8; C8 w9; C8 w10]
        /\ rw_cells usegs m' (RCTX + 912) [C1 q0; CB 7 q1; C8 (Z_to_bv 64 nw)])
      (MS (mkR x1 sp gp tp t0 t1 t2 (Z_to_bv 64 4096) (Z_to_bv 64 nw) (Z_to_bv 64 nw) a1 a2 a3 a4 a5 a6 a7
               (Z_to_bv 64 RSSP_GUARD) (Z_to_bv 64 RMLOCK) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x19874) fc None m (seg_rom usegs)).
Proof using MSECV TB. pin_using (fun (MSECV TB : unit) => tt). ceil_facts. msec_facts.
  intros until nw. intros NW HC TC MI.
  (* [comment removed for export] *)
  st1. rewrite bv_eqb_refl. cbv iota.
  eapply (ram_b_store sp gp tp t0 t1 t2 _ a1 a2 a3 a4 a5 a6 a7 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 x1 w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 q0 q1 q2 F fc m nw NW HC TC MI).
Qed.

(* [comment removed for export] *)
Lemma ram_brk_dead : forall (sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 x1 : word)
    (q0 : byte) (q1 : list byte) (q2 : word) F fc (m0 m : word -> option byte) (st : mstate),
  rmrep st m0 -> munch [(RCTX + 920, RCTX + 928)]%Z m0 m -> wmono usegs m0 m ->
  c_avail_meta_area_count (ctx st) = 0 ->
  rw_cells usegs m (RCTX + 912) [C1 q0; CB 7 q1; C8 q2] -> q0 = b8 (c_seq (ctx st)) -> q1 = zeros 7 -> mem_inv usegs m ->
  evt usegs (fun ms' => exists m',
        ms' = MS (mkR x1 sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) (Z_to_bv 64 (-1)) a2 a3 a4 a5 a6 a7
                      (Z_to_bv 64 RSSP_GUARD) (Z_to_bv 64 RMLOCK) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x198fc) fc None m' (seg_rom usegs)
        /\ munch [(RCTX + 920, RCTX + 928)]%Z m m' /\ wmono usegs m m' /\ mem_inv usegs m'
        /\ rmrep (upd_ctx (set_brk BrkDead) st) m')
      (MS (mkR x1 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
               (Z_to_bv 64 RSSP_GUARD) (Z_to_bv 64 RMLOCK) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x198e4) fc None m (seg_rom usegs)).
Proof using Type. pin_using tt. ceil_facts. msec_facts.
  intros until st. intros MR MU0 WM0 CNT TC -> -> MI.
  pose proof MR as (WF & (C1 & _) & _). unfold ctx_head_cells in C1. rewrite CNT in C1. unfold pw in C1. cbn [oconc] in C1. unfold wz in C1.
  lazymatch type of C1 with rw_cells _ _ _ ?cs =>
    assert (C1' : rw_cells usegs m RCTX cs)
      by (eapply OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RMallocRep__S3.RMallocKit_B.TwB.rrw_cells_agree; [exact C1| | exact WM0]; cbn [cells_size csize Nat.add]; intros y Hy; apply MU0;
          rewrite wa_unsigned by (unfold RCTX in *; lia); unfold RCTX in *; cbn; lia) end.
  clear C1.
  pose proof (munch_refl [(RCTX + 920, RCTX + 928)]%Z m) as MU. pose proof (wmono_refl usegs m) as WM.
  unfold RCTX, RMLOCK, RSSP_GUARD in *. change (345440 + 912) with 346352 in TC.
  change (345440 + 920) with 346360 in MU, MU0. change (345440 + 928) with 346368 in MU, MU0.
  (* [comment removed for export] *)
  st1. st1. st1. st1. rewrite bv_eqb_refl. cbv iota.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) => assert (MR' : rmrep (upd_ctx (set_brk BrkDead) st) mX) end.
  { eapply (rmrep_ctx_frameW st _ m0 _ [(RCTX + 920, RCTX + 928)]%Z MR); try reflexivity.
    - unfold RCTX. first [exact MU0 | eapply munch_trans; [exact MU0| exact MU]].
    - first [exact WM0 | eapply wmono_trans; [exact WM0| exact WM]].
    - intros lo' hi' [E|[]]; inversion E; subst; unfold RCTX; lia.
    - right. split; [reflexivity|]. intros lo' hi' [E|[]]; inversion E; subst; unfold RCTX; lia.
    - right. split; [reflexivity|]. intros lo' hi' [E|[]]; inversion E; subst; unfold RCTX; lia.
    - right. split; [reflexivity|]. intros lo' hi' [E|[]]; inversion E; subst; unfold RCTX; lia.
    - right. split; [reflexivity|]. intros lo' hi' [E|[]]; inversion E; subst; unfold RCTX; lia.
    - right. split; [reflexivity|]. intros lo' hi' [E|[]]; inversion E; subst; unfold RCTX; lia.
    - left. unfold ctx_tail_cells, brk_word, RCTX. cbn [ctx upd_ctx s_ctx set_brk c_brk c_seq]. change (345440 + 912) with 346352.
      replace (wz (2 ^ 64 - 1)) with (Z_to_bv 64 (-1)) by (apply Z_to_bv_eqm; reflexivity).
      lazymatch goal with H : rw_cells usegs ?mX 346352 _ |- _ => exact H end. }
  apply evt_done. eexists. split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [assumption|]. exact MR'.
Qed.

(* [comment removed for export] *)
Lemma ram_bl_fail : forall (sp gp tp t0 t1 t2 a2 a3 a4 a5 a6 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 x1 : word)
    F fc (m : word -> option byte) (st : mstate) (old : Z),
  rmrep st m -> c_avail_meta_area_count (ctx st) = 0 -> 0 < old -> old + 4096 < 2^64 -> mem_inv usegs m ->
  evt usegs (fun ms' => exists m',
        ms' = MS (mkR x1 sp gp tp t0 t1 t2 (Z_to_bv 64 4096) (Z_to_bv 64 (old + 4096)) (Z_to_bv 64 0) (Z_to_bv 64 (-1)) a2 a3 a4 a5 a6 (Z_to_bv 64 214)
                      (Z_to_bv 64 RSSP_GUARD) (Z_to_bv 64 RMLOCK) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x198fc) fc None m' (seg_rom usegs)
        /\ munch [(RCTX + 920, RCTX + 928)]%Z m m' /\ wmono usegs m m' /\ mem_inv usegs m'
        /\ rmrep (upd_ctx (set_brk BrkDead) st) m')
      (MS (mkR x1 sp gp tp t0 t1 t2 (Z_to_bv 64 4096) (Z_to_bv 64 (old + 4096)) (Z_to_bv 64 old) (Z_to_bv 64 (-1)) a2 a3 a4 a5 a6 (Z_to_bv 64 214)
               (Z_to_bv 64 RSSP_GUARD) (Z_to_bv 64 RMLOCK) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x19874) fc None m (seg_rom usegs)).
Proof using Type. pin_using tt. ceil_facts. msec_facts.
  intros until old. intros MR CNT O0 O1 MI.
  pose proof MR as (WF & (_ & _ & _ & _ & _ & C6) & _). unfold ctx_tail_cells in C6.
  (* [comment removed for export] *)
  st1.
  assert (CF : bv_eqb (Z_to_bv 64 old) (Z_to_bv 64 (old + 4096)) = false) by (unfold bv_eqb; rewrite !unsigned_lit by lia; apply Z.eqb_neq; lia).
  rewrite CF; clear CF.
  st1.
  eapply (ram_brk_dead sp gp tp t0 t1 t2 _ _ _ _ a2 a3 a4 a5 a6 _ s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 x1 _ _ _ F fc m m st MR (munch_refl _ m) (wmono_refl usegs m) CNT C6 eq_refl eq_refl MI).
Qed.

(* [comment removed for export] *)
Lemma ram_bu_fail : forall (sp gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 x1 : word)
    (q0 : byte) (q1 : list byte) F fc (m0 m : word -> option byte) (st : mstate) (cur : Z),
  rmrep st m0 -> munch [(RCTX + 920, RCTX + 928)]%Z m0 m -> wmono usegs m0 m ->
  c_avail_meta_area_count (ctx st) = 0 -> 0 < cur -> cur < 2^64 ->
  rw_cells usegs m (RCTX + 912) [C1 q0; CB 7 q1; C8 (Z_to_bv 64 cur)] -> q0 = b8 (c_seq (ctx st)) -> q1 = zeros 7 -> mem_inv usegs m ->
  evt usegs (fun ms' => exists m',
        ms' = MS (mkR x1 sp gp tp t0 t1 t2 (Z_to_bv 64 4096) (Z_to_bv 64 (cur + 8192)) (Z_to_bv 64 0) (Z_to_bv 64 (-1)) a2 a3 a4 a5 a6 (Z_to_bv 64 214)
                      (Z_to_bv 64 RSSP_GUARD) (Z_to_bv 64 RMLOCK) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x198fc) fc None m' (seg_rom usegs)
        /\ munch [(RCTX + 920, RCTX + 928)]%Z m m' /\ wmono usegs m m' /\ mem_inv usegs m'
        /\ rmrep (upd_ctx (set_brk BrkDead) st) m')
      (MS (mkR x1 sp gp tp t0 t1 t2 (Z_to_bv 64 4096) (Z_to_bv 64 (cur + 8192)) (Z_to_bv 64 cur) a1 a2 a3 a4 a5 a6 (Z_to_bv 64 214)
               (Z_to_bv 64 RSSP_GUARD) (Z_to_bv 64 RMLOCK) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x198b0) fc None m (seg_rom usegs)).
Proof using Type. pin_using tt. ceil_facts. msec_facts.
  intros until cur. intros MR MU0 WM0 CNT C0 C1b TC -> -> MI.
  (* [comment removed for export] *)
  st1.
  assert (CF : negb (bv_eqb (Z_to_bv 64 cur) (Z_to_bv 64 (cur + 8192))) = true).
  { apply Bool.negb_true_iff. unfold bv_eqb. rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2^64).
    apply Z.eqb_neq. rewrite (Z.mod_small cur) by lia. Z.div_mod_to_equations. lia. }
  rewrite CF; clear CF.
  eapply (ram_brk_dead sp gp tp t0 t1 t2 _ _ _ _ a2 a3 a4 a5 a6 _ s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 x1 _ _ _ F fc m0 m st MR MU0 WM0 CNT TC eq_refl eq_refl MI).
Qed.

End PORT.

End WithCeil.
End TwB.
End RF_am_H.

(* [comment removed for export] *)
Module RF_free_C.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require AllocBridge__Spec. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.AllocBridge__Spec.AllocBridge.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require Import TlsBase.
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import Tac Image ZBridge SysStep  Arr.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require Import SFModel.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import ImgSrc3.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require F_malloc_free__MA. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require F_am_F__MA. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.F_malloc_free__MA.F_malloc_free OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.F_am_F__MA.F_free_C.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require RMallocRep__S3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require RF_get_meta__S3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require RF_malloc_entry__S3. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RMallocRep__S3.RMallocRep OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RMallocRep__S3.RMallocTree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RMallocRep__S3.RMallocKit_B OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RMallocRep__S3.RMallocKit_B3 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RF_get_meta__S3.RF_get_meta OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RF_mm_syscalls__S3.RF_mm_syscalls OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RF_malloc_entry__S3.RPeek.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Import STree Malloc MallocCtrl.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require Import MSecret.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import LiaPin.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require SecDiet.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac lia ::= pinned_lia.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
Section WithCeil.
Context {CEILV : CEIL} {MSECV : MSEC}.
Section PORT.
Context {PState : Type} {AS : AllocSt PState} {TB : TlsBase}.
Let TLSFACTS := the_tb_facts (TB:=TB).

Definition rffin_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (lo : Z) (W : list (Z * Z)) (m : word -> option byte) (st : mstate) (errv : word) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom ssegs)
    /\ munch W m m' /\ wmono ssegs m m' /\ mem_inv ssegs m'
    /\ stk ssegs m' lo (bv_unsigned sp)
    /\ rw_cells ssegs m' (errno_addr tp) [C4 errv]
    /\ rmrep st m'.

Definition rfree_fin0__stmt : Prop := forall (sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 x1 ra bw q0 q1 : word) F fc
    (m : word -> option byte) (junk : list byte) (lo : Z) (st : mstate) (errv : word),
  tp = Z_to_bv 64 RATP ->
  rmrep st m -> mem_inv ssegs m ->
  rw_cells ssegs m (bv_unsigned sp + -48) [CB 8 junk; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
  rw_cells ssegs m (errno_addr tp) [C4 errv] ->
  stk ssegs m lo (bv_unsigned sp + -48) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - 48 ->
  evt ssegs (rffin_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo [(bv_unsigned sp - 48, bv_unsigned sp)]%Z m st errv)
      (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 q0 q1 bw (wz 0) a2 a3 a4 a5 a6 a7
               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x18a44) fc None m (seg_rom ssegs)).
Section Sz1.
Variables sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 x1 ra bw q0 q1 F fc m junk lo st errv : ltac2:(SecDiet.SzSec.tyM 'rfree_fin0__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @sp).
Lemma rfree_fin0__body : ltac2:(SecDiet.SzSec.bodyP 'rfree_fin0__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
Proof using Type. pin_using tt. ceil_facts. msec_facts.
  intros TP MR MI FR ERR ST LO LOLE.
  pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp)]%Z m) as MU.
  pose proof (wmono_refl ssegs m) as WM.
  pose proof MR as (WF & CX & GL & AR & GR & SH). destruct GL as (LK & NL & _).
  unfold RMLOCK, RNEED_LOCKS in *; ceil_facts.
  assert (TPR : 164 <= bv_unsigned tp < 2^64) by (rewrite TP, RATP_unsigned; lia). pose proof (rerrno_addr tp TP) as ETP.
  (* [comment removed for export] *)
  st1. st1. st1. st1.
  (* [comment removed for export] *)
  st1.
  eapply evt_cut.
  { eapply runlock_spec; rewrite unsigned_lit by lia; [reflexivity| exact LK]. }
  intros ms' ->.
  replace (ret_pc (Z_to_bv 64 0x18a58)) with (Z_to_bv 64 0x18a58) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]).
  (* [comment removed for export] *)
  st1. if_cases K; zify_cond K. 2:{ exfalso. apply K. reflexivity. }
  st1. st1. st1. st1. st1. st1. st1.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
    assert (MR2 : rmrep st mX)
      by (eapply rmrep_transport_high; [exact MR | exact MU | exact WM | intros l h [E|[]]; inversion E; subst; ceil_facts; lia]) end.
  release_frame FR ST (bv_unsigned sp).
  apply evt_done. unfold rffin_post. do 16 eexists. split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact ST|]. split; [| exact MR2].
  exact ERR.
Qed.
End Sz1.
Lemma rfree_fin0 : ltac:(let t := eval cbv delta [rfree_fin0__stmt] in rfree_fin0__stmt in exact t).
Proof using Type. intros sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 x1 ra bw q0 q1 F fc m junk lo st errv. ltac2:(SecDiet.SzSec.closeP 'rfree_fin0__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.

(* [comment removed for export] *)
Definition rfmun_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (lo : Z) (junk : list byte) (m : word -> option byte) (st : mstate) (errv bw lw : word) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR (Z_to_bv 64 0x18a74) (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 bw lw bw lw a2 a3 a4 a5 a6 a7
                  (Z_to_bv 64 (errno_addr tp)) (sx32 errv) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (Z_to_bv 64 rmunmap_entry) fc None m' (seg_rom ssegs)
    /\ munch [(bv_unsigned sp - 48, bv_unsigned sp)]%Z m m' /\ wmono ssegs m m' /\ mem_inv ssegs m'
    /\ stk ssegs m' lo (bv_unsigned sp + -48)
    /\ rw_cells ssegs m' (bv_unsigned sp + -48) [CB 8 junk; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]
    /\ rw_cells ssegs m' (errno_addr tp) [C4 errv]
    /\ rmrep st m'.

Definition rfree_tomunmap__stmt : Prop := forall (sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 x1 ra bw q0 q1 : word) F fc
    (m : word -> option byte) (junk : list byte) (lo len : Z) (st : mstate) (errv : word),
  tp = Z_to_bv 64 RATP ->
  rmrep st m -> mem_inv ssegs m -> 0 < len < 2^64 ->
  rw_cells ssegs m (bv_unsigned sp + -48) [CB 8 junk; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
  rw_cells ssegs m (errno_addr tp) [C4 errv] ->
  stk ssegs m lo (bv_unsigned sp + -48) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - 48 ->
  evt ssegs (rfmun_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo junk m st errv bw (wz len))
      (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 q0 q1 bw (wz len) a2 a3 a4 a5 a6 a7
               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x18a44) fc None m (seg_rom ssegs)).
Section Sz2.
Variables sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 x1 ra bw q0 q1 F fc m junk lo len st errv : ltac2:(SecDiet.SzSec.tyM 'rfree_tomunmap__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @sp).
Lemma rfree_tomunmap__body : ltac2:(SecDiet.SzSec.bodyP 'rfree_tomunmap__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
Proof using Type. pin_using tt. ceil_facts. msec_facts.
  intros TP MR MI HL FR ERR ST LO LOLE.
  pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp)]%Z m) as MU.
  pose proof (wmono_refl ssegs m) as WM.
  pose proof MR as (WF & CX & GL & AR & GR & SH). destruct GL as (LK & NL & _).
  unfold RMLOCK, RNEED_LOCKS in *; ceil_facts.
  assert (TPR : 164 <= bv_unsigned tp < 2^64) by (rewrite TP, RATP_unsigned; lia). pose proof (rerrno_addr tp TP) as ETP.
  (* [comment removed for export] *)
  st1. st1. st1. st1.
  (* [comment removed for export] *)
  st1.
  eapply evt_cut.
  { eapply runlock_spec; rewrite unsigned_lit by lia; [reflexivity| exact LK]. }
  intros ms' ->.
  replace (ret_pc (Z_to_bv 64 0x18a58)) with (Z_to_bv 64 0x18a58) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]).
  (* [comment removed for export] *)
  st1. if_cases K; zify_cond K. { exfalso. rewrite wz_unsigned in K by lia. lia. }
  (* [comment removed for export] *)
  st1. st1. st1. st1.
  replace (ret_pc (Z_to_bv 64 0x18a60)) with (Z_to_bv 64 0x18a60) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]).
  (* [comment removed for export] *)
  st1. st1. st1. st1. st1.
  lazymatch goal with |- evt _ _ (MS ?R _ _ _ _ ?mX _) =>
    assert (MR2 : rmrep st mX)
      by (eapply rmrep_transport_high; [exact MR | exact MU | exact WM | intros l h [E|[]]; inversion E; subst; ceil_facts; lia]) end.
  apply evt_done. unfold rfmun_post. do 14 eexists. split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact ST|]. split; [exact FR|].
  split; [exact ERR| exact MR2].
Qed.
End Sz2.
Lemma rfree_tomunmap : ltac:(let t := eval cbv delta [rfree_tomunmap__stmt] in rfree_tomunmap__stmt in exact t).
Proof using Type. intros sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 x1 ra bw q0 q1 F fc m junk lo len st errv. ltac2:(SecDiet.SzSec.closeP 'rfree_tomunmap__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.

(* [comment removed for export] *)
Definition rerrno_avoids_repfoot__stmt : Prop := forall st m a, rmrep st m -> RERRNO <= a < RERRNO + 4 -> ~ rrepfoot st a.
Section Sz3.
Variables st m a : ltac2:(SecDiet.SzSec.tyM 'rerrno_avoids_repfoot__stmt "vvv" @st).
Lemma rerrno_avoids_repfoot__body : ltac2:(SecDiet.SzSec.bodyP 'rerrno_avoids_repfoot__stmt "vvv").
Proof using Type. pin_using tt. ceil_facts. msec_facts.
  intros MR Ha.
 pose proof MR as (WF & _). pose proof WF as (Hres & WR & DJ & WA & WG).
  intros [C|[C|[C|[C|[C|[C|[C|[C|C]]]]]]]].
  - unfold RCTX in C. lia.
  - unfold RMLOCK in C. lia.
  - unfold RNEED_LOCKS in C. lia.
  - unfold RPAGE_SIZE in C. lia.
  - destruct C as (ak & ar & Hak & Hin).
    destruct (rarea_conc st ak ar WF Hak) as (ra & Hra & Ca & Sa0 & Sa1 & SaL & NK & RB0 & RBAL & RBC).
    destruct (WR _ _ Hra) as (_ & _ & _ & _ & RF). destruct (rreserved_disjoint _ _ RF) as [D1 D2]. pose proof (rreserved_tlsF _ _ RF). pose proof (round_up_pg_ge (r_len ra)). lia.
  - destruct C as (b & gh & Hb & Hin).
    destruct (rgroup_conc st b gh WF Hb) as (rb & Hrb & Cb & Krb & Sb0 & Sb1 & SbA & RB0 & RBC).
    destruct (WR _ _ Hrb) as (_ & _ & _ & _ & RF). destruct (rreserved_disjoint _ _ RF) as [D1 D2]. pose proof (rreserved_tlsF _ _ RF). pose proof (round_up_pg_ge (r_len rb)). lia.
  - destruct C as (rid & r & v & Hr & Hk & Hin & HC).
    destruct (WR _ _ Hr) as (_ & _ & _ & _ & RF). destruct (rreserved_disjoint _ _ RF) as [D1 D2]. pose proof (rreserved_tlsF _ _ RF). lia.
  - unfold RGOT_SSP in C. lia.
  - unfold RSSP_GUARD in C. lia.
Qed.
End Sz3.
Lemma rerrno_avoids_repfoot : ltac:(let t := eval cbv delta [rerrno_avoids_repfoot__stmt] in rerrno_avoids_repfoot__stmt in exact t).
Proof using Type. intros st m a. ltac2:(SecDiet.SzSec.closeP 'rerrno_avoids_repfoot__body "vvv"). Qed.

Definition rmrep_transport_frame_errno__stmt : Prop := forall st m m' (sp : Z),
  rmrep st m -> munch [(sp - 48, sp); (RERRNO, RERRNO + 4)]%Z m m' -> wmono ssegs m m' -> alloc_ceiling <= sp - 48 -> rmrep st m'.
Section Sz4.
Variables st m m' sp : ltac2:(SecDiet.SzSec.tyM 'rmrep_transport_frame_errno__stmt "vvvv" @st).
Lemma rmrep_transport_frame_errno__body : ltac2:(SecDiet.SzSec.bodyP 'rmrep_transport_frame_errno__stmt "vvvv").
Proof using Type. pin_using tt. ceil_facts. msec_facts.
  intros MR MU WM HS.
 eapply rmrep_transport_unowned; [exact MR | exact MU | exact WM |].
  apply ivs_avoid_cons; [| apply ivs_avoid_cons; [| apply ivs_avoid_nil]].
  - intros a Ha. pose proof MR as (WF & _). pose proof WF as (Hres & WR & DJ & WA & WG). ceil_facts.
    intros [C|[C|[C|[C|[C|[C|[C|[C|C]]]]]]]].
    + unfold RCTX in C. lia.
    + unfold RMLOCK in C. lia.
    + unfold RNEED_LOCKS in C. lia.
    + unfold RPAGE_SIZE in C. lia.
    + destruct C as (ak & ar & Hak & Hin).
      destruct (rarea_conc st ak ar WF Hak) as (ra & Hra & Ca & Sa0 & Sa1 & SaL & NK & RB0 & RBAL & RBC). ceil_facts. lia.
    + destruct C as (b & gh & Hb & Hin).
      destruct (rgroup_conc st b gh WF Hb) as (rb & Hrb & Cb & Krb & Sb0 & Sb1 & SbA & RB0 & RBC). ceil_facts. lia.
    + destruct C as (rid & r & v & Hr & Hk & Hin & HC).
      destruct (WR _ _ Hr) as (_ & _ & _ & RBC & _). ceil_facts. lia.
    + unfold RGOT_SSP in C. lia.
    + unfold RSSP_GUARD in C. lia.
  - intros a Ha. eapply rerrno_avoids_repfoot; [exact MR | exact Ha].
Qed.
End Sz4.
Lemma rmrep_transport_frame_errno : ltac:(let t := eval cbv delta [rmrep_transport_frame_errno__stmt] in rmrep_transport_frame_errno__stmt in exact t).
Proof using Type. intros st m m' sp. ltac2:(SecDiet.SzSec.closeP 'rmrep_transport_frame_errno__body "vvvv"). Qed.

(* [comment removed for export] *)
Definition rfree_fin1__stmt : Prop := forall (sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 x1 ra ew bw lw e' : word) F fc
    (m : word -> option byte) (junk : list byte) (lo : Z) (st : mstate) (errv : word),
  tp = Z_to_bv 64 RATP ->
  rmrep st m -> mem_inv ssegs m ->
  rw_cells ssegs m (bv_unsigned sp + -48) [CB 8 junk; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
  le4 ew = le4 errv ->
  rw_cells ssegs m (errno_addr tp) [C4 e'] ->
  stk ssegs m lo (bv_unsigned sp + -48) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - 48 ->
  evt ssegs (rffin_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo [(bv_unsigned sp - 48, bv_unsigned sp); (RERRNO, RERRNO + 4)]%Z m st errv)
      (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 bw lw a0 a1 a2 a3 a4 a5 a6 a7
               (Z_to_bv 64 (errno_addr tp)) ew s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x18a74) fc None m (seg_rom ssegs)).
Section Sz5.
Variables sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 x1 ra ew bw lw e' F fc m junk lo st errv : ltac2:(SecDiet.SzSec.tyM 'rfree_fin1__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @sp).
Lemma rfree_fin1__body : ltac2:(SecDiet.SzSec.bodyP 'rfree_fin1__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
Proof using Type. pin_using tt. ceil_facts. msec_facts.
  intros TP MR MI FR EW ERR ST LO LOLE.
  pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp); (RERRNO, RERRNO + 4)]%Z m) as MU.
  pose proof (wmono_refl ssegs m) as WM.
  ceil_facts. pose proof (rerrno_addr tp TP) as ETP.
  rewrite ETP in ERR. rewrite ETP.
  (* [comment removed for export] *)
  st1.
  (* [comment removed for export] *)
  st1. st1. st1. st1. st1. st1. st1. st1.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
    assert (MR2 : rmrep st mX) by (eapply (rmrep_transport_frame_errno st m mX (bv_unsigned sp)); [exact MR | exact MU | exact WM | ceil_facts; lia]) end.
  release_frame FR ST (bv_unsigned sp).
  apply evt_done. unfold rffin_post. do 16 eexists. split; [reflexivity|].
  split; [fastfirst (first [ noevar_assumption |exact MU | replace (the_tb + 40) with (RERRNO + 4) by lia; exact MU])|]. split; [exact WM|]. split; [assumption|]. split; [exact ST|]. split; [| exact MR2].
  rewrite ?ETP.
  eapply rw_cells_congr; [| | | exact ERR]; [cbn [cells_bytes cbytes app]; rewrite EW; reflexivity| reflexivity| cbn; tauto].
Qed.
End Sz5.
Lemma rfree_fin1 : ltac:(let t := eval cbv delta [rfree_fin1__stmt] in rfree_fin1__stmt in exact t).
Proof using Type. intros sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 x1 ra ew bw lw e' F fc m junk lo st errv. ltac2:(SecDiet.SzSec.closeP 'rfree_fin1__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.

End PORT.

End WithCeil.

(* [comment removed for export] *)
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require ImgTgtUbsan.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require TlsBaseU.
Module TwB.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.AllocBridge__Spec.AllocBridge.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.TlsBaseU.
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Tac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Image OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ZBridge OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.SysStep OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Arr.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.SFModel.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ImgTgtUbsan.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.F_malloc_free__MA.F_malloc_free OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.F_am_F__MA.F_free_C.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RMallocRep__S3.RMallocRep.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RMallocRep__S3.RMallocTree.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RMallocRep__S3.RMallocKit_B.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RMallocRep__S3.RMallocKit_B3.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RF_get_meta__S3.RF_get_meta.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RF_mm_syscalls__S3.RF_mm_syscalls.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RF_malloc_entry__S3.RPeek.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.STree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Malloc OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MallocCtrl.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MSecret.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.LiaPin.
(* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac lia ::= pinned_lia.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
Section WithCeil.
Context {CEILV : CEIL} {MSECV : MSEC}.
Section PORT.
Context {PState : Type} {AS : AllocSt PState} {TB : TlsBase}.
Let TLSFACTS := the_tb_facts (TB:=TB).

Definition rffin_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (lo : Z) (W : list (Z * Z)) (m : word -> option byte) (st : mstate) (errv : word) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom usegs)
    /\ munch W m m' /\ wmono usegs m m' /\ mem_inv usegs m'
    /\ stk usegs m' lo (bv_unsigned sp)
    /\ rw_cells usegs m' (errno_addr tp) [C4 errv]
    /\ rmrep st m'.

Definition rfree_fin0__stmt : Prop := forall (sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 x1 ra bw q0 q1 : word) F fc
    (m : word -> option byte) (junk : list byte) (lo : Z) (st : mstate) (errv : word),
  tp = Z_to_bv 64 RATP ->
  rmrep st m -> mem_inv usegs m ->
  rw_cells usegs m (bv_unsigned sp + -48) [CB 8 junk; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
  rw_cells usegs m (errno_addr tp) [C4 errv] ->
  stk usegs m lo (bv_unsigned sp + -48) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - 48 ->
  evt usegs (rffin_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo [(bv_unsigned sp - 48, bv_unsigned sp)]%Z m st errv)
      (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 q0 q1 bw (wz 0) a2 a3 a4 a5 a6 a7
               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x19204) fc None m (seg_rom usegs)).
Section Sz1.
Variables sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 x1 ra bw q0 q1 F fc m junk lo st errv : ltac2:(SecDiet.SzSec.tyM 'rfree_fin0__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @sp).
Lemma rfree_fin0__body : ltac2:(SecDiet.SzSec.bodyP 'rfree_fin0__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
Proof using Type. pin_using tt. ceil_facts. msec_facts.
 intros TP MR MI FR ERR ST LO LOLE.
  pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp)]%Z m) as MU.
  pose proof (wmono_refl usegs m) as WM.
  pose proof MR as (WF & CX & GL & AR & GR & SH). destruct GL as (LK & NL & _).
  unfold RMLOCK, RNEED_LOCKS in *; ceil_facts.
  assert (TPR : 164 <= bv_unsigned tp < 2^64) by (rewrite TP, RATP_unsigned; lia). pose proof (rerrno_addr tp TP) as ETP.
  (* [comment removed for export] *)
  st1. st1. st1. st1.
  (* [comment removed for export] *)
  st1.
  eapply evt_cut.
  { eapply runlock_spec; rewrite unsigned_lit by lia; [reflexivity| exact LK]. }
  intros ms' ->.
  replace (ret_pc (Z_to_bv 64 0x19218)) with (Z_to_bv 64 0x19218) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]).
  (* [comment removed for export] *)
  st1. if_cases K; zify_cond K. 2:{ exfalso. apply K. reflexivity. }
  st1. st1. st1. st1. st1. st1. st1.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
    assert (MR2 : rmrep st mX)
      by (eapply rmrep_transport_high; [exact MR | exact MU | exact WM | intros l h [E|[]]; inversion E; subst; ceil_facts; lia]) end.
  release_frame FR ST (bv_unsigned sp).
  apply evt_done. unfold rffin_post. do 16 eexists. split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact ST|]. split; [| exact MR2].
  exact ERR.
Qed.
End Sz1.
Lemma rfree_fin0 : ltac:(let t := eval cbv delta [rfree_fin0__stmt] in rfree_fin0__stmt in exact t).
Proof using Type. intros sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 x1 ra bw q0 q1 F fc m junk lo st errv. ltac2:(SecDiet.SzSec.closeP 'rfree_fin0__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.

(* [comment removed for export] *)
Definition rfmun_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (lo : Z) (junk : list byte) (m : word -> option byte) (st : mstate) (errv bw lw : word) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR (Z_to_bv 64 0x19234) (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 bw lw bw lw a2 a3 a4 a5 a6 a7
                  (Z_to_bv 64 (errno_addr tp)) (sx32 errv) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (Z_to_bv 64 rmunmap_entry) fc None m' (seg_rom usegs)
    /\ munch [(bv_unsigned sp - 48, bv_unsigned sp)]%Z m m' /\ wmono usegs m m' /\ mem_inv usegs m'
    /\ stk usegs m' lo (bv_unsigned sp + -48)
    /\ rw_cells usegs m' (bv_unsigned sp + -48) [CB 8 junk; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]
    /\ rw_cells usegs m' (errno_addr tp) [C4 errv]
    /\ rmrep st m'.

Definition rfree_tomunmap__stmt : Prop := forall (sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 x1 ra bw q0 q1 : word) F fc
    (m : word -> option byte) (junk : list byte) (lo len : Z) (st : mstate) (errv : word),
  tp = Z_to_bv 64 RATP ->
  rmrep st m -> mem_inv usegs m -> 0 < len < 2^64 ->
  rw_cells usegs m (bv_unsigned sp + -48) [CB 8 junk; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
  rw_cells usegs m (errno_addr tp) [C4 errv] ->
  stk usegs m lo (bv_unsigned sp + -48) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - 48 ->
  evt usegs (rfmun_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo junk m st errv bw (wz len))
      (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 q0 q1 bw (wz len) a2 a3 a4 a5 a6 a7
               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x19204) fc None m (seg_rom usegs)).
Section Sz2.
Variables sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 x1 ra bw q0 q1 F fc m junk lo len st errv : ltac2:(SecDiet.SzSec.tyM 'rfree_tomunmap__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @sp).
Lemma rfree_tomunmap__body : ltac2:(SecDiet.SzSec.bodyP 'rfree_tomunmap__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
Proof using Type. pin_using tt. ceil_facts. msec_facts.
 intros TP MR MI HL FR ERR ST LO LOLE.
  pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp)]%Z m) as MU.
  pose proof (wmono_refl usegs m) as WM.
  pose proof MR as (WF & CX & GL & AR & GR & SH). destruct GL as (LK & NL & _).
  unfold RMLOCK, RNEED_LOCKS in *; ceil_facts.
  assert (TPR : 164 <= bv_unsigned tp < 2^64) by (rewrite TP, RATP_unsigned; lia). pose proof (rerrno_addr tp TP) as ETP.
  (* [comment removed for export] *)
  st1. st1. st1. st1.
  (* [comment removed for export] *)
  st1.
  eapply evt_cut.
  { eapply runlock_spec; rewrite unsigned_lit by lia; [reflexivity| exact LK]. }
  intros ms' ->.
  replace (ret_pc (Z_to_bv 64 0x19218)) with (Z_to_bv 64 0x19218) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]).
  (* [comment removed for export] *)
  st1. if_cases K; zify_cond K. { exfalso. rewrite wz_unsigned in K by lia. lia. }
  (* [comment removed for export] *)
  st1. st1. st1. st1.
  replace (ret_pc (Z_to_bv 64 0x19220)) with (Z_to_bv 64 0x19220) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]).
  (* [comment removed for export] *)
  st1. st1. st1. st1. st1.
  lazymatch goal with |- evt _ _ (MS ?R _ _ _ _ ?mX _) =>
    assert (MR2 : rmrep st mX)
      by (eapply rmrep_transport_high; [exact MR | exact MU | exact WM | intros l h [E|[]]; inversion E; subst; ceil_facts; lia]) end.
  apply evt_done. unfold rfmun_post. do 14 eexists. split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact ST|]. split; [exact FR|].
  split; [exact ERR| exact MR2].
Qed.
End Sz2.
Lemma rfree_tomunmap : ltac:(let t := eval cbv delta [rfree_tomunmap__stmt] in rfree_tomunmap__stmt in exact t).
Proof using Type. intros sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 x1 ra bw q0 q1 F fc m junk lo len st errv. ltac2:(SecDiet.SzSec.closeP 'rfree_tomunmap__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.

(* [comment removed for export] *)
Definition rerrno_avoids_repfoot__stmt : Prop := forall st m a, rmrep st m -> RERRNO <= a < RERRNO + 4 -> ~ rrepfoot st a.
Section Sz3.
Variables st m a : ltac2:(SecDiet.SzSec.tyM 'rerrno_avoids_repfoot__stmt "vvv" @st).
Lemma rerrno_avoids_repfoot__body : ltac2:(SecDiet.SzSec.bodyP 'rerrno_avoids_repfoot__stmt "vvv").
Proof using Type. pin_using tt. ceil_facts. msec_facts.
  intros MR Ha.
 pose proof MR as (WF & _). pose proof WF as (Hres & WR & DJ & WA & WG).
  intros [C|[C|[C|[C|[C|[C|[C|[C|C]]]]]]]].
  - unfold RCTX in C. lia.
  - unfold RMLOCK in C. lia.
  - unfold RNEED_LOCKS in C. lia.
  - unfold RPAGE_SIZE in C. lia.
  - destruct C as (ak & ar & Hak & Hin).
    destruct (rarea_conc st ak ar WF Hak) as (ra & Hra & Ca & Sa0 & Sa1 & SaL & NK & RB0 & RBAL & RBC).
    destruct (WR _ _ Hra) as (_ & _ & _ & _ & RF). destruct (rreserved_disjoint _ _ RF) as [D1 D2]. pose proof (rreserved_tlsF _ _ RF). pose proof (round_up_pg_ge (r_len ra)). lia.
  - destruct C as (b & gh & Hb & Hin).
    destruct (rgroup_conc st b gh WF Hb) as (rb & Hrb & Cb & Krb & Sb0 & Sb1 & SbA & RB0 & RBC).
    destruct (WR _ _ Hrb) as (_ & _ & _ & _ & RF). destruct (rreserved_disjoint _ _ RF) as [D1 D2]. pose proof (rreserved_tlsF _ _ RF). pose proof (round_up_pg_ge (r_len rb)). lia.
  - destruct C as (rid & r & v & Hr & Hk & Hin & HC).
    destruct (WR _ _ Hr) as (_ & _ & _ & _ & RF). destruct (rreserved_disjoint _ _ RF) as [D1 D2]. pose proof (rreserved_tlsF _ _ RF). lia.
  - unfold RGOT_SSP in C. lia.
  - unfold RSSP_GUARD in C. lia.
Qed.
End Sz3.
Lemma rerrno_avoids_repfoot : ltac:(let t := eval cbv delta [rerrno_avoids_repfoot__stmt] in rerrno_avoids_repfoot__stmt in exact t).
Proof using Type. intros st m a. ltac2:(SecDiet.SzSec.closeP 'rerrno_avoids_repfoot__body "vvv"). Qed.

Definition rmrep_transport_frame_errno__stmt : Prop := forall st m m' (sp : Z),
  rmrep st m -> munch [(sp - 48, sp); (RERRNO, RERRNO + 4)]%Z m m' -> wmono usegs m m' -> alloc_ceiling <= sp - 48 -> rmrep st m'.
Section Sz4.
Variables st m m' sp : ltac2:(SecDiet.SzSec.tyM 'rmrep_transport_frame_errno__stmt "vvvv" @st).
Lemma rmrep_transport_frame_errno__body : ltac2:(SecDiet.SzSec.bodyP 'rmrep_transport_frame_errno__stmt "vvvv").
Proof using Type. pin_using tt. ceil_facts. msec_facts.
  intros MR MU WM HS.
 eapply rmrep_transport_unowned; [exact MR | exact MU | exact WM |].
  apply ivs_avoid_cons; [| apply ivs_avoid_cons; [| apply ivs_avoid_nil]].
  - intros a Ha. pose proof MR as (WF & _). pose proof WF as (Hres & WR & DJ & WA & WG). ceil_facts.
    intros [C|[C|[C|[C|[C|[C|[C|[C|C]]]]]]]].
    + unfold RCTX in C. lia.
    + unfold RMLOCK in C. lia.
    + unfold RNEED_LOCKS in C. lia.
    + unfold RPAGE_SIZE in C. lia.
    + destruct C as (ak & ar & Hak & Hin).
      destruct (rarea_conc st ak ar WF Hak) as (ra & Hra & Ca & Sa0 & Sa1 & SaL & NK & RB0 & RBAL & RBC). ceil_facts. lia.
    + destruct C as (b & gh & Hb & Hin).
      destruct (rgroup_conc st b gh WF Hb) as (rb & Hrb & Cb & Krb & Sb0 & Sb1 & SbA & RB0 & RBC). ceil_facts. lia.
    + destruct C as (rid & r & v & Hr & Hk & Hin & HC).
      destruct (WR _ _ Hr) as (_ & _ & _ & RBC & _). ceil_facts. lia.
    + unfold RGOT_SSP in C. lia.
    + unfold RSSP_GUARD in C. lia.
  - intros a Ha. eapply rerrno_avoids_repfoot; [exact MR | exact Ha].
Qed.
End Sz4.
Lemma rmrep_transport_frame_errno : ltac:(let t := eval cbv delta [rmrep_transport_frame_errno__stmt] in rmrep_transport_frame_errno__stmt in exact t).
Proof using Type. intros st m m' sp. ltac2:(SecDiet.SzSec.closeP 'rmrep_transport_frame_errno__body "vvvv"). Qed.

(* [comment removed for export] *)
Definition rfree_fin1__stmt : Prop := forall (sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 x1 ra ew bw lw e' : word) F fc
    (m : word -> option byte) (junk : list byte) (lo : Z) (st : mstate) (errv : word),
  tp = Z_to_bv 64 RATP ->
  rmrep st m -> mem_inv usegs m ->
  rw_cells usegs m (bv_unsigned sp + -48) [CB 8 junk; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
  le4 ew = le4 errv ->
  rw_cells usegs m (errno_addr tp) [C4 e'] ->
  stk usegs m lo (bv_unsigned sp + -48) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - 48 ->
  evt usegs (rffin_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo [(bv_unsigned sp - 48, bv_unsigned sp); (RERRNO, RERRNO + 4)]%Z m st errv)
      (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 bw lw a0 a1 a2 a3 a4 a5 a6 a7
               (Z_to_bv 64 (errno_addr tp)) ew s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x19234) fc None m (seg_rom usegs)).
Section Sz5.
Variables sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 x1 ra ew bw lw e' F fc m junk lo st errv : ltac2:(SecDiet.SzSec.tyM 'rfree_fin1__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @sp).
Lemma rfree_fin1__body : ltac2:(SecDiet.SzSec.bodyP 'rfree_fin1__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
Proof using Type. pin_using tt. ceil_facts. msec_facts.
 intros TP MR MI FR EW ERR ST LO LOLE.
  pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp); (RERRNO, RERRNO + 4)]%Z m) as MU.
  pose proof (wmono_refl usegs m) as WM.
  ceil_facts. pose proof (rerrno_addr tp TP) as ETP.
  rewrite ETP in ERR. rewrite ETP.
  (* [comment removed for export] *)
  st1.
  (* [comment removed for export] *)
  st1. st1. st1. st1. st1. st1. st1. st1.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
    assert (MR2 : rmrep st mX) by (eapply (rmrep_transport_frame_errno st m mX (bv_unsigned sp)); [exact MR | exact MU | exact WM | ceil_facts; lia]) end.
  release_frame FR ST (bv_unsigned sp).
  apply evt_done. unfold rffin_post. do 16 eexists. split; [reflexivity|].
  split; [fastfirst (first [ noevar_assumption |exact MU | replace (the_tb + 40) with (RERRNO + 4) by lia; exact MU])|]. split; [exact WM|]. split; [assumption|]. split; [exact ST|]. split; [| exact MR2].
  rewrite ?ETP.
  eapply rw_cells_congr; [| | | exact ERR]; [cbn [cells_bytes cbytes app]; rewrite EW; reflexivity| reflexivity| cbn; tauto].
Qed.
End Sz5.
Lemma rfree_fin1 : ltac:(let t := eval cbv delta [rfree_fin1__stmt] in rfree_fin1__stmt in exact t).
Proof using Type. intros sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 x1 ra ew bw lw e' F fc m junk lo st errv. ltac2:(SecDiet.SzSec.closeP 'rfree_fin1__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.

End PORT.

End WithCeil.
End TwB.
End RF_free_C.

(* [comment removed for export] *)
Module RF_malloc_bigw.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require AllocBridge__Spec. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.AllocBridge__Spec.AllocBridge.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require Import TlsBase.
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import Tac Image ZBridge SysStep  ITree Nodes Decode Arr.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require Import SFModel.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import ImgSrc3.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require F_malloc_free__MA. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require MallocTree. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require MallocFacts_A__MA. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require MallocBlocks__MA. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require MallocKit_A2__MA. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.F_malloc_free__MA.F_malloc_free OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.F_malloc_free__MA.F_malloc_fast OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.F_malloc_free__MA.F_malloc_enframe OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocTree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocFacts_A__MA.MallocFacts_A OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocFacts_A__MA.MallocKit_A OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocBlocks__MA.MallocKit_AB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocKit_A2__MA.MallocKit_A2.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require STree Malloc MallocCtrl Monad. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require AllocBridge__Spec. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require MI_Realloc2__Spec. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.STree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Malloc OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MallocCtrl OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Monad OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.AllocBridge__Spec.AllocBridge OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_Realloc2__Spec.ProgFull.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require Import Malloc_fp F_malloc_bigw.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require RMallocRep__S3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require RF_get_meta__S3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require RF_malloc_entry__S3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require RMallocKit_A. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require RF_enframe. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require RF_free_K__S3. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RMallocRep__S3.RMallocRep OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RMallocRep__S3.RMallocTree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RF_get_meta__S3.RF_get_meta OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RMallocRep__S3.RMallocKit_B OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RF_malloc_entry__S3.RMallocKit_B2 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RMallocRep__S3.RMallocKit_B3 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RF_mm_syscalls__S3.RF_mm_syscalls OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RMallocKit_A OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RF_malloc_entry__S3.RMalloc_fp OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RF_enframe OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RF_free_K__S3.RMallocKit_A2.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require Import MSecret.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import LiaPin.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require SecDiet.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac lia ::= pinned_lia.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Ltac fix_lit_store :=
  try (lazymatch goal with
       | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 8 ?z)) _) =>
           change (Z_to_le_bytes 8 z) with (le8 (Z_to_bv 64 z)); mem_after_store
       | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 4 ?z)) _) =>
           change (Z_to_le_bytes 4 z) with (le4 (Z_to_bv 64 z)); mem_after_store
       | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 1 ?z)) _) =>
           change (Z_to_le_bytes 1 z) with [Z_to_bv 8 z]; mem_after_store
       | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (le1 (Z_to_bv 64 ?z))) _) =>
           change (le1 (Z_to_bv 64 z)) with [Z_to_bv 8 z]; mem_after_store
       end).

Ltac raw_store_finishR A bs' FR ST MU WM SOK :=
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?mX ?a ?bs) _) =>
    replace (write_to_mem mX a bs) with (write_to_mem mX (wa A) bs')
      by (f_equal; try reflexivity; try (rewrite le1_lit by lia; reflexivity); unfold wa, RCTX; f_equal; lia);
    let L := fresh "LEN" in
    assert (L : Z.of_nat (length bs') = Z.of_nat (length bs')) by reflexivity;
    rewrite ?length_le8, ?length_le4, ?length_le2 in L at 1; cbn [length] in L;
    apply (rw_cells_frame ssegs mX _ _ A bs') in FR; [| unfold RCTX; lia | rewrite <- L; unfold RCTX; lia | rewrite <- L; unfold RCTX; cbn [cells_size csize Nat.add]; lia];
    apply (stk_write ssegs mX _ _ A bs') in ST; [| unfold RCTX; lia | rewrite <- L; unfold RCTX; lia];
    apply (munch_write _ _ mX A bs') in MU; [| unfold RCTX; lia | rewrite <- L; unfold RCTX; lia | rewrite <- L; unfold RCTX; cbn [inside]; lia];
    apply (wmono_write ssegs _ mX (wa A) bs') in WM;
    lazymatch goal with HI : mem_inv ssegs mX |- _ =>
      apply (mem_inv_store ssegs mX (wa A) bs') in HI;
      [| fastfirst (first [ exact SOK | rewrite <- ?L; replace (wa A) with a by (unfold wa, RCTX; f_equal; lia); exact SOK ]) ]
    end;
    clear L SOK;
    let m' := fresh "m" in remember (write_to_mem mX (wa A) bs') as m' eqn:Em'; clear Em'
  end.

Section WithCeil.
Context {CEILV : CEIL} {MSECV : MSEC}.
Section PORT.
Context {PState : Type} {AS : AllocSt PState} {TB : TlsBase}.
Let TLSFACTS := the_tb_facts (TB:=TB).

Lemma rzeros_bytes_at : forall m x k, 0 <= x -> x + Z.of_nat k <= 2^64 ->
  (forall o, 0 <= o < Z.of_nat k -> bytes_at ssegs m (x + o) [b8 0]) -> bytes_at ssegs m x (zeros k).
Proof using MSECV TB. pin_using (fun (MSECV TB : unit) => tt). ceil_facts. msec_facts.
  intros m x k X0 XK H. split; [lia|]. split; [unfold zeros; rewrite repeat_length; lia|].
  intros i Hi. unfold zeros in Hi |- *. rewrite repeat_length in Hi.
  rewrite nth_error_repeat by exact Hi.
  destruct (H (Z.of_nat i) ltac:(lia)) as (_ & _ & HB). specialize (HB 0%nat ltac:(cbn; lia)). cbn [nth_error] in HB.
  rewrite Z.add_0_r in HB. exact HB.
Qed.

(* [comment removed for export] *)
Lemma lor_land_2048_4064 x : 0 <= x -> Z.lor (Z.land x 18446744073709549568) 4064 = Z.lor (Z.land x 18446744073709547520) 4064.
Proof using MSECV TB. pin_using (fun (MSECV TB : unit) => tt). ceil_facts. msec_facts.
  intros Hx. apply Z.bits_inj'. intros i Hi. rewrite !Z.lor_spec, !Z.land_spec.
  change 18446744073709549568 with (Z.ldiff (Z.ones 64) (Z.ones 11)). change 18446744073709547520 with (Z.ldiff (Z.ones 64) (Z.ones 12)).
  rewrite !Z.ldiff_spec, !Z.testbit_ones by lia.
  assert (T4064 : Z.testbit 4064 i = ((5 <=? i) && (i <? 12))).
  { change 4064 with (Z.ldiff (Z.ones 12) (Z.ones 5)). rewrite Z.ldiff_spec, !Z.testbit_ones by lia.
    destruct (Z.leb_spec 0 i); destruct (Z.ltb_spec i 12); destruct (Z.ltb_spec i 5); destruct (Z.leb_spec 5 i); cbn; try reflexivity; lia. }
  rewrite T4064.
  destruct (Z.leb_spec 0 i); destruct (Z.ltb_spec i 64); destruct (Z.ltb_spec i 11); destruct (Z.ltb_spec i 12); destruct (Z.leb_spec 5 i); cbn;
    rewrite ?andb_true_r, ?andb_false_r, ?orb_true_r, ?orb_false_r; try reflexivity; try lia.
Qed.

Lemma rbig_word_eq rid n : 0 <= n < 2^32 ->
  Z.lor (Z.land (n + 4064 + 51) 18446744073709549568) 4064 = meta_word (big_meta rid n).
Proof using MSECV TLSFACTS. pin_using (fun (MSECV TLSFACTS : unit) => tt). ceil_facts. msec_facts.
  intros Hn. rewrite lor_land_2048_4064 by lia. rewrite land_m4096 by lia.
  unfold meta_word, big_meta. cbn [m_last_idx m_freeable m_sizeclass m_maplen]. rewrite big_ml_eq by lia.
  replace (n + 4064 + 51) with (n + 4115) by lia.
  assert (D : Z.land (n + 4115 - (n + 4115) mod 4096) 4064 = 0).
  { apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec, Z.bits_0.
    replace (n + 4115 - (n + 4115) mod 4096) with (4096 * ((n + 4115) / 4096)) by (Z.div_mod_to_equations; lia).
    destruct (Z.lt_ge_cases i 12).
    - rewrite Z.mul_comm. change 4096 with (2 ^ 12). rewrite Z.mul_pow2_bits_low by lia. reflexivity.
    - replace (Z.testbit 4064 i) with false; [apply andb_false_r|]. symmetry. apply Z.bits_above_log2; [lia|]. cbn. lia. }
  rewrite <- Z.lxor_lor by exact D. rewrite <- Z.add_nocarry_lxor by exact D. Z.div_mod_to_equations. lia.
Qed.

Lemma le4_sxv_succ c : 0 <= c -> le4 (Z_to_bv 64 (bv_unsigned (wz (sxv c)) + 1)) = le4 (wz (u32 (c + 1))).
Proof using MSECV TB. pin_using (fun (MSECV TB : unit) => tt). ceil_facts. msec_facts.
  intros Hc. apply le4_congr. rewrite (wz_unsigned (sxv c)) by apply sxv_range.
  rewrite unsigned_lit_wrap. rewrite (wz_unsigned (u32 (c + 1))) by (unfold u32; Z.div_mod_to_equations; lia).
  unfold u32. rewrite (MallocRep.mod_mod_pow2 _ 32 64) by lia.
  rewrite <- Zplus_mod_idemp_l, sxv_mod32, Zplus_mod_idemp_l. rewrite Z.mod_mod by lia. reflexivity.
Qed.

Lemma le4_swrap_succ c0 : 0 <= c0 < 2^32 -> le4 (Z_to_bv 64 (bv_swrap 32 c0 + 1)) = le4 (wz (u32 (c0 + 1))).
Proof using MSECV TLSFACTS. pin_using (fun (MSECV TLSFACTS : unit) => tt). ceil_facts. msec_facts.
  intros Hc. apply le4_congr. rewrite unsigned_lit_wrap. rewrite (wz_unsigned (u32 (c0 + 1))) by (unfold u32; Z.div_mod_to_equations; lia).
  unfold u32, bv_swrap, bv_wrap. change (bv_modulus 32) with (2^32). change (bv_half_modulus 32) with (2^31).
  Z.div_mod_to_equations. lia.
Qed.

(* [comment removed for export] *)
Definition rbig_fail1_walk__stmt : Prop := forall (sp gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 ra' nw rav s0v s1v s2v s3v s4v : word) F fc (m : mem) (lo : Z),
  rw_cells ssegs m (bv_unsigned sp + -48) [C8 s4v; C8 s3v; C8 s2v; C8 s1v; C8 s0v; C8 rav] ->
  stk ssegs m lo (bv_unsigned sp + -48) -> lo <= bv_unsigned sp - 48 -> 48 <= bv_unsigned sp ->
  evt ssegs (fun ms' => ms' = MS (mkR rav sp gp tp t0 t1 t2 s0v s1v (wz 0) a1 a2 a3 a4 a5 a6 a7 s2v s3v s4v s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                F (ret_pc rav) fc None m (seg_rom ssegs)
                        /\ stk ssegs m lo (bv_unsigned sp))
      (MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 nw (Z_to_bv 64 RMLOCK) (Z_to_bv 64 (-1)) a1 a2 a3 a4 a5 a6 a7
               (Z_to_bv 64 (-1)) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x192f4) fc None m (seg_rom ssegs)).
Section Sz2.
Variables sp gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 ra' nw rav s0v s1v s2v s3v s4v F fc m lo : ltac2:(SecDiet.SzSec.tyM 'rbig_fail1_walk__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @sp).
Lemma rbig_fail1_walk__body : ltac2:(SecDiet.SzSec.bodyP 'rbig_fail1_walk__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
Proof using MSECV TB. pin_using (fun (MSECV TB : unit) => tt). ceil_facts. msec_facts.
  intros FR ST LO SP48.
  pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  step. if_cases K; zify_cond K. 2:{ exfalso. apply K. reflexivity. }
  step. step. step. step. step. step. step. step. step.
  release_frame FR ST (bv_unsigned sp).
  apply evt_done. split; [reflexivity| exact ST].
Qed.
End Sz2.
Lemma rbig_fail1_walk : ltac:(let t := eval cbv delta [rbig_fail1_walk__stmt] in rbig_fail1_walk__stmt in exact t).
Proof using MSECV TB. intros sp gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 ra' nw rav s0v s1v s2v s3v s4v F fc m lo. ltac2:(SecDiet.SzSec.closeP 'rbig_fail1_walk__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.

(* [comment removed for export] *)
Lemma rbig_fail2b_walk :
  forall (sp gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 ra' nw s1w rav s0v s1v s2v s3v s4v : word) F fc (m : mem) (lo : Z),
  rw_cells ssegs m (bv_unsigned sp + -48) [C8 s4v; C8 s3v; C8 s2v; C8 s1v; C8 s0v; C8 rav] ->
  stk ssegs m lo (bv_unsigned sp + -48) -> lo <= bv_unsigned sp - 48 -> 48 <= bv_unsigned sp ->
  evt ssegs (fun ms' => ms' = MS (mkR rav sp gp tp t0 t1 t2 s0v s1v (wz 0) a1 a2 a3 a4 a5 a6 a7 s2v s3v s4v s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                F (ret_pc rav) fc None m (seg_rom ssegs)
                        /\ stk ssegs m lo (bv_unsigned sp))
      (MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 nw s1w a0 a1 a2 a3 a4 a5 a6 a7
               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x194c0) fc None m (seg_rom ssegs)).
Proof using MSECV TB. pin_using (fun (MSECV TB : unit) => tt). ceil_facts. msec_facts.
  intros until lo. intros FR ST LO SP48.
  pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  step. step. step. step. step. step. step. step. step. step.
  release_frame FR ST (bv_unsigned sp).
  apply evt_done. split; [reflexivity| exact ST].
Qed.

(* [comment removed for export] *)
Definition rbig_fail2a_walk__stmt : Prop := forall (sp gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s2 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 ra' nw xw ndw : word) F fc (m : mem),
  rw_cells ssegs m RMLOCK [C4 (wz 0)] ->
  evt ssegs (fun ms' => ms' = MS (mkR (Z_to_bv 64 0x194c0) (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 nw (Z_to_bv 64 RMLOCK) xw ndw a2 a3 a4 a5 a6 a7
                                     s2 ndw xw s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 rmunmap_entry) fc None m (seg_rom ssegs))
      (MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 nw (Z_to_bv 64 RMLOCK) (wz 0) a1 a2 a3 a4 a5 a6 a7
               s2 ndw xw s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x193e8) fc None m (seg_rom ssegs)).
Section Sz4.
Variables sp gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s2 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 ra' nw xw ndw F fc m : ltac2:(SecDiet.SzSec.tyM 'rbig_fail2a_walk__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @sp).
Lemma rbig_fail2a_walk__body : ltac2:(SecDiet.SzSec.bodyP 'rbig_fail2a_walk__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
Proof using MSECV TB. pin_using (fun (MSECV TB : unit) => tt). ceil_facts. msec_facts.
  intros LK.
 unfold RMLOCK in *.
  step. if_cases K; zify_cond K. 2:{ exfalso. apply K. reflexivity. }
  step. step. step.
  eapply evt_cut. { eapply runlock_spec; rewrite unsigned_lit by lia; [reflexivity| exact LK]. }
  intros ms' ->.
  replace (ret_pc (Z_to_bv 64 0x194b4)) with (Z_to_bv 64 0x194b4) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]).
  step. step. step. apply evt_done. unfold rmunmap_entry. reflexivity.
Qed.
End Sz4.
Lemma rbig_fail2a_walk : ltac:(let t := eval cbv delta [rbig_fail2a_walk__stmt] in rbig_fail2a_walk__stmt in exact t).
Proof using MSECV TB. intros sp gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s2 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 ra' nw xw ndw F fc m. ltac2:(SecDiet.SzSec.closeP 'rbig_fail2a_walk__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.

Definition rseq_post (sp gp tp s5 s6 s7 s8 s9 s10 s11 t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 nw xw rav s0v s1v s2v s3v s4v : word)
    (F : bvmap 5 word) (fc : bv 32) (lo : Z) (st' : mstate) (m : mem) (n : Z) : machine_state -> Prop :=
  fun ms' => exists (a0 a1 : word) m',
    ms' = MS (mkR (Z_to_bv 64 0x193e8) (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 nw (Z_to_bv 64 RMLOCK)
                  a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 (-1)) (Z_to_bv 64 (n + 20)) xw s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (Z_to_bv 64 ralloc_meta_entry) fc None m' (seg_rom ssegs)
    /\ munch [(RCTX + 848, RCTX + 880); (RCTX + 912, RCTX + 913)]%Z m m'
    /\ wmono ssegs m m' /\ mem_inv ssegs m'
    /\ stk ssegs m' lo (bv_unsigned sp + -48)
    /\ rw_cells ssegs m' (bv_unsigned sp + -48) [C8 s4v; C8 s3v; C8 s2v; C8 s1v; C8 s0v; C8 rav]
    /\ rmrep st' m'.

(* [comment removed for export] *)
Definition rbig_seq_walk__stmt : Prop := forall (sp gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 ra' nw xw rav s0v s1v s2v s3v s4v : word) F fc (m : mem)
    (lo n : Z) (st : mstate),
  rmrep st m -> 0 <= c_seq (ctx st) < 256 ->
  bv_unsigned xw <> 2^64 - 1 ->
  rw_cells ssegs m (bv_unsigned sp + -48) [C8 s4v; C8 s3v; C8 s2v; C8 s1v; C8 s0v; C8 rav] ->
  stk ssegs m lo (bv_unsigned sp + -48) -> lo <= bv_unsigned sp - 48 -> alloc_ceiling <= lo -> mem_inv ssegs m ->
  evt ssegs (rseq_post sp gp tp s5 s6 s7 s8 s9 s10 s11 t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 nw xw rav s0v s1v s2v s3v s4v F fc lo (step_seq st) m n)
      (MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 nw (Z_to_bv 64 RMLOCK)
               xw a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 (-1)) (Z_to_bv 64 (n + 20)) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x192f4) fc None m (seg_rom ssegs)).
Section Sz5.
Variables sp gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 ra' nw xw rav s0v s1v s2v s3v s4v F fc m lo n st : ltac2:(SecDiet.SzSec.tyM 'rbig_seq_walk__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @sp).
Lemma rbig_seq_walk__body : ltac2:(SecDiet.SzSec.bodyP 'rbig_seq_walk__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
Proof using Type. pin_using tt. ceil_facts. msec_facts.
  intros MR SEQ XNE FR ST LO ILO MI.
  pose proof (munch_refl [(RCTX + 848, RCTX + 880); (RCTX + 912, RCTX + 913)]%Z m) as MU.
  pose proof (wmono_refl ssegs m) as WM.
  pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  pose proof (bv_unsigned_in_range _ xw) as XR. change (bv_modulus 64) with (2^64) in XR.
  pose proof MR as (_ & (_ & _ & _ & US & _ & C6) & (_ & NL & _) & _).
  unfold RNEED_LOCKS, RCTX, RMLOCK, ralloc_meta_entry in *; ceil_facts. unfold ctx_tail_cells in C6.
  replace (343456 + 912) with 344368 in C6 by reflexivity. replace (343456 + 848) with 344304 in US by reflexivity.
  (* [comment removed for export] *)
  step. if_cases K0; zify_cond K0. { exfalso. apply XNE. rewrite K0. reflexivity. } clear K0.
  (* [comment removed for export] *)
  step. step. step. rewrite ?zxb_b8 by lia. step. if_cases K1; zify_cond K1. 2:{ exfalso. rewrite ?wz_unsigned, ?unsigned_lit in K1 by lia. lia. } clear K1 NL.
  (* [comment removed for export] *)
  step. rewrite ?zxb_b8 by lia. step.
  (* [comment removed for export] *)
  assert (TAIL : forall (a1' : word) (mj : mem) (stj : mstate) (ns : Z),
    0 <= ns < 256 -> rmrep stj mj -> ctx_tail_cells stj = ctx_tail_cells st ->
    rw_cells ssegs mj (bv_unsigned sp + -48) [C8 s4v; C8 s3v; C8 s2v; C8 s1v; C8 s0v; C8 rav] ->
    stk ssegs mj lo (bv_unsigned sp + -48) -> mem_inv ssegs mj ->
    munch [(343456 + 848, 343456 + 880); (343456 + 912, 343456 + 913)]%Z m mj -> wmono ssegs m mj ->
    evt ssegs (rseq_post sp gp tp s5 s6 s7 s8 s9 s10 s11 t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 nw xw rav s0v s1v s2v s3v s4v F fc lo (upd_ctx (set_seq ns) stj) m n)
      (MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 nw (Z_to_bv 64 343448)
               (Z_to_bv 64 ns) a1' a2 a3 a4 a5 a6 a7 (Z_to_bv 64 (-1)) (Z_to_bv 64 (n + 20)) xw s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x193e0) fc None mj (seg_rom ssegs))).
  { intros a1' mj stj ns NS MRj CTj FRj STj MIj MUj WMj.
    pose proof MRj as (_ & (_ & _ & _ & _ & _ & C6j) & _). rewrite CTj in C6j. unfold ctx_tail_cells in C6j. unfold RCTX in C6j.
    replace (343456 + 912) with 344368 in C6j by reflexivity.
    pose proof (rw_cells_store_ok_at ssegs _ _ _ 0 (C1 (b8 (c_seq (ctx st)))) 1 (Z_to_bv 64 344368) C6j eq_refl eq_refl
                  ltac:(unfold wa; f_equal; lia)) as SOK.
    clear C6j.
    st1.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?mX _ _) _) =>
      pose proof (rmrep_set_seq stj mX ns MRj NS) as MR1; unfold RCTX in MR1 end.
    raw_store_finishR (343456 + 912) [b8 ns] FRj STj MUj WMj SOK.
    (* [comment removed for export] *)
    step.
    apply evt_done. unfold rseq_post, RCTX, RMLOCK, ralloc_meta_entry. do 3 eexists. split; [reflexivity|].
    split; [exact MUj|]. split; [exact WMj|]. split; [assumption|]. split; [assumption|]. split; [exact FRj|]. exact MR1. }
  step. if_cases K2; zify_cond K2; rewrite ?wz_unsigned, ?unsigned_lit in K2 by lia.
  - (* [comment removed for export] *)
    step. rewrite (wz_unsigned (c_seq (ctx st))) by lia.
    eapply evt_mono; [eapply (TAIL _ m st (c_seq (ctx st) + 1)); [lia| exact MR| reflexivity| exact FR| exact ST| exact MI| exact MU| exact WM]|].
    intros ms' PO. rewrite (step_seq_eq st). replace (c_seq (ctx st) =? 255) with false by (symmetry; apply Z.eqb_neq; lia). exact PO.
  - (* [comment removed for export] *)
    pose proof (rw_cells_of_u8arr ssegs _ _ _ US) as USC. rewrite unmap_seqs_length in USC. clear US.
    step. fix_lit_store. step. fix_lit_store. step. fix_lit_store. step. fix_lit_store.
    assert (UZ : u8arr ssegs m1 344304 (zeros 32)).
    { apply (u8arr_of_rw_cells ssegs m1 344304 32). apply (rw_cells_congr ssegs m1 344304 [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)] [CB 32 (zeros 32)]); [reflexivity| reflexivity| cbn; split; [reflexivity| exact I]| exact USC]. }
    clear USC.
    set (stz := upd_ctx (fun c => set_unmap_seq_map ∅ c) st).
    lazymatch goal with MUc : munch _ m m1, WMc : wmono ssegs m m1 |- _ =>
    assert (MRz : rmrep stz m1);
    [ eapply (rmrep_ctx_frameW st stz _ m1 _ MR MUc WMc); try reflexivity;
      [ intros lo' hi' [E|[E|[]]]; inversion E; subst; unfold RCTX; lia
      | right; split; [reflexivity| intros lo' hi' [E|[E|[]]]; inversion E; subst; unfold RCTX; lia]
      | right; split; [reflexivity| intros lo' hi' [E|[E|[]]]; inversion E; subst; unfold RCTX; lia]
      | right; split; [reflexivity| intros lo' hi' [E|[E|[]]]; inversion E; subst; unfold RCTX; lia]
      | left; unfold stz; rewrite unmap_seqs_empty; unfold RCTX; exact UZ
      | right; split; [reflexivity| intros lo' hi' [E|[E|[]]]; inversion E; subst; unfold RCTX; lia]
      | left; unfold RCTX; replace (343456 + 912) with 344368 by reflexivity;
        unfold ctx_tail_cells, brk_word, ctx, stz; cbn [s_ctx upd_ctx c_seq c_brk set_unmap_seq_map]; unfold brk_word, ctx in C6; exact C6 ] |] end.
    (* [comment removed for export] *)
    step. step.
    lazymatch goal with MUc : munch _ m ?mX, WMc : wmono ssegs m ?mX, FRc : rw_cells ssegs ?mX (bv_unsigned sp + -48) _, STc : stk ssegs ?mX _ _, MIc : mem_inv ssegs ?mX |- _ =>
      eapply evt_mono; [eapply (TAIL _ mX stz 1); [lia| exact MRz| reflexivity| exact FRc| exact STc| exact MIc| exact MUc| exact WMc]|] end.
    intros ms' PO. rewrite (step_seq_eq st). replace (c_seq (ctx st) =? 255) with true by (symmetry; apply Z.eqb_eq; lia). exact PO.
Qed.
End Sz5.
Lemma rbig_seq_walk : ltac:(let t := eval cbv delta [rbig_seq_walk__stmt] in rbig_seq_walk__stmt in exact t).
Proof using Type. intros sp gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 ra' nw xw rav s0v s1v s2v s3v s4v F fc m lo n st. ltac2:(SecDiet.SzSec.closeP 'rbig_seq_walk__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.

Section SUCC.
Variables (st : mstate) (m : mem) (g : aptr) (rid : N) (x n c lo : Z).
Let G := conc st g.
Hypothesis MR : rmrep st m.
Hypothesis TK : ticks_ok st.
Hypothesis G0 : get_meta_rec st g = meta0.
Hypothesis MSL : meta_slot st g.
Hypothesis RR : (s_regions st) !! rid = Some (mkRegion RKGroup x (n + IB + UNIT)).
Hypothesis GN : forall off, (s_groups st) !! (rid, off) = None.
Hypothesis AN : forall off, (s_areas st) !! (rid, off) = None.
Hypothesis SHN : (s_shadow st) !! rid = None.
Hypothesis HC : c_mmap_counter (ctx st) = c.
Hypothesis CR : 0 <= c < 2^32.
Hypothesis NR : MMAP_THRESHOLD <= n < 2^32.
Hypothesis CLO : alloc_ceiling <= lo.

Definition rbig_succ_walk__stmt : Prop := forall (sp gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s2 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 ra' gw s0v s1v s2v s3v s4v rav : word) F fc,
  bv_unsigned gw = G ->
  rw_cells ssegs m (bv_unsigned sp + -48) [C8 s4v; C8 s3v; C8 s2v; C8 s1v; C8 s0v; C8 rav] ->
  stk ssegs m lo (bv_unsigned sp + -48) -> lo <= bv_unsigned sp - 48 -> mem_inv ssegs m ->
  evt ssegs (fun ms' => exists (a0' a1' : word) m',
      ms' = MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 (Z_to_bv 64 n) (Z_to_bv 64 RMLOCK)
                   a0' a1' a2 a3 a4 a5 a6 a7 gw (wz 0) (wz x) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
              F (Z_to_bv 64 0x19580) fc None m' (seg_rom ssegs)
      /\ munch [(G, G + 40); (x, x + 8); (RCTX + 12, RCTX + 16)]%Z m m' /\ wmono ssegs m m' /\ mem_inv ssegs m'
      /\ stk ssegs m' lo (bv_unsigned sp + -48)
      /\ rw_cells ssegs m' (bv_unsigned sp + -48) [C8 s4v; C8 s3v; C8 s2v; C8 s1v; C8 s0v; C8 rav]
      /\ rmrep (big_st st g rid n (u32 (c + 1))) m' /\ ticks_ok (big_st st g rid n (u32 (c + 1))))
    (MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 (Z_to_bv 64 n) (Z_to_bv 64 RMLOCK)
             gw a1 a2 a3 a4 a5 a6 a7 s2 (Z_to_bv 64 (n + 20)) (wz x) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x193e8) fc None m (seg_rom ssegs)).
Section Sz6.
Variables sp gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s2 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 ra' gw s0v s1v s2v s3v s4v rav F fc : ltac2:(SecDiet.SzSec.tyM 'rbig_succ_walk__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @sp).
Lemma rbig_succ_walk__body : ltac2:(SecDiet.SzSec.bodyP 'rbig_succ_walk__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
Proof using AN CLO CR G0 GN HC MR MSL NR RR SHN TK. pin_using (fun (AN CLO CR G0 GN HC MR MSL NR RR SHN TK : unit) => tt). ceil_facts. msec_facts.
  intros HG FR ST LO MI.
 unfold MMAP_THRESHOLD in NR. unfold IB, UNIT in RR.
  set (r0 := mkRegion RKGroup x (n + 4 + 16)) in RR.
  pose proof (munch_refl [(G, G + 40); (x, x + 8); (RCTX + 12, RCTX + 16)]%Z m) as MU. pose proof (wmono_refl ssegs m) as WM.
  pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  pose proof MR as (WF & (CX1 & _) & _ & AR & GRP & SH). pose proof WF as (RS & WR & DJ & WA & WG).
  pose proof (rmeta_chunk_facts st m g MR MSL) as (CH & Gpos & GC & GI1 & GI2 & GRG & (rid0 & rg0 & Hrg0 & Krg0 & GL0 & GH0)).
  fold G in CH, Gpos, GC, GI1, GI2, GRG, GL0, GH0. rewrite G0 in CH. unfold meta_cells in CH. cbn [m_prev m_next m_mem m_avail m_freed meta0 pw oconc] in CH.
  change (meta_word meta0) with 0 in CH.
  destruct (WR rid r0 RR) as (X0 & _ & XL & XC & XRF). cbn [r_base r_len r0] in X0, XL, XC, XRF.
  pose proof (round_up_pg_ge (n + 4 + 16)) as XRU.
  destruct (rreserved_disjoint2 _ _ XRF ltac:(lia)) as [XI1 XI2].
  (* [comment removed for export] *)
  destruct (SH rid r0 RR eq_refl) as [XW XB]. cbn [r_base r_len r0] in XW, XB.
  assert (HDR : rw_cells ssegs m x [C8 (wz 0); C1 (b8 0)]).
  { apply rw_cells_of_bytes; [cbn; repeat split; reflexivity| |].
    - cbn [cells_bytes cbytes app]. change (le8 (wz 0) ++ [b8 0]) with (zeros 9).
      apply rzeros_bytes_at; [lia| cbn; ceil_facts; lia|].
      intros o Ho. cbn in Ho. refine (proj1 (XB o 0 ltac:(lia) _)).
      unfold get_shadow. rewrite SHN. apply cell_read_shadow0.
    - cbn. eapply wr_at_sub; [exact XW| lia| lia]. }
  (* [comment removed for export] *)
  pose proof (GRG rid r0 RR eq_refl) as GX. cbn [r_base r_len r0] in GX.
  rewrite <- HG in CH.
  unfold RCTX, RMLOCK in *; ceil_facts.
  (* [comment removed for export] *)
  step. if_cases K; zify_cond K; rewrite ?wz_unsigned in K by lia. { exfalso. lia. } clear K.
  (* [comment removed for export] *)
  unfold ctx_head_cells in CX1. rewrite HC in CX1.
  pose proof (rw_cells_prefix ssegs m _ [C8 (wz (c_secret (ctx st))); C4 (wz (c_init_done (ctx st))); C4 (wz c)] _ CX1) as CX3. clear CX1.
  assert (GW0 : gw = wz G) by (rewrite <- HG; symmetry; apply Z_to_bv_bv_unsigned).
  (* [comment removed for export] *)
  step. step.
  (* [comment removed for export] *)
  pose proof (munch_refl [(G, G + 40)]%Z m) as MUa. pose proof (wmono_refl ssegs m) as WMa.
  step.
  assert (PWX : pw st (Some (rid, 0)) = wz x).
  { unfold pw, oconc, conc, get_region. cbn [fst snd]. rewrite RR. cbn [r_base r0]. rewrite Z.add_0_r. reflexivity. }
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
    assert (CHA : rw_cells ssegs mX (conc st g) (meta_cells st (big_metaA rid)));
    [ unfold meta_cells; cbn [m_prev m_next m_mem m_avail m_freed big_metaA]; rewrite PWX;
      change (meta_word (big_metaA rid)) with 0; change (pw st None) with (wz 0); fold G; rewrite <- HG; exact CH
    | pose proof (rmrep_put_meta_frame st m mX g (big_metaA rid) MR MSL MUa WMa CHA) as MRA ] end.
  clear MUa WMa CHA.
  (* [comment removed for export] *)
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
    pose proof (munch_refl [(x, x + 8)]%Z mX) as MUb; pose proof (wmono_refl ssegs mX) as WMb end.
  cbv delta [wz]. step.
  set (stA := put_meta g (big_metaA rid) st) in MRA.
  destruct (rmrep_hdr_havoc stA _ (rid, 0) MRA TK) as [MRB0 TKB].
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
    assert (MRB1 : rmrep (hdr_havoc (rid, 0) stA) mX) end.
  { eapply (rmrep_transport_unowned _ _ _ _ MRB0 MUb WMb).
    intros lo' hi' a [E|[]] Ha. inversion E; subst lo' hi'. intros RF.
    destruct RF as [R1|[R2|[R3|[R4|[(ak & ar & Hak & Rak)|[(b & gh & Hb & Rb)|[(q & rq & v & Hq & Kq & Rq & Cq)|[R5|R6]]]]]]]].
    - unfold RCTX in R1. lia.
    - unfold RMLOCK in R2. lia.
    - unfold RNEED_LOCKS in R3. lia.
    - unfold RPAGE_SIZE in R4. lia.
    - change (s_areas (hdr_havoc (rid, 0) stA)) with (s_areas st) in Hak. change (conc (hdr_havoc (rid, 0) stA) ak) with (conc st ak) in Rak.
      destruct (rarea_conc st ak ar WF Hak) as (rga & Hra & Ca & Sa0 & Sa1 & _ & NK & _).
      assert (NE : fst ak <> rid) by (intros EQ; destruct ak as [ak1 ak2]; cbn in EQ; subst ak1; rewrite (AN ak2) in Hak; discriminate).
      pose proof (rarea_lr_lo st ak ar rga WF Hak Hra). destruct (DJ _ _ _ _ Hra RR NE) as [D|D]; cbn [r_base r_len r0 lr_lo r_kind] in D; lia.
    - change (s_groups (hdr_havoc (rid, 0) stA)) with (s_groups st) in Hb. change (conc (hdr_havoc (rid, 0) stA) b) with (conc st b) in Rb.
      destruct (rgroup_conc st b gh WF Hb) as (rb & Hrb & Cb & Kb & Sb0 & Sb1 & _).
      assert (NE : fst b <> rid) by (intros EQ; destruct b as [b1 b2]; cbn in EQ; subst b1; rewrite (GN b2) in Hb; discriminate).
      pose proof (lr_lo_group rb Kb). destruct (DJ _ _ _ _ Hrb RR NE) as [D|D]; cbn [r_base r_len r0 lr_lo r_kind] in D; lia.
    - change (s_regions (hdr_havoc (rid, 0) stA)) with (s_regions st) in Hq.
      destruct (N.eq_dec q rid) as [->|NE].
      + rewrite RR in Hq. inversion Hq; subst rq. cbn [r_base r0] in Cq.
        destruct (cell_read_hdr_havoc_fresh stA (rid, 0) (a - x) SHN ltac:(reflexivity) ltac:(cbn; lia)) as [h Hh].
        cbn [fst snd] in Hh. rewrite Z.add_0_l in Hh. rewrite Hh in Cq. discriminate.
      + pose proof (lr_lo_group rq Kq). destruct (DJ _ _ _ _ Hq RR NE) as [D|D]; cbn [r_base r_len r0 lr_lo r_kind] in D; lia.
    - unfold RGOT_SSP in R5. lia.
    - unfold RSSP_GUARD in R6. lia. }
  clear MRB0 MUb WMb.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
    assert (MRB : rmrep (put_group (rid, 0) (Some g) 0 (hdr_havoc (rid, 0) stA)) mX) end.
  { eapply (rmrep_put_group_new _ _ (rid, 0) g 0 r0 (b8 0) MRB1); [apply GN| exact RR| reflexivity| cbn; lia| cbn [snd r_len r0]; lia| reflexivity| |reflexivity].
    change (conc (hdr_havoc (rid, 0) stA) (rid, 0)) with (conc st (rid, 0)). change (pw (hdr_havoc (rid, 0) stA) (Some g)) with (wz G).
    unfold conc, get_region. cbn [fst snd]. rewrite RR. cbn [r_base r0]. rewrite Z.add_0_r. rewrite <- GW0. exact HDR. }
  clear MRB1.
  (* [comment removed for export] *)
  step. step. step. step. step. step.
  rewrite (unsigned_lit (n + 4115)) by lia.
  assert (LR : 0 <= Z.land (n + 4115) 18446744073709549568 <= n + 4115) by (split; [apply Z.land_nonneg; lia| apply land_le_l; lia]).
  rewrite (unsigned_lit (Z.land (n + 4115) 18446744073709549568)) by lia.
  replace (n + 4115) with (n + 4064 + 51) by lia. rewrite (rbig_word_eq rid n) by lia.
  pose proof (meta_word_big_range rid n ltac:(lia)) as MWR.
  (* [comment removed for export] *)
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
    pose proof (munch_refl [(G, G + 40)]%Z mX) as MUc; pose proof (wmono_refl ssegs mX) as WMc end.
  change (Z_to_bv 64 (meta_word (big_meta rid n))) with (wz (meta_word (big_meta rid n))).
  step. step. step.
  set (stB := put_group (rid, 0) (Some g) 0 (hdr_havoc (rid, 0) stA)) in MRB.
  lazymatch goal with H : rw_cells ssegs ?mX (bv_unsigned gw) _ |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
    assert (CHC : rw_cells ssegs mX (conc stB g) (meta_cells stB (big_meta rid n)));
    [ change (conc stB g) with G; rewrite <- HG; unfold meta_cells; cbn [m_prev m_next m_mem m_avail m_freed big_meta];
      change (pw stB (Some (rid, 0))) with (pw st (Some (rid, 0))); rewrite PWX; change (pw stB None) with (pw st None); exact H
    | pose proof (rmrep_put_meta_frame stB _ mX g (big_meta rid n) MRB MSL MUc WMc CHC) as MRC ] end.
  clear MUc WMc CHC MRB.
  (* [comment removed for export] *)
  step. rewrite (sx32_wz_sxv c) by lia. step.
  (* [comment removed for export] *)
  lazymatch goal with H : rw_cells ssegs ?mX 343456 _ |- _ =>
    pose proof (rw_cells_store_ok_at ssegs _ _ _ 12 (C4 (wz c)) 4 (Z_to_bv 64 343468) H eq_refl eq_refl ltac:(unfold wa; f_equal; lia)) as SOK;
    clear H end.
  st1. rewrite le4_swrap_succ by lia.
  set (stC := put_meta g (big_meta rid n) stB) in MRC.
  assert (VR : 0 <= u32 (c + 1) < 2^32) by (unfold u32; Z.div_mod_to_equations; lia).
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?mX _ _) _) =>
    pose proof (rmrep_set_mmap_counter stC mX (u32 (c + 1)) MRC VR) as MRD; unfold RCTX in MRD end.
  clear MRC.
  raw_store_finishR (343456 + 12) (le4 (wz (u32 (c + 1)))) FR ST MU WM SOK.
  (* [comment removed for export] *)
  step.
  apply evt_done. do 3 eexists. split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact ST|]. split; [exact FR|].
  split; [exact MRD| exact TKB].
Qed.
End Sz6.
Lemma rbig_succ_walk : ltac:(let t := eval cbv delta [rbig_succ_walk__stmt] in rbig_succ_walk__stmt in exact t).
Proof using AN CLO CR G0 GN HC MR MSL NR RR SHN TK. intros sp gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s2 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 ra' gw s0v s1v s2v s3v s4v rav F fc. ltac2:(SecDiet.SzSec.closeP 'rbig_succ_walk__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.
End SUCC.

End PORT.

End WithCeil.

(* [comment removed for export] *)
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require ImgTgtUbsan.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require TlsBaseU.
Module TwB.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.AllocBridge__Spec.AllocBridge.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.TlsBaseU.
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Tac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Image OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ZBridge OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.SysStep OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ITree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Nodes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Decode OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Arr.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.SFModel.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ImgTgtUbsan.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.F_malloc_free__MA.F_malloc_free OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.F_malloc_free__MA.F_malloc_fast OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.F_malloc_free__MA.F_malloc_enframe OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocTree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocFacts_A__MA.MallocFacts_A OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocFacts_A__MA.MallocKit_A OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocBlocks__MA.MallocKit_AB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocKit_A2__MA.MallocKit_A2.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.STree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Malloc OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MallocCtrl OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Monad OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.AllocBridge__Spec.AllocBridge OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_Realloc2__Spec.ProgFull.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.Malloc_fp OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.F_malloc_bigw.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RMallocRep__S3.RMallocRep.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RMallocRep__S3.RMallocTree.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RF_get_meta__S3.RF_get_meta.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RMallocRep__S3.RMallocKit_B.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RF_malloc_entry__S3.RMallocKit_B2.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RMallocRep__S3.RMallocKit_B3.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RF_mm_syscalls__S3.RF_mm_syscalls.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RMallocKit_A.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RF_malloc_entry__S3.RMalloc_fp.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RF_enframe.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RF_free_K__S3.RMallocKit_A2.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MSecret.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.LiaPin.
(* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac lia ::= pinned_lia.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Ltac fix_lit_store :=
  try (lazymatch goal with
       | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 8 ?z)) _) =>
           change (Z_to_le_bytes 8 z) with (le8 (Z_to_bv 64 z)); mem_after_store
       | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 4 ?z)) _) =>
           change (Z_to_le_bytes 4 z) with (le4 (Z_to_bv 64 z)); mem_after_store
       | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 1 ?z)) _) =>
           change (Z_to_le_bytes 1 z) with [Z_to_bv 8 z]; mem_after_store
       | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (le1 (Z_to_bv 64 ?z))) _) =>
           change (le1 (Z_to_bv 64 z)) with [Z_to_bv 8 z]; mem_after_store
       end).

Ltac raw_store_finishR A bs' FR ST MU WM SOK :=
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?mX ?a ?bs) _) =>
    replace (write_to_mem mX a bs) with (write_to_mem mX (wa A) bs')
      by (f_equal; try reflexivity; try (rewrite le1_lit by lia; reflexivity); unfold wa, RCTX; f_equal; lia);
    let L := fresh "LEN" in
    assert (L : Z.of_nat (length bs') = Z.of_nat (length bs')) by reflexivity;
    rewrite ?length_le8, ?length_le4, ?length_le2 in L at 1; cbn [length] in L;
    apply (rw_cells_frame usegs mX _ _ A bs') in FR; [| unfold RCTX; lia | rewrite <- L; unfold RCTX; lia | rewrite <- L; unfold RCTX; cbn [cells_size csize Nat.add]; lia];
    apply (stk_write usegs mX _ _ A bs') in ST; [| unfold RCTX; lia | rewrite <- L; unfold RCTX; lia];
    apply (munch_write _ _ mX A bs') in MU; [| unfold RCTX; lia | rewrite <- L; unfold RCTX; lia | rewrite <- L; unfold RCTX; cbn [inside]; lia];
    apply (wmono_write usegs _ mX (wa A) bs') in WM;
    lazymatch goal with HI : mem_inv usegs mX |- _ =>
      apply (mem_inv_store usegs mX (wa A) bs') in HI;
      [| fastfirst (first [ exact SOK | rewrite <- ?L; replace (wa A) with a by (unfold wa, RCTX; f_equal; lia); exact SOK ]) ]
    end;
    clear L SOK;
    let m' := fresh "m" in remember (write_to_mem mX (wa A) bs') as m' eqn:Em'; clear Em'
  end.

Section WithCeil.
Context {CEILV : CEIL} {MSECV : MSEC}.
Section PORT.
Context {PState : Type} {AS : AllocSt PState} {TB : TlsBase}.
Let TLSFACTS := the_tb_facts (TB:=TB).

Lemma rzeros_bytes_at : forall m x k, 0 <= x -> x + Z.of_nat k <= 2^64 ->
  (forall o, 0 <= o < Z.of_nat k -> bytes_at usegs m (x + o) [b8 0]) -> bytes_at usegs m x (zeros k).
Proof using MSECV TB. pin_using (fun (MSECV TB : unit) => tt). ceil_facts. msec_facts.
  intros m x k X0 XK H. split; [lia|]. split; [unfold zeros; rewrite repeat_length; lia|].
  intros i Hi. unfold zeros in Hi |- *. rewrite repeat_length in Hi.
  rewrite nth_error_repeat by exact Hi.
  destruct (H (Z.of_nat i) ltac:(lia)) as (_ & _ & HB). specialize (HB 0%nat ltac:(cbn; lia)). cbn [nth_error] in HB.
  rewrite Z.add_0_r in HB. exact HB.
Qed.

(* [comment removed for export] *)
Lemma lor_land_2048_4064 x : 0 <= x -> Z.lor (Z.land x 18446744073709549568) 4064 = Z.lor (Z.land x 18446744073709547520) 4064.
Proof using MSECV TB. pin_using (fun (MSECV TB : unit) => tt). ceil_facts. msec_facts.
  intros Hx. apply Z.bits_inj'. intros i Hi. rewrite !Z.lor_spec, !Z.land_spec.
  change 18446744073709549568 with (Z.ldiff (Z.ones 64) (Z.ones 11)). change 18446744073709547520 with (Z.ldiff (Z.ones 64) (Z.ones 12)).
  rewrite !Z.ldiff_spec, !Z.testbit_ones by lia.
  assert (T4064 : Z.testbit 4064 i = ((5 <=? i) && (i <? 12))).
  { change 4064 with (Z.ldiff (Z.ones 12) (Z.ones 5)). rewrite Z.ldiff_spec, !Z.testbit_ones by lia.
    destruct (Z.leb_spec 0 i); destruct (Z.ltb_spec i 12); destruct (Z.ltb_spec i 5); destruct (Z.leb_spec 5 i); cbn; try reflexivity; lia. }
  rewrite T4064.
  destruct (Z.leb_spec 0 i); destruct (Z.ltb_spec i 64); destruct (Z.ltb_spec i 11); destruct (Z.ltb_spec i 12); destruct (Z.leb_spec 5 i); cbn;
    rewrite ?andb_true_r, ?andb_false_r, ?orb_true_r, ?orb_false_r; try reflexivity; try lia.
Qed.

Lemma rbig_word_eq rid n : 0 <= n < 2^32 ->
  Z.lor (Z.land (n + 4064 + 51) 18446744073709549568) 4064 = meta_word (big_meta rid n).
Proof using MSECV TLSFACTS. pin_using (fun (MSECV TLSFACTS : unit) => tt). ceil_facts. msec_facts.
  intros Hn. rewrite lor_land_2048_4064 by lia. rewrite land_m4096 by lia.
  unfold meta_word, big_meta. cbn [m_last_idx m_freeable m_sizeclass m_maplen]. rewrite big_ml_eq by lia.
  replace (n + 4064 + 51) with (n + 4115) by lia.
  assert (D : Z.land (n + 4115 - (n + 4115) mod 4096) 4064 = 0).
  { apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec, Z.bits_0.
    replace (n + 4115 - (n + 4115) mod 4096) with (4096 * ((n + 4115) / 4096)) by (Z.div_mod_to_equations; lia).
    destruct (Z.lt_ge_cases i 12).
    - rewrite Z.mul_comm. change 4096 with (2 ^ 12). rewrite Z.mul_pow2_bits_low by lia. reflexivity.
    - replace (Z.testbit 4064 i) with false; [apply andb_false_r|]. symmetry. apply Z.bits_above_log2; [lia|]. cbn. lia. }
  rewrite <- Z.lxor_lor by exact D. rewrite <- Z.add_nocarry_lxor by exact D. Z.div_mod_to_equations. lia.
Qed.

Lemma le4_sxv_succ c : 0 <= c -> le4 (Z_to_bv 64 (bv_unsigned (wz (sxv c)) + 1)) = le4 (wz (u32 (c + 1))).
Proof using MSECV TB. pin_using (fun (MSECV TB : unit) => tt). ceil_facts. msec_facts.
  intros Hc. apply le4_congr. rewrite (wz_unsigned (sxv c)) by apply sxv_range.
  rewrite unsigned_lit_wrap. rewrite (wz_unsigned (u32 (c + 1))) by (unfold u32; Z.div_mod_to_equations; lia).
  unfold u32. rewrite (MallocRep.mod_mod_pow2 _ 32 64) by lia.
  rewrite <- Zplus_mod_idemp_l, sxv_mod32, Zplus_mod_idemp_l. rewrite Z.mod_mod by lia. reflexivity.
Qed.

Lemma le4_swrap_succ c0 : 0 <= c0 < 2^32 -> le4 (Z_to_bv 64 (bv_swrap 32 c0 + 1)) = le4 (wz (u32 (c0 + 1))).
Proof using MSECV TLSFACTS. pin_using (fun (MSECV TLSFACTS : unit) => tt). ceil_facts. msec_facts.
  intros Hc. apply le4_congr. rewrite unsigned_lit_wrap. rewrite (wz_unsigned (u32 (c0 + 1))) by (unfold u32; Z.div_mod_to_equations; lia).
  unfold u32, bv_swrap, bv_wrap. change (bv_modulus 32) with (2^32). change (bv_half_modulus 32) with (2^31).
  Z.div_mod_to_equations. lia.
Qed.

(* [comment removed for export] *)
Definition rbig_fail1_walk__stmt : Prop := forall (sp gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 ra' nw rav s0v s1v s2v s3v s4v : word) F fc (m : mem) (lo : Z),
  rw_cells usegs m (bv_unsigned sp + -48) [C8 s4v; C8 s3v; C8 s2v; C8 s1v; C8 s0v; C8 rav] ->
  stk usegs m lo (bv_unsigned sp + -48) -> lo <= bv_unsigned sp - 48 -> 48 <= bv_unsigned sp ->
  evt usegs (fun ms' => ms' = MS (mkR rav sp gp tp t0 t1 t2 s0v s1v (wz 0) a1 a2 a3 a4 a5 a6 a7 s2v s3v s4v s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                F (ret_pc rav) fc None m (seg_rom usegs)
                        /\ stk usegs m lo (bv_unsigned sp))
      (MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 nw (Z_to_bv 64 RMLOCK) (Z_to_bv 64 (-1)) a1 a2 a3 a4 a5 a6 a7
               (Z_to_bv 64 (-1)) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x19ab4) fc None m (seg_rom usegs)).
Section Sz2.
Variables sp gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 ra' nw rav s0v s1v s2v s3v s4v F fc m lo : ltac2:(SecDiet.SzSec.tyM 'rbig_fail1_walk__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @sp).
Lemma rbig_fail1_walk__body : ltac2:(SecDiet.SzSec.bodyP 'rbig_fail1_walk__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
Proof using MSECV TB. pin_using (fun (MSECV TB : unit) => tt). ceil_facts. msec_facts.
 intros FR ST LO SP48.
  pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  step. if_cases K; zify_cond K. 2:{ exfalso. apply K. reflexivity. }
  step. step. step. step. step. step. step. step. step.
  release_frame FR ST (bv_unsigned sp).
  apply evt_done. split; [reflexivity| exact ST].
Qed.
End Sz2.
Lemma rbig_fail1_walk : ltac:(let t := eval cbv delta [rbig_fail1_walk__stmt] in rbig_fail1_walk__stmt in exact t).
Proof using MSECV TB. intros sp gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 ra' nw rav s0v s1v s2v s3v s4v F fc m lo. ltac2:(SecDiet.SzSec.closeP 'rbig_fail1_walk__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.

(* [comment removed for export] *)
Lemma rbig_fail2b_walk :
  forall (sp gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 ra' nw s1w rav s0v s1v s2v s3v s4v : word) F fc (m : mem) (lo : Z),
  rw_cells usegs m (bv_unsigned sp + -48) [C8 s4v; C8 s3v; C8 s2v; C8 s1v; C8 s0v; C8 rav] ->
  stk usegs m lo (bv_unsigned sp + -48) -> lo <= bv_unsigned sp - 48 -> 48 <= bv_unsigned sp ->
  evt usegs (fun ms' => ms' = MS (mkR rav sp gp tp t0 t1 t2 s0v s1v (wz 0) a1 a2 a3 a4 a5 a6 a7 s2v s3v s4v s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                F (ret_pc rav) fc None m (seg_rom usegs)
                        /\ stk usegs m lo (bv_unsigned sp))
      (MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 nw s1w a0 a1 a2 a3 a4 a5 a6 a7
               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x19c80) fc None m (seg_rom usegs)).
Proof using MSECV TB. pin_using (fun (MSECV TB : unit) => tt). ceil_facts. msec_facts.
  intros until lo. intros FR ST LO SP48.
  pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  step. step. step. step. step. step. step. step. step. step.
  release_frame FR ST (bv_unsigned sp).
  apply evt_done. split; [reflexivity| exact ST].
Qed.

(* [comment removed for export] *)
Definition rbig_fail2a_walk__stmt : Prop := forall (sp gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s2 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 ra' nw xw ndw : word) F fc (m : mem),
  rw_cells usegs m RMLOCK [C4 (wz 0)] ->
  evt usegs (fun ms' => ms' = MS (mkR (Z_to_bv 64 0x19c80) (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 nw (Z_to_bv 64 RMLOCK) xw ndw a2 a3 a4 a5 a6 a7
                                     s2 ndw xw s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 rmunmap_entry) fc None m (seg_rom usegs))
      (MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 nw (Z_to_bv 64 RMLOCK) (wz 0) a1 a2 a3 a4 a5 a6 a7
               s2 ndw xw s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x19ba8) fc None m (seg_rom usegs)).
Section Sz4.
Variables sp gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s2 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 ra' nw xw ndw F fc m : ltac2:(SecDiet.SzSec.tyM 'rbig_fail2a_walk__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @sp).
Lemma rbig_fail2a_walk__body : ltac2:(SecDiet.SzSec.bodyP 'rbig_fail2a_walk__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
Proof using MSECV TB. pin_using (fun (MSECV TB : unit) => tt). ceil_facts. msec_facts.
 intros LK. unfold RMLOCK in *.
  step. if_cases K; zify_cond K. 2:{ exfalso. apply K. reflexivity. }
  step. step. step.
  eapply evt_cut. { eapply runlock_spec; rewrite unsigned_lit by lia; [reflexivity| exact LK]. }
  intros ms' ->.
  replace (ret_pc (Z_to_bv 64 0x19c74)) with (Z_to_bv 64 0x19c74) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]).
  step. step. step. apply evt_done. unfold rmunmap_entry. reflexivity.
Qed.
End Sz4.
Lemma rbig_fail2a_walk : ltac:(let t := eval cbv delta [rbig_fail2a_walk__stmt] in rbig_fail2a_walk__stmt in exact t).
Proof using MSECV TB. intros sp gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s2 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 ra' nw xw ndw F fc m. ltac2:(SecDiet.SzSec.closeP 'rbig_fail2a_walk__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.

Definition rseq_post (sp gp tp s5 s6 s7 s8 s9 s10 s11 t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 nw xw rav s0v s1v s2v s3v s4v : word)
    (F : bvmap 5 word) (fc : bv 32) (lo : Z) (st' : mstate) (m : mem) (n : Z) : machine_state -> Prop :=
  fun ms' => exists (a0 a1 : word) m',
    ms' = MS (mkR (Z_to_bv 64 0x19ba8) (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 nw (Z_to_bv 64 RMLOCK)
                  a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 (-1)) (Z_to_bv 64 (n + 20)) xw s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (Z_to_bv 64 ralloc_meta_entry) fc None m' (seg_rom usegs)
    /\ munch [(RCTX + 848, RCTX + 880); (RCTX + 912, RCTX + 913)]%Z m m'
    /\ wmono usegs m m' /\ mem_inv usegs m'
    /\ stk usegs m' lo (bv_unsigned sp + -48)
    /\ rw_cells usegs m' (bv_unsigned sp + -48) [C8 s4v; C8 s3v; C8 s2v; C8 s1v; C8 s0v; C8 rav]
    /\ rmrep st' m'.

(* [comment removed for export] *)
Definition rbig_seq_walk__stmt : Prop := forall (sp gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 ra' nw xw rav s0v s1v s2v s3v s4v : word) F fc (m : mem)
    (lo n : Z) (st : mstate),
  rmrep st m -> 0 <= c_seq (ctx st) < 256 ->
  bv_unsigned xw <> 2^64 - 1 ->
  rw_cells usegs m (bv_unsigned sp + -48) [C8 s4v; C8 s3v; C8 s2v; C8 s1v; C8 s0v; C8 rav] ->
  stk usegs m lo (bv_unsigned sp + -48) -> lo <= bv_unsigned sp - 48 -> alloc_ceiling <= lo -> mem_inv usegs m ->
  evt usegs (rseq_post sp gp tp s5 s6 s7 s8 s9 s10 s11 t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 nw xw rav s0v s1v s2v s3v s4v F fc lo (step_seq st) m n)
      (MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 nw (Z_to_bv 64 RMLOCK)
               xw a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 (-1)) (Z_to_bv 64 (n + 20)) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x19ab4) fc None m (seg_rom usegs)).
Section Sz5.
Variables sp gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 ra' nw xw rav s0v s1v s2v s3v s4v F fc m lo n st : ltac2:(SecDiet.SzSec.tyM 'rbig_seq_walk__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @sp).
Lemma rbig_seq_walk__body : ltac2:(SecDiet.SzSec.bodyP 'rbig_seq_walk__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
Proof using Type. pin_using tt. ceil_facts. msec_facts.
 intros MR SEQ XNE FR ST LO ILO MI.
  pose proof (munch_refl [(RCTX + 848, RCTX + 880); (RCTX + 912, RCTX + 913)]%Z m) as MU.
  pose proof (wmono_refl usegs m) as WM.
  pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  pose proof (bv_unsigned_in_range _ xw) as XR. change (bv_modulus 64) with (2^64) in XR.
  pose proof MR as (_ & (_ & _ & _ & US & _ & C6) & (_ & NL & _) & _).
  unfold RNEED_LOCKS, RCTX, RMLOCK, ralloc_meta_entry in *; ceil_facts. unfold ctx_tail_cells in C6.
  replace (345440 + 912) with 346352 in C6 by reflexivity. replace (345440 + 848) with 346288 in US by reflexivity.
  (* [comment removed for export] *)
  step. if_cases K0; zify_cond K0. { exfalso. apply XNE. rewrite K0. reflexivity. } clear K0.
  (* [comment removed for export] *)
  step. step. step. rewrite ?zxb_b8 by lia. step. if_cases K1; zify_cond K1. 2:{ exfalso. rewrite ?wz_unsigned, ?unsigned_lit in K1 by lia. lia. } clear K1 NL.
  (* [comment removed for export] *)
  step. rewrite ?zxb_b8 by lia. step.
  (* [comment removed for export] *)
  assert (TAIL : forall (a1' : word) (mj : mem) (stj : mstate) (ns : Z),
    0 <= ns < 256 -> rmrep stj mj -> ctx_tail_cells stj = ctx_tail_cells st ->
    rw_cells usegs mj (bv_unsigned sp + -48) [C8 s4v; C8 s3v; C8 s2v; C8 s1v; C8 s0v; C8 rav] ->
    stk usegs mj lo (bv_unsigned sp + -48) -> mem_inv usegs mj ->
    munch [(345440 + 848, 345440 + 880); (345440 + 912, 345440 + 913)]%Z m mj -> wmono usegs m mj ->
    evt usegs (rseq_post sp gp tp s5 s6 s7 s8 s9 s10 s11 t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 nw xw rav s0v s1v s2v s3v s4v F fc lo (upd_ctx (set_seq ns) stj) m n)
      (MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 nw (Z_to_bv 64 345432)
               (Z_to_bv 64 ns) a1' a2 a3 a4 a5 a6 a7 (Z_to_bv 64 (-1)) (Z_to_bv 64 (n + 20)) xw s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x19ba0) fc None mj (seg_rom usegs))).
  { intros a1' mj stj ns NS MRj CTj FRj STj MIj MUj WMj.
    pose proof MRj as (_ & (_ & _ & _ & _ & _ & C6j) & _). rewrite CTj in C6j. unfold ctx_tail_cells in C6j. unfold RCTX in C6j.
    replace (345440 + 912) with 346352 in C6j by reflexivity.
    pose proof (rw_cells_store_ok_at usegs _ _ _ 0 (C1 (b8 (c_seq (ctx st)))) 1 (Z_to_bv 64 346352) C6j eq_refl eq_refl
                  ltac:(unfold wa; f_equal; lia)) as SOK.
    clear C6j.
    st1.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?mX _ _) _) =>
      pose proof (rmrep_set_seq stj mX ns MRj NS) as MR1; unfold RCTX in MR1 end.
    raw_store_finishR (345440 + 912) [b8 ns] FRj STj MUj WMj SOK.
    (* [comment removed for export] *)
    step.
    apply evt_done. unfold rseq_post, RCTX, RMLOCK, ralloc_meta_entry. do 3 eexists. split; [reflexivity|].
    split; [exact MUj|]. split; [exact WMj|]. split; [assumption|]. split; [assumption|]. split; [exact FRj|]. exact MR1. }
  step. if_cases K2; zify_cond K2; rewrite ?wz_unsigned, ?unsigned_lit in K2 by lia.
  - (* [comment removed for export] *)
    step. rewrite (wz_unsigned (c_seq (ctx st))) by lia.
    eapply evt_mono; [eapply (TAIL _ m st (c_seq (ctx st) + 1)); [lia| exact MR| reflexivity| exact FR| exact ST| exact MI| exact MU| exact WM]|].
    intros ms' PO. rewrite (step_seq_eq st). replace (c_seq (ctx st) =? 255) with false by (symmetry; apply Z.eqb_neq; lia). exact PO.
  - (* [comment removed for export] *)
    pose proof (rw_cells_of_u8arr usegs _ _ _ US) as USC. rewrite unmap_seqs_length in USC. clear US.
    step. fix_lit_store. step. fix_lit_store. step. fix_lit_store. step. fix_lit_store.
    assert (UZ : u8arr usegs m1 346288 (zeros 32)).
    { apply (u8arr_of_rw_cells usegs m1 346288 32). apply (rw_cells_congr usegs m1 346288 [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)] [CB 32 (zeros 32)]); [reflexivity| reflexivity| cbn; split; [reflexivity| exact I]| exact USC]. }
    clear USC.
    set (stz := upd_ctx (fun c => set_unmap_seq_map ∅ c) st).
    lazymatch goal with MUc : munch _ m m1, WMc : wmono usegs m m1 |- _ =>
    assert (MRz : rmrep stz m1);
    [ eapply (rmrep_ctx_frameW st stz _ m1 _ MR MUc WMc); try reflexivity;
      [ intros lo' hi' [E|[E|[]]]; inversion E; subst; unfold RCTX; lia
      | right; split; [reflexivity| intros lo' hi' [E|[E|[]]]; inversion E; subst; unfold RCTX; lia]
      | right; split; [reflexivity| intros lo' hi' [E|[E|[]]]; inversion E; subst; unfold RCTX; lia]
      | right; split; [reflexivity| intros lo' hi' [E|[E|[]]]; inversion E; subst; unfold RCTX; lia]
      | left; unfold stz; rewrite unmap_seqs_empty; unfold RCTX; exact UZ
      | right; split; [reflexivity| intros lo' hi' [E|[E|[]]]; inversion E; subst; unfold RCTX; lia]
      | left; unfold RCTX; replace (345440 + 912) with 346352 by reflexivity;
        unfold ctx_tail_cells, brk_word, ctx, stz; cbn [s_ctx upd_ctx c_seq c_brk set_unmap_seq_map]; unfold brk_word, ctx in C6; exact C6 ] |] end.
    (* [comment removed for export] *)
    step. step.
    lazymatch goal with MUc : munch _ m ?mX, WMc : wmono usegs m ?mX, FRc : rw_cells usegs ?mX (bv_unsigned sp + -48) _, STc : stk usegs ?mX _ _, MIc : mem_inv usegs ?mX |- _ =>
      eapply evt_mono; [eapply (TAIL _ mX stz 1); [lia| exact MRz| reflexivity| exact FRc| exact STc| exact MIc| exact MUc| exact WMc]|] end.
    intros ms' PO. rewrite (step_seq_eq st). replace (c_seq (ctx st) =? 255) with true by (symmetry; apply Z.eqb_eq; lia). exact PO.
Qed.
End Sz5.
Lemma rbig_seq_walk : ltac:(let t := eval cbv delta [rbig_seq_walk__stmt] in rbig_seq_walk__stmt in exact t).
Proof using Type. intros sp gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 ra' nw xw rav s0v s1v s2v s3v s4v F fc m lo n st. ltac2:(SecDiet.SzSec.closeP 'rbig_seq_walk__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.

Section SUCC.
Variables (st : mstate) (m : mem) (g : aptr) (rid : N) (x n c lo : Z).
Let G := conc st g.
Hypothesis MR : rmrep st m.
Hypothesis TK : ticks_ok st.
Hypothesis G0 : get_meta_rec st g = meta0.
Hypothesis MSL : meta_slot st g.
Hypothesis RR : (s_regions st) !! rid = Some (mkRegion RKGroup x (n + IB + UNIT)).
Hypothesis GN : forall off, (s_groups st) !! (rid, off) = None.
Hypothesis AN : forall off, (s_areas st) !! (rid, off) = None.
Hypothesis SHN : (s_shadow st) !! rid = None.
Hypothesis HC : c_mmap_counter (ctx st) = c.
Hypothesis CR : 0 <= c < 2^32.
Hypothesis NR : MMAP_THRESHOLD <= n < 2^32.
Hypothesis CLO : alloc_ceiling <= lo.

Definition rbig_succ_walk__stmt : Prop := forall (sp gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s2 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 ra' gw s0v s1v s2v s3v s4v rav : word) F fc,
  bv_unsigned gw = G ->
  rw_cells usegs m (bv_unsigned sp + -48) [C8 s4v; C8 s3v; C8 s2v; C8 s1v; C8 s0v; C8 rav] ->
  stk usegs m lo (bv_unsigned sp + -48) -> lo <= bv_unsigned sp - 48 -> mem_inv usegs m ->
  evt usegs (fun ms' => exists (a0' a1' : word) m',
      ms' = MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 (Z_to_bv 64 n) (Z_to_bv 64 RMLOCK)
                   a0' a1' a2 a3 a4 a5 a6 a7 gw (wz 0) (wz x) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
              F (Z_to_bv 64 0x19d40) fc None m' (seg_rom usegs)
      /\ munch [(G, G + 40); (x, x + 8); (RCTX + 12, RCTX + 16)]%Z m m' /\ wmono usegs m m' /\ mem_inv usegs m'
      /\ stk usegs m' lo (bv_unsigned sp + -48)
      /\ rw_cells usegs m' (bv_unsigned sp + -48) [C8 s4v; C8 s3v; C8 s2v; C8 s1v; C8 s0v; C8 rav]
      /\ rmrep (big_st st g rid n (u32 (c + 1))) m' /\ ticks_ok (big_st st g rid n (u32 (c + 1))))
    (MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 (Z_to_bv 64 n) (Z_to_bv 64 RMLOCK)
             gw a1 a2 a3 a4 a5 a6 a7 s2 (Z_to_bv 64 (n + 20)) (wz x) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x19ba8) fc None m (seg_rom usegs)).
Section Sz6.
Variables sp gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s2 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 ra' gw s0v s1v s2v s3v s4v rav F fc : ltac2:(SecDiet.SzSec.tyM 'rbig_succ_walk__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @sp).
Lemma rbig_succ_walk__body : ltac2:(SecDiet.SzSec.bodyP 'rbig_succ_walk__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
Proof using AN CLO CR G0 GN HC MR MSL NR RR SHN TK. pin_using (fun (AN CLO CR G0 GN HC MR MSL NR RR SHN TK : unit) => tt). ceil_facts. msec_facts.
 intros HG FR ST LO MI. unfold MMAP_THRESHOLD in NR. unfold IB, UNIT in RR.
  set (r0 := mkRegion RKGroup x (n + 4 + 16)) in RR.
  pose proof (munch_refl [(G, G + 40); (x, x + 8); (RCTX + 12, RCTX + 16)]%Z m) as MU. pose proof (wmono_refl usegs m) as WM.
  pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  pose proof MR as (WF & (CX1 & _) & _ & AR & GRP & SH). pose proof WF as (RS & WR & DJ & WA & WG).
  pose proof (rmeta_chunk_facts st m g MR MSL) as (CH & Gpos & GC & GI1 & GI2 & GRG & (rid0 & rg0 & Hrg0 & Krg0 & GL0 & GH0)).
  fold G in CH, Gpos, GC, GI1, GI2, GRG, GL0, GH0. rewrite G0 in CH. unfold meta_cells in CH. cbn [m_prev m_next m_mem m_avail m_freed meta0 pw oconc] in CH.
  change (meta_word meta0) with 0 in CH.
  destruct (WR rid r0 RR) as (X0 & _ & XL & XC & XRF). cbn [r_base r_len r0] in X0, XL, XC, XRF.
  pose proof (round_up_pg_ge (n + 4 + 16)) as XRU.
  destruct (rreserved_disjoint2 _ _ XRF ltac:(lia)) as [XI1 XI2].
  (* [comment removed for export] *)
  destruct (SH rid r0 RR eq_refl) as [XW XB]. cbn [r_base r_len r0] in XW, XB.
  assert (HDR : rw_cells usegs m x [C8 (wz 0); C1 (b8 0)]).
  { apply rw_cells_of_bytes; [cbn; repeat split; reflexivity| |].
    - cbn [cells_bytes cbytes app]. change (le8 (wz 0) ++ [b8 0]) with (zeros 9).
      apply rzeros_bytes_at; [lia| cbn; ceil_facts; lia|].
      intros o Ho. cbn in Ho. refine (proj1 (XB o 0 ltac:(lia) _)).
      unfold get_shadow. rewrite SHN. apply cell_read_shadow0.
    - cbn. eapply wr_at_sub; [exact XW| lia| lia]. }
  (* [comment removed for export] *)
  pose proof (GRG rid r0 RR eq_refl) as GX. cbn [r_base r_len r0] in GX.
  rewrite <- HG in CH.
  unfold RCTX, RMLOCK in *; ceil_facts.
  (* [comment removed for export] *)
  step. if_cases K; zify_cond K; rewrite ?wz_unsigned in K by lia. { exfalso. lia. } clear K.
  (* [comment removed for export] *)
  unfold ctx_head_cells in CX1. rewrite HC in CX1.
  pose proof (rw_cells_prefix usegs m _ [C8 (wz (c_secret (ctx st))); C4 (wz (c_init_done (ctx st))); C4 (wz c)] _ CX1) as CX3. clear CX1.
  assert (GW0 : gw = wz G) by (rewrite <- HG; symmetry; apply Z_to_bv_bv_unsigned).
  (* [comment removed for export] *)
  step. step.
  (* [comment removed for export] *)
  pose proof (munch_refl [(G, G + 40)]%Z m) as MUa. pose proof (wmono_refl usegs m) as WMa.
  step.
  assert (PWX : pw st (Some (rid, 0)) = wz x).
  { unfold pw, oconc, conc, get_region. cbn [fst snd]. rewrite RR. cbn [r_base r0]. rewrite Z.add_0_r. reflexivity. }
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
    assert (CHA : rw_cells usegs mX (conc st g) (meta_cells st (big_metaA rid)));
    [ unfold meta_cells; cbn [m_prev m_next m_mem m_avail m_freed big_metaA]; rewrite PWX;
      change (meta_word (big_metaA rid)) with 0; change (pw st None) with (wz 0); fold G; rewrite <- HG; exact CH
    | pose proof (rmrep_put_meta_frame st m mX g (big_metaA rid) MR MSL MUa WMa CHA) as MRA ] end.
  clear MUa WMa CHA.
  (* [comment removed for export] *)
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
    pose proof (munch_refl [(x, x + 8)]%Z mX) as MUb; pose proof (wmono_refl usegs mX) as WMb end.
  cbv delta [wz]. step.
  set (stA := put_meta g (big_metaA rid) st) in MRA.
  destruct (rmrep_hdr_havoc stA _ (rid, 0) MRA TK) as [MRB0 TKB].
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
    assert (MRB1 : rmrep (hdr_havoc (rid, 0) stA) mX) end.
  { eapply (rmrep_transport_unowned _ _ _ _ MRB0 MUb WMb).
    intros lo' hi' a [E|[]] Ha. inversion E; subst lo' hi'. intros RF.
    destruct RF as [R1|[R2|[R3|[R4|[(ak & ar & Hak & Rak)|[(b & gh & Hb & Rb)|[(q & rq & v & Hq & Kq & Rq & Cq)|[R5|R6]]]]]]]].
    - unfold RCTX in R1. lia.
    - unfold RMLOCK in R2. lia.
    - unfold RNEED_LOCKS in R3. lia.
    - unfold RPAGE_SIZE in R4. lia.
    - change (s_areas (hdr_havoc (rid, 0) stA)) with (s_areas st) in Hak. change (conc (hdr_havoc (rid, 0) stA) ak) with (conc st ak) in Rak.
      destruct (rarea_conc st ak ar WF Hak) as (rga & Hra & Ca & Sa0 & Sa1 & _ & NK & _).
      assert (NE : fst ak <> rid) by (intros EQ; destruct ak as [ak1 ak2]; cbn in EQ; subst ak1; rewrite (AN ak2) in Hak; discriminate).
      pose proof (rarea_lr_lo st ak ar rga WF Hak Hra). destruct (DJ _ _ _ _ Hra RR NE) as [D|D]; cbn [r_base r_len r0 lr_lo r_kind] in D; lia.
    - change (s_groups (hdr_havoc (rid, 0) stA)) with (s_groups st) in Hb. change (conc (hdr_havoc (rid, 0) stA) b) with (conc st b) in Rb.
      destruct (rgroup_conc st b gh WF Hb) as (rb & Hrb & Cb & Kb & Sb0 & Sb1 & _).
      assert (NE : fst b <> rid) by (intros EQ; destruct b as [b1 b2]; cbn in EQ; subst b1; rewrite (GN b2) in Hb; discriminate).
      pose proof (lr_lo_group rb Kb). destruct (DJ _ _ _ _ Hrb RR NE) as [D|D]; cbn [r_base r_len r0 lr_lo r_kind] in D; lia.
    - change (s_regions (hdr_havoc (rid, 0) stA)) with (s_regions st) in Hq.
      destruct (N.eq_dec q rid) as [->|NE].
      + rewrite RR in Hq. inversion Hq; subst rq. cbn [r_base r0] in Cq.
        destruct (cell_read_hdr_havoc_fresh stA (rid, 0) (a - x) SHN ltac:(reflexivity) ltac:(cbn; lia)) as [h Hh].
        cbn [fst snd] in Hh. rewrite Z.add_0_l in Hh. rewrite Hh in Cq. discriminate.
      + pose proof (lr_lo_group rq Kq). destruct (DJ _ _ _ _ Hq RR NE) as [D|D]; cbn [r_base r_len r0 lr_lo r_kind] in D; lia.
    - unfold RGOT_SSP in R5. lia.
    - unfold RSSP_GUARD in R6. lia. }
  clear MRB0 MUb WMb.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
    assert (MRB : rmrep (put_group (rid, 0) (Some g) 0 (hdr_havoc (rid, 0) stA)) mX) end.
  { eapply (rmrep_put_group_new _ _ (rid, 0) g 0 r0 (b8 0) MRB1); [apply GN| exact RR| reflexivity| cbn; lia| cbn [snd r_len r0]; lia| reflexivity| |reflexivity].
    change (conc (hdr_havoc (rid, 0) stA) (rid, 0)) with (conc st (rid, 0)). change (pw (hdr_havoc (rid, 0) stA) (Some g)) with (wz G).
    unfold conc, get_region. cbn [fst snd]. rewrite RR. cbn [r_base r0]. rewrite Z.add_0_r. rewrite <- GW0. exact HDR. }
  clear MRB1.
  (* [comment removed for export] *)
  step. step. step. step. step. step.
  rewrite (unsigned_lit (n + 4115)) by lia.
  assert (LR : 0 <= Z.land (n + 4115) 18446744073709549568 <= n + 4115) by (split; [apply Z.land_nonneg; lia| apply land_le_l; lia]).
  rewrite (unsigned_lit (Z.land (n + 4115) 18446744073709549568)) by lia.
  replace (n + 4115) with (n + 4064 + 51) by lia. rewrite (rbig_word_eq rid n) by lia.
  pose proof (meta_word_big_range rid n ltac:(lia)) as MWR.
  (* [comment removed for export] *)
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
    pose proof (munch_refl [(G, G + 40)]%Z mX) as MUc; pose proof (wmono_refl usegs mX) as WMc end.
  change (Z_to_bv 64 (meta_word (big_meta rid n))) with (wz (meta_word (big_meta rid n))).
  step. step. step.
  set (stB := put_group (rid, 0) (Some g) 0 (hdr_havoc (rid, 0) stA)) in MRB.
  lazymatch goal with H : rw_cells usegs ?mX (bv_unsigned gw) _ |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
    assert (CHC : rw_cells usegs mX (conc stB g) (meta_cells stB (big_meta rid n)));
    [ change (conc stB g) with G; rewrite <- HG; unfold meta_cells; cbn [m_prev m_next m_mem m_avail m_freed big_meta];
      change (pw stB (Some (rid, 0))) with (pw st (Some (rid, 0))); rewrite PWX; change (pw stB None) with (pw st None); exact H
    | pose proof (rmrep_put_meta_frame stB _ mX g (big_meta rid n) MRB MSL MUc WMc CHC) as MRC ] end.
  clear MUc WMc CHC MRB.
  (* [comment removed for export] *)
  step. rewrite (sx32_wz_sxv c) by lia. step.
  (* [comment removed for export] *)
  lazymatch goal with H : rw_cells usegs ?mX 345440 _ |- _ =>
    pose proof (rw_cells_store_ok_at usegs _ _ _ 12 (C4 (wz c)) 4 (Z_to_bv 64 345452) H eq_refl eq_refl ltac:(unfold wa; f_equal; lia)) as SOK;
    clear H end.
  st1. rewrite le4_swrap_succ by lia.
  set (stC := put_meta g (big_meta rid n) stB) in MRC.
  assert (VR : 0 <= u32 (c + 1) < 2^32) by (unfold u32; Z.div_mod_to_equations; lia).
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?mX _ _) _) =>
    pose proof (rmrep_set_mmap_counter stC mX (u32 (c + 1)) MRC VR) as MRD; unfold RCTX in MRD end.
  clear MRC.
  raw_store_finishR (345440 + 12) (le4 (wz (u32 (c + 1)))) FR ST MU WM SOK.
  (* [comment removed for export] *)
  step.
  apply evt_done. do 3 eexists. split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact ST|]. split; [exact FR|].
  split; [exact MRD| exact TKB].
Qed.
End Sz6.
Lemma rbig_succ_walk : ltac:(let t := eval cbv delta [rbig_succ_walk__stmt] in rbig_succ_walk__stmt in exact t).
Proof using AN CLO CR G0 GN HC MR MSL NR RR SHN TK. intros sp gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s2 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 ra' gw s0v s1v s2v s3v s4v rav F fc. ltac2:(SecDiet.SzSec.closeP 'rbig_succ_walk__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.
End SUCC.

End PORT.

End WithCeil.
End TwB.
End RF_malloc_bigw.
