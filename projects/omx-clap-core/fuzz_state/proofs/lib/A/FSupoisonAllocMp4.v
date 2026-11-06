(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_disco/lib/Reusable/YFet.v, with its module paths and module names changed; 85 of its 109 lines of code are new or changed and 708 lines of the source are left out. *)
(* Malloc PRIMARY miss-g walk under ARU, any UP: threads lib/A/AFim.v (malloc_missg) over AFiw.v / AFi4.v (the miss seed MS0, MREG0), AFiu.v / AFit.v / AFiv.v (the miss runs), AFl1.v (the refill contract, here in its any-UP form FSupoisonAllocR.tfib_refill_specU), AFj2.v's tail (here FSupoisonAllocMp2.tail_innerU), AFi5.v (AR_oom), with lib/A/FSupoison.v, FSupoisonU.v, FSupoisonAllocR.v, FSupoisonAllocMp1.v and FSupoisonAllocMp2.v. *)
(* Shared any-U allocator, within-budget units (cgif's EV_MAX 11,776, < 2 GiB per class); the cf form (fuzz_preset / fuzz_reply, YG0dcf.v) bridges to this. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s YO0d.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YP0j.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0p YA0q YG0b.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YG02 YG06 YG07 YG0k.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require Import AFl1.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YG00 YG0a YG01 YG04 YG03 YG0f YG0v YG0n YG0d YG0s YG0q YG0t.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YG0l YG0m.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require Import AB1v AB1q AF0l AF0m AF0x AFl0 AFl3.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YO0a.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require Import AB1w AE3d AE2y AE3g AFhy AFhz AFi4 AFhm.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YFen.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require Import AFis AFi3 AFiy AFiz AFj0 AFix AFj2 AFiw AFiu AFit AFiv AFi5 AB13.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YFfk.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YA00.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require FSupoison FSupoisonU FSupoisonAllocR FSupoisonAllocMp1 FSupoisonAllocMp2.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Set Warnings "-notation-for-abbreviation".
Open Scope Z_scope.
Module FSP := OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A.FSupoison.
Module FSU := OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A.FSupoisonU.
Module AllocR := OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A.FSupoisonAllocR.
Module Mp1 := OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A.FSupoisonAllocMp1.
Module Mp2 := OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A.FSupoisonAllocMp2.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Ltac ceil := try (let H := fresh "CR" in let H2 := fresh "CR" in pose proof (proj1 (@YG0f.ASAN_CEIL_range _)) as H; pose proof H as H2; unfold YG0f.ASAN_CEIL in H2).
Ltac zlia := first [ lia | ceil; unfold zone3, zone3cases, in_app, app_addr, in_band_rw, TFIB_IMG_LO, TFIB_IMG_END, kLowShadowBeg, kLowShadowEnd, kHighShadowBeg, kHighShadowEnd, kHighMemBeg, ASAN_CEIL in *; lia ].
Local Open Scope am_scope.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* Region lemmas (to move to FSupoisonAllocR.v at integration): the miss seed MS0 (AFi4.v MREG0) has INERT regions  *)
(* (no chunk, empty write window) over the cached chunk's extent and its first shadow byte, which a user-poisoned    *)
(* head may meet; those constrain no byte, so the seed moves between the two readings of memory without any          *)
(* condition on them. The kit's regions_offU asks for every byte of every region, which is more than the seed needs. *)
(* ---------------------------------------------------------------------------------------------------------------- *)

Definition reg_inert (r : YP09.region) : bool :=
  (YP09.r_whi r <=? YP09.r_wlo r) && (match YP09.r_chunks r with [] => true | _ => false end).
Definition reg_appb (r : YP09.region) : bool :=
  match YP09.r_base r with
  | None => (0 <=? YP09.r_lo r) && (YP09.r_hi r <=? SHADOW_OFF)
  | Some k =>
      (Nat.eqb k 2 && (- ASTACK <=? YP09.r_lo r) && (YP09.r_hi r <=? 0)) ||
      (Nat.eqb k 32 && (0 <=? YP09.r_lo r) && (YP09.r_hi r <=? kThreadObjSize)) ||
      (Nat.eqb k 33 && (0 <=? YP09.r_lo r) && (YP09.r_hi r <=? 256)) ||
      (Nat.eqb k 40 && (0 <=? YP09.r_lo r) && (YP09.r_hi r <=? 16)) ||
      (Nat.eqb k 44 && (0 <=? YP09.r_lo r) && (YP09.r_hi r <=? 4)) ||
      (Nat.eqb k 52 && (0 <=? YP09.r_lo r) && (YP09.r_hi r <=? 8))
  end.
Lemma MREG0_classb : forallb (fun r => reg_inert r || reg_appb r) MREG0 = true.
Proof. vm_compute. reflexivity. Qed.

Section r.
Variable UP : list (Z * Z).

(* A region all of whose constrained bytes read the same in the two readings holds of both; an inert region holds
   of both outright. *)
Lemma region_ok_real : forall E (Hh : word -> bool) (m : word -> option byte) r,
  (reg_inert r = true \/
   (forall a, base_val E (YP09.r_base r) + YP09.r_lo r <= a < base_val E (YP09.r_base r) + YP09.r_hi r ->
      AllocR.offU UP a)) ->
  region_wf r = true ->
  region_ok tfibsegs E (mrestrict Hh (FSP.unpoison UP m)) r -> region_ok tfibsegs E (mrestrict Hh m) r.
Proof.
intros E Hh m r CL WF (B1 & B2 & Hw & Hc).
pose proof (region_wf_facts r WF) as (Hlohi & Hwin & Hcin).
split; [exact B1|]. split; [exact B2|]. destruct CL as [IN|OFF].
- unfold reg_inert in IN. apply andb_prop in IN as [I1 I2]. apply Z.leb_le in I1.
  split; [intros o Ho; exfalso; lia|].
  destruct (YP09.r_chunks r) as [|c0 t0]; [apply Forall_nil | discriminate I2].
- split.
  + intros o Ho. apply (AE2y.writable_at_same (mrestrict Hh (FSP.unpoison UP m)) (mrestrict Hh m)
      (base_val E (YP09.r_base r) + o)); [|exact (Hw o Ho)].
    unfold mrestrict.
    rewrite (AllocR.unpoison_offU UP m (base_val E (YP09.r_base r) + o)
      (OFF (base_val E (YP09.r_base r) + o) ltac:(lia))). reflexivity.
  + rewrite Forall_forall in Hc |- *. intros c Hcin'.
    pose proof (YP09.chunk_inside_facts r c (proj1 (forallb_forall _ _) Hcin c Hcin')) as (C1 & C2 & C3).
    apply (AE3g.chunk_ok_same tfibsegs E (mrestrict Hh (FSP.unpoison UP m)) (mrestrict Hh m)); [exact (Hc c Hcin')|].
    intros i Hi. unfold mrestrict.
    rewrite (AllocR.unpoison_offU UP m (base_val E (YP09.r_base r) + c_off c + i)
      (OFF (base_val E (YP09.r_base r) + c_off c + i) ltac:(lia))). reflexivity.
Qed.

Lemma regions_ok_real : forall E (Hh : word -> bool) (m : word -> option byte) rs,
  regions_wf rs = true ->
  (forall r, In r rs -> reg_inert r = true \/
     (forall a, base_val E (YP09.r_base r) + YP09.r_lo r <= a < base_val E (YP09.r_base r) + YP09.r_hi r ->
        AllocR.offU UP a)) ->
  Forall (region_ok tfibsegs E (mrestrict Hh (FSP.unpoison UP m))) rs ->
  Forall (region_ok tfibsegs E (mrestrict Hh m)) rs.
Proof.
intros E Hh m rs WF CL F. rewrite Forall_forall in F |- *. intros r Hr.
exact (region_ok_real E Hh m r (CL r Hr) (regions_wf_In rs r WF Hr) (F r Hr)).
Qed.

Lemma st_ok_real : forall E ss (Hh : word -> bool) regs pc (m : word -> option byte) rom,
  (forall r, In r (ss_mem ss) -> reg_inert r = true \/
     (forall a, base_val E (YP09.r_base r) + YP09.r_lo r <= a < base_val E (YP09.r_base r) + YP09.r_hi r ->
        AllocR.offU UP a)) ->
  YP0l.st_ok tfibsegs E ss (restrict Hh (YK11.mkst regs pc (FSP.unpoison UP m) rom)) ->
  YP0l.st_ok tfibsegs E ss (restrict Hh (YK11.mkst regs pc m rom)).
Proof.
intros E ss Hh regs pc m rom CL H.
unfold YP0l.st_ok, restrict, YK11.mkst in H |- *.
cbn [ms_fregs ms_pc_val ms_svc_pending ms_resv ms_fcsr ms_rom ms_regs ms_mem] in H |- *.
destruct H as (X1 & X2 & X3 & X4 & X5 & X6 & X7 & X8 & X9).
refine (conj X1 (conj X2 (conj X3 (conj X4 (conj X5 (conj X6 (conj X7 (conj _ X9)))))))).
destruct X8 as (WF & RO & PD). split; [exact WF|]. split; [|exact PD].
exact (regions_ok_real E Hh m (ss_mem ss) WF CL RO).
Qed.
End r.
End a.
