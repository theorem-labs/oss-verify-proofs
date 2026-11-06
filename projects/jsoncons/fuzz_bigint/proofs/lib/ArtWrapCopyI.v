(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.jsoncons.fuzz_bigint.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib Require Import PropExec CatExec CatSim StoreOk Hoare ShapeAlg SpinAlg AsanAcct RefMemcpyLib MemSplit HeapIface HeapIfaceA ArtMem ArtRuns ArtBridge ArtInv ArtFsInv ArtFsInvLaws
     As0RegionPoisoned As0MemcpyBase As0IntMemmove.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib Require Import As0AsanMemset As0AsanMemcpy As0AsanMemmove As0MemcpyIcpt As0MemmoveIcpt ArtWrapCopy.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

#[local] Abbreviation ASEGS := Asan.M.loaded_segments.
#[local] Notation "'U' r" := (bv_unsigned r) (at level 10, r at level 9).

Section Inst.
Context {fx : PropExec.FPState}.

Lemma copy_run_asan_memcpy : copy_run_spec (0x5e0d4 : word) 2216.
Proof.
  intros mem0 sp ra pd ps n s bs kS fS lS kD fD lD Es EfS ElS EfD ElD Hn AS AD Hs HshS HshD DJS DJD NOV HOK HDST HSRC Hret HG HI HZS HLS HkS HWS HZD HLD HkD HWD regs H10 H11 H12 H2 H1.
  destruct (@asan_memcpy_run fx mem0 (seg_rom ASEGS) sp ra pd ps n s bs kS fS lS (fS - fS mod 8) (lS - lS mod 8) kD fD lD (fD - fD mod 8) (lD - lD mod 8)
              Es EfS ElS eq_refl eq_refl EfD ElD eq_refl eq_refl Hn AS AD Hs HshS HshD DJS DJD NOV HOK HDST HSRC Hret HG HI HZS HLS HkS HWS HZD HLD HkD HWD regs H10 H11 H12 H2 H1)
    as (R' & Mj & RUN & Q10 & Q2 & Q1 & KCS & OA & GR).
  exists R', (wbytes Mj (Z_to_bv 64 pd) bs), Mj. split; [exact RUN|]. split; [exact Q10|]. split; [exact KCS|].
  split; [eapply mem_grows_trans; [exact GR | apply wbytes_grows]|]. split; [exact OA | reflexivity].
Qed.

Lemma copy_run_memcpy_libc : copy_run_spec (0x5e0d0 : word) 2232.
Proof.
  intros mem0 sp ra pd ps n s bs kS fS lS kD fD lD Es EfS ElS EfD ElD Hn AS AD Hs HshS HshD DJS DJD NOV HOK HDST HSRC Hret HG HI HZS HLS HkS HWS HZD HLD HkD HWD regs H10 H11 H12 H2 H1.
  destruct (@wrap_memcpy_run fx mem0 (seg_rom ASEGS) sp ra pd ps n s bs kS fS lS (fS - fS mod 8) (lS - lS mod 8) kD fD lD (fD - fD mod 8) (lD - lD mod 8)
              Es EfS ElS eq_refl eq_refl EfD ElD eq_refl eq_refl Hn AS AD Hs HshS HshD DJS DJD NOV HOK HDST HSRC Hret HG HI HZS HLS HkS HWS HZD HLD HkD HWD regs H10 H11 H12 H2 H1)
    as (R' & Mj & RUN & Q10 & Q2 & Q1 & KCS & OA & GR).
  exists R', (wbytes Mj (Z_to_bv 64 pd) bs), Mj. split; [exact RUN|]. split; [exact Q10|]. split; [exact KCS|].
  split; [eapply mem_grows_trans; [exact GR | apply wbytes_grows]|]. split; [exact OA | reflexivity].
Qed.

Lemma mm_globs_of_mc : forall M, mc_icpt_globs M -> mm_icpt_globs M.
Proof. intros M (G1 & G2 & _). split; assumption. Qed.

Lemma copy_run_asan_memmove : copy_run_spec (0x5e7b0 : word) 2216.
Proof.
  intros mem0 sp ra pd ps n s bs kS fS lS kD fD lD Es EfS ElS EfD ElD Hn AS AD Hs HshS HshD DJS DJD NOV HOK HDST HSRC Hret HG HI HZS HLS HkS HWS HZD HLD HkD HWD regs H10 H11 H12 H2 H1.
  destruct (@asan_memmove_run fx mem0 (seg_rom ASEGS) sp ra pd ps n s bs kS fS lS (fS - fS mod 8) (lS - lS mod 8) kD fD lD (fD - fD mod 8) (lD - lD mod 8)
              Es EfS ElS eq_refl eq_refl EfD ElD eq_refl eq_refl Hn AS AD Hs HshS HshD DJS DJD NOV HOK HDST HSRC Hret HG (mm_globs_of_mc _ HI) HZS HLS HkS HWS HZD HLD HkD HWD regs H10 H11 H12 H2 H1)
    as (R' & Mj & RUN & Q10 & Q2 & Q1 & KCS & OA & GR & MC).
  exists R', (mm_result Mj (Z_to_bv 64 pd) (Z_to_bv 64 ps) bs), Mj. split; [exact RUN|]. split; [exact Q10|]. split; [exact KCS|].
  split. { intros a Ha. rewrite (mm_result_pw Mj (Z_to_bv 64 pd) (Z_to_bv 64 ps) n bs MC). apply wbytes_grows. apply GR. exact Ha. }
  split; [exact OA|]. intros x. exact (mm_result_pw Mj (Z_to_bv 64 pd) (Z_to_bv 64 ps) n bs MC x).
Qed.

Lemma copy_run_memmove_libc : copy_run_spec (0x5e0cc : word) 2216.
Proof.
  intros mem0 sp ra pd ps n s bs kS fS lS kD fD lD Es EfS ElS EfD ElD Hn AS AD Hs HshS HshD DJS DJD NOV HOK HDST HSRC Hret HG HI HZS HLS HkS HWS HZD HLD HkD HWD regs H10 H11 H12 H2 H1.
  destruct (@wrap_memmove_run fx mem0 (seg_rom ASEGS) sp ra pd ps n s bs kS fS lS (fS - fS mod 8) (lS - lS mod 8) kD fD lD (fD - fD mod 8) (lD - lD mod 8)
              Es EfS ElS eq_refl eq_refl EfD ElD eq_refl eq_refl Hn AS AD Hs HshS HshD DJS DJD NOV HOK HDST HSRC Hret HG (mm_globs_of_mc _ HI) HZS HLS HkS HWS HZD HLD HkD HWD regs H10 H11 H12 H2 H1)
    as (R' & Mj & RUN & Q10 & Q2 & Q1 & KCS & OA & GR & MC).
  exists R', (mm_result Mj (Z_to_bv 64 pd) (Z_to_bv 64 ps) bs), Mj. split; [exact RUN|]. split; [exact Q10|]. split; [exact KCS|].
  split. { intros a Ha. rewrite (mm_result_pw Mj (Z_to_bv 64 pd) (Z_to_bv 64 ps) n bs MC). apply wbytes_grows. apply GR. exact Ha. }
  split; [exact OA|]. intros x. exact (mm_result_pw Mj (Z_to_bv 64 pd) (Z_to_bv 64 ps) n bs MC x).
Qed.
End Inst.
