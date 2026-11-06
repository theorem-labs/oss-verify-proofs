(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Datatypes"; "list"; "bool"; "true"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.Virt"; "paid"; "MI"; "@Stdlib.ZArith.BinInt.Z"; "le"; "add"; "lt"; "pow"; "@stdpp.bitvector.definitions"; "Z_to_bv"; "bv"; "bv_unsigned"; "@Corelib.Init.Logic"; "eq"; "and"; "@Corelib.Numbers.BinNums"; "Z"; "@LinuxProcessSemantics.LinuxProcessSem.MemImageType"; "Segment"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "m_vmmaps"; "map_remove"; "region_free"; "vm_maps"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.SysSpec"; "munmap_model"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MmapFixedA"; "tp_forget"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith List Bool Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Mmap.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety SysSpec.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import BackingAlgebra LedgerA Virt MmapFixedA MmapFixedA2.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Lemma paid_munmap_le : ltac2:(tb__ "0|3|
S0SfA1S10S0SaQ40M0A1M1A1G1G1S4R5R4R3A3ScS1S13S12S14S11R5A1A1R3A2R3R2A3S2A3S5S3S15R6R4R3A3S16SbG0R4A2M2S6G2SbG0R3A2A2R5A3A2S3R6R5A2A2F_;F_;Fn;Fa;Ftp;Fmd;Fsegs;").
Proof.
  intros segs md tp a n HMI Hfree.
  pose proof HMI as (HW & HT & Hmat & Hsub & HpaidMI & Hlc & Hivs & Hlm & Htm).
  set (h' := munmap_vm (m_vmmaps md) a n).
  assert (Emd : munmap_model md a n = vm_forget_range (bv_unsigned a) (bv_unsigned a + bv_unsigned n) (with_vmmaps h' md)) by reflexivity.
  rewrite Emd.
  pose proof (used_munmap_le md h' a n Hivs Hfree eq_refl eq_refl) as U1.
  set (md1 := with_vmmaps h' md) in *.
  set (lo := bv_unsigned a) in *. set (hi := lo + bv_unsigned n) in *.
  assert (Wl1 : ivs_wf (m_vm_lazy md1)) by (unfold md1; rewrite m_vm_lazy_with_vmmaps; exact (proj2 (proj2 Hivs))).
  assert (HT' : List.NoDup (tp_forget lo hi tp)) by (unfold tp_forget; apply List.NoDup_filter; exact HT).
  assert (U2 : (length (unpaid (vm_forget_range lo hi md1) (tp_forget lo hi tp)) <= length (unpaid md tp))%nat).
  { apply List.NoDup_incl_length; [unfold unpaid; apply List.NoDup_filter; exact HT'|].
    intros p Hpp. assert (Hp' : In p (unpaid (vm_forget_range lo hi md1) tp)).
    { unfold unpaid in Hpp |- *. apply filter_In in Hpp as [Hpp Hb]. apply filter_In. split; [|exact Hb].
      unfold tp_forget in Hpp. apply filter_In in Hpp as [Hpp _]. exact Hpp. }
    pose proof (unpaid_forget_incl md1 lo hi tp p Wl1 Hp') as Hq. unfold md1 in Hq. rewrite (unpaid_ext md (with_vmmaps h' md) tp) in Hq by reflexivity. exact Hq. }
  unfold paid. pose proof page_size_pos. clear -U1 U2 H. nia.
Qed.

Lemma paid_munmap_leZ : ltac2:(tb__ "0|3|
S0SfA1S10S0SaQ40M0A1A1SeSeSdS5Z0R2A2S7R2S8Z2Z40A2A2A2M1G1S4R7R6R5A3ScS1S13S12S14S11R7A1A1S9G0R5A2M2A2G2S9G0R4A2A3S2A3S5S3S15R8S9G0R6A2G2A3S16R6S6R6R5A2R7A3A2S3R8R7A2A2F_;F_;F_;F_;Fmsz;Fh;Ftp;Fmd;Fsegs;").
Proof.
  intros segs md tp h msz Hh Hm HMI Hfree. pose proof (paid_munmap_le segs md tp _ _ HMI Hfree) as P.
  assert (U : forall z, 0 <= z < 2 ^ 64 -> bv_unsigned (Z_to_bv 64 z) = z).
  { intros z Hz. rewrite Z_to_bv_unsigned. apply bv_wrap_small. unfold bv_modulus. exact Hz. }
  rewrite (U h Hh), (U msz Hm) in P. exact P.
Qed.
