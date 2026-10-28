(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import FunctionalExtensionality.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Mmap Madvise.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import Tac Image ZBridge SysStep SFModel CellsX Arr TacX.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib Require Import AllocSim MmapSim SReach LazyRestrict LazyLedger LazySR LazyNodes LazyMadvise.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.As Require Import ASegs SecLazy.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Lemma ecall_1d69c0 : fetch_word asegs (Z_to_bv 64 0x1d1948) = Some ECALLW.
Proof. vm_compute. reflexivity. Qed.

(* [comment removed for export] *)
Lemma zfill_zero_id : forall (a n : word) (m : word -> option byte) (A : Z) (k : nat),
  u8arr asegs m A (repeat (b8 0) k) -> 12599296 <= A ->
  A <= bv_unsigned a -> bv_unsigned a + bv_unsigned n <= A + Z.of_nat k ->
  zfill a n m = m.
Proof.
  intros a n m A k [BA WR] HI LO UP. apply functional_extensionality. intros x.
  unfold zfill, AllocSim.zmem.
  destruct (Z.leb_spec (bv_unsigned a) (bv_unsigned x)); destruct (Z.ltb_spec (bv_unsigned x) (bv_unsigned a + bv_unsigned n)); cbn [andb]; try reflexivity.
  destruct BA as (_ & BH & BA). destruct WR as (_ & _ & WR). rewrite repeat_length in *.
  pose proof (bv_unsigned_in_range 64 x) as XR. change (bv_modulus 64) with (2^64) in XR.
  assert (EX : wa (A + Z.of_nat (Z.to_nat (bv_unsigned x - A))) = x).
  { unfold wa. replace (A + Z.of_nat (Z.to_nat (bv_unsigned x - A))) with (bv_unsigned x) by lia. apply Z_to_bv_bv_unsigned. }
  specialize (BA (Z.to_nat (bv_unsigned x - A)) ltac:(lia)). specialize (WR (Z.of_nat (Z.to_nat (bv_unsigned x - A))) ltac:(lia)).
  rewrite EX in BA, WR. rewrite nth_error_repeat in BA by lia.
  unfold mrd in BA. unfold wview in WR.
  destruct (m x) as [b|] eqn:E.
  - symmetry. exact BA.
  - exfalso. apply WR. rewrite asegs_find_segment_none_high by lia. reflexivity.
Qed.

Section CjMadvise.
  Variables (L S Zr : list (word * word)).
  Variables (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word)
            (F : bvmap 5 word) (pc : Z) (fc : bv 32) (rv : option word) (m : word -> option byte).
  Let R := mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31.
  Let Ra (a : word) := mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 a x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31.

  (* [comment removed for export] *)
  Lemma sr_madvise_MS : forall msF mo (Q : config -> Prop),
    lzok asegs L S Zr (mkCfg msF mo) ->
    restrict L S msF = MSsvc R F (Z_to_bv 64 pc) x17 fc rv m (seg_rom asegs) ->
    x17 = Z_to_bv 64 233 ->
    let addr := x10 in
    let nZ := page_round_up_Z (bv_unsigned x11) in
    let n := Z_to_bv 64 nZ in
    let h := m_vmmaps mo in
    bv_unsigned addr mod page_size = 0 -> bv_unsigned x12 mod 2 ^ 32 = 4 -> x11 <> Z_to_bv 64 0 -> bv_unsigned addr + nZ < 2 ^ 64 ->
    region_free (vm_reserved h) addr n = true -> map_contains (vm_maps h) addr n = true -> region_free (vm_noaccess h) addr n = true ->
    (forall x : word, bv_unsigned addr <= bv_unsigned x < bv_unsigned addr + nZ -> hiddenb L S x = true -> in_rangesb x Zr = true) ->
    (forall msF' : machine_state,
       let mo' := madvise_dontneed_next mo addr n in
       lzok asegs L S Zr (mkCfg msF' mo') ->
       restrict L S msF' = MS (Ra (Z_to_bv 64 0)) F (Z_to_bv 64 (pc + 4)) fc rv (mzero L S (addr, n) m) (seg_rom asegs) ->
       hid_same L S msF msF' ->
       same_but_materialized mo mo' ->
       sreach asegs Q (mkCfg msF' mo')) ->
    sreach asegs Q (mkCfg msF mo).
  Proof.
    intros msF mo Q OK VIS H17. cbv zeta. intros AL ADV LEN NW RF MC NA HZ K.
    eapply (sreach_madvise_dontneed_lazy asegs L S Zr msF _ mo x17 Q OK VIS eq_refl); [ rewrite H17; reflexivity | ..];
    change (ms_gpr (MSsvc R F (Z_to_bv 64 pc) x17 fc rv m (seg_rom asegs)) 0) with x10;
    change (ms_gpr (MSsvc R F (Z_to_bv 64 pc) x17 fc rv m (seg_rom asegs)) 1) with x11;
    change (ms_gpr (MSsvc R F (Z_to_bv 64 pc) x17 fc rv m (seg_rom asegs)) 2) with x12;
      [ exact AL | exact ADV | exact LEN | exact NW | exact RF | exact MC | exact NA | exact HZ | ].
    intros msF'.
    change (ms_mem (MSsvc R F (Z_to_bv 64 pc) x17 fc rv m (seg_rom asegs))) with m.
    cbv zeta. intros OK' VIS' HS' SBM. apply (K msF' OK'); [| exact HS' | exact SBM].
    rewrite VIS', sysret_MSsvc. unfold R. rewrite mkR_set_a0, lit_add_lit. reflexivity.
  Qed.
End CjMadvise.
