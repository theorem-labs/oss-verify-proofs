(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import FunctionalExtensionality.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Mmap Madvise.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import Tac Image ZBridge SysStep SFModel CellsX Arr TacX.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Import AllocSim MmapSim SReach LazyRestrict LazyLedger LazySR LazyNodes LazyMadvise.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Bs Require Import ASegs SecLazy.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import Nd.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
Local Ltac2 zQ s := CDef.cdeft "37Corelib7Numbers7BinNums04Npos35stdpp9bitvectorbdefinitionshf2bv37Corelib4Init9Datatypesk14Somek16option37Corelib4Init5Logicm92eq3h5LinuxProcessSemanticsfLinuxProcessSemeRiscvSemanticso2afetch_word79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2Bs5ASegs~~~~~~s65asegs79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2Bs7SecLazy~~~~~~hg96ECALLWhf7Z_to_bv46Stdlib6ZArith6BinInt1Zhla2lehfbbv_unsignedhla3addk13nat37Corelib5Lists7ListDefhp36repeat01Z79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib3Arr~~~~~~hr75u8arr79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib4TacX~~~~~~hva2b869OSSVerify6Proofsaboost_jsonafuzz_parse3lib7MmapSim~~~~~~ijb5zfillhla6of_nat" s.   (* [comment removed for export] *)
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Lemma ecall_a2a94 : ltac2:(zQ "90!h9!jc!l9!m0!nd!r9!hg1!hk6!hl0@3$4@1$3@1$1@1$0#i0@2$5$6@2$8@1$0#k0+qiqnc@2$2@1$1@1$0#i0$7").
Proof. vm_compute. reflexivity. Qed.

(* [comment removed for export] *)
Lemma zfill_zero_id : ltac2:(zQ "f1!h9!jc!hn2!hn8!m0!ho6!hod!nd!hqa!hr4!hg1!hv1!ij5!in5!ine&>0@1$1@1$0#k0@1$4@1$1@1$0#8>1a@1$1@1$0#k0>1n@1$1@1$0#k0>1m~0>1A$9>1k$6>0@4$b$a^3^2@3$8@1$1@1$0#8@1$cZ^1>0@2$2+nhjgg0^3>0@2$2^4@2$3@1$0#k0^7>0@2$2@2$5@2$3@1$0#k0^8@2$3@1$0#k0^7@2$5^5@1$e^4@3$7~0@3$d^9^8^7^7").
Proof.
  intros a n m A k [BA WR] HI LO UP. apply functional_extensionality. intros x.
  unfold zfill, AllocSim.zmem.
  destruct (Z.leb_spec (bv_unsigned a) (bv_unsigned x)); destruct (Z.ltb_spec (bv_unsigned x) (bv_unsigned a + bv_unsigned n)); cbn [andb]; try reflexivity.
  ndestruct BA as (_ & BH & BA). ndestruct WR as (_ & _ & WR). rewrite repeat_length in *.
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
