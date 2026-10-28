(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.spirv_tools.spvtools_binary_parser_fuzzer.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BeapCeil.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import PropExec CatSim SymExec3 SymExec3Sound SymRun3.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash Require Import HLib.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BMState BMem BCells BArr BExec BLFrame BStep BSysStep BacX BellsX.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BSegs BsShadow BsConst BsIface BsStack0 BllocRepX.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont Require Import CRep ContLib.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibDiag Require Import DiagTac.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require Import LbB_Bridge LbB_Conv LbB_DStat.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Import SymExec3.SX2. Import SymExec3Sound.SX2S.

Definition A_CANARY : Z := ASSPGUARD.

Definition relro_clear (M : mem) : Prop := forall a, 0x17e000 <= a < 0x186000 -> M (Z_to_bv 64 a) = None.
Lemma relro_clear_iff : forall M, relro_clear M <-> relro0 M.
Proof. intros M. unfold relro_clear, relro0. tauto. Qed.

Lemma kimg_relro : forall E M, relro_clear M -> kentry_ok asegs E M (KImg 0x17e000 0x186000).
Proof. intros E M H. apply LbB_DStat.kimg_relro. exact (proj1 (relro_clear_iff M) H). Qed.

Lemma kimg_ro : forall E M, mem_inv asegs M -> kentry_ok asegs E M (KImg 0x10000 0x17e000).
Proof. intros E M H. apply kimg_of_mem_inv; [exact H | lia | lia]. Qed.

Lemma relro_clear_hi : forall W M M', relro_clear M -> stores_in W M M' -> (forall a, W a -> 0x186000 <= a) -> relro_clear M'.
Proof.
  intros W M M' RRC [A D] HW a Ha. rewrite (A (Z_to_bv 64 a)); [exact (RRC a Ha)|]. rewrite u64_of_Z by lia. intros Hw. pose proof (HW a Hw). lia.
Qed.

Lemma mem_inv_hi : forall W M M', mem_inv asegs M -> stores_in W M M' -> (forall a, W a -> 0x186000 <= a) -> mem_inv asegs M'.
Proof.
  intros W M M' MI [A D] HW a b Hb. pose proof (bv_unsigned_in_range 64 a) as Ra. change (bv_modulus 64) with (2 ^ 64) in Ra.
  destruct (M a) as [b0|] eqn:E0.
  - exact (MI a b0 E0).
  - assert (Wa : W (bv_unsigned a)).
    { destruct (Classical_Prop.classic (W (bv_unsigned a))) as [Y|N]; [exact Y|]. exfalso. rewrite (A a N) in Hb. congruence. }
    pose proof (HW _ Wa) as Hi.
    destruct (ro_addr asegs a) eqn:ER; [|reflexivity]. exfalso.
    rewrite <- (Z_to_bv_bv_unsigned a) in ER.
    unfold ro_addr in ER. rewrite Z_to_bv_bv_unsigned in ER.
    revert ER. unfold asegs, RefMemImage.Ref.loaded_segments, AsanUbsan.M.loaded_segments,
      AsanUbsan_loaded_segments. cbn [find_segment].
    change (seg_base AsanUbsan_segment_000) with 0x10000%N.
    change (seg_size AsanUbsan_segment_000) with 0x81000%N.
    change (seg_base AsanUbsan_segment_001) with 0x91000%N.
    change (seg_size AsanUbsan_segment_001) with 0xed000%N.
    change (seg_base AsanUbsan_segment_002) with 0x17e000%N.
    change (seg_size AsanUbsan_segment_002) with 0x8000%N.
    change (seg_base AsanUbsan_segment_003) with 0x186000%N.
    cbn [Z.of_N].
    replace ((65536 <=? bv_unsigned a) && (bv_unsigned a + 1 <=? 65536 + 528384))%bool with false
      by (symmetry; apply andb_false_iff; right; apply Z.leb_gt; lia).
    replace ((593920 <=? bv_unsigned a) && (bv_unsigned a + 1 <=? 593920 + 970752))%bool with false
      by (symmetry; apply andb_false_iff; right; apply Z.leb_gt; lia).
    replace ((1564672 <=? bv_unsigned a) && (bv_unsigned a + 1 <=? 1564672 + 32768))%bool with false
      by (symmetry; apply andb_false_iff; right; apply Z.leb_gt; lia).
    match goal with |- context [if ?c then _ else _] => destruct c end;
      [ replace (seg_writable AsanUbsan_segment_003) with true by reflexivity; discriminate | discriminate ].
Qed.

Lemma ro_none : forall M a, mem_inv asegs M -> 0x10000 <= a < 0x17e000 -> M (Z_to_bv 64 a) = None.
Proof.
  intros M a MI Ha. destruct (M (Z_to_bv 64 a)) as [b|] eqn:E; [|reflexivity]. exfalso.
  pose proof (MI _ _ E) as R. rewrite (ro_addr_seg01 a Ha) in R. discriminate.
Qed.

Lemma munch_of_stores_in : forall (W : Z -> Prop) (Wl : list (Z * Z)) M M',
  stores_in W M M' -> (forall a, W a -> ~ outside Wl a) -> munch Wl M M'.
Proof. intros W Wl M M' [A _] HW x Ho. apply A. intros Wx. exact (HW _ Wx Ho). Qed.

Lemma wmono_of_stores_in : forall (W : Z -> Prop) M M', stores_in W M M' -> wmono asegs M M'.
Proof.
  intros W M M' [_ D] x Hx. unfold wview in *. destruct (M x) as [b|] eqn:E.
  - pose proof (D x ltac:(rewrite E; discriminate)) as K. destruct (M' x); [discriminate | contradiction].
  - destruct (M' x); [discriminate | exact Hx].
Qed.

Lemma stk_stores : forall (W : Z -> Prop) M M' lo hi, stk asegs M lo hi -> stores_in W M M' ->
  (forall a, lo <= a < hi -> ~ W a) -> stk asegs M' lo hi.
Proof.
  intros W M M' lo hi (H0 & H1 & HW) [A D] HN. split; [exact H0|]. split; [exact H1|].
  intros i Hi. pose proof (bv_unsigned_in_range 64 (wa i)) as Ri.
  assert (E : M' (wa i) = M (wa i)) by (apply A; unfold wa; rewrite unsigned_lit by lia; exact (HN i Hi)).
  destruct (HW i Hi) as [W0 [b Hb]].
  split; [eapply wmono_of_stores_in; [split; [exact A | exact D] | exact W0]|].
  exists b. unfold mrd in *. rewrite E. exact Hb.
Qed.

Lemma stk_join : forall mm lo' mid hi, stk asegs mm lo' mid -> stk asegs mm mid hi -> stk asegs mm lo' hi.
Proof.
  intros mm lo' mid hi (A1 & A2 & A3) (B1 & B2 & B3). split; [exact A1|]. split; [exact B2|].
  intros a Ha. destruct (Z.lt_ge_cases a mid); [apply A3 | apply B3]; lia.
Qed.
