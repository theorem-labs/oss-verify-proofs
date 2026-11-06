(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.fast_float.from_chars.images Require Import Ubsan.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec CatExec CatSim StoreOk SeqExec AxSymExec3 AxSymExec3Sound AxSymRun3.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require Import MallocModel MallocInv.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require AxMng MngHeap MngWb.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require MngHeap.
Import OSSVerify.Proofs.fast_float.from_chars.lib.MAX.AxMng OSSVerify.Proofs.fast_float.from_chars.lib.MAX.MngHeap OSSVerify.Proofs.fast_float.from_chars.lib.MAX.MngWb OSSVerify.Proofs.fast_float.from_chars.lib.MAX.MngHeap.AxTry2.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAXU Require AxBits MngZ MngNtfM AxTry AXG_as5 AXG_ag0 AXG_ag1.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAXU Require AXF_eez.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAXU Require AXF_nmz.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAXU Require AXF_eez.
Import OSSVerify.Proofs.fast_float.from_chars.lib.MAXU.AxBits OSSVerify.Proofs.fast_float.from_chars.lib.MAXU.MngZ OSSVerify.Proofs.fast_float.from_chars.lib.MAXU.MngNtfM OSSVerify.Proofs.fast_float.from_chars.lib.MAXU.AxTry OSSVerify.Proofs.fast_float.from_chars.lib.MAXU.AXG_as5 OSSVerify.Proofs.fast_float.from_chars.lib.MAXU.AXG_ag0 OSSVerify.Proofs.fast_float.from_chars.lib.MAXU.AXG_ag1 OSSVerify.Proofs.fast_float.from_chars.lib.MAXU.AXF_eez.AXF_nj0z OSSVerify.Proofs.fast_float.from_chars.lib.MAXU.AXF_nmz OSSVerify.Proofs.fast_float.from_chars.lib.MAXU.AXF_eez.AXF_ncallz.
Import ListNotations AX2 AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Lemma stc_total : forall sz, 0 <= sz -> sz mod 16 = 0 -> size_to_class (sz + 12) = class_of_units (Z.shiftr sz 4).
Proof.
  intros sz H0 H16. unfold size_to_class, IB. f_equal. rewrite !Z.shiftr_div_pow2 by lia. change (2^4) with 16.
  apply Z.mod_divide in H16; [|lia]. destruct H16 as (k & ->). replace (k * 16 + 12 + 4 - 1) with (k * 16 + 15) by ring.
  rewrite Z.div_mul by lia. rewrite Z.div_add_l by lia. change (15 / 16) with 0. ring.
Qed.

Section AG8.
Context {fx : FPState}.

#[using="Type"] Theorem seg_npre : forall R m rom sz,
  getr R 14 = wa sz -> getr R 25 = wa 98984 -> 16 <= sz <= 2032 -> sz mod 16 = 0 ->
  (forall sc, 0 <= sc < 48 -> rdn SEGS m (wa (98984 + 2 * sc)) 2 = Some (word_to_le_bytes 2 (wa (znth sc size_classes)))) -> DBT m ->
  exists R', msteps SEGS (mkst R (wa 0x543b8) m rom) (mkst R' (wa 0x540a8) m rom) /\
    getr R' 1 = wa 0x54488 /\ getr R' 10 = wa (size_to_class (sz + 12)) /\ getr R' 11 = wa (sz + 12) /\
    getr R' 18 = wa (size_to_class (sz + 12)) /\
    (forall k, In k [2; 3; 4; 8; 9; 19; 20; 21; 22; 23; 24; 25; 26; 27]%nat -> getr R' (Z_to_bv 5 (Z.of_nat k)) = getr R (Z_to_bv 5 (Z.of_nat k))).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros R m rom sz R14 R25 Hsz A16 Mtab Mdb.
  assert (P : nj0_pre R m sz) by (constructor; [exact R14 | lia | exact A16]).
  pose proof (size_to_class_range (sz + 12) ltac:(unfold MMAP_THRESHOLD; lia)) as (Hj & _).
  rewrite (stc_total sz ltac:(lia) A16) in *.
  set (u := Z.shiftr sz 4) in *.
  assert (Hu : u = sz / 16) by (unfold u; rewrite Z.shiftr_div_pow2 by lia; reflexivity).
  destruct (Z_lt_ge_dec (sz + 12) 157) as [Sm|Me].
  - destruct (nj0_pnjs R m rom sz P) as (R1 & Hms1 & A10 & A11 & A14 & AK).
    { scs_go; zats. rewrite !Z.mod_small by lia. apply Z.ltb_lt. lia. }
    assert (Cu : class_of_units u = u) by (unfold class_of_units; replace (u <? 10) with true by (symmetry; apply Z.ltb_lt; lia); reflexivity).
    rewrite Cu. fold u in A14.
    destruct (ncall_pncall R1 m rom u ltac:(constructor; [exact A14 | lia]) ltac:(constructor)) as (R2 & Hms2 & B1 & B10 & B14 & B18 & BK).
    unfold nj0_mem_pnjs, ncall_mem_pncall in *.
    exists R2. split; [exact (msteps_trans SEGS _ _ _ Hms1 Hms2)|].
    split; [exact B1|]. split; [exact B10|]. split; [regk BK 11%nat; exact A11|]. split; [exact B18|].
    intros k Hk. rewrite (BK k ltac:(clear - Hk; klist Hk)). apply AK. clear - Hk. klist Hk.
  - destruct (nj0_pnjm R m rom sz P) as (R1 & Hms1 & A10 & A11 & A14 & AK).
    { scs_go; zats. rewrite !Z.mod_small by lia. apply Z.ltb_ge. lia. }
    fold u in A14.
    destruct (njm_arm R1 m rom u A14 ltac:(regk AK 25%nat; exact R25) ltac:(lia) Mtab Mdb) as (R1' & Hms1' & C14 & CK).
    destruct (ncall_pncall R1' m rom (class_of_units u) ltac:(constructor; [exact C14 | lia]) ltac:(constructor))
      as (R2 & Hms2 & B1 & B10 & B14 & B18 & BK).
    unfold nj0_mem_pnjm, ncall_mem_pncall in *.
    exists R2. split; [exact (msteps_trans SEGS _ _ _ Hms1 (msteps_trans SEGS _ _ _ Hms1' Hms2))|].
    split; [exact B1|]. split; [exact B10|]. split; [regk BK 11%nat; regk CK 11%nat; exact A11|]. split; [exact B18|].
    intros k Hk. rewrite (BK k ltac:(clear - Hk; klist Hk)), (CK k ltac:(clear - Hk; klist Hk)). apply AK. clear - Hk. klist Hk.
Qed.
End AG8.
