(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Spec Require Import FseNCount FseLemmas ZdFrame ZdDCtx ZdSeqTable.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib Require Import Tac Arr Bytes ZBridge Image.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import StrFun STRW_tac WStr FseWalkKit FseWalkMem MemRange ZdCellKit ZdWalkKit ZdTbl ZdSeqBuildW.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Ubsan Require Import UImg RZ_blk_iface6 seqH_kit.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Section OI.
  Variables (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m : fmem) (SPV OFT tl : Z).
  Hypothesis RD : rdbl usegs m OFT (OFT + (8 + 8 * 2^tl)).
  Hypothesis TLR : 0 <= tl <= 8.
  Hypothesis OFR : 4096 <= OFT /\ OFT + 2056 < 2^47.
  Hypothesis SPR : 0 <= SPV < 2^64.
  Hypothesis MI : mem_inv usegs m.
  Notation POST := (zd_offinfo_post ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc SPV m).
  Notation ST pc x5 x6 x7 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 x28 x29 x30 x31 :=
    (MS (mkR ra (Z_to_bv 64 SPV) gp tp x5 x6 x7 s0 s1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
        F (Z_to_bv 64 pc) fc None m (seg_rom usegs)).

  (* [comment removed for export] *)
  Lemma oi_tail : forall u B x5 x6 x7 xa2 xa3 x28 x29 x30 x31,
    0 <= u < 2^tl -> 0 <= B < 256 ->
    (u + 1 < 2^tl -> forall p q x5 x6 x7 xa2 xa3 xa7 x28 x29 x30 x31, p = OFT + 10 + 8 * (u + 1) -> q = OFT + 8 + 8 * (u + 1) ->
       evt usegs POST (ST 0x17a48 x5 x6 x7 (Z_to_bv 64 p) (Z_to_bv 64 tl) xa2 xa3 (Z_to_bv 64 (OFT + 8)) (Z_to_bv 64 (u + 1 + 1)) (Z_to_bv 64 q) xa7 x28 x29 x30 x31)) ->
    evt usegs POST (ST 0x17a28 x5 x6 x7 (Z_to_bv 64 (OFT + 10 + 8 * u)) (Z_to_bv 64 tl) xa2 xa3 (Z_to_bv 64 (OFT + 8)) (Z_to_bv 64 (u + 1)) (Z_to_bv 64 (OFT + 8 + 8 * u)) (Z_to_bv 64 B) x28 x29 x30 x31).
  Proof.
    intros until x31. intros UR BR KONT.
    assert (P8 : 1 <= 2^tl <= 256) by (split; [apply (Z.pow_le_mono_r 2 0 tl); lia | change 256 with (2^8); apply Z.pow_le_mono_r; lia]).
    zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep.
    assert (EX : bv_swrap 32 (bv_wrap 32 (u + 1) ≫ (tl mod 32)) = if u + 1 =? 2^tl then 1 else 0).
    { replace (bv_wrap 32 (u + 1)) with (u + 1) by (unfold bv_wrap, bv_modulus; change (2 ^ Z.of_N 32) with 4294967296; rewrite Z.mod_small by lia; reflexivity).
      rewrite (Z.mod_small tl 32) by lia. rewrite Z.shiftr_div_pow2 by lia.
      destruct (Z.eqb_spec (u + 1) (2^tl)) as [E|NE].
      - rewrite E, Z.div_same by lia. reflexivity.
      - rewrite Z.div_small by lia. reflexivity. }
    rewrite EX. clear EX.
    destruct (Z.eqb_spec (u + 1) (2^tl)) as [E|NE].
    - if_true.
      zstep. zstep. zstep. zstep. rewrite (swrap32_small (8 - tl)) by lia. uck. zstep. zstep. zstep. zstep. zstep. zstep.
      apply evt_done. unfold zd_offinfo_post. do 15 eexists. exists m.
      split; [reflexivity|]. split; [apply munch_refl|]. split; [apply wmono_refl| exact MI].
    - if_false. replace (u + 2) with (u + 1 + 1) by lia. apply KONT; lia.
  Qed.

  (* [comment removed for export] *)
  Lemma oi_loop : forall (n : nat) u p q x5 x6 x7 xa2 xa3 xa7 x28 x29 x30 x31,
    Z.of_nat n = 2^tl - u -> 0 <= u < 2^tl -> p = OFT + 10 + 8 * u -> q = OFT + 8 + 8 * u ->
    evt usegs POST (ST 0x17a48 x5 x6 x7 (Z_to_bv 64 p) (Z_to_bv 64 tl) xa2 xa3 (Z_to_bv 64 (OFT + 8)) (Z_to_bv 64 (u + 1)) (Z_to_bv 64 q) xa7 x28 x29 x30 x31).
  Proof.
    induction n as [|n IH]; intros until x31; intros EN UR -> ->; [lia|].
    assert (P8 : 1 <= 2^tl <= 256) by (split; [apply (Z.pow_le_mono_r 2 0 tl); lia | change 256 with (2^8); apply Z.pow_le_mono_r; lia]).
    zstep. uck. zstep. uck.
    destruct (rdbl_read_at usegs m _ _ (OFT + 10 + 8 * u) 1 (wa (OFT + 10 + 8 * u)) RD ltac:(lia) ltac:(lia) eq_refl) as (bs & LB & RDB).
    destruct bs as [|b [|? ?]]; try discriminate LB. clear LB.
    zstep. cbv beta.
    pose proof (bv_unsigned_in_range 8 b) as BR. unfold bv_modulus in BR. change (2 ^ Z.of_N 8) with 256 in BR.
    set (B := bv_unsigned b) in *. clearbody B.
    assert (KONT : u + 1 < 2^tl -> forall p q x5 x6 x7 xa2 xa3 xa7 x28 x29 x30 x31, p = OFT + 10 + 8 * (u + 1) -> q = OFT + 8 + 8 * (u + 1) ->
              evt usegs POST (ST 0x17a48 x5 x6 x7 (Z_to_bv 64 p) (Z_to_bv 64 tl) xa2 xa3 (Z_to_bv 64 (OFT + 8)) (Z_to_bv 64 (u + 1 + 1)) (Z_to_bv 64 q) xa7 x28 x29 x30 x31)).
    { intros LT. intros. apply (IH (u + 1)); lia. }
    zstep. if_cases KC; zify_cond KC.
    - eapply oi_tail; [exact UR | lia | exact KONT].
    - zstep. zstep. eapply oi_tail; [exact UR | lia | exact KONT].
  Qed.
End OI.

Theorem zd_offinfo_proof : zd_offinfo_stmt.
Proof.
  unfold zd_offinfo_stmt, PZD_OFFINFO. intros until t. intros (TB & TOK) OL OH SPR MI AL ->.
  destruct (seq_tbl_len K_OF t TOK) as (TLEN & TLR). cbn [kind_maxLog] in TLR.
  pose proof (rdbl_of_bytes_at usegs m OFT _ TB) as RD. rewrite TLEN in RD. replace (8 * (1 + 2 ^ st_log t)) with (8 + 8 * 2^st_log t) in RD by lia.
  assert (P8 : 1 <= 2^st_log t <= 256) by (split; [apply (Z.pow_le_mono_r 2 0); lia | change 256 with (2^8); apply Z.pow_le_mono_r; lia]).
  zstep. if_cases K0; zify_cond K0.
  { zstep. zstep. apply evt_done. unfold zd_offinfo_post. do 15 eexists. exists m.
    split; [reflexivity|]. split; [apply munch_refl|]. split; [apply wmono_refl| exact MI]. }
  zstep. uck. zstep. zstep. uck.
  zstep. zstep. uck.
  pose proof (bytes_at_ov_read usegs m OFT _ 4 4 TB ltac:(rewrite length_map; pose proof (seq_table_bytes_length t) as L; unfold FseNCount.Zlength in L; lia)) as RD4.
  unfold seq_table_bytes in RD4. rewrite !map_app in RD4. cbn [zle4 map app firstn skipn] in RD4.
  change (Z.of_nat 4) with 4 in RD4.
  lazymatch type of RD4 with _ = Some ?l => replace l with (le4 (Z_to_bv 64 (st_log t))) in RD4 by (rewrite (le4_Z (st_log t) (st_log t) eq_refl); reflexivity) end.
  zstep. rewrite (sx32w_small (st_log t)) by lia.
  zstep. zstep. uck. zstep. zstep. zstep. zstep. zstep. zstep. zstep.
  eapply (oi_loop ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m SPV OFT (st_log t)) with (n := Z.to_nat (2^st_log t)) (u := 0); try eassumption; try lia.
Qed.
