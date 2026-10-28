(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Spec Require Import FseNCount FseLemmas ZdFrame ZdHufStats ZdHufX1 ZdSeqTable.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Spec Require FseNCountRT.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib Require Import Tac Arr Bytes ZBridge.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib Require SysStep.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import StrFun STRW_tac WStr FseWalkKit FseWalkMem FseRdKit MemRange ZdCellKit ZdWalkKit ZdSeqBuildW ZdHufW ZdHufWM ZdHufWR ZdHufWX SepHide.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Ubsan Require Import UImg F_memset RZ_huf_iface RZ_hft_iface RZ_hft_rs_iface RZ_hft_kit RZ_hft_bdt_defs RZ_hft_x1_kit.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Ltac u32st2 RK s x v :=
  lazymatch type of RK with u32arr ?segs ?mx ?Wb (map (Z_to_bv 64) ?l) =>
    let a := cur_mem_addr in
    let SOK := fresh "SOK" in
    pose proof (u32arr_store_ok segs mx Wb _ s a RK ltac:(rewrite length_map, ?Zupd_length; lia) ltac:(unfold wa; f_equal; lia)) as SOK;
    zstep;
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem mx ?a2 _) _) =>
      replace a2 with (wa (Wb + 4 * s)) by (unfold wa; f_equal; lia) end;
    let S2 := fresh "RK" in
    pose proof (u32arr_write segs mx Wb _ s (Z_to_bv 64 x) RK ltac:(rewrite length_map, ?Zupd_length; lia)) as S2;
    clear RK; store_done;
    apply (u32arr_upd_Z segs _ Wb l (Z.to_nat s) x v) in S2; [| first [ reflexivity | rewrite Z.mod_mod by lia; reflexivity ]];
    rename S2 into RK
  end.

Definition ux1_K32 : Z := - 2^31 - 1.
Definition ux1_K120 : Z := 2^48 + 2^32 + 2^16 + 1.

Definition x1s (DT WK wksz SPV lo : Z) (m : fmem) (SAV : list cell) (hw rank : list Z) (fl : list cell) (wn wt : word)
    (dt rst : list Z) (syb : list byte) (m1 : fmem) : Prop :=
  u8arr usegs m1 DT (map (Z_to_bv 8) dt) /\ Z.of_nat (length dt) = HUF_DTABLE_BYTES /\ Forall isbyte dt
  /\ u8arr usegs m1 (WK + 1236) (map (Z_to_bv 8) hw)
  /\ u32arr usegs m1 WK (map (Z_to_bv 64) rank)
  /\ u32arr usegs m1 (WK + 52) (map (Z_to_bv 64) rst) /\ Z.of_nat (length rst) = 13
  /\ stk usegs m1 (WK + 104) (WK + 980)
  /\ u8arr usegs m1 (WK + 980) syb /\ Z.of_nat (length syb) = 256
  /\ stk usegs m1 (WK + 1492) (WK + wksz)
  /\ rw_cells usegs m1 (SPV + -240) fl /\ cells_size fl = 128%nat
  /\ rw_cells usegs m1 (SPV + -112) [C4 wn; C4 wt]
  /\ rw_cells usegs m1 (SPV + -104) SAV /\ stk usegs m1 lo (SPV + -240)
  /\ mem_inv usegs m1 /\ munch [(DT, DT + HUF_DTABLE_BYTES); (WK, WK + wksz); (SPV - HUF_TBL_STACK, SPV)] m m1 /\ wmono usegs m m1.

Definition x1m (DT WK wksz SPV lo : Z) (m : fmem) (SAV : list cell) (fl : list cell) (wn wt : word)
    (dt hw rank : list Z) (m1 : fmem) : Prop :=
  u8arr usegs m1 DT (map (Z_to_bv 8) dt) /\ Z.of_nat (length dt) = HUF_DTABLE_BYTES /\ Forall isbyte dt
  /\ u8arr usegs m1 (WK + 1236) (map (Z_to_bv 8) hw) /\ Z.of_nat (length hw) = 256 /\ Forall isbyte hw
  /\ u32arr usegs m1 WK (map (Z_to_bv 64) rank) /\ Z.of_nat (length rank) = 13
  /\ stk usegs m1 (WK + 52) (WK + 104) /\ stk usegs m1 (WK + 104) (WK + 980) /\ stk usegs m1 (WK + 980) (WK + 1236)
  /\ stk usegs m1 (WK + 1492) (WK + wksz)
  /\ rw_cells usegs m1 (SPV + -240) fl /\ cells_size fl = 128%nat
  /\ rw_cells usegs m1 (SPV + -112) [C4 wn; C4 wt]
  /\ rw_cells usegs m1 (SPV + -104) SAV /\ stk usegs m1 lo (SPV + -240)
  /\ mem_inv usegs m1 /\ munch [(DT, DT + HUF_DTABLE_BYTES); (WK, WK + wksz); (SPV - HUF_TBL_STACK, SPV)] m m1 /\ wmono usegs m m1.

Lemma upd_bytes_map4 : forall (f : Z -> byte) (l : list Z) (i : nat) a b c d, (i + 4 <= length l)%nat ->
  upd_bytes (map f l) i [f a; f b; f c; f d] = map f (upd_nat (i + 3) d (upd_nat (i + 2) c (upd_nat (i + 1) b (upd_nat i a l)))).
Proof.
  intros f l i. revert l. induction i as [|i IH]; intros l a b c d H.
  - destruct l as [|x [|y [|z [|u t]]]]; cbn [length] in H; try lia. reflexivity.
  - destruct l as [|x t]; cbn [length] in H; [lia|].
    change (upd_bytes (map f (x :: t)) (S i) [f a; f b; f c; f d]) with (f x :: upd_bytes (map f t) i [f a; f b; f c; f d]).
    rewrite IH by lia. reflexivity.
Qed.

Lemma u8arr_sw : forall m A (buf : list Z) i x v,
  u8arr usegs m A (map (Z_to_bv 8) buf) -> 0 <= i -> i + 4 <= Z.of_nat (length buf) -> x mod 2^32 = v mod 2^32 ->
  u8arr usegs (write_to_mem m (wa (A + i)) (le4 (Z_to_bv 64 x))) A
        (map (Z_to_bv 8) (Zupd (i + 3) ((v / 16777216) mod 256) (Zupd (i + 2) ((v / 65536) mod 256)
                          (Zupd (i + 1) ((v / 256) mod 256) (Zupd i (v mod 256) buf))))).
Proof.
  intros m A buf i x v ARR Hi Hl E.
  pose proof (u8arr_writen usegs m A _ i (le4 (Z_to_bv 64 x)) ARR Hi ltac:(rewrite length_map, length_le4; lia)) as H.
  rewrite (le4_Z x v E) in H. unfold zle4 in H. cbn [map] in H.
  rewrite upd_bytes_map4 in H by lia. unfold Zupd.
  replace (Z.to_nat (i + 1)) with (Z.to_nat i + 1)%nat by lia.
  replace (Z.to_nat (i + 2)) with (Z.to_nat i + 2)%nat by lia.
  replace (Z.to_nat (i + 3)) with (Z.to_nat i + 3)%nat by lia.
  rewrite (le4_Z x v E). exact H.
Qed.

Lemma rw_cells_C8_CB : forall segs m A pre y post,
  rw_cells segs m A (pre ++ C8 y :: post) -> rw_cells segs m A (pre ++ CB 8 (le8 y) :: post).
Proof.
  intros segs m A pre y post H.
  pose proof (rw_cells_merge segs m A pre [C8 y] post) as M. cbn [cells_size cells_bytes cbytes csize] in M.
  rewrite app_nil_r in M. apply M. exact H.
Qed.

Section X1E.
  Variables (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m : fmem)
            (SPV DT WK wksz lo : Z).
  Hypothesis LO0 : 4096 <= lo.  Hypothesis LOS : lo <= SPV - HUF_TBL_STACK.  Hypothesis SPR : SPV < 2^47.

  Notation POST := (huf_rd_post ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc SPV DT WK wksz lo false m).
  Notation MUNCH := [(DT, DT + HUF_DTABLE_BYTES); (WK, WK + wksz); (SPV - HUF_TBL_STACK, SPV)].
  Notation STF pc mm x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 :=
    (MS (mkR x1 (Z_to_bv 64 (SPV + -240)) gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
        F (Z_to_bv 64 pc) fc None mm (seg_rom usegs)).
  Notation SAVED := [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

  Lemma x1_exit : forall m1 f0 dtb' r x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31,
    u8arr usegs m1 DT dtb' -> huf_hdr_ok dtb' -> stk usegs m1 WK (WK + wksz) -> stk usegs m1 lo (SPV + -240) ->
    rw_cells usegs m1 (SPV + -240) f0 -> cells_size f0 = 136%nat -> rw_cells usegs m1 (SPV + -104) SAVED ->
    mem_inv usegs m1 -> munch MUNCH m m1 -> wmono usegs m m1 -> 0 <= r < 2^64 ->
    (zd_is_error r = false -> huf_tbl_ok dtb' /\ exists ty, nth_error dtb' 1 = Some ty /\ (bv_unsigned ty <> 0 <-> false = true)) ->
    evt usegs POST (STF 0x1f2f0 m1 x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 r) x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31).
  Proof.
    intros until x31; intros DTC HDR' WKS STK F0 SZ0 FSAV MI MU WM RR RES. unfold HUF_TBL_STACK, HUF_DTABLE_BYTES in *.
    zstep. do 13 zstep. zstep.
    apply stk_of_rw_cells in F0, FSAV. rewrite SZ0 in F0. cbn [cells_size csize Nat.add] in FSAV.
    assert (STK' : stk usegs m1 lo SPV).
    { apply (stk_merge usegs m1 lo (SPV + -240) SPV STK); [|lia].
      apply (stk_merge usegs m1 (SPV + -240) (SPV + -104) SPV); [replace (SPV + -104) with (SPV + -240 + Z.of_nat 136) by lia; exact F0| |lia].
      replace SPV with (SPV + -104 + Z.of_nat 104) at 2 by lia. exact FSAV. }
    zstep. apply evt_done. unfold huf_rd_post.
    do 14 eexists. exists m1, r, dtb'.
    split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact STK'|].
    split; [exact WKS|]. split; [exact DTC|]. split; [exact HDR'|]. split; [exact RR| exact RES].
  Qed.

  Lemma x1_exit_stk : forall m1 dtb' r x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31,
    u8arr usegs m1 DT dtb' -> huf_hdr_ok dtb' -> stk usegs m1 WK (WK + wksz) -> stk usegs m1 lo (SPV + -240) ->
    stk usegs m1 (SPV + -240) (SPV + -104) -> rw_cells usegs m1 (SPV + -104) SAVED ->
    mem_inv usegs m1 -> munch MUNCH m m1 -> wmono usegs m m1 -> 0 <= r < 2^64 ->
    (zd_is_error r = false -> huf_tbl_ok dtb' /\ exists ty, nth_error dtb' 1 = Some ty /\ (bv_unsigned ty <> 0 <-> false = true)) ->
    evt usegs POST (STF 0x1f2f0 m1 x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 r) x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31).
  Proof.
    intros until x31; intros DTC HDR' WKS STK STF0 FSAV MI MU WM RR RES.
    destruct (stk_open usegs m1 (SPV + -240) (SPV + -104) (SPV + -240) 136%nat STF0 ltac:(lia) ltac:(lia)) as (j & C & _ & _).
    eapply (x1_exit m1 [CB 136 j] dtb' r); try eassumption. reflexivity.
  Qed.
End X1E.
