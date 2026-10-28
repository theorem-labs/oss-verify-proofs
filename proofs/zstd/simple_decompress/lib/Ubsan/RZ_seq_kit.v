(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib Require Import Tac Arr Bytes ZBridge Walk.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import MemRange ZdWalkKit ZdDctxRep.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Ubsan Require Import UImg F_memcpy F_memmove.
Import ListNotations.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Lemma memcpy_safe_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte),
  stk usegs m (bv_unsigned a0) (bv_unsigned a0 + bv_unsigned a2) ->
  rdbl usegs m (bv_unsigned a1) (bv_unsigned a1 + bv_unsigned a2) ->
  (bv_unsigned a1 + bv_unsigned a2 <= bv_unsigned a0 \/ bv_unsigned a0 + bv_unsigned a2 <= bv_unsigned a1) ->
  mem_inv usegs m ->
  evt usegs (memmove_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0 a1 a2 m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x3526c) fc None m (seg_rom usegs)).
Proof.
  intros until m. intros STD RDS SEP MI.
  set (S := bv_unsigned a1) in *. set (D := bv_unsigned a0) in *. set (n := bv_unsigned a2) in *.
  assert (RN : 0 <= n) by (subst n; pose proof (bv_unsigned_in_range 64 a2); lia).
  destruct (rdbl_bytes usegs m S (S + n) RDS ltac:(lia)) as (src & LEN & SRC).
  replace (S + n - S) with n in LEN by lia.
  destruct (stk_carve usegs m D (D + n) (Z.to_nat n) STD ltac:(lia)) as (_ & junk & DST).
  replace (D + n - Z.of_nat (Z.to_nat n)) with D in DST by lia.
  eapply evt_mono; [eapply (memcpy_spec _ _ _ _ _ _ _ _ _ a0 a1 a2 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m src junk SRC LEN DST SEP MI)|].
  intros ms' (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & m' & -> & MU & WM & MI' & DST' & SRC').
  do 15 eexists. split; [reflexivity|].
  split. { pose proof (stk_of_rw_cells usegs m' D _ DST') as ST'. cbn [cells_size csize Nat.add] in ST'. rewrite Nat.add_0_r, Z2Nat.id in ST' by lia. exact ST'. }
  split. { pose proof (rdbl_of_bytes_at usegs m' S src SRC') as R'. rewrite LEN, Z2Nat.id in R' by lia. exact R'. }
  split; [exact MI'|]. split; [exact MU| exact WM].
Qed.

(* [comment removed for export] *)
Definition held (P : Prop) : Prop := P.
Lemma held_intro : forall P : Prop, P -> held P. Proof. intros P H; exact H. Qed.
Ltac hold H := apply held_intro in H.

Lemma stk_mid_frame : forall (m m' : word -> option byte) D n lo hi,
  stk usegs m lo hi -> munch [(D, D + n)] m m' -> wmono usegs m m' -> stk usegs m' D (D + n) -> stk usegs m' lo hi.
Proof.
  intros m m' D n lo hi (H1 & H2 & H) MU WM (_ & _ & HD). split; [lia|]. split; [lia|].
  intros a Ha. destruct (Z_lt_ge_dec a D) as [L|L]; [|destruct (Z_lt_ge_dec a (D + n)) as [L2|L2]].
  - destruct (H a Ha) as [Hw (b & Hb)]. split; [apply WM; exact Hw|]. exists b. unfold mrd in *. rewrite MU; [exact Hb|].
    rewrite wa_unsigned by lia. cbn [outside]. split; [lia|exact I].
  - apply HD. lia.
  - destruct (H a Ha) as [Hw (b & Hb)]. split; [apply WM; exact Hw|]. exists b. unfold mrd in *. rewrite MU; [exact Hb|].
    rewrite wa_unsigned by lia. cbn [outside]. split; [lia|exact I].
Qed.

Lemma rdbl_mid_frame : forall (m m' : word -> option byte) D n lo hi,
  rdbl usegs m lo hi -> munch [(D, D + n)] m m' -> stk usegs m' D (D + n) -> rdbl usegs m' lo hi.
Proof.
  intros m m' D n lo hi (H1 & H2 & H) MU (_ & _ & HD). split; [lia|]. split; [lia|].
  intros a Ha. destruct (Z_lt_ge_dec a D) as [L|L]; [|destruct (Z_lt_ge_dec a (D + n)) as [L2|L2]].
  - destruct (H a Ha) as (b & Hb). exists b. unfold mrd in *. rewrite MU; [exact Hb|].
    rewrite wa_unsigned by lia. cbn [outside]. split; [lia|exact I].
  - apply HD. lia.
  - destruct (H a Ha) as (b & Hb). exists b. unfold mrd in *. rewrite MU; [exact Hb|].
    rewrite wa_unsigned by lia. cbn [outside]. split; [lia|exact I].
Qed.

Definition copy_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (a0 : word) (D n : Z) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1' a2' a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1' a2' a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom usegs)
    /\ munch [(D, D + n)] m m' /\ wmono usegs m m' /\ mem_inv usegs m'
    /\ (forall lo hi, held (stk usegs m lo hi) -> stk usegs m' lo hi)
    /\ (forall lo hi, held (rdbl usegs m lo hi) -> rdbl usegs m' lo hi).

Lemma copy_post_of_mv : forall ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0 a1 a2 m ms',
  memmove_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0 a1 a2 m ms' ->
  copy_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0 (bv_unsigned a0) (bv_unsigned a2) m ms'.
Proof.
  intros until ms'. intros (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & m' & -> & STD & RDS & MI' & MU & WM).
  do 15 eexists. split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI'|]. split.
  - intros lo hi H. eapply stk_mid_frame; eauto.
  - intros lo hi H. eapply rdbl_mid_frame; eauto.
Qed.

(* [comment removed for export] *)
Lemma memmove_call_spec : forall (D S n : Z) ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte),
  stk usegs m D (D + n) -> rdbl usegs m S (S + n) -> 0 <= n -> 0 <= S -> 0 <= D -> S + n <= 2^63 -> D + n <= 2^63 -> mem_inv usegs m ->
  evt usegs (copy_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (Z_to_bv 64 D) D n m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 D) (Z_to_bv 64 S) (Z_to_bv 64 n) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x35670) fc None m (seg_rom usegs)).
Proof.
  intros until m. intros STD RDS Hn HS HD BS BD MI.
  assert (ED : bv_unsigned (Z_to_bv 64 D) = D) by (apply unsigned_lit; lia).
  assert (ES : bv_unsigned (Z_to_bv 64 S) = S) by (apply unsigned_lit; lia).
  assert (En : bv_unsigned (Z_to_bv 64 n) = n) by (apply unsigned_lit; lia).
  eapply evt_mono.
  { eapply memmove_spec; rewrite ?ED, ?ES, ?En; [split; lia | exact STD | exact RDS | exact MI]. }
  intros ms' PO. apply copy_post_of_mv in PO. rewrite ED, En in PO. exact PO.
Qed.

Lemma memcpy_call_spec : forall (D S n : Z) ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte),
  stk usegs m D (D + n) -> rdbl usegs m S (S + n) -> 0 <= n -> 0 <= S -> 0 <= D -> S + n <= 2^63 -> D + n <= 2^63 ->
  (S + n <= D \/ D + n <= S) -> mem_inv usegs m ->
  evt usegs (copy_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (Z_to_bv 64 D) D n m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 D) (Z_to_bv 64 S) (Z_to_bv 64 n) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x3526c) fc None m (seg_rom usegs)).
Proof.
  intros until m. intros STD RDS Hn HS HD BS BD SEP MI.
  assert (ED : bv_unsigned (Z_to_bv 64 D) = D) by (apply unsigned_lit; lia).
  assert (ES : bv_unsigned (Z_to_bv 64 S) = S) by (apply unsigned_lit; lia).
  assert (En : bv_unsigned (Z_to_bv 64 n) = n) by (apply unsigned_lit; lia).
  eapply evt_mono.
  { eapply memcpy_safe_spec; rewrite ?ED, ?ES, ?En; [exact STD | exact RDS | exact SEP | exact MI]. }
  intros ms' PO. apply copy_post_of_mv in PO. rewrite ED, En in PO. exact PO.
Qed.

(* [comment removed for export] *)
Lemma stk_sub : forall (m : word -> option byte) lo hi lo' hi',
  stk usegs m lo hi -> lo <= lo' -> lo' <= hi' -> hi' <= hi -> stk usegs m lo' hi'.
Proof.
  intros m lo hi lo' hi' ST H1 H2 H3.
  destruct (stk_split usegs m lo lo' hi ST ltac:(lia)) as [_ T]. destruct (stk_split usegs m lo' hi' hi T ltac:(lia)) as [T2 _]. exact T2.
Qed.

(* [comment removed for export] *)
Lemma rw_cells_forget : forall (m : word -> option byte) A cs (k n : nat),
  rw_cells usegs m A cs -> cells_size (firstn k cs) = n ->
  rw_cells usegs m A (CB n (cells_bytes (firstn k cs)) :: skipn k cs).
Proof.
  intros m A cs k n RW SZ. pose proof RW as [[WF _] _].
  rewrite <- (firstn_skipn k cs) in WF. apply cells_wf_app in WF. destruct WF as [W1 W2].
  eapply rw_cells_recell; [exact RW| |].
  - cbn [cells_wf cell_wf]. split; [|exact W2]. rewrite cells_bytes_length by exact W1. exact SZ.
  - cbn [cells_bytes cbytes]. rewrite <- cells_bytes_app, firstn_skipn. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma h5_explode : forall ws : list word, length ws = 44%nat ->
  exists w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 w21 w22 w23 w24 w25 w26 w27 w28 w29 w30 w31 w32 w33 w34 w35 w36 w37 w38 w39 w40 w41 w42 w43 : word,
    ws = [w0; w1; w2; w3; w4; w5; w6; w7; w8; w9; w10; w11; w12; w13; w14; w15; w16; w17; w18; w19; w20; w21; w22; w23; w24; w25; w26; w27; w28; w29; w30; w31; w32; w33; w34; w35; w36; w37; w38; w39; w40; w41; w42; w43].
Proof.
  intros ws L. do 44 (destruct ws as [|? ws]; [discriminate L|]). destruct ws; [|discriminate L].
  do 44 eexists. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma h5_view : forall (m : word -> option byte) DCTX ws,
  dctx_h5 usegs m DCTX ws ->
  exists j1 j2 j3, length j1 = 24%nat /\ length j2 = 24%nat /\ length j3 = 192%nat /\
    rw_cells usegs m (DCTX + 30096)
      [CB 24 j1; C8 (wnth ws H5_litPtr); CB 24 j2; C8 (wnth ws H5_litSize); CB 192 j3;
       C8 (wnth ws H5_litBuffer); C8 (wnth ws H5_litBufferEnd); C4 (wnth ws H5_litBufferLocation)].
Proof.
  intros m DCTX ws (RW & WL).
  destruct (h5_explode ws WL) as (w0 & w1 & w2 & w3 & w4 & w5 & w6 & w7 & w8 & w9 & w10 & w11 & w12 & w13 & w14 & w15 & w16 & w17 & w18 & w19 & w20 & w21 & w22 & w23 & w24 & w25 & w26 & w27 & w28 & w29 & w30 & w31 & w32 & w33 & w34 & w35 & w36 & w37 & w38 & w39 & w40 & w41 & w42 & w43 & ->).
  cbv beta iota delta [h5_cells h5_sizes mk_wcells wnth nth H5_litPtr H5_litSize H5_litBuffer H5_litBufferEnd H5_litBufferLocation] in *.
  exists (le8 w0 ++ le4 w1 ++ le4 w2 ++ le4 w3 ++ le4 w4),
         (le8 w6 ++ le8 w7 ++ le8 w8),
         (le8 w10 ++ le8 w11 ++ le4 w12 ++ le4 w13 ++ le8 w14 ++ le8 w15 ++ le4 w16 ++ le4 w17 ++ le4 w18 ++ le4 w19 ++ le8 w20 ++
          le4 w21 ++ le4 w22 ++ le4 w23 ++ le4 w24 ++ le8 w25 ++ le8 w26 ++ le8 w27 ++ le8 w28 ++ le8 w29 ++ le8 w30 ++ le8 w31 ++
          le8 w32 ++ le8 w33 ++ le4 w34 ++ le4 w35 ++ le4 w36 ++ le4 w37 ++ le8 w38 ++ le8 w39 ++ le8 w40).
  split; [rewrite !length_app, ?length_le8, ?length_le4; reflexivity|].
  split; [rewrite !length_app, ?length_le8, ?length_le4; reflexivity|].
  split; [rewrite !length_app, ?length_le8, ?length_le4; reflexivity|].
  eapply rw_cells_recell; [exact RW| |].
  - cbn [cells_wf cell_wf]. rewrite !length_app, ?length_le8, ?length_le4. repeat split; reflexivity.
  - cbn [cells_bytes cbytes]. rewrite <- !app_assoc. reflexivity.
Qed.

(* [comment removed for export] *)
Definition BITMASK : Z := 0x10f10.
Definition bitmask_bytes : list byte := Eval vm_compute in match image_bytes usegs BITMASK 128 with Some bs => bs | None => [] end.

Lemma bitmask_at : forall m, mem_inv usegs m -> bytes_at usegs m BITMASK bitmask_bytes.
Proof.
  intros m MI. pose proof (ro_cells_image usegs m BITMASK bitmask_bytes MI ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)) as [_ H].
  cbn [cells_bytes cbytes] in H. rewrite app_nil_r in H. exact H.
Qed.

Lemma bitmask_val : forall nb, 0 <= nb <= 31 ->
  bytes_le_to_Z (firstn 4 (skipn (Z.to_nat (4 * nb)) bitmask_bytes)) = 2^nb - 1.
Proof.
  intros nb H. assert (C : exists k : nat, (k <= 31)%nat /\ nb = Z.of_nat k) by (exists (Z.to_nat nb); lia).
  destruct C as (k & Hk & ->). do 32 (destruct k as [|k]; [vm_compute; reflexivity|]). lia.
Qed.

Lemma bytes_eq_unsigned : forall a b : list byte, map (@bv_unsigned 8) a = map (@bv_unsigned 8) b -> a = b.
Proof.
  induction a as [|x a IH]; intros [|y b] H; try discriminate; [reflexivity|].
  cbn [map] in H. injection H as H1 H2. f_equal; [apply bv_eq; exact H1 | apply IH; exact H2].
Qed.

(* [comment removed for export] *)
Lemma bitmask_know : forall m nb, mem_inv usegs m -> 0 <= nb <= 31 ->
  rdn usegs m (wa (BITMASK + 4 * nb)) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 (2^nb - 1))).
Proof.
  intros m nb MI H. replace (BITMASK + 4 * nb) with (BITMASK + Z.of_nat (Z.to_nat (4 * nb))) by lia.
  rewrite (bytes_at_rdn usegs m BITMASK bitmask_bytes (Z.to_nat (4 * nb)) 4 (bitmask_at m MI)) by (change (length bitmask_bytes) with 128%nat; lia).
  f_equal. assert (C : exists k : nat, (k <= 31)%nat /\ nb = Z.of_nat k) by (exists (Z.to_nat nb); lia).
  destruct C as (k & Hk & ->). do 32 (destruct k as [|k]; [apply bytes_eq_unsigned; vm_compute; reflexivity|]). lia.
Qed.

(* [comment removed for export] *)
Lemma land_mask_lt : forall x nb, 0 <= x -> 0 <= nb -> 0 <= Z.land x (2^nb - 1) < 2^nb.
Proof.
  intros x nb Hx Hn. replace (2^nb - 1) with (Z.ones nb) by (rewrite Z.ones_equiv; lia).
  rewrite Z.land_ones by lia. apply Z.mod_pos_bound. apply Z.pow_pos_nonneg; lia.
Qed.
