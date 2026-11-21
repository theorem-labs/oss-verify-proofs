(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_halts_any_exit.zspec.zmodel Require Import ZIface InflateState.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_halts_any_exit Require Import PropExec CatExec CatSim StoreOk ShapeAlg.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_halts_any_exit.IK Require Import TSet ZStep ZMem ZPrune ZTac ZCall ZCallL ZArr IDefs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Section FXG. Context {fx : OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_halts_any_exit.PropExec.FPState}.

Lemma disj_all_sub : forall rs a n a' n', disj_all a n rs -> a <= a' -> a' + n' <= a + n -> disj_all a' n' rs.
Proof.
  induction rs as [|[lo len] rs' IH]; cbn; intros a n a' n' Hd H1 H2; [tauto|].
  destruct Hd as [X Y]. split; [lia_std | eapply IH; [exact Y | lia_std | lia_std]].
Qed.

Lemma mpost_mpostL : forall segs M M' lo1 hi1 lo2 hi2,
  mpost segs M M' lo1 hi1 lo2 hi2 -> mpostL segs M M' [(lo1, hi1 - lo1); (lo2, hi2 - lo2)].
Proof.
  intros segs M M' lo1 hi1 lo2 hi2 [HA HW]. split; [| exact HW].
  intros x Hx. cbn in Hx. destruct Hx as (H1 & H2 & _). apply HA; lia_std.
Qed.

Lemma mpost_mpostL1 : forall segs M M' lo hi,
  mpost segs M M' lo hi 0 0 -> mpostL segs M M' [(lo, hi - lo)].
Proof.
  intros segs M M' lo hi [HA HW]. split; [| exact HW].
  intros x Hx. cbn in Hx. destruct Hx as (H1 & _). apply HA; lia_std.
Qed.

Section WithSegs.
Variable segs : list Segment.

Definition i_cst (cx : ictx) (M : mem) : Prop :=
  let u := c_u cx in let p := c_p cx in
  mem_u64 segs M (u + 56) p /\ mem_u64 segs M (u + 80) 0 /\
  mem_u64 segs M p (u) /\ mem_u32 segs M (p + 16) 5 /\ mem_u64 segs M (p + 56) 0 /\
  mem_u32 segs M (p + 68) 15 /\ mem_u32 segs M (p + 72) (wsz cx) /\ mem_u64 segs M (p + 88) (c_w cx) /\
  mem_u32 segs M (p + 7160) 1.

Definition i_cst_ok (cx : ictx) (a k : Z) : Prop :=
  let u := c_u cx in let p := c_p cx in
  (a + k <= u + 56 \/ u + 88 <= a) /\
  (a + k <= p \/ (p + 8 <= a /\ a + k <= p + 16) \/ (p + 24 <= a /\ a + k <= p + 56) \/
   (p + 76 <= a /\ a + k <= p + 88) \/ (p + 96 <= a /\ a + k <= p + 7160) \/ p + 7164 <= a).

Lemma i_cst_frame : forall cx M a bs,
  i_cst cx M -> 0 <= c_u cx -> c_u cx + 208 <= two64 -> 0 <= c_p cx -> c_p cx + STATE_SIZE <= two64 ->
  0 <= a -> 0 < Z.of_nat (length bs) -> a + Z.of_nat (length bs) <= two64 ->
  i_cst_ok cx a (Z.of_nat (length bs)) ->
  i_cst cx (wbytes M (w64 a) bs).
Proof.
  intros cx M a bs H Hu1 Hu2 Hp1 Hp2 Ha1 Hl Ha2 [D1 D2]. unfold i_cst, STATE_SIZE in *.
  destruct H as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9).
  repeat split; ((apply mem_u64_frame || apply mem_u32_frame); [assumption | unfold zdisj; lia_std]).
Qed.

Lemma i_cst_magreeL : forall cx M0 M rs,
  magreeL M0 M rs -> i_cst cx M0 ->
  0 <= c_u cx -> c_u cx + 208 <= two64 -> 0 <= c_p cx -> c_p cx + STATE_SIZE <= two64 ->
  disj_all (c_u cx + 56) 32 rs -> disj_all (c_p cx) 8 rs -> disj_all (c_p cx + 16) 4 rs ->
  disj_all (c_p cx + 56) 20 rs -> disj_all (c_p cx + 88) 8 rs -> disj_all (c_p cx + 7160) 4 rs ->
  i_cst cx M.
Proof.
  intros cx M0 M rs HA H Hu1 Hu2 Hp1 Hp2 D1 D2 D3 D4 D5 D6. unfold i_cst in *. unfold STATE_SIZE in *.
  destruct H as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9).
  repeat split;
    ((eapply mem_u64_magreeL || eapply mem_u32_magreeL);
    [ exact HA | eassumption | lia_std | lia_std
    | first [ solve [eapply (disj_all_sub rs); [exact D1 | lia_std | lia_std]]
            | solve [eapply (disj_all_sub rs); [exact D2 | lia_std | lia_std]]
            | solve [eapply (disj_all_sub rs); [exact D3 | lia_std | lia_std]]
            | solve [eapply (disj_all_sub rs); [exact D4 | lia_std | lia_std]]
            | solve [eapply (disj_all_sub rs); [exact D5 | lia_std | lia_std]]
            | solve [eapply (disj_all_sub rs); [exact D6 | lia_std | lia_std]] ] ]).
Qed.

Definition st_rest (cx : ictx) (st : ist) (M : mem) : Prop :=
  let p := c_p cx in
  mem_u32 segs M (p + 12) (t_last st) /\ mem_u32 segs M (p + 28) (t_flags st) /\
  mem_u32 segs M (p + 76) (t_whave st) /\ mem_u32 segs M (p + 80) (t_wnext st) /\
  mem_u32 segs M (p + 108) (t_length st) /\ mem_u32 segs M (p + 112) (t_offset st) /\ mem_u32 segs M (p + 116) (t_extra st) /\
  mem_u64 segs M (p + 120) (cp_addr cx (t_lc st)) /\ mem_u64 segs M (p + 128) (cp_addr cx (t_dc st)) /\
  mem_u32 segs M (p + 136) (t_lb st) /\ mem_u32 segs M (p + 140) (t_db st) /\
  mem_u32 segs M (p + 144) (t_ncode st) /\ mem_u32 segs M (p + 148) (t_nlen st) /\ mem_u32 segs M (p + 152) (t_ndist st) /\
  mem_u32 segs M (p + 156) (t_shave st) /\ mem_u64 segs M (p + 160) (p + 1384 + 4 * t_nx st).
Definition st_at (cx : ictx) (st : ist) (M : mem) : Prop :=
  mem_u32 segs M (c_p cx + 8) (t_mode st) /\ st_rest cx st M.

Lemma st_at_magreeL : forall cx st M0 M rs,
  magreeL M0 M rs -> st_at cx st M0 -> 0 <= c_p cx -> c_p cx + STATE_SIZE <= two64 ->
  disj_all (c_p cx + 8) 160 rs -> st_at cx st M.
Proof.
  intros cx st M0 M rs HA H Hp1 Hp2 D. unfold st_at, st_rest in *. unfold STATE_SIZE in *.
  destruct H as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9 & A10 & A11 & A12 & A13 & A14 & A15 & A16 & A17).
  repeat split;
    ((eapply mem_u64_magreeL || eapply mem_u32_magreeL);
    [ exact HA | eassumption | lia_std | lia_std | eapply (disj_all_sub rs); [exact D | lia_std | lia_std] ]).
Qed.

Lemma st_rest_frame : forall cx st M a bs,
  st_rest cx st M -> 0 <= c_p cx -> c_p cx + STATE_SIZE <= two64 -> 0 <= a -> 0 < Z.of_nat (length bs) -> a + Z.of_nat (length bs) <= two64 ->
  (a + Z.of_nat (length bs) <= c_p cx + 12 \/ c_p cx + 168 <= a) ->
  st_rest cx st (wbytes M (w64 a) bs).
Proof.
  intros cx st M a bs H Hp1 Hp2 Ha1 Hl Ha2 D. unfold st_rest, STATE_SIZE in *.
  destruct H as (A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9 & A10 & A11 & A12 & A13 & A14 & A15 & A16 & A17).
  repeat split; ((apply mem_u64_frame || apply mem_u32_frame); [assumption | unfold zdisj; lia_std]).
Qed.
Lemma st_rest_magreeL : forall cx st M0 M rs,
  magreeL M0 M rs -> st_rest cx st M0 -> 0 <= c_p cx -> c_p cx + STATE_SIZE <= two64 ->
  disj_all (c_p cx + 12) 156 rs -> st_rest cx st M.
Proof.
  intros cx st M0 M rs HA H Hp1 Hp2 D. unfold st_rest in *. unfold STATE_SIZE in *.
  destruct H as (A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9 & A10 & A11 & A12 & A13 & A14 & A15 & A16 & A17).
  repeat split;
    ((eapply mem_u64_magreeL || eapply mem_u32_magreeL);
    [ exact HA | eassumption | lia_std | lia_std | eapply (disj_all_sub rs); [exact D | lia_std | lia_std] ]).
Qed.

Lemma st_at_frame : forall cx st M a bs,
  st_at cx st M -> 0 <= c_p cx -> c_p cx + STATE_SIZE <= two64 -> 0 <= a -> 0 < Z.of_nat (length bs) -> a + Z.of_nat (length bs) <= two64 ->
  (a + Z.of_nat (length bs) <= c_p cx + 8 \/ c_p cx + 168 <= a) ->
  st_at cx st (wbytes M (w64 a) bs).
Proof.
  intros cx st M a bs H Hp1 Hp2 Ha1 Hl Ha2 D. unfold st_at, st_rest, STATE_SIZE in *.
  destruct H as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9 & A10 & A11 & A12 & A13 & A14 & A15 & A16 & A17).
  repeat split; ((apply mem_u64_frame || apply mem_u32_frame); [assumption | unfold zdisj; lia_std]).
Qed.

Definition strm_at (cx : ictx) (st : ist) (M : mem) : Prop :=
  let u := c_u cx in let p := c_p cx in
  mem_u64 segs M (u) (c_q cx + t_cin st) /\ mem_u32 segs M (u + 8) (c_n cx - t_cin st) /\
  mem_u64 segs M (u + 24) (c_ob cx + t_cout st) /\ mem_u32 segs M (u + 32) (c_osz cx - t_cout st) /\
  mem_u64 segs M (p + 96) (t_hold st) /\ mem_u32 segs M (p + 104) (t_bits st).

Lemma strm_at_magreeL : forall cx st M0 M rs,
  magreeL M0 M rs -> strm_at cx st M0 ->
  0 <= c_u cx -> c_u cx + 208 <= two64 -> 0 <= c_p cx -> c_p cx + STATE_SIZE <= two64 ->
  disj_all (c_u cx) 40 rs -> disj_all (c_p cx + 96) 12 rs -> strm_at cx st M.
Proof.
  intros cx st M0 M rs HA H Hu1 Hu2 Hp1 Hp2 D1 D2. unfold strm_at in *. unfold STATE_SIZE in *.
  destruct H as (A1 & A2 & A3 & A4 & A5 & A6).
  repeat split;
    ((eapply mem_u64_magreeL || eapply mem_u32_magreeL);
    [ exact HA | eassumption | lia_std | lia_std
    | first [ solve [eapply (disj_all_sub rs); [exact D1 | lia_std | lia_std]]
            | solve [eapply (disj_all_sub rs); [exact D2 | lia_std | lia_std]] ] ]).
Qed.

Lemma strm_at_frame : forall cx st M a bs,
  strm_at cx st M -> 0 <= c_u cx -> c_u cx + 208 <= two64 -> 0 <= c_p cx -> c_p cx + STATE_SIZE <= two64 ->
  0 <= a -> 0 < Z.of_nat (length bs) -> a + Z.of_nat (length bs) <= two64 ->
  (a + Z.of_nat (length bs) <= c_u cx + 0 \/ c_u cx + 40 <= a) ->
  (a + Z.of_nat (length bs) <= c_p cx + 96 \/ c_p cx + 108 <= a) ->
  strm_at cx st (wbytes M (w64 a) bs).
Proof.
  intros cx st M a bs H Hu1 Hu2 Hp1 Hp2 Ha1 Hl Ha2 D1 D2. unfold strm_at, STATE_SIZE in *.
  destruct H as (A1 & A2 & A3 & A4 & A5 & A6).
  repeat split; ((apply mem_u64_frame || apply mem_u32_frame); [assumption | unfold zdisj; lia_std]).
Qed.
End WithSegs.

End FXG.
Ltac icx_cbn := cbn [c_u c_p c_q c_n c_ob c_osz c_w c_cin0 c_cout0 c_W0 c_K c_zc
                     t_mode t_last t_flags t_cin t_cout t_hold t_bits t_out t_ret t_length t_offset t_extra
                     t_lc t_dc t_lb t_db t_ncode t_nlen t_ndist t_shave t_nx t_whave t_wnext] in *.
