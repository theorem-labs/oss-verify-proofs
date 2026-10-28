(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.Lib Require Import SFModel Arr.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.Spec Require Import Prelim StrFun ScanInt.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.Lib Require Import SFW1_lemmas.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.U0.P0 Require Import Segs F_memcpy F_memchr Printf_lib.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.U0.P0 Require Export F_shgetc_A.
Import ListNotations.
Open Scope Z_scope.
Open Scope bv_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Definition rtext (T : Z) (txt pre post : list Z) : Prop :=
  txt = pre ++ 0%Z :: post /\ Forall (fun c => 0 < c < 256)%Z pre /\ Forall (fun c => 0 <= c < 256)%Z txt /\
  ((- (T + zlength pre + 1)) mod 8 <= zlength post)%Z /\ (zlength txt <= 2^40)%Z.

Definition win (p co : Z) : Z := if (p - co <? 257)%Z then p else (co + 257)%Z.
Lemma win_range : forall p co, (0 <= co <= p)%Z -> (co <= win p co <= p /\ (co < p -> co < win p co) /\ win p co <= co + 257)%Z.
Proof. intros p co H. unfold win. destruct (Z.ltb_spec0 (p - co) 257); lia. Qed.

Lemma nonul_pos : forall l, Forall (fun c => 0 < c < 256)%Z l -> ~ In (Z_to_bv 8 0) (zbytes l).
Proof.
  intros l H IN. unfold zbytes in IN. apply in_map_iff in IN. destruct IN as [c [E INc]].
  pose proof (proj1 (Forall_forall _ _) H c INc) as X. cbv beta in X.
  pose proof (f_equal bv_unsigned E) as E2. rewrite !unsigned_lit8 in E2 by lia. lia.
Qed.
Lemma Forall_skipn' : forall {A} (P : A -> Prop) k l, Forall P l -> Forall P (skipn k l).
Proof. intros A P k l H. rewrite <- (firstn_skipn k l) in H. apply Forall_app in H. LiaTuning.ctauto. Qed.
Lemma skipn_hd : forall (l : list byte) k b, nth_error l k = Some b -> skipn k l = b :: skipn (S k) l.
Proof.
  induction l as [|x l IH]; intros k b H; [destruct k; discriminate H|].
  destruct k as [|k]; cbn in H |- *; [injection H as ->; reflexivity|]. exact (IH k b H).
Qed.
Lemma hd_eq : forall (l : list byte) b, nth_error l 0 = Some b -> l = b :: skipn 1 l.
Proof. intros [|x l] b H; [discriminate H|]. cbn in H |- *. injection H as ->. reflexivity. Qed.
Lemma rw_cells_CB1 : forall m A bs, rw_cells rsegs m A [CB 1 bs] -> exists b, rw_cells rsegs m A [CB 1 [b]].
Proof.
  intros m A bs H. pose proof H as H'. destruct H as [[[W _] _] _]. cbn in W.
  destruct bs as [|b [|]]; try discriminate W. exists b. exact H'.
Qed.
Lemma rw_cells_CB0 : forall m A cs, rw_cells rsegs m A cs -> rw_cells rsegs m A (CB 0 [] :: cs).
Proof. intros m A cs [[W B] R]. split; [split|]; [split; [reflexivity | exact W] | exact B | exact R]. Qed.
Lemma rw_cells_unCB0 : forall m A cs, rw_cells rsegs m A (CB 0 [] :: cs) -> rw_cells rsegs m A cs.
Proof. intros m A cs [[[_ W] B] R]. split; [split|]; [exact W | exact B | exact R]. Qed.

Definition sread_len (off p : Z) : Z := if (off <? p)%Z then 1 else 0.

Definition memchr_postv (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (A C N : Z) (buf : list byte) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1' a2' a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (memchr_res A C N buf)) a1' a2' a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom rsegs)
    /\ munch [] m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
    /\ bytes_at rsegs m' A buf.
Lemma memchr_callv : forall ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (A C N : Z) (buf : list byte),
  bytes_at rsegs m A buf -> memchr_ok A C N buf -> (0 <= C < 256)%Z -> (0 <= N < 2^64)%Z -> (A < 2^64)%Z -> mem_inv rsegs m ->
  evt rsegs (memchr_postv ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc A C N buf m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 A) (Z_to_bv 64 C) (Z_to_bv 64 N) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x23fe4) fc None m (seg_rom rsegs)).
Proof.
  intros until buf. intros BA OK HC HN HA MI. pose proof (bytes_at_bound _ _ _ _ BA) as B.
  assert (EA : bv_unsigned (Z_to_bv 64 A) = A) by (apply unsigned_lit; lia).
  assert (EC : (bv_unsigned (Z_to_bv 64 C) mod 256 = C)%Z) by (rewrite unsigned_lit by lia; apply Z.mod_small; lia).
  assert (EN : bv_unsigned (Z_to_bv 64 N) = N) by (apply unsigned_lit; lia).
  eapply evt_mono. { eapply F_memchr.memchr_spec with (buf := buf); rewrite ?EA, ?EC, ?EN; [exact BA | exact OK | exact MI]. }
  intros ms' P. unfold F_memchr.memchr_post in P. rewrite EA, EC, EN in P. exact P.
Qed.

Definition memcpy_postv (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (Dst Src N : Z) (src : list byte) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1' a2' a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 Dst) a1' a2' a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom rsegs)
    /\ munch [(Dst, Dst + N)]%Z m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
    /\ rw_cells rsegs m' Dst [CB (Z.to_nat N) src]
    /\ bytes_at rsegs m' Src src.
Lemma memcpy_callv : forall ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (Dst Src N : Z) (src junk : list byte),
  bytes_at rsegs m Src src -> length src = Z.to_nat N -> rw_cells rsegs m Dst [CB (Z.to_nat N) junk] ->
  (Src + N <= Dst \/ Dst + N <= Src)%Z -> (0 <= N)%Z -> (Src + N < 2^64)%Z -> (Dst + N < 2^64)%Z -> mem_inv rsegs m ->
  evt rsegs (memcpy_postv ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc Dst Src N src m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 Dst) (Z_to_bv 64 Src) (Z_to_bv 64 N) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x240e0) fc None m (seg_rom rsegs)).
Proof.
  intros until junk. intros BA LEN DC SEP HN HS HD MI.
  pose proof (bytes_at_bound _ _ _ _ BA) as B1. pose proof (rw_cells_bound _ _ _ _ DC) as B2. cbn [cells_size csize] in B2.
  assert (ED : bv_unsigned (Z_to_bv 64 Dst) = Dst) by (apply unsigned_lit; lia).
  assert (ES : bv_unsigned (Z_to_bv 64 Src) = Src) by (apply unsigned_lit; lia).
  assert (EN : bv_unsigned (Z_to_bv 64 N) = N) by (apply unsigned_lit; lia).
  eapply evt_mono. { eapply F_memcpy.memcpy_spec with (src := src) (junk := junk); rewrite ?ED, ?ES, ?EN; [exact BA | exact LEN | exact DC | exact SEP | exact MI]. }
  intros ms' P. unfold F_memcpy.memcpy_post in P. rewrite ED, ES, EN in P. exact P.
Qed.

Definition sread_post (ra : word) (q : Z) (gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (Fp T D p off : Z) (txt : list Z) (dj : byte) (mode : word) (shend : Z) (shl shc : word) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra (Z_to_bv 64 q) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (sread_len off p)) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom rsegs)
    /\ munch [(q - 64, q); (Fp, Fp + 232); (D, D + 1)]%Z m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
    /\ stk rsegs m' (q - 64) (q)
    /\ rw_cells rsegs m' Fp (ss_cells T (T + off + sread_len off p) (T + win p off) mode (T + win p off) shend shl shc)
    /\ rw_cells rsegs m' D [CB 1 [if (off <? p)%Z then Z_to_bv 8 (znth txt off) else dj]]
    /\ bytes_at rsegs m' T (zbytes txt).

Definition sread_stmt : Prop :=
  forall (ra : word) (q : Z) (gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (Fp T D p off rpos rend shend : Z) (txt pre post : list Z) (dj : byte) (mode shl shc : word),
  rw_cells rsegs m Fp (ss_cells T rpos rend mode (T + off) shend shl shc) ->
  rtext T txt pre post -> p = zlength pre -> (0 <= off <= p)%Z ->
  bytes_at rsegs m T (zbytes txt) -> rw_cells rsegs m D [CB 1 [dj]] ->
  (4096 <= T)%Z -> (T + 2^41 <= 2^63)%Z -> (0 <= rpos < 2^64)%Z -> (0 <= rend < 2^64)%Z -> (0 <= shend < 2^64)%Z ->
  (D + 1 <= Fp \/ Fp + 232 <= D)%Z -> (D + 1 <= T \/ T + zlength txt <= D)%Z -> (Fp + 232 <= T \/ T + zlength txt <= Fp)%Z ->
  stk rsegs m (q - 64) (q) -> (4096 <= q)%Z -> (q <= Fp)%Z -> (Fp + 232 <= 2^63)%Z ->
  (q <= D)%Z -> (D + 1 <= 2^63)%Z -> (T + zlength txt <= q - 64 \/ q <= T)%Z ->
  (0 <= q)%Z -> (q < 2^63)%Z ->
  mem_inv rsegs m ->
  evt rsegs (sread_post ra q gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc Fp T D p off txt dj mode shend shl shc m)
    (MS (mkR ra (Z_to_bv 64 q) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 Fp) (Z_to_bv 64 D) (Z_to_bv 64 1) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 STRING_READ) fc None m (seg_rom rsegs)).

Lemma sread_spec : sread_stmt.
Proof.
  unfold sread_stmt. intros until shc. intros FC TXT Hp Hoff BY DC T0 T1 Rrp Rre Rsh SEP1 SEP2 SEP3 ST SPLO SPF SPF2 SPD SPD2 SPT Q0 Q1 MI.
  pose proof (munch_refl [(q - 64, q); (Fp, Fp + 232); (D, D + 1)]%Z m) as MU. pose proof (wmono_refl rsegs m) as WM.
  destruct TXT as (Htxt & NZ & BYT & AL & L40).
  pose proof (rw_cells_bound _ _ _ _ FC) as B. unfold ss_cells, w0 in FC. cbn [cells_size csize Nat.add] in B.
  assert (LTX : length (zbytes txt) = length txt) by apply zbytes_length.
  assert (LT3 : length txt = (length pre + S (length post))%nat) by (rewrite Htxt, length_app; reflexivity).
  pose proof (bytes_at_bound _ _ _ _ BY) as BB. rewrite LTX in BB.
  unfold STRING_READ, M64 in *. unfold zlength in *. pose_word_ranges.
  zs. carve_frame 64%nat ST.
  do 10 zs.

  set (k := Z.to_nat off).
  assert (SPLIT : zbytes txt = firstn k (zbytes pre) ++ (zbytes (skipn k pre) ++ Z_to_bv 8 0 :: zbytes post)).
  { rewrite Htxt, zbytes_app. cbn [zbytes map]. rewrite app_assoc. f_equal. rewrite zbytes_skipn. symmetry. apply firstn_skipn. }
  assert (LK : length (firstn k (zbytes pre)) = k) by (rewrite firstn_length, zbytes_length; lia).
  pose proof BY as BY2. rewrite SPLIT in BY2. apply bytes_at_app in BY2. destruct BY2 as [_ BY2]. rewrite LK in BY2.
  replace (T + Z.of_nat k)%Z with (T + off)%Z in BY2 by lia.
  assert (LSK : length (zbytes (skipn k pre)) = (length pre - k)%nat) by (rewrite zbytes_length, skipn_length; lia).
  zs. zs. zs. zs. zs.
  zs. callw (eapply memchr_callv; [exact BY2 | apply memchr_ok_cstr; [apply nonul_pos; apply Forall_skipn'; exact NZ | rewrite LSK, zbytes_length; clear -AL LT3 Hoff Hp T0; Z.div_mod_to_equations; lia ] | lia | lia | lia | hyp]).
  rewrite memchr_res_cstr in * by (apply nonul_pos; apply Forall_skipn'; exact NZ). rewrite LSK in *.
  clear POST.
  destruct (Z.ltb_spec0 (Z.of_nat (length pre - k)) 257) as [WIN|WIN].
  -
    replace (T + off + Z.of_nat (length pre - k))%Z with (T + p)%Z by lia.
    assert (Ew : win p off = p) by (unfold win; rewrite (proj2 (Z.ltb_lt _ _)) by lia; reflexivity).
    zs. br K0. zs. zs. zs. br K1.
    +
      assert (Eo : off = p) by lia. replace (T + p - (T + off))%Z with 0%Z by lia.
      zs. zs. zs. zs. callw (eapply memcpy_callv with (src := []) (junk := []);
        [ apply (proj1 (proj1 (bytes_at_app rsegs _ (T + off) [] _) BY2)) | reflexivity | apply (proj1 (proj1 (rw_cells_app rsegs _ D [CB 0 []] _) (rw_cells_CB0 _ _ _ DC))) | lia | lia | lia | lia | hyp ]).
      clear PC POST. replace (T + off + 0)%Z with (T + p)%Z by lia.
      do 15 zs.
      release_frame FR ST q.
      apply evt_done. unfold sread_post, sread_len. rewrite Ew. replace (off <? p) with false by (symmetry; apply Z.ltb_ge; lia).
      repeat (lazymatch goal with |- ex _ => eexists end).
      split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact ST|].
      split; [unfold ss_cells, w0; rewrite Z.add_0_r; subst off; hyp|]. split; [hyp | hyp].
    +
      assert (NTH : nth_error (zbytes (skipn k pre)) 0 = Some (Z_to_bv 8 (znth txt off))).
      { rewrite zbytes_skipn, nth_error_skipn, Nat.add_0_r. subst k. rewrite zbytes_nth by (unfold zlength; lia).
        rewrite Htxt, znth_app_l by (unfold zlength; lia). reflexivity. }
      pose proof (hd_eq _ _ NTH) as SK. rewrite SK in BY2. cbn [app] in BY2.
      replace (T + p - (T + off))%Z with (p - off)%Z by lia.
      zs. zs. zs. zs. zs. callw (eapply memcpy_callv with (src := [Z_to_bv 8 (znth txt off)]) (junk := [dj]);
        [ apply (proj1 (proj1 (bytes_at_app rsegs _ (T + off) [_] _) BY2)) | reflexivity | exact DC | lia | lia | lia | lia | hyp ]).
      clear POST.
      do 15 zs.
      replace (T + off + (p - off))%Z with (T + p)%Z in * by lia.
      release_frame FR ST q.
      apply evt_done. unfold sread_post, sread_len. rewrite Ew. replace (off <? p) with true by (symmetry; apply Z.ltb_lt; lia).
      repeat (lazymatch goal with |- ex _ => eexists end).
      split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact ST|].
      split; [unfold ss_cells, w0; hyp|]. split; [hyp | hyp].
  -
    assert (Ew : win p off = (off + 257)%Z) by (unfold win; rewrite (proj2 (Z.ltb_ge _ _)) by lia; reflexivity).
    assert (NTH : nth_error (zbytes (skipn k pre)) 0 = Some (Z_to_bv 8 (znth txt off))).
    { rewrite zbytes_skipn, nth_error_skipn, Nat.add_0_r. subst k. rewrite zbytes_nth by (unfold zlength; lia).
      rewrite Htxt, znth_app_l by (unfold zlength; lia). reflexivity. }
    pose proof (hd_eq _ _ NTH) as SK. rewrite SK in BY2. cbn [app] in BY2.
    zs. br K0. zs. zs. br K1.
    zs. zs. zs. zs. zs. callw (eapply memcpy_callv with (src := [Z_to_bv 8 (znth txt off)]) (junk := [dj]);
      [ apply (proj1 (proj1 (bytes_at_app rsegs _ (T + off) [_] _) BY2)) | reflexivity | exact DC | lia | lia | lia | lia | hyp ]).
    clear POST.
    do 15 zs.
    release_frame FR ST q.
    apply evt_done. unfold sread_post, sread_len. rewrite Ew. replace (off <? p) with true by (symmetry; apply Z.ltb_lt; lia).
    repeat (lazymatch goal with |- ex _ => eexists end).
    split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact ST|].
    split; [unfold ss_cells, w0; hyp_cells|]. split; [hyp | hyp].
Qed.
