(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP MonadX StoreFast.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Malloc Require Import MallocBlocks Malloc_iface.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.MallocU Require Import RMallocRep RMallocTree RMalloc_iface.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Spec Require Import Prelim StrFun STree Malloc Monad Stdio SjModel AtpModel Target Prog.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.U Require Import Layout Exit Printf_wfile Sj_iface Sj_kit Sj_h_kit F_memchr F_memcmp Atp_defs Atp_h_defs.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Lib Require Import Ceiling.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.P Require Import Rnd.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Local Ltac std_lia__ := lia.
Local Ltac lia := first [std_lia__ | try (pose proof alloc_ceiling_range as CEIL_RANGE__); std_lia__].

Definition find_res (l : list Z) : Z := match find_sep l with Some i => Z.of_nat i | None => -1 end.

Definition SEPB : list byte := to_bytes SEP.

Lemma find_signed_small : forall z, 0 <= z < 2^63 -> bv_signed (Z_to_bv 64 z) = z.
Proof. intros z Hz. rewrite zb_signed. rewrite unsigned_lit by lia. replace (z <? 2^63) with true by (symmetry; apply Z.ltb_lt; lia). reflexivity. Qed.

Lemma u8_val : forall c, 0 <= c < 256 -> bv_unsigned (Z_to_bv 8 c) = c.
Proof. intros c H. rewrite Z_to_bv_unsigned. apply bv_wrap_small. change (bv_modulus 8) with 256. lia. Qed.

Lemma nth_error_firstn_lt : forall {A} n (l : list A) t, (t < n)%nat -> nth_error (firstn n l) t = nth_error l t.
Proof.
  induction n as [|n IH]; intros l t Ht; [lia|]. destruct l as [|x l]; [destruct t; reflexivity|].
  destruct t as [|t]; cbn; [reflexivity|]. apply IH. lia.
Qed.

Lemma nth_error_skipn_add : forall {A} j (l : list A) t, nth_error (skipn j l) t = nth_error l (j + t)%nat.
Proof.
  induction j as [|j IH]; intros l t; [reflexivity|]. destruct l as [|x l]; cbn; [destruct t; reflexivity|]. apply IH.
Qed.

Lemma nth_error_to_bytes : forall l t b, nth_error (to_bytes l) t = Some b -> exists c, nth_error l t = Some c /\ b = Z_to_bv 8 c.
Proof.
  unfold to_bytes. induction l as [|c l IH]; intros [|t] b H; cbn in H; try discriminate.
  - injection H as <-. exists c. split; reflexivity.
  - exact (IH t b H).
Qed.

Lemma to_bytes_firstn : forall n l, to_bytes (firstn n l) = firstn n (to_bytes l).
Proof. unfold to_bytes. induction n as [|n IH]; intros [|c l]; cbn; try reflexivity. f_equal. apply IH. Qed.
Lemma to_bytes_skipn : forall n l, to_bytes (skipn n l) = skipn n (to_bytes l).
Proof. unfold to_bytes. induction n as [|n IH]; intros [|c l]; cbn; try reflexivity. apply IH. Qed.

Lemma Forall_nth_error : forall (P : Z -> Prop) l t c, Forall P l -> nth_error l t = Some c -> P c.
Proof.
  intros P l. induction l as [|x l IH]; intros [|t] c HF H; cbn in H; try discriminate; inversion HF; subst.
  - injection H as <-. assumption.
  - eapply IH; eassumption.
Qed.

Lemma to_bytes_inj : forall a b, Forall (fun c => 0 <= c < 256) a -> Forall (fun c => 0 <= c < 256) b -> to_bytes a = to_bytes b -> a = b.
Proof.
  unfold to_bytes. induction a as [|x a IH]; intros [|y b] Fa Fb H; cbn in H; try discriminate; [reflexivity|].
  inversion Fa; inversion Fb; subst.
  pose proof (f_equal (hd (Z_to_bv 8 0)) H) as Hxy. pose proof (f_equal (@tl byte) H) as Hab. cbn [hd tl] in Hxy, Hab.
  f_equal; [| apply IH; assumption].
  apply (f_equal bv_unsigned) in Hxy. rewrite !u8_val in Hxy by assumption. exact Hxy.
Qed.

Lemma Forall_firstn' : forall (P : Z -> Prop) n l, Forall P l -> Forall P (firstn n l).
Proof. intros P n l H. rewrite <- (firstn_skipn n l) in H. apply Forall_app in H. tauto. Qed.
Lemma Forall_skipn' : forall (P : Z -> Prop) n l, Forall P l -> Forall P (skipn n l).
Proof. intros P n l H. rewrite <- (firstn_skipn n l) in H. apply Forall_app in H. tauto. Qed.

Lemma SEP_bytes : Forall (fun c => 0 <= c < 256) SEP.
Proof. unfold SEP. repeat constructor; lia. Qed.

Lemma sep_at_bound : forall l i, sep_at l i -> (i + 4 <= length l)%nat.
Proof.
  intros l i H. unfold sep_at in H. pose proof (f_equal (@length Z) H) as HL. rewrite firstn_length, length_skipn in HL. change (length SEP) with 4%nat in HL. lia.
Qed.

Lemma sep_at_hd : forall l i, sep_at l i -> nth_error l i = Some 10.
Proof.
  intros l i H. unfold sep_at, SEP in H. replace i with (i + 0)%nat by lia. rewrite <- nth_error_skipn_add.
  destruct (skipn i l) as [|c r]; cbn in H; [discriminate|]. injection H as -> _. reflexivity.
Qed.

Lemma find_sep_None_of : forall l j, (forall i, (i < j)%nat -> ~ sep_at l i) -> (length l < j + 4)%nat -> find_sep l = None.
Proof.
  intros l j H Hl. apply (proj2 (find_sep_None l)). intros i Hi. destruct (Nat.lt_ge_cases i j) as [Hij|Hij]; [exact (H i Hij Hi)|].
  apply sep_at_bound in Hi. lia.
Qed.

Lemma find_sep_Some_of : forall l i, sep_at l i -> (forall i', (i' < i)%nat -> ~ sep_at l i') -> find_sep l = Some i.
Proof. intros l i H Hmin. apply (proj2 (find_sep_Some l i)). split; assumption. Qed.

Lemma find_res_range : forall l, -1 <= find_res l /\ find_res l + 4 <= zlength l \/ find_res l = -1.
Proof.
  intros l. unfold find_res, zlength. destruct (find_sep l) as [i|] eqn:E; [| lia].
  pose proof (find_sep_spec _ _ E). lia.
Qed.

Lemma no_sep_before : forall l j n ix,
  (forall t b, (t < ix)%nat -> nth_error (firstn n (skipn j (to_bytes l))) t = Some b -> bv_unsigned b <> 10) -> (ix <= n)%nat ->
  forall i, (j <= i < j + ix)%nat -> ~ sep_at l i.
Proof.
  intros l j n ix H Hix i Hi S. apply sep_at_hd in S.
  apply (H (i - j)%nat (Z_to_bv 8 10)); [lia| | reflexivity].
  rewrite nth_error_firstn_lt by lia. rewrite nth_error_skipn_add. replace (j + (i - j))%nat with i by lia.
  unfold to_bytes. rewrite nth_error_map. rewrite S. reflexivity.
Qed.

Lemma sep_at_of_bytes : forall l i, Forall (fun c => 0 <= c < 256) l -> (i + 4 <= length l)%nat ->
  firstn 4 (skipn i (to_bytes l)) = SEPB <-> sep_at l i.
Proof.
  intros l i HF Hi. unfold SEPB, sep_at. rewrite <- to_bytes_skipn, <- to_bytes_firstn. split.
  - intros H. apply to_bytes_inj; [apply Forall_firstn', Forall_skipn'; exact HF| exact SEP_bytes| exact H].
  - intros ->. reflexivity.
Qed.

Lemma memchr_ok_all : forall A c n buf, n <= Z.of_nat (length buf) -> memchr_ok A c n buf.
Proof. intros A c n buf H. unfold memchr_ok. destruct (find_byte c (firstn (Z.to_nat n) buf)); [left|]; exact H. Qed.

Lemma sel_found : forall P r L, 0 <= P -> 0 <= r < L ->
  Z.lor (Z.land (Z.b2z (0 <? Z.lxor (P + r) (P + L)) + -1) 18446744073709551615) (P + r + - P) = r.
Proof.
  intros P r L HP Hr.
  assert (NZ : Z.lxor (P + r) (P + L) <> 0) by (intros E; apply Z.lxor_eq in E; lia).
  assert (NN : 0 <= Z.lxor (P + r) (P + L)) by (apply Z.lxor_nonneg; lia).
  replace (0 <? Z.lxor (P + r) (P + L)) with true by (symmetry; apply Z.ltb_lt; lia).
  change (Z.land (Z.b2z true + -1) 18446744073709551615) with 0. rewrite Z.lor_0_l. lia.
Qed.
Lemma sel_notfound : forall P L, 0 <= P -> 0 <= L < 18446744073709551616 ->
  Z.lor (Z.land (Z.b2z (0 <? Z.lxor (P + L) (P + L)) + -1) 18446744073709551615) (P + L + - P) = 18446744073709551615.
Proof.
  intros P L HP HL. rewrite Z.lxor_nilpotent. change (Z.land (Z.b2z (0 <? 0) + -1) 18446744073709551615) with 18446744073709551615.
  replace (P + L + - P) with L by lia. destruct (Z.eq_dec L 0) as [->|NZ]; [reflexivity|].
  rewrite Z.lor_comm. change 18446744073709551615 with (Z.ones 64). apply Z.lor_ones_low; [lia|]. apply Z.log2_lt_pow2; lia.
Qed.

Ltac fix_zxb :=
  match goal with |- evt _ _ (MS ?R _ _ _ _ _ _) => match R with context [zxb ?b] =>
    let v := eval vm_compute in (bv_unsigned b) in replace (zxb b) with (Z_to_bv 64 v) by (unfold zxb; f_equal; vm_compute; reflexivity) end end.

Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.

Lemma bytes_at_skipnZ : forall m A (bs : list byte) k, bytes_at usegs m A bs -> 0 <= k <= Z.of_nat (length bs) ->
  bytes_at usegs m (A + k) (skipn (Z.to_nat k) bs).
Proof. intros m A bs k H Hk. replace (A + k) with (A + Z.of_nat (Z.to_nat k)) by lia. apply bytes_at_skipn; [exact H| lia]. Qed.

Definition find_post (ra : word) (q : Z) (gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (lo : Z) (l : list Z) (m : mem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra (Z_to_bv 64 q) gp (Z_to_bv 64 RATP) t0 t1 t2 s0 s1 (Z_to_bv 64 (find_res l)) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom usegs)
    /\ munch [(q - 80, q)] m m' /\ wmono usegs m m' /\ mem_inv usegs m' /\ stk usegs m' lo q.

Lemma lxor_signbit : forall x, 0 <= x < 2^63 -> Z.lxor x 9223372036854775808 = x + 9223372036854775808.
Proof.
  intros x Hx. symmetry. apply Z.add_nocarry_lxor. apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec, Z.bits_0.
  change 9223372036854775808 with (2 ^ 63). rewrite Z.pow2_bits_eqb by lia.
  destruct (Z.eqb_spec 63 i) as [<-|NE]; [| apply Bool.andb_false_r].
  rewrite Bool.andb_true_r. destruct (Z.eq_dec x 0) as [->|NZ]; [apply Z.bits_0|].
  apply Z.bits_above_log2; [lia|]. apply Z.log2_lt_pow2; lia.
Qed.
Lemma slt_xor_eq : forall x y, 0 <= x < 2^63 -> 0 <= y < 2^63 ->
  (Z.lxor x 9223372036854775808 <? Z.lxor y 9223372036854775808) = (x <? y).
Proof.
  intros x y Hx Hy. rewrite !lxor_signbit by lia.
  destruct (Z.ltb_spec x y); destruct (Z.ltb_spec (x + 9223372036854775808) (y + 9223372036854775808)); try reflexivity; lia.
Qed.

Ltac br_no := first [if_false | if_lia].

Section Proofs.

  Variables (ra gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (q lo P : Z) (l : list Z) (m : mem).
  Let L : Z := zlength l.
  Let W : list (Z * Z) := [(q - 80, q)].
  Notation POST := (find_post ra q gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo l m).

  Notation FRAME xra := ([C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 xra] : list cell).

  Hypothesis LBYT : Forall (fun c => 0 <= c < 256) l.
  Hypothesis P0 : 0 < P.
  Hypothesis PL : P + zlength l <= lo.
  Hypothesis LO0 : 0 <= lo.
  Hypothesis LOQ : lo <= q - 80.
  Hypothesis QH : q < 2^63.

  Lemma find_tail : forall (x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 xs2 xs6 xs7 : word) (m1 : mem) (r : Z) (c0 : list byte),
    (find_sep l = None /\ r = L \/ exists i, find_sep l = Some i /\ r = Z.of_nat i) ->
    mem_inv usegs m1 -> munch W m m1 -> wmono usegs m m1 -> stk usegs m1 lo (q + -80) ->
    rw_cells usegs m1 (q + -80) (CB 8 c0 :: FRAME ra) ->
    evt usegs POST
      (MS (mkR x1 (Z_to_bv 64 (q + -80)) gp (Z_to_bv 64 RATP) t0 t1 t2 (Z_to_bv 64 4) (Z_to_bv 64 ATP_SEP) a0 a1 a2 a3 a4 a5 a6 a7
               xs2 (Z_to_bv 64 (P + r)) (Z_to_bv 64 P) (Z_to_bv 64 (P + L)) xs6 xs7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x3e3d8) fc None m1 (seg_rom usegs)).
  Proof.
    intros until c0. intros HR MI MU WM ST FR.
    assert (L0 : 0 <= L) by (unfold L, zlength; lia).
    assert (LH : L < 2^63) by (unfold L in *; lia).
    unfold ATP_SEP.
    destruct HR as [[HN ->]|(i & HS & ->)].
    -
      zstep. zstep. zstep. zstep. zstep. rewrite sel_notfound by lia. step.
      do 9 step. step. release_frame FR ST q. step.
      replace (Z_to_bv 64 18446744073709551615) with (Z_to_bv 64 (find_res l)) by (unfold find_res; rewrite HN; apply bv_eq; vm_compute; reflexivity).
      apply evt_done. unfold find_post. do 14 eexists. eexists.
      split; [cbv delta [mkR]; reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [assumption| exact ST].
    - pose proof (find_sep_spec _ _ HS) as IB. unfold L in *. unfold zlength in *.
      zstep. zstep. zstep. zstep. zstep. rewrite sel_found by lia. step.
      do 9 step. step. release_frame FR ST q. step.
      replace (Z_to_bv 64 (Z.of_nat i)) with (Z_to_bv 64 (find_res l)) by (unfold find_res; rewrite HS; reflexivity).
      apply evt_done. unfold find_post. do 14 eexists. eexists.
      split; [cbv delta [mkR]; reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [assumption| exact ST].
  Qed.

  Lemma find_loop : forall (k : nat) (j : Z) (x1 t0 t1 t2 a1 a3 a4 a5 a6 a7 t3 t4 t5 t6 xs3 : word) (m1 : mem) (c0 : list byte) (af ar : Z),
    af = P + j -> ar = L - j ->
    L - j <= Z.of_nat k -> 0 <= j -> j + 4 <= L -> (forall i, (i < Z.to_nat j)%nat -> ~ sep_at l i) ->
    mem_inv usegs m1 -> munch W m m1 -> wmono usegs m m1 -> stk usegs m1 lo (q + -80) ->
    rw_cells usegs m1 (q + -80) (CB 8 c0 :: FRAME ra) ->
    bytes_at usegs m1 P (to_bytes l) ->
    evt usegs POST
      (MS (mkR x1 (Z_to_bv 64 (q + -80)) gp (Z_to_bv 64 RATP) t0 t1 t2 (Z_to_bv 64 4) (Z_to_bv 64 ATP_SEP) (Z_to_bv 64 af) a1 (Z_to_bv 64 ar) a3 a4 a5 a6 a7
               (Z_to_bv 64 10) xs3 (Z_to_bv 64 P) (Z_to_bv 64 (P + L)) (Z_to_bv 64 1) (Z_to_bv 64 18446744073709551615) s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x3e428) fc None m1 (seg_rom usegs)).
  Proof.
    induction k as [|k IH]; intros until ar; intros -> -> HK J0 J4 INV MI MU WM ST FR PB.
    { exfalso. unfold L, zlength in *. lia. }
    assert (LH : L < 2^63) by (unfold L in *; lia).
    unfold L in *. unfold zlength in *. unfold ATP_SEP in *.
    assert (LBL : length (to_bytes l) = length l) by apply to_bytes_length.

    zstep. zstep.
    rewrite slt_xor_eq by lia.
    match goal with |- context [Z.b2z (?a <? ?b)] => replace (a <? b) with true by (symmetry; apply Z.ltb_lt; lia) end.
    cbn [Z.b2z]. step. br_no.
    zstep. step. if_cases KB; zify_cond KB; rewrite ?find_signed_small in KB by lia; [exfalso; lia|]. clear KB.
    step. if_cases K0; zify_cond K0; [exfalso; lia|]. clear K0. step. step.
    pose proof (bytes_at_skipnZ m1 P (to_bytes l) j PB ltac:(lia)) as PBJ.
    call memchr_spec.
    1:{ rewrite unsigned_lit by lia. exact PBJ. }
    1:{ rewrite !unsigned_lit by lia. apply memchr_ok_all. rewrite length_skipn. lia. }
    1:{ assumption. }
    rewrite !unsigned_lit by lia. change (10 mod 256) with 10. unfold memchr_res.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m2 end.
    lazymatch goal with H : mem_inv usegs m2 |- _ => rename H into MI2 end.
    lazymatch goal with |- context [find_byte 10 (firstn ?nn ?X)] =>
      destruct (find_byte 10 (firstn nn X)) as [ix|] eqn:FB;
      [ pose proof (find_byte_Some _ _ _ FB) as (Hl & (b & Hb & Hb10) & Hmin); rewrite length_firstn, length_skipn in Hl;
        pose proof (no_sep_before l (Z.to_nat j) nn ix Hmin ltac:(lia)) as NOS
      | pose proof (find_byte_None _ _ FB) as Hmin ] end.
    -
      assert (IXR : 0 <= Z.of_nat ix /\ j + Z.of_nat ix + 4 <= Z.of_nat (length l)) by lia.

      step. if_cases K1; zify_cond K1; [exfalso; lia|]. clear K1. step. step. step. step.
      assert (BP4 : bytes_at usegs m2 (P + j + Z.of_nat ix) (firstn 4 (skipn (Z.to_nat (j + Z.of_nat ix)) (to_bytes l)))).
      { apply bytes_at_firstn. replace (P + j + Z.of_nat ix) with (P + (j + Z.of_nat ix)) by lia. apply bytes_at_skipnZ; [assumption| lia]. }
      assert (LEN4 : length (firstn 4 (skipn (Z.to_nat (j + Z.of_nat ix)) (to_bytes l))) = 4%nat) by (rewrite length_firstn, length_skipn; lia).
      assert (SEPRO : bytes_at usegs m2 75341 SEPB).
      { apply ro_bytes_at; [exact MI2| lia| cbn; lia|]. apply ro_bytes_b_sound. vm_compute. reflexivity. }
      eapply evt_cut.
      { eapply bcmp_spec with (bp := firstn 4 (skipn (Z.to_nat (j + Z.of_nat ix)) (to_bytes l))) (bq := SEPB);
          [reflexivity| reflexivity| rewrite LEN4; reflexivity| rewrite LEN4; reflexivity| lia| lia| rewrite LEN4; cbn; lia| rewrite LEN4; cbn; lia
          | exact BP4| exact SEPRO| exact MI2]. }
      cbv beta. intros ms' (rr & ya1 & ya2 & ya3 & ya4 & -> & RIFF).
      replace (ret_pc (Z_to_bv 64 0x3e45c)) with (Z_to_bv 64 0x3e45c) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
      pose proof (sep_at_of_bytes l (Z.to_nat (j + Z.of_nat ix)) LBYT ltac:(lia)) as SIFF.

      step. if_cases K2.
      +
        assert (Er : rr = Z_to_bv 64 0).
        { unfold bv_eqb in K2. apply Z.eqb_eq in K2. apply bv_eq. rewrite K2. reflexivity. }
        apply (proj1 RIFF) in Er. apply (proj1 SIFF) in Er.
        assert (HS : find_sep l = Some (Z.to_nat (j + Z.of_nat ix))).
        { apply find_sep_Some_of; [exact Er|]. intros i' Hi'. destruct (Nat.lt_ge_cases i' (Z.to_nat j)) as [X|X]; [exact (INV i' X)|].
          apply NOS. lia. }
        replace (Z_to_bv 64 (P + j + Z.of_nat ix)) with (Z_to_bv 64 (P + Z.of_nat (Z.to_nat (j + Z.of_nat ix)))) by (f_equal; lia).
        eapply find_tail; [right; eexists; split; [exact HS| reflexivity]| exact MI2| assumption| assumption| assumption| eassumption].
      +
        assert (NE : ~ sep_at l (Z.to_nat (j + Z.of_nat ix))).
        { intros SA. apply (proj2 SIFF) in SA. apply (proj2 RIFF) in SA. rewrite SA in K2. cbn in K2. discriminate. }
        assert (INV' : forall i, (i < Z.to_nat (j + Z.of_nat ix + 1))%nat -> ~ sep_at l i).
        { intros i Hi. destruct (Nat.lt_ge_cases i (Z.to_nat j)) as [X|X]; [exact (INV i X)|].
          destruct (Nat.eq_dec i (Z.to_nat (j + Z.of_nat ix))) as [->|NEQ]; [exact NE|]. apply NOS. lia. }
        step. br_no.

        zstep. zstep. step. if_cases K3; zify_cond K3; rewrite find_signed_small in K3 by lia.
        *
          eapply (IH (j + Z.of_nat ix + 1)); [lia| lia| lia| lia| lia| exact INV'| exact MI2| assumption| assumption| assumption| eassumption| assumption].
        *
          assert (HN : find_sep l = None) by (apply (find_sep_None_of l (Z.to_nat (j + Z.of_nat ix + 1)) INV'); lia).
          step. step.
          eapply find_tail with (r := Z.of_nat (length l));
            [left; split; [exact HN| reflexivity]| exact MI2| assumption| assumption| assumption| eassumption].
    -
      assert (HN : find_sep l = None).
      { apply (find_sep_None_of l (Z.to_nat (Z.of_nat (length l) - 3))); [| lia]. intros i Hi.
        destruct (Nat.lt_ge_cases i (Z.to_nat j)) as [X|X]; [exact (INV i X)|].
        lazymatch type of FB with find_byte 10 (firstn ?nn _) = None =>
          apply (no_sep_before l (Z.to_nat j) nn nn); [intros t b0 Ht Hn; exact (Hmin t b0 Hn)| lia| lia] end. }
      step. if_cases K1; zify_cond K1; [| exfalso; lia]. clear K1. step.
      eapply find_tail with (r := Z.of_nat (length l));
        [left; split; [exact HN| reflexivity]| exact MI2| assumption| assumption| assumption| eassumption].
  Qed.

  Lemma find_spec_s : forall (t0 t1 t2 a4 a5 a6 a7 t3 t4 t5 t6 : word) (X : Z),
    mem_inv usegs m -> stk usegs m lo q -> q <= X -> X + 16 < 2^63 ->
    rw_cells usegs m X [C8 (Z_to_bv 64 P); C8 (Z_to_bv 64 L)] ->
    bytes_at usegs m P (to_bytes l) ->
    evt usegs POST
      (MS (mkR ra (Z_to_bv 64 q) gp (Z_to_bv 64 RATP) t0 t1 t2 s0 s1 (Z_to_bv 64 X) (Z_to_bv 64 ATP_SEP) (Z_to_bv 64 4) (Z_to_bv 64 0) a4 a5 a6 a7
               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 ATP_FIND) fc None m (seg_rom usegs)).
  Proof.
    intros until X. intros MI ST QX XH XC PB.
    assert (LBL : length (to_bytes l) = length l) by apply to_bytes_length.
    assert (L0 : 0 <= L) by (unfold L, zlength; lia). assert (LH : L < 2^63) by (unfold L in *; lia). unfold L in *. unfold zlength in *.
    unfold ATP_FIND, ATP_SEP.
    pose proof (munch_refl W m) as MU. pose proof (wmono_refl usegs m) as WM. unfold W in MU.
    step. carve_frame 80%nat ST.
    apply (rw_cells_split_CB usegs _ _ [] 80 junk [] [8;8;8;8;8;8;8;8;8;8]%nat) in FR; [|reflexivity]. cbn [mk_CB_cells app] in FR.

    do 9 step.

    step. step. step. if_cases K0; zify_cond K0; [| exfalso; rewrite ?unsigned_lit in K0 by lia; lia]. clear K0.

    step. if_false. step. zstep. step. br_no.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m1 end.

    step. zstep. zstep.
    replace (0 <? P) with true by (symmetry; apply Z.ltb_lt; lia).
    first [ replace (P <? 1) with false by (symmetry; apply Z.ltb_ge; lia)
          | replace (P + 0 <? 1) with false by (symmetry; apply Z.ltb_ge; lia)
          | replace (0 + P <? 1) with false by (symmetry; apply Z.ltb_ge; lia) ].
    cbn [Z.b2z Z.lxor Pos.lxor]. zstep. step. if_false.

    zstep. step. br_no. zstep.
    first [ replace (P + Z.of_nat (length l) <? 1) with false by (symmetry; apply Z.ltb_ge; lia)
          | replace (Z.of_nat (length l) + P <? 1) with false by (symmetry; apply Z.ltb_ge; lia) ].
    cbn [Z.b2z Z.lxor Pos.lxor]. zstep. step. if_false.

    zstep. zstep. step. if_false.

    zstep. try replace (Z.of_nat (length l) - 0) with (Z.of_nat (length l)) by lia.
    step. if_cases K1; zify_cond K1; rewrite find_signed_small in K1 by lia.
    -
      step. fix_zxb. zstep.
      match goal with |- context [Z.b2z ?c] => let v := eval vm_compute in (Z.b2z c) in change (Z.b2z c) with v end.
      step.
      eapply evt_eq; [| eapply (find_loop (S (length l)) 0)];
        [atp_st_eq| lia| lia| lia| lia| lia| intros i Hi; lia| assumption| exact MU| exact WM| exact ST| eassumption| assumption].
    -
      assert (HN : find_sep l = None) by (apply (find_sep_None_of l 0); [intros i Hi; lia| lia]).
      step.
      eapply find_tail with (r := Z.of_nat (length l));
        [left; split; [exact HN| reflexivity]| assumption| exact MU| exact WM| exact ST| eassumption].
  Qed.
End Proofs.

Lemma find_spec : forall (ra gp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem) (q lo P X : Z) (l : list Z),
  mem_inv usegs m -> stk usegs m lo q -> 0 <= lo -> lo <= q - 80 -> q < 2^63 -> q <= X -> X + 16 < 2^63 ->
  rw_cells usegs m X [C8 (Z_to_bv 64 P); C8 (Z_to_bv 64 (zlength l))] ->
  bytes_at usegs m P (to_bytes l) -> Forall (fun c => 0 <= c < 256) l -> 0 < P -> P + zlength l <= lo ->
  evt usegs (find_post ra q gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo l m)
    (MS (mkR ra (Z_to_bv 64 q) gp (Z_to_bv 64 RATP) t0 t1 t2 s0 s1 (Z_to_bv 64 X) (Z_to_bv 64 ATP_SEP) (Z_to_bv 64 4) (Z_to_bv 64 0) a4 a5 a6 a7
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 ATP_FIND) fc None m (seg_rom usegs)).
Proof.
  intros until l. intros MI ST LO0 LOQ QH QX XH XC PB LBYT P0 PL.
  eapply find_spec_s; eassumption.
Qed.

End WithCeiling0.
