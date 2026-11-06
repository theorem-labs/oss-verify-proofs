(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Lib Require Import Tac Arr Bytes ZBridge Image.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Spec Require Import Prelim HarnessM.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Plain Require Import PImg.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Lib Require Import LiaTier0U StoreFast.
Local Ltac Stdlib.micromega.Lia.lia ::= lia_tier0u.
Local Ltac OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Lib.StoreFast.tlia ::= tlia_u.
Local Ltac OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Lib.StoreFast.lia3 ::= lia3_u.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
(* [comment removed for export] *)
Definition boxed (P : Prop) : Prop := P.
Ltac box1 H := lazymatch type of H with ?P => change P with (boxed P) in H end.

Definition PMINIFY : Z := 0x3ecb4.
Definition PJT : Z := 0x17df0.          (* [comment removed for export] *)

(* [comment removed for export] *)
Definition JT : list byte := Eval vm_compute in (match image_bytes psegs PJT 768 with Some bs => bs | None => [] end).
Lemma JT_length : length JT = 768%nat. Proof. vm_compute. reflexivity. Qed.
Lemma JT_ro : ro_bytes_b psegs PJT JT = true. Proof. vm_compute. reflexivity. Qed.
Lemma JT_bytes : forall m, mem_inv psegs m -> bytes_at psegs m PJT JT.
Proof. intros m MI. apply (ro_bytes_at psegs m); [exact MI| unfold PJT; lia| rewrite JT_length; unfold PJT; cbn; lia| apply ro_bytes_b_sound; exact JT_ro]. Qed.

(* [comment removed for export] *)
Definition jtb (k : Z) : byte := nth (Z.to_nat k) JT (Z_to_bv 8 0).
Definition jt (k : Z) : Z := bv_unsigned (jtb k).
Definition col0 (c : Z) : Z := jt (3 * c).
Definition col1 (c : Z) : Z := jt (3 * c + 1).
Definition col2 (c : Z) : Z := jt (3 * c + 2).

Lemma forallb_range : forall (P : Z -> bool) n, forallb P (map Z.of_nat (seq 0 n)) = true -> forall c, 0 <= c < Z.of_nat n -> P c = true.
Proof.
  intros P n H c Hc. rewrite forallb_forall in H. apply H. apply in_map_iff. exists (Z.to_nat c). split; [lia|]. apply in_seq. lia.
Qed.
Lemma col0_spec : forall c, 0 <= c < 256 -> col0 c = (if c =? 34 then 1 else 0).
Proof.
  intros c Hc. apply Z.eqb_eq.
  exact (forallb_range (fun c => col0 c =? (if c =? 34 then 1 else 0)) 256 ltac:(vm_compute; reflexivity) c Hc).
Qed.
Lemma col1_spec : forall c, 0 <= c < 256 -> col1 c = (if c =? 92 then 0 else 1).
Proof.
  intros c Hc. apply Z.eqb_eq.
  exact (forallb_range (fun c => col1 c =? (if c =? 92 then 0 else 1)) 256 ltac:(vm_compute; reflexivity) c Hc).
Qed.
Lemma col2_spec : forall c, 0 <= c < 256 -> 0 <= col2 c <= 1.
Proof.
  intros c Hc.
  pose proof (forallb_range (fun c => (0 <=? col2 c) && (col2 c <=? 1))%bool 256 ltac:(vm_compute; reflexivity) c Hc) as H.
  apply andb_true_iff in H. destruct H as [H1 H2]. apply Z.leb_le in H1. apply Z.leb_le in H2. lia.
Qed.

Lemma cols_range : forall c, 0 <= c < 256 -> 0 <= col0 c <= 1 /\ 0 <= col1 c <= 1 /\ 0 <= col2 c <= 1.
Proof. intros c Hc. rewrite col0_spec, col1_spec by lia. pose proof (col2_spec c Hc). destruct (c =? 34), (c =? 92); lia. Qed.

(* [comment removed for export] *)
Lemma jt_read : forall m k a, mem_inv psegs m -> 0 <= k < 768 -> a = wa (PJT + k) ->
  ov_read_bytes psegs m a 1 = Some [jtb k].
Proof.
  intros m k a MI Hk ->. unfold jtb. eapply (u8ro_read psegs m PJT JT k); [exact (JT_bytes m MI)| | lia| reflexivity].
  apply nth_error_nth'. rewrite JT_length. lia.
Qed.

(* [comment removed for export] *)
Lemma byte_range : forall b : byte, 0 <= bv_unsigned b < 256.
Proof. intros b. pose proof (bv_unsigned_in_range 8 b) as H. unfold bv_modulus in H. cbn in H. lia. Qed.
Lemma jt_rd0 : forall m (b : byte), mem_inv psegs m ->
  ov_read_bytes psegs m (Z_to_bv 64 (97776 + bv_unsigned b + Z.shiftl (bv_unsigned b) 1)) 1 = Some [jtb (3 * bv_unsigned b)].
Proof.
  intros m b MI. pose proof (byte_range b). apply (jt_read m _ _ MI); [lia|]. unfold wa, PJT. f_equal. rewrite Z.shiftl_mul_pow2 by lia. lia.
Qed.
Lemma jt_rd1 : forall m (b : byte), mem_inv psegs m ->
  ov_read_bytes psegs m (Z_to_bv 64 (97776 + bv_unsigned b + Z.shiftl (bv_unsigned b) 1 + 1)) 1 = Some [jtb (3 * bv_unsigned b + 1)].
Proof.
  intros m b MI. pose proof (byte_range b). apply (jt_read m _ _ MI); [lia|]. unfold wa, PJT. f_equal. rewrite Z.shiftl_mul_pow2 by lia. lia.
Qed.
Lemma jt_rd2 : forall m (b : byte), mem_inv psegs m ->
  ov_read_bytes psegs m (Z_to_bv 64 (97776 + bv_unsigned b + Z.shiftl (bv_unsigned b) 1 + 2)) 1 = Some [jtb (3 * bv_unsigned b + 2)].
Proof.
  intros m b MI. pose proof (byte_range b). apply (jt_read m _ _ MI); [lia|]. unfold wa, PJT. f_equal. rewrite Z.shiftl_mul_pow2 by lia. lia.
Qed.

(* [comment removed for export] *)
Definition mstate (pre : list Z) : bool * bool := fold_left minify_step pre (true, false).
Definition qz (pre : list Z) : Z := if snd (mstate pre) then 1 else 0.

Lemma mstate_app1 : forall pre c, mstate (pre ++ [c]) = minify_step (mstate pre) c.
Proof. intros. unfold mstate. rewrite fold_left_app. reflexivity. Qed.

(* [comment removed for export] *)
Lemma forallb_range2 : forall (P : Z -> Z -> bool) n1 n2,
  forallb (fun x => forallb (P x) (map Z.of_nat (seq 0 n2))) (map Z.of_nat (seq 0 n1)) = true ->
  forall x y, 0 <= x < Z.of_nat n1 -> 0 <= y < Z.of_nat n2 -> P x y = true.
Proof.
  intros P n1 n2 H x y Hx Hy. exact (forallb_range (P x) n2 (forallb_range _ n1 H x Hx) y Hy).
Qed.
Lemma lxor_255 : forall x, 0 <= x < 256 -> Z.lxor x 255 = 255 - x.
Proof. intros x Hx. apply Z.eqb_eq. exact (forallb_range (fun x => Z.lxor x 255 =? 255 - x) 256 ltac:(vm_compute; reflexivity) x Hx). Qed.
Lemma odd_255_sub : forall x, 0 <= x < 256 -> Z.odd (255 - x) = negb (Z.odd x).
Proof. intros x Hx. apply Bool.eqb_prop. exact (forallb_range (fun x => Bool.eqb (Z.odd (255 - x)) (negb (Z.odd x))) 256 ltac:(vm_compute; reflexivity) x Hx). Qed.
Lemma land_bit : forall x c, 0 <= x < 256 -> 0 <= c <= 1 -> Z.land x c = (if c =? 1 then (if Z.odd x then 1 else 0) else 0).
Proof.
  intros x c Hx Hc. apply Z.eqb_eq.
  exact (forallb_range2 (fun x c => Z.land x c =? (if c =? 1 then (if Z.odd x then 1 else 0) else 0)) 256 2 ltac:(vm_compute; reflexivity) x c Hx ltac:(lia)).
Qed.
Lemma lor_bit : forall x c, 0 <= x < 256 -> 0 <= c <= 1 -> 0 <= Z.lor x c < 256 /\ Z.odd (Z.lor x c) = (Z.odd x || (c =? 1))%bool.
Proof.
  intros x c Hx Hc.
  pose proof (forallb_range2 (fun x c => (0 <=? Z.lor x c) && (Z.lor x c <? 256) && Bool.eqb (Z.odd (Z.lor x c)) (Z.odd x || (c =? 1)))%bool 256 2
                ltac:(vm_compute; reflexivity) x c Hx ltac:(lia)) as H.
  apply andb_true_iff in H. destruct H as [H E]. apply andb_true_iff in H. destruct H as [H1 H2].
  apply Z.leb_le in H1. apply Z.ltb_lt in H2. apply Bool.eqb_prop in E. split; [lia| exact E].
Qed.
Lemma lxor_bits : forall x y, 0 <= x <= 1 -> 0 <= y <= 1 -> Z.lxor x y = (if x =? y then 0 else 1).
Proof.
  intros x y Hx Hy. apply Z.eqb_eq. exact (forallb_range2 (fun x y => Z.lxor x y =? (if x =? y then 0 else 1)) 2 2 ltac:(vm_compute; reflexivity) x y ltac:(lia) ltac:(lia)).
Qed.
Lemma lor_bits : forall x y, 0 <= x <= 1 -> 0 <= y <= 1 -> Z.lor x y = (if (x =? 1) || (y =? 1) then 1 else 0)%bool.
Proof.
  intros x y Hx Hy. apply Z.eqb_eq. exact (forallb_range2 (fun x y => Z.lor x y =? (if (x =? 1) || (y =? 1) then 1 else 0)%bool) 2 2 ltac:(vm_compute; reflexivity) x y ltac:(lia) ltac:(lia)).
Qed.

(* [comment removed for export] *)
Lemma step_regs : forall (pre : list Z) (c ne q : Z),
  0 <= c < 256 -> 0 <= ne < 256 -> Z.odd ne = fst (mstate pre) -> q = qz pre ->
  let q' := Z.lxor (Z.land ne (col0 c)) q in
  let ne' := Z.lor (Z.lxor ne 255) (col1 c) in
  q' = qz (pre ++ [c]) /\ 0 <= q' <= 1 /\ 0 <= ne' < 256 /\ Z.odd ne' = fst (mstate (pre ++ [c])) /\ 0 <= Z.lor (col2 c) q' <= 1.
Proof.
  intros pre c ne q Hc Hne Hodd Hq. cbv zeta.
  unfold qz in *. rewrite mstate_app1. destruct (mstate pre) as [NE Q]. cbn [fst snd] in *. unfold minify_step.
  rewrite (col0_spec c Hc), (col1_spec c Hc). pose proof (col2_spec c Hc) as C2.
  rewrite (lxor_255 ne Hne).
  assert (HQ : 0 <= q <= 1) by (subst q; destruct Q; lia).
  assert (L1 : Z.land ne (if c =? 34 then 1 else 0) = (if ((c =? 34) && NE)%bool then 1 else 0)).
  { rewrite land_bit by (destruct (c =? 34); lia). rewrite <- Hodd. destruct (c =? 34), NE; reflexivity. }
  rewrite L1.
  assert (X : Z.lxor (if ((c =? 34) && NE)%bool then 1 else 0) q = (if xorb Q ((c =? 34) && NE) then 1 else 0)).
  { rewrite lxor_bits by (destruct ((c =? 34) && NE)%bool; lia). subst q. destruct ((c =? 34) && NE)%bool, Q; reflexivity. }
  rewrite X. split; [reflexivity|]. split; [destruct (xorb _ _); lia|].
  destruct (lor_bit (255 - ne) (if c =? 92 then 0 else 1) ltac:(lia) ltac:(destruct (c =? 92); lia)) as [R O].
  split; [exact R|]. split.
  - rewrite O, odd_255_sub, Hodd by lia. destruct (c =? 92); cbn; rewrite ?orb_true_r, ?orb_false_r; reflexivity.
  - set (q' := if xorb Q ((c =? 34) && NE)%bool then 1 else 0). assert (Hq' : 0 <= q' <= 1) by (subst q'; destruct (xorb _ _); lia).
    rewrite (lor_bits (col2 c) q' C2 Hq'). destruct ((col2 c =? 1) || (q' =? 1))%bool; lia.
Qed.

Lemma firstn_S_nth : forall (l : list Z) i d, (i < length l)%nat -> firstn (S i) l = firstn i l ++ [nth i l d].
Proof.
  induction l as [|x l IHl]; intros i d Hi; cbn in Hi; [lia|].
  destruct i as [|i]; [reflexivity|]. cbn [firstn nth app]. rewrite (IHl i d) by lia. reflexivity.
Qed.
Lemma qz_unclosed : forall pl, qz pl = (if unclosed pl then 1 else 0).
Proof. intros pl. unfold qz, unclosed, mstate. reflexivity. Qed.
(* [comment removed for export] *)
Lemma result_word : forall q, 0 <= q <= 1 ->
  Z_to_bv 64 (Z.land ((Z.b2z (q <? 1) + -1) mod 18446744073709551616) 15) = Z_to_bv 64 (if q =? 1 then 15 else 0).
Proof.
  intros q Hq. assert (E : q = 0 \/ q = 1) by lia. destruct E as [-> | ->]; vm_compute; reflexivity.
Qed.

Section P.
  Variables (ra sp gp tp t0 t1 t2 s0 s1 a0 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (D B R : Z) (pl : list Z) (rv : word).
  Notation n := (zlength pl).
  Notation bs := (map (Z_to_bv 8) pl).
  Hypothesis PLB : Forall (fun c => 0 <= c < 256) pl.
  Hypothesis DLO : 0 <= D.
  Hypothesis BLO : 0 <= B.                               (* [comment removed for export] *)
  Hypothesis NLT : n < 2^26.
  Hypothesis DHI : D + n < 2^47.
  Hypothesis BHI : B + n < 2^47.
  Hypothesis RRNG : 0 <= R /\ R + 8 < 2^64.
  Hypothesis SEP : D + n <= B \/ B + n <= D.              (* [comment removed for export] *)
  Hypothesis SEPR1 : R + 8 <= B \/ B + n <= R.            (* [comment removed for export] *)
  Hypothesis SEPR2 : R + 8 <= D \/ D + n <= R.            (* [comment removed for export] *)
  Hypothesis JTD : PJT + 768 <= D \/ D + n <= PJT.        (* [comment removed for export] *)

  Notation W := [(B, B + n); (R, R + 8)].

  Definition INV (m1 : word -> option byte) : Prop :=
    bytes_at psegs m1 D bs /\ (exists bs1, u8arr psegs m1 B bs1 /\ length bs1 = Z.to_nat n) /\ rw_cells psegs m1 R [C8 rv]
    /\ munch W m m1 /\ wmono psegs m m1 /\ mem_inv psegs m1.

  Definition mf_post : machine_state -> Prop :=
    fun ms' => exists t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m' (pos : Z) (bs1 : list byte),
    ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 (if unclosed pl then 15 else 0)) a1' a2' a3' a4' a5' a6' a7'
                  s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
             F (ret_pc ra) fc None m' (seg_rom psegs)
    /\ munch W m m' /\ wmono psegs m m' /\ mem_inv psegs m'
    /\ 0 <= pos <= n /\ rw_cells psegs m' R [C8 (Z_to_bv 64 pos)]
    /\ u8arr psegs m' B bs1 /\ length bs1 = Z.to_nat n /\ bytes_at psegs m' D bs.

  (* [comment removed for export] *)
  Notation GST pc mm k pos ne q y1 y2 ya7 y3 y4 y5 y6 :=
    (MS (mkR ra sp gp tp (Z_to_bv 64 q) y1 y2 s0 s1 (Z_to_bv 64 97776) (Z_to_bv 64 (D + k)) (Z_to_bv 64 (D + n))
             (Z_to_bv 64 B) (Z_to_bv 64 R) (Z_to_bv 64 pos) (Z_to_bv 64 ne) ya7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 y3 y4 y5 y6)
        F (Z_to_bv 64 pc) fc None mm (seg_rom psegs)).

  (* [comment removed for export] *)
  Lemma payload_rd : forall m1 k, bytes_at psegs m1 D bs -> 0 <= k < n ->
    exists b : byte, ov_read_bytes psegs m1 (Z_to_bv 64 (D + k)) 1 = Some [b] /\ bv_unsigned b = nth (Z.to_nat k) pl 0.
  Proof.
    intros m1 k B1 Hk. unfold zlength in Hk.
    assert (Hn : nth_error bs (Z.to_nat k) = Some (Z_to_bv 8 (nth (Z.to_nat k) pl 0))).
    { rewrite nth_error_map. rewrite (nth_error_nth' pl 0) by lia. reflexivity. }
    exists (Z_to_bv 8 (nth (Z.to_nat k) pl 0)). split.
    - eapply (u8ro_read psegs m1 D bs k); [exact B1| exact Hn| lia| reflexivity].
    - apply Z_to_bv_small. unfold bv_modulus. change (2 ^ Z.of_N 8) with 256.
      rewrite Forall_nth in PLB. apply (PLB (Z.to_nat k) 0). lia.
  Qed.

  Lemma inv_store_ok : forall m1 pos, INV m1 -> 0 <= pos < n -> store_ok psegs m1 (Z_to_bv 64 (B + pos)) 1 = true.
  Proof.
    intros m1 pos (_ & (bs1 & DST & LEN) & _) Hp. eapply (u8arr_store_ok psegs m1 B bs1 pos); [exact DST| rewrite LEN; lia| reflexivity].
  Qed.

  Lemma inv_store : forall m1 pos (v : word), INV m1 -> 0 <= pos < n -> INV (write_to_mem m1 (Z_to_bv 64 (B + pos)) (le1 v)).
  Proof.
    intros m1 pos v (BA1 & (bs1 & DST & LEN) & RC1 & MU & WM & MI) Hp.
    pose proof (bytes_at_bound _ _ _ _ BA1) as DB. rewrite length_map in DB.
    change (le1 v) with [Z_to_bv 8 (bv_unsigned v)]. change (Z_to_bv 64 (B + pos)) with (wa (B + pos)). unfold INV. unfold zlength in *.
    split; [| split; [| split; [| split; [| split]]]].
    - apply bytes_at_write_other; [exact BA1| lia| cbn; lia| rewrite length_map; cbn; lia].
    - exists (upd bs1 (Z.to_nat pos) (Z_to_bv 8 (bv_unsigned v))). split; [| rewrite upd_length; exact LEN].
      apply (u8arr_write psegs m1 B bs1 pos); [exact DST| rewrite LEN; lia].
    - apply rw_cells_frame; [exact RC1| lia| cbn; lia| cbn; lia].
    - apply munch_write; [exact MU| lia| cbn; lia| cbn; left; lia].
    - apply wmono_write. exact WM.
    - apply mem_inv_store; [exact MI|]. cbn [length]. eapply (u8arr_store_ok psegs m1 B bs1 pos); [exact DST| rewrite LEN; lia| reflexivity].
  Qed.

  (* [comment removed for export] *)
  Lemma inv_exit_ok : forall m1, INV m1 -> store_ok psegs m1 (Z_to_bv 64 R) 8 = true.
  Proof.
    intros m1 (_ & _ & RC1 & _). pose proof (rw_cells_store_ok psegs m1 R [C8 rv] 0 (C8 rv) 8 RC1 eq_refl eq_refl) as H.
    unfold wa in H. rewrite Z.add_0_r in H. exact H.
  Qed.
  Lemma inv_exit : forall m1 (v : word), INV m1 ->
    let m' := write_to_mem m1 (Z_to_bv 64 R) (le8 v) in
    bytes_at psegs m' D bs /\ (exists bs1, u8arr psegs m' B bs1 /\ length bs1 = Z.to_nat n) /\ rw_cells psegs m' R [C8 v]
    /\ munch W m m' /\ wmono psegs m m' /\ mem_inv psegs m'.
  Proof.
    intros m1 v (BA1 & (bs1 & DST & LEN) & RC1 & MU & WM & MI). cbv zeta.
    pose proof (bytes_at_bound _ _ _ _ BA1) as DB. rewrite length_map in DB.
    pose proof (rw_cells_write psegs m1 R [C8 rv] 0 (C8 rv) (C8 v) RC1 eq_refl eq_refl I) as RW. cbn [cell_upd Nat.eqb cbytes] in RW.
    unfold wa in RW. rewrite Z.add_0_r in RW.
    replace (Z_to_bv 64 R) with (wa R) in * by reflexivity. unfold zlength in *. pose proof (length_le8 v) as L8.
    split; [| split; [| split; [exact RW| split; [| split]]]].
    - apply bytes_at_write_other; [exact BA1| lia| rewrite L8; lia| rewrite length_map, L8; lia].
    - exists bs1. split; [| exact LEN]. destruct DST as [DB1 DW1]. split.
      + apply bytes_at_write_other; [exact DB1| lia| rewrite L8; lia| rewrite L8, LEN; lia].
      + apply wr_at_write. exact DW1.
    - apply munch_write; [exact MU| lia| rewrite L8; lia| rewrite L8; cbn; right; left; lia].
    - apply wmono_write. exact WM.
    - apply mem_inv_store; [exact MI|]. rewrite L8. exact (inv_exit_ok m1 (conj BA1 (conj (ex_intro _ bs1 (conj DST LEN)) (conj RC1 (conj MU (conj WM MI)))))).
  Qed.

  Ltac beta_ms := lazymatch goal with |- evt _ _ ?ms => let ms' := eval cbv beta in ms in change ms with ms' end.

  (* [comment removed for export] *)
  Lemma mf_loop : forall fuel k pos ne m1 (y1 y2 ya7 y3 y4 y5 y6 : word),
    Z.of_nat fuel > n - k -> 0 <= k < n -> 0 <= pos <= k -> 0 <= ne < 256 ->
    Z.odd ne = fst (mstate (firstn (Z.to_nat k) pl)) -> INV m1 ->
    evt psegs mf_post (GST 0x3ecd0 m1 k pos ne (qz (firstn (Z.to_nat k) pl)) y1 y2 ya7 y3 y4 y5 y6).
  Proof.
    induction fuel as [|fuel IH]; intros k pos ne m1 y1 y2 ya7 y3 y4 y5 y6 FU Hk Hpos Hne Hodd INV1; [lia|].
    (* [comment removed for export] *)
    box1 SEP. box1 SEPR1. box1 SEPR2. box1 JTD. box1 RRNG.
    pose proof INV1 as (BA1 & (bs1 & DST & LEN) & RC1 & MU & WM & MI).
    assert (PLn : length pl = Z.to_nat n) by (unfold zlength; lia).
    set (pre := firstn (Z.to_nat k) pl) in *.
    assert (Hq : 0 <= qz pre <= 1) by (unfold qz; destruct (snd _); lia).
    destruct (payload_rd m1 k BA1 Hk) as (b & R0 & Hb).
    pose proof (byte_range b) as Rb. destruct (cols_range (bv_unsigned b) Rb) as (C0 & C1 & C2).
    assert (PRE' : firstn (Z.to_nat (k + 1)) pl = pre ++ [bv_unsigned b]).
    { rewrite Hb. replace (Z.to_nat (k + 1)) with (S (Z.to_nat k)) by lia. subst pre. apply firstn_S_nth. lia. }
    destruct (step_regs pre (bv_unsigned b) ne (qz pre) Rb Hne Hodd eq_refl) as (Q1 & Q2 & N1 & N2 & P1).
    zstep. clear R0. beta_ms.                                  (* [comment removed for export] *)
    do 6 zstep.                                                (* [comment removed for export] *)
    pose proof (jt_rd0 m1 b MI) as R1. zstep. clear R1. beta_ms.      (* [comment removed for export] *)
    change (bv_unsigned (jtb (3 * bv_unsigned b))) with (col0 (bv_unsigned b)).
    pose proof (inv_store_ok m1 pos INV1 ltac:(lia)) as ST1. zstep. clear ST1.   (* [comment removed for export] *)
    pose proof (inv_store m1 pos (Z_to_bv 64 (bv_unsigned b)) INV1 ltac:(lia)) as INV2.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => remember mx as m2 eqn:Em2; clear Em2 end.
    clear BA1 DST RC1 MU WM MI INV1. pose proof INV2 as (BA2 & (bs2 & DST2 & LEN2) & RC2 & MU2 & WM2 & MI2).
    pose proof (jt_rd1 m2 b MI2) as R2. zstep. clear R2. beta_ms.     (* [comment removed for export] *)
    change (bv_unsigned (jtb (3 * bv_unsigned b + 1))) with (col1 (bv_unsigned b)).
    pose proof (jt_rd2 m2 b MI2) as R3. zstep. clear R3. beta_ms.     (* [comment removed for export] *)
    change (bv_unsigned (jtb (3 * bv_unsigned b + 2))) with (col2 (bv_unsigned b)).
    do 6 zstep.                                                (* [comment removed for export] *)
    zstep. if_cases K; zify_cond K.
    - (* [comment removed for export] *)
      replace (D + k + 1) with (D + (k + 1)) by lia.
      rewrite Q1 in P1 |- *. rewrite <- PRE'.
      apply IH; [lia| lia| rewrite PRE'; lia| exact N1| rewrite PRE'; exact N2| exact INV2].
    - (* [comment removed for export] *)
      do 4 zstep.
      rewrite (result_word _ Q2). rewrite Q1 in P1 |- *.
      assert (FIN : pre ++ [bv_unsigned b] = pl) by (rewrite <- PRE'; replace (Z.to_nat (k + 1)) with (length pl) by lia; apply firstn_all).
      rewrite FIN in P1 |- *. rewrite qz_unclosed in P1 |- *.
      replace (if (if unclosed pl then 1 else 0) =? 1 then 15 else 0) with (if unclosed pl then 15 else 0) by (destruct (unclosed pl); reflexivity).
      clear RC2. pose proof (inv_exit_ok m2 INV2) as ST2. zstep. clear ST2.      (* [comment removed for export] *)
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (le8 ?v)) _) =>
        destruct (inv_exit m2 v INV2) as (BA3 & (bs3 & DST3 & LEN3) & RC3 & MU3 & WM3 & MI3) end.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => remember mx as m3 eqn:Em3; clear Em3 end.
      zstep.                                                   (* [comment removed for export] *)
      apply evt_done. unfold mf_post.
      do 14 eexists. exists m3, (pos + Z.lor (col2 (bv_unsigned b)) (if unclosed pl then 1 else 0)), bs3.
      split; [reflexivity|]. split; [exact MU3|]. split; [exact WM3|]. split; [exact MI3|]. split; [lia|].
      split; [exact RC3|]. split; [exact DST3|]. split; [exact LEN3| exact BA3].
  Qed.

  (* [comment removed for export] *)
  Lemma mf_body : INV m ->
    evt psegs mf_post
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 (Z_to_bv 64 D) (Z_to_bv 64 n) (Z_to_bv 64 B) (Z_to_bv 64 R) a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 PMINIFY) fc None m (seg_rom psegs)).
  Proof.
    intros INV1. unfold PMINIFY. pose proof INV1 as (BA1 & (bs1 & DST & LEN) & RC1 & MU & WM & MI).
    assert (N0 : 0 <= n) by (unfold zlength; lia).
    zstep. if_cases K0; zify_cond K0.
    - (* [comment removed for export] *)
      zstep.
      clear RC1. pose proof (inv_exit_ok m INV1) as ST2. zstep. clear ST2.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (le8 ?v)) _) =>
        destruct (inv_exit m v INV1) as (BA3 & (bs3 & DST3 & LEN3) & RC3 & MU3 & WM3 & MI3) end.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => remember mx as m3 eqn:Em3; clear Em3 end.
      zstep. apply evt_done. unfold mf_post.
      do 14 eexists. exists m3, 0, bs3.
      assert (U : unclosed pl = false) by (destruct pl; [reflexivity| exfalso; unfold zlength in K0; cbn in K0; lia]).
      rewrite U.
      split; [reflexivity|]. split; [exact MU3|]. split; [exact WM3|]. split; [exact MI3|]. split; [lia|].
      split; [exact RC3|]. split; [exact DST3|]. split; [exact LEN3| exact BA3].
    - do 6 zstep.
      replace (Z_to_bv 64 D) with (Z_to_bv 64 (D + 0)) by (f_equal; lia).
      change (Z_to_bv 64 0) with (Z_to_bv 64 (qz (firstn (Z.to_nat 0) pl))) at 1.
      eapply (mf_loop (S (Z.to_nat n)) 0 0 1); [lia| lia| lia| lia| reflexivity| exact INV1].
  Qed.
End P.

(* [comment removed for export] *)
Definition minify_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (D B R : Z) (pl : list Z) (bs0 : list byte) (rv : word),
    bytes_at psegs m D (map (Z_to_bv 8) pl) -> Forall (fun c => 0 <= c < 256) pl ->
    u8arr psegs m B bs0 -> length bs0 = Z.to_nat (zlength pl) ->
    rw_cells psegs m R [C8 rv] ->
    0 <= D -> 0 <= B -> zlength pl < 2^26 -> D + zlength pl < 2^47 -> B + zlength pl < 2^47 -> 0 <= R /\ R + 8 < 2^64 ->
    (D + zlength pl <= B \/ B + zlength pl <= D) -> (R + 8 <= B \/ B + zlength pl <= R) -> (R + 8 <= D \/ D + zlength pl <= R) ->
    (PJT + 768 <= D \/ D + zlength pl <= PJT) ->
    mem_inv psegs m ->
    a1 = Z_to_bv 64 D -> a2 = Z_to_bv 64 (zlength pl) -> a3 = Z_to_bv 64 B -> a4 = Z_to_bv 64 R ->
    evt psegs (mf_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m D B R pl)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 PMINIFY) fc None m (seg_rom psegs)).

Theorem minify_proof : minify_stmt.
Proof.
  unfold minify_stmt. intros until rv. intros BA PLB DST LEN RC D0 B0 NLT DHI BHI RR SEP SEPR1 SEPR2 JTD MI -> -> -> ->.
  apply (mf_body ra sp gp tp t0 t1 t2 s0 s1 a0 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m D B R pl rv
           PLB D0 B0 NLT DHI BHI RR SEP SEPR1 SEPR2 JTD).
  split; [exact BA|]. split; [exists bs0; split; [exact DST| exact LEN]|]. split; [exact RC|].
  split; [apply munch_refl|]. split; [apply wmono_refl| exact MI].
Qed.
