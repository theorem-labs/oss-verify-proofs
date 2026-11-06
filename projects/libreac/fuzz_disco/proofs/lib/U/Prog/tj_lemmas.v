From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Arr Bytes ZBridge FP Image.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.U Require Import Img0.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.U Require MemNorm.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.U.Prog Require Import printf_facts_c snprintf_c snprintf_stk_c.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require Import disco_box_name_model.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.U.Prog Require Import reac_box_name_c.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.U.Prog Require Import disco_table_c disco_table.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require Import disco_json_text.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.U.Prog Require Import reac_disco_table_json_c.
Import ListNotations.
Open Scope Z_scope.

Definition KDv : Z := 4835703278458516699.

Lemma tj_quot : forall x, 0 <= x < 2^64 -> x * KDv / 2^64 / 2^18 = x / 1000000.
Proof.
  intros x Hx. unfold KDv. rewrite Z.div_div by lia.
  change (2^64 * 2^18) with 4835703278458516698824704.
  pose proof (Z.div_mod x 1000000 ltac:(lia)) as Hd. pose proof (Z.mod_pos_bound x 1000000 ltac:(lia)) as Hm.
  set (q := x / 1000000) in *. set (r := x mod 1000000) in *.
  symmetry. apply Z.div_unique with (r := x * 4835703278458516699 - q * 4835703278458516698824704); [left|ring].
  split; lia.
Qed.

Lemma tj_quot_mach : forall x, 0 <= x < 2^64 ->
  Z.shiftr (bv_unsigned (Z_to_bv 64 (Z.shiftr (x * KDv) 64))) 18 = x / 1000000.
Proof.
  intros x Hx. rewrite !Z.shiftr_div_pow2 by lia.
  assert (B : 0 <= x * KDv / 2^64 < 2^64).
  { unfold KDv. split; [apply Z.div_pos; lia|]. apply Z.div_lt_upper_bound; lia. }
  rewrite unsigned_lit by exact B. apply tj_quot. exact Hx.
Qed.

Lemma dec_aux_pf : forall f x acc, 1 <= x < 10 ^ Z.of_nat f -> dec_aux (S f) x acc = pf_digits f x acc.
Proof.
  induction f as [|f IH]; intros x acc Hx; [cbn in Hx; lia|].
  change (dec_aux (S (S f)) x acc) with (if x =? 0 then acc else dec_aux (S f) (x / 10) ((48 + x mod 10) :: acc)).
  change (pf_digits (S f) x acc) with (if x <? 10 then (48 + x) :: acc else pf_digits f (x / 10) ((48 + x mod 10) :: acc)).
  replace (x =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
  destruct (Z.ltb_spec x 10) as [L|L].
  - rewrite Z.div_small by lia. rewrite Z.mod_small by lia. reflexivity.
  - cbv beta iota. apply IH. rewrite Nat2Z.inj_succ, Z.pow_succ_r in Hx by lia. split.
    + apply Z.div_le_lower_bound; lia.
    + apply Z.div_lt_upper_bound; lia.
Qed.

Lemma pf_digits_fuel : forall f x acc, 0 <= x < 10 ^ Z.of_nat (S f) -> pf_digits (S f) x acc = pf_digits (S (S f)) x acc.
Proof.
  induction f as [|f IH]; intros x acc Hx.
  - cbn in Hx. cbn [pf_digits]. replace (x <? 10) with true by (symmetry; apply Z.ltb_lt; lia). reflexivity.
  - change (pf_digits (S (S f)) x acc) with (if x <? 10 then (48 + x) :: acc else pf_digits (S f) (x / 10) ((48 + x mod 10) :: acc)).
    change (pf_digits (S (S (S f))) x acc)
      with (if x <? 10 then (48 + x) :: acc else pf_digits (S (S f)) (x / 10) ((48 + x mod 10) :: acc)).
    destruct (Z.ltb_spec x 10) as [L|L]; [reflexivity|].
    cbv beta iota. apply IH. rewrite (Nat2Z.inj_succ (S f)), Z.pow_succ_r in Hx by lia. split.
    + apply Z.div_pos; lia.
    + apply Z.div_lt_upper_bound; lia.
Qed.

Lemma pf_digits_mono : forall k f x acc, 0 <= x < 10 ^ Z.of_nat (S f) ->
  pf_digits (S f) x acc = pf_digits (k + S f) x acc.
Proof.
  induction k as [|k IH]; intros f x acc Hx; [reflexivity|].
  rewrite (IH f x acc Hx).
  assert (E1 : (S k + S f)%nat = S (S (k + f))) by lia. assert (E2 : (k + S f)%nat = S (k + f)) by lia.
  rewrite E1, E2. apply pf_digits_fuel.
  split; [lia|]. apply Z.lt_le_trans with (10 ^ Z.of_nat (S f)); [lia|].
  apply Z.pow_le_mono_r; lia.
Qed.

Lemma dec_udec : forall u, 0 <= u < 10 ^ 19 -> dec u = pf_udec u.
Proof.
  intros u Hu. unfold dec, pf_udec. destruct (Z.eqb_spec u 0) as [->|N]; [reflexivity|].
  change 20%nat with (S 19). rewrite dec_aux_pf by (cbn; lia).
  apply (pf_digits_fuel 18). cbn. lia.
Qed.

Lemma dec_pfdec : forall v, 0 <= v < 10 ^ 10 -> dec v = pf_dec v.
Proof.
  intros v Hv. unfold dec, pf_dec. destruct (Z.ltb_spec v 0) as [L|L]; [lia|]. cbv beta iota.
  destruct (Z.eqb_spec v 0) as [->|N]; [reflexivity|].
  change 20%nat with (S 19). rewrite dec_aux_pf by (cbn; lia).
  symmetry. apply (pf_digits_mono 8 10). cbn. lia.
Qed.

Lemma pf_hex2_hex2 : forall v, 0 <= v < 256 -> pf_hex2 v = hex2 v.
Proof.
  intros v Hv.
  assert (A : forallb (fun k => if list_eq_dec Z.eq_dec (pf_hex2 (Z.of_nat k)) (hex2 (Z.of_nat k)) then true else false)
                (seq 0 256) = true) by (vm_compute; reflexivity).
  rewrite forallb_forall in A. specialize (A (Z.to_nat v) ltac:(apply in_seq; lia)).
  rewrite Z2Nat.id in A by lia. destruct (list_eq_dec Z.eq_dec _ _); [assumption | discriminate].
Qed.

Lemma tj_resv : map (fun s => (bv_unsigned (fst s), bv_unsigned (snd s))) (segments_reserved rsegs) =
  [(65536, 8192); (73728, 57344); (131072, 4096); (135168, 204800)].
Proof. vm_compute. reflexivity. Qed.

Lemma img_free_res : forall D n lo len, pf_img_free D n -> 0 < n -> 0 < len ->
  In (lo, len) (map (fun s => (bv_unsigned (fst s), bv_unsigned (snd s))) (segments_reserved rsegs)) ->
  D + n <= lo \/ lo + len <= D.
Proof.
  intros D n lo len H Hn Hl Hin. apply in_map_iff in Hin. destruct Hin as [s [E Hs]].
  injection E as E1 E2.
  destruct (Z.leb_spec (D + n) lo) as [A|A]; [left; lia|].
  destruct (Z.leb_spec (lo + len) D) as [B|B]; [right; lia|].
  exfalso. apply (H (Z.max D lo - D) ltac:(lia) s Hs). rewrite E1, E2. lia.
Qed.

Ltac resv_in := rewrite tj_resv; cbn [In]; repeat first [left; reflexivity | right].

Lemma img_free_out : forall D n, pf_img_free D n -> 0 < n -> D + n <= 0x10000 \/ 0x53000 <= D.
Proof.
  intros D n H Hn.
  pose proof (img_free_res D n 65536 8192 H Hn ltac:(lia) ltac:(resv_in)).
  pose proof (img_free_res D n 73728 57344 H Hn ltac:(lia) ltac:(resv_in)).
  pose proof (img_free_res D n 131072 4096 H Hn ltac:(lia) ltac:(resv_in)).
  pose proof (img_free_res D n 135168 204800 H Hn ltac:(lia) ltac:(resv_in)).
  lia.
Qed.

Lemma img_free_sub : forall D n k n', pf_img_free D n -> 0 <= k -> k + n' <= n -> pf_img_free (D + k) n'.
Proof. intros D n k n' H Hk Hn i Hi s Hs. replace (D + k + i) with (D + (k + i)) by lia. apply H; [lia | exact Hs]. Qed.

Lemma rw_cells_app : forall m A c1 c2,
  rw_cells rsegs m A (c1 ++ c2) <-> rw_cells rsegs m A c1 /\ rw_cells rsegs m (A + Z.of_nat (cells_size c1)) c2.
Proof.
  intros m A c1 c2. unfold rw_cells, cells_at, wr_at.
  rewrite cells_wf_app, cells_bytes_app, cells_size_app, bytes_at_app.
  split.
  - intros [[[W1 W2] [B1 B2]] (Ha & Hl & Hw)].
    rewrite cells_bytes_length in B2 by exact W1.
    split; split; try (split; assumption).
    + split; [lia|]. split; [lia|]. intros i Hi. apply Hw. lia.
    + split; [lia|]. split; [lia|]. intros i Hi.
      replace (A + Z.of_nat (cells_size c1) + i) with (A + (Z.of_nat (cells_size c1) + i)) by lia. apply Hw. lia.
  - intros [[[W1 B1] (Ha1 & Hl1 & Hw1)] [[W2 B2] (Ha2 & Hl2 & Hw2)]].
    rewrite cells_bytes_length by exact W1.
    split; [split; [split; assumption | split; assumption]|].
    split; [lia|]. split; [lia|]. intros i Hi.
    destruct (Z.ltb_spec i (Z.of_nat (cells_size c1))).
    + apply Hw1. lia.
    + replace (A + i) with (A + Z.of_nat (cells_size c1) + (i - Z.of_nat (cells_size c1))) by lia. apply Hw2. lia.
Qed.

Lemma bytes_at_mrd : forall m A bs x, bytes_at rsegs m A bs -> A <= x < A + Z.of_nat (length bs) ->
  exists b, mrd rsegs m (wa x) = Some b.
Proof.
  intros m A bs x (Ha & Hl & H) Hx.
  replace x with (A + Z.of_nat (Z.to_nat (x - A))) by lia. rewrite H by lia.
  destruct (nth_error bs (Z.to_nat (x - A))) eqn:E; [eexists; reflexivity|].
  apply nth_error_None in E. lia.
Qed.

Lemma stk_tr : forall W m m' lo hi, stk rsegs m lo hi -> munch W m m' -> wmono rsegs m m' ->
  (forall x, lo <= x < hi -> outside W x \/ exists b, mrd rsegs m' (wa x) = Some b) -> stk rsegs m' lo hi.
Proof.
  intros W m m' lo hi (H1 & H2 & H) Hm Hw Hc. split; [lia|]. split; [lia|].
  intros a Ha. destruct (H a Ha) as [Hwa (b & Hb)]. split; [apply Hw; exact Hwa|].
  destruct (Hc a Ha) as [Ho | Hb'].
  - exists b. unfold mrd in *. rewrite Hm; [exact Hb|]. rewrite wa_unsigned by lia. exact Ho.
  - exact Hb'.
Qed.

Lemma stk_cb : forall m A n, stk rsegs m A (A + Z.of_nat n) -> exists j, rw_cells rsegs m A [CB n j].
Proof.
  intros m A n H. pose proof H as (H1 & _ & _).
  destruct (stk_carve rsegs m A (A + Z.of_nat n) n H ltac:(lia)) as [_ (j & J)].
  exists j. replace (A + Z.of_nat n - Z.of_nat n) with A in J by lia. exact J.
Qed.

Lemma pf_bytes_app : forall a b, pf_bytes (a ++ b) = pf_bytes a ++ pf_bytes b.
Proof. intros. unfold pf_bytes. apply map_app. Qed.

Lemma length_pf_bytes : forall a, length (pf_bytes a) = length a.
Proof. intros. unfold pf_bytes. apply length_map. Qed.

Lemma objs_text_app : forall tok now A B i,
  objs_text tok now i (A ++ B) = objs_text tok now i A ++ objs_text tok now (i + length A) B.
Proof.
  intros tok now A. induction A as [|e A IH]; intros B i; cbn [app objs_text length].
  - rewrite Nat.add_0_r. reflexivity.
  - rewrite IH, app_assoc. replace (S i + length A)%nat with (i + S (length A))%nat by lia. reflexivity.
Qed.

Definition tj_rest (T : list byte) (now i : Z) : list Z :=
  objs_text box_tok now (Z.to_nat i) (map (fun k => tj_entry T (Z.of_nat k)) (seq (Z.to_nat i) (Z.to_nat (n_of T - i))))
  ++ [93].

Lemma tj_rest_0 : forall T now, tj_text T now = [91] ++ tj_rest T now 0.
Proof.
  intros T now. unfold tj_text, table_json_text, tj_entries, tj_rest.
  rewrite Z.sub_0_r. reflexivity.
Qed.

Lemma tj_rest_step : forall T now i, 0 <= i < n_of T ->
  tj_rest T now i = obj_text box_tok now (Z.to_nat i) (tj_entry T i) ++ tj_rest T now (i + 1).
Proof.
  intros T now i Hi. unfold tj_rest.
  replace (Z.to_nat (n_of T - i)) with (S (Z.to_nat (n_of T - (i + 1)))) by lia.
  replace (Z.to_nat (i + 1)) with (S (Z.to_nat i)) by lia.
  cbn [seq map objs_text]. rewrite Z2Nat.id by lia. rewrite app_assoc. reflexivity.
Qed.

Lemma tj_rest_end : forall T now, 0 <= n_of T -> tj_rest T now (n_of T) = [93].
Proof. intros T now H. unfold tj_rest. rewrite Z.sub_diag. reflexivity. Qed.

Lemma ld_val : forall bs, length bs = 8%nat -> bv_extract 0 64 (le_bytes_to_word bs) = Z_to_bv 64 (bytes_le_to_Z bs).
Proof.
  intros bs L. apply bv_eq. rewrite extract_low_mod by lia. unfold le_bytes_to_word.
  pose proof (bv_unsigned_in_range 64 (Z_to_bv 64 (bytes_le_to_Z bs))) as H. unfold bv_modulus in H.
  change (Z.of_N 64) with 64. rewrite Z.mod_small by lia. reflexivity.
Qed.

Ltac img := apply ro_bytes_at; [assumption | lia | cbn; lia | apply ro_bytes_b_sound; vm_compute; reflexivity].
Ltac fp_tac := unfold sub_fp; let x := fresh "x" in let Hx := fresh "Hx" in intros x Hx; cbn [outside] in *;
  repeat split; try exact I; lia.
Ltac dj_tac := cbn [disjoint_from]; repeat split; try exact I; lia.

Lemma task_mem_munch : forall W m m', MemNorm.task_mem rsegs m -> munch W m m' ->
  (forall a : word, ~ outside W (bv_unsigned a) -> wview rsegs m a <> None) -> MemNorm.task_mem rsegs m'.
Proof.
  intros W m m' TK MU HW a b E. destruct (m a) as [b0|] eqn:E0; [exact (TK a b0 E0)|].
  assert (HI : ~ outside W (bv_unsigned a)) by (intros Ho; rewrite (MU a Ho), E0 in E; discriminate).
  pose proof (HW a HI) as W0. unfold wview in W0. rewrite E0 in W0.
  destruct (find_segment rsegs (bv_unsigned a) 1) eqn:EF; [left; discriminate|].
  exfalso. apply W0. reflexivity.
Qed.

Lemma dec_aux_len : forall f v acc, (length (dec_aux f v acc) <= f + length acc)%nat.
Proof.
  induction f as [|f IH]; intros v acc; cbn [dec_aux]; [lia|]. destruct (v =? 0); [lia|].
  specialize (IH (v / 10) ((48 + v mod 10) :: acc)). cbn [length] in IH. lia.
Qed.

Lemma dec_len : forall v, (length (dec v) <= 20)%nat.
Proof.
  intros v. unfold dec. destruct (v =? 0); [cbn; lia|]. pose proof (dec_aux_len 20 v []) as H. cbn [length] in H. lia.
Qed.

Lemma tj_box_ok : forall f a b, bn_ret f [] a b = 0 ->
  bn_ok a = true /\ bn_ok b = true /\ (a =? 0) && (b =? 0) = false.
Proof.
  intros f a b H. unfold bn_ret in H.
  destruct (bn_ok a && bn_ok b && negb ((a =? 0) && (b =? 0)) && _) eqn:E; [|discriminate].
  apply andb_prop in E as [E _]. apply andb_prop in E as [E E3]. apply andb_prop in E as [E1 E2].
  apply negb_true_iff in E3. auto.
Qed.

Lemma tj_accept : forall f a b A1 A2 A3, bn_ret f [] a b = 0 -> A1 <> 0 -> A2 <> 0 -> A3 <> 0 ->
  bn_accept f [] a b A1 24 A2 24 A3 48 = true.
Proof.
  intros f a b A1 A2 A3 H N1 N2 N3. destruct (tj_box_ok f a b H) as (Ea & Eb & Ez).
  destruct (bn_c17 f a b Ea Eb Ez) as (_ & L1 & L2 & L3 & _). cbv zeta in *.
  unfold bn_accept, bn_args_ok.
  repeat (apply andb_true_iff; split);
    first [ assumption | reflexivity | apply negb_true_iff; first [assumption | apply Z.eqb_neq; lia]
          | apply Z.eqb_eq; exact H | apply Z.ltb_lt; lia ].
Qed.

Lemma tj_reject : forall f a b A1 n1 A2 n2 A3 n3, bn_ret f [] a b <> 0 ->
  bn_accept f [] a b A1 n1 A2 n2 A3 n3 = false.
Proof.
  intros f a b A1 n1 A2 n2 A3 n3 H. unfold bn_accept.
  rewrite (proj2 (Z.eqb_neq _ _) H). rewrite andb_false_r. reflexivity.
Qed.

Lemma rwc_stk : forall m A n j, rw_cells rsegs m A [CB n j] -> stk rsegs m A (A + Z.of_nat n).
Proof.
  intros m A n j [[[Lj _] B] (H1 & H2 & HW)]. cbn [cells_size csize cells_bytes cbytes] in *.
  rewrite app_nil_r in B. rewrite Nat.add_0_r in *.
  split; [lia|]. split; [lia|]. intros a Ha. split.
  - replace a with (A + (a - A)) by lia. apply HW. lia.
  - eapply bytes_at_mrd; [exact B|]. rewrite Lj. lia.
Qed.

Lemma stk_sub : forall m a b a' b', stk rsegs m a b -> a <= a' -> a' <= b' -> b' <= b -> stk rsegs m a' b'.
Proof.
  intros m a b a' b' (H1 & H2 & H) X1 X2 X3. split; [lia|]. split; [lia|]. intros x Hx. apply H. lia.
Qed.

Lemma tj_c8c8 : forall m A w0 w1 cs, rw_cells rsegs m A (C8 w0 :: C8 w1 :: cs) -> bytes_at rsegs m A (le8 w0 ++ le8 w1).
Proof.
  intros m A w0 w1 cs [[_ B] _]. cbn [cells_bytes cbytes] in B. rewrite app_assoc in B.
  apply bytes_at_app in B. exact (proj1 B).
Qed.

Lemma rwc_cb : forall m A n j, rw_cells rsegs m A [CB n j] -> length j = n /\ bytes_at rsegs m A j.
Proof. intros m A n j [[[Lj _] B] _]. cbn [cells_bytes cbytes] in B. rewrite app_nil_r in B. split; assumption. Qed.

Lemma tok_rng : forall l, Forall (fun c => bn_tok_char c = true) l -> Forall (fun c => 0 < c < 256) l.
Proof.
  intros l H. eapply Forall_impl; [|exact H]. intros c Hc. unfold bn_tok_char in Hc.
  repeat (apply orb_true_iff in Hc; destruct Hc as [Hc|Hc]); repeat (apply andb_true_iff in Hc; destruct Hc as [? Hc]);
    rewrite ?Z.leb_le, ?Z.eqb_eq in *; lia.
Qed.

Section TJ.
Variables (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F0 : bvmap 5 word) (m0 : word -> option byte)
  (lo S t now buf cap : Z) (T : list byte) (canary : word).

Hypothesis Rlo : 0x524f8 <= lo.
Hypothesis RK : lo + 6240 <= S.
Hypothesis RS63 : S < 2^63.
Hypothesis RS16 : S mod 16 = 0.
Hypothesis Rt : 0 < t < 2^64.
Hypothesis Rt8 : t mod 8 = 0.
Hypothesis RtS : t + 400 <= lo \/ S <= t.
Hypothesis Rnow : 0 <= now < 2^64.
Hypothesis Rbuf : 0 <= buf < 2^64.
Hypothesis Rcap : 0 <= cap < 2^31.
Hypothesis LT : length T = 400%nat.
Hypothesis TOK : disco_table_c.table_ok T.
Hypothesis TK0 : MemNorm.task_mem rsegs m0.

Local Abbreviation tj_sv := [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

Definition tj_len : Z := Z.of_nat (length (tj_text T now)).

Definition tj_res (v : Z) (m : word -> option byte) : Prop :=
  (cap < 3 -> v = -1 /\ munch [(lo, S)] m0 m) /\
  (3 <= cap -> tj_len < cap ->
     v = tj_len /\ munch [(lo, S); (buf, buf + tj_len + 1)] m0 m /\
     bytes_at rsegs m buf (pf_bytes (tj_text T now ++ [0]))) /\
  (3 <= cap -> cap <= tj_len -> v = -1 /\ munch [(lo, S); (buf, buf + cap)] m0 m).

Definition tj_post : machine_state -> Prop :=
  fun ms' => exists (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word)
                    (F' : bvmap 5 word) (fc' : bv 32) (m' : word -> option byte),
    ms' = MS (mkR ra (Z_to_bv 64 S) gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7'
                  s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
             F' (ret_pc ra) fc' None m' (seg_rom rsegs) /\
    frm0 fc' /\ (forall k : reg, bv_unsigned k <> 10 -> reg_get F' k = reg_get F0 k) /\
    wmono rsegs m0 m' /\ mem_inv rsegs m' /\ MemNorm.task_mem rsegs m' /\ stk rsegs m' lo S /\
    (cap < 3 -> a0' = Z_to_bv 64 (-1) /\ munch [(lo, S)] m0 m') /\
    (3 <= cap -> Z.of_nat (length (tj_text T now)) < cap ->
       a0' = Z_to_bv 64 (Z.of_nat (length (tj_text T now))) /\
       munch [(lo, S); (buf, buf + Z.of_nat (length (tj_text T now)) + 1)] m0 m' /\
       bytes_at rsegs m' buf (pf_bytes (tj_text T now ++ [0]))) /\
    (3 <= cap -> cap <= Z.of_nat (length (tj_text T now)) ->
       a0' = Z_to_bv 64 (-1) /\ munch [(lo, S); (buf, buf + cap)] m0 m').

Lemma tj_exit : forall (m : word -> option byte) (F : bvmap 5 word) (fc : bv 32) (v : Z) (j : list byte)
    (x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word),
  rw_cells rsegs m (S + -304) (CB 200 j :: tj_sv) -> stk rsegs m lo (S + -304) ->
  frm0 fc -> (forall k : reg, bv_unsigned k <> 10 -> reg_get F k = reg_get F0 k) ->
  wmono rsegs m0 m -> mem_inv rsegs m -> MemNorm.task_mem rsegs m -> tj_res v m ->
  evt rsegs tj_post (MS (mkR x1 (Z_to_bv 64 (S + -304)) gp tp x5 x6 x7 (Z_to_bv 64 v) x9 x10 x11 x12 x13 x14 x15 x16
                             x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
                        F (Z_to_bv 64 0x15c88) fc None m (seg_rom rsegs)).
Proof.
  intros m F fc v j x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29
    x30 x31 FR ST FC FK WM MI TK RES.
  do 14 step.
  release_frame FR ST S.
  step. step.
  apply evt_done. unfold tj_post.
  exists x5, x6, x7, (Z_to_bv 64 v), x11, x12, x13, x14, x15, x16, x17, x28, x29, x30, x31, F, fc, m.
  split; [reflexivity|].
  unfold tj_res, tj_len in RES. destruct RES as (R1 & R2 & R3).
  split; [exact FC|]. split; [exact FK|]. split; [exact WM|]. split; [exact MI|]. split; [exact TK|].
  split; [exact ST|].
  split; [intros C; destruct (R1 C) as (-> & ?); split; [reflexivity|assumption]|].
  split; [intros C1 C2; destruct (R2 C1 C2) as (-> & ? & ?); split; [reflexivity|split; assumption]|].
  intros C1 C2; destruct (R3 C1 C2) as (-> & ?); split; [reflexivity|assumption].
Qed.

Lemma tj_small : forall (t0 t1 t2 a4 a5 a6 a7 t3 t4 t5 t6 : word) (fc : bv 32),
  cap < 3 -> stk rsegs m0 lo S -> frm0 fc -> mem_inv rsegs m0 ->
  evt rsegs tj_post (MS (mkR ra (Z_to_bv 64 S) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 t) (Z_to_bv 64 now) (Z_to_bv 64 buf)
                         (Z_to_bv 64 cap) a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                    F0 (Z_to_bv 64 0x15c40) fc None m0 (seg_rom rsegs)).
Proof.
  intros t0 t1 t2 a4 a5 a6 a7 t3 t4 t5 t6 fc C3 ST FC MI.
  assert (SW : forall a : word, ~ outside [(lo, S)] (bv_unsigned a) -> wview rsegs m0 a <> None).
  { intros a HI. assert (HR : lo <= bv_unsigned a < S) by (cbn [outside] in HI; lia).
    destruct ST as (_ & _ & SS). destruct (SS _ HR) as [W _]. unfold wa in W. rewrite Z_to_bv_lit_self in W. exact W. }
  pose proof (munch_refl [(lo, S)] m0) as MU. pose proof (wmono_refl rsegs m0) as WM.
  carve_frame 304%nat ST.
  do 18 step. rewrite ltu_lit by lia. if_false.
  eapply tj_exit; [exact FR | exact ST | exact FC | intros; reflexivity | exact WM | exact MI
                  | eapply task_mem_munch; [exact TK0 | exact MU | exact SW] | ].
  unfold tj_res. split; [intros _; split; [reflexivity | exact MU] | split; intros; lia].
Qed.

Hypothesis Rcap3 : 3 <= cap.
Hypothesis Rb0 : 0 < buf.
Hypothesis Rbl : buf + cap <= lo \/ S <= buf.
Hypothesis Rbt : buf + cap <= t \/ t + 400 <= buf.
Hypothesis Rbi : pf_img_free buf cap.
Hypothesis Rbo : buf + cap <= 0x10000 \/ 0x53000 <= buf.
Hypothesis Rb64 : buf + cap <= 2^64.
Hypothesis ST0 : stk rsegs m0 lo S.
Hypothesis SB0 : stk rsegs m0 buf (buf + cap).
Hypothesis SNP : snprintf_contract.
Hypothesis SNK : snprintf_stk_contract.
Hypothesis BOX : reac_box_name_contract.

Lemma tj_task : forall m hi, munch [(lo, S); (buf, hi)] m0 m -> buf <= hi <= buf + cap -> MemNorm.task_mem rsegs m.
Proof.
  intros m hi MU HL. eapply task_mem_munch; [exact TK0 | exact MU |]. intros a HI.
  assert (HR : lo <= bv_unsigned a < S \/ buf <= bv_unsigned a < buf + cap) by (cbn [outside] in HI; lia).
  destruct HR as [HR|HR]; [destruct ST0 as (_ & _ & SS) | destruct SB0 as (_ & _ & SS)];
    destruct (SS _ HR) as [W _]; unfold wa in W; rewrite Z_to_bv_lit_self in W; exact W.
Qed.

Definition tj_mem (cs : list cell) (acc : list Z) (m : word -> option byte) : Prop :=
  rw_cells rsegs m (S + -304) cs /\ stk rsegs m lo (S + -304) /\ bytes_at rsegs m t T /\
  bytes_at rsegs m 0x205f8 bn_table /\ bytes_at rsegs m 0x206a0 (le8 (Z_to_bv 64 0x51c90)) /\
  bytes_at rsegs m 0x51c90 (le8 canary) /\ mem_inv rsegs m /\ wmono rsegs m0 m /\
  munch [(lo, S); (buf, buf + Z.of_nat (length acc) + 1)] m0 m /\
  stk rsegs m buf (buf + cap) /\ bytes_at rsegs m buf (pf_bytes acc).

Lemma length_bn_table : length bn_table = 24%nat.
Proof. reflexivity. Qed.

Lemma tj_mem_after : forall cs acc m m' (q : list Z) (Tw : list Z),
  tj_mem cs acc m -> cells_size cs = 304%nat ->
  Tw = firstn (Z.to_nat (cap - Z.of_nat (length acc) - 1)) q -> Z.of_nat (length acc) < cap ->
  munch [(lo, S + -304); (buf + Z.of_nat (length acc), buf + Z.of_nat (length acc) + Z.of_nat (length Tw) + 1)] m m' ->
  wmono rsegs m m' -> mem_inv rsegs m' -> stk rsegs m' lo (S + -304) ->
  bytes_at rsegs m' (buf + Z.of_nat (length acc)) (pf_bytes (Tw ++ [0])) ->
  tj_mem cs (acc ++ Tw) m'.
Proof.
  intros cs acc m m' q Tw TM Hcs ETw Hoff MU' WM' MI' ST' BY'.
  destruct TM as (FR & ST & HT & BNT & GG & GD & MI & WM & MU & SB & BA).
  assert (LW : Z.of_nat (length Tw) <= cap - Z.of_nat (length acc) - 1) by (subst Tw; rewrite length_firstn; lia).
  pose proof (bytes_at_bound rsegs m' _ _ BY') as BYB. rewrite length_pf_bytes, length_app in BYB. cbn [length] in BYB.
  pose proof length_bn_table as LBN.
  unfold tj_mem. rewrite length_app.
  split; [eapply rw_cells_transport; [exact FR | exact MU' | exact WM' | rewrite Hcs; dj_tac]|].
  split; [exact ST'|].
  split; [eapply bytes_at_transport; [exact HT | exact MU' | rewrite LT; dj_tac]|].
  split; [eapply bytes_at_transport; [exact BNT | exact MU' | rewrite LBN; dj_tac]|].
  split; [eapply bytes_at_transport; [exact GG | exact MU' | rewrite length_le8; dj_tac]|].
  split; [eapply bytes_at_transport; [exact GD | exact MU' | rewrite length_le8; dj_tac]|].
  split; [exact MI'|].
  split; [eapply wmono_trans; [exact WM | exact WM']|].
  split; [eapply munch_trans; [eapply munch_weaken; [|exact MU] | eapply munch_weaken; [|exact MU']]; fp_tac|].
  split.
  - eapply stk_tr; [exact SB | exact MU' | exact WM' |]. intros x Hx.
    destruct (Z.leb_spec (buf + Z.of_nat (length acc)) x) as [X1|X1];
      [destruct (Z.ltb_spec x (buf + Z.of_nat (length acc) + Z.of_nat (length Tw) + 1)) as [X2|X2]|].
    + right. eapply bytes_at_mrd; [exact BY' | rewrite length_pf_bytes, length_app; cbn [length]; lia].
    + left. cbn [outside]. repeat split; try exact I; lia.
    + left. cbn [outside]. repeat split; try exact I; lia.
  - rewrite pf_bytes_app. apply bytes_at_app. split.
    + eapply bytes_at_transport; [exact BA | exact MU' | rewrite length_pf_bytes; dj_tac].
    + rewrite length_pf_bytes. rewrite pf_bytes_app in BY'. apply bytes_at_app in BY'. exact (proj1 BY').
Qed.

Lemma tj_call : forall (cs : list cell) (acc : list Z) (m : word -> option byte) (F : bvmap 5 word) (fc : bv 32)
    (x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word)
    (A : Z) (fmt : list Z) (ps : list pf_piece) (args : list pf_arg) (q : list Z) (ret : Z) (Q : machine_state -> Prop),
  tj_mem cs acc m -> cells_size cs = 304%nat -> Z.of_nat (length acc) < cap ->
  bytes_at rsegs m A (pf_bytes (fmt ++ [0])) -> RO_LO <= A -> A + Z.of_nat (length fmt) + 1 <= RO_END ->
  pf_parse fmt = Some ps ->
  pf_args_ok m (S + -304) lo (buf + Z.of_nat (length acc)) (cap - Z.of_nat (length acc)) [x13; x14; x15; x16; x17] args ->
  pf_text ps args = Some q -> Z.of_nat (length q) < 2^31 - 1 -> frm0 fc ->
  x1 = Z_to_bv 64 ret -> 0 <= ret < 2^64 -> ret mod 2 = 0 ->
  (forall (m' : word -> option byte) (Ft : bvmap 5 word) (fc' : bv 32)
          (y5 y6 y7 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31 : word),
     tj_mem cs (acc ++ firstn (Z.to_nat (cap - Z.of_nat (length acc) - 1)) q) m' ->
     bytes_at rsegs m' (buf + Z.of_nat (length acc))
       (pf_bytes (firstn (Z.to_nat (cap - Z.of_nat (length acc) - 1)) q ++ [0])) ->
     frm0 fc' ->
     (forall k : reg, bv_unsigned k <> 10 -> reg_get Ft k = reg_get F k) ->
     evt rsegs Q (MS (mkR x1 (Z_to_bv 64 (S + -304)) gp tp y5 y6 y7 x8 x9 (Z_to_bv 64 (Z.of_nat (length q))) y11 y12
                          y13 y14 y15 y16 y17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 y28 y29 y30 y31)
                     Ft (Z_to_bv 64 ret) fc' None m' (seg_rom rsegs))) ->
  x10 = Z_to_bv 64 (buf + Z.of_nat (length acc)) -> x11 = Z_to_bv 64 (cap - Z.of_nat (length acc)) ->
  x12 = Z_to_bv 64 A ->
  evt rsegs Q (MS (mkR x1 (Z_to_bv 64 (S + -304)) gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21
                       x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
                  F (Z_to_bv 64 SNPRINTF) fc None m (seg_rom rsegs)).
Proof.
  intros cs acc m F fc x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28
    x29 x30 x31 A fmt ps args q ret Q TM Hcs Hoff FB FLO FHI FP FA FT FL FC E1 Hr He K E10 E11 E12.
  subst x10 x11 x12.
  pose proof TM as (FR & ST & HT & BNT & GG & GD & MI & WM & MU & SB & BA).
  pose proof (bytes_at_bound rsegs m A _ FB) as FBB. rewrite length_pf_bytes, length_app in FBB. cbn [length] in FBB.
  destruct (stk_carve rsegs m buf (buf + cap) (Z.to_nat (cap - Z.of_nat (length acc))) SB ltac:(lia)) as [_ (jb & JB)].
  replace (buf + cap - Z.of_nat (Z.to_nat (cap - Z.of_nat (length acc)))) with (buf + Z.of_nat (length acc)) in JB
    by lia.
  assert (PFI : pf_img_free (buf + Z.of_nat (length acc)) (cap - Z.of_nat (length acc)))
    by (eapply img_free_sub; [exact Rbi | lia | lia]).
  pose proof (SNP x1 (Z_to_bv 64 (S + -304)) gp tp x5 x6 x7 x8 x9 (Z_to_bv 64 (buf + Z.of_nat (length acc)))
                (Z_to_bv 64 (cap - Z.of_nat (length acc))) (Z_to_bv 64 A) x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23
                x24 x25 x26 x27 x28 x29 x30 x31 F fc m lo canary fmt ps args q jb) as H.
  cbv zeta in H.
  rewrite (unsigned_lit (S + -304)), (unsigned_lit (buf + Z.of_nat (length acc))),
    (unsigned_lit (cap - Z.of_nat (length acc))), (unsigned_lit A) in H by lia.
  assert (TKm : MemNorm.task_mem rsegs m) by (eapply tj_task; [exact MU | lia]).
  eapply evt_cut.
  { apply H; try assumption; unfold RO_LO, RO_END, IMG_END, SNPRINTF_K in *; lia. }
  intros ms' PP. unfold printf_post in PP.
  destruct PP as (y5 & y6 & y7 & y11 & y12 & y13 & y14 & y15 & y16 & y17 & y28 & y29 & y30 & y31 & Ft & fc' & m'
                  & E & MU' & WM' & MI' & TK' & FC' & FK' & ST' & BY').
  subst ms' x1. rewrite (ret_pc_even ret Hr He).
  rewrite (unsigned_lit (S + -304)) in MU', ST' by lia.
  apply K; [ | exact BY' | exact FC' | exact FK' ].
  eapply tj_mem_after; [exact TM | exact Hcs | reflexivity | exact Hoff | exact MU' | exact WM' | exact MI' | exact ST'
                       | exact BY'].
Qed.

Lemma tj_call_stk : forall (cs : list cell) (w0 w1 : word) (acc : list Z) (m : word -> option byte)
    (F : bvmap 5 word) (fc : bv 32)
    (x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word)
    (A : Z) (fmt : list Z) (ps : list pf_piece) (args : list pf_arg) (q : list Z) (ret : Z) (Q : machine_state -> Prop),
  tj_mem (C8 w0 :: C8 w1 :: cs) acc m -> cells_size cs = 288%nat -> Z.of_nat (length acc) < cap ->
  bytes_at rsegs m A (pf_bytes (fmt ++ [0])) -> RO_LO <= A -> A + Z.of_nat (length fmt) + 1 <= RO_END ->
  pf_parse fmt = Some ps ->
  pf_args_ok m (S + -304) lo (buf + Z.of_nat (length acc)) (cap - Z.of_nat (length acc))
    ([x13; x14; x15; x16; x17] ++ [w0; w1]) args ->
  pf_text ps args = Some q -> Z.of_nat (length q) < 2^31 - 1 -> frm0 fc ->
  x1 = Z_to_bv 64 ret -> 0 <= ret < 2^64 -> ret mod 2 = 0 ->
  (forall (m' : word -> option byte) (Ft : bvmap 5 word) (fc' : bv 32)
          (y5 y6 y7 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31 : word),
     tj_mem (C8 w0 :: C8 w1 :: cs) (acc ++ firstn (Z.to_nat (cap - Z.of_nat (length acc) - 1)) q) m' ->
     bytes_at rsegs m' (buf + Z.of_nat (length acc))
       (pf_bytes (firstn (Z.to_nat (cap - Z.of_nat (length acc) - 1)) q ++ [0])) ->
     frm0 fc' ->
     (forall k : reg, bv_unsigned k <> 10 -> reg_get Ft k = reg_get F k) ->
     evt rsegs Q (MS (mkR x1 (Z_to_bv 64 (S + -304)) gp tp y5 y6 y7 x8 x9 (Z_to_bv 64 (Z.of_nat (length q))) y11 y12
                          y13 y14 y15 y16 y17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 y28 y29 y30 y31)
                     Ft (Z_to_bv 64 ret) fc' None m' (seg_rom rsegs))) ->
  x10 = Z_to_bv 64 (buf + Z.of_nat (length acc)) -> x11 = Z_to_bv 64 (cap - Z.of_nat (length acc)) ->
  x12 = Z_to_bv 64 A ->
  evt rsegs Q (MS (mkR x1 (Z_to_bv 64 (S + -304)) gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21
                       x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
                  F (Z_to_bv 64 SNPRINTF) fc None m (seg_rom rsegs)).
Proof.
  intros cs w0 w1 acc m F fc x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26
    x27 x28 x29 x30 x31 A fmt ps args q ret Q TM Hcs Hoff FB FLO FHI FP FA FT FL FC E1 Hr He K E10 E11 E12.
  subst x10 x11 x12.
  pose proof TM as (FR & ST & HT & BNT & GG & GD & MI & WM & MU & SB & BA).
  pose proof (bytes_at_bound rsegs m A _ FB) as FBB. rewrite length_pf_bytes, length_app in FBB. cbn [length] in FBB.
  destruct (stk_carve rsegs m buf (buf + cap) (Z.to_nat (cap - Z.of_nat (length acc))) SB ltac:(lia)) as [_ (jb & JB)].
  replace (buf + cap - Z.of_nat (Z.to_nat (cap - Z.of_nat (length acc)))) with (buf + Z.of_nat (length acc)) in JB
    by lia.
  assert (PFI : pf_img_free (buf + Z.of_nat (length acc)) (cap - Z.of_nat (length acc)))
    by (eapply img_free_sub; [exact Rbi | lia | lia]).
  assert (XS : bytes_at rsegs m (S + -304) (u64s [w0; w1])).
  { change (C8 w0 :: C8 w1 :: cs) with ([C8 w0; C8 w1] ++ cs) in FR. apply rw_cells_app in FR.
    destruct FR as [[[_ FB2] _] _]. cbn [cells_bytes cbytes] in FB2. cbn [u64s]. rewrite app_nil_r in FB2.
    rewrite app_nil_r. exact FB2. }
  pose proof (SNK x1 (Z_to_bv 64 (S + -304)) gp tp x5 x6 x7 x8 x9 (Z_to_bv 64 (buf + Z.of_nat (length acc)))
                (Z_to_bv 64 (cap - Z.of_nat (length acc))) (Z_to_bv 64 A) x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23
                x24 x25 x26 x27 x28 x29 x30 x31 F fc m lo canary fmt ps args q jb [w0; w1]) as H.
  cbv zeta in H.
  rewrite (unsigned_lit (S + -304)), (unsigned_lit (buf + Z.of_nat (length acc))),
    (unsigned_lit (cap - Z.of_nat (length acc))), (unsigned_lit A) in H by lia.
  assert (TKm : MemNorm.task_mem rsegs m) by (eapply tj_task; [exact MU | lia]).
  eapply evt_cut.
  { apply H; try assumption; cbn [length]; unfold RO_LO, RO_END, IMG_END, SNPRINTF_K in *; lia. }
  intros ms' PP. unfold printf_post in PP.
  destruct PP as (y5 & y6 & y7 & y11 & y12 & y13 & y14 & y15 & y16 & y17 & y28 & y29 & y30 & y31 & Ft & fc' & m'
                  & E & MU' & WM' & MI' & TK' & FC' & FK' & ST' & BY').
  subst ms' x1. rewrite (ret_pc_even ret Hr He).
  rewrite (unsigned_lit (S + -304)) in MU', ST' by lia.
  apply K; [ | exact BY' | exact FC' | exact FK' ].
  eapply tj_mem_after; [exact TM | cbn [cells_size csize]; rewrite Hcs; reflexivity | reflexivity | exact Hoff
                       | exact MU' | exact WM' | exact MI' | exact ST' | exact BY'].
Qed.

Lemma tj_exit2 : forall (pre : list cell) (acc : list Z) (m : word -> option byte) (F : bvmap 5 word) (fc : bv 32) (v : Z)
    (x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word),
  tj_mem (pre ++ tj_sv) acc m -> cells_size pre = 200%nat ->
  frm0 fc -> (forall k : reg, bv_unsigned k <> 10 -> reg_get F k = reg_get F0 k) -> tj_res v m ->
  evt rsegs tj_post (MS (mkR x1 (Z_to_bv 64 (S + -304)) gp tp x5 x6 x7 (Z_to_bv 64 v) x9 x10 x11 x12 x13 x14 x15 x16
                             x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
                        F (Z_to_bv 64 0x15c88) fc None m (seg_rom rsegs)).
Proof.
  intros pre acc m F fc v x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28
    x29 x30 x31 TM Hp FC FK RES.
  destruct TM as (FR & ST & HT & BNT & GG & GD & MI & WM & MU & SB & BA).
  pose proof (rw_cells_merge rsegs m (S + -304) [] pre tj_sv FR) as FR'. cbn [app] in FR'. rewrite Hp in FR'.
  assert (TKm : MemNorm.task_mem rsegs m).
  { pose proof RES as (_ & R2 & R3). destruct (Z.ltb_spec tj_len cap) as [C|C].
    - destruct (R2 Rcap3 C) as (_ & MU2 & _). eapply tj_task; [exact MU2 | unfold tj_len in *; lia].
    - destruct (R3 Rcap3 C) as (_ & MU2). eapply tj_task; [exact MU2 | lia]. }
  eapply tj_exit; [exact FR' | exact ST | exact FC | exact FK | exact WM | exact MI | exact TKm | exact RES].
Qed.

Lemma tj_fail : forall (pre : list cell) (acc : list Z) (m : word -> option byte) (F : bvmap 5 word) (fc : bv 32)
    (x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word),
  tj_mem (pre ++ tj_sv) acc m -> cells_size pre = 200%nat -> Z.of_nat (length acc) < cap -> cap <= tj_len ->
  frm0 fc -> (forall k : reg, bv_unsigned k <> 10 -> reg_get F k = reg_get F0 k) ->
  evt rsegs tj_post (MS (mkR x1 (Z_to_bv 64 (S + -304)) gp tp x5 x6 x7 (Z_to_bv 64 (-1)) x9 x10 x11 x12 x13 x14 x15
                             x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
                        F (Z_to_bv 64 0x15c88) fc None m (seg_rom rsegs)).
Proof.
  intros pre acc m F fc x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28
    x29 x30 x31 TM Hp Hl Hc FC FK.
  eapply tj_exit2; [exact TM | exact Hp | exact FC | exact FK |].
  pose proof TM as (FR & ST & HT & BNT & GG & GD & MI & WM & MU & SB & BA).
  unfold tj_res. split; [intros; lia|]. split; [intros; lia|].
  intros _ _. split; [reflexivity|]. eapply munch_weaken; [|exact MU]. fp_tac.
Qed.

Definition tj_nt : word := Z_to_bv 64 (2^64 - 1 - t).

Local Abbreviation tj_ptrs := [C8 (Z_to_bv 64 0x1031b); C8 (Z_to_bv 64 0x1038e); C8 (Z_to_bv 64 KDv);
  C8 (Z_to_bv 64 0x102c6); C8 (Z_to_bv 64 0x102ad); C8 (Z_to_bv 64 0x103e6); C8 (Z_to_bv 64 0x10363);
  C8 (Z_to_bv 64 0x10323); C8 tj_nt].

Definition tj_lo (j0 jb : list byte) : list cell := CB 24 j0 :: tj_ptrs ++ [CB 104 jb].
Definition tj_loa (j0 : list byte) (a : Z) (jb : list byte) : list cell :=
  CB 24 j0 :: tj_ptrs ++ [C8 (Z_to_bv 64 a); CB 96 jb].

Definition tj_ok (acc : list Z) (m : word -> option byte) (F : bvmap 5 word) (fc : bv 32) : Prop :=
  (exists j0 jb, tj_mem (tj_lo j0 jb ++ tj_sv) acc m) /\ Z.of_nat (length acc) < cap /\ frm0 fc /\
  (forall k : reg, bv_unsigned k <> 10 -> reg_get F k = reg_get F0 k).

Definition tj_oka (acc : list Z) (a : Z) (m : word -> option byte) (F : bvmap 5 word) (fc : bv 32) : Prop :=
  (exists j0 jb, tj_mem (tj_loa j0 a jb ++ tj_sv) acc m) /\ Z.of_nat (length acc) < cap /\ frm0 fc /\
  (forall k : reg, bv_unsigned k <> 10 -> reg_get F k = reg_get F0 k).

Definition tj_st (i pc : Z) (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
    (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x20 x23 x24 x25 x28 x29 x30 x31 : word) : machine_state :=
  MS (mkR x1 (Z_to_bv 64 (S + -304)) gp tp x5 x6 x7 (Z_to_bv 64 (-1)) (Z_to_bv 64 cap) x10 x11 x12 x13 x14 x15 x16 x17
          (Z_to_bv 64 buf) (Z_to_bv 64 now) x20 (Z_to_bv 64 t) (Z_to_bv 64 1) x23 x24 x25 (Z_to_bv 64 (48 * i))
          (Z_to_bv 64 i) x28 x29 x30 x31)
     F (Z_to_bv 64 pc) fc None m (seg_rom rsegs).

Definition tj_K (i : Z) (acc : list Z) (a : Z) : Prop :=
  forall (o1' o2' : Z) (m' : word -> option byte) (F' : bvmap 5 word) (fc' : bv 32)
         (y1 y5 y6 y7 y11 y12 y13 y14 y15 y16 y17 y24 y25 y28 y29 y30 y31 : word),
    tj_oka acc a m' F' fc' -> 0 <= o1' -> 0 <= o2' -> o1' + o2' = Z.of_nat (length acc) ->
    evt rsegs tj_post (tj_st i 0x15f7c F' fc' m' y1 y5 y6 y7 (Z_to_bv 64 o2') y11 y12 y13 y14 y15 y16 y17
                         (Z_to_bv 64 (t + 48 * i)) (Z_to_bv 64 o1') y24 y25 y28 y29 y30 y31).

Lemma tj_str : forall m (A : Z) (s sl : list Z) (off : Z),
  mem_inv rsegs m -> ro_bytes_b rsegs A (pf_bytes (s ++ [0] ++ sl)) = true ->
  Forall (fun c => 0 < c < 256) s ->
  (- (A + Z.of_nat (length s) + 1)) mod 8 <= Z.of_nat (length sl) ->
  0x10000 <= A -> A + Z.of_nat (length s) + 1 + Z.of_nat (length sl) <= 0x11d40 -> 0 <= off <= cap ->
  pf_arg_ok m (S + -304) lo (buf + off) (cap - off) (Z_to_bv 64 A) (APtr s).
Proof.
  intros m A s sl off MI RB FA HM HA HE Ho. cbn [pf_arg_ok]. rewrite unsigned_lit by lia.
  split; [exact FA|]. exists (pf_bytes sl). rewrite length_pf_bytes.
  split; [|split; [lia|split; [lia|split; lia]]].
  rewrite <- pf_bytes_app, <- app_assoc. apply ro_bytes_at; [exact MI | lia | | apply ro_bytes_b_sound; exact RB].
  rewrite length_pf_bytes, !length_app. cbn [length]. lia.
Qed.

Ltac str_tac sl := intros m off MI Ho; eapply (tj_str m _ _ sl off MI); [vm_compute; reflexivity |
  rewrite Forall_forall; intros c Hc; cbn in Hc; lia | cbn; lia | lia | cbn; lia | exact Ho].

Lemma tj_s_empty : forall m off, mem_inv rsegs m -> 0 <= off <= cap ->
  pf_arg_ok m (S + -304) lo (buf + off) (cap - off) (Z_to_bv 64 0x10323) (APtr []).
Proof. str_tac [46; 0; 110; 117]. Qed.

Lemma tj_s_comma : forall m off, mem_inv rsegs m -> 0 <= off <= cap ->
  pf_arg_ok m (S + -304) lo (buf + off) (cap - off) (Z_to_bv 64 0x1038e) (APtr [44]).
Proof. str_tac (@nil Z). Qed.

Lemma tj_s_unknown : forall m off, mem_inv rsegs m -> 0 <= off <= cap ->
  pf_arg_ok m (S + -304) lo (buf + off) (cap - off) (Z_to_bv 64 0x1031b) (APtr s_unknown).
Proof. str_tac [0; 46; 0; 110; 117]. Qed.

Lemma tj_s_box : forall m off, mem_inv rsegs m -> 0 <= off <= cap ->
  pf_arg_ok m (S + -304) lo (buf + off) (cap - off) (Z_to_bv 64 0x102ad) (APtr s_box).
Proof. str_tac [104; 117; 110; 116; 105; 110; 103]. Qed.

Lemma tj_s_master : forall m off, mem_inv rsegs m -> 0 <= off <= cap ->
  pf_arg_ok m (S + -304) lo (buf + off) (cap - off) (Z_to_bv 64 0x103e6) (APtr s_master).
Proof. str_tac [44; 34; 97]. Qed.

Lemma tj_s_true : forall m off, mem_inv rsegs m -> 0 <= off <= cap ->
  pf_arg_ok m (S + -304) lo (buf + off) (cap - off) (Z_to_bv 64 0x103aa) (APtr s_true).
Proof. str_tac [114]. Qed.

Lemma tj_s_false : forall m off, mem_inv rsegs m -> 0 <= off <= cap ->
  pf_arg_ok m (S + -304) lo (buf + off) (cap - off) (Z_to_bv 64 0x10298) (APtr s_false).
Proof. str_tac [114; 111]. Qed.

Ltac run_to pc :=
  repeat lazymatch goal with
  | |- evt _ _ (MS _ _ (Z_to_bv 64 pc) _ _ _ _) => fail
  | |- evt _ _ (MS _ _ (Z_to_bv 64 _) _ _ _ _) => step
  | |- evt _ _ (MS _ _ (if _ then _ else _) _ _ _ _) => first [if_true | if_false]
  end.

Ltac fk_tac FK1 FK := let k := fresh "k" in let Hk := fresh "Hk" in
  intros k Hk; rewrite FK1 by exact Hk; apply FK; exact Hk.

Lemma tj_P2_len : forall e, (length (P2 e) <= 17)%nat.
Proof.
  intros e. unfold P2, key, qstr, rolename.
  destruct (e_role e =? 1); [|destruct (e_role e =? 2)]; cbn; lia.
Qed.

Lemma tj_u8 : forall k, 0 <= k -> k + 1 <= 400 -> 0 <= u_at T k 1 < 256.
Proof.
  intros k H1 H2. unfold u_at. pose proof (ble_range (sub T k 1)) as H.
  rewrite length_sub in H by (rewrite ?LT; lia). change (2 ^ (8 * Z.of_nat 1)) with 256 in H. exact H.
Qed.

Lemma tj_byte_arg : forall mm D n k, 0 <= k -> k + 1 <= 400 ->
  pf_arg_ok mm (S + -304) lo D n (Z_to_bv 64 (u_at T k 1)) (AInt (u_at T k 1)).
Proof.
  intros mm D n k H1 H2. pose proof (tj_u8 k H1 H2). cbn [pf_arg_ok]. rewrite unsigned_lit by lia.
  split; [lia | reflexivity].
Qed.

Lemma tj_nth_mac : forall i k, 0 <= i < 8 -> (k < 6)%nat ->
  nth k (map bv_unsigned (mac_of T i)) 0 = u_at T (48 * i + Z.of_nat k) 1.
Proof.
  intros i k Hi Hk. unfold mac_of, u_at, sub.
  assert (LL : (k < length (skipn (Z.to_nat (48 * i)) T))%nat) by (rewrite length_skipn, LT; lia).
  destruct (nth_error (skipn (Z.to_nat (48 * i)) T) k) as [b|] eqn:E; [|apply nth_error_None in E; lia].
  replace (Z.to_nat (48 * i + Z.of_nat k)) with (k + Z.to_nat (48 * i))%nat by lia.
  rewrite <- skipn_skipn. rewrite <- (firstn_skipn_step _ k 0 b E). cbn [firstn].
  cbn [bytes_le_to_Z]. rewrite Z.shiftl_0_l, Z.lor_0_r.
  apply nth_error_nth. rewrite nth_error_map, nth_firstn by lia. rewrite E. reflexivity.
Qed.

Lemma tj_P1_eq : forall i, 0 <= i < 8 ->
  P1 (Z.to_nat i) (tj_entry T i) = (if Nat.eqb (Z.to_nat i) 0 then [] else [44]) ++ [123; 34; 109; 97; 99; 34; 58; 34] ++
    hex2 (u_at T (48 * i + 0) 1) ++ [58] ++ hex2 (u_at T (48 * i + 1) 1) ++ [58] ++ hex2 (u_at T (48 * i + 2) 1) ++ [58] ++
    hex2 (u_at T (48 * i + 3) 1) ++ [58] ++ hex2 (u_at T (48 * i + 4) 1) ++ [58] ++ hex2 (u_at T (48 * i + 5) 1) ++ [34].
Proof.
  intros i Hi. unfold P1, key, qstr, mac_text, k_mac. cbn [e_mac tj_entry].
  rewrite !(tj_nth_mac i) by lia. reflexivity.
Qed.

Lemma tj_P1_len : forall n e, (length (P1 n e) <= 28)%nat.
Proof. intros n e. unfold P1, key, qstr, mac_text, hex2, k_mac. destruct (Nat.eqb n 0); cbn; lia. Qed.

Lemma tj_last_range : forall i, 0 <= i < 8 -> 0 <= last_of T i < 2^64.
Proof.
  intros i Hi. unfold last_of, u_at. pose proof (ble_range (sub T (48 * i + 40) 8)) as H.
  rewrite length_sub in H by (rewrite ?LT; lia). change (2 ^ (8 * Z.of_nat 8)) with (2^64) in H. exact H.
Qed.

Lemma tj_age_range : forall i, 0 <= i < 8 -> 0 <= age_of now (last_of T i) < 2^45.
Proof.
  intros i Hi. pose proof (tj_last_range i Hi) as R. unfold age_of.
  destruct (last_of T i <? now) eqn:E; [|lia]. apply Z.ltb_lt in E.
  split; [apply Z.div_pos; lia|]. apply Z.div_lt_upper_bound; lia.
Qed.

Lemma tj_mem_merge : forall w0 w1 j rest acc m,
  tj_mem (C8 w0 :: C8 w1 :: CB 8 j :: tj_ptrs ++ rest) acc m ->
  exists j0, tj_mem (CB 24 j0 :: tj_ptrs ++ rest) acc m.
Proof.
  intros w0 w1 j rest acc m (FR & R).
  pose proof (rw_cells_merge rsegs m (S + -304) [] [C8 w0; C8 w1; CB 8 j] (tj_ptrs ++ rest) FR) as FR'.
  eexists. split; [exact FR' | exact R].
Qed.

Lemma tj_age_merge : forall j0 a jb acc m,
  tj_mem (tj_loa j0 a jb ++ tj_sv) acc m -> exists jb', tj_mem (tj_lo j0 jb' ++ tj_sv) acc m.
Proof.
  intros j0 a jb acc m (FR & R). unfold tj_loa in FR. cbn [app] in FR.
  pose proof (rw_cells_merge rsegs m (S + -304) (CB 24 j0 :: tj_ptrs) [C8 (Z_to_bv 64 a); CB 96 jb] tj_sv) as FR'.
  cbn [app] in FR'. specialize (FR' FR). cbn [cells_size csize Nat.add] in FR'.
  eexists. split; [unfold tj_lo; cbn [app]; exact FR' | exact R].
Qed.

Lemma tj_jb : forall m w0 w1 j a jb,
  rw_cells rsegs m (S + -304) (C8 w0 :: C8 w1 :: CB 8 j :: tj_ptrs ++ C8 (Z_to_bv 64 a) :: CB 96 jb :: tj_sv) ->
  stk rsegs m (S + -200) (S + -104).
Proof.
  intros m w0 w1 j a jb FR.
  destruct (proj1 (rw_cells_app m (S + -304) (C8 w0 :: C8 w1 :: CB 8 j :: tj_ptrs ++ [C8 (Z_to_bv 64 a)])
                    (CB 96 jb :: tj_sv)) FR) as [_ FB].
  destruct (proj1 (rw_cells_app m _ [CB 96 jb] tj_sv) FB) as [FJ _].
  apply rwc_stk in FJ. cbn [cells_size csize Nat.add app] in FJ.
  replace (S + -200) with (S + -304 + Z.of_nat 104) by lia.
  replace (S + -104) with (S + -304 + Z.of_nat 104 + Z.of_nat 96) by lia.
  exact FJ.
Qed.

Lemma tj_jb2 : forall m j0 a jb, rw_cells rsegs m (S + -304) (tj_loa j0 a jb ++ tj_sv) -> stk rsegs m (S + -200) (S + -104).
Proof.
  intros m j0 a jb FR. unfold tj_loa in FR. cbn [app] in FR.
  destruct (proj1 (rw_cells_app m (S + -304) (CB 24 j0 :: tj_ptrs ++ [C8 (Z_to_bv 64 a)]) (CB 96 jb :: tj_sv))
                    ltac:(cbn [app]; exact FR)) as [_ FB].
  destruct (proj1 (rw_cells_app m _ [CB 96 jb] tj_sv) FB) as [FJ _].
  apply rwc_stk in FJ. cbn [cells_size csize Nat.add app] in FJ.
  replace (S + -200) with (S + -304 + Z.of_nat 104) by lia.
  replace (S + -104) with (S + -304 + Z.of_nat 104 + Z.of_nat 96) by lia.
  exact FJ.
Qed.

Ltac bn_cs sl := split; [rewrite Forall_forall; intros c Hc; cbn in Hc; lia
                        | exists (pf_bytes sl); split; [img | split; [cbn; lia | simpl; dj_tac]]].

Lemma tj_bn_image : forall m lo' hi', mem_inv rsegs m -> bytes_at rsegs m BN_TS bn_table -> 0x53000 <= lo' ->
  bn_image m lo' hi'.
Proof.
  intros m lo' hi' MI BT Hl. unfold bn_image, BN_S1, BN_S2, BN_S3, BN_REAC, BN_PAREN, BN_IN, BN_OUT, BN_TS in *.
  split; [exact BT|]. split; [dj_tac|].
  split; [bn_cs [44; 34]|]. split; [bn_cs [105; 110; 102; 0; 32]|]. split; [bn_cs [255; 255; 255; 255; 255]|].
  split; [bn_cs [47]|].
  split; [split; [img | simpl; dj_tac]|]. split; [split; [img | simpl; dj_tac]|]. split; [img | simpl; dj_tac].
Qed.

Lemma tj_box_mem : forall (w0 w1 : word) j a jb acc m m' x y z,
  tj_mem (C8 w0 :: C8 w1 :: CB 8 j :: tj_ptrs ++ C8 (Z_to_bv 64 a) :: CB 96 jb :: tj_sv) acc m ->
  Z.of_nat (length acc) < cap ->
  0 <= x <= 24 -> 0 <= y <= 24 -> 0 <= z <= 48 ->
  munch [(S + -720, S + -304); (S + -128, S + -128 + x); (S + -152, S + -152 + y); (S + -200, S + -200 + z)] m m' ->
  wmono rsegs m m' -> mem_inv rsegs m' -> stk rsegs m' lo (S + -304) ->
  (forall q, S + -200 <= q < S + -104 ->
     outside [(S + -720, S + -304); (S + -128, S + -128 + x); (S + -152, S + -152 + y); (S + -200, S + -200 + z)] q \/
     exists v, mrd rsegs m' (wa q) = Some v) ->
  exists j0 jb', tj_mem (tj_loa j0 a jb' ++ tj_sv) acc m'.
Proof.
  intros w0 w1 j a jb acc m m' x y z TM HL Hx Hy Hz MU' WM' MI' ST' RD.
  pose proof (tj_jb m w0 w1 j a jb (proj1 TM)) as SJ.
  destruct TM as (FR & ST & HT & BNT & GG & GD & MI & WM & MU & SB & BA).
  pose proof length_bn_table as LBN.
  assert (LPB : length (pf_bytes acc) = length acc) by apply length_pf_bytes.
  destruct (proj1 (rw_cells_app m (S + -304) (C8 w0 :: C8 w1 :: CB 8 j :: tj_ptrs ++ [C8 (Z_to_bv 64 a)])
                    (CB 96 jb :: tj_sv)) FR) as [FA FB].
  destruct (proj1 (rw_cells_app m _ [CB 96 jb] tj_sv) FB) as [_ FS].
  cbn [cells_size csize Nat.add app] in FA, FB, FS.
  assert (SJ' : stk rsegs m' (S + -200) (S + -200 + Z.of_nat 96)).
  { replace (S + -200 + Z.of_nat 96) with (S + -104) by lia.
    eapply stk_tr; [exact SJ | exact MU' | exact WM' | exact RD]. }
  destruct (stk_cb m' (S + -200) 96 SJ') as [jb' FJ'].
  assert (FR' : rw_cells rsegs m' (S + -304)
                  ((C8 w0 :: C8 w1 :: CB 8 j :: tj_ptrs ++ [C8 (Z_to_bv 64 a)]) ++ CB 96 jb' :: tj_sv)).
  { apply (proj2 (rw_cells_app m' (S + -304) (C8 w0 :: C8 w1 :: CB 8 j :: tj_ptrs ++ [C8 (Z_to_bv 64 a)])
                    (CB 96 jb' :: tj_sv))). split.
    - eapply rw_cells_transport; [exact FA | exact MU' | exact WM' | cbn [cells_size csize Nat.add app]; dj_tac].
    - apply (proj2 (rw_cells_app m' _ [CB 96 jb'] tj_sv)). cbn [cells_size csize Nat.add app]. split.
      + replace (S + -304 + Z.of_nat 104) with (S + -200) by lia. exact FJ'.
      + eapply rw_cells_transport; [exact FS | exact MU' | exact WM' | cbn [cells_size csize Nat.add]; dj_tac]. }
  cbn [app] in FR'.
  cut (tj_mem (C8 w0 :: C8 w1 :: CB 8 j :: tj_ptrs ++ C8 (Z_to_bv 64 a) :: CB 96 jb' :: tj_sv) acc m').
  { intros TM'. destruct (tj_mem_merge _ _ _ _ _ _ TM') as [j0' TM'']. exists j0', jb'.
    unfold tj_loa. cbn [app]. exact TM''. }
  unfold tj_mem.
  split; [exact FR'|]. split; [exact ST'|].
  split; [eapply bytes_at_transport; [exact HT | exact MU' | rewrite LT; dj_tac]|].
  split; [eapply bytes_at_transport; [exact BNT | exact MU' | rewrite LBN; dj_tac]|].
  split; [eapply bytes_at_transport; [exact GG | exact MU' | rewrite length_le8; dj_tac]|].
  split; [eapply bytes_at_transport; [exact GD | exact MU' | rewrite length_le8; dj_tac]|].
  split; [exact MI'|].
  split; [eapply wmono_trans; [exact WM | exact WM']|].
  split; [eapply munch_trans; [exact MU | eapply munch_weaken; [|exact MU']]; fp_tac|].
  split; [eapply stk_tr; [exact SB | exact MU' | exact WM' |]; intros q Hq; left; cbn [outside]; repeat split; try exact I; lia|].
  eapply bytes_at_transport; [exact BA | exact MU' | rewrite LPB; dj_tac].
Qed.

Local Abbreviation tj_L1 := [44; 34; 109; 111; 100; 101; 108; 34; 58; 34; 117; 110; 107; 110; 111; 119; 110; 34].
Local Abbreviation tj_L2 := [44; 34; 119; 105; 100; 116; 104; 34; 58; 34; 48; 120; 48; 34].

Ltac snp_check := step; rewrite lts_lit by lia; if_false; step; rewrite ltu_lit by lia.

Ltac wq_tac := rewrite ?length_app in *; cbn [length] in *; repeat rewrite unsigned_lit by lia; f_equal; lia.

Lemma tj_snez : forall b, 0 < b < 2^64 -> v_sltu (Z_to_bv 64 0) (Z_to_bv 64 b) = Z_to_bv 64 1.
Proof.
  intros b Hb. rewrite v_sltu_b2z, !unsigned_lit by lia. rewrite (proj2 (Z.ltb_lt 0 b)) by lia. reflexivity.
Qed.

Lemma tj_seqz : forall x, 0 < x < 2^64 -> v_sltiu (Z_to_bv 64 x) 1 = Z_to_bv 64 0.
Proof.
  intros x Hx. rewrite v_sltiu_b2z, unsigned_lit by lia. change (bv_wrap 64 1) with 1.
  rewrite (proj2 (Z.ltb_ge x 1)) by lia. reflexivity.
Qed.

Ltac pck := step; step; rewrite ltu_lit by lia; if_false; step; step; step; rewrite tj_seqz by lia; if_false.

Ltac pck8 := step; rewrite ltu_lit by lia; if_false; step; step; step; rewrite tj_seqz by lia; if_false.

Lemma tj_end : forall (pre : list cell) (acc : list Z) (m : word -> option byte) (F : bvmap 5 word) (fc : bv 32)
    (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x19 x20 x21 x22 x23 x25 x26 x27 x28 x29 x30 x31 : word),
  tj_mem (pre ++ tj_sv) acc m -> cells_size pre = 200%nat -> Z.of_nat (length acc) < cap ->
  tj_text T now = acc ++ [93] -> frm0 fc -> (forall k : reg, bv_unsigned k <> 10 -> reg_get F k = reg_get F0 k) ->
  evt rsegs tj_post (MS (mkR x1 (Z_to_bv 64 (S + -304)) gp tp x5 x6 x7 (Z_to_bv 64 (-1)) (Z_to_bv 64 cap)
                             x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 buf) x19 x20 x21 x22 x23
                             (Z_to_bv 64 (Z.of_nat (length acc))) x25 x26 x27 x28 x29 x30 x31)
                        F (Z_to_bv 64 0x16018) fc None m (seg_rom rsegs)).
Proof.
  intros pre acc m F fc x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x19 x20 x21 x22 x23 x25 x26 x27 x28 x29 x30 x31
    TM Hp Hl RT FC FK.
  pose proof TM as (FR & ST & HT & BNT & GG & GD & MI & WM & MU & SB & BA).
  assert (Lq : tj_len = Z.of_nat (length acc) + 1) by (unfold tj_len; rewrite RT, length_app; cbn [length]; lia).
  assert (Hcs : cells_size (pre ++ tj_sv) = 304%nat) by (rewrite cells_size_app, Hp; reflexivity).
  step. step.
  rewrite ltu_lit by lia. if_false.
  step. step. step. step.
  rewrite tj_snez, tj_seqz by lia. if_false.
  do 5 step.
  eapply tj_call with (A := 0x10427) (fmt := [93]) (ps := [PLit 93]) (args := []) (q := [93]) (ret := 0x16044).
  { exact TM. }
  { exact Hcs. }
  { exact Hl. }
  { img. }
  { unfold RO_LO. lia. }
  { unfold RO_END. cbn [length]. lia. }
  { reflexivity. }
  { exact I. }
  { reflexivity. }
  { cbn [length]. lia. }
  { exact FC. }
  { reflexivity. }
  { lia. }
  { reflexivity. }
  2: { wq_tac. }
  2: { wq_tac. }
  2: { wq_tac. }
  intros m1 F1 fc1 y5 y6 y7 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31 TM1 BY1 FC1 FK1.
  change (Z.of_nat (length [93])) with 1.
  step. rewrite lts_lit by lia. if_false.
  step. rewrite (unsigned_lit cap), (unsigned_lit (Z.of_nat (length acc))) by lia. rewrite ltu_lit by lia.
  destruct (Z.ltb_spec 1 (cap - Z.of_nat (length acc))) as [OK|BAD]; cbn [negb].
  2: { eapply tj_fail; [exact TM1 | exact Hp | rewrite length_app, length_firstn; cbn [length]; lia | lia | exact FC1 |].
       intros k Hk. rewrite FK1 by exact Hk. apply FK. exact Hk. }
  rewrite firstn_all2 in TM1, BY1 by (cbn [length]; lia).
  step. step.
  rewrite (unsigned_lit (Z.of_nat (length acc))) by lia.
  rewrite swrap32_small by lia.
  eapply tj_exit2; [exact TM1 | exact Hp | exact FC1 | intros k Hk; rewrite FK1 by exact Hk; apply FK; exact Hk |].
  destruct TM1 as (FR1 & ST1 & HT1 & BNT1 & GG1 & GD1 & MI1 & WM1 & MU1 & SB1 & BA1).
  unfold tj_res. split; [intros; lia|]. split; [|intros; lia].
  intros _ _. split; [lia|]. split.
  - rewrite length_app in MU1. cbn [length] in MU1. rewrite Lq. eapply munch_weaken; [|exact MU1]. fp_tac.
  - rewrite RT, <- app_assoc, pf_bytes_app. apply bytes_at_app. split.
    + rewrite pf_bytes_app in BA1. apply bytes_at_app in BA1. exact (proj1 BA1).
    + rewrite length_pf_bytes. exact BY1.
Qed.

Lemma tj_unk : forall (i : Z) (acc rest : list Z) (m : word -> option byte) (F : bvmap 5 word) (fc : bv 32)
    (a : Z) (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x25 x28 x29 x30 x31 : word),
  0 <= i < n_of T -> tj_oka acc a m F fc -> tj_text T now = acc ++ tj_L1 ++ tj_L2 ++ rest ->
  tj_K i (acc ++ tj_L1 ++ tj_L2) a ->
  evt rsegs tj_post (tj_st i 0x15ea8 F fc m x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17
                       (Z_to_bv 64 (t + 48 * i)) (Z_to_bv 64 (Z.of_nat (length acc)))
                       (Z_to_bv 64 (Z.of_nat (length acc) + buf)) x25 x28 x29 x30 x31).
Proof.
  intros i acc rest m F fc a x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x25 x28 x29 x30 x31 Hi OK TX K.
  destruct OK as ((j0 & jb & TM) & Hl & FC & FK).
  pose proof TM as (FR & ST & HT & BNT & GG & GD & MI & WM & MU & SB & BA).
  assert (LT2 : Z.of_nat (length (tj_text T now)) = Z.of_nat (length acc) + 32 + Z.of_nat (length rest))
    by (rewrite TX, !length_app; cbn [length]; lia).
  unfold tj_st. pck8.
  run_to 0x19d00.
  eapply tj_call with (cs := tj_loa j0 a jb ++ tj_sv) (acc := acc) (A := 0x102d3) (fmt := tj_L1)
    (ps := [PLit 44; PLit 34; PLit 109; PLit 111; PLit 100; PLit 101; PLit 108; PLit 34; PLit 58; PLit 34; PLit 117;
            PLit 110; PLit 107; PLit 110; PLit 111; PLit 119; PLit 110; PLit 34])
    (args := []) (q := tj_L1) (ret := 0x15ed0);
    [ exact TM | reflexivity | exact Hl | img | unfold RO_LO; lia | unfold RO_END; cbn [length]; lia | reflexivity
    | exact I | reflexivity | cbn [length]; lia | exact FC | reflexivity | lia | reflexivity | | wq_tac | wq_tac
    | reflexivity ].
  intros m1 F1 fc1 y5 y6 y7 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31 TM1 BY1 FC1 FK1.
  change (Z.of_nat (length tj_L1)) with 18 in *.
  step. rewrite lts_lit by lia. if_false.
  step. rewrite (unsigned_lit cap), (unsigned_lit (Z.of_nat (length acc))) by lia. rewrite ltu_lit by lia.
  destruct (Z.ltb_spec 18 (cap - Z.of_nat (length acc))) as [OK1|BAD]; cbn [negb].
  2: { eapply tj_fail; [exact TM1 | reflexivity | rewrite length_app, length_firstn; lia
                       | unfold tj_len; lia | exact FC1 | fk_tac FK1 FK]. }
  rewrite firstn_all2 in TM1 by (cbn [length]; lia).
  pose proof TM1 as (FR1 & ST1 & HT1 & BNT1 & GG1 & GD1 & MI1 & WM1 & MU1 & SB1 & BA1).
  step. pck.
  run_to 0x19d00.
  eapply tj_call with (cs := tj_loa j0 a jb ++ tj_sv) (acc := acc ++ tj_L1) (A := 0x10444) (fmt := tj_L2)
    (ps := [PLit 44; PLit 34; PLit 119; PLit 105; PLit 100; PLit 116; PLit 104; PLit 34; PLit 58; PLit 34; PLit 48;
            PLit 120; PLit 48; PLit 34])
    (args := []) (q := tj_L2) (ret := 0x15f04);
    [ exact TM1 | reflexivity | rewrite length_app; cbn [length] in *; lia | img | unfold RO_LO; lia
    | unfold RO_END; cbn [length]; lia | reflexivity | exact I | reflexivity | cbn [length]; lia | exact FC1
    | reflexivity | lia | reflexivity | | wq_tac | wq_tac | reflexivity ].
  intros m2 F2 fc2 z5 z6 z7 z11 z12 z13 z14 z15 z16 z17 z28 z29 z30 z31 TM2 BY2 FC2 FK2.
  change (Z.of_nat (length tj_L2)) with 14 in *.
  step. rewrite lts_lit by lia. if_false. step. step.
  rewrite (unsigned_lit cap), (unsigned_lit (Z.of_nat (length acc) + 18)) by lia. rewrite ltu_lit by lia.
  destruct (Z.ltb_spec 14 (cap - (Z.of_nat (length acc) + 18))) as [OK2|BAD]; cbn [negb].
  2: { eapply tj_fail; [exact TM2 | reflexivity | rewrite !length_app, length_firstn; cbn [length] in *; lia
                       | unfold tj_len; rewrite length_app in *; cbn [length] in *; lia | exact FC2
                       | intros k Hk; rewrite FK2, FK1 by exact Hk; apply FK; exact Hk]. }
  rewrite firstn_all2 in TM2 by (rewrite ?length_app; cbn [length]; lia). rewrite <- app_assoc in TM2.
  eapply K; [split; [exists j0, jb; exact TM2|] | | | ].
  - split; [rewrite !length_app in *; cbn [length] in *; lia|]. split; [exact FC2|].
    intros k Hk; rewrite FK2, FK1 by exact Hk; apply FK; exact Hk.
  - lia.
  - lia.
  - rewrite !length_app; cbn [length]; lia.
Qed.

Lemma tj_model : forall (i : Z) (acc rest : list Z) (m : word -> option byte) (F : bvmap 5 word) (fc : bv 32)
    (a : Z) (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x25 x28 x29 x30 x31 : word),
  0 <= i < n_of T -> hd_of T i = 1 -> tj_oka acc a m F fc ->
  bn_ret (u_at T (48 * i + 15) 1) [] (u_at T (48 * i + 13) 1) (u_at T (48 * i + 14) 1) = 0 ->
  bytes_at rsegs m (S + -152)
    (pf_bytes (bn_TK (bn_NM (u_at T (48 * i + 15) 1) [] (u_at T (48 * i + 13) 1) (u_at T (48 * i + 14) 1)) ++ [0])) ->
  tj_text T now = acc ++ P3 box_tok (tj_entry T i) ++ P4 box_tok (tj_entry T i) ++ rest ->
  tj_K i (acc ++ P3 box_tok (tj_entry T i) ++ P4 box_tok (tj_entry T i)) a ->
  evt rsegs tj_post (tj_st i 0x15f0c F fc m x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17
                       (Z_to_bv 64 (t + 48 * i)) (Z_to_bv 64 (Z.of_nat (length acc)))
                       (Z_to_bv 64 (Z.of_nat (length acc) + buf)) x25 x28 x29 x30 x31).
Proof.
  intros i acc rest m F fc a x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x25 x28 x29 x30 x31 Hi HD OK BR BTK TX K.
  destruct OK as ((j0 & jb & TM) & Hl & FC & FK).
  pose proof TM as (FR & ST & HT & BNT & GG & GD & MI & WM & MU & SB & BA).
  pose proof TOK as (T1 & T2 & T3 & T4). unfold tbl_T1 in T1.
  pose proof (tj_jb2 m j0 a jb FR) as SJ.
  set (fa := u_at T (48 * i + 15) 1) in *. set (da := u_at T (48 * i + 13) 1) in *. set (db := u_at T (48 * i + 14) 1) in *.
  pose proof (tj_u8 (48 * i + 13) ltac:(lia) ltac:(lia)) as U13. pose proof (tj_u8 (48 * i + 14) ltac:(lia) ltac:(lia)) as U14.
  fold da in U13. fold db in U14.
  destruct (tj_box_ok fa da db BR) as (Ea & Eb & Ez).
  destruct (bn_c17 fa da db Ea Eb Ez) as (_ & LNM & LTK & LDP & CTK). cbv zeta in LNM, LTK, LDP, CTK.
  set (tk := bn_TK (bn_NM fa [] da db)) in *.
  assert (EM : fst (model_of box_tok (tj_entry T i)) = tk /\ snd (model_of box_tok (tj_entry T i)) = dec da ++ [120] ++ dec db).
  { unfold model_of, tj_entry, box_tok, din_of, dout_of. cbn [e_has_decl e_family e_decl_in e_decl_out].
    change (u_at T (48 * i + 12) 1) with (hd_of T i). rewrite HD. fold fa da db. rewrite BR. cbn. split; reflexivity. }
  destruct EM as [EM3 EM4].
  assert (LP3 : length (P3 box_tok (tj_entry T i)) = (11 + length tk)%nat)
    by (unfold P3, key, qstr, k_model; rewrite EM3, !length_app; cbn [length]; lia).
  assert (LP4 : (length (P4 box_tok (tj_entry T i)) <= 60)%nat)
    by (unfold P4, key, qstr, k_width; rewrite EM4, !length_app; cbn [length];
        pose proof (dec_len da); pose proof (dec_len db); lia).
  destruct (stk_cb m (S + -152 + Z.of_nat (length (pf_bytes (tk ++ [0])))) 8) as [sl SL].
  { eapply stk_sub; [exact SJ | | | ]; rewrite length_pf_bytes, length_app; cbn [length]; lia. }
  destruct (rwc_cb _ _ _ _ SL) as [LSL BSL].
  unfold tj_st.
  pck8.
  run_to 0x19d00.
  pose proof (tok_rng tk CTK) as CR.
  eapply tj_call with (cs := tj_loa j0 a jb ++ tj_sv) (acc := acc) (A := 0x10436)
    (fmt := [44; 34; 109; 111; 100; 101; 108; 34; 58; 34; 37; 115; 34])
    (ps := [PLit 44; PLit 34; PLit 109; PLit 111; PLit 100; PLit 101; PLit 108; PLit 34; PLit 58; PLit 34; Ps; PLit 34])
    (args := [APtr tk]) (q := P3 box_tok (tj_entry T i)) (ret := 0x15f38);
    [ exact TM | reflexivity | exact Hl | img | unfold RO_LO; lia | unfold RO_END; cbn [length]; lia | reflexivity
    | | unfold P3; rewrite EM3; reflexivity
    | rewrite LP3; lia | exact FC | reflexivity | lia | reflexivity | | wq_tac | wq_tac | first [reflexivity | wq_tac] ].
  { cbn [pf_args_ok pf_arg_ok]. split; [|exact I]. split; [exact CR|].
    exists sl. rewrite unsigned_lit by lia.
    split; [apply bytes_at_app; split; [exact BTK | exact BSL]|].
    rewrite LSL. pose proof (Z.mod_pos_bound (- (S + -152 + Z.of_nat (length tk) + 1)) 8 ltac:(lia)).
    split; [lia|]. split; [lia|]. split; [lia|]. lia. }
  intros m1 F1 fc1 y5 y6 y7 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31 TM1 BY1 FC1 FK1.
  step; rewrite lts_lit by lia; if_false.
  step. rewrite (unsigned_lit cap), (unsigned_lit (Z.of_nat (length acc))) by lia. rewrite ltu_lit by lia.
  destruct (Z.ltb_spec (Z.of_nat (length (P3 box_tok (tj_entry T i)))) (cap - Z.of_nat (length acc))) as [OK3|BAD];
    cbn [negb].
  2: { eapply tj_fail; [exact TM1 | reflexivity | rewrite length_app, length_firstn; lia
                       | unfold tj_len; rewrite TX, !length_app; lia | exact FC1 | fk_tac FK1 FK]. }
  rewrite firstn_all2 in TM1 by lia.
  pose proof TM1 as (FR1 & ST1 & HT1 & _ & _ & _ & MI1 & _).
  assert (RM : forall k, 13 <= k < 15 -> ov_read_bytes rsegs m1 (Z_to_bv 64 (t + (48 * i + k))) 1 = Some (sub T (48 * i + k) 1))
    by (intros k Hk; apply rd_sub; [exact HT1 | lia | rewrite LT; lia]).
  pose proof (RM 13 ltac:(lia)) as RM13. pose proof (RM 14 ltac:(lia)) as RM14. clear RM.
  step.
  pck.
  run_to 0x19d00.
  rewrite !lbu_val by (apply length_sub; [lia | rewrite LT; lia]).
  assert (D10 : forall v, 0 <= v < 256 -> 0 <= v < 10 ^ 10)
    by (intros v Hv; split; [lia | apply Z.lt_le_trans with 256; [lia | apply Z.leb_le; reflexivity]]).
  eapply tj_call with (cs := tj_loa j0 a jb ++ tj_sv) (acc := acc ++ P3 box_tok (tj_entry T i)) (A := 0x103b7)
    (fmt := [44; 34; 119; 105; 100; 116; 104; 34; 58; 34; 37; 100; 120; 37; 100; 34])
    (ps := [PLit 44; PLit 34; PLit 119; PLit 105; PLit 100; PLit 116; PLit 104; PLit 34; PLit 58; PLit 34; Pd; PLit 120;
            Pd; PLit 34])
    (args := [AInt da; AInt db]) (q := P4 box_tok (tj_entry T i)) (ret := 0x15f74);
    [ exact TM1 | reflexivity | rewrite length_app; lia | img | unfold RO_LO; lia | unfold RO_END; cbn [length]; lia
    | reflexivity
    | cbn [pf_args_ok]; split; [apply tj_byte_arg; lia | split; [apply tj_byte_arg; lia | exact I]]
    | unfold P4, qstr; rewrite EM4; rewrite (dec_pfdec da), (dec_pfdec db) by (apply D10; lia);
      rewrite <- !app_assoc; reflexivity
    | lia | exact FC1 | reflexivity | lia | reflexivity | | wq_tac | wq_tac | first [reflexivity | wq_tac] ].
  intros m2 F2 fc2 z5 z6 z7 z11 z12 z13 z14 z15 z16 z17 z28 z29 z30 z31 TM2 BY2 FC2 FK2.
  step; rewrite lts_lit by lia; if_false.
  step. rewrite (unsigned_lit cap), (unsigned_lit (Z.of_nat (length acc) + Z.of_nat (length (P3 box_tok (tj_entry T i)))))
    by lia.
  rewrite ltu_lit by lia.
  destruct (Z.ltb_spec (Z.of_nat (length (P4 box_tok (tj_entry T i))))
              (cap - (Z.of_nat (length acc) + Z.of_nat (length (P3 box_tok (tj_entry T i)))))) as [OK4|BAD]; cbn [negb].
  2: { eapply tj_fail; [exact TM2 | reflexivity | rewrite !length_app, length_firstn; lia
                       | unfold tj_len; rewrite TX, !length_app; lia | exact FC2
                       | intros k Hk; rewrite FK2, FK1 by exact Hk; apply FK; exact Hk]. }
  rewrite firstn_all2 in TM2 by (rewrite ?length_app; lia). rewrite <- app_assoc in TM2.
  eapply K with (o1' := Z.of_nat (length acc) + Z.of_nat (length (P3 box_tok (tj_entry T i))));
    [ split; [exists j0, jb; exact TM2 | split; [rewrite !length_app; lia | split; [exact FC2 |]]] | lia | lia
    | rewrite !length_app; lia ].
  intros k Hk; rewrite FK2, FK1 by exact Hk; apply FK; exact Hk.
Qed.

Lemma tj_decl : forall (i : Z) (acc rest : list Z) (m : word -> option byte) (F : bvmap 5 word) (fc : bv 32)
    (a : Z) (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x25 x28 x29 x30 x31 : word),
  0 <= i < n_of T -> hd_of T i = 1 -> tj_oka acc a m F fc ->
  tj_text T now = acc ++ P3 box_tok (tj_entry T i) ++ P4 box_tok (tj_entry T i) ++ rest ->
  tj_K i (acc ++ P3 box_tok (tj_entry T i) ++ P4 box_tok (tj_entry T i)) a ->
  evt rsegs tj_post (tj_st i 0x15e70 F fc m x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17
                       (Z_to_bv 64 (t + 48 * i)) (Z_to_bv 64 (Z.of_nat (length acc)))
                       (Z_to_bv 64 (Z.of_nat (length acc) + buf)) x25 x28 x29 x30 x31).
Proof.
  intros i acc rest m F fc a x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x25 x28 x29 x30 x31 Hi HD OK TX K.
  pose proof OK as ((j0 & jb & TM) & Hl & FC & FK).
  pose proof TM as (FR & ST & HT & BNT & GG & GD & MI & WM & MU & SB & BA).
  pose proof TOK as (T1 & T2 & T3 & T4). unfold tbl_T1 in T1.
  assert (RM : forall k, 13 <= k < 16 -> ov_read_bytes rsegs m (Z_to_bv 64 (t + (48 * i + k))) 1 = Some (sub T (48 * i + k) 1))
    by (intros k Hk; apply rd_sub; [exact HT | lia | rewrite LT; lia]).
  pose proof (RM 13 ltac:(lia)) as RM13. pose proof (RM 14 ltac:(lia)) as RM14. pose proof (RM 15 ltac:(lia)) as RM15.
  clear RM.
  pose proof (tj_u8 (48 * i + 13) ltac:(lia) ltac:(lia)) as U13. pose proof (tj_u8 (48 * i + 14) ltac:(lia) ltac:(lia)) as U14.
  pose proof (tj_u8 (48 * i + 15) ltac:(lia) ltac:(lia)) as U15.
  pose proof length_bn_table as LBN.
  assert (LPB : length (pf_bytes acc) = length acc) by apply length_pf_bytes.
  unfold tj_loa in FR. cbn [app] in FR.
  unfold tj_st. run_to 0x14e14.
  rewrite !lbu_val by (apply length_sub; [lia | rewrite LT; lia]).
  change (bytes_le_to_Z (sub T (48 * i + 13) 1)) with (u_at T (48 * i + 13) 1).
  change (bytes_le_to_Z (sub T (48 * i + 14) 1)) with (u_at T (48 * i + 14) 1).
  change (bytes_le_to_Z (sub T (48 * i + 15) 1)) with (u_at T (48 * i + 15) 1).
  set (fa := u_at T (48 * i + 15) 1) in *. set (da := u_at T (48 * i + 13) 1) in *. set (db := u_at T (48 * i + 14) 1) in *.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => rename mm into mB end.
  assert (TMB : tj_mem (C8 (Z_to_bv 64 (S + -200)) :: C8 (Z_to_bv 64 48) :: CB 8 (skipn 8 (skipn 8 j0)) :: tj_ptrs ++
                        C8 (Z_to_bv 64 a) :: CB 96 jb :: tj_sv) acc mB)
    by (unfold tj_mem; repeat (split; [eassumption|]); eassumption).
  pose proof TMB as (FRB & STB & _ & BNTB & _ & _ & MIB & _).
  eapply evt_cut.
  { eapply BOX with (lo := lo) (f := fa) (i := da) (o := db) (display := Z_to_bv 64 (S + -200))
      (display_len := Z_to_bv 64 48) (sd := []);
      [ reflexivity | lia | reflexivity | lia | reflexivity | lia
      | rewrite (unsigned_lit (S + -304)) by lia; eapply tj_c8c8; exact FRB
      | rewrite (unsigned_lit (S + -304)) by lia; exact STB
      | rewrite (unsigned_lit (S + -304)) by lia; unfold BN_K; lia
      | rewrite (unsigned_lit (S + -304)) by lia; replace (S + -304) with (S + (-19) * 16) by lia;
        rewrite Z_mod_plus_full; exact RS16
      | rewrite (unsigned_lit (S + -304)) by lia; apply tj_bn_image; [exact MIB | exact BNTB | unfold BN_K; lia]
      |
      | exact MIB ].
    intros _. repeat (rewrite unsigned_lit by lia). split; [left; split; reflexivity|].
    pose proof (tj_jb _ _ _ _ _ _ FRB) as SJ. unfold bn_bufs.
    change (Z.min 24 24) with 24. change (Z.min 48 48) with 48. change (Z.to_nat 24) with 24%nat.
    change (Z.to_nat 48) with 48%nat.
    split; [apply stk_cb; eapply stk_sub; [exact SJ | lia | lia | lia]|].
    split; [apply stk_cb; eapply stk_sub; [exact SJ | lia | lia | lia]|].
    split; [apply stk_cb; eapply stk_sub; [exact SJ | lia | lia | lia]|].
    split; [dj_tac|]. split; [dj_tac|]. dj_tac. }
  intros ms' (y5 & y6 & y7 & y10 & y11 & y12 & y13 & y14 & y15 & y16 & y17 & y28 & y29 & y30 & y31 & m3 & E & WM3 & MI3
              & ST3 & ACC).
  subst ms'.
  repeat (rewrite unsigned_lit in ACC by lia). rewrite (unsigned_lit (S + -304)) in ST3 by lia.
  rewrite (ret_pc_even 89764) by (first [lia | reflexivity]).
  unfold BN_K in ACC.
  destruct (Z.eqb_spec (bn_ret fa [] da db) 0) as [BR|BR].
  - rewrite tj_accept in ACC by (first [exact BR | lia]).
    destruct ACC as (A0 & MU3 & BN1 & BN2 & BN3). subst y10.
    destruct (tj_box_ok fa da db BR) as (Ea & Eb & Ez).
    destruct (bn_c17 fa da db Ea Eb Ez) as (_ & LNM & LTK & LDP & _). cbv zeta in LNM, LTK, LDP.
    destruct (tj_box_mem _ _ _ _ _ acc mB m3 (Z.of_nat (length (bn_NM fa [] da db)) + 1)
                (Z.of_nat (length (bn_TK (bn_NM fa [] da db))) + 1)
                (Z.of_nat (length (bn_DP (bn_NM fa [] da db) da db)) + 1) TMB Hl ltac:(lia) ltac:(lia) ltac:(lia))
      as (j0' & jb' & TM3);
      [ eapply munch_weaken; [|exact MU3]; fp_tac | exact WM3 | exact MI3 | exact ST3 | |].
    { intros x Hx.
      assert (LB : forall s, length (bn_bytes s) = length s) by (intros s; unfold bn_bytes; apply length_map).
      destruct (Z_lt_le_dec x (S + -152)) as [X1|X1]; [|destruct (Z_lt_le_dec x (S + -128)) as [X2|X2]].
      - destruct (Z_lt_le_dec x (S + -200 + (Z.of_nat (length (bn_DP (bn_NM fa [] da db) da db)) + 1))) as [Y|Y].
        + right. eapply bytes_at_mrd; [exact BN3 | rewrite LB, length_app; cbn [length]; lia].
        + left. cbn [outside]. repeat split; try exact I; lia.
      - destruct (Z_lt_le_dec x (S + -152 + (Z.of_nat (length (bn_TK (bn_NM fa [] da db))) + 1))) as [Y|Y].
        + right. eapply bytes_at_mrd; [exact BN2 | rewrite LB, length_app; cbn [length]; lia].
        + left. cbn [outside]. repeat split; try exact I; lia.
      - destruct (Z_lt_le_dec x (S + -128 + (Z.of_nat (length (bn_NM fa [] da db)) + 1))) as [Y|Y].
        + right. eapply bytes_at_mrd; [exact BN1 | rewrite LB, length_app; cbn [length]; lia].
        + left. cbn [outside]. repeat split; try exact I; lia. }
    step.
    eapply tj_model; [exact Hi | exact HD | split; [exists j0', jb'; exact TM3 | split; [exact Hl | split; [exact FC | exact FK]]]
                     | exact BR | exact BN2 | exact TX | exact K].
  - rewrite tj_reject in ACC by exact BR.
    destruct ACC as (A0 & MU3). subst y10.
    destruct (tj_box_mem _ _ _ _ _ acc mB m3 0 0 0 TMB Hl ltac:(lia) ltac:(lia) ltac:(lia)) as (j0' & jb' & TM3);
      [ eapply munch_weaken; [|exact MU3]; fp_tac | exact WM3 | exact MI3 | exact ST3
      | intros x Hx; left; cbn [outside]; repeat split; try exact I; lia |].
    step.
    assert (E34 : forall l, acc ++ P3 box_tok (tj_entry T i) ++ P4 box_tok (tj_entry T i) ++ l = acc ++ tj_L1 ++ tj_L2 ++ l).
    { intros l. unfold P3, P4, model_of, tj_entry, box_tok, din_of, dout_of.
      cbn [e_has_decl e_family e_decl_in e_decl_out]. rewrite HD. fold fa da db.
      rewrite (proj2 (Z.eqb_neq _ _) BR). reflexivity. }
    eapply tj_unk; [exact Hi | split; [exists j0', jb'; exact TM3 | split; [exact Hl | split; [exact FC | exact FK]]]
                  | rewrite TX; apply E34 |].
    pose proof (E34 []) as E'. rewrite !app_nil_r in E'. rewrite <- E'. exact K.
Qed.

Lemma tj_hd : forall (i o1 o2 : Z) (acc rest : list Z) (m : word -> option byte) (F : bvmap 5 word) (fc : bv 32)
    (a : Z) (x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x24 x25 x28 x29 x30 x31 : word),
  0 <= i < n_of T -> tj_oka acc a m F fc ->
  tj_text T now = acc ++ P3 box_tok (tj_entry T i) ++ P4 box_tok (tj_entry T i) ++ rest ->
  0 <= o1 -> 0 <= o2 -> o1 + o2 = Z.of_nat (length acc) ->
  tj_K i (acc ++ P3 box_tok (tj_entry T i) ++ P4 box_tok (tj_entry T i)) a ->
  evt rsegs tj_post (tj_st i 0x15e60 F fc m x1 x5 x6 x7 (Z_to_bv 64 o2) x11 x12 x13 x14 x15 x16 x17
                       (Z_to_bv 64 (t + 48 * i)) (Z_to_bv 64 o1) x24 x25 x28 x29 x30 x31).
Proof.
  intros i o1 o2 acc rest m F fc a x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x24 x25 x28 x29 x30 x31 Hi OK TX H1 H2 H12 K.
  pose proof OK as ((j0 & jb & TM) & Hl & FC & FK).
  pose proof TM as (FR & ST & HT & _).
  pose proof TOK as (T1 & T2 & T3 & T4). unfold tbl_T1 in T1.
  assert (RH : ov_read_bytes rsegs m (Z_to_bv 64 (t + (48 * i + 12))) 1 = Some (sub T (48 * i + 12) 1))
    by (apply rd_sub; [exact HT | lia | rewrite LT; lia]).
  assert (HD : hd_of T i = 0 \/ hd_of T i = 1) by (apply T4; lia).
  unfold tj_st. step.
  rewrite lbu_val by (apply length_sub; [lia | rewrite LT; lia]).
  change (bytes_le_to_Z (sub T (48 * i + 12) 1)) with (hd_of T i).
  step. step.
  replace (o1 + o2) with (Z.of_nat (length acc)) by lia.
  destruct HD as [HD|HD]; rewrite HD; step.
  - assert (E34 : forall l, acc ++ P3 box_tok (tj_entry T i) ++ P4 box_tok (tj_entry T i) ++ l = acc ++ tj_L1 ++ tj_L2 ++ l)
      by (intros l; unfold P3, P4, model_of, tj_entry; cbn [e_has_decl]; change (u_at T (48 * i + 12) 1) with (hd_of T i);
          rewrite HD; reflexivity).
    eapply tj_unk; [exact Hi | exact OK | rewrite TX; apply E34 |].
    pose proof (E34 []) as E. rewrite !app_nil_r in E. rewrite <- E. exact K.
  - eapply tj_decl; [exact Hi | exact HD | exact OK | exact TX | exact K].
Qed.

Lemma tj_oka_of : forall j0 a jb acc m,
  tj_mem (CB 24 j0 :: tj_ptrs ++ C8 (Z_to_bv 64 a) :: CB 96 jb :: tj_sv) acc m -> tj_mem (tj_loa j0 a jb ++ tj_sv) acc m.
Proof. intros j0 a jb acc m H. exact H. Qed.

Lemma tj_role : forall (i : Z) (acc rest : list Z) (m : word -> option byte) (F : bvmap 5 word) (fc : bv 32)
    (a : Z) (x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x24 x25 x28 x29 x30 x31 : word),
  0 <= i < n_of T -> tj_oka acc a m F fc -> tj_text T now = acc ++ P2 (tj_entry T i) ++ rest ->
  (forall (o1' o2' : Z) (m' : word -> option byte) (F' : bvmap 5 word) (fc' : bv 32)
      (y1 y5 y6 y7 y11 y12 y13 y14 y15 y16 y17 y24 y25 y28 y29 y30 y31 : word),
     tj_oka (acc ++ P2 (tj_entry T i)) a m' F' fc' -> 0 <= o1' -> 0 <= o2' ->
     o1' + o2' = Z.of_nat (length (acc ++ P2 (tj_entry T i))) ->
     evt rsegs tj_post (tj_st i 0x15e60 F' fc' m' y1 y5 y6 y7 (Z_to_bv 64 o2') y11 y12 y13 y14 y15 y16 y17
                          (Z_to_bv 64 (t + 48 * i)) (Z_to_bv 64 o1') y24 y25 y28 y29 y30 y31)) ->
  evt rsegs tj_post (tj_st i 0x15e24 F fc m x1 x5 x6 x7 (Z_to_bv 64 (Z.of_nat (length acc) + buf))
                       x11 x12 x13 x14 x15 x16 x17
                       (Z_to_bv 64 (t + 48 * i)) (Z_to_bv 64 (Z.of_nat (length acc))) x24 x25 x28 x29 x30 x31).
Proof.
  intros i acc rest m F fc a x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x24 x25 x28 x29 x30 x31 Hi OK TX K.
  destruct OK as ((j0 & jb & TM) & Hl & FC & FK).
  pose proof TM as (FR & ST & HT & BNT & GG & GD & MI & WM & MU & SB & BA).
  pose proof TOK as (T1 & T2 & T3 & T4). unfold tbl_T1 in T1.
  pose proof (tj_P2_len (tj_entry T i)) as LQ.
  assert (RR : ov_read_bytes rsegs m (Z_to_bv 64 (t + (48 * i + 8))) 4 = Some (sub T (48 * i + 8) 4))
    by (apply rd_sub; [exact HT | lia | rewrite LT; lia]).
  assert (RC : role_of_e T i = 0 \/ role_of_e T i = 1 \/ role_of_e T i = 2) by (apply T2; lia).
  unfold tj_loa in FR. cbn [app] in FR.
  unfold tj_st. step.
  rewrite lw_val by (apply length_sub; [lia | rewrite LT; lia]).
  change (bv_swrap 32 (bytes_le_to_Z (sub T (48 * i + 8) 4))) with (role_of_e T i).
  destruct RC as [R|[R|R]]; rewrite R; run_to 0x19d00.
  all: rewrite (unsigned_lit cap), (unsigned_lit (Z.of_nat (length acc))) by lia.
  all: eapply tj_call with (cs := tj_loa j0 a jb ++ tj_sv) (acc := acc) (A := 0x102c6)
         (fmt := [44; 34; 114; 111; 108; 101; 34; 58; 34; 37; 115; 34])
         (ps := [PLit 44; PLit 34; PLit 114; PLit 111; PLit 108; PLit 101; PLit 34; PLit 58; PLit 34; Ps; PLit 34])
         (args := [APtr (rolename (role_of_e T i))]) (q := P2 (tj_entry T i)) (ret := 0x15e58);
    [ exact TM | reflexivity | exact Hl | img | unfold RO_LO; lia | unfold RO_END; cbn [length]; lia | reflexivity
    | cbn [pf_args_ok]; split; [|exact I]; rewrite R;
      first [apply tj_s_box | apply tj_s_master | apply tj_s_unknown]; [exact MI | lia]
    | reflexivity | lia | exact FC | reflexivity | lia | reflexivity | | f_equal; lia | reflexivity | reflexivity ].
  all: intros m1 F1 fc1 y5 y6 y7 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31 TM1 BY1 FC1 FK1.
  all: step; rewrite lts_lit by lia; if_false.
  all: step; rewrite ltu_lit by lia.
  all: destruct (Z.ltb_spec (Z.of_nat (length (P2 (tj_entry T i)))) (cap - Z.of_nat (length acc))) as [OK|BAD]; cbn [negb];
    [ rewrite firstn_all2 in TM1 by lia;
      eapply K; [ split; [exists j0, jb; exact TM1 | split; [rewrite length_app; lia | split; [exact FC1 | fk_tac FK1 FK]]]
                | lia | lia | rewrite length_app; lia ]
    | eapply tj_fail; [exact TM1 | reflexivity | rewrite length_app, length_firstn; lia
                      | unfold tj_len; rewrite TX, !length_app; lia | exact FC1 | fk_tac FK1 FK] ].
Qed.

Lemma tj_mac : forall (i : Z) (acc rest : list Z) (m : word -> option byte) (F : bvmap 5 word) (fc : bv 32)
    (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x20 x23 x25 x28 x29 x30 x31 : word),
  0 <= i < n_of T -> tj_ok acc m F fc -> tj_text T now = acc ++ P1 (Z.to_nat i) (tj_entry T i) ++ rest ->
  (forall (m' : word -> option byte) (F' : bvmap 5 word) (fc' : bv 32)
      (y1 y5 y6 y7 y11 y12 y13 y14 y15 y16 y17 y24 y25 y28 y29 y30 y31 : word),
     tj_oka (acc ++ P1 (Z.to_nat i) (tj_entry T i)) (age_of now (last_of T i)) m' F' fc' ->
     evt rsegs tj_post (tj_st i 0x15e24 F' fc' m' y1 y5 y6 y7
                          (Z_to_bv 64 (Z.of_nat (length (acc ++ P1 (Z.to_nat i) (tj_entry T i))) + buf))
                          y11 y12 y13 y14 y15 y16 y17
                          (Z_to_bv 64 (t + 48 * i))
                          (Z_to_bv 64 (Z.of_nat (length (acc ++ P1 (Z.to_nat i) (tj_entry T i)))))
                          y24 y25 y28 y29 y30 y31)) ->
  evt rsegs tj_post (tj_st i 0x15d7c F fc m x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x20 x23
                       (Z_to_bv 64 (Z.of_nat (length acc))) x25 x28 x29 x30 x31).
Proof.
  intros i acc rest m F fc x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x20 x23 x25 x28 x29 x30 x31 Hi OK TX K.
  destruct OK as ((j0 & jb & TM) & Hl & FC & FK).
  pose proof TM as (FR & ST & HT & BNT & GG & GD & MI & WM & MU & SB & BA).
  pose proof TOK as (T1 & T2 & T3 & T4). unfold tbl_T1 in T1.
  pose proof length_bn_table as LBN.
  assert (LPB : length (pf_bytes acc) = length acc) by apply length_pf_bytes.
  pose proof (tj_last_range i ltac:(lia)) as LR.
  pose proof (bytes_at_bound rsegs m t T HT) as HTB. rewrite LT in HTB.
  pose proof (tj_P1_len (Z.to_nat i) (tj_entry T i)) as LQ.
  assert (LA : Z.of_nat (length (acc ++ P1 (Z.to_nat i) (tj_entry T i))) =
               Z.of_nat (length acc) + Z.of_nat (length (P1 (Z.to_nat i) (tj_entry T i)))) by (rewrite length_app; lia).
  assert (RL : ov_read_bytes rsegs m (Z_to_bv 64 (t + (48 * i + 40))) 8 = Some (sub T (48 * i + 40) 8))
    by (apply rd_sub; [exact HT | lia | rewrite LT; lia]).
  unfold tj_lo in FR. cbn [app] in FR.
  unfold tj_st.

  step. step. rewrite eqb_lit by lia. if_false.
  step. step. unfold tj_nt. rewrite ltu_lit by lia. if_false.

  step. step.
  rewrite ld_val by (apply length_sub; [lia | rewrite LT; lia]).
  change (bytes_le_to_Z (sub T (48 * i + 40) 8)) with (last_of T i).
  step. rewrite ltu_lit by lia.

  destruct (Z.ltb_spec (last_of T i) now) as [LN|LN]; cbn [negb];
    [ do 4 step;
      rewrite (unsigned_lit now), (unsigned_lit (last_of T i)), (unsigned_lit (now - last_of T i)),
        (unsigned_lit KDv) by (unfold KDv; lia);
      rewrite tj_quot_mach by lia;
      replace ((now - last_of T i) / 1000000) with (age_of now (last_of T i))
        by (unfold age_of; rewrite (proj2 (Z.ltb_lt _ _) LN); reflexivity);
      step; step
    | step;
      replace (Z_to_bv 64 0) with (Z_to_bv 64 (age_of now (last_of T i))) in FR
        by (unfold age_of; rewrite (proj2 (Z.ltb_ge _ _) LN); reflexivity) ].
  all: match goal with HT' : bytes_at rsegs ?mm t T |- _ =>
         assert (RM : forall k, 0 <= k < 6 ->
                   ov_read_bytes rsegs mm (Z_to_bv 64 (t + (48 * i + k))) 1 = Some (sub T (48 * i + k) 1))
           by (intros k Hk; apply rd_sub; [exact HT' | lia | rewrite LT; lia]) end.
  all: pose proof (RM 0 ltac:(lia)) as RM0; pose proof (RM 1 ltac:(lia)) as RM1; pose proof (RM 2 ltac:(lia)) as RM2;
       pose proof (RM 3 ltac:(lia)) as RM3; pose proof (RM 4 ltac:(lia)) as RM4; pose proof (RM 5 ltac:(lia)) as RM5;
       clear RM.

  all: pck.
  all: step; step; rewrite eqb_lit by lia.
  all: destruct (Z.eqb_spec (48 * i) 0) as [I0|I0]; run_to 0x19d00.
  all: rewrite !lbu_val in FR by (apply length_sub; [lia | rewrite LT; lia]).
  all: rewrite !lbu_val by (apply length_sub; [lia | rewrite LT; lia]).
  all: rewrite (unsigned_lit cap), (unsigned_lit (Z.of_nat (length acc))) by lia.
  all: eapply tj_call_stk with (acc := acc) (A := 0x10363)
         (fmt := [37; 115; 123; 34; 109; 97; 99; 34; 58; 34; 37; 48; 50; 120; 58; 37; 48; 50; 120; 58; 37; 48; 50; 120; 58;
                  37; 48; 50; 120; 58; 37; 48; 50; 120; 58; 37; 48; 50; 120; 34])
         (ps := [Ps; PLit 123; PLit 34; PLit 109; PLit 97; PLit 99; PLit 34; PLit 58; PLit 34; Px02; PLit 58; Px02;
                 PLit 58; Px02; PLit 58; Px02; PLit 58; Px02; PLit 58; Px02; PLit 34])
         (args := [APtr (if Nat.eqb (Z.to_nat i) 0 then [] else [44]); AInt (u_at T (48 * i + 0) 1);
                   AInt (u_at T (48 * i + 1) 1); AInt (u_at T (48 * i + 2) 1); AInt (u_at T (48 * i + 3) 1);
                   AInt (u_at T (48 * i + 4) 1); AInt (u_at T (48 * i + 5) 1)])
         (q := P1 (Z.to_nat i) (tj_entry T i)) (ret := 0x15e04);
    [ unfold tj_mem; repeat (split; [eassumption|]); eassumption
    | reflexivity | exact Hl | img | unfold RO_LO; lia | unfold RO_END; cbn [length]; lia | reflexivity
    | cbn [pf_args_ok app]; split;
      [ first [ assert (E0 : Nat.eqb (Z.to_nat i) 0 = true) by (apply Nat.eqb_eq; lia); rewrite E0; apply tj_s_empty
              | assert (E0 : Nat.eqb (Z.to_nat i) 0 = false) by (apply Nat.eqb_neq; lia); rewrite E0; apply tj_s_comma ];
        [exact MI | lia]
      | repeat (split; [apply tj_byte_arg; lia|]); exact I ]
    | rewrite tj_P1_eq by lia; cbn [pf_text option_map]; rewrite !pf_hex2_hex2 by (apply tj_u8; lia); reflexivity
    | lia | exact FC | reflexivity | lia | reflexivity | | f_equal; lia | reflexivity | reflexivity ].

  all: intros mq Fq fcq y5 y6 y7 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31 TM1 BY1 FC1 FK1.
  all: apply tj_mem_merge in TM1; destruct TM1 as [j1 TM1]; apply tj_oka_of in TM1.
  all: step; rewrite lts_lit by lia; if_false.
  all: step; rewrite ltu_lit by lia.
  all: destruct (Z.ltb_spec (Z.of_nat (length (P1 (Z.to_nat i) (tj_entry T i)))) (cap - Z.of_nat (length acc)))
         as [OK|BAD]; cbn [negb];
    [ rewrite firstn_all2 in TM1 by lia;
      step;
      replace (Z.of_nat (length acc) + Z.of_nat (length (P1 (Z.to_nat i) (tj_entry T i))))
        with (Z.of_nat (length (acc ++ P1 (Z.to_nat i) (tj_entry T i)))) by lia;
      pck;
      eapply K; split; [do 2 eexists; exact TM1 | split; [lia | split; [exact FC1 | fk_tac FK1 FK]]]
    | eapply tj_fail; [exact TM1 | reflexivity | rewrite length_app, length_firstn; lia
                      | unfold tj_len; rewrite TX, !length_app; lia | exact FC1 | fk_tac FK1 FK] ].
Qed.

Lemma tj_tail : forall (i o1 o2 : Z) (acc : list Z) (m : word -> option byte) (F : bvmap 5 word) (fc : bv 32)
    (x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x24 x25 x28 x29 x30 x31 : word),
  0 <= i < n_of T -> tj_oka acc (age_of now (last_of T i)) m F fc ->
  tj_text T now = acc ++ P5 (tj_entry T i) ++ P6 now (tj_entry T i) ++ tj_rest T now (i + 1) ->
  0 <= o1 -> 0 <= o2 -> o1 + o2 = Z.of_nat (length acc) ->
  (forall (acc' : list Z) (m' : word -> option byte) (F' : bvmap 5 word) (fc' : bv 32)
      (y1 y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y20 y23 y25 y28 y29 y30 y31 : word),
     i + 1 < n_of T -> tj_ok acc' m' F' fc' -> tj_text T now = acc' ++ tj_rest T now (i + 1) ->
     evt rsegs tj_post (tj_st (i + 1) 0x15d7c F' fc' m' y1 y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y20 y23
                          (Z_to_bv 64 (Z.of_nat (length acc'))) y25 y28 y29 y30 y31)) ->
  evt rsegs tj_post (tj_st i 0x15f7c F fc m x1 x5 x6 x7 (Z_to_bv 64 o2) x11 x12 x13 x14 x15 x16 x17
                       (Z_to_bv 64 (t + 48 * i)) (Z_to_bv 64 o1) x24 x25 x28 x29 x30 x31).
Proof.
  intros i o1 o2 acc m F fc x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x24 x25 x28 x29 x30 x31 Hi OK TX H1 H2 H12 KL.
  destruct OK as ((j0 & jb & TM) & Hl & FC & FK).
  pose proof TM as (FR & ST & HT & BNT & GG & GD & MI & WM & MU & SB & BA).
  pose proof TOK as (T1 & T2 & T3 & T4). unfold tbl_T1 in T1.
  pose proof (tj_age_range i ltac:(lia)) as AR.
  assert (RO : ov_read_bytes rsegs m (Z_to_bv 64 (t + 48 * i + 24)) 4 = Some (sub T (48 * i + 24) 4)).
  { replace (t + 48 * i + 24) with (t + (48 * i + 24)) by lia. apply rd_sub; [exact HT | lia | rewrite LT; lia]. }
  assert (OW : owned_of T i = 0 \/ owned_of T i = 1) by (apply T4; lia).
  unfold tj_loa in FR. cbn [app] in FR.
  unfold tj_st. step.
  pck.
  step.
  rewrite lw_val by (apply length_sub; [lia | rewrite LT; lia]).
  change (bv_swrap 32 (bytes_le_to_Z (sub T (48 * i + 24) 4))) with (owned_of T i).
  assert (LQ5 : (length (P5 (tj_entry T i)) <= 14)%nat)
    by (unfold P5, owned_text; destruct (e_owned _ =? 0); cbn; lia).
  destruct OW as [W|W]; rewrite W; run_to 0x19d00.
  all: rewrite (unsigned_lit cap), (unsigned_lit (o1 + o2)) by lia.
  all: eapply tj_call with (cs := tj_loa j0 (age_of now (last_of T i)) jb ++ tj_sv) (acc := acc) (A := 0x10390)
         (fmt := [44; 34; 111; 119; 110; 101; 100; 34; 58; 37; 115])
         (ps := [PLit 44; PLit 34; PLit 111; PLit 119; PLit 110; PLit 101; PLit 100; PLit 34; PLit 58; Ps])
         (args := [APtr (owned_text (tj_entry T i))]) (q := P5 (tj_entry T i)) (ret := 0x15fc4);
    [ exact TM | reflexivity | exact Hl | img | unfold RO_LO; lia | unfold RO_END; cbn [length]; lia | reflexivity
    | cbn [pf_args_ok]; split; [|exact I]; unfold owned_text, tj_entry; cbn [e_owned]; rewrite W;
      first [apply tj_s_false | apply tj_s_true]; [exact MI | lia]
    | unfold P5, owned_text, tj_entry; cbn [e_owned]; rewrite W; reflexivity
    | lia | exact FC | reflexivity | lia | reflexivity | | wq_tac | wq_tac | reflexivity ].
  all: intros m1 F1 fc1 y5 y6 y7 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31 TM1 BY1 FC1 FK1.
  all: step; rewrite lts_lit by lia; if_false.
  all: step; rewrite ltu_lit by lia.
  all: destruct (Z.ltb_spec (Z.of_nat (length (P5 (tj_entry T i)))) (cap - (o1 + o2))) as [OK5|BAD]; cbn [negb].
  2,4: eapply tj_fail; [exact TM1 | reflexivity | rewrite length_app, length_firstn; lia
                       | unfold tj_len; rewrite TX, !length_app; lia | exact FC1 | fk_tac FK1 FK].
  all: rewrite firstn_all2 in TM1 by lia.
  all: pose proof TM1 as (FR1 & _ & _ & _ & _ & _ & MI1 & _).
  all: unfold tj_loa in FR1; cbn [app] in FR1.
  all: assert (A19 : 0 <= age_of now (last_of T i) < 10 ^ 19)
         by (split; [lia|]; apply Z.lt_le_trans with (2 ^ 45); [lia | apply Z.leb_le; reflexivity]).
  all: step; pck.
  all: run_to 0x19d00.
  all: rewrite (unsigned_lit cap), (unsigned_lit (o1 + o2 + Z.of_nat (length (P5 (tj_entry T i))))) by lia.
  all: assert (LQ6 : (length (P6 now (tj_entry T i)) <= 31)%nat)
         by (pose proof (dec_len (age_of now (e_last_seen (tj_entry T i)))); unfold P6, key, k_age_ms;
             rewrite !length_app; cbn [length]; lia).
  all: eapply tj_call with (cs := tj_loa j0 (age_of now (last_of T i)) jb ++ tj_sv) (acc := acc ++ P5 (tj_entry T i))
         (A := 0x103ed)
         (fmt := [44; 34; 97; 103; 101; 95; 109; 115; 34; 58; 37; 108; 108; 117; 125])
         (ps := [PLit 44; PLit 34; PLit 97; PLit 103; PLit 101; PLit 95; PLit 109; PLit 115; PLit 34; PLit 58; Pllu;
                 PLit 125])
         (args := [AU64 (age_of now (last_of T i))]) (q := P6 now (tj_entry T i)) (ret := 0x15ffc);
    [ exact TM1 | reflexivity | rewrite length_app; lia | img | unfold RO_LO; lia | unfold RO_END; cbn [length]; lia
    | reflexivity
    | cbn [pf_args_ok pf_arg_ok]; split; [apply unsigned_lit; lia | exact I]
    | unfold P6, tj_entry; cbn [e_last_seen]; rewrite dec_udec by exact A19; reflexivity
    | lia | exact FC1 | reflexivity | lia | reflexivity | | wq_tac | wq_tac | reflexivity ].
  all: intros m2 F2 fc2 z5 z6 z7 z11 z12 z13 z14 z15 z16 z17 z28 z29 z30 z31 TM2 BY2 FC2 FK2.
  all: step; rewrite lts_lit by lia; if_false.
  all: step; rewrite ltu_lit by lia.
  all: destruct (Z.ltb_spec (Z.of_nat (length (P6 now (tj_entry T i))))
                   (cap - (o1 + o2 + Z.of_nat (length (P5 (tj_entry T i)))))) as [OK6|BAD]; cbn [negb].
  2,4: eapply tj_fail; [exact TM2 | reflexivity | rewrite !length_app, length_firstn; lia
                       | unfold tj_len; rewrite TX, !length_app; lia | exact FC2
                       | intros k Hk; rewrite FK2, FK1 by exact Hk; apply FK; exact Hk].
  all: rewrite firstn_all2 in TM2 by (rewrite ?length_app; lia).
  all: pose proof TM2 as (FR2 & ST2 & HT2 & _).
  all: assert (RN : ov_read_bytes rsegs m2 (Z_to_bv 64 (t + 384)) 4 = Some (sub T 384 4))
         by (apply rd_sub; [exact HT2 | lia | rewrite LT; lia]).
  all: step.
  all: rewrite lw_val by (apply length_sub; [lia | rewrite LT; lia]).
  all: change (bv_swrap 32 (bytes_le_to_Z (sub T 384 4))) with (n_of T).
  all: step. all: step. all: step. all: step.
  all: rewrite lts_lit by lia.
  all: replace (o1 + o2 + Z.of_nat (length (P5 (tj_entry T i))) + Z.of_nat (length (P6 now (tj_entry T i))))
         with (Z.of_nat (length ((acc ++ P5 (tj_entry T i)) ++ P6 now (tj_entry T i)))) by (rewrite !length_app; lia).
  all: destruct (Z.ltb_spec (i + 1) (n_of T)) as [NX|NX]; cbv iota.
  1,3: replace (Z_to_bv 64 (48 * i + 48)) with (Z_to_bv 64 (48 * (i + 1))) by (f_equal; lia);
       destruct (tj_age_merge _ _ _ _ _ TM2) as [jb2 TM2'];
       eapply KL; [ exact NX
                  | split; [exists j0, jb2; exact TM2' | split; [rewrite !length_app; lia | split; [exact FC2 |]]]
                  | rewrite TX, <- !app_assoc; reflexivity ];
       intros k Hk; rewrite FK2, FK1 by exact Hk; apply FK; exact Hk.
  all: eapply tj_end; [ exact TM2 | reflexivity | rewrite !length_app; lia
                      | rewrite TX; replace (i + 1) with (n_of T) by lia; rewrite tj_rest_end by lia;
                        rewrite <- !app_assoc; reflexivity
                      | exact FC2 | intros k Hk; rewrite FK2, FK1 by exact Hk; apply FK; exact Hk ].
Qed.

Lemma tj_land7 : forall x, Z.land x 7 = x mod 8.
Proof. intros x. change 7 with (Z.ones 3). rewrite Z.land_ones by lia. reflexivity. Qed.

Ltac tzcu HC := unfold bv_eqb, bv_ltu in HC; rewrite ?unsigned_lit_wrap in HC;
  try change (bv_wrap 64 7) with 7 in HC; rewrite ?tj_land7 in HC; zify_bool HC; Z.div_mod_to_equations; lia.
Ltac ttrap := let HC := fresh "HC" in if_cases HC; [exfalso; tzcu HC | clear HC].

Lemma tj_loop : forall (k : nat) (i : Z) (acc : list Z) (m : word -> option byte) (F : bvmap 5 word) (fc : bv 32)
    (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x20 x23 x25 x28 x29 x30 x31 : word),
  Z.to_nat (n_of T - i) = k -> 0 <= i < n_of T -> tj_ok acc m F fc -> tj_text T now = acc ++ tj_rest T now i ->
  evt rsegs tj_post (tj_st i 0x15d7c F fc m x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x20 x23
                       (Z_to_bv 64 (Z.of_nat (length acc))) x25 x28 x29 x30 x31).
Proof.
  induction k as [|k IH];
    intros i acc m F fc x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x20 x23 x25 x28 x29 x30 x31 Hk Hi OK TX; [lia|].
  rewrite tj_rest_step in TX by exact Hi. unfold obj_text in TX.
  set (e := tj_entry T i) in *.
  eapply tj_mac with (rest := P2 e ++ P3 box_tok e ++ P4 box_tok e ++ P5 e ++ P6 now e ++ tj_rest T now (i + 1));
    [exact Hi | exact OK | rewrite TX, <- !app_assoc; reflexivity |].
  intros * OK1.
  eapply tj_role with (rest := P3 box_tok e ++ P4 box_tok e ++ P5 e ++ P6 now e ++ tj_rest T now (i + 1));
    [exact Hi | exact OK1 | rewrite TX, <- !app_assoc; reflexivity |].
  intros * OK2 H1' H2' H12'.
  eapply tj_hd with (rest := P5 e ++ P6 now e ++ tj_rest T now (i + 1));
    [exact Hi | exact OK2 | rewrite TX, <- !app_assoc; reflexivity | exact H1' | exact H2' | exact H12' |].
  unfold tj_K. intros * OK3 H1'' H2'' H12''.
  eapply tj_tail; [exact Hi | exact OK3 | rewrite TX, <- !app_assoc; reflexivity | exact H1'' | exact H2'' | exact H12'' |].
  intros * NX OK4 TX4.
  eapply IH; [lia | lia | exact OK4 | exact TX4].
Qed.

Lemma tj_not_eq : Z_to_bv 64 (Z.lxor (bv_unsigned (Z_to_bv 64 t)) 18446744073709551615) = tj_nt.
Proof.
  unfold tj_nt. rewrite unsigned_lit by lia. rewrite lnot_mod64 by lia. f_equal.
  symmetry. apply (Z.mod_unique _ _ (-1)); [left; lia | unfold Z.lnot, Z.pred; lia].
Qed.

Lemma tj_main : forall (t0 t1 t2 a4 a5 a6 a7 t3 t4 t5 t6 : word) (fc : bv 32),
  bytes_at rsegs m0 t T -> bytes_at rsegs m0 0x205f8 bn_table -> bytes_at rsegs m0 0x206a0 (le8 (Z_to_bv 64 0x51c90)) ->
  bytes_at rsegs m0 0x51c90 (le8 canary) -> frm0 fc -> mem_inv rsegs m0 ->
  evt rsegs tj_post (MS (mkR ra (Z_to_bv 64 S) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 t) (Z_to_bv 64 now) (Z_to_bv 64 buf)
                         (Z_to_bv 64 cap) a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                    F0 (Z_to_bv 64 0x15c40) fc None m0 (seg_rom rsegs)).
Proof.
  intros t0 t1 t2 a4 a5 a6 a7 t3 t4 t5 t6 fc HT BNT GG GD FC MI.
  pose proof length_bn_table as LBN.
  pose proof TOK as (T1 & T2 & T3 & T4). unfold tbl_T1 in T1.
  pose proof ST0 as ST. pose proof SB0 as SB.
  set (mm := m0) in HT, BNT, GG, GD, MI, ST, SB |- *.
  assert (MU : munch [(lo, S)] m0 mm) by apply munch_refl.
  assert (WM : wmono rsegs m0 mm) by apply wmono_refl.
  carve_frame 304%nat ST.
  do 18 step. rewrite ltu_lit by lia. if_true.
  do 8 step.
  lazymatch type of FR with rw_cells _ _ _ (CB 200 ?jj :: _) => set (j := jj) in FR end.
  eapply tj_call with (cs := CB 200 j :: tj_sv) (acc := []) (A := 0x1038c) (fmt := [91]) (ps := [PLit 91]) (args := [])
    (q := [91]) (ret := 0x15ce8);
    [ | reflexivity | cbn [length]; lia | img | unfold RO_LO; lia | unfold RO_END; cbn [length]; lia | reflexivity
    | exact I | reflexivity | cbn [length]; lia | exact FC | reflexivity | lia | reflexivity | | f_equal; cbn [length]; lia
    | f_equal; cbn [length]; lia | reflexivity ].
  { unfold tj_mem. split; [exact FR|]. split; [exact ST|]. split; [exact HT|]. split; [exact BNT|].
    split; [exact GG|]. split; [exact GD|]. split; [exact MI|]. split; [exact WM|].
    split; [eapply munch_weaken; [|exact MU]; fp_tac|]. split; [exact SB|]. apply bytes_at_nil. lia. }
  intros m1 F1 fc1 y5 y6 y7 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31 TM1 BY1 FC1 FK1.
  rewrite firstn_all2 in TM1 by (cbn [length]; lia). cbn [app] in TM1.
  pose proof TM1 as (FR1 & ST1 & HT1 & BNT1 & GG1 & GD1 & MI1 & WM1 & MU1 & SB1 & BA1).
  change (pf_bytes [91]) with [Z_to_bv 8 91] in BA1.
  step. rewrite lts_lit by (cbn [length]; lia). if_false.
  step. step. cbn [length] in *. change (Z.of_nat 1) with 1 in *.
  rewrite ltu_lit by lia. rewrite (proj2 (Z.ltb_lt 1 cap)) by lia. cbn [negb].
  step. ttrap. step. step. ttrap.
  pose proof (rd_sub _ t T 384 4 HT1 ltac:(lia) ltac:(rewrite LT; lia)) as RN.
  step. rewrite lw_val by (apply length_sub; [lia | rewrite LT; lia]).
  change (bv_swrap 32 (bytes_le_to_Z (sub T 384 4))) with (n_of T).
  step. rewrite lts_lit by lia.
  destruct (Z.ltb_spec 0 (n_of T)) as [N0|N0]; cbn [negb].
  2: { assert (N : n_of T = 0) by lia.
       eapply tj_end with (pre := [CB 200 j]) (acc := [91]);
         [ exact TM1 | reflexivity | cbn [length]; lia
         | rewrite tj_rest_0, <- N, tj_rest_end by lia; reflexivity | exact FC1 | exact FK1 ]. }
  assert (BK : bytes_at rsegs m1 0x10518 (le8 (Z_to_bv 64 KDv))) by img.
  assert (RKD : ov_read_bytes rsegs m1 (Z_to_bv 64 0x10518) 8 = Some (le8 (Z_to_bv 64 KDv))).
  { replace (Z_to_bv 64 0x10518) with (wa (0x10518 + 0)) by reflexivity.
    rewrite (bytes_at_read rsegs m1 0x10518 (le8 (Z_to_bv 64 KDv)) 0 8 BK ltac:(lia)) by (rewrite length_le8; lia).
    reflexivity. }
  run_to 0x15d7c.
  lazymatch goal with H : rw_cells rsegs _ (S + -304) _ |- _ => rewrite tj_not_eq in H end.
  rewrite tj_snez by lia.
  eapply (tj_loop (Z.to_nat (n_of T - 0)) 0 [91]); [reflexivity | lia | | rewrite tj_rest_0; reflexivity].
  split; [|split; [cbn [length]; lia | split; [exact FC1 | exact FK1]]].
  unfold tj_lo; cbn [app]; do 2 eexists; unfold tj_mem.
  repeat (split; [eassumption|]). exact BA1.
Qed.

End TJ.
