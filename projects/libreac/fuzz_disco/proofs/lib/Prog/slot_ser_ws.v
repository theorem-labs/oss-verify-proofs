From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes ZBridge FP.
From OSSVerify.Proofs.libreac.fuzz_disco.lib Require Import Img0.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require Import slot_inv slot_lib printf_facts_c.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require Import disco_jscalar_model disco_json_reader_model.
Import ListNotations.
Open Scope Z_scope.

Lemma ws_f_stable : forall B f i, jlen B - i <= Z.of_nat f -> json_ws_f B i (S f) = json_ws_f B i f.
Proof.
  intros B f. induction f as [|f IH]; intros i Hf.
  - cbn [json_ws_f]. replace (i <? jlen B) with false by (symmetry; apply Z.ltb_ge; lia). reflexivity.
  - change (json_ws_f B i (S (S f))) with
      (if (i <? jlen B) && jws_char (jbyte B i) then json_ws_f B (i + 1) (S f) else i).
    change (json_ws_f B i (S f)) with
      (if (i <? jlen B) && jws_char (jbyte B i) then json_ws_f B (i + 1) f else i).
    rewrite IH by lia. reflexivity.
Qed.

Lemma ws_unfold : forall B i, 0 <= i ->
  json_ws B i = if (i <? jlen B) && jws_char (jbyte B i) then json_ws B (i + 1) else i.
Proof.
  intros B i Hi. unfold json_ws. destruct (length B) as [|f] eqn:L.
  - cbn [json_ws_f]. unfold jlen. rewrite L. replace (i <? Z.of_nat 0) with false by (symmetry; apply Z.ltb_ge; lia).
    reflexivity.
  - cbn [json_ws_f]. destruct ((i <? jlen B) && jws_char (jbyte B i)) eqn:C; [|reflexivity].
    apply andb_true_iff in C as [C _]. apply Z.ltb_lt in C.
    symmetry. apply ws_f_stable. unfold jlen in *. lia.
Qed.

Lemma ws_ge : forall B i, 0 <= i -> i <= json_ws B i.
Proof.
  intros B i Hi. remember (Z.to_nat (jlen B - i)) as k eqn:Hk. revert i Hi Hk.
  induction k as [|k IH]; intros i Hi Hk; rewrite ws_unfold by lia.
  - replace (i <? jlen B) with false by (symmetry; apply Z.ltb_ge; lia). cbn. lia.
  - destruct ((i <? jlen B) && jws_char (jbyte B i)); [|lia].
    pose proof (IH (i + 1) ltac:(lia) ltac:(lia)). lia.
Qed.

Lemma ws_lt : forall B i, 0 <= i -> json_ws B i < jlen B -> i < jlen B.
Proof.
  intros B i Hi H. destruct (Z.ltb_spec i (jlen B)) as [L|L]; [exact L|].
  rewrite ws_unfold in H by lia. replace (i <? jlen B) with false in H by (symmetry; apply Z.ltb_ge; lia).
  cbn [andb] in H. lia.
Qed.

Lemma ws_le : forall B i, 0 <= i <= jlen B -> json_ws B i <= jlen B.
Proof.
  intros B i Hi. remember (Z.to_nat (jlen B - i)) as k eqn:Hk. revert i Hi Hk.
  induction k as [|k IH]; intros i Hi Hk; rewrite ws_unfold by lia.
  - replace (i <? jlen B) with false by (symmetry; apply Z.ltb_ge; lia). cbn. lia.
  - destruct ((i <? jlen B) && jws_char (jbyte B i)) eqn:C; [|lia].
    apply andb_true_iff in C as [C _]. apply Z.ltb_lt in C. apply IH; lia.
Qed.

Lemma ws_mask : forall c, 0 <= c <= 32 -> Z.land (Z.shiftr WS_MASK c) 1 = if jws_char c then 1 else 0.
Proof.
  intros c Hc. replace c with (Z.of_nat (Z.to_nat c)) by lia.
  assert (Hk : (Z.to_nat c <= 32)%nat) by lia. revert Hk. generalize (Z.to_nat c). clear c Hc. intros k Hk.
  do 33 (destruct k as [|k]; [reflexivity|]). lia.
Qed.

Lemma ws_byte : forall B i, Forall (fun c => 0 <= c < 256) B -> 0 <= jbyte B i < 256.
Proof.
  intros B i F. unfold jbyte. destruct (Nat.ltb_spec (Z.to_nat i) (length B)) as [L|L].
  - rewrite Forall_forall in F. apply F. apply nth_In. exact L.
  - rewrite nth_overflow by exact L. lia.
Qed.

Lemma ws_rd : forall m b B i, bytes_at rsegs m b (pf_bytes (B ++ [0])) -> 0 <= i <= jlen B ->
  ov_read_bytes rsegs m (wa (b + i)) 1 = Some [Z_to_bv 8 (jbyte B i)].
Proof.
  intros m b B i H Hi. unfold jlen in Hi.
  pose proof (read1 m b _ (Z.to_nat i) H) as R.
  rewrite Z2Nat.id in R by lia. rewrite R by (unfold pf_bytes; rewrite length_map, length_app; cbn [length]; lia).
  f_equal. f_equal. unfold pf_bytes, jbyte. rewrite map_app.
  destruct (Nat.ltb_spec (Z.to_nat i) (length B)) as [L|L].
  - rewrite app_nth1 by (rewrite length_map; lia). rewrite (map_nth (Z_to_bv 8) B 0). reflexivity.
  - rewrite app_nth2 by (rewrite length_map; lia). rewrite length_map.
    replace (Z.to_nat i - length B)%nat with O by lia. rewrite (nth_overflow B) by lia. reflexivity.
Qed.

Lemma ws_zxb : forall c, 0 <= c < 256 -> zxb (Z_to_bv 8 c) = Z_to_bv 64 c.
Proof.
  intros c Hc. unfold zxb. f_equal. rewrite Z_to_bv_unsigned. apply bv_wrap_small.
  change (bv_modulus 8) with 256. lia.
Qed.

Lemma ws_eqb : forall x y, - 2 ^ 63 <= x < 2 ^ 63 -> - 2 ^ 63 <= y < 2 ^ 63 ->
  bv_eqb (Z_to_bv 64 x) (Z_to_bv 64 y) = (x =? y).
Proof.
  intros x y Hx Hy. unfold bv_eqb. rewrite !unsigned_lit_wrap.
  destruct (Z.eqb_spec x y) as [->|N]; [apply Z.eqb_refl|]. apply Z.eqb_neq. intro E. apply N.
  assert (Hx' : x mod 2 ^ 64 = if x <? 0 then x + 2 ^ 64 else x).
  { destruct (Z.ltb_spec x 0).
    - replace x with ((x + 2 ^ 64) + (-1) * 2 ^ 64) at 1 by lia. rewrite Z.mod_add by lia. apply Z.mod_small. lia.
    - apply Z.mod_small. lia. }
  assert (Hy' : y mod 2 ^ 64 = if y <? 0 then y + 2 ^ 64 else y).
  { destruct (Z.ltb_spec y 0).
    - replace y with ((y + 2 ^ 64) + (-1) * 2 ^ 64) at 1 by lia. rewrite Z.mod_add by lia. apply Z.mod_small. lia.
    - apply Z.mod_small. lia. }
  rewrite Hx', Hy' in E. destruct (Z.ltb_spec x 0), (Z.ltb_spec y 0); lia.
Qed.

Lemma ws_cond : forall c, 0 <= c <= 32 ->
  bv_eqb (Z_to_bv 64 (Z.land (bv_unsigned (Z_to_bv 64 (Z.shiftr (bv_unsigned (Z_to_bv 64 WS_MASK))
                                                         (bv_unsigned (Z_to_bv 64 c) mod 64)))) 1))
         (Z_to_bv 64 0) = negb (jws_char c).
Proof.
  intros c Hc. rewrite (unsigned_lit WS_MASK) by (unfold WS_MASK; lia). rewrite (unsigned_lit c) by lia.
  rewrite (Z.mod_small c 64) by lia.
  assert (HS : 0 <= Z.shiftr WS_MASK c <= WS_MASK).
  { rewrite Z.shiftr_div_pow2 by lia. split; [apply Z.div_pos; unfold WS_MASK; lia|].
    apply Z.div_le_upper_bound; [lia|]. pose proof (Z.pow_pos_nonneg 2 c ltac:(lia) ltac:(lia)).
    unfold WS_MASK; nia. }
  rewrite (unsigned_lit (Z.shiftr WS_MASK c)) by (unfold WS_MASK in *; lia).
  rewrite ws_mask by lia. destruct (jws_char c); reflexivity.
Qed.


Lemma ws_end : forall B, jbyte B (jlen B) = 0.
Proof. intros B. unfold jbyte, jlen. rewrite Nat2Z.id. apply nth_overflow. lia. Qed.

Lemma ws_big : forall c, 32 < c -> jws_char c = false.
Proof. intros c Hc. unfold jws_char. repeat rewrite (proj2 (Z.eqb_neq _ _)) by lia. reflexivity. Qed.

Lemma ws_stop : forall B i, 0 <= i -> jws_char (jbyte B i) = false -> json_ws B i = i.
Proof. intros B i Hi W. rewrite ws_unfold by exact Hi. rewrite W, andb_false_r. reflexivity. Qed.

Lemma ws_step : forall B i, 0 <= i <= jlen B -> jws_char (jbyte B i) = true ->
  i < jlen B /\ json_ws B i = json_ws B (i + 1).
Proof.
  intros B i Hi W. assert (L : i < jlen B).
  { destruct (Z.eq_dec i (jlen B)) as [E|E]; [|lia]. rewrite E, ws_end in W. discriminate. }
  split; [exact L|]. rewrite ws_unfold by lia. rewrite (proj2 (Z.ltb_lt _ _) L), W. reflexivity.
Qed.

Lemma ws_at_end : forall B, json_ws B (jlen B) = jlen B.
Proof.
  intros B. rewrite ws_unfold by (unfold jlen; lia). rewrite Z.ltb_irrefl. reflexivity.
Qed.

Ltac ws_byte_test B i :=
  rewrite ws_zxb by lia; rewrite ltu_lit by lia;
  destruct (Z.ltb_spec 32 (jbyte B i)) as [C|C]; cbv iota.

Ltac ws_mask_test B i W :=
  rewrite ws_cond by lia; destruct (jws_char (jbyte B i)) eqn:W; cbn [negb]; cbv iota.

Ltac ws_exit B i := rewrite (ws_stop B i ltac:(lia)) by first [assumption | apply ws_big; lia];
  apply evt_done; eexists; reflexivity.

Lemma ws_L5 : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (b i : Z) (B : list Z),
  s0 = Z_to_bv 64 32 -> s2 = Z_to_bv 64 WS_MASK -> s3 = Z_to_bv 64 b -> s4 = Z_to_bv 64 (jlen B) -> s10 = Z_to_bv 64 i -> a0 = Z_to_bv 64 (b + i + 1) -> a1 = Z_to_bv 64 (-1 - i) ->
  0 <= i -> json_ws B i < jlen B ->
  0 < b -> b + jlen B + 1 < 2 ^ 63 ->
  Forall (fun c => 0 <= c < 256) B -> bytes_at rsegs m b (pf_bytes (B ++ [0])) ->
  evt rsegs
    (fun ms' => exists a3' : word,
       ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (b + (json_ws B i) + 1)) (Z_to_bv 64 (-1 - (json_ws B i))) (Z_to_bv 64 (jbyte B (json_ws B i))) a3' a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 (Z_to_bv 64 (json_ws B i)) s11 t3 t4 t5 t6)
                F (Z_to_bv 64 0x13698) fc None m (seg_rom rsegs))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x1366c) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m b i B
    E0 E2 E3 E4 E10 Ea0 Ea1 Hi HW Hb HbB FB BB.
  subst s0 s2 s3 s4.
  remember (Z.to_nat (jlen B - i)) as k eqn:Hk.
  revert i a0 a1 a2 a3 s10 Hk E10 Ea0 Ea1 Hi HW.
  induction k as [|k IH]; intros i a0 a1 a2 a3 s10 Hk E10 Ea0 Ea1 Hi HW; subst a0 a1 s10;
    (assert (HiB : i < jlen B) by (apply (ws_lt B i Hi); lia)); [lia|].
  pose proof (ws_rd m b B i BB ltac:(lia)) as RD. pose proof (ws_byte B i FB) as HC.
  step. step. step. ws_byte_test B i; [ws_exit B i|].
  step. step. step. ws_mask_test B i W; [|ws_exit B i].
  destruct (ws_step B i ltac:(lia) W) as [_ E1]. rewrite E1 in HW |- *.
  pose proof (ws_ge B (i + 1) ltac:(lia)) as G1.
  step. step. step. step. rewrite eqb_lit by lia.
  replace (jlen B =? i + 1) with false by (symmetry; apply Z.eqb_neq; lia). cbv iota.
  step. eapply (IH (i + 1)); [lia | reflexivity | f_equal; lia | f_equal; lia | lia | exact HW].
Qed.

Lemma ws_L6 : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (b i : Z) (B : list Z),
  s0 = Z_to_bv 64 32 -> s2 = Z_to_bv 64 WS_MASK -> a2 = Z_to_bv 64 (- jlen B) -> a0 = Z_to_bv 64 (b + i) -> a1 = Z_to_bv 64 (- i) ->
  0 <= i -> json_ws B i < jlen B ->
  0 < b -> b + jlen B + 1 < 2 ^ 63 ->
  Forall (fun c => 0 <= c < 256) B -> bytes_at rsegs m b (pf_bytes (B ++ [0])) ->
  evt rsegs
    (fun ms' => exists a3' : word,
       ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (b + (json_ws B i))) (Z_to_bv 64 (- (json_ws B i))) a2 a3' a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                F (Z_to_bv 64 0x138d8) fc None m (seg_rom rsegs))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x136b0) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m b i B
    E0 E2 En Ep Ec Hi HW Hb HbB FB BB.
  subst s0 s2 a2.
  remember (Z.to_nat (jlen B - i)) as k eqn:Hk.
  revert i a0 a1 a3 Hk Ep Ec Hi HW.
  induction k as [|k IH]; intros i a0 a1 a3 Hk Ep Ec Hi HW; subst a0 a1;
    (assert (HiB : i < jlen B) by (apply (ws_lt B i Hi); lia)); [lia|].
  pose proof (ws_rd m b B i BB ltac:(lia)) as RD. pose proof (ws_byte B i FB) as HC.
  step. step. ws_byte_test B i; [ws_exit B i|].
  step. step. step. ws_mask_test B i W; [|ws_exit B i].
  destruct (ws_step B i ltac:(lia) W) as [_ E1]. rewrite E1 in HW |- *.
  pose proof (ws_ge B (i + 1) ltac:(lia)) as G1.
  step. step. step. rewrite ws_eqb by lia.
  replace (- jlen B =? - i + -1) with false by (symmetry; apply Z.eqb_neq; lia). cbv iota.
  step.
  eapply (IH (i + 1)); [lia | f_equal; lia | f_equal; lia | lia | exact HW].
Qed.

Lemma ws_L9 : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (b i : Z) (B : list Z),
  s0 = Z_to_bv 64 32 -> s2 = Z_to_bv 64 WS_MASK -> s7 = Z_to_bv 64 (- jlen B) -> s10 = Z_to_bv 64 (b + i) -> a0 = Z_to_bv 64 (- i) ->
  0 <= i -> json_ws B i < jlen B ->
  0 < b -> b + jlen B + 1 < 2 ^ 63 ->
  Forall (fun c => 0 <= c < 256) B -> bytes_at rsegs m b (pf_bytes (B ++ [0])) ->
  evt rsegs
    (fun ms' => exists a1' : word,
       ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (- (json_ws B i))) a1' a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 (Z_to_bv 64 (b + (json_ws B i))) s11 t3 t4 t5 t6)
                F (Z_to_bv 64 0x139a0) fc None m (seg_rom rsegs))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x13978) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m b i B
    E0 E2 En Ep Ec Hi HW Hb HbB FB BB.
  subst s0 s2 s7.
  remember (Z.to_nat (jlen B - i)) as k eqn:Hk.
  revert i s10 a0 a1 Hk Ep Ec Hi HW.
  induction k as [|k IH]; intros i s10 a0 a1 Hk Ep Ec Hi HW; subst s10 a0;
    (assert (HiB : i < jlen B) by (apply (ws_lt B i Hi); lia)); [lia|].
  pose proof (ws_rd m b B i BB ltac:(lia)) as RD. pose proof (ws_byte B i FB) as HC.
  step. step. ws_byte_test B i; [ws_exit B i|].
  step. step. step. ws_mask_test B i W; [|ws_exit B i].
  destruct (ws_step B i ltac:(lia) W) as [_ E1]. rewrite E1 in HW |- *.
  pose proof (ws_ge B (i + 1) ltac:(lia)) as G1.
  step. step. step. rewrite ws_eqb by lia.
  replace (- jlen B =? - i + -1) with false by (symmetry; apply Z.eqb_neq; lia). cbn [negb]. cbv iota.
  eapply (IH (i + 1)); [lia | f_equal; lia | f_equal; lia | lia | exact HW].
Qed.

Lemma ws_L11 : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (b i : Z) (B : list Z),
  s0 = Z_to_bv 64 32 -> s2 = Z_to_bv 64 WS_MASK -> s7 = Z_to_bv 64 (- jlen B) -> a0 = Z_to_bv 64 (b + i) -> a1 = Z_to_bv 64 (- i) ->
  0 <= i -> json_ws B i < jlen B ->
  0 < b -> b + jlen B + 1 < 2 ^ 63 ->
  Forall (fun c => 0 <= c < 256) B -> bytes_at rsegs m b (pf_bytes (B ++ [0])) ->
  evt rsegs
    (fun ms' => exists a2' : word,
       ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (b + (json_ws B i))) (Z_to_bv 64 (- (json_ws B i))) a2' a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                F (Z_to_bv 64 0x13a4c) fc None m (seg_rom rsegs))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x13a28) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m b i B
    E0 E2 En Ep Ec Hi HW Hb HbB FB BB.
  subst s0 s2 s7.
  remember (Z.to_nat (jlen B - i)) as k eqn:Hk.
  revert i a0 a1 a2 Hk Ep Ec Hi HW.
  induction k as [|k IH]; intros i a0 a1 a2 Hk Ep Ec Hi HW; subst a0 a1;
    (assert (HiB : i < jlen B) by (apply (ws_lt B i Hi); lia)); [lia|].
  pose proof (ws_rd m b B i BB ltac:(lia)) as RD. pose proof (ws_byte B i FB) as HC.
  step. step. ws_byte_test B i; [ws_exit B i|].
  step. step. step. ws_mask_test B i W; [|ws_exit B i].
  destruct (ws_step B i ltac:(lia) W) as [_ E1]. rewrite E1 in HW |- *.
  pose proof (ws_ge B (i + 1) ltac:(lia)) as G1.
  step. step. step. rewrite ws_eqb by lia.
  replace (- jlen B =? - i + -1) with false by (symmetry; apply Z.eqb_neq; lia). cbv iota.
  step.
  eapply (IH (i + 1)); [lia | f_equal; lia | f_equal; lia | lia | exact HW].
Qed.

Lemma ws_L15 : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (b i : Z) (B : list Z),
  s0 = Z_to_bv 64 32 -> s2 = Z_to_bv 64 WS_MASK -> s7 = Z_to_bv 64 (- jlen B) -> s6 = Z_to_bv 64 (b + i) -> a0 = Z_to_bv 64 (- i) ->
  0 <= i -> json_ws B i < jlen B ->
  0 < b -> b + jlen B + 1 < 2 ^ 63 ->
  Forall (fun c => 0 <= c < 256) B -> bytes_at rsegs m b (pf_bytes (B ++ [0])) ->
  evt rsegs
    (fun ms' => exists a1' : word,
       ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (- (json_ws B i))) a1' a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 (Z_to_bv 64 (b + (json_ws B i))) s7 s8 s9 s10 s11 t3 t4 t5 t6)
                F (Z_to_bv 64 0x13c44) fc None m (seg_rom rsegs))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x13c20) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m b i B
    E0 E2 En Ep Ec Hi HW Hb HbB FB BB.
  subst s0 s2 s7.
  remember (Z.to_nat (jlen B - i)) as k eqn:Hk.
  revert i s6 a0 a1 Hk Ep Ec Hi HW.
  induction k as [|k IH]; intros i s6 a0 a1 Hk Ep Ec Hi HW; subst s6 a0;
    (assert (HiB : i < jlen B) by (apply (ws_lt B i Hi); lia)); [lia|].
  pose proof (ws_rd m b B i BB ltac:(lia)) as RD. pose proof (ws_byte B i FB) as HC.
  step. step. ws_byte_test B i; [ws_exit B i|].
  step. step. step. ws_mask_test B i W; [|ws_exit B i].
  destruct (ws_step B i ltac:(lia) W) as [_ E1]. rewrite E1 in HW |- *.
  pose proof (ws_ge B (i + 1) ltac:(lia)) as G1.
  step. step. step. rewrite ws_eqb by lia.
  replace (- jlen B =? - i + -1) with false by (symmetry; apply Z.eqb_neq; lia). cbv iota.
  step.
  eapply (IH (i + 1)); [lia | f_equal; lia | f_equal; lia | lia | exact HW].
Qed.

Lemma ws_L16 : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (b i : Z) (B : list Z),
  s0 = Z_to_bv 64 32 -> s2 = Z_to_bv 64 WS_MASK -> s7 = Z_to_bv 64 (- jlen B) -> a0 = Z_to_bv 64 (b + i) -> a1 = Z_to_bv 64 (- i) ->
  0 <= i -> json_ws B i < jlen B ->
  0 < b -> b + jlen B + 1 < 2 ^ 63 ->
  Forall (fun c => 0 <= c < 256) B -> bytes_at rsegs m b (pf_bytes (B ++ [0])) ->
  evt rsegs
    (fun ms' => exists a2' : word,
       ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (b + (json_ws B i))) (Z_to_bv 64 (- (json_ws B i))) a2' a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                F (Z_to_bv 64 0x13c98) fc None m (seg_rom rsegs))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x13c74) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m b i B
    E0 E2 En Ep Ec Hi HW Hb HbB FB BB.
  subst s0 s2 s7.
  remember (Z.to_nat (jlen B - i)) as k eqn:Hk.
  revert i a0 a1 a2 Hk Ep Ec Hi HW.
  induction k as [|k IH]; intros i a0 a1 a2 Hk Ep Ec Hi HW; subst a0 a1;
    (assert (HiB : i < jlen B) by (apply (ws_lt B i Hi); lia)); [lia|].
  pose proof (ws_rd m b B i BB ltac:(lia)) as RD. pose proof (ws_byte B i FB) as HC.
  step. step. ws_byte_test B i; [ws_exit B i|].
  step. step. step. ws_mask_test B i W; [|ws_exit B i].
  destruct (ws_step B i ltac:(lia) W) as [_ E1]. rewrite E1 in HW |- *.
  pose proof (ws_ge B (i + 1) ltac:(lia)) as G1.
  step. step. step. rewrite ws_eqb by lia.
  replace (- jlen B =? - i + -1) with false by (symmetry; apply Z.eqb_neq; lia). cbn [negb]. cbv iota.
  eapply (IH (i + 1)); [lia | f_equal; lia | f_equal; lia | lia | exact HW].
Qed.

Lemma ws_L7 : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (b i : Z) (B : list Z),
  s0 = Z_to_bv 64 32 -> s2 = Z_to_bv 64 WS_MASK -> s3 = Z_to_bv 64 b -> s4 = Z_to_bv 64 (jlen B) -> s10 = Z_to_bv 64 i ->
  0 <= i <= jlen B ->
  0 < b -> b + jlen B + 1 < 2 ^ 63 ->
  Forall (fun c => 0 <= c < 256) B -> bytes_at rsegs m b (pf_bytes (B ++ [0])) ->
  evt rsegs
    (fun ms' => exists a0' : word,
       ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0' a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 (Z_to_bv 64 (json_ws B i)) s11 t3 t4 t5 t6)
                F (Z_to_bv 64 0x1391c) fc None m (seg_rom rsegs))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x138f8) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m b i B
    E0 E2 E3 E4 Ei Hi Hb HbB FB BB.
  subst s0 s2 s3 s4.
  remember (Z.to_nat (jlen B + 1 - i)) as k eqn:Hk.
  revert i s10 a0 Hk Ei Hi.
  induction k as [|k IH]; intros i s10 a0 Hk Ei Hi; subst s10; [lia|].
  pose proof (ws_rd m b B i BB ltac:(lia)) as RD. pose proof (ws_byte B i FB) as HC.
  step. step. step. ws_byte_test B i; [ws_exit B i|].
  step. step. step. ws_mask_test B i W; [|ws_exit B i].
  destruct (ws_step B i ltac:(lia) W) as [HiB E1]. rewrite E1.
  step. step. rewrite eqb_lit by lia.
  destruct (Z.eqb_spec (jlen B) (i + 1)) as [EN|EN]; cbn [negb]; cbv iota.
  - step. rewrite <- EN, ws_at_end. apply evt_done. eexists. reflexivity.
  - eapply (IH (i + 1)); [lia | reflexivity | lia].
Qed.

Lemma ws_L12 : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (b i : Z) (B : list Z),
  s0 = Z_to_bv 64 32 -> s2 = Z_to_bv 64 WS_MASK -> s3 = Z_to_bv 64 b -> s4 = Z_to_bv 64 (jlen B) -> a1 = Z_to_bv 64 i ->
  0 <= i <= jlen B ->
  0 < b -> b + jlen B + 1 < 2 ^ 63 ->
  Forall (fun c => 0 <= c < 256) B -> bytes_at rsegs m b (pf_bytes (B ++ [0])) ->
  evt rsegs
    (fun ms' => exists a0' : word,
       ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0' (Z_to_bv 64 (json_ws B i)) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                F (Z_to_bv 64 0x13a90) fc None m (seg_rom rsegs))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x13a6c) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m b i B
    E0 E2 E3 E4 Ei Hi Hb HbB FB BB.
  subst s0 s2 s3 s4.
  remember (Z.to_nat (jlen B + 1 - i)) as k eqn:Hk.
  revert i a1 a0 Hk Ei Hi.
  induction k as [|k IH]; intros i a1 a0 Hk Ei Hi; subst a1; [lia|].
  pose proof (ws_rd m b B i BB ltac:(lia)) as RD. pose proof (ws_byte B i FB) as HC.
  step. step. step. ws_byte_test B i; [ws_exit B i|].
  step. step. step. ws_mask_test B i W; [|ws_exit B i].
  destruct (ws_step B i ltac:(lia) W) as [HiB E1]. rewrite E1.
  step. step. rewrite eqb_lit by lia.
  destruct (Z.eqb_spec (jlen B) (i + 1)) as [EN|EN]; cbn [negb]; cbv iota.
  - step. rewrite <- EN, ws_at_end. apply evt_done. eexists. reflexivity.
  - eapply (IH (i + 1)); [lia | reflexivity | lia].
Qed.

Lemma ws_L13 : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (b i : Z) (B : list Z),
  s0 = Z_to_bv 64 32 -> s2 = Z_to_bv 64 WS_MASK -> s3 = Z_to_bv 64 b -> s4 = Z_to_bv 64 (jlen B) -> s6 = Z_to_bv 64 i ->
  0 <= i <= jlen B ->
  0 < b -> b + jlen B + 1 < 2 ^ 63 ->
  Forall (fun c => 0 <= c < 256) B -> bytes_at rsegs m b (pf_bytes (B ++ [0])) ->
  evt rsegs
    (fun ms' => exists a0' : word,
       ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0' a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 (Z_to_bv 64 (json_ws B i)) s7 s8 s9 s10 s11 t3 t4 t5 t6)
                F (Z_to_bv 64 0x13ad4) fc None m (seg_rom rsegs))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x13ab0) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m b i B
    E0 E2 E3 E4 Ei Hi Hb HbB FB BB.
  subst s0 s2 s3 s4.
  remember (Z.to_nat (jlen B + 1 - i)) as k eqn:Hk.
  revert i s6 a0 Hk Ei Hi.
  induction k as [|k IH]; intros i s6 a0 Hk Ei Hi; subst s6; [lia|].
  pose proof (ws_rd m b B i BB ltac:(lia)) as RD. pose proof (ws_byte B i FB) as HC.
  step. step. step. ws_byte_test B i; [ws_exit B i|].
  step. step. step. ws_mask_test B i W; [|ws_exit B i].
  destruct (ws_step B i ltac:(lia) W) as [HiB E1]. rewrite E1.
  step. step. rewrite eqb_lit by lia.
  destruct (Z.eqb_spec (jlen B) (i + 1)) as [EN|EN]; cbn [negb]; cbv iota.
  - step. rewrite <- EN, ws_at_end. apply evt_done. eexists. reflexivity.
  - eapply (IH (i + 1)); [lia | reflexivity | lia].
Qed.

Lemma ws_L14 : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (b i : Z) (B : list Z),
  s0 = Z_to_bv 64 32 -> s2 = Z_to_bv 64 WS_MASK -> s3 = Z_to_bv 64 b -> s4 = Z_to_bv 64 (jlen B) -> a1 = Z_to_bv 64 i ->
  0 <= i <= jlen B ->
  0 < b -> b + jlen B + 1 < 2 ^ 63 ->
  Forall (fun c => 0 <= c < 256) B -> bytes_at rsegs m b (pf_bytes (B ++ [0])) ->
  evt rsegs
    (fun ms' => exists a0' : word,
       ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0' (Z_to_bv 64 (json_ws B i)) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                F (Z_to_bv 64 0x13bdc) fc None m (seg_rom rsegs))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x13bb8) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m b i B
    E0 E2 E3 E4 Ei Hi Hb HbB FB BB.
  subst s0 s2 s3 s4.
  remember (Z.to_nat (jlen B + 1 - i)) as k eqn:Hk.
  revert i a1 a0 Hk Ei Hi.
  induction k as [|k IH]; intros i a1 a0 Hk Ei Hi; subst a1; [lia|].
  pose proof (ws_rd m b B i BB ltac:(lia)) as RD. pose proof (ws_byte B i FB) as HC.
  step. step. step. ws_byte_test B i; [ws_exit B i|].
  step. step. step. ws_mask_test B i W; [|ws_exit B i].
  destruct (ws_step B i ltac:(lia) W) as [HiB E1]. rewrite E1.
  step. step. rewrite eqb_lit by lia.
  destruct (Z.eqb_spec (jlen B) (i + 1)) as [EN|EN]; cbn [negb]; cbv iota.
  - step. rewrite <- EN, ws_at_end. apply evt_done. eexists. reflexivity.
  - eapply (IH (i + 1)); [lia | reflexivity | lia].
Qed.

Lemma ws_L17 : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (b i : Z) (B : list Z),
  s0 = Z_to_bv 64 32 -> s2 = Z_to_bv 64 WS_MASK -> a1 = Z_to_bv 64 (- jlen B) -> a2 = Z_to_bv 64 (b + i) -> a0 = Z_to_bv 64 (- i) ->
  0 <= i < jlen B -> json_ws B i = jlen B ->
  0 < b -> b + jlen B + 1 < 2 ^ 63 ->
  Forall (fun c => 0 <= c < 256) B -> bytes_at rsegs m b (pf_bytes (B ++ [0])) ->
  evt rsegs
    (fun ms' => exists a3' : word,
       ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (- jlen B)) a1 (Z_to_bv 64 (b + jlen B)) a3' a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                F (Z_to_bv 64 0x140bc) fc None m (seg_rom rsegs))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x13cfc) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m b i B
    E0 E2 En Ep Ec Hi HW Hb HbB FB BB.
  subst s0 s2 a1.
  remember (Z.to_nat (jlen B - i)) as k eqn:Hk.
  revert i a0 a2 a3 Hk Ep Ec Hi HW.
  induction k as [|k IH]; intros i a0 a2 a3 Hk Ep Ec Hi HW; subst a0 a2; [lia|].
  pose proof (ws_rd m b B i BB ltac:(lia)) as RD. pose proof (ws_byte B i FB) as HC.
  step. step. ws_byte_test B i.
  - rewrite (ws_stop B i ltac:(lia) (ws_big _ C)) in HW. lia.
  - step. step. step. ws_mask_test B i W.
    + destruct (ws_step B i ltac:(lia) W) as [_ E1]. rewrite E1 in HW.
      step. step. step. rewrite ws_eqb by lia.
      destruct (Z.eqb_spec (- jlen B) (- i + -1)) as [EN|EN]; cbn [negb]; cbv iota.
      * step. replace (- i + -1) with (- jlen B) by lia. replace (b + i + 1) with (b + jlen B) by lia.
        apply evt_done. eexists. reflexivity.
      * eapply (IH (i + 1)); [lia | f_equal; lia | f_equal; lia | lia | exact HW].
    + rewrite (ws_stop B i ltac:(lia) W) in HW. lia.
Qed.
