From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes Arr.
From OSSVerify.Proofs.libreac.fuzz_disco.lib Require Import Img0.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require Import disco_box_name_model reac_box_name_c.
Import ListNotations.
Open Scope Z_scope.

Definition sb_n (cm n0 i : Z) : Z := Z.min (n0 + i) cm.
Definition sb_o (cm n0 i : Z) (ov : word) : word := if cm <? n0 + i then Z_to_bv 64 1 else ov.
Definition sb_b (bs : list byte) (cm n0 : Z) (s : list Z) : list byte :=
  upd_bytes bs (Z.to_nat n0) (bn_bytes (firstn (Z.to_nat (cm - n0)) s)).

Lemma bl_ltu : forall a b, 0 <= a < 2^64 -> 0 <= b < 2^64 -> bv_ltu (Z_to_bv 64 a) (Z_to_bv 64 b) = (a <? b).
Proof. intros a b Ha Hb. unfold bv_ltu. rewrite !unsigned_lit by assumption. reflexivity. Qed.

Lemma bl_eqb : forall a b, 0 <= a < 2^64 -> 0 <= b < 2^64 -> bv_eqb (Z_to_bv 64 a) (Z_to_bv 64 b) = (a =? b).
Proof. intros a b Ha Hb. unfold bv_eqb. rewrite !unsigned_lit by assumption. reflexivity. Qed.

Lemma bl_zxb : forall c, 0 <= c < 256 -> zxb (Z_to_bv 8 c) = Z_to_bv 64 c.
Proof.
  intros c Hc. unfold zxb. f_equal. rewrite Z_to_bv_unsigned. apply bv_wrap_small.
  change (bv_modulus 8) with 256. lia.
Qed.

Lemma bl_le1 : forall c, 0 <= c < 256 -> le1 (Z_to_bv 64 c) = [Z_to_bv 8 c].
Proof. intros c Hc. unfold le1. rewrite unsigned_lit by lia. reflexivity. Qed.

Lemma bl_firstn1 : forall (l : list Z) j d, (j < length l)%nat -> firstn 1 (skipn j l) = [nth j l d].
Proof.
  induction l as [|x l IH]; intros j d Hj; cbn in Hj; [lia|].
  destruct j as [|j]; [reflexivity|]. cbn [skipn nth]. apply IH. lia.
Qed.

Lemma bl_rd : forall m P l j, bytes_at rsegs m P (bn_bytes l) -> (S j < length l)%nat ->
  ov_read_bytes rsegs m (Z_to_bv 64 (P + Z.of_nat j + 1)) 1 = Some [Z_to_bv 8 (nth (S j) l 0)].
Proof.
  intros m P l j H Hj. replace (Z_to_bv 64 (P + Z.of_nat j + 1)) with (wa (P + Z.of_nat (S j))) by (unfold wa; f_equal; lia).
  rewrite (bytes_at_ov_read rsegs m P (bn_bytes l) (S j) 1 H) by (unfold bn_bytes; rewrite length_map; lia).
  unfold bn_bytes. rewrite skipn_map, firstn_map. rewrite (bl_firstn1 l (S j) 0 Hj). reflexivity.
Qed.

Lemma bl_nth_rng : forall s j, Forall (fun c => 0 < c < 256) s -> 0 <= nth j (s ++ [0]) 0 < 256.
Proof.
  intros s j H. destruct (Nat.ltb_spec j (length (s ++ [0]))) as [L|L].
  - assert (I : In (nth j (s ++ [0]) 0) (s ++ [0])) by (apply nth_In; exact L).
    apply in_app_or in I. destruct I as [I|I].
    + rewrite Forall_forall in H. specialize (H _ I). lia.
    + destruct I as [I|I]; [lia|destruct I].
  - rewrite nth_overflow by lia. lia.
Qed.

Lemma bl_store : forall m0 m1 B L buf P src i c,
  u8arr rsegs m1 B buf -> Z.of_nat (length buf) = L -> bytes_at rsegs m1 P src ->
  munch [(B, B + L)] m0 m1 -> wmono rsegs m0 m1 -> mem_inv rsegs m1 ->
  0 <= i < L -> (P + Z.of_nat (length src) <= B \/ B + L <= P) ->
  u8arr rsegs (write_to_mem m1 (Z_to_bv 64 (B + i)) [c]) B (upd buf (Z.to_nat i) c) /\
  bytes_at rsegs (write_to_mem m1 (Z_to_bv 64 (B + i)) [c]) P src /\
  munch [(B, B + L)] m0 (write_to_mem m1 (Z_to_bv 64 (B + i)) [c]) /\
  wmono rsegs m0 (write_to_mem m1 (Z_to_bv 64 (B + i)) [c]) /\
  mem_inv rsegs (write_to_mem m1 (Z_to_bv 64 (B + i)) [c]).
Proof.
  intros m0 m1 B L buf P src i c HU HL HS MU WM MI Hi DJ.
  pose proof (u8arr_bound rsegs m1 B buf HU) as BB.
  pose proof (bytes_at_bound rsegs m1 P src HS) as SB.
  change (Z_to_bv 64 (B + i)) with (wa (B + i)).
  split; [apply u8arr_write; [exact HU | lia]|].
  split; [apply bytes_at_write_other; [exact HS | lia | cbn; lia | cbn; lia]|].
  split; [apply munch_write; [exact MU | lia | cbn; lia | cbn; lia]|].
  split; [apply wmono_write; exact WM|].
  apply mem_inv_store; [exact MI|]. apply (u8arr_store_ok rsegs m1 B buf i); [exact HU | lia | reflexivity].
Qed.

Lemma bl_upd_mid : forall {X} (l1 l2 : list X) y x, upd (l1 ++ y :: l2) (length l1) x = l1 ++ x :: l2.
Proof. intros X l1. induction l1 as [|z l1 IH]; intros l2 y x; cbn; [reflexivity|]. rewrite IH. reflexivity. Qed.

Lemma bl_skipn_cons : forall {X} n (l : list X) d, (n < length l)%nat -> skipn n l = nth n l d :: skipn (S n) l.
Proof.
  intros X n. induction n as [|n IH]; intros l d H; destruct l as [|x l]; cbn in *; try lia; [reflexivity|].
  apply IH. lia.
Qed.

Lemma bl_firstn_snoc : forall {X} (l : list X) i d, (i < length l)%nat -> firstn (S i) l = firstn i l ++ [nth i l d].
Proof.
  intros X l. induction l as [|x l IH]; intros i d H; cbn in H; [lia|].
  destruct i as [|i]; [reflexivity|]. cbn [firstn nth]. rewrite (IH i d) by lia. reflexivity.
Qed.

Lemma bl_upd_bytes_snoc : forall cs k xs b, (k + length xs < length cs)%nat ->
  upd (upd_bytes cs k xs) (k + length xs) b = upd_bytes cs k (xs ++ [b]).
Proof.
  intros cs k xs b H. unfold upd_bytes.
  rewrite (bl_skipn_cons (k + length xs) cs b) by lia.
  rewrite length_app. cbn [length].
  replace (k + (length xs + 1))%nat with (S (k + length xs)) by lia.
  generalize (skipn (S (k + length xs)) cs) (nth (k + length xs) cs b). intros R r.
  rewrite app_assoc.
  replace (k + length xs)%nat with (length (firstn k cs ++ xs)) by (rewrite length_app, length_firstn; lia).
  rewrite bl_upd_mid. rewrite <- !app_assoc. reflexivity.
Qed.

Lemma sb_b_step : forall bs cm n0 s i,
  (Z.to_nat n0 + i < length bs)%nat -> 0 <= n0 -> (i < length s)%nat -> n0 + Z.of_nat i < cm ->
  upd (sb_b bs cm n0 (firstn i s)) (Z.to_nat (n0 + Z.of_nat i)) (Z_to_bv 8 (nth i s 0)) =
  sb_b bs cm n0 (firstn (S i) s).
Proof.
  intros bs cm n0 s i Hb Hn Hi Hc. unfold sb_b. rewrite !firstn_firstn.
  replace (Nat.min (Z.to_nat (cm - n0)) i) with i by lia.
  replace (Nat.min (Z.to_nat (cm - n0)) (S i)) with (S i) by lia.
  rewrite (bl_firstn_snoc s i 0) by exact Hi.
  unfold bn_bytes. rewrite map_app. cbn [map].
  replace (Z.to_nat (n0 + Z.of_nat i)) with (Z.to_nat n0 + length (map (Z_to_bv 8) (firstn i s)))%nat
    by (rewrite length_map, length_firstn; lia).
  apply bl_upd_bytes_snoc. rewrite length_map, length_firstn. lia.
Qed.

Lemma sb_b_full : forall bs cm n0 s i,
  cm <= n0 + Z.of_nat i -> sb_b bs cm n0 (firstn (S i) s) = sb_b bs cm n0 (firstn i s).
Proof.
  intros bs cm n0 s i Hc. unfold sb_b. rewrite !firstn_firstn.
  replace (Nat.min (Z.to_nat (cm - n0)) (S i)) with (Nat.min (Z.to_nat (cm - n0)) i) by lia.
  reflexivity.
Qed.

Lemma sb_b_length : forall bs cm n0 s, 0 <= n0 <= cm -> Z.of_nat (length bs) = cm + 1 ->
  length (sb_b bs cm n0 s) = length bs.
Proof.
  intros bs cm n0 s Hn Hb. unfold sb_b. apply upd_bytes_length. unfold bn_bytes.
  rewrite length_map, length_firstn. lia.
Qed.

Lemma sb_b_nil : forall bs cm n0, sb_b bs cm n0 [] = bs.
Proof.
  intros bs cm n0. unfold sb_b, upd_bytes, bn_bytes. rewrite firstn_nil. cbn [map app length].
  rewrite Nat.add_0_r. apply firstn_skipn.
Qed.

Ltac zl_tail ex P s i CR IH :=
  intros m2 n' ov' x' Hn' Hov' HU2 HS2 MU2 WM2 MI2;
  pose proof (bl_rd m2 P (s ++ [0]) i HS2 ltac:(rewrite length_app; cbn [length]; lia)) as RD;
  pose proof (bl_nth_rng s (S i) CR) as Rc';
  step;
  clear RD; rewrite bl_zxb by lia;
  step; step;
  rewrite bl_eqb by lia;
  destruct (Nat.ltb_spec (S i) (length s)) as [Hl|Hl];
  [ rewrite app_nth1 in * by lia;
    assert (Rc2 : 0 < nth (S i) s 0 < 256) by (rewrite Forall_forall in CR; apply CR; apply nth_In; exact Hl);
    if_true;
    replace (P + Z.of_nat i + 2) with (P + Z.of_nat (S i) + 1) by lia;
    eapply (IH (S i)); try eassumption; lia
  | rewrite app_nth2 by lia; replace (S i - length s)%nat with 0%nat by lia; cbn [nth];
    if_false;
    (lazymatch ex with true => step | false => idtac end);
    rewrite firstn_all2 in HU2 by lia;
    replace (Z_to_bv 64 (P + Z.of_nat i + 2)) with (Z_to_bv 64 (P + Z.of_nat (length s) + 1)) by (f_equal; lia);
    replace (S i) with (length s) in Hn', Hov' by lia;
    subst n' ov';
    apply evt_done; hnf; eexists; exists m2; split; [reflexivity|];
    split; [exact HU2|]; split; [exact MU2|]; split; [exact WM2|exact MI2] ].

Ltac zl_over cm n0 i TAIL HU1 :=
  step;
  eapply TAIL; try eassumption;
  [ unfold sb_n; lia
  | unfold sb_o; replace (cm <? n0 + Z.of_nat (S i)) with true by (symmetry; apply Z.ltb_lt; lia); reflexivity
  | rewrite sb_b_full by lia; exact HU1 ].

Ltac zl_store cm L m m1 B P s i n n0 TAIL HU1 HS1 MU1 WM1 MI1 Hov :=
  step;
  pose proof (u8arr_store_ok rsegs m1 B _ n _ HU1 ltac:(rewrite sb_b_length by lia; lia) eq_refl) as HST;
  step;
  rewrite (bl_le1 (nth i s 0)) by lia;
  destruct (bl_store m m1 B L _ P (bn_bytes (s ++ [0])) n (Z_to_bv 8 (nth i s 0)) HU1
              ltac:(rewrite sb_b_length by lia; lia) HS1 MU1 WM1 MI1 ltac:(lia)
              ltac:(unfold bn_bytes; rewrite length_map, length_app; cbn [length]; lia))
    as (HU2 & HS2 & MU2 & WM2 & MI2);
  remember (write_to_mem m1 (Z_to_bv 64 (B + n)) [Z_to_bv 8 (nth i s 0)]) as m2 eqn:Em2;
  clear Em2 HST;
  replace n with (n0 + Z.of_nat i) in HU2 by lia;
  rewrite sb_b_step in HU2 by lia;
  step; step;
  eapply TAIL; try eassumption;
  [ unfold sb_n; lia
  | rewrite Hov; unfold sb_o;
    replace (cm <? n0 + Z.of_nat (S i)) with false by (symmetry; apply Z.ltb_ge; lia);
    replace (cm <? n0 + Z.of_nat i) with false by (symmetry; apply Z.ltb_ge; lia); reflexivity ].

Ltac zl_body cm L m m1 B P s i n n0 TAIL HU1 HS1 MU1 WM1 MI1 Hov :=
  step; step;
  rewrite bl_ltu by lia;
  destruct (Z.ltb_spec cm (n + 1)) as [Hc|Hc];
  [ zl_over cm n0 i TAIL HU1
  | zl_store cm L m m1 B P s i n n0 TAIL HU1 HS1 MU1 WM1 MI1 Hov ].

Ltac zl_body_geu cm L m m1 B P s i n n0 TAIL HU1 HS1 MU1 WM1 MI1 Hov :=
  step; step;
  rewrite bl_ltu by lia;
  destruct (Z.ltb_spec (n + 1) L) as [Hc|Hc]; cbn [negb];
  [ zl_store cm L m m1 B P s i n n0 TAIL HU1 HS1 MU1 WM1 MI1 Hov
  | zl_over cm n0 i TAIL HU1 ].

Ltac pl_tail P s i CR IH :=
  intros m2 n' ov' x' Hn' Hov' HU2 HS2 MU2 WM2 MI2;
  pose proof (bl_rd m2 P (s ++ [0]) i HS2 ltac:(rewrite length_app; cbn [length]; lia)) as RD;
  pose proof (bl_nth_rng s (S i) CR) as Rc';
  step;
  clear RD; rewrite bl_zxb by lia;
  step; step;
  rewrite bl_eqb by lia;
  destruct (Nat.ltb_spec (S i) (length s)) as [Hl|Hl];
  [ rewrite app_nth1 in * by lia;
    if_true;
    replace (P + Z.of_nat i + 2) with (P + Z.of_nat (S i) + 1) by lia;
    eapply (IH (S i)); try eassumption; lia
  | rewrite app_nth2 by lia; replace (S i - length s)%nat with 0%nat by lia; cbn [nth];
    if_false;
    rewrite firstn_all2 in HU2 by lia;
    replace (Z_to_bv 64 (P + Z.of_nat i + 2)) with (Z_to_bv 64 (P + Z.of_nat (length s) + 1)) by (f_equal; lia);
    replace (S i) with (length s) in Hn', Hov' by lia;
    subst n' ov';
    apply evt_done; hnf; eexists; exists m2; split; [reflexivity|];
    split; [exact HU2|]; split; [exact MU2|]; split; [exact WM2|exact MI2] ].

Ltac zl_init cm P s n0 LOOP HU :=
  replace (P + 1) with (P + Z.of_nat 0 + 1) by lia;
  replace (hd 0 s) with (nth 0 s 0) by (destruct s; reflexivity);
  eapply (LOOP (length s) 0%nat); try eassumption;
  [ lia
  | destruct s as [|c s']; [congruence|]; cbn [length]; lia
  | unfold sb_n; lia
  | unfold sb_o; replace (cm <? n0 + Z.of_nat 0) with false by (symmetry; apply Z.ltb_ge; lia); reflexivity
  | cbn [firstn]; rewrite sb_b_nil; exact HU
  | apply munch_refl
  | apply wmono_refl ].

Lemma box_name_stem_loop : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (P B n0 : Z) (ov0 : word) (s : list Z)
    (bs : list byte),
  s <> [] -> Forall (fun c => 0 < c < 256) s -> bytes_at rsegs m P (bn_bytes (s ++ [0])) ->
  u8arr rsegs m B bs -> length bs = 24%nat -> 0 <= n0 <= 23 ->
  (P + Z.of_nat (length s) + 1 <= B \/ B + 24 <= P) -> mem_inv rsegs m ->
  evt rsegs
    (fun ms' => exists (x15 : word) (m' : word -> option byte),
       ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 (Z_to_bv 64 (P + Z.of_nat (length s) + 1)) (Z_to_bv 64 23)
                     (Z_to_bv 64 B) (Z_to_bv 64 0) x15 a6 a7 s2 s3 s4 s5 s6 s7 s8
                     (Z_to_bv 64 (sb_n 23 n0 (Z.of_nat (length s)))) (sb_o 23 n0 (Z.of_nat (length s)) ov0)
                     s11 t3 t4 t5 t6)
                F (Z_to_bv 64 0x14d0c) fc None m' (seg_rom rsegs) /\
       u8arr rsegs m' B (sb_b bs 23 n0 s) /\ munch [(B, B + 24)] m m' /\ wmono rsegs m m' /\ mem_inv rsegs m')
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 (Z_to_bv 64 (P + 1)) (Z_to_bv 64 23) (Z_to_bv 64 B)
             (Z_to_bv 64 (hd 0 s)) a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 (Z_to_bv 64 n0) ov0 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x14cd8) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s11 t3 t4 t5 t6 F fc m P B n0 ov0 s bs
    NE CR HS HU LB Hn0 DJ MI.
  lazymatch goal with |- evt _ ?Q _ => set (QQ := Q) end.
  pose proof (bytes_at_bound rsegs m P _ HS) as SB.
  unfold bn_bytes in SB. rewrite length_map, length_app in SB. cbn [length] in SB.
  pose proof (u8arr_bound rsegs m B bs HU) as BB. rewrite LB in BB.
  assert (LOOP : forall (k i : nat) (m1 : word -> option byte) (n : Z) (ov x15 : word),
    k = (length s - i)%nat -> (i < length s)%nat ->
    n = sb_n 23 n0 (Z.of_nat i) -> ov = sb_o 23 n0 (Z.of_nat i) ov0 ->
    u8arr rsegs m1 B (sb_b bs 23 n0 (firstn i s)) -> bytes_at rsegs m1 P (bn_bytes (s ++ [0])) ->
    munch [(B, B + 24)] m m1 -> wmono rsegs m m1 -> mem_inv rsegs m1 ->
    evt rsegs QQ (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 (Z_to_bv 64 (P + Z.of_nat i + 1)) (Z_to_bv 64 23)
                       (Z_to_bv 64 B) (Z_to_bv 64 (nth i s 0)) x15 a6 a7 s2 s3 s4 s5 s6 s7 s8 (Z_to_bv 64 n) ov
                       s11 t3 t4 t5 t6)
                  F (Z_to_bv 64 0x14cd8) fc None m1 (seg_rom rsegs))).
  { induction k as [|k IH]; intros i m1 n ov x15 Hk Hi Hn Hov HU1 HS1 MU1 WM1 MI1; [lia|].
    assert (Rn : n = Z.min (n0 + Z.of_nat i) 23) by (rewrite Hn; reflexivity).
    assert (Rc : 0 < nth i s 0 < 256) by (rewrite Forall_forall in CR; apply CR; apply nth_In; exact Hi).
    assert (TAIL : forall (m2 : word -> option byte) (n' : Z) (ov' x15' : word),
      n' = sb_n 23 n0 (Z.of_nat (S i)) -> ov' = sb_o 23 n0 (Z.of_nat (S i)) ov0 ->
      u8arr rsegs m2 B (sb_b bs 23 n0 (firstn (S i) s)) -> bytes_at rsegs m2 P (bn_bytes (s ++ [0])) ->
      munch [(B, B + 24)] m m2 -> wmono rsegs m m2 -> mem_inv rsegs m2 ->
      evt rsegs QQ (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 (Z_to_bv 64 (P + Z.of_nat i + 1)) (Z_to_bv 64 23)
                         (Z_to_bv 64 B) (Z_to_bv 64 (nth i s 0)) x15' a6 a7 s2 s3 s4 s5 s6 s7 s8 (Z_to_bv 64 n') ov'
                         s11 t3 t4 t5 t6)
                    F (Z_to_bv 64 0x14cf4) fc None m2 (seg_rom rsegs))).
    { zl_tail true P s i CR IH. }
    zl_body constr:(23) constr:(24) m m1 B P s i n n0 TAIL HU1 HS1 MU1 WM1 MI1 Hov. }
  zl_init constr:(23) P s n0 LOOP HU.
Qed.

Lemma box_name_w4_loop : forall (ra sp gp tp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (P B n0 : Z) (ov0 : word) (s : list Z)
    (bs : list byte),
  s <> [] -> Forall (fun c => 0 < c < 256) s -> bytes_at rsegs m P (bn_bytes (s ++ [0])) ->
  u8arr rsegs m B bs -> length bs = 24%nat -> 0 <= n0 <= 23 ->
  (P + Z.of_nat (length s) + 1 <= B \/ B + 24 <= P) -> mem_inv rsegs m ->
  evt rsegs
    (fun ms' => exists (x14 : word) (m' : word -> option byte),
       ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (P + Z.of_nat (length s) + 1)) (Z_to_bv 64 23)
                     (Z_to_bv 64 B) (Z_to_bv 64 0) x14 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8
                     (Z_to_bv 64 (sb_n 23 n0 (Z.of_nat (length s)))) (sb_o 23 n0 (Z.of_nat (length s)) ov0)
                     s11 t3 t4 t5 t6)
                F (Z_to_bv 64 0x14dd8) fc None m' (seg_rom rsegs) /\
       u8arr rsegs m' B (sb_b bs 23 n0 s) /\ munch [(B, B + 24)] m m' /\ wmono rsegs m m' /\ mem_inv rsegs m')
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (P + 1)) (Z_to_bv 64 23) (Z_to_bv 64 B)
             (Z_to_bv 64 (hd 0 s)) a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 (Z_to_bv 64 n0) ov0 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x14db0) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s11 t3 t4 t5 t6 F fc m P B n0 ov0 s bs
    NE CR HS HU LB Hn0 DJ MI.
  lazymatch goal with |- evt _ ?Q _ => set (QQ := Q) end.
  pose proof (bytes_at_bound rsegs m P _ HS) as SB.
  unfold bn_bytes in SB. rewrite length_map, length_app in SB. cbn [length] in SB.
  pose proof (u8arr_bound rsegs m B bs HU) as BB. rewrite LB in BB.
  assert (LOOP : forall (k i : nat) (m1 : word -> option byte) (n : Z) (ov x14 : word),
    k = (length s - i)%nat -> (i < length s)%nat ->
    n = sb_n 23 n0 (Z.of_nat i) -> ov = sb_o 23 n0 (Z.of_nat i) ov0 ->
    u8arr rsegs m1 B (sb_b bs 23 n0 (firstn i s)) -> bytes_at rsegs m1 P (bn_bytes (s ++ [0])) ->
    munch [(B, B + 24)] m m1 -> wmono rsegs m m1 -> mem_inv rsegs m1 ->
    evt rsegs QQ (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (P + Z.of_nat i + 1)) (Z_to_bv 64 23)
                       (Z_to_bv 64 B) (Z_to_bv 64 (nth i s 0)) x14 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 (Z_to_bv 64 n) ov
                       s11 t3 t4 t5 t6)
                  F (Z_to_bv 64 0x14db0) fc None m1 (seg_rom rsegs))).
  { induction k as [|k IH]; intros i m1 n ov x14 Hk Hi Hn Hov HU1 HS1 MU1 WM1 MI1; [lia|].
    assert (Rn : n = Z.min (n0 + Z.of_nat i) 23) by (rewrite Hn; reflexivity).
    assert (Rc : 0 < nth i s 0 < 256) by (rewrite Forall_forall in CR; apply CR; apply nth_In; exact Hi).
    assert (TAIL : forall (m2 : word -> option byte) (n' : Z) (ov' x14' : word),
      n' = sb_n 23 n0 (Z.of_nat (S i)) -> ov' = sb_o 23 n0 (Z.of_nat (S i)) ov0 ->
      u8arr rsegs m2 B (sb_b bs 23 n0 (firstn (S i) s)) -> bytes_at rsegs m2 P (bn_bytes (s ++ [0])) ->
      munch [(B, B + 24)] m m2 -> wmono rsegs m m2 -> mem_inv rsegs m2 ->
      evt rsegs QQ (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (P + Z.of_nat i + 1)) (Z_to_bv 64 23)
                         (Z_to_bv 64 B) (Z_to_bv 64 (nth i s 0)) x14' a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 (Z_to_bv 64 n') ov'
                         s11 t3 t4 t5 t6)
                    F (Z_to_bv 64 0x14dcc) fc None m2 (seg_rom rsegs))).
    { zl_tail false P s i CR IH. }
    zl_body constr:(23) constr:(24) m m1 B P s i n n0 TAIL HU1 HS1 MU1 WM1 MI1 Hov. }
  zl_init constr:(23) P s n0 LOOP HU.
Qed.

Lemma box_name_nm_dp_loop : forall (ra sp gp tp t0 t1 t2 s0 s1 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (P B n0 : Z) (ov0 : word) (s : list Z)
    (bs : list byte),
  s <> [] -> Forall (fun c => 0 < c < 256) s -> bytes_at rsegs m P (bn_bytes (s ++ [0])) ->
  u8arr rsegs m B bs -> length bs = 48%nat -> 0 <= n0 <= 47 ->
  (P + Z.of_nat (length s) + 1 <= B \/ B + 48 <= P) -> mem_inv rsegs m ->
  evt rsegs
    (fun ms' => exists (x16 : word) (m' : word -> option byte),
       ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 B) (sb_o 47 n0 (Z.of_nat (length s)) ov0)
                     (Z_to_bv 64 (sb_n 47 n0 (Z.of_nat (length s)))) (Z_to_bv 64 0)
                     (Z_to_bv 64 (P + Z.of_nat (length s) + 1)) (Z_to_bv 64 47) x16 a7
                     s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                F (Z_to_bv 64 0x14ecc) fc None m' (seg_rom rsegs) /\
       u8arr rsegs m' B (sb_b bs 47 n0 s) /\ munch [(B, B + 48)] m m' /\ wmono rsegs m m' /\ mem_inv rsegs m')
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 B) ov0 (Z_to_bv 64 n0) (Z_to_bv 64 (hd 0 s))
             (Z_to_bv 64 (P + 1)) (Z_to_bv 64 47) a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x14ea4) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m P B n0 ov0 s bs
    NE CR HS HU LB Hn0 DJ MI.
  lazymatch goal with |- evt _ ?Q _ => set (QQ := Q) end.
  pose proof (bytes_at_bound rsegs m P _ HS) as SB.
  unfold bn_bytes in SB. rewrite length_map, length_app in SB. cbn [length] in SB.
  pose proof (u8arr_bound rsegs m B bs HU) as BB. rewrite LB in BB.
  assert (LOOP : forall (k i : nat) (m1 : word -> option byte) (n : Z) (ov x16 : word),
    k = (length s - i)%nat -> (i < length s)%nat ->
    n = sb_n 47 n0 (Z.of_nat i) -> ov = sb_o 47 n0 (Z.of_nat i) ov0 ->
    u8arr rsegs m1 B (sb_b bs 47 n0 (firstn i s)) -> bytes_at rsegs m1 P (bn_bytes (s ++ [0])) ->
    munch [(B, B + 48)] m m1 -> wmono rsegs m m1 -> mem_inv rsegs m1 ->
    evt rsegs QQ (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 B) ov (Z_to_bv 64 n) (Z_to_bv 64 (nth i s 0))
                       (Z_to_bv 64 (P + Z.of_nat i + 1)) (Z_to_bv 64 47) x16 a7
                       s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (Z_to_bv 64 0x14ea4) fc None m1 (seg_rom rsegs))).
  { induction k as [|k IH]; intros i m1 n ov x16 Hk Hi Hn Hov HU1 HS1 MU1 WM1 MI1; [lia|].
    assert (Rn : n = Z.min (n0 + Z.of_nat i) 47) by (rewrite Hn; reflexivity).
    assert (Rc : 0 < nth i s 0 < 256) by (rewrite Forall_forall in CR; apply CR; apply nth_In; exact Hi).
    assert (TAIL : forall (m2 : word -> option byte) (n' : Z) (ov' x16' : word),
      n' = sb_n 47 n0 (Z.of_nat (S i)) -> ov' = sb_o 47 n0 (Z.of_nat (S i)) ov0 ->
      u8arr rsegs m2 B (sb_b bs 47 n0 (firstn (S i) s)) -> bytes_at rsegs m2 P (bn_bytes (s ++ [0])) ->
      munch [(B, B + 48)] m m2 -> wmono rsegs m m2 -> mem_inv rsegs m2 ->
      evt rsegs QQ (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 B) ov' (Z_to_bv 64 n') (Z_to_bv 64 (nth i s 0))
                         (Z_to_bv 64 (P + Z.of_nat i + 1)) (Z_to_bv 64 47) x16' a7
                         s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                    F (Z_to_bv 64 0x14ec0) fc None m2 (seg_rom rsegs))).
    { zl_tail false P s i CR IH. }
    zl_body constr:(47) constr:(48) m m1 B P s i n n0 TAIL HU1 HS1 MU1 WM1 MI1 Hov. }
  zl_init constr:(47) P s n0 LOOP HU.
Qed.

Lemma box_name_paren_loop : forall (ra sp gp tp t0 t1 t2 s0 s1 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (P B n0 : Z) (ov0 : word) (s : list Z)
    (bs : list byte),
  s <> [] -> Forall (fun c => 0 < c < 256) s -> bytes_at rsegs m P (bn_bytes (s ++ [0])) ->
  P + Z.of_nat (length s) + 1 < 2^64 ->
  u8arr rsegs m B bs -> length bs = 48%nat -> 0 <= n0 <= 47 ->
  (P + Z.of_nat (length s) + 1 <= B \/ B + 48 <= P) -> mem_inv rsegs m ->
  evt rsegs
    (fun ms' => exists (x17 : word) (m' : word -> option byte),
       ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 B) (sb_o 47 n0 (Z.of_nat (length s)) ov0)
                     (Z_to_bv 64 (sb_n 47 n0 (Z.of_nat (length s)))) (Z_to_bv 64 47)
                     (Z_to_bv 64 (P + Z.of_nat (length s) + 1)) (Z_to_bv 64 (P + Z.of_nat (length s) + 1))
                     (Z_to_bv 64 0) x17 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                F (Z_to_bv 64 0x14f0c) fc None m' (seg_rom rsegs) /\
       u8arr rsegs m' B (sb_b bs 47 n0 s) /\ munch [(B, B + 48)] m m' /\ wmono rsegs m m' /\ mem_inv rsegs m')
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 B) ov0 (Z_to_bv 64 n0) (Z_to_bv 64 47) (Z_to_bv 64 (P + 1))
             (Z_to_bv 64 (P + Z.of_nat (length s) + 1)) (Z_to_bv 64 (hd 0 s)) a7
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x14ee4) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m P B n0 ov0 s bs
    NE CR HS HE HU LB Hn0 DJ MI.
  lazymatch goal with |- evt _ ?Q _ => set (QQ := Q) end.
  pose proof (bytes_at_bound rsegs m P _ HS) as SB.
  unfold bn_bytes in SB. rewrite length_map, length_app in SB. cbn [length] in SB.
  pose proof (u8arr_bound rsegs m B bs HU) as BB. rewrite LB in BB.
  assert (LOOP : forall (k i : nat) (m1 : word -> option byte) (n : Z) (ov x17 : word),
    k = (length s - i)%nat -> (i < length s)%nat ->
    n = sb_n 47 n0 (Z.of_nat i) -> ov = sb_o 47 n0 (Z.of_nat i) ov0 ->
    u8arr rsegs m1 B (sb_b bs 47 n0 (firstn i s)) -> bytes_at rsegs m1 P (bn_bytes (s ++ [0])) ->
    munch [(B, B + 48)] m m1 -> wmono rsegs m m1 -> mem_inv rsegs m1 ->
    evt rsegs QQ (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 B) ov (Z_to_bv 64 n) (Z_to_bv 64 47)
                       (Z_to_bv 64 (P + Z.of_nat i + 1)) (Z_to_bv 64 (P + Z.of_nat (length s) + 1))
                       (Z_to_bv 64 (nth i s 0)) x17 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (Z_to_bv 64 0x14ee4) fc None m1 (seg_rom rsegs))).
  { induction k as [|k IH]; intros i m1 n ov x17 Hk Hi Hn Hov HU1 HS1 MU1 WM1 MI1; [lia|].
    assert (Rn : n = Z.min (n0 + Z.of_nat i) 47) by (rewrite Hn; reflexivity).
    assert (Rc : 0 < nth i s 0 < 256) by (rewrite Forall_forall in CR; apply CR; apply nth_In; exact Hi).
    assert (TAIL : forall (m2 : word -> option byte) (n' : Z) (ov' x17' : word),
      n' = sb_n 47 n0 (Z.of_nat (S i)) -> ov' = sb_o 47 n0 (Z.of_nat (S i)) ov0 ->
      u8arr rsegs m2 B (sb_b bs 47 n0 (firstn (S i) s)) -> bytes_at rsegs m2 P (bn_bytes (s ++ [0])) ->
      munch [(B, B + 48)] m m2 -> wmono rsegs m m2 -> mem_inv rsegs m2 ->
      evt rsegs QQ (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 B) ov' (Z_to_bv 64 n') (Z_to_bv 64 47)
                         (Z_to_bv 64 (P + Z.of_nat i + 1)) (Z_to_bv 64 (P + Z.of_nat (length s) + 1))
                         (Z_to_bv 64 (nth i s 0)) x17' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                    F (Z_to_bv 64 0x14f00) fc None m2 (seg_rom rsegs))).
    { pl_tail P s i CR IH. }
    zl_body constr:(47) constr:(48) m m1 B P s i n n0 TAIL HU1 HS1 MU1 WM1 MI1 Hov. }
  zl_init constr:(47) P s n0 LOOP HU.
Qed.

Lemma box_name_in_loop : forall (ra sp gp tp t0 t1 t2 s0 s1 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (P B n0 : Z) (ov0 : word) (s : list Z)
    (bs : list byte),
  s <> [] -> Forall (fun c => 0 < c < 256) s -> bytes_at rsegs m P (bn_bytes (s ++ [0])) ->
  P + Z.of_nat (length s) + 1 < 2^64 ->
  u8arr rsegs m B bs -> length bs = 48%nat -> 0 <= n0 <= 47 ->
  (P + Z.of_nat (length s) + 1 <= B \/ B + 48 <= P) -> mem_inv rsegs m ->
  evt rsegs
    (fun ms' => exists (x17 : word) (m' : word -> option byte),
       ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 B) (Z_to_bv 64 48) (sb_o 47 n0 (Z.of_nat (length s)) ov0)
                     (Z_to_bv 64 (sb_n 47 n0 (Z.of_nat (length s))))
                     (Z_to_bv 64 (P + Z.of_nat (length s) + 1)) (Z_to_bv 64 (P + Z.of_nat (length s) + 1))
                     (Z_to_bv 64 0) x17 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                F (Z_to_bv 64 0x14f70) fc None m' (seg_rom rsegs) /\
       u8arr rsegs m' B (sb_b bs 47 n0 s) /\ munch [(B, B + 48)] m m' /\ wmono rsegs m m' /\ mem_inv rsegs m')
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 B) (Z_to_bv 64 48) ov0 (Z_to_bv 64 n0) (Z_to_bv 64 (P + 1))
             (Z_to_bv 64 (P + Z.of_nat (length s) + 1)) (Z_to_bv 64 (hd 0 s)) a7
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x14f48) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m P B n0 ov0 s bs
    NE CR HS HE HU LB Hn0 DJ MI.
  lazymatch goal with |- evt _ ?Q _ => set (QQ := Q) end.
  pose proof (bytes_at_bound rsegs m P _ HS) as SB.
  unfold bn_bytes in SB. rewrite length_map, length_app in SB. cbn [length] in SB.
  pose proof (u8arr_bound rsegs m B bs HU) as BB. rewrite LB in BB.
  assert (LOOP : forall (k i : nat) (m1 : word -> option byte) (n : Z) (ov x17 : word),
    k = (length s - i)%nat -> (i < length s)%nat ->
    n = sb_n 47 n0 (Z.of_nat i) -> ov = sb_o 47 n0 (Z.of_nat i) ov0 ->
    u8arr rsegs m1 B (sb_b bs 47 n0 (firstn i s)) -> bytes_at rsegs m1 P (bn_bytes (s ++ [0])) ->
    munch [(B, B + 48)] m m1 -> wmono rsegs m m1 -> mem_inv rsegs m1 ->
    evt rsegs QQ (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 B) (Z_to_bv 64 48) ov (Z_to_bv 64 n)
                       (Z_to_bv 64 (P + Z.of_nat i + 1)) (Z_to_bv 64 (P + Z.of_nat (length s) + 1))
                       (Z_to_bv 64 (nth i s 0)) x17 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (Z_to_bv 64 0x14f48) fc None m1 (seg_rom rsegs))).
  { induction k as [|k IH]; intros i m1 n ov x17 Hk Hi Hn Hov HU1 HS1 MU1 WM1 MI1; [lia|].
    assert (Rn : n = Z.min (n0 + Z.of_nat i) 47) by (rewrite Hn; reflexivity).
    assert (Rc : 0 < nth i s 0 < 256) by (rewrite Forall_forall in CR; apply CR; apply nth_In; exact Hi).
    assert (TAIL : forall (m2 : word -> option byte) (n' : Z) (ov' x17' : word),
      n' = sb_n 47 n0 (Z.of_nat (S i)) -> ov' = sb_o 47 n0 (Z.of_nat (S i)) ov0 ->
      u8arr rsegs m2 B (sb_b bs 47 n0 (firstn (S i) s)) -> bytes_at rsegs m2 P (bn_bytes (s ++ [0])) ->
      munch [(B, B + 48)] m m2 -> wmono rsegs m m2 -> mem_inv rsegs m2 ->
      evt rsegs QQ (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 B) (Z_to_bv 64 48) ov' (Z_to_bv 64 n')
                         (Z_to_bv 64 (P + Z.of_nat i + 1)) (Z_to_bv 64 (P + Z.of_nat (length s) + 1))
                         (Z_to_bv 64 (nth i s 0)) x17' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                    F (Z_to_bv 64 0x14f64) fc None m2 (seg_rom rsegs))).
    { pl_tail P s i CR IH. }
    zl_body_geu constr:(47) constr:(48) m m1 B P s i n n0 TAIL HU1 HS1 MU1 WM1 MI1 Hov. }
  zl_init constr:(47) P s n0 LOOP HU.
Qed.

Lemma box_name_out_loop : forall (ra sp gp tp t0 t1 t2 s0 s1 a6 a7 s2 s3 s4 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (P B n0 : Z) (ov0 : word) (s : list Z)
    (bs : list byte),
  s <> [] -> Forall (fun c => 0 < c < 256) s -> bytes_at rsegs m P (bn_bytes (s ++ [0])) ->
  P + Z.of_nat (length s) + 1 < 2^64 ->
  u8arr rsegs m B bs -> length bs = 48%nat -> 0 <= n0 <= 47 ->
  (P + Z.of_nat (length s) + 1 <= B \/ B + 48 <= P) -> mem_inv rsegs m ->
  evt rsegs
    (fun ms' => exists (x16 : word) (m' : word -> option byte),
       ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 B) (sb_o 47 n0 (Z.of_nat (length s)) ov0) (Z_to_bv 64 48)
                     (Z_to_bv 64 (P + Z.of_nat (length s) + 1)) (Z_to_bv 64 (P + Z.of_nat (length s) + 1))
                     (Z_to_bv 64 0) x16 a7 s2 s3 s4 (Z_to_bv 64 (sb_n 47 n0 (Z.of_nat (length s))))
                     s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                F (Z_to_bv 64 0x14fd4) fc None m' (seg_rom rsegs) /\
       u8arr rsegs m' B (sb_b bs 47 n0 s) /\ munch [(B, B + 48)] m m' /\ wmono rsegs m m' /\ mem_inv rsegs m')
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 B) ov0 (Z_to_bv 64 48) (Z_to_bv 64 (P + 1))
             (Z_to_bv 64 (P + Z.of_nat (length s) + 1)) (Z_to_bv 64 (hd 0 s)) a6 a7
             s2 s3 s4 (Z_to_bv 64 n0) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x14fac) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a6 a7 s2 s3 s4 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m P B n0 ov0 s bs
    NE CR HS HE HU LB Hn0 DJ MI.
  lazymatch goal with |- evt _ ?Q _ => set (QQ := Q) end.
  pose proof (bytes_at_bound rsegs m P _ HS) as SB.
  unfold bn_bytes in SB. rewrite length_map, length_app in SB. cbn [length] in SB.
  pose proof (u8arr_bound rsegs m B bs HU) as BB. rewrite LB in BB.
  assert (LOOP : forall (k i : nat) (m1 : word -> option byte) (n : Z) (ov x16 : word),
    k = (length s - i)%nat -> (i < length s)%nat ->
    n = sb_n 47 n0 (Z.of_nat i) -> ov = sb_o 47 n0 (Z.of_nat i) ov0 ->
    u8arr rsegs m1 B (sb_b bs 47 n0 (firstn i s)) -> bytes_at rsegs m1 P (bn_bytes (s ++ [0])) ->
    munch [(B, B + 48)] m m1 -> wmono rsegs m m1 -> mem_inv rsegs m1 ->
    evt rsegs QQ (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 B) ov (Z_to_bv 64 48)
                       (Z_to_bv 64 (P + Z.of_nat i + 1)) (Z_to_bv 64 (P + Z.of_nat (length s) + 1))
                       (Z_to_bv 64 (nth i s 0)) x16 a7 s2 s3 s4 (Z_to_bv 64 n) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (Z_to_bv 64 0x14fac) fc None m1 (seg_rom rsegs))).
  { induction k as [|k IH]; intros i m1 n ov x16 Hk Hi Hn Hov HU1 HS1 MU1 WM1 MI1; [lia|].
    assert (Rn : n = Z.min (n0 + Z.of_nat i) 47) by (rewrite Hn; reflexivity).
    assert (Rc : 0 < nth i s 0 < 256) by (rewrite Forall_forall in CR; apply CR; apply nth_In; exact Hi).
    assert (TAIL : forall (m2 : word -> option byte) (n' : Z) (ov' x16' : word),
      n' = sb_n 47 n0 (Z.of_nat (S i)) -> ov' = sb_o 47 n0 (Z.of_nat (S i)) ov0 ->
      u8arr rsegs m2 B (sb_b bs 47 n0 (firstn (S i) s)) -> bytes_at rsegs m2 P (bn_bytes (s ++ [0])) ->
      munch [(B, B + 48)] m m2 -> wmono rsegs m m2 -> mem_inv rsegs m2 ->
      evt rsegs QQ (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 B) ov' (Z_to_bv 64 48)
                         (Z_to_bv 64 (P + Z.of_nat i + 1)) (Z_to_bv 64 (P + Z.of_nat (length s) + 1))
                         (Z_to_bv 64 (nth i s 0)) x16' a7 s2 s3 s4 (Z_to_bv 64 n') s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                    F (Z_to_bv 64 0x14fc8) fc None m2 (seg_rom rsegs))).
    { pl_tail P s i CR IH. }
    zl_body_geu constr:(47) constr:(48) m m1 B P s i n n0 TAIL HU1 HS1 MU1 WM1 MI1 Hov. }
  zl_init constr:(47) P s n0 LOOP HU.
Qed.

Definition tk_d (l : list Z) : Z := if existsb (fun c => c =? 45) l then 1 else 0.
Definition bn_low (c : Z) : Z := if (65 <=? c) && (c <=? 90) then c + 32 else c.

Lemma bn_tk_app : forall a b seen,
  bn_tk seen (a ++ b) = bn_tk seen a ++ bn_tk (seen || existsb (fun c => c =? 45) a) b.
Proof.
  induction a as [|c a IH]; intros b seen.
  - cbn [app bn_tk existsb]. rewrite orb_false_r. reflexivity.
  - cbn [app bn_tk existsb].
    destruct (c =? 45); destruct seen; cbn [andb negb orb]; rewrite IH; cbn [orb app]; reflexivity.
Qed.

Lemma bn_tk_len : forall l seen, (length (bn_tk seen l) <= length l)%nat.
Proof.
  induction l as [|c l IH]; intros seen; cbn [bn_tk length]; [lia|].
  destruct ((c =? 45) && negb seen); cbn [length]; [specialize (IH true) | specialize (IH seen)]; lia.
Qed.

Lemma bn_tk_snoc : forall l i, (i < length l)%nat ->
  bn_tk false (firstn (S i) l) =
  bn_tk false (firstn i l) ++
  (if (nth i l 0 =? 45) && negb (existsb (fun c => c =? 45) (firstn i l)) then [] else [bn_low (nth i l 0)]).
Proof.
  intros l i H. rewrite (bl_firstn_snoc l i 0) by exact H. rewrite bn_tk_app. cbn [orb].
  reflexivity.
Qed.

Lemma tk_d_snoc : forall l i, (i < length l)%nat ->
  tk_d (firstn (S i) l) = if existsb (fun c => c =? 45) (firstn i l) || (nth i l 0 =? 45) then 1 else 0.
Proof.
  intros l i H. unfold tk_d. rewrite (bl_firstn_snoc l i 0) by exact H. rewrite existsb_app. cbn [existsb].
  rewrite orb_false_r. reflexivity.
Qed.

Lemma tk_d_rng : forall l, 0 <= tk_d l <= 1.
Proof. intros l. unfold tk_d. destruct (existsb (fun c => c =? 45) l); lia. Qed.

Lemma bn_low_rng : forall c, 0 <= c < 256 -> 0 <= bn_low c < 256 /\ (c <> 45 -> bn_low c <> 45).
Proof.
  intros c Hc. unfold bn_low. destruct ((65 <=? c) && (c <=? 90)) eqn:E; [|lia].
  apply andb_true_iff in E. destruct E as [E1 E2]. apply Z.leb_le in E1. apply Z.leb_le in E2. lia.
Qed.

Lemma bl_rd0 : forall m P l j, bytes_at rsegs m P (bn_bytes l) -> (j < length l)%nat ->
  ov_read_bytes rsegs m (Z_to_bv 64 (P + Z.of_nat j)) 1 = Some [Z_to_bv 8 (nth j l 0)].
Proof.
  intros m P l j H Hj. change (Z_to_bv 64 (P + Z.of_nat j)) with (wa (P + Z.of_nat j)).
  rewrite (bytes_at_ov_read rsegs m P (bn_bytes l) j 1 H) by (unfold bn_bytes; rewrite length_map; lia).
  unfold bn_bytes. rewrite skipn_map, firstn_map. rewrite (bl_firstn1 l j 0 Hj). reflexivity.
Qed.

Lemma bl_lower : forall c, 0 <= c < 256 ->
  Z_to_bv 64 (Z.lor (bv_unsigned (Z_to_bv 64 c))
                    (bv_unsigned (Z_to_bv 64 (Z.shiftl (bv_unsigned (v_sltiu (Z_to_bv 64 (c + -65)) 26)) 5)))) =
  Z_to_bv 64 (bn_low c).
Proof.
  intros c Hc.
  assert (A : forallb (fun c => bv_unsigned (Z_to_bv 64 (Z.lor (bv_unsigned (Z_to_bv 64 c))
                    (bv_unsigned (Z_to_bv 64 (Z.shiftl (bv_unsigned (v_sltiu (Z_to_bv 64 (c + -65)) 26)) 5)))))
                                =? bn_low c) (map Z.of_nat (seq 0 256)) = true) by (vm_compute; reflexivity).
  rewrite forallb_forall in A.
  specialize (A c ltac:(apply in_map_iff; exists (Z.to_nat c); split; [lia | apply in_seq; lia])).
  apply Z.eqb_eq in A. apply bv_eq. rewrite A.
  pose proof (bn_low_rng c Hc) as R. rewrite unsigned_lit by lia. reflexivity.
Qed.

Lemma box_name_token_loop : forall (ra sp gp tp t0 t1 t2 s0 s1 a7 s2 s3 s4 s5 s6 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (N T : Z) (ov0 : word) (l : list Z)
    (bs : list byte),
  (1 <= length l <= 23)%nat -> Forall (fun c => 0 <= c < 256) l -> bytes_at rsegs m N (bn_bytes l) ->
  N + Z.of_nat (length l) < 2^64 -> u8arr rsegs m T bs -> length bs = 24%nat ->
  (N + Z.of_nat (length l) <= T \/ T + 24 <= N) -> mem_inv rsegs m ->
  evt rsegs
    (fun ms' => exists (x5 x6 x17 : word) (m' : word -> option byte),
       ms' = MS (mkR ra sp gp tp x5 x6 t2 s0 s1 (Z_to_bv 64 (tk_d l)) ov0 (Z_to_bv 64 (N + Z.of_nat (length l)))
                     (Z_to_bv 64 45) (Z_to_bv 64 23) (Z_to_bv 64 (N + Z.of_nat (length l))) (Z_to_bv 64 T) x17
                     s2 s3 s4 s5 s6 (Z_to_bv 64 (Z.of_nat (length (bn_tk false l)))) s8 s9 s10 s11 t3 t4 t5 t6)
                F (Z_to_bv 64 0x14e68) fc None m' (seg_rom rsegs) /\
       u8arr rsegs m' T (upd_bytes bs 0 (bn_bytes (bn_tk false l))) /\ munch [(T, T + 24)] m m' /\
       wmono rsegs m m' /\ mem_inv rsegs m')
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) ov0 (Z_to_bv 64 N) (Z_to_bv 64 45) (Z_to_bv 64 23)
             (Z_to_bv 64 (N + Z.of_nat (length l))) (Z_to_bv 64 T) a7 s2 s3 s4 s5 s6 (Z_to_bv 64 0)
             s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x14e20) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a7 s2 s3 s4 s5 s6 s8 s9 s10 s11 t3 t4 t5 t6 F fc m N T ov0 l bs
    LL CR HS HE HU LB DJ MI.
  lazymatch goal with |- evt _ ?Q _ => set (QQ := Q) end.
  pose proof (bytes_at_bound rsegs m N _ HS) as SB.
  unfold bn_bytes in SB. rewrite length_map in SB.
  pose proof (u8arr_bound rsegs m T bs HU) as BB. rewrite LB in BB.
  assert (LOOP : forall (k i : nat) (m1 : word -> option byte) (x5 x6 x17 : word),
    k = (length l - i)%nat -> (i < length l)%nat ->
    u8arr rsegs m1 T (upd_bytes bs 0 (bn_bytes (bn_tk false (firstn i l)))) -> bytes_at rsegs m1 N (bn_bytes l) ->
    munch [(T, T + 24)] m m1 -> wmono rsegs m m1 -> mem_inv rsegs m1 ->
    evt rsegs QQ (MS (mkR ra sp gp tp x5 x6 t2 s0 s1 (Z_to_bv 64 (tk_d (firstn i l))) ov0
                       (Z_to_bv 64 (N + Z.of_nat i)) (Z_to_bv 64 45) (Z_to_bv 64 23)
                       (Z_to_bv 64 (N + Z.of_nat (length l))) (Z_to_bv 64 T) x17 s2 s3 s4 s5 s6
                       (Z_to_bv 64 (Z.of_nat (length (bn_tk false (firstn i l))))) s8 s9 s10 s11 t3 t4 t5 t6)
                  F (Z_to_bv 64 0x14e20) fc None m1 (seg_rom rsegs))).
  { induction k as [|k IH]; intros i m1 x5 x6 x17 Hk Hi HU1 HS1 MU1 WM1 MI1; [lia|].
    assert (Rc : 0 <= nth i l 0 < 256) by (rewrite Forall_forall in CR; apply CR; apply nth_In; exact Hi).
    pose proof (bn_tk_len (firstn i l) false) as TL. rewrite length_firstn in TL.
    pose proof (tk_d_rng (firstn i l)) as DR.
    assert (TAIL : forall (m2 : word -> option byte) (d tn : Z) (x5' x6' x17' : word),
      d = tk_d (firstn (S i) l) -> tn = Z.of_nat (length (bn_tk false (firstn (S i) l))) ->
      u8arr rsegs m2 T (upd_bytes bs 0 (bn_bytes (bn_tk false (firstn (S i) l)))) ->
      bytes_at rsegs m2 N (bn_bytes l) ->
      munch [(T, T + 24)] m m2 -> wmono rsegs m m2 -> mem_inv rsegs m2 ->
      evt rsegs QQ (MS (mkR ra sp gp tp x5' x6' t2 s0 s1 (Z_to_bv 64 d) ov0
                         (Z_to_bv 64 (N + Z.of_nat i)) (Z_to_bv 64 45) (Z_to_bv 64 23)
                         (Z_to_bv 64 (N + Z.of_nat (length l))) (Z_to_bv 64 T) x17' s2 s3 s4 s5 s6
                         (Z_to_bv 64 tn) s8 s9 s10 s11 t3 t4 t5 t6)
                    F (Z_to_bv 64 0x14e60) fc None m2 (seg_rom rsegs))).
    { intros m2 d tn x5' x6' x17' Hd Htn HU2 HS2 MU2 WM2 MI2.
      step. step.
      rewrite bl_eqb by lia.
      destruct (Nat.ltb_spec (S i) (length l)) as [Hl|Hl].
      - if_true.
        replace (N + Z.of_nat i + 1) with (N + Z.of_nat (S i)) by lia.
        subst d tn.
        eapply (IH (S i)); try eassumption; lia.
      - if_false.
        assert (E : firstn (S i) l = l) by (apply firstn_all2; lia).
        rewrite E in HU2, Hd, Htn. subst d tn.
        replace (Z_to_bv 64 (N + Z.of_nat i + 1)) with (Z_to_bv 64 (N + Z.of_nat (length l))) by (f_equal; lia).
        apply evt_done. hnf. do 3 eexists. exists m2. split; [reflexivity|].
        split; [exact HU2|]. split; [exact MU2|]. split; [exact WM2|exact MI2]. }
    assert (STORE :
      bn_tk false (firstn (S i) l) = bn_tk false (firstn i l) ++ [bn_low (nth i l 0)] ->
      tk_d (firstn (S i) l) = tk_d (firstn i l) ->
      evt rsegs QQ (MS (mkR ra sp gp tp x5 x6 t2 s0 s1 (Z_to_bv 64 (tk_d (firstn i l))) ov0
                         (Z_to_bv 64 (N + Z.of_nat i)) (Z_to_bv 64 45) (Z_to_bv 64 23)
                         (Z_to_bv 64 (N + Z.of_nat (length l))) (Z_to_bv 64 T) (Z_to_bv 64 (nth i l 0))
                         s2 s3 s4 s5 s6 (Z_to_bv 64 (Z.of_nat (length (bn_tk false (firstn i l)))))
                         s8 s9 s10 s11 t3 t4 t5 t6)
                    F (Z_to_bv 64 0x14e34) fc None m1 (seg_rom rsegs))).
    { intros ETK ETD.
      step. step.
      rewrite bl_ltu by lia.
      if_false.
      step. step. step. step.
      rewrite (bl_lower (nth i l 0)) by lia.
      pose proof (bn_low_rng _ Rc) as LR.
      assert (UL : length (upd_bytes bs 0 (bn_bytes (bn_tk false (firstn i l)))) = 24%nat)
        by (rewrite upd_bytes_length; [exact LB | unfold bn_bytes; rewrite length_map; lia]).
      step.
      pose proof (u8arr_store_ok rsegs m1 T _ (Z.of_nat (length (bn_tk false (firstn i l)))) _ HU1
                    ltac:(rewrite UL; lia) eq_refl) as HST.
      step.
      rewrite (bl_le1 (bn_low (nth i l 0))) by lia.
      destruct (bl_store m m1 T 24 _ N (bn_bytes l) (Z.of_nat (length (bn_tk false (firstn i l))))
                  (Z_to_bv 8 (bn_low (nth i l 0))) HU1 ltac:(rewrite UL; reflexivity) HS1 MU1 WM1 MI1
                  ltac:(lia) ltac:(unfold bn_bytes; rewrite length_map; lia))
        as (HU2 & HS2 & MU2 & WM2 & MI2).
      remember (write_to_mem m1 (Z_to_bv 64 (T + Z.of_nat (length (bn_tk false (firstn i l)))))
                  [Z_to_bv 8 (bn_low (nth i l 0))]) as m2 eqn:Em2.
      clear Em2 HST.
      step. step.
      eapply TAIL; try eassumption.
      + rewrite ETD. reflexivity.
      + rewrite ETK, length_app. cbn [length]. lia.
      + rewrite ETK. unfold bn_bytes in *. rewrite map_app. cbn [map].
        rewrite <- bl_upd_bytes_snoc by (rewrite length_map; lia).
        replace (0 + length (map (Z_to_bv 8) (bn_tk false (firstn i l))))%nat
          with (Z.to_nat (Z.of_nat (length (bn_tk false (firstn i l))))) by (rewrite length_map; lia).
        exact HU2. }
    pose proof (bl_rd0 m1 N l i HS1 Hi) as RD.
    step.
    clear RD. rewrite bl_zxb by lia.
    step.
    rewrite bl_eqb by lia.
    destruct (Z.eqb_spec (nth i l 0) 45) as [E45|E45]; cbn [negb].
    - step.
      rewrite bl_eqb by lia.
      destruct (existsb (fun c => c =? 45) (firstn i l)) eqn:EX.
      + replace (tk_d (firstn i l)) with 1 by (unfold tk_d; rewrite EX; reflexivity).
        cbn [Z.eqb negb].
        replace (Z_to_bv 64 1) with (Z_to_bv 64 (tk_d (firstn i l))) by (unfold tk_d; rewrite EX; reflexivity).
        apply STORE.
        * rewrite bn_tk_snoc by exact Hi. rewrite EX, E45. reflexivity.
        * rewrite tk_d_snoc by exact Hi. unfold tk_d. rewrite EX. reflexivity.
      + replace (tk_d (firstn i l)) with 0 by (unfold tk_d; rewrite EX; reflexivity).
        cbn [Z.eqb negb].
        step. step.
        eapply TAIL; try eassumption.
        * rewrite tk_d_snoc by exact Hi. rewrite EX, E45. reflexivity.
        * rewrite bn_tk_snoc by exact Hi. rewrite EX, E45, Z.eqb_refl. cbn [andb negb]. rewrite app_nil_r. reflexivity.
        * rewrite bn_tk_snoc by exact Hi. rewrite EX, E45, Z.eqb_refl. cbn [andb negb]. rewrite app_nil_r. exact HU1.
    - apply STORE.
      + rewrite bn_tk_snoc by exact Hi. replace (nth i l 0 =? 45) with false by (symmetry; apply Z.eqb_neq; exact E45).
        reflexivity.
      + rewrite tk_d_snoc by exact Hi. replace (nth i l 0 =? 45) with false by (symmetry; apply Z.eqb_neq; exact E45).
        rewrite orb_false_r. reflexivity. }
  replace (Z_to_bv 64 N) with (Z_to_bv 64 (N + Z.of_nat 0)) by (f_equal; lia).
  eapply (LOOP (length l) 0%nat).
  - lia.
  - lia.
  - exact HU.
  - exact HS.
  - apply munch_refl.
  - apply wmono_refl.
  - exact MI.
Qed.
