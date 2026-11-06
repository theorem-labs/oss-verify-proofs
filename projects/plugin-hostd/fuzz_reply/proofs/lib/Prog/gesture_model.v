From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame Tac Bytes ZBridge.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib Require Import Img0.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Spec Require Import StrFun.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import RelayModel bcmp_c list_find_c.
Import ListNotations.
Open Scope Z_scope.

Definition gm_keep (P : Prop) : Prop := P.
Ltac hide H := let T := type of H in change (gm_keep T) in H.

Lemma gm_ub : forall b : byte, bv_unsigned (Z_to_bv 64 (bv_unsigned b)) = bv_unsigned b.
Proof.
  intros b. pose proof (bv_unsigned_in_range 8 b) as R. unfold bv_modulus in R. cbn in R.
  apply unsigned_lit. lia.
Qed.

Lemma gm_signed : forall z, -2^63 <= z < 2^63 -> bv_signed (Z_to_bv 64 z) = z.
Proof.
  intros z Hz. rewrite zb_signed, unsigned_lit_wrap.
  change (2^64) with 18446744073709551616. change (2^63) with 9223372036854775808 in *.
  destruct (Z.ltb_spec (z mod 18446744073709551616) 9223372036854775808); cbv iota;
    Z.div_mod_to_equations; lia.
Qed.

Lemma gm_byte : forall m LINE (ln : list byte) i, bytes_at rsegs m LINE ln -> (i < length ln)%nat ->
  ov_read_bytes rsegs m (Z_to_bv 64 (LINE + Z.of_nat i)) 1 = Some [nth i ln (Z_to_bv 8 0)].
Proof.
  intros m LINE ln i H Hi. change (Z_to_bv 64 (LINE + Z.of_nat i)) with (wa (LINE + Z.of_nat i)).
  rewrite (bytes_at_read rsegs m LINE ln (Z.of_nat i) 1 H ltac:(lia)) by (rewrite Nat2Z.id; lia).
  rewrite Nat2Z.id. clear H. revert ln Hi. induction i as [|i IH]; intros [|b ln] Hi; cbn in Hi |- *; try lia.
  - reflexivity.
  - apply IH. lia.
Qed.

Lemma gm_scan : forall (c : nat) (t p : Z) (ln : list byte)
    (ra sp gp tp t0 t1 t2 w0 s1 a3 a4 a5 a6 a7 w2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte),
  bytes_at rsegs m (bv_unsigned w0) ln -> Z.of_nat (length ln) = bv_unsigned w2 ->
  bv_unsigned w0 + bv_unsigned w2 < 2 ^ 63 ->
  0 <= p -> 0 <= t -> p + t + 1 + Z.of_nat c = bv_unsigned w2 ->
  bv_unsigned (nth (Z.to_nat p) ln (Z_to_bv 8 0)) = 32 ->
  (forall i, p < i < bv_unsigned w2 -> bv_unsigned (nth (Z.to_nat i) ln (Z_to_bv 8 0)) <> 32) ->
  evt rsegs
    (fun ms' => exists a3',
       ms' = MS (mkR ra sp gp tp t0 t1 t2 w0 s1 (Z_to_bv 64 (p + 1 - bv_unsigned w2)) (Z_to_bv 64 32)
                     (Z_to_bv 64 (bv_unsigned w0 + bv_unsigned w2)) a3' a4 a5 a6 a7 w2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                     t3 t4 t5 t6)
                F (Z_to_bv 64 0x1487c) fc None m (seg_rom rsegs))
    (MS (mkR ra sp gp tp t0 t1 t2 w0 s1 (Z_to_bv 64 (- t)) (Z_to_bv 64 32) (Z_to_bv 64 (bv_unsigned w0 + bv_unsigned w2))
             a3 a4 a5 a6 a7 w2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x14860) fc None m (seg_rom rsegs)).
Proof.
  induction c as [|c IH]; intros t p ln ra sp gp tp t0 t1 t2 w0 s1 a3 a4 a5 a6 a7 w2 s3 s4 s5 s6 s7 s8 s9 s10 s11
    t3 t4 t5 t6 F fc m HB HL HL1 Hp Ht Hc HSP HNS;
    pose proof (zr_word w0) as R0; pose proof (zr_word w2) as R2; unfold inr64 in R0, R2.
  - pose proof (gm_byte m (bv_unsigned w0) ln (Z.to_nat p) HB ltac:(lia)) as RD.
    replace (bv_unsigned w0 + Z.of_nat (Z.to_nat p)) with (bv_unsigned w0 + bv_unsigned w2 + - t + -1) in RD by lia.
    step. step. step. if_cases Q.
    + apply evt_done. eexists. replace (p + 1 - bv_unsigned w2) with (- t) by lia. reflexivity.
    + exfalso. zify_cond Q. rewrite gm_ub in Q. exact (Q HSP).
  - pose proof (gm_byte m (bv_unsigned w0) ln (Z.to_nat (bv_unsigned w2 - t - 1)) HB ltac:(lia)) as RD.
    replace (bv_unsigned w0 + Z.of_nat (Z.to_nat (bv_unsigned w2 - t - 1)))
      with (bv_unsigned w0 + bv_unsigned w2 + - t + -1) in RD by lia.
    pose proof (HNS (bv_unsigned w2 - t - 1) ltac:(lia)) as NS.
    step. step. step. if_cases Q.
    + exfalso. zify_cond Q. rewrite gm_ub in Q. exact (NS Q).
    + step. step. step. if_cases Q2.
      * replace (- t + -1) with (- (t + 1)) by lia.
        apply (IH (t + 1) p ln); try assumption; lia.
      * exfalso. zify_cond Q2. Z.div_mod_to_equations. lia.
Qed.

Lemma gm_last_space : forall (ln : list byte) (d k : nat), (k + d < length ln)%nat ->
  bv_unsigned (nth k ln (Z_to_bv 8 0)) = 32 ->
  exists p, (k <= p <= k + d)%nat /\ bv_unsigned (nth p ln (Z_to_bv 8 0)) = 32 /\
    forall i, (p < i <= k + d)%nat -> bv_unsigned (nth i ln (Z_to_bv 8 0)) <> 32.
Proof.
  intros ln d. induction d as [|d IH]; intros k Hk H.
  - exists k. split; [lia|]. split; [exact H|]. intros i Hi. lia.
  - destruct (Z.eq_dec (bv_unsigned (nth (k + S d) ln (Z_to_bv 8 0))) 32) as [E|E].
    + exists (k + S d)%nat. split; [lia|]. split; [exact E|]. intros i Hi. lia.
    + destruct (IH k ltac:(lia) H) as (p & Hp & Hs & Hn). exists p. split; [lia|]. split; [exact Hs|].
      intros i Hi. destruct (Nat.eq_dec i (k + S d)) as [->|Ne]; [exact E|]. apply Hn. lia.
Qed.

Lemma gm_lr_tr : forall m m' lo hi V (recs : list (word * list byte)), munch [(lo, hi)] m m' ->
  (forall j r, nth_error recs j = Some r -> list_rec m V j r) ->
  (forall j r, nth_error recs j = Some r ->
     V + 16 * Z.of_nat j + 16 <= lo /\ bv_unsigned (fst r) + Z.of_nat (length (snd r)) + 1 <= lo) ->
  forall j r, nth_error recs j = Some r -> list_rec m' V j r.
Proof.
  intros m m' lo hi V recs MU LR D j r H. destruct (LR j r H) as [B1 B2]. destruct (D j r H) as [D1 D2].
  split.
  - eapply bytes_at_transport; [exact B1 | exact MU |]. cbn [disjoint_from].
    rewrite length_app, !length_le8. split; [lia | exact I].
  - eapply bytes_at_transport; [exact B2 | exact MU |]. cbn [disjoint_from].
    rewrite length_app. cbn [length]. split; [lia | exact I].
Qed.

Lemma gm_neg : forall z, Z_to_bv 64 (0 - bv_unsigned (Z_to_bv 64 z)) = Z_to_bv 64 (- z).
Proof.
  intros z. apply bv_eq. rewrite !unsigned_lit_wrap. Z.div_mod_to_equations. lia.
Qed.

Lemma gm_skip : forall m P (l : list byte) k, bytes_at rsegs m P l -> (k <= length l)%nat ->
  bytes_at rsegs m (P + Z.of_nat k) (skipn k l).
Proof.
  intros m P l k H Hk. rewrite <- (firstn_skipn k l) in H. apply bytes_at_app in H. destruct H as [_ H].
  rewrite length_firstn, Nat.min_l in H by exact Hk. exact H.
Qed.

Lemma gm_first : forall m P (l : list byte) k, bytes_at rsegs m P l -> bytes_at rsegs m P (firstn k l).
Proof.
  intros m P l k H. rewrite <- (firstn_skipn k l) in H. apply bytes_at_app in H. exact (proj1 H).
Qed.

Lemma gm_lsf_none : forall l i, (forall k, (k < length l)%nat -> nth k l 0 <> SPACE) -> last_space_from i l = None.
Proof.
  induction l as [|b l IH]; intros i H; [reflexivity|].
  cbn [last_space_from]. rewrite IH by (intros k Hk; apply (H (S k)); cbn; lia).
  destruct (Z.eqb_spec b SPACE) as [E|E]; [exfalso; apply (H 0%nat); [cbn; lia | exact E] | reflexivity].
Qed.

Lemma gm_lsf : forall l i j, (j < length l)%nat -> nth j l 0 = SPACE ->
  (forall k, (j < k < length l)%nat -> nth k l 0 <> SPACE) -> last_space_from i l = Some (i + j)%nat.
Proof.
  induction l as [|b l IH]; intros i j Hj HS HN; [cbn in Hj; lia|].
  cbn [last_space_from]. destruct j as [|j].
  - rewrite gm_lsf_none by (intros k Hk; apply (HN (S k)); cbn; lia).
    cbn in HS. rewrite HS. cbn. f_equal. lia.
  - rewrite (IH (S i) j) by (cbn in *; first [lia | exact HS | intros k Hk; apply (HN (S k)); lia]).
    f_equal. lia.
Qed.

Lemma gm_eqb_true : forall a b, list_eqb a b = true <-> a = b.
Proof. intros a b. unfold list_eqb. destruct (list_eq_dec Z.eq_dec a b); split; intros H; congruence. Qed.

Lemma gm_short : forall l, (length l <= 13)%nat -> gesture l = None.
Proof. intros l H. unfold gesture. rewrite (proj2 (Nat.ltb_ge 13 (length l)) H), !andb_false_r. reflexivity. Qed.

Lemma gm_nok : forall l, firstn 13 l <> K_GESTURE -> gesture l = None.
Proof.
  intros l H. unfold gesture. destruct (list_eqb (firstn 13 l) K_GESTURE) eqn:E; [|reflexivity].
  exfalso. apply H. apply gm_eqb_true. exact E.
Qed.

Lemma gm_nosp : forall l, nth 13 l 0 <> SPACE -> gesture l = None.
Proof.
  intros l H. unfold gesture. rewrite (proj2 (Z.eqb_neq _ _) H), andb_false_r. cbn [andb]. reflexivity.
Qed.

Lemma gm_at : forall l j, (13 < length l)%nat -> firstn 13 l = K_GESTURE -> nth 13 l 0 = SPACE ->
  last_space_from 0 l = Some j ->
  gesture l = if Nat.ltb 13 j then
                if list_eqb (skipn (S j) l) W_BEGIN then Some (GBegin, firstn j l)
                else if list_eqb (skipn (S j) l) W_END then Some (GEnd, firstn j l) else None
              else None.
Proof.
  intros l j H1 H2 H3 H4. unfold gesture.
  rewrite (proj2 (gm_eqb_true _ _) H2), (proj2 (Z.eqb_eq _ _) H3), (proj2 (Nat.ltb_lt _ _) H1), H4.
  reflexivity.
Qed.

Lemma gm_eqb_len : forall a b, length a <> length b -> list_eqb a b = false.
Proof.
  intros a b H. destruct (list_eqb a b) eqn:E; [|reflexivity]. apply gm_eqb_true in E. subst. contradiction.
Qed.

Lemma gm_upd_none : forall G l, gesture l = None -> upd G l = G.
Proof. intros G l H. unfold upd. rewrite H. reflexivity. Qed.

Lemma gm_upd_begin_in : forall G l x, gesture l = Some (GBegin, x) -> In x G -> upd G l = G.
Proof.
  intros G l x H I. unfold upd. rewrite H.
  replace (existsb (list_eqb x) G) with true; [reflexivity|].
  symmetry. apply existsb_exists. exists x. split; [exact I | apply gm_eqb_true; reflexivity].
Qed.

Lemma gm_filter_out : forall x G, ~ In x G -> List.filter (fun y => negb (list_eqb x y)) G = G.
Proof.
  intros x G. induction G as [|y G IH]; intros N; [reflexivity|].
  cbn [List.filter]. destruct (list_eqb x y) eqn:E.
  - exfalso. apply gm_eqb_true in E. subst. apply N. left. reflexivity.
  - cbn [negb]. f_equal. apply IH. intros I. apply N. right. exact I.
Qed.

Lemma gm_upd_end_out : forall G l x, gesture l = Some (GEnd, x) -> ~ In x G -> upd G l = G.
Proof. intros G l x H N. unfold upd. rewrite H. exact (gm_filter_out x G N). Qed.

Lemma gm_upd_begin_new : forall G l x, gesture l = Some (GBegin, x) -> ~ In x G -> upd G l = G ++ [x].
Proof.
  intros G l x H N. unfold upd. rewrite H.
  replace (existsb (list_eqb x) G) with false; [reflexivity|].
  symmetry. apply not_true_iff_false. intros E. apply existsb_exists in E as (y & Iy & Ey).
  apply gm_eqb_true in Ey. subst. exact (N Iy).
Qed.

Lemma gm_filter_nth : forall (G : list (list Z)) i, List.NoDup G -> (i < length G)%nat ->
  List.filter (fun y => negb (list_eqb (nth i G []) y)) G = firstn i G ++ skipn (S i) G.
Proof.
  induction G as [|y G IH]; intros i ND Hi; [cbn in Hi; lia|].
  inversion ND as [|y' G' Ny NDG]; subst.
  destruct i as [|i].
  - cbn [nth List.filter firstn skipn app]. rewrite (proj2 (gm_eqb_true y y) eq_refl). cbn [negb].
    apply gm_filter_out. exact Ny.
  - cbn [nth List.filter firstn skipn app].
    assert (Ny' : nth i G [] <> y).
    { intros E. apply Ny. rewrite <- E. apply nth_In. cbn in Hi. lia. }
    destruct (list_eqb (nth i G []) y) eqn:E; [apply gm_eqb_true in E; exfalso; exact (Ny' E)|].
    cbn [negb]. f_equal. apply IH; [exact NDG | cbn in Hi; lia].
Qed.

Lemma gm_upd_end_at : forall G l i, gesture l = Some (GEnd, nth i G []) -> List.NoDup G -> (i < length G)%nat ->
  upd G l = firstn i G ++ skipn (S i) G.
Proof. intros G l i H ND Hi. unfold upd. rewrite H. exact (gm_filter_nth G i ND Hi). Qed.

Definition gm_txt (b : list byte) : list Z := map (fun x => bv_unsigned x) b.

Lemma gm_txt_inj : forall a b, gm_txt a = gm_txt b -> a = b.
Proof.
  induction a as [|x a IH]; intros [|y b] H; cbn in H; try discriminate; [reflexivity|].
  injection H as H1 H2. f_equal; [apply bv_eq; exact H1 | exact (IH b H2)].
Qed.

Definition KLIT : list byte := map (Z_to_bv 8) K_GESTURE.
Definition BLIT : list byte := map (Z_to_bv 8) W_BEGIN.
Definition ELIT : list byte := map (Z_to_bv 8) W_END.

Lemma gm_memcmp : forall n (L R : list byte) v, length L = n -> length R = n -> memcmp_model L R n = Some v ->
  -255 <= v <= 255 /\ (v = 0 <-> L = R).
Proof.
  induction n as [|n IH]; intros L R v HL HR HM.
  - destruct L, R; cbn in *; try lia. injection HM as <-. split; [lia|]. tauto.
  - destruct L as [|a L], R as [|b R]; cbn in HL, HR; try lia.
    cbn in HM. destruct (Z.eqb_spec (bv_unsigned a) (bv_unsigned b)) as [E|NE].
    + destruct (IH L R v ltac:(lia) ltac:(lia) HM) as [RV IV]. split; [exact RV|].
      rewrite IV. split; intro H.
      * f_equal; [apply bv_eq; exact E | exact H].
      * injection H as _ H. exact H.
    + injection HM as <-. pose proof (bv_unsigned_in_range 8 a) as Ra. pose proof (bv_unsigned_in_range 8 b) as Rb.
      unfold bv_modulus in Ra, Rb. change (Z.of_N 8) with 8 in Ra, Rb.
      split; [lia|]. split; intro H; [lia|]. injection H as H _. subst. contradiction.
Qed.

Lemma gm_klit_txt : gm_txt KLIT = K_GESTURE.
Proof. vm_compute. reflexivity. Qed.
Lemma gm_blit_txt : gm_txt BLIT = W_BEGIN.
Proof. vm_compute. reflexivity. Qed.
Lemma gm_elit_txt : gm_txt ELIT = W_END.
Proof. vm_compute. reflexivity. Qed.

Lemma gm_z0 : forall v, -255 <= v <= 255 -> bv_unsigned (Z_to_bv 64 v) = 0 -> v = 0.
Proof. intros v Hv H. rewrite unsigned_lit_wrap in H. Z.div_mod_to_equations. lia. Qed.



Lemma gm_img : forall m A bs, mem_inv rsegs m -> ro_bytes_b rsegs A bs = true -> 0 <= A -> A + Z.of_nat (length bs) <= 2 ^ 64 ->
  bytes_at rsegs m A bs.
Proof.
  intros m A bs MI H1 H2 H3. destruct (ro_cells_image rsegs m A bs MI H1 H2 H3) as [_ RO].
  cbn [cells_bytes cbytes] in RO. rewrite app_nil_r in RO. exact RO.
Qed.

Lemma gm_klit : forall m, mem_inv rsegs m -> bytes_at rsegs m 0x103e6 KLIT.
Proof. intros m MI. apply gm_img; [exact MI | vm_compute; reflexivity | lia | cbn; lia]. Qed.
Lemma gm_blit : forall m, mem_inv rsegs m -> bytes_at rsegs m 0x10358 BLIT.
Proof. intros m MI. apply gm_img; [exact MI | vm_compute; reflexivity | lia | cbn; lia]. Qed.
Lemma gm_elit : forall m, mem_inv rsegs m -> bytes_at rsegs m 0x103af ELIT.
Proof. intros m MI. apply gm_img; [exact MI | vm_compute; reflexivity | lia | cbn; lia]. Qed.

Lemma gm_txt_firstn : forall n l, gm_txt (firstn n l) = firstn n (gm_txt l).
Proof. intros n l. unfold gm_txt. symmetry. apply firstn_map. Qed.
Lemma gm_txt_skipn : forall n l, gm_txt (skipn n l) = skipn n (gm_txt l).
Proof. intros n l. unfold gm_txt. symmetry. apply skipn_map. Qed.
Lemma gm_txt_nth : forall n l, nth n (gm_txt l) 0 = bv_unsigned (nth n l (Z_to_bv 8 0)).
Proof.
  intros n l. unfold gm_txt. revert l. induction n as [|n IH]; intros [|b l]; cbn; try reflexivity. apply IH.
Qed.
Lemma gm_txt_length : forall l, length (gm_txt l) = length l.
Proof. intros l. unfold gm_txt. apply length_map. Qed.

Definition gm_G (recs : list (word * list byte)) : list (list Z) := map (fun r => gm_txt (snd r)) recs.

Definition gm_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (lo LA LINE : Z) (ln : list byte) (recs : list (word * list byte)) (m : word -> option byte)
    : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    munch [(bv_unsigned sp - 96, bv_unsigned sp)] m m' /\ wmono rsegs m m' /\ mem_inv rsegs m' /\
    stk rsegs m' lo (bv_unsigned sp) /\
    ((upd (gm_G recs) (gm_txt ln) = gm_G recs /\
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (ret_pc ra) fc None m' (seg_rom rsegs)) \/
     (exists j, (j < length ln)%nat /\ gesture (gm_txt ln) = Some (GBegin, gm_txt (firstn j ln)) /\
        ~ In (gm_txt (firstn j ln)) (gm_G recs) /\
        ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 LA) (Z_to_bv 64 LINE) (Z_to_bv 64 (Z.of_nat j))
                      a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                 F (Z_to_bv 64 0x14284) fc None m' (seg_rom rsegs)) \/
     (exists i, (i < length recs)%nat /\ gesture (gm_txt ln) = Some (GEnd, nth i (gm_G recs) []) /\
        ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 LA) (Z_to_bv 64 (Z.of_nat i)) a2
                      a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                 F (Z_to_bv 64 0x14684) fc None m' (seg_rom rsegs))).

Ltac gm_ret FR ST sp :=
  do 6 step; release_frame FR ST (bv_unsigned sp);
  apply evt_done; unfold gm_post; do 16 eexists;
  split; [eassumption|]; split; [eassumption|]; split; [eassumption|]; split; [eassumption|];
  left; split; [|reflexivity].

Lemma gm_run : bcmp_contract -> list_find_contract ->
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo : Z) (ln : list byte) (v : word) (N : Z)
    (recs : list (word * list byte)),
  stk rsegs m lo (bv_unsigned sp) -> lo + 96 <= bv_unsigned sp -> bv_unsigned sp < 2 ^ 63 -> 0x100000 <= lo ->
  mem_inv rsegs m ->
  bytes_at rsegs m (bv_unsigned a1) ln -> bv_unsigned a2 = Z.of_nat (length ln) ->
  bv_unsigned a1 + Z.of_nat (length ln) <= lo -> 4096 <= bv_unsigned a1 ->
  bytes_at rsegs m (bv_unsigned a0 + 80) (le8 v) -> bytes_at rsegs m (bv_unsigned a0 + 88) (le4 (Z_to_bv 64 N)) ->
  (bv_unsigned a0 + 80) mod 8 = 0 -> bv_unsigned a0 + 96 <= lo ->
  0 <= N < 2 ^ 31 -> Z.of_nat (length recs) = N -> (0 < N -> 0 < bv_unsigned v /\ bv_unsigned v mod 8 = 0) ->
  (forall j r, nth_error recs j = Some r -> list_rec m (bv_unsigned v) j r) ->
  (0 < N -> bv_unsigned v + 16 * N <= lo) ->
  (forall j r, nth_error recs j = Some r -> bv_unsigned (fst r) + Z.of_nat (length (snd r)) + 1 <= lo) ->
  evt rsegs (gm_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo (bv_unsigned a0 + 80)
               (bv_unsigned a1) ln recs m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x1480c) fc None m (seg_rom rsegs)).
Proof.
  intros HBC HLF ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m lo ln v N recs ST LO S63 HI MI HB HL HBL HB4 LV LN LAL LAH HN HRL HVN LR HVL HRB.
  pose proof (zr_word sp) as Rsp. pose proof (zr_word a0) as Ra0. pose proof (zr_word a1) as Ra1.
  pose proof (zr_word a2) as Ra2. pose proof (zr_word v) as Rv. unfold inr64 in *.
  unfold bcmp_contract in HBC. unfold list_find_contract in HLF.
  pose proof (munch_refl [(bv_unsigned sp - 96, bv_unsigned sp)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  hide LR. hide HVN. hide HRB. hide HVL.
  carve_frame 32%nat ST.
  do 8 step.
  if_cases Q0.
  { zify_cond Q0.
    do 6 step. release_frame FR ST (bv_unsigned sp).
    apply evt_done. unfold gm_post. do 16 eexists.
    split; [eassumption|]. split; [eassumption|]. split; [eassumption|]. split; [eassumption|].
    left. split; [|reflexivity].
    apply gm_upd_none. apply gm_short. rewrite gm_txt_length. lia. }
  zify_cond Q0.
  assert (HB13 : bytes_at rsegs m1 (bv_unsigned a1) (firstn 13 ln)).
  { exact (proj1 (proj1 (bytes_at_app rsegs m1 (bv_unsigned a1) (firstn 13 ln) (skipn 13 ln))
                    ltac:(rewrite firstn_skipn; exact HB))). }
  destruct (memcmp_model_total (firstn 13 ln) KLIT 13 ltac:(rewrite length_firstn; lia) ltac:(cbn; lia))
    as [vK HK].
  destruct (gm_memcmp 13 (firstn 13 ln) KLIT vK ltac:(rewrite length_firstn; lia) eq_refl HK) as [HKr HKe].
  do 7 step.
  eapply evt_cut.
  { eapply HBC with (ls := firstn 13 ln) (rs := KLIT) (v := vK).
    - exact HB13.
    - rewrite unsigned_lit by lia. exact (gm_klit _ MI).
    - rewrite unsigned_lit by lia. exact HK.
    - exact MI. }
  post_call rsegs m1.
  step. if_cases Q1.
  { assert (NK : vK <> 0) by (intro E; subst vK; zify_cond Q1; apply Q1; reflexivity).
    gm_ret FR ST sp.
    apply gm_upd_none. apply gm_nok. intro E. apply NK. apply HKe.
    apply gm_txt_inj. rewrite gm_txt_firstn, gm_klit_txt. exact E. }
  zify_cond Q1. pose proof (gm_z0 vK HKr Q1) as VK0. subst vK.
  pose proof (proj1 HKe eq_refl) as K13.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    pose proof (gm_byte mm (bv_unsigned a1) ln 13 HB ltac:(lia)) as RD13 end.
  step. step. step. if_cases Q2.
  { zify_cond Q2. rewrite gm_ub in Q2.
    gm_ret FR ST sp.
    apply gm_upd_none. apply gm_nosp. rewrite gm_txt_nth. exact Q2. }
  zify_cond Q2. rewrite gm_ub in Q2.
  step. step.
  destruct (gm_last_space ln (length ln - 14) 13 ltac:(lia) Q2) as (pn & Hp1 & Hp2 & Hp3).
  eapply evt_cut.
  { apply (gm_scan (length ln - pn - 1) 0 (Z.of_nat pn) ln).
    - exact HB.
    - lia.
    - lia.
    - lia.
    - lia.
    - lia.
    - rewrite Nat2Z.id. exact Hp2.
    - intros i Hi. apply Hp3. lia. }
  intros ms' (a3' & ->).
  step. step. step.
  replace (bv_unsigned a2 + (Z.of_nat pn + 1 - bv_unsigned a2)) with (Z.of_nat pn + 1) by lia.
  assert (GM : gesture (gm_txt ln) =
            if Nat.ltb 13 pn then
              if list_eqb (skipn (S pn) (gm_txt ln)) W_BEGIN then Some (GBegin, firstn pn (gm_txt ln))
              else if list_eqb (skipn (S pn) (gm_txt ln)) W_END then Some (GEnd, firstn pn (gm_txt ln)) else None
            else None).
  { apply gm_at.
    - rewrite gm_txt_length. lia.
    - rewrite <- gm_txt_firstn, K13. exact gm_klit_txt.
    - rewrite gm_txt_nth. exact Q2.
    - apply (gm_lsf (gm_txt ln) 0 pn).
      + rewrite gm_txt_length. lia.
      + rewrite gm_txt_nth. exact Hp2.
      + intros k Hk. rewrite gm_txt_nth. rewrite gm_txt_length in Hk. apply Hp3. lia. }
  if_cases Q3.
  { zify_cond Q3. assert (P13 : pn = 13%nat) by (try (rewrite !unsigned_lit in Q3 by lia); lia).
    gm_ret FR ST sp. apply gm_upd_none. rewrite GM, P13. reflexivity. }
  zify_cond Q3. assert (P14 : (13 < pn)%nat) by (try (rewrite !unsigned_lit in Q3 by lia); lia).
  rewrite (proj2 (Nat.ltb_lt 13 pn) P14) in GM.
  step. step. step. step. step.
  rewrite gm_neg. replace (- (Z.of_nat pn + 1 - bv_unsigned a2)) with (bv_unsigned a2 - Z.of_nat pn - 1) by lia.
  assert (WL : length (skipn (S pn) ln) = (length ln - S pn)%nat) by apply length_skipn.
  assert (HBW : forall mm, bytes_at rsegs mm (bv_unsigned a1) ln ->
                 bytes_at rsegs mm (bv_unsigned (Z_to_bv 64 (Z.of_nat pn + 1 + bv_unsigned a1))) (skipn (S pn) ln)).
  { intros mm H. rewrite unsigned_lit by lia.
    replace (Z.of_nat pn + 1 + bv_unsigned a1) with (bv_unsigned a1 + Z.of_nat (S pn)) by lia.
    apply gm_skip; [exact H | lia]. }
  assert (LR0 := LR). unfold gm_keep in LR0. assert (HRB0 := HRB). unfold gm_keep in HRB0.
  assert (HVL0 := HVL). unfold gm_keep in HVL0. assert (HVN0 := HVN). unfold gm_keep in HVN0.
  assert (LRD : forall j r, nth_error recs j = Some r ->
            bv_unsigned v + 16 * Z.of_nat j + 16 <= bv_unsigned sp - 96 /\
            bv_unsigned (fst r) + Z.of_nat (length (snd r)) + 1 <= bv_unsigned sp - 96).
  { intros j r H. pose proof (nth_error_Some recs j) as NS. rewrite H in NS.
    assert (Hj : (j < length recs)%nat) by (apply NS; discriminate).
    split; [|pose proof (HRB0 j r H); lia]. pose proof (HVL0 ltac:(lia)); lia. }
  if_cases Q4.
  { zify_cond Q4. assert (W3 : (length ln - S pn = 3)%nat) by (try (rewrite !unsigned_lit in Q4 by lia); lia).
    destruct (memcmp_model_total (skipn (S pn) ln) ELIT 3 ltac:(lia) ltac:(cbn; lia)) as [vE HE].
    destruct (gm_memcmp 3 (skipn (S pn) ln) ELIT vE ltac:(lia) eq_refl HE) as [HEr HEe].
    do 4 step.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => rename mm into mE end.
    eapply evt_cut.
    { eapply HBC with (ls := skipn (S pn) ln) (rs := ELIT) (v := vE).
      - apply HBW. exact HB.
      - rewrite unsigned_lit by lia. apply gm_elit; assumption.
      - rewrite unsigned_lit by lia. exact HE.
      - assumption. }
    post_call rsegs mE.
    step. if_cases Q5.
    2: { zify_cond Q5. assert (NE : vE <> 0) by (intro E; subst vE; apply Q5; reflexivity).
         gm_ret FR ST sp. apply gm_upd_none. rewrite GM.
         rewrite (gm_eqb_len _ W_BEGIN) by (rewrite length_skipn, gm_txt_length; cbn; lia).
         destruct (list_eqb (skipn (S pn) (gm_txt ln)) W_END) eqn:EW; [|reflexivity].
         exfalso. apply NE. apply HEe. apply gm_txt_inj. rewrite gm_txt_skipn, gm_elit_txt.
         apply gm_eqb_true. exact EW. }
    zify_cond Q5. pose proof (gm_z0 vE HEr Q5) as VE0. subst vE. pose proof (proj1 HEe eq_refl) as E3.
    do 5 step.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => rename mm into mF end.
    assert (LRF : forall j r, nth_error recs j = Some r -> list_rec mF (bv_unsigned v) j r).
    { apply (gm_lr_tr m mF (bv_unsigned sp - 96) (bv_unsigned sp) _ recs MU LR0).
      intros j r H. destruct (LRD j r H); split; lia. }
    eapply evt_cut.
    { eapply HLF with (lo := lo) (N := N) (v := v) (recs := recs) (src := firstn pn ln).
      all: unfold LIST_FIND_FRAME;
        rewrite ?(unsigned_lit (bv_unsigned sp + -32)), ?(unsigned_lit (bv_unsigned a0 + 80)),
          ?(unsigned_lit (Z.of_nat pn)) by lia.
      all: first [ assumption | exact HVN0 | exact LRF | (apply gm_first; assumption)
                 | (replace (bv_unsigned a0 + 80 + 8) with (bv_unsigned a0 + 88) by lia; assumption)
                 | (rewrite length_firstn; lia) | lia
                 | (left; rewrite length_firstn; lia) | (left; lia)
                 | (intros HN0; pose proof (HVL0 HN0); left; lia)
                 | (intros j r H; pose proof (HRB0 j r H); left; lia) ]. }
    assert (HSPU : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -32)) = bv_unsigned sp - 32) by (apply unsigned_lit; lia).
    assert (HLFF : LIST_FIND_FRAME = 64) by reflexivity.
    post_call rsegs mF.
    match goal with H : stk rsegs _ lo (bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -32))) |- _ =>
      rewrite HSPU in H; replace (bv_unsigned sp - 32) with (bv_unsigned sp + -32) in H by lia; rename H into ST end.
    assert (GE : gesture (gm_txt ln) = Some (GEnd, firstn pn (gm_txt ln))).
    { rewrite GM. rewrite (gm_eqb_len _ W_BEGIN) by (rewrite length_skipn, gm_txt_length; cbn; lia).
      rewrite (proj2 (gm_eqb_true _ _)); [reflexivity|].
      rewrite <- gm_txt_skipn, E3. exact gm_elit_txt. }
    match goal with H : (exists j r, _) \/ _ |- _ => rename H into FR0 end.
    destruct FR0 as [(j & r & Hj & Hsr & Hmin & ->)|(Hnone & ->)].
    + assert (Hjl : (j < length recs)%nat) by (apply nth_error_Some; rewrite Hj; discriminate).
      step. if_cases Q6; [exfalso; zify_cond Q6; try (rewrite unsigned_lit in Q6 by lia); try (rewrite unsigned_lit_wrap in Q6); Z.div_mod_to_equations; lia|].
      do 8 step. release_frame FR ST (bv_unsigned sp).
      apply evt_done. unfold gm_post. do 16 eexists.
      split; [eassumption|]. split; [eassumption|]. split; [eassumption|]. split; [eassumption|].
      right. right. exists j. split; [exact Hjl|]. split; [|reflexivity].
      rewrite GE. f_equal. f_equal. unfold gm_G.
      replace (nth j (map (fun r0 => gm_txt (snd r0)) recs) []) with (gm_txt (snd r)).
      * rewrite Hsr. symmetry. apply gm_txt_firstn.
      * symmetry. apply nth_error_nth. rewrite nth_error_map, Hj. reflexivity.
    + step. if_cases Q6.
      2: { exfalso. zify_cond Q6. try (rewrite unsigned_lit_wrap in Q6). Z.div_mod_to_equations. lia. }
      gm_ret FR ST sp. apply (gm_upd_end_out _ _ _ GE).
      intros I. unfold gm_G in I. apply in_map_iff in I as (r' & Er & Ir).
      apply In_nth_error in Ir as (k & Hk). apply (Hnone k r' Hk).
      apply gm_txt_inj. rewrite Er. symmetry. apply gm_txt_firstn. }
  zify_cond Q4. assert (W3 : (length ln - S pn <> 3)%nat) by (try (rewrite !unsigned_lit in Q4 by lia); lia).
  step. step. if_cases Q7.
  { zify_cond Q7. assert (W5 : (length ln - S pn <> 5)%nat) by (try (rewrite !unsigned_lit in Q7 by lia); lia).
    gm_ret FR ST sp. apply gm_upd_none. rewrite GM.
    rewrite (gm_eqb_len _ W_BEGIN) by (rewrite length_skipn, gm_txt_length; cbn; lia).
    rewrite (gm_eqb_len _ W_END) by (rewrite length_skipn, gm_txt_length; cbn; lia). reflexivity. }
  zify_cond Q7. assert (W5 : (length ln - S pn = 5)%nat) by (try (rewrite !unsigned_lit in Q7 by lia); lia).
  destruct (memcmp_model_total (skipn (S pn) ln) BLIT 5 ltac:(lia) ltac:(cbn; lia)) as [vB HBg].
  destruct (gm_memcmp 5 (skipn (S pn) ln) BLIT vB ltac:(lia) eq_refl HBg) as [HBr HBe].
  do 4 step.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => rename mm into mE end.
  eapply evt_cut.
  { eapply HBC with (ls := skipn (S pn) ln) (rs := BLIT) (v := vB).
    - apply HBW. exact HB.
    - rewrite unsigned_lit by lia. apply gm_blit; assumption.
    - rewrite unsigned_lit by lia. exact HBg.
    - assumption. }
  post_call rsegs mE.
  step. if_cases Q8.
  { zify_cond Q8. assert (NE : vB <> 0) by (intro E; subst vB; apply Q8; reflexivity).
    gm_ret FR ST sp. apply gm_upd_none. rewrite GM.
    destruct (list_eqb (skipn (S pn) (gm_txt ln)) W_BEGIN) eqn:EW.
    - exfalso. apply NE. apply HBe. apply gm_txt_inj. rewrite gm_txt_skipn, gm_blit_txt.
      apply gm_eqb_true. exact EW.
    - rewrite (gm_eqb_len _ W_END) by (rewrite length_skipn, gm_txt_length; cbn; lia). reflexivity. }
  zify_cond Q8. pose proof (gm_z0 vB HBr Q8) as VB0. subst vB. pose proof (proj1 HBe eq_refl) as B5.
  do 5 step.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => rename mm into mF end.
  assert (LRF : forall j r, nth_error recs j = Some r -> list_rec mF (bv_unsigned v) j r).
  { apply (gm_lr_tr m mF (bv_unsigned sp - 96) (bv_unsigned sp) _ recs MU LR0).
    intros j r H. destruct (LRD j r H); split; lia. }
  eapply evt_cut.
  { eapply HLF with (lo := lo) (N := N) (v := v) (recs := recs) (src := firstn pn ln).
    all: unfold LIST_FIND_FRAME;
      rewrite ?(unsigned_lit (bv_unsigned sp + -32)), ?(unsigned_lit (bv_unsigned a0 + 80)),
        ?(unsigned_lit (Z.of_nat pn)) by lia.
    all: first [ assumption | exact HVN0 | exact LRF | (apply gm_first; assumption)
               | (replace (bv_unsigned a0 + 80 + 8) with (bv_unsigned a0 + 88) by lia; assumption)
               | (rewrite length_firstn; lia) | lia
               | (left; rewrite length_firstn; lia) | (left; lia)
               | (intros HN0; pose proof (HVL0 HN0); left; lia)
               | (intros j r H; pose proof (HRB0 j r H); left; lia) ]. }
  assert (HSPU : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -32)) = bv_unsigned sp - 32) by (apply unsigned_lit; lia).
  assert (HLFF : LIST_FIND_FRAME = 64) by reflexivity.
  post_call rsegs mF.
  match goal with H : stk rsegs _ lo (bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -32))) |- _ =>
    rewrite HSPU in H; replace (bv_unsigned sp - 32) with (bv_unsigned sp + -32) in H by lia; rename H into ST end.
  assert (GB : gesture (gm_txt ln) = Some (GBegin, firstn pn (gm_txt ln))).
  { rewrite GM. rewrite (proj2 (gm_eqb_true _ _)); [reflexivity|].
    rewrite <- gm_txt_skipn, B5. exact gm_blit_txt. }
  match goal with H : (exists j r, _) \/ _ |- _ => rename H into FR0 end.
  destruct FR0 as [(j & r & Hj & Hsr & Hmin & ->)|(Hnone & ->)].
  - step. if_cases Q9.
    2: { exfalso. zify_cond Q9. assert (Hjl : (j < length recs)%nat) by (apply nth_error_Some; rewrite Hj; discriminate).
         try (rewrite gm_signed in Q9 by lia). try (rewrite unsigned_lit in Q9 by lia).
         try (rewrite unsigned_lit_wrap in Q9). Z.div_mod_to_equations. lia. }
    gm_ret FR ST sp. apply (gm_upd_begin_in _ _ _ GB). unfold gm_G.
    replace (firstn pn (gm_txt ln)) with (gm_txt (snd r)) by (rewrite Hsr; apply gm_txt_firstn).
    apply (in_map (fun r0 => gm_txt (snd r0))). exact (nth_error_In _ _ Hj).
  - step. if_cases Q9; [exfalso; zify_cond Q9; try (rewrite gm_signed in Q9 by lia); try (rewrite unsigned_lit_wrap in Q9); Z.div_mod_to_equations; lia|].
    do 9 step. release_frame FR ST (bv_unsigned sp).
    apply evt_done. unfold gm_post. do 16 eexists.
    split; [eassumption|]. split; [eassumption|]. split; [eassumption|]. split; [eassumption|].
    right. left. exists pn. split; [lia|].
    split; [rewrite GB, gm_txt_firstn; reflexivity|].
    split.
    + intros I. unfold gm_G in I. apply in_map_iff in I as (r' & Er & Ir).
      apply In_nth_error in Ir as (k & Hk). apply (Hnone k r' Hk). apply gm_txt_inj. exact Er.
    + rewrite Z_to_bv_bv_unsigned. reflexivity.
  Unshelve. all: exact (Z_to_bv 64 0).
Qed.

From LinuxProcessSemantics.LinuxProcessSem Require Import StackLayout Fs Monad Specs.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK11 YK0o YK0s YK14 YK15 YM06 YP09.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YL0i YL01.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YI04.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Lib Require Regs6ss RegisterBridge.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib Require Import Contract ContractT.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import RelayFrame RelayRunT RelayRunF HarnessRep ListRep
  CheckRep ListTr HarnessTr TrModel list_push_c list_drop_c gesture_model_c
  KindB HarnessGlue HarnessFrame.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05.
Import ListNotations.
Local Open Scope Z_scope.

Lemma gm_G_wrecs : forall l, gm_G (wrecs l) = texts l.
Proof. intros l. unfold gm_G, wrecs, texts. rewrite map_map. reflexivity. Qed.

Ltac gm_saved GR :=
  let r := fresh "r" in let Hr := fresh "Hr" in let Hc := fresh "Hc" in
  intros r Hr; rewrite GR; unfold callee_saved in Hr;
  assert (Hc : r = 2 \/ r = 3 \/ r = 4 \/ r = 8 \/ r = 9 \/ r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/
               r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia;
  repeat (destruct Hc as [Hc|Hc]; [subst r; reflexivity|]); subst r; reflexivity.

Lemma gm_find_key_in : forall x ks i, find_key x ks = Some i -> In x ks.
Proof.
  intros x ks. induction ks as [|k ks IH]; intros i H; simpl in H; [discriminate|].
  destruct (list_eqb x k) eqn:E; [left; symmetry; apply gm_eqb_true; exact E|].
  destruct (find_key x ks) as [i'|] eqn:E2; [|discriminate]. right. exact (IH i' eq_refl).
Qed.

Lemma gm_find_key_nth : forall (G : list (list Z)) i, List.NoDup G -> (i < length G)%nat ->
  find_key (nth i G []) G = Some i.
Proof.
  induction G as [|y G IH]; intros i ND Hi; [cbn in Hi; lia|].
  inversion ND as [|y' G' Ny NDG]; subst.
  destruct i as [|i].
  - cbn [nth find_key]. rewrite (proj2 (gm_eqb_true y y) eq_refl). reflexivity.
  - cbn [nth find_key]. destruct (list_eqb (nth i G []) y) eqn:E.
    + exfalso. apply gm_eqb_true in E. apply Ny. rewrite <- E. apply nth_In. cbn in Hi. lia.
    + rewrite IH; [reflexivity | exact NDG | cbn in Hi; lia].
Qed.

Lemma gm_sh_keys : forall nm l, sh_keys (sh_of nm l) = texts l.
Proof. intros nm l. unfold sh_keys, sh_of, texts. cbn [sh_recs]. rewrite map_map. reflexivity. Qed.

Lemma gm_tr_none : forall s l j, upd (sh_keys s) l = sh_keys s ->
  gesture_model_tr s l = [] /\ gesture_model_sh j s l = s.
Proof.
  intros s l j Hu. unfold upd in Hu. unfold gesture_model_tr, gesture_model_sh.
  destruct (gesture l) as [[g x]|]; [|split; reflexivity]. destruct g.
  - destruct (existsb (list_eqb x) (sh_keys s)) eqn:E; [split; reflexivity|].
    exfalso. apply (f_equal (@length (list Z))) in Hu. rewrite length_app in Hu. cbn in Hu. lia.
  - destruct (find_key x (sh_keys s)) as [i|] eqn:E; [|split; reflexivity]. exfalso.
    apply gm_find_key_in in E. rewrite <- Hu in E. apply filter_In in E as [_ E].
    rewrite (proj2 (gm_eqb_true x x) eq_refl) in E. discriminate.
Qed.

Lemma gm_tr_begin : forall s l x, gesture l = Some (GBegin, x) -> existsb (list_eqb x) (sh_keys s) = false ->
  gesture_model_tr s l = list_push_tr s x /\ forall j, gesture_model_sh j s l = list_push_sh j s x.
Proof.
  intros s l x G E. unfold gesture_model_tr, gesture_model_sh. rewrite G. cbn beta iota. rewrite E.
  split; [reflexivity | intros j; reflexivity].
Qed.

Lemma gm_tr_end : forall s l i, gesture l = Some (GEnd, nth i (sh_keys s) []) -> List.NoDup (sh_keys s) ->
  (i < length (sh_keys s))%nat ->
  gesture_model_tr s l = list_drop_tr s i /\ forall j, gesture_model_sh j s l = list_drop_sh s i.
Proof.
  intros s l i G ND Hi. unfold gesture_model_tr, gesture_model_sh. rewrite G. cbn beta iota.
  rewrite (gm_find_key_nth _ i ND Hi). split; [reflexivity | intros j; reflexivity].
Qed.

Lemma gm_sptr_of_addr : forall L A a n, In (a, n) (blocks L A) -> ptr_addr L (sptr_of L A a) = a.
Proof.
  intros L A a n Hin. unfold blocks in Hin.
  apply in_map_iff in Hin as [[p k] [Hpk Hb]]. cbn [fst snd] in Hpk. injection Hpk as Hp _.
  unfold sptr_of.
  destruct (find (fun pb => ptr_addr L (fst pb) =? a) (user_blocks A)) as [[q m]|] eqn:Hf.
  - apply find_some in Hf as [_ Hqa]. cbn [fst] in Hqa |- *. apply Z.eqb_eq in Hqa. exact Hqa.
  - exfalso. apply (find_none _ _ Hf) in Hb. cbn [fst] in Hb. rewrite Hp, Z.eqb_refl in Hb. discriminate.
Qed.

Lemma gm_sptr_of_live : forall L A a n, In (a, n) (blocks L A) -> exists m, In (sptr_of L A a, m) (user_blocks A).
Proof.
  intros L A a n Hin. unfold blocks in Hin.
  apply in_map_iff in Hin as [[p k] [Hpk Hb]]. cbn [fst snd] in Hpk. injection Hpk as Hp _.
  unfold sptr_of.
  destruct (find (fun pb => ptr_addr L (fst pb) =? a) (user_blocks A)) as [[q m]|] eqn:Hf.
  - apply find_some in Hf as [Hq _]. exists m. exact Hq.
  - exfalso. apply (find_none _ _ Hf) in Hb. cbn [fst] in Hb. rewrite Hp, Z.eqb_refl in Hb. discriminate.
Qed.

Section GMB.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable Bm : malloc_syms.
Variable API : AllocAPI Bm.
Variable RF : ResFormT.
Hypothesis AX : AllocExtra Bm (aa_MR API).
Hypothesis BW : blocks_writable Bm API.

Lemma gm_sh_real : forall L A mem LA l lines qs, list_at Bm L A mem LA l lines -> sh_real L qs (sh_of (known_at L A) l) l.
Proof.
  intros L A mem LA l lines qs (_ & _ & AR & _ & _ & FA). unfold sh_real, sh_of, known_at, sh_keys.
  cbn [sh_cap sh_v sh_recs]. split; [reflexivity|]. split.
  - intros Hc. destruct AR as [(C0 & _)|(_ & Hin & _)]; [contradiction|]. simpl. symmetry.
    exact (gm_sptr_of_addr L A _ _ Hin).
  - split.
    + rewrite map_map. reflexivity.
    + rewrite map_map. apply map_ext_in. intros r Hr. rewrite Forall_forall in FA. destruct (FA r Hr) as (Hin & _).
      simpl. symmetry. exact (gm_sptr_of_addr L A _ _ Hin).
Qed.

Lemma gm_sh_live : forall L A mem LA l lines, list_at Bm L A mem LA l lines -> sh_live A [] (sh_of (known_at L A) l).
Proof.
  intros L A mem LA l lines (_ & _ & AR & _ & _ & FA). unfold sh_live, sh_of, known_at.
  cbn [sh_cap sh_v sh_recs]. split.
  - intros Hc. destruct AR as [(C0 & _)|(_ & Hin & _)]; [contradiction|]. simpl.
    exact (gm_sptr_of_live L A _ _ Hin).
  - intros r Hr. apply in_map_iff in Hr as (r0 & <- & Hr0). rewrite Forall_forall in FA.
    destruct (FA r0 Hr0) as (Hin & _). simpl. exact (gm_sptr_of_live L A _ _ Hin).
Qed.

Theorem gesture_model_holds : bcmp_contract -> list_find_contract -> list_push_contract Bm API RF ->
  list_drop_contract Bm API RF -> gesture_model_contract Bm API RF.
Proof.
  intros HBC HLF PUSH DROP. unfold gesture_model_contract.
  intros L A regs mem md bnd h j ln.
  intros SEG PRE INIT RO PLR Hj4 R10 SRC NDT HN22 HLN NZ HLEN HL6 BLK RES ROOM.
  set (HA := G_S + SRC_SIZE * Z.of_nat j) in *.
  set (LINE := bv_unsigned (PropExec.getr regs 11)) in *.
  set (LEN := bv_unsigned (PropExec.getr regs 12)) in *.
  set (H := hs_held h) in *.
  set (N := hl_n H) in *. set (CAP := hl_cap H) in *.
  pose proof (gm_sh_keys (known_at L A) H) as SK.
  pose proof (aa_laws API) as LAWS.
  pose proof (@YM05.alloc_ceiling_value rc) as ACV. pose proof (@YM05.alloc_ceiling_lt rc) as ACL.
  pose proof PRE as (HMR & HWF & HBD & HRA & HAL & HCEIL & H63 & HWS & HTP & HERR & HAUX).
  destruct (mr_model _ _ LAWS _ _ _ _ HMR) as (Hh & Hl & Hmat).
  assert (EK : GESTURE_MODEL_K = 8304) by reflexivity. rewrite EK in *.
  set (sp := reg_get regs 2) in *.
  assert (SPE : spZ regs = bv_unsigned sp) by reflexivity. rewrite SPE in *.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. change (bv_modulus 64) with (2 ^ 64) in RSP.
  assert (HAr : 200768 <= HA <= 201056) by (unfold HA, G_S, SRC_SIZE; lia).
  assert (PLR' : forall a, HA <= a < HA + 96 -> img_plain Bm a)
    by (intros a Ha; apply PLR; unfold HA, G_S, SRC_SIZE, SOURCES_MAX in *; lia).
  assert (A0 : bv_unsigned (reg_get regs 10) = HA).
  { transitivity (bv_unsigned (PropExec.getr regs 10)); [reflexivity|]. rewrite R10. apply unsigned_lit. lia. }
  assert (A1 : bv_unsigned (reg_get regs 11) = LINE) by reflexivity.
  assert (A2 : bv_unsigned (reg_get regs 12) = LEN) by reflexivity.
  rewrite SEG in RO, HLN, HWS, HERR |- *.
  pose proof SRC as SRC0. apply src_at_iff in SRC0. destruct SRC0 as (SB & LE & LH & NDB).
  change (hs_held h) with H in LH.
  destruct (hf_list_head Bm L A mem (HA + 80) H true LH) as (HV8 & HN4 & VR & VB).
  rewrite SEG in HV8, HN4.
  pose proof LH as (_ & NC & ARH & _).
  assert (N0 : 0 <= N) by (unfold N, hl_n; lia).
  destruct BLK as (q0 & m0 & Bq & Fq & Q1 & Q2 & Qn).
  pose proof Fq as (Fq1 & Fq2 & Fq3).
  assert (LEN1 : 1 <= LEN \/ LEN = 0) by lia.
  assert (QV : q0 <> hl_v H).
  { intros E. destruct ARH as [(C0 & V0)|(Hc & _)].
    - lia.
    - apply Qn. rewrite E. exact (proj2 (hf_list_v Bm L A mem _ H true LH Hc)). }
  assert (ST : stk rsegs mem (bv_unsigned sp - 8304) (bv_unsigned sp)).
  { split; [lia|]. split; [lia|]. intros a Ha. assert (W : writable_at rsegs mem a) by (apply HWS; lia).
    split; [exact W|]. destruct (writable_hi_present mem a ltac:(lia) W) as [bb E]. exists bb.
    unfold mrd, wa. rewrite E. reflexivity. }
  pose proof (stk_normalize mem _ _ ST ltac:(lia)) as ST0.
  pose proof (mem_inv_normalize rsegs mem) as MI0.
  assert (WX : wx_apart rsegs = true) by (vm_compute; reflexivity).
  assert (LR0 : forall jj r, nth_error (wrecs H) jj = Some r ->
            list_rec (normalize rsegs mem) (bv_unsigned (Z_to_bv 64 (hl_v H))) jj r /\
            bv_unsigned (fst r) + Z.of_nat (length (snd r)) + 1 <= alloc_ceiling /\
            0 < hl_cap H /\ hl_v H + 16 * hl_cap H <= alloc_ceiling).
  { intros jj r Hr. destruct (hf_lrec Bm L A mem _ H true LH jj r Hr) as (X1 & X2 & X3 & X4 & X5 & X6).
    rewrite SEG in X1, X2. rewrite (unsigned_lit (hl_v H)) by lia.
    split; [split; apply bytes_at_normalize; assumption|]. lia. }
  unfold GESTURE_MODEL.
  eapply (kseg regs (Z_to_bv 64 0x1480c) mem md); [exact WX | exact RO | exact Hh | exact Hl | | |].
  { unfold Regs6ss.mkR_of. fold sp.
    eapply (gm_run HBC HLF) with (lo := bv_unsigned sp - 8304) (v := Z_to_bv 64 (hl_v H)) (N := N) (recs := wrecs H)
      (ln := ln).
    all: rewrite ?A0, ?A1, ?A2.
    - exact ST0.
    - lia.
    - exact H63.
    - lia.
    - exact MI0.
    - exact (bytes_at_normalize rsegs mem LINE ln RO HLN).
    - symmetry. exact HLEN.
    - lia.
    - lia.
    - exact (bytes_at_normalize rsegs mem _ _ RO HV8).
    - replace (HA + 88) with (HA + 80 + 8) by lia. exact (bytes_at_normalize rsegs mem _ _ RO HN4).
    - unfold HA, G_S, SRC_SIZE. Z.div_mod_to_equations. lia.
    - lia.
    - lia.
    - unfold wrecs. rewrite length_map. reflexivity.
    - intros HN. rewrite (unsigned_lit (hl_v H)) by lia. destruct NC as [NC1 NC2].
      destruct (VB ltac:(lia)) as [VB1 VB2].
      pose proof (hf_blk_align Bm API L A mem md _ _ HMR (proj1 (hf_list_v Bm L A mem _ H true LH ltac:(lia)))).
      split; [lia|]. Z.div_mod_to_equations. lia.
    - intros jj r Hr. exact (proj1 (LR0 jj r Hr)).
    - intros HN. rewrite (unsigned_lit (hl_v H)) by lia. destruct NC as [NC1 NC2].
      destruct (VB ltac:(lia)) as [VB1 VB2]. lia.
    - intros jj r Hr. destruct (LR0 jj r Hr) as (_ & X & _). lia. }
  { intros s0 HQ. unfold gm_post in HQ.
    destruct HQ as (u0 & u1 & u2 & u3 & u4 & u5 & u6 & u7 & u8 & u9 & u10 & u11 & u12 & u13 & u14 & mm &
      _ & _ & _ & _ & [(_ & ->)|[(jj & _ & _ & _ & ->)|(ii & _ & _ & ->)]]); do 3 eexists; reflexivity. }
  intros R pc' m0' regs1 m1 HQ GR MREL ROS. unfold gm_post in HQ.
  destruct HQ as (u0 & u1 & u2 & u3 & u4 & u5 & u6 & u7 & u8 & u9 & u10 & u11 & u12 & u13 & u14 & mm &
    MU & WM & MI & STK & ARM).
  assert (EM : m0' = mm).
  { destruct ARM as [(_ & EQ)|[(jj & _ & _ & _ & EQ)|(ii & _ & _ & EQ)]]; inversion EQ; reflexivity. }
  subst m0'.
  destruct (rmid_norm Bm API 8304 (bv_unsigned sp) (fun _ => False) (fun _ => False) L A mem md mm m1
              [(bv_unsigned sp - 96, bv_unsigned sp)] SEG RO MREL ROS MU WM HMR HWF HBD ltac:(lia))
    as (RM0 & MU0 & WM0).
  { unfold sk. rewrite SEG. intros a [X|X]; [apply HWS; lia | apply HERR; exact X]. }
  { intros x Hx O. destruct (hg_not_out _ _ O) as (lo & hi & [E|[]] & Hlh). injection E as <- <-. left. lia. }
  { intros a Ho. pose proof (mr_owned_low _ _ LAWS _ _ _ _ a HMR Ho). apply hg_out. intros lo hi [E|[]].
    injection E as <- <-. left. lia. }
  { intros p n i Hp Hi O. exfalso. destruct (mr_blocks _ _ LAWS _ _ _ _ p n i HMR Hp Hi) as (_ & B1 & B2 & _).
    destruct (hg_not_out _ _ O) as (lo & hi & [E|[]] & Hlh). injection E as <- <-. lia. }
  pose proof (ro_agree_same rsegs mem m1 RO ROS) as RO1.
  pose proof RM0 as (HM1 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & SC1).
  assert (HK0 : alloc_ceiling <= bv_unsigned sp - 8304) by lia.
  destruct (src_rest_rmid Bm API AX BW 8304 (bv_unsigned sp) (fun _ => False) (fun _ => False) L A mem md L A m1 md
              HA h SEG HK0 HMR RM0 PLR' SRC (fun a X => False_ind _ X) (fun q X => False_ind _ X)) as (SB1 & LE1).
  assert (LH1 : list_at Bm L A m1 (HA + 80) H true).
  { apply (list_at_rmid Bm API AX BW 8304 (bv_unsigned sp) (fun _ => False) (fun _ => False) L A mem md L A m1 md
             (HA + 80) H true SEG HK0 HMR RM0 LH).
    - intros i Hi. split; [apply PLR'; lia | intros []].
    - intros q _. split; [intros [] | intros k i _ _ []]. }
  assert (SRC1 : src_at Bm L A m1 HA h).
  { apply src_at_iff. split; [exact SB1|]. split; [exact LE1|]. split; [exact LH1 | exact NDB]. }
  assert (HLN1 : bytes_at rsegs m1 LINE ln).
  { eapply bytes_at_transport; [exact HLN | exact MU0 |]. cbn [disjoint_from]. split; [lia | exact I]. }
  assert (PRT : forall q, In q (list_blocks (hs_pending h) ++ [hs_partial h] ++ list_blocks (hs_expected h)) ->
                exists k0, 0 < k0 /\ In (q, k0) (blocks L A))
    by exact (src_parts_pos Bm L A mem HA h SB LE).
  assert (EHS : forall (E : Z -> Prop), (forall a, E a -> (HA + 80 <= a < HA + 96) \/
                  (0 < CAP /\ hl_v H <= a < hl_v H + 16 * CAP)) -> forall a, E a -> (HA + 80 <= a < HA + 96) \/
                  (0 < hl_cap (hs_held h) /\ hl_v (hs_held h) <= a < hl_v (hs_held h) + 16 * hl_cap (hs_held h)))
    by (intros E HE a X; exact (HE a X)).
  destruct ARM as [(UPD & EQ)|[(jj & Hjj & GB & NIN & EQ)|(ii & Hii & GE & EQ)]].
  - injection EQ as ER EP. subst R pc'.
    rewrite gm_G_wrecs in UPD.
    destruct (gm_tr_none (sh_of (known_at L A) H) (bzs ln) O ltac:(rewrite SK; exact UPD)) as [TR0 SH0].
    apply SR_ret. exists L, A, regs1, m1, md, H.
    split; [f_equal; f_equal; change (reg_get regs 1) with (getr regs 1); exact (ret_pc_of_ok _ HRA)|].
    split.
    { apply rp_join; [rewrite SPE | gm_saved GR].
      apply (rmid_EF Bm API _ _ _ _ _ _ _ _ _ _ _ _ _ _ RM0); intros ? []. }
    split; [exact INIT|].
    split.
    { rewrite TR0, SH0. exists []. split; [reflexivity|]. split; [exact RES|].
      split; [exact (gm_sh_real L A mem (HA + 80) H true [] LH)|].
      exact (gm_sh_live L A mem (HA + 80) H true LH). }
    split; [exact RO1|].
    split; [change (set_held h H) with (set_held h (hs_held h)); rewrite set_held_self; exact SRC1|].
    split; [exact NDT|].
    split; [symmetry; exact UPD|].
    split; [exact HLN1|].
    split; [intros q m Hq _; exact Hq|].
    split.
    { intros q m Hq. destruct (in_dec Z.eq_dec q (list_blocks H)) as [I|I];
        [right; exact I | left; split; [exact Hq | intros _; exact I]]. }
    split; [intros q m _ _ I; exact I|].
    left. split; [reflexivity | split; reflexivity].
  - injection EQ as ER EP. subst R pc'.
    set (x := firstn jj ln) in *.
    assert (GB' : gesture (bzs ln) = Some (GBegin, bzs x)) by exact GB.
    assert (NIN' : ~ In (bzs x) (texts H)) by (rewrite <- gm_G_wrecs; exact NIN).
    assert (LX : Z.of_nat (length x) = Z.of_nat jj) by (unfold x; rewrite length_firstn; lia).
    assert (EXF : existsb (list_eqb (bzs x)) (texts H) = false).
    { apply not_true_iff_false. intros E. apply existsb_exists in E as (y & Iy & Ey).
      apply gm_eqb_true in Ey. subst y. exact (NIN' Iy). }
    destruct (gm_tr_begin (sh_of (known_at L A) H) (bzs ln) (bzs x) GB' ltac:(rewrite SK; exact EXF)) as [TRB SHB].
    assert (E1_1 : getr regs1 1 = getr regs 1) by (rewrite GR; reflexivity).
    assert (E1_2 : getr regs1 2 = sp) by (rewrite GR; reflexivity).
    assert (E1_4 : getr regs1 4 = getr regs 4) by (rewrite GR; reflexivity).
    assert (E1_10 : PropExec.getr regs1 10 = Z_to_bv 64 (HA + 80)).
    { change (PropExec.getr regs1 10) with (getr regs1 10). rewrite GR.
      transitivity (Z_to_bv 64 (bv_unsigned (reg_get regs 10) + 80)); [reflexivity | rewrite A0; reflexivity]. }
    assert (E1_11 : PropExec.getr regs1 11 = Z_to_bv 64 LINE)
      by (change (PropExec.getr regs1 11) with (getr regs1 11); rewrite GR; reflexivity).
    assert (E1_12 : PropExec.getr regs1 12 = Z_to_bv 64 (Z.of_nat jj))
      by (change (PropExec.getr regs1 12) with (getr regs1 12); rewrite GR; reflexivity).
    assert (SP1 : spZ regs1 = bv_unsigned sp) by (unfold spZ; rewrite E1_2; reflexivity).
    assert (LINEu : bv_unsigned (Z_to_bv 64 LINE) = LINE) by (apply unsigned_lit; lia).
    assert (LAu : bv_unsigned (Z_to_bv 64 (HA + 80)) = HA + 80) by (apply unsigned_lit; lia).
    assert (JJu : bv_unsigned (Z_to_bv 64 (Z.of_nat jj)) = Z.of_nat jj) by (apply unsigned_lit; lia).
    assert (HLNx : bytes_at rsegs m1 LINE x) by (apply gm_first; exact HLN1).
    pose proof PUSH as PUSHc. unfold list_push_contract in PUSHc. rewrite SEG in PUSHc.
    assert (EKP : LIST_PUSH_K = 8304) by reflexivity. rewrite EKP in PUSHc.
    unfold LIST_PUSH in PUSHc.
    eapply SR_mono.
    { apply (PUSHc L A regs1 m1 md bnd H true x).
      - reflexivity.
      - eapply cpk_of_rmid; [exact RM0 | exact INIT | rewrite E1_1; exact HRA | rewrite E1_4; exact HTP
                             | rewrite SP1; exact HAL | rewrite SP1; lia | rewrite SP1; lia | lia
                             | rewrite SP1; lia | rewrite SP1; exact H63].
      - exact INIT.
      - exact RO1.
      - rewrite E1_10, LAu. intros a Ha. split; [apply PLR'; lia | apply hf_ro_glob; lia].
      - rewrite E1_10, LAu. exact LH1.
      - intros X. unfold N, CAP in *. lia.
      - rewrite E1_12, JJu. lia.
      - rewrite E1_11, LINEu. exact HLNx.
      - rewrite E1_12, JJu. exact LX.
      - rewrite E1_11, E1_12, LINEu, JJu, SP1. right. left. exists q0, m0.
        split; [exact Bq|]. split; [exact QV|]. lia.
      - rewrite E1_10, E1_11, E1_12, LAu, LINEu, JJu.
        destruct (Z_le_gt_dec (LINE + Z.of_nat jj) (HA + 80)) as [D|D]; [left; exact D|].
        destruct (Z_le_gt_dec (HA + 80 + 16) LINE) as [D'|D']; [right; exact D'|]. exfalso.
        assert (Ha1 : q0 <= Z.max LINE (HA + 80) < q0 + m0) by lia.
        assert (Ha2 : HA + 80 <= Z.max LINE (HA + 80) < HA + 96) by lia.
        apply (Fq3 (Z.max LINE (HA + 80) - q0) ltac:(lia)).
        replace (q0 + (Z.max LINE (HA + 80) - q0)) with (Z.max LINE (HA + 80)) by lia.
        exact (proj1 (PLR' (Z.max LINE (HA + 80)) ltac:(lia))).
      - intros _. rewrite E1_12, JJu. split; [|lia].
        intros X. apply NZ. rewrite <- (firstn_skipn jj ln). apply in_or_app. left. exact X.
      - intros X. discriminate.
      - exact RES.
      - rewrite <- TRB. exact ROOM. }
    intros c' (L' & A' & regs' & mem' & md' & l' & d & -> & RP & INIT' & RES' & RO' & LH' & RECS' & CAP' & VS' &
      B1' & B2' & B3').
    rewrite E1_10, LAu in LH', RP.
    destruct (rp_split Bm API _ _ _ _ _ _ _ _ _ _ _ _ _ RP) as (RMp & PRp). rewrite SP1 in RMp.
    pose proof (rmid_seq Bm API _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HWF RM0 RMp) as RMall.
    assert (EP' : forall a, (fun a => HA + 80 <= a < HA + 80 + 16 \/
                     (N < CAP /\ hl_v H + 16 * N <= a < hl_v H + 16 * (N + 1))) a ->
                  (HA + 80 <= a < HA + 96) \/ (0 < CAP /\ hl_v H <= a < hl_v H + 16 * CAP)).
    { intros a [X|(X1 & X2)]; [left; lia | right; split; lia]. }
    assert (FP' : forall q, (fun q => N = CAP /\ 0 < CAP /\ q = hl_v H) q -> In q (list_blocks H)).
    { intros q (X1 & X2 & ->). exact (proj2 (hf_list_v Bm L A mem _ H true LH X2)). }
    destruct (src_rest_rmid Bm API AX BW 8304 (bv_unsigned sp) _ _ L A m1 md L' A' mem' md' HA h SEG HK0 HM1 RMp
                PLR' SRC1 EP' FP') as (SB2 & LE2).
    exists L', A', regs', mem', md', l'.
    split; [do 2 f_equal; exact E1_1|].
    split.
    { apply rp_join; [rewrite SPE; apply (rmid_EF Bm API _ _ _ _ _ _ _ _ _ _ _ _ _ _ RMall)|].
      - intros a [[]|X]. exact (EP' a X).
      - intros q [[]|X]. exact (FP' q X).
      - intros r Hr. rewrite (PRp r Hr). revert r Hr. gm_saved GR. }
    split; [exact INIT'|].
    split; [rewrite TRB, SHB; exact RES'|].
    split; [exact RO'|].
    split.
    { apply (src_at_set_held Bm L' A' mem' HA h l' SB2 LE2 LH'); [|exact NDB].
      intros q Hq. destruct (PRT q Hq) as (k0 & Hk0 & Hin). exact (B3' q k0 Hin Hk0 (src_out h NDB q Hq)). }
    assert (TX : texts l' = texts H ++ [bzs x]) by (unfold texts; rewrite RECS', map_app; reflexivity).
    split.
    { rewrite TX. apply hf_nodup. apply hf_nodup_app; [apply hf_nodup; exact NDT | |].
      - constructor; [intros [] | constructor].
      - intros a Ha [<-|[]]. exact (NIN' Ha). }
    split; [rewrite TX, (gm_upd_begin_new _ _ _ GB' NIN'); reflexivity|].
    split.
    { assert (KQ : kept_block (fun a => HA + 80 <= a < HA + 80 + 16 \/
                     (N < CAP /\ hl_v H + 16 * N <= a < hl_v H + 16 * (N + 1)))
                     (fun q => N = CAP /\ 0 < CAP /\ q = hl_v H) L A q0).
      { apply (hf_kept Bm API AX L A m1 md _ _ (HA + 80) (HA + 96) CAP (hl_v H) q0 HM1).
        - intros a Ha. exact (proj1 (PLR' a ltac:(lia))).
        - exact EP'.
        - intros HC. exact (proj1 (hf_list_v Bm L A mem _ H true LH HC)).
        - intros (_ & _ & X). exact (QV X).
        - intros _. exact QV. }
      destruct KQ as [NF NE].
      rewrite <- SEG.
      eapply (rmid_bytes_block Bm API BW _ _ _ _ _ _ _ _ _ _ _ _ q0 m0 _ _ RMp Bq ltac:(lia) NF);
        [rewrite SEG; exact HLN1 | lia | lia |].
      intros i Hi. replace (LINE + i) with (q0 + (LINE - q0 + i)) by lia. apply (NE m0 (LINE - q0 + i) Bq). lia. }
    split; [exact B1'|]. split; [exact B2'|]. split; [exact B3'|].
    right. left. exists x, d. split; [exact GB'|]. split; [exact NIN'|]. split; [exact RECS'|].
    split; [exact CAP' | exact VS'].
  - injection EQ as ER EP. subst R pc'.
    rewrite gm_G_wrecs in GE. change (gm_txt ln) with (bzs ln) in GE.
    assert (Hii' : (ii < length (hl_recs H))%nat) by (unfold wrecs in Hii; rewrite length_map in Hii; exact Hii).
    assert (LT : (ii < length (texts H))%nat) by (unfold texts; rewrite length_map; exact Hii').
    destruct (gm_tr_end (sh_of (known_at L A) H) (bzs ln) ii ltac:(rewrite SK; exact GE)
                ltac:(rewrite SK; apply hf_nodup; exact NDT) ltac:(rewrite SK; exact LT)) as [TRE SHE].
    assert (E1_1 : getr regs1 1 = getr regs 1) by (rewrite GR; reflexivity).
    assert (E1_2 : getr regs1 2 = sp) by (rewrite GR; reflexivity).
    assert (E1_4 : getr regs1 4 = getr regs 4) by (rewrite GR; reflexivity).
    assert (E1_10 : PropExec.getr regs1 10 = Z_to_bv 64 (HA + 80)).
    { change (PropExec.getr regs1 10) with (getr regs1 10). rewrite GR.
      transitivity (Z_to_bv 64 (bv_unsigned (reg_get regs 10) + 80)); [reflexivity | rewrite A0; reflexivity]. }
    assert (E1_11 : PropExec.getr regs1 11 = Z_to_bv 64 (Z.of_nat ii))
      by (change (PropExec.getr regs1 11) with (getr regs1 11); rewrite GR; reflexivity).
    assert (SP1 : spZ regs1 = bv_unsigned sp) by (unfold spZ; rewrite E1_2; reflexivity).
    assert (LAu : bv_unsigned (Z_to_bv 64 (HA + 80)) = HA + 80) by (apply unsigned_lit; lia).
    assert (IIu : bv_unsigned (Z_to_bv 64 (Z.of_nat ii)) = Z.of_nat ii) by (apply unsigned_lit; unfold N, hl_n in *; lia).
    pose proof DROP as DROPc. unfold list_drop_contract in DROPc. rewrite SEG in DROPc.
    assert (EKD : LIST_DROP_K = 8224) by reflexivity. rewrite EKD in DROPc.
    unfold LIST_DROP in DROPc.
    eapply SR_mono.
    { apply (DROPc L A regs1 m1 md bnd H true).
      - reflexivity.
      - eapply cpk_of_rmid; [exact RM0 | exact INIT | rewrite E1_1; exact HRA | rewrite E1_4; exact HTP
                             | rewrite SP1; exact HAL | rewrite SP1; lia | rewrite SP1; lia | lia
                             | rewrite SP1; lia | rewrite SP1; exact H63].
      - exact INIT.
      - exact RO1.
      - rewrite E1_10, LAu. intros a Ha. split; [apply PLR'; lia | apply hf_ro_glob; lia].
      - rewrite E1_10, LAu. exact LH1.
      - rewrite E1_11, IIu. unfold hl_n. lia.
      - exact RES. }
    intros c' (L' & A' & regs' & mem' & md' & l' & -> & RP & INIT' & RES' & RO' & LH' & VS' & CS' & RECS' & _ &
      (b1 & b2 & BLa & BLb)).
    rewrite E1_10, LAu in LH', RP. rewrite E1_11, IIu, Nat2Z.id in RP, RES', RECS', BLa.
    set (r := nth ii (hl_recs H) (0, [])) in *.
    assert (Ir : In (fst r) (list_blocks H)).
    { unfold list_blocks. apply in_or_app. right. apply in_map. apply nth_In. exact Hii'. }
    destruct (rp_split Bm API _ _ _ _ _ _ _ _ _ _ _ _ _ RP) as (RMd0 & PRd). rewrite SP1 in RMd0.
    assert (WR1 : forall a, bv_unsigned sp - 8304 <= a < bv_unsigned sp -> writable_at (ms_segs Bm) m1 a)
      by (intros a Ha; apply SC1; unfold sk; left; exact Ha).
    assert (NE1 : forall a, bv_unsigned sp - 8304 <= a < bv_unsigned sp ->
              ~ (HA + 80 + 8 <= a < HA + 80 + 12 \/ hl_v H + 16 * Z.of_nat ii <= a < hl_v H + 16 * (hl_n H - 1))).
    { intros a Ha [X|X]; [lia|]. destruct NC as [NC1 NC2]. destruct (VB ltac:(lia)) as [VB1 VB2]. lia. }
    pose proof (rmid_widen Bm API 8224 (bv_unsigned sp) 8304 (bv_unsigned sp) _ _ _ _ _ _ _ _ _ _ HM1
                  ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) WR1 NE1 RMd0) as RMd.
    pose proof (rmid_seq Bm API _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HWF RM0 RMd) as RMall.
    assert (ED' : forall a, (fun a => HA + 80 + 8 <= a < HA + 80 + 12 \/
                     hl_v H + 16 * Z.of_nat ii <= a < hl_v H + 16 * (N - 1)) a ->
                  (HA + 80 <= a < HA + 96) \/ (0 < CAP /\ hl_v H <= a < hl_v H + 16 * CAP)).
    { intros a [X|X]; [left; lia | right; destruct NC as [NC1 NC2]; split; lia]. }
    assert (FD' : forall q, (fun q => q = fst r) q -> In q (list_blocks H)) by (intros q ->; exact Ir).
    destruct (src_rest_rmid Bm API AX BW 8304 (bv_unsigned sp) _ _ L A m1 md L' A' mem' md' HA h SEG HK0 HM1 RMd
                PLR' SRC1 ED' FD') as (SB2 & LE2).
    exists L', A', regs', mem', md', l'.
    split; [do 2 f_equal; exact E1_1|].
    split.
    { apply rp_join; [rewrite SPE; apply (rmid_EF Bm API _ _ _ _ _ _ _ _ _ _ _ _ _ _ RMall)|].
      - intros a [[]|X]. exact (ED' a X).
      - intros q [[]|X]. exact (FD' q X).
      - intros rr Hr. rewrite (PRd rr Hr). revert rr Hr. gm_saved GR. }
    split; [exact INIT'|].
    split; [rewrite TRE, SHE; exact RES'|].
    split; [exact RO'|].
    split.
    { apply (src_at_set_held Bm L' A' mem' HA h l' SB2 LE2 LH'); [|exact NDB].
      intros q Hq X. apply (src_out h NDB q Hq). exact (hf_lb_drop H l' ii q VS' CS' RECS' X). }
    assert (TX : texts l' = firstn ii (texts H) ++ skipn (S ii) (texts H)).
    { unfold texts. rewrite RECS'. apply hf_texts_drop. }
    split; [rewrite TX; apply hf_nodup; apply hf_nodup_drop; apply hf_nodup; exact NDT|].
    split; [rewrite TX; symmetry; apply (gm_upd_end_at _ _ ii GE); [apply hf_nodup; exact NDT | exact LT]|].
    split.
    { assert (KQ : kept_block (fun a => HA + 80 + 8 <= a < HA + 80 + 12 \/
                     hl_v H + 16 * Z.of_nat ii <= a < hl_v H + 16 * (N - 1)) (fun q => q = fst r) L A q0).
      { apply (hf_kept Bm API AX L A m1 md _ _ (HA + 80) (HA + 96) CAP (hl_v H) q0 HM1).
        - intros a Ha. exact (proj1 (PLR' a ltac:(lia))).
        - exact ED'.
        - intros HC. exact (proj1 (hf_list_v Bm L A mem _ H true LH HC)).
        - intros X. apply Qn. rewrite X. exact Ir.
        - intros _. exact QV. }
      destruct KQ as [NF NE].
      assert (LP : 1 <= LEN \/ LEN = 0) by lia. destruct LP as [LP|LZ].
      - rewrite <- SEG.
        eapply (rmid_bytes_block Bm API BW _ _ _ _ _ _ _ _ _ _ _ _ q0 m0 _ _ RMd Bq ltac:(lia) NF);
          [rewrite SEG; exact HLN1 | lia | lia |].
        intros i Hi. replace (LINE + i) with (q0 + (LINE - q0 + i)) by lia. apply (NE m0 (LINE - q0 + i) Bq). lia.
      - destruct ln as [|b ln']; [split; [cbn; lia | split; [cbn; lia | intros i Hi; cbn in Hi; lia]] | cbn in HLEN; lia]. }
    split.
    { intros q m Hq Hn. rewrite BLb. rewrite BLa in Hq. apply in_app_iff in Hq as [Hq|[Hq|Hq]].
      - apply in_or_app. left. exact Hq.
      - exfalso. injection Hq as E1 E2. apply Hn. rewrite <- E1. exact Ir.
      - apply in_or_app. right. exact Hq. }
    split.
    { intros q m Hq. rewrite BLb in Hq.
      assert (HqA : In (q, m) (blocks L A)).
      { rewrite BLa. apply in_app_iff in Hq as [Hq|Hq]; apply in_or_app; [left; exact Hq | right; right; exact Hq]. }
      destruct (in_dec Z.eq_dec q (list_blocks H)) as [I|I]; [|left; split; [exact HqA | intros _; exact I]].
      destruct (Z.eq_dec q (fst r)) as [Eq|Nq].
      - left. split; [exact HqA|]. intros Hm. exfalso. subst q.
        destruct (blocks_mid_disjoint Bm (aa_MR API) LAWS L A mem md b1 b2 (fst r) (text_len r) (fst r) m HMR BLa Hq);
          unfold text_len in *; lia.
      - right. unfold list_blocks in I |- *. rewrite VS', CS', RECS'.
        apply in_app_iff in I as [I|I]; apply in_or_app; [left; exact I | right].
        apply in_map_iff in I as (r' & <- & Ir'). apply in_map.
        apply (hf_in_keep _ ii r' (0, [])); [exact Hii' | exact Ir' | intros X; apply Nq; rewrite X; reflexivity]. }
    split; [intros q m Hq Hm Hn X; exact (Hn (hf_lb_drop H l' ii q VS' CS' RECS' X))|].
    right. right. exists ii. split; [exact Hii'|]. split; [exact GE|]. split; [exact RECS'|].
    split; [exact VS'|]. split; [exact CS'|]. exists b1, b2. split; [exact BLa | exact BLb].
Qed.

End GMB.
