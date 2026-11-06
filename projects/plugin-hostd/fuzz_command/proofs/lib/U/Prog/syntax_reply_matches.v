From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes ZBridge.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U Require Import Img0.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Spec Require Import StrFun.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog Require Import CommandModel CommandTac strcspn_c bcmp_c syntax_reply_matches_c.
Import ListNotations.
Open Scope Z_scope.

Lemma hd_skipn_S : forall (l : list byte) k, (k < length l)%nat -> skipn k l = hd NUL (skipn k l) :: skipn (S k) l.
Proof. induction l as [|x l IH]; intros [|k] H; cbn in *; try lia; [reflexivity|]. apply IH. lia. Qed.

Lemma hd_skipn_end : forall (l : list byte) k, (length l <= k)%nat -> hd NUL (skipn k l) = NUL.
Proof. intros l k H. rewrite skipn_all2 by exact H. reflexivity. Qed.

Lemma hd_nz_lt : forall (l : list byte) k, bv_unsigned (hd NUL (skipn k l)) <> 0 -> (k < length l)%nat.
Proof.
  intros l k H. destruct (Nat.lt_ge_cases k (length l)) as [L|L]; [exact L|].
  rewrite hd_skipn_end in H by exact L. exfalso. apply H. reflexivity.
Qed.

Lemma hd_in : forall (l : list byte) k, (k < length l)%nat -> In (hd NUL (skipn k l)) l.
Proof.
  induction l as [|x l IH]; intros [|k] H; cbn in *; try lia.
  - left. reflexivity.
  - right. apply IH. lia.
Qed.

Lemma hd_z_end : forall (l : list byte) k, ~ In NUL l -> (k <= length l)%nat ->
  bv_unsigned (hd NUL (skipn k l)) = 0 -> k = length l.
Proof.
  intros l k Hn Hk H. destruct (Nat.lt_ge_cases k (length l)) as [L|L]; [|lia].
  exfalso. apply Hn. replace NUL with (hd NUL (skipn k l)); [apply hd_in; exact L|].
  apply bv_eq. rewrite H. reflexivity.
Qed.

Lemma hd_nz : forall (l : list byte) k, ~ In NUL l -> (k < length l)%nat -> bv_unsigned (hd NUL (skipn k l)) <> 0.
Proof. intros l k Hn Hk H. pose proof (hd_z_end l k Hn ltac:(lia) H). lia. Qed.

Lemma rd_hd : forall m A (l sl : list byte) k, bytes_at rsegs m A (l ++ NUL :: sl) -> (k <= length l)%nat ->
  ov_read_bytes rsegs m (wa (A + Z.of_nat k)) 1 = Some [hd NUL (skipn k l)].
Proof.
  intros m A l sl k H Hk.
  rewrite (bytes_at_read rsegs m A (l ++ NUL :: sl) (Z.of_nat k) 1 H) by (try rewrite Nat2Z.id; try rewrite length_app; cbn [length]; lia).
  rewrite Nat2Z.id, skipn_app. replace (k - length l)%nat with 0%nat by lia. cbn [skipn].
  destruct (skipn k l) as [|b t]; reflexivity.
Qed.

Lemma rd_in : forall m A (l : list byte) k, bytes_at rsegs m A l -> (k < length l)%nat ->
  ov_read_bytes rsegs m (wa (A + Z.of_nat k)) 1 = Some [hd NUL (skipn k l)].
Proof.
  intros m A l k H Hk.
  rewrite (bytes_at_read rsegs m A l (Z.of_nat k) 1 H) by (try rewrite Nat2Z.id; lia).
  rewrite Nat2Z.id. rewrite (hd_skipn_S l k Hk). reflexivity.
Qed.

Lemma bytes_at_sub : forall m A (l : list byte) k n, bytes_at rsegs m A l -> (k + n <= length l)%nat ->
  bytes_at rsegs m (A + Z.of_nat k) (firstn n (skipn k l)).
Proof.
  intros m A l k n H Hk. pose proof (bytes_at_skipn m A l k H ltac:(lia)) as H1.
  rewrite <- (firstn_skipn n (skipn k l)) in H1. apply bytes_at_app in H1. exact (proj1 H1).
Qed.

Lemma skip_sp_at : forall (l : list byte) k, (k <= length l)%nat ->
  skip_sp (skipn k l) = if bz (hd NUL (skipn k l)) =? 32 then skip_sp (skipn (S k) l) else skipn k l.
Proof.
  intros l k Hk. destruct (Nat.lt_ge_cases k (length l)) as [L|L].
  - rewrite (hd_skipn_S l k L). cbn [skip_sp hd]. reflexivity.
  - rewrite (skipn_all2 l L). reflexivity.
Qed.

Definition dstep (d : Z) (b : byte) : Z :=
  if (bz b =? 60) || (bz b =? 91) then d + 1
  else if ((bz b =? 62) || (bz b =? 93)) && (0 <? d) then d - 1 else d.

Definition ilen (d : Z) (s : list byte) : nat := length (fst (item_scan d s)).

Lemma ilen_cons : forall d b s,
  ilen d (b :: s) = if (d =? 0) && (bz b =? 32) then 0%nat else S (ilen (dstep d b) s).
Proof.
  intros d b s. unfold ilen, dstep. cbn [item_scan].
  destruct ((d =? 0) && (bz b =? 32)); [reflexivity|].
  destruct (item_scan _ s); reflexivity.
Qed.

Lemma ilen_nil : forall d, ilen d [] = 0%nat.
Proof. reflexivity. Qed.

Lemma item_scan_app : forall s d it rest, item_scan d s = (it, rest) -> it ++ rest = s.
Proof.
  induction s as [|b s IH]; intros d it rest H; cbn [item_scan] in H.
  - injection H as <- <-. reflexivity.
  - destruct ((d =? 0) && (bz b =? 32)).
    + injection H as <- <-. reflexivity.
    + destruct (item_scan _ s) as [it' rest'] eqn:E. injection H as <- <-. cbn [app]. f_equal. eapply IH. exact E.
Qed.

Lemma item_scan_fst : forall d s, fst (item_scan d s) = firstn (ilen d s) s.
Proof.
  intros d s. unfold ilen. destruct (item_scan d s) as [it rest] eqn:E. cbn [fst].
  rewrite <- (item_scan_app s d it rest E). rewrite firstn_app, Nat.sub_diag, firstn_all, firstn_O, app_nil_r. reflexivity.
Qed.

Lemma item_scan_snd : forall d s, snd (item_scan d s) = skipn (ilen d s) s.
Proof.
  intros d s. unfold ilen. destruct (item_scan d s) as [it rest] eqn:E. cbn [fst snd].
  rewrite <- (item_scan_app s d it rest E). rewrite skipn_app, Nat.sub_diag, skipn_all. reflexivity.
Qed.

Lemma ilen_le : forall d s, (ilen d s <= length s)%nat.
Proof.
  intros d s. unfold ilen. destruct (item_scan d s) as [it rest] eqn:E. cbn [fst].
  rewrite <- (item_scan_app s d it rest E). rewrite length_app. lia.
Qed.

Lemma items_f_nil : forall f s, skip_sp s = [] -> items_f f s = [].
Proof. intros [|f] s H; cbn [items_f]; [reflexivity|]. rewrite H. reflexivity. Qed.

Lemma items_f_cons : forall f s s1, skip_sp s = s1 -> s1 <> [] ->
  items_f (S f) s = fst (item_scan 0 s1) :: items_f f (snd (item_scan 0 s1)).
Proof.
  intros f s s1 E N. cbn [items_f]. rewrite E. destruct s1 as [|b t]; [congruence|].
  cbn beta iota. destruct (item_scan 0 (b :: t)); reflexivity.
Qed.

Lemma cspn_word : forall r, cspn_len [Z_to_bv 8 32] r = word_len r.
Proof.
  induction r as [|b r IH]; cbn [cspn_len word_len existsb]; [reflexivity|].
  replace (bv_unsigned (Z_to_bv 8 32)) with 32 by reflexivity.
  rewrite orb_false_r, Z.eqb_sym, IH. reflexivity.
Qed.

Lemma word_len_le : forall r, (word_len r <= length r)%nat.
Proof. induction r as [|b r IH]; cbn [word_len length]; [lia|]. destruct (bz b =? 32); lia. Qed.

Lemma word_len_skip : forall r, skipn (word_len r) r = [] \/ exists b t, skipn (word_len r) r = b :: t /\ bz b = 32.
Proof.
  induction r as [|b r IH]; cbn [word_len]; [left; reflexivity|].
  destruct (Z.eqb_spec (bz b) 32) as [E|E].
  - right. exists b, r. split; [reflexivity|exact E].
  - cbn [skipn]. exact IH.
Qed.

Lemma memcmp_eq : forall n l r, (n <= length l)%nat -> (n <= length r)%nat ->
  exists v, memcmp_model l r n = Some v /\ (v = 0 <-> firstn n l = firstn n r).
Proof.
  induction n as [|n IH]; intros l r Hl Hr.
  - exists 0. split; [reflexivity|]. split; intros; reflexivity.
  - destruct l as [|a l]; [cbn in Hl; lia|]. destruct r as [|b r]; [cbn in Hr; lia|].
    cbn [length] in Hl, Hr. cbn [memcmp_model firstn].
    destruct (Z.eqb_spec (bv_unsigned a) (bv_unsigned b)) as [E|E].
    + destruct (IH l r ltac:(lia) ltac:(lia)) as (v & Hv & Hv0). exists v. split; [exact Hv|].
      rewrite Hv0. replace b with a by (apply bv_eq; exact E).
      split; [intros ->; reflexivity | intros H; injection H as H; exact H].
    + eexists. split; [reflexivity|]. split; [intros H; lia | intros H; injection H as H1 _; subst; lia].
Qed.

Lemma bytes_eqb_len : forall a b, length a <> length b -> bytes_eqb a b = false.
Proof.
  intros a b H. destruct (bytes_eqb a b) eqn:E; [|reflexivity].
  apply bytes_eqb_iff in E. subst. congruence.
Qed.

Lemma has_lt_skipn : forall (it : list byte) q, (q < length it)%nat ->
  has_lt (skipn q it) = (bz (hd NUL (skipn q it)) =? 60) || has_lt (skipn (S q) it).
Proof. intros it q H. rewrite (hd_skipn_S it q H) at 1. reflexivity. Qed.

Lemma has_lt_end : forall (it : list byte) q, (length it <= q)%nat -> has_lt (skipn q it) = false.
Proof. intros it q H. rewrite skipn_all2 by exact H. reflexivity. Qed.

Lemma dstep_open : forall d b, bv_unsigned b = 60 \/ bv_unsigned b = 91 -> dstep d b = d + 1.
Proof. intros d b [H|H]; unfold dstep, bz; rewrite H; reflexivity. Qed.

Lemma dstep_close : forall d b, bv_unsigned b = 62 \/ bv_unsigned b = 93 -> 0 < d -> bv_unsigned b <> 60 -> bv_unsigned b <> 91 ->
  dstep d b = d - 1.
Proof.
  intros d b H Hd H60 H91. unfold dstep, bz.
  rewrite (proj2 (Z.eqb_neq _ _) H60), (proj2 (Z.eqb_neq _ _) H91). cbn [orb].
  rewrite (proj2 (Z.ltb_lt _ _) Hd). destruct H as [H|H]; rewrite H; reflexivity.
Qed.

Lemma dstep_same : forall d b, bv_unsigned b <> 60 -> bv_unsigned b <> 91 ->
  (bv_unsigned b <> 62 /\ bv_unsigned b <> 93) \/ d <= 0 -> dstep d b = d.
Proof.
  intros d b H60 H91 H. unfold dstep, bz.
  rewrite (proj2 (Z.eqb_neq _ _) H60), (proj2 (Z.eqb_neq _ _) H91). cbn [orb].
  destruct H as [[H1 H2]|H].
  - rewrite (proj2 (Z.eqb_neq _ _) H1), (proj2 (Z.eqb_neq _ _) H2). reflexivity.
  - rewrite (proj2 (Z.ltb_ge _ _) H), andb_false_r. reflexivity.
Qed.

Lemma swrap32_id : forall z, -2^31 <= z < 2^31 -> bv_swrap 32 z = z.
Proof. intros z Hz. apply bv_swrap_small. replace (bv_half_modulus 32) with (2^31) by reflexivity. lia. Qed.

Lemma pos_false : forall d, (0 <? d) && (d <? 9223372036854775808) = false -> d < 9223372036854775808 -> d <= 0.
Proof.
  intros d H1 H2. destruct (Z.ltb_spec 0 d) as [L|L]; [|lia].
  destruct (Z.ltb_spec d 9223372036854775808); [discriminate | lia].
Qed.

Lemma memcmp_range : forall n l r v, memcmp_model l r n = Some v -> -256 < v < 256.
Proof.
  induction n as [|n IH]; intros [|a l] [|b r] v H; cbn in H; try discriminate; try (injection H as <-; lia).
  pose proof (byte_range a). pose proof (byte_range b).
  destruct (bv_unsigned a =? bv_unsigned b); [eapply IH; exact H | injection H as <-; lia].
Qed.

Lemma skipn_add : forall (l : list byte) k n, skipn (k + n) l = skipn n (skipn k l).
Proof. intros. rewrite skipn_skipn, Nat.add_comm. reflexivity. Qed.

Ltac pos_false_tac :=
  match goal with H : (0 <? _) && (_ <? 9223372036854775808) = false |- _ => apply pos_false in H; [|lia] end.

Lemma rmi_cons : forall it its r, reply_matches_items (it :: its) r =
  if Nat.eqb (word_len r) 0 then false
  else if negb (has_lt it) && negb (bytes_eqb it (firstn (word_len r) r)) then false
  else match skipn (word_len r) r with
       | [] => reply_matches_items its []
       | _ :: [] => false
       | _ :: r'' => reply_matches_items its r''
       end.
Proof. reflexivity. Qed.

Lemma rmi_w0 : forall it its r, word_len r = 0%nat -> reply_matches_items (it :: its) r = false.
Proof. intros it its r H. rewrite rmi_cons, H. reflexivity. Qed.

Lemma rmi_mis : forall it its r,
  negb (has_lt it) && negb (bytes_eqb it (firstn (word_len r) r)) = true -> reply_matches_items (it :: its) r = false.
Proof. intros it its r H. rewrite rmi_cons, H. destruct (Nat.eqb _ 0); reflexivity. Qed.

Lemma rmi_ok : forall it its r, word_len r <> 0%nat ->
  negb (has_lt it) && negb (bytes_eqb it (firstn (word_len r) r)) = false ->
  reply_matches_items (it :: its) r =
    match skipn (word_len r) r with
    | [] => reply_matches_items its []
    | _ :: [] => false
    | _ :: r'' => reply_matches_items its r''
    end.
Proof. intros it its r H1 H2. rewrite rmi_cons, H2, (proj2 (Nat.eqb_neq _ 0) H1). reflexivity. Qed.

Lemma firstn_len_id : forall (l : list byte) n, length l = n -> firstn n l = l.
Proof. intros l n <-. apply firstn_all. Qed.

Lemma signed_small : forall z, -2^63 <= z < 2^63 -> bv_signed (Z_to_bv 64 z) = z.
Proof.
  intros z Hz. rewrite zb_signed, unsigned_lit_wrap. destruct (Z_le_gt_dec 0 z) as [P|N].
  - rewrite Z.mod_small by lia. destruct (Z.ltb_spec z (2^63)); lia.
  - rewrite <- (Z.mod_add z 1 (2^64)), Z.mod_small by lia. destruct (Z.ltb_spec (z + 1 * 2^64) (2^63)); lia.
Qed.

Ltac fix_ret :=
  lazymatch goal with
  | |- evt _ _ (MS _ _ (ret_pc (Z_to_bv 64 ?n)) _ _ _ _) =>
      replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [lia | reflexivity])
  end.

Ltac after_call MU1 WM1 :=
  lazymatch type of MU1 with munch _ ?mq ?mq' => transport_after_call rsegs mq mq' MU1 WM1 end.

Section SRM.
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
            (m0 : word -> option byte) (lo P R : Z) (shape reply slack : list byte) (can : word).
  Hypothesis HSn : ~ In NUL shape.
  Hypothesis HRn : ~ In NUL reply.
  Hypothesis LSH : Z.of_nat (length shape) < 2^31.
  Hypothesis SL : (- (R + Z.of_nat (length reply) + 1)) mod 8 <= Z.of_nat (length slack).
  Hypothesis HSd : P + (Z.of_nat (length shape) + 1) <= lo \/ bv_unsigned sp <= P.
  Hypothesis HRd : R + (Z.of_nat (length reply) + 1 + Z.of_nat (length slack)) <= lo \/ bv_unsigned sp <= R.
  Hypothesis LO : lo + 208 <= bv_unsigned sp.
  Hypothesis IE : 348056 <= lo.
  Hypothesis BSH : 0 <= P /\ P + Z.of_nat (length shape) + 1 <= 2^64.
  Hypothesis BRE : 0 <= R /\ R + Z.of_nat (length reply) + 1 + Z.of_nat (length slack) <= 2^64.
  Hypothesis PNZ : P <> 0.
  Hypothesis RNZ : R <> 0.
  Hypothesis SPR : 0 <= bv_unsigned sp < 2^64.
  Hypothesis SCS : strcspn_contract.
  Hypothesis BC : bcmp_contract.

  Definition INV (m : word -> option byte) : Prop :=
    mem_inv rsegs m /\ stk rsegs m lo (bv_unsigned sp + -112) /\
    (exists jk, rw_cells rsegs m (bv_unsigned sp + -112)
       [CB 8 jk; C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]) /\
    munch [(lo, bv_unsigned sp)] m0 m /\ wmono rsegs m0 m /\
    bytes_at rsegs m P (shape ++ [NUL]) /\ bytes_at rsegs m R (reply ++ NUL :: slack) /\
    bytes_at rsegs m 142656 (le8 (Z_to_bv 64 345904)) /\ bytes_at rsegs m 345904 (le8 can).

  Definition POST : machine_state -> Prop := fun ms' =>
    exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : word -> option byte),
      ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 (if reply_matches shape reply then 1 else 0))
                    a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
               F (ret_pc ra) fc None m' (seg_rom rsegs) /\
      munch [(lo, bv_unsigned sp)] m0 m' /\ wmono rsegs m0 m' /\ mem_inv rsegs m' /\ stk rsegs m' lo (bv_unsigned sp).

  Ltac mk_inv := unfold INV; repeat (lazymatch goal with |- _ /\ _ => split | |- ex _ => eexists end); eassumption.

  Abbreviation LS pc xra xt0 xt1 xt2 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs11 xt3 xt4 xt5 xt6 m :=
    (MS (mkR xra (Z_to_bv 64 (bv_unsigned sp + -112)) gp tp xt0 xt1 xt2 (Z_to_bv 64 66380) xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7
             xs2 xs3 xs4 (Z_to_bv 64 32) (Z_to_bv 64 (-1)) (Z_to_bv 64 91) (Z_to_bv 64 62) (Z_to_bv 64 60) (Z_to_bv 64 93) xs11
             xt3 xt4 xt5 xt6)
        F (Z_to_bv 64 pc) fc None m (seg_rom rsegs)).

  Lemma skip_loop : forall n k m xra xt0 xt1 xt2 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs3 xs4 xt3 xt4 xt5 xt6,
    (length shape - k < n)%nat -> (k <= length shape)%nat -> bytes_at rsegs m P (shape ++ [NUL]) ->
    evt rsegs (fun ms' => exists k', (k <= k' <= length shape)%nat /\ skipn k' shape = skip_sp (skipn k shape) /\
                 bz (hd NUL (skipn k' shape)) <> 32 /\
                 ms' = LS 0x151e8 xra xt0 xt1 xt2 xs1 xa0 xa1 (zxb (hd NUL (skipn k' shape))) xa3 xa4 xa5 xa6 xa7
                          (Z_to_bv 64 (P + Z.of_nat k')) xs3 xs4 (Z_to_bv 64 (P + Z.of_nat k')) xt3 xt4 xt5 xt6 m)
      (LS 0x151d0 xra xt0 xt1 xt2 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7
          (Z_to_bv 64 (P + Z.of_nat k)) xs3 xs4 (Z_to_bv 64 (P + Z.of_nat k)) xt3 xt4 xt5 xt6 m).
  Proof.
    induction n as [|n IH]; intros k m xra xt0 xt1 xt2 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs3 xs4 xt3 xt4 xt5 xt6 HN HK HB;
      [lia|].
    pose proof (rd_hd m P shape [] k HB HK) as RD.
    pose proof (byte_range (hd NUL (skipn k shape))) as BR.
    zstep. zstep. if_cases C.
    - zify_cond C. apply evt_done. exists k. split; [lia|]. split.
      + rewrite (skip_sp_at shape k HK), (proj2 (Z.eqb_neq (bz (hd NUL (skipn k shape))) 32) C). reflexivity.
      + split; [exact C | reflexivity].
    - zify_cond C.
      pose proof (hd_nz_lt shape k ltac:(lia)) as LT.
      zstep. if_cases T.
      { exfalso. zify_cond T. lia. }
      zstep. zstep. zstep.
      replace (P + Z.of_nat k + 1) with (P + Z.of_nat (S k)) by lia.
      eapply evt_mono; [eapply IH; [lia | lia | exact HB] |].
      intros ms' (k' & Hk' & Hs & Hb & E). exists k'. split; [lia|]. split.
      + rewrite Hs, (skip_sp_at shape k HK), (proj2 (Z.eqb_eq (bz (hd NUL (skipn k shape))) 32) C). reflexivity.
      + split; [exact Hb | exact E].
  Qed.

  Lemma scan_loop : forall n q d m xra xt0 xt1 xt2 xs1 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs11 xt3 xt4 xt5 xt6,
    (length shape - q < n)%nat -> (q <= length shape)%nat -> 0 <= d <= Z.of_nat q ->
    bv_unsigned (hd NUL (skipn q shape)) <> 0 ->
    bytes_at rsegs m P (shape ++ [NUL]) ->
    evt rsegs (fun ms' => exists ya0 ya1 ya2,
                 ms' = LS 0x15240 xra xt0 xt1 xt2 xs1 ya0 ya1 ya2 xa3 xa4 xa5 xa6 xa7 xs2
                          (Z_to_bv 64 (P + Z.of_nat (q + ilen d (skipn q shape)))) xs4 xs11 xt3 xt4 xt5 xt6 m)
      (LS 0x151f4 xra xt0 xt1 xt2 xs1 (Z_to_bv 64 (P + Z.of_nat q)) (Z_to_bv 64 d) (zxb (hd NUL (skipn q shape)))
          xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs11 xt3 xt4 xt5 xt6 m).
  Proof.
    induction n as [|n IH]; intros q d m xra xt0 xt1 xt2 xs1 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs11 xt3 xt4 xt5 xt6 HN HQ HD NZ HB;
      [lia|].
    pose proof (hd_nz_lt shape q NZ) as LT.
    pose proof (byte_range (hd NUL (skipn q shape))) as BR.
    match goal with |- evt _ ?Q _ => set (POSTQ := Q) end.
    assert (TAIL : forall d' ya2, 0 <= d' <= Z.of_nat q + 1 -> d' = dstep d (hd NUL (skipn q shape)) ->
      (d =? 0) && (bz (hd NUL (skipn q shape)) =? 32) = false ->
      evt rsegs POSTQ (LS 0x15224 xra xt0 xt1 xt2 xs1 (Z_to_bv 64 (P + Z.of_nat q)) (Z_to_bv 64 d') ya2
                          xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs11 xt3 xt4 xt5 xt6 m)).
    { intros d' ya2 HD' Ed' NS.
      assert (IL : ilen d (skipn q shape) = S (ilen d' (skipn (S q) shape))).
      { rewrite (hd_skipn_S shape q LT) at 1. rewrite ilen_cons, NS, Ed'. reflexivity. }
      pose proof (rd_hd m P shape [] (S q) HB ltac:(lia)) as RD1.
      pose proof (byte_range (hd NUL (skipn (S q) shape))) as BR1.
      zstep. if_cases T.
      { exfalso. zify_cond T. lia. }
      zstep. zstep. zstep. zstep. if_cases C.
      - zify_cond C.
        replace (P + Z.of_nat q + 1) with (P + Z.of_nat (S q)) by lia.
        eapply evt_mono; [eapply IH; [lia | lia | lia | exact C | exact HB] |].
        intros ms' (ya0 & ya1 & ya2' & E). subst ms'. unfold POSTQ. exists ya0, ya1, ya2'.
        rewrite IL. replace (q + S (ilen d' (skipn (S q) shape)))%nat with (S q + ilen d' (skipn (S q) shape))%nat by lia.
        reflexivity.
      - zify_cond C.
        pose proof (hd_z_end shape (S q) HSn ltac:(lia) C) as EQ.
        rewrite (skipn_all2 shape (n := S q)) in IL by lia. rewrite ilen_nil in IL.
        zstep. apply evt_done. unfold POSTQ. do 3 eexists. rewrite IL.
        replace (P + Z.of_nat q + 1) with (P + Z.of_nat (q + 1)) by lia. reflexivity. }
    assert (INC : bv_unsigned (hd NUL (skipn q shape)) = 60 \/ bv_unsigned (hd NUL (skipn q shape)) = 91 ->
      (d =? 0) && (bz (hd NUL (skipn q shape)) =? 32) = false ->
      evt rsegs POSTQ (LS 0x15208 xra xt0 xt1 xt2 xs1 (Z_to_bv 64 (P + Z.of_nat q)) (Z_to_bv 64 d)
                          (zxb (hd NUL (skipn q shape))) xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs11 xt3 xt4 xt5 xt6 m)).
    { intros Hc NS.
      zstep. rewrite swrap32_id by lia.
      zstep. if_cases Ho.
      { exfalso. zify_cond Ho. try rewrite !signed_small in Ho by lia. lia. }
      zstep. zstep.
      apply TAIL; [lia | rewrite dstep_open by lia; lia | exact NS]. }
    assert (CLS : bv_unsigned (hd NUL (skipn q shape)) = 62 \/ bv_unsigned (hd NUL (skipn q shape)) = 93 ->
      (d =? 0) && (bz (hd NUL (skipn q shape)) =? 32) = false ->
      evt rsegs POSTQ (LS 0x1521c xra xt0 xt1 xt2 xs1 (Z_to_bv 64 (P + Z.of_nat q)) (Z_to_bv 64 d)
                          (zxb (hd NUL (skipn q shape))) xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs11 xt3 xt4 xt5 xt6 m)).
    { intros Hc NS.
      zstep. if_cases Hb.
      - zify_cond Hb. pos_false_tac.
        apply TAIL; [lia | rewrite dstep_same by lia; lia | exact NS].
      - zify_cond Hb. zstep. rewrite swrap32_id by lia.
        apply TAIL; [lia | rewrite dstep_close by lia; lia | exact NS]. }
    assert (MID : (d =? 0) && (bz (hd NUL (skipn q shape)) =? 32) = false ->
      evt rsegs POSTQ (LS 0x151fc xra xt0 xt1 xt2 xs1 (Z_to_bv 64 (P + Z.of_nat q)) (Z_to_bv 64 d)
                          (zxb (hd NUL (skipn q shape))) xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs11 xt3 xt4 xt5 xt6 m)).
    { intros NS.
      zstep. if_cases Hc2.
      - zify_cond Hc2. apply INC; [lia | exact NS].
      - zify_cond Hc2. zstep. if_cases Hc3.
        + zify_cond Hc3. apply CLS; [lia | exact NS].
        + zify_cond Hc3. zstep. if_cases Hc5.
          * zify_cond Hc5. zstep. if_cases Hc6.
            -- zify_cond Hc6.
               apply TAIL; [lia | rewrite dstep_same by lia; lia | exact NS].
            -- zify_cond Hc6. apply CLS; [lia | exact NS].
          * zify_cond Hc5. apply INC; [lia | exact NS]. }
    zstep. if_cases Hc1.
    - zify_cond Hc1. apply MID. unfold bz.
      rewrite (proj2 (Z.eqb_neq (bv_unsigned (hd NUL (skipn q shape))) 32)) by lia. rewrite andb_false_r. reflexivity.
    - zify_cond Hc1. zstep. if_cases Hc8.
      + zify_cond Hc8. pos_false_tac. zstep. apply evt_done. unfold POSTQ. do 3 eexists.
        assert (IL : ilen d (skipn q shape) = 0%nat).
        { rewrite (hd_skipn_S shape q LT), ilen_cons. unfold bz.
          rewrite (proj2 (Z.eqb_eq d 0)) by lia. rewrite (proj2 (Z.eqb_eq _ 32) Hc1). reflexivity. }
        rewrite IL, Nat.add_0_r. reflexivity.
      + zify_cond Hc8. apply MID. rewrite (proj2 (Z.eqb_neq d 0)) by lia. reflexivity.
  Qed.

  Lemma lt_loop : forall n q (it : list byte) B len m xra xt0 xt1 xt2 xs1 xa1 xa3 xa4 xa5 xa6 xa7 xs3 xs4 xs11 xt3 xt4 xt5 xt6,
    (len - q < n)%nat -> (q < len)%nat -> length it = len -> Z.of_nat len < 2^31 -> 0 <= B -> B + Z.of_nat len <= 2^64 ->
    bv_unsigned xa1 = 2^64 - 1 - B ->
    bytes_at rsegs m B it ->
    evt rsegs (fun ms' => exists ya0 ya3,
        (has_lt (skipn q it) = true /\
         ms' = LS 0x15298 xra xt0 xt1 xt2 xs1 ya0 xa1 (Z_to_bv 64 (Z.of_nat len)) ya3 xa4 xa5 xa6 xa7
                  (Z_to_bv 64 B) xs3 xs4 xs11 xt3 xt4 xt5 xt6 m) \/
        (has_lt (skipn q it) = false /\
         ms' = LS 0x15280 xra xt0 xt1 xt2 xs1 ya0 xa1 (Z_to_bv 64 (Z.of_nat len)) ya3 xa4 xa5 xa6 xa7
                  (Z_to_bv 64 B) xs3 xs4 xs11 xt3 xt4 xt5 xt6 m))
      (LS 0x15264 xra xt0 xt1 xt2 xs1 (Z_to_bv 64 (Z.of_nat q)) xa1 (Z_to_bv 64 (Z.of_nat len)) xa3 xa4 xa5 xa6 xa7
          (Z_to_bv 64 B) xs3 xs4 xs11 xt3 xt4 xt5 xt6 m).
  Proof.
    induction n as [|n IH]; intros q it B len m xra xt0 xt1 xt2 xs1 xa1 xa3 xa4 xa5 xa6 xa7 xs3 xs4 xs11 xt3 xt4 xt5 xt6
      HN HQ HL HL31 HB0 HB1 HA1 HB; [lia|].
    pose proof (rd_in m B it q HB ltac:(lia)) as RD.
    pose proof (byte_range (hd NUL (skipn q it))) as BR.
    zstep. if_cases T.
    { exfalso. zify_cond T. lia. }
    zstep. zstep. zstep. if_cases Hc.
    - zify_cond Hc. apply evt_done. do 2 eexists. left. split; [|reflexivity].
      rewrite has_lt_skipn by lia. unfold bz. rewrite (proj2 (Z.eqb_eq _ 60) Hc). reflexivity.
    - zify_cond Hc. zstep. zstep. zstep. if_cases Hg.
      + zify_cond Hg.
        replace (Z.of_nat q + 1) with (Z.of_nat (S q)) by lia.
        eapply evt_mono; [eapply IH; [lia | lia | exact HL | exact HL31 | exact HB0 | exact HB1 | exact HA1 | exact HB] |].
        intros ms' (ya0 & ya3 & [[H1 E]|[H1 E]]); exists ya0, ya3; [left|right]; (split; [|exact E]);
          rewrite has_lt_skipn by lia; unfold bz; rewrite (proj2 (Z.eqb_neq _ 60) Hc); exact H1.
      + zify_cond Hg. apply evt_done. do 2 eexists. right. split; [|reflexivity].
        rewrite has_lt_skipn by lia. unfold bz. rewrite (proj2 (Z.eqb_neq _ 60) Hc). cbn [orb].
        apply has_lt_end. lia.
  Qed.

  Lemma epi : forall m v xra xt0 xt1 xt2 xs1 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs11 xt3 xt4 xt5 xt6,
    INV m -> v = (if reply_matches shape reply then 1 else 0) ->
    evt rsegs POST (LS 0x152dc xra xt0 xt1 xt2 xs1 (Z_to_bv 64 v) xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs11 xt3 xt4 xt5 xt6 m).
  Proof.
    intros m v xra xt0 xt1 xt2 xs1 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs11 xt3 xt4 xt5 xt6
      (MI & ST & (jk & FR) & MU & WM & _) ->.
    do 13 zstep. release_frame FR ST (bv_unsigned sp). zstep. zstep. finish.
  Qed.

  Lemma ret_end : forall j m xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs11 xt3 xt4 xt5 xt6,
    INV m -> (j <= length reply)%nat ->
    reply_matches_items [] (skipn j reply) = reply_matches shape reply ->
    evt rsegs POST (LS 0x152d0 xra xt0 xt1 xt2 (Z_to_bv 64 (R + Z.of_nat j)) xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7
                       xs2 xs3 xs4 xs11 xt3 xt4 xt5 xt6 m).
  Proof.
    intros j m xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs11 xt3 xt4 xt5 xt6 HI Hj HV.
    pose proof HI as (MI & ST & FR & MU & WM & HS & HR & HG & HC).
    pose proof (rd_hd m R reply slack j HR Hj) as RD.
    pose proof (byte_range (hd NUL (skipn j reply))) as BR.
    zstep. if_cases T.
    { exfalso. zify_cond T. lia. }
    zstep. zstep.
    apply epi; [exact HI |].
    rewrite <- HV. cbn [reply_matches_items].
    destruct (Nat.lt_ge_cases j (length reply)) as [L|L].
    - pose proof (hd_nz reply j HRn L) as NZ.
      rewrite (proj2 (Z.ltb_ge (bv_unsigned (hd NUL (skipn j reply))) 1)) by lia.
      rewrite (hd_skipn_S reply j L). reflexivity.
    - rewrite (hd_skipn_end reply j L), (skipn_all2 reply L). reflexivity.
  Qed.

  Lemma SPv : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -112)) = bv_unsigned sp + -112.
  Proof. apply unsigned_lit. lia. Qed.

  Lemma main_loop : forall n k j f m xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs4 xs11 xt3 xt4 xt5 xt6,
    (length shape - k < n)%nat -> (k <= length shape)%nat -> (j <= length reply)%nat ->
    (length shape - k <= f)%nat ->
    reply_matches_items (items_f f (skipn k shape)) (skipn j reply) = reply_matches shape reply ->
    INV m ->
    evt rsegs POST (LS 0x151c8 xra xt0 xt1 xt2 (Z_to_bv 64 (R + Z.of_nat j)) xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7
                       xs2 (Z_to_bv 64 (P + Z.of_nat k)) xs4 xs11 xt3 xt4 xt5 xt6 m).
  Proof.
    induction n as [|n IH]; intros k j f m xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs4 xs11 xt3 xt4 xt5 xt6
      HN HK HJ HF HV HI; [lia|].
    pose proof HI as (MI & ST & (jk & FR) & MU & WM & HS & HR & HG & HC).
    zstep. zstep.
    eapply evt_cut; [eapply skip_loop with (n := S (length shape - k)); [lia | exact HK | exact HS] |].
    intros ms' (k' & Hk' & Hsk & Hb & ->).
    pose proof (byte_range (hd NUL (skipn k' shape))) as BR.
    zstep. if_cases C.
    { zify_cond C.
      pose proof (hd_z_end shape k' HSn ltac:(lia) C) as EK.
      apply ret_end; [exact HI | exact HJ |].
      rewrite <- HV, (items_f_nil f (skipn k shape)); [reflexivity|].
      rewrite <- Hsk, EK. apply skipn_all. }
    zify_cond C.
    pose proof (hd_nz_lt shape k' ltac:(lia)) as LT.
    destruct f as [|f']; [lia|].
    assert (L1 : (1 <= ilen 0 (skipn k' shape))%nat).
    { rewrite (hd_skipn_S shape k' LT), ilen_cons.
      replace ((0 =? 0) && (bz (hd NUL (skipn k' shape)) =? 32)) with false
        by (rewrite (proj2 (Z.eqb_neq _ 32) Hb); reflexivity).
      cbv beta iota. lia. }
    assert (LS1 : (ilen 0 (skipn k' shape) <= length shape - k')%nat)
      by (pose proof (ilen_le 0 (skipn k' shape)) as H; rewrite length_skipn in H; exact H).
    assert (NE : skipn k' shape <> []) by (rewrite (hd_skipn_S shape k' LT); discriminate).
    assert (HI1 : items_f (S f') (skipn k shape) =
                  firstn (ilen 0 (skipn k' shape)) (skipn k' shape)
                    :: items_f f' (skipn (k' + ilen 0 (skipn k' shape)) shape)).
    { rewrite (items_f_cons f' (skipn k shape) (skipn k' shape) (eq_sym Hsk) NE).
      rewrite item_scan_fst, item_scan_snd, <- skipn_add. reflexivity. }
    zstep. zstep.
    eapply evt_cut; [eapply scan_loop with (n := S (length shape - k')) (q := k') (d := 0);
                     [lia | lia | lia | lia | exact HS] |].
    intros ms' (ya0 & ya1 & ya2 & ->).
    remember (ilen 0 (skipn k' shape)) as L eqn:EL.
    pose proof (lit_at m 66380 [Z_to_bv 8 32; NUL] MI ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(cbn; lia)) as HSP.
    assert (HR0 : bytes_at rsegs m (R + Z.of_nat j) (skipn j reply ++ NUL :: slack)).
    { pose proof (bytes_at_skipn m R (reply ++ NUL :: slack) j HR ltac:(rewrite length_app; lia)) as H.
      rewrite skipn_app in H. replace (j - length reply)%nat with 0%nat in H by lia. exact H. }
    zstep. zstep. zstep.
    eapply evt_cut.
    { eapply SCS with (str := skipn j reply) (slack := slack) (set := [Z_to_bv 8 32]) (lo := lo) (can := can).
      - rewrite (unsigned_lit (R + Z.of_nat j)) by lia. exact HR0.
      - apply notin_skipn. exact HRn.
      - intros _. rewrite (unsigned_lit (R + Z.of_nat j)) by lia. rewrite length_skipn.
        replace (R + Z.of_nat j + Z.of_nat (length reply - j) + 1) with (R + Z.of_nat (length reply) + 1) by lia.
        exact SL.
      - rewrite (unsigned_lit 66380) by lia. exact HSP.
      - apply notin_nul_lit. vm_compute. reflexivity.
      - exact HG.
      - exact HC.
      - rewrite SPv. exact ST.
      - rewrite SPv. lia.
      - rewrite (unsigned_lit (R + Z.of_nat j)) by lia. rewrite SPv, length_skipn. lia.
      - rewrite (unsigned_lit 66380) by lia. left. cbn. lia.
      - unfold CSPN_SSP_GOT. lia.
      - unfold CSPN_SSP_GUARD. lia.
      - exact MI. }
    intros ms' (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m1 &
                E & MU1 & WM1 & MI1 & ST1).
    subst ms'. rewrite SPv in MU1, ST1.
    clear HSP HR0.
    after_call MU1 WM1.
    try clear MI. clear MU1 WM1.
    fix_ret.
    rewrite cspn_word.
    remember (word_len (skipn j reply)) as w eqn:EW.
    assert (WLE : (w <= length reply - j)%nat) by (rewrite EW, <- length_skipn; apply word_len_le).
    zstep. if_cases CW.
    { zify_cond CW.
      apply epi; [mk_inv |].
      rewrite <- HV, HI1, rmi_w0 by (rewrite <- EW; lia). cbv beta iota. lia. }
    zify_cond CW.
    zstep. zstep.
    replace (P + Z.of_nat (k' + L) - (P + Z.of_nat k')) with (Z.of_nat L) by lia.
    zstep. if_cases CE.
    { exfalso. zify_cond CE. lia. }
    zify_cond CE.
    zstep. zstep.
    assert (NA1 : bv_unsigned (Z_to_bv 64 (Z.lxor (P + Z.of_nat k') 18446744073709551615)) = 2^64 - 1 - (P + Z.of_nat k'))
      by (rewrite zb_lxor_ones by lia; rewrite unsigned_lit by lia; lia).
    pose proof (proj1 (proj1 (bytes_at_app rsegs m1 P shape [NUL]) HS)) as HS0.
    pose proof (bytes_at_sub m1 P shape k' L HS0 ltac:(lia)) as HIT.
    pose proof (proj1 (proj1 (bytes_at_app rsegs m1 R reply (NUL :: slack)) HR)) as HR1.
    pose proof (bytes_at_skipn m1 R reply j HR1 HJ) as HRJ.
    assert (LIT : length (firstn L (skipn k' shape)) = L) by (rewrite length_firstn, length_skipn; lia).
    assert (JOIN : forall mj yra yt0 yt1 yt2 yb0 yb1 yb2 yb3 yb4 yb5 yb6 yb7 yt3 yt4 yt5 yt6,
      INV mj ->
      negb (has_lt (firstn L (skipn k' shape))) && negb (bytes_eqb (firstn L (skipn k' shape)) (firstn w (skipn j reply)))
        = false ->
      evt rsegs POST (LS 0x15298 yra yt0 yt1 yt2 (Z_to_bv 64 (R + Z.of_nat j)) yb0 yb1 yb2 yb3 yb4 yb5 yb6 yb7
                         (Z_to_bv 64 (P + Z.of_nat k')) (Z_to_bv 64 (P + Z.of_nat (k' + L))) (Z_to_bv 64 (Z.of_nat w))
                         (Z_to_bv 64 (P + Z.of_nat k')) yt3 yt4 yt5 yt6 mj)).
    { intros mj yra yt0 yt1 yt2 yb0 yb1 yb2 yb3 yb4 yb5 yb6 yb7 yt3 yt4 yt5 yt6 HIj Hcond.
      assert (HV1 : match skipn (j + w) reply with
                    | [] => reply_matches_items (items_f f' (skipn (k' + L) shape)) []
                    | _ :: [] => false
                    | _ :: r'' => reply_matches_items (items_f f' (skipn (k' + L) shape)) r''
                    end = reply_matches shape reply).
      { rewrite <- HV, HI1, rmi_ok; rewrite <- EW; [rewrite (skipn_add reply j w); reflexivity | lia | exact Hcond]. }
      pose proof HIj as (MIj & STj & FRj & MUj & WMj & HSj & HRj & HGj & HCj).
      pose proof (rd_hd mj R reply slack (j + w) HRj ltac:(lia)) as RD.
      pose proof (byte_range (hd NUL (skipn (j + w) reply))) as BR1.
      zstep.
      zstep. if_cases T1.
      { exfalso. zify_cond T1. lia. }
      zstep. if_cases T2.
      { exfalso. zify_cond T2. lia. }
      zstep. if_cases T3.
      { exfalso. zify_cond T3. lia. }
      zstep. zstep. zstep. if_cases Cj1.
      - zify_cond Cj1.
        pose proof (hd_z_end reply (j + w) HRn ltac:(lia) Cj1) as EJ.
        assert (E0 : skipn (j + w) reply = []) by (rewrite EJ; apply skipn_all).
        rewrite E0 in HV1.
        replace (R + Z.of_nat j + Z.of_nat w) with (R + Z.of_nat (j + w)) by lia.
        apply (IH (k' + L)%nat (j + w)%nat f'); [lia | lia | lia | lia | | exact HIj].
        rewrite E0. exact HV1.
      - zify_cond Cj1.
        pose proof (hd_nz_lt reply (j + w) Cj1) as LTJ.
        destruct (word_len_skip (skipn j reply)) as [E0 | (b & t & E0 & Eb)];
          rewrite <- EW, <- (skipn_add reply j w) in E0.
        + exfalso. rewrite (hd_skipn_S reply (j + w) LTJ) in E0. discriminate.
        + assert (HB32 : bv_unsigned (hd NUL (skipn (j + w) reply)) = 32) by (rewrite E0; exact Eb).
          assert (ET : t = skipn (S (j + w)) reply).
          { pose proof E0 as E1. rewrite (hd_skipn_S reply (j + w) LTJ) in E1. injection E1 as _ E1.
            symmetry. exact E1. }
          rewrite E0, ET in HV1.
          zstep. zstep. if_cases Cj2.
          * exfalso. zify_cond Cj2. lia.
          * zify_cond Cj2.
            zstep. if_cases T4.
            { exfalso. zify_cond T4. lia. }
            pose proof (rd_hd mj R reply slack (S (j + w)) HRj ltac:(lia)) as RD2.
            pose proof (byte_range (hd NUL (skipn (S (j + w)) reply))) as BR2.
            zstep. zstep. zstep. if_cases Cj3.
            -- zify_cond Cj3.
               pose proof (hd_nz_lt reply (S (j + w)) Cj3) as LTJ2.
               replace (R + Z.of_nat j + Z.of_nat w + 1) with (R + Z.of_nat (S (j + w))) by lia.
               apply (IH (k' + L)%nat (S (j + w)) f'); [lia | lia | lia | lia | | exact HIj].
               rewrite <- HV1. rewrite (hd_skipn_S reply (S (j + w)) LTJ2). reflexivity.
            -- zify_cond Cj3.
               pose proof (hd_z_end reply (S (j + w)) HRn ltac:(lia) Cj3) as EJ2.
               zstep.
               apply epi; [exact HIj |].
               rewrite <- HV1, EJ2, skipn_all. reflexivity. }
    eapply evt_cut.
    { eapply lt_loop with (n := S L) (q := 0%nat) (it := firstn L (skipn k' shape)) (B := P + Z.of_nat k') (len := L);
        [lia | lia | exact LIT | lia | lia | lia | exact NA1 | exact HIT]. }
    intros ms' (yb0 & yb3 & [[HLT ->] | [HLT ->]]); change (has_lt (skipn 0 ?x)) with (has_lt x) in HLT.
    { apply JOIN; [mk_inv | rewrite HLT; reflexivity]. }
    zstep. zstep. if_cases Cf4.
    { zify_cond Cf4.
      assert (LW : L <> w) by mlia.
      zstep. zstep.
      apply epi; [mk_inv |].
      rewrite <- HV, HI1, rmi_mis; [reflexivity|].
      rewrite <- EW, HLT, bytes_eqb_len; [reflexivity|].
      rewrite LIT, length_firstn, length_skipn. lia. }
    zify_cond Cf4.
    assert (LW : L = w) by mlia.
    zstep. zstep. zstep.
    destruct (memcmp_eq L (firstn L (skipn k' shape)) (skipn j reply) ltac:(lia) ltac:(rewrite length_skipn; lia))
      as (v & Hv & Hv0).
    pose proof (memcmp_range _ _ _ _ Hv) as VR.
    eapply evt_cut.
    { eapply BC with (ls := firstn L (skipn k' shape)) (rs := skipn j reply) (v := v).
      - rewrite (unsigned_lit (P + Z.of_nat k')) by lia. exact HIT.
      - rewrite (unsigned_lit (R + Z.of_nat j)) by lia. exact HRJ.
      - rewrite (unsigned_lit (Z.of_nat L)) by lia. rewrite Nat2Z.id. exact Hv.
      - exact MI1. }
    intros ms' (u0 & u1 & u2 & u3 & u4 & u5 & u6 & u7 & u8 & u9 & u10 & u11 & u12 & u13 & m2 &
                E & MU2 & WM2 & MI2 & HB1 & HB2).
    subst ms'. clear HB1 HB2 HIT HRJ HS0 HR1.
    after_call MU2 WM2.
    try clear MI1. clear MU2 WM2.
    fix_ret.
    zstep. if_cases Cb5.
    { zify_cond Cb5.
      assert (VN : v <> 0) by mlia.
      zstep. zstep.
      apply epi; [mk_inv |].
      rewrite <- HV, HI1, rmi_mis; [reflexivity|].
      rewrite <- EW, HLT.
      replace (bytes_eqb (firstn L (skipn k' shape)) (firstn w (skipn j reply))) with false; [reflexivity|].
      symmetry. destruct (bytes_eqb _ _) eqn:EB; [|reflexivity].
      exfalso. apply VN. apply Hv0. apply bytes_eqb_iff in EB. rewrite <- LW in EB.
      rewrite (firstn_len_id (firstn L (skipn k' shape)) L LIT). exact EB. }
    zify_cond Cb5.
    assert (V0 : v = 0) by mlia.
    apply JOIN; [mk_inv |].
    assert (EQ : firstn L (skipn k' shape) = firstn w (skipn j reply)).
    { rewrite <- LW. transitivity (firstn L (firstn L (skipn k' shape))).
      - symmetry. apply firstn_len_id. exact LIT.
      - apply Hv0. exact V0. }
    rewrite (proj2 (bytes_eqb_iff _ _) EQ). destruct (negb _); reflexivity.
  Qed.

  Lemma entry : forall t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6,
    mem_inv rsegs m0 -> stk rsegs m0 lo (bv_unsigned sp) ->
    bytes_at rsegs m0 P (shape ++ [NUL]) -> bytes_at rsegs m0 R (reply ++ NUL :: slack) ->
    bytes_at rsegs m0 142656 (le8 (Z_to_bv 64 345904)) -> bytes_at rsegs m0 345904 (le8 can) ->
    evt rsegs POST (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 P) (Z_to_bv 64 R) a2 a3 a4 a5 a6 a7
                            s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                       F (Z_to_bv 64 0x15164) fc None m0 (seg_rom rsegs)).
  Proof.
    intros t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 MI ST HS HR HG HC.
    pose proof (munch_refl [(lo, bv_unsigned sp)] m0) as MU.
    pose proof (wmono_refl rsegs m0) as WM.
    carve_frame 112%nat ST.
    do 14 zstep.
    zstep. if_cases T.
    { exfalso. zify_cond T. lia. }
    do 10 zstep.
    replace (Z_to_bv 64 R) with (Z_to_bv 64 (R + Z.of_nat 0)) by (f_equal; lia).
    replace (Z_to_bv 64 P) with (Z_to_bv 64 (P + Z.of_nat 0)) by (f_equal; lia).
    eapply (main_loop (S (length shape)) 0 0 (length shape)); [lia | lia | lia | lia | reflexivity | mk_inv].
  Qed.

End SRM.

Theorem syntax_reply_matches_holds : strcspn_contract -> bcmp_contract -> syntax_reply_matches_contract.
Proof.
  intros SCS BC. unfold syntax_reply_matches_contract, SYNTAX_REPLY_MATCHES, SYNTAX_REPLY_MATCHES_K.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo
    shape reply slack can MI ST LO IE A0NZ [HS HSn] HSd A1NZ HR HRn SL HRd HG HC LSH.
  unfold outside_stack, disjoint_from in HSd, HRd. destruct HSd as [HSd _]. destruct HRd as [HRd _].
  unfold IMG_END, GOT_GUARD, GUARD in *.
  pose proof (bv_unsigned_in_range 64 sp) as Rsp. unfold bv_modulus in Rsp.
  pose proof HS as (HS0 & HS1 & _). pose proof HR as (HR0 & HR1 & _).
  rewrite length_app in HS1, HR1. cbn [length] in HS1, HR1.
  replace a0 with (Z_to_bv 64 (bv_unsigned a0)) by apply Z_to_bv_bv_unsigned.
  replace a1 with (Z_to_bv 64 (bv_unsigned a1)) by apply Z_to_bv_bv_unsigned.
  eapply entry with (P := bv_unsigned a0) (R := bv_unsigned a1) (shape := shape) (reply := reply) (slack := slack)
    (lo := lo) (can := can) (m0 := m).
  all: first [ eassumption | lia ].
Qed.
