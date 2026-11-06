(** The walk segment of reac_headamp_prop_parse_result (plain image): [S_WALK] of Prog/Seg/ParseCut.v, the head of
    SPA_POD_STRUCT_FOREACH at 0x14a28 .. 0x14ab0, from the statements of the cuts it reaches ([S_EXIT] at 0x149a0,
    [S_KEY] at 0x14ab4) and strncmp_contract (Prog/strncmp_c.v). An induction on the walk's fuel (fuzz_role's
    walk_loop, Prog/reac_role_prop_parse.v, is the template): each pass is one unfolding of ParseCut.v's walk_pairs
    (walk_pairs_step). The pass on the child at offset cc of the pod:
      - 0x14a28-0x14a4c: the guards of spa_pod_is_inside (iter.h:31-37), the Struct's size re-read from the pod at
        s9 = P + r + 8 each pass; a failed guard ends the walk at [S_EXIT] (walk_pairs is [] there);
      - 0x14a54-0x14a78, the key slot open (s6 = 0): spa_pod_get_string (body.h:224-237); a String child fills the
        slot with s6 = P + cc + 8, any other child leaves it open (0x14a90);
      - 0x14a7c-0x14a8c, a key pending (s6 = P + kk): strncmp(key, "reac.headamp.", 13) (0x1d80c); 0 goes to
        [S_KEY] (the key has the prefix: ha_fold_cons, fold_after), else the pair is skipped (0x14a90);
      - 0x14a94-0x14aac: the advance cc' = cc + SPA_ROUND_UP_N(8 + size, 8) (iter.h:41), the alignment test
        (always 0: P mod 16 = 0, cc' mod 8 = 0), then the next pass. The advance with s6 = 0 is [K_ADV], the
        continuation [S_KEY] takes. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Sem.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame FP Tac.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib Require Import Img0.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Pod Require Import Cursor Model Accessors Spa SpaBool Headamp.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Spec Require Import HeadBytes.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Spec Require StrFun.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Prog Require Import reac_headamp_prop_parse_result_c ParseSites.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Prog Require Import strncmp_c.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Prog.Seg Require Import ParseCut.
Import ListNotations.
Open Scope Z_scope.

(** * The key test: strncmp(key, "reac.headamp.", 13) on a C string key *)
Lemma pw_nul_u : bv_unsigned NUL = 0.
Proof. reflexivity. Qed.

Lemma pw_ne_nul : forall b : byte, b <> NUL -> bv_unsigned b <> 0.
Proof. intros b H E. apply H. apply bv_eq. rewrite E. reflexivity. Qed.

(** strncmp_walk on two NUL-terminated strings without inner NUL, r of k + 1 bytes: some byte difference, 0 exactly
    when the first k + 1 bytes of l are r. *)
Lemma pw_cmp_walk : forall l r k, ~ In NUL l -> ~ In NUL r -> length r = S k ->
  exists v, StrFun.strncmp_walk (l ++ [NUL]) (r ++ [NUL]) k = Some v /\ -256 < v < 256 /\
            (v = 0 <-> bytes_eqb (firstn (S k) l) r = true).
Proof.
  induction l as [|a l IH]; intros r k Hl Hr Lr; (destruct r as [|b r]; [discriminate Lr|]).
  - assert (Hb : bv_unsigned b <> 0) by (apply pw_ne_nul; intros E; apply Hr; left; exact E).
    pose proof (byte_range b) as Rb.
    exists (0 - bv_unsigned b). cbn [app StrFun.strncmp_walk]. rewrite pw_nul_u. cbn [Z.eqb orb].
    split; [reflexivity|]. split; [lia|]. cbn [firstn bytes_eqb]. split; [lia | intros E; discriminate E].
  - assert (Ha : bv_unsigned a <> 0) by (apply pw_ne_nul; intros E; apply Hl; left; exact E).
    assert (Hb : bv_unsigned b <> 0) by (apply pw_ne_nul; intros E; apply Hr; left; exact E).
    assert (Hl' : ~ In NUL l) by (intros H; apply Hl; right; exact H).
    assert (Hr' : ~ In NUL r) by (intros H; apply Hr; right; exact H).
    pose proof (byte_range a) as Ra. pose proof (byte_range b) as Rb.
    cbn [app StrFun.strncmp_walk].
    rewrite (proj2 (Z.eqb_neq _ _) Ha), (proj2 (Z.eqb_neq _ _) Hb). cbn [orb].
    destruct (Z.eqb_spec (bv_unsigned a) (bv_unsigned b)) as [E|E].
    + destruct k as [|k].
      * cbn [Nat.eqb orb negb]. exists (bv_unsigned a - bv_unsigned b). split; [reflexivity|]. split; [lia|].
        destruct r as [|b' r]; [|cbn [length] in Lr; discriminate Lr].
        cbn [firstn bytes_eqb]. rewrite E, Z.eqb_refl. cbn [andb]. split; intros _; [reflexivity | lia].
      * cbn [Nat.eqb orb negb].
        destruct (IH r k Hl' Hr' ltac:(cbn [length] in Lr; lia)) as (v & Ev & Rv & Iv).
        exists v. split; [exact Ev|]. split; [exact Rv|].
        cbn [firstn bytes_eqb]. rewrite E, Z.eqb_refl. cbn [andb]. exact Iv.
    + cbn [negb]. rewrite Bool.orb_true_r.
      exists (bv_unsigned a - bv_unsigned b). split; [reflexivity|]. split; [lia|].
      cbn [firstn bytes_eqb]. rewrite (proj2 (Z.eqb_neq _ _) E). cbn [andb].
      split; [lia | intros F; discriminate F].
Qed.

Lemma pw_no_nul : forall l, forallb (fun b => negb (bv_unsigned b =? 0)) l = true -> ~ In NUL l.
Proof.
  induction l as [|x l IH]; cbn [forallb In]; [tauto|]. intros H [E|E].
  - subst x. rewrite pw_nul_u in H. cbn [Z.eqb negb andb] in H. discriminate H.
  - apply andb_prop in H as [_ H]. exact (IH H E).
Qed.

Lemma pw_prefix_nonul : ~ In NUL HA_PREFIX.
Proof. apply pw_no_nul. vm_compute. reflexivity. Qed.

Lemma pw_prefix_len : length HA_PREFIX = 13%nat.
Proof. vm_compute. reflexivity. Qed.

(** The value of strncmp(key, "reac.headamp.", 13) (0x14a88) on the C string k: 0 exactly when k has the prefix. *)
Lemma pw_strncmp_prefix : forall k, ~ In NUL k ->
  exists v, StrFun.strncmp_model (k ++ [NUL]) (HA_PREFIX ++ [NUL]) 13 = Some v /\ -256 < v < 256 /\
            (v = 0 <-> ha_prefix k = true).
Proof.
  intros k Hk. unfold ha_prefix. rewrite pw_prefix_len.
  change (StrFun.strncmp_model (k ++ [NUL]) (HA_PREFIX ++ [NUL]) 13) with
    (StrFun.strncmp_walk (k ++ [NUL]) (HA_PREFIX ++ [NUL]) 12).
  exact (pw_cmp_walk k HA_PREFIX 12 Hk pw_prefix_nonul pw_prefix_len).
Qed.

(** * The pod's words and bytes *)
Lemma pw_le_rt : forall l : list byte, Z_to_le_bytes (length l) (bytes_le_to_Z l) = l.
Proof.
  induction l as [|b l IH]; [reflexivity|]. cbn [length Z_to_le_bytes bytes_le_to_Z].
  pose proof (byte_range b) as Hb. pose proof (le_bytes_nonneg l) as Hl.
  rewrite lor_low_shiftl by lia. f_equal.
  - apply bv_eq. rewrite Z_to_bv_unsigned. change (bv_wrap 8 ?z) with (z mod 2^8). change (2^8) with 256.
    rewrite Z.mod_add by lia. apply Z.mod_small. lia.
  - rewrite Z.shiftr_div_pow2 by lia. change (2^8) with 256. rewrite Z.div_add by lia.
    rewrite Z.div_small, Z.add_0_l by lia. exact IH.
Qed.

Lemma pw_u32 : forall bs o, 0 <= u32_at bs o < 2^32.
Proof. intros bs o. unfold u32_at. apply rd32_range. Qed.

Lemma pw_rd4 : forall bs o, 0 <= o -> (Z.to_nat o + 4 <= length bs)%nat ->
  firstn 4 (skipn (Z.to_nat o) bs) = le4 (Z_to_bv 64 (u32_at bs o)).
Proof.
  intros bs o H0 H1. unfold le4, u32_at, rd32.
  pose proof (rd32_range (skipn (Z.to_nat o) bs)) as R. unfold rd32 in R.
  rewrite unsigned_lit by lia.
  assert (L : length (firstn 4 (skipn (Z.to_nat o) bs)) = 4%nat) by (rewrite length_firstn, length_skipn; lia).
  pose proof (pw_le_rt (firstn 4 (skipn (Z.to_nat o) bs))) as E. rewrite L in E. symmetry. exact E.
Qed.

Lemma pw_rd1 : forall (l : list byte) i, (i < length l)%nat -> firstn 1 (skipn i l) = [nth i l NUL].
Proof.
  induction l as [|x l IH]; intros i H; [cbn in H; lia|].
  destruct i as [|i]; [reflexivity|]. cbn [skipn nth length] in *. apply IH. lia.
Qed.

Lemma pw_ld4 : forall m P bs o, bytes_at rsegs m P bs -> 0 <= o -> o + 4 <= Z.of_nat (length bs) ->
  ov_read_bytes rsegs m (wa (P + o)) 4 = Some (le4 (Z_to_bv 64 (u32_at bs o))).
Proof.
  intros m P bs o B H0 H1. rewrite (bytes_at_read rsegs m P bs o 4 B H0 ltac:(lia)).
  rewrite pw_rd4 by lia. reflexivity.
Qed.

Lemma pw_ld1 : forall m P bs o, bytes_at rsegs m P bs -> 0 <= o -> o + 1 <= Z.of_nat (length bs) ->
  ov_read_bytes rsegs m (wa (P + o)) 1 = Some [nth (Z.to_nat o) bs NUL].
Proof.
  intros m P bs o B H0 H1. rewrite (bytes_at_read rsegs m P bs o 1 B H0 ltac:(lia)).
  rewrite pw_rd1 by lia. reflexivity.
Qed.

Lemma pw_sub : forall m P bs o n, bytes_at rsegs m P bs -> 0 <= o -> (Z.to_nat o + n <= length bs)%nat ->
  bytes_at rsegs m (P + o) (firstn n (skipn (Z.to_nat o) bs)).
Proof.
  intros m P bs o n B H0 H1.
  rewrite <- (firstn_skipn (Z.to_nat o) bs) in B. apply bytes_at_app in B as [_ B].
  rewrite length_firstn, Nat.min_l in B by lia. rewrite Z2Nat.id in B by lia.
  rewrite <- (firstn_skipn n (skipn (Z.to_nat o) bs)) in B. apply bytes_at_app in B as [B _]. exact B.
Qed.

Lemma pw_nth_firstn : forall (l : list byte) n i, (i < n)%nat -> nth i (firstn n l) NUL = nth i l NUL.
Proof.
  induction l as [|x l IH]; intros n i H.
  - rewrite firstn_nil. reflexivity.
  - destruct n as [|n]; [lia|]. destruct i as [|i]; [reflexivity|]. cbn [firstn nth]. apply IH. lia.
Qed.

Lemma pw_nth_skipn : forall (l : list byte) a i, nth i (skipn a l) NUL = nth (a + i) l NUL.
Proof.
  induction l as [|x l IH]; intros a i.
  - rewrite skipn_nil. destruct i as [|i]; destruct (a + _)%nat; reflexivity.
  - destruct a as [|a]; [reflexivity|]. cbn [skipn Nat.add nth]. apply IH.
Qed.

Lemma pw_nul_idx_le : forall (l : list byte) i, (i < length l)%nat -> bv_unsigned (nth i l NUL) = 0 ->
  (nul_idx l <= i)%nat.
Proof.
  induction l as [|x l IH]; intros i Hi H; cbn [length] in Hi; [lia|]. cbn [nul_idx].
  destruct (bv_unsigned x =? 0) eqn:E; [lia|].
  destruct i as [|i]; [cbn [nth] in H; apply Z.eqb_neq in E; contradiction|].
  cbn [nth] in H. specialize (IH i ltac:(lia) H). lia.
Qed.

Lemma pw_nul_idx_bound : forall l : list byte, (nul_idx l <= length l)%nat.
Proof.
  induction l as [|x l IH]; cbn [nul_idx length]; [lia|]. destruct (bv_unsigned x =? 0); lia.
Qed.

Lemma pw_cstr_nul : forall l, (nul_idx l < length l)%nat -> firstn (S (nul_idx l)) l = cstr l ++ [NUL].
Proof.
  induction l as [|x l IH]; intros H; [cbn in H; lia|]. unfold cstr in *. cbn [nul_idx length] in *.
  destruct (bv_unsigned x =? 0) eqn:E.
  - cbn [firstn app]. f_equal. apply bv_eq. apply Z.eqb_eq in E. rewrite E. reflexivity.
  - cbn [firstn app]. f_equal. apply IH. lia.
Qed.

Lemma pw_cstr_nonul : forall l, ~ In NUL (cstr l).
Proof.
  induction l as [|x l IH]; unfold cstr in *; cbn [nul_idx]; [cbn; tauto|].
  destruct (bv_unsigned x =? 0) eqn:E; cbn [firstn In]; [tauto|]. intros [Hx|Hx].
  - subst x. rewrite pw_nul_u in E. cbn [Z.eqb] in E. discriminate E.
  - exact (IH Hx).
Qed.

(** spa_pod_get_string (body.h:224-237) of the child at cc, as the walk tests it. *)
Lemma pw_gs : forall bs cc, 0 <= cc ->
  spa_get_string (child_at bs cc) =
  if (u32_at bs cc <? 2^20) && (u32_at bs (cc + 4) =? 8) && (1 <=? u32_at bs cc) &&
     (bv_unsigned (nth (Z.to_nat (cc + 8 + u32_at bs cc - 1)) bs NUL) =? 0)
  then Some (cstr (firstn (Z.to_nat (u32_at bs cc)) (skipn (Z.to_nat (cc + 8)) bs))) else None.
Proof.
  intros bs cc H0. unfold spa_get_string, child_at, last_body_byte, SPA_POD_MAX_SIZE, POD_STRING.
  cbn [e_size e_type e_body].
  destruct (u32_at bs cc <? 2^20), (u32_at bs (cc + 4) =? 8); cbn [andb]; try reflexivity.
  destruct (1 <=? u32_at bs cc) eqn:E1; cbn [andb]; [|reflexivity].
  apply Z.leb_le in E1.
  rewrite pw_nth_firstn by lia. rewrite pw_nth_skipn.
  replace (Z.to_nat (cc + 8) + Z.to_nat (u32_at bs cc - 1))%nat with (Z.to_nat (cc + 8 + u32_at bs cc - 1)) by lia.
  reflexivity.
Qed.

(** The key spa_pod_get_string gives is a C string at cc + 8 of the pod, its NUL inside the pod. *)
Lemma pw_key_ok : forall c cc, 0 <= cc -> cc + 8 + u32_at (c_bs c) cc <= Z.of_nat (length (c_bs c)) ->
  1 <= u32_at (c_bs c) cc ->
  bv_unsigned (nth (Z.to_nat (cc + 8 + u32_at (c_bs c) cc - 1)) (c_bs c) NUL) = 0 ->
  key_ok c (Some (cc + 8))
    (Some (cstr (firstn (Z.to_nat (u32_at (c_bs c) cc)) (skipn (Z.to_nat (cc + 8)) (c_bs c))))).
Proof.
  intros c cc H0 H1 H2 H3.
  remember (firstn (Z.to_nat (u32_at (c_bs c) cc)) (skipn (Z.to_nat (cc + 8)) (c_bs c))) as body eqn:EB.
  assert (LB : length body = Z.to_nat (u32_at (c_bs c) cc))
    by (subst body; rewrite length_firstn, length_skipn; lia).
  assert (NB : bv_unsigned (nth (Z.to_nat (u32_at (c_bs c) cc) - 1) body NUL) = 0).
  { subst body. rewrite pw_nth_firstn by lia. rewrite pw_nth_skipn.
    replace (Z.to_nat (cc + 8) + (Z.to_nat (u32_at (c_bs c) cc) - 1))%nat
      with (Z.to_nat (cc + 8 + u32_at (c_bs c) cc - 1)) by lia.
    exact H3. }
  pose proof (pw_nul_idx_le body (Z.to_nat (u32_at (c_bs c) cc) - 1) ltac:(lia) NB) as NI.
  assert (LC : length (cstr body) = nul_idx body).
  { unfold cstr. rewrite length_firstn. pose proof (pw_nul_idx_bound body). lia. }
  cbn [key_ok]. split; [lia|]. split; [rewrite LC; lia|]. split; [apply pw_cstr_nonul|].
  rewrite LC. rewrite <- pw_cstr_nul by lia. subst body.
  rewrite firstn_firstn. rewrite Nat.min_l by lia. reflexivity.
Qed.

(** * The branch tests and register forms *)
Lemma pw_zx32 : forall z, 0 <= z < 2^32 -> zx32 (Z_to_bv 64 z) = Z_to_bv 64 z.
Proof. intros z H. unfold zx32. rewrite unsigned_lit by lia. rewrite Z.mod_small by lia. reflexivity. Qed.

Lemma pw_sx32_eqb : forall z, 0 <= z < 2^32 -> bv_eqb (sx32 (Z_to_bv 64 z)) (Z_to_bv 64 8) = (z =? 8).
Proof.
  intros z H. unfold sx32, bv_eqb. rewrite (unsigned_lit z) by lia. rewrite (unsigned_lit 8) by lia.
  rewrite unsigned_lit_wrap. unfold bv_swrap, bv_wrap.
  change (bv_half_modulus 32) with (2^31). change (bv_modulus 32) with (2^32).
  destruct (Z.eqb_spec z 8) as [->|E]; [reflexivity|]. apply Z.eqb_neq. Z.div_mod_to_equations. lia.
Qed.

Lemma pw_srl20 : forall z, 0 <= z < 2^32 -> bv_eqb (Z_to_bv 64 (Z.shiftr z 20)) (Z_to_bv 64 0) = (z <? 2^20).
Proof.
  intros z H. unfold bv_eqb. rewrite Z.shiftr_div_pow2 by lia.
  assert (D : 0 <= z / 2^20 < 2^64) by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
  rewrite (unsigned_lit (z / 2^20)) by exact D. rewrite (unsigned_lit 0) by lia.
  destruct (Z.ltb_spec z (2^20)) as [L|L].
  - rewrite Z.div_small by lia. reflexivity.
  - apply Z.eqb_neq. assert (1 <= z / 2^20) by (apply Z.div_le_lower_bound; lia). lia.
Qed.

Lemma pw_byte_eqb : forall b : byte, bv_eqb (Z_to_bv 64 (bv_unsigned b)) (Z_to_bv 64 0) = (bv_unsigned b =? 0).
Proof.
  intros b. pose proof (byte_range b). unfold bv_eqb. rewrite (unsigned_lit (bv_unsigned b)) by lia.
  rewrite (unsigned_lit 0) by lia. reflexivity.
Qed.

(** beqz on strncmp's value, a byte difference. *)
Lemma pw_eqb_small : forall v, -256 < v < 256 -> bv_eqb (Z_to_bv 64 v) (Z_to_bv 64 0) = (v =? 0).
Proof.
  intros v Hv. unfold bv_eqb. rewrite !unsigned_lit_wrap. change (0 mod 2^64) with 0.
  destruct (Z.eqb_spec v 0) as [->|E]; [reflexivity|]. apply Z.eqb_neq. Z.div_mod_to_equations. lia.
Qed.

Lemma pw_land3 : forall x, 0 <= x -> x mod 8 = 0 -> Z.land x 3 = 0.
Proof.
  intros x H0 H8. change 3 with (Z.ones 2). rewrite Z.land_ones by lia. change (2^2) with 4.
  Z.div_mod_to_equations. lia.
Qed.

Lemma pw_lor7 : forall z, 0 <= z -> z + 7 <= Z.lor (z + 7) 7 <= z + 14 /\ Z.lor (z + 7) 7 + 1 = round_up8 (8 + z) /\
  (Z.lor (z + 7) 7 + 1) mod 8 = 0.
Proof.
  intros z H. unfold round_up8. replace (8 + z - 1) with (z + 7) by lia. rewrite lor7 by lia.
  split; [Z.div_mod_to_equations; lia|]. split; [reflexivity|].
  replace (8 * ((z + 7) / 8) + 7 + 1) with (((z + 7) / 8 + 1) * 8) by lia. apply Z.mod_mul. lia.
Qed.

(** The guard of the walk (spa_pod_is_inside, iter.h:31-37) on a child offset cc that is 0 mod 8. *)
Lemma pw_inside : forall bs r vs cc, r + 16 <= cc -> cc mod 8 = 0 -> 8 <= vs ->
  pod_is_inside bs (r + 16) vs cc = (cc - (r + 16) <=? vs - 8) && (u32_at bs cc <=? r + 8 + vs - cc).
Proof.
  intros bs r vs cc H1 H2 H3. unfold pod_is_inside, ptr_type_inside, ptrinside, ptr_remaining.
  replace (cc mod 4) with 0 by (Z.div_mod_to_equations; lia).
  rewrite (proj2 (Z.leb_le (r + 16) cc) H1), (proj2 (Z.leb_le 8 vs) H3). cbn [Z.eqb andb].
  replace (r + 16 + vs - (cc + 8)) with (r + 8 + vs - cc) by lia. reflexivity.
Qed.

(** A Struct of fewer than 8 bytes has no child. *)
Lemma pw_inside_small : forall bs body vs cc, vs < 8 -> pod_is_inside bs body vs cc = false.
Proof.
  intros bs body vs cc H. unfold pod_is_inside, ptr_type_inside, ptrinside.
  rewrite (proj2 (Z.leb_gt 8 vs) H). destruct (cc mod 4 =? 0), (body <=? cc); reflexivity.
Qed.

Lemma pw_mod8_add2 : forall a b, a mod 8 = 0 -> b mod 8 = 0 -> (a + b) mod 8 = 0.
Proof. intros a b Ha Hb. rewrite Z.add_mod, Ha, Hb by lia. reflexivity. Qed.

(** A fact kept out of sight of lia. *)
Definition pw_hide (A : Prop) : Prop := A.

(** A branch whose condition the context decides. *)
Ltac pw_cond := unfold bv_eqb, bv_ltu, bv_lts, bv_leu;
  repeat match goal with |- context [bv_unsigned (Z_to_bv 64 ?e)] => rewrite (unsigned_lit e) by lia end;
  solve_cond_rec.
Ltac pw_go := lazymatch goal with
  | |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
      first [ replace c with true; [cbv iota | symmetry; pw_cond]
            | replace c with false; [cbv iota | symmetry; pw_cond] ]
  end.
Ltac pw_ret := lazymatch goal with |- evt _ _ (MS _ _ (ret_pc (Z_to_bv 64 ?n)) _ _ _ _) =>
  replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [lia | reflexivity]) end.

(** * The memory at a cut *)
(** The pod's bytes in any memory of a cut with at most cap cells written. *)
Lemma pw_pod_at : forall c fr cl m, pc_ok c -> Z.of_nat (length cl) <= c_cap c -> PMem c fr cl m ->
  bytes_at rsegs m (c_P c) (c_bs c).
Proof.
  intros c fr cl m (HA & _ & HST & _ & _) Hn (_ & _ & MU & _).
  pose proof HA as (HB & _).
  eapply pod_kept with (n := Z.of_nat (length cl));
    [exact HA | exact HST | split; [lia | exact Hn] | exact MU | lia | lia | exact HB].
Qed.

(** A call that writes nothing (strncmp: munch []) keeps the memory of a cut. *)
Lemma pw_pmem_keep : forall c fr cl m m', PMem c fr cl m -> munch [] m m' -> wmono rsegs m m' ->
  mem_inv rsegs m' -> PMem c fr cl m'.
Proof.
  intros c fr cl m m' (FR & ST & MU & BO & (ev' & EV) & WM & MI) MU' WM' MI'.
  split; [eapply rw_cells_transport; [exact FR | exact MU' | exact WM' | exact I]|].
  split; [eapply stk_transport_disjoint; [exact ST | exact MU' | exact WM' | exact I]|].
  split.
  { eapply munch_trans; [exact MU|]. eapply munch_weaken; [|exact MU']. intros x _. exact I. }
  split; [eapply bytes_at_transport; [exact BO | exact MU' | exact I]|].
  split; [exists ev'; eapply rw_cells_transport; [exact EV | exact MU' | exact WM' | exact I]|].
  split; [eapply wmono_trans; [exact WM | exact WM']|].
  exact MI'.
Qed.

(** The walk's frame as the exit's: the three temporary cells of wframe as one block of 56 bytes. *)
Lemma pw_pmem_cb56 : forall c ja jb cl m, PMem c (wframe c ja jb) cl m ->
  exists ja', PMem c (CB 56 ja' :: saves c) cl m.
Proof.
  intros c ja jb cl m (FR & REST).
  exists (cells_bytes [CB 24 ja; C8 (Z_to_bv 64 LIT_PREFIX); CB 24 jb]). split; [|exact REST].
  pose proof (rw_cells_merge rsegs m (c_spf c) [] [CB 24 ja; C8 (Z_to_bv 64 LIT_PREFIX); CB 24 jb] (saves c)) as M.
  cbn [app] in M. apply M. exact FR.
Qed.

(** * The walk *)
Lemma pw_walk : strncmp_contract -> forall c, pc_ok c -> S_EXIT c -> S_KEY c -> S_WALK c.
Proof.
  intros HSN c HC HEX HKY. unfold S_WALK. intros r n.
  induction n as [|n IH];
    intros cc k km cl keys rf m F fc x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 ja jb
      Hst Hcc Hc8 Hn HK Hcl Hk0 Hk8 Hrf HW HM HF; [lia|].
  pose proof HC as (HA & HSTK & HLO & _ & _).
  pose proof HA as (_ & HP0 & HP16 & _ & _ & HPL & _).
  pose proof HSTK as (_ & Hsp64 & _).
  assert (HTOP : c_P c + Z.of_nat (length (c_bs c)) + 528 <= bv_unsigned (c_sp c) < 2^64).
  { pose proof (bv_unsigned_in_range 64 (c_sp c)) as R. change (bv_modulus 64) with (2^64) in R.
    unfold PARSE_STACK in HLO. lia. }
  clear HA HSTK HLO Hsp64 HPL.
  assert (HP8 : pw_hide (c_P c mod 8 = 0)) by (unfold pw_hide; Z.div_mod_to_equations; lia). clear HP16.
  pose proof Hst as (Hr16 & Hr8 & Hvs20 & Hrvs).
  change (pw_hide (r mod 8 = 0)) in Hr8. change (pw_hide (cc mod 8 = 0)) in Hc8.
  change (pw_hide (Z.to_nat (r + 16 + u32_at (c_bs c) (r + 8) - cc) < S n)%nat) in Hn.
  pose proof (pw_u32 (c_bs c) (r + 8)) as Rvs.
  pose proof (pw_pod_at c _ _ m HC Hcl HM) as HPOD.
  (* the walk's end: walk_pairs is [] *)
  assert (EXIT : pod_is_inside (c_bs c) (r + 16) (u32_at (c_bs c) (r + 8)) cc = false ->
    forall (y1 y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y18 y19 y21 y22 y24 y25 y26 y27 y28 y29 y30 y31 : word),
    evt rsegs (PPost c (RESM c))
      (MS (mkR y1 (Z_to_bv 64 (c_spf c)) (c_gp c) (c_tp c) y5 y6 y7 (Z_to_bv 64 (c_R c))
               (Z_to_bv 64 (Z.of_nat (length cl))) y10 y11 y12 y13 y14 y15 y16 y17 y18 y19 (Z_to_bv 64 rf) y21 y22
               (Z_to_bv 64 keys) y24 y25 y26 y27 y28 y29 y30 y31)
          F (Z_to_bv 64 0x149a0) fc None m (seg_rom rsegs))).
  { intros HIN y1 y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y18 y19 y21 y22 y24 y25 y26 y27 y28 y29 y30 y31.
    rewrite walk_pairs_step, HIN in HW. cbn [ha_fold] in HW.
    destruct (pw_pmem_cb56 c ja jb cl m HM) as [ja' HM'].
    exact (HEX cl keys rf m F fc y1 y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y18 y19 y21 y22 y24 y25 y26 y27 y28
             y29 y30 y31 ja' HW HM' (proj2 HF)). }
  (* 0x14a28: bltu s10,s5 (never) *)
  step. pw_go.
  (* 0x14a2c: lwu a1,0(s9): the Struct's size vs, from the pod *)
  pose proof (pw_ld4 m (c_P c) (c_bs c) (r + 8) HPOD ltac:(lia) ltac:(lia)) as HRD. unfold wa in HRD.
  zstep. clear HRD. rewrite (pw_zx32 _ Rvs).
  (* 0x14a30: bltu a1,s11: vs < 8 ends the walk *)
  zstep.
  destruct (Z.lt_ge_cases (u32_at (c_bs c) (r + 8)) 8) as [V8|V8].
  { pw_go. apply EXIT. apply pw_inside_small. exact V8. }
  pw_go.
  (* 0x14a34-0x14a3c: cc - (r + 16) > vs - 8 ends the walk *)
  zstep. zstep. zstep.
  destruct (Z.le_gt_cases (cc - (r + 16)) (u32_at (c_bs c) (r + 8) - 8)) as [D1|D1].
  2:{ pw_go. apply EXIT. rewrite (pw_inside _ r _ cc ltac:(lia) Hc8 V8). rewrite (proj2 (Z.leb_gt _ _) D1).
      reflexivity. }
  pw_go.
  (* 0x14a40: lwu a0,0(s10): the child's size CS *)
  pose proof (pw_u32 (c_bs c) cc) as RCS.
  pose proof (pw_ld4 m (c_P c) (c_bs c) cc HPOD ltac:(lia) ltac:(lia)) as HRD. unfold wa in HRD.
  zstep. clear HRD. rewrite (pw_zx32 _ RCS).
  (* 0x14a44-0x14a4c: CS > r + 8 + vs - cc ends the walk *)
  zstep. zstep. zstep.
  destruct (Z.le_gt_cases (u32_at (c_bs c) cc) (r + 8 + u32_at (c_bs c) (r + 8) - cc)) as [D2|D2].
  2:{ pw_go. apply EXIT. rewrite (pw_inside _ r _ cc ltac:(lia) Hc8 V8).
      rewrite (proj2 (Z.leb_le _ _) D1), (proj2 (Z.leb_gt _ _) D2). reflexivity. }
  pw_go.
  assert (HIN : pod_is_inside (c_bs c) (r + 16) (u32_at (c_bs c) (r + 8)) cc = true).
  { rewrite (pw_inside _ r _ cc ltac:(lia) Hc8 V8), (proj2 (Z.leb_le _ _) D1), (proj2 (Z.leb_le _ _) D2).
    reflexivity. }
  rewrite walk_pairs_step, HIN in HW. clear EXIT.
  (* 0x14a94-0x14aac: the next child cc' = cc + SPA_ROUND_UP_N(8 + CS, 8), then the next pass *)
  assert (ADV : forall (y1 y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y22 y28 y29 y30 y31 : word) k' km'
                  cl' keys' rf' m' F' fc' ja' jb',
    y22 = key_reg c k' -> key_ok c k' km' ->
    Z.of_nat (length cl') <= c_cap c -> 0 <= keys' -> keys' * 8 <= cc + 8 - (r + 16) -> 0 <= rf' <= 5 ->
    ha_result (ha_fold parse_cell (c_cap c)
      (walk_pairs (c_bs c) r (cc + round_up8 (8 + u32_at (c_bs c) cc)) n km') cl' keys' rf') = RESM c ->
    PMem c (wframe c ja' jb') cl' m' -> fp_ok F' fc' ->
    evt rsegs (PPost c (RESM c))
      (MS (mkR y1 (Z_to_bv 64 (c_spf c)) (c_gp c) (c_tp c) y5 y6 y7 (Z_to_bv 64 (c_R c))
               (Z_to_bv 64 (Z.of_nat (length cl'))) y10 y11 y12 y13 y14 y15 y16 y17
               (Z_to_bv 64 (c_cap c)) (Z_to_bv 64 (c_O c)) (Z_to_bv 64 rf') (Z_to_bv 64 (c_P c + r + 16))
               y22 (Z_to_bv 64 keys') (Z_to_bv 64 LIT_PREFIX) (Z_to_bv 64 (c_P c + r + 8))
               (Z_to_bv 64 (c_P c + cc)) (Z_to_bv 64 8) y28 y29 y30 y31)
          F' (Z_to_bv 64 0x14a94) fc' None m' (seg_rom rsegs))).
  { intros y1 y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y22 y28 y29 y30 y31 k' km' cl' keys' rf' m' F' fc' ja' jb'
      E22 HK' Hcl' Hk0' Hk8' Hrf' HW' HM' HF'.
    subst y22.
    pose proof (pw_pod_at c _ _ m' HC Hcl' HM') as HPOD'.
    pose proof (pw_ld4 m' (c_P c) (c_bs c) cc HPOD' ltac:(lia) ltac:(lia)) as HRD. unfold wa in HRD.
    zstep. clear HRD. rewrite (pw_zx32 _ RCS).
    (* 0x14a98-0x14aa4: addi 7, ori 7, add, addi 1: s10 = P + cc + round_up8 (8 + CS) *)
    destruct (pw_lor7 (u32_at (c_bs c) cc) (proj1 RCS)) as (L7 & L7e & L7m).
    zstep. zstep. zstep. zstep.
    replace (c_P c + cc + Z.lor (u32_at (c_bs c) cc + 7) 7 + 1)
      with (c_P c + (cc + round_up8 (8 + u32_at (c_bs c) cc))) by lia.
    assert (M8 : (cc + round_up8 (8 + u32_at (c_bs c) cc)) mod 8 = 0)
      by (apply pw_mod8_add2; [exact Hc8 | rewrite <- L7e; exact L7m]).
    (* 0x14aa8-0x14aac: andi a0,s10,3 is 0 (P mod 16 = 0, cc' mod 8 = 0): the j 0x149a0 at 0x14ab0 never runs *)
    zstep.
    rewrite (pw_land3 (c_P c + (cc + round_up8 (8 + u32_at (c_bs c) cc))))
      by (first [lia | apply pw_mod8_add2; [exact HP8 | exact M8]]).
    zstep.
    pw_go.
    (* 0x14a28: the next pass, fuel n *)
    unfold pw_hide in Hn.
    eapply (IH (cc + round_up8 (8 + u32_at (c_bs c) cc)) k' km' cl' keys' rf' m' F' fc');
      [exact Hst | lia | exact M8 | lia | exact HK' | exact Hcl' | exact Hk0' | lia | exact Hrf' | exact HW'
      | exact HM' | exact HF']. }
  (* 0x14a90: mv s6,zero, the key slot emptied, then the advance *)
  assert (NEXT0 : forall (y1 y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y22 y28 y29 y30 y31 : word)
                    cl' keys' rf' m' F' fc' ja' jb',
    Z.of_nat (length cl') <= c_cap c -> 0 <= keys' -> keys' * 8 <= cc + 8 - (r + 16) -> 0 <= rf' <= 5 ->
    ha_result (ha_fold parse_cell (c_cap c)
      (walk_pairs (c_bs c) r (cc + round_up8 (8 + u32_at (c_bs c) cc)) n None) cl' keys' rf') = RESM c ->
    PMem c (wframe c ja' jb') cl' m' -> fp_ok F' fc' ->
    evt rsegs (PPost c (RESM c))
      (MS (mkR y1 (Z_to_bv 64 (c_spf c)) (c_gp c) (c_tp c) y5 y6 y7 (Z_to_bv 64 (c_R c))
               (Z_to_bv 64 (Z.of_nat (length cl'))) y10 y11 y12 y13 y14 y15 y16 y17
               (Z_to_bv 64 (c_cap c)) (Z_to_bv 64 (c_O c)) (Z_to_bv 64 rf') (Z_to_bv 64 (c_P c + r + 16))
               y22 (Z_to_bv 64 keys') (Z_to_bv 64 LIT_PREFIX) (Z_to_bv 64 (c_P c + r + 8))
               (Z_to_bv 64 (c_P c + cc)) (Z_to_bv 64 8) y28 y29 y30 y31)
          F' (Z_to_bv 64 0x14a90) fc' None m' (seg_rom rsegs))).
  { intros y1 y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y22 y28 y29 y30 y31 cl' keys' rf' m' F' fc' ja' jb'
      Hcl' Hk0' Hk8' Hrf' HW' HM' HF'.
    zstep.
    exact (ADV y1 y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 (Z_to_bv 64 0) y28 y29 y30 y31 None None cl' keys' rf'
             m' F' fc' ja' jb' eq_refl I Hcl' Hk0' Hk8' Hrf' HW' HM' HF'). }
  (* the advance with the key slot empty: the continuation of the key, value and refusal cuts *)
  assert (KADV : K_ADV c r cc (walk_pairs (c_bs c) r (cc + round_up8 (8 + u32_at (c_bs c) cc)) n None)).
  { intros cl' keys' rf' m' F' fc' y1 y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31 ja' jb'
      Hcl' Hk0' Hk8' Hrf' HW' HM' HF'.
    exact (ADV y1 y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 (Z_to_bv 64 0) y28 y29 y30 y31 None None cl' keys' rf'
             m' F' fc' ja' jb' eq_refl I Hcl' Hk0' Hk8' Hrf' HW' HM' HF'). }
  pose proof HM as (_ & _ & _ & _ & _ & _ & MI).
  destruct k as [kk|]; destruct km as [sx|]; cbn [key_ok] in HK; try contradiction; cbn [key_reg].
  - (* a key pending: strncmp(key, "reac.headamp.", 13) at 0x14a7c-0x14a8c *)
    pose proof HK as (Hkk0 & Hkk1 & Hkk2 & Hkk3). cbv iota beta in HW.
    zstep.
    pw_go.
    zstep. zstep. zstep. zstep.
    destruct (pw_strncmp_prefix sx Hkk2) as (v & Ev & Rv & Iv).
    eapply evt_cut.
    { eapply HSN with (ls := sx ++ [NUL]) (rs := HA_PREFIX ++ [NUL]) (v := v).
      - rewrite unsigned_lit by lia. rewrite <- Hkk3. apply pw_sub; [exact HPOD | exact Hkk0 | lia].
      - rewrite unsigned_lit by (unfold LIT_PREFIX; lia). exact (proj1 (lits_at m MI)).
      - rewrite unsigned_lit by lia. exact Ev.
      - exact MI. }
    intros ms' (t0 & t1 & t2 & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3 & t4 & t5 & t6 & m' & E & MU' & WM' & MI'
                & _ & _).
    subst ms'. pw_ret.
    pose proof (pw_pmem_keep c _ _ m m' HM MU' WM' MI') as HM'.
    (* 0x14a8c: beqz a0: strncmp's 0 is the prefix *)
    zstep. rewrite (pw_eqb_small v Rv).
    destruct (Z.eqb_spec v 0) as [V0|V0]; cbv iota.
    + (* 0x14ab4: [S_KEY] *)
      assert (HP : ha_prefix sx = true) by (apply Iv; exact V0).
      rewrite ha_fold_cons, HP in HW.
      eapply (HKY r cc kk sx _ cl keys rf m' F fc);
        [exact KADV | exact Hst | lia | exact Hc8 | unfold child_in; lia | exact Hcl | exact Hk0 | exact Hk8
        | exact Hrf | exact HK | exact HP | exact HW | exact HM' | exact HF].
    + (* 0x14a90: no prefix, the pair is skipped *)
      assert (HP : ha_prefix sx = false)
        by (destruct (ha_prefix sx) eqn:EP; [exfalso; apply V0, Iv; reflexivity | reflexivity]).
      rewrite ha_fold_cons, HP in HW.
      eapply NEXT0; [exact Hcl | exact Hk0 | lia | exact Hrf | exact HW | exact HM' | exact HF].
  - (* the key slot open: spa_pod_get_string at 0x14a54-0x14a78 *)
    cbv iota beta in HW.
    (* 0x14a50: bnez s6 (s6 = 0) *)
    zstep. pw_go.
    (* 0x14a54-0x14a58: size >= 2^20 *)
    zstep. zstep.
    rewrite (pw_srl20 _ RCS).
    pose proof (pw_gs (c_bs c) cc ltac:(lia)) as GSE.
    destruct (Z.lt_ge_cases (u32_at (c_bs c) cc) (2^20)) as [B20|B20].
    2:{ pw_go. eapply NEXT0; [exact Hcl | exact Hk0 | lia | exact Hrf | | exact HM | exact HF].
        rewrite GSE, (proj2 (Z.ltb_ge _ _) B20) in HW. exact HW. }
    pw_go.
    (* 0x14a5c: beqz a0: size 0 *)
    zstep.
    destruct (Z.eq_dec (u32_at (c_bs c) cc) 0) as [B0|B0].
    { pw_go. eapply NEXT0; [exact Hcl | exact Hk0 | lia | exact Hrf | | exact HM | exact HF].
      rewrite GSE, (proj2 (Z.ltb_lt _ _) B20), (proj2 (Z.leb_gt 1 (u32_at (c_bs c) cc)) ltac:(lia)),
        andb_false_r in HW.
      exact HW. }
    pw_go.
    (* 0x14a60-0x14a64: lw a1,4(s10), the type, then bne a1,s11 *)
    pose proof (pw_u32 (c_bs c) (cc + 4)) as RCT.
    pose proof (pw_ld4 m (c_P c) (c_bs c) (cc + 4) HPOD ltac:(lia) ltac:(lia)) as HRD. unfold wa in HRD.
    replace (c_P c + (cc + 4)) with (c_P c + cc + 4) in HRD by lia.
    zstep. clear HRD.
    zstep.
    rewrite (pw_sx32_eqb _ RCT).
    destruct (Z.eq_dec (u32_at (c_bs c) (cc + 4)) 8) as [T8|T8].
    2:{ pw_go. eapply NEXT0; [exact Hcl | exact Hk0 | lia | exact Hrf | | exact HM | exact HF].
        rewrite GSE, (proj2 (Z.ltb_lt _ _) B20), (proj2 (Z.eqb_neq _ _) T8) in HW. exact HW. }
    pw_go.
    (* 0x14a68-0x14a74: s6 = key, the last body byte, bnez *)
    zstep. zstep.
    pose proof (pw_ld1 m (c_P c) (c_bs c) (cc + 8 + u32_at (c_bs c) cc - 1) HPOD ltac:(lia) ltac:(lia)) as HRD.
    unfold wa in HRD.
    replace (c_P c + (cc + 8 + u32_at (c_bs c) cc - 1)) with (c_P c + cc + 8 + u32_at (c_bs c) cc + -1) in HRD
      by lia.
    zstep. clear HRD.
    zstep.
    rewrite pw_byte_eqb.
    destruct (Z.eq_dec (bv_unsigned (nth (Z.to_nat (cc + 8 + u32_at (c_bs c) cc - 1)) (c_bs c) NUL)) 0) as [L0|L0].
    + (* 0x14a78: j 0x14a94 with the key kept *)
      pw_go. zstep.
      eapply (ADV _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (Some (cc + 8))
                (Some (cstr (firstn (Z.to_nat (u32_at (c_bs c) cc)) (skipn (Z.to_nat (cc + 8)) (c_bs c)))))
                cl keys rf m F fc ja jb).
      * cbn [key_reg]. f_equal. lia.
      * apply pw_key_ok; lia.
      * exact Hcl.
      * exact Hk0.
      * lia.
      * exact Hrf.
      * rewrite GSE, (proj2 (Z.ltb_lt _ _) B20), (proj2 (Z.eqb_eq _ _) T8),
          (proj2 (Z.leb_le 1 (u32_at (c_bs c) cc)) ltac:(lia)), (proj2 (Z.eqb_eq _ _) L0) in HW. exact HW.
      * exact HM.
      * exact HF.
    + pw_go. eapply NEXT0; [exact Hcl | exact Hk0 | lia | exact Hrf | | exact HM | exact HF].
      rewrite GSE, (proj2 (Z.ltb_lt _ _) B20), (proj2 (Z.eqb_eq _ _) T8),
        (proj2 (Z.leb_le 1 (u32_at (c_bs c) cc)) ltac:(lia)), (proj2 (Z.eqb_neq _ _) L0) in HW. exact HW.
Qed.
