From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes ZBridge.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.U Require Import Img0.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.U.Prog Require Import ManifestModel ManifestMem LibcNeeds_c plain_c expected_m expected_s.
Import ListNotations.
Open Scope Z_scope.

Definition cmatch (x y : Z) : bool := (x =? y) || (x =? y - 32).

Lemma ci_eqb_nth : forall p l, Forall (fun y => y <> 0 /\ y - 32 <> 0) p ->
  ci_eqb (firstn (length p) l) p = true <-> (forall k, (k < length p)%nat -> cmatch (nth k l 0) (nth k p 0) = true).
Proof.
  induction p as [|y p IH]; intros l Hp; cbn.
  - split; [intros _ k Hk; lia|reflexivity].
  - inversion Hp as [|? ? [Hy1 Hy2] Hp']; subst. destruct l as [|x l]; cbn.
    + split; [discriminate|]. intros H. specialize (H 0%nat ltac:(lia)). cbn in H. unfold cmatch in H.
      apply orb_true_iff in H as [H|H]; apply Z.eqb_eq in H; lia.
    + rewrite andb_true_iff, IH by exact Hp'. split.
      * intros [H1 H2] [|k] Hk; cbn; [exact H1|apply H2; lia].
      * intros H. split; [exact (H 0%nat ltac:(lia))|]. intros k Hk. exact (H (S k) ltac:(lia)).
Qed.

Lemma ci6 : forall t i, ci_eqb (firstn 6 (skipn i t)) prefix_lc = true <->
  (forall k, (k < 6)%nat -> cmatch (byte_at t (i + k)) (nth k prefix_lc 0) = true).
Proof.
  intros t i. change 6%nat with (length prefix_lc) at 1.
  rewrite (ci_eqb_nth prefix_lc (skipn i t)) by (repeat constructor; lia).
  unfold byte_at. setoid_rewrite nth_skipn0. reflexivity.
Qed.

Lemma pl_range : forall k, (k < 6)%nat -> 101 <= nth k prefix_lc 0 <= 120.
Proof. intros k Hk. do 6 (destruct k as [|k]; [cbn; lia|]). lia. Qed.

Lemma cmatch_nz : forall x k, (k < 6)%nat -> cmatch x (nth k prefix_lc 0) = true -> x <> 0.
Proof.
  intros x k Hk H. pose proof (pl_range k Hk). unfold cmatch in H.
  apply orb_true_iff in H as [H|H]; apply Z.eqb_eq in H; lia.
Qed.

Lemma pfb_val : forall k, (k < 6)%nat ->
  bv_unsigned (nth k [Z_to_bv 8 112; Z_to_bv 8 114; Z_to_bv 8 101; Z_to_bv 8 102; Z_to_bv 8 105; Z_to_bv 8 120;
    Z_to_bv 8 0] (Z_to_bv 8 0)) = nth k prefix_lc 0.
Proof. intros k Hk. do 6 (destruct k as [|k]; [reflexivity|]). lia. Qed.

Lemma byte_dec : forall (C G : Z -> bool) z, forallb (fun x => implb (C x) (G x)) (map Z.of_nat (seq 0 256)) = true ->
  C z = true -> 0 <= z < 256 -> G z = true.
Proof.
  intros C G z H Hc Hz. rewrite forallb_forall in H. specialize (H z). rewrite Hc in H. apply H.
  apply in_map_iff. exists (Z.to_nat z). split; [lia|apply in_seq; lia].
Qed.

Lemma bq : forall a b : bool, a = b -> Bool.eqb a b = true.
Proof. intros a b ->. destruct b; reflexivity. Qed.

Lemma band' : forall a b : bool, a = true -> b = true -> (a && b) = true.
Proof. intros a b -> ->. reflexivity. Qed.

Ltac bdec z H :=
  lazymatch type of H with ?c = true =>
    let Cz := eval pattern z in c in
    lazymatch Cz with ?Cf _ =>
      lazymatch goal with |- ?g = true =>
        let Gz := eval pattern z in g in
        lazymatch Gz with ?Gf _ =>
          apply (byte_dec Cf Gf z); [vm_compute; reflexivity | exact H | ]
        end end end end.

Ltac bjoin H1 H2 H := apply bq in H1; apply bq in H2; pose proof (band' _ _ H1 H2) as H; clear H1 H2.

Lemma skipn_cons_nth : forall (t : list Z) p, (p < length t)%nat -> skipn p t = byte_at t p :: skipn (S p) t.
Proof. induction t as [|x t IH]; intros [|p] H; cbn in *; try lia; [reflexivity|]. apply IH. lia. Qed.

Lemma cw_step : forall f t p, (p < length t)%nat ->
  count_while f (skipn p t) = if f (byte_at t p) then S (count_while f (skipn (S p) t)) else O.
Proof. intros f t p H. rewrite (skipn_cons_nth t p H). reflexivity. Qed.

Lemma cw_end : forall f t p, (length t <= p)%nat -> count_while f (skipn p t) = O.
Proof. intros f t p H. rewrite skipn_all2 by lia. reflexivity. Qed.

Lemma ci_len : forall a b, ci_eqb a b = true -> length a = length b.
Proof.
  induction a as [|x a IH]; intros [|y b] H; cbn in *; try discriminate; [reflexivity|].
  apply andb_true_iff in H as [_ H]. rewrite (IH b H). reflexivity.
Qed.

Lemma head_le : forall t i p0, head t i = Some p0 -> (p0 <= length t)%nat.
Proof.
  intros t i p0 H. unfold head in H.
  destruct ((byte_at t i =? 64) && zl_eqb (firstn 6 (skipn (S i) t)) prefix_lc) eqn:E1.
  - injection H as <-. apply andb_true_iff in E1 as [_ E1]. apply zl_eqb_eq in E1.
    apply (f_equal (@length Z)) in E1. rewrite length_firstn, length_skipn in E1.
    change (length prefix_lc) with 6%nat in E1. lia.
  - destruct (ci_eqb (firstn 6 (skipn i t)) prefix_lc) eqn:E2; cbn [andb] in H; [|discriminate].
    apply ci_len in E2. rewrite length_firstn, length_skipn in E2. change (length prefix_lc) with 6%nat in E2.
    destruct i as [|i']; [|destruct (is_space (byte_at t i'))]; try discriminate; injection H as <-; lia.
Qed.

Lemma ncmp6 : forall x : list Z,
  firstn (Z.to_nat (bv_unsigned (Z_to_bv 64 6))) (x ++ [0]) =
  firstn (Z.to_nat (bv_unsigned (Z_to_bv 64 6))) (zbytes (map (Z_to_bv 8) prefix_lc) ++ [0]) <->
  firstn 6 x = prefix_lc.
Proof.
  intros x. change (Z.to_nat (bv_unsigned (Z_to_bv 64 6))) with 6%nat.
  replace (firstn 6 (zbytes (map (Z_to_bv 8) prefix_lc) ++ [0])) with prefix_lc by (vm_compute; reflexivity).
  change 6%nat with (length prefix_lc). apply firstn_noz. unfold prefix_lc. repeat constructor; lia.
Qed.

Lemma ulit : forall e v, e = v -> 0 <= v < 2^64 -> bv_unsigned (Z_to_bv 64 e) = v.
Proof. intros e v -> Hv. apply unsigned_lit. exact Hv. Qed.

Lemma firstn_app_le : forall (a b : list Z) k, (k <= length a)%nat -> firstn k (a ++ b) = firstn k a.
Proof.
  intros a b k Hk. rewrite firstn_app. replace (k - length a)%nat with 0%nat by lia. cbn [firstn].
  apply app_nil_r.
Qed.

Lemma token_at_eq : forall t pre loc j, (j + length pre + 1 + length loc <= length t)%nat ->
  token_at t pre loc j =
    zl_eqb (firstn (length pre) (skipn j t)) pre && (byte_at t (j + length pre) =? 58)
    && zl_eqb (firstn (length loc) (skipn (j + length pre + 1) t)) loc
    && match j with O => true | S j' => negb (name_char (byte_at t j')) && negb (byte_at t j' =? 46) end
    && negb (name_char (byte_at t (j + length pre + 1 + length loc))).
Proof. intros t pre loc j H. unfold token_at. rewrite (proj2 (Nat.leb_le _ _) H). reflexivity. Qed.

Lemma cw_le : forall f l, (count_while f l <= length l)%nat.
Proof. intros f. induction l as [|x l IH]; cbn; [lia|]. destruct (f x); lia. Qed.

Lemma decl_sp_none : forall t i p0, head t i = Some p0 -> is_space (byte_at t p0) = false -> decl t i = DNone.
Proof. intros t i p0 Hh Hs. unfold decl. rewrite Hh. cbv beta iota zeta. rewrite Hs. reflexivity. Qed.

Lemma decl_colon_none : forall t i p0 p1 p2, head t i = Some p0 -> is_space (byte_at t p0) = true ->
  p1 = (p0 + count_while is_space (skipn p0 t))%nat -> p2 = (p1 + count_while name_ok (skipn p1 t))%nat ->
  byte_at t p2 <> 58 -> decl t i = DNone.
Proof.
  intros t i p0 p1 p2 Hh Hs E1 E2 H58. subst p1 p2. unfold decl. rewrite Hh. cbv beta iota zeta. rewrite Hs.
  cbn [negb]. rewrite (proj2 (Z.eqb_neq _ _) H58). reflexivity.
Qed.

Lemma decl_lt_none : forall t i p0 p1 p2 p3, head t i = Some p0 -> is_space (byte_at t p0) = true ->
  p1 = (p0 + count_while is_space (skipn p0 t))%nat -> p2 = (p1 + count_while name_ok (skipn p1 t))%nat ->
  byte_at t p2 = 58 -> p3 = (S p2 + count_while is_space (skipn (S p2) t))%nat -> byte_at t p3 <> 60 ->
  decl t i = DNone.
Proof.
  intros t i p0 p1 p2 p3 Hh Hs E1 E2 H58 E3 H60. subst p1 p2 p3. unfold decl. rewrite Hh. cbv beta iota zeta.
  rewrite Hs. cbn [negb]. rewrite (proj2 (Z.eqb_eq _ _) H58). cbn [negb].
  rewrite (proj2 (Z.eqb_neq _ _) H60). reflexivity.
Qed.

Lemma decl_cut : forall t i p0 p1 p2 p3, head t i = Some p0 -> is_space (byte_at t p0) = true ->
  p1 = (p0 + count_while is_space (skipn p0 t))%nat -> p2 = (p1 + count_while name_ok (skipn p1 t))%nat ->
  byte_at t p2 = 58 -> p3 = (S p2 + count_while is_space (skipn (S p2) t))%nat -> byte_at t p3 = 60 ->
  find_idx (fun c => c =? 62) (skipn (S p3) t) = None -> decl t i = DCut.
Proof.
  intros t i p0 p1 p2 p3 Hh Hs E1 E2 H58 E3 H60 Hf. subst p1 p2 p3. unfold decl. rewrite Hh. cbv beta iota zeta.
  rewrite Hs. cbn [negb]. rewrite (proj2 (Z.eqb_eq _ _) H58). cbn [negb].
  rewrite (proj2 (Z.eqb_eq _ _) H60). cbn [negb]. rewrite Hf. reflexivity.
Qed.

Lemma decl_found : forall t i p0 p1 p2 p3 o, head t i = Some p0 -> is_space (byte_at t p0) = true ->
  p1 = (p0 + count_while is_space (skipn p0 t))%nat -> p2 = (p1 + count_while name_ok (skipn p1 t))%nat ->
  byte_at t p2 = 58 -> p3 = (S p2 + count_while is_space (skipn (S p2) t))%nat -> byte_at t p3 = 60 ->
  find_idx (fun c => c =? 62) (skipn (S p3) t) = Some o -> decl t i = DFound p1 (p2 - p1) (S p3) o (S p3 + o).
Proof.
  intros t i p0 p1 p2 p3 o Hh Hs E1 E2 H58 E3 H60 Hf. subst p1 p2 p3. unfold decl. rewrite Hh. cbv beta iota zeta.
  rewrite Hs. cbn [negb]. rewrite (proj2 (Z.eqb_eq _ _) H58). cbn [negb].
  rewrite (proj2 (Z.eqb_eq _ _) H60). cbn [negb]. rewrite Hf. reflexivity.
Qed.

Section M.
Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
  (m0 : word -> option byte) (lo : Z) (tx ux : word) (tb ts ub us : list byte).
Hypotheses (NT : Forall (fun b => bv_unsigned b <> 0) tb) (NU : Forall (fun b => bv_unsigned b <> 0) ub)
  (LT : (- (bv_unsigned tx + Z.of_nat (length tb) + 1)) mod 8 <= Z.of_nat (length ts))
  (LU : (- (bv_unsigned ux + Z.of_nat (length ub) + 1)) mod 8 <= Z.of_nat (length us))
  (T0 : 4096 <= bv_unsigned tx) (U0 : 4096 <= bv_unsigned ux)
  (TL : Z.of_nat (length tb) + 1 < 2^62) (UL : Z.of_nat (length ub) + 1 < 2^62)
  (TB : bv_unsigned tx + Z.of_nat (length tb + 1 + length ts) <= 2^64)
  (UB : bv_unsigned ux + Z.of_nat (length ub + 1 + length us) <= 2^64)
  (LO : lo + 272 <= bv_unsigned sp) (LO0 : 0 <= lo) (RSP : bv_unsigned sp < 2^64)
  (DT : bv_unsigned tx + Z.of_nat (length tb + 1 + length ts) <= bv_unsigned sp - 272 \/ bv_unsigned sp <= bv_unsigned tx)
  (DU : bv_unsigned ux + Z.of_nat (length ub + 1 + length us) <= bv_unsigned sp - 272 \/ bv_unsigned sp <= bv_unsigned ux)
  (DP : 66693 + 7 <= bv_unsigned sp - 272 \/ bv_unsigned sp <= 66693).
Hypotheses (STRLEN_C : strlen_contract) (STRCHR_C : strchr_contract) (STRNCMP_C : strncmp_contract)
  (BCMP_C : bcmp_contract) (PLAIN_C : plain_contract).

Abbreviation MST x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27
    x28 x29 x30 x31 pc m :=
  (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28
    x29 x30 x31) F (Z_to_bv 64 pc) fc None m (seg_rom rsegs)).
Abbreviation SPV := (Z_to_bv 64 (bv_unsigned sp + -240)).
Abbreviation tt := (zbytes tb).
Abbreviation uu := (zbytes ub).
Abbreviation Qx := (Q ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 lo tb ub).
Abbreviation MIx := (MI sp m0 lo tx ux tb ts ub us).
Abbreviation SAVEDx := (SAVED ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11).
Abbreviation MASK := (Z_to_bv 64 4294983169).
Abbreviation NN := (Z_to_bv 64 (Z.of_nat (length ub))).
Abbreviation LXT := (Z.lxor (bv_unsigned tx) 18446744073709551615).
Abbreviation NTX := (Z_to_bv 64 (Z.lxor (bv_unsigned tx) 18446744073709551615)).
Abbreviation NUX := (Z_to_bv 64 (Z.lxor (bv_unsigned ux) 18446744073709551615)).
Abbreviation XS pc x1 x5 x6 x7 x9 x10 x11 x12 x13 x17 x20 x21 x23 x24 x25 x27 x28 x29 x30 x31 m :=
  (MST x1 SPV gp tp x5 x6 x7 (Z_to_bv 64 6) x9 x10 x11 x12 x13 tx (Z_to_bv 64 58) MASK x17 (Z_to_bv 64 5)
    (Z_to_bv 64 66693) x20 x21 (Z_to_bv 64 (-1)) x23 x24 x25 (Z_to_bv 64 32) x27 x28 x29 x30 x31 pc m).
Abbreviation FRM d j1 j2 j3 :=
  ([CB 40 j1; C8 (Z_to_bv 64 324259173172773121); C8 NUX; C8 (Z_to_bv 64 (Z.of_nat d)); C8 ux; CB 8 j2; C8 NN;
    CB 8 j3; C8 (Z_to_bv 64 (bv_unsigned tx + 1)); C8 (Z_to_bv 64 (bv_unsigned ux + -2)); C8 MASK; C8 tx; C8 NTX;
    C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]).
Abbreviation TFRM c8 c16 c24 c32 c56 c72 c88 j0 :=
  ([CB 8 j0; C8 c8; C8 c16; C8 c24; C8 c32; C8 (Z_to_bv 64 324259173172773121); C8 NUX; C8 c56; C8 ux; C8 c72;
    C8 NN; C8 c88; C8 (Z_to_bv 64 (bv_unsigned tx + 1)); C8 (Z_to_bv 64 (bv_unsigned ux + -2)); C8 MASK; C8 tx;
    C8 NTX; C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]).

Ltac ldrop n l :=
  lazymatch n with
  | O => l
  | S ?n' => lazymatch l with _ :: ?l' => ldrop n' l' end
  end.
Ltac ltake n l :=
  lazymatch n with
  | O => constr:(@nil cell)
  | S ?n' => lazymatch l with ?x :: ?l' => let r := ltake n' l' in constr:(x :: r) end
  end.
Ltac llen l := lazymatch l with nil => constr:(O) | _ :: ?l' => let r := llen l' in constr:(S r) end.

Lemma sp_u2 : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -240)) = bv_unsigned sp + -240.
Proof. apply unsigned_lit. lia. Qed.

Ltac zc H := zify_cond H; try rewrite !Z.mod_small in H by lia.
Ltac mi := unfold MI; repeat match goal with |- _ /\ _ => split end; try assumption.
Ltac weq := first [ reflexivity | rewrite ?tbyte_val; reflexivity | word_eq_tac ].
Ltac notrap H := zify_cond H; pose proof (lxt tx); pose proof (lxu ux); rewrite ?zb_lxor_ones in H by lia; lia.
Ltac xpost :=
  lazymatch goal with
  | |- forall _, kret _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ?m _ _ _ -> _ =>
      let ms' := fresh "ms'" in let PO := fresh "PO" in intros ms' PO;
      unfold kret in PO; rewrite ?sp_u2 in PO; unfold STRCHR_K, PLAIN_K in PO; revert ms' PO;
      post_call rsegs m
  end.
Ltac merge_at FR p k :=
  lazymatch type of FR with
  | rw_cells ?s ?m ?A ?cs =>
      let pre := ltake p cs in let r := ldrop p cs in let mid := ltake k r in let post := ldrop k r in
      apply (rw_cells_merge s m A pre mid post) in FR; cbn [app cells_size csize Nat.add] in FR
  end.

Lemma bt_sub : forall m k n, bytes_at rsegs m (bv_unsigned tx) (tb ++ Z_to_bv 8 0 :: ts) -> (k + n <= length tb)%nat ->
  bytes_at rsegs m (bv_unsigned tx + Z.of_nat k) (firstn n (skipn k tb)).
Proof.
  intros m k n H Hk. replace (firstn n (skipn k tb)) with (firstn n (skipn k (tb ++ Z_to_bv 8 0 :: ts))).
  - apply bytes_at_first. apply bytes_at_skip; [exact H|rewrite length_app; cbn [length]; lia].
  - rewrite skipn_app, firstn_app, length_skipn. replace (k - length tb)%nat with 0%nat by lia.
    replace (n - (length tb - k))%nat with 0%nat by lia. cbn [skipn firstn]. apply app_nil_r.
Qed.

Lemma bu_sub : forall m k n, bytes_at rsegs m (bv_unsigned ux) (ub ++ Z_to_bv 8 0 :: us) -> (k + n <= length ub)%nat ->
  bytes_at rsegs m (bv_unsigned ux + Z.of_nat k) (firstn n (skipn k ub)).
Proof.
  intros m k n H Hk. replace (firstn n (skipn k ub)) with (firstn n (skipn k (ub ++ Z_to_bv 8 0 :: us))).
  - apply bytes_at_first. apply bytes_at_skip; [exact H|rewrite length_app; cbn [length]; lia].
  - rewrite skipn_app, firstn_app, length_skipn. replace (k - length ub)%nat with 0%nat by lia.
    replace (n - (length ub - k))%nat with 0%nat by lia. cbn [skipn firstn]. apply app_nil_r.
Qed.

Lemma rdt : forall m k, bytes_at rsegs m (bv_unsigned tx) (tb ++ Z_to_bv 8 0 :: ts) -> (k <= length tb)%nat ->
  ov_read_bytes rsegs m (wa (bv_unsigned tx + Z.of_nat k)) 1 = Some [tbyte tb k].
Proof. intros. eapply rd_t; eassumption. Qed.

Lemma rdp : forall m k, bytes_at rsegs m 66693 [Z_to_bv 8 112; Z_to_bv 8 114; Z_to_bv 8 101; Z_to_bv 8 102;
    Z_to_bv 8 105; Z_to_bv 8 120; Z_to_bv 8 0] -> (k < 7)%nat ->
  ov_read_bytes rsegs m (wa (66693 + Z.of_nat k)) 1 = Some [nth k [Z_to_bv 8 112; Z_to_bv 8 114; Z_to_bv 8 101;
    Z_to_bv 8 102; Z_to_bv 8 105; Z_to_bv 8 120; Z_to_bv 8 0] (Z_to_bv 8 0)].
Proof.
  intros m k H Hk. rewrite (bytes_at_read rsegs m _ _ (Z.of_nat k) 1 H) by (cbn [length]; lia).
  rewrite Nat2Z.id. rewrite (firstn1_skipn _ _ (Z_to_bv 8 0)) by (cbn [length]; lia). reflexivity.
Qed.

Lemma epiM : forall m low (x1 x5 x6 x7 x8 x9 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27
    x28 x29 x30 x31 : word) (r : Z),
  MIx m -> rw_cells rsegs m (bv_unsigned sp + -240) (low ++ SAVEDx) -> cells_size low = 136%nat ->
  r = names tt uu ->
  evt rsegs Qx (MST x1 SPV gp tp x5 x6 x7 x8 x9 (Z_to_bv 64 r) x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23
    x24 x25 x26 x27 x28 x29 x30 x31 0x13b14 m).
Proof. intros. eapply epi; eassumption. Qed.
Ltac ret_epi FR :=
  lazymatch type of FR with
  | rw_cells _ _ _ ?cs =>
      let n := llen cs in let k := eval cbv in (n - 13)%nat in let low := ltake k cs in
      eapply (epiM _ low); [mi | exact FR | reflexivity | ]
  end.

Lemma nz_lt : forall k, byte_at tt k <> 0 -> (k < length tb)%nat.
Proof. intros k H. rewrite <- (len_tt tb). apply byte_at_nz_lt. exact H. Qed.

Lemma pw : forall k i d m j1 j2 j3 (x1 x5 x6 x7 x10 x11 x12 x13 x17 x20 x21 x24 x25 x27 x28 x29 x30 x31 : word),
  (k < 6)%nat -> (i < length tb)%nat ->
  (forall k', (k' < k)%nat -> cmatch (byte_at tt (i + k')) (nth k' prefix_lc 0) = true) ->
  x10 = Z_to_bv 64 (Z.of_nat k) -> x11 = Z_to_bv 64 (Z.lxor (bv_unsigned tx + Z.of_nat i) 18446744073709551615) ->
  MIx m -> rw_cells rsegs m (bv_unsigned sp + -240) (FRM d j1 j2 j3) ->
  (ci_eqb (firstn 6 (skipn i tt)) prefix_lc = true -> forall (y10 y11 y12 y13 : word),
     evt rsegs Qx (XS 0x137e8 x1 x5 x6 x7 (Z_to_bv 64 (bv_unsigned tx + Z.of_nat i)) y10 y11 y12 y13 x17 x20 x21
       (Z_to_bv 64 (Z.of_nat i)) x24 x25 x27 x28 x29 x30 x31 m)) ->
  (ci_eqb (firstn 6 (skipn i tt)) prefix_lc = false -> forall (y10 y11 y12 y13 : word),
     evt rsegs Qx (XS 0x13958 x1 x5 x6 x7 (Z_to_bv 64 (bv_unsigned tx + Z.of_nat i)) y10 y11 y12 y13 x17 x20 x21
       (Z_to_bv 64 (Z.of_nat i)) x24 x25 x27 x28 x29 x30 x31 m)) ->
  evt rsegs Qx (XS 0x137c0 x1 x5 x6 x7 (Z_to_bv 64 (bv_unsigned tx + Z.of_nat i)) x10 x11 x12 x13 x17 x20 x21
    (Z_to_bv 64 (Z.of_nat i)) x24 x25 x27 x28 x29 x30 x31 m).
Proof.
  intros k. remember (6 - k)%nat as e eqn:Ee. revert k Ee. induction e as [e IH] using lt_wf_ind.
  intros k Ee i d m j1 j2 j3 x1 x5 x6 x7 x10 x11 x12 x13 x17 x20 x21 x24 x25 x27 x28 x29 x30 x31
    Hk Hi Hpre E10 E11 HM FR KY KN.
  subst x10 x11.
  pose proof HM as HM0. destruct HM as (BT & BU & PF & MEM & ST & MU & WM).
  assert (Hik : (i + k <= length tb)%nat).
  { destruct k as [|k]; [lia|]. specialize (Hpre k ltac:(lia)). apply cmatch_nz in Hpre; [|lia].
    rewrite <- (len_tt tb). apply byte_at_nz_lt in Hpre. lia. }
  pose proof (rdt m (i + k) BT Hik) as R1.
  pose proof (rdp m k PF ltac:(lia)) as R2.
  pose proof (pl_range k Hk) as PR. pose proof (tb_range tb (i + k)) as BR.
  assert (AFTER : cmatch (byte_at tt (i + k)) (nth k prefix_lc 0) = true -> forall y11 y12 y13,
    y11 = Z_to_bv 64 (Z.lxor (bv_unsigned tx + Z.of_nat i) 18446744073709551615) ->
    evt rsegs Qx (XS 0x137e0 x1 x5 x6 x7 (Z_to_bv 64 (bv_unsigned tx + Z.of_nat i)) (Z_to_bv 64 (Z.of_nat k)) y11
      y12 y13 x17 x20 x21 (Z_to_bv 64 (Z.of_nat i)) x24 x25 x27 x28 x29 x30 x31 m)).
  { intros Hc y11 y12 y13 E11. subst y11. clear R1 R2. zstep. zstep. if_cases HC; zc HC.
    - eapply (IH (6 - S k)%nat ltac:(lia) (S k) eq_refl); try eassumption; try lia; try weq.
      intros k' Hk'. destruct (Nat.eq_dec k' k) as [->|Hne]; [exact Hc|apply Hpre; lia].
    - apply KY. apply ci6. intros k' Hk'. destruct (Nat.eq_dec k' k) as [->|Hne]; [exact Hc|apply Hpre; lia]. }
  zstep. if_cases HT; [notrap HT|].
  zstep. zstep. zstep. zstep. cbv beta. rewrite tbyte_val, (pfb_val k Hk). zstep.
  if_cases HC.
  - zc HC. apply AFTER; [|reflexivity]. unfold cmatch. rewrite HC, Z.eqb_refl. reflexivity.
  - zc HC. zstep. zstep. if_cases HC2; zc HC2.
    + assert (HN : ci_eqb (firstn 6 (skipn i tt)) prefix_lc = false).
      { destruct (ci_eqb _ _) eqn:E; [|reflexivity]. apply ci6 with (k := k) in E; [|lia].
        unfold cmatch in E. apply orb_true_iff in E as [E|E]; apply Z.eqb_eq in E; lia. }
      apply KN. exact HN.
    + apply AFTER; [|reflexivity]. unfold cmatch. apply orb_true_iff. right. apply Z.eqb_eq. lia.
Qed.

Lemma sp1 : forall e p q m (x1 x5 x6 x7 x9 x10 x11 x12 x13 x17 x20 x21 x23 x24 x25 x27 x28 x29 x30 x31 : word),
  e = (length tb - p)%nat -> (p <= length tb)%nat -> q = (p + count_while is_space (skipn p tt))%nat ->
  bytes_at rsegs m (bv_unsigned tx) (tb ++ Z_to_bv 8 0 :: ts) ->
  x20 = Z_to_bv 64 (bv_unsigned tx + Z.of_nat p) -> x10 = Z_to_bv 64 (bv_unsigned tx + Z.of_nat p + 1) ->
  x27 = Z_to_bv 64 (bv_unsigned tx + Z.of_nat p + 2) ->
  x9 = Z_to_bv 64 (bv_unsigned ux + -2 - (bv_unsigned tx + Z.of_nat p)) ->
  (forall y9 y10 y11 y12 y20 y27 : word,
     y20 = Z_to_bv 64 (bv_unsigned tx + Z.of_nat q) -> y10 = Z_to_bv 64 (bv_unsigned tx + Z.of_nat q + 1) ->
     y27 = Z_to_bv 64 (bv_unsigned tx + Z.of_nat q + 2) ->
     y9 = Z_to_bv 64 (bv_unsigned ux + -2 - (bv_unsigned tx + Z.of_nat q)) ->
     y11 = Z_to_bv 64 (byte_at tt q) ->
     evt rsegs Qx (XS 0x13868 x1 x5 x6 x7 y9 y10 y11 y12 x13 x17 y20 x21 x23 x24 x25 y27 x28 x29 x30 x31 m)) ->
  evt rsegs Qx (XS 0x13840 x1 x5 x6 x7 x9 x10 x11 x12 x13 x17 x20 x21 x23 x24 x25 x27 x28 x29 x30 x31 m).
Proof.
  intros e. induction e as [e IH] using lt_wf_ind.
  intros p q m x1 x5 x6 x7 x9 x10 x11 x12 x13 x17 x20 x21 x23 x24 x25 x27 x28 x29 x30 x31
    Ee Hp Hq BT E20 E10 E27 E9 K. subst x20 x10 x27 x9.
  pose proof (tb_range tb p) as BR. pose proof (rdt m p BT Hp) as R.
  assert (SPC : is_space (byte_at tt p) = true -> forall y11 y12,
    evt rsegs Qx (XS 0x1384c x1 x5 x6 x7 (Z_to_bv 64 (bv_unsigned ux + -2 - (bv_unsigned tx + Z.of_nat p)))
      (Z_to_bv 64 (bv_unsigned tx + Z.of_nat p + 1)) y11 y12 x13 x17 (Z_to_bv 64 (bv_unsigned tx + Z.of_nat p)) x21
      x23 x24 x25 (Z_to_bv 64 (bv_unsigned tx + Z.of_nat p + 2)) x28 x29 x30 x31 m)).
  { intros Hs y11 y12.
    assert (Hlt : (p < length tb)%nat).
    { apply nz_lt. intro E. rewrite E in Hs. discriminate Hs. }
    clear R. zstep. if_cases HT; [notrap HT|]. do 5 zstep.
    eapply (IH (length tb - S p)%nat ltac:(lia) (S p) q); try exact BT; try weq; try lia; [|exact K].
    rewrite Hq, (cw_step is_space tt p ltac:(rewrite (len_tt tb); lia)), Hs. lia. }
  zstep. cbv beta. rewrite tbyte_val. zstep. zstep. if_cases HC.
  - zstep. if_cases HC2.
    + apply SPC. apply bq in HC2. bdec (byte_at tt p) HC2. exact BR.
    + assert (HS : is_space (byte_at tt p) = false).
      { apply negb_true_iff. bjoin HC HC2 HJ. bdec (byte_at tt p) HJ. exact BR. }
      assert (Hqp : q = p).
      { rewrite Hq. destruct (Nat.lt_ge_cases p (length tb)) as [Hl|Hl].
        - rewrite (cw_step is_space tt p ltac:(rewrite (len_tt tb); lia)), HS. lia.
        - rewrite cw_end by (rewrite (len_tt tb); lia). lia. }
      clear Hq. subst q. eapply K; weq.
  - apply SPC. apply bq in HC. bdec (byte_at tt p) HC. exact BR.
Qed.

Lemma nl : forall e p p1 q m (x1 x5 x6 x7 x9 x10 x11 x12 x13 x17 x20 x21 x23 x24 x25 x27 x28 x29 x30 x31 : word),
  e = (length tb - p)%nat -> (p1 <= p)%nat -> (p <= length tb)%nat ->
  q = (p + count_while name_ok (skipn p tt))%nat ->
  bytes_at rsegs m (bv_unsigned tx) (tb ++ Z_to_bv 8 0 :: ts) ->
  x11 = Z_to_bv 64 (byte_at tt p) -> x20 = Z_to_bv 64 (bv_unsigned tx + Z.of_nat p1) ->
  x21 = Z_to_bv 64 (Z.of_nat (p - p1)) -> x24 = Z_to_bv 64 (1 + Z.of_nat (p - p1)) ->
  x25 = Z_to_bv 64 (bv_unsigned tx + 1 + Z.of_nat (p - p1)) ->
  x10 = Z_to_bv 64 (bv_unsigned tx + Z.of_nat p + 1) -> x27 = Z_to_bv 64 (bv_unsigned tx + Z.of_nat p + 2) ->
  x9 = Z_to_bv 64 (bv_unsigned ux + -2 - (bv_unsigned tx + Z.of_nat p)) ->
  (byte_at tt q <> 58 -> forall y9 y10 y11 y12 y13 y21 y24 y25 y27 : word,
     evt rsegs Qx (XS 0x13958 x1 x5 x6 x7 y9 y10 y11 y12 y13 x17 x20 y21 x23 y24 y25 y27 x28 x29 x30 x31 m)) ->
  (byte_at tt q = 58 -> forall y9 y10 y11 y12 y13 y21 y24 y25 y27 : word,
     y21 = Z_to_bv 64 (Z.of_nat (q - p1)) -> y24 = Z_to_bv 64 (1 + Z.of_nat (q - p1)) ->
     y25 = Z_to_bv 64 (bv_unsigned tx + 1 + Z.of_nat (q - p1)) -> y11 = Z_to_bv 64 (bv_unsigned tx + Z.of_nat q) ->
     y10 = Z_to_bv 64 (bv_unsigned tx + Z.of_nat q + 1) -> y27 = Z_to_bv 64 (bv_unsigned tx + Z.of_nat q + 2) ->
     y9 = Z_to_bv 64 (bv_unsigned ux + -2 - (bv_unsigned tx + Z.of_nat q)) ->
     evt rsegs Qx (XS 0x138c4 x1 x5 x6 x7 y9 y10 y11 y12 y13 x17 x20 y21 x23 y24 y25 y27 x28 x29 x30 x31 m)) ->
  evt rsegs Qx (XS 0x13874 x1 x5 x6 x7 x9 x10 x11 x12 x13 x17 x20 x21 x23 x24 x25 x27 x28 x29 x30 x31 m).
Proof.
  intros e. induction e as [e IH] using lt_wf_ind.
  intros p p1 q m x1 x5 x6 x7 x9 x10 x11 x12 x13 x17 x20 x21 x23 x24 x25 x27 x28 x29 x30 x31
    Ee Hp1 Hp Hq BT E11 E20 E21 E24 E25 E10 E27 E9 KN K58. subst x11 x20 x21 x24 x25 x10 x27 x9.
  pose proof (tb_range tb p) as BR.
  assert (CONT : name_ok (byte_at tt p) = true -> forall y11 y12 y13,
    y11 = Z_to_bv 64 (bv_unsigned tx + Z.of_nat p1 + Z.of_nat (p - p1)) ->
    evt rsegs Qx (XS 0x13890 x1 x5 x6 x7 (Z_to_bv 64 (bv_unsigned ux + -2 - (bv_unsigned tx + Z.of_nat p)))
      (Z_to_bv 64 (bv_unsigned tx + Z.of_nat p + 1)) y11 y12 y13 x17 (Z_to_bv 64 (bv_unsigned tx + Z.of_nat p1))
      (Z_to_bv 64 (Z.of_nat (p - p1))) x23 (Z_to_bv 64 (1 + Z.of_nat (p - p1)))
      (Z_to_bv 64 (bv_unsigned tx + 1 + Z.of_nat (p - p1))) (Z_to_bv 64 (bv_unsigned tx + Z.of_nat p + 2)) x28 x29
      x30 x31 m)).
  { intros Hs y11 y12 y13 E11. subst y11.
    assert (Hlt : (p < length tb)%nat).
    { apply nz_lt. intro E. rewrite E in Hs. discriminate Hs. }
    pose proof (rdt m (S p) BT ltac:(lia)) as R.
    zstep. if_cases HT; [notrap HT|].
    zstep. cbv beta. rewrite tbyte_val. do 7 zstep.
    eapply (IH (length tb - S p)%nat ltac:(lia) (S p) p1 q); try exact BT; try weq; try lia; [|exact KN|exact K58].
    rewrite Hq, (cw_step name_ok tt p ltac:(rewrite (len_tt tb); lia)), Hs. lia. }
  assert (STOP : name_ok (byte_at tt p) = false -> q = p).
  { intros Hs. rewrite Hq. destruct (Nat.lt_ge_cases p (length tb)) as [Hl|Hl].
    - rewrite (cw_step name_ok tt p ltac:(rewrite (len_tt tb); lia)), Hs. lia.
    - rewrite cw_end by (rewrite (len_tt tb); lia). lia. }
  zstep. zstep. zstep. if_cases HC1.
  - eapply CONT; [|reflexivity]. apply bq in HC1. bdec (byte_at tt p) HC1. exact BR.
  - zstep. zstep. zstep. if_cases HC2.
    + assert (HS : (negb (name_ok (byte_at tt p)) && negb (byte_at tt p =? 58)) = true).
      { bjoin HC1 HC2 HJ. bdec (byte_at tt p) HJ. exact BR. }
      apply andb_true_iff in HS as [HS1 HS2]. apply negb_true_iff in HS1, HS2. apply Z.eqb_neq in HS2.
      rewrite (STOP HS1) in KN. apply KN. exact HS2.
    + zstep. if_cases HC3.
      * assert (HS : (negb (name_ok (byte_at tt p)) && (byte_at tt p =? 58)) = true).
        { apply bq in HC3. pose proof HC3 as HC3'. bjoin HC1 HC2 HJ. pose proof (band' _ _ HJ HC3') as HJ2.
          bdec (byte_at tt p) HJ2. exact BR. }
        apply andb_true_iff in HS as [HS1 HS2]. apply negb_true_iff in HS1. apply Z.eqb_eq in HS2.
        pose proof (STOP HS1) as Hqp. clear Hq STOP. subst q. eapply K58; [exact HS2|weq..].
      * eapply CONT; [|reflexivity]. apply bq in HC3. bjoin HC1 HC2 HJ. pose proof (band' _ _ HJ HC3) as HJ2.
        bdec (byte_at tt p) HJ2. exact BR.
Qed.

Lemma sp2 : forall e p p3 m (x1 x5 x6 x7 x9 x10 x11 x12 x13 x17 x20 x21 x23 x24 x25 x27 x28 x29 x30 x31 : word),
  e = (length tb - p)%nat -> (p <= length tb)%nat -> p3 = (p + count_while is_space (skipn p tt))%nat ->
  bytes_at rsegs m (bv_unsigned tx) (tb ++ Z_to_bv 8 0 :: ts) ->
  x10 = Z_to_bv 64 (bv_unsigned tx + Z.of_nat p) -> x27 = Z_to_bv 64 (bv_unsigned tx + Z.of_nat p + 1) ->
  x9 = Z_to_bv 64 (bv_unsigned ux + -1 - (bv_unsigned tx + Z.of_nat p)) ->
  (byte_at tt p3 <> 60 -> forall y9 y10 y11 y12 y27 : word,
     evt rsegs Qx (XS 0x13958 x1 x5 x6 x7 y9 y10 y11 y12 x13 x17 x20 x21 x23 x24 x25 y27 x28 x29 x30 x31 m)) ->
  (byte_at tt p3 = 60 -> forall y9 y10 y11 y12 y27 : word,
     y10 = Z_to_bv 64 (bv_unsigned tx + Z.of_nat p3) -> y27 = Z_to_bv 64 (bv_unsigned tx + Z.of_nat p3 + 1) ->
     y9 = Z_to_bv 64 (bv_unsigned ux + -1 - (bv_unsigned tx + Z.of_nat p3)) ->
     evt rsegs Qx (XS 0x138f4 x1 x5 x6 x7 y9 y10 y11 y12 x13 x17 x20 x21 x23 x24 x25 y27 x28 x29 x30 x31 m)) ->
  evt rsegs Qx (XS 0x138c8 x1 x5 x6 x7 x9 x10 x11 x12 x13 x17 x20 x21 x23 x24 x25 x27 x28 x29 x30 x31 m).
Proof.
  intros e. induction e as [e IH] using lt_wf_ind.
  intros p p3 m x1 x5 x6 x7 x9 x10 x11 x12 x13 x17 x20 x21 x23 x24 x25 x27 x28 x29 x30 x31
    Ee Hp Hq BT E10 E27 E9 KN KL. subst x10 x27 x9.
  pose proof (tb_range tb p) as BR.
  pose proof (rdt m p BT Hp) as R.
  assert (SPC : is_space (byte_at tt p) = true -> forall y11 y12,
    evt rsegs Qx (XS 0x138d4 x1 x5 x6 x7 (Z_to_bv 64 (bv_unsigned ux + -1 - (bv_unsigned tx + Z.of_nat p)))
      (Z_to_bv 64 (bv_unsigned tx + Z.of_nat p)) y11 y12 x13 x17 x20 x21 x23 x24 x25
      (Z_to_bv 64 (bv_unsigned tx + Z.of_nat p + 1)) x28 x29 x30 x31 m)).
  { intros Hs y11 y12.
    assert (Hlt : (p < length tb)%nat).
    { apply nz_lt. intro E. rewrite E in Hs. discriminate Hs. }
    clear R. do 4 zstep. if_cases HC; [|zify_cond HC; lia].
    eapply (IH (length tb - S p)%nat ltac:(lia) (S p) p3); try exact BT; try weq; try lia; [|exact KN|exact KL].
    rewrite Hq, (cw_step is_space tt p ltac:(rewrite (len_tt tb); lia)), Hs. lia. }
  assert (STOP : is_space (byte_at tt p) = false -> p3 = p).
  { intros Hs. rewrite Hq. destruct (Nat.lt_ge_cases p (length tb)) as [Hl|Hl].
    - rewrite (cw_step is_space tt p ltac:(rewrite (len_tt tb); lia)), Hs. lia.
    - rewrite cw_end by (rewrite (len_tt tb); lia). lia. }
  zstep. cbv beta. rewrite tbyte_val. zstep. zstep. if_cases HC.
  - zstep. if_cases HC2.
    + apply SPC. apply bq in HC2. bdec (byte_at tt p) HC2. exact BR.
    + assert (HS : is_space (byte_at tt p) = false).
      { apply negb_true_iff. bjoin HC HC2 HJ. bdec (byte_at tt p) HJ. exact BR. }
      rewrite (STOP HS) in KN, KL.
      zstep. zstep. if_cases HC3; zc HC3.
      * apply KN. exact HC3.
      * eapply KL; [exact HC3|weq..].
  - apply SPC. apply bq in HC. bdec (byte_at tt p) HC. exact BR.
Qed.


Ltac bj1 H1 H := pose proof (bq _ _ H1) as H.
Ltac bj2 H1 H2 H := pose proof (band' _ _ (bq _ _ H1) (bq _ _ H2)) as H.
Ltac bj3 H1 H2 H3 H := pose proof (band' _ _ (band' _ _ (bq _ _ H1) (bq _ _ H2)) (bq _ _ H3)) as H.
Ltac bj4 H1 H2 H3 H4 H :=
  pose proof (band' _ _ (band' _ _ (band' _ _ (bq _ _ H1) (bq _ _ H2)) (bq _ _ H3)) (bq _ _ H4)) as H.

Definition p30 (z : Z) : bool := negb (is_alnum z || (z =? 95) || (z =? 45) || (z =? 58) || (z =? 37) || (z =? 92)).

Lemma tk_next : forall j nl o m c24 c32 c56 c72 j0 (x1 x5 x6 x7 x10 x11 x12 x13 x17 x20 x21 x23 x24 x25 x28 x29 x30
    x31 : word),
  (o < length ub)%nat -> (j + nl + 1 + (length ub - o) <= length tb)%nat ->
  MIx m -> rw_cells rsegs m (bv_unsigned sp + -240)
    (TFRM (Z_to_bv 64 (bv_unsigned tx + 1 + Z.of_nat nl + (Z.of_nat (length ub) - Z.of_nat o)))
      (Z_to_bv 64 (Z.of_nat (length ub) - Z.of_nat o + Z.of_nat nl + 1)) c24 c32 c56 c72
      (Z_to_bv 64 (Z.of_nat (length tb))) j0) ->
  (negb (name_char (byte_at tt (j + nl + 1 + (length ub - o)))) = true -> 1 = names tt uu) ->
  (negb (name_char (byte_at tt (j + nl + 1 + (length ub - o)))) = false -> forall y10 y11 y12 : word,
    evt rsegs Qx (XS 0x13a54 x1 x5 x6 x7 (Z_to_bv 64 (LXT - Z.of_nat j)) y10 y11 y12 x13 x17 x20 x21 x23 x24 x25
      (Z_to_bv 64 (Z.of_nat j)) x28 x29 x30 x31 m)) ->
  evt rsegs Qx (XS 0x13ac0 x1 x5 x6 x7 (Z_to_bv 64 (LXT - Z.of_nat j)) x10 x11 x12 x13 x17 x20 x21 x23 x24 x25
    (Z_to_bv 64 (Z.of_nat j)) x28 x29 x30 x31 m).
Proof.
  intros j nl o m c24 c32 c56 c72 j0 x1 x5 x6 x7 x10 x11 x12 x13 x17 x20 x21 x23 x24 x25 x28 x29 x30 x31
    Ho Hj HM FR KOK KBAD.
  pose proof HM as HM0. destruct HM as (BT & BU & PF & MEM & ST & MU & WM).
  pose proof (rdt m (j + nl + 1 + (length ub - o)) BT Hj) as R.
  pose proof (tb_range tb (j + nl + 1 + (length ub - o))) as BR.
  zstep. zstep. if_cases HT; [notrap HT|].
  zstep. zstep. zstep. cbv beta. rewrite tbyte_val.
  assert (N30 : p30 (byte_at tt (j + nl + 1 + (length ub - o))) = true -> forall y11 y12,
    evt rsegs Qx (XS 0x13b08 x1 x5 x6 x7 (Z_to_bv 64 (LXT - Z.of_nat j))
      (Z_to_bv 64 (byte_at tt (j + nl + 1 + (length ub - o)))) y11 y12 x13 x17 x20 x21 x23 x24 x25
      (Z_to_bv 64 (Z.of_nat j)) x28 x29 x30 x31 m)).
  { intros Hp y11 y12. zstep. zstep. if_cases HC.
    - apply KBAD. apply negb_false_iff. bj1 HC HJ.
      bdec (byte_at tt (j + nl + 1 + (length ub - o))) HJ. exact BR.
    - zstep. ret_epi FR. apply KOK. bj2 Hp HC HJ. bdec (byte_at tt (j + nl + 1 + (length ub - o))) HJ. exact BR. }
  do 3 zstep. if_cases HC1.
  - apply KBAD. apply negb_false_iff. bj1 HC1 HJ. bdec (byte_at tt (j + nl + 1 + (length ub - o))) HJ. exact BR.
  - do 4 zstep. if_cases HC2.
    + apply KBAD. apply negb_false_iff. bj1 HC2 HJ. bdec (byte_at tt (j + nl + 1 + (length ub - o))) HJ. exact BR.
    + do 2 zstep. if_cases HC3.
      * apply N30. bj3 HC1 HC2 HC3 HJ. bdec (byte_at tt (j + nl + 1 + (length ub - o))) HJ. exact BR.
      * do 4 zstep. if_cases HC4.
        -- apply KBAD. apply negb_false_iff. bj2 HC3 HC4 HJ.
           bdec (byte_at tt (j + nl + 1 + (length ub - o))) HJ. exact BR.
        -- apply N30. bj4 HC1 HC2 HC3 HC4 HJ. bdec (byte_at tt (j + nl + 1 + (length ub - o))) HJ. exact BR.
Qed.

Lemma tk_prev : forall j' m c8 c16 c24 c32 c56 c72 c88 j0 (x1 x5 x6 x7 x9 x10 x11 x12 x13 x17 x20 x21 x23 x24 x25 x27
    x28 x29 x30 x31 : word),
  (S j' <= length tb)%nat -> x23 = Z_to_bv 64 (bv_unsigned tx + Z.of_nat (S j')) ->
  MIx m -> rw_cells rsegs m (bv_unsigned sp + -240) (TFRM c8 c16 c24 c32 c56 c72 c88 j0) ->
  (negb (name_char (byte_at tt j')) && negb (byte_at tt j' =? 46) = true -> forall y10 y11 y12 : word,
    evt rsegs Qx (XS 0x13ac0 x1 x5 x6 x7 x9 y10 y11 y12 x13 x17 x20 x21 x23 x24 x25 x27 x28 x29 x30 x31 m)) ->
  (negb (name_char (byte_at tt j')) && negb (byte_at tt j' =? 46) = false -> forall y10 y11 y12 : word,
    evt rsegs Qx (XS 0x13a54 x1 x5 x6 x7 x9 y10 y11 y12 x13 x17 x20 x21 x23 x24 x25 x27 x28 x29 x30 x31 m)) ->
  evt rsegs Qx (XS 0x13a70 x1 x5 x6 x7 x9 x10 x11 x12 x13 x17 x20 x21 x23 x24 x25 x27 x28 x29 x30 x31 m).
Proof.
  intros j' m c8 c16 c24 c32 c56 c72 c88 j0 x1 x5 x6 x7 x9 x10 x11 x12 x13 x17 x20 x21 x23 x24 x25 x27 x28 x29 x30
    x31 Hj E23 HM FR KOK KBAD. subst x23.
  pose proof HM as HM0. destruct HM as (BT & BU & PF & MEM & ST & MU & WM).
  pose proof (rdt m j' BT ltac:(lia)) as R. pose proof (tb_range tb j') as BR.
  zstep. zstep. if_cases HT; [notrap HT|].
  zstep. cbv beta. rewrite tbyte_val.
  assert (P4 : p30 (byte_at tt j') = true -> forall y11 y12,
    evt rsegs Qx (XS 0x13ab0 x1 x5 x6 x7 x9 (Z_to_bv 64 (byte_at tt j')) y11 y12 x13 x17 x20 x21
      (Z_to_bv 64 (bv_unsigned tx + Z.of_nat (S j'))) x24 x25 x27 x28 x29 x30 x31 m)).
  { intros Hp y11 y12. zstep. zstep. if_cases HC.
    - apply KBAD. apply negb_true_iff. bj1 HC HJ. bdec (byte_at tt j') HJ. exact BR.
    - zstep. zstep. if_cases HC'.
      + apply KBAD. apply negb_true_iff. bj1 HC' HJ. bdec (byte_at tt j') HJ. exact BR.
      + apply KOK. bj3 Hp HC HC' HJ. bdec (byte_at tt j') HJ. exact BR. }
  do 3 zstep. if_cases HC1.
  - apply KBAD. apply negb_true_iff. bj1 HC1 HJ. bdec (byte_at tt j') HJ. exact BR.
  - do 4 zstep. if_cases HC2.
    + apply KBAD. apply negb_true_iff. bj1 HC2 HJ. bdec (byte_at tt j') HJ. exact BR.
    + do 2 zstep. if_cases HC3.
      * apply P4. bj3 HC1 HC2 HC3 HJ. bdec (byte_at tt j') HJ. exact BR.
      * do 4 zstep. if_cases HC4.
        -- apply KBAD. apply negb_true_iff. bj2 HC3 HC4 HJ. bdec (byte_at tt j') HJ. exact BR.
        -- apply P4. bj4 HC1 HC2 HC3 HC4 HJ. bdec (byte_at tt j') HJ. exact BR.
Qed.

Lemma token_run : forall e j p1 nl o m (c8 c16 c24 c32 c56 c72 c88 : word) j0
    (x1 x5 x6 x7 x9 x10 x11 x12 x13 x15 x16 x17 x20 x21 x23 x24 x25 x27 x28 x29 x30 x31 : word),
  e = (length tb - j)%nat -> (p1 + nl < length tb)%nat -> (o < length ub)%nat ->
  (j + nl + 1 + (length ub - o) <= length tb)%nat ->
  (forall j', (j' < j)%nat -> token_at tt (firstn nl (skipn p1 tt)) (skipn o uu) j' = false) ->
  x27 = Z_to_bv 64 (Z.of_nat j) -> x9 = Z_to_bv 64 (LXT - Z.of_nat j) ->
  x20 = Z_to_bv 64 (bv_unsigned tx + Z.of_nat p1) -> x21 = Z_to_bv 64 (Z.of_nat nl) ->
  x24 = Z_to_bv 64 (Z.of_nat (length ub) - Z.of_nat o + (1 + Z.of_nat nl)) ->
  x25 = Z_to_bv 64 (bv_unsigned tx + Z.of_nat nl) ->
  c8 = Z_to_bv 64 (bv_unsigned tx + 1 + Z.of_nat nl + (Z.of_nat (length ub) - Z.of_nat o)) ->
  c16 = Z_to_bv 64 (Z.of_nat (length ub) - Z.of_nat o + Z.of_nat nl + 1) ->
  c24 = Z_to_bv 64 (Z.of_nat (length ub) - Z.of_nat o) -> c32 = Z_to_bv 64 (bv_unsigned ux + Z.of_nat o) ->
  c88 = Z_to_bv 64 (Z.of_nat (length tb)) ->
  MIx m -> rw_cells rsegs m (bv_unsigned sp + -240) (TFRM c8 c16 c24 c32 c56 c72 c88 j0) ->
  (token tt (firstn nl (skipn p1 tt)) (skipn o uu) = true -> 1 = names tt uu) ->
  (token tt (firstn nl (skipn p1 tt)) (skipn o uu) = false -> forall m' (y1 y5 y6 y7 y9 y10 y11 y12 y13 y17 y20 y21
      y23 y24 y25 y27 y28 y29 y30 y31 : word),
     MIx m' -> rw_cells rsegs m' (bv_unsigned sp + -240) (TFRM c8 c16 c24 c32 c56 c72 c88 j0) ->
     evt rsegs Qx (XS 0x13940 y1 y5 y6 y7 y9 y10 y11 y12 y13 y17 y20 y21 y23 y24 y25 y27 y28 y29 y30 y31 m')) ->
  evt rsegs Qx (MST x1 SPV gp tp x5 x6 x7 (Z_to_bv 64 6) x9 x10 x11 x12 x13 tx x15 x16 x17 (Z_to_bv 64 5)
    (Z_to_bv 64 66693) x20 x21 (Z_to_bv 64 (-1)) x23 x24 x25 (Z_to_bv 64 32) x27 x28 x29 x30 x31 0x139f4 m).
Proof.
  intros e. induction e as [e IH] using lt_wf_ind.
  intros j p1 nl o m c8 c16 c24 c32 c56 c72 c88 j0 x1 x5 x6 x7 x9 x10 x11 x12 x13 x15 x16 x17 x20 x21 x23 x24 x25 x27
    x28 x29 x30 x31 Ee Hpn Ho Hj Hbef E27 E9 E20 E21 E24 E25 C8e C16e C24e C32e C88e HM FR KT KF.
  subst x27 x9 x20 x21 x24 x25 c8 c16 c24 c32 c88.
  pose proof HM as HM0. destruct HM as (BT & BU & PF & MEM & ST & MU & WM).
  pose proof (lxt tx) as LX.
  assert (Lpre : length (firstn nl (skipn p1 tt)) = nl).
  { rewrite length_firstn, length_skipn, (len_tt tb). lia. }
  assert (Lloc : length (skipn o uu) = (length ub - o)%nat).
  { rewrite length_skipn, (len_uu ub). reflexivity. }
  assert (TA : token_at tt (firstn nl (skipn p1 tt)) (skipn o uu) j =
    zl_eqb (firstn nl (skipn j tt)) (firstn nl (skipn p1 tt)) && (byte_at tt (j + nl) =? 58)
    && zl_eqb (firstn (length ub - o) (skipn (j + nl + 1) tt)) (skipn o uu)
    && match j with O => true | S j' => negb (name_char (byte_at tt j')) && negb (byte_at tt j' =? 46) end
    && negb (name_char (byte_at tt (j + nl + 1 + (length ub - o))))).
  { rewrite token_at_eq by (rewrite Lpre, Lloc, (len_tt tb); lia). rewrite Lpre, Lloc. reflexivity. }
  assert (FAIL : token_at tt (firstn nl (skipn p1 tt)) (skipn o uu) j = false ->
    forall m' (y1 y5 y6 y7 y10 y11 y12 y13 y17 y23 y28 y29 y30 y31 : word),
    MIx m' -> rw_cells rsegs m' (bv_unsigned sp + -240)
      (TFRM (Z_to_bv 64 (bv_unsigned tx + 1 + Z.of_nat nl + (Z.of_nat (length ub) - Z.of_nat o)))
        (Z_to_bv 64 (Z.of_nat (length ub) - Z.of_nat o + Z.of_nat nl + 1))
        (Z_to_bv 64 (Z.of_nat (length ub) - Z.of_nat o)) (Z_to_bv 64 (bv_unsigned ux + Z.of_nat o)) c56 c72
        (Z_to_bv 64 (Z.of_nat (length tb))) j0) ->
    evt rsegs Qx (XS 0x13a54 y1 y5 y6 y7 (Z_to_bv 64 (LXT - Z.of_nat j)) y10 y11 y12 y13 y17
      (Z_to_bv 64 (bv_unsigned tx + Z.of_nat p1)) (Z_to_bv 64 (Z.of_nat nl)) y23
      (Z_to_bv 64 (Z.of_nat (length ub) - Z.of_nat o + (1 + Z.of_nat nl))) (Z_to_bv 64 (bv_unsigned tx + Z.of_nat nl))
      (Z_to_bv 64 (Z.of_nat j)) y28 y29 y30 y31 m')).
  { intros Hf m' y1 y5 y6 y7 y10 y11 y12 y13 y17 y23 y28 y29 y30 y31 HM' FR'.
    assert (Hb' : forall j', (j' < S j)%nat -> token_at tt (firstn nl (skipn p1 tt)) (skipn o uu) j' = false).
    { intros j' Hj'. destruct (Nat.eq_dec j' j) as [->|Hne]; [exact Hf|apply Hbef; lia]. }
    do 5 zstep. if_cases HC; zc HC.
    - eapply (IH (length tb - S j)%nat ltac:(lia) (S j) p1 nl o m'); [reflexivity|lia|lia|lia|exact Hb'|
        weq..|exact HM'|exact FR'|exact KT|exact KF].
    - zstep. eapply KF; [|exact HM'|exact FR'].
      apply (token_false_of _ _ _ (S j)); [exact Hb'|]. rewrite Lpre, Lloc, (len_tt tb). lia. }
  zstep. zstep. if_cases HT; [notrap HT|].
  do 5 zstep.
  eapply evt_cut; [eapply BCMP_C | xpost].
  { rewrite unsigned_lit by lia. apply (bt_sub _ j nl); [exact BT|lia]. }
  { rewrite unsigned_lit by lia. apply (bt_sub _ p1 nl); [exact BT|lia]. }
  { rewrite unsigned_lit by lia. rewrite length_firstn, length_skipn. lia. }
  { rewrite unsigned_lit by lia. rewrite length_firstn, length_skipn. lia. }
  { eassumption. }
  { rewrite sp_u2. eassumption. }
  rewrite !zbytes_firstn, !zbytes_skipn in POST. rename POST into P1.
  do 3 zstep.
  zstep. if_cases HC1; zc HC1.
  - assert (HZ : zl_eqb (firstn nl (skipn j tt)) (firstn nl (skipn p1 tt)) = false).
    { destruct (zl_eqb (firstn nl (skipn j tt)) (firstn nl (skipn p1 tt))) eqn:E; [|reflexivity].
        apply zl_eqb_eq, P1 in E. contradiction. }
    eapply FAIL; [|mi|exact FR]. rewrite TA, HZ. reflexivity.
  - apply P1 in HC1. clear P1.
    assert (Z1 : zl_eqb (firstn nl (skipn j tt)) (firstn nl (skipn p1 tt)) = true) by (apply zl_eqb_eq; exact HC1).
    pose proof (rdt _ (j + nl) BT ltac:(lia)) as R1. pose proof (tb_range tb (j + nl)) as BR1.
    zstep. if_cases HT2; [notrap HT2|].
    zstep. zstep. cbv beta. rewrite tbyte_val. zstep.
    if_cases HC2; zc HC2.
    + eapply FAIL; [|mi|exact FR]. rewrite TA, Z1, (proj2 (Z.eqb_neq _ _) HC2). reflexivity.
    + assert (Z2 : (byte_at tt (j + nl) =? 58) = true) by (apply Z.eqb_eq; exact HC2).
      zstep. if_cases HT3; [notrap HT3|].
      do 4 zstep.
      eapply evt_cut; [eapply BCMP_C | xpost].
      { rewrite (ulit _ (bv_unsigned tx + Z.of_nat (j + nl + 1))) by lia.
        apply (bt_sub _ (j + nl + 1) (length ub - o)); [exact BT|lia]. }
      { rewrite (ulit _ (bv_unsigned ux + Z.of_nat o)) by lia. apply (bu_sub _ o (length ub - o)); [exact BU|lia]. }
      { rewrite (ulit _ (Z.of_nat (length ub) - Z.of_nat o)) by lia. rewrite length_firstn, length_skipn. lia. }
      { rewrite (ulit _ (Z.of_nat (length ub) - Z.of_nat o)) by lia. rewrite length_firstn, length_skipn. lia. }
      { eassumption. }
      { rewrite sp_u2. eassumption. }
      rewrite !zbytes_firstn, !zbytes_skipn in POST.
      rewrite (firstn_all2 (n := (length ub - o)%nat) (skipn o uu)) in POST by (rewrite Lloc; lia).
      rename POST into P2.
      do 3 zstep.
      zstep. if_cases HC3; zc HC3.
      * apply P2 in HC3. clear P2.
        assert (Z3 : zl_eqb (firstn (length ub - o) (skipn (j + nl + 1) tt)) (skipn o uu) = true)
          by (apply zl_eqb_eq; exact HC3).
        rewrite Z1, Z2, Z3 in TA. cbn [andb] in TA.
        zstep. if_cases HC4; zc HC4.
        -- assert (j = 0)%nat by lia. subst j.
           eapply (tk_next 0 nl o); [lia|lia|mi|exact FR| |].
           ++ intros Hn. apply KT. apply (token_true_of _ _ _ 0). rewrite TA. exact Hn.
           ++ intros Hn y10 y11 y12. eapply FAIL; [|mi|exact FR]. rewrite TA. exact Hn.
        -- destruct j as [|j']; [lia|].
           eapply (tk_prev j'); [lia|weq|mi|exact FR| |].
           ++ intros Hp y10 y11 y12. eapply (tk_next (S j') nl o); [lia|lia|mi|exact FR| |].
              ** intros Hn. apply KT. apply (token_true_of _ _ _ (S j')). rewrite TA, Hp. exact Hn.
              ** intros Hn y10' y11' y12'. eapply FAIL; [|mi|exact FR]. rewrite TA, Hp. exact Hn.
           ++ intros Hp y10 y11 y12. eapply FAIL; [|mi|exact FR]. rewrite TA, Hp. reflexivity.
      * assert (HZ : zl_eqb (firstn (length ub - o) (skipn (j + nl + 1) tt)) (skipn o uu) = false).
        { destruct (zl_eqb (firstn (length ub - o) (skipn (j + nl + 1) tt)) (skipn o uu)) eqn:E; [|reflexivity].
          apply zl_eqb_eq, P2 in E. contradiction. }
        eapply FAIL; [|mi|exact FR]. rewrite TA, Z1, Z2, HZ. reflexivity.
Qed.

Lemma cstr0t : forall m k, bytes_at rsegs m (bv_unsigned tx) (tb ++ Z_to_bv 8 0 :: ts) -> (k <= length tb)%nat ->
  cstr0 m (bv_unsigned tx + Z.of_nat k) (skipn k tb).
Proof. intros. eapply cstr0_t; eassumption. Qed.
Lemma cstrt : forall m k, bytes_at rsegs m (bv_unsigned tx) (tb ++ Z_to_bv 8 0 :: ts) -> (k <= length tb)%nat ->
  cstr_at m (bv_unsigned tx + Z.of_nat k) (skipn k tb) ts.
Proof. intros. eapply cstr_t; eassumption. Qed.
Lemma cstru : forall m k, bytes_at rsegs m (bv_unsigned ux) (ub ++ Z_to_bv 8 0 :: us) -> (k <= length ub)%nat ->
  cstr_at m (bv_unsigned ux + Z.of_nat k) (skipn k ub) us.
Proof. intros. eapply cstr_u; eassumption. Qed.
Lemma cstr0u : forall m, bytes_at rsegs m (bv_unsigned ux) (ub ++ Z_to_bv 8 0 :: us) -> cstr0 m (bv_unsigned ux) ub.
Proof. intros. eapply cstr0_u; eassumption. Qed.

Definition KPC (k d : nat) : Prop :=
  forall m j1 j2 j3 (x1 x5 x6 x7 x9 x10 x11 x12 x13 x17 x20 x21 x24 x25 x27 x28 x29 x30 x31 x23 : word),
  x23 = Z_to_bv 64 (Z.of_nat k) ->
  MIx m -> rw_cells rsegs m (bv_unsigned sp + -240) (FRM d j1 j2 j3) ->
  evt rsegs Qx (XS 0x13958 x1 x5 x6 x7 x9 x10 x11 x12 x13 x17 x20 x21 x23 x24 x25 x27 x28 x29 x30 x31 m).

Definition KONT (i d : nat) : Prop := forall i' d', sstep tt uu i d = SCont i' d' -> KPC i' d'.
Definition KRET (i d : nat) : Prop := forall r, sstep tt uu i d = SRet r -> r = names tt uu.

Lemma match_run : forall i d p1 p2 p3 o m j1 j2 j3 (x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x20 x21 x23 x24
    x25 x27 x28 x29 x30 x31 : word),
  decl tt i = DFound p1 (p2 - p1) (S p3) o (S p3 + o) -> (p1 <= p2)%nat -> (p2 < p3)%nat ->
  (S p3 + o < length tb)%nat -> (d <= 16)%nat ->
  x10 = Z_to_bv 64 (bv_unsigned tx + 1 + Z.of_nat p3 + Z.of_nat o) ->
  x27 = Z_to_bv 64 (bv_unsigned tx + Z.of_nat p3 + 1) -> x23 = x27 ->
  x9 = Z_to_bv 64 (bv_unsigned ux + -1 - (bv_unsigned tx + Z.of_nat p3)) ->
  x20 = Z_to_bv 64 (bv_unsigned tx + Z.of_nat p1) -> x21 = Z_to_bv 64 (Z.of_nat (p2 - p1)) ->
  x24 = Z_to_bv 64 (1 + Z.of_nat (p2 - p1)) -> x25 = Z_to_bv 64 (bv_unsigned tx + 1 + Z.of_nat (p2 - p1)) ->
  MIx m -> rw_cells rsegs m (bv_unsigned sp + -240) (FRM d j1 j2 j3) -> KONT i d -> KRET i d ->
  evt rsegs Qx (MST x1 SPV gp tp x5 x6 x7 (Z_to_bv 64 6) x9 x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 5)
    (Z_to_bv 64 66693) x20 x21 (Z_to_bv 64 (-1)) x23 x24 x25 (Z_to_bv 64 32) x27 x28 x29 x30 x31 0x1390c m).
Proof.
  intros i d p1 p2 p3 o m j1 j2 j3 x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x20 x21 x23 x24 x25 x27 x28 x29 x30
    x31
    Hdc Hp12 Hp23 Hcl Hd E10 E27 E23 E9 E20 E21 E24 E25 HM FR KO KR.
  subst x23. subst x10 x27 x9 x20 x21 x24 x25.
  pose proof HM as HM0. destruct HM as (BT & BU & PF & MEM & ST & MU & WM).
  pose proof (lxt tx) as LXT0. pose proof (lxu ux) as LXU0.
  set (nl := (p2 - p1)%nat) in *.
  assert (Hss : sstep tt uu i d = if matches tt uu (S p3) o then if (16 <? S d)%nat then SRet 1
     else if token tt (firstn nl (skipn p1 tt)) (skipn o uu) then SRet 1 else SCont (S p3 + o) (S d)
     else SCont (S p3 + o) d).
  { unfold sstep. rewrite Hdc. reflexivity. }
  assert (KB : matches tt uu (S p3) o = false -> KPC (S p3 + o) d).
  { intros Hm. apply KO. rewrite Hss, Hm. reflexivity. }
  zstep. zstep. zstep. zstep. if_cases HC; zc HC.
  - assert (K := KB ltac:(unfold matches; rewrite (proj2 (Nat.ltb_ge _ _)) by (rewrite (len_uu ub); lia);
      reflexivity)).
    do 4 zstep. unfold KPC in K. eapply K; [weq|exact HM0|exact FR].
  - do 5 zstep.
    eapply evt_cut; [eapply STRNCMP_C | xpost].
    { apply cstr0u. exact BU. }
    { rewrite (ulit _ (bv_unsigned tx + Z.of_nat (S p3))) by lia. apply cstr0t; [exact BT|lia]. }
    { eassumption. }
    { rewrite sp_u2. eassumption. }
    rewrite (ulit _ (Z.of_nat o)) in POST by lia. rewrite Nat2Z.id, zbytes_skipn in POST.
    rewrite (firstn_app_le uu) in POST by (rewrite (len_uu ub); lia).
    rewrite (firstn_app_le (skipn (S p3) tt)) in POST by (rewrite length_skipn, (len_tt tb); lia).
    rename POST into PN.
    zstep. if_cases HC2; zc HC2.
    + apply PN in HC2. clear PN.
      do 3 zstep. if_cases HT; [notrap HT|].
      do 3 zstep.
      eapply evt_cut; [eapply PLAIN_C | xpost].
      { rewrite (ulit _ (bv_unsigned ux + Z.of_nat o)) by lia. apply cstru; [exact BU|lia]. }
      { eassumption. }
      { rewrite sp_u2. eassumption. }
      { unfold PLAIN_K. rewrite sp_u2. lia. }
      { unfold off_stack, PLAIN_K. rewrite sp_u2, (ulit _ (bv_unsigned ux + Z.of_nat o)) by lia.
        rewrite length_skipn. lia. }
      rewrite zbytes_skipn in POST.
      destruct (plain_name (skipn o uu)) eqn:Hpl; subst.
      * assert (Hmt : matches tt uu (S p3) o = true).
        { unfold matches. rewrite (proj2 (Nat.ltb_lt _ _)) by (rewrite (len_uu ub); lia). rewrite HC2, zl_eqb_refl, Hpl.
          reflexivity. }
        zstep. if_cases HC3; zc HC3; [lia|].
        do 5 zstep. if_cases HC4; zc HC4.
        -- ret_epi FR. apply KR. rewrite Hss, Hmt. rewrite (proj2 (Nat.ltb_lt _ _)) by lia. reflexivity.
        -- assert (H16 : (16 <? S d)%nat = false) by (apply Nat.ltb_ge; lia).
           do 3 zstep.
           eapply evt_cut; [eapply STRLEN_C | xpost].
           { rewrite (ulit _ (bv_unsigned ux + Z.of_nat o)) by lia. apply cstru; [exact BU|lia]. }
           { eassumption. }
           { rewrite sp_u2. eassumption. }
           subst. rewrite length_skipn, Nat2Z.inj_sub by lia.
           do 4 zstep.
           eapply evt_cut; [eapply STRLEN_C | xpost].
           { replace (bv_unsigned tx) with (bv_unsigned tx + Z.of_nat 0) by lia. apply cstrt; [exact BT|lia]. }
           { eassumption. }
           { rewrite sp_u2. eassumption. }
           subst. change (skipn 0 tb) with tb.
           do 4 zstep. if_cases HC5; zc HC5.
           ++ do 9 zstep.
              lazymatch type of FR with
              | rw_cells _ _ _ (CB 8 ?j0 :: C8 ?c8 :: C8 ?c16 :: C8 ?c24 :: C8 ?c32 :: _ :: _ :: C8 ?c56 :: _ :: C8 ?c72
                  :: _ :: C8 ?c88 :: _) =>
                  eapply (token_run _ 0 p1 nl o _ c8 c16 c24 c32 c56 c72 c88 j0)
              end; [reflexivity|lia|lia|lia|intros; lia|weq..|mi|exact FR| |].
              ** intros Htk. apply KR. rewrite Hss, Hmt, H16, Htk. reflexivity.
              ** intros Htk m' y1 y5 y6 y7 y9 y10 y11 y12 y13 y17 y20 y21 y23 y24 y25 y27 y28 y29 y30 y31 HM' FR'.
                 do 3 zstep.
                 merge_at FR' 0%nat 5%nat. merge_at FR' 5%nat 1%nat. merge_at FR' 7%nat 1%nat.
                 replace (Z.of_nat d + 1) with (Z.of_nat (S d)) in FR' by lia.
                 assert (K := KO (S p3 + o)%nat (S d) ltac:(rewrite Hss, Hmt, H16, Htk; reflexivity)).
                 unfold KPC in K. eapply K; [weq|exact HM'|exact FR'].
           ++ assert (Htk : token tt (firstn nl (skipn p1 tt)) (skipn o uu) = false).
              { apply (token_false_of _ _ _ 0); [intros; lia|].
                rewrite length_firstn, !length_skipn, (len_tt tb), (len_uu ub). lia. }
              do 7 zstep.
              merge_at FR 0%nat 2%nat. merge_at FR 5%nat 1%nat. merge_at FR 7%nat 1%nat.
              replace (Z.of_nat d + 1) with (Z.of_nat (S d)) in FR by lia.
              assert (K := KO (S p3 + o)%nat (S d) ltac:(rewrite Hss, Hmt, H16, Htk; reflexivity)).
              unfold KPC in K. eapply K; [weq|mi|exact FR].
      * zstep. if_cases HC3; zc HC3; [|lia].
        do 6 zstep.
        merge_at FR 0%nat 2%nat. merge_at FR 5%nat 1%nat.
        assert (K := KB ltac:(unfold matches; rewrite Hpl; apply andb_false_r)). unfold KPC in K.
        eapply K; [weq|mi|exact FR].
    + assert (HZ : zl_eqb (firstn o (skipn (S p3) tt)) (firstn o uu) = false).
      { destruct (zl_eqb _ _) eqn:E; [|reflexivity]. apply zl_eqb_eq in E. symmetry in E. apply PN in E.
        contradiction. }
      do 6 zstep.
      merge_at FR 5%nat 1%nat.
      assert (K := KB ltac:(unfold matches; rewrite HZ, andb_false_r; reflexivity)). unfold KPC in K.
      eapply K; [weq|mi|exact FR].
Qed.

Lemma decl_run : forall i a d m j1 j2 j3 (x1 x5 x6 x7 x9 x10 x11 x12 x13 x17 x20 x21 x23 x24 x25 x27 x28 x29 x30
    x31 : word),
  head tt i = Some (i + a)%nat -> (i < length tb)%nat -> (d <= 16)%nat ->
  x9 = Z_to_bv 64 (bv_unsigned tx + Z.of_nat i) -> x10 = Z_to_bv 64 (Z.of_nat a) -> x23 = Z_to_bv 64 (Z.of_nat i) ->
  MIx m -> rw_cells rsegs m (bv_unsigned sp + -240) (FRM d j1 j2 j3) -> KONT i d -> KRET i d ->
  evt rsegs Qx (XS 0x1381c x1 x5 x6 x7 x9 x10 x11 x12 x13 x17 x20 x21 x23 x24 x25 x27 x28 x29 x30 x31 m).
Proof.
  intros i a d m j1 j2 j3 x1 x5 x6 x7 x9 x10 x11 x12 x13 x17 x20 x21 x23 x24 x25 x27 x28 x29 x30 x31
    Hh Hi Hd E9 E10 E23 HM FR KO KR. subst x9 x10 x23.
  pose proof HM as HM0. destruct HM as (BT & BU & PF & MEM & ST & MU & WM).
  pose proof (head_le _ _ _ Hh) as Hp0. rewrite (len_tt tb) in Hp0.
  assert (NONE : decl tt i = DNone -> KPC i d).
  { intros Hd'. apply KO. unfold sstep. rewrite Hd'. reflexivity. }
  set (p0 := (i + a)%nat) in *.
  pose proof (rdt m p0 BT Hp0) as R0. pose proof (tb_range tb p0) as BR0.
  set (p1 := (p0 + count_while is_space (skipn p0 tt))%nat).
  set (p2 := (p1 + count_while name_ok (skipn p1 tt))%nat).
  set (p3 := (S p2 + count_while is_space (skipn (S p2) tt))%nat).
  assert (Hp1 : (p1 <= length tb)%nat).
  { pose proof (cw_le is_space (skipn p0 tt)) as X. rewrite length_skipn, (len_tt tb) in X. unfold p1. lia. }
  assert (Hp2 : (p1 <= p2 <= length tb)%nat).
  { pose proof (cw_le name_ok (skipn p1 tt)) as X. rewrite length_skipn, (len_tt tb) in X. unfold p2. lia. }
  assert (SP0 : is_space (byte_at tt p0) = true -> forall y11 y12 y20 : word,
    y20 = Z_to_bv 64 (bv_unsigned tx + Z.of_nat p0) ->
    evt rsegs Qx (XS 0x1382c x1 x5 x6 x7 (Z_to_bv 64 (bv_unsigned tx + Z.of_nat i)) (Z_to_bv 64 (Z.of_nat a)) y11 y12
      x13 x17 y20 x21 (Z_to_bv 64 (Z.of_nat i)) x24 x25 x27 x28 x29 x30 x31 m)).
  { intros Hs z11 z12 z20 E20. subst z20.
    do 5 zstep.
    eapply (sp1 _ p0 p1 m); [reflexivity|lia|reflexivity|exact BT|weq|weq|weq|weq|].
    intros w9 w10 w11 w12 w20 w27 E20 E10 E27 E9 E11. subst w9 w10 w11 w20 w27.
    do 3 zstep.
    eapply (nl _ p1 p1 p2 m); [reflexivity|lia|lia|reflexivity|exact BT|weq..| |].
    - intros H58 v9 v10 v11 v12 v13 v21 v24 v25 v27.
      assert (K := NONE (decl_colon_none tt i p0 p1 p2 Hh Hs eq_refl eq_refl H58)). unfold KPC in K.
      eapply K; [weq|exact HM0|exact FR].
    - intros H58 v9 v10 v11 v12 v13 v21 v24 v25 v27 E21 E24 E25 E11 E10 E27 E9.
      subst v21 v24 v25 v11 v10 v27 v9.
      assert (Hp2' : (p2 < length tb)%nat) by (apply nz_lt; lia).
      zstep. if_cases HT; [notrap HT|].
      eapply (sp2 _ (S p2) p3 m); [reflexivity|lia|reflexivity|exact BT|weq|weq|weq| |].
      + intros H60 u9 u10 u11 u12 u27.
        assert (K := NONE (decl_lt_none tt i p0 p1 p2 p3 Hh Hs eq_refl eq_refl H58 eq_refl H60)). unfold KPC in K.
        eapply K; [weq|exact HM0|exact FR].
      + intros H60 u9 u10 u11 u12 u27 E10 E27 E9. subst u10 u27 u9.
        assert (Hp3 : (p3 < length tb)%nat) by (apply nz_lt; lia).
        assert (Hp23 : (p2 < p3)%nat) by (unfold p3; lia).
        zstep. if_cases HT2; [notrap HT2|].
        do 4 zstep.
        eapply evt_cut; [eapply STRCHR_C | xpost].
        { rewrite (ulit _ (bv_unsigned tx + Z.of_nat (S p3))) by lia. apply cstrt; [exact BT|lia]. }
        { rewrite unsigned_lit by lia. lia. }
        { eassumption. }
        { rewrite sp_u2. eassumption. }
        { unfold STRCHR_K. rewrite sp_u2. lia. }
        { unfold off_stack, STRCHR_K. rewrite sp_u2, (ulit _ (bv_unsigned tx + Z.of_nat (S p3))) by lia.
          rewrite length_skipn. lia. }
        change (bv_unsigned (Z_to_bv 64 62)) with 62 in POST. rewrite zbytes_skipn in POST.
        destruct (find_idx (fun x => x =? 62) (skipn (S p3) tt)) as [o|] eqn:Ef; subst.
        * pose proof (find_idx_some _ _ _ Ef) as (Ho & _ & _). rewrite length_skipn, (len_tt tb) in Ho.
          rewrite unsigned_lit by lia.
          zstep. if_cases HC; zc HC; [lia|].
          eapply (match_run i d p1 p2 p3 o); [|lia|lia|lia|lia|weq..|mi|exact FR|exact KO|exact KR].
          eapply (decl_found tt i p0 p1 p2 p3 o); [exact Hh|exact Hs|reflexivity|reflexivity|exact H58|reflexivity|
            exact H60|exact Ef].
        * zstep. if_cases HC; zc HC; [|lia]. ret_epi FR.
          apply KR. unfold sstep.
          rewrite (decl_cut tt i p0 p1 p2 p3 Hh Hs eq_refl eq_refl H58 eq_refl H60 Ef). reflexivity. }
  zstep. zstep. cbv beta. rewrite tbyte_val. zstep. zstep. if_cases HC.
  - zstep. if_cases HC2.
    + eapply SP0; [|weq]. apply bq in HC2. bdec (byte_at tt p0) HC2. exact BR0.
    + assert (HS : is_space (byte_at tt p0) = false).
      { apply negb_true_iff. bjoin HC HC2 HJ. bdec (byte_at tt p0) HJ. exact BR0. }
      zstep. assert (K := NONE (decl_sp_none tt i p0 Hh HS)). unfold KPC in K. eapply K; [weq|mi|exact FR].
  - eapply SP0; [|weq]. apply bq in HC. bdec (byte_at tt p0) HC. exact BR0.
Qed.

Lemma body : forall i d m j1 j2 j3 (x1 x5 x6 x7 x9 x10 x11 x12 x13 x17 x20 x21 x23 x24 x25 x27 x28 x29 x30
    x31 : word),
  (i < length tb)%nat -> (d <= 16)%nat -> x9 = Z_to_bv 64 (bv_unsigned tx + Z.of_nat i) ->
  x23 = Z_to_bv 64 (Z.of_nat i) ->
  MIx m -> rw_cells rsegs m (bv_unsigned sp + -240) (FRM d j1 j2 j3) -> KONT i d -> KRET i d ->
  evt rsegs Qx (XS 0x13780 x1 x5 x6 x7 x9 x10 x11 x12 x13 x17 x20 x21 x23 x24 x25 x27 x28 x29 x30 x31 m).
Proof.
  intros i d m j1 j2 j3 x1 x5 x6 x7 x9 x10 x11 x12 x13 x17 x20 x21 x23 x24 x25 x27 x28 x29 x30 x31
    Hi Hd E9 E23 HM FR KO KR. subst x9 x23.
  pose proof HM as HM0. destruct HM as (BT & BU & PF & MEM & ST & MU & WM).
  assert (NONE : head tt i = None -> KPC i d).
  { intros Hh. apply KO. unfold sstep, decl. rewrite Hh. reflexivity. }
  pose proof (rdt m i BT ltac:(lia)) as R1. pose proof (tb_range tb i) as BR.
  pose proof (tb_nz tb NT i Hi) as BNZ.
  assert (KN0 : ci_eqb (firstn 6 (skipn i tt)) prefix_lc = false ->
    ((byte_at tt i =? 64) && zl_eqb (firstn 6 (skipn (S i) tt)) prefix_lc) = false -> KPC i d).
  { intros H1 H2. apply NONE. unfold head. rewrite H2. cbv iota. rewrite H1. reflexivity. }
  zstep. cbv beta. rewrite tbyte_val. zstep. zstep. if_cases HC; zc HC.
  - zstep. if_cases HT; [notrap HT|].
    do 4 zstep.
    eapply evt_cut; [eapply STRNCMP_C | xpost].
    { rewrite (ulit _ (bv_unsigned tx + Z.of_nat (S i))) by lia. apply cstr0t; [exact BT|lia]. }
    { rewrite unsigned_lit by lia. apply cstr0_pf. exact PF. }
    { eassumption. }
    { rewrite sp_u2. eassumption. }
    rewrite ncmp6, zbytes_skipn in POST.
    do 4 zstep. if_cases HC2; zc HC2.
    + apply POST in HC2.
      assert (Hi7 : (S i + 6 <= length tb)%nat).
      { pose proof HC2 as X. apply (f_equal (@length Z)) in X. rewrite length_firstn, length_skipn, (len_tt tb) in X.
        cbn [length prefix_lc] in X. lia. }
      zstep. zstep. if_cases HT2; [notrap HT2|]. zstep.
      eapply (decl_run i 7 d); [|lia|lia|weq|weq|weq|mi|exact FR|exact KO|exact KR].
      unfold head. rewrite HC, Z.eqb_refl. cbn [andb]. rewrite (proj2 (zl_eqb_eq _ _) HC2). reflexivity.
    + zstep. zstep.
      assert (HZ : zl_eqb (firstn 6 (skipn (S i) tt)) prefix_lc = false).
      { destruct (zl_eqb _ _) eqn:E; [|reflexivity]. apply zl_eqb_eq, POST in E. contradiction. }
      eapply (pw 0 i d); [lia|lia|intros; lia|weq|weq|mi|exact FR| |].
      * intros Hci. exfalso. apply ci6 with (k := 0%nat) in Hci; [|lia]. rewrite Nat.add_0_r, HC in Hci.
        vm_compute in Hci. discriminate Hci.
      * intros Hci y10 y11 y12 y13.
        assert (K := KN0 Hci ltac:(rewrite HZ; apply andb_false_r)). unfold KPC in K. eapply K; [weq|mi|exact FR].
  - zstep. if_cases HC2; zc HC2; [lia|].
    do 3 zstep.
    assert (H64 : ((byte_at tt i =? 64) && zl_eqb (firstn 6 (skipn (S i) tt)) prefix_lc) = false).
    { rewrite (proj2 (Z.eqb_neq _ _) HC). reflexivity. }
    eapply (pw 0 i d); [lia|lia|intros; lia|weq|weq|mi|exact FR| |].
    + intros Hci y10 y11 y12 y13.
      assert (Hi6 : (i + 6 <= length tb)%nat).
      { pose proof Hci as X. apply ci_len in X. rewrite length_firstn, length_skipn, (len_tt tb) in X.
        cbn [length prefix_lc] in X. lia. }
      assert (DR : (match i with O => true | S i' => is_space (byte_at tt i') end) = true -> forall z10 z11 z12 z13,
        evt rsegs Qx (XS 0x13800 x1 x5 x6 x7 (Z_to_bv 64 (bv_unsigned tx + Z.of_nat i)) z10 z11 z12 z13 x17 x20 x21
          (Z_to_bv 64 (Z.of_nat i)) x24 x25 x27 x28 x29 x30 x31 m)).
      { intros Hp z10 z11 z12 z13. zstep. zstep. if_cases HT; [notrap HT|]. zstep. zstep.
        eapply (decl_run i 6 d); [|lia|lia|weq|weq|weq|mi|exact FR|exact KO|exact KR].
        unfold head. rewrite H64, Hci, Hp. reflexivity. }
      zstep. if_cases HC3; zc HC3.
      * assert (i = 0)%nat by lia. subst i. apply DR. reflexivity.
      * destruct i as [|i']; [lia|].
        pose proof (rdt m i' BT ltac:(lia)) as R2. pose proof (tb_range tb i') as BR2.
        zstep. zstep. if_cases HT; [notrap HT|].
        zstep. cbv beta. rewrite tbyte_val. zstep. zstep. if_cases HC4.
        -- zstep. if_cases HC5.
           ++ apply DR. cbv beta iota. apply bq in HC5. bdec (byte_at tt i') HC5. exact BR2.
           ++ zstep.
              assert (HS : is_space (byte_at tt i') = false).
              { apply negb_true_iff. bjoin HC4 HC5 HJ. bdec (byte_at tt i') HJ. exact BR2. }
              assert (K := NONE ltac:(unfold head; rewrite H64, Hci; cbv iota; rewrite HS; reflexivity)).
              unfold KPC in K. eapply K; [weq|mi|exact FR].
        -- apply DR. cbv beta iota. apply bq in HC4. bdec (byte_at tt i') HC4. exact BR2.
    + intros Hci y10 y11 y12 y13. assert (K := KN0 Hci H64). unfold KPC in K. eapply K; [weq|mi|exact FR].
Qed.

Lemma ml : forall e i d f m j1 j2 j3 (x1 x5 x6 x7 x9 x10 x11 x12 x13 x17 x20 x21 x23 x24 x25 x27 x28 x29 x30
    x31 : word),
  e = (length tb - i)%nat -> (i <= length tb)%nat -> (d <= 16)%nat -> (length tb - i < f)%nat ->
  names tt uu = scan tt uu i d f -> x9 = Z_to_bv 64 (bv_unsigned tx + Z.of_nat i) -> x23 = Z_to_bv 64 (Z.of_nat i) ->
  MIx m -> rw_cells rsegs m (bv_unsigned sp + -240) (FRM d j1 j2 j3) ->
  evt rsegs Qx (XS 0x13780 x1 x5 x6 x7 x9 x10 x11 x12 x13 x17 x20 x21 x23 x24 x25 x27 x28 x29 x30 x31 m).
Proof.
  intros e. induction e as [e IH] using lt_wf_ind.
  intros i d f m j1 j2 j3 x1 x5 x6 x7 x9 x10 x11 x12 x13 x17 x20 x21 x23 x24 x25 x27 x28 x29 x30 x31
    Ee Hi Hd Hf HR E9 E23 HM FR.
  destruct f as [|f]; [lia|].
  destruct (Nat.eq_dec i (length tb)) as [Ei|Ei].
  - subst x9 x23. pose proof HM as HM0. destruct HM as (BT & BU & PF & MEM & ST & MU & WM).
    pose proof (rdt m i BT ltac:(lia)) as R.
    assert (B0 : byte_at tt i = 0) by (apply byte_at_ge; rewrite (len_tt tb); lia).
    zstep. cbv beta. rewrite tbyte_val, B0. zstep. zstep. if_cases HC; zc HC; [lia|].
    zstep. if_cases HC2; zc HC2; [|lia]. ret_epi FR.
    rewrite HR, scan_end by (rewrite (len_tt tb); lia). reflexivity.
  - eapply (body i d m j1 j2 j3); [lia|lia|exact E9|exact E23|exact HM|exact FR| |].
    + intros i' d' Hs. unfold KPC.
      intros m' j1' j2' j3' y1 y5 y6 y7 y9 y10 y11 y12 y13 y17 y20 y21 y24 y25 y27 y28 y29 y30 y31 y23 E23' HM' FR'.
      subst y23. destruct (sstep_cont tt uu i d i' d' ltac:(rewrite (len_tt tb); lia) Hd Hs) as [Hii' Hd'].
      rewrite (len_tt tb) in Hii'.
      zstep. zstep. zstep. zstep. if_cases HC; [|notrap HC].
      eapply (IH (length tb - S i')%nat ltac:(lia) (S i') d' f); [reflexivity|lia|lia|lia| |weq|weq|exact HM'|exact FR'].
      rewrite HR, scan_step by (rewrite (len_tt tb); lia). rewrite Hs. reflexivity.
    + intros r Hs. rewrite HR, scan_step by (rewrite (len_tt tb); lia). rewrite Hs. reflexivity.
Qed.

Lemma msetup : whole tt uu = false -> (length ub <> 0)%nat ->
  forall m j j' (y1 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16 y17 y18 y19 y20 y23 y24 y25 y26 y27 y28 y29 y30
    y31 : word),
  MIx m -> rw_cells rsegs m (bv_unsigned sp + -240) (CB 120 j :: C8 tx :: CB 8 j' :: SAVEDx) ->
  evt rsegs Qx (MST y1 SPV gp tp y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16 y17 y18 y19 y20 ux NN y23 y24 y25 y26
    y27 y28 y29 y30 y31 0x13704 m).
Proof.
  intros Hw Hu m j j' y1 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16 y17 y18 y19 y20 y23 y24 y25 y26 y27 y28 y29 y30
    y31 HM FR.
  destruct HM as (BT & BU & PF & MEM & ST & MU & WM). unfold SAVED in FR.
  do 31 zstep.
  eapply (ml (length tb - 0) 0 0 (S (length tt))); [reflexivity|lia|lia|rewrite (len_tt tb); lia| |
    symmetry; apply Z_to_bv_plus0|weq|mi|exact FR].
  unfold names. rewrite (len_uu ub). destruct (length ub =? 0)%nat eqn:E; [apply Nat.eqb_eq in E; contradiction|].
  rewrite Hw. reflexivity.
Qed.

End M.
