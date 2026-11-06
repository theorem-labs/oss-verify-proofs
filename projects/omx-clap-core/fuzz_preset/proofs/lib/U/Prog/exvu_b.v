From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Lib Require Import PropExec MState Mem Cells Step Exec Frame FP Tac Bytes ZBridge.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U Require Import Img0.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U Require MemNorm.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require Import PjTree PjGrammar.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Spec Require Import StrFun.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Import PjStruct ex_value_c ex_value_m.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog Require Import strtod_c ex_value_c ex_word_c ex_string_c strcmp_c bcmp_c memcpy_c ex_ws_c.
Import ListNotations.
Open Scope Z_scope.

Ltac lia1 := first [ (repeat match goal with H : _ \/ _ |- _ => clear H end); lia
                   | match goal with H : _ \/ _ |- _ =>
                       (repeat match goal with H' : _ \/ _ |- _ => tryif constr_eq H H' then fail else clear H' end);
                       lia end
                   | lia ].
Ltac slia ::= first [ exact I | repeat split; lia1 ].

Definition ev_hid (P : Prop) : Prop := P.
Ltac ev_stash := repeat match goal with H : ?T |- _ =>
  lazymatch T with
  | ev_hid _ => fail
  | _ \/ _ => change T with (ev_hid T) in H
  | _ <-> _ => change T with (ev_hid T) in H
  end end.

Definition ev_jl (w0 w1 w2 w3 w4 : word) : list byte := le8 w0 ++ le8 w1 ++ le8 w2 ++ le8 w3 ++ le8 w4.

Lemma ev_jl_len : forall w0 w1 w2 w3 w4, length (ev_jl w0 w1 w2 w3 w4) = 40%nat.
Proof. intros. unfold ev_jl. rewrite !length_app, !length_le8. reflexivity. Qed.

Lemma ev_le8 : forall bs : list byte, length bs = 8%nat -> le8 (le_bytes_to_word bs) = bs.
Proof.
  intros bs HL. unfold le8, word_to_le_bytes, le_bytes_to_word.
  rewrite unsigned_lit_wrap, (Z_to_le_bytes_mod 8 _ 64) by lia.
  rewrite <- HL. apply Z_to_le_bytes_to_Z.
Qed.

Lemma ev_jl_ex : forall j : list byte, length j = 40%nat -> exists w0 w1 w2 w3 w4, j = ev_jl w0 w1 w2 w3 w4.
Proof.
  intros j HL.
  exists (le_bytes_to_word (firstn 8 j)), (le_bytes_to_word (firstn 8 (skipn 8 j))),
    (le_bytes_to_word (firstn 8 (skipn 16 j))), (le_bytes_to_word (firstn 8 (skipn 24 j))),
    (le_bytes_to_word (firstn 8 (skipn 32 j))).
  unfold ev_jl. rewrite !ev_le8 by (rewrite length_firstn, ?length_skipn; lia).
  do 40 (destruct j as [|? j]; [cbn in HL; lia|]). destruct j; [reflexivity|cbn in HL; lia].
Qed.

Lemma ev_byte_range : forall b : byte, 0 <= bv_unsigned b < 256.
Proof. intros b. pose proof (bv_unsigned_in_range 8 b) as H. unfold bv_modulus in H. exact H. Qed.

Lemma ev_byte_all : forall (P : Z -> bool), forallb P (map Z.of_nat (seq 0 256)) = true ->
  forall b : byte, P (bv_unsigned b) = true.
Proof.
  intros P H b. rewrite forallb_forall in H. apply H. apply in_map_iff.
  pose proof (ev_byte_range b) as R.
  exists (Z.to_nat (bv_unsigned b)). split; [apply Z2Nat.id; lia | apply in_seq; lia].
Qed.

Lemma ev_ws_mask : forall b : byte, bv_unsigned b <= 32 ->
  (Z.land (Z.shiftr 4294977024 (bv_unsigned b mod 64)) 1 =? 0) = negb (ws (bv_unsigned b)).
Proof.
  intros b Hb.
  pose proof (ev_byte_all (fun z => implb (z <=? 32)
    (Bool.eqb (Z.land (Z.shiftr 4294977024 (z mod 64)) 1 =? 0) (negb (ws z)))) ltac:(vm_compute; reflexivity) b) as H.
  cbv beta in H. rewrite (proj2 (Z.leb_le _ _) Hb) in H. cbn [implb] in H. apply Bool.eqb_prop in H. exact H.
Qed.

Lemma ev_ws_big : forall b : byte, 32 < bv_unsigned b -> ws (bv_unsigned b) = false.
Proof.
  intros b Hb. unfold ws. repeat match goal with |- context [Z.eqb ?a ?c] => destruct (Z.eqb_spec a c) end;
  cbn [orb]; first [reflexivity | lia].
Qed.

Definition ev_X (x : list byte) (k : Z) : list Z := map bv_unsigned (skipn (Z.to_nat k) x).

Lemma ev_X_cons : forall x k, 0 <= k < Z.of_nat (length x) ->
  ev_X x k = bv_unsigned (nth (Z.to_nat k) x (Z_to_bv 8 0)) :: ev_X x (k + 1).
Proof.
  intros x k Hk. unfold ev_X. replace (Z.to_nat (k + 1)) with (S (Z.to_nat k)) by lia.
  assert (H : (Z.to_nat k < length x)%nat) by lia. clear Hk. revert H. generalize (Z.to_nat k) as n.
  induction x as [|a x IH]; intros n H; cbn in H; [lia|]. destruct n as [|n]; [reflexivity|].
  cbn [skipn nth]. apply IH. lia.
Qed.

Lemma ev_X_end : forall x k, Z.of_nat (length x) <= k -> ev_X x k = [].
Proof.
  intros x k Hk. unfold ev_X. rewrite skipn_all2 by lia. reflexivity.
Qed.

Lemma ev_X_len : forall x k, 0 <= k <= Z.of_nat (length x) -> Z.of_nat (length (ev_X x k)) = Z.of_nat (length x) - k.
Proof. intros x k Hk. unfold ev_X. rewrite length_map, length_skipn. lia. Qed.

Lemma ev_read_x : forall m x0 x k, bytes_at rsegs m x0 x -> 0 <= k < Z.of_nat (length x) ->
  ov_read_bytes rsegs m (wa (x0 + k)) 1 = Some [nth (Z.to_nat k) x (Z_to_bv 8 0)].
Proof.
  intros m x0 x k H Hk. rewrite (bytes_at_read rsegs m x0 x k 1 H) by lia.
  assert (Hn : (Z.to_nat k < length x)%nat) by lia. clear Hk H. revert Hn. generalize (Z.to_nat k) as n.
  induction x as [|a x IH]; intros n Hn; cbn in Hn; [lia|]. destruct n as [|n]; [reflexivity|].
  cbn [skipn nth]. apply IH. lia.
Qed.

Lemma ev_outside_dec : forall W z, outside W z \/ ~ outside W z.
Proof.
  induction W as [|[lo hi] W IH]; intros z; cbn [outside]; [left; exact I|].
  destruct (IH z) as [H|H]; [|right; intros [_ A]; exact (H A)].
  destruct (Z_le_dec lo z) as [H1|H1]; [destruct (Z_lt_dec z hi) as [H2|H2]|].
  - right. intros [A _]. lia.
  - left. split; [lia|exact H].
  - left. split; [lia|exact H].
Qed.

Lemma ev_not_outside : forall W z, ~ outside W z -> exists lo hi, In (lo, hi) W /\ lo <= z < hi.
Proof.
  induction W as [|[lo hi] W IH]; intros z H; cbn [outside] in H; [exfalso; exact (H I)|].
  destruct (Z_le_dec lo z) as [H1|H1]; [destruct (Z_lt_dec z hi) as [H2|H2]|].
  - exists lo, hi. split; [left; reflexivity|lia].
  - destruct (IH z) as (l & h & Hin & Hr); [intros Ho; apply H; split; [lia|exact Ho]|].
    exists l, h. split; [right; exact Hin|exact Hr].
  - destruct (IH z) as (l & h & Hin & Hr); [intros Ho; apply H; split; [lia|exact Ho]|].
    exists l, h. split; [right; exact Hin|exact Hr].
Qed.

Lemma ev_tm_munch : forall W m1 m2, OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.MemNorm.task_mem rsegs m1 -> munch W m1 m2 ->
  (forall a : word, ~ outside W (bv_unsigned a) -> wview rsegs m1 a <> None) -> OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.MemNorm.task_mem rsegs m2.
Proof.
  intros W m1 m2 TM MU HW a b Ha.
  destruct (ev_outside_dec W (bv_unsigned a)) as [Ho|Hi].
  - rewrite (MU a Ho) in Ha. exact (TM a b Ha).
  - specialize (HW a Hi). unfold wview in HW. destruct (m1 a) as [b1|] eqn:E.
    + exact (TM a b1 E).
    + destruct (find_segment rsegs (bv_unsigned a) 1) as [sg|] eqn:Ef; [left; congruence | contradiction].
Qed.

Lemma ev_wv_wr : forall m1 A n (a : word), wr_at rsegs m1 A n -> A <= bv_unsigned a < A + n -> wview rsegs m1 a <> None.
Proof.
  intros m1 A n a (_ & _ & H) Ha. rewrite <- (Z_to_bv_bv_unsigned a). specialize (H (bv_unsigned a - A) ltac:(lia)).
  replace (A + (bv_unsigned a - A)) with (bv_unsigned a) in H by lia. exact H.
Qed.

Lemma ev_wv_stk : forall m1 lo1 hi1 (a : word), stk rsegs m1 lo1 hi1 -> lo1 <= bv_unsigned a < hi1 ->
  wview rsegs m1 a <> None.
Proof.
  intros m1 lo1 hi1 a (_ & _ & H) Ha. rewrite <- (Z_to_bv_bv_unsigned a). exact (proj1 (H _ Ha)).
Qed.

Lemma ev_V_skip : forall d xs, ex_V d (skip xs) = ex_V d xs.
Proof.
  intros d xs. induction xs as [|b r IH]; [reflexivity|]. cbn [skip].
  destruct (ws b) eqn:E; [rewrite IH; symmetry; apply ex_V_ws; exact E|reflexivity].
Qed.

Lemma ev_wr_app : forall m1 A n1 n2, 0 <= n1 -> 0 <= n2 ->
  wr_at rsegs m1 A (n1 + n2) <-> wr_at rsegs m1 A n1 /\ wr_at rsegs m1 (A + n1) n2.
Proof.
  intros m1 A n1 n2 H1 H2. unfold wr_at. split.
  - intros (Ha & Hl & H). split; [split; [lia|split; [lia|intros i Hi; apply H; lia]]|].
    split; [lia|split; [lia|intros i Hi; replace (A + n1 + i) with (A + (n1 + i)) by lia; apply H; lia]].
  - intros [(Ha & Hl & H) (Ha2 & Hl2 & H2')]. split; [lia|split; [lia|]]. intros i Hi.
    destruct (Z_lt_dec i n1); [apply H; lia|]. replace (A + i) with (A + n1 + (i - n1)) by lia. apply H2'; lia.
Qed.

Lemma ev_rw_app : forall m1 A cs1 cs2,
  rw_cells rsegs m1 A (cs1 ++ cs2) <-> rw_cells rsegs m1 A cs1 /\ rw_cells rsegs m1 (A + Z.of_nat (cells_size cs1)) cs2.
Proof.
  intros m1 A cs1 cs2. unfold rw_cells, cells_at. split.
  - intros [[Hwf Hb] Hw]. apply cells_wf_app in Hwf as [W1 W2]. rewrite cells_bytes_app in Hb.
    apply bytes_at_app in Hb as [B1 B2].
    rewrite cells_size_app, Nat2Z.inj_add in Hw. apply ev_wr_app in Hw as [H1 H2]; try lia.
    rewrite (cells_bytes_length cs1 W1) in B2.
    split; [split; [split; assumption|exact H1]|split; [split; assumption|exact H2]].
  - intros [[[W1 B1] H1] [[W2 B2] H2]]. split; [split|].
    + apply cells_wf_app. split; assumption.
    + rewrite cells_bytes_app. apply bytes_at_app. split; [exact B1|]. rewrite (cells_bytes_length cs1 W1). exact B2.
    + rewrite cells_size_app, Nat2Z.inj_add. apply ev_wr_app; [lia|lia|split; assumption].
Qed.

Lemma ev_rec_iff : forall m1 q p e dep scr dl',
  ex_rec m1 q p e dep scr dl' <->
  rw_cells rsegs m1 q [C8 (Z_to_bv 64 p)] /\ rw_cells rsegs m1 (q + 8) [C8 (Z_to_bv 64 e)] /\
  rw_cells rsegs m1 (q + 16) [C4 (Z_to_bv 64 dep)] /\ rw_cells rsegs m1 (q + 24) [C8 (Z_to_bv 64 scr)] /\
  rw_cells rsegs m1 (q + 32) [C4 (Z_to_bv 64 dl')].
Proof.
  intros m1 q p e dep scr dl'. unfold ex_rec.
  change [C8 (Z_to_bv 64 p); C8 (Z_to_bv 64 e); C4 (Z_to_bv 64 dep)]
    with ([C8 (Z_to_bv 64 p)] ++ [C8 (Z_to_bv 64 e)] ++ [C4 (Z_to_bv 64 dep)]).
  change [C8 (Z_to_bv 64 scr); C4 (Z_to_bv 64 dl')] with ([C8 (Z_to_bv 64 scr)] ++ [C4 (Z_to_bv 64 dl')]).
  rewrite !ev_rw_app. cbn [cells_size csize Nat.add]. change (Z.of_nat 8) with 8.
  replace (q + 8 + 8) with (q + 16) by lia. replace (q + 24 + 8) with (q + 32) by lia. tauto.
Qed.

Lemma ev_sgn : forall z, 0 <= z < 2 ^ 63 -> bv_signed (Z_to_bv 64 z) = z.
Proof. intros z Hz. rewrite zb_signed, unsigned_lit by lia. destruct (Z.ltb_spec z (2 ^ 63)); lia. Qed.

Lemma ev_rw8_bytes : forall m1 A w, rw_cells rsegs m1 A [C8 w] -> bytes_at rsegs m1 A (le8 w).
Proof. intros m1 A w [[_ B] _]. cbn [cells_bytes cbytes] in B. rewrite app_nil_r in B. exact B. Qed.

Lemma ev_rw4_bytes : forall m1 A w, rw_cells rsegs m1 A [C4 w] -> bytes_at rsegs m1 A (le4 w).
Proof. intros m1 A w [[_ B] _]. cbn [cells_bytes cbytes] in B. rewrite app_nil_r in B. exact B. Qed.

Lemma ev_rw_wr : forall m1 A cs, rw_cells rsegs m1 A cs -> wr_at rsegs m1 A (Z.of_nat (cells_size cs)).
Proof. intros m1 A cs [_ W]. exact W. Qed.

Lemma ev_rw8_mk : forall m1 A w, bytes_at rsegs m1 A (le8 w) -> wr_at rsegs m1 A 8 -> rw_cells rsegs m1 A [C8 w].
Proof.
  intros m1 A w B W. split; [split; [exact (conj I I)|cbn [cells_bytes cbytes]; rewrite app_nil_r; exact B]|exact W].
Qed.

Lemma ev_rw4_mk : forall m1 A w, bytes_at rsegs m1 A (le4 w) -> wr_at rsegs m1 A 4 -> rw_cells rsegs m1 A [C4 w].
Proof.
  intros m1 A w B W. split; [split; [exact (conj I I)|cbn [cells_bytes cbytes]; rewrite app_nil_r; exact B]|exact W].
Qed.

Lemma ev_stk_wr : forall m1 a b, stk rsegs m1 a b -> a <= b -> wr_at rsegs m1 a (b - a).
Proof.
  intros m1 a b (H1 & H2 & H) Hab. split; [lia|split; [lia|]]. intros i Hi. exact (proj1 (H (a + i) ltac:(lia))).
Qed.

Lemma ev_stk_of : forall m1 A bs, bytes_at rsegs m1 A bs -> wr_at rsegs m1 A (Z.of_nat (length bs)) ->
  stk rsegs m1 A (A + Z.of_nat (length bs)).
Proof.
  intros m1 A bs B W. pose proof (stk_of_rw_cells rsegs m1 A [CB (length bs) bs]) as H.
  cbn [cells_size csize] in H. rewrite Nat.add_0_r in H. apply H.
  split; [split; [split; [reflexivity|exact I]|cbn [cells_bytes cbytes]; rewrite app_nil_r; exact B]|].
  cbn [cells_size csize]. rewrite Nat.add_0_r. exact W.
Qed.

Lemma ev_u64_rd : forall m1 a w, pj_u64 rsegs m1 a w -> ov_read_bytes rsegs m1 (wa a) 8 = Some (le8 (Z_to_bv 64 w)).
Proof.
  intros m1 a w [Hw B]. rewrite <- (Z.add_0_r a) at 1.
  rewrite (bytes_at_read rsegs m1 a _ 0 8 B) by (rewrite ?length_le8; lia). reflexivity.
Qed.

Lemma ev_u32_rd : forall m1 a w, pj_u32 rsegs m1 a w -> ov_read_bytes rsegs m1 (wa a) 4 = Some (le4 (Z_to_bv 64 w)).
Proof.
  intros m1 a w [Hw B]. rewrite <- (Z.add_0_r a) at 1.
  rewrite (bytes_at_read rsegs m1 a _ 0 4 B) by (rewrite ?length_le4; lia). reflexivity.
Qed.

Lemma ev_hdr : forall m1 L p t1 D1, pj_node rsegs m1 L p t1 D1 ->
  exists num str kids keys n cap, pj_hdr rsegs m1 p (tag t1) num str kids keys n cap.
Proof.
  intros m1 L p t1 D1 H. destruct t1; cbn [pj_node] in H;
    destruct H as (_ & _ & num & str & kids & keys & n & cap & Hh & _); exists num, str, kids, keys, n, cap; exact Hh.
Qed.

Lemma ev_sx32 : forall z, 0 <= z < 2 ^ 31 -> sx32 (Z_to_bv 64 z) = Z_to_bv 64 z.
Proof.
  intros z Hz. unfold sx32. rewrite unsigned_lit by lia. f_equal.
  unfold bv_swrap, bv_wrap. change (bv_half_modulus 32) with 2147483648. change (bv_modulus 32) with 4294967296.
  rewrite Z.mod_small by lia. lia.
Qed.

Lemma ev_tag_range : forall t1, 0 <= tag t1 <= 6.
Proof. destruct t1; cbn; lia. Qed.

Lemma ev_map_inj : forall l1 l2 : list Z, Forall (fun c => 0 <= c < 256) l1 -> Forall (fun c => 0 <= c < 256) l2 ->
  map (Z_to_bv 8) l1 = map (Z_to_bv 8) l2 -> l1 = l2.
Proof.
  induction l1 as [|a l1 IH]; intros [|b l2] H1 H2 E; cbn in E; try discriminate; [reflexivity|].
  assert (Eab : Z_to_bv 8 a = Z_to_bv 8 b) by congruence.
  assert (Er : map (Z_to_bv 8) l1 = map (Z_to_bv 8) l2) by congruence. apply Forall_cons_iff in H1 as [Ha H1]. apply Forall_cons_iff in H2 as [Hb H2].
  f_equal; [|apply IH; assumption].
  apply (f_equal (@bv_unsigned 8)) in Eab. rewrite !Z_to_bv_unsigned in Eab. unfold bv_wrap in Eab.
  change (bv_modulus 8) with 256 in Eab. rewrite !Z.mod_small in Eab by lia. exact Eab.
Qed.

Lemma ev_no0 : forall l : list Z, Forall (fun c => 0 < c < 256) l -> ~ In (Z_to_bv 8 0) (map (Z_to_bv 8) l).
Proof.
  intros l H Hin. apply in_map_iff in Hin as (c & E & Hc). rewrite Forall_forall in H. specialize (H c Hc).
  apply (f_equal (@bv_unsigned 8)) in E. rewrite !Z_to_bv_unsigned in E. unfold bv_wrap in E.
  change (bv_modulus 8) with 256 in E. rewrite !Z.mod_small in E by lia. lia.
Qed.

Lemma ev_bytes_X : forall x k, Forall (fun c => 0 <= c < 256) (ev_X x k).
Proof. intros x k. unfold ev_X. apply Forall_forall. intros c Hc. apply in_map_iff in Hc as (b & <- & _). apply ev_byte_range. Qed.

Lemma ev_map_Xb : forall x k, map (Z_to_bv 8) (ev_X x k) = skipn (Z.to_nat k) x.
Proof.
  intros x k. unfold ev_X. rewrite map_map. induction (skipn (Z.to_nat k) x) as [|b l IH]; [reflexivity|].
  cbn [map]. rewrite IH. f_equal. apply bv_eq. rewrite Z_to_bv_unsigned. apply bv_wrap_small. apply bv_unsigned_in_range.
Qed.

Lemma ev_wr_sub : forall m1 A n k, wr_at rsegs m1 A n -> 0 <= k <= n -> wr_at rsegs m1 A k.
Proof. intros m1 A n k (H1 & H2 & H) Hk. split; [lia|split; [lia|]]. intros i Hi. apply H. lia. Qed.

Lemma ev_tag4 : forall t1, tag t1 = 4 -> exists s', t1 = JStr s'.
Proof. intros [| | | ? ? | s' | ? | ?] H; cbn in H; try discriminate. exists s'. reflexivity. Qed.

Definition tkids (u : jv) : list (list Z * jv) :=
  match u with JArr ts => map (fun w => (@nil Z, w)) ts | JObj ms => ms | _ => [] end.

Lemma close_pdec : forall a b : list Z * jv, {a = b} + {a <> b}.
Proof.
  intros [n1 u1] [n2 u2].
  destruct (list_eq_dec Z.eq_dec n1 n2) as [<-|N]; [|right; congruence].
  destruct (jv_eq_dec u1 u2) as [<-|N]; [left; reflexivity|right; congruence].
Qed.

Lemma close_lneq : forall l1 l2 : list (list Z * jv), l1 <> l2 <-> (length l1 <> length l2 \/
  exists jj, (jj < length l1)%nat /\ (jj < length l2)%nat /\ nth jj l1 ([], JNull) <> nth jj l2 ([], JNull)).
Proof.
  intros l1 l2. split.
  - intros H. exact (list_neq_split _ close_pdec ([], JNull) l1 l2 H).
  - intros [L|(jj & _ & _ & N)] E; subst l2; [exact (L eq_refl)|exact (N eq_refl)].
Qed.

Lemma close_map_snd : forall us : list (list Z * jv), Forall (fun nu => fst nu = []) us ->
  map (fun w => (@nil Z, w)) (map snd us) = us.
Proof.
  intros us. induction us as [|[nm w] us IH]; intros H; [reflexivity|].
  pose proof (Forall_inv H) as Hn. pose proof (Forall_inv_tail H) as Hf. cbn [fst] in Hn. subst nm.
  cbn [map snd]. rewrite (IH Hf). reflexivity.
Qed.

Lemma close_mk_eq : forall (u : jv) (o : bool) (us : list (list Z * jv)), tag u = 5 + Z.b2z o ->
  (o = false -> Forall (fun nu => fst nu = []) us) -> (u = mk o us <-> tkids u = us).
Proof.
  intros u o us Ht Hus. destruct o; destruct u as [| | | ? ? | ? | ts | ms]; cbn in Ht; try discriminate; cbn [mk tkids].
  - split; [intros E; injection E as E; exact E|intros ->; reflexivity].
  - specialize (Hus eq_refl). split.
    + intros E. injection E as ->. apply close_map_snd. exact Hus.
    + intros <-. clear Hus. f_equal. induction ts as [|w ts IH]; [reflexivity|]. cbn [map snd]. f_equal. exact IH.
Qed.

Lemma ev_mk_neq : forall (u : jv) (o : bool) (us : list (list Z * jv)), tag u = 5 + Z.b2z o ->
  (o = false -> Forall (fun nu => fst nu = []) us) ->
  (u <> mk o us <-> length (tkids u) <> length us \/
     exists jj, (jj < length (tkids u))%nat /\ (jj < length us)%nat /\
       nth jj (tkids u) ([], JNull) <> nth jj us ([], JNull)).
Proof.
  intros u o us Ht Hus. apply (iff_trans (B := tkids u <> us)); [|apply close_lneq].
  pose proof (close_mk_eq u o us Ht Hus) as E. split; intros N E1; apply N; apply E; exact E1.
Qed.

Lemma close_nth_arr : forall ts jj, nth jj (map (fun w => (@nil Z, w)) ts) ([], JNull) = ([], nth jj ts JNull).
Proof. intros ts jj. exact (map_nth (fun w => (@nil Z, w)) ts JNull jj). Qed.

Lemma close_items_nth : forall (P : Z -> jv -> list (Z * Z) -> Prop) l a Di jj, pj_items P a l Di ->
  (jj < length l)%nat -> exists Dj, P (a + 56 * Z.of_nat jj) (nth jj l JNull) Dj /\ incl Dj Di.
Proof.
  intros P l. induction l as [|w l IH]; intros a Di jj H Hj; cbn [length] in Hj; [lia|].
  cbn [pj_items] in H. destruct H as (D1 & D2 & -> & HP & HR). destruct jj as [|jj].
  - exists D1. split; [replace (a + 56 * Z.of_nat 0) with a by lia; exact HP|].
    intros b Hb. apply in_or_app. left. exact Hb.
  - destruct (IH (a + 56) D2 jj HR ltac:(lia)) as (Dj & HPj & Hinc). exists Dj. split.
    + replace (a + 56 * Z.of_nat (S jj)) with (a + 56 + 56 * Z.of_nat jj) by lia. exact HPj.
    + intros b Hb. apply in_or_app. right. apply Hinc. exact Hb.
Qed.

Lemma close_mems_nth : forall m1 L (P : Z -> jv -> list (Z * Z) -> Prop) l a ka Di jj,
  pj_mems rsegs m1 L P a ka l Di -> (jj < length l)%nat ->
  (exists Dj, P (a + 56 * Z.of_nat jj) (snd (nth jj l ([], JNull))) Dj /\ incl Dj Di) /\
  exists xk k, pj_u64 rsegs m1 (ka + 8 * Z.of_nat jj) xk /\ pj_cstr rsegs m1 L xk k (fst (nth jj l ([], JNull))) /\
    In (xk, k) Di.
Proof.
  intros m1 L P l. induction l as [|[nm w] l IH]; intros a ka Di jj H Hj; cbn [length] in Hj; [lia|].
  cbn [pj_mems] in H. destruct H as (xk & k & D1 & D2 & -> & Hx & Hc & HP & HR). destruct jj as [|jj].
  - cbn [nth fst snd]. split.
    + exists D1. split; [replace (a + 56 * Z.of_nat 0) with a by lia; exact HP|].
      intros b Hb. right. apply in_or_app. left. exact Hb.
    + exists xk, k. split; [replace (ka + 8 * Z.of_nat 0) with ka by lia; exact Hx|]. split; [exact Hc|].
      left. reflexivity.
  - destruct (IH (a + 56) (ka + 8) D2 jj HR ltac:(lia)) as ((Dj & HPj & Hinc) & (xk' & k' & Hx' & Hc' & Hin')).
    cbn [nth]. split.
    + exists Dj. split; [replace (a + 56 * Z.of_nat (S jj)) with (a + 56 + 56 * Z.of_nat jj) by lia; exact HPj|].
      intros b Hb. right. apply in_or_app. right. apply Hinc. exact Hb.
    + exists xk', k'. split; [replace (ka + 8 * Z.of_nat (S jj)) with (ka + 8 + 8 * Z.of_nat jj) by lia; exact Hx'|].
      split; [exact Hc'|]. right. apply in_or_app. right. exact Hin'.
Qed.

Lemma ev_node_cont : forall m1 L p (u : jv) D1 (o : bool), pj_node rsegs m1 L p u D1 -> tag u = 5 + Z.b2z o ->
  exists num kids keys cap,
    pj_hdr rsegs m1 p (tag u) num 0 kids keys (Z.of_nat (length (tkids u))) cap /\
    forall jj, (jj < length (tkids u))%nat ->
      Z.of_nat jj < cap /\ In (kids, 56 * cap) D1 /\
      (exists Dj, pj_node rsegs m1 L (kids + 56 * Z.of_nat jj) (snd (nth jj (tkids u) ([], JNull))) Dj /\ incl Dj D1) /\
      (o = true -> In (keys, 8 * cap) D1 /\ exists xk k, pj_u64 rsegs m1 (keys + 8 * Z.of_nat jj) xk /\
          pj_cstr rsegs m1 L xk k (fst (nth jj (tkids u) ([], JNull))) /\ In (xk, k) D1).
Proof.
  intros m1 L p u D1 o H Ht.
  destruct o; destruct u as [| | | ? ? | ? | ts | ms]; cbn in Ht; try discriminate; cbn [pj_node] in H;
    destruct H as (_ & _ & num & str & kids & keys & n & cap & Hh & HB).
  - destruct HB as (-> & -> & Hnc & Hcap & Di & -> & HM).
    exists num, kids, keys, cap. cbn [tkids]. split; [exact Hh|].
    intros jj Hj. destruct (Z.eqb_spec cap 0) as [E|_]; [lia|].
    destruct (close_mems_nth m1 L _ ms kids keys Di jj HM Hj) as ((Dj & HP & Hinc) & (xk & k & Hx & Hc & Hin)).
    split; [lia|]. split; [apply in_or_app; left; left; reflexivity|]. split.
    + exists Dj. split; [exact HP|]. intros b Hb. apply in_or_app. right. apply Hinc. exact Hb.
    + intros _. split; [apply in_or_app; left; right; left; reflexivity|].
      exists xk, k. split; [exact Hx|]. split; [exact Hc|]. apply in_or_app. right. exact Hin.
  - destruct HB as (-> & -> & -> & Hnc & Hcap & Di & -> & HI).
    exists num, kids, 0, cap. cbn [tkids]. rewrite length_map. split; [exact Hh|].
    intros jj Hj. destruct (Z.eqb_spec cap 0) as [E|_]; [lia|].
    destruct (close_items_nth _ ts kids Di jj HI Hj) as (Dj & HP & Hinc).
    split; [lia|]. split; [apply in_or_app; left; left; reflexivity|]. split.
    + exists Dj. rewrite close_nth_arr. cbn [snd]. split; [exact HP|].
      intros b Hb. apply in_or_app. right. apply Hinc. exact Hb.
    + intros E. discriminate E.
Qed.

Lemma ev_fkeep_trans : forall F1 F2 F3, ex_fkeep F1 F2 -> ex_fkeep F2 F3 -> ex_fkeep F1 F3.
Proof. intros F1 F2 F3 H1 H2 k Hk. rewrite (H2 k Hk). exact (H1 k Hk). Qed.

Lemma ev_L_nil : forall dn o n cap acc, ex_L dn o n cap acc [] = None.
Proof. intros. unfold ex_L. apply jrl_nil. Qed.

Lemma ev_apart_sub : forall a n b k b' k', ex_apart a n b k -> b <= b' -> b' + k' <= b + k -> 0 < k' ->
  ex_apart a n b' k'.
Proof. unfold ex_apart. intros. lia. Qed.

Lemma ev_fst_arr : forall u n, tag u = 5 -> fst (nth n (tkids u) ([], JNull)) = [].
Proof.
  intros u n H. destruct u as [| | | ? ? | ? | ts | ?]; cbn in H; try discriminate. cbn [tkids].
  revert n. induction ts as [|a ts IH]; intros [|n]; cbn; try reflexivity. apply IH.
Qed.

Lemma ev_X_tail : forall x i r, 0 <= i <= Z.of_nat (length x) -> (exists k, r = skipn k (ev_X x i)) ->
  r = ev_X x (Z.of_nat (length x) - Z.of_nat (length r)) /\ i <= Z.of_nat (length x) - Z.of_nat (length r).
Proof.
  intros x i r Hi [k ->]. unfold ev_X. rewrite skipn_map, skipn_skipn, length_map, length_skipn.
  split; [|lia].
  destruct (Nat.le_gt_cases (k + Z.to_nat i) (length x)).
  - f_equal. f_equal. lia.
  - rewrite (skipn_all2 x) by lia. rewrite (skipn_all2 x); [reflexivity|lia].
Qed.

Lemma ev_off_out_g : forall p D1 b k z, ex_off p D1 b k -> pj_foot p D1 z -> ~ (b <= z < b + k).
Proof.
  intros p D1 b k z (H1 & H2) [Hz|(bk & Hin & Hz)].
  - unfold ex_apart in H1. lia.
  - rewrite Forall_forall in H2. specialize (H2 bk Hin). unfold ex_apart, pj_holds in *. lia.
Qed.

Lemma ev_fr_jl : forall m1 A w0 w1 w2 w3 w4 cs,
  rw_cells rsegs m1 A (CB 40 (ev_jl w0 w1 w2 w3 w4) :: cs) <->
  rw_cells rsegs m1 A (C8 w0 :: C8 w1 :: C8 w2 :: C8 w3 :: C8 w4 :: cs).
Proof.
  intros m1 A w0 w1 w2 w3 w4 cs. pose proof (ev_jl_len w0 w1 w2 w3 w4) as L. unfold rw_cells, cells_at.
  cbn [cells_wf cell_wf cells_bytes cbytes cells_size csize]. unfold ev_jl in *. rewrite <- !app_assoc.
  replace (40 + cells_size cs)%nat with (8 + (8 + (8 + (8 + (8 + cells_size cs)))))%nat by lia.
  tauto.
Qed.

Set Default Proof Using "All".

Section EV.
Hypotheses (ESC : ex_string_contract) (EWC : ex_word_contract) (SCC : strcmp_contract) (BCC : bcmp_contract)
  (MCC : memcpy_contract) (SDC : strtod_contract) (EWS : ex_ws_contract).
Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word)
  (m : word -> option byte) (q v x0 i0 d dl scr lo : Z) (x : list byte) (lblk : Z -> Z -> Prop) (t : jv)
  (D : list (Z * Z)) (canary ev : word).

Local Abbreviation SP := (bv_unsigned sp).
Local Abbreviation len := (Z.of_nat (length x)).
Local Abbreviation KD := ((33 - d) * 144 + 8928).
Local Abbreviation X := (ev_X x).

Hypotheses (HTP : tp = Z_to_bv 64 0x35348) (QA : q mod 8 = 0) (QG : 0x56000 <= q)
  (RQ0 : ex_rec m q (x0 + i0) (x0 + len) d scr dl)
  (BX : bytes_at rsegs m x0 x) (X0 : 0 < x0) (XE : x0 + len < 2 ^ 62) (XL : len <= 3 * 2 ^ 20)
  (I0 : 0 <= i0 <= len) (DD : 0 <= d <= 32) (DL : dl = 0 \/ dl = 1)
  (SS0 : stk rsegs m scr (scr + len + 1)) (SG : 4096 <= scr) (SGd : scr + len + 1 <= 0x10000 \/ 0x56000 <= scr)
  (SW : scr + len + 1 <= SP - KD)
  (TV : v = 0 \/ pj_node rsegs m lblk v t D /\ Forall (fun ak => 0 < fst ak /\ fst ak mod 8 = 0) D)
  (ST0 : stk rsegs m lo SP) (LOW : lo <= SP - KD) (SA : SP mod 16 = 0) (SB : SP < 2 ^ 62)
  (SG2 : 0x56000 <= SP - KD)
  (AQX : ex_apart q 40 x0 len) (AQS : ex_apart q 40 scr (len + 1)) (AXS : ex_apart x0 len scr (len + 1))
  (AQW : ex_apart q 40 (SP - KD) KD) (AXW : ex_apart x0 len (SP - KD) KD) (AXE : ex_apart x0 len 0x352a4 4)
  (TO : v <> 0 -> ex_off v D q 40 /\ ex_off v D scr (len + 1) /\ ex_off v D (SP - KD) KD /\
                 ex_off v D 0x352a4 4)
  (GG0 : rw_cells rsegs m 0x23f98 [C8 (Z_to_bv 64 0x555b8)]) (GQ0 : rw_cells rsegs m 0x555b8 [C8 canary])
  (GE0 : rw_cells rsegs m 0x352a4 [C4 ev])
  (MI0 : mem_inv rsegs m) (TM0 : OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.MemNorm.task_mem rsegs m).

Hypothesis IHV : forall (ra' sp' gp' tp' t0' t1' t2' s0' s1' a0' a1' a2' a3' a4' a5' a6' a7' s2' s3' s4' s5' s6' s7' s8'
    s9' s10' s11' t3' t4' t5' t6' : word) (F'' : bvmap 5 word) (fc'' : bv 32) (m'' : word -> option byte)
    (q' v' x0' i0' d' dl' scr' lo' : Z) (x' : list byte) (lblk' : Z -> Z -> Prop) (t' : jv) (D' : list (Z * Z))
    (canary' ev'' : word),
  (Z.to_nat (Z.of_nat (length x') - i0') < Z.to_nat (len - i0))%nat ->
  ex_value_spec ra' sp' gp' tp' t0' t1' t2' s0' s1' a0' a1' a2' a3' a4' a5' a6' a7' s2' s3' s4' s5' s6' s7' s8' s9' s10'
    s11' t3' t4' t5' t6' F'' fc'' m'' q' v' x0' i0' d' dl' scr' lo' x' lblk' t' D' canary' ev''.


Definition ev_W : list (Z * Z) :=
  [(SP - KD, SP); (q, q + 8); (q + 16, q + 20); (q + 32, q + 36); (scr, scr + len + 1); (0x352a4, 0x352a4 + 4)].

Definition ev_Q : machine_state -> Prop :=
  ex_value_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F m q v x0 i0 d dl scr lo x t.

Definition ev_SAVED : list cell :=
  [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

Definition ev_FI (m' : word -> option byte) (j : list byte) (pv dep dl' : Z) (fc' : bv 32) (F' : bvmap 5 word)
  : Prop :=
  munch ev_W m m' /\ wmono rsegs m m' /\ mem_inv rsegs m' /\
  rw_cells rsegs m' (SP + -144) (CB 40 j :: ev_SAVED) /\ stk rsegs m' lo (SP + -144) /\
  (exists ev', rw_cells rsegs m' 0x352a4 [C4 ev']) /\
  ex_rec m' q (x0 + pv) (x0 + len) dep scr dl' /\ (dl' = 0 \/ dl' = 1) /\ frm0 fc' /\ ex_fkeep F F'.

Definition ev_FIN (r : word) (m' : word -> option byte) (pv dep dl' : Z) : Prop :=
  match ex_V d (X i0) with
  | None => r = Z_to_bv 64 (-1) /\ 0 <= pv <= len /\ d <= dep <= 33
  | Some (u, rest) =>
      r = Z_to_bv 64 0 /\ pv = len - Z.of_nat (length rest) /\ dep = d /\
      stk rsegs m' scr (scr + len + 1) /\ (dl' = 1 <-> dl = 1 \/ (v <> 0 /\ t <> u))
  end.


Definition ev_D0 (o : bool) : Prop := dl = 1 \/ (v <> 0 /\ tag t <> 5 + Z.b2z o).

Definition ev_VV (o : bool) (vv : Z) : Prop :=
  (vv = 0 /\ (v = 0 \/ tag t <> 5 + Z.b2z o)) \/ (vv = v /\ v <> 0 /\ tag t = 5 + Z.b2z o).

Definition ev_US (o : bool) (us : list (list Z * jv)) : Prop := o = false -> Forall (fun nu => fst nu = []) us.

Definition ev_DI (o : bool) (vv : Z) (n : nat) (us : list (list Z * jv)) (dlc : Z) : Prop :=
  (dlc = 0 \/ dlc = 1) /\
  (dlc = 1 <-> ev_D0 o \/ (vv <> 0 /\ exists jj, (jj < n)%nat /\
     ((length (tkids t) <= jj)%nat \/ nth jj (tkids t) ([], JNull) <> nth jj us ([], JNull)))).

Definition ev_KID (vv : Z) (n : nat) (kid fl : Z) : Prop :=
  (fl = 0 /\ kid = 0 /\ (vv = 0 \/ (length (tkids t) <= n)%nat)) \/
  (fl = 1 /\ vv = v /\ v <> 0 /\ (n < length (tkids t))%nat /\ 0 < kid /\
   exists blk bk Dn, In (blk, bk) D /\ blk <= kid /\ kid + 56 <= blk + bk /\
     pj_node rsegs m lblk kid (snd (nth n (tkids t) ([], JNull))) Dn /\ incl Dn D).


Definition ev_HEAD (o : bool) (vv : Z) (n : nat)
    (y1 y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y19 y27 y28 y29 y30 y31 : word)
    (F' : bvmap 5 word) (fc' : bv 32) (m' : word -> option byte) : machine_state :=
  MS (mkR y1 (Z_to_bv 64 (SP + -144)) gp tp y5 y6 y7 (Z_to_bv 64 q) (Z_to_bv 64 vv) y10 y11 y12 y13 y14 y15 y16 y17
    (Z_to_bv 64 (-1)) y19 (Z_to_bv 64 (if o then 123 else 91)) (Z_to_bv 64 44) (Z_to_bv 64 (Z.of_nat n))
    (Z_to_bv 64 (8 * Z.of_nat n)) (Z_to_bv 64 (56 * Z.of_nat n)) (Z_to_bv 64 123) (Z_to_bv 64 (-1)) y27 y28 y29 y30
    y31) F' (Z_to_bv 64 (if vv =? 0 then 0x14b08 else 0x14a98)) fc' None m' (seg_rom rsegs).

Ltac ap H := let H' := fresh "A" in pose proof H as H'; unfold ex_apart in H'.

Ltac fi_pack := unfold ev_FI; rewrite ?ev_rec_iff; repeat (first [ eassumption | apply conj | eexists ]).
Ltac fi_open HFI := let MU := fresh "MU" in let WM := fresh "WM" in let MI := fresh "MI" in let FR := fresh "FR" in
  let ST := fresh "ST" in let EV := fresh "EV" in let REC := fresh "REC" in let DL' := fresh "DL'" in
  let FRM := fresh "FRM" in let FK := fresh "FK" in let ev' := fresh "ev'" in
  pose proof HFI as (MU & WM & MI & FR & ST & (ev' & EV) & REC & DL' & FRM & FK);
  apply ev_rec_iff in REC; destruct REC as (RP & RE & RD & RS & RF); unfold ev_W in MU; unfold ev_SAVED in FR.

Lemma ev_tm : forall m', munch ev_W m m' -> OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.MemNorm.task_mem rsegs m'.
Proof.
  intros m' MU. apply (ev_tm_munch ev_W m m' TM0 MU). intros a Ha.
  pose proof (zr_word a) as Ra. unfold inr64 in Ra.
  destruct (ev_not_outside _ _ Ha) as (l & h & Hin & Hr). unfold ev_W in Hin. cbn [In] in Hin.
  destruct RQ0 as [[_ W1] [_ W2]]. destruct GE0 as [_ W3]. cbn [cells_size csize Nat.add Z.of_nat] in W1, W2, W3.
  destruct Hin as [E|[E|[E|[E|[E|[E|[]]]]]]]; injection E as <- <-.
  - apply (ev_wv_stk m lo SP a ST0). lia.
  - apply (ev_wv_wr m q _ a W1). lia.
  - apply (ev_wv_wr m q _ a W1). lia.
  - apply (ev_wv_wr m (q + 24) _ a W2). lia.
  - apply (ev_wv_stk m scr (scr + len + 1) a SS0). lia.
  - apply (ev_wv_wr m 0x352a4 _ a W3). lia.
Qed.

Lemma ev_bx : forall m', munch ev_W m m' -> bytes_at rsegs m' x0 x.
Proof.
  intros m' MU. ap AQX. ap AXS. ap AXW. ap AXE. destruct x as [|b0 x1] eqn:Ex.
  - apply bytes_at_nil. cbn [length Z.of_nat] in *. lia.
  - rewrite <- Ex in *. apply (bytes_at_transport rsegs ev_W m m' x0 x BX MU). unfold ev_W. cbn [disjoint_from].
    assert (0 < len) by (rewrite Ex; cbn [length]; lia). repeat split; lia.
Qed.

Lemma ev_gg : forall m', munch ev_W m m' -> wmono rsegs m m' -> rw_cells rsegs m' 0x23f98 [C8 (Z_to_bv 64 0x555b8)].
Proof.
  intros m' MU WM. ap AQW. apply (rw_cells_transport rsegs ev_W m m' _ _ GG0 MU WM). unfold ev_W. cbn [disjoint_from cells_size csize]. repeat split; lia.
Qed.

Lemma ev_gq : forall m', munch ev_W m m' -> wmono rsegs m m' -> rw_cells rsegs m' 0x555b8 [C8 canary].
Proof.
  intros m' MU WM. ap AQW. apply (rw_cells_transport rsegs ev_W m m' _ _ GQ0 MU WM). unfold ev_W. cbn [disjoint_from cells_size csize]. repeat split; lia.
Qed.

Lemma ev_off_out : forall b k z, ex_off v D b k -> pj_foot v D z -> ~ (b <= z < b + k).
Proof. intros b k z. apply ev_off_out_g. Qed.

Lemma ev_tree : forall m', v <> 0 -> munch ev_W m m' -> pj_node rsegs m' (fun a k => In (a, k) D) v t D.
Proof.
  intros m' Hv MU. destruct TV as [E|[TN _]]; [contradiction|].
  apply (pj_node_munch rsegs ev_W m lblk m' (fun a k => In (a, k) D) v t D TN); [intros a k H; exact H|exact MU|].
  intros z Hz. destruct (TO Hv) as (Oq & Os & Ow & Oe). unfold ev_W. cbn [outside].
  pose proof (ev_off_out _ _ z Oq Hz). pose proof (ev_off_out _ _ z Os Hz).
  pose proof (ev_off_out _ _ z Ow Hz). pose proof (ev_off_out _ _ z Oe Hz).
  repeat split; lia.
Qed.

Lemma ev_epi : forall (y1 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16 y17 y19 y20 y21 y22 y23 y24 y25 y26 y27 y28 y29
    y30 y31 r : word) (F' : bvmap 5 word) (fc' : bv 32) m' j pv dep dl',
  ev_FI m' j pv dep dl' fc' F' -> ev_FIN r m' pv dep dl' ->
  evt rsegs ev_Q (MS (mkR y1 (Z_to_bv 64 (SP + -144)) gp tp y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16 y17 r y19 y20
    y21 y22 y23 y24 y25 y26 y27 y28 y29 y30 y31) F' (Z_to_bv 64 0x14c70) fc' None m' (seg_rom rsegs)).
Proof.
  intros y1 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16 y17 y19 y20 y21 y22 y23 y24 y25 y26 y27 y28 y29 y30 y31 r
    F' fc' m' j pv dep dl' HFI HFIN.
  destruct HFI as (MU & WM & MI & FR & ST & (ev' & EV) & RQ & DL' & FRM & FK).
  pose proof (ev_tm m' MU) as TM.
  unfold ev_SAVED in FR.
  pose proof (zr_word sp) as Rsp. unfold inr64 in Rsp.
  Time do 14 zstep.
  release_frame FR ST (bv_unsigned sp).
  zstep. zstep.
  apply evt_done. unfold ev_Q, ex_value_post.
  exists y5, y6, y7, r, y11, y12, y13, y14, y15, y16, y17, y28, y29, y30, y31, F', fc', m', pv, dep, dl', ev'.
  split; [reflexivity|].
  unfold ex_value_K, EX_VALUE_FE, EX_VALUE_KC, STRTOD_ERRNO. unfold ev_W in MU.
  split; [exact FK|]. split; [exact FRM|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI|].
  split; [exact TM|]. split; [exact ST|]. split; [exact EV|]. split; [exact RQ|]. split; [exact DL'|].
  exact HFIN.
Qed.

Ltac epi_go := eapply ev_epi; [fi_pack|unfold ev_FIN].

Lemma ev_vr : 0 <= v < 2 ^ 64.
Proof.
  destruct TV as [->|[TN _]]; [lia|]. destruct (ev_hdr _ _ _ _ _ TN) as (? & ? & ? & ? & ? & ? & ((_ & (S1 & S2 & _)) & _)).
  lia.
Qed.

Lemma strlit_find_rw : forall (l : list Segment) z n sg,
  forallb (fun s => implb (seg_writable s) (seg_readable s)) l = true ->
  find_segment l z n = Some sg -> seg_writable sg = true -> seg_readable sg = true.
Proof.
  induction l as [|s l IH]; intros z n sg Hf E Hw; cbn [find_segment] in E; [discriminate|].
  cbn [forallb] in Hf. apply andb_true_iff in Hf as [H1 H2].
  match type of E with context [if ?c then _ else _] => destruct c end.
  - injection E as <-. rewrite Hw in H1. exact H1.
  - exact (IH z n sg H2 E Hw).
Qed.

Lemma strlit_wv_mrd : forall m1 (a : word), wview rsegs m1 a <> None -> exists b, mrd rsegs m1 a = Some b.
Proof.
  intros m1 a H. unfold mrd. destruct (m1 a) as [b|] eqn:Em; [exists b; reflexivity|].
  revert H. unfold wview, seg_rom, memory_read. rewrite Em. cbv beta iota. change (Z.of_N 1) with 1.
  destruct (find_segment rsegs (bv_unsigned a) 1) as [sg|] eqn:E; [|intros H; exfalso; exact (H eq_refl)].
  destruct (seg_writable sg) eqn:Ew; [|intros H; exfalso; exact (H eq_refl)].
  rewrite (strlit_find_rw rsegs _ _ sg ltac:(vm_compute; reflexivity) E Ew).
  intros H. change (N.to_nat 1) with 1%nat. cbn [segment_read_bytes].
  destruct (segment_byte_at _ _) as [b|]; [exists b; reflexivity|exfalso; exact (H eq_refl)].
Qed.

Lemma strlit_stk_mono : forall m1 m2 lo1 hi1, stk rsegs m1 lo1 hi1 -> wmono rsegs m1 m2 -> stk rsegs m2 lo1 hi1.
Proof.
  intros m1 m2 lo1 hi1 (H1 & H2 & H) W. split; [lia|]. split; [lia|]. intros a Ha.
  pose proof (W (wa a) (proj1 (H a Ha))) as Hw. split; [exact Hw|]. exact (strlit_wv_mrd m2 (wa a) Hw).
Qed.

Lemma strlit_prefixb : forall (wz : list Z) (s : list byte), Forall (fun c => 0 <= c < 256) wz ->
  prefixb wz (map bv_unsigned s) = true <-> (length wz <= length s)%nat /\ firstn (length wz) s = map (Z_to_bv 8) wz.
Proof.
  induction wz as [|a wz IH]; intros s Hw.
  - cbn [prefixb length firstn map]. split; [intros _; split; [lia|reflexivity]|reflexivity].
  - apply Forall_cons_iff in Hw as [Ha Hw].
    destruct s as [|b s]; cbn [prefixb map length firstn].
    + split; [discriminate|intros [H _]; lia].
    + rewrite andb_true_iff, (IH s Hw). split.
      * intros [E1 [L E2]]. apply Z.eqb_eq in E1. subst a. split; [lia|]. f_equal; [|exact E2].
        apply bv_eq. rewrite Z_to_bv_unsigned. symmetry. apply bv_wrap_small. apply bv_unsigned_in_range.
      * intros [L E]. injection E as E1 E2. split; [|split; [lia|exact E2]].
        apply Z.eqb_eq. subst b. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256.
        rewrite Z.mod_small by lia. reflexivity.
Qed.

Lemma strlit_match : forall (xs : list byte) k wz, 0 <= k <= Z.of_nat (length xs) -> Forall (fun c => 0 <= c < 256) wz ->
  ex_word_match xs k (map (Z_to_bv 8) wz) <-> prefixb wz (ev_X xs k) = true.
Proof.
  intros xs k wz Hk Hw. unfold ex_word_match, ev_X. rewrite (strlit_prefixb wz _ Hw), length_map, length_skipn.
  split; intros [H1 H2]; (split; [lia|exact H2]).
Qed.

Lemma strlit_lit_tag : forall u : jv, (forall t', tag t' = tag u -> t' = u) -> 0 <= tag u <= 2.
Proof.
  intros [| | |txt bits|zs|l1|ms] H; cbn [tag]; try lia; exfalso.
  - specialize (H (JNum txt (bits + 1)) eq_refl).
    apply (f_equal (fun t1 => match t1 with JNum _ b => b | _ => 0 end)) in H. cbn in H. lia.
  - specialize (H (JStr (0 :: zs)) eq_refl).
    apply (f_equal (fun t1 => match t1 with JStr zz => length zz | _ => 0%nat end)) in H. cbn in H. lia.
  - specialize (H (JArr (JNull :: l1)) eq_refl).
    apply (f_equal (fun t1 => match t1 with JArr l2 => length l2 | _ => 0%nat end)) in H. cbn in H. lia.
  - specialize (H (JObj (([], JNull) :: ms)) eq_refl).
    apply (f_equal (fun t1 => match t1 with JObj l2 => length l2 | _ => 0%nat end)) in H. cbn in H. lia.
Qed.

Ltac fi_pack2 := unfold ev_FI; rewrite ?ev_rec_iff; repeat (first [ eassumption | apply conj | eexists ]).

Lemma ev_v_tr : v <> 0 -> forall m' a bs, munch ev_W m m' -> bytes_at rsegs m a bs -> v <= a ->
  a + Z.of_nat (length bs) <= v + 56 -> bytes_at rsegs m' a bs.
Proof.
  intros Hv m' a bs MU B H1 H2. apply (bytes_at_transport rsegs ev_W m m' a bs B MU).
  destruct (TO Hv) as ((Oq & _) & (Os & _) & (Ow & _) & (Oe & _)). unfold ex_apart in Oq, Os, Ow, Oe.
  unfold ev_W. cbn [disjoint_from]. pose proof (bytes_at_bound _ _ _ _ B). repeat split; lia.
Qed.

Lemma ev_kid_ok : forall vv n kid fl m', ev_KID vv n kid fl -> munch ev_W m m' ->
  exists Dk, (kid = 0 \/ pj_node rsegs m' (fun a k => In (a, k) D) kid (snd (nth n (tkids t) ([], JNull))) Dk /\
               Forall (fun ak => 0 < fst ak /\ fst ak mod 8 = 0) Dk) /\
    (kid <> 0 -> ex_off kid Dk q 40 /\ ex_off kid Dk scr (len + 1) /\ ex_off kid Dk (SP - KD) (KD - 144) /\
                 ex_off kid Dk 0x352a4 4) /\ 0 <= kid < 2 ^ 64.
Proof.
  intros vv n kid fl m' K MU.
  destruct K as [(_ & -> & _)|(_ & _ & Hv & _ & Hk & blk & bk & Dn & HinD & Hb1 & Hb2 & TNk & InclD)].
  - exists []. split; [left; reflexivity|]. split; [intro H; contradiction|lia].
  - destruct TV as [E|[TN FD]]; [contradiction|]. destruct (TO Hv) as (Oq & Os & Ow & Oe).
    assert (OFF : forall b k, ex_off v D b k -> 0 < k -> ex_off kid Dn b k).
    { intros b k (_ & HF) Hkp. rewrite Forall_forall in HF. split.
      - specialize (HF (blk, bk) HinD). cbn [fst snd] in HF. unfold ex_apart in HF |- *. lia.
      - apply Forall_forall. intros ak Hak. apply HF. apply InclD. exact Hak. }
    pose proof (OFF _ _ Oq ltac:(lia)) as Kq. pose proof (OFF _ _ Os ltac:(lia)) as Ks.
    pose proof (OFF _ _ Ow ltac:(lia)) as Kw. pose proof (OFF _ _ Oe ltac:(lia)) as Ke.
    destruct (ev_hdr _ _ _ _ _ TNk) as (? & ? & ? & ? & ? & ? & ((_ & (S1 & S2 & _)) & _)).
    exists Dn. split; [right; split|split; [|lia]].
    + apply (pj_node_munch rsegs ev_W m lblk m' (fun a k => In (a, k) D) kid _ Dn TNk);
        [intros a k H; apply InclD; exact H|exact MU|].
      intros z Hz. unfold ev_W. cbn [outside].
      pose proof (ev_off_out_g _ _ _ _ z Kq Hz). pose proof (ev_off_out_g _ _ _ _ z Ks Hz).
      pose proof (ev_off_out_g _ _ _ _ z Kw Hz). pose proof (ev_off_out_g _ _ _ _ z Ke Hz).
      repeat split; lia.
    + rewrite Forall_forall in FD |- *. intros ak Hak. apply FD. apply InclD. exact Hak.
    + intros _. split; [exact Kq|]. split; [exact Ks|]. split; [|exact Ke].
      destruct Kw as (Kw1 & Kw2). split.
      * unfold ex_apart in Kw1 |- *. lia.
      * rewrite Forall_forall in Kw2 |- *. intros ak Hak. specialize (Kw2 ak Hak). unfold ex_apart in Kw2 |- *. lia.
Qed.

Lemma ev_US_app : forall o l nm (a b : jv), ev_US o (l ++ [(nm, a)]) -> ev_US o (l ++ [(nm, b)]).
Proof.
  intros o l nm a b H Ho. specialize (H Ho). apply Forall_app in H as [H1 H2]. apply Forall_app. split; [exact H1|].
  inversion H2; subst. constructor; [exact H3|constructor].
Qed.

Lemma close_dl : forall (o : bool) vv (n : nat) us dlc dl',
  ev_VV o vv -> n = length us -> ev_US o us -> ev_DI o vv n us dlc ->
  (dl' = 1 <-> dlc = 1 \/ (vv <> 0 /\ n <> length (tkids t))) ->
  (dl' = 1 <-> dl = 1 \/ (v <> 0 /\ t <> mk o us)).
Proof.
  intros o vv n us dlc dl' VV Hn US (Dc & DI) HD. rewrite HD, DI. unfold ev_D0.
  destruct VV as [(Hv0 & Hv)|(Hvv & Hv & Ht)].
  - subst vv. split.
    + intros [[[G|(Hv' & Ht')]|(N & _)]|(N & _)].
      * left. exact G.
      * right. split; [exact Hv'|]. intros E. apply Ht'. rewrite E. destruct o; reflexivity.
      * exfalso. exact (N eq_refl).
      * exfalso. exact (N eq_refl).
    + intros [G|(Hv' & Hne)]; [left; left; left; exact G|]. left; left; right. split; [exact Hv'|].
      destruct Hv as [E0|Ht']; [contradiction|exact Ht'].
  - subst vv. rewrite (ev_mk_neq t o us Ht US). subst n. split.
    + intros [[[G|(_ & Ht')]|(_ & jj & Hj & [Hl|Hne])]|(_ & Hne)].
      * left. exact G.
      * contradiction.
      * right. split; [exact Hv|]. left. lia.
      * destruct (Nat.lt_ge_cases jj (length (tkids t))) as [Hlt|Hge].
        -- right. split; [exact Hv|]. right. exists jj. split; [exact Hlt|]. split; [exact Hj|exact Hne].
        -- right. split; [exact Hv|]. left. lia.
      * right. split; [exact Hv|]. left. lia.
    + intros [G|(_ & [Hl|(jj & J1 & J2 & J3)])].
      * left. left. left. exact G.
      * right. split; [exact Hv|]. lia.
      * left. right. split; [exact Hv|]. exists jj. split; [exact J2|]. right. exact J3.
Qed.

Lemma ev_DI_next : forall (o : bool) vv (n : nat) us dlc dlA kid fl nm u dlB dlC,
  ev_VV o vv -> n = length us -> ev_DI o vv n us dlc -> ev_KID vv n kid fl -> (o = false -> nm = []) ->
  (dlA = 1 <-> dlc = 1 \/ (vv <> 0 /\ (length (tkids t) <= n)%nat)) ->
  (dlB = 1 <-> dlA = 1 \/ (fl = 1 /\ fst (nth n (tkids t) ([], JNull)) <> nm)) ->
  (dlC = 0 \/ dlC = 1) ->
  (dlC = 1 <-> dlB = 1 \/ (kid <> 0 /\ snd (nth n (tkids t) ([], JNull)) <> u)) ->
  ev_DI o vv (S n) (us ++ [(nm, u)]) dlC.
Proof.
  intros o vv n us dlc dlA kid fl nm u dlB dlC VV Hn (Dc & DI) KID Hnm HA HB HC0 HC.
  unfold ev_DI. split; [exact HC0|].
  assert (NA : forall jj, (jj < n)%nat -> nth jj (us ++ [(nm, u)]) ([], JNull) = nth jj us ([], JNull))
    by (intros jj Hj; apply app_nth1; lia).
  assert (NB : nth n (us ++ [(nm, u)]) ([], JNull) = (nm, u)).
  { rewrite app_nth2 by lia. replace (n - length us)%nat with 0%nat by lia. reflexivity. }
  assert (P : forall a b : list Z * jv, a <> b <-> fst a <> fst b \/ snd a <> snd b).
  { intros [a1 a2] [b1 b2]. cbn [fst snd]. split.
    - intros N. destruct (list_eq_dec Z.eq_dec a1 b1) as [<-|N1]; [|left; exact N1].
      right. intros <-. exact (N eq_refl).
    - intros [N|N] E; injection E as E1 E2; [exact (N E1)|exact (N E2)]. }
  rewrite HC, HB, HA, DI. split.
  - intros [[[[D0|(Hv & jj & Hj & Hjj)]|(Hv & Hl)]|(Hf & Hnf)]|(Hk & Hnu)].
    + left. exact D0.
    + right. split; [exact Hv|]. exists jj. split; [lia|]. rewrite (NA jj Hj). exact Hjj.
    + right. split; [exact Hv|]. exists n. split; [lia|]. left. exact Hl.
    + destruct KID as [(F0 & _ & _)|(_ & Ev & Hv0 & _)]; [lia|].
      right. split; [lia|]. exists n. split; [lia|]. right. rewrite NB. apply (proj2 (P _ _)). left. exact Hnf.
    + destruct KID as [(_ & K0 & _)|(_ & Ev & Hv0 & _)]; [lia|].
      right. split; [lia|]. exists n. split; [lia|]. right. rewrite NB. apply (proj2 (P _ _)). right. exact Hnu.
  - intros [D0|(Hv & jj & Hj & Hjj)].
    + left. left. left. left. exact D0.
    + destruct (Nat.lt_ge_cases jj n) as [Hl|Hge].
      * rewrite (NA jj Hl) in Hjj. left. left. left. right. split; [exact Hv|]. exists jj. split; [exact Hl|exact Hjj].
      * assert (jj = n) by lia. subst jj. rewrite NB in Hjj.
        destruct Hjj as [Hl|Hne]; [left; left; right; split; [exact Hv|exact Hl]|].
        destruct KID as [(F0 & K0 & [Hvv|Hl])|(F1 & _ & _ & Hlt & Hk0 & _)]; [lia| |].
        -- left. left. right. split; [exact Hv|exact Hl].
        -- apply (proj1 (P _ _)) in Hne. destruct Hne as [N1|N2].
           ++ left. right. split; [exact F1|exact N1].
           ++ right. split; [lia|exact N2].
Qed.

Lemma objn_skip_map : forall (f : byte -> Z) k (l : list byte), skipn k (map f l) = map f (skipn k l).
Proof. intros f k. induction k as [|k IH]; intros [|b l]; cbn [skipn map]; try reflexivity. apply IH. Qed.

Lemma objn_X_skip : forall k a, 0 <= a -> skipn k (X a) = X (a + Z.of_nat k).
Proof.
  intros k a Ha. unfold ev_X. rewrite objn_skip_map, skipn_skipn.
  replace (Z.to_nat (a + Z.of_nat k)) with (k + Z.to_nat a)%nat by lia. reflexivity.
Qed.

Lemma objn_stk_fill : forall W m1 m2 lo1 hi1 A bs, stk rsegs m1 lo1 hi1 -> munch W m1 m2 -> wmono rsegs m1 m2 ->
  bytes_at rsegs m2 A bs -> (forall z, lo1 <= z < hi1 -> outside W z \/ A <= z < A + Z.of_nat (length bs)) ->
  stk rsegs m2 lo1 hi1.
Proof.
  intros W m1 m2 lo1 hi1 A bs (H1 & H2 & H) MU WM (B1 & B2 & B) HC. split; [lia|]. split; [lia|].
  intros a Ha. destruct (H a Ha) as [Hw (b & Hb)]. split; [apply WM; exact Hw|].
  destruct (HC a Ha) as [Ho|Hin].
  - exists b. unfold mrd in *. rewrite MU; [exact Hb|]. rewrite wa_unsigned by lia. exact Ho.
  - specialize (B (Z.to_nat (a - A)) ltac:(lia)). replace (A + Z.of_nat (Z.to_nat (a - A))) with a in B by lia.
    rewrite B. destruct (nth_error bs (Z.to_nat (a - A))) eqn:E; [eexists; reflexivity|].
    apply nth_error_None in E. lia.
Qed.

Lemma objn_name_nil : forall y, skip y = [] -> ex_name true y = None.
Proof. intros y H. unfold ex_name. rewrite H. reflexivity. Qed.

Lemma objn_name_nq : forall y b z, skip y = b :: z -> b <> 34 -> ex_name true y = None.
Proof.
  intros y b z H Hb. unfold ex_name. rewrite H. cbv beta iota. rewrite (proj2 (Z.eqb_neq b 34) Hb). reflexivity.
Qed.

Lemma objn_name_str0 : forall y z, skip y = 34 :: z -> run0 (jr_string z) = None -> ex_name true y = None.
Proof. intros y z H Hs. unfold ex_name. rewrite H. cbv beta iota. rewrite Z.eqb_refl, Hs. reflexivity. Qed.

Lemma objn_name_str : forall y z nm r, skip y = 34 :: z -> run0 (jr_string z) = Some (nm, r) ->
  ex_name true y = match skip r with c :: r1 => if c =? 58 then Some (nm, r1) else None | [] => None end.
Proof. intros y z nm r H Hs. unfold ex_name. rewrite H. cbv beta iota. rewrite Z.eqb_refl, Hs. reflexivity. Qed.

Lemma ev_skip_hd : forall l c r, skip l = c :: r -> ws c = false.
Proof.
  induction l as [|b l IH]; intros c r H; cbn [skip] in H; [discriminate|].
  destruct (ws b) eqn:E; [exact (IH c r H)|]. injection H as <- _. exact E.
Qed.

Lemma ev_v8 : v <> 0 -> v mod 8 = 0.
Proof.
  intros Hv. destruct TV as [E|[TN _]]; [contradiction|].
  destruct (ev_hdr _ _ _ _ _ TN) as (? & ? & ? & ? & ? & ? & ((Hal & _) & _)). exact Hal.
Qed.

Lemma ev_D8 : v <> 0 -> forall a k, In (a, k) D -> 0 < a /\ a mod 8 = 0.
Proof.
  intros Hv a k H. destruct TV as [E|[_ FD]]; [contradiction|]. rewrite Forall_forall in FD. exact (FD _ H).
Qed.

End EV.
