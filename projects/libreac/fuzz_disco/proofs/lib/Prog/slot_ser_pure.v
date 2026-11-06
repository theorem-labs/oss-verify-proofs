From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes ZBridge.
From OSSVerify.Proofs.libreac.fuzz_disco.lib Require Import Img0.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require Import slot_inv slot_lib slot_ser_defs.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require Import disco_box_name_model reac_box_name_c.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require Import disco_table_c disco_json_text reac_disco_table_json_c.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require Import disco_jscalar_model disco_json_reader_model disco_json_lemmas.
Import ListNotations.
Open Scope Z_scope.

Lemma ser_enum : forall (P : Z -> bool) op, 0 <= op < 256 ->
  forallb (fun k => P (Z.of_nat k)) (seq 0 256) = true -> P op = true.
Proof.
  intros P op Hop A. rewrite forallb_forall in A. specialize (A (Z.to_nat op) ltac:(apply in_seq; lia)).
  rewrite Z2Nat.id in A by lia. exact A.
Qed.

Lemma ser_k_bits : forall op, 0 <= op < 256 ->
  Z.shiftr (bv_unsigned (Z_to_bv 64 (Z.shiftl op 57))) 59 = ser_k op.
Proof.
  intros op Hop. rewrite unsigned_lit_wrap. apply Z.eqb_eq.
  exact (ser_enum (fun o => Z.shiftr (Z.shiftl o 57 mod 2 ^ 64) 59 =? ser_k o) op Hop ltac:(vm_compute; reflexivity)).
Qed.

Lemma ser_k_range : forall op, 0 <= op < 256 -> 0 <= ser_k op < 32.
Proof.
  intros op Hop.
  pose proof (ser_enum (fun o => (0 <=? ser_k o) && (ser_k o <? 32)) op Hop ltac:(vm_compute; reflexivity)) as A.
  cbn beta in A. lia.
Qed.

Lemma ser_cap_range : forall op, 0 <= op < 256 -> 2 <= ser_cap op <= 1280 /\ ser_capz op = ser_cap op.
Proof.
  intros op Hop.
  pose proof (ser_enum (fun o => (2 <=? ser_cap o) && (ser_cap o <=? 1280) && (ser_capz o =? ser_cap o)) op Hop
    ltac:(vm_compute; reflexivity)) as A.
  cbn beta in A. apply andb_prop in A as [A A3]. apply andb_prop in A as [A1 A2]. lia.
Qed.

Lemma ser_tok_ok : tok_ok box_tok.
Proof.
  intros f a b t H. unfold box_tok in H.
  destruct (Z.eqb_spec (bn_ret f [] a b) 0) as [R|R]; [|discriminate].
  injection H as <-.
  assert (G : bn_ok a && bn_ok b && negb ((a =? 0) && (b =? 0)) = true).
  { destruct (bn_ok a && bn_ok b && negb ((a =? 0) && (b =? 0))) eqn:E; [reflexivity|].
    rewrite (bn_ret_refuse f [] a b E) in R. discriminate. }
  apply andb_prop in G as [G G3]. apply andb_prop in G as [G1 G2]. apply negb_true_iff in G3.
  destruct (bn_c17 f a b G1 G2 G3) as (_ & _ & L & _ & Fc). split; [exact L|].
  eapply Forall_impl; [|exact Fc]. intros c Hc. unfold bn_tok_char in Hc. unfold tok_char.
  apply orb_prop in Hc as [Hc|Hc]; [apply orb_prop in Hc as [Hc|Hc]|].
  - apply andb_prop in Hc as [H1 H2]. lia.
  - apply andb_prop in Hc as [H1 H2]. lia.
  - lia.
Qed.

Lemma ser_byte_self : forall b : byte, Z_to_bv 8 (bv_unsigned b) = b.
Proof. intros b. apply bv_eq. rewrite Z_to_bv_unsigned. apply bv_wrap_small. apply bv_unsigned_in_range. Qed.

Lemma ser_map_unsigned_inj : forall xs ys : list byte, map bv_unsigned xs = map bv_unsigned ys -> xs = ys.
Proof.
  intros xs ys H. apply (f_equal (map (Z_to_bv 8))) in H. rewrite !map_map in H.
  rewrite !(map_ext (fun x : byte => Z_to_bv 8 (bv_unsigned x)) (fun b => b) ser_byte_self), !map_id in H. exact H.
Qed.

Lemma ser_sub_len : forall T k n, length T = 400%nat -> 0 <= k -> k + Z.of_nat n <= 400 -> length (sub T k n) = n.
Proof. intros T k n HT Hk Hn. unfold sub. rewrite length_firstn, length_skipn. lia. Qed.

Lemma ser_u_at_bound : forall T k n, 0 <= u_at T k n < 2 ^ (8 * Z.of_nat n).
Proof.
  intros T k n. unfold u_at. split; [apply bytes_le_to_Z_nonneg|].
  eapply Z.lt_le_trans; [apply bytes_le_to_Z_bound|]. apply Z.pow_le_mono_r; [lia|].
  unfold sub. rewrite length_firstn. lia.
Qed.

Lemma ser_s32_bound : forall T k, - 2 ^ 31 <= s32_at T k < 2 ^ 31.
Proof.
  intros T k. unfold s32_at, bv_swrap, bv_wrap. change (bv_half_modulus 32) with (2 ^ 31). change (bv_modulus 32) with (2 ^ 32).
  pose proof (Z.mod_pos_bound (u_at T k 4 + 2 ^ 31) (2 ^ 32) ltac:(lia)). lia.
Qed.

Lemma ser_tj_len : forall T, length (tj_entries T) = Z.to_nat (n_of T).
Proof. intros T. unfold tj_entries. rewrite length_map, length_seq. reflexivity. Qed.

Lemma ser_tj_ok : forall T, length T = 400%nat -> disco_table_c.table_ok T ->
  disco_json_text.table_ok (tj_entries T) /\ Forall entry_wf (tj_entries T).
Proof.
  intros T HT (T1 & T2 & T3 & T4). unfold tbl_T1 in T1.
  assert (Hin : forall k, In k (seq 0 (Z.to_nat (n_of T))) -> 0 <= Z.of_nat k < n_of T)
    by (intros k Hk; apply in_seq in Hk; lia).
  split; [split; [|split; [|split]]|].
  - rewrite ser_tj_len. lia.
  - unfold tj_entries. apply Forall_map. apply Forall_forall. intros k Hk. specialize (Hin k Hk).
    cbn [e_role tj_entry]. destruct (T2 (Z.of_nat k) Hin) as [E|[E|E]]; rewrite E; lia.
  - unfold tj_entries. rewrite map_map. apply NoDup_map_NoDup_ForallPairs; [|apply seq_NoDup].
    intros x y Hx Hy E. cbn [e_mac tj_entry] in E. apply ser_map_unsigned_inj in E.
    pose proof (Hin x Hx) as Hx'. pose proof (Hin y Hy) as Hy'.
    destruct (Nat.lt_trichotomy x y) as [L|[L|L]]; [|exact L|].
    + exfalso. exact (T3 (Z.of_nat x) (Z.of_nat y) ltac:(lia) ltac:(lia) ltac:(lia) E).
    + exfalso. exact (T3 (Z.of_nat y) (Z.of_nat x) ltac:(lia) ltac:(lia) ltac:(lia) (eq_sym E)).
  - unfold tj_entries. apply Forall_map. apply Forall_forall. intros k Hk. specialize (Hin k Hk).
    destruct (T4 (Z.of_nat k) Hin) as (H1 & H2 & H3). cbn [e_has_decl e_decl_in e_decl_out e_owned tj_entry].
    split; [|exact H3]. destruct H1 as [H1|H1]; [left; exact H1|right]. split; [exact H1|]. apply H2. exact H1.
  - unfold tj_entries. apply Forall_map. apply Forall_forall. intros k Hk. specialize (Hin k Hk).
    unfold entry_wf. cbn [e_mac e_role e_has_decl e_decl_in e_decl_out e_family e_owned e_last_seen tj_entry].
    unfold mac_of, hd_of, din_of, dout_of, role_of_e, owned_of, last_of, byte_ok.
    pose proof (ser_u_at_bound T (48 * Z.of_nat k + 12) 1). pose proof (ser_u_at_bound T (48 * Z.of_nat k + 13) 1).
    pose proof (ser_u_at_bound T (48 * Z.of_nat k + 14) 1). pose proof (ser_u_at_bound T (48 * Z.of_nat k + 15) 1).
    pose proof (ser_u_at_bound T (48 * Z.of_nat k + 40) 8).
    pose proof (ser_s32_bound T (48 * Z.of_nat k + 8)). pose proof (ser_s32_bound T (48 * Z.of_nat k + 24)).
    change (2 ^ (8 * Z.of_nat 1)) with 256 in *. change (2 ^ (8 * Z.of_nat 8)) with (2 ^ 64) in *.
    split; [rewrite length_map; apply ser_sub_len; lia|].
    split; [apply Forall_map; apply Forall_forall; intros b _; pose proof (byte_range b); lia|].
    lia.
Qed.

Definition g33 (c : Z) : Prop := 33 <= c <= 255.

Lemma g33_digits : forall ds, Forall digc ds -> Forall g33 ds.
Proof. intros ds F. eapply Forall_impl; [|exact F]. intros c H. unfold digc, g33 in *. lia. Qed.

Lemma g33_hex2 : forall x, byte_ok x -> Forall g33 (hex2 x).
Proof.
  intros x H. unfold byte_ok in H. pose proof (div16_range x H) as D1.
  pose proof (Z.mod_pos_bound x 16 ltac:(lia)) as D2.
  unfold hex2. apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]; unfold g33;
    [destruct (hexc_range (x / 16) D1) | destruct (hexc_range (x mod 16) ltac:(lia))]; lia.
Qed.

Lemma g33_mac : forall m, Forall byte_ok m -> Forall g33 (mac_text m).
Proof.
  intros m F. unfold mac_text.
  repeat (apply Forall_app; split); try (repeat constructor; unfold g33; lia);
    apply g33_hex2; apply nth_byte_ok; exact F.
Qed.

Lemma g33_model : forall tok e, tok_ok tok -> entry_wf e -> Forall g33 (fst (model_of tok e)) /\ Forall g33 (snd (model_of tok e)).
Proof.
  intros tok e Ht Hw. destruct Hw as (_ & _ & _ & Hi & Ho & _). unfold byte_ok in Hi, Ho. unfold model_of.
  destruct (e_has_decl e =? 0); [cbn; unfold s_unknown, s_0x0; split; repeat constructor; unfold g33; lia|].
  destruct (tok (e_family e) (e_decl_in e) (e_decl_out e)) as [t|] eqn:E;
    [|cbn; unfold s_unknown, s_0x0; split; repeat constructor; unfold g33; lia].
  cbn [fst snd]. split.
  - destruct (Ht _ _ _ _ E) as [_ Fc]. eapply Forall_impl; [|exact Fc]. intros c Hc. unfold tok_char, g33 in *. lia.
  - destruct (dec_spec (e_decl_in e) ltac:(lia)) as [D1 _]. destruct (dec_spec (e_decl_out e) ltac:(lia)) as [D2 _].
    apply Forall_app; split; [apply g33_digits; exact D1|].
    apply Forall_app; split; [repeat constructor; unfold g33; lia|apply g33_digits; exact D2].
Qed.

Lemma g33_body : forall tok now e, tok_ok tok -> entry_wf e -> 0 <= now < 2 ^ 64 -> Forall g33 (body tok now e).
Proof.
  intros tok now e Ht Hw Hn.
  assert (HmB : Forall byte_ok (e_mac e)) by apply Hw.
  destruct (g33_model tok e Ht Hw) as [Fm1 Fm2].
  assert (Ha : 0 <= age_of now (e_last_seen e) < 10 ^ 20).
  { pose proof (age_range now (e_last_seen e) Hn ltac:(apply Hw)). lia. }
  pose proof (g33_digits _ (proj1 (dec_spec _ Ha))) as Fd.
  unfold body, P2, P3, P4, P5, P6, key, qstr, k_mac, k_role, k_model, k_width, k_owned, k_age_ms.
  repeat (apply Forall_app; split);
  try first [ assumption
            | apply g33_mac; assumption
            | unfold rolename, s_box, s_master, s_unknown; destruct (e_role e =? 1); [|destruct (e_role e =? 2)];
              repeat constructor; unfold g33; lia
            | unfold owned_text, s_true, s_false; destruct (e_owned e =? 0); repeat constructor; unfold g33; lia
            | repeat constructor; unfold g33; lia ].
  all: apply g33_hex2; apply nth_byte_ok; exact HmB.
Qed.

Lemma ser_text_g33 : forall tok E now, tok_ok tok -> Forall entry_wf E -> 0 <= now < 2 ^ 64 ->
  Forall (fun c => 33 <= c <= 255) (table_json_text tok E now).
Proof.
  intros tok E now Ht Hw Hn. unfold table_json_text.
  apply Forall_app; split; [repeat constructor; lia|].
  apply Forall_app; split; [|repeat constructor; lia].
  generalize 0%nat. induction E as [|e E IH]; intros k; [constructor|].
  apply Forall_cons_iff in Hw as [He Hw]. cbn [objs_text]. rewrite obj_text_body.
  apply Forall_app; split; [apply Forall_app; split|].
  - destruct (Nat.eqb k 0); repeat constructor; lia.
  - exact (g33_body tok now e Ht He Hn).
  - apply IH. exact Hw.
Qed.
