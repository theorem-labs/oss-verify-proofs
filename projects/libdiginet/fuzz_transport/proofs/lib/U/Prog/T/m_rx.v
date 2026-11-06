(* The walk of m_rx in the ubsan image, against m_rx_c.v. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem Fpu.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Import Tac Arr Bytes.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.U Require Import Img0.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.U.Spec Require Import StrFun.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.U.Prog Require Import bcmp_c memcpy_c.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require Import TWorld TWorldLemmas TWorldMem TImg TSess0 TCb.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require Import DgnSpec.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.U.Prog.T Require Import TImgU WMem TContract.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.U.Prog.T Require Import spec_read_frame_c host_offset_c
  desk_named_c m_set_c m_wake_c m_maybe_online_c m_tick_c m_rx_c.
Import ListNotations.
Open Scope Z_scope.

Local Notation "'let*' p ':=' c1 'in' c2" := (match c1 with Some p => c2 | None => None end)
  (at level 200, p pattern, c1 at level 200, c2 at level 200).

(* ---- the model m_rx_m (TCb.v:244-330) cut at the points the walk reaches ---- *)

Definition mr_f (fr : tframe) (n : Z) : spec_frame := spec_read_frame (zs (tf_bytes fr)) n.

(* :313-316, e0 after the desk fields *)
Definition mr_e0 (B4 : list byte) : option (list byte * unit) :=
  let B5 := set_M_foreign B4 0 in
  let* (B6, _) := if M_state B5 =? S_ONLINE then m_lost_m B5 R_DESK_OFFLINE else Some (B5, tt) in
  if (M_state B6 =? S_IDLE) && truth (Cfg_auto_wake B6) then
    let* (B7, _) := m_wake_m B6 in Some (B7, tt)
  else Some (B6, tt).

(* :319-328, e1 after the desk fields *)
Definition mr_e1 (off : Z) (B4 : list byte) : option (list byte * unit) :=
  if 0 <=? off then m_maybe_online_m (set_M_e1_us (set_M_foreign B4 0) 1)
  else
    let B5 := set_M_foreign B4 1 in
    let* fo := int_inc (OW_foreign B5) in
    let B6 := set_OW_foreign B5 fo in
    if (M_state B6 =? S_ONLINE) || (M_state B6 =? S_WAKING) then m_lost_m B6 R_FOREIGN
    else Some (B6, tt).

(* :308-328, after host_offset *)
Definition mr_ann2 (I : timg) (fr : tframe) (n off : Z) (B2 : list byte) : option (list byte * unit) :=
  let f := mr_f fr n in
  let body := skipn (Z.to_nat (sf_body f)) (tf_bytes fr) in
  let* d := int_inc (OW_desk B2) in
  let B3 := set_OW_desk_off (set_OW_desk B2 d) off in
  let* (_, dp) := desk_named_m I B3 body in
  let B4 := set_OW_desk_body (set_OW_desk_p B3 dp) (tf_addr fr + sf_body f) in
  if sf_cmd f =? SPEC_CMD_E0 then mr_e0 B4 else mr_e1 off B4.

(* :303-329 *)
Definition mr_ann (I : timg) (fr : tframe) (n : Z) (B2 : list byte) : option (list byte * unit) :=
  let f := mr_f fr n in
  let body := skipn (Z.to_nat (sf_body f)) (tf_bytes fr) in
  if sf_body_len f <? SPEC_ANN_MIN then Some (B2, tt) else
  let* (_, off) := if sf_cmd f =? SPEC_CMD_E1 then host_offset_m B2 body else Some (B2, -1) in
  mr_ann2 I fr n off B2.

(* :332-342 *)
Definition mr_ack (fr : tframe) (n : Z) (B2 : list byte) : option (list byte * unit) :=
  let f := mr_f fr n in
  if truth (M_fly_on B2) && (sf_ack f =? M_fly_counter B2) then
    let* a := int_inc (OW_acked B2) in
    let B3 := set_OW_acked B2 a in
    let B4 := set_OW_acked_counter B3 (M_fly_counter B3) in
    let B5 := set_OW_acked_retry B4 (M_fly_retries B4) in
    let B6 := set_M_fly_on B5 0 in
    if M_state B6 =? S_WAKING then m_maybe_online_m (set_M_e2_acked B6 1)
    else Some (B6, tt)
  else Some (B2, tt).

(* :356-364, the OW.dn[] record *)
Definition mr_dn (fr : tframe) (n : Z) (B5 : list byte) : option (list byte * unit) :=
  let f := mr_f fr n in
  let nd := OW_ndata B5 in
  let* B6 :=
    if nd <? 2 then
      if nd <? 0 then None
      else Some (set_OW_dn_retry (set_OW_dn_counter (set_OW_dn_len (set_OW_dn_body B5 nd (tf_addr fr + sf_body f))
                    nd (sf_body_len f)) nd (sf_send f)) nd (sf_retry f))
    else Some B5 in
  let* nd1 := int_inc nd in
  Some (set_OW_ndata B6 nd1, tt).

(* :352-364, after the desk counter check *)
Definition mr_data3 (fr : tframe) (n : Z) (B4 : list byte) : option (list byte * unit) :=
  let f := mr_f fr n in
  let body := skipn (Z.to_nat (sf_body f)) (tf_bytes fr) in
  let B5 := set_M_desk_counter_valid (set_M_desk_counter B4 (sf_send f)) 1 in
  if (sf_body_len f =? 1) && (at8 body 0 =? 0) then Some (B5, tt)
  else mr_dn fr n B5.

(* :352-364 *)
Definition mr_data2 (fr : tframe) (n : Z) (B4 : list byte) : option (list byte * unit) :=
  let f := mr_f fr n in
  if truth (M_desk_counter_valid B4) && (sf_send f =? M_desk_counter B4) && truth (sf_retry f) then Some (B4, tt)
  else mr_data3 fr n B4.

(* :344-364 *)
Definition mr_data (fr : tframe) (n : Z) (B2 : list byte) : option (list byte * unit) :=
  let f := mr_f fr n in
  let* ak := int_inc (OW_acks B2) in
  let B3 := set_M_fail (set_OW_acks B2 ak) 0 in
  let B4 := if truth (sf_retry f) then set_M_backoff_until B3 (u64 (g_now B3 + h_ms_m (Cfg_backoff_ms B3)))
            else B3 in
  mr_data2 fr n B4.

(* :366-368 *)
Definition mr_e3 (B2 : list byte) : option (list byte * unit) :=
  if (M_state B2 =? S_ONLINE) || (M_state B2 =? S_WAKING) then m_lost_m B2 R_DESK_DISCONNECT
  else Some (B2, tt).

(* :302-372 *)
Definition mr_sw (I : timg) (fr : tframe) (n : Z) (B2 : list byte) : option (list byte * unit) :=
  let fc := sf_cmd (mr_f fr n) in
  if (fc =? SPEC_CMD_E0) || (fc =? SPEC_CMD_E1) then mr_ann I fr n B2
  else if fc =? SPEC_CMD_ACK then mr_ack fr n B2
  else if fc =? SPEC_CMD_DATA then mr_data fr n B2
  else if fc =? SPEC_CMD_E3 then mr_e3 B2
  else Some (B2, tt).

(* :299-301, :373-374 *)
Definition mr_k (I : timg) (fr : tframe) (n : Z) (B1 : list byte) : option (list byte * Z) :=
  if M_state B1 =? S_CLOSED then Some (B1, 0)
  else
    let* (B3, _) := mr_sw I fr n (set_M_last_rx B1 (g_now B1)) in
    let* (B4, _) := m_tick_m B3 in
    Some (B4, 1).

Lemma mr_unfold : forall I fr B n, m_rx_m I (Some fr) B n =
  if (n <? 0) || (Z.of_nat (length (tf_bytes fr)) <? n) then None else
  if negb (sf_code (mr_f fr n) =? SPEC_OK) then Some (B, 0) else
  let src := sub (tf_bytes fr) (sf_src (mr_f fr n)) 6 in
  let dst := sub (tf_bytes fr) (sf_dst (mr_f fr n)) 6 in
  let fc := sf_cmd (mr_f fr n) in
  if beq_bytes src HOST || (negb (beq_bytes dst HOST) && negb (beq_bytes dst SPEC_BCAST)) then Some (B, 0)
  else if truth (M_desk_known B) then
    if beq_bytes src (M_desk B) then mr_k I fr n B else Some (B, 0)
  else if negb ((fc =? SPEC_CMD_E0) || (fc =? SPEC_CMD_E1)) then Some (B, 0)
  else if negb (beq_bytes (firstn 3 src) SPEC_OUI) then Some (B, 0)
  else mr_k I fr n (set_M_desk_known (set_M_desk B src) 1).
Proof.
  intros I fr B n.
  unfold m_rx_m, mr_k, mr_sw, mr_ann, mr_ann2, mr_e0, mr_e1, mr_ack, mr_data, mr_data2, mr_data3, mr_dn,
    mr_e3, mr_f.
  cbv beta zeta. reflexivity.
Qed.

(* ---- spec_read_frame (DgnSpec.v:227-250) ---- *)

Lemma mr_lor_range : forall a b k, 0 <= k -> 0 <= a < 2 ^ k -> 0 <= b < 2 ^ k -> 0 <= Z.lor a b < 2 ^ k.
Proof.
  intros a b k Hk Ha Hb. split; [apply Z.lor_nonneg; lia|].
  apply Z_bounded_by_bits; [lia | apply Z.lor_nonneg; lia |].
  intros j Hj. rewrite Z.lor_spec, (Z_testbit_high k a j), (Z_testbit_high k b j) by lia. reflexivity.
Qed.

Lemma mr_byte_at_range : forall (l : list byte) i, 0 <= byte_at (zs l) i < 256.
Proof.
  intros l i. unfold byte_at, zs.
  destruct (nth_in_or_default (Z.to_nat i) (map bv_unsigned l) 0) as [H|H].
  - apply in_map_iff in H. destruct H as (x & <- & _). pose proof (bv_unsigned_in_range 8 x) as R.
    unfold bv_modulus in R. exact R.
  - rewrite H. lia.
Qed.

Lemma mr_be32_range : forall (l : list byte) p, 0 <= spec_be32 (zs l) p < 2 ^ 32.
Proof.
  intros l p. unfold spec_be32, u32.
  pose proof (mr_byte_at_range l (p + 3)) as R3.
  repeat apply mr_lor_range; try lia; apply Z.mod_pos_bound; lia.
Qed.

Ltac mr_rec := cbv beta zeta iota delta
  [sf_code sf_dst sf_src sf_body sf_body_len sf_cmd sf_retry sf_send sf_ack
   SPEC_OK SPEC_E_SHORT SPEC_E_ETHERTYPE SPEC_E_LENGTH].

Lemma mr_srf_code : forall b len, -4 <= sf_code (spec_read_frame b len) <= 0.
Proof.
  intros b len. unfold spec_read_frame.
  destruct (len <? SPEC_BODY_AT); [mr_rec; lia|].
  destruct (negb (spec_be16 b 12 =? SPEC_ETHERTYPE)); [mr_rec; lia|].
  destruct ((spec_be16 b SPEC_AT_NUMBYTES <? SPEC_HDR) || (len - SPEC_ETH_HDR <? spec_be16 b SPEC_AT_NUMBYTES));
    mr_rec; lia.
Qed.

Lemma mr_srf_ok : forall (l : list byte) len, sf_code (spec_read_frame (zs l) len) = SPEC_OK ->
  let f := spec_read_frame (zs l) len in
  sf_dst f = 0 /\ sf_src f = 6 /\ sf_body f = 30 /\ 30 <= len /\ 0 <= sf_body_len f /\ 30 + sf_body_len f <= len /\
  0 <= sf_cmd f < 256 /\ 0 <= sf_retry f < 2 ^ 16 /\ 0 <= sf_send f < 2 ^ 32 /\ 0 <= sf_ack f < 2 ^ 32.
Proof.
  intros l len H. cbv zeta. revert H. unfold spec_read_frame.
  destruct (len <? SPEC_BODY_AT) eqn:E1; [mr_rec; discriminate|].
  destruct (negb (spec_be16 (zs l) 12 =? SPEC_ETHERTYPE)) eqn:E2; [mr_rec; discriminate|].
  destruct ((spec_be16 (zs l) SPEC_AT_NUMBYTES <? SPEC_HDR) ||
            (len - SPEC_ETH_HDR <? spec_be16 (zs l) SPEC_AT_NUMBYTES)) eqn:E3; [mr_rec; discriminate|].
  intros _. mr_rec.
  apply Z.ltb_ge in E1. apply orb_false_iff in E3. destruct E3 as [E3 E4].
  apply Z.ltb_ge in E3. apply Z.ltb_ge in E4.
  unfold SPEC_BODY_AT, SPEC_HDR, SPEC_ETH_HDR, SPEC_MAC in *.
  split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [lia|].
  split; [lia|]. split; [lia|]. split; [apply mr_byte_at_range|].
  split; [unfold spec_be16, u16; apply Z.mod_pos_bound; lia|].
  split; apply mr_be32_range.
Qed.

(* ---- memcmp ---- *)

Lemma mr_beq_iff : forall l r, beq_bytes l r = true <-> zs l = zs r.
Proof. intros l r. unfold beq_bytes. destruct (list_eq_dec Z.eq_dec (zs l) (zs r)); split; congruence. Qed.

Lemma mr_memcmp : forall k l r v, memcmp_model l r k = Some v -> length l = k -> length r = k ->
  -256 < v < 256 /\ (v =? 0) = beq_bytes l r.
Proof.
  induction k as [|k IH]; intros l r v H Ll Lr.
  - destruct l; [|discriminate]. destruct r; [|discriminate]. cbn in H. injection H as <-.
    split; [lia|]. reflexivity.
  - destruct l as [|a l]; [discriminate|]. destruct r as [|b r]; [discriminate|].
    cbn in Ll, Lr. injection Ll as Ll. injection Lr as Lr. cbn [memcmp_model] in H.
    pose proof (bv_unsigned_in_range 8 a) as Ra. pose proof (bv_unsigned_in_range 8 b) as Rb.
    unfold bv_modulus in Ra, Rb. change (2 ^ Z.of_N 8) with 256 in Ra, Rb.
    destruct (Z.eqb_spec (bv_unsigned a) (bv_unsigned b)) as [Eab|Nab].
    + destruct (IH l r v H Ll Lr) as [Rv Ev]. split; [exact Rv|]. rewrite Ev.
      destruct (beq_bytes l r) eqn:E.
      * symmetry. apply mr_beq_iff. apply mr_beq_iff in E. cbn [zs map]. unfold zs in E. rewrite E, Eab. reflexivity.
      * symmetry. destruct (beq_bytes (a :: l) (b :: r)) eqn:E2; [|reflexivity].
        apply mr_beq_iff in E2. cbn [zs map] in E2. injection E2 as _ E2.
        assert (E3 : beq_bytes l r = true) by (apply mr_beq_iff; exact E2). congruence.
    + injection H as <-. split; [lia|].
      destruct (beq_bytes (a :: l) (b :: r)) eqn:E2.
      * apply mr_beq_iff in E2. cbn [zs map] in E2. injection E2 as E2 _. contradiction.
      * apply Z.eqb_neq. lia.
Qed.

(* ---- memory pieces ---- *)

Lemma mr_bsub : forall m a (bs : list byte) k n, bytes_at rsegs m a bs -> 0 <= k ->
  k + Z.of_nat n <= Z.of_nat (length bs) -> bytes_at rsegs m (a + k) (sub bs k n).
Proof.
  intros m a bs k n (Ha & Hl & H) Hk Hn.
  assert (L : length (sub bs k n) = n) by (apply length_sub; lia).
  split; [lia|]. split; [rewrite L; lia|].
  intros i Hi. rewrite L in Hi. rewrite ne_sub by lia.
  replace (i <? n)%nat with true by (symmetry; apply Nat.ltb_lt; lia).
  replace (a + k + Z.of_nat i) with (a + Z.of_nat (Z.to_nat k + i)) by lia.
  apply H. lia.
Qed.

Lemma mr_bskip : forall m a (bs : list byte) k, bytes_at rsegs m a bs -> (k <= length bs)%nat ->
  bytes_at rsegs m (a + Z.of_nat k) (skipn k bs).
Proof.
  intros m a bs k (Ha & Hl & H) Hk.
  assert (L : length (skipn k bs) = (length bs - k)%nat) by apply length_skipn.
  split; [lia|]. split; [rewrite L; lia|].
  intros i Hi. rewrite L in Hi. rewrite nth_skipn.
  replace (a + Z.of_nat k + Z.of_nat i) with (a + Z.of_nat (k + i)) by lia.
  apply H. lia.
Qed.

(* the struct spec_frame at sp + 8, cut into the fields the walk loads *)
Definition sf_cells (fa : Z) (f : spec_frame) : list cell :=
  [CB 8 (put 4 (sf_code f) ++ repeat (b8 0) 4);
   C8 (Z_to_bv 64 (sf_ptr fa f (sf_dst f)));
   C8 (Z_to_bv 64 (sf_ptr fa f (sf_src f)));
   CB 6 (put 2 (sf_ethertype f) ++ put 2 (sf_numbytes f) ++ put 2 (sf_sum f));
   C2 (Z_to_bv 64 (sf_retry f));
   C4 (Z_to_bv 64 (sf_send f));
   C4 (Z_to_bv 64 (sf_ack f));
   C1 (Z_to_bv 8 (sf_cmd f));
   CB 7 (put 1 (sf_ncmds f) ++ repeat (b8 0) 6);
   C8 (Z_to_bv 64 (sf_ptr fa f (sf_body f)));
   C8 (Z_to_bv 64 (sf_body_len f));
   CB 16 (put 8 (sf_pad_len f) ++ put 2 (sf_body_sum f) ++ repeat (b8 0) 6)].

Lemma mr_sf_bytes : forall fa f, cells_bytes (sf_cells fa f) = sf_bytes fa f.
Proof.
  intros fa f. unfold sf_cells, sf_bytes. cbn [cells_bytes cbytes].
  rewrite !le8_put, !le4_put, le2_put.
  change [Z_to_bv 8 (sf_cmd f)] with (put 1 (sf_cmd f)).
  rewrite <- !app_assoc. rewrite app_nil_r. reflexivity.
Qed.

Lemma mr_sf_cells : forall m fp fa f, rw_cells rsegs m fp [CB 80 (sf_bytes fa f)] -> rw_cells rsegs m fp (sf_cells fa f).
Proof.
  intros m fp fa f [[_ Hb] Hw]. split; [split|].
  - cbn [cells_wf cell_wf sf_cells].
    rewrite !length_app, !length_put, !repeat_length. repeat split.
  - rewrite mr_sf_bytes. cbn [cells_bytes cbytes] in Hb. rewrite app_nil_r in Hb. exact Hb.
  - change (cells_size (sf_cells fa f)) with 80%nat. exact Hw.
Qed.

Lemma mr_ro : forall m, mem_inv rsegs m ->
  bytes_at rsegs m 0x10470 HOST /\ bytes_at rsegs m 0x1047c SPEC_BCAST /\ bytes_at rsegs m 0x10482 SPEC_OUI.
Proof.
  intros m MI.
  split; [|split]; (apply ro_bytes_at; [exact MI | vm_compute; discriminate | vm_compute; discriminate |]);
    apply ro_bytes_b_sound; vm_compute; reflexivity.
Qed.

(* ---- machine-word arithmetic ---- *)

Lemma mr_mod32_64 : forall v, (v mod 2 ^ 64) mod 2 ^ 32 = v mod 2 ^ 32.
Proof.
  intros v. change (2 ^ 64) with 18446744073709551616. change (2 ^ 32) with 4294967296.
  Z.div_mod_to_equations. lia.
Qed.

Lemma mr_signed_lit : forall z, -2 ^ 63 <= z < 2 ^ 63 -> bv_signed (Z_to_bv 64 z) = z.
Proof.
  intros z Hz. rewrite Z_to_bv_signed. unfold bv_swrap, bv_wrap.
  change (bv_half_modulus 64) with (2 ^ 63). change (bv_modulus 64) with (2 ^ 64).
  rewrite Z.mod_small by lia. lia.
Qed.

Lemma mr_eqb : forall a b, -2 ^ 63 <= a < 2 ^ 63 -> -2 ^ 63 <= b < 2 ^ 63 ->
  bv_eqb (Z_to_bv 64 a) (Z_to_bv 64 b) = (a =? b).
Proof.
  intros a b Ha Hb. unfold bv_eqb. rewrite !unsigned_lit_wrap.
  change (2 ^ 64) with 18446744073709551616 in *. change (2 ^ 63) with 9223372036854775808 in *.
  destruct (Z.eqb_spec a b) as [->|N]; [apply Z.eqb_refl|].
  apply Z.eqb_neq. intros E. apply N. revert E. Z.div_mod_to_equations. lia.
Qed.

Lemma mr_lts : forall a b, -2 ^ 63 <= a < 2 ^ 63 -> -2 ^ 63 <= b < 2 ^ 63 ->
  bv_lts (Z_to_bv 64 a) (Z_to_bv 64 b) = (a <? b).
Proof. intros a b Ha Hb. unfold bv_lts. rewrite !mr_signed_lit by assumption. reflexivity. Qed.

Lemma mr_ltu : forall a b, 0 <= a < 2 ^ 64 -> 0 <= b < 2 ^ 64 ->
  bv_ltu (Z_to_bv 64 a) (Z_to_bv 64 b) = (a <? b).
Proof. intros a b Ha Hb. unfold bv_ltu. rewrite !unsigned_lit by assumption. reflexivity. Qed.

Lemma mr_swrap32_eq : forall v, bv_swrap 32 v = (v + 2 ^ 31) mod 2 ^ 32 - 2 ^ 31.
Proof.
  intros v. unfold bv_swrap, bv_wrap.
  change (bv_half_modulus 32) with (2 ^ 31). change (bv_modulus 32) with (2 ^ 32). reflexivity.
Qed.

Lemma mr_swrap32_small : forall v, -2 ^ 31 <= v < 2 ^ 31 -> bv_swrap 32 v = v.
Proof. intros v H. rewrite mr_swrap32_eq, Z.mod_small by lia. lia. Qed.

Lemma mr_swrap32_range : forall v, -2 ^ 31 <= bv_swrap 32 v < 2 ^ 31.
Proof.
  intros v. rewrite mr_swrap32_eq. pose proof (Z.mod_pos_bound (v + 2 ^ 31) (2 ^ 32) ltac:(lia)). lia.
Qed.

Lemma mr_swrap32_mod : forall a b, a mod 2 ^ 32 = b mod 2 ^ 32 -> bv_swrap 32 a = bv_swrap 32 b.
Proof.
  intros a b H. rewrite !mr_swrap32_eq. f_equal.
  rewrite <- Zplus_mod_idemp_l, H, Zplus_mod_idemp_l. reflexivity.
Qed.

Lemma mr_swrap32_lit : forall v, bv_swrap 32 (bv_unsigned (Z_to_bv 64 v)) = bv_swrap 32 v.
Proof. intros v. rewrite unsigned_lit_wrap. apply mr_swrap32_mod. apply mr_mod32_64. Qed.

Lemma mr_swrap32_inj : forall a b, 0 <= a < 2 ^ 32 -> 0 <= b < 2 ^ 32 ->
  (bv_swrap 32 a =? bv_swrap 32 b) = (a =? b).
Proof.
  intros a b Ha Hb. rewrite !mr_swrap32_eq.
  destruct (Z.eqb_spec a b) as [->|N]; [apply Z.eqb_refl|].
  apply Z.eqb_neq. intros E. apply N.
  assert (E2 : (a + 2 ^ 31) mod 2 ^ 32 = (b + 2 ^ 31) mod 2 ^ 32) by lia. revert E2.
  change (2 ^ 32) with 4294967296 in *. change (2 ^ 31) with 2147483648 in *.
  Z.div_mod_to_equations. lia.
Qed.

(* After a call: give the post's memory facts their standing names. *)
Ltac mr_names :=
  lazymatch goal with
  | |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      try (match goal with H : mem_inv rsegs mm |- _ => rename H into MIc end);
      try (match goal with H : stk rsegs mm _ _ |- _ => rename H into STc end);
      try (match goal with H : rw_cells rsegs mm W_BASE_UBSAN _ |- _ => rename H into WMc end)
  end.

(* Reduce the model hypothesis after one of its conditions became a literal boolean. *)
Ltac mr_mod H :=
  cbn [negb andb orb] in H; rewrite ?andb_false_r, ?andb_true_r, ?orb_false_r, ?orb_true_r in H;
  cbv beta iota in H.

(* the struct cells of a parsed frame at fa (sf_cells with the OK-branch pointers put in) *)
Definition mr_sfc (fa : Z) (f : spec_frame) : list cell :=
  [CB 8 (put 4 (sf_code f) ++ repeat (b8 0) 4);
   C8 (Z_to_bv 64 (fa + 0));
   C8 (Z_to_bv 64 (fa + 6));
   CB 6 (put 2 (sf_ethertype f) ++ put 2 (sf_numbytes f) ++ put 2 (sf_sum f));
   C2 (Z_to_bv 64 (sf_retry f));
   C4 (Z_to_bv 64 (sf_send f));
   C4 (Z_to_bv 64 (sf_ack f));
   C1 (Z_to_bv 8 (sf_cmd f));
   CB 7 (put 1 (sf_ncmds f) ++ repeat (b8 0) 6);
   C8 (Z_to_bv 64 (fa + 30));
   C8 (Z_to_bv 64 (sf_body_len f));
   CB 16 (put 8 (sf_pad_len f) ++ put 2 (sf_body_sum f) ++ repeat (b8 0) 6)].

Lemma mr_u8 : forall c, 0 <= c < 256 -> bv_unsigned (Z_to_bv 8 c) = c.
Proof.
  intros c Hc. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus.
  change (2 ^ Z.of_N 8) with 256. apply Z.mod_small. lia.
Qed.

Lemma mr_land254 : forall c, 0 <= c < 256 -> (Z.land c 254 =? 224) = ((c =? 224) || (c =? 225)).
Proof.
  intros c Hc.
  assert (H : forallb (fun x => Bool.eqb (Z.land x 254 =? 224) ((x =? 224) || (x =? 225)))
                (map Z.of_nat (seq 0 256)) = true) by (vm_compute; reflexivity).
  rewrite forallb_forall in H.
  assert (IN : In c (map Z.of_nat (seq 0 256))).
  { apply in_map_iff. exists (Z.to_nat c). split; [lia|]. apply in_seq. lia. }
  apply Bool.eqb_prop. exact (H c IN).
Qed.

Lemma mr_land254r : forall c, 0 <= c < 256 -> 0 <= Z.land c 254 < 256.
Proof.
  intros c Hc.
  assert (H : forallb (fun x => (0 <=? Z.land x 254) && (Z.land x 254 <? 256))
                (map Z.of_nat (seq 0 256)) = true) by (vm_compute; reflexivity).
  rewrite forallb_forall in H.
  assert (IN : In c (map Z.of_nat (seq 0 256))).
  { apply in_map_iff. exists (Z.to_nat c). split; [lia|]. apply in_seq. lia. }
  specialize (H c IN). apply andb_prop in H. destruct H as [H1 H2].
  apply Z.leb_le in H1. apply Z.ltb_lt in H2. lia.
Qed.

Lemma mr_firstn3 : forall (bs : list byte) k, firstn 3 (sub bs k 6) = sub bs k 3.
Proof. intros bs k. unfold sub. rewrite firstn_firstn. reflexivity. Qed.

Lemma mr_ltu1 : forall w, -2 ^ 31 <= w < 2 ^ 31 ->
  bv_ltu (Z_to_bv 64 1) (Z_to_bv 64 w) = negb ((w =? 0) || (w =? 1)).
Proof.
  intros w Hw. unfold bv_ltu. rewrite (unsigned_lit 1) by lia. rewrite unsigned_lit_wrap.
  destruct (Z_lt_le_dec w 0) as [L|L].
  - rewrite <- (Z.mod_add w 1 (2 ^ 64)) by lia. rewrite Z.mod_small by lia.
    replace ((w =? 0) || (w =? 1)) with false
      by (symmetry; apply orb_false_intro; apply Z.eqb_neq; lia).
    cbn [negb]. apply Z.ltb_lt. lia.
  - rewrite Z.mod_small by lia.
    destruct (Z.eqb_spec w 0) as [->|N0]; [reflexivity|].
    destruct (Z.eqb_spec w 1) as [->|N1]; [reflexivity|].
    cbn [orb negb]. apply Z.ltb_lt. lia.
Qed.

Lemma mr_st12 : forall st, -2 ^ 31 <= st < 2 ^ 31 ->
  ((bv_swrap 32 (st + -1) =? 0) || (bv_swrap 32 (st + -1) =? 1)) = ((st =? 2) || (st =? 1)).
Proof.
  intros st Hst.
  destruct (Z.eqb_spec st 1) as [->|N1]; [rewrite mr_swrap32_small by lia; reflexivity|].
  destruct (Z.eqb_spec st 2) as [->|N2]; [rewrite mr_swrap32_small by lia; reflexivity|].
  cbn [orb].
  destruct (Z_lt_le_dec st (-2 ^ 31 + 1)) as [L|L].
  - assert (E : st = -2 ^ 31) by lia. subst st. vm_compute. reflexivity.
  - rewrite mr_swrap32_small by lia.
    rewrite (proj2 (Z.eqb_neq _ _)) by lia. rewrite (proj2 (Z.eqb_neq _ _)) by lia. reflexivity.
Qed.

Lemma mr_swrap32_lit_add : forall v d, bv_swrap 32 (bv_unsigned (Z_to_bv 64 v) + d) = bv_swrap 32 (v + d).
Proof.
  intros v d. apply mr_swrap32_mod. rewrite unsigned_lit_wrap.
  change (2 ^ 64) with 18446744073709551616. change (2 ^ 32) with 4294967296.
  Z.div_mod_to_equations. lia.
Qed.

Lemma mr_inc_trap : forall x, -2 ^ 31 <= x < 2 ^ 31 ->
  (bv_swrap 32 (x + 1) <? x) = (x =? 2 ^ 31 - 1).
Proof.
  intros x Hx. destruct (Z.eqb_spec x (2 ^ 31 - 1)) as [->|N].
  - vm_compute. reflexivity.
  - rewrite mr_swrap32_small by lia. apply Z.ltb_ge. lia.
Qed.

Lemma mr_put4_swrap : forall v, put 4 (bv_swrap 32 v) = put 4 v.
Proof.
  intros v. unfold put.
  rewrite <- (Z_to_le_bytes_mod 4 (bv_swrap 32 v) 32) by lia.
  rewrite <- (Z_to_le_bytes_mod 4 v 32) by lia. f_equal.
  rewrite mr_swrap32_eq. change (2 ^ 32) with 4294967296. change (2 ^ 31) with 2147483648.
  Z.div_mod_to_equations. lia.
Qed.

Lemma mr_dcv_fly : forall Bx, length Bx = Z.to_nat W_LEN ->
  set_M_fly_on (set_M_desk_counter_valid Bx 0) 0 = set_M_desk_counter_valid (set_M_fly_on Bx 0) 0.
Proof.
  intros Bx L. unfold set_M_fly_on, set_M_desk_counter_valid, A_M_fly_on, A_M_desk_counter_valid, OFF_M.
  rewrite upd_upd_comm; try reflexivity;
    rewrite ?length_put, ?length_upd_put, ?L; unfold W_LEN; lia.
Qed.

Lemma mr_dcv_fly_m : forall Bx, length Bx = Z.to_nat W_LEN ->
  upd (upd Bx 76 (put 4 0)) 96 (put 4 0) = set_M_desk_counter_valid (set_M_fly_on Bx 0) 0.
Proof. intros Bx L. exact (mr_dcv_fly Bx L). Qed.

Ltac mr_br := cbn [negb orb andb]; cbv beta iota.

Lemma mr_lt12 : forall x, (1 <? x) = negb (x <? 2).
Proof. intros x. destruct (Z.ltb_spec 1 x); destruct (Z.ltb_spec x 2); cbn; first [reflexivity | lia]. Qed.

Lemma mr_firstn1 : forall (bs : list byte) k, (k < length bs)%nat -> firstn 1 (skipn k bs) = [nth k bs (b8 0)].
Proof.
  induction bs as [|b bs IH]; intros k Hk; cbn in Hk; [lia|].
  destruct k as [|k]; [reflexivity|]. cbn [skipn nth]. apply IH. lia.
Qed.

Lemma mr_nth_skipn : forall (l : list byte) k d, nth 0 (skipn k l) d = nth k l d.
Proof. induction l as [|x l IH]; intros [|k] d; cbn; try reflexivity. apply IH. Qed.

Lemma mr_put8_mod : forall a b, a mod 2 ^ 64 = b mod 2 ^ 64 -> put 8 a = put 8 b.
Proof. intros a b H. rewrite <- (put_mod64 8 a), <- (put_mod64 8 b) by lia. rewrite H. reflexivity. Qed.

Lemma mr_eqbu : forall a b, 0 <= a < 2 ^ 64 -> 0 <= b < 2 ^ 64 ->
  bv_eqb (Z_to_bv 64 a) (Z_to_bv 64 b) = (a =? b).
Proof. intros a b Ha Hb. unfold bv_eqb. rewrite !unsigned_lit by assumption. reflexivity. Qed.

Lemma mr_rd1 : forall m a (bs : list byte) k, bytes_at rsegs m a bs -> (k < length bs)%nat ->
  ov_read_bytes rsegs m (Z_to_bv 64 (a + Z.of_nat k)) 1 = Some [nth k bs (b8 0)].
Proof.
  intros m a bs k B Hk.
  pose proof (bytes_at_read rsegs m a bs (Z.of_nat k) 1 B ltac:(lia) ltac:(lia)) as R.
  rewrite Nat2Z.id, mr_firstn1 in R by exact Hk. exact R.
Qed.

Lemma mr_dcv_cnt : forall Bx s, length Bx = Z.to_nat W_LEN ->
  upd (upd Bx 76 (put 4 1)) 80 (put 4 s) = set_M_desk_counter_valid (set_M_desk_counter Bx s) 1.
Proof.
  intros Bx s L. unfold set_M_desk_counter_valid, set_M_desk_counter, A_M_desk_counter_valid, A_M_desk_counter, OFF_M.
  rewrite upd_upd_comm; try reflexivity; rewrite ?length_put, ?length_upd_put, ?L; unfold W_LEN; lia.
Qed.

(* a branch whose condition is a closed term (every operand a literal) *)
Ltac mr_vbr :=
  lazymatch goal with
  | |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
      let v := eval vm_compute in c in change c with v; cbv beta iota
  end.

(* a callee that wrote one cell keeps a stack fact whose span may meet the cell: the written bytes are there *)
Lemma mr_stk_cell : forall m m' lo hi X n cs,
  stk rsegs m lo hi -> munch [(X, X + n)] m m' -> wmono rsegs m m' ->
  rw_cells rsegs m' X cs -> Z.of_nat (cells_size cs) = n -> stk rsegs m' lo hi.
Proof.
  intros m m' lo hi X n cs (H1 & H2 & H) MU WM [[Hwf (HXa & HXl & Hb)] Hw] Hn.
  rewrite cells_bytes_length in HXl, Hb by exact Hwf.
  split; [lia|]. split; [lia|]. intros a Ha.
  destruct (H a Ha) as [Hv [b Hb0]].
  split; [apply WM; exact Hv|].
  destruct (Z_lt_le_dec a X) as [L|L].
  - exists b. unfold mrd in *. rewrite (MU (wa a)); [exact Hb0|].
    cbn [outside]. rewrite wa_unsigned by lia. split; [lia | exact I].
  - destruct (Z_lt_le_dec a (X + n)) as [L2|L2].
    + assert (Hi : (Z.to_nat (a - X) < cells_size cs)%nat) by lia.
      pose proof (Hb (Z.to_nat (a - X)) Hi) as R.
      replace (X + Z.of_nat (Z.to_nat (a - X))) with a in R by lia.
      destruct (nth_error (cells_bytes cs) (Z.to_nat (a - X))) as [c|] eqn:E.
      * exists c. exact R.
      * apply nth_error_None in E. rewrite cells_bytes_length in E by exact Hwf. lia.
    + exists b. unfold mrd in *. rewrite (MU (wa a)); [exact Hb0|].
      cbn [outside]. rewrite wa_unsigned by lia. split; [lia | exact I].
Qed.

(* the value a sign- / zero-extending load leaves in its register *)
Ltac mr_ext :=
  repeat first [ progress unfold sx32 | progress unfold zx32 | progress unfold sx16 | progress unfold zx16
               | progress unfold sxb | progress unfold zxb ].

(* ---- a field read of an updated world is the read of the world, off the written span ---- *)

Lemma mr_lu : forall (Bx v : list byte) k, length Bx = Z.to_nat W_LEN -> 0 <= k ->
  k + Z.of_nat (length v) <= W_LEN -> length (upd Bx k v) = Z.to_nat W_LEN.
Proof.
  intros Bx v k L Hk Hv. rewrite length_upd; [exact L | lia | rewrite L; unfold W_LEN in *; lia].
Qed.

Lemma mr_uo : forall (Bx v : list byte) (k k' : Z) (nn : nat),
  length Bx = Z.to_nat W_LEN -> 0 <= k -> 0 <= k' -> k + Z.of_nat (length v) <= W_LEN ->
  (k' + Z.of_nat nn <= k \/ k + Z.of_nat (length v) <= k') ->
  u_at (upd Bx k v) k' nn = u_at Bx k' nn.
Proof.
  intros Bx v k k' nn L Hk Hk' Hv Hd. apply u_at_upd_out; [lia | lia | lia |].
  rewrite L. unfold W_LEN in *. lia.
Qed.

Ltac mr_wl L :=
  first [ exact L | apply mr_lu; [ mr_wl L | lia | rewrite ?length_put; unfold W_LEN; lia ] ].
Ltac mr_push L :=
  repeat (rewrite mr_uo by first [ mr_wl L | lia | (rewrite ?length_put; unfold W_LEN in *; lia) ]).

Ltac mr_dcvfly H L :=
  lazymatch type of H with context [upd (upd ?Bx 76 (put 4 0)) 96 (put 4 0)] =>
    rewrite (mr_dcv_fly_m Bx ltac:(mr_wl L)) in H end.

Ltac mr_unf :=
  unfold M_state, M_fly_on, M_fly_counter, M_fly_retries, M_desk_counter_valid, M_desk_counter,
         M_foreign, M_e1_us, M_e2_acked, M_desk_known, M_fail, M_last_rx, M_backoff_until,
         OW_acks, OW_desk, OW_foreign, OW_acked, OW_ndata, g_now, Cfg_auto_wake, Cfg_backoff_ms,
         set_M_fly_on, set_M_e2_acked, set_M_e1_us, set_M_foreign, set_M_desk_counter_valid,
         set_M_desk_counter, set_M_fail, set_M_last_rx, set_M_backoff_until, set_M_desk, set_M_desk_known,
         set_OW_acked, set_OW_acked_counter, set_OW_acked_retry, set_OW_acks, set_OW_desk, set_OW_desk_off,
         set_OW_desk_p, set_OW_desk_body, set_OW_foreign, set_OW_ndata,
         set_OW_dn_body, set_OW_dn_len, set_OW_dn_counter, set_OW_dn_retry, s32_at,
         A_M_state, A_M_fly_on, A_M_fly_counter, A_M_fly_retries, A_M_desk_counter_valid, A_M_desk_counter,
         A_M_foreign, A_M_e1_us, A_M_e2_acked, A_M_desk_known, A_M_fail, A_M_last_rx, A_M_backoff_until,
         A_M_desk, A_OW_acks, A_OW_desk, A_OW_foreign, A_OW_acked, A_OW_ndata, A_OW_acked_counter,
         A_OW_acked_retry, A_OW_desk_off, A_OW_desk_p, A_OW_desk_body, A_OW_dn_body, A_OW_dn_len,
         A_OW_dn_counter, A_OW_dn_retry, A_Cfg_auto_wake, A_Cfg_backoff_ms,
         OFF_M, OFF_OW, OFF_g_now, OFF_g_cfg.

(* read a getter of an updated world as the getter of the world it was built from *)
Ltac mr_pushH H Bb Lb :=
  repeat match type of H with
  | context [M_state ?W] =>
      lazymatch W with Bb => fail | _ => idtac end;
      let E := fresh "EP" in assert (E : M_state W = M_state Bb) by (mr_unf; mr_push Lb; reflexivity);
      rewrite E in H; clear E
  | context [OW_foreign ?W] =>
      lazymatch W with Bb => fail | _ => idtac end;
      let E := fresh "EP" in assert (E : OW_foreign W = OW_foreign Bb) by (mr_unf; mr_push Lb; reflexivity);
      rewrite E in H; clear E
  | context [Cfg_auto_wake ?W] =>
      lazymatch W with Bb => fail | _ => idtac end;
      let E := fresh "EP" in assert (E : Cfg_auto_wake W = Cfg_auto_wake Bb) by (mr_unf; mr_push Lb; reflexivity);
      rewrite E in H; clear E
  end.

(* the same for a value the machine loaded: s32_at W k of an updated world *)
Ltac mr_pushG k getter Bb Lb :=
  lazymatch goal with |- context [s32_at ?W k] =>
    let E := fresh "EP" in assert (E : s32_at W k = getter Bb) by (mr_unf; mr_push Lb; reflexivity);
    rewrite E; clear E
  end.

Lemma mr_ho_range : forall fuel body i r, host_offset_loop fuel body i = Some r ->
  r = -1 \/ (i <= r /\ r < i + Z.of_nat fuel).
Proof.
  induction fuel as [|fuel IH]; intros body i r H; cbn [host_offset_loop] in H.
  - injection H as <-. left. reflexivity.
  - destruct (i + SPEC_MAC <=? SPEC_ANN_UNKNOWN); [|injection H as <-; left; reflexivity].
    destruct (Z.of_nat (length body) <? i + SPEC_MAC); [discriminate|].
    destruct (beq_bytes (sub body i 6) HOST); [injection H as <-; right; lia|].
    destruct (IH body (i + 1) r H) as [E|E]; [left; exact E | right; lia].
Qed.

Lemma mr_ho_off : forall B2 body Bh off, host_offset_m B2 body = Some (Bh, off) -> Bh = B2 /\ -1 <= off < 10.
Proof.
  intros B2 body Bh off H. unfold host_offset_m in H.
  destruct (host_offset_loop 10 body 0) as [rr|] eqn:E; [|discriminate].
  injection H as <- <-. split; [reflexivity|].
  destruct (mr_ho_range _ _ _ _ E) as [->|R]; lia.
Qed.

Lemma mr_dn_world : forall I B3 body B4 dp, desk_named_m I B3 body = Some (B4, dp) -> B4 = B3.
Proof.
  intros I B3 body B4 dp H. unfold desk_named_m in H. cbv zeta in H.
  destruct (list_strz_len (skipn (Z.to_nat SPEC_ANN_NAME) body)) as [k|]; [|discriminate].
  destruct ((k =? 8)%nat && beq_bytes (firstn k (skipn (Z.to_nat SPEC_ANN_NAME) body)) C24_NAME);
    [injection H as <- _; reflexivity|].
  destruct ((k =? 8)%nat && beq_bytes (firstn k (skipn (Z.to_nat SPEC_ANN_NAME) body)) PC_NAME);
    injection H as <- _; reflexivity.
Qed.

Lemma mr_e1_fo : forall Bx, length Bx = Z.to_nat W_LEN ->
  upd (upd Bx 20 (put 4 1)) 24 (put 4 0) = set_M_e1_us (set_M_foreign Bx 0) 1.
Proof.
  intros Bx L. unfold set_M_e1_us, set_M_foreign, A_M_e1_us, A_M_foreign, OFF_M.
  rewrite upd_upd_comm; try reflexivity; rewrite ?length_put, ?length_upd_put, ?L; unfold W_LEN; lia.
Qed.

(* mr_ack with every field read taken of the world it starts from *)
Lemma mr_ack_norm : forall frx nx B2, length B2 = Z.to_nat W_LEN ->
  mr_ack frx nx B2 =
  if negb (M_fly_on B2 =? 0) && (sf_ack (mr_f frx nx) =? M_fly_counter B2) then
    if OW_acked B2 =? INT_MAX then None else
    if M_state B2 =? 1
    then m_maybe_online_m (set_M_e2_acked (set_M_fly_on (set_OW_acked_retry (set_OW_acked_counter
           (set_OW_acked B2 (OW_acked B2 + 1)) (M_fly_counter B2)) (M_fly_retries B2)) 0) 1)
    else Some (set_M_fly_on (set_OW_acked_retry (set_OW_acked_counter
           (set_OW_acked B2 (OW_acked B2 + 1)) (M_fly_counter B2)) (M_fly_retries B2)) 0, tt)
  else Some (B2, tt).
Proof.
  intros frx nx B2 L. unfold mr_ack, truth, S_WAKING, int_inc.
  destruct (negb (M_fly_on B2 =? 0) && (sf_ack (mr_f frx nx) =? M_fly_counter B2)); [|reflexivity].
  destruct (OW_acked B2 =? INT_MAX); [reflexivity|].
  cbv beta zeta iota.
  mr_unf. mr_push L. reflexivity.
Qed.

Theorem m_rx_holds : bcmp_contract -> memcpy_contract -> spec_read_frame_contract -> host_offset_contract ->
  desk_named_contract -> m_set_contract -> m_wake_contract -> m_maybe_online_contract -> m_tick_contract ->
  m_rx_contract.
Proof.
  intros BC MC SRF HO DN MSET MW MMO MT.
  unfold bcmp_contract, BCMP in BC. unfold memcpy_contract in MC.
  unfold spec_read_frame_contract, spec_read_frame_ENTRY, spec_read_frame_FRAME in SRF.
  unfold host_offset_contract, host_offset_ENTRY, host_offset_FRAME in HO.
  unfold desk_named_contract, desk_named_ENTRY, desk_named_FRAME in DN.
  unfold m_set_contract, m_set_ENTRY, m_set_FRAME in MSET.
  unfold m_wake_contract, m_wake_ENTRY, m_wake_FRAME in MW.
  unfold m_maybe_online_contract, m_maybe_online_ENTRY, m_maybe_online_FRAME in MMO.
  unfold m_tick_contract, m_tick_ENTRY, m_tick_FRAME in MT.
  unfold m_rx_contract, m_rx_ENTRY, m_rx_FRAME.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo
    B B' fr n r -> -> TF NW S16 ST LO WOS MI WM MOD.
  destruct TF as (Hp & BF & OWd & OWn).
  unfold off_world in OWd. unfold off_window in OWn. unfold w_off_stack in WOS.
  pose proof (bv_unsigned_in_range 64 sp) as Rsp. unfold bv_modulus in Rsp.
  pose proof (bytes_at_bound rsegs m _ _ BF) as FB.
  rewrite mr_unfold in MOD. cbv zeta in MOD.
  destruct ((n <? 0) || (Z.of_nat (length (tf_bytes fr)) <? n)) eqn:HN; [discriminate|].
  apply orb_false_iff in HN. destruct HN as [HN1 HN2]. apply Z.ltb_ge in HN1. apply Z.ltb_ge in HN2.
  pose proof (munch_refl [(bv_unsigned sp - 208, bv_unsigned sp); (W_BASE_UBSAN, W_BASE_UBSAN + W_LEN)] m) as MU.
  pose proof (wmono_refl rsegs m) as WMo.
  lazymatch goal with |- evt _ ?Q _ => set (QQ := Q) end.
  wk_facts.
  carve_frame 40%nat ST. rename FR into FR40.
  carve_frame 80%nat ST. rename FR into SF.
  carve_frame 8%nat ST. rename FR into FR8.
  assert (Hsp : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -128)) = bv_unsigned sp + -128)
    by (apply unsigned_lit; lia).
  (* ---- the epilogue, 0x15930 ---- *)
  assert (EPI : forall (mz : word -> option byte) (Bz : list byte) (rz : Z)
                  (raz x5 x6 x7 x8 x9 x11 x12 x13 x14 x15 x16 x17 x18 x19 x28 x29 x30 x31 : word)
                  (j8 : list byte) (sfcs : list cell),
    rz = r -> Bz = B' ->
    rw_cells rsegs mz (bv_unsigned sp + -40) [C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
    rw_cells rsegs mz (bv_unsigned sp + -120) sfcs -> cells_size sfcs = 80%nat ->
    rw_cells rsegs mz (bv_unsigned sp + -128) [CB 8 j8] ->
    stk rsegs mz lo (bv_unsigned sp + -128) ->
    munch [(bv_unsigned sp - 208, bv_unsigned sp); (W_BASE_UBSAN, W_BASE_UBSAN + W_LEN)] m mz ->
    wmono rsegs m mz -> mem_inv rsegs mz -> wmem rsegs mz Bz ->
    evt rsegs QQ
      (MS (mkR raz (Z_to_bv 64 (bv_unsigned sp + -128)) gp tp x5 x6 x7 x8 x9 (Z_to_bv 64 rz)
               x11 x12 x13 x14 x15 x16 x17 x18 x19 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
          F (Z_to_bv 64 0x15930) fc None mz (seg_rom rsegs))).
  { clear MOD MU WMo WM MI ST FR40 SF FR8 BF.
    intros mz Bz rz raz x5 x6 x7 x8 x9 x11 x12 x13 x14 x15 x16 x17 x18 x19 x28 x29 x30 x31 j8 sfcs -> ->
      FRz SFz HSZ F8z STz MUz WMz MIz WMEMz.
    do 6 step.
    release_frame F8z STz (bv_unsigned sp + -120).
    eapply stk_release in SFz; [| exact STz | lia]. clear STz. rename SFz into STz.
    rewrite HSZ in STz. replace (bv_unsigned sp + -120 + Z.of_nat 80) with (bv_unsigned sp + -40) in STz by lia.
    release_frame FRz STz (bv_unsigned sp).
    step.
    apply evt_done. unfold QQ. do 15 eexists. split; [reflexivity|].
    split; [exact MUz|]. split; [exact WMz|]. split; [exact MIz|]. split; [exact STz|]. exact WMEMz. }
  (* ---- 0x15c3c: m_tick, then return 1 ---- *)
  assert (TICK : forall (mz : word -> option byte) (Bx : list byte)
                   (raz x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x28 x29 x30 x31 : word)
                   (j8 : list byte) (sfcs : list cell),
    m_tick_m Bx = Some (B', tt) -> r = 1 ->
    rw_cells rsegs mz (bv_unsigned sp + -40) [C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
    rw_cells rsegs mz (bv_unsigned sp + -120) sfcs -> cells_size sfcs = 80%nat ->
    rw_cells rsegs mz (bv_unsigned sp + -128) [CB 8 j8] ->
    stk rsegs mz lo (bv_unsigned sp + -128) ->
    munch [(bv_unsigned sp - 208, bv_unsigned sp); (W_BASE_UBSAN, W_BASE_UBSAN + W_LEN)] m mz ->
    wmono rsegs m mz -> mem_inv rsegs mz -> wmem rsegs mz Bx ->
    evt rsegs QQ
      (MS (mkR raz (Z_to_bv 64 (bv_unsigned sp + -128)) gp tp x5 x6 x7 x8 x9 x10
               x11 x12 x13 x14 x15 x16 x17 x18 x19 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
          F (Z_to_bv 64 0x15c3c) fc None mz (seg_rom rsegs))).
  { intros mz Bx raz x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x28 x29 x30 x31 j8 sfcs
      MTx Hr1 FRz SFz HSZ F8z STz MUz WMz MIz WMEMz.
    step.
    lazymatch goal with
    | |- evt ?sg _ (MS _ _ _ _ _ ?mm _) =>
        eapply evt_cut;
        [ eapply MT with (lo := lo) (B := Bx) (B' := B');
          [ rewrite Hsp; Z.div_mod_to_equations; lia | rewrite Hsp; exact STz | rewrite Hsp; lia
          | unfold w_off_stack; rewrite Hsp; lia | exact MIz | exact WMEMz | exact MTx ]
        | wk_post_call sg mm ]
    end.
    mr_names. rewrite Hsp in STc.
    do 2 step.
    eapply EPI; [ lia | reflexivity | exact FRz | exact SFz | exact HSZ | exact F8z
                | exact STc | exact MUz | exact WMz | exact MIc | exact WMc ]. }
  (* ---- 0x15c38: m_maybe_online, then m_tick ---- *)
  assert (MO : forall (mz : word -> option byte) (Bx By : list byte)
                 (raz x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x28 x29 x30 x31 : word)
                 (j8 : list byte) (sfcs : list cell),
    m_maybe_online_m Bx = Some (By, tt) -> m_tick_m By = Some (B', tt) -> r = 1 ->
    rw_cells rsegs mz (bv_unsigned sp + -40) [C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
    rw_cells rsegs mz (bv_unsigned sp + -120) sfcs -> cells_size sfcs = 80%nat ->
    rw_cells rsegs mz (bv_unsigned sp + -128) [CB 8 j8] ->
    stk rsegs mz lo (bv_unsigned sp + -128) ->
    munch [(bv_unsigned sp - 208, bv_unsigned sp); (W_BASE_UBSAN, W_BASE_UBSAN + W_LEN)] m mz ->
    wmono rsegs m mz -> mem_inv rsegs mz -> wmem rsegs mz Bx ->
    evt rsegs QQ
      (MS (mkR raz (Z_to_bv 64 (bv_unsigned sp + -128)) gp tp x5 x6 x7 x8 x9 x10
               x11 x12 x13 x14 x15 x16 x17 x18 x19 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
          F (Z_to_bv 64 0x15c38) fc None mz (seg_rom rsegs))).
  { intros mz Bx By raz x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x28 x29 x30 x31 j8 sfcs
      MOx MTx Hr1 FRz SFz HSZ F8z STz MUz WMz MIz WMEMz.
    step.
    lazymatch goal with
    | |- evt ?sg _ (MS _ _ _ _ _ ?mm _) =>
        eapply evt_cut;
        [ eapply MMO with (lo := lo) (B := Bx) (B' := By);
          [ rewrite Hsp; Z.div_mod_to_equations; lia | rewrite Hsp; exact STz | rewrite Hsp; lia
          | unfold w_off_stack; rewrite Hsp; lia | exact MIz | exact WMEMz | exact MOx ]
        | wk_post_call sg mm ]
    end.
    mr_names. rewrite Hsp in STc.
    eapply TICK; [ exact MTx | exact Hr1 | exact FRz | exact SFz | exact HSZ | exact F8z
                 | exact STc | exact MUz | exact WMz | exact MIc | exact WMc ]. }
  (* ---- 0x15ae0: a0 := 0; m_set (0, a1); then m_tick ---- *)
  assert (LOST : forall (mz : word -> option byte) (Bx By : list byte) (why : Z)
                   (raz x5 x6 x7 x8 x9 x10 x12 x13 x14 x15 x16 x17 x18 x19 x28 x29 x30 x31 : word)
                   (j8 : list byte) (sfcs : list cell),
    -2 ^ 31 <= why < 2 ^ 31 -> m_set_m Bx 0 why = Some (By, tt) -> m_tick_m By = Some (B', tt) -> r = 1 ->
    rw_cells rsegs mz (bv_unsigned sp + -40) [C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
    rw_cells rsegs mz (bv_unsigned sp + -120) sfcs -> cells_size sfcs = 80%nat ->
    rw_cells rsegs mz (bv_unsigned sp + -128) [CB 8 j8] ->
    stk rsegs mz lo (bv_unsigned sp + -128) ->
    munch [(bv_unsigned sp - 208, bv_unsigned sp); (W_BASE_UBSAN, W_BASE_UBSAN + W_LEN)] m mz ->
    wmono rsegs m mz -> mem_inv rsegs mz -> wmem rsegs mz Bx ->
    evt rsegs QQ
      (MS (mkR raz (Z_to_bv 64 (bv_unsigned sp + -128)) gp tp x5 x6 x7 x8 x9 x10
               (Z_to_bv 64 why) x12 x13 x14 x15 x16 x17 x18 x19 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
          F (Z_to_bv 64 0x15ae0) fc None mz (seg_rom rsegs))).
  { intros mz Bx By why raz x5 x6 x7 x8 x9 x10 x12 x13 x14 x15 x16 x17 x18 x19 x28 x29 x30 x31 j8 sfcs
      HW MSx MTx Hr1 FRz SFz HSZ F8z STz MUz WMz MIz WMEMz.
    do 2 step.
    lazymatch goal with
    | |- evt ?sg _ (MS _ _ _ _ _ ?mm _) =>
        eapply evt_cut;
        [ eapply MSET with (lo := lo) (B := Bx) (B' := By) (st := 0) (why := why);
          [ reflexivity | reflexivity | lia | lia
          | rewrite Hsp; Z.div_mod_to_equations; lia | rewrite Hsp; exact STz | rewrite Hsp; lia
          | unfold w_off_stack; rewrite Hsp; lia | exact MIz | exact WMEMz | exact MSx ]
        | wk_post_call sg mm ]
    end.
    mr_names. rewrite Hsp in STc.
    step.
    eapply TICK; [ exact MTx | exact Hr1 | exact FRz | exact SFz | exact HSZ | exact F8z
                 | exact STc | exact MUz | exact WMz | exact MIc | exact WMc ]. }
  (* ---- the prologue and spec_read_frame ---- *)
  do 8 step.
  lazymatch goal with
  | |- evt ?sg _ (MS _ _ _ _ _ ?mm _) =>
      eapply evt_cut;
      [ eapply SRF with (p := tf_addr fr) (len := n) (fp := bv_unsigned sp + -120) (lo := lo) (B := B)
          (fr := tf_bytes fr);
        [ reflexivity | reflexivity | reflexivity | exact Hp | eassumption | lia | exact NW
        | Z.div_mod_to_equations; lia | rewrite Hsp; lia | eassumption
        | destruct OWn; [left|right]; lia
        | unfold off_window; rewrite Hsp; destruct OWn; [left|right]; lia
        | rewrite Hsp; Z.div_mod_to_equations; lia | rewrite Hsp; eassumption | rewrite Hsp; lia
        | unfold w_off_stack; rewrite Hsp; lia | eassumption | eassumption ]
      | wk_post_call sg mm ]
  end.
  mr_names. rename POST into SFc. rewrite Hsp in STc.
  change (spec_read_frame (zs (tf_bytes fr)) n) with (mr_f fr n) in *.
  pose proof (mr_srf_code (zs (tf_bytes fr)) n) as CODER.
  change (spec_read_frame (zs (tf_bytes fr)) n) with (mr_f fr n) in CODER.
  unfold SPEC_OK in MOD.
  (* ---- 0x15928: the parse failed ---- *)
  step.
  rewrite (mr_eqb (sf_code (mr_f fr n)) 0) by lia.
  destruct (sf_code (mr_f fr n) =? 0) eqn:ECODE; try rewrite ECODE in MOD; mr_mod MOD; cbv iota.
  2: { step. injection MOD as EB Er. subst B' r.
       eapply EPI; [ reflexivity | reflexivity
                   | exact FR40 | exact SFc | reflexivity | exact FR8 | exact STc | exact MU | exact WMo
                   | exact MIc | exact WMc ]. }
  apply Z.eqb_eq in ECODE.
  pose proof (mr_srf_ok (tf_bytes fr) n ECODE) as OKF. cbv zeta in OKF.
  change (spec_read_frame (zs (tf_bytes fr)) n) with (mr_f fr n) in OKF.
  destruct OKF as (DST0 & SRC6 & BODY30 & LEN30 & BLEN0 & BLENN & CMDR & RETR & SENDR & ACKR).
  assert (SPTR : forall k, sf_ptr (tf_addr fr) (mr_f fr n) k = tf_addr fr + k).
  { intros k. unfold sf_ptr. rewrite ECODE. reflexivity. }
  apply mr_sf_cells in SFc. cbv beta delta [sf_cells] in SFc.
  rewrite !SPTR, DST0, SRC6, BODY30 in SFc.
  rewrite SRC6, DST0 in MOD.
  (* ---- 0x15ac0: cmd = 0xe3 ---- *)
  assert (SW_E3 : forall (mz : word -> option byte) (B2 B3 : list byte)
                    (raz q5 q6 q7 q8 q10 q12 q13 q14 q15 q16 q17 q18 q28 q29 q30 q31 : word)
                    (j8 : list byte),
    (if sf_cmd (mr_f fr n) =? 227 then mr_e3 B2 else Some (B2, tt)) = Some (B3, tt) ->
    m_tick_m B3 = Some (B', tt) -> r = 1 ->
    rw_cells rsegs mz (bv_unsigned sp + -40) [C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
    rw_cells rsegs mz (bv_unsigned sp + -120) (mr_sfc (tf_addr fr) (mr_f fr n)) ->
    rw_cells rsegs mz (bv_unsigned sp + -128) [CB 8 j8] ->
    stk rsegs mz lo (bv_unsigned sp + -128) ->
    munch [(bv_unsigned sp - 208, bv_unsigned sp); (W_BASE_UBSAN, W_BASE_UBSAN + W_LEN)] m mz ->
    wmono rsegs m mz -> mem_inv rsegs mz -> wmem rsegs mz B2 ->
    evt rsegs QQ
      (MS (mkR raz (Z_to_bv 64 (bv_unsigned sp + -128)) gp tp q5 q6 q7 q8 (Z_to_bv 64 209664) q10
               (Z_to_bv 64 (M_state B2)) q12 q13 q14 q15 q16 q17 q18 (Z_to_bv 64 (sf_cmd (mr_f fr n)))
               s4 s5 s6 s7 s8 s9 s10 s11 q28 q29 q30 q31)
          F (Z_to_bv 64 0x15ac0) fc None mz (seg_rom rsegs))).
  { clear FR40 FR8 STc WMc SFc MIc BF MU WMo MOD.
    intros mz B2 B3 raz q5 q6 q7 q8 q10 q12 q13 q14 q15 q16 q17 q18 q28 q29 q30 q31 j8
      ME3 MTx Hr1 FRz SFz F8z STc MUz WMz MIc WMc.
    pose proof (wm_len rsegs W_BASE_UBSAN mz B2 WMc) as LB2.
    pose proof (s32_range B2 A_M_state) as RST.
    change (s32_at B2 A_M_state) with (M_state B2) in RST.
    do 2 step.
    rewrite (mr_eqb (sf_cmd (mr_f fr n)) 227) by lia.
    destruct (sf_cmd (mr_f fr n) =? 227) eqn:EE3; mr_br.
    2: { injection ME3 as EB3. subst B3.
         eapply TICK; [ exact MTx | exact Hr1 | exact FRz | exact SFz | reflexivity | exact F8z
                      | exact STc | exact MUz | exact WMz | exact MIc | exact WMc ]. }
    unfold mr_e3, S_ONLINE, S_WAKING, R_DESK_DISCONNECT in ME3.
    do 3 step.
    rewrite mr_swrap32_lit_add.
    rewrite mr_ltu1 by apply mr_swrap32_range.
    rewrite mr_st12 by lia.
    destruct ((M_state B2 =? 2) || (M_state B2 =? 1)) eqn:EST; mr_br.
    2: { injection ME3 as EB3. subst B3.
         eapply TICK; [ exact MTx | exact Hr1 | exact FRz | exact SFz | reflexivity | exact F8z
                      | exact STc | exact MUz | exact WMz | exact MIc | exact WMc ]. }
    do 3 step.
    mr_names.
    change (upd (upd B2 76 (put 4 0)) 96 (put 4 0))
      with (set_M_fly_on (set_M_desk_counter_valid B2 0) 0) in WMc.
    rewrite (mr_dcv_fly B2 LB2) in WMc.
    unfold m_lost_m, S_IDLE in ME3.
    eapply LOST with (Bx := set_M_desk_counter_valid (set_M_fly_on B2 0) 0) (By := B3) (why := 7);
      [ lia | exact ME3 | exact MTx | exact Hr1 | exact FRz | exact SFz | reflexivity | exact F8z
      | exact STc | exact MUz | exact WMz | exact MIc | exact WMc ]. }
  (* ---- 0x15b58: the OW.dn[] record, then OW.ndata++ ---- *)
  assert (SW_DN : forall (mz : word -> option byte) (B5 B3 : list byte)
                    (raz q5 q6 q7 q8 q13 q15 q16 q17 q19 q28 q29 q30 q31 : word)
                    (j8 : list byte),
    mr_dn fr n B5 = Some (B3, tt) -> m_tick_m B3 = Some (B', tt) -> r = 1 ->
    rw_cells rsegs mz (bv_unsigned sp + -40) [C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
    rw_cells rsegs mz (bv_unsigned sp + -120) (mr_sfc (tf_addr fr) (mr_f fr n)) ->
    rw_cells rsegs mz (bv_unsigned sp + -128) [CB 8 j8] ->
    stk rsegs mz lo (bv_unsigned sp + -128) ->
    munch [(bv_unsigned sp - 208, bv_unsigned sp); (W_BASE_UBSAN, W_BASE_UBSAN + W_LEN)] m mz ->
    wmono rsegs m mz -> mem_inv rsegs mz -> wmem rsegs mz B5 ->
    evt rsegs QQ
      (MS (mkR raz (Z_to_bv 64 (bv_unsigned sp + -128)) gp tp q5 q6 q7 q8 (Z_to_bv 64 209664)
               (Z_to_bv 64 (sf_retry (mr_f fr n))) (Z_to_bv 64 (bv_swrap 32 (sf_send (mr_f fr n))))
               (Z_to_bv 64 (sf_body_len (mr_f fr n))) q13 (Z_to_bv 64 1) q15 q16 q17 (Z_to_bv 64 274632) q19
               s4 s5 s6 s7 s8 s9 s10 s11 q28 q29 q30 q31)
          F (Z_to_bv 64 0x15b58) fc None mz (seg_rom rsegs))).
  { clear FR40 FR8 STc WMc SFc MIc BF MU WMo MOD SW_E3.
    intros mz B5 B3 raz q5 q6 q7 q8 q13 q15 q16 q17 q19 q28 q29 q30 q31 j8
      MDN MTx Hr1 FRz SFz F8z STc MUz WMz MIc WMc.
    cbv beta delta [mr_sfc] in SFz.
    pose proof (wm_len rsegs W_BASE_UBSAN mz B5 WMc) as LB5.
    pose proof (s32_range B5 A_OW_ndata) as RND.
    change (s32_at B5 A_OW_ndata) with (OW_ndata B5) in RND.
    unfold mr_dn in MDN. cbv zeta in MDN. unfold int_inc, INT_MAX in MDN.
    do 2 step.
    change (s32_at B5 65532) with (OW_ndata B5).
    rewrite (mr_lts 1 (OW_ndata B5)) by lia.
    rewrite mr_lt12.
    destruct (OW_ndata B5 <? 2) eqn:ND2; mr_br; mr_mod MDN.
    2: { (* 0x15ba4 with nd >= 2: OW.ndata++ only *)
         do 2 step.
         rewrite mr_swrap32_lit_add.
         rewrite (mr_lts (bv_swrap 32 (OW_ndata B5 + 1)) (OW_ndata B5))
           by (pose proof (mr_swrap32_range (OW_ndata B5 + 1)); lia).
         rewrite mr_inc_trap by lia.
         destruct (OW_ndata B5 =? 2 ^ 31 - 1) eqn:EOV; mr_br; mr_mod MDN; [discriminate MDN|].
         do 2 step.
         mr_names.
         rewrite mr_put4_swrap in WMc.
         injection MDN as EB3. subst B3.
         eapply TICK; [ exact MTx | exact Hr1 | exact FRz | exact SFz | reflexivity | exact F8z
                      | exact STc | exact MUz | exact WMz | exact MIc | exact WMc ]. }
    destruct (OW_ndata B5 <? 0) eqn:ND0; mr_mod MDN; [discriminate MDN|].
    apply Z.ltb_lt in ND2. apply Z.ltb_ge in ND0.
    assert (NDV : OW_ndata B5 = 0 \/ OW_ndata B5 = 1) by lia.
    rewrite BODY30 in MDN.
    destruct NDV as [NDV|NDV]; rewrite NDV in *.
    - do 6 step. mr_vbr.
      do 5 step. mr_vbr.
      do 8 step. mr_vbr.
      do 2 step.
      mr_names.
      rewrite !mr_put4_swrap in WMc.
      replace (0 =? 2 ^ 31 - 1) with false in MDN by reflexivity. mr_mod MDN.
      injection MDN as EB3. subst B3.
      eapply TICK; [ exact MTx | exact Hr1 | exact FRz | exact SFz | reflexivity | exact F8z
                   | exact STc | exact MUz | exact WMz | exact MIc | exact WMc ].
    - do 6 step. mr_vbr.
      do 5 step. mr_vbr.
      do 8 step. mr_vbr.
      do 2 step.
      mr_names.
      rewrite !mr_put4_swrap in WMc.
      replace (1 =? 2 ^ 31 - 1) with false in MDN by reflexivity. mr_mod MDN.
      injection MDN as EB3. subst B3.
      eapply TICK; [ exact MTx | exact Hr1 | exact FRz | exact SFz | reflexivity | exact F8z
                   | exact STc | exact MUz | exact WMz | exact MIc | exact WMc ].
  }
  (* ---- 0x15b34: the desk counter, then the one-byte body check ---- *)
  assert (SW_D3 : forall (mz : word -> option byte) (B4 B3 : list byte)
                    (raz q5 q6 q7 q8 q12 q13 q14 q15 q16 q17 q19 q28 q29 q30 q31 : word)
                    (j8 : list byte),
    mr_data3 fr n B4 = Some (B3, tt) -> m_tick_m B3 = Some (B', tt) -> r = 1 ->
    rw_cells rsegs mz (bv_unsigned sp + -40) [C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
    rw_cells rsegs mz (bv_unsigned sp + -120) (mr_sfc (tf_addr fr) (mr_f fr n)) ->
    rw_cells rsegs mz (bv_unsigned sp + -128) [CB 8 j8] ->
    stk rsegs mz lo (bv_unsigned sp + -128) ->
    munch [(bv_unsigned sp - 208, bv_unsigned sp); (W_BASE_UBSAN, W_BASE_UBSAN + W_LEN)] m mz ->
    wmono rsegs m mz -> mem_inv rsegs mz -> wmem rsegs mz B4 -> bytes_at rsegs mz (tf_addr fr) (tf_bytes fr) ->
    evt rsegs QQ
      (MS (mkR raz (Z_to_bv 64 (bv_unsigned sp + -128)) gp tp q5 q6 q7 q8 (Z_to_bv 64 209664)
               (Z_to_bv 64 (sf_retry (mr_f fr n))) (Z_to_bv 64 (bv_swrap 32 (sf_send (mr_f fr n))))
               q12 q13 q14 q15 q16 q17 (Z_to_bv 64 274632) q19
               s4 s5 s6 s7 s8 s9 s10 s11 q28 q29 q30 q31)
          F (Z_to_bv 64 0x15b34) fc None mz (seg_rom rsegs))).
  { clear FR40 FR8 STc WMc SFc MIc BF MU WMo MOD SW_E3.
    intros mz B4 B3 raz q5 q6 q7 q8 q12 q13 q14 q15 q16 q17 q19 q28 q29 q30 q31 j8
      MD3 MTx Hr1 FRz SFz F8z STc MUz WMz MIc WMc BFz.
    pose proof (wm_len rsegs W_BASE_UBSAN mz B4 WMc) as LB4.
    pose proof (bytes_at_bound rsegs mz _ _ BFz) as FBz.
    unfold mr_data3 in MD3. cbv zeta in MD3. rewrite BODY30 in MD3.
    change (Z.to_nat 30) with 30%nat in MD3. unfold at8, bz in MD3. rewrite mr_nth_skipn in MD3.
    cbv beta delta [mr_sfc] in SFz.
    do 5 step.
    mr_names.
    rewrite mr_put4_swrap, (mr_dcv_cnt B4 _ LB4) in WMc.
    rewrite (mr_eqbu (sf_body_len (mr_f fr n)) 1) by lia.
    destruct (sf_body_len (mr_f fr n) =? 1) eqn:EBL; mr_br; mr_mod MD3.
    2: { eapply SW_DN; [ exact MD3 | exact MTx | exact Hr1 | exact FRz | exact SFz | exact F8z
                       | exact STc | exact MUz | exact WMz | exact MIc | exact WMc ]. }
    apply Z.eqb_eq in EBL.
    do 2 step.
    rewrite (mr_eqbu (tf_addr fr + 30) 0) by lia.
    destruct (tf_addr fr + 30 =? 0) eqn:ENUL; mr_br; [apply Z.eqb_eq in ENUL; lia|].
    pose proof (mr_rd1 _ _ _ 30 BFz ltac:(lia)) as HR. change (Z.of_nat 30) with 30 in HR.
    do 2 step.
    mr_ext.
    rewrite (mr_eqb (bv_unsigned (nth 30 (tf_bytes fr) (b8 0))) 0)
      by (pose proof (bv_unsigned_in_range 8 (nth 30 (tf_bytes fr) (b8 0))) as R8;
          unfold bv_modulus in R8; lia).
    destruct (bv_unsigned (nth 30 (tf_bytes fr) (b8 0)) =? 0) eqn:EB0; mr_br; mr_mod MD3.
    - injection MD3 as EB3. subst B3.
      eapply TICK; [ exact MTx | exact Hr1 | exact FRz | exact SFz | reflexivity | exact F8z
                      | exact STc | exact MUz | exact WMz | exact MIc | exact WMc ].
    - eapply SW_DN; [ exact MD3 | exact MTx | exact Hr1 | exact FRz | exact SFz | exact F8z
                       | exact STc | exact MUz | exact WMz | exact MIc | exact WMc ]. }
  (* ---- 0x15b1c: the duplicate check ---- *)
  assert (SW_D2 : forall (mz : word -> option byte) (B4 B3 : list byte)
                    (raz q5 q6 q7 q8 q11 q12 q13 q14 q15 q16 q17 q19 q28 q29 q30 q31 : word)
                    (j8 : list byte),
    mr_data2 fr n B4 = Some (B3, tt) -> m_tick_m B3 = Some (B', tt) -> r = 1 ->
    rw_cells rsegs mz (bv_unsigned sp + -40) [C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
    rw_cells rsegs mz (bv_unsigned sp + -120) (mr_sfc (tf_addr fr) (mr_f fr n)) ->
    rw_cells rsegs mz (bv_unsigned sp + -128) [CB 8 j8] ->
    stk rsegs mz lo (bv_unsigned sp + -128) ->
    munch [(bv_unsigned sp - 208, bv_unsigned sp); (W_BASE_UBSAN, W_BASE_UBSAN + W_LEN)] m mz ->
    wmono rsegs m mz -> mem_inv rsegs mz -> wmem rsegs mz B4 -> bytes_at rsegs mz (tf_addr fr) (tf_bytes fr) ->
    evt rsegs QQ
      (MS (mkR raz (Z_to_bv 64 (bv_unsigned sp + -128)) gp tp q5 q6 q7 q8 (Z_to_bv 64 209664)
               (Z_to_bv 64 (sf_retry (mr_f fr n))) q11 q12 q13 q14 q15 q16 q17 (Z_to_bv 64 274632) q19
               s4 s5 s6 s7 s8 s9 s10 s11 q28 q29 q30 q31)
          F (Z_to_bv 64 0x15b1c) fc None mz (seg_rom rsegs))).
  { clear FR40 FR8 STc WMc SFc MIc BF MU WMo MOD SW_E3.
    intros mz B4 B3 raz q5 q6 q7 q8 q11 q12 q13 q14 q15 q16 q17 q19 q28 q29 q30 q31 j8
      MD2 MTx Hr1 FRz SFz F8z STc MUz WMz MIc WMc BFz.
    pose proof (wm_len rsegs W_BASE_UBSAN mz B4 WMc) as LB4.
    unfold mr_data2 in MD2. cbv zeta in MD2. unfold truth in MD2.
    cbv beta delta [mr_sfc] in SFz.
    do 3 step.
    change (s32_at B4 76) with (M_desk_counter_valid B4).
    mr_ext. rewrite mr_swrap32_lit.
    rewrite (mr_eqb (M_desk_counter_valid B4) 0)
      by (pose proof (s32_range B4 A_M_desk_counter_valid) as R2;
          change (s32_at B4 A_M_desk_counter_valid) with (M_desk_counter_valid B4) in R2; lia).
    destruct (M_desk_counter_valid B4 =? 0) eqn:EDV; mr_br; mr_mod MD2.
    { eapply SW_D3; [ exact MD2 | exact MTx | exact Hr1 | exact FRz | exact SFz | exact F8z
                       | exact STc | exact MUz | exact WMz | exact MIc | exact WMc | exact BFz ]. }
    step.
    rewrite (mr_eqb (sf_retry (mr_f fr n)) 0) by lia.
    destruct (sf_retry (mr_f fr n) =? 0) eqn:ERT; mr_br; mr_mod MD2.
    { eapply SW_D3; [ exact MD2 | exact MTx | exact Hr1 | exact FRz | exact SFz | exact F8z
                       | exact STc | exact MUz | exact WMz | exact MIc | exact WMc | exact BFz ]. }
    do 2 step.
    change (s32_at B4 80) with (bv_swrap 32 (M_desk_counter B4)).
    rewrite (mr_eqb (bv_swrap 32 (sf_send (mr_f fr n))) (bv_swrap 32 (M_desk_counter B4)))
      by (pose proof (mr_swrap32_range (sf_send (mr_f fr n)));
          pose proof (mr_swrap32_range (M_desk_counter B4)); lia).
    rewrite mr_swrap32_inj by (first [ lia | (unfold M_desk_counter; apply u_at_range) ]).
    destruct (sf_send (mr_f fr n) =? M_desk_counter B4) eqn:ESD; mr_br; mr_mod MD2.
    - injection MD2 as EB3. subst B3.
      eapply TICK; [ exact MTx | exact Hr1 | exact FRz | exact SFz | reflexivity | exact F8z
                      | exact STc | exact MUz | exact WMz | exact MIc | exact WMc ].
    - eapply SW_D3; [ exact MD2 | exact MTx | exact Hr1 | exact FRz | exact SFz | exact F8z
                       | exact STc | exact MUz | exact WMz | exact MIc | exact WMc | exact BFz ]. }
  (* ---- 0x15aec: cmd = 0 (DATA) ---- *)
  assert (SW_DATA : forall (mz : word -> option byte) (B2 B3 : list byte)
                      (raz q5 q6 q7 q8 q10 q11 q13 q14 q15 q16 q17 q19 q28 q29 q30 q31 : word)
                      (j8 : list byte),
    mr_data fr n B2 = Some (B3, tt) -> m_tick_m B3 = Some (B', tt) -> r = 1 ->
    rw_cells rsegs mz (bv_unsigned sp + -40) [C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
    rw_cells rsegs mz (bv_unsigned sp + -120) (mr_sfc (tf_addr fr) (mr_f fr n)) ->
    rw_cells rsegs mz (bv_unsigned sp + -128) [CB 8 j8] ->
    stk rsegs mz lo (bv_unsigned sp + -128) ->
    munch [(bv_unsigned sp - 208, bv_unsigned sp); (W_BASE_UBSAN, W_BASE_UBSAN + W_LEN)] m mz ->
    wmono rsegs m mz -> mem_inv rsegs mz -> wmem rsegs mz B2 -> bytes_at rsegs mz (tf_addr fr) (tf_bytes fr) ->
    evt rsegs QQ
      (MS (mkR raz (Z_to_bv 64 (bv_unsigned sp + -128)) gp tp q5 q6 q7 q8 (Z_to_bv 64 209664) q10 q11
               (Z_to_bv 64 (g_now B2)) q13 q14 q15 q16 q17 (Z_to_bv 64 274632) q19
               s4 s5 s6 s7 s8 s9 s10 s11 q28 q29 q30 q31)
          F (Z_to_bv 64 0x15aec) fc None mz (seg_rom rsegs))).
  { clear FR40 FR8 STc WMc SFc MIc BF MU WMo MOD SW_E3.
    intros mz B2 B3 raz q5 q6 q7 q8 q10 q11 q13 q14 q15 q16 q17 q19 q28 q29 q30 q31 j8
      MDA MTx Hr1 FRz SFz F8z STc MUz WMz MIc WMc BFz.
    pose proof (wm_len rsegs W_BASE_UBSAN mz B2 WMc) as LB2.
    pose proof (s32_range B2 A_OW_acks) as RAC.
    change (s32_at B2 A_OW_acks) with (OW_acks B2) in RAC.
    unfold mr_data in MDA. cbv zeta in MDA. unfold int_inc, INT_MAX, truth in MDA.
    cbv beta delta [mr_sfc] in SFz.
    do 3 step.
    change (s32_at B2 65516) with (OW_acks B2).
    rewrite mr_swrap32_lit_add.
    rewrite (mr_lts (bv_swrap 32 (OW_acks B2 + 1)) (OW_acks B2))
      by (pose proof (mr_swrap32_range (OW_acks B2 + 1)); lia).
    rewrite mr_inc_trap by lia.
    destruct (OW_acks B2 =? 2 ^ 31 - 1) eqn:EOV; mr_br; mr_mod MDA; [discriminate MDA|].
    do 4 step.
    mr_names. rewrite mr_put4_swrap in WMc.
    mr_ext.
    rewrite (unsigned_lit (sf_retry (mr_f fr n))) by lia.
    rewrite (Z.mod_small (sf_retry (mr_f fr n)) (2 ^ 16)) by lia.
    rewrite (mr_eqb (sf_retry (mr_f fr n)) 0) by lia.
    destruct (sf_retry (mr_f fr n) =? 0) eqn:ERT; mr_br; mr_mod MDA.
    { eapply SW_D2; [ exact MDA | exact MTx | exact Hr1 | exact FRz | exact SFz | exact F8z
                       | exact STc | exact MUz | exact WMz | exact MIc | exact WMc | exact BFz ]. }
    do 5 step.
    mr_names.
    assert (EBO : put 8 (bv_unsigned (Z_to_bv 64 (u_at (upd (upd B2 65516 (put 4 (OW_acks B2 + 1))) 88
                                                          (put 4 0)) 65060 4)) * 1000 + g_now B2)
                  = put 8 (u64 (g_now (set_M_fail (set_OW_acks B2 (OW_acks B2 + 1)) 0)
                                + h_ms_m (Cfg_backoff_ms (set_M_fail (set_OW_acks B2 (OW_acks B2 + 1)) 0))))).
    { apply mr_put8_mod.
      change (u_at (upd (upd B2 65516 (put 4 (OW_acks B2 + 1))) 88 (put 4 0)) 65060 4)
        with (Cfg_backoff_ms (set_M_fail (set_OW_acks B2 (OW_acks B2 + 1)) 0)).
      assert (EG : g_now (set_M_fail (set_OW_acks B2 (OW_acks B2 + 1)) 0) = g_now B2)
        by (mr_unf; mr_push LB2; reflexivity).
      rewrite EG.
      pose proof (u_at_range (set_M_fail (set_OW_acks B2 (OW_acks B2 + 1)) 0) A_Cfg_backoff_ms 4) as RC.
      change (u_at (set_M_fail (set_OW_acks B2 (OW_acks B2 + 1)) 0) A_Cfg_backoff_ms 4)
        with (Cfg_backoff_ms (set_M_fail (set_OW_acks B2 (OW_acks B2 + 1)) 0)) in RC.
      rewrite unsigned_lit by (change (2 ^ (8 * Z.of_nat 4)) with (2 ^ 32) in RC; lia).
      unfold h_ms_m, u64. rewrite Zmod_mod, Zplus_mod_idemp_r. f_equal. lia. }
    rewrite EBO in WMc.
    eapply SW_D2; [ exact MDA | exact MTx | exact Hr1 | exact FRz | exact SFz | exact F8z | exact STc | exact MUz | exact WMz | exact MIc | exact WMc | exact BFz ]. }
  (* ---- 0x15a74: cmd = 0xa0 ---- *)
  assert (SW_ACK : forall (mz : word -> option byte) (B2 B3 : list byte)
                     (raz q5 q6 q7 q8 q10 q12 q13 q14 q15 q16 q17 q28 q29 q30 q31 : word)
                     (j8 : list byte),
    (if sf_cmd (mr_f fr n) =? 160 then mr_ack fr n B2 else Some (B2, tt)) = Some (B3, tt) ->
    m_tick_m B3 = Some (B', tt) -> r = 1 ->
    rw_cells rsegs mz (bv_unsigned sp + -40) [C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
    rw_cells rsegs mz (bv_unsigned sp + -120) (mr_sfc (tf_addr fr) (mr_f fr n)) ->
    rw_cells rsegs mz (bv_unsigned sp + -128) [CB 8 j8] ->
    stk rsegs mz lo (bv_unsigned sp + -128) ->
    munch [(bv_unsigned sp - 208, bv_unsigned sp); (W_BASE_UBSAN, W_BASE_UBSAN + W_LEN)] m mz ->
    wmono rsegs m mz -> mem_inv rsegs mz -> wmem rsegs mz B2 ->
    evt rsegs QQ
      (MS (mkR raz (Z_to_bv 64 (bv_unsigned sp + -128)) gp tp q5 q6 q7 q8 (Z_to_bv 64 209664) q10
               (Z_to_bv 64 (M_state B2)) q12 q13 q14 q15 q16 q17 (Z_to_bv 64 274632)
               (Z_to_bv 64 (sf_cmd (mr_f fr n))) s4 s5 s6 s7 s8 s9 s10 s11 q28 q29 q30 q31)
          F (Z_to_bv 64 0x15a74) fc None mz (seg_rom rsegs))).
  { clear FR40 FR8 STc WMc SFc MIc BF MU WMo MOD SW_E3 SW_DN.
    intros mz B2 B3 raz q5 q6 q7 q8 q10 q12 q13 q14 q15 q16 q17 q28 q29 q30 q31 j8
      MACK MTx Hr1 FRz SFz F8z STc MUz WMz MIc WMc.
    cbv beta delta [mr_sfc] in SFz.
    pose proof (wm_len rsegs W_BASE_UBSAN mz B2 WMc) as LB2.
    pose proof (s32_range B2 A_M_state) as RST.
    change (s32_at B2 A_M_state) with (M_state B2) in RST.
    do 2 step.
    rewrite (mr_eqb (sf_cmd (mr_f fr n)) 160) by lia.
    destruct (sf_cmd (mr_f fr n) =? 160) eqn:EAC; mr_br.
    2: { injection MACK as EB3. subst B3.
         eapply TICK; [ exact MTx | exact Hr1 | exact FRz | exact SFz | reflexivity | exact F8z
                      | exact STc | exact MUz | exact WMz | exact MIc | exact WMc ]. }
    rewrite (mr_ack_norm fr n B2 LB2) in MACK. unfold INT_MAX in MACK.
    (* 0x15a7c: M.fly_on *)
    do 2 step.
    change (s32_at B2 96) with (M_fly_on B2).
    rewrite (mr_eqb (M_fly_on B2) 0)
      by (pose proof (s32_range B2 A_M_fly_on) as R2;
          change (s32_at B2 A_M_fly_on) with (M_fly_on B2) in R2; lia).
    destruct (M_fly_on B2 =? 0) eqn:EFL; mr_br; mr_mod MACK.
    { injection MACK as EB3. subst B3.
      eapply TICK; [ exact MTx | exact Hr1 | exact FRz | exact SFz | reflexivity | exact F8z
                   | exact STc | exact MUz | exact WMz | exact MIc | exact WMc ]. }
    (* 0x15a84: f.ack against M.fly_counter *)
    do 3 step.
    mr_ext. rewrite mr_swrap32_lit.
    change (s32_at B2 104) with (bv_swrap 32 (M_fly_counter B2)).
    rewrite (mr_eqb (bv_swrap 32 (sf_ack (mr_f fr n))) (bv_swrap 32 (M_fly_counter B2)))
      by (pose proof (mr_swrap32_range (sf_ack (mr_f fr n)));
          pose proof (mr_swrap32_range (M_fly_counter B2)); lia).
    rewrite mr_swrap32_inj by (first [ lia | (unfold M_fly_counter; apply u_at_range) ]).
    destruct (sf_ack (mr_f fr n) =? M_fly_counter B2) eqn:EAK; mr_br; mr_mod MACK.
    2: { injection MACK as EB3. subst B3.
         eapply TICK; [ exact MTx | exact Hr1 | exact FRz | exact SFz | reflexivity | exact F8z
                      | exact STc | exact MUz | exact WMz | exact MIc | exact WMc ]. }
    apply Z.eqb_eq in EAK.
    (* 0x15a90: OW.acked++ *)
    do 3 step.
    change (s32_at B2 65528) with (OW_acked B2).
    rewrite mr_swrap32_lit_add.
    pose proof (s32_range B2 A_OW_acked) as RAK.
    change (s32_at B2 A_OW_acked) with (OW_acked B2) in RAK.
    rewrite (mr_lts (bv_swrap 32 (OW_acked B2 + 1)) (OW_acked B2))
      by (pose proof (mr_swrap32_range (OW_acked B2 + 1)); lia).
    rewrite mr_inc_trap by lia.
    destruct (OW_acked B2 =? 2 ^ 31 - 1) eqn:EOV; mr_br; mr_mod MACK.
    { discriminate MACK. }
    (* 0x15a9c: the OW.acked record and M.fly_on *)
    do 7 step.
    mr_names.
    change (s32_at B2 108) with (bv_swrap 32 (M_fly_retries B2)) in WMc.
    rewrite !mr_put4_swrap, EAK in WMc.
    rewrite (mr_eqb (M_state B2) 1) by lia.
    destruct (M_state B2 =? 1) eqn:EW1; mr_br; mr_mod MACK.
    - do 2 step.
      mr_names.
      eapply MO; [ exact MACK | exact MTx | exact Hr1 | exact FRz | exact SFz | reflexivity | exact F8z
                 | exact STc | exact MUz | exact WMz | exact MIc | exact WMc ].
    - injection MACK as EB3. subst B3.
      eapply TICK; [ exact MTx | exact Hr1 | exact FRz | exact SFz | reflexivity | exact F8z
                   | exact STc | exact MUz | exact WMz | exact MIc | exact WMc ]. }
  (* ---- 0x15bb8: OW.desk++, the desk fields, then the e0 / e1 tails ---- *)
  assert (SW_ANN2 : forall (mz : word -> option byte) (B2 B3 : list byte) (off : Z)
                      (raz q5 q6 q7 q10 q11 q12 q13 q14 q15 q16 q17 q19 q28 q29 q30 q31 : word)
                      (j8 : list byte),
    mr_ann2 timg_ubsan fr n off B2 = Some (B3, tt) -> m_tick_m B3 = Some (B', tt) -> r = 1 ->
    -1 <= off < 10 -> (sf_cmd (mr_f fr n) = 224 \/ sf_cmd (mr_f fr n) = 225) ->
    rw_cells rsegs mz (bv_unsigned sp + -40) [C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
    rw_cells rsegs mz (bv_unsigned sp + -120) (mr_sfc (tf_addr fr) (mr_f fr n)) ->
    rw_cells rsegs mz (bv_unsigned sp + -128) [CB 8 j8] ->
    stk rsegs mz lo (bv_unsigned sp + -128) ->
    munch [(bv_unsigned sp - 208, bv_unsigned sp); (W_BASE_UBSAN, W_BASE_UBSAN + W_LEN)] m mz ->
    wmono rsegs m mz -> mem_inv rsegs mz -> wmem rsegs mz B2 -> bytes_at rsegs mz (tf_addr fr) (tf_bytes fr) ->
    evt rsegs QQ
      (MS (mkR raz (Z_to_bv 64 (bv_unsigned sp + -128)) gp tp q5 q6 q7 (Z_to_bv 64 off) (Z_to_bv 64 209664)
               q10 q11 q12 q13 q14 q15 q16 q17 (Z_to_bv 64 274632) q19
               s4 s5 s6 s7 s8 s9 s10 s11 q28 q29 q30 q31)
          F (Z_to_bv 64 0x15bb8) fc None mz (seg_rom rsegs))).
  { clear FR40 FR8 STc WMc SFc MIc BF MU WMo MOD SW_E3.
    intros mz B2 B3 off raz q5 q6 q7 q10 q11 q12 q13 q14 q15 q16 q17 q19 q28 q29 q30 q31 j8
      MA2 MTx Hr1 ROFF HCMD FRz SFz F8z STc MUz WMz MIc WMc BFz.
    cbv beta delta [mr_sfc] in SFz.
    pose proof (wm_len rsegs W_BASE_UBSAN mz B2 WMc) as LB2.
    pose proof (s32_range B2 A_OW_desk) as RDK.
    change (s32_at B2 A_OW_desk) with (OW_desk B2) in RDK.
    pose proof (s32_range B2 A_M_state) as RST.
    change (s32_at B2 A_M_state) with (M_state B2) in RST.
    pose proof (s32_range B2 A_OW_foreign) as RFO.
    change (s32_at B2 A_OW_foreign) with (OW_foreign B2) in RFO.
    pose proof (s32_range B2 A_Cfg_auto_wake) as RAW.
    change (s32_at B2 A_Cfg_auto_wake) with (Cfg_auto_wake B2) in RAW.
    unfold mr_ann2 in MA2. cbv zeta in MA2. unfold int_inc, INT_MAX, SPEC_CMD_E0 in MA2.
    rewrite BODY30 in MA2. change (Z.to_nat 30) with 30%nat in MA2.
    (* 0x15bb8: OW.desk++ *)
    do 3 step.
    change (s32_at B2 65520) with (OW_desk B2).
    rewrite mr_swrap32_lit_add.
    rewrite (mr_lts (bv_swrap 32 (OW_desk B2 + 1)) (OW_desk B2))
      by (pose proof (mr_swrap32_range (OW_desk B2 + 1)); lia).
    rewrite mr_inc_trap by lia.
    destruct (OW_desk B2 =? 2 ^ 31 - 1) eqn:EOV; mr_br; mr_mod MA2; [discriminate MA2|].
    (* 0x15bc4: OW.desk, OW.desk_off, then desk_named (f.body) *)
    do 4 step.
    mr_names. rewrite mr_put4_swrap in WMc.
    destruct (desk_named_m timg_ubsan (set_OW_desk_off (set_OW_desk B2 (OW_desk B2 + 1)) off)
                (skipn 30 (tf_bytes fr))) as [[Bd dp]|] eqn:EDN; mr_mod MA2; [|discriminate MA2].
    pose proof (mr_dn_world _ _ _ _ _ EDN) as EBd. subst Bd.
    lazymatch goal with
    | |- evt ?sg _ (MS _ _ _ _ _ ?mm _) =>
        eapply evt_cut;
        [ eapply DN with (p := tf_addr fr + 30) (body := skipn 30 (tf_bytes fr)) (lo := lo)
            (B := set_OW_desk_off (set_OW_desk B2 (OW_desk B2 + 1)) off)
            (B' := set_OW_desk_off (set_OW_desk B2 (OW_desk B2 + 1)) off) (r := dp);
          [ reflexivity | lia
          | pose proof (mr_bskip _ _ _ 30 BFz ltac:(lia)) as BB; change (Z.of_nat 30) with 30 in BB; exact BB
          | unfold off_window; rewrite Hsp, length_skipn; destruct OWn; [left|right]; lia
          | rewrite Hsp; Z.div_mod_to_equations; lia | rewrite Hsp; exact STc | rewrite Hsp; lia
          | unfold w_off_stack; rewrite Hsp; lia | exact MIc | exact WMc | exact EDN ]
        | wk_post_call sg mm ]
    end.
    mr_names. rewrite Hsp in STc.
    (* 0x15bd4: OW.desk_p, OW.desk_body, then the e0 / e1 split *)
    do 6 step.
    mr_names. mr_ext. rewrite mr_u8 by lia.
    pose proof (wm_len rsegs W_BASE_UBSAN _ _ WMc) as LB4.
    rewrite (mr_eqb (sf_cmd (mr_f fr n)) 224) by lia.
    destruct (sf_cmd (mr_f fr n) =? 224) eqn:E224; mr_br; mr_mod MA2.
    - (* e0, 0x15bec *)
      unfold mr_e0 in MA2. cbv zeta in MA2.
      unfold m_lost_m, S_ONLINE, S_IDLE, R_DESK_OFFLINE, truth in MA2.
      mr_pushH MA2 B2 LB2.
      do 4 step.
      mr_pushG 12 M_state B2 LB2.
      mr_names.
      rewrite (mr_eqb (M_state B2) 2) by lia.
      destruct (M_state B2 =? 2) eqn:EON; mr_br; mr_mod MA2.
      + (* ONLINE: m_lost (DESK_OFFLINE) *)
        do 5 step.
        mr_names.
        mr_dcvfly WMc LB4.
        destruct (m_set_m (set_M_desk_counter_valid (set_M_fly_on (set_M_foreign
                    (set_OW_desk_body (set_OW_desk_p (set_OW_desk_off (set_OW_desk B2 (OW_desk B2 + 1)) off) dp)
                       (tf_addr fr + 30)) 0) 0) 0) 0 3) as [[B6 []]|] eqn:EMS;
          mr_mod MA2; [|discriminate MA2].
        lazymatch goal with
        | |- evt ?sg _ (MS _ _ _ _ _ ?mm _) =>
            eapply evt_cut;
            [ eapply MSET with (lo := lo) (B' := B6) (st := 0) (why := 3);
              [ reflexivity | reflexivity | lia | lia
              | rewrite Hsp; Z.div_mod_to_equations; lia | rewrite Hsp; exact STc | rewrite Hsp; lia
              | unfold w_off_stack; rewrite Hsp; lia | exact MIc | exact WMc | exact EMS ]
            | wk_post_call sg mm ]
        end.
        mr_names. rewrite Hsp in STc.
        do 2 step.
        change (s32_at B6 12) with (M_state B6).
        rewrite (mr_eqb (M_state B6) 0)
          by (pose proof (s32_range B6 A_M_state) as R6; change (s32_at B6 A_M_state) with (M_state B6) in R6; lia).
        destruct (M_state B6 =? 0) eqn:EID; mr_br; mr_mod MA2.
        2: { injection MA2 as EB3. subst B3. eapply TICK; [ exact MTx | exact Hr1 | exact FRz | exact SFz | reflexivity | exact F8z
                   | exact STc | exact MUz | exact WMz | exact MIc | exact WMc ]. }
        do 2 step.
        change (s32_at B6 65040) with (Cfg_auto_wake B6).
        rewrite (mr_eqb (Cfg_auto_wake B6) 0)
          by (pose proof (s32_range B6 A_Cfg_auto_wake) as R6;
              change (s32_at B6 A_Cfg_auto_wake) with (Cfg_auto_wake B6) in R6; lia).
        destruct (Cfg_auto_wake B6 =? 0) eqn:EAW; mr_br; mr_mod MA2.
        { injection MA2 as EB3. subst B3. eapply TICK; [ exact MTx | exact Hr1 | exact FRz | exact SFz | reflexivity | exact F8z
                   | exact STc | exact MUz | exact WMz | exact MIc | exact WMc ]. }
        destruct (m_wake_m B6) as [[B7 rw]|] eqn:EMW; mr_mod MA2; [|discriminate MA2].
        injection MA2 as EB3. subst B3.
        step.
        lazymatch goal with
        | |- evt ?sg _ (MS _ _ _ _ _ ?mm _) =>
            eapply evt_cut;
            [ eapply MW with (lo := lo) (B := B6) (B' := B7) (r := rw);
              [ rewrite Hsp; Z.div_mod_to_equations; lia | rewrite Hsp; exact STc | rewrite Hsp; lia
              | unfold w_off_stack; rewrite Hsp; lia | exact MIc | exact WMc | exact EMW ]
            | wk_post_call sg mm ]
        end.
        mr_names. rewrite Hsp in STc.
        step.
        eapply TICK; [ exact MTx | exact Hr1 | exact FRz | exact SFz | reflexivity | exact F8z
                   | exact STc | exact MUz | exact WMz | exact MIc | exact WMc ].
      + (* not ONLINE: the state is unchanged *)
        mr_pushH MA2 B2 LB2.
        step.
        rewrite (mr_eqb (M_state B2) 0) by lia.
        destruct (M_state B2 =? 0) eqn:EID; mr_br; mr_mod MA2.
        2: { injection MA2 as EB3. subst B3. eapply TICK; [ exact MTx | exact Hr1 | exact FRz | exact SFz | reflexivity | exact F8z
                   | exact STc | exact MUz | exact WMz | exact MIc | exact WMc ]. }
        do 2 step.
        mr_pushG 65040 Cfg_auto_wake B2 LB2.
        rewrite (mr_eqb (Cfg_auto_wake B2) 0) by lia.
        destruct (Cfg_auto_wake B2 =? 0) eqn:EAW; mr_br; mr_mod MA2.
        { injection MA2 as EB3. subst B3. eapply TICK; [ exact MTx | exact Hr1 | exact FRz | exact SFz | reflexivity | exact F8z
                   | exact STc | exact MUz | exact WMz | exact MIc | exact WMc ]. }
        destruct (m_wake_m (set_M_foreign (set_OW_desk_body (set_OW_desk_p (set_OW_desk_off
                    (set_OW_desk B2 (OW_desk B2 + 1)) off) dp) (tf_addr fr + 30)) 0))
          as [[B7 rw]|] eqn:EMW; mr_mod MA2; [|discriminate MA2].
        injection MA2 as EB3. subst B3.
        step.
        lazymatch goal with
        | |- evt ?sg _ (MS _ _ _ _ _ ?mm _) =>
            eapply evt_cut;
            [ eapply MW with (lo := lo) (B' := B7) (r := rw);
              [ rewrite Hsp; Z.div_mod_to_equations; lia | rewrite Hsp; exact STc | rewrite Hsp; lia
              | unfold w_off_stack; rewrite Hsp; lia | exact MIc | exact WMc | exact EMW ]
            | wk_post_call sg mm ]
        end.
        mr_names. rewrite Hsp in STc.
        step.
        eapply TICK; [ exact MTx | exact Hr1 | exact FRz | exact SFz | reflexivity | exact F8z
                   | exact STc | exact MUz | exact WMz | exact MIc | exact WMc ].
    - (* e1, 0x15c28 *)
      unfold mr_e1 in MA2. cbv zeta in MA2.
      unfold int_inc, INT_MAX, S_ONLINE, S_WAKING, R_FOREIGN, m_lost_m, S_IDLE in MA2.
      rewrite Z.leb_antisym in MA2.
      step.
      rewrite (mr_lts off 0) by lia.
      destruct (off <? 0) eqn:ENEG; mr_br; mr_mod MA2.
      + (* a foreign desk: 0x15c48 *)
        mr_pushH MA2 B2 LB2.
        do 5 step.
        mr_pushG 65524 OW_foreign B2 LB2.
        rewrite mr_swrap32_lit_add.
        rewrite (mr_lts (bv_swrap 32 (OW_foreign B2 + 1)) (OW_foreign B2))
          by (pose proof (mr_swrap32_range (OW_foreign B2 + 1)); lia).
        rewrite mr_inc_trap by lia.
        destruct (OW_foreign B2 =? 2 ^ 31 - 1) eqn:EOV2; mr_br; mr_mod MA2; [discriminate MA2|].
        mr_pushH MA2 B2 LB2.
        do 4 step.
        mr_pushG 12 M_state B2 LB2.
        rewrite mr_swrap32_lit_add.
        rewrite mr_ltu1 by apply mr_swrap32_range.
        rewrite mr_st12 by lia.
        mr_names. rewrite !mr_put4_swrap in WMc.
        destruct ((M_state B2 =? 2) || (M_state B2 =? 1)) eqn:EST; mr_br; mr_mod MA2.
        * do 4 step.
          mr_names.
          mr_dcvfly WMc LB4.
          eapply LOST; [ lia | exact MA2 | exact MTx | exact Hr1 | exact FRz | exact SFz | reflexivity
                       | exact F8z | exact STc | exact MUz | exact WMz | exact MIc | exact WMc ].
        * injection MA2 as EB3. subst B3. eapply TICK; [ exact MTx | exact Hr1 | exact FRz | exact SFz | reflexivity | exact F8z
                   | exact STc | exact MUz | exact WMz | exact MIc | exact WMc ].
      + (* the desk answered the host: 0x15c2c *)
        do 3 step.
        mr_names.
        rewrite (mr_e1_fo _ LB4) in WMc.
        eapply MO; [ exact MA2 | exact MTx | exact Hr1 | exact FRz | exact SFz | reflexivity | exact F8z
                   | exact STc | exact MUz | exact WMz | exact MIc | exact WMc ]. }
  (* ---- 0x159fc: cmd = 0xe0 / 0xe1 ---- *)
  assert (SW_ANN : forall (mz : word -> option byte) (B2 B3 : list byte)
                     (raz q5 q6 q7 q8 q10 q11 q12 q13 q14 q15 q16 q17 q28 q29 q30 q31 : word)
                     (j8 : list byte),
    mr_ann timg_ubsan fr n B2 = Some (B3, tt) -> m_tick_m B3 = Some (B', tt) -> r = 1 ->
    (sf_cmd (mr_f fr n) = 224 \/ sf_cmd (mr_f fr n) = 225) ->
    rw_cells rsegs mz (bv_unsigned sp + -40) [C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
    rw_cells rsegs mz (bv_unsigned sp + -120) (mr_sfc (tf_addr fr) (mr_f fr n)) ->
    rw_cells rsegs mz (bv_unsigned sp + -128) [CB 8 j8] ->
    stk rsegs mz lo (bv_unsigned sp + -128) ->
    munch [(bv_unsigned sp - 208, bv_unsigned sp); (W_BASE_UBSAN, W_BASE_UBSAN + W_LEN)] m mz ->
    wmono rsegs m mz -> mem_inv rsegs mz -> wmem rsegs mz B2 -> bytes_at rsegs mz (tf_addr fr) (tf_bytes fr) ->
    evt rsegs QQ
      (MS (mkR raz (Z_to_bv 64 (bv_unsigned sp + -128)) gp tp q5 q6 q7 q8 (Z_to_bv 64 209664) q10 q11 q12
               q13 q14 q15 q16 q17 (Z_to_bv 64 274632) (Z_to_bv 64 (sf_cmd (mr_f fr n)))
               s4 s5 s6 s7 s8 s9 s10 s11 q28 q29 q30 q31)
          F (Z_to_bv 64 0x159fc) fc None mz (seg_rom rsegs))).
  { clear FR40 FR8 STc WMc SFc MIc BF MU WMo MOD SW_E3.
    intros mz B2 B3 raz q5 q6 q7 q8 q10 q11 q12 q13 q14 q15 q16 q17 q28 q29 q30 q31 j8
      MAN MTx Hr1 HCMD FRz SFz F8z STc MUz WMz MIc WMc BFz.
    cbv beta delta [mr_sfc] in SFz.
    unfold mr_ann in MAN. cbv zeta in MAN. unfold SPEC_ANN_MIN, SPEC_CMD_E1 in MAN.
    rewrite BODY30 in MAN. change (Z.to_nat 30) with 30%nat in MAN.
    do 3 step.
    rewrite (mr_ltu (sf_body_len (mr_f fr n)) 33) by lia.
    destruct (sf_body_len (mr_f fr n) <? 33) eqn:EB33; mr_br; mr_mod MAN.
    { injection MAN as EB3. subst B3. eapply TICK; [ exact MTx | exact Hr1 | exact FRz | exact SFz | reflexivity | exact F8z
                   | exact STc | exact MUz | exact WMz | exact MIc | exact WMc ]. }
    apply Z.ltb_ge in EB33.
    do 2 step.
    rewrite (mr_eqb (sf_cmd (mr_f fr n)) 225) by lia.
    destruct (sf_cmd (mr_f fr n) =? 225) eqn:E225; mr_br; mr_mod MAN.
    - destruct (host_offset_m B2 (skipn 30 (tf_bytes fr))) as [[Bh off]|] eqn:EHO; mr_mod MAN;
        [|discriminate MAN].
      destruct (mr_ho_off _ _ _ _ EHO) as [EBh ROFF]. subst Bh.
      do 2 step.
      lazymatch goal with
      | |- evt ?sg _ (MS _ _ _ _ _ ?mm _) =>
          eapply evt_cut;
          [ eapply HO with (p := tf_addr fr + 30) (body := skipn 30 (tf_bytes fr)) (lo := lo) (B := B2) (B' := B2)
              (r := off);
            [ reflexivity | lia
            | pose proof (mr_bskip _ _ _ 30 BFz ltac:(lia)) as BB; change (Z.of_nat 30) with 30 in BB; exact BB
            | unfold off_window; rewrite Hsp, length_skipn; destruct OWn; [left|right]; lia
            | rewrite Hsp; Z.div_mod_to_equations; lia | rewrite Hsp; exact STc | rewrite Hsp; lia
            | unfold w_off_stack; rewrite Hsp; lia | exact MIc | exact WMc | exact EHO ]
          | wk_post_call sg mm ]
      end.
      mr_names. rewrite Hsp in STc.
      do 2 step.
      eapply SW_ANN2; [ exact MAN | exact MTx | exact Hr1 | exact ROFF | exact HCMD | exact FRz | exact SFz | exact F8z | exact STc | exact MUz | exact WMz | exact MIc | exact WMc | exact BFz ].
    - step.
      eapply SW_ANN2 with (off := -1); [ exact MAN | exact MTx | exact Hr1 | lia | exact HCMD | exact FRz | exact SFz | exact F8z | exact STc | exact MUz | exact WMz | exact MIc | exact WMc | exact BFz ].
  }
  (* ---- 0x159d8: M.last_rx := g_now, then the switch on f.cmd ---- *)
  assert (MID2 : forall (mz : word -> option byte) (Bx B3 : list byte)
                   (raz q5 q6 q7 q8 q10 q12 q13 q14 q15 q16 q17 q18 q28 q29 q30 q31 : word)
                   (j8 : list byte),
    mr_sw timg_ubsan fr n (set_M_last_rx Bx (g_now Bx)) = Some (B3, tt) ->
    m_tick_m B3 = Some (B', tt) -> r = 1 ->
    rw_cells rsegs mz (bv_unsigned sp + -40) [C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
    rw_cells rsegs mz (bv_unsigned sp + -120) (mr_sfc (tf_addr fr) (mr_f fr n)) ->
    rw_cells rsegs mz (bv_unsigned sp + -128) [CB 8 j8] ->
    stk rsegs mz lo (bv_unsigned sp + -128) ->
    munch [(bv_unsigned sp - 208, bv_unsigned sp); (W_BASE_UBSAN, W_BASE_UBSAN + W_LEN)] m mz ->
    wmono rsegs m mz -> mem_inv rsegs mz -> wmem rsegs mz Bx -> bytes_at rsegs mz (tf_addr fr) (tf_bytes fr) ->
    evt rsegs QQ
      (MS (mkR raz (Z_to_bv 64 (bv_unsigned sp + -128)) gp tp q5 q6 q7 q8 (Z_to_bv 64 209664) q10
               (Z_to_bv 64 (M_state Bx)) q12 q13 q14 q15 q16 q17 q18 (Z_to_bv 64 (sf_cmd (mr_f fr n)))
               s4 s5 s6 s7 s8 s9 s10 s11 q28 q29 q30 q31)
          F (Z_to_bv 64 0x159d8) fc None mz (seg_rom rsegs))).
  { clear FR40 FR8 STc WMc SFc MIc BF MU WMo MOD.
    intros mz Bx B3 raz q5 q6 q7 q8 q10 q12 q13 q14 q15 q16 q17 q18 q28 q29 q30 q31 j8
      MSW MTx Hr1 FRz SFz F8z STc MUz WMz MIc WMc BFz.
    pose proof (wm_len rsegs W_BASE_UBSAN mz Bx WMc) as LBx.
    assert (EST2 : M_state (set_M_last_rx Bx (g_now Bx)) = M_state Bx) by (mr_unf; mr_push LBx; reflexivity).
    assert (EGN2 : g_now (set_M_last_rx Bx (g_now Bx)) = g_now Bx) by (mr_unf; mr_push LBx; reflexivity).
    unfold mr_sw in MSW. cbv zeta in MSW.
    unfold SPEC_CMD_E0, SPEC_CMD_E1, SPEC_CMD_ACK, SPEC_CMD_DATA, SPEC_CMD_E3 in MSW.
    do 6 step.
    change (u_at Bx 65000 8) with (g_now Bx).
    mr_names.
    rewrite (mr_lts 223 (sf_cmd (mr_f fr n))) by lia.
    destruct (223 <? sf_cmd (mr_f fr n)) eqn:EC223; mr_br.
    - apply Z.ltb_lt in EC223.
      do 3 step.
      rewrite (mr_ltu (sf_cmd (mr_f fr n) + -224) 2) by lia.
      destruct (sf_cmd (mr_f fr n) + -224 <? 2) eqn:EC2; mr_br.
      + apply Z.ltb_lt in EC2.
        assert (HCMD : sf_cmd (mr_f fr n) = 224 \/ sf_cmd (mr_f fr n) = 225) by lia.
        replace ((sf_cmd (mr_f fr n) =? 224) || (sf_cmd (mr_f fr n) =? 225)) with true in MSW
          by (destruct HCMD as [E|E]; rewrite E; reflexivity).
        mr_mod MSW.
        eapply SW_ANN; [ exact MSW | exact MTx | exact Hr1 | exact HCMD | exact FRz | exact SFz | exact F8z | exact STc | exact MUz | exact WMz | exact MIc | exact WMc | exact BFz ].
      + apply Z.ltb_ge in EC2.
        replace (sf_cmd (mr_f fr n) =? 224) with false in MSW by (symmetry; apply Z.eqb_neq; lia).
        replace (sf_cmd (mr_f fr n) =? 225) with false in MSW by (symmetry; apply Z.eqb_neq; lia).
        replace (sf_cmd (mr_f fr n) =? 160) with false in MSW by (symmetry; apply Z.eqb_neq; lia).
        replace (sf_cmd (mr_f fr n) =? 0) with false in MSW by (symmetry; apply Z.eqb_neq; lia).
        mr_mod MSW.
        rewrite <- EST2.
        eapply SW_E3; [ exact MSW | exact MTx | exact Hr1 | exact FRz | exact SFz | exact F8z | exact STc | exact MUz | exact WMz | exact MIc | exact WMc ].
    - apply Z.ltb_ge in EC223.
      replace (sf_cmd (mr_f fr n) =? 224) with false in MSW by (symmetry; apply Z.eqb_neq; lia).
      replace (sf_cmd (mr_f fr n) =? 225) with false in MSW by (symmetry; apply Z.eqb_neq; lia).
      replace (sf_cmd (mr_f fr n) =? 227) with false in MSW by (symmetry; apply Z.eqb_neq; lia).
      mr_mod MSW.
      step.
      rewrite (mr_eqb (sf_cmd (mr_f fr n)) 0) by lia.
      destruct (sf_cmd (mr_f fr n) =? 0) eqn:EC0; mr_br.
      + apply Z.eqb_eq in EC0.
        replace (sf_cmd (mr_f fr n) =? 160) with false in MSW by (rewrite EC0; reflexivity).
        replace (sf_cmd (mr_f fr n) =? 0) with true in MSW by (rewrite EC0; reflexivity).
        mr_mod MSW.
        rewrite <- EGN2.
        eapply SW_DATA; [ exact MSW | exact MTx | exact Hr1 | exact FRz | exact SFz | exact F8z | exact STc | exact MUz | exact WMz | exact MIc | exact WMc | exact BFz ].
      + replace (sf_cmd (mr_f fr n) =? 0) with false in MSW by (symmetry; exact EC0).
        mr_mod MSW.
        rewrite <- EST2.
        eapply SW_ACK; [ exact MSW | exact MTx | exact Hr1 | exact FRz | exact SFz | exact F8z | exact STc | exact MUz | exact WMz | exact MIc | exact WMc ].
  }
  (* ---- 0x1599c: the desk check ---- *)
  assert (MID1 : forall (mz : word -> option byte)
                   (raz q5 q6 q7 q9 q10 q11 q12 q13 q14 q15 q16 q17 q18 q19 q28 q29 q30 q31 : word)
                   (j8 : list byte),
    (if truth (M_desk_known B)
     then if beq_bytes (sub (tf_bytes fr) 6 6) (M_desk B) then mr_k timg_ubsan fr n B else Some (B, 0)
     else if negb ((sf_cmd (mr_f fr n) =? SPEC_CMD_E0) || (sf_cmd (mr_f fr n) =? SPEC_CMD_E1))
          then Some (B, 0)
          else if negb (beq_bytes (firstn 3 (sub (tf_bytes fr) 6 6)) SPEC_OUI)
               then Some (B, 0)
               else mr_k timg_ubsan fr n (set_M_desk_known (set_M_desk B (sub (tf_bytes fr) 6 6)) 1))
      = Some (B', r) ->
    rw_cells rsegs mz (bv_unsigned sp + -40) [C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
    rw_cells rsegs mz (bv_unsigned sp + -120) (mr_sfc (tf_addr fr) (mr_f fr n)) ->
    rw_cells rsegs mz (bv_unsigned sp + -128) [CB 8 j8] ->
    stk rsegs mz lo (bv_unsigned sp + -128) ->
    munch [(bv_unsigned sp - 208, bv_unsigned sp); (W_BASE_UBSAN, W_BASE_UBSAN + W_LEN)] m mz ->
    wmono rsegs m mz -> mem_inv rsegs mz -> wmem rsegs mz B -> bytes_at rsegs mz (tf_addr fr) (tf_bytes fr) ->
    evt rsegs QQ
      (MS (mkR raz (Z_to_bv 64 (bv_unsigned sp + -128)) gp tp q5 q6 q7 (Z_to_bv 64 (tf_addr fr + 6)) q9 q10
               q11 q12 q13 q14 q15 q16 q17 q18 q19 s4 s5 s6 s7 s8 s9 s10 s11 q28 q29 q30 q31)
          F (Z_to_bv 64 0x1599c) fc None mz (seg_rom rsegs))).
  { clear FR40 FR8 STc WMc SFc MIc BF MU WMo MOD.
    intros mz raz q5 q6 q7 q9 q10 q11 q12 q13 q14 q15 q16 q17 q18 q19 q28 q29 q30 q31 j8
      MD1 FRz SFz F8z STc MUz WMz MIc WMc BFz.
    pose proof (wm_len rsegs W_BASE_UBSAN mz B WMc) as LB.
    pose proof (bytes_at_bound rsegs mz _ _ BFz) as FBz.
    cbv beta delta [mr_sfc] in SFz.
    unfold truth, SPEC_CMD_E0, SPEC_CMD_E1 in MD1.
    pose proof (s32_range B A_M_state) as RST.
    change (s32_at B A_M_state) with (M_state B) in RST.
    do 4 step.
    change (s32_at B 0) with (M_desk_known B).
    rewrite (mr_eqb (M_desk_known B) 0)
      by (pose proof (s32_range B A_M_desk_known) as R;
          change (s32_at B A_M_desk_known) with (M_desk_known B) in R; lia).
    assert (BSRC : bytes_at rsegs mz (tf_addr fr + 6) (sub (tf_bytes fr) 6 6))
      by (apply mr_bsub; [exact BFz | lia | lia]).
    assert (L6 : length (sub (tf_bytes fr) 6 6) = 6%nat) by (apply length_sub; lia).
    destruct (M_desk_known B =? 0) eqn:EDK; mr_br; mr_mod MD1.
    - (* no desk yet: 0x15a20 *)
      do 4 step.
      mr_ext. rewrite mr_u8 by lia. rewrite (unsigned_lit (sf_cmd (mr_f fr n))) by lia.
      rewrite (mr_eqb (Z.land (sf_cmd (mr_f fr n)) 254) 224)
        by (pose proof (mr_land254r (sf_cmd (mr_f fr n)) CMDR); lia).
      rewrite mr_land254 by lia.
      destruct ((sf_cmd (mr_f fr n) =? 224) || (sf_cmd (mr_f fr n) =? 225)) eqn:EANN; mr_br; mr_mod MD1.
      2: { step. injection MD1 as EB Er. subst B' r.
           eapply EPI; [ reflexivity | reflexivity | exact FRz | exact SFz | reflexivity | exact F8z
                       | exact STc | exact MUz | exact WMz | exact MIc | exact WMc ]. }
      rewrite mr_firstn3 in MD1.
      assert (BSRC3 : bytes_at rsegs mz (tf_addr fr + 6) (sub (tf_bytes fr) 6 3))
        by (apply mr_bsub; [exact BFz | lia | lia]).
      assert (L3 : length (sub (tf_bytes fr) 6 3) = 3%nat) by (apply length_sub; lia).
      destruct (memcmp_model_total (sub (tf_bytes fr) 6 3) SPEC_OUI 3 ltac:(lia) ltac:(vm_compute; lia))
        as [v5 Hv5].
      destruct (mr_memcmp 3 _ _ _ Hv5 L3 ltac:(vm_compute; reflexivity)) as [RV5 EV5].
      pose proof (mr_ro _ MIc) as (RH5 & RB5 & RO5).
      do 6 step.
      lazymatch goal with
      | |- evt ?sg _ (MS _ _ _ _ _ ?mm _) =>
          eapply evt_cut;
          [ eapply BC with (ls := sub (tf_bytes fr) 6 3) (rs := SPEC_OUI) (v := v5);
            [ rewrite unsigned_lit by lia; exact BSRC3
            | rewrite unsigned_lit by lia; exact RO5
            | rewrite unsigned_lit by lia; exact Hv5
            | exact MIc ]
          | wk_post_call sg mm ]
      end.
      mr_names.
      step.
      rewrite (mr_eqb v5 0) by lia. rewrite <- EV5 in MD1.
      destruct (v5 =? 0) eqn:EH5; mr_br; mr_mod MD1.
      2: { step. injection MD1 as EB Er. subst B' r.
           eapply EPI; [ reflexivity | reflexivity | exact FRz | exact SFz | reflexivity | exact F8z
                       | exact STc | exact MUz | exact WMz | exact MIc | exact WMc ]. }
      (* 0x15a4c: memcpy (M.desk, f.src, 6) *)
      do 4 step.
      assert (DST : rw_cells rsegs _ (bv_unsigned (Z_to_bv 64 209668))
                      [CB (Z.to_nat (bv_unsigned (Z_to_bv 64 6))) (sub B 4 (Z.to_nat (bv_unsigned (Z_to_bv 64 6))))])
        by (apply (wm_piece rsegs W_BASE_UBSAN _ B 4); [exact WMc | vm_compute; reflexivity | lia | wk_side | wk_side]).
      assert (U1 : bv_unsigned (Z_to_bv 64 209668) = 209668) by reflexivity.
      assert (U2 : bv_unsigned (Z_to_bv 64 6) = 6) by reflexivity.
      lazymatch goal with
      | |- evt ?sg _ (MS _ _ _ _ _ ?mm _) =>
          eapply evt_cut;
          [ eapply MC with (src := sub (tf_bytes fr) 6 6);
            [ rewrite unsigned_lit by lia; exact BSRC
            | rewrite unsigned_lit by lia; exact L6
            | exact DST
            | rewrite !unsigned_lit by lia; destruct OWd; [left|right]; lia
            | exact MIc ]
          | let ms' := fresh "ms'" in let PO := fresh "PO" in
            intros ms' PO; unfold memcpy_post in PO;
            destruct PO as (y5 & y6 & y7 & y11 & y12 & y13 & y14 & y15 & y16 & y17 & y28 & y29 & y30 & y31 & m2 &
                            EQ & MUm & WMm & MIm & DC & BSm);
            subst ms';
            pose proof (mr_stk_cell _ _ _ _ _ _ _ STc MUm WMm DC ltac:(reflexivity)) as ST2;
            wk_facts;
            wk_world_after_call sg mm m2;
            transport_after_call sg mm m2 MUm WMm;
            clear MUm WMm;
            try (match goal with H : mem_inv sg mm |- _ => clear H end);
            try clear mm ]
      end.
      rewrite (ret_pc_even 88668) by (first [lia | reflexivity]).
      try clear STc. rename ST2 into STc.
      mr_names.
      (* 0x15a5c: lw a1,12(s1); li a0,1; sw a0,0(s1); beq a1,s2,15c50 *)
      do 4 step.
      mr_pushG 12 M_state B LB.
      mr_names.
      unfold mr_k, S_CLOSED in MD1.
      assert (ESTD : M_state (set_M_desk_known (set_M_desk B (sub (tf_bytes fr) 6 6)) 1) = M_state B)
        by (mr_unf; mr_push LB; reflexivity).
      rewrite ESTD in MD1.
      rewrite (mr_eqb (M_state B) 3) by lia.
      destruct (M_state B =? 3) eqn:ECL; mr_br; mr_mod MD1.
      { step. injection MD1 as EB Er. subst B' r.
        eapply EPI; [ reflexivity | reflexivity | exact FRz | exact SFz | reflexivity | exact F8z
                    | exact STc | exact MUz | exact WMz | exact MIc | exact WMc ]. }
      destruct (mr_sw timg_ubsan fr n (set_M_last_rx (set_M_desk_known (set_M_desk B (sub (tf_bytes fr) 6 6)) 1)
                  (g_now (set_M_desk_known (set_M_desk B (sub (tf_bytes fr) 6 6)) 1))))
        as [[B3 []]|] eqn:EMSW; mr_mod MD1; [|discriminate MD1].
      destruct (m_tick_m B3) as [[B4 []]|] eqn:EMT; mr_mod MD1; [|discriminate MD1].
      injection MD1 as EB Er. subst B' r.
      step.
      rewrite <- ESTD.
      eapply MID2; [ exact EMSW | exact EMT | reflexivity | exact FRz | exact SFz | exact F8z | exact STc | exact MUz | exact WMz | exact MIc | exact WMc | exact BFz ].
    - (* a known desk: 0x159ac, bcmp (f.src, M.desk, 6) *)
      assert (BDESK : bytes_at rsegs mz 209668 (sub B 4 6))
        by (apply (wm_src rsegs W_BASE_UBSAN mz B 4 6 209668 WMc); lia).
      assert (LD : length (sub B 4 6) = 6%nat) by (apply length_sub; [lia | rewrite LB; unfold W_LEN; lia]).
      destruct (memcmp_model_total (sub (tf_bytes fr) 6 6) (sub B 4 6) 6 ltac:(lia) ltac:(lia)) as [v4 Hv4].
      destruct (mr_memcmp 6 _ _ _ Hv4 L6 LD) as [RV4 EV4].
      do 4 step.
      lazymatch goal with
      | |- evt ?sg _ (MS _ _ _ _ _ ?mm _) =>
          eapply evt_cut;
          [ eapply BC with (ls := sub (tf_bytes fr) 6 6) (rs := sub B 4 6) (v := v4);
            [ rewrite unsigned_lit by lia; exact BSRC
            | rewrite unsigned_lit by lia; exact BDESK
            | rewrite unsigned_lit by lia; exact Hv4
            | exact MIc ]
          | wk_post_call sg mm ]
      end.
      mr_names.
      do 3 step.
      rewrite (mr_eqb v4 0) by lia.
      change (M_desk B) with (sub B 4 6) in MD1. rewrite <- EV4 in MD1.
      destruct (v4 =? 0) eqn:EH4; mr_br; mr_mod MD1.
      2: { injection MD1 as EB Er. subst B' r.
           eapply EPI; [ reflexivity | reflexivity | exact FRz | exact SFz | reflexivity | exact F8z
                       | exact STc | exact MUz | exact WMz | exact MIc | exact WMc ]. }
      do 3 step.
      change (s32_at B 12) with (M_state B).
      rewrite (mr_eqb (M_state B) 3) by lia.
      unfold mr_k, S_CLOSED in MD1.
      destruct (M_state B =? 3) eqn:ECL; mr_br; mr_mod MD1.
      { injection MD1 as EB Er. subst B' r.
        eapply EPI; [ reflexivity | reflexivity | exact FRz | exact SFz | reflexivity | exact F8z
                    | exact STc | exact MUz | exact WMz | exact MIc | exact WMc ]. }
      destruct (mr_sw timg_ubsan fr n (set_M_last_rx B (g_now B))) as [[B3 []]|] eqn:EMSW; mr_mod MD1;
        [|discriminate MD1].
      destruct (m_tick_m B3) as [[B4 []]|] eqn:EMT; mr_mod MD1; [|discriminate MD1].
      injection MD1 as EB Er. subst B' r.
      step.
      mr_ext. rewrite mr_u8 by lia.
      eapply MID2; [ exact EMSW | exact EMT | reflexivity | exact FRz | exact SFz | exact F8z | exact STc | exact MUz | exact WMz | exact MIc | exact WMc | exact BFz ].
  }
  (* ---- 0x1594c: bcmp (f.src, HOST, 6) ---- *)
  pose proof (mr_ro _ MIc) as (RHOST & RBCAST & ROUI).
  assert (BSRC : bytes_at rsegs _ (tf_addr fr + 6) (sub (tf_bytes fr) 6 6))
    by (apply mr_bsub; [exact BF | lia | lia]).
  assert (L6 : length (sub (tf_bytes fr) 6 6) = 6%nat) by (apply length_sub; lia).
  destruct (memcmp_model_total (sub (tf_bytes fr) 6 6) HOST 6 ltac:(lia) ltac:(vm_compute; lia)) as [v1 Hv1].
  destruct (mr_memcmp 6 _ _ _ Hv1 L6 ltac:(vm_compute; reflexivity)) as [RV1 EV1].
  do 6 step.
  lazymatch goal with
  | |- evt ?sg _ (MS _ _ _ _ _ ?mm _) =>
      eapply evt_cut;
      [ eapply BC with (ls := sub (tf_bytes fr) 6 6) (rs := HOST) (v := v1);
        [ rewrite unsigned_lit by lia; exact BSRC
        | rewrite unsigned_lit by lia; exact RHOST
        | rewrite unsigned_lit by lia; exact Hv1
        | exact MIc ]
      | wk_post_call sg mm ]
  end.
  mr_names.
  (* 0x15964: f.src = HOST *)
  step.
  rewrite (mr_eqb v1 0) by lia. rewrite <- EV1 in MOD.
  destruct (v1 =? 0) eqn:EH1; mr_br; mr_mod MOD.
  { apply Z.eqb_eq in EH1. injection MOD as EB Er. subst B' r.
    eapply EPI; [ exact EH1 | reflexivity | exact FR40 | exact SFc | reflexivity | exact FR8 | exact STc
                | exact MU | exact WMo | exact MIc | exact WMc ]. }
  (* 0x15968: bcmp (f.dst, HOST, 6) *)
  assert (BDST : bytes_at rsegs _ (tf_addr fr + 0) (sub (tf_bytes fr) 0 6))
    by (apply mr_bsub; [exact BF | lia | lia]).
  assert (L0 : length (sub (tf_bytes fr) 0 6) = 6%nat) by (apply length_sub; lia).
  destruct (memcmp_model_total (sub (tf_bytes fr) 0 6) HOST 6 ltac:(lia) ltac:(vm_compute; lia)) as [v2 Hv2].
  destruct (mr_memcmp 6 _ _ _ Hv2 L0 ltac:(vm_compute; reflexivity)) as [RV2 EV2].
  pose proof (mr_ro _ MIc) as (RH2 & RB2 & RO2).
  do 6 step.
  lazymatch goal with
  | |- evt ?sg _ (MS _ _ _ _ _ ?mm _) =>
      eapply evt_cut;
      [ eapply BC with (ls := sub (tf_bytes fr) 0 6) (rs := HOST) (v := v2);
        [ rewrite unsigned_lit by lia; first [ exact BDST | rewrite Z.add_0_r in BDST; exact BDST ]
        | rewrite unsigned_lit by lia; exact RH2
        | rewrite unsigned_lit by lia; exact Hv2
        | exact MIc ]
      | wk_post_call sg mm ]
  end.
  mr_names.
  step.
  rewrite (mr_eqb v2 0) by lia. rewrite <- EV2 in MOD.
  destruct (v2 =? 0) eqn:EH2; mr_br; mr_mod MOD.
  { eapply MID1; [ exact MOD | exact FR40 | exact SFc | exact FR8 | exact STc | exact MU | exact WMo | exact MIc
                 | exact WMc | exact BF ]. }
  (* 0x15984: bcmp (f.dst, SPEC_BCAST, 6) *)
  destruct (memcmp_model_total (sub (tf_bytes fr) 0 6) SPEC_BCAST 6 ltac:(lia) ltac:(vm_compute; lia)) as [v3 Hv3].
  destruct (mr_memcmp 6 _ _ _ Hv3 L0 ltac:(vm_compute; reflexivity)) as [RV3 EV3].
  pose proof (mr_ro _ MIc) as (RH3 & RB3 & RO3).
  do 5 step.
  lazymatch goal with
  | |- evt ?sg _ (MS _ _ _ _ _ ?mm _) =>
      eapply evt_cut;
      [ eapply BC with (ls := sub (tf_bytes fr) 0 6) (rs := SPEC_BCAST) (v := v3);
        [ rewrite unsigned_lit by lia; first [ exact BDST | rewrite Z.add_0_r in BDST; exact BDST ]
        | rewrite unsigned_lit by lia; exact RB3
        | rewrite unsigned_lit by lia; exact Hv3
        | exact MIc ]
      | wk_post_call sg mm ]
  end.
  mr_names.
  step.
  rewrite (mr_eqb v3 0) by lia. rewrite <- EV3 in MOD.
  destruct (v3 =? 0) eqn:EH3; mr_br; mr_mod MOD.
  - eapply MID1; [ exact MOD | exact FR40 | exact SFc | exact FR8 | exact STc | exact MU | exact WMo | exact MIc
                 | exact WMc | exact BF ].
  - step. injection MOD as EB Er. subst B' r.
    eapply EPI; [ reflexivity | reflexivity | exact FR40 | exact SFc | reflexivity | exact FR8 | exact STc
                | exact MU | exact WMo | exact MIc | exact WMc ].
Qed.
