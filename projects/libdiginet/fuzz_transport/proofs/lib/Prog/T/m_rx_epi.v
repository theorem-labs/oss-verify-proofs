From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Arr Bytes.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib Require Import Img0.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require Import DgnSpec DgnLib StrFun.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require Import TWorld TWorldLemmas TWorldMem TImg TSess0 TCb.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Prog Require Import bcmp_c memcpy_c.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Prog.T Require Import TImgP WMem TContract.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Prog.T Require Import m_rx_c m_lost_c m_maybe_online_c m_tick_c.
Import ListNotations.
Open Scope Z_scope.

Local Notation "'let*' p ':=' c1 'in' c2" := (match c1 with Some p => c2 | None => None end)
  (at level 200, p pattern, c1 at level 200, c2 at level 200).

(* ---- m_rx_m (TCb.v:244-330) split at the points the binary branches to. The fields of the parse when it is
   SPEC_OK (DgnSpec.v spec_read_frame, :243-250): src = bytes 6 .. 11, dst = bytes 0 .. 5, the rest below. ---- *)
Definition mrx_fc (fr : tframe) : Z := byte_at (zs (tf_bytes fr)) 28.
Definition mrx_blen (fr : tframe) : Z := spec_be16 (zs (tf_bytes fr)) 14 - 16.
Definition mrx_retry (fr : tframe) : Z := spec_be16 (zs (tf_bytes fr)) 26.
Definition mrx_send (fr : tframe) : Z := spec_be32 (zs (tf_bytes fr)) 18.
Definition mrx_ack (fr : tframe) : Z := spec_be32 (zs (tf_bytes fr)) 22.
Definition mrx_body (fr : tframe) : list byte := skipn 30 (tf_bytes fr).
Definition mrx_src (fr : tframe) : list byte := sub (tf_bytes fr) 6 6.
Definition mrx_dst (fr : tframe) : list byte := sub (tf_bytes fr) 0 6.

(* :319-329, cmd e1 once OW.desk_p / OW.desk_body are stored (world B4) *)
Definition mrx_e1 (B4 : list byte) (off : Z) : option (list byte * unit) :=
  if 0 <=? off then
    m_maybe_online_m (set_M_e1_us (set_M_foreign B4 0) 1)
  else
    let* fo := int_inc (OW_foreign (set_M_foreign B4 1)) in
    if (M_state (set_OW_foreign (set_M_foreign B4 1) fo) =? S_ONLINE) ||
       (M_state (set_OW_foreign (set_M_foreign B4 1) fo) =? S_WAKING)
    then m_lost_m (set_OW_foreign (set_M_foreign B4 1) fo) R_FOREIGN
    else Some (set_OW_foreign (set_M_foreign B4 1) fo, tt).

(* :317-318, cmd e0 after its m_lost (world B6) *)
Definition mrx_e0w (B6 : list byte) : option (list byte * unit) :=
  if (M_state B6 =? S_IDLE) && truth (Cfg_auto_wake B6) then
    let* (B7, _) := m_wake_m B6 in Some (B7, tt)
  else Some (B6, tt).

(* :312-318, cmd e0 once OW.desk_p / OW.desk_body are stored (world B4) *)
Definition mrx_e0 (B4 : list byte) : option (list byte * unit) :=
  let* (B6, _) := if M_state (set_M_foreign B4 0) =? S_ONLINE then m_lost_m (set_M_foreign B4 0) R_DESK_OFFLINE
                  else Some (set_M_foreign B4 0, tt) in
  mrx_e0w B6.

(* :308-330, once host_offset gave off *)
Definition mrx_ann_tail (I : timg) (fr : tframe) (B2 : list byte) (off : Z) : option (list byte * unit) :=
  let* d := int_inc (OW_desk B2) in
  let* (_, dp) := desk_named_m I (set_OW_desk_off (set_OW_desk B2 d) off) (mrx_body fr) in
  if mrx_fc fr =? SPEC_CMD_E0 then
    mrx_e0 (set_OW_desk_body (set_OW_desk_p (set_OW_desk_off (set_OW_desk B2 d) off) dp) (tf_addr fr + 30))
  else
    mrx_e1 (set_OW_desk_body (set_OW_desk_p (set_OW_desk_off (set_OW_desk B2 d) off) dp) (tf_addr fr + 30)) off.

(* :303-330, cmd e0 / e1 *)
Definition mrx_ann (I : timg) (fr : tframe) (B2 : list byte) : option (list byte * unit) :=
  if mrx_blen fr <? SPEC_ANN_MIN then Some (B2, tt) else
  let* (_, off) := if mrx_fc fr =? SPEC_CMD_E1 then host_offset_m B2 (mrx_body fr) else Some (B2, -1) in
  mrx_ann_tail I fr B2 off.

(* :332-342, cmd ACK *)
Definition mrx_ackb (fr : tframe) (B2 : list byte) : option (list byte * unit) :=
  if truth (M_fly_on B2) && (mrx_ack fr =? M_fly_counter B2) then
    let* a := int_inc (OW_acked B2) in
    let B6 := set_M_fly_on (set_OW_acked_retry (set_OW_acked_counter (set_OW_acked B2 a)
                (M_fly_counter (set_OW_acked B2 a)))
                (M_fly_retries (set_OW_acked_counter (set_OW_acked B2 a) (M_fly_counter (set_OW_acked B2 a))))) 0 in
    if M_state B6 =? S_WAKING then m_maybe_online_m (set_M_e2_acked B6 1)
    else Some (B6, tt)
  else Some (B2, tt).

(* :358-364, OW.dn[OW.ndata] and OW.ndata, from the world B5 after the desk counter *)
Definition mrx_data6 (fr : tframe) (B5 : list byte) : option (list byte * unit) :=
  let* B6 :=
    if OW_ndata B5 <? 2 then
      if OW_ndata B5 <? 0 then None
      else Some (set_OW_dn_retry (set_OW_dn_counter (set_OW_dn_len (set_OW_dn_body B5 (OW_ndata B5) (tf_addr fr + 30))
                    (OW_ndata B5) (mrx_blen fr)) (OW_ndata B5) (mrx_send fr)) (OW_ndata B5) (mrx_retry fr))
    else Some B5 in
  let* nd1 := int_inc (OW_ndata B5) in
  Some (set_OW_ndata B6 nd1, tt).

(* :354-357, the desk counter and the keepalive *)
Definition mrx_data5 (fr : tframe) (B4 : list byte) : option (list byte * unit) :=
  if (mrx_blen fr =? 1) && (at8 (mrx_body fr) 0 =? 0)
  then Some (set_M_desk_counter_valid (set_M_desk_counter B4 (mrx_send fr)) 1, tt)
  else mrx_data6 fr (set_M_desk_counter_valid (set_M_desk_counter B4 (mrx_send fr)) 1).

(* :344-365, cmd DATA, from the world B4 after OW.acks, M.fail and the backoff *)
Definition mrx_data4 (fr : tframe) (B4 : list byte) : option (list byte * unit) :=
  if truth (M_desk_counter_valid B4) && (mrx_send fr =? M_desk_counter B4) && truth (mrx_retry fr) then Some (B4, tt)
  else mrx_data5 fr B4.

Definition mrx_data (fr : tframe) (B2 : list byte) : option (list byte * unit) :=
  let* ak := int_inc (OW_acks B2) in
  mrx_data4 fr
    (if truth (mrx_retry fr)
     then set_M_backoff_until (set_M_fail (set_OW_acks B2 ak) 0)
            (u64 (g_now (set_M_fail (set_OW_acks B2 ak) 0) + h_ms_m (Cfg_backoff_ms (set_M_fail (set_OW_acks B2 ak) 0))))
     else set_M_fail (set_OW_acks B2 ak) 0).

(* :302-372, the switch *)
Definition mrx_sw (I : timg) (fr : tframe) (B2 : list byte) : option (list byte * unit) :=
  if (mrx_fc fr =? SPEC_CMD_E0) || (mrx_fc fr =? SPEC_CMD_E1) then mrx_ann I fr B2
  else if mrx_fc fr =? SPEC_CMD_ACK then mrx_ackb fr B2
  else if mrx_fc fr =? SPEC_CMD_DATA then mrx_data fr B2
  else if mrx_fc fr =? SPEC_CMD_E3 then
    if (M_state B2 =? S_ONLINE) || (M_state B2 =? S_WAKING) then m_lost_m B2 R_DESK_DISCONNECT
    else Some (B2, tt)
  else Some (B2, tt).

(* :299-301, :373-374, once the desk is known *)
Definition mrx_k (I : timg) (fr : tframe) (B1 : list byte) : option (list byte * Z) :=
  if M_state B1 =? S_CLOSED then Some (B1, 0)
  else
    let* (B3, _) := mrx_sw I fr (set_M_last_rx B1 (g_now B1)) in
    let* (B4, _) := m_tick_m B3 in
    Some (B4, 1).

(* :288-297, once the frame is from not-HOST to HOST or broadcast *)
Definition mrx_desk_m (I : timg) (fr : tframe) (B : list byte) : option (list byte * Z) :=
  if truth (M_desk_known B) then
    if beq_bytes (mrx_src fr) (M_desk B) then mrx_k I fr B else Some (B, 0)
  else if negb ((mrx_fc fr =? SPEC_CMD_E0) || (mrx_fc fr =? SPEC_CMD_E1)) then Some (B, 0)
  else if negb (beq_bytes (firstn 3 (mrx_src fr)) SPEC_OUI) then Some (B, 0)
  else mrx_k I fr (set_M_desk_known (set_M_desk B (mrx_src fr)) 1).

(* :285-297 *)
Definition mrx_top (I : timg) (fr : tframe) (B : list byte) : option (list byte * Z) :=
  if beq_bytes (mrx_src fr) HOST || (negb (beq_bytes (mrx_dst fr) HOST) && negb (beq_bytes (mrx_dst fr) SPEC_BCAST))
  then Some (B, 0)
  else mrx_desk_m I fr B.

Lemma mrx_m_ok : forall I fr B n, 30 <= n <= Z.of_nat (length (tf_bytes fr)) ->
  spec_be16 (zs (tf_bytes fr)) 12 = SPEC_ETHERTYPE ->
  16 <= spec_be16 (zs (tf_bytes fr)) 14 <= n - 14 ->
  m_rx_m I (Some fr) B n = mrx_top I fr B.
Proof.
  intros I fr B n Hn Het Hnb.
  assert (E1 : (n <? 0) || (Z.of_nat (length (tf_bytes fr)) <? n) = false)
    by (apply orb_false_iff; split; apply Z.ltb_ge; lia).
  assert (E2 : (n <? SPEC_BODY_AT) = false) by (apply Z.ltb_ge; unfold SPEC_BODY_AT; lia).
  assert (E3 : (spec_be16 (zs (tf_bytes fr)) 12 =? SPEC_ETHERTYPE) = true) by (apply Z.eqb_eq; exact Het).
  assert (E4 : (spec_be16 (zs (tf_bytes fr)) SPEC_AT_NUMBYTES <? SPEC_HDR) ||
               (n - SPEC_ETH_HDR <? spec_be16 (zs (tf_bytes fr)) SPEC_AT_NUMBYTES) = false)
    by (apply orb_false_iff; split; apply Z.ltb_ge; unfold SPEC_AT_NUMBYTES, SPEC_HDR, SPEC_ETH_HDR; lia).
  unfold m_rx_m. cbv zeta. rewrite E1. unfold spec_read_frame. cbv zeta. rewrite E2, E3, E4.
  reflexivity.
Qed.

Lemma mrx_m_et : forall I fr B n, 30 <= n <= Z.of_nat (length (tf_bytes fr)) ->
  spec_be16 (zs (tf_bytes fr)) 12 <> SPEC_ETHERTYPE ->
  m_rx_m I (Some fr) B n = Some (B, 0).
Proof.
  intros I fr B n Hn Het.
  assert (E1 : (n <? 0) || (Z.of_nat (length (tf_bytes fr)) <? n) = false)
    by (apply orb_false_iff; split; apply Z.ltb_ge; lia).
  assert (E2 : (n <? SPEC_BODY_AT) = false) by (apply Z.ltb_ge; unfold SPEC_BODY_AT; lia).
  assert (E3 : (spec_be16 (zs (tf_bytes fr)) 12 =? SPEC_ETHERTYPE) = false) by (apply Z.eqb_neq; exact Het).
  unfold m_rx_m. cbv zeta. rewrite E1. unfold spec_read_frame. cbv zeta. rewrite E2, E3.
  reflexivity.
Qed.

Lemma mrx_m_len : forall I fr B n, 30 <= n <= Z.of_nat (length (tf_bytes fr)) ->
  spec_be16 (zs (tf_bytes fr)) 12 = SPEC_ETHERTYPE ->
  spec_be16 (zs (tf_bytes fr)) 14 < 16 \/ n - 14 < spec_be16 (zs (tf_bytes fr)) 14 ->
  m_rx_m I (Some fr) B n = Some (B, 0).
Proof.
  intros I fr B n Hn Het Hnb.
  assert (E1 : (n <? 0) || (Z.of_nat (length (tf_bytes fr)) <? n) = false)
    by (apply orb_false_iff; split; apply Z.ltb_ge; lia).
  assert (E2 : (n <? SPEC_BODY_AT) = false) by (apply Z.ltb_ge; unfold SPEC_BODY_AT; lia).
  assert (E3 : (spec_be16 (zs (tf_bytes fr)) 12 =? SPEC_ETHERTYPE) = true) by (apply Z.eqb_eq; exact Het).
  assert (E4 : (spec_be16 (zs (tf_bytes fr)) SPEC_AT_NUMBYTES <? SPEC_HDR) ||
               (n - SPEC_ETH_HDR <? spec_be16 (zs (tf_bytes fr)) SPEC_AT_NUMBYTES) = true)
    by (apply orb_true_iff; unfold SPEC_AT_NUMBYTES, SPEC_HDR, SPEC_ETH_HDR;
        destruct Hnb; [left | right]; apply Z.ltb_lt; lia).
  unfold m_rx_m. cbv zeta. rewrite E1. unfold spec_read_frame. cbv zeta. rewrite E2, E3, E4.
  reflexivity.
Qed.

(* ---- the frame block's bytes ---- *)
Lemma mrx_bytes_skipn : forall m a bs k, bytes_at rsegs m a bs -> (k <= length bs)%nat ->
  bytes_at rsegs m (a + Z.of_nat k) (skipn k bs).
Proof.
  intros m a bs k H Hk. rewrite <- (firstn_skipn k bs) in H. apply bytes_at_app in H. destruct H as [_ H].
  rewrite length_firstn, Nat.min_l in H by exact Hk. exact H.
Qed.

Lemma mrx_bytes_sub : forall m a bs k n, bytes_at rsegs m a bs -> 0 <= k -> k + Z.of_nat n <= Z.of_nat (length bs) ->
  bytes_at rsegs m (a + k) (sub bs k n).
Proof.
  intros m a bs k n H Hk Hn. pose proof (mrx_bytes_skipn m a bs (Z.to_nat k) H ltac:(lia)) as H1.
  rewrite Z2Nat.id in H1 by exact Hk. unfold sub.
  rewrite <- (firstn_skipn n (skipn (Z.to_nat k) bs)) in H1. apply bytes_at_app in H1. exact (proj1 H1).
Qed.

(* ---- bcmp: memcmp_model and beq_bytes ---- *)
Lemma mrx_memcmp : forall n l r, (n <= length l)%nat -> (n <= length r)%nat ->
  exists v, memcmp_model l r n = Some v /\ -256 < v < 256 /\ (v = 0 <-> zs (firstn n l) = zs (firstn n r)).
Proof.
  induction n as [|n IH]; intros l r Hl Hr.
  - exists 0. split; [reflexivity|]. split; [lia|]. cbn. tauto.
  - destruct l as [|a l]; [cbn in Hl; lia|]. destruct r as [|b r]; [cbn in Hr; lia|].
    cbn [length] in Hl, Hr. cbn [memcmp_model firstn].
    pose proof (bv_unsigned_in_range 8 a) as Ra. pose proof (bv_unsigned_in_range 8 b) as Rb.
    unfold bv_modulus in Ra, Rb. change (2 ^ Z.of_N 8) with 256 in Ra, Rb.
    destruct (Z.eqb_spec (bv_unsigned a) (bv_unsigned b)) as [E|E].
    + destruct (IH l r ltac:(lia) ltac:(lia)) as (v & Hv & Rv & Iv). exists v. split; [exact Hv|]. split; [exact Rv|].
      unfold zs in *. cbn [map]. rewrite Iv. rewrite E. split; [intros ->; reflexivity | intros H; inversion H; reflexivity].
    + exists (bv_unsigned a - bv_unsigned b). split; [reflexivity|]. split; [lia|].
      unfold zs. cbn [map]. split; [lia|]. intros H. inversion H. lia.
Qed.

Lemma mrx_beq_iff : forall a b, beq_bytes a b = true <-> zs a = zs b.
Proof.
  intros a b. unfold beq_bytes. destruct (list_eq_dec Z.eq_dec (zs a) (zs b)); split; congruence.
Qed.

(* bcmp of two 6-byte lists: the value is 0 exactly when beq_bytes holds. *)
Lemma mrx_bcmp6 : forall l r, length l = 6%nat -> length r = 6%nat ->
  exists v, memcmp_model l r 6 = Some v /\ -256 < v < 256 /\ ((v =? 0) = beq_bytes l r).
Proof.
  intros l r Hl Hr. destruct (mrx_memcmp 6 l r ltac:(lia) ltac:(lia)) as (v & Hv & Rv & Iv).
  exists v. split; [exact Hv|]. split; [exact Rv|].
  rewrite firstn_all2 in Iv by lia. rewrite (firstn_all2 r) in Iv by lia.
  destruct (Z.eqb_spec v 0) as [E|E]; destruct (beq_bytes l r) eqn:B; try reflexivity.
  - exfalso. apply Iv in E. apply mrx_beq_iff in E. congruence.
  - exfalso. apply E. apply Iv. apply mrx_beq_iff. exact B.
Qed.

Lemma mrx_bcmp3 : forall l r, (3 <= length l)%nat -> length r = 3%nat ->
  exists v, memcmp_model l r 3 = Some v /\ -256 < v < 256 /\ ((v =? 0) = beq_bytes (firstn 3 l) r).
Proof.
  intros l r Hl Hr. destruct (mrx_memcmp 3 l r ltac:(lia) ltac:(lia)) as (v & Hv & Rv & Iv).
  exists v. split; [exact Hv|]. split; [exact Rv|].
  rewrite (firstn_all2 r) in Iv by lia.
  destruct (Z.eqb_spec v 0) as [E|E]; destruct (beq_bytes (firstn 3 l) r) eqn:B; try reflexivity.
  - exfalso. apply Iv in E. apply mrx_beq_iff in E. congruence.
  - exfalso. apply E. apply Iv. apply mrx_beq_iff. exact B.
Qed.

(* ---- the read-only tables bcmp compares against (.rodata, fuzz_transport.c:109-113, spec.h:67-69) ---- *)
Lemma mrx_host_at : forall m, mem_inv rsegs m -> bytes_at rsegs m 0x10480 HOST.
Proof.
  intros m MI. apply ro_bytes_at; [exact MI | lia | cbn; lia |]. apply ro_bytes_b_sound. vm_compute. reflexivity.
Qed.
Lemma mrx_bcast_at : forall m, mem_inv rsegs m -> bytes_at rsegs m 0x1048c SPEC_BCAST.
Proof.
  intros m MI. apply ro_bytes_at; [exact MI | lia | cbn; lia |]. apply ro_bytes_b_sound. vm_compute. reflexivity.
Qed.
Lemma mrx_oui_at : forall m, mem_inv rsegs m -> bytes_at rsegs m 0x10492 SPEC_OUI.
Proof.
  intros m MI. apply ro_bytes_at; [exact MI | lia | cbn; lia |]. apply ro_bytes_b_sound. vm_compute. reflexivity.
Qed.

(* ---- big-endian fields of the frame (spec.h:148-156) as the machine assembles them ---- *)
Definition mrx_byte (bs : list byte) (k : Z) : Z := bytes_le_to_Z (sub bs k 1).

Lemma mrx_byte_range : forall bs k, 0 <= mrx_byte bs k < 256.
Proof.
  intros bs k. unfold mrx_byte. pose proof (ble_small (sub bs k 1) 1 (length_sub_le bs k 1)) as R. exact R.
Qed.

Lemma mrx_byte_at : forall bs k, 0 <= k -> k < Z.of_nat (length bs) -> byte_at (zs bs) k = mrx_byte bs k.
Proof.
  intros bs k Hk Hl. unfold mrx_byte, byte_at, zs, sub.
  rewrite (nth_indep _ 0 (bv_unsigned (b8 0))) by (rewrite length_map; lia).
  rewrite map_nth.
  destruct (skipn (Z.to_nat k) bs) as [|b bs'] eqn:ESK.
  - exfalso. apply (f_equal (@length _)) in ESK. rewrite length_skipn in ESK. cbn in ESK. lia.
  - cbn [firstn]. rewrite ?firstn_O.
    assert (EB : bytes_le_to_Z [b] = bv_unsigned b) by (rewrite bytes_le_to_Z_le_val; cbn [map le_val]; lia).
    rewrite EB. f_equal.
    pose proof (f_equal (fun l => nth 0%nat l (b8 0)) ESK) as E. cbv beta in E.
    rewrite List.nth_skipn, Nat.add_0_r in E. rewrite E. reflexivity.
Qed.

Lemma mrx_be16 : forall bs p, 0 <= p -> p + 1 < Z.of_nat (length bs) ->
  spec_be16 (zs bs) p = mrx_byte bs p * 2^8 + mrx_byte bs (p + 1).
Proof.
  intros bs p Hp Hl. unfold spec_be16, u16.
  rewrite !mrx_byte_at by lia.
  pose proof (mrx_byte_range bs p). pose proof (mrx_byte_range bs (p + 1)).
  rewrite Z.shiftl_mul_pow2 by lia.
  rewrite (lor_add (mrx_byte bs p * 2^8) (mrx_byte bs (p + 1)) 8) by (try lia; rewrite Z_mod_mult; reflexivity).
  apply Z.mod_small. lia.
Qed.

Lemma mrx_be16_range : forall b p, 0 <= spec_be16 b p < 65536.
Proof. intros b p. unfold spec_be16, u16. apply Z.mod_pos_bound. lia. Qed.

(* ---- branch conditions on 64-bit literals ---- *)
Lemma mrxk_eqb : forall a b, -2^63 <= a < 2^63 -> -2^63 <= b < 2^63 ->
  bv_eqb (Z_to_bv 64 a) (Z_to_bv 64 b) = (a =? b).
Proof.
  intros a b Ha Hb. unfold bv_eqb. rewrite !unsigned_lit_wrap.
  destruct (Z.eqb_spec a b) as [->|N]; [apply Z.eqb_refl|].
  apply Z.eqb_neq. intros E. apply N.
  assert (D : (a - b) mod 2^64 = 0) by (rewrite Zminus_mod, E, Z.sub_diag; reflexivity).
  apply Z.mod_divide in D; [|lia]. destruct D as [c Ec]. nia.
Qed.

Lemma mrxk_ltu : forall a b, 0 <= a < 2^64 -> 0 <= b < 2^64 ->
  bv_ltu (Z_to_bv 64 a) (Z_to_bv 64 b) = (a <? b).
Proof. intros a b Ha Hb. unfold bv_ltu. rewrite !unsigned_lit by lia. reflexivity. Qed.

Lemma mrxk_lts : forall a b, -2^63 <= a < 2^63 -> -2^63 <= b < 2^63 ->
  bv_lts (Z_to_bv 64 a) (Z_to_bv 64 b) = (a <? b).
Proof.
  intros a b Ha Hb. unfold bv_lts. rewrite !Z_to_bv_signed.
  assert (HM : bv_half_modulus 64 = 2^63) by reflexivity.
  rewrite !bv_swrap_small by (rewrite HM; lia). reflexivity.
Qed.

Lemma mrx_be32 : forall bs p, 0 <= p -> p + 3 < Z.of_nat (length bs) ->
  spec_be32 (zs bs) p =
  mrx_byte bs p * 2^24 + mrx_byte bs (p + 1) * 2^16 + mrx_byte bs (p + 2) * 2^8 + mrx_byte bs (p + 3).
Proof.
  intros bs p Hp Hl. unfold spec_be32, u32. rewrite !mrx_byte_at by lia.
  pose proof (mrx_byte_range bs p) as R0. pose proof (mrx_byte_range bs (p + 1)) as R1.
  pose proof (mrx_byte_range bs (p + 2)) as R2. pose proof (mrx_byte_range bs (p + 3)) as R3.
  set (x0 := mrx_byte bs p) in *. set (x1 := mrx_byte bs (p + 1)) in *.
  set (x2 := mrx_byte bs (p + 2)) in *. set (x3 := mrx_byte bs (p + 3)) in *.
  rewrite !Z.shiftl_mul_pow2 by lia.
  rewrite (Z.mod_small (x0 * 2^24)) by lia. rewrite (Z.mod_small (x1 * 2^16)) by lia.
  rewrite (Z.mod_small (x2 * 2^8)) by lia.
  rewrite (lor_add (x2 * 2^8) x3 8) by (try lia; rewrite Z_mod_mult; reflexivity).
  rewrite (lor_add (x1 * 2^16) (x2 * 2^8 + x3) 16) by (try lia; rewrite Z_mod_mult; reflexivity).
  rewrite (lor_add (x0 * 2^24) (x1 * 2^16 + (x2 * 2^8 + x3)) 24) by (try lia; rewrite Z_mod_mult; reflexivity).
  lia.
Qed.

Lemma mrx_be32_range : forall b p, 0 <= p -> p + 3 < Z.of_nat (length b) -> 0 <= spec_be32 (zs b) p < 2^32.
Proof.
  intros b p Hp Hl. rewrite mrx_be32 by lia.
  pose proof (mrx_byte_range b p). pose proof (mrx_byte_range b (p + 1)).
  pose proof (mrx_byte_range b (p + 2)). pose proof (mrx_byte_range b (p + 3)). lia.
Qed.

(* slliw x0, 24: the byte in the top of a 32-bit word, sign-extended *)
Lemma mrx_sw24 : forall x0, 0 <= x0 < 256 ->
  bv_unsigned (Z_to_bv 64 (bv_swrap 32 (bv_unsigned (Z_to_bv 64 x0) ≪ 24))) =
  (if x0 <? 128 then x0 else x0 + (2^40 - 2^8)) * 2^24.
Proof.
  intros x0 H. rewrite (unsigned_lit x0) by lia. rewrite Z.shiftl_mul_pow2 by lia.
  rewrite unsigned_lit_wrap. unfold bv_swrap, bv_wrap.
  change (bv_half_modulus 32) with (2^31). change (bv_modulus 32) with (2^32).
  destruct (Z.ltb_spec x0 128).
  - rewrite (Z.mod_small (x0 * 2^24 + 2^31)) by lia. rewrite Z.mod_small by lia. lia.
  - rewrite <- (Z.mod_unique (x0 * 2^24 + 2^31) (2^32) 1 (x0 * 2^24 + 2^31 - 2^32)) by lia.
    rewrite <- (Z.mod_unique (x0 * 2^24 + 2^31 - 2^32 - 2^31) (2^64) (-1) (x0 * 2^24 - 2^32 + 2^64)) by lia.
    lia.
Qed.

(* slliw x0, 24; slli x1, 16; or; slli x2, 8; or x3; or: the 32-bit big-endian word, sign-extended *)
Lemma mrx_asm_be32 : forall x0 x1 x2 x3, 0 <= x0 < 256 -> 0 <= x1 < 256 -> 0 <= x2 < 256 -> 0 <= x3 < 256 ->
  Z_to_bv 64
    (Z.lor
       (bv_unsigned (Z_to_bv 64 (Z.lor (bv_unsigned (Z_to_bv 64 (bv_unsigned (Z_to_bv 64 x1) ≪ 16)))
                                      (bv_unsigned (Z_to_bv 64 (bv_swrap 32 (bv_unsigned (Z_to_bv 64 x0) ≪ 24)))))))
       (bv_unsigned (Z_to_bv 64 (Z.lor (bv_unsigned (Z_to_bv 64 (bv_unsigned (Z_to_bv 64 x2) ≪ 8)))
                                      (bv_unsigned (Z_to_bv 64 x3))))))
  = Z_to_bv 64 (bv_swrap 32 (x0 * 2^24 + x1 * 2^16 + x2 * 2^8 + x3)).
Proof.
  intros x0 x1 x2 x3 H0 H1 H2 H3.
  rewrite (mrx_sw24 x0 H0).
  rewrite (unsigned_lit x1), (unsigned_lit x2), (unsigned_lit x3) by lia.
  rewrite !Z.shiftl_mul_pow2 by lia.
  rewrite (unsigned_lit (x1 * 2^16)), (unsigned_lit (x2 * 2^8)) by lia.
  set (s := if x0 <? 128 then x0 else x0 + (2^40 - 2^8)).
  assert (Hs : 0 <= s < 2^40 /\ s * 2^24 = x0 * 2^24 + (if x0 <? 128 then 0 else 2^64 - 2^32)).
  { unfold s. destruct (Z.ltb_spec x0 128); lia. }
  rewrite (lor_add' (x1 * 2^16) (s * 2^24) 24) by (try lia; rewrite Z_mod_mult; reflexivity).
  rewrite (unsigned_lit (x1 * 2^16 + s * 2^24)) by lia.
  rewrite (lor_add (x2 * 2^8) x3 8) by (try lia; rewrite Z_mod_mult; reflexivity).
  rewrite (unsigned_lit (x2 * 2^8 + x3)) by lia.
  replace (x1 * 2^16 + s * 2^24) with ((x1 + s * 2^8) * 2^16) by lia.
  rewrite (lor_add ((x1 + s * 2^8) * 2^16) (x2 * 2^8 + x3) 16) by (try lia; rewrite Z_mod_mult; reflexivity).
  apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with (2^64).
  unfold bv_swrap, bv_wrap. change (bv_half_modulus 32) with (2^31). change (bv_modulus 32) with (2^32).
  destruct Hs as [Hs1 Hs2]. unfold s in *. destruct (Z.ltb_spec x0 128).
  - rewrite (Z.mod_small (x0 * 2^24 + x1 * 2^16 + x2 * 2^8 + x3 + 2^31)) by lia.
    rewrite !Z.mod_small by lia. lia.
  - rewrite <- (Z.mod_unique (x0 * 2^24 + x1 * 2^16 + x2 * 2^8 + x3 + 2^31) (2^32) 1
                 (x0 * 2^24 + x1 * 2^16 + x2 * 2^8 + x3 + 2^31 - 2^32)) by lia.
    rewrite (Z.mod_small ((x1 + (x0 + (2^40 - 2^8)) * 2^8) * 2^16 + (x2 * 2^8 + x3))) by lia.
    rewrite <- (Z.mod_unique (x0 * 2^24 + x1 * 2^16 + x2 * 2^8 + x3 + 2^31 - 2^32 - 2^31) (2^64) (-1)
                 (x0 * 2^24 + x1 * 2^16 + x2 * 2^8 + x3 - 2^32 + 2^64)) by lia.
    lia.
Qed.

(* slliw x0, 24; slli x1, 16; or; slli x2, 8; or; then or x3 (DATA's order, 0x156cc-0x15718) *)
Lemma mrx_asm_be32b : forall x0 x1 x2 x3, 0 <= x0 < 256 -> 0 <= x1 < 256 -> 0 <= x2 < 256 -> 0 <= x3 < 256 ->
  Z_to_bv 64
    (Z.lor
       (bv_unsigned (Z_to_bv 64
          (Z.lor
             (bv_unsigned (Z_to_bv 64 (Z.lor (bv_unsigned (Z_to_bv 64 (bv_unsigned (Z_to_bv 64 x1) ≪ 16)))
                                            (bv_unsigned (Z_to_bv 64 (bv_swrap 32 (bv_unsigned (Z_to_bv 64 x0) ≪ 24)))))))
             (bv_unsigned (Z_to_bv 64 (bv_unsigned (Z_to_bv 64 x2) ≪ 8))))))
       (bv_unsigned (Z_to_bv 64 x3)))
  = Z_to_bv 64 (bv_swrap 32 (x0 * 2^24 + x1 * 2^16 + x2 * 2^8 + x3)).
Proof.
  intros x0 x1 x2 x3 H0 H1 H2 H3.
  rewrite (mrx_sw24 x0 H0).
  rewrite (unsigned_lit x1), (unsigned_lit x2), (unsigned_lit x3) by lia.
  rewrite !Z.shiftl_mul_pow2 by lia.
  rewrite (unsigned_lit (x1 * 2^16)), (unsigned_lit (x2 * 2^8)) by lia.
  set (s := if x0 <? 128 then x0 else x0 + (2^40 - 2^8)).
  assert (Hs : 0 <= s < 2^40 /\ s * 2^24 = x0 * 2^24 + (if x0 <? 128 then 0 else 2^64 - 2^32)).
  { unfold s. destruct (Z.ltb_spec x0 128); lia. }
  rewrite (lor_add' (x1 * 2^16) (s * 2^24) 24) by (try lia; rewrite Z_mod_mult; reflexivity).
  rewrite (unsigned_lit (x1 * 2^16 + s * 2^24)) by lia.
  replace (x1 * 2^16 + s * 2^24) with ((x1 + s * 2^8) * 2^16) by lia.
  rewrite (lor_add ((x1 + s * 2^8) * 2^16) (x2 * 2^8) 16) by (try lia; rewrite Z_mod_mult; reflexivity).
  rewrite (unsigned_lit ((x1 + s * 2^8) * 2^16 + x2 * 2^8)) by lia.
  replace ((x1 + s * 2^8) * 2^16 + x2 * 2^8) with ((x1 * 2^8 + s * 2^16 + x2) * 2^8) by lia.
  rewrite (lor_add ((x1 * 2^8 + s * 2^16 + x2) * 2^8) x3 8) by (try lia; rewrite Z_mod_mult; reflexivity).
  apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with (2^64).
  unfold bv_swrap, bv_wrap. change (bv_half_modulus 32) with (2^31). change (bv_modulus 32) with (2^32).
  destruct Hs as [Hs1 Hs2]. unfold s in *. destruct (Z.ltb_spec x0 128).
  - rewrite (Z.mod_small (x0 * 2^24 + x1 * 2^16 + x2 * 2^8 + x3 + 2^31)) by lia.
    rewrite !Z.mod_small by lia. lia.
  - rewrite <- (Z.mod_unique (x0 * 2^24 + x1 * 2^16 + x2 * 2^8 + x3 + 2^31) (2^32) 1
                 (x0 * 2^24 + x1 * 2^16 + x2 * 2^8 + x3 + 2^31 - 2^32)) by lia.
    rewrite (Z.mod_small ((x1 * 2^8 + (x0 + (2^40 - 2^8)) * 2^16 + x2) * 2^8 + x3)) by lia.
    rewrite <- (Z.mod_unique (x0 * 2^24 + x1 * 2^16 + x2 * 2^8 + x3 + 2^31 - 2^32 - 2^31) (2^64) (-1)
                 (x0 * 2^24 + x1 * 2^16 + x2 * 2^8 + x3 - 2^32 + 2^64)) by lia.
    lia.
Qed.

(* slli x, 8; or y: a 16-bit big-endian field *)
Lemma mrx_or8 : forall x y, 0 <= x < 256 -> 0 <= y < 256 ->
  Z.lor (bv_unsigned (Z_to_bv 64 (bv_unsigned (Z_to_bv 64 x) ≪ 8))) (bv_unsigned (Z_to_bv 64 y)) = x * 2^8 + y.
Proof.
  intros x y Hx Hy. rewrite (unsigned_lit x), (unsigned_lit y) by lia. rewrite Z.shiftl_mul_pow2 by lia.
  rewrite (unsigned_lit (x * 2^8)) by lia.
  apply (lor_add (x * 2^8) y 8); [lia | lia | rewrite Z_mod_mult; reflexivity].
Qed.

(* the first byte of the body, as lbu 0(s0) reads it *)
Lemma mrx_at8 : forall bs, 30 < Z.of_nat (length bs) -> at8 (skipn 30 bs) 0 = u_at bs 30 1.
Proof.
  intros bs Hl. unfold at8, bz, u_at, sub. change (Z.to_nat 30) with 30%nat.
  destruct (skipn 30 bs) as [|b bs'] eqn:ESK.
  - exfalso. apply (f_equal (@length _)) in ESK. rewrite length_skipn in ESK. cbn in ESK. lia.
  - cbn [firstn nth]. rewrite ?firstn_O. rewrite bytes_le_to_Z_le_val. cbn [map le_val]. lia.
Qed.

Lemma mrx_sub_skipn : forall bs i n, 0 <= i -> sub (skipn 30 bs) i n = sub bs (30 + i) n.
Proof. intros bs i n Hi. unfold sub. rewrite skipn_skipn. f_equal. f_equal. lia. Qed.

(* addiw x, x, 1 on a small index *)
Lemma mrx_addiw1 : forall i, 0 <= i < 2^31 - 1 -> bv_swrap 32 (bv_unsigned (Z_to_bv 64 i) + 1) = i + 1.
Proof.
  intros i Hi. rewrite unsigned_lit by lia. apply bv_swrap_small.
  change (bv_half_modulus 32) with (2^31). lia.
Qed.

(* two sign-extended 32-bit words compare as their unsigned values *)
Lemma mrx_eqb_sw : forall a b, 0 <= a < 2^32 -> 0 <= b < 2^32 ->
  bv_eqb (Z_to_bv 64 (bv_swrap 32 a)) (Z_to_bv 64 (bv_swrap 32 b)) = (a =? b).
Proof.
  intros a b Ha Hb.
  assert (Ra : -2^31 <= bv_swrap 32 a < 2^31).
  { unfold bv_swrap, bv_wrap. change (bv_half_modulus 32) with (2^31). change (bv_modulus 32) with (2^32).
    pose proof (Z.mod_pos_bound (a + 2^31) (2^32) ltac:(lia)). lia. }
  assert (Rb : -2^31 <= bv_swrap 32 b < 2^31).
  { unfold bv_swrap, bv_wrap. change (bv_half_modulus 32) with (2^31). change (bv_modulus 32) with (2^32).
    pose proof (Z.mod_pos_bound (b + 2^31) (2^32) ltac:(lia)). lia. }
  rewrite mrxk_eqb by lia.
  destruct (Z.eqb_spec a b) as [->|N]; [apply Z.eqb_refl|].
  apply Z.eqb_neq. intros E. apply N. unfold bv_swrap, bv_wrap in E.
  change (bv_half_modulus 32) with (2^31) in E. change (bv_modulus 32) with (2^32) in E.
  destruct (Z.ltb_spec a (2^31)); destruct (Z.ltb_spec b (2^31)).
  - rewrite !Z.mod_small in E by lia. lia.
  - rewrite (Z.mod_small (a + 2^31)) in E by lia.
    rewrite <- (Z.mod_unique (b + 2^31) (2^32) 1 (b + 2^31 - 2^32)) in E by lia. lia.
  - rewrite (Z.mod_small (b + 2^31)) in E by lia.
    rewrite <- (Z.mod_unique (a + 2^31) (2^32) 1 (a + 2^31 - 2^32)) in E by lia. lia.
  - rewrite <- (Z.mod_unique (a + 2^31) (2^32) 1 (a + 2^31 - 2^32)) in E by lia.
    rewrite <- (Z.mod_unique (b + 2^31) (2^32) 1 (b + 2^31 - 2^32)) in E by lia. lia.
Qed.

Lemma mrx_swrap_mod : forall x, bv_swrap 32 x mod 2^32 = x mod 2^32.
Proof.
  intros x. unfold bv_swrap, bv_wrap. change (bv_half_modulus 32) with (2^31). change (bv_modulus 32) with (2^32).
  rewrite Zminus_mod, Zmod_mod, <- Zminus_mod. f_equal. lia.
Qed.

(* ---- what the walk keeps from m_rx_contract's premises, for every segment ---- *)
Definition mrx_fix (sp : word) (lo : Z) (fr : tframe) (n : Z) : Prop :=
  bv_unsigned sp mod 16 = 0 /\ lo + 144 <= bv_unsigned sp /\ W_BASE_PLAIN + W_LEN <= bv_unsigned sp - 144 /\
  0 < tf_addr fr /\
  (tf_addr fr + Z.of_nat (length (tf_bytes fr)) <= W_BASE_PLAIN \/ W_BASE_PLAIN + W_LEN <= tf_addr fr) /\
  (tf_addr fr + Z.of_nat (length (tf_bytes fr)) <= bv_unsigned sp - 144 \/ bv_unsigned sp <= tf_addr fr) /\
  tf_addr fr + Z.of_nat (length (tf_bytes fr)) <= 2^64 /\
  30 <= n <= Z.of_nat (length (tf_bytes fr)) /\
  16 <= spec_be16 (zs (tf_bytes fr)) 14 <= n - 14.

Ltac mrx_fix_intro H :=
  destruct H as (HS16 & LO & WOF & Hfa_pos & HFR_offW & HFR_offSP & Hfa_hi & HN & HNB).

(* ---- reads of the world through disjoint stores (TWorldLemmas.v, with the world's length 65616 carried) ---- *)
Lemma mrx_lenu : forall (bs v : list byte) k, Z.of_nat (length bs) = 65616 -> 0 <= k ->
  k + Z.of_nat (length v) <= 65616 -> Z.of_nat (length (upd bs k v)) = 65616.
Proof. intros bs v k L Hk Hv. rewrite length_upd; lia. Qed.

Lemma mrx_s32_out : forall (bs v : list byte) k k', Z.of_nat (length bs) = 65616 -> 0 <= k -> 0 <= k' ->
  (k' + 4 <= k \/ k + Z.of_nat (length v) <= k') -> k + Z.of_nat (length v) <= 65616 ->
  s32_at (upd bs k v) k' = s32_at bs k'.
Proof. intros. apply s32_at_upd_out; lia. Qed.

Lemma mrx_u_out : forall (bs v : list byte) k k' n, Z.of_nat (length bs) = 65616 -> 0 <= k -> 0 <= k' ->
  (k' + Z.of_nat n <= k \/ k + Z.of_nat (length v) <= k') -> k + Z.of_nat (length v) <= 65616 ->
  u_at (upd bs k v) k' n = u_at bs k' n.
Proof. intros. apply u_at_upd_out; lia. Qed.

Lemma mrx_comm : forall (bs v w : list byte) k k', Z.of_nat (length bs) = 65616 -> 0 <= k -> 0 <= k' ->
  (k' + Z.of_nat (length w) <= k \/ k + Z.of_nat (length v) <= k') ->
  k + Z.of_nat (length v) <= 65616 -> k' + Z.of_nat (length w) <= 65616 ->
  upd (upd bs k v) k' w = upd (upd bs k' w) k v.
Proof. intros. apply upd_upd_comm; lia. Qed.

(* put n only sees its value modulo 2^(8n) *)
Lemma mrx_put_eqm : forall n a b w, 8 * Z.of_nat n <= w -> a mod 2 ^ w = b mod 2 ^ w -> put n a = put n b.
Proof.
  intros n a b w Hw E. unfold put.
  rewrite <- (Z_to_le_bytes_mod n a w), <- (Z_to_le_bytes_mod n b w) by lia. rewrite E. reflexivity.
Qed.

Ltac mrx_len :=
  lazymatch goal with
  | |- Z.of_nat (length (upd ?bs ?k ?v)) = 65616 => apply mrx_lenu; [mrx_len | lia | rewrite ?length_put; lia]
  | |- Z.of_nat (length ?bs) = 65616 => assumption
  end.
Ltac mrx_side := first [ mrx_len | lia | (rewrite ?length_put; lia) ].
(* every read of a world after a store elsewhere, back to the world before it *)
Ltac mrx_rw := repeat first [ rewrite mrx_s32_out by mrx_side | rewrite mrx_u_out by mrx_side ].

(* the world's names unfolded to offsets (lia sees the numbers) *)
Ltac mrx_unf :=
  unfold M_state, M_desk_known, M_foreign, M_e1_us, M_e2_acked, M_fly_on, M_fly_counter, M_fly_retries,
    M_desk_counter, M_desk_counter_valid, M_fail, M_last_rx, M_backoff_until,
    OW_desk, OW_desk_off, OW_desk_p, OW_desk_body, OW_foreign, OW_acked, OW_acked_counter, OW_acked_retry,
    OW_acks, OW_ndata, Cfg_auto_wake, Cfg_backoff_ms, g_now,
    set_M_desk_known, set_M_desk, set_M_foreign, set_M_e1_us, set_M_e2_acked, set_M_fly_on, set_M_desk_counter,
    set_M_desk_counter_valid, set_M_fail, set_M_last_rx, set_M_backoff_until,
    set_OW_desk, set_OW_desk_off, set_OW_desk_p, set_OW_desk_body, set_OW_foreign, set_OW_acked,
    set_OW_acked_counter, set_OW_acked_retry, set_OW_acks, set_OW_ndata,
    A_M_state, A_M_desk_known, A_M_desk, A_M_foreign, A_M_e1_us, A_M_e2_acked, A_M_fly_on, A_M_fly_counter,
    A_M_fly_retries, A_M_desk_counter, A_M_desk_counter_valid, A_M_fail, A_M_last_rx, A_M_backoff_until,
    A_OW_desk, A_OW_desk_off, A_OW_desk_p, A_OW_desk_body, A_OW_foreign, A_OW_acked, A_OW_acked_counter,
    A_OW_acked_retry, A_OW_acks, A_OW_ndata, A_Cfg_auto_wake, A_Cfg_backoff_ms,
    OFF_M, OFF_OW, OFF_g_cfg, OFF_g_now.

(* Two worlds built by the same stores, one with the model's names unfolded: equal store by store (never one
   conversion of the whole: the unifier may unfold upd and compute 65536-deep nats). *)
Ltac mrx_upd_eq :=
  lazymatch goal with
  | |- upd _ _ _ = upd _ _ _ =>
      apply (f_equal3 upd);
      [ mrx_upd_eq | first [ reflexivity | lia ] | first [ reflexivity | (f_equal; first [ reflexivity | lia ]) ] ]
  | |- _ => reflexivity
  end.

(* decide every [c =? k] in H by lia, then reduce the ifs *)
Ltac mrx_cmd_rw H c :=
  repeat match type of H with
  | context [c =? ?k] =>
      first [ replace (c =? k) with true in H by (symmetry; apply Z.eqb_eq; lia)
            | replace (c =? k) with false in H by (symmetry; apply Z.eqb_neq; lia) ]
  end;
  cbn [orb andb negb] in H; cbv iota in H.

(* addiw a0, st, -1; li a1, 1; bltu a1, a0: taken unless the state is ONLINE (2) or WAKING (1) *)
Lemma mrx_state12 : forall st, -2^31 <= st < 2^31 ->
  bv_ltu (Z_to_bv 64 1) (Z_to_bv 64 (bv_swrap 32 (bv_unsigned (Z_to_bv 64 st) + -1))) = negb ((st =? 2) || (st =? 1)).
Proof.
  intros st Hst. unfold bv_ltu. rewrite !unsigned_lit_wrap.
  change (1 mod 2^64) with 1.
  unfold bv_swrap, bv_wrap. change (bv_half_modulus 32) with (2^31). change (bv_modulus 32) with (2^32).
  assert (E : (st mod 2^64 + -1 + 2^31) mod 2^32 = (st - 1 + 2^31) mod 2^32).
  { destruct (Z_lt_le_dec st 0) as [N|P].
    - rewrite <- (Z.mod_unique st (2^64) (-1) (st + 2^64)) by lia.
      replace (st + 2^64 + -1 + 2^31) with ((st - 1 + 2^31) + 2^32 * 2^32) by lia.
      apply Z_mod_plus_full.
    - rewrite (Z.mod_small st) by lia. f_equal; lia. }
  rewrite E.
  destruct (Z.eq_dec st (-2^31)) as [M|M].
  - subst st. vm_compute. reflexivity.
  - rewrite (Z.mod_small (st - 1 + 2^31)) by lia.
    replace (st - 1 + 2^31 - 2^31) with (st - 1) by lia.
    destruct (Z_lt_le_dec (st - 1) 0) as [N|P].
    + rewrite <- (Z.mod_unique (st - 1) (2^64) (-1) (st - 1 + 2^64)) by lia.
      replace (st =? 2) with false by (symmetry; apply Z.eqb_neq; lia).
      replace (st =? 1) with false by (symmetry; apply Z.eqb_neq; lia).
      cbn [orb negb]. apply Z.ltb_lt. lia.
    + rewrite Z.mod_small by lia.
      destruct (Z.eqb_spec st 2); destruct (Z.eqb_spec st 1); cbn [orb negb];
        first [apply Z.ltb_lt; lia | apply Z.ltb_ge; lia].
Qed.

(* The postcondition of m_rx_contract, as a name. *)
Definition mrx_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (mI : word -> option byte) (lo : Z) (B' : list byte) (r : Z) : machine_state -> Prop :=
  fun ms' => exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : word -> option byte),
    ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 r) a1' a2' a3' a4' a5' a6' a7'
                  s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
             F (ret_pc ra) fc None m' (seg_rom rsegs) /\
    munch [(bv_unsigned sp - 144, bv_unsigned sp); (W_BASE_PLAIN, W_BASE_PLAIN + W_LEN)] mI m' /\
    wmono rsegs mI m' /\ mem_inv rsegs m' /\ stk rsegs m' lo (bv_unsigned sp) /\ wmem rsegs m' B'.

(* The epilogue at 0x1546c (ld ra, s0-s11; addi sp, sp, 128; ret), a0 = r. The frame's low 24 bytes are free. *)
Lemma mrx_epi : forall (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (mI m : word -> option byte) (lo : Z) (B' : list byte) (r : Z) (X : list byte)
    (ra' t0 t1 t2 s0' s1' a1 a2 a3 a4 a5 a6 a7 s2' s3' s4' s5' s6' s7' s8' s9' s10' s11' t3 t4 t5 t6 : word),
  lo + 144 <= bv_unsigned sp ->
  munch [(bv_unsigned sp - 144, bv_unsigned sp); (W_BASE_PLAIN, W_BASE_PLAIN + W_LEN)] mI m ->
  wmono rsegs mI m -> mem_inv rsegs m ->
  stk rsegs m lo (bv_unsigned sp + -128) ->
  rw_cells rsegs m (bv_unsigned sp + -128)
    [CB 24 X; C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
  wmem rsegs m B' ->
  evt rsegs (mrx_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc mI lo B' r)
    (MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -128)) gp tp t0 t1 t2 s0' s1' (Z_to_bv 64 r) a1 a2 a3 a4 a5 a6 a7
             s2' s3' s4' s5' s6' s7' s8' s9' s10' s11' t3 t4 t5 t6)
        F (Z_to_bv 64 0x1546c) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc mI m lo B' r X
    ra' t0 t1 t2 s0' s1' a1 a2 a3 a4 a5 a6 a7 s2' s3' s4' s5' s6' s7' s8' s9' s10' s11' t3 t4 t5 t6
    LO MU WM0 MI ST FR WM.
  pose proof (bv_unsigned_in_range 64 sp) as Rsp. unfold bv_modulus in Rsp.
  pose proof ST as (Hlo & _ & _).
  do 13 step.
  release_frame FR ST (bv_unsigned sp).
  do 2 step.
  apply evt_done. unfold mrx_post. do 15 eexists. split; [reflexivity|].
  split; [exact MU|]. split; [exact WM0|]. split; [exact MI|]. split; [exact ST|]. exact WM.
Qed.

(* Close a goal at 0x1546c by mrx_epi from the hypotheses about the goal's memory (found by shape, so the names
   the call tactics give them do not matter). *)
Ltac mrx_epi_close :=
  lazymatch goal with
  | |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    lazymatch goal with
    | LO : _ + 144 <= bv_unsigned ?sp, MU : munch _ _ mm, WMo : wmono rsegs _ mm, MI : mem_inv rsegs mm,
      ST : stk rsegs mm _ _, FR : rw_cells rsegs mm (bv_unsigned ?sp + -128) _,
      WM : rw_cells rsegs mm W_BASE_PLAIN _ |- _ =>
        eapply mrx_epi; [exact LO | exact MU | exact WMo | exact MI | exact ST | exact FR | exact WM]
    end
  end.

(* ---- small facts the continuations share ---- *)
Lemma mrx_sp16 : forall (sp : word), bv_unsigned sp mod 16 = 0 -> (bv_unsigned sp + -128) mod 16 = 0.
Proof. intros sp H. rewrite Zplus_mod, H. reflexivity. Qed.

(* The frame's three low 8-byte slots (0, 8, 16 (sp)) as one 24-byte cell. *)
Lemma mrx_fr_merge : forall m A X (w1 w2 : word) rest,
  rw_cells rsegs m A (CB 8 X :: C8 w1 :: C8 w2 :: rest) -> rw_cells rsegs m A (CB 24 (X ++ le8 w1 ++ le8 w2) :: rest).
Proof.
  intros m A X w1 w2 rest H.
  pose proof (rw_cells_merge rsegs m A [] [CB 8 X; C8 w1; C8 w2] rest H) as H'. cbn [app] in H'.
  cbn [cells_size cells_bytes csize cbytes Nat.add] in H'. rewrite app_nil_r in H'. exact H'.
Qed.

Lemma mrx_c8_cb : forall m A (w : word) rest, rw_cells rsegs m A (C8 w :: rest) -> rw_cells rsegs m A (CB 8 (le8 w) :: rest).
Proof.
  intros m A w rest [[Hwf Hb] Hw]. split; [split|].
  - cbn [cells_wf cell_wf] in *. split; [apply length_le8 | exact (proj2 Hwf)].
  - exact Hb.
  - exact Hw.
Qed.

(* The mem_inv / frame hypotheses by shape. *)
Ltac mrx_mi := lazymatch goal with H : mem_inv rsegs ?m |- mem_inv rsegs ?m => exact H end.
Ltac mrx_fr_merge_tac :=
  lazymatch goal with
  | FR : rw_cells _ _ _ (CB 8 _ :: C8 _ :: C8 _ :: _) |- _ => apply mrx_fr_merge in FR
  | FR : rw_cells _ _ _ (C8 _ :: C8 _ :: C8 _ :: C8 _ :: _) |- _ => apply mrx_c8_cb in FR; apply mrx_fr_merge in FR
  end.

(* A premise about the current memory, by its shape (never eassumption: unifying a frame cell list with the world's
   [CB (Z.to_nat W_LEN) _] computes a 65616-deep nat). *)
Ltac mrx_hyp :=
  lazymatch goal with
  | |- rw_cells rsegs ?m W_BASE_PLAIN _ => lazymatch goal with H : rw_cells rsegs m W_BASE_PLAIN _ |- _ => exact H end
  | |- rw_cells rsegs ?m (bv_unsigned ?sp + -128) _ =>
      lazymatch goal with H : rw_cells rsegs m (bv_unsigned sp + -128) _ |- _ => exact H end
  | |- stk rsegs ?m _ _ => lazymatch goal with H : stk rsegs m _ _ |- _ => exact H end
  | |- munch _ _ ?m => lazymatch goal with H : munch _ _ m |- _ => exact H end
  | |- wmono rsegs _ ?m => lazymatch goal with H : wmono rsegs _ m |- _ => exact H end
  | |- mem_inv rsegs ?m => lazymatch goal with H : mem_inv rsegs m |- _ => exact H end
  | |- bytes_at rsegs ?m (tf_addr ?fr) _ => lazymatch goal with H : bytes_at rsegs m (tf_addr fr) _ |- _ => exact H end
  end.

(* A callee that writes one cell [X, X + n) (memcpy) keeps the stack window a stack, wherever it lies. *)
Lemma mrx_stk_fill : forall m m' lo hi X n src,
  stk rsegs m lo hi -> munch [(X, X + n)] m m' -> wmono rsegs m m' ->
  rw_cells rsegs m' X [CB (Z.to_nat n) src] -> 0 <= n -> stk rsegs m' lo hi.
Proof.
  intros m m' lo hi X n src (H1 & H2 & H) MU WM [[Dwf Db] _] Hn.
  cbn [cells_wf cell_wf] in Dwf. destruct Dwf as [LS _]. cbn [cells_bytes cbytes] in Db. rewrite app_nil_r in Db.
  destruct Db as (DX & DL & Dbi).
  split; [lia|]. split; [lia|]. intros a Ha.
  destruct (H a Ha) as [Hw (b & Hb)]. split; [apply WM; exact Hw|].
  destruct (Z_le_dec X a) as [L1|L1]; [destruct (Z_lt_dec a (X + n)) as [L2|L2]|].
  - rewrite LS in DL.
    replace a with (X + Z.of_nat (Z.to_nat (a - X))) by lia.
    rewrite Dbi by lia. destruct (nth_error src (Z.to_nat (a - X))) eqn:E; [eexists; reflexivity|].
    apply nth_error_None in E. lia.
  - exists b. unfold mrd in *. rewrite MU; [exact Hb|]. cbn [outside]. rewrite wa_unsigned by lia. split; [lia | exact I].
  - exists b. unfold mrd in *. rewrite MU; [exact Hb|]. cbn [outside]. rewrite wa_unsigned by lia. split; [lia | exact I].
Qed.

(* 0x155f0-0x155f8: addi a0, s5, -226; li a1, -2; bltu a0, a1: taken unless cmd is e0 or e1 *)
Lemma mrx_cmd_ann : forall c, 0 <= c < 256 ->
  bv_ltu (Z_to_bv 64 (c + -226)) (Z_to_bv 64 (-2)) = negb ((c =? 224) || (c =? 225)).
Proof.
  intros c Hc. unfold bv_ltu. rewrite !unsigned_lit_wrap.
  change ((-2) mod 2^64) with (2^64 - 2).
  destruct (Z_lt_le_dec c 226) as [L|L].
  - rewrite <- (Z.mod_unique (c + -226) (2^64) (-1) (c + -226 + 2^64)) by lia.
    destruct (Z.eqb_spec c 224); destruct (Z.eqb_spec c 225); cbn [orb negb];
      first [apply Z.ltb_lt; lia | apply Z.ltb_ge; lia].
  - rewrite Z.mod_small by lia.
    replace (c =? 224) with false by (symmetry; apply Z.eqb_neq; lia).
    replace (c =? 225) with false by (symmetry; apply Z.eqb_neq; lia).
    cbn [orb negb]. apply Z.ltb_lt. lia.
Qed.

(* 0x157e8: jal m_tick; li a0, 1; j 0x1546c. *)
Lemma mrx_tick : m_tick_contract ->
  forall (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (mI m : word -> option byte) (lo : Z) (B3 B4 : list byte) (X : list byte)
    (x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word),
  bv_unsigned sp mod 16 = 0 -> lo + 144 <= bv_unsigned sp -> W_BASE_PLAIN + W_LEN <= bv_unsigned sp - 144 ->
  munch [(bv_unsigned sp - 144, bv_unsigned sp); (W_BASE_PLAIN, W_BASE_PLAIN + W_LEN)] mI m ->
  wmono rsegs mI m -> mem_inv rsegs m ->
  stk rsegs m lo (bv_unsigned sp + -128) ->
  rw_cells rsegs m (bv_unsigned sp + -128)
    [CB 24 X; C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
  wmem rsegs m B3 ->
  m_tick_m B3 = Some (B4, tt) ->
  evt rsegs (mrx_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc mI lo B4 1)
    (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -128)) gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17
             x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
        F (Z_to_bv 64 0x157e8) fc None m (seg_rom rsegs)).
Proof.
  intros TC ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc mI m lo B3 B4 X
    x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31
    HS16 LO WOF MU WM0 MI ST FR WM HT.
  unfold m_tick_contract, m_tick_ENTRY, m_tick_FRAME in TC.
  pose proof (bv_unsigned_in_range 64 sp) as Rsp. unfold bv_modulus in Rsp.
  pose proof ST as (Hlo & _ & _).
  assert (Hsp : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -128)) = bv_unsigned sp + -128) by (apply unsigned_lit; lia).
  wk_facts.
  step.
  eapply evt_cut.
  { eapply TC with (lo := lo) (B := B3) (B' := B4);
      [rewrite Hsp; apply mrx_sp16; exact HS16 | rewrite Hsp; exact ST | rewrite Hsp; lia
      | unfold w_off_stack; rewrite Hsp; lia | exact MI | exact WM | exact HT]. }
  intros ms' PO. rewrite Hsp in PO. revert ms' PO.
  wk_post_call rsegs m.
  step. step.
  eapply mrx_epi; eassumption.
Qed.

(* 0x157e4: jal m_maybe_online, then m_tick at 0x157e8. *)
Lemma mrx_mo : m_maybe_online_contract -> m_tick_contract ->
  forall (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (mI m : word -> option byte) (lo : Z) (B2 B3 B4 : list byte) (X : list byte)
    (x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word),
  bv_unsigned sp mod 16 = 0 -> lo + 144 <= bv_unsigned sp -> W_BASE_PLAIN + W_LEN <= bv_unsigned sp - 144 ->
  munch [(bv_unsigned sp - 144, bv_unsigned sp); (W_BASE_PLAIN, W_BASE_PLAIN + W_LEN)] mI m ->
  wmono rsegs mI m -> mem_inv rsegs m ->
  stk rsegs m lo (bv_unsigned sp + -128) ->
  rw_cells rsegs m (bv_unsigned sp + -128)
    [CB 24 X; C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
  wmem rsegs m B2 ->
  m_maybe_online_m B2 = Some (B3, tt) ->
  m_tick_m B3 = Some (B4, tt) ->
  evt rsegs (mrx_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc mI lo B4 1)
    (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -128)) gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17
             x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
        F (Z_to_bv 64 0x157e4) fc None m (seg_rom rsegs)).
Proof.
  intros MOC TC ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc mI m lo B2 B3 B4 X
    x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31
    HS16 LO WOF MU WM0 MI ST FR WM HM HT.
  unfold m_maybe_online_contract, m_maybe_online_ENTRY, m_maybe_online_FRAME in MOC.
  pose proof (bv_unsigned_in_range 64 sp) as Rsp. unfold bv_modulus in Rsp.
  pose proof ST as (Hlo & _ & _).
  assert (Hsp : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -128)) = bv_unsigned sp + -128) by (apply unsigned_lit; lia).
  wk_facts.
  step.
  eapply evt_cut.
  { eapply MOC with (lo := lo) (B := B2) (B' := B3);
      [rewrite Hsp; apply mrx_sp16; exact HS16 | rewrite Hsp; exact ST | rewrite Hsp; lia
      | unfold w_off_stack; rewrite Hsp; lia | exact MI | exact WM | exact HM]. }
  intros ms' PO. rewrite Hsp in PO. revert ms' PO.
  wk_post_call rsegs m.
  eapply mrx_tick; eassumption.
Qed.

(* 0x156c4: jal m_lost (a0 = why); j 0x157e8 (m_tick). *)
Lemma mrx_lost : m_lost_contract -> m_tick_contract ->
  forall (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (mI m : word -> option byte) (lo : Z) (B2 B3 B4 : list byte) (X : list byte) (why : Z)
    (x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word),
  bv_unsigned sp mod 16 = 0 -> lo + 144 <= bv_unsigned sp -> W_BASE_PLAIN + W_LEN <= bv_unsigned sp - 144 ->
  munch [(bv_unsigned sp - 144, bv_unsigned sp); (W_BASE_PLAIN, W_BASE_PLAIN + W_LEN)] mI m ->
  wmono rsegs mI m -> mem_inv rsegs m ->
  stk rsegs m lo (bv_unsigned sp + -128) ->
  rw_cells rsegs m (bv_unsigned sp + -128)
    [CB 24 X; C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
  wmem rsegs m B2 ->
  x10 = Z_to_bv 64 why -> -2^31 <= why < 2^31 ->
  m_lost_m B2 why = Some (B3, tt) ->
  m_tick_m B3 = Some (B4, tt) ->
  evt rsegs (mrx_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc mI lo B4 1)
    (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -128)) gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17
             x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
        F (Z_to_bv 64 0x156c4) fc None m (seg_rom rsegs)).
Proof.
  intros LC TC ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc mI m lo B2 B3 B4 X why
    x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31
    HS16 LO WOF MU WM0 MI ST FR WM -> Hwhy HL HT.
  unfold m_lost_contract, m_lost_ENTRY, m_lost_FRAME in LC.
  pose proof (bv_unsigned_in_range 64 sp) as Rsp. unfold bv_modulus in Rsp.
  pose proof ST as (Hlo & _ & _).
  assert (Hsp : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -128)) = bv_unsigned sp + -128) by (apply unsigned_lit; lia).
  wk_facts.
  step.
  eapply evt_cut.
  { eapply LC with (lo := lo) (B := B2) (B' := B3) (why := why);
      [reflexivity | exact Hwhy | rewrite Hsp; apply mrx_sp16; exact HS16 | rewrite Hsp; exact ST | rewrite Hsp; lia
      | unfold w_off_stack; rewrite Hsp; lia | exact MI | exact WM | exact HL]. }
  intros ms' PO. rewrite Hsp in PO. revert ms' PO.
  wk_post_call rsegs m.
  step.
  eapply mrx_tick; eassumption.
Qed.
