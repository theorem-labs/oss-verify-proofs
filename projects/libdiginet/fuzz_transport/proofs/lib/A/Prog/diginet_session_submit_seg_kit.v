(* diginet_session_submit_seg_kit: the image-free pieces of the walk of diginet_session_submit on
   fuzz_transport.asan (lib/A/Prog/diginet_session_submit_cg.v states the contract at 0x89ef0).

   Three groups, none of them about a machine state:
   - the model: lib/TModel/TSess0.v diginet_session_submit_m with its queue tail named (ssk_k), the shape of one
     turn of its search (ssk_find_S), and the world each arm leaves (ssk_arg / ssk_refused / ssk_app / ssk_coal);
   - the tests: each branch the symbolic run cannot decide, read at a valuation E, equals the model's test
     (ssk_br_len, ssk_br_kind08, ssk_br_kind9, ssk_br_q512, ssk_br_qzero, ssk_br_key);
   - two list facts the stores need (ssk_put_refused / ssk_put_coal: a store of the loaded value + 1 is the
     model's set_S_stats_*; ssk_app_world: the queued store and the memcpy of the entry in either order).

   The function returns 0, -1 (E_ARG), -5 (E_SPACE) or -10 (E_REFUSED); its four writes into g_s are
   g_s.stats.refused, g_s.queued, one entry g_s.queue[j] and g_s.stats.coalesced. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YK11 YP0m YP0e YP09 YP0l YP06 YP03.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Import MState. 
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Mem.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require Import DgnSpec DgnLib.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require Import TWorld TWorldLemmas TSess0.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope Z_scope.

Module LMem := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib.Mem.

(* ------------------------------------------------------------------ *)
(* The model                                                           *)
(* ------------------------------------------------------------------ *)

(* diginet_session_submit_m's queue tail (:336-348), taking the result of the search. *)
Definition ssk_k (B C : list byte) (o : option (option Z)) : option (list byte * Z) :=
  match o with
  | None => None
  | Some (Some i) =>
      let B1 := upd B (A_S_queue_bytes i) C in
      Some (set_S_stats_coalesced B1 (u64 (S_stats_coalesced B1 + 1)), DIGINET_OK)
  | Some None =>
      let q := S_queued B in
      if q =? DIGINET_QUEUE_MAX then Some (B, DIGINET_E_SPACE)
      else if S_queue_N <=? q then None
      else Some (set_S_queued (upd B (A_S_queue_bytes q) C) (u32 (q + 1)), DIGINET_OK)
  end.

Lemma ssk_m_eq : forall B C, diginet_session_submit_m B C =
  if (cmd_len_of C =? 0) || (DIGINET_CMD_MAX_LEN <? cmd_len_of C) then Some (B, DIGINET_E_ARG)
  else if negb (body_check (firstn (Z.to_nat (cmd_len_of C)) C) =? DIGINET_OK) then
    Some (set_S_stats_refused B (u64 (S_stats_refused B + 1)), DIGINET_E_REFUSED)
  else ssk_k B C (if coalescable_m (cmd_key_of C) =? 0 then Some None
                  else submit_find_m B (cmd_key_of C) 0 (Z.to_nat (S_queued B))).
Proof. reflexivity. Qed.

Lemma ssk_find_S : forall B key i f, submit_find_m B key i (S f) =
  if 512 <=? i then None else if S_queue_key B i =? key then Some (Some i) else submit_find_m B key (i + 1) f.
Proof. reflexivity. Qed.

Lemma ssk_some_inv : forall (x y : list byte) (r s : Z), Some (x, r) = Some (y, s) -> y = x /\ s = r.
Proof. intros x y r s H. injection H as H1 H2. split; [symmetry; exact H1 | symmetry; exact H2]. Qed.

(* The len test fails (:330-331): the world is unchanged and the result is -1. *)
Lemma ssk_arg : forall B C B' r, (cmd_len_of C =? 0) || (DIGINET_CMD_MAX_LEN <? cmd_len_of C) = true ->
  diginet_session_submit_m B C = Some (B', r) -> B' = B /\ r = DIGINET_E_ARG.
Proof.
  intros B C B' r Ht Hm. rewrite ssk_m_eq, Ht in Hm. exact (ssk_some_inv _ _ _ _ Hm).
Qed.

(* diginet_body_check answers a value other than 0 (:332-334): the refused counter is bumped, the result -10. *)
Lemma ssk_refused : forall B C B' r, (cmd_len_of C =? 0) || (DIGINET_CMD_MAX_LEN <? cmd_len_of C) = false ->
  body_check (firstn (Z.to_nat (cmd_len_of C)) C) <> DIGINET_OK ->
  diginet_session_submit_m B C = Some (B', r) ->
  B' = set_S_stats_refused B (u64 (S_stats_refused B + 1)) /\ r = DIGINET_E_REFUSED.
Proof.
  intros B C B' r Ht Hb Hm. rewrite ssk_m_eq, Ht in Hm.
  rewrite (proj2 (negb_true_iff _) (proj2 (Z.eqb_neq _ _) Hb)) in Hm. cbv iota in Hm.
  exact (ssk_some_inv _ _ _ _ Hm).
Qed.

(* The tail after a search that found nothing (:345-348). *)
Lemma ssk_k_none : forall B C B' r, ssk_k B C (Some None) = Some (B', r) ->
  (S_queued B = 512 /\ B' = B /\ r = DIGINET_E_SPACE) \/
  (S_queued B < 512 /\ B' = set_S_queued (upd B (A_S_queue_bytes (S_queued B)) C) (u32 (S_queued B + 1)) /\
   r = DIGINET_OK).
Proof.
  intros B C B' r H. unfold ssk_k in H. cbv zeta in H. unfold DIGINET_QUEUE_MAX, S_queue_N in H. revert H.
  destruct (Z.eqb_spec (S_queued B) 512) as [E|E]; intros H.
  - injection H as <- <-. left. split; [exact E | split; reflexivity].
  - revert H. destruct (Z.leb_spec 512 (S_queued B)) as [L|L]; intros H; [discriminate H|].
    injection H as <- <-. right. split; [lia | split; reflexivity].
Qed.

(* The tail after a search that found the entry i (:339-341). *)
Lemma ssk_k_some : forall B C i B' r, ssk_k B C (Some (Some i)) = Some (B', r) ->
  B' = set_S_stats_coalesced (upd B (A_S_queue_bytes i) C) (u64 (S_stats_coalesced (upd B (A_S_queue_bytes i) C) + 1))
  /\ r = DIGINET_OK.
Proof. intros B C i B' r H. unfold ssk_k in H. cbv zeta in H. injection H as <- <-. split; reflexivity. Qed.

(* The model's world is the tail's when the len test passes and diginet_body_check answers 0. *)
Lemma ssk_ok_tail : forall B C B' r, (cmd_len_of C =? 0) || (DIGINET_CMD_MAX_LEN <? cmd_len_of C) = false ->
  body_check (firstn (Z.to_nat (cmd_len_of C)) C) = DIGINET_OK ->
  diginet_session_submit_m B C = Some (B', r) ->
  ssk_k B C (if coalescable_m (cmd_key_of C) =? 0 then Some None
             else submit_find_m B (cmd_key_of C) 0 (Z.to_nat (S_queued B))) = Some (B', r).
Proof.
  intros B C B' r Ht Hb Hm. rewrite ssk_m_eq, Ht in Hm. rewrite Hb in Hm. cbn [Z.eqb negb] in Hm. exact Hm.
Qed.

(* ------------------------------------------------------------------ *)
(* The stores into g_s                                                 *)
(* ------------------------------------------------------------------ *)

(* The 8-byte store of the loaded refused counter + 1 is the model's set_S_stats_refused. *)
Lemma ssk_put_refused : forall B,
  upd B A_S_stats_refused (put 8 (u_at B A_S_stats_refused 8 + 1)) =
  set_S_stats_refused B (u64 (S_stats_refused B + 1)).
Proof.
  intros B. unfold set_S_stats_refused, S_stats_refused, u64. rewrite put_mod64 by lia. reflexivity.
Qed.

(* The 8-byte store of the loaded coalesced counter + 1 is the model's set_S_stats_coalesced. *)
Lemma ssk_put_coal : forall B,
  upd B A_S_stats_coalesced (put 8 (u_at B A_S_stats_coalesced 8 + 1)) =
  set_S_stats_coalesced B (u64 (S_stats_coalesced B + 1)).
Proof.
  intros B. unfold set_S_stats_coalesced, S_stats_coalesced, u64. rewrite put_mod64 by lia. reflexivity.
Qed.

(* The append's two writes (the 4-byte store of queued + 1 at :347, then the memcpy of the entry at :348) in the
   order the code makes them, as the model's one world. *)
Lemma ssk_app_world : forall B C q, length B = Z.to_nat W_LEN -> length C = 32%nat -> 0 <= q < 512 ->
  upd (upd B A_S_queued (put 4 (q + 1))) (A_S_queue_bytes q) C =
  set_S_queued (upd B (A_S_queue_bytes q) C) (u32 (q + 1)).
Proof.
  intros B C q LB LC Hq. unfold set_S_queued, u32.
  replace (put 4 ((q + 1) mod 2 ^ 32)) with (put 4 (q + 1)) by (unfold put; symmetry; apply LMem.Z_to_le_bytes_mod; lia).
  apply upd_upd_comm; rewrite ?length_put, ?LC, ?LB;
    unfold A_S_queue_bytes, A_S_queued, OFF_g_s, W_LEN; lia.
Qed.

(* The coalescing write (the memcpy of the entry at :339) leaves the coalesced counter where it was. *)
Lemma ssk_coal_read : forall B C i, length B = Z.to_nat W_LEN -> length C = 32%nat -> 0 <= i < 512 ->
  u_at (upd B (A_S_queue_bytes i) C) A_S_stats_coalesced 8 = S_stats_coalesced B.
Proof.
  intros B C i LB LC Hi. unfold S_stats_coalesced. apply u_at_upd_out;
    rewrite ?LC, ?LB; unfold A_S_queue_bytes, A_S_stats_coalesced, OFF_g_s, W_LEN; lia.
Qed.

(* ------------------------------------------------------------------ *)
(* The branch tests at a valuation                                     *)
(* ------------------------------------------------------------------ *)

Lemma ssk_u1 : forall C k, 0 <= u_at C k 1 < 256.
Proof. intros C k. pose proof (u_at_range C k 1) as R. cbn in R. lia. Qed.
Lemma ssk_u4 : forall C k, 0 <= u_at C k 4 < 2 ^ 32.
Proof. intros C k. pose proof (u_at_range C k 4) as R. cbn in R. exact R. Qed.

(* `addi a2,a1,-25; bltu a2,-24` (0x89f40-0x89f48) is the model's len test (:330-331). *)
Lemma ssk_br_len : forall E n (len : Z), ew E n = Z_to_bv 64 len -> 0 <= len < 256 ->
  branch_taken BC_LTU (sv_denot E (SOff n (-25))) (sv_denot E (SLit (-24))) =
  ((len =? 0) || (DIGINET_CMD_MAX_LEN <? len)).
Proof.
  intros E n len Hn Hlen. cbn [branch_taken sv_denot]. unfold bv_ltu, DIGINET_CMD_MAX_LEN. rewrite Hn.
  rewrite !unsigned_lit_wrap.
  destruct (Z.eqb_spec len 0); destruct (Z.ltb_spec 24 len); cbn [orb];
    first [apply Z.ltb_lt | apply Z.ltb_ge]; Z.div_mod_to_equations; lia.
Qed.

(* The kind byte of a key (DIGINET_KEY_KIND, diginet_session.c:324). *)
Definition ssk_kind (key : Z) : Z := u8 (Z.shiftr key 16).

Lemma ssk_kind_range : forall key, 0 <= ssk_kind key < 256.
Proof. intros key. unfold ssk_kind, u8. apply Z.mod_pos_bound. lia. Qed.

(* coalescable (:322-326) is false exactly at the kinds 0, 8 and 9. *)
Lemma ssk_coal_kinds : forall key,
  (coalescable_m key =? 0) = ((ssk_kind key =? 0) || (ssk_kind key =? 8) || (ssk_kind key =? 9)).
Proof.
  intros key. unfold coalescable_m, ssk_kind, int_of_bool, DIGINET_KEY_INPUT, DIGINET_KEY_KEEPALIVE. cbv zeta.
  set (k := u8 (Z.shiftr key 16)).
  destruct (Z.eqb_spec k 0) as [->|H0]; [reflexivity|].
  destruct (Z.eqb_spec k 8) as [->|H8]; [reflexivity|].
  destruct (Z.eqb_spec k 9) as [->|H9]; [reflexivity|].
  cbn [negb andb]. reflexivity.
Qed.

(* branch_taken BC_EQ at a valuation reads two atoms' unsigned values. *)
Lemma ssk_br_eq_U : forall E a b, branch_taken BC_EQ (sv_denot E a) (sv_denot E b) = (U E a =? U E b).
Proof. intros E a b. cbn [branch_taken]. unfold bv_eqb, U. reflexivity. Qed.

(* 256-value enumeration (as the plain walk's sub_z256). *)
Lemma ssk_z256 : forall (P : Z -> bool), forallb P (map Z.of_nat (seq 0 256)) = true ->
  forall k, 0 <= k < 256 -> P k = true.
Proof.
  intros P H k Hk. rewrite forallb_forall in H. apply H. apply in_map_iff. exists (Z.to_nat k).
  split; [lia | apply in_seq; lia].
Qed.

(* Z.land distributes a single-bit mask through a low mask. *)
Lemma ssk_and_lor_255 : forall b, 0 <= b -> Z.land (Z.lor b 8) 255 = Z.lor (b mod 256) 8.
Proof.
  intros b Hb. apply Z.bits_inj'. intros i Hi.
  rewrite Z.land_spec, !Z.lor_spec.
  assert (B255 : Z.testbit 255 i = (i <? 8)).
  { destruct (Z.ltb_spec i 8); change 255 with (Z.ones 8);
    [apply Z.ones_spec_low | apply Z.ones_spec_high]; lia. }
  assert (Bmod : Z.testbit (b mod 256) i = (if (i <? 8)%Z then Z.testbit b i else false)).
  { change 256 with (2 ^ 8). destruct (Z.ltb_spec i 8);
    [apply Z.mod_pow2_bits_low | apply Z.mod_pow2_bits_high]; lia. }
  rewrite B255, Bmod. destruct (Z.ltb_spec i 8) as [Hl|Hl]; cbn [andb orb]; [apply andb_true_r|].
  assert (T8 : Z.testbit 8 i = false).
  { apply (proj2 (Z.testbit_false 8 i ltac:(lia))). rewrite Z.div_small; [reflexivity|].
    split; [lia | apply (Z.lt_le_trans _ (2 ^ 8)); [lia | apply Z.pow_le_mono_r; lia]]. }
  rewrite T8, andb_false_r. reflexivity.
Qed.

(* Z.lor of two values below 2^n is below 2^n. *)
Lemma ssk_lor_lt : forall a b n, 0 <= a < 2 ^ n -> 0 <= b < 2 ^ n -> 0 <= Z.lor a b < 2 ^ n.
Proof.
  intros a b n Ha Hb.
  assert (Hn : 0 <= n) by (destruct (Z.le_gt_cases 0 n) as [|Hc]; [lia|]; rewrite Z.pow_neg_r in Ha by lia; lia).
  assert (Hnn : 0 <= Z.lor a b) by (apply Z.lor_nonneg; lia).
  assert (Hsh : (Z.lor a b) / 2 ^ n = 0).
  { rewrite <- Z.shiftr_div_pow2 by lia. rewrite Z.shiftr_lor, !Z.shiftr_div_pow2 by lia.
    rewrite (Z.div_small a (2 ^ n)) by lia. rewrite (Z.div_small b (2 ^ n)) by lia. reflexivity. }
  apply Z.div_small_iff in Hsh; [lia | lia].
Qed.

(* An and-255 value is a byte. *)
Lemma ssk_land255 : forall a, 0 <= a -> 0 <= Z.land a 255 < 256.
Proof.
  intros a Ha. change 255 with (Z.ones 8). rewrite Z.land_ones by lia. change (2 ^ 8) with 256.
  apply Z.mod_pos_bound; lia.
Qed.

(* `and a0, (b|8), 255 == 8` iff the kind b mod 256 is 0 or 8. *)
Lemma ssk_lor8 : forall k, 0 <= k < 256 -> (Z.lor k 8 =? 8) = ((k =? 0) || (k =? 8)).
Proof.
  intros k Hk. apply Bool.eqb_prop.
  exact (ssk_z256 (fun j => Bool.eqb (Z.lor j 8 =? 8) ((j =? 0) || (j =? 8)))
    ltac:(vm_compute; reflexivity) k Hk).
Qed.

(* Z.land with a mask shifted left by 16 (the plain walk's sub_land_shl16). *)
Lemma ssk_land_shl16 : forall key M, 0 <= M ->
  Z.land key (Z.shiftl M 16) = Z.shiftl (Z.land (Z.shiftr key 16) M) 16.
Proof.
  intros key M HM. apply Z.bits_inj'. intros n Hn. rewrite Z.land_spec.
  destruct (Z.lt_ge_cases n 16) as [L|L].
  - rewrite !Z.shiftl_spec_low by lia. apply andb_false_r.
  - rewrite !Z.shiftl_spec_high by lia. rewrite Z.land_spec, Z.shiftr_spec by lia.
    replace (n - 16 + 16) with n by lia. reflexivity.
Qed.

(* The reduction of the kind-0-or-8 test expression. *)
Lemma ssk_U_kind08 : forall E n key, ew E n = Z_to_bv 64 key -> 0 <= key < 2 ^ 32 ->
  U E (SAlu ALU_AND (SAlu ALU_OR (SAlu ALU_SRL (SOff n 0) (SLit 16)) (SLit 8)) (SLit 255)) =
  Z.lor (ssk_kind key) 8.
Proof.
  intros E n key Hn Hk. rewrite !U_SAlu. cbn [zalu_raw]. rewrite !U_SOff, !U_SLit, Hn.
  rewrite unsigned_lit_small by lia. rewrite Z.add_0_r. unfold zcanon, M64.
  rewrite (Z.mod_small 16 (2 ^ 64)) by lia. change (Z.land 16 63) with 16.
  rewrite (Z.mod_small key (2 ^ 64)) by lia. rewrite Z.shiftr_div_pow2 by lia.
  assert (Hd : 0 <= key / 2 ^ 16 < 2 ^ 16) by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
  rewrite (Z.mod_small (key / 2 ^ 16) (2 ^ 64)) by lia.
  rewrite (Z.mod_small 8 (2 ^ 64)) by lia.
  assert (Hlo : 0 <= Z.lor (key / 2 ^ 16) 8 < 2 ^ 17)
    by (apply ssk_lor_lt; lia).
  rewrite (Z.mod_small (Z.lor (key / 2 ^ 16) 8) (2 ^ 64)) by lia.
  rewrite (Z.mod_small 255 (2 ^ 64)) by lia.
  assert (Hr : 0 <= Z.land (Z.lor (key / 2 ^ 16) 8) 255 < 256)
    by (apply ssk_land255; lia).
  rewrite (Z.mod_small (Z.land (Z.lor (key / 2 ^ 16) 8) 255) (2 ^ 64)) by lia.
  rewrite (ssk_and_lor_255 (key / 2 ^ 16) ltac:(lia)).
  unfold ssk_kind, u8. rewrite Z.shiftr_div_pow2 by lia. reflexivity.
Qed.

(* `srli a0,a4,16; ori a0,a0,8; andi a0,a0,255; bne a0,8` (0x89fa4-0x89fb8): the kind is 0 or 8. *)
Lemma ssk_br_kind08 : forall E n (key : Z), ew E n = Z_to_bv 64 key -> 0 <= key < 2 ^ 32 ->
  branch_taken BC_EQ
    (sv_denot E (SAlu ALU_AND (SAlu ALU_OR (SAlu ALU_SRL (SOff n 0) (SLit 16)) (SLit 8)) (SLit 255)))
    (sv_denot E (SLit 8)) = ((ssk_kind key =? 0) || (ssk_kind key =? 8)).
Proof.
  intros E n key Hn Hk. rewrite ssk_br_eq_U, (ssk_U_kind08 E n key Hn Hk), U_SLit.
  change (zcanon 8) with 8. apply ssk_lor8. apply ssk_kind_range.
Qed.

(* The reduction of the kind-9 test expression. *)
Lemma ssk_U_kind9 : forall E n key, ew E n = Z_to_bv 64 key -> 0 <= key < 2 ^ 32 ->
  U E (SAlu ALU_AND (SOff n 0) (SLit 16711680)) = Z.shiftl (ssk_kind key) 16.
Proof.
  intros E n key Hn Hk. rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SOff, U_SLit, Hn.
  rewrite unsigned_lit_small by lia. rewrite Z.add_0_r. unfold zcanon, M64.
  rewrite (Z.mod_small key (2 ^ 64)) by lia.
  change 16711680 with (Z.shiftl 255 16).
  rewrite (Z.mod_small (Z.shiftl 255 16) (2 ^ 64)) by (rewrite Z.shiftl_mul_pow2 by lia; lia).
  rewrite (ssk_land_shl16 key 255 ltac:(lia)).
  assert (Hsr : 0 <= Z.shiftr key 16) by (rewrite Z.shiftr_div_pow2 by lia; apply Z.div_pos; lia).
  assert (Hla : 0 <= Z.land (Z.shiftr key 16) 255 < 256) by (apply ssk_land255; exact Hsr).
  assert (Hsh : 0 <= Z.shiftl (Z.land (Z.shiftr key 16) 255) 16 < 2 ^ 64).
  { rewrite Z.shiftl_mul_pow2 by lia.
    assert (E16 : (2:Z) ^ 16 = 65536) by reflexivity.
    assert (E64 : (2:Z) ^ 64 = 18446744073709551616) by reflexivity.
    rewrite E16, E64. lia. }
  rewrite (Z.mod_small _ (2 ^ 64)) by lia.
  unfold ssk_kind, u8. f_equal. change 255 with (Z.ones 8). rewrite Z.land_ones by lia.
  change (2 ^ 8) with 256. reflexivity.
Qed.

Lemma ssk_shl16_eqb : forall a, 0 <= a -> (Z.shiftl a 16 =? Z.shiftl 9 16) = (a =? 9).
Proof.
  intros a Ha. rewrite !Z.shiftl_mul_pow2 by lia.
  destruct (Z.eqb_spec a 9) as [->|N]; [apply Z.eqb_refl | apply Z.eqb_neq; intros E; apply N; lia].
Qed.

(* `lui a0,0xff0; and a0,a4,a0; lui a1,0x90; beq a0,a1` (0x8a024-0x8a030): the kind is 9. *)
Lemma ssk_br_kind9 : forall E n (key : Z), ew E n = Z_to_bv 64 key -> 0 <= key < 2 ^ 32 ->
  branch_taken BC_EQ (sv_denot E (SAlu ALU_AND (SOff n 0) (SLit 16711680))) (sv_denot E (SLit 589824)) =
  (ssk_kind key =? 9).
Proof.
  intros E n key Hn Hk. rewrite ssk_br_eq_U, (ssk_U_kind9 E n key Hn Hk), U_SLit.
  change (zcanon 589824) with (Z.shiftl 9 16). apply ssk_shl16_eqb. apply ssk_kind_range.
Qed.

(* A value below 2^32 is below 2^64. *)
Lemma ssk_u64 : forall q, 0 <= q < 2 ^ 32 -> 0 <= q < 2 ^ 64.
Proof. intros q Hq. lia. Qed.

(* An equality branch of an atom against a literal, both in range. *)
Lemma ssk_br_eq_lit : forall E n (v c : Z), ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> 0 <= c < 2 ^ 64 ->
  branch_taken BC_EQ (sv_denot E (SOff n 0)) (sv_denot E (SLit c)) = (v =? c).
Proof.
  intros E n v c Hn Hv Hc. rewrite ssk_br_eq_U, U_SOff, U_SLit, Hn, Z.add_0_r.
  rewrite (unsigned_lit_small v Hv). unfold zcanon, M64.
  rewrite (Z.mod_small v (2 ^ 64) Hv), (Z.mod_small c (2 ^ 64) Hc). reflexivity.
Qed.

(* `lwu a0,0(s2); li a1,512; bne a0,a1` (0x89fc8-0x89fd0): the queue is full. *)
Lemma ssk_br_q512 : forall E n (q : Z), ew E n = Z_to_bv 64 q -> 0 <= q < 2 ^ 32 ->
  branch_taken BC_EQ (sv_denot E (SOff n 0)) (sv_denot E (SLit 512)) = (q =? 512).
Proof. intros E n q Hn Hq. exact (ssk_br_eq_lit E n q 512 Hn (ssk_u64 q Hq) ltac:(lia)). Qed.

(* `beq a3,zero` (0x8a044): no command queued. *)
Lemma ssk_br_qzero : forall E n (q : Z), ew E n = Z_to_bv 64 q -> 0 <= q < 2 ^ 32 ->
  branch_taken BC_EQ (sv_denot E (SOff n 0)) (sv_denot E (SLit 0)) = (q =? 0).
Proof. intros E n q Hn Hq. exact (ssk_br_eq_lit E n q 0 Hn (ssk_u64 q Hq) ltac:(lia)). Qed.

(* bv_eqb of two sign-extended 4-byte values is the model's unsigned compare (the plain walk's sub_eqb_s32). *)
Lemma ssk_eqb_s32 : forall x y, 0 <= x < 2 ^ 32 -> 0 <= y < 2 ^ 32 ->
  bv_eqb (Z_to_bv 64 (bv_swrap 32 x)) (Z_to_bv 64 (bv_swrap 32 y)) = (x =? y).
Proof.
  intros x y Hx Hy. unfold bv_eqb. rewrite !unsigned_lit_wrap.
  unfold bv_swrap, bv_wrap. change (bv_half_modulus 32) with (2 ^ 31). change (bv_modulus 32) with (2 ^ 32).
  destruct (Z.eqb_spec x y) as [->|N]; [apply Z.eqb_refl|].
  apply Z.eqb_neq. intros E. apply N. Z.div_mod_to_equations. lia.
Qed.

(* SExt true 32 of an atom holding a value below 2^32 is its sign-extension. *)
Lemma ssk_sext : forall E n (key : Z), ew E n = Z_to_bv 64 key -> 0 <= key < 2 ^ 32 ->
  sv_denot E (SExt true 32 (SOff n 0)) = Z_to_bv 64 (bv_swrap 32 key).
Proof.
  intros E n key Hn Hk. cbn [sv_denot]. rewrite LMem.sext_small, LMem.signed_of_extract by lia.
  rewrite Hn, Z.add_0_r, Z_to_bv_bv_unsigned. f_equal. f_equal. apply unsigned_lit_small; lia.
Qed.

(* `lw a5,28(a0); beq a5,a4` (0x8a064-0x8a068): the entry's key a5 (sign-extended) is the command's key a4
   (held sign-extended, from the addiw at 0x8a050). The compare is the model's on the unsigned keys. *)
Lemma ssk_br_key : forall E n m (ki key : Z),
  ew E n = Z_to_bv 64 ki -> ew E m = Z_to_bv 64 (bv_swrap 32 key) ->
  0 <= ki < 2 ^ 32 -> 0 <= key < 2 ^ 32 ->
  branch_taken BC_EQ (sv_denot E (SExt true 32 (SOff n 0))) (sv_denot E (SOff m 0)) = (ki =? key).
Proof.
  intros E n m ki key Hn Hm Hki Hkey. cbn [branch_taken]. rewrite (ssk_sext E n ki Hn Hki).
  replace (sv_denot E (SOff m 0)) with (Z_to_bv 64 (bv_swrap 32 key))
    by (cbn [sv_denot]; rewrite Hm, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
  apply ssk_eqb_s32; assumption.
Qed.

(* `addiw a4,a4,0` (0x8a050): the key register is sign-extended before the loop. *)
Lemma ssk_sextw : forall E n (key : Z), ew E n = Z_to_bv 64 key -> 0 <= key < 2 ^ 32 ->
  sv_denot E (SAluw ALU_ADD (SOff n 0) (SLit 0)) = Z_to_bv 64 (bv_swrap 32 key).
Proof.
  intros E n key Hn Hk. rewrite <- (ssk_sext E n key Hn Hk). cbn [sv_denot].
  unfold alu32, low32. cbn [alu zalu_raw]. f_equal. apply bv_eq. rewrite bv_add_unsigned.
  replace (bv_unsigned (bv_extract 0 32 (sv_denot E (SLit 0)))) with 0.
  2:{ cbn [sv_denot]. rewrite bv_extract_unsigned, Z.shiftr_0_r, unsigned_lit_small by lia.
      change (2 ^ Z.of_N 32) with (2 ^ 32). reflexivity. }
  rewrite Z.add_0_r. apply bv_wrap_small. apply bv_unsigned_in_range.
Qed.
