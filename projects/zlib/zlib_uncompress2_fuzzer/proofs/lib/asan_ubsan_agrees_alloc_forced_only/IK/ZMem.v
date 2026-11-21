(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)

From Stdlib Require Strings.String Strings.Ascii.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only Require Import PropExec CatExec CatSim SeqExec StreamExec StoreOk ShapeAlg.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.IK Require Import ZStep.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
Section FXG. Context {fx : OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.PropExec.FPState}.

Definition mem := word -> option byte.

Definition byte_of_ascii (c : Ascii.ascii) : byte := Z_to_bv 8 (Z.of_N (Ascii.N_of_ascii c)).
Fixpoint str (s : String.string) : list byte :=
  match s with
  | String.EmptyString => []
  | String.String c r => byte_of_ascii c :: str r
  end.


Definition mem_is (segs : list Segment) (M : mem) (a : Z) (bs : list byte) : Prop :=
  rdn segs M (w64 a) (length bs) = Some bs.

Definition mem_u64 segs M a (e : Z) : Prop := mem_is segs M a (Z_to_le_bytes 8 e).
Definition mem_u32 segs M a (e : Z) : Prop := mem_is segs M a (Z_to_le_bytes 4 e).
Definition mem_u16 segs M a (e : Z) : Prop := mem_is segs M a (Z_to_le_bytes 2 e).
Definition mem_u8  segs M a (e : Z) : Prop := mem_is segs M a (Z_to_le_bytes 1 e).

Definition mem_zero (segs : list Segment) (M : mem) (a len : Z) : Prop :=
  forall i, 0 <= i < len -> rdn segs M (w64 (a + i)) 1 = Some [Z_to_bv 8 0].

Definition mem_wr (segs : list Segment) (M : mem) (a len : Z) : Prop :=
  forall i, 0 <= i < len -> wview segs M (w64 (a + i)) <> None.


Lemma length_Z_to_le_bytes' : forall n z, length (Z_to_le_bytes n z) = n.
Proof. apply length_Z_to_le_bytes. Qed.

Lemma Z_to_le_bytes_mod : forall n z, (n <= 8)%nat ->
  Z_to_le_bytes n (z mod two64) = Z_to_le_bytes n z.
Proof.
  intros n z Hn. change (z mod two64) with (bv_wrap 64 z).
  apply Z_to_le_bytes_wrap. cbn. lia.
Qed.

Lemma Z_to_le_bytes_mod32 : forall n z, (n <= 4)%nat ->
  Z_to_le_bytes n (z mod two32) = Z_to_le_bytes n z.
Proof.
  intros n z Hn. change (z mod two32) with (bv_wrap 32 z).
  apply Z_to_le_bytes_wrap. cbn. lia.
Qed.

Lemma bytes_le_Z_to_le_any : forall k z, (k <= 8)%nat ->
  bytes_le_to_Z (Z_to_le_bytes k z) = z mod 2^(8 * Z.of_nat k).
Proof.
  intros k z Hk.
  rewrite <- (Z_to_le_bytes_mod k z Hk).
  rewrite bytes_le_Z_to_le by (apply Z.mod_pos_bound; lia).
  rewrite two64_eq.
  rewrite <- Znumtheory.Zmod_div_mod; try (apply Z.pow_pos_nonneg; lia).
  - reflexivity.
  - exists (2 ^ (64 - 8 * Z.of_nat k)). rewrite <- Z.pow_add_r by lia. f_equal. lia.
Qed.

Lemma bytes_le_to_Z_small : forall bs, (length bs <= 8)%nat ->
  0 <= bytes_le_to_Z bs < two64.
Proof.
  intros bs Hl. split; [apply bytes_le_to_Z_nonneg|].
  pose proof (bytes_le_to_Z_bound bs) as Hb.
  assert (2 ^ (8 * Z.of_nat (length bs)) <= 2^64) by (apply Z.pow_le_mono_r; lia).
  rewrite two64_eq. lia.
Qed.


Lemma w64_add_nat : forall a (k : nat), (w64 a + nat_to_word k)%bv = w64 (a + Z.of_nat k).
Proof.
  intros a k. apply bv_eq. unfold nat_to_word, w64. rewrite bv_add_unsigned, !Z_to_bv_unsigned.
  unfold bv_wrap. rewrite <- Zplus_mod. reflexivity.
Qed.

Lemma mem_is_skip : forall segs M a bs (k : nat),
  mem_is segs M a bs -> (k <= length bs)%nat ->
  mem_is segs M (a + Z.of_nat k) (skipn k bs).
Proof.
  intros segs M a bs k H Hk. unfold mem_is in *.
  revert a bs H Hk. induction k as [|k IH]; intros a bs H Hk.
  - rewrite Z.add_0_r. exact H.
  - destruct bs as [|b bs']; [cbn in Hk; lia|].
    cbn [skipn]. cbn [length rdn] in H.
    destruct (match M (w64 a) with Some b0 => Some b0 | None => seg_rom segs (w64 a) end); [|discriminate].
    destruct (rdn segs M (w64 a + 1) (length bs')) as [r|] eqn:Er; [|discriminate].
    injection H as Hb Hr. subst r.
    replace (a + Z.of_nat (S k)) with ((a + 1) + Z.of_nat k) by lia.
    apply IH; [|cbn in Hk; lia].
    replace (w64 (a + 1)) with (w64 a + 1)%bv; [exact Er|].
    rewrite word1_nat, w64_add_nat. reflexivity.
Qed.

Lemma mem_is_firstn : forall segs M a bs (k : nat),
  mem_is segs M a bs -> (k <= length bs)%nat ->
  mem_is segs M a (firstn k bs).
Proof.
  intros segs M a bs k H Hk. unfold mem_is in *.
  rewrite firstn_length_le by lia. eapply rdn_firstn; eauto.
Qed.

Lemma mem_is_sub : forall segs M a bs off (n : nat),
  mem_is segs M a bs -> 0 <= off -> off + Z.of_nat n <= Z.of_nat (length bs) ->
  rdn segs M (w64 (a + off)) n = Some (firstn n (skipn (Z.to_nat off) bs)).
Proof.
  intros segs M a bs off n H Hoff Hn.
  pose proof (mem_is_skip segs M a bs (Z.to_nat off) H ltac:(lia)) as H1.
  rewrite Z2Nat.id in H1 by lia.
  pose proof (mem_is_firstn segs M (a + off) _ n H1) as H2.
  rewrite skipn_length in H2.
  specialize (H2 ltac:(lia)). unfold mem_is in H2.
  rewrite firstn_length_le in H2 by (rewrite skipn_length; lia). exact H2.
Qed.

Lemma mem_is_byte : forall segs M a bs off,
  mem_is segs M a bs -> 0 <= off < Z.of_nat (length bs) ->
  rdn segs M (w64 (a + off)) 1 = Some [nth (Z.to_nat off) bs (Z_to_bv 8 0)].
Proof.
  intros segs M a bs off H Hoff.
  rewrite (mem_is_sub segs M a bs off 1 H) by lia.
  f_equal.
  rewrite <- (firstn_skipn (Z.to_nat off) bs) at 2.
  rewrite List.app_nth2 by (rewrite firstn_length_le; lia).
  rewrite firstn_length_le by lia. rewrite Nat.sub_diag.
  destruct (skipn (Z.to_nat off) bs) as [|b r] eqn:E.
  - exfalso. apply (f_equal (@length byte)) in E. rewrite skipn_length in E. cbn in E. lia.
  - reflexivity.
Qed.

Lemma mem_zero_byte : forall segs M a len off,
  mem_zero segs M a len -> 0 <= off < len ->
  rdn segs M (w64 (a + off)) 1 = Some [Z_to_bv 8 0].
Proof. intros segs M a len off H Hoff. apply H. lia. Qed.

Lemma mem_zero_sub : forall segs M a len off (n : nat),
  mem_zero segs M a len -> 0 <= off -> off + Z.of_nat n <= len ->
  0 <= a + off -> a + off + Z.of_nat n <= two64 ->
  rdn segs M (w64 (a + off)) n = Some (repeat (Z_to_bv 8 0) n).
Proof.
  intros segs M a len off n Hz Hoff Hn Hlo Hhi.
  revert off Hoff Hn Hlo Hhi. induction n as [|n IH]; intros off Hoff Hn Hlo Hhi; [reflexivity|].
  replace (S n) with (1 + n)%nat by lia.
  change (repeat (Z_to_bv 8 0) (1 + n)) with ([Z_to_bv 8 0] ++ repeat (Z_to_bv 8 0) n).
  apply rdn_app.
  - apply Hz. lia.
  - rewrite w64_add_nat. replace (a + off + Z.of_nat 1) with (a + (off + 1)) by lia.
    apply IH; lia.
Qed.


Definition zdisj (a : Z) (n : Z) (a' : Z) (n' : Z) : Prop :=
  0 <= a < two64 /\ a + n <= two64 /\ 0 <= a' < two64 /\ a' + n' <= two64 /\
  (a + n <= a' \/ a' + n' <= a).

Lemma rdn_wbytes_frame : forall segs M a bs a' (n : nat),
  zdisj a (Z.of_nat (length bs)) a' (Z.of_nat n) ->
  rdn segs (wbytes M (w64 a) bs) (w64 a') n = rdn segs M (w64 a') n.
Proof.
  intros segs M a bs a' n (H1 & H2 & H3 & H4 & H5).
  pose proof (Nat2Z.is_nonneg (length bs)). pose proof (Nat2Z.is_nonneg n).
  apply rdn_wbytes_out; rewrite !w64_unsigned, !mod_small_u64; lia.
Qed.

Lemma mem_is_frame : forall segs M a bs a' bs',
  mem_is segs M a' bs' ->
  zdisj a (Z.of_nat (length bs)) a' (Z.of_nat (length bs')) ->
  mem_is segs (wbytes M (w64 a) bs) a' bs'.
Proof. intros. unfold mem_is. rewrite rdn_wbytes_frame; assumption. Qed.

Lemma mem_zero_frame : forall segs M a bs a' len,
  mem_zero segs M a' len ->
  zdisj a (Z.of_nat (length bs)) a' len ->
  mem_zero segs (wbytes M (w64 a) bs) a' len.
Proof.
  intros segs M a bs a' len Hz Hd i Hi.
  rewrite rdn_wbytes_frame; [apply Hz; lia|].
  destruct Hd as (H1 & H2 & H3 & H4 & H5). unfold zdisj. cbn [length Z.of_nat]. lia.
Qed.

Lemma wview_wbytes_mono : forall segs bs M (a x : word),
  wview segs M x <> None -> wview segs (wbytes M a bs) x <> None.
Proof.
  intros segs bs. induction bs as [|b bs IH]; intros M a x H; [exact H|].
  cbn [wbytes]. apply IH. unfold wview in *.
  destruct (bv_eqb x a); [discriminate|]. exact H.
Qed.

Lemma mem_wr_frame : forall segs M a bs a' len,
  mem_wr segs M a' len -> mem_wr segs (wbytes M (w64 a) bs) a' len.
Proof. intros segs M a bs a' len H i Hi. apply wview_wbytes_mono. apply H. lia. Qed.

Lemma mem_is_stored : forall segs M a bs,
  0 <= a < two64 -> a + Z.of_nat (length bs) <= two64 ->
  mem_is segs (wbytes M (w64 a) bs) a bs.
Proof.
  intros segs M a bs H0 H1. unfold mem_is. apply rdn_wbytes_hit.
  rewrite w64_unsigned, mod_small_u64; lia.
Qed.


Lemma store_ok_of_mem_wr : forall segs M a' len a (k : nat),
  mem_wr segs M a' len -> a' <= a -> a + Z.of_nat k <= a' + len ->
  store_ok segs M (w64 a) k = true.
Proof.
  intros segs M a' len a k Hw Hlo Hhi.
  revert a Hlo Hhi. induction k as [|k IH]; intros a Hlo Hhi; [reflexivity|].
  cbn [store_ok].
  pose proof (Hw (a - a') ltac:(lia)) as H1. replace (a' + (a - a')) with a in H1 by lia.
  destruct (wview segs M (w64 a)); [|exfalso; apply H1; reflexivity].
  replace (w64 a + 1)%bv with (w64 (a + 1)).
  - apply IH; lia.
  - rewrite word1_nat, w64_add_nat. reflexivity.
Qed.

Lemma mem_wr_sub : forall segs M a len a' len',
  mem_wr segs M a len -> a <= a' -> a' + len' <= a + len -> mem_wr segs M a' len'.
Proof. intros segs M a len a' len' H H1 H2 i Hi. replace (a' + i) with (a + (a' - a + i)) by lia. apply H. lia. Qed.


Section LoadStore.
Variable segs : list Segment.

Lemma zrd_addr : forall R rs (imm : bv 12),
  v_addi (getr (zden R) rs) (bv_signed imm) = w64 (zrd R rs + bv_signed imm).
Proof. intros. rewrite getr_zden. apply w64_addi. Qed.

Lemma rdn_len : forall M a n bs, rdn segs M a n = Some bs -> length bs = n.
Proof. intros. eapply rdn_length. eassumption. Qed.

Lemma zx_ld : forall pc R M MD T w rd rs (imm : bv 12) bs,
  fetch_word segs (w64 pc) = Some w -> is_ecall w = false ->
  decode_any w = Some (Load SZ8 true rd rs imm, 4%Z) ->
  m_halted MD = None ->
  rdn segs M (w64 (zrd R rs + bv_signed imm)) 8 = Some bs ->
  realizes segs (zcfg segs (pc + 4)
    (if is_x0 rd then R else zset R (bv_key rd) (bytes_le_to_Z bs)) M MD) T ->
  realizes segs (zcfg segs pc R M MD) T.
Proof.
  intros until T. intros w rd rs imm bs F E D Hh Hr Hk.
  eapply zx_raw; [exact Hh| |exact Hk].
  unfold zst. erewrite (step_ld segs _ _ _ _ w rd rs imm bs (w64 (bytes_le_to_Z bs))); try eassumption.
  - rewrite wb_zden, w64_pc4. reflexivity.
  - rewrite zrd_addr. exact Hr.
  - rewrite w64_unsigned, mod_small_u64; [reflexivity|].
    apply bytes_le_to_Z_small. rewrite (rdn_len _ _ _ _ Hr). lia.
Qed.

Lemma zx_lwu : forall pc R M MD T w rd rs (imm : bv 12) bs,
  fetch_word segs (w64 pc) = Some w -> is_ecall w = false ->
  decode_any w = Some (Load SZ4 false rd rs imm, 4%Z) ->
  m_halted MD = None ->
  rdn segs M (w64 (zrd R rs + bv_signed imm)) 4 = Some bs ->
  realizes segs (zcfg segs (pc + 4)
    (if is_x0 rd then R else zset R (bv_key rd) (bytes_le_to_Z bs)) M MD) T ->
  realizes segs (zcfg segs pc R M MD) T.
Proof.
  intros until T. intros w rd rs imm bs F E D Hh Hr Hk.
  eapply zx_raw; [exact Hh| |exact Hk].
  unfold zst. erewrite (step_lwu segs _ _ _ _ w rd rs imm bs (w64 (bytes_le_to_Z bs))); try eassumption.
  - rewrite wb_zden, w64_pc4. reflexivity.
  - rewrite zrd_addr. exact Hr.
  - rewrite w64_unsigned, mod_small_u64; [reflexivity|].
    apply bytes_le_to_Z_small. rewrite (rdn_len _ _ _ _ Hr). lia.
Qed.

Lemma zx_lhu : forall pc R M MD T w rd rs (imm : bv 12) bs,
  fetch_word segs (w64 pc) = Some w -> is_ecall w = false ->
  decode_any w = Some (Load SZ2 false rd rs imm, 4%Z) ->
  m_halted MD = None ->
  rdn segs M (w64 (zrd R rs + bv_signed imm)) 2 = Some bs ->
  realizes segs (zcfg segs (pc + 4)
    (if is_x0 rd then R else zset R (bv_key rd) (bytes_le_to_Z bs)) M MD) T ->
  realizes segs (zcfg segs pc R M MD) T.
Proof.
  intros until T. intros w rd rs imm bs F E D Hh Hr Hk.
  eapply zx_raw; [exact Hh| |exact Hk].
  unfold zst. erewrite (step_lhu segs _ _ _ _ w rd rs imm bs (w64 (bytes_le_to_Z bs))); try eassumption.
  - rewrite wb_zden, w64_pc4. reflexivity.
  - rewrite zrd_addr. exact Hr.
  - rewrite w64_unsigned, mod_small_u64; [reflexivity|].
    apply bytes_le_to_Z_small. rewrite (rdn_len _ _ _ _ Hr). lia.
Qed.

Lemma zx_lbu : forall pc R M MD T w rd rs (imm : bv 12) b,
  fetch_word segs (w64 pc) = Some w -> is_ecall w = false ->
  decode_any w = Some (Load SZ1 false rd rs imm, 4%Z) ->
  m_halted MD = None ->
  rdn segs M (w64 (zrd R rs + bv_signed imm)) 1 = Some [b] ->
  realizes segs (zcfg segs (pc + 4)
    (if is_x0 rd then R else zset R (bv_key rd) (bv_unsigned b)) M MD) T ->
  realizes segs (zcfg segs pc R M MD) T.
Proof.
  intros until T. intros w rd rs imm b F E D Hh Hr Hk.
  eapply zx_raw; [exact Hh| |exact Hk].
  unfold zst. erewrite (step_lbu segs _ _ _ _ w rd rs imm b); try eassumption.
  - change (Z_to_bv 64 (bv_unsigned b)) with (w64 (bv_unsigned b)).
    rewrite wb_zden, w64_pc4. reflexivity.
  - rewrite zrd_addr. exact Hr.
Qed.

Lemma zx_lw : forall pc R M MD T w rd rs (imm : bv 12) bs,
  fetch_word segs (w64 pc) = Some w -> is_ecall w = false ->
  decode_any w = Some (Load SZ4 true rd rs imm, 4%Z) ->
  m_halted MD = None ->
  rdn segs M (w64 (zrd R rs + bv_signed imm)) 4 = Some bs ->
  realizes segs (zcfg segs (pc + 4)
    (if is_x0 rd then R else zset R (bv_key rd) (bv_swrap 32 (bytes_le_to_Z bs))) M MD) T ->
  realizes segs (zcfg segs pc R M MD) T.
Proof.
  intros until T. intros w rd rs imm bs F E D Hh Hr Hk.
  eapply zx_raw; [exact Hh| |exact Hk].
  unfold zst. erewrite (step_lw segs _ _ _ _ w rd rs imm bs (w64 (bytes_le_to_Z bs))); try eassumption.
  - unfold v_lw. rewrite w64_unsigned, mod_small_u64.
    + change (Z_to_bv 64 ?x) with (w64 x). rewrite wb_zden, w64_pc4. reflexivity.
    + apply bytes_le_to_Z_small. rewrite (rdn_len _ _ _ _ Hr). lia.
  - rewrite zrd_addr. exact Hr.
  - rewrite w64_unsigned, mod_small_u64; [reflexivity|].
    apply bytes_le_to_Z_small. rewrite (rdn_len _ _ _ _ Hr). lia.
Qed.

Lemma zx_lh : forall pc R M MD T w rd rs (imm : bv 12) bs,
  fetch_word segs (w64 pc) = Some w -> is_ecall w = false ->
  decode_any w = Some (Load SZ2 true rd rs imm, 4%Z) ->
  m_halted MD = None ->
  rdn segs M (w64 (zrd R rs + bv_signed imm)) 2 = Some bs ->
  realizes segs (zcfg segs (pc + 4)
    (if is_x0 rd then R else zset R (bv_key rd) (bv_swrap 16 (bytes_le_to_Z bs))) M MD) T ->
  realizes segs (zcfg segs pc R M MD) T.
Proof.
  intros until T. intros w rd rs imm bs F E D Hh Hr Hk.
  eapply zx_raw; [exact Hh| |exact Hk].
  unfold zst. erewrite (step_lh segs _ _ _ _ w rd rs imm bs (w64 (bytes_le_to_Z bs))); try eassumption.
  - unfold v_lh. rewrite w64_unsigned, mod_small_u64.
    + change (Z_to_bv 64 ?x) with (w64 x). rewrite wb_zden, w64_pc4. reflexivity.
    + apply bytes_le_to_Z_small. rewrite (rdn_len _ _ _ _ Hr). lia.
  - rewrite zrd_addr. exact Hr.
  - rewrite w64_unsigned, mod_small_u64; [reflexivity|].
    apply bytes_le_to_Z_small. rewrite (rdn_len _ _ _ _ Hr). lia.
Qed.

Lemma zx_lb : forall pc R M MD T w rd rs (imm : bv 12) b,
  fetch_word segs (w64 pc) = Some w -> is_ecall w = false ->
  decode_any w = Some (Load SZ1 true rd rs imm, 4%Z) ->
  m_halted MD = None ->
  rdn segs M (w64 (zrd R rs + bv_signed imm)) 1 = Some [b] ->
  realizes segs (zcfg segs (pc + 4)
    (if is_x0 rd then R else zset R (bv_key rd) (bv_signed b)) M MD) T ->
  realizes segs (zcfg segs pc R M MD) T.
Proof.
  intros until T. intros w rd rs imm b F E D Hh Hr Hk.
  eapply zx_raw; [exact Hh| |exact Hk].
  unfold zst. erewrite (step_lb segs _ _ _ _ w rd rs imm b); try eassumption.
  - unfold v_lb. change (Z_to_bv 64 ?x) with (w64 x). rewrite wb_zden, w64_pc4. reflexivity.
  - rewrite zrd_addr. exact Hr.
Qed.

Lemma zden_zset_mod : forall R k e, zden (zset R k (e mod two64)) = zden (zset R k e).
Proof. intros. unfold zset. rewrite <- !tset_zden, w64_mod. reflexivity. Qed.

Lemma zcfg_leaf_mod : forall pc R k e M MD,
  zcfg segs pc (zset R k (e mod two64)) M MD = zcfg segs pc (zset R k e) M MD.
Proof. intros. unfold zcfg, zst. rewrite zden_zset_mod. reflexivity. Qed.

Lemma zx_ld_u64 : forall pc R M MD T w rd rs (imm : bv 12) e,
  fetch_word segs (w64 pc) = Some w -> is_ecall w = false ->
  decode_any w = Some (Load SZ8 true rd rs imm, 4%Z) ->
  m_halted MD = None ->
  mem_u64 segs M (zrd R rs + bv_signed imm) e ->
  realizes segs (zcfg segs (pc + 4)
    (if is_x0 rd then R else zset R (bv_key rd) e) M MD) T ->
  realizes segs (zcfg segs pc R M MD) T.
Proof.
  intros until T. intros w rd rs imm e F E D Hh Hr Hk.
  eapply zx_ld; try eassumption.
  rewrite bytes_le_Z_to_le_any by lia. change (2 ^ (8 * Z.of_nat 8)) with two64.
  destruct (is_x0 rd); [exact Hk|]. rewrite zcfg_leaf_mod. exact Hk.
Qed.

Lemma zx_lwu_u32 : forall pc R M MD T w rd rs (imm : bv 12) e,
  fetch_word segs (w64 pc) = Some w -> is_ecall w = false ->
  decode_any w = Some (Load SZ4 false rd rs imm, 4%Z) ->
  m_halted MD = None ->
  mem_u32 segs M (zrd R rs + bv_signed imm) e ->
  realizes segs (zcfg segs (pc + 4)
    (if is_x0 rd then R else zset R (bv_key rd) (e mod two32)) M MD) T ->
  realizes segs (zcfg segs pc R M MD) T.
Proof.
  intros until T. intros w rd rs imm e F E D Hh Hr Hk.
  eapply zx_lwu; try eassumption.
  rewrite bytes_le_Z_to_le_any by lia. exact Hk.
Qed.

Lemma zx_lw_u32 : forall pc R M MD T w rd rs (imm : bv 12) e,
  fetch_word segs (w64 pc) = Some w -> is_ecall w = false ->
  decode_any w = Some (Load SZ4 true rd rs imm, 4%Z) ->
  m_halted MD = None ->
  mem_u32 segs M (zrd R rs + bv_signed imm) e ->
  realizes segs (zcfg segs (pc + 4)
    (if is_x0 rd then R else zset R (bv_key rd) (bv_swrap 32 e)) M MD) T ->
  realizes segs (zcfg segs pc R M MD) T.
Proof.
  intros until T. intros w rd rs imm e F E D Hh Hr Hk.
  eapply zx_lw; try eassumption.
  rewrite bytes_le_Z_to_le_any by lia. change (2 ^ (8 * Z.of_nat 4)) with two32.
  rewrite swrap32_mod32. exact Hk.
Qed.


Lemma word_to_le_bytes_w64 : forall (k : nat) e, (k <= 8)%nat ->
  word_to_le_bytes k (w64 e) = Z_to_le_bytes k e.
Proof. intros. unfold word_to_le_bytes. rewrite w64_unsigned. apply Z_to_le_bytes_mod. assumption. Qed.

Lemma zx_sd : forall pc R M MD T w rs1 rs2 (imm : bv 12) a,
  fetch_word segs (w64 pc) = Some w -> is_ecall w = false ->
  decode_any w = Some (Store SZ8 rs1 rs2 imm, 4%Z) ->
  m_halted MD = None ->
  zrd R rs1 + bv_signed imm = a ->
  store_ok segs M (w64 a) 8 = true ->
  realizes segs (zcfg segs (pc + 4) R (wbytes M (w64 a) (Z_to_le_bytes 8 (zrd R rs2))) MD) T ->
  realizes segs (zcfg segs pc R M MD) T.
Proof.
  intros until T. intros w rs1 rs2 imm a F E D Hh Ha Hok Hk.
  eapply zx_raw; [exact Hh| |exact Hk].
  unfold zst. erewrite (step_sd_at segs _ _ _ _ w rs1 rs2 imm (w64 a) (w64 (zrd R rs2))); try eassumption.
  - rewrite w64_pc4, word_to_le_bytes_w64 by lia. reflexivity.
  - rewrite zrd_addr, Ha. reflexivity.
  - apply getr_zden.
Qed.

Lemma zx_sw : forall pc R M MD T w rs1 rs2 (imm : bv 12) a,
  fetch_word segs (w64 pc) = Some w -> is_ecall w = false ->
  decode_any w = Some (Store SZ4 rs1 rs2 imm, 4%Z) ->
  m_halted MD = None ->
  zrd R rs1 + bv_signed imm = a ->
  store_ok segs M (w64 a) 4 = true ->
  realizes segs (zcfg segs (pc + 4) R (wbytes M (w64 a) (Z_to_le_bytes 4 (zrd R rs2))) MD) T ->
  realizes segs (zcfg segs pc R M MD) T.
Proof.
  intros until T. intros w rs1 rs2 imm a F E D Hh Ha Hok Hk.
  eapply zx_raw; [exact Hh| |exact Hk].
  unfold zst. erewrite (step_sw_at segs _ _ _ _ w rs1 rs2 imm (w64 a) (w64 (zrd R rs2))); try eassumption.
  - rewrite w64_pc4, word_to_le_bytes_w64 by lia. reflexivity.
  - rewrite zrd_addr, Ha. reflexivity.
  - apply getr_zden.
Qed.

Lemma zx_sh : forall pc R M MD T w rs1 rs2 (imm : bv 12) a,
  fetch_word segs (w64 pc) = Some w -> is_ecall w = false ->
  decode_any w = Some (Store SZ2 rs1 rs2 imm, 4%Z) ->
  m_halted MD = None ->
  zrd R rs1 + bv_signed imm = a ->
  store_ok segs M (w64 a) 2 = true ->
  realizes segs (zcfg segs (pc + 4) R (wbytes M (w64 a) (Z_to_le_bytes 2 (zrd R rs2))) MD) T ->
  realizes segs (zcfg segs pc R M MD) T.
Proof.
  intros until T. intros w rs1 rs2 imm a F E D Hh Ha Hok Hk.
  eapply zx_raw; [exact Hh| |exact Hk].
  unfold zst. erewrite (step_sh_at segs _ _ _ _ w rs1 rs2 imm (w64 a) (w64 (zrd R rs2))); try eassumption.
  - rewrite w64_pc4, word_to_le_bytes_w64 by lia. reflexivity.
  - rewrite zrd_addr, Ha. reflexivity.
  - apply getr_zden.
Qed.

Lemma zx_sb : forall pc R M MD T w rs1 rs2 (imm : bv 12) a,
  fetch_word segs (w64 pc) = Some w -> is_ecall w = false ->
  decode_any w = Some (Store SZ1 rs1 rs2 imm, 4%Z) ->
  m_halted MD = None ->
  zrd R rs1 + bv_signed imm = a ->
  store_ok segs M (w64 a) 1 = true ->
  realizes segs (zcfg segs (pc + 4) R (wbytes M (w64 a) (Z_to_le_bytes 1 (zrd R rs2))) MD) T ->
  realizes segs (zcfg segs pc R M MD) T.
Proof.
  intros until T. intros w rs1 rs2 imm a F E D Hh Ha Hok Hk.
  eapply zx_raw; [exact Hh| |exact Hk].
  unfold zst. erewrite (step_sb segs _ _ _ _ w rs1 rs2 imm); try eassumption.
  - rewrite w64_pc4, zrd_addr, Ha, getr_zden, word_to_le_bytes_w64 by lia. reflexivity.
  - rewrite zrd_addr, Ha. exact Hok.
Qed.

End LoadStore.


Lemma mem_u64_stored : forall segs M a e,
  0 <= a -> a + 8 <= two64 -> mem_u64 segs (wbytes M (w64 a) (Z_to_le_bytes 8 e)) a e.
Proof. intros. unfold mem_u64. apply mem_is_stored; rewrite ?length_Z_to_le_bytes'; lia. Qed.

Lemma mem_u32_stored : forall segs M a e,
  0 <= a -> a + 4 <= two64 -> mem_u32 segs (wbytes M (w64 a) (Z_to_le_bytes 4 e)) a e.
Proof. intros. unfold mem_u32. apply mem_is_stored; rewrite ?length_Z_to_le_bytes'; lia. Qed.

Lemma mem_u16_stored : forall segs M a e,
  0 <= a -> a + 2 <= two64 -> mem_u16 segs (wbytes M (w64 a) (Z_to_le_bytes 2 e)) a e.
Proof. intros. unfold mem_u16. apply mem_is_stored; rewrite ?length_Z_to_le_bytes'; lia. Qed.

Lemma mem_u8_stored : forall segs M a e,
  0 <= a -> a + 1 <= two64 -> mem_u8 segs (wbytes M (w64 a) (Z_to_le_bytes 1 e)) a e.
Proof. intros. unfold mem_u8. apply mem_is_stored; rewrite ?length_Z_to_le_bytes'; lia. Qed.

Lemma mem_u64_frame : forall segs M a bs a' e,
  mem_u64 segs M a' e -> zdisj a (Z.of_nat (length bs)) a' 8 ->
  mem_u64 segs (wbytes M (w64 a) bs) a' e.
Proof. intros. unfold mem_u64 in *. apply mem_is_frame; rewrite ?length_Z_to_le_bytes'; assumption. Qed.

Lemma mem_u32_frame : forall segs M a bs a' e,
  mem_u32 segs M a' e -> zdisj a (Z.of_nat (length bs)) a' 4 ->
  mem_u32 segs (wbytes M (w64 a) bs) a' e.
Proof. intros. unfold mem_u32 in *. apply mem_is_frame; rewrite ?length_Z_to_le_bytes'; assumption. Qed.

Lemma mem_u16_frame : forall segs M a bs a' e,
  mem_u16 segs M a' e -> zdisj a (Z.of_nat (length bs)) a' 2 ->
  mem_u16 segs (wbytes M (w64 a) bs) a' e.
Proof. intros. unfold mem_u16 in *. apply mem_is_frame; rewrite ?length_Z_to_le_bytes'; assumption. Qed.

Lemma mem_u8_frame : forall segs M a bs a' e,
  mem_u8 segs M a' e -> zdisj a (Z.of_nat (length bs)) a' 1 ->
  mem_u8 segs (wbytes M (w64 a) bs) a' e.
Proof. intros. unfold mem_u8 in *. apply mem_is_frame; rewrite ?length_Z_to_le_bytes'; assumption. Qed.

Lemma mem_u64_rdn : forall segs M a e, mem_u64 segs M a e -> rdn segs M (w64 a) 8 = Some (Z_to_le_bytes 8 e).
Proof. intros. exact H. Qed.
Lemma mem_u32_rdn : forall segs M a e, mem_u32 segs M a e -> rdn segs M (w64 a) 4 = Some (Z_to_le_bytes 4 e).
Proof. intros. exact H. Qed.
Lemma mem_u16_rdn : forall segs M a e, mem_u16 segs M a e -> rdn segs M (w64 a) 2 = Some (Z_to_le_bytes 2 e).
Proof. intros. exact H. Qed.
Lemma mem_u8_rdn : forall segs M a e, mem_u8 segs M a e -> rdn segs M (w64 a) 1 = Some [Z_to_bv 8 e].
Proof. intros. exact H. Qed.


Section ULoadStore.
Variable segs : list Segment.

Local Ltac lift L :=
  intros; rewrite <- ?wb_zupd, <- ?zrd_zupd in *; eapply L; eassumption.

Lemma zu_ld : forall pc Rb l M MD T w rd rs (imm : bv 12) bs,
  fetch_word segs (w64 pc) = Some w -> is_ecall w = false ->
  decode_any w = Some (Load SZ8 true rd rs imm, 4%Z) -> m_halted MD = None ->
  rdn segs M (w64 (zrd_l Rb l rs + bv_signed imm)) 8 = Some bs ->
  realizes segs (zcfg segs (pc + 4) (zupd Rb (wb rd (bytes_le_to_Z bs) l)) M MD) T ->
  realizes segs (zcfg segs pc (zupd Rb l) M MD) T.
Proof. lift (zx_ld segs). Qed.

Lemma zu_lwu : forall pc Rb l M MD T w rd rs (imm : bv 12) bs,
  fetch_word segs (w64 pc) = Some w -> is_ecall w = false ->
  decode_any w = Some (Load SZ4 false rd rs imm, 4%Z) -> m_halted MD = None ->
  rdn segs M (w64 (zrd_l Rb l rs + bv_signed imm)) 4 = Some bs ->
  realizes segs (zcfg segs (pc + 4) (zupd Rb (wb rd (bytes_le_to_Z bs) l)) M MD) T ->
  realizes segs (zcfg segs pc (zupd Rb l) M MD) T.
Proof. lift (zx_lwu segs). Qed.

Lemma zu_lhu : forall pc Rb l M MD T w rd rs (imm : bv 12) bs,
  fetch_word segs (w64 pc) = Some w -> is_ecall w = false ->
  decode_any w = Some (Load SZ2 false rd rs imm, 4%Z) -> m_halted MD = None ->
  rdn segs M (w64 (zrd_l Rb l rs + bv_signed imm)) 2 = Some bs ->
  realizes segs (zcfg segs (pc + 4) (zupd Rb (wb rd (bytes_le_to_Z bs) l)) M MD) T ->
  realizes segs (zcfg segs pc (zupd Rb l) M MD) T.
Proof. lift (zx_lhu segs). Qed.

Lemma zu_lbu : forall pc Rb l M MD T w rd rs (imm : bv 12) b,
  fetch_word segs (w64 pc) = Some w -> is_ecall w = false ->
  decode_any w = Some (Load SZ1 false rd rs imm, 4%Z) -> m_halted MD = None ->
  rdn segs M (w64 (zrd_l Rb l rs + bv_signed imm)) 1 = Some [b] ->
  realizes segs (zcfg segs (pc + 4) (zupd Rb (wb rd (bv_unsigned b) l)) M MD) T ->
  realizes segs (zcfg segs pc (zupd Rb l) M MD) T.
Proof. lift (zx_lbu segs). Qed.

Lemma zu_lw : forall pc Rb l M MD T w rd rs (imm : bv 12) bs,
  fetch_word segs (w64 pc) = Some w -> is_ecall w = false ->
  decode_any w = Some (Load SZ4 true rd rs imm, 4%Z) -> m_halted MD = None ->
  rdn segs M (w64 (zrd_l Rb l rs + bv_signed imm)) 4 = Some bs ->
  realizes segs (zcfg segs (pc + 4) (zupd Rb (wb rd (bv_swrap 32 (bytes_le_to_Z bs)) l)) M MD) T ->
  realizes segs (zcfg segs pc (zupd Rb l) M MD) T.
Proof. lift (zx_lw segs). Qed.

Lemma zu_lh : forall pc Rb l M MD T w rd rs (imm : bv 12) bs,
  fetch_word segs (w64 pc) = Some w -> is_ecall w = false ->
  decode_any w = Some (Load SZ2 true rd rs imm, 4%Z) -> m_halted MD = None ->
  rdn segs M (w64 (zrd_l Rb l rs + bv_signed imm)) 2 = Some bs ->
  realizes segs (zcfg segs (pc + 4) (zupd Rb (wb rd (bv_swrap 16 (bytes_le_to_Z bs)) l)) M MD) T ->
  realizes segs (zcfg segs pc (zupd Rb l) M MD) T.
Proof. lift (zx_lh segs). Qed.

Lemma zu_lb : forall pc Rb l M MD T w rd rs (imm : bv 12) b,
  fetch_word segs (w64 pc) = Some w -> is_ecall w = false ->
  decode_any w = Some (Load SZ1 true rd rs imm, 4%Z) -> m_halted MD = None ->
  rdn segs M (w64 (zrd_l Rb l rs + bv_signed imm)) 1 = Some [b] ->
  realizes segs (zcfg segs (pc + 4) (zupd Rb (wb rd (bv_signed b) l)) M MD) T ->
  realizes segs (zcfg segs pc (zupd Rb l) M MD) T.
Proof. lift (zx_lb segs). Qed.

Lemma zu_ld_u64 : forall pc Rb l M MD T w rd rs (imm : bv 12) e,
  fetch_word segs (w64 pc) = Some w -> is_ecall w = false ->
  decode_any w = Some (Load SZ8 true rd rs imm, 4%Z) -> m_halted MD = None ->
  mem_u64 segs M (zrd_l Rb l rs + bv_signed imm) e ->
  realizes segs (zcfg segs (pc + 4) (zupd Rb (wb rd e l)) M MD) T ->
  realizes segs (zcfg segs pc (zupd Rb l) M MD) T.
Proof. lift (zx_ld_u64 segs). Qed.

Lemma zu_lwu_u32 : forall pc Rb l M MD T w rd rs (imm : bv 12) e,
  fetch_word segs (w64 pc) = Some w -> is_ecall w = false ->
  decode_any w = Some (Load SZ4 false rd rs imm, 4%Z) -> m_halted MD = None ->
  mem_u32 segs M (zrd_l Rb l rs + bv_signed imm) e ->
  realizes segs (zcfg segs (pc + 4) (zupd Rb (wb rd (e mod two32) l)) M MD) T ->
  realizes segs (zcfg segs pc (zupd Rb l) M MD) T.
Proof. lift (zx_lwu_u32 segs). Qed.

Lemma zu_lw_u32 : forall pc Rb l M MD T w rd rs (imm : bv 12) e,
  fetch_word segs (w64 pc) = Some w -> is_ecall w = false ->
  decode_any w = Some (Load SZ4 true rd rs imm, 4%Z) -> m_halted MD = None ->
  mem_u32 segs M (zrd_l Rb l rs + bv_signed imm) e ->
  realizes segs (zcfg segs (pc + 4) (zupd Rb (wb rd (bv_swrap 32 e) l)) M MD) T ->
  realizes segs (zcfg segs pc (zupd Rb l) M MD) T.
Proof. lift (zx_lw_u32 segs). Qed.

Lemma zu_sd : forall pc Rb l M MD T w rs1 rs2 (imm : bv 12) a,
  fetch_word segs (w64 pc) = Some w -> is_ecall w = false ->
  decode_any w = Some (Store SZ8 rs1 rs2 imm, 4%Z) -> m_halted MD = None ->
  zrd_l Rb l rs1 + bv_signed imm = a -> store_ok segs M (w64 a) 8 = true ->
  realizes segs (zcfg segs (pc + 4) (zupd Rb l) (wbytes M (w64 a) (Z_to_le_bytes 8 (zrd_l Rb l rs2))) MD) T ->
  realizes segs (zcfg segs pc (zupd Rb l) M MD) T.
Proof. lift (zx_sd segs). Qed.

Lemma zu_sw : forall pc Rb l M MD T w rs1 rs2 (imm : bv 12) a,
  fetch_word segs (w64 pc) = Some w -> is_ecall w = false ->
  decode_any w = Some (Store SZ4 rs1 rs2 imm, 4%Z) -> m_halted MD = None ->
  zrd_l Rb l rs1 + bv_signed imm = a -> store_ok segs M (w64 a) 4 = true ->
  realizes segs (zcfg segs (pc + 4) (zupd Rb l) (wbytes M (w64 a) (Z_to_le_bytes 4 (zrd_l Rb l rs2))) MD) T ->
  realizes segs (zcfg segs pc (zupd Rb l) M MD) T.
Proof. lift (zx_sw segs). Qed.

Lemma zu_sh : forall pc Rb l M MD T w rs1 rs2 (imm : bv 12) a,
  fetch_word segs (w64 pc) = Some w -> is_ecall w = false ->
  decode_any w = Some (Store SZ2 rs1 rs2 imm, 4%Z) -> m_halted MD = None ->
  zrd_l Rb l rs1 + bv_signed imm = a -> store_ok segs M (w64 a) 2 = true ->
  realizes segs (zcfg segs (pc + 4) (zupd Rb l) (wbytes M (w64 a) (Z_to_le_bytes 2 (zrd_l Rb l rs2))) MD) T ->
  realizes segs (zcfg segs pc (zupd Rb l) M MD) T.
Proof. lift (zx_sh segs). Qed.

Lemma zu_sb : forall pc Rb l M MD T w rs1 rs2 (imm : bv 12) a,
  fetch_word segs (w64 pc) = Some w -> is_ecall w = false ->
  decode_any w = Some (Store SZ1 rs1 rs2 imm, 4%Z) -> m_halted MD = None ->
  zrd_l Rb l rs1 + bv_signed imm = a -> store_ok segs M (w64 a) 1 = true ->
  realizes segs (zcfg segs (pc + 4) (zupd Rb l) (wbytes M (w64 a) (Z_to_le_bytes 1 (zrd_l Rb l rs2))) MD) T ->
  realizes segs (zcfg segs pc (zupd Rb l) M MD) T.
Proof. lift (zx_sb segs). Qed.

End ULoadStore.
End FXG.
