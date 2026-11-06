(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.Info Require Import PropExec CatExec CatSim SeqExec StoreOk SymExec Hoare Frame PropExecFP.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.Info Require Import LibDefs LibFrame.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.AsLib Require Import AsSymExec AsSymExecSound AsSymRun AsSymDrive AsSymCall AsLibBswap AsLibFPLib AsLibTagsLib.
Unset Lia Cache. Unset Nia Cache.   (* [comment removed for export] *)
From Stdlib Require Import Zify.
(* [comment removed for export] *)
Local Ltac el_t1 := (intros; Zify.zify_pre_hook; zify_elim_let; zify_op; zify_iter_specs; Zify.zify_post_hook); xlia zchecker.
(* [comment removed for export] *)
Local Ltac el_dm_pose x k := let v := eval vm_compute in k in lazymatch v with Zpos _ =>   (* [comment removed for export] *)
  lazymatch goal with _ : (x = k * (x / k) + x mod k)%Z |- _ => fail | _ =>
    pose proof (Z.div_mod x k ltac:(vm_compute; discriminate)); pose proof (Z.mod_pos_bound x k ltac:(vm_compute; reflexivity)) end end.
Local Ltac el_dm := repeat match goal with
  | |- context [ (?x / ?k)%Z ] => el_dm_pose x k
  | |- context [ (?x mod ?k)%Z ] => el_dm_pose x k
  | H : ?T |- _ => lazymatch T with (_ <= _)%Z => idtac | (_ < _)%Z => idtac | @eq Z _ _ => idtac | _ /\ _ => idtac | _ \/ _ => idtac end;
      match T with context [ (?x / ?k)%Z ] => el_dm_pose x k | context [ (?x mod ?k)%Z ] => el_dm_pose x k end
  end.
Local Ltac el_lia_core3 := first [ el_t1 | Zify.zify; xlia zchecker ].   (* [comment removed for export] *)
Local Ltac el_lia_core := first [ el_t1 | ((progress el_dm); el_t1) ].
Local Ltac el_goal_has_var := match goal with |- ?G => match G with context [?x] => is_var x end end.
Local Ltac Lia.lia ::= tryif el_goal_has_var then el_lia_core else first [ solve [clear; el_lia_core] | el_lia_core ].
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
Import ASX. Import ASXS.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

(* [comment removed for export] *)
Definition hidden (P : Prop) : Prop := P.
Ltac hide H := lazymatch type of H with ?T => change (hidden T) in H end.
Ltac unhide H := unfold hidden in H.

Lemma regs_kept_trans : forall l r1 r2 r3, regs_kept l r1 r2 -> regs_kept l r2 r3 -> regs_kept l r1 r3.
Proof. intros l r1 r2 r3 A B r Hr. rewrite (B r Hr). apply A. exact Hr. Qed.
Lemma fregs_kept_trans : forall l r1 r2 r3, fregs_kept l r1 r2 -> fregs_kept l r2 r3 -> fregs_kept l r1 r3.
Proof. intros l r1 r2 r3 A B r Hr. rewrite (B r Hr). apply A. exact Hr. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition sub (bs : list byte) (o L : Z) : list byte :=
  firstn (Z.to_nat L) (skipn (Z.to_nat o) bs).

Lemma sub_length : forall bs o L,
  0 <= o -> 0 <= L -> o + L <= Z.of_nat (length bs) -> Z.of_nat (length (sub bs o L)) = L.
Proof.
  intros bs o L Ho HL H. unfold sub. rewrite length_firstn, length_skipn. lia.
Qed.

Lemma sub_nth : forall bs o L i (d : byte),
  0 <= o -> 0 <= i < L -> nth (Z.to_nat i) (sub bs o L) d = nth (Z.to_nat (o + i)) bs d.
Proof.
  intros bs o L i d Ho Hi. unfold sub.
  rewrite nth_firstn. replace (Z.to_nat i <? Z.to_nat L)%nat with true by (symmetry; apply Nat.ltb_lt; lia).
  rewrite nth_skipn. f_equal. lia.
Qed.

Section WithSegs.
Variable segs : list Segment.

Lemma kblob_sub : forall E mem (e : expr) (buf data : word) len bs o L k,
  edenot E e = buf -> eb E k = sub bs o L ->
  data_ok mem data len bs -> o = bv_unsigned buf - bv_unsigned data -> 0 <= o ->
  0 <= L -> bv_unsigned buf + L <= bv_unsigned data + len ->
  kentry_ok segs E mem (KBlob (SA e 0) (ELit L) k).
Proof.
  intros E mem e buf data len bs o L k He Hk (D1 & D2 & D3 & D4 & D5) Ho Ho0 HL Hhi.
  pose proof (u64_range buf). pose proof (u64_range data).
  assert (Hlen : Z.of_nat (length (sub bs o L)) = L) by (apply sub_length; lia).
  eapply (kblob_intro segs E mem e buf 0 (ELit L) k (sub bs o L) He Hk).
  - cbn [edenot]. rewrite u_small by lia. lia.
  - lia.
  - lia.
  - lia.
  - intros i Hi. rewrite Hlen in Hi. rewrite Z.add_0_r.
    replace (bv_unsigned buf + i) with (bv_unsigned data + (o + i)) by lia.
    rewrite (D5 (o + i)) by lia. f_equal. symmetry. apply sub_nth; lia.
Qed.

Lemma blob_val_sub_u8 : forall bs o L i,
  0 <= o -> 0 <= i < L -> o + L <= Z.of_nat (length bs) ->
  bv_unsigned (blob_val false (sub bs o L) i 1) = bs_byte bs (o + i).
Proof.
  intros bs o L i Ho Hi H.
  rewrite blob_val_u8; [| lia | rewrite (sub_length bs o L); lia].
  unfold bs_byte. rewrite sub_nth by lia. reflexivity.
Qed.

Lemma blob_val_sub_s8 : forall bs o L i,
  0 <= o -> 0 <= i < L -> o + L <= Z.of_nat (length bs) ->
  bv_unsigned (blob_val true (sub bs o L) i 1) = (bv_swrap 8 (bs_byte bs (o + i))) mod 2 ^ 64.
Proof.
  intros bs o L i Ho Hi H.
  rewrite blob_val_s8; [| lia | rewrite (sub_length bs o L); lia].
  unfold bs_byte. rewrite sub_nth by lia. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma blob_val_sub_u8w : forall bs o L i,
  0 <= o -> 0 <= i < L -> o + L <= Z.of_nat (length bs) ->
  blob_val false (sub bs o L) i 1 = Z_to_bv 64 (bs_byte bs (o + i)).
Proof.
  intros. rewrite <- (blob_val_sub_u8 bs o L i) by assumption. symmetry. apply Z_to_bv_bv_unsigned.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition cb (k : Z) : Z :=
  match k with 0 => 4 | 1 => 12 | 2 => 16 | 3 => 20 | _ => 28 end.

Lemma cb_range : forall k, 4 <= cb k <= 28.
Proof. intros k. unfold cb. destruct k as [|p|p]; try lia; destruct p as [p|p|]; try lia; destruct p; lia. Qed.

(* [comment removed for export] *)
Lemma u_sll32_srl31 : forall w : word,
  bv_unsigned (alu64 ALU_SRL (alu64 ALU_SLL w (Z_to_bv 64 32)) (Z_to_bv 64 31)) = 2 * (bv_unsigned w mod 2 ^ 32).
Proof.
  intros w. rewrite u_srl64, u_sll64. rewrite !u_small by lia.
  change (32 mod 64) with 32. change (31 mod 64) with 31.
  pose proof (u64_range w). lia.
Qed.

(* [comment removed for export] *)
Lemma u_mul32_srl31 : forall w : word,
  bv_unsigned (alu64 ALU_SRL (mul_div M_MUL (Z_to_bv 64 4294967296) w) (Z_to_bv 64 31)) = 2 * (bv_unsigned w mod 2 ^ 32).
Proof.
  intros w. rewrite u_srl64, u_mul64. rewrite !u_small by lia.
  change (31 mod 64) with 31.
  pose proof (u64_range w). lia.
Qed.

(* [comment removed for export] *)
Lemma u_sll32_srl32 : forall w : word,
  bv_unsigned (alu64 ALU_SRL (alu64 ALU_SLL w (Z_to_bv 64 32)) (Z_to_bv 64 32)) = bv_unsigned w mod 2 ^ 32.
Proof.
  intros w. rewrite u_srl64, u_sll64. rewrite !u_small by lia.
  change (32 mod 64) with 32.
  pose proof (u64_range w). lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma curve_ok_zero4 : forall mem data len c (a b cc d : word),
  0 <= c -> c + 32 <= 2 ^ 64 ->
  cell segs mem c 4 (Z_to_bv 64 0) ->
  cell segs mem (c + 8) 4 a -> cell segs mem (c + 12) 4 b ->
  cell segs mem (c + 16) 4 cc -> cell segs mem (c + 20) 4 d ->
  curve_ok segs mem data len c.
Proof.
  intros mem data len c a b cc d Hc0 Hc32 H0 Ha Hb Hcc Hd. unfold cell in *.
  assert (R8 : rdn segs mem (Z_to_bv 64 (c + 8)) (4 + 4) = Some (word_to_le_bytes 4 a ++ word_to_le_bytes 4 b)).
  { apply rdn_app; [exact Ha|]. rewrite u_small by lia. replace (c + 8 + Z.of_nat 4) with (c + 12) by lia. exact Hb. }
  assert (R16 : rdn segs mem (Z_to_bv 64 (c + 16)) (4 + 4) = Some (word_to_le_bytes 4 cc ++ word_to_le_bytes 4 d)).
  { apply rdn_app; [exact Hcc|]. rewrite u_small by lia. replace (c + 16 + Z.of_nat 4) with (c + 20) by lia. exact Hd. }
  destruct (cell_of_rdn segs mem (c + 8) 8 _ R8 ltac:(lia)) as [t8 Ht8].
  destruct (cell_of_rdn segs mem (c + 16) 8 _ R16 ltac:(lia)) as [t16 Ht16].
  exists 0, t8, t16. split; [split; [lia | exact H0]|]. split; [exact Ht8|]. split; [exact Ht16|]. left. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma curve_ok_zero8 : forall mem data len c (t8 t16 : word),
  cell segs mem c 4 (Z_to_bv 64 0) -> cell64 segs mem (c + 8) t8 -> cell64 segs mem (c + 16) t16 ->
  curve_ok segs mem data len c.
Proof.
  intros mem data len c t8 t16 H0 H8 H16.
  exists 0, t8, t16. split; [split; [lia | exact H0]|]. split; [exact H8|]. split; [exact H16|]. left. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma curve_ok_table16 : forall mem data len c n (t16 : word),
  cell32 segs mem c n -> cell64 segs mem (c + 8) (Z_to_bv 64 0) -> cell64 segs mem (c + 16) t16 ->
  2 <= n <= 2 ^ 24 -> bv_unsigned t16 <> 0 -> inDATA data len (bv_unsigned t16) (2 * n) ->
  curve_ok segs mem data len c.
Proof.
  intros mem data len c n t16 Hn H8 H16 Hr Ht Hin.
  exists n, (Z_to_bv 64 0), t16. split; [exact Hn|]. split; [exact H8|]. split; [exact H16|].
  right. split; [lia|]. change (bv_unsigned (Z_to_bv 64 0)) with 0.
  split; [right; exact Ht|]. split; [intros; lia|]. intros _. exact Hin.
Qed.

(* [comment removed for export] *)
Lemma cell32_of_cell4 : forall mem a (w : word),
  cell segs mem a 4 w -> exists v, cell32 segs mem a v.
Proof. intros mem a w H. eexists. apply cell32_of_word. exact H. Qed.

End WithSegs.
