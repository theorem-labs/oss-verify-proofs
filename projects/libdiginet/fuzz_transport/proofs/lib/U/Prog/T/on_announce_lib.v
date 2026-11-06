(* Machine-side helpers of the ubsan walk of on_announce (on_announce.v and its segment files): byte spans of the
   frame struct and the announce, the entry facts carried to a callee, the DESK and FOREIGN notices read as
   TContract's ntc_at, the post of on_announce_contract, the branch conditions and the session's own stores. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require ZBridge.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.U Require Import Img0.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require Import DgnSpec.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require Import TWorld TWorldLemmas TImg TWorldMem TSess0 TCb TSess.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.U.Prog Require Import diginet_announce_parse_c.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.U.Prog Require codec_cells.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.U.Prog.T Require Import WMem TContract TSessC on_announce_model.
Import ListNotations.
Open Scope Z_scope.

(* ---- byte spans ---- *)

Lemma bytes_at_sub : forall m a bs k n, bytes_at rsegs m a bs -> (k + n <= length bs)%nat ->
  bytes_at rsegs m (a + Z.of_nat k) (firstn n (skipn k bs)).
Proof.
  intros m a bs k n (Ha & Hl & H) Hk.
  assert (LF : length (firstn n (skipn k bs)) = n) by (rewrite length_firstn, length_skipn; lia).
  split; [lia|]. split; [rewrite LF; lia|].
  intros i Hi. rewrite LF in Hi.
  rewrite nth_error_firstn. replace (i <? n)%nat with true by (symmetry; apply Nat.ltb_lt; lia).
  rewrite nth_skipn. replace (a + Z.of_nat k + Z.of_nat i) with (a + Z.of_nat (k + i)) by lia.
  apply H. lia.
Qed.

Lemma bytes_at_firstn : forall m a bs n, bytes_at rsegs m a bs -> (n <= length bs)%nat ->
  bytes_at rsegs m a (firstn n bs).
Proof.
  intros m a bs n H Hn. pose proof (bytes_at_sub m a bs 0 n H ltac:(lia)) as R.
  rewrite Z.add_0_r in R. exact R.
Qed.

Lemma rw_cells_bytes : forall m A cs, rw_cells rsegs m A cs -> bytes_at rsegs m A (cells_bytes cs).
Proof. intros m A cs [[_ Hb] _]. exact Hb. Qed.

(* the bytes of the cell at offset k of a cell list *)
Lemma rw_cells_cell_bytes : forall m A cs k c, rw_cells rsegs m A cs -> cell_at cs k = Some c ->
  bytes_at rsegs m (A + Z.of_nat k) (cbytes c).
Proof.
  intros m A cs k c [[WF HB] _] HC.
  destruct (cell_at_split cs k c c HC) as (pre & post & -> & Hsz & _).
  rewrite cells_bytes_app in HB. cbn [cells_bytes] in HB.
  apply (proj1 (bytes_at_app rsegs m A _ _)) in HB. destruct HB as [_ HB].
  apply (proj1 (bytes_at_app rsegs m _ _ _)) in HB. destruct HB as [HB _].
  apply cells_wf_app in WF. destruct WF as [WF1 _].
  rewrite cells_bytes_length in HB by exact WF1. rewrite Hsz in HB. exact HB.
Qed.

(* ---- the frame struct diginet_frame f (TSessC.v dframe_cells): the bytes diginet_announce_parse reads ---- *)

Lemma dframe_cmd : forall m fp buf b fj, rw_cells rsegs m fp (dframe_cells buf b fj) ->
  bytes_at rsegs m (fp + 30) [b8 (fr_cmd b)].
Proof.
  intros m fp buf b fj H.
  exact (rw_cells_cell_bytes m fp _ 30 (C1 (b8 (fr_cmd b))) H ltac:(cells_cbv; reflexivity)).
Qed.

Lemma dframe_body : forall m fp buf b fj, rw_cells rsegs m fp (dframe_cells buf b fj) ->
  bytes_at rsegs m (fp + 32) (le8 (Z_to_bv 64 (buf + 30)) ++ le8 (Z_to_bv 64 (fr_body_len b))).
Proof.
  intros m fp buf b fj H.
  pose proof (rw_cells_cell_bytes m fp _ 32 (C8 (Z_to_bv 64 (buf + 30))) H ltac:(cells_cbv; reflexivity)) as H1.
  pose proof (rw_cells_cell_bytes m fp _ 40 (C8 (Z_to_bv 64 (fr_body_len b))) H ltac:(cells_cbv; reflexivity)) as H2.
  cbn [cbytes] in H1, H2.
  apply (proj2 (bytes_at_app rsegs m _ _ _)). split; [exact H1|].
  rewrite length_le8. replace (fp + 32 + Z.of_nat 8) with (fp + Z.of_nat 40) by lia. exact H2.
Qed.

(* the body bytes of the frame b at buf *)
Lemma frame_body_at : forall m buf b, fr_code b = 0 -> bytes_at rsegs m buf b ->
  bytes_at rsegs m (buf + 30) (fr_body b).
Proof.
  intros m buf b C H. pose proof (fr_code_ok b C) as (L30 & _ & N16 & NL).
  pose proof (bytes_at_sub m buf b 30 (Z.to_nat (fr_body_len b)) H) as R.
  unfold fr_body. apply R. unfold fr_body_len. lia.
Qed.

Lemma len_fr_body : forall b, fr_code b = 0 -> Z.of_nat (length (fr_body b)) = fr_body_len b.
Proof.
  intros b C. rewrite length_fr_body by exact C. pose proof (fr_body_len_ok b C) as (H & _). lia.
Qed.

(* ---- branch conditions ---- *)

Lemma oa_eqb0 : forall v, -2^63 <= v < 2^63 -> bv_eqb (Z_to_bv 64 v) (Z_to_bv 64 0) = (v =? 0).
Proof.
  intros v Hv. unfold bv_eqb. rewrite !unsigned_lit_wrap. change (0 mod 2^64) with 0.
  destruct (Z.eqb_spec v 0) as [->|N]; [reflexivity|].
  apply Z.eqb_neq. intros E. apply Z.mod_divide in E; [|lia]. destruct E as [c Ec]. nia.
Qed.

Lemma ann_code_range : forall cmd blen, -9 <= ann_code cmd blen <= 0.
Proof. intros. unfold ann_code. destruct (negb _); [lia|]. destruct (blen <? 33); lia. Qed.

(* the UBSan alignment checks of s = &g_s and of f: andi a0, s0, 7 / andi a0, s2, 7, then bnez to the trap *)
Lemma gs_land7 : Z.land (bv_unsigned (Z_to_bv 64 (W_BASE_UBSAN + OFF_g_s))) 7 = 0.
Proof. vm_compute. reflexivity. Qed.

Lemma fp_land7 : forall fp, 0 <= fp < 2^64 -> fp mod 8 = 0 -> Z.land (bv_unsigned (Z_to_bv 64 fp)) 7 = 0.
Proof.
  intros fp Hf H8. rewrite unsigned_lit by lia. change 7 with (Z.ones 3). rewrite Z.land_ones by lia.
  exact H8.
Qed.

(* ---- the entry facts carried to a callee: the heap frame and the RELRO tables lie off the footprint ---- *)

Lemma tframe_at_move : forall m0 m (sp sp' : word) K TF,
  tframe_at m0 sp 1056 TF ->
  munch [(bv_unsigned sp - 1056, bv_unsigned sp); (W_BASE_UBSAN, W_BASE_UBSAN + W_LEN)] m0 m ->
  bv_unsigned sp - 1056 <= bv_unsigned sp' - K -> bv_unsigned sp' <= bv_unsigned sp ->
  tframe_at m sp' K TF.
Proof.
  intros m0 m sp sp' K TF T MU H1 H2. destruct TF as [fr|]; [|exact I].
  unfold tframe_at in *. destruct T as (P & BA & OW & OWin). unfold off_world, off_window in *.
  refine (conj P (conj _ (conj OW _))); [| lia].
  eapply bytes_at_transport; [exact BA | exact MU |]. cbn [disjoint_from].
  refine (conj _ (conj _ I)); lia.
Qed.

Lemma relro_img_move : forall m0 m (sp : word),
  relro_img m0 ->
  munch [(bv_unsigned sp - 1056, bv_unsigned sp); (W_BASE_UBSAN, W_BASE_UBSAN + W_LEN)] m0 m ->
  W_BASE_UBSAN + W_LEN <= bv_unsigned sp - 1056 -> relro_img m.
Proof.
  intros m0 m sp R MU H i Hi. unfold mrd. rewrite (MU (wa (RELRO_BASE + i))); [exact (R i Hi) |].
  unfold RELRO_BASE, RELRO_LEN in *. cbn [outside]. rewrite wa_unsigned by lia.
  unfold W_BASE_UBSAN, W_LEN in *. refine (conj _ (conj _ I)); lia.
Qed.

(* diginet_personality_from_name's contract states the RELRO tables with codec_cells' copy of the same definition *)
Lemma relro_codec : forall m, relro_img m -> codec_cells.relro_img m.
Proof. intros m R i Hi. exact (R i Hi). Qed.

(* ---- the local struct diginet_announce a after diginet_announce_parse (ann_cells): what the notices point at ---- *)

Lemma ann_field_prefix : forall src old, length old = 10%nat ->
  firstn (S (copy_len 10 9 src)) (copy_strz 10 9 src old) = ann_field src.
Proof.
  intros src old Lo. unfold ann_field, copy_strz.
  assert (K : (copy_len 10 9 src <= length src)%nat).
  { unfold copy_len. pose proof (nz_run_le (firstn (Nat.min 9 (10 - 1)) src)) as H.
    rewrite length_firstn in H. lia. }
  rewrite firstn_app. rewrite firstn_firstn. rewrite length_firstn.
  replace (Nat.min (S (copy_len 10 9 src)) (copy_len 10 9 src)) with (copy_len 10 9 src) by lia.
  replace (S (copy_len 10 9 src) - Nat.min (copy_len 10 9 src) (length src))%nat with 1%nat by lia.
  reflexivity.
Qed.

Lemma copy_strz_len : forall src old, length old = 10%nat ->
  (S (copy_len 10 9 src) <= length (copy_strz 10 9 src old))%nat.
Proof.
  intros src old Lo. unfold copy_strz. rewrite length_app, length_firstn. cbn [length].
  assert (K : (copy_len 10 9 src <= length src)%nat).
  { unfold copy_len. pose proof (nz_run_le (firstn (Nat.min 9 (10 - 1)) src)) as H.
    rewrite length_firstn in H. lia. }
  lia.
Qed.

Lemma ann_cells_ann : forall m A body bb aj, length aj = 40%nat ->
  rw_cells rsegs m A (ann_cells body bb aj) ->
  bytes_at rsegs m A (ta_version (TAnn (ann_field (skipn 15 bb)) (ann_field (skipn 24 bb)))) /\
  bytes_at rsegs m (A + 10) (ta_name (TAnn (ann_field (skipn 15 bb)) (ann_field (skipn 24 bb)))).
Proof.
  intros m A body bb aj La H. cbn [ta_version ta_name].
  pose proof (rw_cells_cell_bytes m A _ 0 _ H ltac:(cells_cbv; reflexivity)) as V.
  pose proof (rw_cells_cell_bytes m A _ 10 _ H ltac:(cells_cbv; reflexivity)) as N.
  cbn [cbytes] in V, N. rewrite Z.add_0_r in V.
  assert (L1 : length (firstn 10 aj) = 10%nat) by (rewrite length_firstn; lia).
  assert (L2 : length (firstn 10 (skipn 10 aj)) = 10%nat) by (rewrite length_firstn, length_skipn; lia).
  split.
  - unfold ann_version in V. rewrite <- (ann_field_prefix (skipn 15 bb) (firstn 10 aj) L1).
    apply bytes_at_firstn; [exact V | apply copy_strz_len; exact L1].
  - unfold ann_name in N. rewrite <- (ann_field_prefix (skipn 24 bb) (firstn 10 (skipn 10 aj)) L2).
    apply bytes_at_firstn; [exact N | apply copy_strz_len; exact L2].
Qed.

(* ---- reading a struct diginet_notice the walk built field by field (TContract.v ntc_at) ---- *)

Lemma u_at_app_l : forall (l1 l2 : list byte) k n, 0 <= k -> k + Z.of_nat n <= Z.of_nat (length l1) ->
  u_at (l1 ++ l2) k n = u_at l1 k n.
Proof.
  intros l1 l2 k n Hk Hn. unfold u_at, sub. f_equal.
  rewrite skipn_app. replace (Z.to_nat k - length l1)%nat with 0%nat by lia. cbn [skipn].
  rewrite firstn_app. rewrite length_skipn. replace (n - (length l1 - Z.to_nat k))%nat with 0%nat by lia.
  cbn [firstn]. rewrite app_nil_r. reflexivity.
Qed.

Lemma u_at_app_r : forall (l1 l2 : list byte) k n, Z.of_nat (length l1) <= k ->
  u_at (l1 ++ l2) k n = u_at l2 (k - Z.of_nat (length l1)) n.
Proof.
  intros l1 l2 k n Hk. unfold u_at, sub. f_equal.
  rewrite skipn_app. rewrite skipn_all2 by lia. cbn [app].
  f_equal. f_equal. lia.
Qed.

Lemma u_at_put_n : forall n v k, k = 0 -> u_at (put n v) k n = v mod 2 ^ (8 * Z.of_nat n).
Proof. intros n v k ->. apply u_at_put. Qed.

Lemma swrap32_mod : forall v, - 2 ^ 31 <= v < 2 ^ 31 -> bv_swrap 32 (v mod 2 ^ 32) = v.
Proof.
  intros v Hv. unfold bv_swrap, bv_wrap. change (bv_half_modulus 32) with (2 ^ 31).
  change (bv_modulus 32) with (2 ^ 32). Z.div_mod_to_equations. lia.
Qed.

Lemma firstn_repeat_le : forall (x : byte) j n, (j <= n)%nat -> firstn j (repeat x n) = repeat x j.
Proof. induction j as [|j IH]; intros n H; [reflexivity |]. destruct n as [|n]; [lia |]. cbn. f_equal. apply IH. lia. Qed.

Lemma skipn_repeat_sub : forall (x : byte) k n, skipn k (repeat x n) = repeat x (n - k).
Proof.
  induction k as [|k IH]; intros n; [cbn [skipn]; rewrite Nat.sub_0_r; reflexivity |].
  destruct n as [|n]; [reflexivity |]. cbn. apply IH.
Qed.

Lemma ble_zeros : forall j, bytes_le_to_Z (repeat (Z_to_bv 8 0) j) = 0.
Proof.
  intros j. rewrite bytes_le_to_Z_le_val. induction j as [|j IH]; [reflexivity |].
  cbn [repeat map le_val]. rewrite IH. reflexivity.
Qed.

Lemma u_at_zeros : forall n k j, 0 <= k -> k + Z.of_nat j <= Z.of_nat n -> u_at (repeat (Z_to_bv 8 0) n) k j = 0.
Proof.
  intros n k j Hk Hj. unfold u_at, sub. rewrite skipn_repeat_sub, firstn_repeat_le by lia. apply ble_zeros.
Qed.

Ltac ntc_norm := rewrite ?length_app, ?length_put, ?repeat_length.
Ltac ntc_field :=
  repeat (rewrite u_at_app_r by (ntc_norm; cbn; lia); ntc_norm);
  first [ rewrite u_at_zeros by (ntc_norm; cbn; lia)
        | rewrite u_at_app_l by (ntc_norm; cbn; lia); ntc_norm;
          first [ rewrite u_at_zeros by (cbn; lia) | rewrite u_at_put_n by (cbn; lia) | idtac ]
        | rewrite u_at_put_n by (cbn; lia)
        | idtac ];
  try reflexivity.

(* the DESK notice of :196-197 as the binary writes it at sp + 88: kind 1, state, old and reason 0 (one sd zero),
   the frame f, the announce a, the personality pv, mac_offset off, then 28 bytes of memset 0 *)
Definition desk_nb (st fpz apz pv off : Z) : list byte :=
  put 4 1 ++ put 4 st ++ put 8 0 ++ put 8 fpz ++ put 8 apz ++ put 8 pv ++ put 4 off ++ repeat (Z_to_bv 8 0) 28.

(* the FOREIGN notice of :217 at sp + 16: kind 6, state, old and reason 0, f, a, then 40 bytes of memset 0 *)
Definition foreign_nb (st fpz apz : Z) : list byte :=
  put 4 6 ++ put 4 st ++ put 8 0 ++ put 8 fpz ++ put 8 apz ++ repeat (Z_to_bv 8 0) 40.

Lemma ntc_desk_at : forall m p (sp : word) K st fpz apz pv off a,
  bytes_at rsegs m p (desk_nb st fpz apz pv off) ->
  0 < p -> p mod 8 = 0 -> off_world p 72 -> off_window sp K p 72 -> 0 <= bv_unsigned sp - K ->
  - 2 ^ 31 <= st < 2 ^ 31 -> 0 <= pv < 2 ^ 64 -> - 2 ^ 31 <= off < 2 ^ 31 ->
  0 < apz < 2 ^ 64 -> apz mod 8 = 0 ->
  bytes_at rsegs m apz (ta_version a) -> bytes_at rsegs m (apz + 10) (ta_name a) ->
  off_world apz 20 -> off_window sp K apz 20 ->
  ntc_at m p (Ntc DIGINET_N_DESK st 0 0 0 0 off pv (Some a) [] 0) sp K.
Proof.
  intros m p sp K st fpz apz pv off a BA P0 P8 OW OWin SK Hst Hpv Hoff Ha Ha8 AV AN AOW AOWin.
  unfold ntc_at. refine (conj P0 (conj P8 (conj OW (conj OWin _)))).
  exists (desk_nb st fpz apz pv off). unfold desk_nb, s32_at.
  cbn [n_kind n_state n_old n_reason n_pers n_mac_offset n_body_len n_counter n_retry n_body n_ann length].
  assert (Z48 : u_at (put 4 1 ++ put 4 st ++ put 8 0 ++ put 8 fpz ++ put 8 apz ++ put 8 pv ++ put 4 off
                      ++ repeat (Z_to_bv 8 0) 28) 48 8 = 0) by ntc_field.
  assert (Z24 : u_at (put 4 1 ++ put 4 st ++ put 8 0 ++ put 8 fpz ++ put 8 apz ++ put 8 pv ++ put 4 off
                      ++ repeat (Z_to_bv 8 0) 28) 24 8 = apz) by (ntc_field; apply Z.mod_small; cbn; lia).
  rewrite Z48, Z24.
  split; [exact BA |].
  split; [ntc_norm; reflexivity |].
  split; [ntc_field |].
  split; [ntc_field; apply swrap32_mod; exact Hst |].
  split; [ntc_field |].
  split; [ntc_field |].
  split; [ntc_field; apply Z.mod_small; cbn; lia |].
  split; [ntc_field; apply swrap32_mod; exact Hoff |].
  split; [ntc_field |].
  split; [ntc_field |].
  split; [ntc_field |].
  split; [apply bytes_at_nil; lia |].
  split; [unfold off_world, W_BASE_UBSAN; cbn; lia |].
  split; [unfold off_window; cbn; lia |].
  refine (conj _ (conj Ha8 (conj AV (conj AN (conj AOW AOWin))))). lia.
Qed.

Lemma ntc_foreign_at : forall m p (sp : word) K st fpz apz a,
  bytes_at rsegs m p (foreign_nb st fpz apz) ->
  0 < p -> p mod 8 = 0 -> off_world p 72 -> off_window sp K p 72 -> 0 <= bv_unsigned sp - K ->
  - 2 ^ 31 <= st < 2 ^ 31 ->
  0 < apz < 2 ^ 64 -> apz mod 8 = 0 ->
  bytes_at rsegs m apz (ta_version a) -> bytes_at rsegs m (apz + 10) (ta_name a) ->
  off_world apz 20 -> off_window sp K apz 20 ->
  ntc_at m p (Ntc DIGINET_N_FOREIGN st 0 0 0 0 0 0 (Some a) [] 0) sp K.
Proof.
  intros m p sp K st fpz apz a BA P0 P8 OW OWin SK Hst Ha Ha8 AV AN AOW AOWin.
  unfold ntc_at. refine (conj P0 (conj P8 (conj OW (conj OWin _)))).
  exists (foreign_nb st fpz apz). unfold foreign_nb, s32_at.
  cbn [n_kind n_state n_old n_reason n_pers n_mac_offset n_body_len n_counter n_retry n_body n_ann length].
  assert (Z48 : u_at (put 4 6 ++ put 4 st ++ put 8 0 ++ put 8 fpz ++ put 8 apz ++ repeat (Z_to_bv 8 0) 40) 48 8 = 0)
    by ntc_field.
  assert (Z24 : u_at (put 4 6 ++ put 4 st ++ put 8 0 ++ put 8 fpz ++ put 8 apz ++ repeat (Z_to_bv 8 0) 40) 24 8 = apz)
    by (ntc_field; apply Z.mod_small; cbn; lia).
  rewrite Z48, Z24.
  split; [exact BA |].
  split; [ntc_norm; reflexivity |].
  split; [ntc_field |].
  split; [ntc_field; apply swrap32_mod; exact Hst |].
  split; [ntc_field |].
  split; [ntc_field |].
  split; [ntc_field |].
  split; [ntc_field |].
  split; [ntc_field |].
  split; [ntc_field |].
  split; [ntc_field |].
  split; [apply bytes_at_nil; lia |].
  split; [unfold off_world, W_BASE_UBSAN; cbn; lia |].
  split; [unfold off_window; cbn; lia |].
  refine (conj _ (conj Ha8 (conj AV (conj AN (conj AOW AOWin))))). lia.
Qed.

(* ---- the postcondition of on_announce_contract (on_announce_c.v), for the segment lemmas ---- *)

Definition oa_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (m : word -> option byte) (lo : Z) (B' : list byte) : machine_state -> Prop :=
  fun ms' => exists (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word)
                    (m' : word -> option byte),
    ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7'
                  s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
             F (ret_pc ra) fc None m' (seg_rom rsegs) /\
    munch [(bv_unsigned sp - 1056, bv_unsigned sp); (W_BASE_UBSAN, W_BASE_UBSAN + W_LEN)] m m' /\
    wmono rsegs m m' /\ mem_inv rsegs m' /\ stk rsegs m' lo (bv_unsigned sp) /\
    wmem rsegs m' B' /\ g_fail_next B' <= 1.

(* ---- more branch conditions and the session's own stores ---- *)

Lemma oa_eqbk : forall v k, -2^63 <= v < 2^63 -> -2^63 <= k < 2^63 ->
  bv_eqb (Z_to_bv 64 v) (Z_to_bv 64 k) = (v =? k).
Proof.
  intros v k Hv Hk. unfold bv_eqb. rewrite !unsigned_lit_wrap.
  destruct (Z.eqb_spec v k) as [->|N]; [apply Z.eqb_refl|].
  apply Z.eqb_neq. intros E.
  assert (D : (v - k) mod 2^64 = 0) by (rewrite Zminus_mod, E, Z.sub_diag; reflexivity).
  apply Z.mod_divide in D; [|lia]. destruct D as [c Ec]. nia.
Qed.

(* a store of the session below g_fail_next keeps it *)
Lemma gfn_upd : forall B k v, length B = Z.to_nat W_LEN -> 0 <= k ->
  k + Z.of_nat (length v) <= OFF_g_fail_next -> g_fail_next (upd B k v) = g_fail_next B.
Proof.
  intros B k v L Hk Hl. unfold g_fail_next. apply u_at_upd_out; unfold OFF_g_fail_next, W_LEN in *; try lia.
Qed.

Lemma oa_ltz : forall v, -2^63 <= v < 2^63 -> bv_lts (Z_to_bv 64 v) (Z_to_bv 64 0) = (v <? 0).
Proof.
  intros v Hv. rewrite ZBridge.bv_lts_zero_r. rewrite unsigned_lit_wrap.
  destruct (Z.ltb_spec v 0) as [H|H]; [apply Z.leb_le | apply Z.leb_gt]; Z.div_mod_to_equations; lia.
Qed.

(* :219 as the binary tests it: addiw a0, a0, -1 on the sign-extended state, then bltu 1, a0 *)
Lemma oa_state_test : forall st, -2^31 <= st < 2^31 ->
  bv_ltu (Z_to_bv 64 1) (Z_to_bv 64 (bv_swrap 32 (bv_unsigned (Z_to_bv 64 st) + -1))) =
  negb ((st =? 2) || (st =? 1)).
Proof.
  intros st Hst.
  destruct (Z.eqb_spec st 2) as [->|N2]; [reflexivity|].
  destruct (Z.eqb_spec st 1) as [->|N1]; [reflexivity|].
  cbn [orb negb]. unfold bv_ltu. rewrite !unsigned_lit_wrap. unfold bv_swrap, bv_wrap.
  change (bv_half_modulus 32) with (2^31). change (bv_modulus 32) with (2^32).
  apply Z.ltb_lt. Z.div_mod_to_equations. lia.
Qed.

(* lbu of the byte b8 v *)
Lemma b8_unsigned : forall v, 0 <= v < 2^8 -> bv_unsigned (b8 v) = v.
Proof. intros v Hv. exact (bz_b8 v Hv). Qed.

Lemma zxb_b8 : forall v, 0 <= v < 2^8 -> zxb (b8 v) = Z_to_bv 64 v.
Proof. intros v Hv. unfold zxb. rewrite b8_unsigned by exact Hv. reflexivity. Qed.

(* find_mac's loop test of a.unknown + i against NULL (s11 = a.unknown != NULL, s10 = a.unknown + i) *)
Lemma loop_nn : forall r10 r11 : word, bv_unsigned r11 = 1 -> 1 <= bv_unsigned r10 ->
  Z.lxor (bv_unsigned r11) (bv_unsigned (v_sltiu r10 1)) = 1.
Proof.
  intros r10 r11 H11 H10. unfold v_sltiu. rewrite H11.
  replace (bv_unsigned r10 <? bv_wrap 64 1) with false by (symmetry; apply Z.ltb_ge; change (bv_wrap 64 1) with 1; lia).
  reflexivity.
Qed.

Lemma word_of_unsigned : forall (r : word) v, bv_unsigned r = v -> r = Z_to_bv 64 v.
Proof. intros r v <-. symmetry. apply Z_to_bv_lit_self. Qed.

Lemma bytes_at_skipn : forall m a bs k, bytes_at rsegs m a bs -> (k <= length bs)%nat ->
  bytes_at rsegs m (a + Z.of_nat k) (skipn k bs).
Proof.
  intros m a bs k H Hk. pose proof (bytes_at_sub m a bs k (length bs - k) H ltac:(lia)) as R.
  rewrite firstn_all2 in R by (rewrite length_skipn; lia). exact R.
Qed.

Lemma swrap32_small : forall z, 0 <= z < 2^31 -> bv_swrap 32 z = z.
Proof.
  intros z Hz. unfold bv_swrap, bv_wrap. change (bv_half_modulus 32) with (2^31). change (bv_modulus 32) with (2^32).
  rewrite Z.mod_small by lia. lia.
Qed.

Lemma ann_code_ok : forall cmd blen, ann_code cmd blen = 0 -> 33 <= blen /\ (cmd = 0xe0 \/ cmd = 0xe1).
Proof.
  intros cmd blen H. unfold ann_code, ann_cmd in H.
  destruct ((cmd =? 0xe0) || (cmd =? 0xe1)) eqn:E; cbn [negb] in H; [|discriminate H].
  destruct (blen <? 33) eqn:E2; [discriminate H|].
  split; [apply Z.ltb_ge; exact E2|].
  apply orb_true_iff in E. destruct E as [E|E]; [left|right]; apply Z.eqb_eq; exact E.
Qed.

(* snez s11, s1 on a nonzero pointer *)
Lemma snez_pos : forall v, 0 < v < 2^64 -> bv_unsigned (v_sltu (Z_to_bv 64 0) (Z_to_bv 64 v)) = 1.
Proof.
  intros v Hv. unfold v_sltu, c_ltu, bv_ltu. rewrite (unsigned_lit v) by lia.
  change (bv_unsigned (Z_to_bv 64 0)) with 0.
  replace (0 <? v) with true by (symmetry; apply Z.ltb_lt; lia). reflexivity.
Qed.

(* a hypothesis whose type is the goal, matched syntactically: eassumption's unification against every hypothesis
   of a large context is slow (minutes for a segment lemma's 50 premises) *)
Ltac sassump := match goal with H : ?G |- ?G => exact H end.

(* reflexivity only where it is cheap: an equation of words or of cell-list sizes, never a model equation *)
Ltac oa_refl :=
  lazymatch goal with
  | |- @eq (bv 64) _ _ => reflexivity
  | |- @eq nat (cells_size _) _ => reflexivity
  | |- @eq Z (bv_unsigned (Z_to_bv 64 ?x)) _ => first [ (rewrite unsigned_lit by lia; lia) | reflexivity ]
  end.

Lemma len_upd_W : forall B k v, length B = Z.to_nat W_LEN -> 0 <= k -> k + Z.of_nat (length v) <= W_LEN ->
  length (upd B k v) = Z.to_nat W_LEN.
Proof. intros B k v L Hk Hl. rewrite length_upd; [exact L | exact Hk | rewrite L; unfold W_LEN in *; lia]. Qed.

Lemma s32_upd_W : forall B k v k', length B = Z.to_nat W_LEN -> 0 <= k -> k + Z.of_nat (length v) <= W_LEN ->
  0 <= k' -> (k' + 4 <= k \/ k + Z.of_nat (length v) <= k') -> s32_at (upd B k v) k' = s32_at B k'.
Proof. intros. apply s32_at_upd_out; try assumption. rewrite H. unfold W_LEN in *. lia. Qed.

Lemma u_upd_W : forall B k v k' n, length B = Z.to_nat W_LEN -> 0 <= k -> k + Z.of_nat (length v) <= W_LEN ->
  0 <= k' -> (k' + Z.of_nat n <= k \/ k + Z.of_nat (length v) <= k') -> u_at (upd B k v) k' n = u_at B k' n.
Proof. intros. apply u_at_upd_out; try assumption. rewrite H. unfold W_LEN in *. lia. Qed.

Lemma upd_comm_W : forall B v w k k', length B = Z.to_nat W_LEN -> 0 <= k -> 0 <= k' ->
  k + Z.of_nat (length v) <= W_LEN -> k' + Z.of_nat (length w) <= W_LEN ->
  (k' + Z.of_nat (length w) <= k \/ k + Z.of_nat (length v) <= k') ->
  upd (upd B k v) k' w = upd (upd B k' w) k v.
Proof. intros. apply upd_upd_comm; try assumption; rewrite H; unfold W_LEN in *; lia. Qed.

(* side goals of the lemmas above: a closed numeric comparison over the TWorld offsets, or the length of a world
   built by upd from one of W_LEN bytes *)
Ltac wnum := rewrite ?length_put;
  cbv [W_LEN OFF_g_fail_next OFF_g_s A_S_state A_S_foreign A_S_e1_named_us A_S_inflight A_S_desk_counter_valid
       A_S_personality A_S_stats_rx_ignored A_S_cfg_auto_wake A_S_notify];
  lia.
Ltac wlen := first [ assumption | (apply len_upd_W; [ wlen | wnum | wnum ]) ].
Ltac wside := first [ wlen | wnum ].
