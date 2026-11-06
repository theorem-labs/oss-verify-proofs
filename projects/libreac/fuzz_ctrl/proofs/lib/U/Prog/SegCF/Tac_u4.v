(* Helpers for the segment lemmas of batch u4 (F01-F10) of fuzz_ctrl LLVMFuzzerTestOneInput (ubsan), ported from
   the plain batch b5 helpers (lib/Prog/Seg/Tac_b5.v): the frame-loop model facts (Φ's length,
   ID_j and FG_j lengths, Φ's first 50 bytes), u4_mid (sl_mid with a fixed write set W whose munch over the
   unnormalized memory reaches the continuation), Φ's heap bound, and the transport of the turn-j bundles (FB, IFS
   and their parts) across a run that keeps s0-s11 and writes only in W.
   libreac v1.9.0 stack offsets (a Theorem Labs lane's ubsan table, sections 6a / 7a (a working note, not in this delivery)): the -7 pair (M7) sp+8, TF sp+16,
   left - h sp+24, `first` (FS) sp+36..76, ID sp+76, OUR sp+114, FG sp+120, B sp+1752. v1.9 loop registers: j in
   s1 (x9), s2 = 1 (x18), s0 = sp+128 = &frag + 8 (x8; set at 0x137b8, kept by every loop segment), body s5, len
   s6, Φ s7, Φ + 18 s8, k s9, is_8819 s3, sum_ok s11, big s4, rf s10. u4_LK_s2 / u4_LK_s0 are the only places that
   take s2 = 1 and s0 = sp+128 out of LK. *)
(* N.1b mis-bind audit of these 19 files (read-only, 2026-10-28):
   the lane's v190-U mis-bind audit - 98 sites, 0 mis-binds. lib/U has no
   a_call_post / a_laws* / amalloc_at family at all; u4_LK_s2 / u4_LK_s0 read LK by `decompose`, not by position. *)
From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.U.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.U.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.U.Reusable Require Import YL01 YL00 YL0g YI06 YI16 YI14.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.U.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import Mem Frame.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require MState Regs6ss RegisterBridge Exec Cells Step.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.U Require Import Img0 Contract FrameAPI.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.U.Prog Require Import SlotModel SlotInvCF.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require RcParse RcReply RcIdentModel RcFrag.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.U.Prog.SegCF Require Import Tac_slot Tac_u1.
Import ListNotations.
Open Scope Z_scope.

(* ---- Model facts of the frame loop ---- *)

Lemma u4_byte_nn : forall b : byte, 0 <= bv_unsigned b.
Proof. intros b. pose proof (bv_unsigned_in_range 8 b) as H. lia. Qed.

Lemma u4_fL_nn : forall inp c, 0 <= f_L inp c.
Proof.
  intros inp c. unfold f_L, inb, RcIdentModel.bz.
  pose proof (u4_byte_nn (RcIdentModel.nthb inp (Z.to_nat c))).
  pose proof (u4_byte_nn (RcIdentModel.nthb inp (Z.to_nat (c + 1)))).
  destruct (2 <=? f_left inp c); lia.
Qed.

Lemma u4_fc_range : forall inp j, 0 <= fc inp j <= nlen inp.
Proof.
  intros inp j. assert (Hn : 0 <= nlen inp) by (unfold nlen; lia).
  induction j as [|j IH]; cbn [fc].
  - unfold c0. lia.
  - pose proof (u4_fL_nn inp (fc inp j)). unfold f_next, f_body, f_len, f_h, f_left. lia.
Qed.

Lemma u4_len_range : forall inp j,
  0 <= t_len inp j /\ 0 <= t_body inp j /\ t_body inp j + t_len inp j <= nlen inp.
Proof.
  intros inp j. pose proof (u4_fc_range inp j). pose proof (u4_fL_nn inp (fc inp j)).
  unfold t_len, t_body, f_len, f_body, f_h, f_left. lia.
Qed.

Lemma u4_phi_len : forall inp j, length (t_phi inp j) = Z.to_nat (t_len inp j).
Proof.
  intros inp j. pose proof (u4_len_range inp j) as (H1 & H2 & H3).
  unfold t_phi, f_phi. fold (t_len inp j). fold (t_body inp j).
  rewrite length_firstn, length_skipn. unfold nlen in H3. lia.
Qed.

Lemma u4_tg_len : forall inp j, length (t_g inp j) = 50%nat.
Proof. intros inp j. apply fr50_length. Qed.

Lemma u4_tg_eq : forall inp j, 50 <= t_len inp j -> t_g inp j = firstn 50 (t_phi inp j).
Proof.
  intros inp j Hb. unfold t_g, fr50. rewrite firstn_app, u4_phi_len.
  replace (50 - Z.to_nat (t_len inp j))%nat with 0%nat by lia. cbn [firstn]. apply app_nil_r.
Qed.

Lemma u4_ba_prefix : forall m a bs k, bytes_at rsegs m a bs -> bytes_at rsegs m a (firstn k bs).
Proof.
  intros m a bs k H. rewrite <- (firstn_skipn k bs) in H. apply bytes_at_app in H. exact (proj1 H).
Qed.

Lemma u4_phi_g : forall m inp j phi, bytes_at rsegs m phi (t_phi inp j) -> 50 <= t_len inp j ->
  bytes_at rsegs m phi (t_g inp j).
Proof. intros m inp j phi H Hb. rewrite (u4_tg_eq inp j Hb). apply u4_ba_prefix. exact H. Qed.

Lemma u4_rpid_len : forall idb len g, length idb = 38%nat -> length (rp_id idb len g) = 38%nat.
Proof.
  intros idb len g H. unfold rp_id. destruct (RcReply.ir len g); [|exact H].
  apply RcIdentModel.ING_length. exact H.
Qed.

Lemma u4_fgid_len : forall idb len st g, length idb = 38%nat -> length (fg_id idb len st g) = 38%nat.
Proof.
  intros idb len st g H. unfold fg_id. destruct (fg_rf len st g =? 1); [|exact H].
  apply RcIdentModel.ING_length. exact H.
Qed.

Lemma u4_tID_len : forall inp j, length (t_ID inp j) = 38%nat.
Proof.
  intros inp j. unfold t_ID. induction j as [|j IH]; [reflexivity|].
  rewrite fst_at_S. unfold turn. cbv zeta.
  destruct (f_opens (t_len inp j) (t_g inp j)); cbn [fs_id];
    apply u4_fgid_len; apply u4_rpid_len; exact IH.
Qed.

Lemma u4_tIDr_len : forall inp j, length (t_IDr inp j) = 38%nat.
Proof. intros inp j. unfold t_IDr. apply u4_rpid_len. apply u4_tID_len. Qed.

Lemma u4_fgfr_n : forall len g, RcFrag.fg_fr len g = true -> 1 <= RcFrag.fg_n g <= 22.
Proof.
  intros len g H. unfold RcFrag.fg_fr in H.
  repeat (apply andb_true_iff in H; destruct H as [H ?]).
  repeat match goal with
  | E : (_ <=? _) = true |- _ => apply Z.leb_le in E
  end.
  lia.
Qed.

Lemma u4_bat_nn : forall bs i, 0 <= RcFrag.bat bs i.
Proof. intros bs i. unfold RcFrag.bat. apply u4_byte_nn. Qed.

Lemma u4_body_len : forall g, length g = 50%nat -> 1 <= RcFrag.fg_n g <= 22 ->
  length (RcFrag.fg_body g) = Z.to_nat (RcFrag.fg_n g).
Proof.
  intros g Hg Hn. unfold RcFrag.fg_body, RcFrag.bsl. rewrite length_firstn, length_skipn, Hg. lia.
Qed.

Lemma u4_clear_len : forall st, length st = 72%nat -> length (RcFrag.fg_clear st) = 72%nat.
Proof.
  intros st H. unfold RcFrag.fg_clear. rewrite !length_app, length_firstn, length_skipn, H. reflexivity.
Qed.

Lemma u4_fgst_len : forall len st g, length st = 72%nat -> length g = 50%nat -> length (fg_st len st g) = 72%nat.
Proof.
  intros len st g Hs Hg. unfold fg_st, fg_next, fcls, RcFrag.fg_class. cbn [Z.eqb orb].
  destruct (RcFrag.fg_fr len g) eqn:Efr; cbn [negb]; [|exact Hs].
  pose proof (u4_fgfr_n len g Efr) as Hn. pose proof (u4_body_len g Hg Hn) as Hb.
  destruct (RcFrag.bat g 19 =? 1); cbn [negb].
  - unfold RcFrag.fg_first, RcFrag.bsl.
    rewrite !length_app, !length_firstn, !length_skipn, Hb, Hs, Hg. cbn [length]. lia.
  - destruct (RcFrag.fg_keep st g) eqn:Ek; cbn [negb]; [|apply u4_clear_len; exact Hs].
    unfold RcFrag.fg_keep in Ek. apply andb_true_iff in Ek as [_ Ek]. apply Z.leb_le in Ek.
    pose proof (u4_bat_nn st 7) as H7. unfold RcFrag.fg_T, RcFrag.fg_lf in Ek.
    assert (Hj : length (RcFrag.fg_join st g) = 72%nat).
    { unfold RcFrag.fg_join, RcFrag.fg_T, RcFrag.fg_lf.
      rewrite !length_app, length_firstn, Hb, length_skipn, Hs. lia. }
    destruct (RcFrag.fg_close st g); cbn [negb]; apply u4_clear_len; exact Hj.
Qed.

Lemma u4_tFG_len : forall inp j, length (t_FG inp j) = 72%nat.
Proof.
  intros inp j. unfold t_FG. induction j as [|j IH]; [reflexivity|].
  rewrite fst_at_S. unfold turn. cbv zeta.
  destruct (f_opens (t_len inp j) (t_g inp j)); cbn [fs_fg];
    (apply u4_fgst_len; [exact IH | apply u4_tg_len]).
Qed.

Lemma u4_tFGf_len : forall inp j, length (t_FGf inp j) = 72%nat.
Proof. intros inp j. unfold t_FGf. apply u4_fgst_len; [apply u4_tFG_len | apply u4_tg_len]. Qed.

Lemma u4_k_range : forall inp j, 0 <= t_k inp j <= 13.
Proof. intros inp j. apply RcParse.ctrlparse_kind_range. Qed.

(* A small case split: a fact checked by computation at each of 0 .. 13. *)
Ltac u4_cases13 k :=
  let E := fresh "E" in
  assert (E : k = 0 \/ k = 1 \/ k = 2 \/ k = 3 \/ k = 4 \/ k = 5 \/ k = 6 \/ k = 7 \/ k = 8 \/ k = 9 \/
              k = 10 \/ k = 11 \/ k = 12 \/ k = 13) by lia;
  repeat match type of E with
  | _ \/ _ => destruct E as [E|E]; [subst k; vm_compute; reflexivity|]
  | _ => subst k; vm_compute; reflexivity
  end.

Lemma u4_le4_small : forall k, 0 <= k <= 13 ->
  [Z_to_bv 8 k; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0] = le4 (Z_to_bv 64 k).
Proof. intros k Hk. u4_cases13 k. Qed.

Lemma u4_tB_read : forall m a inp j, bytes_at rsegs m a (t_B inp j) ->
  ov_read_bytes rsegs m (wa a) 4 = Some (le4 (Z_to_bv 64 (t_k inp j))).
Proof.
  intros m a inp j H.
  assert (L : (0 + 4 <= length (t_B inp j))%nat) by (unfold t_B; rewrite RcParse.ctrlparse_length; lia).
  pose proof (bytes_at_ov_read rsegs m a _ 0 4 H L) as R.
  cbn [Z.of_nat skipn] in R. rewrite Z.add_0_r in R. rewrite R. f_equal.
  unfold t_B, t_k. cbv [skipn].
  rewrite RcParse.ctrlparse_kind_bytes. apply u4_le4_small. apply RcParse.ctrlparse_kind_range.
Qed.

(* ---- Input bytes ---- *)

Lemma u4_ld1 : forall m a b, bytes_at rsegs m a [b] -> ov_read_bytes rsegs m (wa a) 1 = Some [b].
Proof.
  intros m a b H. replace (wa a) with (wa (a + Z.of_nat 0)) by (f_equal; lia).
  rewrite (bytes_at_ov_read rsegs m a [b] 0 1 H) by (cbn; lia).
  reflexivity.
Qed.

Lemma u4_ba_sub : forall m a bs k n, bytes_at rsegs m a bs -> (k + n <= length bs)%nat ->
  bytes_at rsegs m (a + Z.of_nat k) (firstn n (skipn k bs)).
Proof.
  intros m a bs k n H Hk.
  rewrite <- (firstn_skipn k bs) in H. apply bytes_at_app in H as [_ H].
  rewrite length_firstn in H. replace (Nat.min k (length bs)) with k in H by lia.
  rewrite <- (firstn_skipn n (skipn k bs)) in H. apply bytes_at_app in H as [H _]. exact H.
Qed.

Lemma u4_firstn1 : forall (l : list byte) k, (k < length l)%nat ->
  firstn 1 (skipn k l) = [RcIdentModel.nthb l k].
Proof.
  intros l k Hk. unfold RcIdentModel.nthb. revert k Hk.
  induction l as [|x l IH]; intros [|k] Hk; cbn [skipn nth firstn length] in *; try lia; [reflexivity|].
  apply IH. lia.
Qed.

Lemma u4_byte_rng : forall b : byte, 0 <= bv_unsigned b < 256.
Proof. intros b. pose proof (bv_unsigned_in_range 8 b) as H. unfold bv_modulus in H. exact H. Qed.

(* len_j fits the two length bytes. *)
Lemma u4_len_le : forall inp j, 0 <= t_len inp j <= 65535.
Proof.
  intros inp j. pose proof (u4_len_range inp j) as (H0 & _).
  unfold t_len, f_len, f_L, inb, RcIdentModel.bz in *.
  pose proof (u4_byte_rng (RcIdentModel.nthb inp (Z.to_nat (fc inp j)))).
  pose proof (u4_byte_rng (RcIdentModel.nthb inp (Z.to_nat (fc inp j + 1)))).
  destruct (2 <=? f_left inp (fc inp j)); lia.
Qed.

(* ---- Branch conditions on in-range values ---- *)

Lemma u4_eqb0 : forall z, 0 < z < 2 ^ 64 -> bv_eqb (Z_to_bv 64 z) (Z_to_bv 64 0) = false.
Proof. intros z Hz. unfold bv_eqb. rewrite !MState.unsigned_lit by lia. apply Z.eqb_neq. lia. Qed.

Lemma u4_ltu_true : forall a b, 0 <= a < b -> b < 2 ^ 64 -> bv_ltu (Z_to_bv 64 a) (Z_to_bv 64 b) = true.
Proof. intros a b H1 H2. unfold bv_ltu. rewrite !MState.unsigned_lit by lia. apply Z.ltb_lt. lia. Qed.

Lemma u4_ltu_false : forall a b, 0 <= b <= a -> a < 2 ^ 64 -> bv_ltu (Z_to_bv 64 a) (Z_to_bv 64 b) = false.
Proof. intros a b H1 H2. unfold bv_ltu. rewrite !MState.unsigned_lit by lia. apply Z.ltb_ge. lia. Qed.

(* a < 2^64 + z for a negative immediate z (an address room test against the sign-extended z). *)
Lemma u4_ltu_neg : forall a z, 0 <= a -> - 2 ^ 64 < z < 0 -> a - z < 2 ^ 64 ->
  bv_ltu (Z_to_bv 64 a) (Z_to_bv 64 z) = true.
Proof.
  intros a z H1 H2 H3. unfold bv_ltu. rewrite MState.unsigned_lit by lia. rewrite MState.unsigned_lit_wrap.
  rewrite <- (Z.mod_unique z (2 ^ 64) (-1) (2 ^ 64 + z)) by lia. apply Z.ltb_lt. lia.
Qed.

(* The same test with the constant on the left: 2^64 + z < a is false. *)
Lemma u4_ltu_neg_l : forall a z, 0 <= a -> - 2 ^ 64 < z < 0 -> a - z <= 2 ^ 64 ->
  bv_ltu (Z_to_bv 64 z) (Z_to_bv 64 a) = false.
Proof.
  intros a z H1 H2 H3. unfold bv_ltu. rewrite (MState.unsigned_lit a) by lia. rewrite MState.unsigned_lit_wrap.
  rewrite <- (Z.mod_unique z (2 ^ 64) (-1) (2 ^ 64 + z)) by lia. apply Z.ltb_ge. lia.
Qed.

(* ---- Memory and registers ---- *)

Lemma u4_stk_sub : forall m lo hi lo' hi', Frame.stk rsegs m lo hi -> lo <= lo' -> hi' <= hi ->
  Frame.stk rsegs m lo' hi'.
Proof. intros m lo hi lo' hi' (H1 & H2 & H3) H4 H5. split; [lia|]. split; [lia|]. intros a Ha. apply H3. lia. Qed.

Lemma u4_dj_sub : forall W a n a' n', disjoint_from W a n -> a <= a' -> a' + n' <= a + n -> disjoint_from W a' n'.
Proof.
  induction W as [|[lo hi] W IH]; cbn; intros a n a' n' H H1 H2; [exact I|].
  destruct H as [H3 H4]. split; [lia | exact (IH a n a' n' H4 H1 H2)].
Qed.

Lemma u4_ba : forall W mem m' a bs, bytes_at rsegs mem a bs -> Frame.munch W mem m' ->
  disjoint_from W a (Z.of_nat (length bs)) -> bytes_at rsegs m' a bs.
Proof. intros W mem m' a bs H MU D. exact (bytes_at_transport rsegs W mem m' a bs H MU D). Qed.

Lemma u4_q64 : forall W mem m' a v, q64 mem a v -> Frame.munch W mem m' -> disjoint_from W a 8 -> q64 m' a v.
Proof. unfold q64. intros W mem m' a v H MU D. apply (u4_ba W mem); [exact H | exact MU|]. rewrite length_le8. exact D. Qed.

(* s0, s1, s2-s9, s11 kept. v1.9 leaves s10 (x26) out: no part of FB / GF names it (sum_ok is s11 = x27 now),
   and seg_G03 / seg_G07 write it (rf, then the address of 0x13b10). *)
Definition SKP (regs regs' : bvmap 5 word) : Prop :=
  getr regs' 8 = getr regs 8 /\ getr regs' 9 = getr regs 9 /\ getr regs' 18 = getr regs 18 /\
  getr regs' 19 = getr regs 19 /\ getr regs' 20 = getr regs 20 /\ getr regs' 21 = getr regs 21 /\
  getr regs' 22 = getr regs 22 /\ getr regs' 23 = getr regs 23 /\ getr regs' 24 = getr regs 24 /\
  getr regs' 25 = getr regs 25 /\ getr regs' 27 = getr regs 27.

Lemma u4_rg : forall regs regs' r v, getr regs' r = getr regs r -> rg regs r v -> rg regs' r v.
Proof. unfold rg. intros regs regs' r v E H. rewrite E. exact H. Qed.

(* The two v1.9 loop constants of LK (positions 6 and 5): s2 = 1 (S2) and s0 = sp+128 (OVF). *)
Lemma u4_LK_s2 : forall g j regs m, LK g j regs m -> rg regs 18 1.
Proof. intros g j regs m H. unfold LK in H. decompose [and] H. unfold S2 in *. assumption. Qed.

Lemma u4_LK_s0 : forall g j regs m, LK g j regs m -> rg regs 8 (spk g 128).
Proof. intros g j regs m H. unfold LK in H. decompose [and] H. unfold OVF in *. assumption. Qed.

Lemma u4_phi_keep : forall g j phi mem m' W, bytes_at rsegs mem phi (t_phi (g_in g) j) -> Frame.munch W mem m' ->
  disjoint_from W phi (t_len (g_in g) j) -> bytes_at rsegs m' phi (t_phi (g_in g) j).
Proof.
  intros g j phi mem m' W H MU D. pose proof (u4_len_range (g_in g) j) as (R1 & _).
  apply (u4_ba W mem); [exact H | exact MU|]. rewrite u4_phi_len, Z2Nat.id by lia. exact D.
Qed.

Lemma u4_LK_keep : forall g j regs regs' mem m' W,
  LK g j regs mem -> getr regs' 8 = getr regs 8 -> getr regs' 18 = getr regs 18 -> getr regs' 9 = getr regs 9 ->
  Frame.munch W mem m' -> disjoint_from W (spk g 8) 8 -> disjoint_from W (spk g 114) 6 -> LK g j regs' m'.
Proof.
  intros g j regs regs' mem m' W (Hj & H9 & HOUR & HM7 & H8 & H18) E8 E18 E9 MU D8 D114.
  split; [exact Hj|]. split; [exact (u4_rg _ _ _ _ E9 H9)|].
  split; [unfold OURb in *; apply (u4_ba W mem); [exact HOUR | exact MU|]; rewrite OUR_length; exact D114|].
  split; [unfold M7 in *; apply (u4_q64 W mem m' _ _ HM7 MU); apply (u4_dj_sub W _ _ _ _ D8); unfold spk; lia|].
  split; [unfold OVF in *; exact (u4_rg _ _ _ _ E8 H8)|].
  unfold S2 in *. exact (u4_rg _ _ _ _ E18 H18).
Qed.

(* s0, s2, s5, s6, s7, s1 kept: the registers of FT. *)
Definition FTK (regs regs' : bvmap 5 word) : Prop :=
  getr regs' 8 = getr regs 8 /\ getr regs' 18 = getr regs 18 /\ getr regs' 21 = getr regs 21 /\
  getr regs' 22 = getr regs 22 /\ getr regs' 23 = getr regs 23 /\ getr regs' 9 = getr regs 9.

Lemma u4_FT_keep : forall g j phi regs regs' mem m' W,
  FT g j phi regs mem -> FTK regs regs' -> Frame.munch W mem m' ->
  disjoint_from W phi (t_len (g_in g) j) -> disjoint_from W (spk g 8) 8 -> disjoint_from W (spk g 24) 8 ->
  disjoint_from W (spk g 114) 6 -> FT g j phi regs' m'.
Proof.
  intros g j phi regs regs' mem m' W (HLK & (H24 & H21 & H22) & H23 & Hphi & H18)
    (E8 & E18 & E21 & E22 & E23 & E9) MU Dp D8 D24 D114.
  split; [exact (u4_LK_keep g j regs regs' mem m' W HLK E8 E18 E9 MU D8 D114)|].
  split; [|split; [|split]].
  - split; [exact (u4_q64 W mem m' _ _ H24 MU D24)|].
    split; [exact (u4_rg _ _ _ _ E21 H21) | exact (u4_rg _ _ _ _ E22 H22)].
  - exact (u4_rg _ _ _ _ E23 H23).
  - exact (u4_phi_keep g j phi mem m' W Hphi MU Dp).
  - exact (u4_rg _ _ _ _ E18 H18).
Qed.

(* A record shorter than 50 bytes: no header, k = 0, none of the len >= 50 flags (struct P2.1). *)
Lemma u4_small : forall inp j, t_len inp j <= 49 ->
  t_k inp j = 0 /\ t_big inp j = false /\ t_8819 inp j = false /\ t_sum_ok inp j = false /\
  t_TF inp j = false.
Proof.
  intros inp j H.
  assert (Hb : t_big inp j = false) by (unfold t_big; apply Z.leb_gt; lia).
  split; [unfold t_k; apply RcParse.ctrlparse_none; intros (Hn & _); lia|].
  split; [exact Hb|].
  unfold t_TF, t_8819, t_sum_ok, t_tfill. rewrite Hb. cbn [andb orb].
  refine (conj eq_refl (conj eq_refl eq_refl)).
Qed.

Lemma u4_FB_keep : forall g j phi regs regs' mem m' W,
  FB g j phi regs mem -> SKP regs regs' -> Frame.munch W mem m' ->
  disjoint_from W phi (t_len (g_in g) j) -> disjoint_from W (spk g 8) 8 -> disjoint_from W (spk g 16) 16 ->
  disjoint_from W (spk g 114) 6 -> disjoint_from W (spk g 1752) 36 ->
  FB g j phi regs' m'.
Proof.
  intros g j phi regs regs' mem m' W (HFT & (H25 & H19 & H27 & H20 & (H24 & H16 & HB)))
    (E8 & E9 & E18 & E19 & E20 & E21 & E22 & E23 & E24 & E25 & E27) MU Dp D8 D16 D114 DB.
  split.
  - apply (u4_FT_keep g j phi regs regs' mem m' W HFT);
      [unfold FTK; repeat split; assumption | exact MU | exact Dp | exact D8
      | apply (u4_dj_sub W _ _ _ _ D16); unfold spk; lia | exact D114].
  - split; [exact (u4_rg _ _ _ _ E25 H25)|]. split; [exact (u4_rg _ _ _ _ E19 H19)|].
    split; [exact (u4_rg _ _ _ _ E27 H27)|]. split; [exact (u4_rg _ _ _ _ E20 H20)|].
    split; [exact (u4_rg _ _ _ _ E24 H24)|].
    split; [apply (u4_q64 W mem m' _ _ H16 MU); apply (u4_dj_sub W _ _ _ _ D16); unfold spk; lia|].
    apply (u4_ba W mem); [exact HB | exact MU|]. unfold t_B. rewrite RcParse.ctrlparse_length. exact DB.
Qed.

Lemma u4_IDb_keep : forall g idb mem m' W, length idb = 38%nat -> IDb g idb mem -> Frame.munch W mem m' ->
  disjoint_from W (spk g 76) 38 -> IDb g idb m'.
Proof.
  intros g idb mem m' W L (H & Hok) MU D. split; [|exact Hok]. unfold IDB in *.
  apply (u4_ba W mem); [exact H | exact MU|]. rewrite L. exact D.
Qed.

Lemma u4_FGb_keep : forall g st mem m' W, length st = 72%nat -> FGb g st mem -> Frame.munch W mem m' ->
  disjoint_from W (spk g 120) 72 -> FGb g st m'.
Proof.
  intros g st mem m' W L (H & Hok) MU D. split; [|exact Hok]. unfold FGB in *.
  apply (u4_ba W mem); [exact H | exact MU|]. rewrite L. exact D.
Qed.

(* FS_j = `first`: n <= 22 and the body has n bytes (an open sets n = fg_n g with 1 <= fg_n g <= 22, else kept). *)
Lemma u4_fst_nb : forall inp j,
  0 <= fs_nb (fst_at inp j) <= 22 /\ length (fs_body (fst_at inp j)) = Z.to_nat (fs_nb (fst_at inp j)).
Proof.
  intros inp j. induction j as [|j IH]; [cbn; split; [lia | reflexivity]|].
  rewrite fst_at_S. unfold turn. cbv zeta.
  destruct (f_opens (t_len inp j) (t_g inp j)) eqn:Eo; cbn [fs_nb fs_body]; [|exact IH].
  unfold f_opens in Eo. apply andb_true_iff in Eo as [Efr _].
  pose proof (u4_fgfr_n _ _ Efr) as Hn.
  pose proof (u4_body_len (t_g inp j) (u4_tg_len inp j) Hn) as HL.
  unfold RcFrag.fg_n in Hn, HL. split; [lia | exact HL].
Qed.

(* FS: the 40-byte local `first` at sp+36 (have u32 at +0, n at +4, body at +5). *)
Lemma u4_FSb_keep : forall g s st mem m' W, FSb g s st mem -> fs_nb s <= 35 -> Frame.munch W mem m' ->
  disjoint_from W (spk g 36) 40 -> FSb g s st m'.
Proof.
  intros g s st mem m' W (Hh & Hn & Hb & HL & HFI) Hle MU D. unfold u32, b8 in *.
  split; [|split; [|split; [|split; [exact HL | exact HFI]]]].
  - apply (u4_ba W mem); [exact Hh | exact MU|]. rewrite length_le4.
    apply (u4_dj_sub W _ _ _ _ D); unfold spk; lia.
  - apply (u4_ba W mem); [exact Hn | exact MU|]. cbn [length].
    apply (u4_dj_sub W _ _ _ _ D); unfold spk; lia.
  - apply (u4_ba W mem); [exact Hb | exact MU|].
    apply (u4_dj_sub W _ _ _ _ D); unfold spk; lia.
Qed.

Lemma u4_FSj_keep : forall g j mem m' W, FSj g j mem -> Frame.munch W mem m' ->
  disjoint_from W (spk g 36) 40 -> FSj g j m'.
Proof.
  intros g j mem m' W HS MU D. unfold FSj in *.
  pose proof (u4_fst_nb (g_in g) j) as (Hn & _).
  exact (u4_FSb_keep g _ _ mem m' W HS ltac:(lia) MU D).
Qed.

Lemma u4_IFS_keep : forall g j mem m' W, IFS g j mem -> Frame.munch W mem m' ->
  disjoint_from W (spk g 36) 40 -> disjoint_from W (spk g 120) 72 -> disjoint_from W (spk g 76) 38 ->
  IFS g j m'.
Proof.
  intros g j mem m' W (HI & HG & HS) MU D36 D120 D76.
  split; [exact (u4_IDb_keep g _ mem m' W (u4_tID_len _ _) HI MU D76)|].
  split; [exact (u4_FGb_keep g _ mem m' W (u4_tFG_len _ _) HG MU D120)|].
  exact (u4_FSj_keep g j mem m' W HS MU D36).
Qed.

(* A disjointness goal over a literal W: every bound is linear in g_S g, phi and the model lengths. *)
Ltac u4_dj := cbn [disjoint_from]; unfold spk, fsp, SLOT_FRAME in *; repeat split; try exact I; lia.

(* Every interval of W lies in [S - K, S - 104): so does every address a run writes. *)
Lemma u4_fp : forall g W, Forall (fun iv => g_S g - SLOT_K <= fst iv /\ snd iv <= g_S g - 104) W ->
  forall x, 0 <= x < 2 ^ 64 -> ~ Frame.outside W x -> g_S g - SLOT_K <= x < g_S g - 104.
Proof.
  intros g W HW. induction HW as [|[lo hi] W Hh HW IH]; intros x Hx O; cbn [Frame.outside] in O.
  - exfalso. apply O. exact I.
  - cbn [fst snd] in Hh.
    destruct (Z_le_dec lo x); destruct (Z_lt_dec x hi);
      [lia | | |]; apply IH; try exact Hx; intros O'; apply O; split; try exact O'; lia.
Qed.

Lemma u4_c_bytes : forall m A c, Step.rw_cells rsegs m A [c] -> bytes_at rsegs m A (Cells.cbytes c).
Proof. intros m A c H. pose proof (sl_cells_bytes m A [c] H) as Hb. cbn [Cells.cells_bytes] in Hb. rewrite app_nil_r in Hb. exact Hb. Qed.

Ltac u4_fp_tac := apply u4_fp; repeat constructor; cbn [fst snd]; unfold SLOT_K, SLOT_STACK in *; lia.

(* ---- Bundles across a call that keeps the slot frame [fsp, S) byte for byte (malloc's post) ---- *)
Lemma u4_ba_frame : forall g m m' a bs,
  (forall x, fsp g <= x < g_S g -> mbyte rsegs m' x = mbyte rsegs m x) ->
  bytes_at rsegs m a bs -> fsp g <= a -> a + Z.of_nat (length bs) <= g_S g -> bytes_at rsegs m' a bs.
Proof. intros g m m' a bs K H H1 H2. apply (u1_ba_mbyte m m' a bs H). intros i Hi. apply K. lia. Qed.

Lemma u4_LK_frame : forall g j regs regs' m m',
  (forall x, fsp g <= x < g_S g -> mbyte rsegs m' x = mbyte rsegs m x) ->
  getr regs' 8 = getr regs 8 -> getr regs' 18 = getr regs 18 -> getr regs' 9 = getr regs 9 ->
  LK g j regs m -> LK g j regs' m'.
Proof.
  intros g j regs regs' m m' K E8 E18 E9 (Hj & H9 & HOUR & HM7 & H8 & H18).
  unfold OURb, M7, OVF, S2, q64 in *.
  split; [exact Hj|]. split; [exact (u4_rg _ _ _ _ E9 H9)|].
  split; [apply (u4_ba_frame g m m' _ _ K HOUR); unfold spk, fsp, SLOT_FRAME; rewrite ?OUR_length; lia|].
  split; [apply (u4_ba_frame g m m' _ _ K HM7); unfold spk, fsp, SLOT_FRAME; rewrite ?length_le8; lia|].
  split; [exact (u4_rg _ _ _ _ E8 H8) | exact (u4_rg _ _ _ _ E18 H18)].
Qed.

Lemma u4_IFS_frame : forall g j m m',
  (forall x, fsp g <= x < g_S g -> mbyte rsegs m' x = mbyte rsegs m x) -> IFS g j m -> IFS g j m'.
Proof.
  intros g j m m' K ((HID & Hok) & (HFG & Hfok) & (Hh & Hn & Hb & HL & HFI)).
  unfold IFS, IDj, FGj, FSj, IDb, FGb, FSb, IDB, FGB, u32, b8 in *.
  pose proof (u4_tID_len (g_in g) j) as L1. pose proof (u4_tFG_len (g_in g) j) as L2.
  pose proof (u4_fst_nb (g_in g) j) as (Hnb & _).
  refine (conj (conj _ Hok) (conj (conj _ Hfok) (conj _ (conj _ (conj _ (conj HL HFI)))))).
  all: eapply u4_ba_frame; [exact K | eassumption | unfold spk, fsp, SLOT_FRAME; lia
                           | rewrite ?length_le4, ?L1, ?L2; cbn [length]; unfold spk, fsp, SLOT_FRAME; lia].
Qed.

Section S.
Context {fx : FPState} {rc : RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : RunCeil, AllocAPI B.
Context {LS : lib_shape} {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.
Hypothesis FF : frame_facts B APIf LS SH SK ra empty.

(* Φ, a block of the allocator (hb1 Φ n), lies in [4096, S - K). *)
Lemma u4_phi_bnd : forall g phi n L A regs mem md, FR B APIf ra empty g (hb1 phi n) L A regs mem md ->
  Permutation (blocks L A) (hb1 phi n ++ blocks (g_L g) (g_A g)) ->
  4096 <= phi /\ phi + n <= g_S g - SLOT_K.
Proof.
  intros g phi n L A regs mem md HFR HP.
  destruct HFR as (HGV & _ & _ & _ & _ & _ & _ & _ & HM & _).
  pose proof HGV as (_ & _ & _ & _ & HSK & _).
  assert (Hin : In (phi, n) (blocks L A)).
  { apply (Permutation_in _ (Permutation_sym HP)). apply in_or_app. left. left. reflexivity. }
  apply blocks_In in Hin as (p & Hp & Hpin).
  destruct (mr_blocks_range B (aa_MR (APIf rc)) (aa_laws (APIf rc)) L A mem md p n HM Hpin) as (H1 & H2).
  lia.
Qed.

Lemma u4_mid : forall g hb L A regs mem md pc W (Q : machine_state -> Prop) (P : config -> Prop),
  FR B APIf ra empty g hb L A regs mem md ->
  Permutation (blocks L A) (hb ++ blocks (g_L g) (g_A g)) ->
  (forall x, 0 <= x < 2 ^ 64 -> ~ Frame.outside W x -> g_S g - SLOT_K <= x < g_S g - 104) ->
  Exec.evt rsegs Q (MState.MS (Regs6ss.mkR_of regs) fp_regs pc fp_csr None (normalize rsegs mem) (seg_rom rsegs)) ->
  (forall ms, Q ms -> exists R pc' m', ms = MState.MS R fp_regs pc' fp_csr None m' (seg_rom rsegs) /\
     Frame.munch W (normalize rsegs mem) m' /\ Frame.wmono rsegs (normalize rsegs mem) m' /\
     getr R 2 = getr regs 2 /\ getr R 3 = getr regs 3 /\ getr R 4 = getr regs 4) ->
  (forall R pc' m0' regs' m', Q (MState.MS R fp_regs pc' fp_csr None m0' (seg_rom rsegs)) ->
     Regs6ss.xregs_eqv R regs' -> mem_rel rsegs m' m0' -> Frame.munch W mem m' ->
     FR B APIf ra empty g hb L A regs' m' md ->
     SR (ms_segs B) (mkCfg (mkst regs' pc' m' (seg_rom (ms_segs B))) md) P) ->
  SR (ms_segs B) (mkCfg (mkst regs pc mem (seg_rom (ms_segs B))) md) P.
Proof.
  intros g hb L A regs mem md pc W Q P HFR HP HW HE Hform HK.
  pose proof (sl_segs B APIf ra empty FF) as SEGS.
  pose proof HFR as (_ & _ & _ & _ & _ & _ & HMI & _ & HM & _).
  unfold MI in HMI. rewrite SEGS in HMI.
  destruct (mr_model B _ (aa_laws (APIf rc)) _ _ _ _ HM) as (Hh & Hl & _).
  rewrite SEGS.
  apply (sl_run regs pc mem md Q P Hh Hl HMI HE).
  - intros ms HQ. destruct (Hform ms HQ) as (R & pc' & m' & -> & _). exists R, pc', m'. reflexivity.
  - intros R pc' m0' HQ regs' m' Hx Hrel Hsame.
    destruct (Hform _ HQ) as (R1 & pc1 & m1 & E & MU & WM & E2 & E3 & E4).
    injection E; intros; subst.
    pose proof (mem_rel_normalize rsegs mem HMI) as HR0.
    pose proof (munch_rel rsegs W mem (normalize rsegs mem) m' m1 HR0 Hrel Hsame MU) as MU'.
    rewrite <- SEGS. apply (HK R1 pc1 m1 regs' m' HQ Hx Hrel MU').
    apply (sl_fr_run B APIf ra empty FF g hb L A regs mem md regs' m' W HFR HP).
    + exact MU'.
    + exact (wmono_rel rsegs mem (normalize rsegs mem) m' m1 HR0 Hrel Hsame WM).
    + exact (ro_agree_same rsegs mem m' HMI Hsame).
    + exact HW.
    + rewrite (sl_getr_eqv _ _ _ Hx). exact E2.
    + rewrite (sl_getr_eqv _ _ _ Hx). exact E3.
    + rewrite (sl_getr_eqv _ _ _ Hx). exact E4.
Qed.

(* The input block at a cut: [p, p + n) is a live entry block, so its bytes are those of the entry memory
   (FR's entry-block clause) and the entry memory holds the input there (GV's blk_data). *)
Lemma u4_in_all : forall g hb L A regs mem md,
  FR B APIf ra empty g hb L A regs mem md ->
  Permutation (blocks L A) (hb ++ blocks (g_L g) (g_A g)) -> 0 < g_n g ->
  4096 <= g_p g /\ g_p g + g_n g <= YM05.alloc_ceiling /\ bytes_at rsegs mem (g_p g) (g_in g).
Proof.
  intros g hb L A regs mem md HFR HP Hn.
  pose proof HFR as (HGV & _ & _ & _ & _ & _ & _ & _ & HM & _ & _ & _ & _ & _ & _ & Hblk & _).
  pose proof HGV as (_ & Hpn & Hdat & _).
  destruct Hpn as [(Hn0 & _) | (_ & Hin)]; [lia|].
  pose proof (sl_segs B APIf ra empty FF) as SEGS.
  destruct (u1_blk B APIf ra empty FF L A mem md (g_p g) (g_n g) HM
             (Permutation_in _ (Permutation_sym HP) (in_or_app _ _ _ (or_intror Hin)))) as (_ & H1 & H2).
  pose proof alloc_ceiling_value as Hac.
  split; [exact H1|]. split; [exact H2|].
  split; [lia|]. split; [unfold g_n, nlen in *; lia|].
  intros k Hk.
  assert (Hk' : 0 <= Z.of_nat k < g_n g) by (unfold g_n, nlen; lia).
  pose proof (Hblk (g_p g) (g_n g) (Z.of_nat k) Hin Hk') as E1.
  assert (Hk'' : 0 <= Z.of_nat k < Z.of_nat (length (g_in g))) by lia.
  pose proof (Hdat (Z.of_nat k) Hk'') as E2.
  rewrite E2, Nat2Z.id, SEGS in E1. exact E1.
Qed.

(* The live harness block and an entry block are disjoint (the allocator's blocks are pairwise disjoint). *)
Lemma u4_hb_disj : forall g phi n L A regs mem md a k,
  FR B APIf ra empty g (hb1 phi n) L A regs mem md ->
  Permutation (blocks L A) (hb1 phi n ++ blocks (g_L g) (g_A g)) ->
  In (a, k) (blocks (g_L g) (g_A g)) -> phi + n <= a \/ a + k <= phi.
Proof.
  intros g phi n L A regs mem md a k HFR HP Hin.
  pose proof HFR as (_ & _ & _ & _ & _ & _ & _ & _ & HM & _).
  pose proof (mr_blocks_disjoint B _ (aa_laws (APIf rc)) _ _ _ _ HM) as PD.
  apply (u1_pw_perm _ ranges_disjoint u1_rd_sym _ _ HP) in PD.
  destruct PD as [PD _]. pose proof (PD (a, k) Hin) as Hd. unfold ranges_disjoint in Hd. cbn [fst snd] in Hd.
  exact Hd.
Qed.

(* The input block is an entry block when n > 0. *)
Lemma u4_in_blk : forall g, GV B empty g -> 0 < g_n g -> In (g_p g, g_n g) (blocks (g_L g) (g_A g)).
Proof.
  intros g (_ & Hpn & _) Hn. destruct Hpn as [(Hn0 & _) | (_ & Hin)]; [lia | exact Hin].
Qed.

(* The input-byte lemma: the byte at p + i (0 <= i < n) in the memory of a cut is in[i]. *)
Lemma u4_in_byte : forall g hb L A regs mem md i,
  FR B APIf ra empty g hb L A regs mem md ->
  Permutation (blocks L A) (hb ++ blocks (g_L g) (g_A g)) -> 0 <= i < g_n g ->
  bytes_at rsegs mem (g_p g + i) [RcIdentModel.nthb (g_in g) (Z.to_nat i)].
Proof.
  intros g hb L A regs mem md i HFR HP Hi.
  destruct (u4_in_all g hb L A regs mem md HFR HP ltac:(lia)) as (H1 & H2 & HB).
  pose proof (u4_ba_sub mem (g_p g) (g_in g) (Z.to_nat i) 1 HB ltac:(unfold g_n, nlen in Hi; lia)) as H.
  rewrite Z2Nat.id in H by lia. rewrite (u4_firstn1 (g_in g) (Z.to_nat i)) in H by (unfold g_n, nlen in Hi; lia).
  exact H.
Qed.

(* The same read in the normalized memory of a run. *)
Lemma u4_in_rd : forall g hb L A regs mem md i,
  FR B APIf ra empty g hb L A regs mem md ->
  Permutation (blocks L A) (hb ++ blocks (g_L g) (g_A g)) -> 0 <= i < g_n g ->
  ov_read_bytes rsegs (normalize rsegs mem) (wa (g_p g + i)) 1 = Some [RcIdentModel.nthb (g_in g) (Z.to_nat i)].
Proof.
  intros g hb L A regs mem md i HFR HP Hi. apply u4_ld1.
  pose proof HFR as (_ & _ & _ & _ & _ & _ & HMI & _). unfold MI in HMI. rewrite (sl_segs B APIf ra empty FF) in HMI.
  exact (proj1 (bytes_at_rel rsegs _ _ _ _ (mem_rel_normalize rsegs mem HMI)) (u4_in_byte g hb L A regs mem md i HFR HP Hi)).
Qed.

End S.
