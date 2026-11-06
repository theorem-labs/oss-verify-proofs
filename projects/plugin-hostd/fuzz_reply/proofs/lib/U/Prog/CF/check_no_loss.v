(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/jsoncons/fuzz_msgpack_encoder/lib/CJ/Ref/Mh_0118.v, with its module paths, module names and addresses changed; 1147 of its 1229 lines of code are new or changed and 2359 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_reply/lib/Prog/drain_b_seg.v, with its module paths and module names changed; 618 of its 664 lines of code are new or changed and 1183 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_reply/lib/Prog/CF/SlotPass9G.v, with its module paths and module names changed; 466 of its 523 lines of code are new or changed and 607 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_reply/lib/Prog/CF/HarnessGlue.v, with its module paths and module names changed; 1635 of its 1713 lines of code are new or changed and 445 lines of the source are left out. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame Tac Bytes ZBridge.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U Require Import Img0.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Spec Require Import StrFun.
From LinuxProcessSemantics.LinuxProcessSem Require Import StackLayout Fs Monad Specs.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Reusable Require Import YK11 YK0o YK0s YK14 YK15 YM06 YP09.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Reusable Require Import YO0i YO0f YO0d YO05 YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Reusable Require Import YL0i YL01.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Reusable Require YI04 YO10.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Lib Require Regs6ss RegisterBridge.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U Require Import Contract ContractT.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Prog Require Import RelayFrame RelayRunT RelayRunF TrNames RelayModel HarnessRep ListRep CheckRep ListTr.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Prog.CF Require Import HarnessTr.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Prog Require Import TrModel.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Prog Require Import next_line_c bcmp_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Prog.CF Require Import list_push_c list_drop_c gesture_model_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Prog.CF Require Import check_no_loss_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Prog Require Import check_no_loss_seg KindB.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Prog.CF Require Import HarnessGlue HarnessFrame.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Prog.CF Require Import SRCF SRCF3.
Import ListNotations.
Open Scope Z_scope.

Definition cn_bs (rs : list (Z * list byte)) : list byte := concat (map (fun r => snd r ++ [Z_to_bv 8 0]) rs).

Definition cn_tx (rs : list (Z * list byte)) : list (list Z) := map (fun r => bzs (snd r)) rs.

Definition cn_b (l : list Z) : Z := if is_begin l then 1 else 0.

Lemma cn_bs_app : forall a b, cn_bs (a ++ b) = cn_bs a ++ cn_bs b.
Proof. intros a b. unfold cn_bs. rewrite map_app, concat_app. reflexivity. Qed.

Lemma cn_bs_cons : forall r rs, cn_bs (r :: rs) = snd r ++ Z_to_bv 8 0 :: cn_bs rs.
Proof. intros r rs. unfold cn_bs. cbn [map concat]. rewrite <- app_assoc. reflexivity. Qed.

Lemma cn_tx_app : forall a b, cn_tx (a ++ b) = cn_tx a ++ cn_tx b.
Proof. intros a b. unfold cn_tx. apply map_app. Qed.

Lemma cn_upds_app : forall G a b, upds G (a ++ b) = upds (upds G a) b.
Proof. intros G a b. unfold upds. apply fold_left_app. Qed.

Lemma nret_rec_drop : forall r, nretF (rec_drop_tr r) = 0%nat.
Proof. reflexivity. Qed.

Lemma cn_tr_app : forall pre rs j s,
  check_no_loss_tr j s (pre ++ rs) =
  check_no_loss_tr j s pre ++ check_no_loss_tr (j + nretF (check_no_loss_tr j s pre)) (check_no_loss_sh j s pre) rs.
Proof.
  induction pre as [|r pre IH]; intros rs j s; cbn [app check_no_loss_tr check_no_loss_sh].
  - rewrite Nat.add_0_r. reflexivity.
  - rewrite IH, <- !app_assoc, !nret_app, nret_rec_drop. do 4 f_equal. lia.
Qed.

Lemma cn_sh_app : forall pre rs j s,
  check_no_loss_sh j s (pre ++ rs) = check_no_loss_sh (j + nretF (check_no_loss_tr j s pre)) (check_no_loss_sh j s pre) rs.
Proof.
  induction pre as [|r pre IH]; intros rs j s; cbn [app check_no_loss_tr check_no_loss_sh].
  - rewrite Nat.add_0_r. reflexivity.
  - rewrite IH, !nret_app, nret_rec_drop. f_equal. lia.
Qed.

Lemma cn_tr_one : forall j s r, check_no_loss_tr j s [r] = gesture_model_tr s (snd r) ++ rec_drop_tr r.
Proof. intros j s r. cbn [check_no_loss_tr]. rewrite app_nil_r. reflexivity. Qed.

Lemma cn_texts_length : forall l, Z.of_nat (length (texts l)) = hl_n l.
Proof. intros l. unfold texts, hl_n. rewrite length_map. reflexivity. Qed.

Lemma cn_sh_n_of : forall nm l, sh_n (sh_of nm l) = hl_n l.
Proof. intros nm l. unfold sh_n, sh_of, hl_n. cbn [sh_recs]. rewrite length_map. reflexivity. Qed.

Lemma cn_f2_in : forall (X Y : Type) (Rr : X -> Y -> Prop) l1 l2 x, Forall2 Rr l1 l2 -> In x l1 -> exists y, In y l2 /\ Rr x y.
Proof.
  intros X Y Rr l1 l2 x H. induction H as [|a b l1 l2 Hab _ IH]; intros Hx; [destruct Hx|].
  destruct Hx as [<-|Hx]; [exists b; split; [left; reflexivity | exact Hab]|].
  destruct (IH Hx) as (y & Hy & Hr). exists y. split; [right; exact Hy | exact Hr].
Qed.

Lemma cn_f2_trans : forall q1 q2 q3 l1 l2 l3,
  Forall2 (rec_rel q1 q2) l1 l2 -> Forall2 (rec_rel q2 q3) l2 l3 -> Forall2 (rec_rel q1 q3) l1 l3.
Proof.
  intros q1 q2 q3 l1 l2 l3 H. revert l3. induction H as [|a b l1 l2 Hab _ IH]; intros l3 H2.
  - inversion H2. constructor.
  - inversion H2 as [|b' c l2' l3' Hbc Hrest]; subst. constructor; [|exact (IH _ Hrest)].
    destruct Hab as [Hx1 Ha1]. destruct Hbc as [Hx2 Ha2]. split; [congruence|]. unfold ad_eq in *. congruence.
Qed.

Lemma cn_rel_trans : forall q1 q2 q3 s1 s2 s3, sh_rel q1 q2 s1 s2 -> sh_rel q2 q3 s2 s3 -> sh_rel q1 q3 s1 s3.
Proof.
  intros q1 q2 q3 s1 s2 s3 (E1 & V1 & R1) (E2 & V2 & R2). split; [congruence|]. split.
  - intros Hc. unfold ad_eq in *. rewrite (V1 ltac:(rewrite E2; exact Hc)). exact (V2 Hc).
  - exact (cn_f2_trans _ _ _ _ _ _ R1 R2).
Qed.

Lemma cn_rel_refl : forall q1 q2 L A l, sh_rel q1 q2 (sh_of (known_at L A) l) (sh_of (known_at L A) l).
Proof.
  intros q1 q2 L A l. split; [reflexivity|]. split; [intros _; reflexivity|]. unfold sh_of. cbn [sh_recs].
  induction (hl_recs l) as [|r rs IH]; cbn [map]; constructor; [split; reflexivity | exact IH].
Qed.

Lemma cn_recs_names : forall q1 Y (nm1 nm2 : Z -> tad) (hs : list (Z * list byte)) l1,
  (forall r, In r hs -> nm2 (fst r) = nm1 (fst r)) ->
  Forall2 (rec_rel q1 Y) l1 (map (shr nm1) hs) -> Forall2 (rec_rel q1 Y) l1 (map (shr nm2) hs).
Proof.
  induction hs as [|hr hs IH]; intros l1 Hr R; cbn [map] in R |- *.
  - exact R.
  - inversion R as [|r1 r2 l1' l2' Hab Hrest]; subst. constructor.
    + destruct Hab as [Hx Ha]. split; [exact Hx|]. unfold ad_eq in *. cbn [shr fst] in *.
      rewrite (Hr hr (or_introl eq_refl)). exact Ha.
    + apply IH; [intros r0 Hr0; apply Hr; right; exact Hr0 | exact Hrest].
Qed.

Lemma cn_rel_names : forall q1 Y s (nm1 nm2 : Z -> tad) l,
  (hl_cap l <> 0 -> nm2 (hl_v l) = nm1 (hl_v l)) -> (forall r, In r (hl_recs l) -> nm2 (fst r) = nm1 (fst r)) ->
  sh_rel q1 Y s (sh_of nm1 l) -> sh_rel q1 Y s (sh_of nm2 l).
Proof.
  intros q1 Y s nm1 nm2 l Hv Hr (E & V & R). split; [exact E|]. split.
  - intros Hc. specialize (V Hc). unfold ad_eq in *. cbn [sh_of sh_v sh_cap] in *. rewrite (Hv Hc). exact V.
  - exact (cn_recs_names q1 Y nm1 nm2 (hl_recs l) (sh_recs s) Hr R).
Qed.

Lemma cn_rel_live : forall L A qs Y s l, NoDup (map fst (blocks L A)) -> sh_real L qs s l -> sh_live A qs s ->
  sh_rel qs Y s (sh_of (known_at L A) l).
Proof.
  intros L A qs Y s l HN (Rc & Rv & Rk & Ra) (Lv & Lr). split; [cbn [sh_of sh_cap]; symmetry; exact Rc|]. split.
  - intros Hc. cbn [sh_of sh_cap sh_v] in Hc |- *. rewrite Rc in Hc. destruct (Lv Hc) as [n Hn]. unfold ad_eq.
    cbn [known_at resolve]. rewrite (Rv Hc). symmetry. exact (sptr_of_eq L A _ n HN Hn).
  - cbn [sh_of sh_recs]. unfold sh_keys in Rk. clear Rc Rv Lv. revert Rk Ra Lr. generalize (sh_recs s) as rs.
    generalize (hl_recs l) as hs.
    induction hs as [|hr hs IH]; intros [|r rs] Ek Ea Hl; cbn [map] in Ek, Ea |- *; try discriminate.
    + constructor.
    + injection Ek as Ek1 Ek2. injection Ea as Ea1 Ea2. constructor.
      * split; [symmetry; exact Ek1|]. unfold ad_eq. cbn [shr fst known_at resolve].
        destruct (Hl r (or_introl eq_refl)) as [n Hn]. rewrite Ea1. symmetry. exact (sptr_of_eq L A _ n HN Hn).
      * apply IH; [exact Ek2 | exact Ea2 | intros r0 Hr0; apply Hl; right; exact Hr0].
Qed.

Lemma cn_rel_real : forall L A qs Y s l, NoDup (map fst (blocks L A)) ->
  (hl_cap l <> 0 -> exists n, In (hl_v l, n) (blocks L A)) ->
  (forall r, In r (hl_recs l) -> exists n, In (fst r, n) (blocks L A)) ->
  sh_rel qs Y s (sh_of (known_at L A) l) -> sh_real L qs s l /\ sh_live A qs s.
Proof.
  intros L A qs Y s l HN Hv Hr R. split; [exact (sh_rel_real L qs Y s _ l R (sh_real_of L A Y l HN Hv Hr))|].
  destruct R as (E & V & RR). split.
  - intros Hc. cbn [sh_of sh_cap] in E. rewrite E in Hc. destruct (Hv Hc) as [n Hn]. exists n.
    pose proof (V Hc) as X. unfold ad_eq, pdefT in X. cbn [sh_of sh_v known_at resolve] in X. rewrite X.
    exact (proj1 (sptr_of_spec L A _ n HN Hn)).
  - intros r Hin. destruct (cn_f2_in _ _ _ _ _ r RR Hin) as (r2 & Hr2 & [_ Ha]). cbn [sh_of sh_recs] in Hr2.
    apply in_map_iff in Hr2 as (hr & <- & Hhr). destruct (Hr hr Hhr) as [n Hn]. exists n.
    unfold ad_eq, pdefT in Ha. cbn [shr fst known_at resolve] in Ha. rewrite Ha. exact (proj1 (sptr_of_spec L A _ n HN Hn)).
Qed.

Lemma cn_seg_run : forall (F : ResFormT) qs qc X S sc ln b,
  sh_rel (qs ++ qc ++ X) qc S sc -> length qc = nretF (gesture_model_tr sc ln) ->
  run_from (rt_R F) sptr (SP 0 0) (rt_malloc F) (rt_free F) (rt_realloc F) (qs ++ qc ++ X) b (length qs)
    (gesture_model_tr S ln) = runF F qc b (gesture_model_tr sc ln).
Proof.
  intros F qs qc X S sc ln b HR HL. unfold runF, run_tr. apply run_rel; [apply gesture_model_rel; exact HR|].
  pose proof (ret_agree_embed sptr pdefT qs qc X 0 (nretF (gesture_model_tr sc ln)) ltac:(lia)) as RA.
  rewrite Nat.add_0_r in RA. exact RA.
Qed.

Lemma cn_seg_room : forall (F : ResFormT) qs qc X S sc ln b,
  sh_rel (qs ++ qc ++ X) qc S sc -> length qc = nretF (gesture_model_tr sc ln) ->
  (room_from (rt_R F) sptr (SP 0 0) (rt_malloc F) (rt_free F) (rt_realloc F) (rt_room F) (qs ++ qc ++ X) b (length qs)
    (gesture_model_tr S ln) <-> roomF F qc b (gesture_model_tr sc ln)).
Proof.
  intros F qs qc X S sc ln b HR HL. unfold roomF, room_run. apply room_rel; [apply gesture_model_rel; exact HR|].
  pose proof (ret_agree_embed sptr pdefT qs qc X 0 (nretF (gesture_model_tr sc ln)) ltac:(lia)) as RA.
  rewrite Nat.add_0_r in RA. exact RA.
Qed.

Lemma cn_cb_cons : forall x l, count_begin (x :: l) = ((if is_begin x then 1 else 0) + count_begin l)%nat.
Proof. intros x l. unfold count_begin. rewrite list_basics.list.filter_cons. destruct (is_begin x); reflexivity. Qed.

Lemma cn_cb_app : forall a b, count_begin (a ++ b) = (count_begin a + count_begin b)%nat.
Proof. intros a b. unfold count_begin. rewrite list_basics.list.filter_app, length_app. reflexivity. Qed.

Lemma cn_cb_one : forall l, Z.of_nat (count_begin [l]) = cn_b l.
Proof. intros l. rewrite cn_cb_cons. unfold cn_b. destruct (is_begin l); reflexivity. Qed.

Lemma cn_b_range : forall l, 0 <= cn_b l <= 1.
Proof. intros l. unfold cn_b. destruct (is_begin l); lia. Qed.

Lemma cn_filter_len : forall (f : list Z -> bool) l, (length (List.filter f l) <= length l)%nat.
Proof. intros f l. induction l as [|x l IH]; cbn [List.filter length]; [lia|]. destruct (f x); cbn [length]; lia. Qed.

Lemma cn_upd_len : forall G l, Z.of_nat (length (upd G l)) <= Z.of_nat (length G) + cn_b l.
Proof.
  intros G l. unfold upd, cn_b, is_begin. destruct (gesture l) as [[g x]|]; [destruct g|].
  - destruct (existsb (list_eqb x) G); [lia|]. rewrite length_app. cbn [length]. lia.
  - pose proof (cn_filter_len (fun y => negb (list_eqb x y)) G). lia.
  - lia.
Qed.

Lemma cn_cap_step : forall j s l c0 n0 bp,
  sh_n s <= sh_cap s -> sh_n s <= n0 + bp -> 0 <= bp ->
  sh_cap s <= Z.max 8 (Z.max c0 (2 * (n0 + bp))) ->
  sh_cap (gesture_model_sh j s l) <= Z.max 8 (Z.max c0 (2 * (n0 + (bp + cn_b l)))).
Proof.
  intros j s l c0 n0 bp Hn HD Hb Hc. unfold gesture_model_sh, cn_b, is_begin.
  destruct (gesture l) as [[g x]|]; [destruct g|].
  - destruct (existsb (list_eqb x) (sh_keys s)); [lia|]. unfold list_push_sh.
    destruct (Z.eqb_spec (sh_n s) (sh_cap s)) as [E|E]; cbn [sh_cap]; [|lia]. unfold grow_cap.
    rewrite (proj2 (Z.eqb_eq _ _) E). destruct (Z.eqb_spec (sh_cap s) 0); lia.
  - destruct (find_key x (sh_keys s)); cbn [list_drop_sh sh_cap]; lia.
  - lia.
Qed.

Lemma cn_ub_nonneg : forall s p n, WF s -> In (p, n) (user_blocks s) -> 0 <= n.
Proof.
  intros s p n HW Hin.
  destruct (YO10.in_user_blocks_inv s (p, n) Hin) as (g & am & i & fr & Hg & Hi & Hfr & _ & E).
  apply (YO10.used_metas_usedX s g am HW) in Hg.
  destruct (YO10.block_in_slot s g am i fr HW Hg Hi Hfr) as (_ & _ & H).
  injection E as _ ->. exact H.
Qed.

Lemma cn_blocks_in : forall L A q k, In (q, k) (blocks L A) -> exists p, In (p, k) (user_blocks A) /\ ptr_addr L p = q.
Proof.
  intros L A q k Hin. unfold blocks in Hin. apply in_map_iff in Hin. destruct Hin as ([p k0] & E & Hin).
  cbn [fst snd] in E. injection E as E1 E2. subst. exists p. split; [exact Hin | reflexivity].
Qed.

Lemma cn_blocks_of : forall L A p n, In (p, n) (user_blocks A) -> In (ptr_addr L p, n) (blocks L A).
Proof. intros L A p n Hin. unfold blocks. exact (in_map (fun b => (ptr_addr L (fst b), snd b)) _ (p, n) Hin). Qed.

Lemma cn_outside_dec : forall W x, {outside W x} + {~ outside W x}.
Proof.
  induction W as [|[lo hi] W IH]; intros x; cbn [outside]; [left; exact I|].
  destruct (Z_le_gt_dec lo x) as [H1|H1]; [destruct (Z_lt_ge_dec x hi) as [H2|H2]|].
  - right. intros [H _]. lia.
  - destruct (IH x) as [H|H]; [left; split; [lia | exact H] | right; intros [_ H']; exact (H H')].
  - destruct (IH x) as [H|H]; [left; split; [lia | exact H] | right; intros [_ H']; exact (H H')].
Qed.

Lemma cn_ro2 : forall m a w1 w2, bytes_at rsegs m a (le8 w1 ++ le8 w2) -> ro_cells rsegs m a [C8 w1; C8 w2].
Proof. intros m a w1 w2 H. split; [cbn; tauto|]. cbn [cells_bytes cbytes]. rewrite app_nil_r. exact H. Qed.

Lemma cn_skip_add : forall (l a b : list byte) n, skipn n l = a ++ b -> skipn (n + length a) l = b.
Proof. intros l a b n E. rewrite Nat.add_comm, <- skipn_skipn, E. apply skipn_app_exact. Qed.

Lemma cn_c8_cb : forall m a w, rw_cells rsegs m a [C8 w] -> exists jk, rw_cells rsegs m a [CB 8 jk].
Proof.
  intros m a w H. exists (le8 w). apply (rw_cells_retype _ _ _ _ _ H).
  - cbn [cells_wf cell_wf]. split; [exact (length_le8 w) | exact I].
  - reflexivity.
Qed.

Lemma cn_ret : forall z, 0 <= z < 2 ^ 64 -> z mod 2 = 0 -> ret_pc (Z_to_bv 64 z) = Z_to_bv 64 z.
Proof. intros z Hz H2. apply ret_pc_of_ok. apply ret_ok_even. rewrite unsigned_lit by lia. exact H2. Qed.

Lemma cn_bv10 : Z_to_bv 64 1 <> Z_to_bv 64 0.
Proof. intros E. apply (f_equal bv_unsigned) in E. vm_compute in E. discriminate. Qed.

Lemma cn_nul_prefix : forall a b x y : list byte, ~ In (Z_to_bv 8 0) a -> ~ In (Z_to_bv 8 0) b ->
  a ++ Z_to_bv 8 0 :: x = b ++ Z_to_bv 8 0 :: y -> a = b.
Proof.
  induction a as [|c a IH]; intros [|d b] x y Na Nb E; cbn [app] in E.
  - reflexivity.
  - injection E as E1 _. exfalso. apply Nb. left. exact (eq_sym E1).
  - injection E as E1 _. exfalso. apply Na. left. exact E1.
  - injection E as E1 E2. subst d. f_equal. apply (IH b x y); [intro X; apply Na; right; exact X | intro X; apply Nb; right; exact X | exact E2].
Qed.

Lemma cn_memcmp_refl : forall n l, (n <= length l)%nat -> memcmp_model l l n = Some 0.
Proof.
  induction n as [|n IH]; intros [|c l] Hn; cbn [length] in Hn; try lia; [reflexivity|reflexivity|].
  cbn [memcmp_model]. rewrite Z.eqb_refl. apply IH. lia.
Qed.

Lemma cn_bytes_skip : forall m a (l : list byte) k, bytes_at rsegs m a l -> (k <= length l)%nat ->
  bytes_at rsegs m (a + Z.of_nat k) (skipn k l).
Proof.
  intros m a l k H Hk. rewrite <- (firstn_skipn k l) in H. apply bytes_at_app in H. destruct H as [_ H].
  rewrite length_firstn in H. replace (Nat.min k (length l)) with k in H by lia. exact H.
Qed.

Lemma cn_bytes_first : forall m a (l : list byte) k, bytes_at rsegs m a l -> bytes_at rsegs m a (firstn k l).
Proof. intros m a l k H. rewrite <- (firstn_skipn k l) in H. apply bytes_at_app in H. exact (proj1 H). Qed.

Lemma cn_firstn_app_l : forall {X} (a b : list X), firstn (length a) (a ++ b) = a.
Proof. intros X a b. rewrite firstn_app, firstn_all, Nat.sub_diag, firstn_O, app_nil_r. reflexivity. Qed.

Lemma cn_nodup_fst0 : forall {X Y} (l : list (X * Y)) x a b, List.NoDup (map fst l) -> In (x, a) l -> In (x, b) l ->
  a = b.
Proof.
  intros X Y l. induction l as [|[y c] l IH]; intros x a b ND Ha Hb; [destruct Ha|].
  cbn [map fst] in ND. inversion ND as [|z l' Hn Hl]; subst.
  destruct Ha as [Ea|Ha]; destruct Hb as [Eb|Hb].
  - injection Ea as E1 E2. injection Eb as E3 E4. congruence.
  - injection Ea as E1 E2. subst. exfalso. apply Hn. exact (in_map fst _ (x, b) Hb).
  - injection Eb as E3 E4. subst. exfalso. apply Hn. exact (in_map fst _ (x, a) Ha).
  - exact (IH x a b Hl Ha Hb).
Qed.

Lemma cn_run0 : next_line_contract -> bcmp_contract ->
  forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (lo V N CAP q : Z) (x : list byte)
    (at0 nout out : word) (ob rest jl jn : list byte),
  s5 = Z_to_bv 64 0x31f4c ->
  bytes_at rsegs m 0x318a8 [Z_to_bv 8 0] ->
  rw_cells rsegs m (bv_unsigned s2) [C8 (Z_to_bv 64 V); C4 (Z_to_bv 64 N); C4 (Z_to_bv 64 CAP)] ->
  ro_cells rsegs m V [C8 (Z_to_bv 64 q); C8 (Z_to_bv 64 (Z.of_nat (length x)))] ->
  0 < V -> V mod 8 = 0 ->
  bytes_at rsegs m q x -> ~ In (Z_to_bv 8 0) x ->
  stk rsegs m lo (bv_unsigned sp) -> lo + 48 <= bv_unsigned sp -> mem_inv rsegs m ->
  rw_cells rsegs m (bv_unsigned s0) [C8 at0] -> bv_unsigned s0 mod 8 = 0 -> bv_unsigned sp + 24 <= bv_unsigned s0 ->
  rw_cells rsegs m (bv_unsigned sp + 16) [CB 8 jl] -> rw_cells rsegs m (bv_unsigned sp + 8) [CB 8 jn] ->
  bv_unsigned sp mod 8 = 0 ->
  bytes_at rsegs m G_NOUT (le8 nout) -> bytes_at rsegs m G_OUT (le8 out) ->
  bytes_at rsegs m (bv_unsigned out) ob -> Z.of_nat (length ob) = bv_unsigned nout ->
  G_OUT + 8 <= lo -> bv_unsigned out + bv_unsigned nout <= lo -> 0 < bv_unsigned out ->
  bv_unsigned s2 + 16 <= lo -> V + 16 <= lo -> q + Z.of_nat (length x) <= lo ->
  skipn (Z.to_nat (bv_unsigned at0)) ob = x ++ Z_to_bv 8 0 :: rest ->
  evt rsegs (fun ms' => exists (t0' t1' t2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) m',
      munch [(bv_unsigned sp - 48, bv_unsigned sp); (bv_unsigned s0, bv_unsigned s0 + 8);
             (bv_unsigned sp + 16, bv_unsigned sp + 16 + 8); (bv_unsigned sp + 8, bv_unsigned sp + 8 + 8)] m m' /\
      wmono rsegs m m' /\
      rw_cells rsegs m' (bv_unsigned s0) [C8 (Z_to_bv 64 (bv_unsigned at0 + Z.of_nat (length x) + 1))] /\
      rw_cells rsegs m' (bv_unsigned sp + 16) [C8 (Z_to_bv 64 (bv_unsigned out + bv_unsigned at0))] /\
      rw_cells rsegs m' (bv_unsigned sp + 8) [C8 (Z_to_bv 64 (Z.of_nat (length x)))] /\
      ms' = MS (mkR (Z_to_bv 64 0x14fd0) sp gp tp t0' t1' t2' s0 s1 s1
                    (Z_to_bv 64 (bv_unsigned out + bv_unsigned at0)) (Z_to_bv 64 (Z.of_nat (length x)))
                    a3' a4' a5' a6' a7' s2 (Z_to_bv 64 (Z.of_nat (length x)))
                    (Z_to_bv 64 (bv_unsigned out + bv_unsigned at0))
                    s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
               F (Z_to_bv 64 0x15010) fc None m' (seg_rom rsegs))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x14f50) fc None m (seg_rom rsegs)).
Proof.
  intros NLC BCC ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m lo V N CAP q x at0 nout out ob rest jl jn
    H5 HG HH HV HV0 HV8 HQ NZ ST LO MI PA PAM PAL PL PN SPM GN GO BO LOB GOL OUTL OUT0 HAL VL QL SK.
  pose proof (zr_word sp) as Rsp. pose proof (zr_word s0) as Rs0. pose proof (zr_word s2) as Rs2.
  pose proof (zr_word at0) as Rat. pose proof (zr_word out) as Rout. pose proof (zr_word nout) as Rno.
  unfold inr64 in *.
  assert (LSK : (Z.to_nat (bv_unsigned at0) + length x + 1 <= length ob)%nat).
  { pose proof (f_equal (@length byte) SK) as E. rewrite length_skipn, length_app in E. cbn [length] in E. lia. }
  pose proof (bytes_at_bound _ _ _ _ HQ) as HQb.
  eapply evt_cut.
  { apply (cn_head ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
             F fc m 0 V N CAP q (Z.of_nat (length x)) H5 HG ltac:(lia) HH HV ltac:(lia) HV8). }
  intros ms1 [(C & _)|(_ & ->)]; [lia|].
  pose proof (NLC (Z_to_bv 64 0x14f88) sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
                F fc m lo (bv_unsigned s0) (bv_unsigned sp + 16) (bv_unsigned sp + 8) at0 nout out jl jn ob) as HN.
  cbv zeta in HN. unfold NEXT_LINE_FRAME in HN. unfold G_NOUT, G_OUT in *.
  eapply evt_cut.
  { eapply evt_eq; [|apply HN].
    - rewrite Z_to_bv_bv_unsigned. reflexivity.
    - exact ST.
    - lia.
    - exact MI.
    - exact PA.
    - exact PL.
    - exact PN.
    - exact PAM.
    - Z.div_mod_to_equations. lia.
    - Z.div_mod_to_equations. lia.
    - cbn [disjoint_from]; repeat split; lia.
    - cbn [disjoint_from]; repeat split; lia.
    - cbn [disjoint_from]; repeat split; lia.
    - exact GN.
    - cbn [disjoint_from]; repeat split; lia.
    - exact GO.
    - cbn [disjoint_from]; repeat split; lia.
    - exact BO.
    - exact LOB.
    - cbn [disjoint_from]; repeat split; lia.
    - lia.
    - intros _. split; [lia|]. rewrite SK. apply in_or_app. right. left. reflexivity. }
  intros ms2 (u0 & u1 & u2 & b0 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & m2 &
    -> & MU2 & WM2 & MI2 & ST2 & GN2 & GO2 & BO2 & CASE).
  destruct CASE as [(EAO & _)|(ln & AO & (rest2 & SK2 & NZ2) & Eb0 & PA2 & PL2 & PN2)]; [lia|].
  rewrite SK in SK2.
  assert (Eln : x = ln) by exact (cn_nul_prefix x ln rest rest2 NZ NZ2 SK2). subst ln.
  rewrite (cn_ret 0x14f88) by lia.
  assert (DW : forall a k, a + k <= lo -> 0 <= k ->
            disjoint_from [(bv_unsigned sp - 48, bv_unsigned sp); (bv_unsigned s0, bv_unsigned s0 + 8);
                           (bv_unsigned sp + 16, bv_unsigned sp + 16 + 8); (bv_unsigned sp + 8, bv_unsigned sp + 8 + 8)] a k).
  { intros a k Ha Hk. cbn [disjoint_from]. repeat split; lia. }
  pose proof (rw_cells_transport rsegs _ m m2 _ _ HH MU2 WM2 (DW (bv_unsigned s2) 16 ltac:(lia) ltac:(lia))) as HH2.
  pose proof (ro_cells_transport rsegs _ m m2 _ _ HV MU2 (DW V 16 ltac:(lia) ltac:(lia))) as HV2.
  pose proof (bytes_at_transport rsegs _ m m2 _ _ HQ MU2 (DW q (Z.of_nat (length x)) ltac:(lia) ltac:(lia))) as HQ2.
  eapply evt_cut.
  { apply (cn_cmp (Z_to_bv 64 0x14f88) sp gp tp u0 u1 u2 s0 s1 b0 b1 b2 b3 b4 b5 b6 b7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
             u3 u4 u5 u6 F fc m2 V N CAP q (Z.of_nat (length x)) (Z.of_nat (length x)) (bv_unsigned out + bv_unsigned at0)
             HH2 HV2 ltac:(lia) HV8 ltac:(lia) ltac:(lia)).
    intros _. split; [exact PN2 | exact PL2]. }
  intros ms3 [(E0 & _)|[(_ & NE & _)|(_ & _ & ->)]]; [rewrite Eb0 in E0; exact (False_ind _ (cn_bv10 E0)) | lia |].
  pose proof (cn_bytes_skip m2 (bv_unsigned out) ob (Z.to_nat (bv_unsigned at0)) BO2 ltac:(lia)) as BL.
  rewrite SK, Z2Nat.id in BL by lia. apply (cn_bytes_first _ _ _ (length x)) in BL.
  rewrite cn_firstn_app_l in BL.
  eapply evt_cut.
  { apply (BCC (Z_to_bv 64 0x14fbc) sp gp tp u0 u1 u2 s0 s1 (Z_to_bv 64 (bv_unsigned out + bv_unsigned at0)) (Z_to_bv 64 q)
             (Z_to_bv 64 (Z.of_nat (length x))) b3 b4 b5 b6 b7 s2 (Z_to_bv 64 (Z.of_nat (length x)))
             (Z_to_bv 64 (bv_unsigned out + bv_unsigned at0)) s5 s6 s7 s8 s9 s10 s11 u3 u4 u5 u6 F fc m2 x x 0).
    - rewrite unsigned_lit by lia. exact BL.
    - rewrite unsigned_lit by lia. exact HQ2.
    - rewrite unsigned_lit, Nat2Z.id by lia. apply cn_memcmp_refl. lia.
    - exact MI2. }
  intros ms4 (v0 & v1 & v2 & c1 & c2 & c3 & c4 & c5 & c6 & c7 & v3 & v4 & v5 & v6 & m4 & -> & MU4 & WM4 & _ & _ & _).
  rewrite (cn_ret 0x14fbc) by lia.
  eapply evt_cut.
  { apply (cn_gm (Z_to_bv 64 0x14fbc) sp gp tp v0 v1 v2 s0 s1 (Z_to_bv 64 0) c1 c2 c3 c4 c5 c6 c7
             s2 (Z_to_bv 64 (Z.of_nat (length x))) (Z_to_bv 64 (bv_unsigned out + bv_unsigned at0)) s5 s6 s7 s8 s9 s10 s11
             v3 v4 v5 v6 F fc m4). }
  intros ms5 [(NE & _)|(_ & ->)]; [exfalso; exact (NE eq_refl)|].
  apply evt_done. exists v0, v1, v2, c3, c4, c5, c6, c7, v3, v4, v5, v6, m4.
  split; [exact (munch_trans _ m m2 m4 MU2 (munch_weaken [] _ m2 m4 (fun _ _ => I) MU4))|].
  split; [exact (wmono_trans rsegs m m2 m4 WM2 WM4)|].
  split; [exact (rw_cells_transport rsegs [] m2 m4 _ _ PA2 MU4 WM4 I)|].
  split; [exact (rw_cells_transport rsegs [] m2 m4 _ _ PL2 MU4 WM4 I)|].
  split; [exact (rw_cells_transport rsegs [] m2 m4 _ _ PN2 MU4 WM4 I)|].
  reflexivity.
Qed.

Lemma cn_run1 : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (gone V N CAP q L0 : Z),
  s5 = Z_to_bv 64 0x31f4c -> bytes_at rsegs m 0x318a8 [Z_to_bv 8 gone] -> 0 <= gone < 256 -> gone <> 0 ->
  rw_cells rsegs m (bv_unsigned s2) [C8 (Z_to_bv 64 V); C4 (Z_to_bv 64 N); C4 (Z_to_bv 64 CAP)] ->
  ro_cells rsegs m V [C8 (Z_to_bv 64 q); C8 (Z_to_bv 64 L0)] -> 0 < V < 2 ^ 64 -> V mod 8 = 0 ->
  evt rsegs (fun ms' =>
      ms' = MS (mkR (Z_to_bv 64 0x14fd0) sp gp tp t0 t1 t2 s0 s1 s1 (Z_to_bv 64 q) (Z_to_bv 64 L0) a3 a4 a5 a6 a7
                    s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (Z_to_bv 64 0x15010) fc None m (seg_rom rsegs))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x14f50) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m gone V N CAP q L0 H5 HG Hg NZ HH HV HV0 HV8.
  eapply evt_cut; [exact (cn_head ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                            t3 t4 t5 t6 F fc m gone V N CAP q L0 H5 HG Hg HH HV HV0 HV8)|].
  intros ms' [(_ & ->)|(E & _)]; [|contradiction].
  apply evt_done. reflexivity.
Qed.

Section CNB.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable Bm : malloc_syms.
Variable API : AllocAPI Bm.
Variable F : ResFormT.
Hypothesis AX : AllocExtra Bm (aa_MR API).
Hypothesis BW : blocks_writable Bm API.
Hypothesis HERRB : errno_addr Bm + 4 <= alloc_ceiling.
Hypothesis NODUP : forall L A mem md, aa_MR API L A mem md -> NoDup (map fst (blocks L A)).
Hypothesis GMC : gesture_model_contract Bm API F.
Hypothesis NLC : next_line_contract.
Hypothesis BCC : bcmp_contract.
Hypothesis LDC : list_drop_contract Bm API F.
Local Notation MR := (aa_MR API).

Lemma cn_rmid_shrink : forall K sp (E E' Fq Fq' : Z -> Prop) L A mem md L' A' mem' md',
  WF A ->
  rmid Bm API K sp E Fq L A mem md L' A' mem' md' ->
  (forall a, E a -> E' a \/ (a < alloc_ceiling /\ ~ in_img Bm a /\
     forall p n, In (p, n) (user_blocks A) -> ~ Fq' (ptr_addr L p) -> ~ (ptr_addr L p <= a < ptr_addr L p + n))) ->
  (forall p n, In (p, n) (user_blocks A) -> 0 < n -> Fq (ptr_addr L p) -> Fq' (ptr_addr L p)) ->
  rmid Bm API K sp E' Fq' L A mem md L' A' mem' md'.
Proof.
  intros K sp E E' Fq Fq' L A mem md L' A' mem' md' HW
    (M1 & W1 & B1 & LY1 & LN1 & PA1 & SV1 & Z01 & OW1 & MD1 & BY1 & BK1 & SC1) HE HF.
  split; [exact M1|]. split; [exact W1|]. split; [exact B1|]. split; [exact LY1|]. split; [exact LN1|].
  split.
  { intros p n Hp _ _. pose proof (hg_ub_prid_lt A p n HW Hp) as Hr. pose proof LY1 as (_ & _ & _ & G).
    destruct p as [r o]. unfold ptr_addr. cbn [loc_addr]. cbn [prid] in Hr. rewrite G by exact Hr. reflexivity. }
  split; [intros p n Hp Hn NF; apply SV1; [exact Hp | exact Hn | intro X; exact (NF (HF p n Hp Hn X))]|].
  split; [exact Z01|]. split; [exact OW1|]. split; [exact MD1|].
  split.
  { intros a Ha NO NO' NS NE'. apply BY1; [exact Ha | exact NO | exact NO' | exact NS |].
    intro X. destruct (HE a X) as [Y | (Y1 & Y2 & _)]; [exact (NE' Y)|].
    destruct Ha as [Ha|Ha]; [lia | exact (Y2 Ha)]. }
  split.
  { intros p n i Hp Hp' NF Hi NE'. apply (BK1 p n i Hp Hp'); [intro X; exact (NF (HF p n Hp ltac:(lia) X)) | exact Hi |].
    intro X. destruct (HE _ X) as [Y | (_ & _ & Y)]; [exact (NE' Y)|]. exact (Y p n Hp NF ltac:(lia)). }
  exact SC1.
Qed.

Lemma cn_rmid_keep : forall K sp (E Fq : Z -> Prop) L A mem md L' A' mem' md' q m,
  WF A -> rmid Bm API K sp E Fq L A mem md L' A' mem' md' ->
  In (q, m) (blocks L A) -> ~ Fq q -> In (q, m) (blocks L' A').
Proof.
  intros K sp E Fq L A mem md L' A' mem' md' q m HW R Hin NF.
  pose proof R as (_ & _ & _ & _ & _ & PA & SV & Z0 & _).
  apply cn_blocks_in in Hin as (p & Hp & <-).
  pose proof (cn_ub_nonneg A p m HW Hp) as Hm.
  destruct (Z.eq_dec m 0) as [->|Hm0].
  - destruct (Z0 p Hp) as [Hp' EA]. rewrite <- EA. exact (cn_blocks_of L' A' p 0 Hp').
  - assert (Hp' : In (p, m) (user_blocks A')) by (apply SV; [exact Hp | lia | exact NF]).
    rewrite <- (PA p m Hp Hp' NF). exact (cn_blocks_of L' A' p m Hp').
Qed.

Lemma cn_sptr_keep : forall K sp E Fq L1 A1 m1 md1 L2 A2 m2 md2 a n,
  NoDup (map fst (blocks L1 A1)) -> rmid Bm API K sp E Fq L1 A1 m1 md1 L2 A2 m2 md2 ->
  In (a, n) (blocks L1 A1) -> 0 < n -> ~ Fq a -> sptr_of L2 A2 a = sptr_of L1 A1 a.
Proof.
  intros K sp E Fq L1 A1 m1 md1 L2 A2 m2 md2 a n ND R Hin Hn NF.
  pose proof R as (M2 & _ & _ & _ & _ & PA & SV & _).
  destruct (sptr_of_spec L1 A1 a n ND Hin) as (Hp & Ea).
  assert (NF' : ~ Fq (ptr_addr L1 (sptr_of L1 A1 a))) by (rewrite Ea; exact NF).
  pose proof (SV _ n Hp Hn NF') as Hp'.
  pose proof (PA _ n Hp Hp' NF') as Ep.
  transitivity (sptr_of L2 A2 (ptr_addr L2 (sptr_of L1 A1 a))); [rewrite Ep, Ea; reflexivity|].
  exact (sptr_of_eq L2 A2 _ n (NODUP L2 A2 m2 md2 M2) Hp').
Qed.

Lemma cn_seq : forall K sp E Fq E2 F2 L A mem md L1 A1 m1 md1 L2 A2 m2 md2,
  WF A -> rmid Bm API K sp E Fq L A mem md L1 A1 m1 md1 -> rmid Bm API K sp E2 F2 L1 A1 m1 md1 L2 A2 m2 md2 ->
  (forall a, E2 a -> E a \/ (a < alloc_ceiling /\ ~ in_img Bm a /\
     forall p n, In (p, n) (user_blocks A) -> ~ Fq (ptr_addr L p) -> ~ (ptr_addr L p <= a < ptr_addr L p + n))) ->
  (forall p n, In (p, n) (user_blocks A) -> 0 < n -> F2 (ptr_addr L p) -> Fq (ptr_addr L p)) ->
  rmid Bm API K sp E Fq L A mem md L2 A2 m2 md2.
Proof.
  intros K sp E Fq E2 F2 L A mem md L1 A1 m1 md1 L2 A2 m2 md2 HW R1 R2 HE HF.
  apply (cn_rmid_shrink K sp _ E _ Fq L A mem md L2 A2 m2 md2 HW
           (rmid_seq Bm API _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HW R1 R2)).
  - intros a [X|X]; [left; exact X | exact (HE a X)].
  - intros p n Hp Hn [X|X]; [exact X | exact (HF p n Hp Hn X)].
Qed.

Lemma cn_blk_range : forall L A mem md q k, MR L A mem md -> In (q, k) (blocks L A) ->
  4096 <= q /\ q + k <= alloc_ceiling.
Proof.
  intros L A mem md q k HM H. destruct (cn_blocks_in L A q k H) as (p & Hp & <-).
  exact (mr_blocks_range _ _ (aa_laws API) L A mem md p k HM Hp).
Qed.

Lemma cn_blk_side : forall K sp E Fq L A mem md L1 A1 m1 md1 q k a,
  WF A -> rmid Bm API K sp E Fq L A mem md L1 A1 m1 md1 -> In (q, k) (blocks L1 A1) ->
  (forall m, In (q, m) (blocks L A) -> 0 < m -> Fq q) -> q <= a < q + k ->
  a < alloc_ceiling /\ ~ in_img Bm a /\
  forall p n, In (p, n) (user_blocks A) -> ~ Fq (ptr_addr L p) -> ~ (ptr_addr L p <= a < ptr_addr L p + n).
Proof.
  intros K sp E Fq L A mem md L1 A1 m1 md1 q k a HW R Hq HQ Ha.
  pose proof R as (M1 & _ & _ & _ & _ & PA & SV & _).
  pose proof (cn_blk_range L1 A1 m1 md1 q k M1 Hq) as BR.
  split; [lia|].
  split.
  { pose proof (hf_blk_img Bm API AX L1 A1 m1 md1 q k (a - q) M1 Hq ltac:(lia)) as X.
    replace (q + (a - q)) with a in X by lia. exact X. }
  intros p n Hp NF Hin.
  assert (Hn : 0 < n) by lia.
  pose proof (SV p n Hp Hn NF) as Hp'.
  pose proof (PA p n Hp Hp' NF) as EA.
  pose proof (cn_blocks_of L1 A1 p n Hp') as B1. rewrite EA in B1.
  destruct (Z.eq_dec (ptr_addr L p) q) as [E0|E0].
  - apply NF. rewrite E0. apply (HQ n); [rewrite <- E0; exact (cn_blocks_of L A p n Hp) | exact Hn].
  - destruct (blocks_disjoint Bm API L1 A1 m1 md1 _ _ _ _ M1 B1 Hq E0); lia.
Qed.

Lemma cn_bytes_nil : forall m a (l : list byte), bytes_at rsegs m a l -> l = [] -> forall m', bytes_at rsegs m' a l.
Proof. intros m a l (B0 & B1 & _) -> m'. split; [exact B0|]. split; [exact B1|]. intros i Hi. cbn in Hi. lia. Qed.

Lemma cn_seh_gen : forall h0, set_exp_held h0 (HL (hl_v (hs_expected h0)) (hl_cap (hs_expected h0))
  (hl_recs (hs_expected h0)) (hl_junk (hs_expected h0))) (hs_held h0) = h0.
Proof. intros [? ? ? ? ? ? ? ? ? ? ? [? ? ? ?] ?]. reflexivity. Qed.

Section Run.
Variables (L : layout) (A : astate) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model)
  (bnd : rt_R F) (h : hsrc) (j : nat) (gone A0 : Z) (nout out : word) (ob : list byte).

Definition cHA : Z := G_S + SRC_SIZE * Z.of_nat j.
Definition cAT : Z := bv_unsigned (getr regs 11).
Definition cNO : Z := bv_unsigned nout.
Definition cOUT : Z := bv_unsigned out.
Definition cE : hlist := hs_expected h.
Definition cH : hlist := hs_held h.
Definition cBE : nat := count_begin (texts cE).
Definition cLB : Z := Z.of_nat (length (bstream cE)).
Definition cS0 : Z := spZ regs.

Definition cEW (a : Z) : Prop :=
  cHA + 64 <= a < cHA + 96 \/ cAT <= a < cAT + 8 \/
  (0 < hl_cap cE /\ hl_v cE <= a < hl_v cE + 16 * hl_cap cE) \/
  (0 < hl_cap cH /\ hl_v cH <= a < hl_v cH + 16 * hl_cap cH).

Definition cFW (q : Z) : Prop := In q (map fst (hl_recs cE) ++ list_blocks cH).

Definition cval (r : Z) : word :=
  if r =? 2 then Z_to_bv 64 (cS0 - 80) else if r =? 8 then getr regs 11
  else if r =? 9 then Z_to_bv 64 cHA else if r =? 18 then Z_to_bv 64 (cHA + 64)
  else if r =? 21 then Z_to_bv 64 0x31f4c else getr regs (Z_to_bv 5 r).

Definition cRG (R : bvmap 5 word) : Prop :=
  forall r, callee_saved r -> r <> 19 -> r <> 20 -> getr R (Z_to_bv 5 r) = cval r.

Definition cFRM (m : word -> option byte) : Prop :=
  rw_cells rsegs m (cS0 - 56) [C8 (getr regs 21); C8 (getr regs 20); C8 (getr regs 19); C8 (getr regs 18);
                               C8 (getr regs 9); C8 (getr regs 8); C8 (getr regs 1)] /\
  exists j1 j2, rw_cells rsegs m (cS0 - 72) [CB 8 j1] /\ rw_cells rsegs m (cS0 - 64) [CB 8 j2].

Definition cpos (pre : list (Z * list byte)) : Z :=
  if gone =? 0 then A0 + Z.of_nat (length (cn_bs pre)) else A0.

Definition cnm : Z -> tad := known_at L A.
Definition cSH : shl := sh_of cnm cH.
Definition cT (pre : list (Z * list byte)) : trF := check_no_loss_tr 0 cSH (map (shr cnm) pre).
Definition cSp (pre : list (Z * list byte)) : shl := check_no_loss_sh 0 cSH (map (shr cnm) pre).

Lemma cn_cT_app : forall pre rs, cT (pre ++ rs) = cT pre ++ check_no_loss_tr (nretF (cT pre)) (cSp pre) (map (shr cnm) rs).
Proof. intros pre rs. unfold cT, cSp. rewrite map_app, cn_tr_app. reflexivity. Qed.

Lemma cn_cT_snoc : forall pre r,
  cT (pre ++ [r]) = cT pre ++ (gesture_model_tr (cSp pre) (bzs (snd r)) ++ rec_drop_tr (shr cnm r)).
Proof. intros pre r. rewrite cn_cT_app. cbn [map]. rewrite cn_tr_one. reflexivity. Qed.

Lemma cn_cSp_snoc : forall pre r, cSp (pre ++ [r]) = gesture_model_sh (nretF (cT pre)) (cSp pre) (bzs (snd r)).
Proof. intros pre r. unfold cT, cSp. rewrite map_app, cn_sh_app. reflexivity. Qed.

Definition CJ (preH rs : list (Z * list byte)) (L1 : layout) (A1 : astate) (m1 : word -> option byte) (md1 : Model)
    (H1 : hlist) (jk : list byte) : Prop :=
  rmid Bm API CHECK_NO_LOSS_K cS0 cEW cFW L A mem md L1 A1 m1 md1 /\
  st_init_done A1 = true /\ ro_agree rsegs m1 /\
  src_at Bm L1 A1 m1 cHA (set_exp_held h (HL (hl_v cE) (hl_cap cE) rs jk) H1) /\
  rw_cells rsegs m1 cAT [C8 (Z_to_bv 64 (cpos preH))] /\
  cFRM m1 /\
  texts H1 = upds (texts cH) (cn_tx preH) /\
  NoDup (texts H1) /\
  hl_n H1 <= hl_n cH + Z.of_nat (count_begin (cn_tx preH)) /\
  hl_cap H1 <= Z.max 8 (Z.max (hl_cap cH) (2 * (hl_n cH + Z.of_nat (count_begin (cn_tx preH))))) /\
  (forall q m, In (q, m) (blocks L1 A1) ->
     (In (q, m) (blocks L A) /\ (0 < m -> ~ cFW q)) \/ In q (list_blocks H1) \/ In q (map fst rs)) /\
  (forall q m, In (q, m) (blocks L A) -> 0 < m -> ~ cFW q -> ~ In q (list_blocks H1)).

Definition CI (rs : list (Z * list byte)) (L1 : layout) (A1 : astate) (m1 : word -> option byte) (md1 : Model)
    (H1 : hlist) (jk : list byte) (qs : list sptr) : Prop :=
  exists pre, hl_recs cE = pre ++ rs /\ CJ pre rs L1 A1 m1 md1 H1 jk /\
    length qs = nretF (cT pre) /\ rt_ok F A1 (runF F qs bnd (cT pre)) /\
    (forall X, runF F (qs ++ X) bnd (cT pre) = runF F qs bnd (cT pre)) /\
    (forall X Y, sh_rel (qs ++ X) Y (cSp pre) (sh_of (known_at L1 A1) H1)) /\
    (forall r, In r rs -> sptr_of L1 A1 (fst r) = sptr_of L A (fst r)).

Definition J1 (r : Z * list byte) (rs : list (Z * list byte)) (L1 : layout) (A1 : astate)
    (m1 : word -> option byte) (md1 : Model) (H1 : hlist) (jk : list byte) (qs : list sptr) : Prop :=
  exists pre, hl_recs cE = pre ++ r :: rs /\ CJ (pre ++ [r]) (r :: rs) L1 A1 m1 md1 H1 jk /\
    length qs = nretF (cT pre ++ gesture_model_tr (cSp pre) (bzs (snd r))) /\
    rt_ok F A1 (runF F qs bnd (cT pre ++ gesture_model_tr (cSp pre) (bzs (snd r)))) /\
    (forall X, runF F (qs ++ X) bnd (cT pre ++ gesture_model_tr (cSp pre) (bzs (snd r))) =
               runF F qs bnd (cT pre ++ gesture_model_tr (cSp pre) (bzs (snd r)))) /\
    (forall X Y, sh_rel (qs ++ X) Y (cSp (pre ++ [r])) (sh_of (known_at L1 A1) H1)) /\
    (forall r', In r' (r :: rs) -> sptr_of L1 A1 (fst r') = sptr_of L A (fst r')).

Hypothesis SEG : ms_segs Bm = rsegs.
Hypothesis PRE : call_pre_k Bm MR CHECK_NO_LOSS_K L A regs mem md.
Hypothesis INIT : st_init_done A = true.
Hypothesis RO : ro_agree rsegs mem.
Hypothesis PLR : forall a, G_GONE <= a < G_S + SRC_SIZE * SOURCES_MAX -> img_plain Bm a.
Hypothesis Hj4 : (j < 4)%nat.
Hypothesis R10 : getr regs 10 = Z_to_bv 64 cHA.
Hypothesis SRC : src_at Bm L A mem cHA h.
Hypothesis NDT : NoDup (texts cH).
Hypothesis HNE : hl_n cE < 2 ^ 26.
Hypothesis HNH : hl_n cH + Z.of_nat cBE < 2 ^ 22.
Hypothesis ATM : cAT mod 8 = 0.
Hypothesis ATL : cS0 <= cAT.
Hypothesis ATH : cAT + 8 <= 2 ^ 63.
Hypothesis CAT : rw_cells rsegs mem cAT [C8 (Z_to_bv 64 A0)].
Hypothesis GR : 0 <= gone < 256.
Hypothesis CGN : bytes_at rsegs mem G_GONE [Z_to_bv 8 gone].
Hypothesis CNO : bytes_at rsegs mem G_NOUT (le8 nout).
Hypothesis COU : bytes_at rsegs mem G_OUT (le8 out).
Hypothesis COB : bytes_at rsegs mem cOUT ob.
Hypothesis LOB : Z.of_nat (length ob) = cNO.
Hypothesis OBD : ob = [] \/
  exists CO, cNO <= CO /\ In (cOUT, CO) (blocks L A) /\ fresh_block Bm cOUT CO /\ ~ In cOUT (hs_blocks h).
Hypothesis A0R : 0 <= A0 <= cNO.
Hypothesis SKP : gone = 0 -> exists rest, skipn (Z.to_nat A0) ob = bstream cE ++ rest.
Hypothesis RES : rt_ok F A bnd.
Hypothesis ROOM : forall qs, length qs = nretF (cT (hl_recs cE)) -> roomF F qs bnd (cT (hl_recs cE)).

Lemma cn_pre_facts : MR L A mem md /\ WF A /\ bounded A /\ YK0s.ret_ok (getr regs 1) /\ cS0 mod 16 = 0 /\
  alloc_ceiling + 8384 <= cS0 /\ cS0 < 2 ^ 63 /\ (forall a, cS0 - 8384 <= a < cS0 -> writable_at rsegs mem a) /\
  getr regs 4 = Z_to_bv 64 (ms_tp Bm) /\ (forall a, errno_addr Bm <= a < errno_addr Bm + 4 -> writable_at rsegs mem a).
Proof.
  pose proof PRE as (HMR & HWF & HBD & HRA & HAL & HCEIL & H63 & HWS & HTP & HERR & _).
  assert (EK : CHECK_NO_LOSS_K = 8384) by reflexivity. rewrite EK in *.
  rewrite SEG in HWS, HERR. unfold cS0. tauto.
Qed.

Lemma cn_ha : 203040 <= cHA <= 203328 /\ (forall a, cHA <= a < cHA + 96 -> img_plain Bm a) /\ cHA + 96 <= 0x31aa0.
Proof.
  assert (H1 : 203040 <= cHA <= 203328) by (unfold cHA, G_S, SRC_SIZE; lia).
  split; [exact H1|]. split; [|lia].
  intros a Ha. apply PLR. unfold G_GONE, G_S, SRC_SIZE, SOURCES_MAX, cHA in *. lia.
Qed.

Lemma cn_ha8 : cHA mod 8 = 0.
Proof. unfold cHA, G_S, SRC_SIZE. Z.div_mod_to_equations. lia. Qed.

Lemma cn_cfw_hs : forall q, cFW q -> In q (hs_blocks h).
Proof.
  intros q Hq. unfold cFW, hs_blocks in *. apply in_app_iff in Hq as [Hq|Hq].
  - apply in_app_iff. right. apply in_app_iff. right. apply in_app_iff. left.
    unfold list_blocks. apply in_app_iff. right. exact Hq.
  - apply in_app_iff. right. apply in_app_iff. right. apply in_app_iff. right. exact Hq.
Qed.

Lemma cn_bimg : forall K sp E Fq L1 A1 m1 md1 L2 A2 m2 md2 a bs,
  alloc_ceiling <= sp - K -> MR L1 A1 m1 md1 -> rmid Bm API K sp E Fq L1 A1 m1 md1 L2 A2 m2 md2 ->
  bytes_at rsegs m1 a bs -> (forall i, 0 <= i < Z.of_nat (length bs) -> img_plain Bm (a + i) /\ ~ E (a + i)) ->
  bytes_at rsegs m2 a bs.
Proof.
  intros K sp E Fq L1 A1 m1 md1 L2 A2 m2 md2 a bs HK HM R H D. rewrite <- SEG in H |- *.
  exact (rmid_bytes_img Bm API AX K sp E Fq L1 A1 m1 md1 L2 A2 m2 md2 a bs (hg_img_low Bm SEG) HK HM R H D).
Qed.

Lemma cn_rwimg : forall K sp E Fq L1 A1 m1 md1 L2 A2 m2 md2 a cs,
  alloc_ceiling <= sp - K -> MR L1 A1 m1 md1 -> rmid Bm API K sp E Fq L1 A1 m1 md1 L2 A2 m2 md2 ->
  rw_cells rsegs m1 a cs -> (forall i, 0 <= i < Z.of_nat (cells_size cs) -> img_plain Bm (a + i) /\ ~ E (a + i)) ->
  rw_cells rsegs m2 a cs.
Proof.
  intros K sp E Fq L1 A1 m1 md1 L2 A2 m2 md2 a cs HK HM R H D. rewrite <- SEG in H |- *.
  exact (rmid_rw_img Bm API AX K sp E Fq L1 A1 m1 md1 L2 A2 m2 md2 a cs (hg_img_low Bm SEG) HK HM R H D).
Qed.

Lemma cn_bblk : forall K sp E Fq L1 A1 m1 md1 L2 A2 m2 md2 q k a bs,
  rmid Bm API K sp E Fq L1 A1 m1 md1 L2 A2 m2 md2 -> In (q, k) (blocks L1 A1) -> 0 < k -> ~ Fq q ->
  bytes_at rsegs m1 a bs -> q <= a -> a + Z.of_nat (length bs) <= q + k ->
  (forall i, 0 <= i < Z.of_nat (length bs) -> ~ E (a + i)) -> bytes_at rsegs m2 a bs.
Proof.
  intros K sp E Fq L1 A1 m1 md1 L2 A2 m2 md2 q k a bs R Hin Hk NF H Ha Hb D. rewrite <- SEG in H |- *.
  exact (rmid_bytes_block Bm API BW K sp E Fq L1 A1 m1 md1 L2 A2 m2 md2 q k a bs R Hin Hk NF H Ha Hb D).
Qed.

Lemma cn_rwblk : forall K sp E Fq L1 A1 m1 md1 L2 A2 m2 md2 q k a cs,
  rmid Bm API K sp E Fq L1 A1 m1 md1 L2 A2 m2 md2 -> In (q, k) (blocks L1 A1) -> 0 < k -> ~ Fq q ->
  rw_cells rsegs m1 a cs -> q <= a -> a + Z.of_nat (cells_size cs) <= q + k ->
  (forall i, 0 <= i < Z.of_nat (cells_size cs) -> ~ E (a + i)) -> rw_cells rsegs m2 a cs.
Proof.
  intros K sp E Fq L1 A1 m1 md1 L2 A2 m2 md2 q k a cs R Hin Hk NF H Ha Hb D. rewrite <- SEG in H |- *.
  exact (rmid_rw_block Bm API BW K sp E Fq L1 A1 m1 md1 L2 A2 m2 md2 q k a cs R Hin Hk NF H Ha Hb D).
Qed.

Lemma cn_rwhi : forall K sp E Fq L1 A1 m1 md1 L2 A2 m2 md2 a cs,
  alloc_ceiling <= sp -> MR L1 A1 m1 md1 -> rmid Bm API K sp E Fq L1 A1 m1 md1 L2 A2 m2 md2 ->
  rw_cells rsegs m1 a cs -> sp <= a -> a + Z.of_nat (cells_size cs) <= 2 ^ 64 ->
  (forall i, 0 <= i < Z.of_nat (cells_size cs) -> ~ E (a + i)) -> rw_cells rsegs m2 a cs.
Proof.
  intros K sp E Fq L1 A1 m1 md1 L2 A2 m2 md2 a cs H1 HM R H Ha Hb D. rewrite <- SEG in H |- *.
  exact (rmid_rw_hi Bm API K sp E Fq L1 A1 m1 md1 L2 A2 m2 md2 a cs H1 ltac:(lia) HM R H Ha Hb D).
Qed.

Lemma cn_consts : forall L1 A1 m1 md1, rmid Bm API CHECK_NO_LOSS_K cS0 cEW cFW L A mem md L1 A1 m1 md1 ->
  bytes_at rsegs m1 G_GONE [Z_to_bv 8 gone] /\ bytes_at rsegs m1 G_NOUT (le8 nout) /\
  bytes_at rsegs m1 G_OUT (le8 out) /\ bytes_at rsegs m1 cOUT ob.
Proof.
  intros L1 A1 m1 md1 R.
  pose proof cn_pre_facts as (HM & HW & HB & _ & _ & HC & H63 & HWS & _ & _).
  pose proof cn_ha as (HAr & HAp & HAt).
  pose proof (@YM05.alloc_ceiling_value rc) as ACV. pose proof (@YM05.alloc_ceiling_lt rc) as ACL.
  pose proof SRC as SRC0. apply src_at_iff in SRC0. destruct SRC0 as (SB & LE & LH & NDB).
  pose proof (hf_list_v Bm L A mem _ _ _ LE) as VE. pose proof (hf_list_v Bm L A mem _ _ _ LH) as VH.
  assert (EK : CHECK_NO_LOSS_K = 8384) by reflexivity. rewrite EK in R.
  assert (IMGK : forall a, G_GONE <= a < G_S + 64 -> img_plain Bm a /\ ~ cEW a).
  { intros a Ha. assert (P : img_plain Bm a) by (apply PLR; unfold G_GONE, G_S, SRC_SIZE, SOURCES_MAX in *; lia).
    split; [exact P|]. unfold cEW. intros [X|[X|[X|X]]].
    - unfold cHA, G_S, SRC_SIZE in *. lia.
    - unfold G_GONE, G_S in *. lia.
    - destruct X as (X1 & X2).
      apply (hf_blk_img Bm API AX L A mem md (hl_v cE) (16 * hl_cap cE) (a - hl_v cE) HM (proj1 (VE X1)) ltac:(lia)).
      replace (hl_v cE + (a - hl_v cE)) with a by lia. exact (proj1 P).
    - destruct X as (X1 & X2).
      apply (hf_blk_img Bm API AX L A mem md (hl_v cH) (16 * hl_cap cH) (a - hl_v cH) HM (proj1 (VH X1)) ltac:(lia)).
      replace (hl_v cH + (a - hl_v cH)) with a by lia. exact (proj1 P). }
  assert (HK : alloc_ceiling <= cS0 - 8384) by lia.
  split.
  { apply (cn_bimg _ _ _ _ _ _ _ _ _ _ _ _ _ _ HK HM R CGN).
    intros i Hi. cbn in Hi. apply IMGK. unfold G_GONE, G_S. lia. }
  split.
  { apply (cn_bimg _ _ _ _ _ _ _ _ _ _ _ _ _ _ HK HM R CNO).
    intros i Hi. rewrite length_le8 in Hi. apply IMGK. unfold G_GONE, G_S, G_NOUT. lia. }
  split.
  { apply (cn_bimg _ _ _ _ _ _ _ _ _ _ _ _ _ _ HK HM R COU).
    intros i Hi. rewrite length_le8 in Hi. apply IMGK. unfold G_GONE, G_S, G_OUT. lia. }
  destruct (list_eq_dec (@bv_eq_dec 8) ob []) as [E0|E0]; [exact (cn_bytes_nil mem cOUT ob COB E0 m1)|].
  destruct OBD as [X|(CO & HCO & HIN & HFR & HNI)]; [exact (False_ind _ (E0 X))|].
  assert (LP : 0 < Z.of_nat (length ob)) by (destruct ob; [contradiction | cbn [length]; lia]).
  pose proof (cn_blk_range L A mem md _ _ HM HIN) as BR.
  apply (cn_bblk _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ R HIN ltac:(lia) (fun X => HNI (cn_cfw_hs _ X)) COB
           ltac:(lia) ltac:(lia)).
  intros i Hi. unfold cEW. intros [X|[X|[X|X]]].
  - apply (hf_blk_img Bm API AX L A mem md cOUT CO i HM HIN ltac:(lia)). exact (proj1 (HAp (cOUT + i) ltac:(lia))).
  - unfold cS0 in *. lia.
  - destruct X as (X1 & X2). unfold cE in X2. destruct (VE X1) as (B1 & B2).
    assert (D : hl_v cE <> cOUT).
    { intros E1. apply HNI. rewrite <- E1. unfold hs_blocks. apply in_app_iff. right. apply in_app_iff. right.
      apply in_app_iff. left. exact B2. }
    destruct (blocks_disjoint Bm API L A mem md _ _ _ _ HM B1 HIN D); lia.
  - destruct X as (X1 & X2). unfold cH in X2. destruct (VH X1) as (B1 & B2).
    assert (D : hl_v cH <> cOUT).
    { intros E1. apply HNI. rewrite <- E1. unfold hs_blocks. apply in_app_iff. right. apply in_app_iff. right.
      apply in_app_iff. right. exact B2. }
    destruct (blocks_disjoint Bm API L A mem md _ _ _ _ HM B1 HIN D); lia.
Qed.

Lemma cn_src_gen : forall K sp E Fq L1 A1 m1 md1 L2 A2 m2 md2 h1,
  alloc_ceiling <= sp - K -> MR L1 A1 m1 md1 ->
  rmid Bm API K sp E Fq L1 A1 m1 md1 L2 A2 m2 md2 ->
  src_at Bm L1 A1 m1 cHA h1 ->
  (forall a, cHA <= a < cHA + 96 -> ~ E a) ->
  (forall q, In q (hs_blocks h1) -> kept_block E Fq L1 A1 q) ->
  src_at Bm L2 A2 m2 cHA h1.
Proof.
  intros K sp E Fq L1 A1 m1 md1 L2 A2 m2 md2 h1 HK HM R S HE HB.
  pose proof cn_ha as (_ & HAp & _).
  apply src_at_iff in S. destruct S as (SB & LE & LH & ND).
  apply src_at_iff. split; [|split; [|split]].
  - apply (src_base_rmid Bm API AX BW K sp E Fq L1 A1 m1 md1 L2 A2 m2 md2 cHA h1 SEG HK HM R SB).
    + intros i Hi. split; [apply HAp; lia | apply HE; lia].
    + intros q [Hq|Hq]; apply HB; unfold hs_blocks; [apply in_or_app; left; exact Hq|].
      subst q. apply in_app_iff. right. apply in_app_iff. left. left. reflexivity.
  - apply (list_at_rmid Bm API AX BW K sp E Fq L1 A1 m1 md1 L2 A2 m2 md2 (cHA + 64) _ true SEG HK HM R LE).
    + intros i Hi. split; [apply HAp; lia | apply HE; lia].
    + intros q Hq. apply HB. unfold hs_blocks. apply in_app_iff. right. apply in_app_iff. right.
      apply in_app_iff. left. exact Hq.
  - apply (list_at_rmid Bm API AX BW K sp E Fq L1 A1 m1 md1 L2 A2 m2 md2 (cHA + 80) _ true SEG HK HM R LH).
    + intros i Hi. split; [apply HAp; lia | apply HE; lia].
    + intros q Hq. apply HB. unfold hs_blocks. apply in_app_iff. right. apply in_app_iff. right.
      apply in_app_iff. right. exact Hq.
  - exact ND.
Qed.

Lemma cn_hiseg : forall L1 A1 m1 md1 m0' m2 W (Ew : Z -> Prop),
  rmid Bm API CHECK_NO_LOSS_K cS0 cEW cFW L A mem md L1 A1 m1 md1 -> ro_agree rsegs m1 ->
  mem_rel rsegs m2 m0' -> ro_same rsegs m1 m2 ->
  munch W (normalize rsegs m1) m0' -> wmono rsegs (normalize rsegs m1) m0' ->
  (forall x, 0 <= x < 2 ^ 64 -> ~ outside W x -> (cS0 - 8384 <= x < cS0) \/ Ew x) ->
  (forall x, Ew x -> alloc_ceiling <= x) ->
  rmid Bm API 8384 cS0 Ew (fun _ => False) L1 A1 m1 md1 L1 A1 m2 md1 /\ munch W m1 m2 /\ wmono rsegs m1 m2.
Proof.
  intros L1 A1 m1 md1 m0' m2 W Ew R RO1 REL ROS MU WM HW HE.
  pose proof cn_pre_facts as (_ & _ & _ & _ & _ & HC & H63 & _ & _ & _).
  assert (EK : CHECK_NO_LOSS_K = 8384) by reflexivity. rewrite EK in R.
  pose proof R as (M1 & W1 & B1 & _ & _ & _ & _ & _ & _ & _ & _ & _ & SC1).
  pose proof (aa_laws API) as LAWS.
  pose proof (@YM05.alloc_ceiling_value rc) as ACV. pose proof (@YM05.alloc_ceiling_lt rc) as ACL.
  apply (rmid_norm Bm API 8384 cS0 Ew (fun _ => False) L1 A1 m1 md1 m0' m2 W SEG RO1 REL ROS MU WM M1 W1 B1
           ltac:(lia)).
  - exact SC1.
  - exact HW.
  - intros a Ho. destruct (cn_outside_dec W a) as [O|O]; [exact O|]. exfalso.
    pose proof (mr_owned_low _ _ LAWS _ _ _ _ a M1 Ho).
    destruct (HW a ltac:(lia) O) as [X|X]; [lia | pose proof (HE a X); lia].
  - intros p n i Hp Hi O. exfalso. destruct (mr_blocks _ _ LAWS _ _ _ _ p n i M1 Hp Hi) as (_ & B2 & B3 & _).
    destruct (HW (ptr_addr L1 p + i) ltac:(lia) O) as [X|X]; [lia | pose proof (HE _ X); lia].
Qed.

Lemma cn_cb_le : forall pre rs, hl_recs cE = pre ++ rs -> (count_begin (cn_tx pre) <= cBE)%nat.
Proof.
  intros pre rs E. unfold cBE, texts. change (map (fun r => bzs (snd r)) (hl_recs cE)) with (cn_tx (hl_recs cE)).
  rewrite E, cn_tx_app, cn_cb_app. lia.
Qed.

Lemma cn_nodup_fst : forall L1 A1 m1 md1 q k1 k2, MR L1 A1 m1 md1 ->
  In (q, k1) (blocks L1 A1) -> In (q, k2) (blocks L1 A1) -> k1 = k2.
Proof.
  intros L1 A1 m1 md1 q k1 k2 HM H1 H2.
  exact (cn_nodup_fst0 _ q k1 k2 (proj1 (hf_nodup _) (NODUP L1 A1 m1 md1 HM)) H1 H2).
Qed.

Lemma cn_cfw_dec : forall q, cFW q \/ ~ cFW q.
Proof. intros q. unfold cFW. destruct (in_dec Z.eq_dec q (map fst (hl_recs cE) ++ list_blocks cH)); tauto. Qed.

Lemma cn_gm_call : forall pre q x rs L1 A1 m2 md1 H1 jk qs regs2 LINE,
  hl_recs cE = pre ++ (q, x) :: rs ->
  rmid Bm API 8384 cS0 cEW cFW L A mem md L1 A1 m2 md1 ->
  st_init_done A1 = true -> ro_agree rsegs m2 ->
  src_at Bm L1 A1 m2 cHA (set_exp_held h (HL (hl_v cE) (hl_cap cE) ((q, x) :: rs) jk) H1) ->
  rw_cells rsegs m2 cAT [C8 (Z_to_bv 64 (cpos (pre ++ [(q, x)])))] ->
  cFRM m2 ->
  texts H1 = upds (texts cH) (cn_tx pre) ->
  NoDup (texts H1) ->
  hl_n H1 <= hl_n cH + Z.of_nat (count_begin (cn_tx pre)) ->
  hl_cap H1 <= Z.max 8 (Z.max (hl_cap cH) (2 * (hl_n cH + Z.of_nat (count_begin (cn_tx pre))))) ->
  (forall q0 m, In (q0, m) (blocks L1 A1) ->
     (In (q0, m) (blocks L A) /\ (0 < m -> ~ cFW q0)) \/ In q0 (list_blocks H1) \/ In q0 (map fst ((q, x) :: rs))) ->
  (forall q0 m, In (q0, m) (blocks L A) -> 0 < m -> ~ cFW q0 -> ~ In q0 (list_blocks H1)) ->
  length qs = nretF (cT pre) -> rt_ok F A1 (runF F qs bnd (cT pre)) ->
  (forall X, runF F (qs ++ X) bnd (cT pre) = runF F qs bnd (cT pre)) ->
  (forall X Y, sh_rel (qs ++ X) Y (cSp pre) (sh_of (known_at L1 A1) H1)) ->
  (forall r, In r ((q, x) :: rs) -> sptr_of L1 A1 (fst r) = sptr_of L A (fst r)) ->
  cRG regs2 -> getr regs2 1 = Z_to_bv 64 0x14fd0 -> getr regs2 10 = Z_to_bv 64 cHA ->
  getr regs2 11 = Z_to_bv 64 LINE -> getr regs2 12 = Z_to_bv 64 (Z.of_nat (length x)) -> 0 <= LINE < 2 ^ 64 ->
  bytes_at rsegs m2 LINE x -> ~ In (Z_to_bv 8 0) x -> Z.of_nat (length x) <= 6000 ->
  (exists q' m', In (q', m') (blocks L1 A1) /\ fresh_block Bm q' m' /\ q' <= LINE /\
     LINE + Z.of_nat (length x) <= q' + m' /\ ~ In q' (list_blocks H1)) ->
  SR rsegs (mkCfg (YK11.mkst regs2 (Z_to_bv 64 0x15010) m2 (seg_rom rsegs)) md1)
    (fun c => exists L2 A2 R2 m3 md2 H2 qs2, J1 (q, x) rs L2 A2 m3 md2 H2 jk qs2 /\ cRG R2 /\
       c = mkCfg (YK11.mkst R2 (Z_to_bv 64 0x14fd0) m3 (seg_rom rsegs)) md2).
Proof.
  intros pre q x rs L1 A1 m2 md1 H1 jk qs regs2 LINE EPR RMc INI1 RO2 SRC2 AT2 FRM2 TX1 ND1 HN1 HC1 BL1 BK1
    LQ1 RS1 ST1 NM1 EN1 RG2 E1 E10 E11 E12 LR BLN NZ L6 BLK.
  pose proof cn_pre_facts as (HM & HW & HB & HRA & HAL & HC & H63 & HWS & HTP & HERR).
  pose proof cn_ha as (HAr & HAp & HAt).
  pose proof (aa_laws API) as LAWS.
  pose proof (@YM05.alloc_ceiling_value rc) as ACV. pose proof (@YM05.alloc_ceiling_lt rc) as ACL.
  pose proof RMc as (M2 & W2 & B2 & _ & _ & _ & _ & _ & _ & _ & _ & _ & SC2).
  assert (G2 : getr regs2 2 = Z_to_bv 64 (cS0 - 80))
    by exact (RG2 2 ltac:(unfold callee_saved; lia) ltac:(lia) ltac:(lia)).
  assert (SP2 : spZ regs2 = cS0 - 80).
  { unfold spZ. transitivity (bv_unsigned (Z_to_bv 64 (cS0 - 80))); [f_equal; exact G2 | apply unsigned_lit; lia]. }
  assert (G4 : getr regs2 4 = Z_to_bv 64 (ms_tp Bm)).
  { transitivity (cval 4); [exact (RG2 4 ltac:(unfold callee_saved; lia) ltac:(lia) ltac:(lia)) | exact HTP]. }
  assert (UL : bv_unsigned (getr regs2 11) = LINE) by (rewrite E11; apply unsigned_lit; lia).
  assert (UN : bv_unsigned (getr regs2 12) = Z.of_nat (length x)) by (rewrite E12; apply unsigned_lit; lia).
  pose proof SRC2 as S2. apply src_at_iff in S2. destruct S2 as (SB2 & LE2 & LH2 & NDB2).
  cbn [set_exp_held hs_expected hs_held] in LE2, LH2.
  pose proof LE2 as (_ & _ & _ & _ & _ & LFA2).
  pose proof (hf_list_head Bm L1 A1 m2 _ _ _ LH2) as (_ & _ & VR1 & VB1).
  pose proof (hf_list_v Bm L1 A1 m2 _ _ _ LH2) as VH1.
  assert (EKG : GESTURE_MODEL_K = 8304) by reflexivity.
  assert (FIN : forall q0 n, In (q0, n) (blocks L A) -> 0 < n -> In q0 (list_blocks H1) -> cFW q0).
  { intros q0 n Hq Hn Hl. destruct (cn_cfw_dec q0) as [X|X]; [exact X|]. exfalso. exact (BK1 q0 n Hq Hn X Hl). }
  assert (NEH : forall r', In r' ((q, x) :: rs) -> ~ In (fst r') (list_blocks H1)).
  { intros r' Hr' Hl. pose proof NDB2 as ND0. apply hf_nodup in ND0. unfold hs_blocks in ND0.
    cbn [set_exp_held hs_pending hs_partial hs_expected hs_held] in ND0.
    apply (hf_nodup_disj (list_blocks (hs_pending h) ++ [hs_partial h] ++
             list_blocks (HL (hl_v cE) (hl_cap cE) ((q, x) :: rs) jk)) (list_blocks H1) (fst r'));
      [rewrite <- !app_assoc; exact ND0 | | exact Hl].
    apply in_or_app. right. apply in_or_app. right. unfold list_blocks. apply in_or_app. right.
    exact (in_map fst _ _ Hr'). }
  assert (Ekq : nretF (gesture_model_tr (cSp pre) (bzs x)) = nretF (gesture_model_tr (sh_of (known_at L1 A1) H1) (bzs x)))
    by exact (tr_rel_nret _ _ _ _ _ _ (gesture_model_rel _ _ _ _ (bzs x) (NM1 [] qs))).
  pose proof GMC as GC. unfold gesture_model_contract in GC. cbv zeta in GC. rewrite SEG in GC.
  unfold GESTURE_MODEL in GC.
  eapply SR_mono.
  { apply (GC L1 A1 regs2 m2 md1 (runF F qs bnd (cT pre)) (set_exp_held h (HL (hl_v cE) (hl_cap cE) ((q, x) :: rs) jk) H1) j x).
    - reflexivity.
    - rewrite EKG. eapply cpk_of_rmid; [exact RMc | exact INI1 | | exact G4 | | | | | |].
      + rewrite E1. apply ret_ok_even. rewrite unsigned_lit by lia. reflexivity.
      + rewrite SP2. Z.div_mod_to_equations. lia.
      + rewrite SP2. lia.
      + rewrite SP2. lia.
      + lia.
      + rewrite SP2. lia.
      + rewrite SP2. lia.
    - exact INI1.
    - exact RO2.
    - intros a Ha. apply PLR. unfold G_GONE, G_S, SRC_SIZE, SOURCES_MAX in *. lia.
    - exact Hj4.
    - exact E10.
    - exact SRC2.
    - exact ND1.
    - change (hl_n H1 < 2 ^ 22). pose proof (cn_cb_le pre ((q, x) :: rs) EPR). unfold cBE in *. lia.
    - change (bytes_at rsegs m2 (bv_unsigned (getr regs2 11)) x). rewrite UL. exact BLN.
    - exact NZ.
    - change (Z.of_nat (length x) = bv_unsigned (getr regs2 12)). rewrite UN. reflexivity.
    - change (bv_unsigned (getr regs2 12) <= 6000). rewrite UN. exact L6.
    - change (exists q0 m0, In (q0, m0) (blocks L1 A1) /\ fresh_block Bm q0 m0 /\ q0 <= bv_unsigned (getr regs2 11) /\
        bv_unsigned (getr regs2 11) + bv_unsigned (getr regs2 12) <= q0 + m0 /\ ~ In q0 (list_blocks H1)).
      rewrite UL, UN. exact BLK.
    - exact RS1.
    - change (forall qs0, length qs0 = nretF (gesture_model_tr (sh_of (known_at L1 A1) H1) (bzs x)) ->
        roomF F qs0 (runF F qs bnd (cT pre)) (gesture_model_tr (sh_of (known_at L1 A1) H1) (bzs x))).
      intros qc LQC.
      assert (ET : exists Rest, cT (hl_recs cE) = cT pre ++ gesture_model_tr (cSp pre) (bzs x) ++ Rest).
      { rewrite EPR, cn_cT_app. cbn [map check_no_loss_tr]. eexists. reflexivity. }
      destruct ET as [Rest ET].
      set (N := nretF (cT (hl_recs cE))).
      assert (LN : (length qs + length qc <= N)%nat) by (unfold N; rewrite ET, !nret_app, <- LQ1, LQC, <- Ekq; lia).
      set (pad := repeat (SP 0 0) (N - length qs - length qc)).
      pose proof (ROOM (qs ++ qc ++ pad)) as RR.
      specialize (RR ltac:(unfold pad; rewrite !length_app, repeat_length; lia)).
      unfold roomF, room_run in RR. rewrite ET in RR.
      apply (proj1 (room_from_app _ _ _ _ _ _ _ _ _ _ _ _)) in RR. destruct RR as [_ RR].
      apply (proj1 (room_from_app _ _ _ _ _ _ _ _ _ _ _ _)) in RR. destruct RR as [RR _].
      pose proof (ST1 (qc ++ pad)) as S1. unfold runF, run_tr in S1.
      rewrite S1, Nat.add_0_l, <- LQ1 in RR.
      exact (proj1 (cn_seg_room F qs qc pad _ _ (bzs x) _ (NM1 (qc ++ pad) qc) LQC) RR). }
  intros c' (L2 & A2 & regs3 & m3 & md2 & H2 & -> & RP & INI2 & (qc & LQC & RSc & SRc & SLc) & RO3 & SRC3 & ND2 &
    TX2 & LN3 & BA & BB & BC & _).
  cbn [set_exp_held hs_held] in RP, LQC, RSc, SRc, SLc, TX2, BA, BB, BC.
  destruct (rp_split Bm API _ _ _ _ _ _ _ _ _ _ _ _ _ RP) as (RMg & PRg). rewrite SP2, EKG in RMg.
  assert (EGL : forall a, (cHA + 80 <= a < cHA + 96 \/ (0 < hl_cap H1 /\ hl_v H1 <= a < hl_v H1 + 16 * hl_cap H1)) ->
            a < alloc_ceiling).
  { intros a [X|(X1 & X2)]; [lia | destruct (VB1 X1); lia]. }
  pose proof (rmid_widen Bm API 8304 (cS0 - 80) 8384 cS0 _ _ _ _ _ _ _ _ _ _ M2 ltac:(lia) ltac:(lia) ltac:(lia)
                ltac:(lia) (fun a Ha => SC2 a (or_introl Ha)) ltac:(intros a Ha X; pose proof (EGL a X); lia) RMg) as RMw.
  assert (RMall : rmid Bm API 8384 cS0 cEW cFW L A mem md L2 A2 m3 md2).
  { apply (cn_seq _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HW RMc RMw).
    - intros a [X|(X1 & X2)]; [left; unfold cEW; left; lia|right].
      apply (cn_blk_side _ _ _ _ _ _ _ _ _ _ _ _ (hl_v H1) (16 * hl_cap H1) a HW RMc (proj1 (VH1 X1))); [|lia].
      intros m0 Hm0 Hp. exact (FIN _ m0 Hm0 Hp (proj2 (VH1 X1))).
    - intros p n Hp Hn X. exact (FIN _ n (cn_blocks_of L A p n Hp) Hn X). }
  assert (HIW : forall a cs, rw_cells rsegs m2 a cs -> cS0 - 80 <= a -> a + Z.of_nat (cells_size cs) <= 2 ^ 64 ->
            rw_cells rsegs m3 a cs).
  { intros a cs H Ha Hb. apply (cn_rwhi 8304 (cS0 - 80) _ _ _ _ _ _ _ _ _ _ a cs ltac:(lia) M2 RMg H Ha Hb).
    intros i Hi X. pose proof (EGL _ X). lia. }
  assert (CB1 : Z.of_nat (count_begin (cn_tx (pre ++ [(q, x)]))) = Z.of_nat (count_begin (cn_tx pre)) + cn_b (bzs x)).
  { rewrite cn_tx_app, cn_cb_app, Nat2Z.inj_add. f_equal. exact (cn_cb_one (bzs x)). }
  pose proof LH2 as (_ & LB2 & _).
  pose proof RMall as (M3 & _).
  assert (RLc : forall Y, sh_rel qc Y (gesture_model_sh 0 (sh_of (known_at L1 A1) H1) (bzs x)) (sh_of (known_at L2 A2) H2)).
  { intros Y. exact (cn_rel_live L2 A2 qc Y _ H2 (NODUP L2 A2 m3 md2 M3) SRc SLc). }
  assert (SG : forall X, runF F ((qs ++ qc) ++ X) bnd (cT pre ++ gesture_model_tr (cSp pre) (bzs x)) =
                runF F qc (runF F qs bnd (cT pre)) (gesture_model_tr (sh_of (known_at L1 A1) H1) (bzs x))).
  { intros X. unfold runF at 1. unfold run_tr. rewrite run_from_app, <- app_assoc.
    pose proof (ST1 (qc ++ X)) as S1. unfold runF, run_tr in S1. rewrite S1, Nat.add_0_l, <- LQ1.
    exact (cn_seg_run F qs qc X _ _ (bzs x) _ (NM1 (qc ++ X) qc) LQC). }
  pose proof (SG []) as SG0. rewrite app_nil_r in SG0.
  exists L2, A2, regs3, m3, md2, H2, (qs ++ qc).
  split; [|split].
  - exists pre. split; [exact EPR|]. split.
    + split; [exact RMall|]. split; [exact INI2|]. split; [exact RO3|]. split; [exact SRC3|].
      split; [exact (HIW _ _ AT2 ltac:(lia) ltac:(cbn; lia))|].
      split.
      { destruct FRM2 as (FA & j1 & j2 & FB & FC).
        split; [exact (HIW _ _ FA ltac:(lia) ltac:(cbn; lia))|].
        exists j1, j2. split; [exact (HIW _ _ FB ltac:(lia) ltac:(cbn; lia)) | exact (HIW _ _ FC ltac:(lia) ltac:(cbn; lia))]. }
      split; [rewrite TX2, cn_tx_app, cn_upds_app, <- TX1; reflexivity|].
      split; [exact ND2|].
      split.
      { rewrite <- cn_texts_length, TX2, CB1. pose proof (cn_upd_len (texts H1) (bzs x)) as U.
        rewrite cn_texts_length in U. lia. }
      split.
      { pose proof SRc as (Rc2 & _). rewrite Rc2, CB1.
        apply cn_cap_step; [rewrite cn_sh_n_of; change (sh_cap (sh_of (known_at L1 A1) H1)) with (hl_cap H1); lia |
                              rewrite cn_sh_n_of; lia | lia | exact HC1]. }
      split.
      { intros q0 m HQ. destruct (BB q0 m HQ) as [(HQ1 & HQ2)|HQ1]; [|right; left; exact HQ1].
        destruct (BL1 q0 m HQ1) as [X|[X|X]]; [left; exact X| |right; right; exact X].
        exfalso. destruct (Z_lt_le_dec 0 m) as [Hm|Hm]; [exact (HQ2 Hm X)|].
        destruct (hf_list_pos Bm L1 A1 m2 _ _ _ q0 LH2 X) as (k & Hk & Hin).
        pose proof (cn_nodup_fst L1 A1 m2 md1 q0 k m M2 Hin HQ1). lia. }
      intros q0 m Hq Hm NF.
      exact (BC q0 m (cn_rmid_keep _ _ _ _ _ _ _ _ _ _ _ _ q0 m HW RMc Hq NF) Hm (BK1 q0 m Hq Hm NF)).
    + cbn [snd]. split; [rewrite length_app, nret_app, LQ1, LQC, Ekq; reflexivity|].
      split; [rewrite SG0; exact RSc|].
      split; [intros X; rewrite (SG X), SG0; reflexivity|].
      split.
      { intros X Y. rewrite cn_cSp_snoc. cbn [snd]. rewrite <- LQ1, <- app_assoc.
        apply (cn_rel_trans _ qc _ _ (gesture_model_sh 0 (sh_of (known_at L1 A1) H1) (bzs x))); [|exact (RLc Y)].
        apply gesture_model_sh_rel; [exact (NM1 (qc ++ X) qc)|].
        pose proof (ret_agree_embed sptr pdefT qs qc X 0 (nretF (gesture_model_tr (sh_of (known_at L1 A1) H1) (bzs x)))
                      ltac:(lia)) as RA.
        rewrite Nat.add_0_r in RA. exact RA. }
      intros r' Hr'. rewrite <- (EN1 r' Hr').
      destruct (proj1 (Forall_forall _ _) LFA2 r' Hr') as (RB' & _).
      exact (cn_sptr_keep _ _ _ _ _ _ _ _ _ _ _ _ _ _ (NODUP L1 A1 m2 md1 M2) RMg RB' ltac:(lia) (NEH r' Hr')).
  - intros r0 Hr H19 H20. rewrite (PRg r0 Hr). exact (RG2 r0 Hr H19 H20).
  - do 2 f_equal. exact E1.
Qed.

Lemma cn_stk : forall E Fq L1 A1 m1 md1, rmid Bm API 8384 cS0 E Fq L A mem md L1 A1 m1 md1 ->
  stk rsegs m1 (cS0 - 8384) (cS0 - 80).
Proof.
  intros E Fq L1 A1 m1 md1 R. pose proof R as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & SC1).
  pose proof cn_pre_facts as (_ & _ & _ & _ & _ & HC & H63 & _ & _ & _).
  pose proof (@YM05.alloc_ceiling_value rc) as ACV.
  split; [lia|]. split; [lia|]. intros a Ha.
  assert (W : writable_at rsegs m1 a) by (rewrite <- SEG; apply SC1; unfold sk; left; lia).
  split; [exact W|]. destruct (writable_hi_present m1 a ltac:(lia) W) as [bb E0]. exists bb.
  unfold mrd, wa. rewrite E0. reflexivity.
Qed.

Lemma cn_step_gm : forall r rs L1 A1 R1 m1 md1 H1 jk qs,
  CI (r :: rs) L1 A1 m1 md1 H1 jk qs -> cRG R1 ->
  SR rsegs (mkCfg (YK11.mkst R1 (Z_to_bv 64 0x14f50) m1 (seg_rom rsegs)) md1)
    (fun c => exists L2 A2 R2 m2 md2 H2 qs2, J1 r rs L2 A2 m2 md2 H2 jk qs2 /\ cRG R2 /\
       c = mkCfg (YK11.mkst R2 (Z_to_bv 64 0x14fd0) m2 (seg_rom rsegs)) md2).
Proof.
  intros [q x] rs L1 A1 R1 m1 md1 H1 jk qs (pre & EPR & CJ1 & LQ1 & RS1 & SQ1 & NM1 & EN1) RG1.
  destruct CJ1 as (RM1 & INI1 & RO1 & SRC1 & AT1 & FRM1 & TX1 & ND1 & HN1 & HC1 & BL1 & BK1).
  pose proof cn_pre_facts as (HM & HW & HB & HRA & HAL & HC & H63 & HWS & HTP & HERR).
  pose proof cn_ha as (HAr & HAp & HAt).
  pose proof (aa_laws API) as LAWS.
  pose proof (@YM05.alloc_ceiling_value rc) as ACV. pose proof (@YM05.alloc_ceiling_lt rc) as ACL.
  assert (EK : CHECK_NO_LOSS_K = 8384) by reflexivity. rewrite EK in RM1.
  pose proof RM1 as (M1 & W1 & B1 & _ & _ & _ & _ & _ & _ & _ & _ & _ & SC1).
  destruct (mr_model _ _ LAWS _ _ _ _ M1) as (Hh1 & Hl1 & _).
  destruct (cn_consts L1 A1 m1 md1 RM1) as (GN1 & NO1 & OU1 & OB1).
  pose proof SRC1 as S1. apply src_at_iff in S1. destruct S1 as (SB1 & LE1 & LH1 & NDB1).
  cbn [set_exp_held hs_expected hs_held] in LE1, LH1.
  pose proof LE1 as (LC1 & LB1 & LAR1 & LND1 & LNV1 & LFA1).
  rewrite SEG in LC1. unfold hl_n in LC1, LB1. cbn [hl_v hl_cap hl_recs] in LC1, LB1, LAR1, LFA1.
  destruct LAR1 as [(C0 & _)|(CP0 & VIN & VFR & VJ & VC)]; [cbn [length] in LB1; lia|].
  destruct (hf_lrec Bm L1 A1 m1 _ _ _ LE1 0 (Z_to_bv 64 q, x) eq_refl) as (R0a & R0b & _ & _ & _ & _).
  cbn [fst snd hl_v hl_cap] in R0a, R0b. rewrite SEG in R0a, R0b.
  replace (hl_v cE + 16 * Z.of_nat 0) with (hl_v cE) in R0a by lia.
  pose proof (proj1 (Forall_forall _ _) LFA1 (q, x) (or_introl eq_refl)) as (RB & RF & RC & RL & _).
  cbn [fst snd] in RB, RF, RC, RL. destruct (RL eq_refl) as (NZ & L6).
  pose proof (cn_blk_range L1 A1 m1 md1 _ _ M1 RB) as QB.
  pose proof (cn_blk_range L1 A1 m1 md1 _ _ M1 VIN) as VB.
  rewrite unsigned_lit in R0b by lia.
  pose proof (cn_bytes_first _ _ _ (length x) R0b) as R0x. rewrite cn_firstn_app_l in R0x.
  assert (E2 : reg_get R1 2 = Z_to_bv 64 (cS0 - 80))
    by exact (RG1 2 ltac:(unfold callee_saved; lia) ltac:(lia) ltac:(lia)).
  assert (E9 : reg_get R1 9 = Z_to_bv 64 cHA)
    by exact (RG1 9 ltac:(unfold callee_saved; lia) ltac:(lia) ltac:(lia)).
  assert (E8 : reg_get R1 8 = Z_to_bv 64 cAT).
  { transitivity (getr regs 11); [exact (RG1 8 ltac:(unfold callee_saved; lia) ltac:(lia) ltac:(lia))|].
    symmetry. apply Z_to_bv_bv_unsigned. }
  assert (E18 : reg_get R1 18 = Z_to_bv 64 (cHA + 64))
    by exact (RG1 18 ltac:(unfold callee_saved; lia) ltac:(lia) ltac:(lia)).
  assert (E21 : reg_get R1 21 = Z_to_bv 64 0x31f4c)
    by exact (RG1 21 ltac:(unfold callee_saved; lia) ltac:(lia) ltac:(lia)).
  assert (U2 : bv_unsigned (Z_to_bv 64 (cS0 - 80)) = cS0 - 80) by (apply unsigned_lit; lia).
  assert (U9 : bv_unsigned (Z_to_bv 64 cHA) = cHA) by (apply unsigned_lit; lia).
  assert (U8 : bv_unsigned (Z_to_bv 64 cAT) = cAT) by (apply unsigned_lit; lia).
  assert (U18 : bv_unsigned (Z_to_bv 64 (cHA + 64)) = cHA + 64) by (apply unsigned_lit; lia).
  assert (VA : 0 < hl_v cE /\ hl_v cE mod 8 = 0).
  { split; [lia|].
    first [pose proof (hf_blk_align Bm API _ _ _ _ _ _ M1 VIN) as A16 |
           pose proof (hf_blk_align Bm API AX _ _ _ _ _ _ M1 VIN) as A16].
    Z.div_mod_to_equations. lia. }
  pose proof (cn_stk _ _ _ _ _ _ RM1) as ST1.
  destruct FRM1 as (FA1 & j1 & j2 & FB1 & FC1).
  assert (KHI : forall q0, kept_block (fun a => cAT <= a < cAT + 8) (fun _ => False) L1 A1 q0).
  { intros q0. split; [intros []|]. intros k i Hin Hi X. pose proof (cn_blk_range L1 A1 m1 md1 _ _ M1 Hin). lia. }
  assert (KF0 : forall q0, kept_block (fun _ => False) (fun _ => False) L1 A1 q0)
    by (intros q0; split; [intros [] | intros k i _ _ []]).
  assert (RG2 : forall R, (forall r, callee_saved r -> r <> 19 -> r <> 20 ->
                   YK11.getr R (Z_to_bv 5 r) = YK11.getr R1 (Z_to_bv 5 r)) -> cRG R).
  { intros R GQ r0 Hr H19 H20. rewrite (GQ r0 Hr H19 H20). exact (RG1 r0 Hr H19 H20). }
  destruct (Z.eq_dec gone 0) as [G0|G0].
  - destruct (SKP G0) as (rest0 & SK0).
    unfold bstream in SK0. change (concat (map (fun r => snd r ++ [Z_to_bv 8 0]) (hl_recs cE))) with (cn_bs (hl_recs cE)) in SK0.
    rewrite EPR, cn_bs_app, <- app_assoc in SK0.
    pose proof (cn_skip_add ob (cn_bs pre) _ (Z.to_nat A0) SK0) as SK1.
    rewrite cn_bs_cons in SK1. cbn [snd] in SK1. rewrite <- app_assoc in SK1. cbn [app] in SK1.
    assert (OBN : ob <> []) by (intros E0; rewrite E0, skipn_nil in SK1; exact (app_cons_not_nil _ _ _ SK1)).
    destruct OBD as [X|(CO & HCO & HIN & HFR & HNI)]; [contradiction|].
    pose proof (cn_blk_range L A mem md _ _ HM HIN) as OBR.
    assert (LSK : (Z.to_nat A0 + length (cn_bs pre) + length x + 1 <= length ob)%nat).
    { pose proof (f_equal (@length byte) SK1) as E0. rewrite length_skipn, length_app in E0. cbn [length] in E0. lia. }
    assert (CPP : cpos pre = A0 + Z.of_nat (length (cn_bs pre))).
    { unfold cpos. rewrite (proj2 (Z.eqb_eq gone 0) G0). reflexivity. }
    assert (CPQ : cpos (pre ++ [(q, x)]) = cpos pre + Z.of_nat (length x) + 1).
    { rewrite CPP. unfold cpos. rewrite (proj2 (Z.eqb_eq gone 0) G0), cn_bs_app, cn_bs_cons, length_app, length_app.
      cbn [length snd cn_bs map concat]. lia. }
    assert (UP : bv_unsigned (Z_to_bv 64 (cpos pre)) = cpos pre) by (apply unsigned_lit; lia).
    assert (SKP2 : skipn (Z.to_nat (cpos pre)) ob = x ++ Z_to_bv 8 0 :: cn_bs rs ++ rest0).
    { rewrite CPP, Z2Nat.inj_add, Nat2Z.id by lia. exact SK1. }
    eapply (kseg R1 (Z_to_bv 64 0x14f50) m1 md1); [vm_compute; reflexivity | exact RO1 | exact Hh1 | exact Hl1 | | |].
    + unfold Regs6ss.mkR_of.
      eapply (cn_run0 NLC BCC) with (lo := cS0 - 8384) (V := hl_v cE) (N := Z.of_nat (length ((q, x) :: rs)))
        (CAP := hl_cap cE) (q := q) (x := x) (at0 := Z_to_bv 64 (cpos pre)) (nout := nout) (out := out) (ob := ob)
        (rest := cn_bs rs ++ rest0) (jl := j2) (jn := j1).
      * exact E21.
      * rewrite G0 in GN1. exact (bytes_at_normalize rsegs m1 _ _ RO1 GN1).
      * rewrite E18, U18. apply rw_cells_normalize; [exact RO1 | exact LC1 |]. intros i Hi. apply hf_ro_glob. cbn in Hi. lia.
      * apply cn_ro2. exact (bytes_at_normalize rsegs m1 _ _ RO1 R0a).
      * exact (proj1 VA).
      * exact (proj2 VA).
      * exact (bytes_at_normalize rsegs m1 _ _ RO1 R0x).
      * exact NZ.
      * rewrite E2, U2. apply stk_normalize; [exact ST1 | lia].
      * rewrite E2, U2. lia.
      * apply mem_inv_normalize.
      * rewrite E8, U8. apply rw_cells_normalize; [exact RO1 | exact AT1 |]. intros i Hi. apply ro_addr_hi. cbn in Hi. lia.
      * rewrite E8, U8. exact ATM.
      * rewrite E8, U8, E2, U2. lia.
      * rewrite E2, U2. replace (cS0 - 80 + 16) with (cS0 - 64) by lia.
        apply rw_cells_normalize; [exact RO1 | exact FC1 |]. intros i Hi. apply ro_addr_hi. cbn in Hi. lia.
      * rewrite E2, U2. replace (cS0 - 80 + 8) with (cS0 - 72) by lia.
        apply rw_cells_normalize; [exact RO1 | exact FB1 |]. intros i Hi. apply ro_addr_hi. cbn in Hi. lia.
      * rewrite E2, U2. Z.div_mod_to_equations. lia.
      * exact (bytes_at_normalize rsegs m1 _ _ RO1 NO1).
      * exact (bytes_at_normalize rsegs m1 _ _ RO1 OU1).
      * exact (bytes_at_normalize rsegs m1 _ _ RO1 OB1).
      * exact LOB.
      * unfold G_OUT. lia.
      * change (cOUT + cNO <= cS0 - 8384). lia.
      * change (0 < cOUT). lia.
      * rewrite E18, U18. lia.
      * lia.
      * lia.
      * rewrite UP. exact SKP2.
    + intros s0 (t0' & t1' & t2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & _ & _ & _ & _ & _ & ->).
      do 3 eexists. reflexivity.
    + intros R pc' m0' regs2 m2 HQ GR2 MREL2 ROS2.
      destruct HQ as (t0' & t1' & t2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & MU & WM & PA2 & PL2 &
        PN2 & EQ).
      injection EQ as ER EP EM. subst R pc' m0'.
      rewrite ?E2, ?E8, ?U2, ?U8 in MU. rewrite ?E8, ?U8, ?UP in PA2. rewrite ?E2, ?U2, ?UP in PL2. rewrite ?E2, ?U2 in PN2.
      destruct (cn_hiseg L1 A1 m1 md1 m' m2 _ (fun a => cAT <= a < cAT + 8) RM1 RO1 MREL2 ROS2 MU WM) as (RMs & MUs & WMs).
      { intros y Hy O. destruct (hg_not_out _ _ O) as (lo0 & hi0 & HIn & Hlh). cbn [In] in HIn.
        destruct HIn as [E0|[E0|[E0|[E0|[]]]]]; injection E0 as <- <-; lia. }
      { intros y Hy. lia. }
      assert (RMc : rmid Bm API 8384 cS0 cEW cFW L A mem md L1 A1 m2 md1).
      { apply (cn_seq _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HW RM1 RMs).
        - intros a X. left. unfold cEW. right. left. exact X.
        - intros p n _ _ []. }
      destruct (cn_consts L1 A1 m2 md1 RMc) as (_ & _ & _ & OB2).
      pose proof (cn_bytes_skip m2 cOUT ob (Z.to_nat (cpos pre)) OB2 ltac:(lia)) as BL.
      rewrite SKP2, Z2Nat.id in BL by lia. apply (cn_bytes_first _ _ _ (length x)) in BL.
      rewrite cn_firstn_app_l in BL.
      pose proof (rw_cells_of_rel rsegs m2 m' _ _ MREL2 PA2) as AT2.
      rewrite <- CPQ in AT2.
      destruct (cn_c8_cb _ _ _ (rw_cells_of_rel rsegs m2 m' _ _ MREL2 PL2)) as (j2' & FC2).
      destruct (cn_c8_cb _ _ _ (rw_cells_of_rel rsegs m2 m' _ _ MREL2 PN2)) as (j1' & FB2).
      replace (cS0 - 80 + 16) with (cS0 - 64) in FC2 by lia. replace (cS0 - 80 + 8) with (cS0 - 72) in FB2 by lia.
      pose proof (rw_cells_transport rsegs _ m1 m2 _ _ FA1 MUs WMs ltac:(cbn [disjoint_from cells_size csize]; repeat split; lia))
        as FA2.
      apply (cn_gm_call pre q x rs L1 A1 m2 md1 H1 jk qs regs2 (cOUT + cpos pre) EPR RMc INI1
               (ro_agree_same rsegs m1 m2 RO1 ROS2)).
      * apply (cn_src_gen 8384 cS0 _ _ L1 A1 m1 md1 L1 A1 m2 md1 _ ltac:(lia) M1 RMs SRC1); [intros a Ha X; lia|].
        intros q0 _. apply KHI.
      * exact AT2.
      * split; [exact FA2|]. exists j1', j2'. split; [exact FB2 | exact FC2].
      * exact TX1.
      * exact ND1.
      * exact HN1.
      * exact HC1.
      * exact BL1.
      * exact BK1.
      * exact LQ1.
      * exact RS1.
      * exact SQ1.
      * exact NM1.
      * exact EN1.
      * apply RG2. intros r0 Hr H19 H20. rewrite GR2. unfold callee_saved in Hr.
        assert (Hc : r0 = 2 \/ r0 = 3 \/ r0 = 4 \/ r0 = 8 \/ r0 = 9 \/ r0 = 18 \/ r0 = 21 \/ r0 = 22 \/ r0 = 23 \/
                     r0 = 24 \/ r0 = 25 \/ r0 = 26 \/ r0 = 27) by lia.
        repeat (destruct Hc as [Hc|Hc]; [subst r0; reflexivity|]); subst r0; reflexivity.
      * rewrite GR2. reflexivity.
      * rewrite GR2. exact E9.
      * rewrite GR2. transitivity (Z_to_bv 64 (bv_unsigned out + bv_unsigned (Z_to_bv 64 (cpos pre)))); [reflexivity|].
        rewrite UP. reflexivity.
      * rewrite GR2. reflexivity.
      * lia.
      * exact BL.
      * exact NZ.
      * exact L6.
      * exists cOUT, CO. split; [exact (cn_rmid_keep _ _ _ _ _ _ _ _ _ _ _ _ _ _ HW RM1 HIN (fun X => HNI (cn_cfw_hs _ X)))|].
        split; [exact HFR|]. split; [lia|]. split; [lia|].
        exact (BK1 cOUT CO HIN ltac:(lia) (fun X => HNI (cn_cfw_hs _ X))).
  - eapply (kseg R1 (Z_to_bv 64 0x14f50) m1 md1); [vm_compute; reflexivity | exact RO1 | exact Hh1 | exact Hl1 | | |].
    + unfold Regs6ss.mkR_of.
      eapply cn_run1 with (gone := gone) (V := hl_v cE) (N := Z.of_nat (length ((q, x) :: rs))) (CAP := hl_cap cE)
        (q := q) (L0 := Z.of_nat (length x)).
      * exact E21.
      * exact (bytes_at_normalize rsegs m1 _ _ RO1 GN1).
      * exact GR.
      * exact G0.
      * rewrite E18, U18. apply rw_cells_normalize; [exact RO1 | exact LC1 |]. intros i Hi. apply hf_ro_glob. cbn in Hi. lia.
      * apply cn_ro2. exact (bytes_at_normalize rsegs m1 _ _ RO1 R0a).
      * lia.
      * exact (proj2 VA).
    + intros s0 ->. do 3 eexists. reflexivity.
    + intros R pc' m0' regs2 m2 HQ GR2 MREL2 ROS2.
      injection HQ as ER EP EM. subst R pc' m0'.
      destruct (cn_hiseg L1 A1 m1 md1 (normalize rsegs m1) m2 [] (fun _ => False) RM1 RO1 MREL2 ROS2
                  (munch_refl _ _) (wmono_refl _ _)) as (RMs & MUs & WMs).
      { intros y Hy O. exfalso. exact (O I). }
      { intros y []. }
      assert (RMc : rmid Bm API 8384 cS0 cEW cFW L A mem md L1 A1 m2 md1).
      { apply (cn_seq _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HW RM1 RMs); [intros a [] | intros p n _ _ []]. }
      assert (CPQ : cpos (pre ++ [(q, x)]) = cpos pre).
      { unfold cpos. rewrite (proj2 (Z.eqb_neq gone 0) G0). reflexivity. }
      apply (cn_gm_call pre q x rs L1 A1 m2 md1 H1 jk qs regs2 q EPR RMc INI1 (ro_agree_same rsegs m1 m2 RO1 ROS2)).
      * apply (cn_src_gen 8384 cS0 _ _ L1 A1 m1 md1 L1 A1 m2 md1 _ ltac:(lia) M1 RMs SRC1); [intros a Ha []|].
        intros q0 _. apply KF0.
      * rewrite CPQ. exact (rw_cells_transport rsegs [] m1 m2 _ _ AT1 MUs WMs I).
      * split; [exact (rw_cells_transport rsegs [] m1 m2 _ _ FA1 MUs WMs I)|]. exists j1, j2.
        split; [exact (rw_cells_transport rsegs [] m1 m2 _ _ FB1 MUs WMs I) |
                exact (rw_cells_transport rsegs [] m1 m2 _ _ FC1 MUs WMs I)].
      * exact TX1.
      * exact ND1.
      * exact HN1.
      * exact HC1.
      * exact BL1.
      * exact BK1.
      * exact LQ1.
      * exact RS1.
      * exact SQ1.
      * exact NM1.
      * exact EN1.
      * apply RG2. intros r0 Hr H19 H20. rewrite GR2. unfold callee_saved in Hr.
        assert (Hc : r0 = 2 \/ r0 = 3 \/ r0 = 4 \/ r0 = 8 \/ r0 = 9 \/ r0 = 18 \/ r0 = 21 \/ r0 = 22 \/ r0 = 23 \/
                     r0 = 24 \/ r0 = 25 \/ r0 = 26 \/ r0 = 27) by lia.
        repeat (destruct Hc as [Hc|Hc]; [subst r0; reflexivity|]); subst r0; reflexivity.
      * rewrite GR2. reflexivity.
      * rewrite GR2. exact E9.
      * rewrite GR2. reflexivity.
      * rewrite GR2. reflexivity.
      * lia.
      * exact (bytes_at_transport rsegs [] m1 m2 _ _ R0x MUs I).
      * exact NZ.
      * exact L6.
      * exists q, (Z.of_nat (length x) + 1). split; [exact RB|]. split; [exact RF|]. split; [lia|]. split; [lia|].
        apply (src_out (set_exp_held h (HL (hl_v cE) (hl_cap cE) ((q, x) :: rs) jk) H1) NDB1 q).
        apply in_app_iff. right. apply in_app_iff. right. cbn [set_exp_held hs_expected].
        unfold list_blocks. apply in_app_iff. right. left. reflexivity.
Qed.

Lemma cn_blk_ha : forall L1 A1 m1 md1 q0 k, MR L1 A1 m1 md1 -> In (q0, k) (blocks L1 A1) -> 0 < k ->
  q0 + k <= cHA \/ cHA + 96 <= q0.
Proof.
  intros L1 A1 m1 md1 q0 k HM Hin Hk. pose proof cn_ha as (_ & HAp & _).
  destruct (Z_le_gt_dec (q0 + k) cHA) as [D|D]; [left; exact D|].
  destruct (Z_le_gt_dec (cHA + 96) q0) as [D'|D']; [right; exact D'|]. exfalso.
  apply (hf_blk_img Bm API AX L1 A1 m1 md1 q0 k (Z.max q0 cHA - q0) HM Hin ltac:(lia)).
  replace (q0 + (Z.max q0 cHA - q0)) with (Z.max q0 cHA) by lia. exact (proj1 (HAp (Z.max q0 cHA) ltac:(lia))).
Qed.

Lemma cn_in_rm : forall (b1 b2 : list (Z * Z)) y z, In y (b1 ++ z :: b2) -> y <> z -> In y (b1 ++ b2).
Proof.
  intros b1 b2 y z H N. apply in_app_iff in H as [H|[H|H]]; apply in_or_app;
    [left; exact H | exfalso; exact (N (eq_sym H)) | right; exact H].
Qed.

Lemma cn_nd_rm : forall L1 A1 m1 md1 b1 b2 q0 n q1 m0, MR L1 A1 m1 md1 -> blocks L1 A1 = b1 ++ (q0, n) :: b2 ->
  In (q1, m0) (b1 ++ b2) -> q1 <> q0.
Proof.
  intros L1 A1 m1 md1 b1 b2 q0 n q1 m0 HM E H ->.
  pose proof (NODUP L1 A1 m1 md1 HM) as ND. apply hf_nodup in ND. rewrite E, map_app in ND. cbn [map fst] in ND.
  apply NoDup_remove_2 in ND. apply ND. rewrite <- map_app. exact (in_map fst _ (q0, m0) H).
Qed.

Lemma cn_step_drop : forall r rs L1 A1 R1 m1 md1 H1 jk qs,
  J1 r rs L1 A1 m1 md1 H1 jk qs -> cRG R1 ->
  SR rsegs (mkCfg (YK11.mkst R1 (Z_to_bv 64 0x14fd0) m1 (seg_rom rsegs)) md1)
    (fun c => exists L2 A2 R2 m2 md2 jk2 qs2, CI rs L2 A2 m2 md2 H1 jk2 qs2 /\ cRG R2 /\
       ((rs <> [] /\ c = mkCfg (YK11.mkst R2 (Z_to_bv 64 0x14f50) m2 (seg_rom rsegs)) md2) \/
        (rs = [] /\ c = mkCfg (YK11.mkst R2 (Z_to_bv 64 0x14fe4) m2 (seg_rom rsegs)) md2))).
Proof.
  intros [q x] rs L1 A1 R1 m1 md1 H1 jk qs (pre & EPR & CJ1 & LQ1 & RS1 & ST1 & NM1 & EN1) RG1.
  destruct CJ1 as (RM1 & INI1 & RO1 & SRC1 & AT1 & FRM1 & TX1 & ND1 & HN1 & HC1 & BL1 & BK1).
  cbn [snd] in LQ1, RS1, ST1.
  pose proof cn_pre_facts as (HM & HW & HB & HRA & HAL & HC & H63 & HWS & HTP & HERR).
  pose proof cn_ha as (HAr & HAp & HAt).
  pose proof (aa_laws API) as LAWS.
  pose proof (@YM05.alloc_ceiling_value rc) as ACV. pose proof (@YM05.alloc_ceiling_lt rc) as ACL.
  assert (EK : CHECK_NO_LOSS_K = 8384) by reflexivity. rewrite EK in RM1.
  pose proof RM1 as (M1 & W1 & B1 & _ & _ & _ & _ & _ & _ & _ & _ & _ & SC1).
  destruct (mr_model _ _ LAWS _ _ _ _ M1) as (Hh1 & Hl1 & _).
  pose proof SRC1 as S1. apply src_at_iff in S1. destruct S1 as (SB1 & LE1 & LH1 & NDB1).
  cbn [set_exp_held hs_expected hs_held] in LE1, LH1.
  pose proof LE1 as (LC1 & LB1 & LAR1 & LND1 & LNV1 & LFA1).
  rewrite SEG in LC1. unfold hl_n in LC1, LB1. cbn [hl_v hl_cap hl_recs hl_junk] in LC1, LB1, LAR1, LND1, LNV1, LFA1.
  destruct LAR1 as [(C0 & _)|(CP0 & VIN & VFR & VJ & VC)]; [cbn [length] in LB1; lia|].
  pose proof (cn_blk_range L1 A1 m1 md1 _ _ M1 VIN) as VB.
  pose proof (cn_blk_ha L1 A1 m1 md1 _ _ M1 VIN ltac:(lia)) as VHA.
  pose proof LND1 as LNDq. apply hf_nodup in LNDq. cbn [map fst] in LNDq. apply NoDup_cons_iff in LNDq as (QNR & _).
  assert (QNR' : forall r', In r' rs -> fst r' <> q).
  { intros r' Hr E0. apply QNR. rewrite <- E0. exact (in_map fst _ _ Hr). }
  assert (NEL : forall q0, In q0 (list_blocks (hs_pending h) ++ [hs_partial h]) \/ In q0 (list_blocks H1) ->
            ~ In q0 (list_blocks (HL (hl_v cE) (hl_cap cE) ((q, x) :: rs) jk))).
  { pose proof NDB1 as ND0. apply hf_nodup in ND0. unfold hs_blocks in ND0. cbn [set_exp_held hs_pending hs_partial
      hs_expected hs_held] in ND0.
    intros q0 [Hq|Hq] Hl.
    - apply (hf_nodup_disj (list_blocks (hs_pending h) ++ [hs_partial h])
               (list_blocks (HL (hl_v cE) (hl_cap cE) ((q, x) :: rs) jk) ++ list_blocks H1) q0);
        [rewrite <- app_assoc; exact ND0 | exact Hq | apply in_or_app; left; exact Hl].
    - apply (hf_nodup_disj (list_blocks (hs_pending h) ++ [hs_partial h] ++
               list_blocks (HL (hl_v cE) (hl_cap cE) ((q, x) :: rs) jk)) (list_blocks H1) q0);
        [rewrite <- !app_assoc; exact ND0 | apply in_or_app; right; apply in_or_app; right; exact Hl | exact Hq]. }
  assert (QEL : In q (list_blocks (HL (hl_v cE) (hl_cap cE) ((q, x) :: rs) jk))).
  { unfold list_blocks. apply in_or_app. right. left. reflexivity. }
  assert (VEL : In (hl_v cE) (list_blocks (HL (hl_v cE) (hl_cap cE) ((q, x) :: rs) jk))).
  { unfold list_blocks. cbn [hl_cap hl_v]. rewrite (proj2 (Z.eqb_neq (hl_cap cE) 0) ltac:(lia)). left. reflexivity. }
  assert (KEP : forall (Eq Fq : Z -> Prop) q0,
            (forall a, Eq a -> (cHA <= a < cHA + 96) \/ (0 < hl_cap cE /\ hl_v cE <= a < hl_v cE + 16 * hl_cap cE)) ->
            (forall q1, Fq q1 -> q1 = q) ->
            In q0 (list_blocks (hs_pending h) ++ [hs_partial h]) \/ In q0 (list_blocks H1) ->
            kept_block Eq Fq L1 A1 q0).
  { intros Eq Fq q0 HE HF Hq. pose proof (NEL q0 Hq) as N0.
    apply (hf_kept Bm API AX L1 A1 m1 md1 Eq Fq cHA (cHA + 96) (hl_cap cE) (hl_v cE) q0 M1).
    - intros a Ha. exact (proj1 (HAp a Ha)).
    - exact HE.
    - intros _. exact VIN.
    - intros X. apply N0. rewrite (HF q0 X). exact QEL.
    - intros _ E0. apply N0. rewrite E0. exact VEL. }
  assert (E2 : reg_get R1 2 = Z_to_bv 64 (cS0 - 80))
    by exact (RG1 2 ltac:(unfold callee_saved; lia) ltac:(lia) ltac:(lia)).
  assert (E18 : reg_get R1 18 = Z_to_bv 64 (cHA + 64))
    by exact (RG1 18 ltac:(unfold callee_saved; lia) ltac:(lia) ltac:(lia)).
  assert (U2 : bv_unsigned (Z_to_bv 64 (cS0 - 80)) = cS0 - 80) by (apply unsigned_lit; lia).
  assert (U9 : bv_unsigned (Z_to_bv 64 cHA) = cHA) by (apply unsigned_lit; lia).
  assert (U18 : bv_unsigned (Z_to_bv 64 (cHA + 64)) = cHA + 64) by (apply unsigned_lit; lia).
  assert (I0u : bv_unsigned (Z_to_bv 64 0) = 0) by reflexivity.
  destruct FRM1 as (FA1 & j1 & j2 & FB1 & FC1).
  eapply (kseg R1 (Z_to_bv 64 0x14fd0) m1 md1); [vm_compute; reflexivity | exact RO1 | exact Hh1 | exact Hl1 | | |].
  { unfold Regs6ss.mkR_of. apply cn_dcall. }
  { intros s0 ->. do 3 eexists. reflexivity. }
  intros R pc' m0' regs2 m2 HQ GR2 MREL2 ROS2.
  injection HQ as ER EP EM. subst R pc' m0'.
  destruct (cn_hiseg L1 A1 m1 md1 (normalize rsegs m1) m2 [] (fun _ => False) RM1 RO1 MREL2 ROS2
              (munch_refl _ _) (wmono_refl _ _)) as (RMs & MUs & WMs).
  { intros y Hy O. exfalso. exact (O I). }
  { intros y []. }
  assert (RMc : rmid Bm API 8384 cS0 cEW cFW L A mem md L1 A1 m2 md1).
  { apply (cn_seq _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HW RM1 RMs); [intros a [] | intros p n _ _ []]. }
  pose proof RMc as (M2 & W2 & B2 & _ & _ & _ & _ & _ & _ & _ & _ & _ & SC2).
  assert (RO2 : ro_agree rsegs m2) by exact (ro_agree_same rsegs m1 m2 RO1 ROS2).
  assert (G2r : getr regs2 2 = Z_to_bv 64 (cS0 - 80)) by (rewrite GR2; exact E2).
  assert (SP2 : spZ regs2 = cS0 - 80).
  { unfold spZ. transitivity (bv_unsigned (Z_to_bv 64 (cS0 - 80))); [f_equal; exact G2r | exact U2]. }
  assert (RG2 : forall r0, callee_saved r0 -> r0 <> 19 -> r0 <> 20 -> getr regs2 (Z_to_bv 5 r0) = cval r0).
  { intros r0 Hr H19 H20. rewrite GR2. transitivity (getr R1 (Z_to_bv 5 r0)); [|exact (RG1 r0 Hr H19 H20)].
    unfold callee_saved in Hr.
    assert (Hc : r0 = 2 \/ r0 = 3 \/ r0 = 4 \/ r0 = 8 \/ r0 = 9 \/ r0 = 18 \/ r0 = 21 \/ r0 = 22 \/ r0 = 23 \/
                 r0 = 24 \/ r0 = 25 \/ r0 = 26 \/ r0 = 27) by lia.
    repeat (destruct Hc as [Hc|Hc]; [subst r0; reflexivity|]); subst r0; reflexivity. }
  assert (G21 : getr regs2 1 = Z_to_bv 64 0x14fdc) by (rewrite GR2; reflexivity).
  assert (G10 : getr regs2 10 = Z_to_bv 64 (cHA + 64)) by (rewrite GR2; exact E18).
  assert (G11 : getr regs2 11 = Z_to_bv 64 0) by (rewrite GR2; reflexivity).
  assert (P1 : PropExec.getr regs2 1 = Z_to_bv 64 0x14fdc)
    by (change (PropExec.getr regs2 1) with (getr regs2 1); exact G21).
  assert (P10 : PropExec.getr regs2 10 = Z_to_bv 64 (cHA + 64))
    by (change (PropExec.getr regs2 10) with (getr regs2 10); exact G10).
  assert (P11 : PropExec.getr regs2 11 = Z_to_bv 64 0)
    by (change (PropExec.getr regs2 11) with (getr regs2 11); exact G11).
  assert (SRC2 : src_at Bm L1 A1 m2 cHA (set_exp_held h (HL (hl_v cE) (hl_cap cE) ((q, x) :: rs) jk) H1)).
  { apply (cn_src_gen 8384 cS0 _ _ L1 A1 m1 md1 L1 A1 m2 md1 _ ltac:(lia) M1 RMs SRC1); [intros a Ha []|].
    intros q0 _. split; [intros [] | intros k i _ _ []]. }
  pose proof SRC2 as S2. apply src_at_iff in S2. destruct S2 as (_ & LE2 & _ & _).
  cbn [set_exp_held hs_expected] in LE2.
  assert (EKD : LIST_DROP_K = 8240) by reflexivity.
  pose proof LDC as DC. unfold list_drop_contract in DC. rewrite SEG in DC. rewrite EKD in DC. unfold LIST_DROP in DC.
  eapply SR_bind.
  { apply (DC L1 A1 regs2 m2 md1 (runF F qs bnd (cT pre ++ gesture_model_tr (cSp pre) (bzs x)))
             (HL (hl_v cE) (hl_cap cE) ((q, x) :: rs) jk) true).
    - reflexivity.
    - eapply cpk_of_rmid; [exact RMc | exact INI1 | | | | | | | |].
      + rewrite ?G21, ?P1. apply ret_ok_even. rewrite unsigned_lit by lia. reflexivity.
      + transitivity (cval 4); [exact (RG2 4 ltac:(unfold callee_saved; lia) ltac:(lia) ltac:(lia)) | exact HTP].
      + rewrite SP2. Z.div_mod_to_equations. lia.
      + rewrite SP2. lia.
      + rewrite SP2. lia.
      + lia.
      + rewrite SP2. lia.
      + rewrite SP2. lia.
    - exact INI1.
    - exact RO2.
    - rewrite ?G10, ?P10, U18. intros a Ha. split; [apply HAp; lia | apply hf_ro_glob; lia].
    - rewrite ?G10, ?P10, U18. pose proof cn_ha8. Z.div_mod_to_equations. lia.
    - rewrite ?G10, ?P10, U18. exact LE2.
    - rewrite ?G11, ?P11, I0u. unfold hl_n. cbn [hl_recs length]. lia.
    - exact RS1. }
  intros c3 (L3 & A3 & regs3 & m3 & md3 & l3 & -> & RP & INI3 & (qd & _ & RS3 & _ & _) & RO3 & LE3 & VS3 & CS3 & RECS3 &
    JK3 & (bb1 & bb2 & BLa & BLb)).
  rewrite ?G10, ?P10, U18 in RP, LE3. rewrite ?G11, ?P11, I0u in RP, RS3, RECS3, BLa.
  cbn [Z.to_nat nth fst snd hl_recs hl_v hl_cap] in RP, RS3, BLa. cbn [Z.to_nat firstn skipn app hl_recs] in RECS3.
  destruct l3 as [v3 c3' rs3 jk3]. cbn [hl_v hl_cap hl_recs hl_junk] in VS3, CS3, RECS3, JK3.
  subst v3 c3' rs3 jk3.
  destruct (rp_split Bm API _ _ _ _ _ _ _ _ _ _ _ _ _ RP) as (RMd0 & PRd). rewrite SP2 in RMd0.
  pose proof (rmid_EF Bm API _ _ _ (fun a => cHA + 72 <= a < cHA + 76 \/ hl_v cE <= a < hl_v cE + 16 * hl_cap cE)
                _ (fun q0 => q0 = q) _ _ _ _ _ _ _ _ RMd0) as RMd1.
  assert (RMd : rmid Bm API 8240 (cS0 - 80) (fun a => cHA + 72 <= a < cHA + 76 \/ hl_v cE <= a < hl_v cE + 16 * hl_cap cE)
                  (fun q0 => q0 = q) L1 A1 m2 md1 L3 A3 m3 md3).
  { apply RMd1.
    - intros a [X|X]; [left; lia | right; unfold hl_n in X; cbn [hl_v hl_recs] in X; cbn [length] in LB1, X; lia].
    - intros q0 X. exact X. }
  clear RMd1.
  assert (RMdw : rmid Bm API 8384 cS0 (fun a => cHA + 72 <= a < cHA + 76 \/ hl_v cE <= a < hl_v cE + 16 * hl_cap cE)
                   (fun q0 => q0 = q) L1 A1 m2 md1 L3 A3 m3 md3).
  { apply (rmid_widen Bm API 8240 (cS0 - 80) 8384 cS0 _ _ _ _ _ _ _ _ _ _ M2); [lia | lia | lia | lia | | | exact RMd].
    - intros a Ha. exact (SC2 a (or_introl Ha)).
    - intros a Ha [X|X]; lia. }
  assert (QF : cFW q).
  { unfold cFW. apply in_or_app. left. rewrite EPR, map_app. apply in_or_app. right. left. reflexivity. }
  assert (RMc2 : rmid Bm API 8384 cS0 cEW cFW L A mem md L3 A3 m3 md3).
  { apply (cn_seq _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HW RMc RMdw).
    - intros a [X|X]; left; unfold cEW; [left; lia | right; right; left; split; lia].
    - intros p0 n0 Hp0 Hn0 X. rewrite X. exact QF. }
  pose proof (rmid_seq Bm API _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ W1 RMs RMdw) as RMl.
  pose proof RMc2 as (M3 & W3 & B3 & _ & _ & _ & _ & _ & _ & _ & _ & _ & SC3).
  destruct (mr_model _ _ LAWS _ _ _ _ M3) as (Hh3 & Hl3 & _).
  assert (RG3 : forall r0, callee_saved r0 -> r0 <> 19 -> r0 <> 20 -> getr regs3 (Z_to_bv 5 r0) = cval r0).
  { intros r0 Hr H19 H20. rewrite (PRd r0 Hr). exact (RG2 r0 Hr H19 H20). }
  assert (E3_9 : reg_get regs3 9 = Z_to_bv 64 cHA) by exact (RG3 9 ltac:(unfold callee_saved; lia) ltac:(lia) ltac:(lia)).
  pose proof LE3 as (LC3 & LB3 & _).
  rewrite SEG in LC3. unfold hl_n in LC3, LB3. cbn [hl_v hl_cap hl_recs] in LC3, LB3.
  rewrite ?G21, ?P1.
  eapply (kseg regs3 (Z_to_bv 64 0x14fdc) m3 md3); [vm_compute; reflexivity | exact RO3 | exact Hh3 | exact Hl3 | | |].
  { unfold Regs6ss.mkR_of. eapply cn_back with (V := hl_v cE) (N := Z.of_nat (length rs)) (CAP := hl_cap cE).
    - rewrite E3_9, U9.
      apply rw_cells_normalize; [exact RO3 | exact LC3 |]. intros i Hi. apply hf_ro_glob. cbn in Hi. lia.
    - cbn [length] in LB1. lia. }
  { intros s0 [(_ & ->)|(_ & ->)]; do 3 eexists; reflexivity. }
  intros R pc' m0' regs4 m4 HQ GR4 MREL4 ROS4.
  assert (EMm : m0' = normalize rsegs m3) by (destruct HQ as [(_ & EQ)|(_ & EQ)]; injection EQ; intros; congruence).
  subst m0'.
  destruct (cn_hiseg L3 A3 m3 md3 (normalize rsegs m3) m4 [] (fun _ => False) RMc2 RO3 MREL4 ROS4
              (munch_refl _ _) (wmono_refl _ _)) as (RMs4 & MUs4 & WMs4).
  { intros y Hy O. exfalso. exact (O I). }
  { intros y []. }
  pose proof (rmid_seq Bm API _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ W1 RMl RMs4) as RMl2.
  assert (RMall : rmid Bm API 8384 cS0 cEW cFW L A mem md L3 A3 m4 md3).
  { apply (cn_seq _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HW RMc2 RMs4); [intros a [] | intros p n _ _ []]. }
  assert (SB4 : src_base Bm L3 A3 m4 cHA (set_exp_held h (HL (hl_v cE) (hl_cap cE) rs
                  (text_rec (last ((q, x) :: rs) (0, [])) ++ jk)) H1)).
  { apply (src_base_rmid Bm API AX BW 8384 cS0 _ _ L1 A1 m1 md1 L3 A3 m4 md3 cHA _ SEG ltac:(lia) M1 RMl2 SB1).
    - intros i Hi. split; [apply HAp; lia|]. intros [[[]|[X|X]]|[]]; lia.
    - intros q0 Hq. apply KEP.
      + intros a [[[]|[X|X]]|[]]; [left; lia | right; split; lia].
      + intros q1 [[[]|X]|[]]. exact X.
      + left. cbn [set_exp_held hs_pending hs_partial] in Hq.
        destruct Hq as [Hq|Hq]; [apply in_or_app; left; exact Hq | subst q0; apply in_or_app; right; left; reflexivity]. }
  assert (LH4 : list_at Bm L3 A3 m4 (cHA + 80) H1 true).
  { apply (list_at_rmid Bm API AX BW 8384 cS0 _ _ L1 A1 m1 md1 L3 A3 m4 md3 (cHA + 80) H1 true SEG ltac:(lia) M1 RMl2 LH1).
    - intros i Hi. split; [apply HAp; lia|]. intros [[[]|[X|X]]|[]]; lia.
    - intros q0 Hq. apply KEP.
      + intros a [[[]|[X|X]]|[]]; [left; lia | right; split; lia].
      + intros q1 [[[]|X]|[]]. exact X.
      + right. exact Hq. }
  assert (LE4 : list_at Bm L3 A3 m4 (cHA + 64) (HL (hl_v cE) (hl_cap cE) rs
                  (text_rec (last ((q, x) :: rs) (0, [])) ++ jk)) true).
  { apply (list_at_rmid Bm API AX BW 8384 cS0 _ _ L3 A3 m3 md3 L3 A3 m4 md3 (cHA + 64) _ true SEG ltac:(lia) M3 RMs4 LE3).
    - intros i Hi. split; [apply HAp; lia | intros []].
    - intros q0 _. split; [intros [] | intros k i _ _ []]. }
  assert (EQd : forall B, runF F qd B (list_drop_tr (sh_of (known_at L1 A1) (HL (hl_v cE) (hl_cap cE) ((q, x) :: rs) jk)) 0) =
                rt_free F B (Z.of_nat (length x) + 1) (sptr_of L A q)).
  { intros B. pose proof (EN1 (q, x) (or_introl eq_refl)) as EQq. cbn [fst] in EQq.
    unfold list_drop_tr, sh_of, runF, run_tr. cbn [sh_recs hl_recs hl_v hl_cap map nth rec_drop_tr run_from].
    unfold rec_len, shr, known_at. cbn [fst snd resolve]. unfold bzs. rewrite length_map, EQq. reflexivity. }
  assert (RS3' : rt_ok F A3 (rt_free F (runF F qs bnd (cT pre ++ gesture_model_tr (cSp pre) (bzs x)))
                   (Z.of_nat (length x) + 1) (sptr_of L A q))) by (rewrite <- (EQd _); exact RS3).
  assert (NB1 : NoDup (map fst (blocks L1 A1))) by exact (NODUP L1 A1 m1 md1 M1).
  assert (KH : forall a n, In (a, n) (blocks L1 A1) -> 0 < n -> In a (list_blocks H1) -> sptr_of L3 A3 a = sptr_of L1 A1 a).
  { intros a n Ha Hn Hl. apply (cn_sptr_keep _ _ _ _ _ _ _ _ _ _ _ _ _ n NB1 RMd Ha Hn).
    intros X. cbv beta in X. subst a. exact (NEL q (or_intror Hl) QEL). }
  assert (ETq : cT (pre ++ [(q, x)]) = (cT pre ++ gesture_model_tr (cSp pre) (bzs x)) ++ rec_drop_tr (shr cnm (q, x))).
  { rewrite cn_cT_snoc, app_assoc. reflexivity. }
  assert (EQf : forall X, runF F (qs ++ X) bnd (cT (pre ++ [(q, x)])) =
                rt_free F (runF F qs bnd (cT pre ++ gesture_model_tr (cSp pre) (bzs x))) (Z.of_nat (length x) + 1)
                  (sptr_of L A q)).
  { intros X. rewrite ETq. unfold runF at 1. unfold run_tr. rewrite run_from_app.
    pose proof (ST1 X) as S1. unfold runF, run_tr in S1. rewrite S1. cbn [rec_drop_tr run_from].
    unfold rec_len, shr, cnm, known_at. cbn [fst snd resolve]. unfold bzs. rewrite length_map. reflexivity. }
  pose proof (EQf []) as EQ0. rewrite app_nil_r in EQ0.
  assert (CIX : CI rs L3 A3 m4 md3 H1 (text_rec (last ((q, x) :: rs) (0, [])) ++ jk) qs).
  { exists (pre ++ [(q, x)]). split; [rewrite EPR, <- app_assoc; reflexivity|].
    split.
    - split; [exact RMall|]. split; [exact INI3|]. split; [exact (ro_agree_same rsegs m3 m4 RO3 ROS4)|].
      split.
      { apply src_at_iff. split; [exact SB4|]. split; [exact LE4|]. split; [exact LH4|].
        assert (LE1b : list_blocks (HL (hl_v cE) (hl_cap cE) ((q, x) :: rs) jk) = [hl_v cE] ++ q :: map fst rs).
        { unfold list_blocks. cbn [hl_cap hl_v hl_recs map fst]. rewrite (proj2 (Z.eqb_neq (hl_cap cE) 0) ltac:(lia)).
          reflexivity. }
        assert (LE4b : list_blocks (HL (hl_v cE) (hl_cap cE) rs (text_rec (last ((q, x) :: rs) (0, [])) ++ jk)) =
                       [hl_v cE] ++ map fst rs).
        { unfold list_blocks. cbn [hl_cap hl_v hl_recs]. rewrite (proj2 (Z.eqb_neq (hl_cap cE) 0) ltac:(lia)).
          reflexivity. }
        apply hf_nodup. pose proof NDB1 as ND0. apply hf_nodup in ND0. unfold hs_blocks in ND0 |- *.
        cbn [set_exp_held hs_pending hs_partial hs_expected hs_held] in ND0 |- *.
        rewrite LE1b in ND0. rewrite LE4b.
        set (Pl := list_blocks (hs_pending h)) in *. set (Hl := list_blocks H1) in *.
        replace (Pl ++ [hs_partial h] ++ ([hl_v cE] ++ q :: map fst rs) ++ Hl) with
          ((Pl ++ [hs_partial h] ++ [hl_v cE]) ++ q :: (map fst rs ++ Hl)) in ND0 by (rewrite <- !app_assoc; reflexivity).
        replace (Pl ++ [hs_partial h] ++ ([hl_v cE] ++ map fst rs) ++ Hl) with
          ((Pl ++ [hs_partial h] ++ [hl_v cE]) ++ (map fst rs ++ Hl)) by (rewrite <- !app_assoc; reflexivity).
        exact (NoDup_remove_1 _ _ _ ND0). }
      split; [exact (cn_rwhi 8384 cS0 _ _ _ _ _ _ _ _ _ _ _ _ ltac:(lia) M1 RMl2 AT1 ltac:(lia) ltac:(cbn; lia)
                       ltac:(intros i Hi [[[]|[X|X]]|[]]; cbn [cells_size csize] in Hi; lia))|].
      split.
      { assert (TR : forall a cs, rw_cells rsegs m1 a cs -> cS0 - 80 <= a -> a + Z.of_nat (cells_size cs) <= cS0 ->
                  rw_cells rsegs m4 a cs).
        { intros a cs H Ha Hb.
          pose proof (rw_cells_transport rsegs [] m1 m2 _ _ H MUs WMs I) as H2.
          pose proof (cn_rwhi 8240 (cS0 - 80) _ _ _ _ _ _ _ _ _ _ a cs ltac:(lia) M2 RMd H2 Ha ltac:(lia)
                        ltac:(intros i Hi [X|X]; lia)) as H3.
          exact (rw_cells_transport rsegs [] m3 m4 _ _ H3 MUs4 WMs4 I). }
        split; [exact (TR _ _ FA1 ltac:(lia) ltac:(cbn; lia))|]. exists j1, j2.
        split; [exact (TR _ _ FB1 ltac:(lia) ltac:(cbn; lia)) | exact (TR _ _ FC1 ltac:(lia) ltac:(cbn; lia))]. }
      split; [exact TX1|]. split; [exact ND1|]. split; [exact HN1|]. split; [exact HC1|].
      split; [|exact BK1].
      intros q0 m0 Hq. rewrite BLb in Hq. pose proof (cn_nd_rm L1 A1 m2 md1 _ _ _ _ _ _ M2 BLa Hq) as QN.
      assert (Hq1 : In (q0, m0) (blocks L1 A1)).
      { rewrite BLa. apply in_app_iff in Hq as [Hq|Hq]; apply in_or_app; [left; exact Hq | right; right; exact Hq]. }
      destruct (BL1 q0 m0 Hq1) as [X|[X|X]]; [left; exact X | right; left; exact X|].
      right; right. destruct X as [X|X]; [exfalso; apply QN; rewrite <- X; reflexivity | exact X].
    - split; [rewrite ETq, nret_app, nret_rec_drop, Nat.add_0_r; exact LQ1|].
      split; [rewrite EQ0; exact RS3'|].
      split; [intros X; rewrite (EQf X), EQ0; reflexivity|].
      split.
      { intros X Y. apply (cn_rel_names _ _ _ (known_at L1 A1) (known_at L3 A3) H1); [| |exact (NM1 X Y)].
        - intros Hc. unfold known_at. f_equal. pose proof (hf_list_v Bm L1 A1 m1 _ _ _ LH1) as VH.
          pose proof LH1 as (_ & LBH & _). unfold hl_n in LBH. destruct (VH ltac:(lia)) as (B1v & B2v).
          exact (KH _ _ B1v ltac:(lia) B2v).
        - intros r Hr. unfold known_at. f_equal. pose proof LH1 as (_ & _ & _ & _ & _ & LFH).
          destruct (proj1 (Forall_forall _ _) LFH r Hr) as (RBh & _). apply (KH _ _ RBh ltac:(lia)).
          unfold list_blocks. apply in_or_app. right. exact (in_map fst _ _ Hr). }
      intros r' Hr'. rewrite <- (EN1 r' (or_intror Hr')).
      destruct (proj1 (Forall_forall _ _) LFA1 r' (or_intror Hr')) as (RB' & _).
      apply (cn_sptr_keep _ _ _ _ _ _ _ _ _ _ _ _ _ _ NB1 RMd RB' ltac:(lia)).
      intros X. cbv beta in X. exact (QNR' r' Hr' X). }
  assert (RG4 : forall R', (forall r0, callee_saved r0 -> r0 <> 19 -> r0 <> 20 ->
                  getr R' (Z_to_bv 5 r0) = getr regs3 (Z_to_bv 5 r0)) -> cRG R').
  { intros R' GQ r0 Hr H19 H20. rewrite (GQ r0 Hr H19 H20). exact (RG3 r0 Hr H19 H20). }
  apply SR_ret.
  exists L3, A3, regs4, m4, md3, (text_rec (last ((q, x) :: rs) (0, [])) ++ jk), qs.
  split; [exact CIX|].
  destruct HQ as [(HN2 & EQ)|(HN2 & EQ)]; injection EQ as ER EP; subst R pc'; split.
  - apply RG4. intros r0 Hr H19 H20. rewrite GR4. unfold callee_saved in Hr.
    assert (Hc : r0 = 2 \/ r0 = 3 \/ r0 = 4 \/ r0 = 8 \/ r0 = 9 \/ r0 = 18 \/ r0 = 21 \/ r0 = 22 \/ r0 = 23 \/
                 r0 = 24 \/ r0 = 25 \/ r0 = 26 \/ r0 = 27) by lia.
    repeat (destruct Hc as [Hc|Hc]; [subst r0; reflexivity|]); subst r0; reflexivity.
  - left. split; [destruct rs; [exfalso; cbn [length] in HN2; lia | discriminate] | reflexivity].
  - apply RG4. intros r0 Hr H19 H20. rewrite GR4. unfold callee_saved in Hr.
    assert (Hc : r0 = 2 \/ r0 = 3 \/ r0 = 4 \/ r0 = 8 \/ r0 = 9 \/ r0 = 18 \/ r0 = 21 \/ r0 = 22 \/ r0 = 23 \/
                 r0 = 24 \/ r0 = 25 \/ r0 = 26 \/ r0 = 27) by lia.
    repeat (destruct Hc as [Hc|Hc]; [subst r0; reflexivity|]); subst r0; reflexivity.
  - right. split; [destruct rs; [reflexivity | exfalso; cbn [length] in HN2; lia] | reflexivity].
Qed.

Lemma cn_loop : forall rs L1 A1 R1 m1 md1 H1 jk qs, rs <> [] ->
  CI rs L1 A1 m1 md1 H1 jk qs -> cRG R1 ->
  SR rsegs (mkCfg (YK11.mkst R1 (Z_to_bv 64 0x14f50) m1 (seg_rom rsegs)) md1)
    (fun c => exists L2 A2 R2 m2 md2 H2 jk2 qs2, CI [] L2 A2 m2 md2 H2 jk2 qs2 /\ cRG R2 /\
       c = mkCfg (YK11.mkst R2 (Z_to_bv 64 0x14fe4) m2 (seg_rom rsegs)) md2).
Proof.
  induction rs as [|r rs IH]; intros L1 A1 R1 m1 md1 H1 jk qs NE CI1 RG1; [contradiction|].
  eapply SR_bind; [exact (cn_step_gm r rs L1 A1 R1 m1 md1 H1 jk qs CI1 RG1)|].
  intros c (L2 & A2 & R2 & m2 & md2 & H2 & qs2 & J & RG2 & ->).
  eapply SR_bind; [exact (cn_step_drop r rs L2 A2 R2 m2 md2 H2 jk qs2 J RG2)|].
  intros c (L3 & A3 & R3 & m3 & md3 & jk3 & qs3 & CI3 & RG3 & [(NE3 & ->)|(E3 & ->)]).
  - exact (IH L3 A3 R3 m3 md3 H2 jk3 qs3 NE3 CI3 RG3).
  - subst rs. apply SR_ret. exists L3, A3, R3, m3, md3, H2, jk3, qs3. split; [exact CI3|]. split; [exact RG3 | reflexivity].
Qed.

Definition cPOST (c' : config) : Prop :=
  exists L' A' regs' mem' md' (E' H' : hlist),
    c' = mkCfg (YK11.mkst regs' (getr regs 1) mem' (seg_rom rsegs)) md' /\
    relay_post Bm API CHECK_NO_LOSS_K cEW cFW L A regs mem md L' A' regs' mem' md' /\
    st_init_done A' = true /\
    (exists qs, length qs = nretF (cT (hl_recs cE)) /\ rt_ok F A' (runF F qs bnd (cT (hl_recs cE))) /\
       sh_real L' qs (cSp (hl_recs cE)) H' /\ sh_live A' qs (cSp (hl_recs cE))) /\
    ro_agree rsegs mem' /\
    src_at Bm L' A' mem' cHA (set_exp_held h E' H') /\
    hl_recs E' = [] /\ hl_v E' = hl_v cE /\ hl_cap E' = hl_cap cE /\
    NoDup (texts H') /\
    hl_cap H' <= Z.max 8 (Z.max (hl_cap cH) (2 * (hl_n cH + Z.of_nat cBE))) /\
    texts H' = upds (texts cH) (texts cE) /\
    rw_cells rsegs mem' cAT [C8 (Z_to_bv 64 (if gone =? 0 then A0 + cLB else A0))] /\
    bytes_at rsegs mem' G_GONE [Z_to_bv 8 gone] /\
    bytes_at rsegs mem' G_NOUT (le8 nout) /\
    bytes_at rsegs mem' G_OUT (le8 out) /\
    bytes_at rsegs mem' cOUT ob /\
    (forall q m, In (q, m) (blocks L A) -> ~ cFW q -> In (q, m) (blocks L' A')) /\
    (forall q m, In (q, m) (blocks L' A') -> (In (q, m) (blocks L A) /\ (0 < m -> ~ cFW q)) \/ In q (list_blocks H')) /\
    (forall q m, In (q, m) (blocks L A) -> 0 < m -> ~ cFW q -> ~ In q (list_blocks H')).

Lemma cn_fin : forall L1 A1 R1 m1 md1 H1 jk qs, CI [] L1 A1 m1 md1 H1 jk qs ->
  getr R1 2 = Z_to_bv 64 (cS0 - 80) ->
  (forall r, r = 3 \/ r = 4 \/ 22 <= r <= 27 -> getr R1 (Z_to_bv 5 r) = getr regs (Z_to_bv 5 r)) ->
  SR rsegs (mkCfg (YK11.mkst R1 (Z_to_bv 64 0x14fe4) m1 (seg_rom rsegs)) md1) cPOST.
Proof.
  intros L1 A1 R1 m1 md1 H1 jk qs (pre & EPR & CJ1 & LQ1 & RS1 & ST1 & NM1 & EN1) G2 GK.
  rewrite app_nil_r in EPR.
  destruct CJ1 as (RM1 & INI1 & RO1 & SRC1 & AT1 & FRM1 & TX1 & ND1 & HN1 & HC1 & BL1 & BK1).
  pose proof cn_pre_facts as (HM & HW & HB & HRA & HAL & HC & H63 & HWS & HTP & HERR).
  pose proof (aa_laws API) as LAWS.
  pose proof (@YM05.alloc_ceiling_value rc) as ACV. pose proof (@YM05.alloc_ceiling_lt rc) as ACL.
  assert (EK : CHECK_NO_LOSS_K = 8384) by reflexivity. rewrite EK in RM1.
  pose proof RM1 as (M1 & W1 & B1 & _ & _ & _ & _ & _ & _ & _ & _ & _ & SC1).
  destruct (mr_model _ _ LAWS _ _ _ _ M1) as (Hh1 & Hl1 & _).
  destruct FRM1 as (FA1 & _).
  assert (E2 : reg_get R1 2 = Z_to_bv 64 (cS0 - 80)) by exact G2.
  assert (U2 : bv_unsigned (Z_to_bv 64 (cS0 - 80)) = cS0 - 80) by (apply unsigned_lit; lia).
  eapply (kseg R1 (Z_to_bv 64 0x14fe4) m1 md1); [vm_compute; reflexivity | exact RO1 | exact Hh1 | exact Hl1 | | |].
  { unfold Regs6ss.mkR_of. rewrite E2. apply cn_epi. rewrite U2. replace (cS0 - 80 + 24) with (cS0 - 56) by lia.
    apply rw_cells_normalize; [exact RO1 | exact FA1 |]. intros i Hi. apply ro_addr_hi. cbn in Hi. lia. }
  { intros s0 ->. do 3 eexists. reflexivity. }
  intros R pc' m0' regs2 m2 HQ GR2 MREL2 ROS2.
  injection HQ as ER EP EM. subst R pc' m0'.
  destruct (cn_hiseg L1 A1 m1 md1 (normalize rsegs m1) m2 [] (fun _ => False) RM1 RO1 MREL2 ROS2
              (munch_refl _ _) (wmono_refl _ _)) as (RMs & MUs & WMs).
  { intros y Hy O. exfalso. exact (O I). }
  { intros y []. }
  assert (RMc : rmid Bm API 8384 cS0 cEW cFW L A mem md L1 A1 m2 md1).
  { apply (cn_seq _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HW RM1 RMs); [intros a [] | intros p n _ _ []]. }
  destruct (cn_consts L1 A1 m2 md1 RMc) as (GN2 & NO2 & OU2 & OB2).
  apply SR_ret. exists L1, A1, regs2, m2, md1, (HL (hl_v cE) (hl_cap cE) [] jk), H1.
  split; [do 2 f_equal; exact (ret_pc_of_ok _ HRA)|].
  split.
  { apply rp_join.
    - change (spZ regs) with cS0. rewrite EK. exact RMc.
    - intros r0 Hr. rewrite GR2. unfold callee_saved in Hr.
      assert (Hc : r0 = 2 \/ r0 = 3 \/ r0 = 4 \/ r0 = 8 \/ r0 = 9 \/ r0 = 18 \/ r0 = 19 \/ r0 = 20 \/ r0 = 21 \/
                   r0 = 22 \/ r0 = 23 \/ r0 = 24 \/ r0 = 25 \/ r0 = 26 \/ r0 = 27) by lia.
      destruct Hc as [->|Hc].
      + change (Z_to_bv 64 (bv_unsigned (Z_to_bv 64 (cS0 - 80)) + 80) = getr regs (Z_to_bv 5 2)).
        rewrite U2. replace (cS0 - 80 + 80) with cS0 by lia. unfold cS0, spZ. apply Z_to_bv_bv_unsigned.
      + repeat (destruct Hc as [Hc|Hc];
          [subst r0; first [reflexivity | (etransitivity; [|apply GK; lia]; reflexivity)]|]);
          subst r0; first [reflexivity | (etransitivity; [|apply GK; lia]; reflexivity)]. }
  split; [exact INI1|].
  split.
  { exists qs. rewrite EPR. split; [exact LQ1|]. split; [exact RS1|].
    pose proof SRC1 as S1. apply src_at_iff in S1. destruct S1 as (_ & _ & LH1 & _).
    cbn [set_exp_held hs_held] in LH1.
    pose proof LH1 as (_ & LBH & _). pose proof LH1 as (_ & _ & _ & _ & _ & LFH).
    pose proof (hf_list_v Bm L1 A1 m1 _ _ _ LH1) as VH.
    apply (cn_rel_real L1 A1 qs qs _ H1 (NODUP L1 A1 m1 md1 M1)).
    - intros Hc. unfold hl_n in LBH. destruct (VH ltac:(lia)) as (B & _). exists (16 * hl_cap H1). exact B.
    - intros r Hr. destruct (proj1 (Forall_forall _ _) LFH r Hr) as (RB & _). eexists. exact RB.
    - pose proof (NM1 [] qs) as N0. rewrite app_nil_r in N0. exact N0. }
  split; [exact (ro_agree_same rsegs m1 m2 RO1 ROS2)|].
  split.
  { apply (cn_src_gen 8384 cS0 _ _ L1 A1 m1 md1 L1 A1 m2 md1 _ ltac:(lia) M1 RMs SRC1); [intros a Ha []|].
    intros q0 _. split; [intros [] | intros k i _ _ []]. }
  split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
  split; [exact ND1|].
  split; [rewrite <- EPR in HC1; exact HC1|].
  split; [rewrite TX1, <- EPR; reflexivity|].
  split; [rewrite <- EPR in AT1; exact (rw_cells_transport rsegs [] m1 m2 _ _ AT1 MUs WMs I)|].
  split; [exact GN2|]. split; [exact NO2|]. split; [exact OU2|]. split; [exact OB2|].
  split; [intros q0 m0 Hq NF; exact (cn_rmid_keep _ _ _ _ _ _ _ _ _ _ _ _ q0 m0 HW RMc Hq NF)|].
  split; [|exact BK1].
  intros q0 m0 Hq. destruct (BL1 q0 m0 Hq) as [X|[X|[]]]; [left; exact X | right; exact X].
Qed.

Lemma cn_main : SR rsegs (mkCfg (YK11.mkst regs (Z_to_bv 64 CHECK_NO_LOSS) mem (seg_rom rsegs)) md) cPOST.
Proof.
  pose proof cn_pre_facts as (HM & HW & HB & HRA & HAL & HC & H63 & HWS & HTP & HERR).
  pose proof cn_ha as (HAr & HAp & HAt).
  pose proof (aa_laws API) as LAWS.
  pose proof (@YM05.alloc_ceiling_value rc) as ACV. pose proof (@YM05.alloc_ceiling_lt rc) as ACL.
  destruct (mr_model _ _ LAWS _ _ _ _ HM) as (Hh & Hl & _).
  pose proof SRC as S0. apply src_at_iff in S0. destruct S0 as (SB & LE & LH & NDB).
  pose proof LE as (LC & LB & _). rewrite SEG in LC.
  assert (USP : bv_unsigned (reg_get regs 2) = cS0) by reflexivity.
  assert (A10 : reg_get regs 10 = Z_to_bv 64 cHA) by exact R10.
  assert (UHA : bv_unsigned (Z_to_bv 64 cHA) = cHA) by (apply unsigned_lit; lia).
  assert (ST : stk rsegs mem (cS0 - 8384) cS0).
  { split; [lia|]. split; [lia|]. intros a Ha. assert (W : writable_at rsegs mem a) by (apply HWS; lia).
    split; [exact W|]. destruct (writable_hi_present mem a ltac:(lia) W) as [bb E0]. exists bb.
    unfold mrd, wa. rewrite E0. reflexivity. }
  unfold CHECK_NO_LOSS.
  eapply (kseg regs (Z_to_bv 64 0x14f0c) mem md); [vm_compute; reflexivity | exact RO | exact Hh | exact Hl | | |].
  { unfold Regs6ss.mkR_of. eapply cn_pro with (lo := cS0 - 8384) (V := hl_v cE) (N := hl_n cE) (CAP := hl_cap cE).
    - rewrite USP. exact (stk_normalize mem _ _ ST ltac:(lia)).
    - rewrite USP. lia.
    - apply mem_inv_normalize.
    - rewrite A10, UHA. apply rw_cells_normalize; [exact RO | exact LC |]. intros i Hi. apply hf_ro_glob. cbn in Hi. lia.
    - rewrite A10, UHA, USP. lia.
    - unfold hl_n in *. lia.
    - rewrite A10, UHA. lia.
    - rewrite A10, UHA. exact cn_ha8. }
  { intros s0 (j0 & j1 & j2 & m' & _ & _ & _ & _ & _ & _ & _ & _ & _ & [(_ & ->)|(_ & ->)]); do 3 eexists; reflexivity. }
  intros R pc' m0' regs1 m1 HQ GR1 MREL1 ROS1.
  destruct HQ as (j0 & j1 & j2 & m' & MU & WM & MI & STK & F0 & F1 & F2 & FS & HD & CASE).
  assert (EMm : m0' = m') by (destruct CASE as [(_ & EQ)|(_ & EQ)]; injection EQ; intros; congruence).
  subst m0'.
  rewrite ?USP in MU. rewrite ?USP in F1. rewrite ?USP in F2. rewrite ?USP in FS.
  destruct (rmid_norm Bm API 8384 cS0 (fun _ => False) (fun _ => False) L A mem md m' m1 [(cS0 - 80, cS0)] SEG RO
              MREL1 ROS1 MU WM HM HW HB ltac:(lia)) as (RMp & MUp & WMp).
  { unfold sk. rewrite SEG. intros a [X|X]; [apply HWS; lia | apply HERR; exact X]. }
  { intros y Hy O. destruct (hg_not_out _ _ O) as (lo & hi & [E0|[]] & Hlh). injection E0 as <- <-. left. lia. }
  { intros a Ho. pose proof (mr_owned_low _ _ LAWS _ _ _ _ a HM Ho). apply hg_out. intros lo hi [E0|[]].
    injection E0 as <- <-. left. lia. }
  { intros p n i Hp Hi O. exfalso. destruct (mr_blocks _ _ LAWS _ _ _ _ p n i HM Hp Hi) as (_ & B1 & B2 & _).
    destruct (hg_not_out _ _ O) as (lo & hi & [E0|[]] & Hlh). injection E0 as <- <-. lia. }
  pose proof (rmid_EF Bm API _ _ _ cEW _ cFW _ _ _ _ _ _ _ _ RMp (fun a X => False_ind _ X) (fun q X => False_ind _ X))
    as RM0.
  assert (CI0 : CI (hl_recs cE) L A m1 md cH (hl_junk cE) []).
  { exists []. split; [reflexivity|].
    split; [|split; [reflexivity | split; [exact RES | split; [intros X; reflexivity |
      split; [intros X Y; exact (cn_rel_refl ([] ++ X) Y L A cH) | intros r _; reflexivity]]]]].
    split; [exact RM0|]. split; [exact INIT|]. split; [exact (ro_agree_same rsegs mem m1 RO ROS1)|].
    split.
    { replace (set_exp_held h (HL (hl_v cE) (hl_cap cE) (hl_recs cE) (hl_junk cE)) cH) with h
        by (symmetry; exact (cn_seh_gen h)).
      apply (cn_src_gen 8384 cS0 _ _ L A mem md L A m1 md _ ltac:(lia) HM RMp SRC); [intros a Ha []|].
      intros q0 _. split; [intros [] | intros k i _ _ []]. }
    split.
    { assert (CP0 : cpos [] = A0) by (unfold cpos; destruct (gone =? 0); cbn; lia). rewrite CP0.
      exact (cn_rwhi 8384 cS0 _ _ _ _ _ _ _ _ _ _ _ _ ltac:(lia) HM RMp CAT ltac:(lia) ltac:(cbn; lia)
               ltac:(intros i Hi [])). }
    split.
    { split; [exact (rw_cells_of_rel rsegs m1 m' _ _ MREL1 FS)|]. exists j1, j2.
      split; [exact (rw_cells_of_rel rsegs m1 m' _ _ MREL1 F1) | exact (rw_cells_of_rel rsegs m1 m' _ _ MREL1 F2)]. }
    split; [reflexivity|]. split; [exact NDT|].
    split; [cbn; lia|]. split; [cbn; lia|].
    split.
    { intros q0 m0 Hq. destruct (cn_cfw_dec q0) as [X|X].
      - right. unfold cFW in X. apply in_app_iff in X as [X|X]; [right; exact X | left; exact X].
      - left. split; [exact Hq | intros _; exact X]. }
    intros q0 m0 Hq Hm NF Hl0. apply NF. unfold cFW. apply in_or_app. right. exact Hl0. }
  destruct CASE as [(HN0 & EQ)|(HN0 & EQ)]; injection EQ as ER EP; subst R pc'.
  - assert (ER0 : hl_recs cE = []) by (apply length_zero_iff_nil; unfold hl_n in HN0; lia).
    rewrite ER0 in CI0.
    apply (cn_fin L A regs1 m1 md cH (hl_junk cE) [] CI0).
    + rewrite GR1. reflexivity.
    + intros r0 Hr. rewrite GR1.
      assert (Hc : r0 = 3 \/ r0 = 4 \/ r0 = 22 \/ r0 = 23 \/ r0 = 24 \/ r0 = 25 \/ r0 = 26 \/ r0 = 27) by lia.
      repeat (destruct Hc as [Hc|Hc]; [subst r0; reflexivity|]); subst r0; reflexivity.
  - eapply SR_bind.
    { apply (cn_loop (hl_recs cE) L A regs1 m1 md cH (hl_junk cE) []); [| exact CI0 |].
      - intros E0. unfold hl_n in HN0. rewrite E0 in HN0. cbn in HN0. lia.
      - intros r0 Hr H19 H20. rewrite GR1. unfold callee_saved in Hr.
        assert (Hc : r0 = 2 \/ r0 = 3 \/ r0 = 4 \/ r0 = 8 \/ r0 = 9 \/ r0 = 18 \/ r0 = 21 \/ r0 = 22 \/ r0 = 23 \/
                     r0 = 24 \/ r0 = 25 \/ r0 = 26 \/ r0 = 27) by lia.
        repeat (destruct Hc as [Hc|Hc];
          [subst r0; first [reflexivity | exact R10 |
                            (transitivity (Z_to_bv 64 (bv_unsigned (reg_get regs 10) + 64));
                             [reflexivity | rewrite A10, UHA; reflexivity])]|]); subst r0; reflexivity. }
    intros c (L2 & A2 & R2 & m2 & md2 & H2 & jk2 & qs2 & CI2 & RG2 & ->).
    apply (cn_fin L2 A2 R2 m2 md2 H2 jk2 qs2 CI2).
    + exact (RG2 2 ltac:(unfold callee_saved; lia) ltac:(lia) ltac:(lia)).
    + intros r0 Hr. transitivity (cval r0); [apply RG2; unfold callee_saved in *; lia|].
      assert (Hc : r0 = 3 \/ r0 = 4 \/ r0 = 22 \/ r0 = 23 \/ r0 = 24 \/ r0 = 25 \/ r0 = 26 \/ r0 = 27) by lia.
      repeat (destruct Hc as [Hc|Hc]; [subst r0; reflexivity|]); subst r0; reflexivity.
Qed.

End Run.

Theorem check_no_loss_holds : check_no_loss_contract Bm API F.
Proof.
  unfold check_no_loss_contract. intros L A regs mem md bnd h j gone A0 nout out ob. cbv zeta.
  intros SEG PRE INIT RO PLR Hj4 R10 SRC NDT HNE HNH ATM ATL ATH CAT GR CGN CNO COU COB LOB OBD A0R SKP RES ROOM.
  rewrite SEG in *.
  eapply SR_mono.
  - eapply cn_main with (L := L) (A := A) (regs := regs) (mem := mem) (md := md) (bnd := bnd) (h := h) (j := j)
      (gone := gone) (A0 := A0) (nout := nout) (out := out) (ob := ob); assumption.
  - intros c' X. exact X.
Qed.

End CNB.
