(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import
  PropExec CatExec CatSim SeqExec StepTac StoreOk MemSplit Hoare RefMemcpyLib RefReadLib SumWalkTac SumMemsetLib MmapSim LibIface LibEff.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont Require Import CRep.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Lemma u64_of_Z : forall z, 0 <= z < 2 ^ 64 -> bv_unsigned (Z_to_bv 64 z) = z.
Proof. intros z Hz. apply u_Z2bv; lia. Qed.

Definition stores_in (W : Z -> Prop) (M M' : mem) : Prop :=
  (forall a : word, ~ W (bv_unsigned a) -> M' a = M a) /\
  (forall a : word, M a <> None -> M' a <> None).

Lemma stores_in_refl : forall W M, stores_in W M M.
Proof. intros W M. split; [intros a _; reflexivity | intros a H; exact H]. Qed.

Lemma stores_in_trans : forall W M1 M2 M3,
  stores_in W M1 M2 -> stores_in W M2 M3 -> stores_in W M1 M3.
Proof.
  intros W M1 M2 M3 [A1 D1] [A2 D2]. split.
  - intros a Ha. rewrite (A2 a Ha). apply A1, Ha.
  - intros a Ha. apply D2, D1, Ha.
Qed.

Lemma stores_in_weaken : forall (W W' : Z -> Prop) M M',
  stores_in W M M' -> (forall a, W a -> W' a) -> stores_in W' M M'.
Proof.
  intros W W' M M' [A D] HW. split; [|exact D].
  intros a Ha. apply A. intros Hw. apply Ha, HW, Hw.
Qed.

Lemma stores_in_wbytes : forall (W : Z -> Prop) M (a : Z) (bs : list byte),
  0 <= a -> a + Z.of_nat (length bs) < 2 ^ 64 ->
  (forall x, a <= x < a + Z.of_nat (length bs) -> W x) ->
  stores_in W M (wbytes M (Z_to_bv 64 a) bs).
Proof.
  intros W M a bs Ha Hnw HW. split.
  - intros x Hx. apply wbytes_outside; rewrite u64_of_Z by lia; [lia|].
    destruct (Z.lt_ge_cases (bv_unsigned x) a); [left; lia|].
    destruct (Z.lt_ge_cases (bv_unsigned x) (a + Z.of_nat (length bs))); [|right; lia].
    exfalso. apply Hx, HW. lia.
  - intros x Hx. apply wbytes_grows. exact Hx.
Qed.

Lemma stores_in_wbytes_more : forall (W : Z -> Prop) M M1 (a : Z) (bs : list byte),
  stores_in W M M1 ->
  0 <= a -> a + Z.of_nat (length bs) < 2 ^ 64 ->
  (forall x, a <= x < a + Z.of_nat (length bs) -> W x) ->
  stores_in W M (wbytes M1 (Z_to_bv 64 a) bs).
Proof.
  intros W M M1 a bs H Ha Hnw HW. eapply stores_in_trans; [exact H|]. apply stores_in_wbytes; assumption.
Qed.

Lemma stores_in_frame_eq : forall (W F : Z -> Prop) M M',
  stores_in W M M' -> (forall a, W a -> F a) -> frame_eq F M M'.
Proof. intros W F M M' [A D] HF a Ha. apply A. intros Hw. apply Ha, HF, Hw. Qed.

Lemma stores_in_agree : forall (W P : Z -> Prop) M M',
  stores_in W M M' -> (forall a, P a -> 0 <= a < 2 ^ 64 /\ ~ W a) -> agree_on P M M'.
Proof.
  intros W P M M' [A D] HP a Ha. destruct (HP a Ha) as [Hr Hn]. apply A. rewrite u64_of_Z by lia. exact Hn.
Qed.

Lemma stores_in_mdef : forall W M M' a n, stores_in W M M' -> mdef M a n -> mdef M' a n.
Proof. intros W M M' a n [_ D] H i Hi. apply D, H, Hi. Qed.

Lemma stores_in_store_ok : forall segs W M M' (a : word) n,
  stores_in W M M' -> store_ok segs M a n = true -> store_ok segs M' a n = true.
Proof. intros segs W M M' a n [_ D] H. eapply store_ok_mono; [|exact H]. intros x Hx. apply D, Hx. Qed.

Section WithIface.
Context {AC : AllocCeiling}.
Variable SEGS : list Segment.
Variable L : Layout.
Variable MI : MallocIface SEGS L.
Variable ST : StaticsIface SEGS L.

Lemma stores_in_ainv : forall W (A : AS MI) M M' model,
  ainv MI A M model -> stores_in W M M' -> (forall a, W a -> ~ owned MI A a) -> ainv MI A M' model.
Proof using AC SEGS L MI.
  intros W A M M' model AI [Ag D] HW. eapply (ai_frame MI); [exact AI | | exact D | reflexivity | reflexivity].
  intros a Ho. apply Ag. intros Hw. exact (HW _ Hw Ho).
Qed.

Lemma stores_in_sx : forall W (s : SX ST) M M',
  sx_inv ST s M -> stores_in W M M' ->
  (forall a, W a -> ~ sx_region ST a /\ ~ in_ranges (ly_relro L) a) -> sx_inv ST s M'.
Proof using SEGS L ST.
  intros W s M M' SXI [Ag D] HW. apply (sx_frame ST s M M' SXI).
  intros a Ha. apply Ag. intros Hw. destruct (HW _ Hw) as [H1 H2]. destruct Ha as [Ha|Ha]; [exact (H1 Ha)|exact (H2 Ha)].
Qed.

Lemma roc_frame : forall (F : Z -> Prop) M M',
  img_ro_clear L M -> frame_eq F M M' ->
  (forall a, F a -> in_ranges (ly_rw L) a \/ ~ in_ranges (ly_img L) a) -> img_ro_clear L M'.
Proof using L.
  intros F M M' HR HF HD. eapply img_ro_clear_frame; [exact HR | exact HF |].
  intros a Hi Hnrw HFa. destruct (HD a HFa) as [H|H]; [exact (Hnrw H) | exact (H Hi)].
Qed.

Lemma roc_stores : forall (W : Z -> Prop) M M',
  img_ro_clear L M -> stores_in W M M' -> (forall a, W a -> ~ in_ranges (ly_img L) a) -> img_ro_clear L M'.
Proof using L.
  intros W M M' HR SI HW. eapply roc_frame; [exact HR | eapply stores_in_frame_eq; [exact SI | intros a Ha; exact Ha] |].
  intros a Ha. right. exact (HW a Ha).
Qed.

Lemma roc_owned : forall (A : AS MI) M model a,
  ainv MI A M model -> owned MI A a -> in_ranges (ly_rw L) a \/ ~ in_ranges (ly_img L) a.
Proof using AC SEGS L MI. intros A M model a AI Ho. exact (ai_owned_not_img_ro MI A M model a AI Ho). Qed.

Lemma live_mdef : forall (A : AS MI) M model p n,
  ainv MI A M model -> In (p, n) (live MI A) -> mdef M p n.
Proof using AC SEGS L MI.
  intros A M model p n AI Hin i Hi.
  destruct (ai_live_block MI A M model p n AI Hin) as (_ & _ & _ & _ & H). apply (H (p + i)). lia.
Qed.

Lemma live_unowned : forall (A : AS MI) M model p n a,
  ainv MI A M model -> In (p, n) (live MI A) -> p <= a < p + n -> ~ owned MI A a.
Proof using AC SEGS L MI.
  intros A M model p n a AI Hin Ha.
  destruct (ai_live_block MI A M model p n AI Hin) as (_ & _ & _ & _ & H). exact (proj1 (H a Ha)).
Qed.

Lemma live_offimg : forall (A : AS MI) M model p n a,
  ainv MI A M model -> In (p, n) (live MI A) -> p <= a < p + n -> ~ in_ranges (ly_img L) a.
Proof using AC SEGS L MI.
  intros A M model p n a AI Hin Ha.
  destruct (ai_live_block MI A M model p n AI Hin) as (_ & _ & _ & _ & H). exact (proj1 (proj2 (H a Ha))).
Qed.

Lemma live_range : forall (A : AS MI) M model p n,
  ainv MI A M model -> In (p, n) (live MI A) -> 0 <= n /\ p mod 16 = 0 /\ 0 < p /\ p + n <= alloc_ceiling.
Proof using AC SEGS L MI.
  intros A M model p n AI Hin.
  destruct (ai_live_block MI A M model p n AI Hin) as (H1 & H2 & H3 & H4 & _). repeat split; assumption.
Qed.
End WithIface.

Lemma mdef_store_ok : forall segs M a n (k : nat),
  mdef M a n -> 0 <= a -> a + n < 2 ^ 64 -> Z.of_nat k <= n ->
  store_ok segs M (Z_to_bv 64 a) k = true.
Proof.
  intros segs M a n k HD Ha Hn Hk. apply store_ok_of_all; [rewrite u64_of_Z by lia; lia|].
  intros x Hx. rewrite u64_of_Z in Hx by lia. unfold wview.
  specialize (HD (bv_unsigned x - a) ltac:(lia)).
  replace (a + (bv_unsigned x - a)) with (bv_unsigned x) in HD by lia. rewrite Z_to_bv_bv_unsigned in HD.
  destruct (M x); [discriminate | exfalso; apply HD; reflexivity].
Qed.

Lemma mdef_store_ok_off : forall segs M a n d (k : nat),
  mdef M a n -> 0 <= a -> a + n < 2 ^ 64 -> 0 <= d -> d + Z.of_nat k <= n ->
  store_ok segs M (Z_to_bv 64 (a + d)) k = true.
Proof.
  intros segs M a n d k HD Ha Hn Hd Hk. apply (mdef_store_ok segs M (a + d) (n - d)); try lia.
  intros i Hi. replace (a + d + i) with (a + (d + i)) by lia. apply HD. lia.
Qed.

Lemma mdef_sub : forall M a n a' n', mdef M a n -> a <= a' -> a' + n' <= a + n -> mdef M a' n'.
Proof. intros M a n a' n' H H1 H2 i Hi. replace (a' + i) with (a + (a' - a + i)) by lia. apply H. lia. Qed.

Lemma mdef_wbytes : forall M a n (wa : word) bs, mdef M a n -> mdef (wbytes M wa bs) a n.
Proof. intros M a n wa bs H i Hi. apply wbytes_grows. apply H, Hi. Qed.

Lemma stack_room_sub : forall segs M sp S lo (k : nat),
  stack_room segs M sp S -> 0 <= sp - S -> sp <= 2 ^ 63 -> sp - S <= lo -> lo + Z.of_nat k <= sp ->
  store_ok segs M (Z_to_bv 64 lo) k = true.
Proof.
  intros segs M sp S lo k HR H0 Hhi H1 H2. unfold stack_room in HR.
  eapply store_ok_sub; [ | exact HR | rewrite !u64_of_Z by lia; lia | rewrite !u64_of_Z by lia; lia].
  rewrite u64_of_Z by lia. lia.
Qed.

Lemma store_ok_mdef_offimg : forall segs M a n,
  store_ok segs M (Z_to_bv 64 a) (Z.to_nat n) = true -> 0 <= a -> 0 <= n -> a + n < 2 ^ 64 ->
  (forall x, a <= x < a + n -> find_segment segs x 1 = None) ->
  mdef M a n.
Proof.
  intros segs M a n HOK Ha Hn Hnw Hseg i Hi.
  pose proof (store_ok_all segs M (Z.to_nat n) (Z_to_bv 64 a) ltac:(rewrite u64_of_Z by lia; lia) HOK
                (Z_to_bv 64 (a + i)) ltac:(rewrite !u64_of_Z by lia; lia)) as H.
  unfold wview in H. rewrite u64_of_Z in H by lia. rewrite (Hseg (a + i)) in H by lia.
  destruct (M (Z_to_bv 64 (a + i))); [discriminate | exact H].
Qed.

Fixpoint vec_bytes (xs : list Z) : list byte :=
  match xs with
  | [] => []
  | x :: xs' => word_to_le_bytes 4 (Z_to_bv 64 x) ++ vec_bytes xs'
  end.

Lemma vec_bytes_length : forall xs, length (vec_bytes xs) = (4 * length xs)%nat.
Proof. induction xs as [|x xs IH]; [reflexivity|]. cbn [vec_bytes]. rewrite length_app, length_N_to_le_bytes, IH. cbn [length]. lia. Qed.

Section VB.
Context {AC : AllocCeiling}.
Variable SEGS : list Segment.

Lemma fld_vec_rdn : forall M b xs,
  0 <= b -> b + 4 * Zlen xs < 2 ^ 64 ->
  (forall i, 0 <= i < Zlen xs -> 0 <= Znth i xs < 2 ^ 32 /\ fld SEGS M (b + 4 * i) 4 (Znth i xs)) ->
  rdn SEGS M (Z_to_bv 64 b) (4 * length xs)%nat = Some (vec_bytes xs).
Proof using SEGS.
  intros M b xs Hb0 Hnw0 HF0.
  assert (HF1 : forall i, 0 <= i < Zlen xs -> fld SEGS M (b + 4 * i) 4 (Znth i xs)) by (intros i Hi; apply HF0, Hi).
  clear HF0. revert b Hb0 Hnw0 HF1. induction xs as [|x xs IH]; intros b Hb Hnw HF; [reflexivity|].
  cbn [vec_bytes]. replace (4 * length (x :: xs))%nat with (4 + 4 * length xs)%nat by (cbn [length]; lia).
  apply rdn_app.
  - specialize (HF 0). unfold Zlen in HF. cbn [length] in HF. rewrite Z.mul_0_r, Z.add_0_r in HF.
    apply HF. lia.
  - unfold Zlen in *. cbn [length] in *.
    replace (Z_to_bv 64 b + nat_to_word 4)%bv with (Z_to_bv 64 (b + 4)).
    2:{ apply bv_eq. unfold nat_to_word. rewrite bv_add_unsigned, !Z_to_bv_unsigned, !bv_wrap64_mod.
        change (Z.of_nat 4) with 4. rewrite <- Zplus_mod. reflexivity. }
    apply IH; [lia | lia |].
    intros i Hi. specialize (HF (i + 1) ltac:(lia)).
    replace (b + 4 * (i + 1)) with (b + 4 + 4 * i) in HF by lia.
    unfold Znth in *. replace (Z.to_nat (i + 1)) with (S (Z.to_nat i)) in HF by lia. cbn [nth] in HF. exact HF.
Qed.

Lemma rdn_vec_fld : forall M b xs,
  0 <= b -> b + 4 * Zlen xs < 2 ^ 64 ->
  rdn SEGS M (Z_to_bv 64 b) (4 * length xs)%nat = Some (vec_bytes xs) ->
  forall i, 0 <= i < Zlen xs -> fld SEGS M (b + 4 * i) 4 (Znth i xs).
Proof using SEGS.
  intros M b xs. revert b. induction xs as [|x xs IH]; intros b Hb Hnw HR i Hi.
  - unfold Zlen in Hi. cbn in Hi. lia.
  - unfold Zlen in *. cbn [length] in *.
    replace (4 * S (length xs))%nat with (4 + 4 * length xs)%nat in HR by lia.
    cbn [vec_bytes] in HR.
    pose proof (SeqExec.rdn_firstn SEGS M _ (Z_to_bv 64 b) _ 4 HR ltac:(lia)) as H1.
    pose proof (SeqExec.rdn_skipn SEGS M _ (Z_to_bv 64 b) _ 4 HR ltac:(lia)) as H2.
    rewrite firstn_app, length_N_to_le_bytes, Nat.sub_diag, firstn_O, app_nil_r, firstn_all2 in H1
      by (rewrite length_N_to_le_bytes; lia).
    rewrite skipn_app, length_N_to_le_bytes, Nat.sub_diag, skipn_O, skipn_all2 in H2
      by (rewrite length_N_to_le_bytes; lia).
    replace (4 + 4 * length xs - 4)%nat with (4 * length xs)%nat in H2 by lia.
    replace (Z_to_bv 64 b + nat_to_word 4)%bv with (Z_to_bv 64 (b + 4)) in H2.
    2:{ apply bv_eq. unfold nat_to_word. rewrite bv_add_unsigned, !Z_to_bv_unsigned, !bv_wrap64_mod.
        change (Z.of_nat 4) with 4. rewrite <- Zplus_mod. reflexivity. }
    destruct (Z.eq_dec i 0) as [->|Hne].
    + unfold Znth. cbn [Z.to_nat nth]. unfold fld. rewrite Z.mul_0_r, Z.add_0_r. exact H1.
    + specialize (IH (b + 4) ltac:(lia) ltac:(lia) H2 (i - 1) ltac:(lia)).
      replace (b + 4 + 4 * (i - 1)) with (b + 4 * i) in IH by lia.
      unfold Znth in *. replace (Z.to_nat i) with (S (Z.to_nat (i - 1))) by lia. cbn [nth]. exact IH.
Qed.
End VB.

Lemma mod16_sub : forall sp k, sp mod 16 = 0 -> (sp - 16 * k) mod 16 = 0.
Proof.
  intros sp k H. replace (sp - 16 * k) with (sp + (- k) * 16) by lia. rewrite Z.mod_add by lia. exact H.
Qed.

Fixpoint wslots (M : mem) (sp : Z) (vs : list word) : mem :=
  match vs with
  | [] => M
  | v :: vs' => wbytes (wslots M sp vs') (Z_to_bv 64 (sp - 8 * Zlen vs)) (word_to_le_bytes 8 v)
  end.

Lemma wslots_stores_in : forall M sp vs,
  0 <= sp - 8 * Zlen vs -> sp < 2 ^ 63 ->
  stores_in (zwin (sp - 8 * Zlen vs) sp) M (wslots M sp vs).
Proof.
  intros M sp vs. induction vs as [|v vs IH]; intros Hlo Hhi.
  - apply stores_in_refl.
  - cbn [wslots]. unfold Zlen in *. cbn [length] in *.
    eapply stores_in_wbytes_more.
    + eapply stores_in_weaken; [apply IH; lia|]. intros a Ha. unfold zwin in *. lia.
    + lia.
    + rewrite length_N_to_le_bytes. cbn. lia.
    + intros x Hx. rewrite length_N_to_le_bytes in Hx. unfold zwin. cbn in Hx. lia.
Qed.

Section WS.
Context {AC : AllocCeiling}.
Variable SEGS : list Segment.

Lemma wslots_out : forall M sp vs (a : Z) (n : nat),
  0 <= sp - 8 * Zlen vs -> sp < 2 ^ 63 -> 0 <= a -> a + Z.of_nat n < 2 ^ 64 ->
  (a + Z.of_nat n <= sp - 8 * Zlen vs \/ sp <= a) ->
  rdn SEGS (wslots M sp vs) (Z_to_bv 64 a) n = rdn SEGS M (Z_to_bv 64 a) n.
Proof using SEGS.
  intros M sp vs a n. induction vs as [|v vs IH]; intros Hlo Hhi Ha Han Hd; [reflexivity|].
  cbn [wslots]. unfold Zlen in *. cbn [length] in *.
  rewrite rdn_wbytes_out_Z.
  - apply IH; lia.
  - rewrite length_N_to_le_bytes. cbn [Z.of_nat Pos.of_succ_nat Pos.succ]. lia.
Qed.

Lemma wslots_read : forall M sp vs k,
  0 <= sp - 8 * Zlen vs -> sp < 2 ^ 63 -> 1 <= k <= Zlen vs ->
  rdn SEGS (wslots M sp vs) (Z_to_bv 64 (sp - 8 * k)) 8
  = Some (word_to_le_bytes 8 (nth (Z.to_nat (Zlen vs - k)) vs (Z_to_bv 64 0))).
Proof using SEGS.
  intros M sp vs k. induction vs as [|v vs IH]; intros Hlo Hhi Hk.
  - unfold Zlen in Hk. cbn in Hk. lia.
  - cbn [wslots]. unfold Zlen in *. cbn [length] in *.
    destruct (Z.eq_dec k (Z.of_nat (S (length vs)))) as [->|Hne].
    + rewrite Z.sub_diag. cbn [Z.to_nat nth]. apply rdn_wbytes_hit8. rewrite u64_of_Z by lia. lia.
    + rewrite rdn_wbytes_out_Z.
      * rewrite IH by lia.
        replace (Z.to_nat (Z.of_nat (S (length vs)) - k)) with (S (Z.to_nat (Z.of_nat (length vs) - k))) by lia.
        reflexivity.
      * rewrite length_N_to_le_bytes. cbn [Z.of_nat Pos.of_succ_nat Pos.succ]. lia.
Qed.
End WS.

Lemma c_ltu_Z : forall a b, 0 <= a < 2 ^ 64 -> 0 <= b < 2 ^ 64 ->
  c_ltu (Z_to_bv 64 a) (Z_to_bv 64 b) = (a <? b).
Proof. intros a b Ha Hb. unfold c_ltu, bv_ltu. rewrite !u64_of_Z by lia. reflexivity. Qed.

Lemma c_eq_Z' : forall a b, 0 <= a < 2 ^ 64 -> 0 <= b < 2 ^ 64 ->
  c_eq (Z_to_bv 64 a) (Z_to_bv 64 b) = (a =? b).
Proof. intros a b Ha Hb. unfold c_eq, bv_eqb. rewrite !u64_of_Z by lia. reflexivity. Qed.

Lemma lez_w4 : forall x, 0 <= x < 2 ^ 32 ->
  bytes_le_to_Z (word_to_le_bytes 4 (Z_to_bv 64 x)) = x.
Proof.
  intros x Hx. rewrite bytes_le_to_Z_4 by (rewrite u64_of_Z by lia; lia). apply u64_of_Z. lia.
Qed.

Lemma sw_of_lw : forall x, 0 <= x < 2 ^ 32 ->
  word_to_le_bytes 4 (v_lw (Z_to_bv 64 x)) = word_to_le_bytes 4 (Z_to_bv 64 x).
Proof.
  intros x Hx.
  pose proof (sw_bytes_LWv (word_to_le_bytes 4 (Z_to_bv 64 x)) (length_N_to_le_bytes _ _)) as H.
  unfold LWv in H. rewrite lez_w4 in H by lia. exact H.
Qed.

Lemma lwu_val : forall x, 0 <= x < 2 ^ 32 ->
  bytes_le_to_Z (word_to_le_bytes 4 (Z_to_bv 64 x)) = bv_unsigned (Z_to_bv 64 x).
Proof. intros x Hx. rewrite lez_w4, u64_of_Z by lia. reflexivity. Qed.

Section Placed.
Context {AC : AllocCeiling}.
Variable SEGS : list Segment.
Variable L : Layout.
Variable MI : MallocIface SEGS L.
Variable ST : StaticsIface SEGS L.

Hypothesis img_low : forall a, in_ranges (ly_img L) a -> a < alloc_ceiling.
Hypothesis rw_img : forall a, in_ranges (ly_rw L) a -> in_ranges (ly_img L) a.
Hypothesis relro_img : forall a, in_ranges (ly_relro L) a -> in_ranges (ly_img L) a.
Hypothesis errno_img : forall a, errno_win L a -> in_ranges (ly_img L) a.

Lemma stack_sep : forall (A : AS MI) M model a,
  ainv MI A M model -> alloc_ceiling <= a -> ~ owned MI A a /\ ~ in_ranges (ly_img L) a.
Proof using AC SEGS L MI img_low rw_img.
  intros A M model a AI Ha. split.
  - intros Ho. destruct (ai_owned_not_img_ro MI A M model a AI Ho) as [Hrw|Hni].
    + pose proof (img_low a (rw_img a Hrw)). lia.
    + pose proof (ai_owned_below_ceiling MI A M model a AI Ho Hni). lia.
  - intros Hi. pose proof (img_low a Hi). lia.
Qed.

Lemma placed_sep : forall (A : AS MI) M model v n a,
  ainv MI A M model -> placed MI A v n -> v <= a < v + n ->
  ~ owned MI A a /\ ~ in_ranges (ly_img L) a.
Proof using AC SEGS L MI img_low rw_img.
  intros A M model v n a AI [Hst|(q & k & Hin & Hq & Hqn)] Ha.
  - apply (stack_sep A M model a AI). lia.
  - split; [eapply (live_unowned SEGS L MI); [exact AI|exact Hin|lia] | eapply (live_offimg SEGS L MI); [exact AI|exact Hin|lia]].
Qed.

Lemma offimg_sep : forall a, ~ in_ranges (ly_img L) a ->
  ~ sx_region ST a /\ ~ in_ranges (ly_relro L) a /\ ~ errno_win L a.
Proof using SEGS L ST rw_img relro_img errno_img.
  intros a Hni. repeat split; intros H; apply Hni.
  - apply rw_img. exact (sx_region_rw ST a H).
  - apply relro_img, H.
  - apply errno_img, H.
Qed.

Lemma placed_new_block_disjoint : forall (A A' : AS MI) M M' model model' v n p m,
  ainv MI A M model -> ainv MI A' M' model' -> placed MI A v n ->
  live_add p m (live MI A) (live MI A') -> 0 <= m ->
  v + n <= p \/ p + m <= v \/ n <= 0.
Proof using AC SEGS L MI.
  intros A A' M M' model model' v n p m AI AI' PL LADD Hm.
  pose proof (live_add_new p m _ _ LADD) as HinP.
  destruct (live_range SEGS L MI A' M' model' p m AI' HinP) as (_ & _ & Hp & Hpc).
  destruct PL as [Hst|(q & k & Hin & Hq & Hqn)].
  - right; left. lia.
  - pose proof (live_add_keeps p m _ _ (q, k) LADD Hin) as Hin'.
    destruct (Z.eq_dec p q) as [->|Hne].
    + exfalso. destruct LADD as [_ Hnin]. apply Hnin. apply in_map_iff. exists (q, k). split; [reflexivity|exact Hin].
    + destruct (Z.lt_ge_cases 0 n); [|right; right; lia].
      destruct (ai_live_disjoint MI A' M' model' p m q k AI' HinP Hin' Hne); [right; left|left]; lia.
Qed.
End Placed.

Lemma bv_signed_small64 : forall a, 0 <= a < 2 ^ 63 -> bv_signed (Z_to_bv 64 a) = a.
Proof.
  intros a Ha. rewrite Z_to_bv_signed. apply bv_swrap_small. change (bv_half_modulus 64) with (2 ^ 63). lia.
Qed.

Lemma v_sub_Z : forall a b, 0 <= b -> b <= a < 2 ^ 64 -> v_sub (Z_to_bv 64 a) (Z_to_bv 64 b) = Z_to_bv 64 (a - b).
Proof. intros a b Hb Ha. unfold v_sub. rewrite !u64_of_Z by lia. reflexivity. Qed.

Lemma v_add_Z : forall a b, 0 <= a -> 0 <= b -> a + b < 2 ^ 64 -> v_add (Z_to_bv 64 a) (Z_to_bv 64 b) = Z_to_bv 64 (a + b).
Proof. intros a b Ha Hb Hab. unfold v_add. rewrite !u64_of_Z by lia. reflexivity. Qed.

Lemma v_addi_Z : forall a k, 0 <= a < 2 ^ 64 -> v_addi (Z_to_bv 64 a) k = Z_to_bv 64 (a + k).
Proof. intros a k Ha. unfold v_addi. rewrite u64_of_Z by lia. reflexivity. Qed.

Lemma v_slli_Z : forall a k, 0 <= a < 2 ^ 64 -> 0 <= k -> v_slli (Z_to_bv 64 a) k = Z_to_bv 64 (a * 2 ^ k).
Proof. intros a k Ha Hk. unfold v_slli. rewrite u64_of_Z, Z.shiftl_mul_pow2 by lia. reflexivity. Qed.

Lemma v_srli_Z : forall a k, 0 <= a < 2 ^ 64 -> 0 <= k -> v_srli (Z_to_bv 64 a) k = Z_to_bv 64 (a / 2 ^ k).
Proof. intros a k Ha Hk. unfold v_srli. rewrite u64_of_Z, Z.shiftr_div_pow2 by lia. reflexivity. Qed.

Lemma v_srai_Z : forall a k, 0 <= a < 2 ^ 63 -> 0 <= k -> v_srai (Z_to_bv 64 a) k = Z_to_bv 64 (a / 2 ^ k).
Proof. intros a k Ha Hk. unfold v_srai. rewrite bv_signed_small64, Z.shiftr_div_pow2 by lia. reflexivity. Qed.

Section Room.
Context {AC : AllocCeiling}.
Variable SEGS : list Segment.
Variable L : Layout.
Variable MI : MallocIface SEGS L.

Lemma roomL_room_for : forall (A : AS MI) M model n,
  ainv MI A M model -> 0 <= n <= NMAX MI -> roomL MI A (live MI A) n -> room_for MI A n.
Proof using AC SEGS L MI.
  intros A M model n AI Hn [HS HBG].
  destruct (Z.lt_ge_cases n (BIG MI)) as [Hs|Hb].
  - destruct (HS Hs) as [H1 H2]. eapply (room_small MI); [exact AI | lia | exact H1 | exact H2].
  - eapply (room_big MI); [exact AI | lia | apply HBG; lia].
Qed.

Lemma new_size_id : forall n, 1 <= n -> new_size n = n.
Proof using. intros n Hn. unfold new_size. lia. Qed.
End Room.

Section Placed2.
Context {AC : AllocCeiling}.
Variable SEGS : list Segment.
Variable L : Layout.
Variable MI : MallocIface SEGS L.
Lemma placed_mono : forall (A A' : AS MI) v n,
  (forall blk, In blk (live MI A) -> In blk (live MI A')) -> placed MI A v n -> placed MI A' v n.
Proof using AC SEGS L MI.
  intros A A' v n HL [H|(q & k & Hin & H1 & H2)]; [left; exact H | right].
  exists q, k. split; [apply HL, Hin | split; assumption].
Qed.
End Placed2.

Ltac in_cs := cbv; repeat (first [left; reflexivity | right]).

Definition fact (P : Prop) : Prop := P.
Ltac hide H := idtac; lazymatch type of H with ?T => change T with (fact T) in H end.
Ltac unhide H := unfold fact in H.
Ltac unhide_all := unfold fact in *.

Lemma rdn_wbytes_hit4 : forall segs m (a v : word),
  (bv_unsigned a + 4 <= 2 ^ 64)%Z ->
  rdn segs (wbytes m a (word_to_le_bytes 4 v)) a 4 = Some (word_to_le_bytes 4 v).
Proof.
  intros segs m a v H. rewrite <- (length_N_to_le_bytes 4 v) at 2.
  apply SeqExec.rdn_wbytes_hit. rewrite length_N_to_le_bytes. exact H.
Qed.

Lemma rdn_wbytes_hit1 : forall segs m (a v : word),
  (bv_unsigned a + 1 <= 2 ^ 64)%Z ->
  rdn segs (wbytes m a (word_to_le_bytes 1 v)) a 1 = Some (word_to_le_bytes 1 v).
Proof.
  intros segs m a v H. rewrite <- (length_N_to_le_bytes 1 v) at 2.
  apply SeqExec.rdn_wbytes_hit. rewrite length_N_to_le_bytes. exact H.
Qed.

Ltac ok_mdef_direct H :=
  idtac;
  lazymatch type of H with mdef ?M ?a ?n =>
    first [ apply (mdef_store_ok _ M a n _ H); lia
          | lazymatch goal with |- store_ok _ _ (Z_to_bv 64 ?a') ?k = true =>
              replace a' with (a + (a' - a))%Z by lia;
              apply (mdef_store_ok_off _ M a n (a' - a)%Z k H); lia end ]
  end.
Ltac ok_mdef H :=
  idtac;
  lazymatch type of H with mdef ?M _ _ =>
    lazymatch goal with |- store_ok _ ?X _ _ = true =>
      first [ constr_eq X M; ok_mdef_direct H
            | eapply store_ok_mono; [apply wbytes_grows|]; ok_mdef H ]
    end
  end.

Lemma mdef_through : forall (P : Z -> Prop) (M M' : mem) lo n,
  (forall a : word, M a <> None -> M' a <> None \/ P (bv_unsigned a)) ->
  mdef M lo n -> 0 <= lo -> lo + n < 2 ^ 64 -> (forall a, lo <= a < lo + n -> ~ P a) -> mdef M' lo n.
Proof.
  intros P M M' lo n DEF HD Hlo Hn HP i Hi.
  destruct (DEF (Z_to_bv 64 (lo + i)) (HD i Hi)) as [H|H]; [exact H|].
  exfalso. rewrite u64_of_Z in H by lia. exact (HP (lo + i) ltac:(lia) H).
Qed.

Section SxThrough.
Context {AC : AllocCeiling}.
Variable SEGS : list Segment.
Variable L : Layout.
Variable MI : MallocIface SEGS L.
Variable ST : StaticsIface SEGS L.
Hypothesis rw_img : forall a, in_ranges (ly_rw L) a -> in_ranges (ly_img L) a.
Hypothesis relro_img : forall a, in_ranges (ly_relro L) a -> in_ranges (ly_img L) a.
Hypothesis rw_not_relro : forall a, in_ranges (ly_rw L) a -> ~ in_ranges (ly_relro L) a.

Lemma sx_through : forall (s : SX ST) M M' (F : Z -> Prop),
  sx_inv ST s M -> frame_eq F M M' ->
  (forall a, F a -> ~ sx_region ST a /\ ~ in_ranges (ly_relro L) a) -> sx_inv ST s M'.
Proof using SEGS L ST.
  intros s M M' F SXI FR HF. apply (sx_frame ST s M M' SXI). intros a Ha. apply FR.
  intros Hf. destruct (HF _ Hf) as [H1 H2]. destruct Ha as [Ha|Ha]; [exact (H1 Ha)|exact (H2 Ha)].
Qed.

Lemma owned_not_sx : forall (A : AS MI) M model a,
  ainv MI A M model -> (forall a, owned MI A a -> ~ sx_region ST a) ->
  owned MI A a -> ~ sx_region ST a /\ ~ in_ranges (ly_relro L) a.
Proof using AC SEGS L MI ST relro_img rw_not_relro.
  intros A M model a AI Hos Ho. split; [exact (Hos a Ho)|].
  destruct (ai_owned_not_img_ro MI A M model a AI Ho) as [Hrw|Hni].
  - apply rw_not_relro, Hrw.
  - intros Hr. apply Hni, relro_img, Hr.
Qed.

Lemma owned_later_not_sx : forall (A A' : AS MI) M model (Mx : mem) a,
  ainv MI A M model -> (forall a, owned MI A a -> ~ sx_region ST a) ->
  (forall a, owned MI A' a -> owned MI A a \/ (~ in_ranges (ly_img L) a /\ Mx (Z_to_bv 64 a) = None)) ->
  owned MI A' a -> ~ sx_region ST a /\ ~ in_ranges (ly_relro L) a.
Proof using AC SEGS L MI ST rw_img relro_img rw_not_relro.
  intros A A' M model Mx a AI Hos NEWT Ho'. destruct (NEWT a Ho') as [Ho|[Hni _]].
  - exact (owned_not_sx A M model a AI Hos Ho).
  - split; intros H; apply Hni; [apply rw_img; exact (sx_region_rw ST a H) | apply relro_img, H].
Qed.

Lemma offimg_not_sx : forall a, ~ in_ranges (ly_img L) a -> ~ sx_region ST a /\ ~ in_ranges (ly_relro L) a.
Proof using SEGS L ST rw_img relro_img.
  intros a Hni. split; intros H; apply Hni; [apply rw_img; exact (sx_region_rw ST a H) | apply relro_img, H].
Qed.
End SxThrough.

Lemma firstn_repeat' : forall {T} (x : T) n k, (k <= n)%nat -> firstn k (repeat x n) = repeat x k.
Proof. intros T x n. induction n as [|n IH]; intros k Hk; [destruct k; [reflexivity|lia]|]. destruct k; [reflexivity|]. cbn. f_equal. apply IH. lia. Qed.
Lemma skipn_repeat' : forall {T} (x : T) n k, (k <= n)%nat -> skipn k (repeat x n) = repeat x (n - k).
Proof. intros T x n. induction n as [|n IH]; intros k Hk; [destruct k; [reflexivity|lia]|]. destruct k; [reflexivity|]. cbn. apply IH. lia. Qed.

Lemma rdn_zeros_sub : forall segs M (p : Z) (N : nat) (d : Z) (k : nat),
  0 <= p -> p + Z.of_nat N < 2 ^ 64 -> 0 <= d -> d + Z.of_nat k <= Z.of_nat N ->
  rdn segs (wbytes M (Z_to_bv 64 p) (repeat (Z_to_bv 8 0) N)) (Z_to_bv 64 (p + d)) k = Some (repeat (Z_to_bv 8 0) k).
Proof.
  intros segs M p N d k Hp HN Hd Hk.
  pose proof (rdn_wbytes_self segs M (Z_to_bv 64 p) (repeat (Z_to_bv 8 0) N)) as H.
  rewrite repeat_length in H. specialize (H ltac:(rewrite u64_of_Z by lia; lia)).
  pose proof (rdn_sub segs _ N (Z_to_bv 64 p) _ (Z.to_nat d) k H ltac:(lia)) as H2.
  unfold Hoare.at_ in H2. rewrite u64_of_Z in H2 by lia. replace (p + Z.of_nat (Z.to_nat d)) with (p + d) in H2 by lia.
  rewrite H2. unfold sub. rewrite skipn_repeat', firstn_repeat' by lia. reflexivity.
Qed.

Lemma w4_zero : word_to_le_bytes 4 (Z_to_bv 64 0) = repeat (Z_to_bv 8 0) 4.
Proof. reflexivity. Qed.
Lemma cbyte_zero : cbyte (Z_to_bv 64 0) = Z_to_bv 8 0.
Proof. reflexivity. Qed.
Lemma Znth_repeat : forall x n i, 0 <= i < Z.of_nat n -> Znth i (repeat x n) = x.
Proof. intros x n i Hi. unfold Znth. apply nth_repeat_lt. lia. Qed.

Section OpaqueReads.
Context {AC : AllocCeiling}.
Variable SEGS : list Segment.

Lemma mdef_rdn : forall M a n d (k : nat),
  mdef M a n -> 0 <= a -> a + n < 2 ^ 64 -> 0 <= d -> d + Z.of_nat k <= n ->
  exists bs, rdn SEGS M (Z_to_bv 64 (a + d)) k = Some bs /\ length bs = k.
Proof using SEGS.
  intros M a n d k HD Ha Hn Hd. revert d Hd. induction k as [|k IH]; intros d Hd Hk.
  - exists []. split; reflexivity.
  - destruct (M (Z_to_bv 64 (a + d))) as [b0|] eqn:Hb; [| exfalso; exact (HD d ltac:(lia) Hb)].
    destruct (IH (d + 1) ltac:(lia) ltac:(lia)) as (bs & Hbs & Hlen).
    exists (b0 :: bs). split; [| cbn; lia].
    cbn [rdn]. rewrite Hb.
    replace (Z_to_bv 64 (a + d) + 1)%bv with (Z_to_bv 64 (a + (d + 1))).
    + rewrite Hbs. reflexivity.
    + apply bv_eq. rewrite bv_add_unsigned, !Z_to_bv_unsigned, !bv_wrap64_mod. change (bv_unsigned (1%bv : bv 64)) with 1.
      rewrite (Z.mod_small (a + d)) by lia. rewrite (Z.mod_small (a + (d + 1))) by lia. rewrite Z.mod_small by lia. lia.
Qed.

Lemma lez4_val : forall bs, length bs = 4%nat -> bytes_le_to_Z bs = bv_unsigned (Z_to_bv 64 (bytes_le_to_Z bs)).
Proof using.
  intros bs Hl. pose proof (bytes_le_to_Z_bound bs) as Hb. rewrite Hl in Hb.
  pose proof (bytes_le_to_Z_nonneg bs). rewrite u64_of_Z; [reflexivity|]. cbn in Hb. lia.
Qed.
Lemma sw_lw_bytes : forall bs, length bs = 4%nat -> word_to_le_bytes 4 (v_lw (Z_to_bv 64 (bytes_le_to_Z bs))) = bs.
Proof using. intros bs Hl. exact (sw_bytes_LWv bs Hl). Qed.
End OpaqueReads.

Lemma v_mul_inv5 : forall c, 0 <= c -> 5 * c < 2 ^ 64 ->
  v_mul (Z_to_bv 64 (5 * c)) (Z_to_bv 64 0xcccccccccccccccd) = Z_to_bv 64 c.
Proof.
  intros c Hc H5. unfold v_mul. rewrite !u64_of_Z by lia. apply bv_eq.
  rewrite !Z_to_bv_unsigned, !bv_wrap64_mod.
  replace (5 * c * 0xcccccccccccccccd) with (c + (4 * c) * 2 ^ 64) by lia.
  rewrite Z.mod_add by lia. reflexivity.
Qed.

Lemma v_mul_Z : forall a b, 0 <= a < 2 ^ 64 -> 0 <= b < 2 ^ 64 -> v_mul (Z_to_bv 64 a) (Z_to_bv 64 b) = Z_to_bv 64 (a * b).
Proof. intros a b Ha Hb. unfold v_mul. rewrite !u64_of_Z by lia. reflexivity. Qed.
