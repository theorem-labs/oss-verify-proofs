(** What the walk of one property of the inlined pod builder uses (plain image, 0x130cc -> 0x13e68,
    pod.h:399-438): the frame cells as a list, the memory the walk carries through the block's stores, the frame
    stores and the calls of memset, the words the code computes, and the block images of the property's writes. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib Require Import Img0.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Lib Require Import Tac.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Prog Require Import SlotInv LLVMFuzzerTestOneInput_c.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Pod Require Import Cursor Model Layout.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Prog.RoleBuild Require Import Facts Cut Write Post.
Import ListNotations.
Open Scope Z_scope.

(** ** Words *)
(** `andi a1,a0,3` of the selector byte. *)
Lemma land3 : forall z, 0 <= z < 2^64 -> Z.land (bv_unsigned (Z_to_bv 64 z)) 3 = z mod 4.
Proof.
  intros z Hz. rewrite (unsigned_lit z) by lia. change 3 with (Z.ones 2). rewrite Z.land_ones by lia.
  reflexivity.
Qed.

(** A property of every byte, checked on the 256 of them. *)
Lemma all256 : forall (P : Z -> bool), forallb P (map Z.of_nat (seq 0 256)) = true ->
  forall z, 0 <= z < 256 -> P z = true.
Proof.
  intros P H z Hz. rewrite forallb_forall in H. apply H. apply in_map_iff.
  exists (Z.to_nat z). split; [lia | apply in_seq; lia].
Qed.

(** `andi a0,a0,0x10` of the selector byte is its bit 4 (pod.h:412). *)
Lemma land16 : forall z, 0 <= z < 256 ->
  Z.land (bv_unsigned (Z_to_bv 64 z)) 16 = if Z.testbit z 4 then 16 else 0.
Proof.
  intros z Hz. rewrite (unsigned_lit z) by lia.
  pose proof (all256 (fun z => Z.land z 16 =? (if Z.testbit z 4 then 16 else 0))
                ltac:(vm_compute; reflexivity) z Hz) as H.
  apply Z.eqb_eq in H. exact H.
Qed.

(** `subw` of two small nonnegative words. *)
Lemma subw_lit : forall a b, 0 <= a < 2^31 -> 0 <= b < 2^31 ->
  bv_swrap 32 (bv_unsigned (Z_to_bv 64 a) - bv_unsigned (Z_to_bv 64 b)) = a - b.
Proof.
  intros a b Ha Hb. rewrite (unsigned_lit a), (unsigned_lit b) by lia.
  apply bv_swrap_small. change (bv_half_modulus 32) with (2^31). lia.
Qed.

(** `addiw s9,s9,1` of the pod counter. *)
Lemma addiw1_lit : forall k, 0 <= k < 2^30 -> bv_swrap 32 (bv_unsigned (Z_to_bv 64 k) + 1) = k + 1.
Proof.
  intros k Hk. rewrite (unsigned_lit k) by lia.
  apply bv_swrap_small. change (bv_half_modulus 32) with (2^31). lia.
Qed.

(** The pad after a 12-byte tail of 8-aligned data is 4 (pod.h:187). *)
Lemma pad8_L4 : forall L c, (8 | L) -> pad8 (L + 8 * c + 4) = 4.
Proof.
  intros L c [d ->]. replace (d * 8 + 8 * c + 4) with ((d + c) * 8 + 4) by lia.
  rewrite pad8_shift by (exists (d + c); reflexivity). reflexivity.
Qed.

(** The four bytes of a put of a small literal, and of the two property keys (pod.h:407). *)
Lemma lb4 : forall v, 0 <= v < 256 ->
  le1 (Z_to_bv 64 v) ++ le1 (Z_to_bv 64 0) ++ le1 (Z_to_bv 64 0) ++ le1 (Z_to_bv 64 0) = le32 v.
Proof.
  intros v Hv. rewrite !le1_lit, le32_split.
  rewrite !Z.shiftr_div_pow2 by lia.
  change (2^8) with 256. change (2^16) with 65536. change (2^24) with 16777216.
  rewrite !(Z.div_small v) by lia.
  reflexivity.
Qed.

(** Two bytes are equal when their values agree modulo 256. *)
Lemma z8 : forall a b, a mod 256 = b mod 256 -> Z_to_bv 8 a = Z_to_bv 8 b.
Proof. intros a b H. apply bv_eq. rewrite !Z_to_bv_unsigned. exact H. Qed.

Lemma bytes4_eq : forall a0 a1 a2 a3 b0 b1 b2 b3,
  a0 mod 256 = b0 mod 256 -> a1 mod 256 = b1 mod 256 -> a2 mod 256 = b2 mod 256 -> a3 mod 256 = b3 mod 256 ->
  [Z_to_bv 8 a0; Z_to_bv 8 a1; Z_to_bv 8 a2; Z_to_bv 8 a3] = [Z_to_bv 8 b0; Z_to_bv 8 b1; Z_to_bv 8 b2; Z_to_bv 8 b3].
Proof.
  intros a0 a1 a2 a3 b0 b1 b2 b3 H0 H1 H2 H3.
  rewrite (z8 a0 b0 H0), (z8 a1 b1 H1), (z8 a2 b2 H2), (z8 a3 b3 H3). reflexivity.
Qed.

Lemma lbkey : forall K, K = 65539 \/ K = 524289 ->
  le1 (Z_to_bv 64 K) ++ le1 (Z_to_bv 64 0) ++ le1 (Z_to_bv 64 (Z.shiftr (bv_unsigned (Z_to_bv 64 K)) 16))
  ++ le1 (Z_to_bv 64 0) = le32 K.
Proof.
  intros K HK. rewrite !le1_lit, le32_split. cbn [app].
  destruct HK as [-> | ->]; apply bytes4_eq; vm_compute; reflexivity.
Qed.

(** Four byte stores side by side are one four-byte overwrite. *)
Lemma ow4 : forall (I : list byte) (o : Z) (x0 x1 x2 x3 : word), 0 <= o -> (Z.to_nat o + 4 <= length I)%nat ->
  overwrite (overwrite (overwrite (overwrite I (Z.to_nat o) (le1 x0)) (Z.to_nat (o + 1)) (le1 x1))
      (Z.to_nat (o + 2)) (le1 x2)) (Z.to_nat (o + 3)) (le1 x3)
  = overwrite I (Z.to_nat o) (le1 x0 ++ le1 x1 ++ le1 x2 ++ le1 x3).
Proof.
  intros I o x0 x1 x2 x3 Ho HI.
  replace (Z.to_nat (o + 1)) with (Z.to_nat o + length (le1 x0))%nat by (rewrite length_le1; lia).
  rewrite overwrite_adj by (rewrite !length_le1; lia).
  replace (Z.to_nat (o + 2)) with (Z.to_nat o + length (le1 x0 ++ le1 x1))%nat
    by (rewrite length_app, !length_le1; lia).
  rewrite overwrite_adj by (rewrite !length_app, !length_le1; lia).
  replace (Z.to_nat (o + 3)) with (Z.to_nat o + length ((le1 x0 ++ le1 x1) ++ le1 x2))%nat
    by (rewrite !length_app, !length_le1; lia).
  rewrite overwrite_adj by (rewrite !length_app, !length_le1; lia).
  rewrite <- !app_assoc. reflexivity.
Qed.

(** ** The record *)
Lemma seen_snoc : forall ps kv, seen_of (ps ++ [kv]) = seen_of ps || (fst kv =? POD_PROP_PARAMS).
Proof. intros ps kv. unfold seen_of. rewrite existsb_app. cbn [existsb]. rewrite orb_false_r. reflexivity. Qed.

Lemma seen_none : forall ps, seen_of ps = false -> first_params ps = None.
Proof.
  intros ps H. unfold seen_of in H. unfold first_params.
  destruct (find (fun kv => fst kv =? POD_PROP_PARAMS) ps) as [kv|] eqn:E; [|reflexivity].
  apply find_some in E as [Hin Hk]. exfalso.
  assert (HX : existsb (fun kv => fst kv =? POD_PROP_PARAMS) ps = true)
    by (apply existsb_exists; exists kv; split; assumption).
  congruence.
Qed.

Lemma seen_some : forall ps, seen_of ps = true -> first_params ps <> None.
Proof.
  intros ps H. unfold seen_of in H. unfold first_params.
  apply existsb_exists in H as [kv [Hin Hk]].
  destruct (find (fun kv => fst kv =? POD_PROP_PARAMS) ps) as [kv'|] eqn:E; [discriminate|].
  pose proof (find_none _ _ E kv Hin) as Hn. cbn in Hn. congruence.
Qed.

(** One more property keeps the record well formed while the loop has room. *)
Lemma wf_snoc : forall sh ps kv, pc_wf sh ps -> (length ps <= 2)%nat ->
  (0 <= fst kv < 2^32 /\ pval_wf (snd kv)) -> Forall ent_wf (ents_of (snd kv)) ->
  pc_wf sh (ps ++ [kv]).
Proof.
  intros sh ps kv (Hs & Hk & He & Hl) Hp Hkv Hes. unfold pc_wf.
  split; [exact Hs|]. split; [apply Forall_app; split; [exact Hk | constructor; [exact Hkv | constructor]]|].
  split.
  - unfold all_ents. rewrite flat_map_app. apply Forall_app. split; [exact He|].
    cbn [flat_map]. rewrite app_nil_r. destruct kv as [k [v|es]]; cbn in Hes |- *; [constructor | exact Hes].
  - rewrite length_app. cbn [length]. lia.
Qed.

(** ** The frame cells and the memory the walk carries *)
Section Kit.
Variables (sp : word) (m : word -> option byte) (rest : list byte) (src pp lo : Z).
Hypothesis HOK : BOK sp rest src pp lo.

Lemma krng : 0 < pp /\ pp + 19744 <= lo /\ lo + 96 <= bv_unsigned sp /\ 0 <= lo /\
             bv_unsigned sp + 392 <= 2^64 /\ 0 < src /\ src + Z.of_nat (length rest) <= lo.
Proof.
  destruct HOK as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & _).
  unfold POD_PROPS, MID_STACK, FRAME_LOCALS in *. lia.
Qed.

(** An 8-byte cell at sp + o of the frame's locals holding v. *)
Definition cok (m1 : word -> option byte) (ov : Z * Z) : Prop :=
  0 <= fst ov /\ fst ov + 8 <= 392 /\ cell8 m1 (bv_unsigned sp + fst ov) (snd ov).

Definition FC (m1 : word -> option byte) (xs : list (Z * Z)) : Prop := Forall (cok m1) xs.

(** A new cell meets none of the others. *)
Definition apart (o : Z) (xs : list (Z * Z)) : Prop := Forall (fun ov => fst ov + 8 <= o \/ o + 8 <= fst ov) xs.

Lemma FC_munch : forall m1 m2 (a n : Z) xs, FC m1 xs -> munch [(a, a + n)] m1 m2 -> a + n <= bv_unsigned sp ->
  FC m2 xs.
Proof.
  intros m1 m2 a n xs H MU Ha. unfold FC in *. eapply Forall_impl; [|exact H].
  intros [o v] (H1 & H2 & H3). cbn [fst snd] in *. split; [exact H1|]. split; [exact H2|].
  unfold cell8 in *. apply (bytes_at_transport rsegs _ m1 m2 _ _ H3 MU).
  cbn [disjoint_from]. rewrite length_le8. split; [lia | exact I].
Qed.

Lemma FC_write : forall m1 (a : Z) bs xs, FC m1 xs -> 0 <= a -> a + Z.of_nat (length bs) <= bv_unsigned sp ->
  FC (write_to_mem m1 (Z_to_bv 64 a) bs) xs.
Proof.
  intros m1 a bs xs H Ha Hb. pose proof krng as R.
  apply (FC_munch m1 _ a (Z.of_nat (length bs)) xs H); [|lia].
  apply munch_of_write; lia.
Qed.

Lemma FC_get : forall m1 xs o v, FC m1 xs -> In (o, v) xs -> cell8 m1 (bv_unsigned sp + o) v.
Proof. intros m1 xs o v H Hin. unfold FC in H. rewrite Forall_forall in H. exact (proj2 (proj2 (H (o, v) Hin))). Qed.

Lemma FC_sub : forall m1 xs ys, FC m1 xs -> (forall p, In p ys -> In p xs) -> FC m1 ys.
Proof.
  intros m1 xs ys H Hs. unfold FC in *. rewrite Forall_forall in H |- *. intros p Hp. apply H, Hs, Hp.
Qed.

Lemma FC_sd : forall m1 xs o v, FC m1 xs -> 0 <= o -> o + 8 <= 392 -> apart o xs ->
  FC (write_to_mem m1 (Z_to_bv 64 (bv_unsigned sp + o)) (le8 (Z_to_bv 64 v))) ((o, v) :: xs).
Proof.
  intros m1 xs o v H Ho1 Ho2 Hap. pose proof krng as R. constructor.
  - unfold cok. cbn [fst snd]. split; [exact Ho1|]. split; [exact Ho2|]. unfold cell8.
    apply bytes_at_write_same; rewrite ?length_le8; lia.
  - unfold FC, apart in *. rewrite Forall_forall in H, Hap |- *. intros [o' v'] Hin.
    specialize (H _ Hin). specialize (Hap _ Hin). unfold cok in *. cbn [fst snd] in *. destruct H as (H1 & H2 & H3).
    split; [exact H1|]. split; [exact H2|]. unfold cell8 in *.
    apply (bytes_at_write_other rsegs m1 (bv_unsigned sp + o) _ _ _ H3); rewrite ?length_le8; lia.
Qed.

(** The block, the frame cells xs, and pp->len = len (which leads the block image while a put is under way). *)
Definition MQ (xs : list (Z * Z)) (Ib : list byte) (len : Z) (m1 : word -> option byte) : Prop :=
  MBr sp m rest src pp lo Ib m1 /\ FC m1 xs /\ bytes_at rsegs m1 (pp + 16384) (le64 len).

Lemma mq_ilen : forall xs Ib len m1, MQ xs Ib len m1 -> Z.of_nat (length Ib) = 19744.
Proof. intros xs Ib len m1 ((_ & HL & _) & _). unfold POD_PROPS in HL. exact HL. Qed.

Lemma mq_ok : forall xs Ib len m1 (o a : Z) (j : nat), MQ xs Ib len m1 -> a = pp + o -> 0 <= o ->
  o + Z.of_nat j <= 19744 -> store_ok rsegs m1 (wa a) j = true.
Proof.
  intros xs Ib len m1 o a j (MB & _) -> Ho Hj.
  apply (MBr_pp_ok sp m rest src pp lo Ib m1 o j MB Ho). unfold POD_PROPS. lia.
Qed.

Lemma mq_rd_len : forall xs Ib len m1, MQ xs Ib len m1 ->
  ov_read_bytes rsegs m1 (wa (pp + 16384)) 8 = Some (le8 (Z_to_bv 64 len)).
Proof. intros xs Ib len m1 (_ & _ & HL). rewrite le8_lit64. apply rd8; [exact HL | apply length_le64]. Qed.

Lemma mq_rd : forall xs Ib len m1 o v, MQ xs Ib len m1 -> In (o, v) xs ->
  ov_read_bytes rsegs m1 (wa (bv_unsigned sp + o)) 8 = Some (le8 (Z_to_bv 64 v)).
Proof.
  intros xs Ib len m1 o v (_ & HF & _) Hin.
  apply rd8; [exact (FC_get m1 xs o v HF Hin) | apply length_le8].
Qed.

Lemma mq_sub : forall xs ys Ib len m1, MQ xs Ib len m1 -> (forall p, In p ys -> In p xs) -> MQ ys Ib len m1.
Proof.
  intros xs ys Ib len m1 (MB & HF & HL) Hs. split; [exact MB|]. split; [exact (FC_sub m1 xs ys HF Hs) | exact HL].
Qed.

Lemma mq_store : forall xs Ib len m1 (o a : Z) bs, MQ xs Ib len m1 -> a = pp + o -> 0 <= o ->
  o + Z.of_nat (length bs) <= 19744 -> (o + Z.of_nat (length bs) <= 16384 \/ 16392 <= o) ->
  MQ xs (overwrite Ib (Z.to_nat o) bs) len (write_to_mem m1 (Z_to_bv 64 a) bs).
Proof.
  intros xs Ib len m1 o a bs MQm -> Ho Hn Hd. pose proof krng as R.
  pose proof (mq_ilen _ _ _ _ MQm) as BL. pose proof MQm as (MB & HF & HL).
  split; [|split].
  - apply (MBr_pp_store sp m rest src pp lo HOK Ib m1 o bs MB Ho). lia.
  - apply FC_write; [exact HF | lia | lia].
  - apply (bytes_at_write_other rsegs m1 (pp + o) bs (pp + 16384) (le64 len) HL);
      [lia | lia | rewrite length_le64; lia].
Qed.

Lemma mq_setlen : forall xs Ib len len' m1, MQ xs Ib len m1 -> 0 <= len' ->
  MQ xs (overwrite Ib (Z.to_nat 16384) (le64 len')) len'
     (write_to_mem m1 (Z_to_bv 64 (pp + 16384)) (le64 len')).
Proof.
  intros xs Ib len len' m1 MQm Hl. pose proof krng as R.
  pose proof (mq_ilen _ _ _ _ MQm) as BL. pose proof MQm as (MB & HF & HL).
  split; [|split].
  - apply (MBr_pp_store sp m rest src pp lo HOK Ib m1 16384 (le64 len') MB ltac:(lia)).
    rewrite length_le64. lia.
  - apply FC_write; [exact HF | lia | rewrite length_le64; lia].
  - apply bytes_at_write_same; [lia | rewrite length_le64; lia].
Qed.

Lemma mq_call : forall xs Ib len m1 m2 (o n a : Z) bs, MQ xs Ib len m1 -> a = pp + o ->
  munch [(a, a + n)] m1 m2 -> wmono rsegs m1 m2 -> mem_inv rsegs m2 ->
  bytes_at rsegs m2 a bs -> Z.of_nat (length bs) = n -> 0 <= o -> o + n <= 19744 ->
  (o + n <= 16384 \/ 16392 <= o) ->
  MQ xs (overwrite Ib (Z.to_nat o) bs) len m2.
Proof.
  intros xs Ib len m1 m2 o n a bs MQm -> MU WM MI HB Hbs Ho Hn Hd. pose proof krng as R.
  pose proof (mq_ilen _ _ _ _ MQm) as BL. pose proof MQm as (MB & HF & HL).
  split; [|split].
  - apply (MBr_call_pp sp m rest src pp lo HOK Ib m1 m2 o n bs MB MU WM MI HB Hbs Ho).
    unfold POD_PROPS. lia.
  - apply (FC_munch m1 m2 (pp + o) n xs HF MU). lia.
  - apply (bytes_at_transport rsegs _ m1 m2 _ _ HL MU).
    cbn [disjoint_from]. rewrite length_le64. split; [lia | exact I].
Qed.

Lemma mq_sd : forall xs Ib len m1 (o v : Z), MQ xs Ib len m1 -> 0 <= o -> o + 8 <= 392 -> apart o xs ->
  MQ ((o, v) :: xs) Ib len (write_to_mem m1 (Z_to_bv 64 (bv_unsigned sp + o)) (le8 (Z_to_bv 64 v))) /\
  store_ok rsegs m1 (wa (bv_unsigned sp + o)) 8 = true.
Proof.
  intros xs Ib len m1 o v (MB & HF & HL) Ho1 Ho2 Hap. pose proof krng as R.
  split; [split; [|split]|].
  - apply (MBr_stk_store sp m rest src pp lo HOK Ib m1 (bv_unsigned sp + o) _ MB);
      rewrite ?length_le8; unfold MID_STACK, FRAME_LOCALS; lia.
  - apply FC_sd; assumption.
  - apply (bytes_at_write_other rsegs m1 (bv_unsigned sp + o) _ (pp + 16384) (le64 len) HL);
      rewrite ?length_le8, ?length_le64; lia.
  - apply (MBr_stk_ok sp m rest src pp lo HOK Ib m1 (bv_unsigned sp + o) 8 MB);
      unfold FRAME_LOCALS; lia.
Qed.

End Kit.

(** ** The block images of one property *)
Section Img.
Variables (sh : Z) (ps : list (Z * pval)).
Hypothesis HWF : pc_wf sh ps.
Hypothesis HPS : (length ps <= 2)%nat.

(** The buffer, its length and the struct's other fields when the property begins. *)
Definition bp : list byte := pc_buf (PbCut sh ps None).
Definition Lp : Z := Z.of_nat (length bp).
Definition ISP : bool := is_props (PodRec sh ps None).
Definition HSP : bool := has_params (PodRec sh ps None).
Definition PST : bool := params_struct (PodRec sh ps None).
Definition ENS : list ent := ents (PodRec sh ps None).
Definition IMq (b : list byte) : list byte := pp_image b ISP HSP PST ENS false.

Lemma img_start : pc_image (PbCut sh ps None) = IMq bp.
Proof. reflexivity. Qed.

Lemma Lp_rng : 8 <= Lp <= 3632 /\ (8 | Lp).
Proof.
  destruct (wf_facts sh ps HWF) as (H1 & _).
  destruct HWF as (_ & Hk & He & _).
  assert (Hv : Forall (fun kv => pval_wf (snd kv)) ps) by (eapply Forall_impl; [|exact Hk]; intros kv (_ & H); exact H).
  destruct (pc_buf_len_none sh ps Hv He) as (H2 & H3).
  unfold Lp, bp. split; [lia | exact H3].
Qed.

Lemma ENS_wf : (length ENS <= 32)%nat /\ Forall (fun e => (length (e_body e) <= 96)%nat) ENS.
Proof. destruct (wf_facts sh ps HWF) as (_ & _ & H1 & H2). split; assumption. Qed.

Lemma Lp_def : Lp = Z.of_nat (length bp).
Proof. reflexivity. Qed.

Lemma IMq_len : forall b, Z.of_nat (length b) <= 16384 -> Z.of_nat (length (IMq b)) = 19744.
Proof.
  intros b Hb. destruct ENS_wf as (H1 & H2).
  pose proof (length_pp_image b ISP HSP PST ENS false Hb H1 H2) as H. unfold PP_SIZE in H. exact H.
Qed.

(** One put: x after b in buf, then len (pod.h:179-180). *)
Lemma img_put : forall (b x : list byte) (o v : Z), o = Z.of_nat (length b) -> v = o + Z.of_nat (length x) ->
  Z.of_nat (length b + length x) <= 16384 ->
  overwrite (overwrite (IMq b) (Z.to_nat o) x) (Z.to_nat 16384) (le64 v) = IMq (b ++ x).
Proof. intros b x o v -> -> H. rewrite Nat2Z.id. unfold IMq. apply img_app. exact H. Qed.

(** A property that is not the first SPA_PROP_params leaves the struct's other fields as they are. *)
Lemma img_same : forall kv, first_params (ps ++ [kv]) = first_params ps ->
  pc_image (PbCut sh (ps ++ [kv]) None) = IMq (bp ++ prop_bytes sh kv).
Proof.
  intros kv H. unfold pc_image, IMq, bp, ISP, HSP, PST, ENS. rewrite <- pc_buf_prop.
  cbn [pc_shape pc_props pc_open]. unfold has_params, params_struct, pc_ents, ents. cbn [p_props pc_props pc_open].
  rewrite H. destruct (first_params ps) as [[]|]; reflexivity.
Qed.

Lemma fp_other : forall kv, fst kv <> POD_PROP_PARAMS -> first_params (ps ++ [kv]) = first_params ps.
Proof.
  intros kv H. rewrite first_params_app. destruct (first_params ps); [reflexivity|].
  replace (fst kv =? POD_PROP_PARAMS) with false by (symmetry; apply Z.eqb_neq; exact H). reflexivity.
Qed.

Lemma fp_seen : forall kv, seen_of ps = true -> first_params (ps ++ [kv]) = first_params ps.
Proof.
  intros kv H. rewrite first_params_app. destruct (first_params ps) eqn:E; [reflexivity|].
  exfalso. exact (seen_some ps H E).
Qed.

(** The first SPA_PROP_params, an Int: has_params = 1 (pod.h:417-418). *)
Lemma img_int_first : forall v, seen_of ps = false ->
  overwrite (IMq (bp ++ prop_bytes sh (POD_PROP_PARAMS, PInt v))) (Z.to_nat OFF_HAS_PARAMS) (le4 (Z_to_bv 64 1))
  = pc_image (PbCut sh (ps ++ [(POD_PROP_PARAMS, PInt v)]) None).
Proof.
  intros v Hs. pose proof (seen_none ps Hs) as HN.
  destruct ENS_wf as (HE1 & HE2).
  assert (Hb : Z.of_nat (length (bp ++ prop_bytes sh (POD_PROP_PARAMS, PInt v))) <= POD_BUF_MAX).
  { unfold bp. rewrite pc_buf_prop. destruct (wf_facts sh (ps ++ [(POD_PROP_PARAMS, PInt v)])) as (H & _).
    - apply wf_snoc; [exact HWF | exact HPS | cbn; split; [unfold POD_PROP_PARAMS; lia | exact I] | constructor].
    - unfold POD_BUF_MAX. lia. }
  rewrite le4_lit32. replace (le32 1) with (le32 (Z.b2z true)) by reflexivity. unfold IMq.
  rewrite (pp_image_has_params _ _ _ _ _ false Hb) by assumption.
  unfold pc_image, bp, ISP, PST, ENS. rewrite <- pc_buf_prop.
  cbn [pc_shape pc_props pc_open]. unfold has_params, params_struct, pc_ents, ents. cbn [p_props pc_props pc_open].
  rewrite first_params_app, HN. cbn [fst snd]. rewrite Z.eqb_refl. reflexivity.
Qed.

(** Opening a params Struct: its key, flags, a size word 0 and the type (pod.h:407-408, :421-423). *)
Lemma img_open : pc_image (PbCut sh ps (Some [])) =
  IMq (bp ++ le32 POD_PROP_PARAMS ++ le32 0 ++ le32 0 ++ le32 POD_STRUCT).
Proof.
  unfold pc_image, IMq, bp, ISP, HSP, PST, ENS. cbn [pc_shape pc_props].
  rewrite <- pc_buf_open. rewrite <- ?app_assoc. f_equal.
Qed.

(** An Int property of an object that is not a Struct: key, flags, then the pod (pod.h:407-408, :413-416). *)
Lemma pb_int : forall K v, sh <> 7 ->
  prop_bytes sh (K, PInt v) = le32 K ++ le32 0 ++ le32 4 ++ le32 4 ++ le32 v ++ zeros 4.
Proof.
  intros K v H. unfold prop_bytes. replace (sh =? 7) with false by (symmetry; apply Z.eqb_neq; exact H).
  reflexivity.
Qed.

(** The params Struct's size word (pod.h:434): the cut is closed. *)
Lemma img_patch : forall es LEN, sh <> 7 -> LEN = Z.of_nat (length (pc_buf (PbCut sh ps (Some es)))) ->
  overwrite (pc_image (PbCut sh ps (Some es))) (Z.to_nat (Lp + 8)) (le32 (LEN - (Lp + 8) + -8))
  = pp_image (pc_buf (PbCut sh (ps ++ [(POD_PROP_PARAMS, PStruct es)]) None)) ISP HSP PST
      (pc_ents (PbCut sh ps (Some es))) false.
Proof.
  intros es LEN H7 HL.
  assert (E : pc_buf (PbCut sh ps (Some es))
              = bp ++ le32 POD_PROP_PARAMS ++ le32 0 ++ le32 0 ++ le32 POD_STRUCT ++ flat_map enc_pod es).
  { unfold bp, pc_buf, open_bytes. cbn [pc_shape pc_props pc_open]. rewrite <- !app_assoc. reflexivity. }
  assert (HLB : (length bp + 16 <= length (pc_buf (PbCut sh ps (Some es))))%nat)
    by (rewrite E, !length_app, !length_le32; lia).
  unfold pc_image. cbn [pc_shape pc_props].
  rewrite <- pp_image_patch by (rewrite length_le32; unfold Lp; lia).
  f_equal.
  change (pc_buf (PbCut sh (ps ++ [(POD_PROP_PARAMS, PStruct es)]) None))
    with (pc_buf (pc_close (PbCut sh ps (Some es)))).
  rewrite <- (pc_buf_close sh ps es H7).
  replace (Z.to_nat (Lp + 8)) with (length (pc_buf (PbCut sh ps None)) + 8)%nat by (unfold Lp, bp; lia).
  replace (LEN - (Lp + 8) + -8)
    with (Z.of_nat (length (pc_buf (PbCut sh ps (Some es)))) - Z.of_nat (length (pc_buf (PbCut sh ps None))) - 16)
    by (rewrite HL; unfold Lp, bp; lia).
  reflexivity.
Qed.

Lemma struct_wf : forall es, Forall ent_wf es -> (length es <= 32)%nat ->
  pc_wf sh (ps ++ [(POD_PROP_PARAMS, PStruct es)]).
Proof.
  intros es Hes Hel. apply wf_snoc; [exact HWF | exact HPS | cbn; unfold POD_PROP_PARAMS; split; [lia | exact Hel]
                                   | exact Hes].
Qed.

(** The first SPA_PROP_params, a Struct: has_params = params_struct = 1 (pod.h:435-437). *)
Lemma img_close_first : forall es LEN, sh <> 7 -> seen_of ps = false -> Forall ent_wf es -> (length es <= 32)%nat ->
  LEN = Z.of_nat (length (pc_buf (PbCut sh ps (Some es)))) ->
  overwrite (overwrite (overwrite (pc_image (PbCut sh ps (Some es))) (Z.to_nat (Lp + 8))
                                   (le32 (LEN - (Lp + 8) + -8)))
                       (Z.to_nat 16396) (le4 (Z_to_bv 64 1)))
            (Z.to_nat 16400) (le4 (Z_to_bv 64 1))
  = pc_image (PbCut sh (ps ++ [(POD_PROP_PARAMS, PStruct es)]) None).
Proof.
  intros es LEN H7 Hs Hes Hel HL. pose proof (seen_none ps Hs) as HN.
  rewrite (img_patch es LEN H7 HL).
  assert (EE : pc_ents (PbCut sh ps (Some es)) = es)
    by (unfold pc_ents; cbn [pc_props pc_open]; rewrite HN; reflexivity).
  rewrite EE.
  destruct (wf_facts sh (ps ++ [(POD_PROP_PARAMS, PStruct es)]) (struct_wf es Hes Hel)) as (Hb & _).
  assert (Hb' : Z.of_nat (length (pc_buf (PbCut sh (ps ++ [(POD_PROP_PARAMS, PStruct es)]) None))) <= POD_BUF_MAX)
    by (unfold POD_BUF_MAX; lia).
  pose proof (bodies96 es Hes) as HE2.
  replace (le4 (Z_to_bv 64 1)) with (le32 (Z.b2z true)) by (rewrite le4_lit32; reflexivity).
  change 16396%Z with OFF_HAS_PARAMS. change 16400%Z with OFF_PARAMS_STRUCT.
  rewrite (pp_image_has_params _ _ _ _ _ false Hb') by assumption.
  rewrite (pp_image_params_struct _ _ _ _ _ false Hb') by assumption.
  unfold pc_image. cbn [pc_shape pc_props pc_open].
  unfold has_params, params_struct, pc_ents. cbn [p_props pc_props pc_open].
  rewrite first_params_app, HN. cbn [fst snd]. rewrite Z.eqb_refl. reflexivity.
Qed.

(** A later SPA_PROP_params Struct: only its size word. *)
Lemma img_close_other : forall es LEN, sh <> 7 -> seen_of ps = true ->
  LEN = Z.of_nat (length (pc_buf (PbCut sh ps (Some es)))) ->
  overwrite (pc_image (PbCut sh ps (Some es))) (Z.to_nat (Lp + 8)) (le32 (LEN - (Lp + 8) + -8))
  = pc_image (PbCut sh (ps ++ [(POD_PROP_PARAMS, PStruct es)]) None).
Proof.
  intros es LEN H7 Hs HL. pose proof (seen_some ps Hs) as HS.
  rewrite (img_patch es LEN H7 HL).
  unfold pc_image, ISP, HSP, PST. cbn [pc_shape pc_props pc_open].
  unfold has_params, params_struct, pc_ents. cbn [p_props pc_props pc_open].
  rewrite (fp_seen (POD_PROP_PARAMS, PStruct es) Hs).
  destruct (first_params ps) as [[]|]; [reflexivity | reflexivity | exfalso; exact (HS eq_refl)].
Qed.

End Img.
