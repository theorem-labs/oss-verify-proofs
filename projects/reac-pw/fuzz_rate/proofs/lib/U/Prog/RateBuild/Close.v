(** The close of a params Struct in the UBSan builder of reac-pw/fuzz_rate's LLVMFuzzerTestOneInput,
    0x14080 -> 0x140c8 (pod.h:434-437), proved against [Cut.S_close]: the two bounds checks of pod_patch32 on `at`
    (0x14088 `bgeu a5,0x4001`, 0x1408c `bltu s6,a5` with s6 = ~pp; not taken), the Struct's size word written as
    four byte stores at a4 = &buf[at] (0x140a4-0x140b0), and, for the first SPA_PROP_params property (the cell
    `first` at sp + 0xe0, 0x140b4 / 0x140b8), has_params and params_struct at s11 + 0xc / + 0x10 (0x140c0, 0x140c4;
    s11 = pp + 0x4000). seen_params is s9 (= 1 at [PCLOSE]) and stays there to the latch.
    Ported from reac-pw/fuzz_role's U/Prog/RoleBuild/Close.v (its close
    0x13db4 -> 0x13e00), re-walked at rate's registers and cells.

    Also here, shared with [Write], [Shape7] and [Int7]: frame cells (all below sp + 0xe8) are kept by every write
    below sp, a store into the block as an overwrite of its image, the dead pointer-overflow test `~x <u y`, and
    the small 32-bit wraps. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Lib Require Import Tac.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.U Require Import Img0.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.U.Prog Require Import SlotInv LLVMFuzzerTestOneInput_c.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.U.Prog.RateBuild Require Import Facts Cut.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Pod Require Import Cursor Model Layout.
Import ListNotations.
Open Scope Z_scope.

(** ** Words *)
(** `~x <u y` is false when x + y does not wrap: the pointer-overflow checks of pod_patch32 and of &ent[n]. *)
Lemma lnot_ltu_false : forall x y, 0 <= x -> 0 <= y -> x + y < 2^64 ->
  bv_ltu (Z_to_bv 64 (Z.lnot x)) (Z_to_bv 64 y) = false.
Proof.
  intros x y Hx Hy Hxy. rewrite bv_ltu_lit, (umod_id y) by lia.
  pose proof (Z.add_lnot_diag x) as E. replace (Z.lnot x) with (- x - 1) by lia.
  rewrite umod_neg by lia. apply Z.ltb_ge. lia.
Qed.

Lemma swrap32_small : forall z, -2^31 <= z < 2^31 -> bv_swrap 32 z = z.
Proof. intros z Hz. apply bv_swrap_small. change (bv_half_modulus 32) with (2^31). lia. Qed.

(** A four-byte store of a literal word writes the field [le32] holds. *)
Lemma le4_le32 : forall t, le4 (Z_to_bv 64 t) = le32 t.
Proof. intros t. unfold le4, le32. rewrite unsigned_lit_wrap. apply Z_to_le_bytes_mod. cbn. lia. Qed.

(** The four byte stores of pod_patch32: the value, then its three shifts (each as the code computed it). *)
Lemma le1x4_le32 : forall v x0 x1 x2 x3, x0 = v -> x1 = Z.shiftr v 8 -> x2 = Z.shiftr v 16 -> x3 = Z.shiftr v 24 ->
  le1 (Z_to_bv 64 x0) ++ le1 (Z_to_bv 64 x1) ++ le1 (Z_to_bv 64 x2) ++ le1 (Z_to_bv 64 x3) = le32 v.
Proof. intros v x0 x1 x2 x3 -> -> -> ->. apply le32_of_stores. Qed.

(** Four adjacent one-byte overwrites are one four-byte overwrite. *)
Lemma overwrite_4x1 : forall (I b0 b1 b2 b3 : list byte) (o : Z),
  length b0 = 1%nat -> length b1 = 1%nat -> length b2 = 1%nat -> length b3 = 1%nat ->
  0 <= o -> (Z.to_nat o + 4 <= length I)%nat ->
  overwrite (overwrite (overwrite (overwrite I (Z.to_nat o) b0) (Z.to_nat (o + 1)) b1) (Z.to_nat (o + 2)) b2)
    (Z.to_nat (o + 3)) b3
  = overwrite I (Z.to_nat o) (b0 ++ b1 ++ b2 ++ b3).
Proof.
  intros I b0 b1 b2 b3 o L0 L1 L2 L3 Ho HI.
  replace (Z.to_nat (o + 1)) with (Z.to_nat o + length b0)%nat by lia.
  rewrite overwrite_adj by lia.
  replace (Z.to_nat (o + 2)) with (Z.to_nat o + length (b0 ++ b1))%nat by (rewrite length_app; lia).
  rewrite overwrite_adj by (rewrite !length_app; lia).
  replace (Z.to_nat (o + 3)) with (Z.to_nat o + length ((b0 ++ b1) ++ b2))%nat by (rewrite !length_app; lia).
  rewrite overwrite_adj by (rewrite !length_app; lia).
  rewrite <- !app_assoc. reflexivity.
Qed.

(** ** Memory kept by a write that misses it *)
Lemma bytes_at_keep : forall W m1 m2 A bs, bytes_at rsegs m1 A bs -> munch W m1 m2 ->
  (forall x, A <= x < A + Z.of_nat (length bs) -> outside W x) -> bytes_at rsegs m2 A bs.
Proof.
  intros W m1 m2 A bs (H0 & H1 & H) MU HO. split; [exact H0|]. split; [exact H1|].
  intros i Hi. rewrite <- (H i Hi). unfold mrd. rewrite (MU (wa (A + Z.of_nat i))); [reflexivity|].
  rewrite wa_unsigned by lia. apply HO. lia.
Qed.

Lemma MBr_ext : forall sp m rest src pp lo Ib Ib' m1,
  MBr sp m rest src pp lo Ib m1 -> Ib = Ib' -> MBr sp m rest src pp lo Ib' m1.
Proof. intros; subst; assumption. Qed.


(** The frame's cells lie in [sp, sp + 0xe8) (the header values at 0x8-0x30, the preheader's constants, the
    object's and the Struct's cells up to `first` at 0xe0), inside the locals [sp, sp + 0x1e8): a write that misses
    the locals keeps them. *)
Section Above.
Variables (sp : word) (W : list (Z * Z)) (m1 m2 : word -> option byte).
Hypothesis MU : munch W m1 m2.
Hypothesis HW : forall x, bv_unsigned sp <= x < bv_unsigned sp + FRAME_LOCALS -> outside W x.

Lemma bytes_above : forall o bs, 0 <= o -> o + Z.of_nat (length bs) <= FRAME_LOCALS ->
  bytes_at rsegs m1 (bv_unsigned sp + o) bs -> bytes_at rsegs m2 (bv_unsigned sp + o) bs.
Proof. intros o bs H1 H2 H. apply (bytes_at_keep W m1 m2 _ _ H MU). intros x Hx. apply HW. lia. Qed.

Lemma cell8_above : forall o v, 0 <= o -> o + 8 <= FRAME_LOCALS ->
  cell8 m1 (bv_unsigned sp + o) v -> cell8 m2 (bv_unsigned sp + o) v.
Proof. intros o v H1 H2 H. unfold cell8 in *. apply bytes_above; [lia | rewrite length_le8; lia | exact H]. Qed.

Ltac cells_above :=
  repeat match goal with |- _ /\ _ => split end;
  (apply cell8_above; [lia | unfold FRAME_LOCALS; lia | assumption]).

Lemma CFIX_above : forall pp, CFIX sp pp m1 -> CFIX sp pp m2.
Proof.
  intros pp HC. unfold CFIX in *.
  destruct HC as (C00 & C50 & C58 & C78 & C80 & C88 & C90 & C98 & CA0 & CB8 & CC0 & CC8 & CD8). cells_above.
Qed.

Lemma CHDR_above : forall Hd, CHDR sp Hd m1 -> CHDR sp Hd m2.
Proof.
  intros Hd HC. unfold CHDR in *. destruct HC as (C08 & C10 & C18 & C20 & C28 & C30). cells_above.
Qed.

Lemma CPROP_above : forall fl Hd sh np, CPROP sp fl Hd sh np m1 -> CPROP sp fl Hd sh np m2.
Proof.
  intros fl Hd sh np HC. unfold CPROP in *. destruct HC as (C38 & CA8 & CB0 & CH).
  split; [|split; [|split]]; [cells_above | cells_above | cells_above | exact (CHDR_above Hd CH)].
Qed.

Lemma CVAR_above : forall fl pp Hd sh np ps i cnt,
  CVAR sp fl pp Hd sh np ps i cnt m1 -> CVAR sp fl pp Hd sh np ps i cnt m2.
Proof.
  intros fl pp Hd sh np ps i cnt HC. unfold CVAR in *. destruct HC as (CP & C40 & C60 & C68 & C70 & CD0 & CE0).
  split; [exact (CPROP_above fl Hd sh np CP)|]. cells_above.
Qed.

End Above.

(** A write at [a, a + n) below sp misses the frame's cells. *)
Lemma below_misses : forall (sp : word) a n x, a + n <= bv_unsigned sp ->
  bv_unsigned sp <= x < bv_unsigned sp + FRAME_LOCALS -> outside [(a, a + n)] x.
Proof. intros sp a n x Hb Hx. cbn [outside]. split; [lia | exact I]. Qed.

(** A fact about memory that reads only the frame's locals [sp, sp + 0x1e8): every write that misses them keeps
    it. *)
Definition frame_only (sp : word) (P : (word -> option byte) -> Prop) : Prop :=
  forall W m1 m2, munch W m1 m2 -> (forall x, bv_unsigned sp <= x < bv_unsigned sp + FRAME_LOCALS -> outside W x) ->
  P m1 -> P m2.

Lemma frame_only_write : forall sp P m1 (w : word) a bs, frame_only sp P -> P m1 -> w = wa a -> 0 <= a ->
  a + Z.of_nat (length bs) <= bv_unsigned sp -> P (write_to_mem m1 w bs).
Proof.
  intros sp P m1 w a bs HP H1 -> Ha Hb.
  pose proof (bv_unsigned_in_range 64 sp) as Hsp. unfold bv_modulus in Hsp. change (2 ^ Z.of_N 64) with (2^64) in Hsp.
  apply (HP [(a, a + Z.of_nat (length bs))] m1); [apply munch_of_write; lia | | exact H1].
  intros x Hx. apply (below_misses sp); assumption.
Qed.

(** ** A store into the block, at an address the semantics leaves in any convertible form *)
Lemma MBr_pp_store_w : forall sp m rest src pp lo, BOK sp rest src pp lo ->
  forall Ib m1 (w : word) (o : Z) bs, MBr sp m rest src pp lo Ib m1 -> w = wa (pp + o) -> 0 <= o ->
  o + Z.of_nat (length bs) <= POD_PROPS ->
  MBr sp m rest src pp lo (overwrite Ib (Z.to_nat o) bs) (write_to_mem m1 w bs).
Proof.
  intros sp m rest src pp lo HK Ib m1 w o bs MB -> Ho Hl.
  pose proof (MBr_bounds sp m rest src pp lo Ib m1 MB) as (_ & _ & HL).
  apply (MBr_pp_store sp m rest src pp lo HK Ib m1 o bs MB Ho). lia.
Qed.

(** ** The cells this piece reads back: the preheader's constants, the object's (with the header values) and
       `first` (sp + 0xe0) *)
Definition FCL (sp : word) (pp fl : Z) (Hd : hdr) (sh np : Z) (b : bool) (m1 : word -> option byte) : Prop :=
  CFIX sp pp m1 /\ CPROP sp fl Hd sh np m1 /\ cell8 m1 (bv_unsigned sp + 0xe0) (Z.b2z b).

Lemma FCL_frame : forall sp pp fl Hd sh np b, frame_only sp (FCL sp pp fl Hd sh np b).
Proof.
  intros sp pp fl Hd sh np b W m1 m2 MU HW (CF & CP & CE0).
  split; [exact (CFIX_above sp W m1 m2 MU HW pp CF)|].
  split; [exact (CPROP_above sp W m1 m2 MU HW fl Hd sh np CP)|].
  apply (cell8_above sp W m1 m2 MU HW); [lia | unfold FRAME_LOCALS; lia | assumption].
Qed.

(** ** The record at the close *)
Lemma pc_buf_open_len : forall s ps es,
  length (pc_buf (PbCut s ps (Some es))) = (length (pc_buf (PbCut s ps None)) + 16 + length (flat_map enc_pod es))%nat.
Proof.
  intros s ps es. unfold pc_buf, open_bytes. cbn [pc_shape pc_props pc_open].
  rewrite !length_app, !length_le32. cbn [length]. lia.
Qed.

Lemma close_lengths : forall sh ps es, pc_wf sh ps -> Forall ent_wf es -> (length ps <= 2)%nat ->
  (length es <= 32)%nat ->
  Z.of_nat (length (pc_buf (PbCut sh ps None))) <= 3632 /\
  Z.of_nat (length (pc_buf (PbCut sh ps (Some es))))
    = Z.of_nat (length (pc_buf (PbCut sh ps None))) + 16 + Z.of_nat (length (flat_map enc_pod es)) /\
  Z.of_nat (length (flat_map enc_pod es)) <= 1792.
Proof.
  intros sh ps es (_ & Hkv & He & _) Hes Hp Hk.
  assert (Hv : Forall (fun kv => pval_wf (snd kv)) ps)
    by (eapply Forall_impl; [|exact Hkv]; intros kv [_ H]; exact H).
  destruct (pc_buf_len_none sh ps Hv He) as [H1 _]. destruct (ents_len_bound es Hes) as [H2 _].
  split; [lia|]. split; [|lia]. rewrite (pc_buf_open_len sh ps es). lia.
Qed.

Lemma first_params_none : forall ps, seen_of ps = false -> first_params ps = None.
Proof.
  intros ps H. unfold seen_of in H. unfold first_params.
  destruct (find (fun kv => fst kv =? POD_PROP_PARAMS) ps) as [kv|] eqn:E; [|reflexivity].
  apply find_some in E as [Hin Hk]. exfalso.
  assert (HX : existsb (fun kv => fst kv =? POD_PROP_PARAMS) ps = true)
    by (apply existsb_exists; exists kv; split; assumption).
  congruence.
Qed.

Lemma first_params_some : forall ps, seen_of ps = true -> exists v, first_params ps = Some v.
Proof.
  intros ps H. unfold seen_of in H. apply existsb_exists in H as [kv [Hin Hk]]. unfold first_params.
  destruct (find (fun kv => fst kv =? POD_PROP_PARAMS) ps) as [kv'|] eqn:E; [eexists; reflexivity|].
  exfalso. pose proof (find_none _ _ E kv Hin) as Hn. cbn in Hn. congruence.
Qed.

Lemma seen_close : forall ps es, seen_of (ps ++ [(POD_PROP_PARAMS, PStruct es)]) = true.
Proof.
  intros ps es. unfold seen_of. rewrite existsb_app. cbn [existsb fst]. rewrite Z.eqb_refl.
  rewrite orb_true_r. reflexivity.
Qed.

Lemma pc_wf_close : forall sh ps es, pc_wf sh ps -> Forall ent_wf es -> (length es <= 32)%nat ->
  (length ps <= 2)%nat -> pc_wf sh (ps ++ [(POD_PROP_PARAMS, PStruct es)]).
Proof.
  intros sh ps es (H1 & H2 & H3 & H4) He Hl Hp.
  split; [exact H1|]. split.
  - apply Forall_app. split; [exact H2|]. constructor; [|constructor].
    cbn [fst snd pval_wf]. split; [unfold POD_PROP_PARAMS; lia | exact Hl].
  - split.
    + unfold all_ents. rewrite flat_map_app. cbn [flat_map snd]. rewrite app_nil_r.
      apply Forall_app. split; [exact H3 | exact He].
    + rewrite length_app. cbn [length]. lia.
Qed.

(** The size word written over the open Struct's 0 (pod.h:434) turns the cut's buffer into the closed one. *)
Lemma close_image_patch : forall sh ps es, sh <> 7 ->
  overwrite (pc_image (PbCut sh ps (Some es))) (length (pc_buf (PbCut sh ps None)) + 8)
    (le32 (Z.of_nat (length (pc_buf (PbCut sh ps (Some es)))) - Z.of_nat (length (pc_buf (PbCut sh ps None))) - 16))
  = pp_image (pc_buf (PbCut sh (ps ++ [(POD_PROP_PARAMS, PStruct es)]) None))
      (is_props (PodRec sh ps None)) (has_params (PodRec sh ps None)) (params_struct (PodRec sh ps None))
      (pc_ents (PbCut sh ps (Some es))) false.
Proof.
  intros sh ps es Hsh. unfold pc_image. cbn [pc_shape pc_props].
  rewrite <- pp_image_patch.
  - rewrite (pc_buf_close sh ps es Hsh). reflexivity.
  - rewrite length_le32, (pc_buf_open_len sh ps es). lia.
Qed.

Lemma pc_buf_close_len : forall sh ps es, sh <> 7 ->
  length (pc_buf (PbCut sh (ps ++ [(POD_PROP_PARAMS, PStruct es)]) None)) = length (pc_buf (PbCut sh ps (Some es))).
Proof.
  intros sh ps es Hsh.
  change (pc_buf (PbCut sh (ps ++ [(POD_PROP_PARAMS, PStruct es)]) None))
    with (pc_buf (pc_close (PbCut sh ps (Some es)))).
  rewrite <- (pc_buf_close sh ps es Hsh). apply length_overwrite.
  rewrite length_le32, (pc_buf_open_len sh ps es). lia.
Qed.

(** The block after the close: for the first params Struct also has_params and params_struct (pod.h:436-437). *)
Lemma close_image_first : forall sh ps es (I0 : list byte) bsH bsP,
  sh <> 7 -> first_params ps = None ->
  Z.of_nat (length (pc_buf (PbCut sh ps (Some es)))) <= POD_BUF_MAX ->
  (length es <= 32)%nat -> Forall ent_wf es ->
  I0 = overwrite (pc_image (PbCut sh ps (Some es))) (length (pc_buf (PbCut sh ps None)) + 8)
    (le32 (Z.of_nat (length (pc_buf (PbCut sh ps (Some es)))) - Z.of_nat (length (pc_buf (PbCut sh ps None))) - 16)) ->
  bsH = le32 1 -> bsP = le32 1 ->
  overwrite (overwrite I0 (Z.to_nat OFF_HAS_PARAMS) bsH) (Z.to_nat OFF_PARAMS_STRUCT) bsP
  = pc_image (PbCut sh (ps ++ [(POD_PROP_PARAMS, PStruct es)]) None).
Proof.
  intros sh ps es I0 bsH bsP Hsh HN Hb Hl He -> -> ->.
  rewrite (close_image_patch sh ps es Hsh).
  assert (FP : first_params (ps ++ [(POD_PROP_PARAMS, PStruct es)]) = Some (PStruct es)).
  { rewrite first_params_app, HN. cbn [fst snd]. rewrite Z.eqb_refl. reflexivity. }
  assert (E0 : pc_ents (PbCut sh ps (Some es)) = es)
    by (unfold pc_ents; cbn [pc_props pc_open]; rewrite HN; reflexivity).
  assert (H0 : has_params (PodRec sh ps None) = false) by (unfold has_params; cbn [p_props]; rewrite HN; reflexivity).
  assert (P0 : params_struct (PodRec sh ps None) = false)
    by (unfold params_struct; cbn [p_props]; rewrite HN; reflexivity).
  assert (H1 : has_params (PodRec sh (ps ++ [(POD_PROP_PARAMS, PStruct es)]) None) = true)
    by (unfold has_params; cbn [p_props]; rewrite FP; reflexivity).
  assert (P1 : params_struct (PodRec sh (ps ++ [(POD_PROP_PARAMS, PStruct es)]) None) = true)
    by (unfold params_struct; cbn [p_props]; rewrite FP; reflexivity).
  assert (E1 : pc_ents (PbCut sh (ps ++ [(POD_PROP_PARAMS, PStruct es)]) None) = es)
    by (unfold pc_ents; cbn [pc_props pc_open]; rewrite FP; reflexivity).
  assert (HB : Z.of_nat (length (pc_buf (PbCut sh (ps ++ [(POD_PROP_PARAMS, PStruct es)]) None))) <= POD_BUF_MAX)
    by (rewrite (pc_buf_close_len sh ps es Hsh); exact Hb).
  assert (Hs : Forall (fun e => (length (e_body e) <= 96)%nat) es).
  { eapply Forall_impl; [|exact He]. intros x (_ & Hx & Hz). lia. }
  rewrite E0, H0, P0.
  change (le32 1) with (le32 (Z.b2z true)).
  rewrite pp_image_has_params by first [exact HB | exact Hl | exact Hs].
  rewrite pp_image_params_struct by first [exact HB | exact Hl | exact Hs].
  unfold pc_image. cbn [pc_shape pc_props pc_open]. rewrite H1, P1, E1. reflexivity.
Qed.

Lemma close_image_other : forall sh ps es v, sh <> 7 -> first_params ps = Some v ->
  overwrite (pc_image (PbCut sh ps (Some es))) (length (pc_buf (PbCut sh ps None)) + 8)
    (le32 (Z.of_nat (length (pc_buf (PbCut sh ps (Some es)))) - Z.of_nat (length (pc_buf (PbCut sh ps None))) - 16))
  = pc_image (PbCut sh (ps ++ [(POD_PROP_PARAMS, PStruct es)]) None).
Proof.
  intros sh ps es v Hsh HS. rewrite (close_image_patch sh ps es Hsh).
  unfold pc_image, has_params, params_struct, pc_ents. cbn [pc_shape pc_props pc_open p_props].
  rewrite first_params_app, HS. reflexivity.
Qed.


(** ** The block stores of a walk *)
(** The store at the goal's memory, pp + o: MB (the block's image) becomes its overwrite, and FK, a frame_only fact
    (KP), is kept; the new memory is generalized. *)
Ltac blk_store HOK MB FK KP pp o :=
  lazymatch goal with
  | |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?mm ?w ?bs) _) =>
      let E := fresh "Ew" in
      assert (E : w = wa (pp + o)) by (unfold wa; first [reflexivity | f_equal; lia]);
      let MB' := fresh "MBn" in let FK' := fresh "FKn" in
      pose proof (MBr_pp_store_w _ _ _ _ _ _ HOK _ mm w o bs MB E ltac:(lia)
                    ltac:(rewrite ?length_le1, ?length_le4, ?length_le8; cbn [length]; unfold POD_PROPS; lia))
        as MB';
      pose proof (frame_only_write _ _ mm w (pp + o) bs KP FK E ltac:(lia)
                    ltac:(rewrite ?length_le1, ?length_le4, ?length_le8; cbn [length]; lia)) as FK';
      clear MB FK E; rename MB' into MB; rename FK' into FK;
      let m' := fresh "m" in
      remember (write_to_mem mm w bs) as m' eqn:Hm; clear Hm
  end.

(** One store into the block at pp + o (n bytes): its store_ok, the step, then [blk_store]. *)
Ltac blk_step HOK MB FK KP pp o n :=
  lazymatch goal with
  | |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      let HS := fresh "HS" in
      assert (HS : store_ok rsegs mm (wa (pp + o)) n = true)
        by (eapply MBr_pp_ok; [exact MB | lia | unfold POD_PROPS; lia]);
      zstep; clear HS; blk_store HOK MB FK KP pp o
  end.

Ltac len1 := first [apply length_le1 | apply length_le4 | reflexivity].

Theorem close_holds : forall sp gp tp F fc m rest fl src pp lo H, S_close sp gp tp F fc m rest fl src pp lo H.
Proof.
  intros sp gp tp F fc m rest fl src pp lo Hd HOK sh np ps i es r ms
    (ra & t0 & t2 & a1 & a2 & a3 & a6 & s3 & s10 & t3 & t4 & t5 & t6 & m1 & -> &
     MB & CF & CPR & CE0 & CP & Hes32).
  pose proof HOK as (HS0 & HS1 & HP1 & _ & HM1 & HL0 & HSP & HPP & _ & _).
  unfold POD_PROPS, MID_STACK, FRAME_LOCALS in HP1, HM1, HSP.
  pose proof CP as (Hsuf & Hwf & Hsh & Hnp & Hi & Hinp & Hes).
  assert (Hps2 : (length ps <= 2)%nat) by lia.
  destruct (close_lengths sh ps es Hwf Hes Hps2 Hes32) as (HB & HBo & HFl).
  assert (FK : FCL sp pp fl Hd sh np (first_of ps) m1) by (split; [exact CF | split; assumption]).
  pose proof (FCL_frame sp pp fl Hd sh np (first_of ps)) as KP.
  clear CF CPR CE0.
  pose proof (MBr_bounds sp m rest src pp lo _ m1 MB) as (_ & _ & HIL). unfold POD_PROPS in HIL.
  unfold at_of, PROP_CLOSE, POD_LEN_OFF.
  (* 0x14080 lui a1,4; 0x14084 addiw a1,a1,1 *)
  zstep. zstep.
  (* 0x14088 bgeu a5,a1: at >= 0x4001 traps *)
  zstep. if_cases T0; [exfalso; zify_cond T0; lia|].
  (* 0x1408c bltu s6,a5: ~pp <u at traps *)
  zstep. if_cases T1; [exfalso; rewrite lnot_ltu_false in T1 by lia; discriminate T1|].
  (* 0x14090 subw a0,a0,a5; 0x14094 addi a0,a0,-8 *)
  zstep. rewrite swrap32_small by lia. zstep.
  (* 0x14098 srli a1,a0,24; 0x1409c srli a2,a0,16; 0x140a0 srli a3,a0,8 *)
  zstep. zstep. zstep.
  (* 0x140a4-0x140b0: the size word's four bytes at a4 = pp + at *)
  blk_step HOK MB FK KP pp (Z.of_nat (length (pc_buf (PbCut sh ps None))) + 8) 1%nat.
  blk_step HOK MB FK KP pp (Z.of_nat (length (pc_buf (PbCut sh ps None))) + 8 + 1) 1%nat.
  blk_step HOK MB FK KP pp (Z.of_nat (length (pc_buf (PbCut sh ps None))) + 8 + 2) 1%nat.
  blk_step HOK MB FK KP pp (Z.of_nat (length (pc_buf (PbCut sh ps None))) + 8 + 3) 1%nat.
  (* 0x140b4 ld a0,0xe0(sp); 0x140b8 beqz a0 -> 0x140c8 *)
  destruct (first_of ps) eqn:EF.
  - (* the first params Struct: has_params and params_struct (pod.h:436-437) *)
    assert (HN : first_params ps = None)
      by (apply first_params_none; unfold first_of in EF; apply negb_true_iff in EF; exact EF).
    pose proof FK as (_ & _ & CE0). change (Z.b2z true) with 1 in CE0.
    pose proof (cell8_read _ _ _ CE0) as RE0. clear CE0.
    zstep. clear RE0.
    zstep. if_cases T2; [exfalso; zify_cond T2; lia|].
    (* 0x140bc addi a0,zero,1; 0x140c0 sw a0,0xc(s11); 0x140c4 sw a0,0x10(s11) *)
    zstep.
    blk_step HOK MB FK KP pp 16396 4%nat.
    blk_step HOK MB FK KP pp 16400 4%nat.
    pose proof FK as (CF & CPR & _).
    (* 0x140c8 *)
    apply evt_done. unfold PROPL. do 17 eexists.
    split; [rewrite seen_close; reflexivity|].
    split.
    { eapply MBr_ext; [exact MB|].
      apply close_image_first; [exact Hsh | exact HN | unfold POD_BUF_MAX; lia | exact Hes32 | exact Hes | |
                                first [reflexivity | apply le4_le32] | first [reflexivity | apply le4_le32]].
      rewrite overwrite_4x1 by first [len1 | lia].
      f_equal; [lia | apply le1x4_le32; first [reflexivity | f_equal; lia | lia]]. }
    split; [exact CF|]. split; [exact CPR|]. split; [exact Hsuf|].
    split; [apply pc_wf_close; assumption|]. split; [exact Hnp|].
    rewrite length_app. cbn [length]. split; lia.
  - (* a later params Struct: the Struct's size word only *)
    assert (HSn : seen_of ps = true)
      by (unfold first_of in EF; apply negb_false_iff in EF; exact EF).
    destruct (first_params_some ps HSn) as (v & HV).
    pose proof FK as (CF & CPR & CE0). change (Z.b2z false) with 0 in CE0.
    pose proof (cell8_read _ _ _ CE0) as RE0. clear CE0.
    zstep. clear RE0.
    zstep. if_cases T2; [|exfalso; zify_cond T2; lia].
    (* 0x140c8 *)
    apply evt_done. unfold PROPL. do 17 eexists.
    split; [rewrite seen_close; reflexivity|].
    split.
    { eapply MBr_ext; [exact MB|].
      rewrite <- (close_image_other sh ps es v Hsh HV).
      rewrite overwrite_4x1 by first [len1 | lia].
      f_equal; [lia | apply le1x4_le32; first [reflexivity | f_equal; lia | lia]]. }
    split; [exact CF|]. split; [exact CPR|]. split; [exact Hsuf|].
    split; [apply pc_wf_close; assumption|]. split; [exact Hnp|].
    rewrite length_app. cbn [length]. split; lia.
Qed.
