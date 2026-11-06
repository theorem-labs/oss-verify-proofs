(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_role/lib/A/RPgPropKit.v at a529a88a618 (the plumbing of
   the property loop's block lemmas: pa_chunk8, pa_keep, pa_kwr_ro, pa_run, pa_runb, pa_branch, pa_reg, pa_leaf),
   proofs/reac-pw/fuzz_role/lib/A/RPgCfgChanges.v at a529a88a618 (kept_run) and proofs/reac-pw/fuzz_role/lib/A/RPgProp.v
   at a529a88a618 (its section g and its tactics: the (location, value) facts of a cut, the journal-and-frame step,
   the segment's write set, the first block's bounds and pod_put, the model of a shape-7 property, the start facts
   and the input at a cut) for reac-pw/fuzz_headamp's image B: rs_ / rl_ / rm_ -> hsu_ / hd_ / hm_, role's image A
   record and code -> fuzz_headamp.asan-ubsan's (lib/AU/Img0U.v rsegs, HPgImgB.headamp_himg_B: class-4 frame of
   1024 bytes, real frame of 0x220 bytes, write set [F+0x20, F+0x278) / 116 shadow bytes / [R, R+0x198)), the block
   post HPgSteps.hdu_blk_postE in place of pa_post, one table over the four pieces of image B. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_headamp/lib/AU/HPgPropKit.v; 352 of its 424 lines of code are new or changed and 339 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_role/lib/Prog/RoleBuild/Post.v at f3cc5e1ef75 (its image-
   independent lemmas: the corruption step once its test is decided, the record the piece ends with, the block's
   image under the piece's writes) and lib/Prog/RoleBuild/Facts.v lines 25-92 at the same commit (overwrite_adj),
   restated over lib/Pod's Model / Layout for the ASan walk; the plain image's machine-state predicates are left out. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_role/lib/A/RPgPostK.v at 01f4363fe7d2, for reac-pw/fuzz_headamp
   image A: module paths, the rs_ / rl_ / rm_ prefixes renamed to hs_ / hd_ / hm_; the code table at headamp's pcs (the
   piece 0x82c68 .. 0x82e60 and its slow-test blocks; the four shadow checks of pp->len have the `beqz; j` form, whose
   error blocks the engine does not read); hd_seg_pre's conjunct order (pp's block from hd_fresh_block, R 32-aligned);
   the class-4 frame for locals (1024 bytes, 80 shadow bytes P0); the real frame of 0x1e0 bytes; C2's value list, where
   s4 = pp (0x82e54); RPgCfgChanges.kept_run's three lines inlined in w10_frame_kept. *)
(* reac-pw/fuzz_headamp image A (fuzz_headamp.asan, pinned sha256
   f3e0669d2819724922df0556b11c2dcd22d1e16fe7e0fe1535ce784b34436c47; addresses measured on the unstripped twin
   b5f352154c54a97c66fd92dfa228e8a854498f6cd313dba0107900546b043f9a): the kit of the post piece of the walk of
   LLVMFuzzerTestOneInput (0x80bc0), lib/A/HPgSeg.v's hs_piece_W10_post / _corr / _req (cuts P 0x82c68, P1 0x82c6c,
   R 0x82da4, RT 0x82e2c, C2 0x82e60). Proves no function (kind: segment lemma).
   1. The code table the engine reads: the piece 0x82c68 .. 0x82e60 and the out-of-line blocks its instrumented
      checks branch to (0x83850 .. 0x83870, 0x838b0 .. 0x838bc, 0x839d0 .. 0x83a40: each check's second test
      `andi; [addi]; blt back` or its error path, which the proof shows is not reached). The shadow checks of
      pp->len (0x82c70, 0x82d04, 0x82da8, 0x82e48) are `beqz a0,+8; j error`: the engine reads only the `j`.
   2. The model: the corruption step (pod.h:441-448) once its tests are decided, the record's image under the
      piece's three writes (the top size word, one corruption byte, corrupt = 1), the bounds of a record the
      property loop can build.
   3. The run's context read off a cut: the first block (16-aligned, below the allocator ceiling, made since the
      segment's start so writable under the journal), the real frame, and what a cut's journal clauses become after
      an engine run whose writes all lie in the first block. *)
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d YG0q.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YI16 YM05.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Pod Require Import Cursor Model Layout.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.A Require Import Img0 HPgBase HPgCSpec HPgImgA HPgMem HPgSeg HPgSiteA.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.A Require Import HPgW7bBase.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

(* the fields of HPgSeg's segment record take the segments implicitly in this walk's files *)
Local Arguments x_STK {segs} _.
Local Arguments x_sp0 {segs} _.
Local Arguments x_FP {segs} _.
Local Arguments x_ly {segs} _.
Local Arguments x_S {segs} _.
Local Arguments x_W0 {segs} _.
Local Arguments x_mem0 {segs} _.
Local Arguments x_md0 {segs} _.
Local Arguments x_own {segs} _.
Local Arguments x_k {segs} _.
Local Arguments x_regs {segs} _.
Local Arguments x_lyc {segs} _.
Local Arguments x_Sc {segs} _.
Local Arguments x_W {segs} _.
Local Arguments x_memc {segs} _.
Local Arguments x_mdc {segs} _.
Local Arguments x_RLO {segs} _.
Local Arguments x_RHI {segs} _.
Local Arguments x_e {segs} _.
Local Arguments x_pos {segs} _.


(* ======================================== 1. the code table ======================================== *)
Definition W10_A : Z := 0x82c68.
Definition w10_tbl : ctable :=
  build_table rsegs W10_A 127 (build_table rsegs 0x83850 9 (build_table rsegs 0x838b0 4
  (build_table rsegs 0x839d0 29 TEmpty))).
Lemma w10_tbl_ok : table_ok rsegs w10_tbl.
Proof.
unfold w10_tbl. apply build_table_ok; [unfold W10_A; lia|]. apply build_table_ok; [lia|]. apply build_table_ok; [lia|].
apply build_table_ok0. lia.
Qed.
(* the shadow base of the engine's shadow tokens: s7 holds K (the runtime's shadow offset), atom 23 *)
Definition W10Bx : sv := SOff 23 0.
Definition W10Bspan : Z * Z := (SHADOW_OFF, SHADOW_OFF + 2 ^ 44 - 1).
(* the highest address an atom for a byte of the first block or of the input may take: below 2^47, so that its
   shadow byte (a >> 3) + K lies inside W10Bspan *)
Definition W10_HI : Z := 2 ^ 47 - 16.

(* ---- denotations of the symbolic values the piece's states use ---- *)
Lemma w10_den_atom : forall E n v, ew E n = Z_to_bv 64 v -> sv_denot E (SOff n 0) = Z_to_bv 64 v.
Proof. intros E n v H. cbn [sv_denot]. rewrite H, Z.add_0_r. apply Z_to_bv_bv_unsigned. Qed.
Lemma w10_den_off : forall E n v c, ew E n = Z_to_bv 64 v -> sv_denot E (SOff n c) = Z_to_bv 64 (v + c).
Proof.
intros E n v c H. cbn [sv_denot]. rewrite H. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap.
rewrite Z.add_mod_idemp_l by (unfold bv_modulus; lia). reflexivity.
Qed.
(* the shadow address of an atom's value: `srli t,x,3; add t,t,s7` *)
Lemma w10_den_sh : forall E nx nb v, ew E nx = Z_to_bv 64 v -> 0 <= v < 2 ^ 47 -> ew E nb = Z_to_bv 64 SHADOW_OFF ->
  sv_denot E (SAlu ALU_ADD (SAlu ALU_SRL (SOff nx 0) (SLit 3)) (SOff nb 0)) = Z_to_bv 64 (shadow_addr v).
Proof.
intros E nx nb v Hx Hv Hb. rewrite denot_lit_U. f_equal.
rewrite !U_SAlu, U_SLit, (U_atom E nx v Hx ltac:(lia)), (U_atom E nb SHADOW_OFF Hb ltac:(unfold SHADOW_OFF; lia)).
cbn [zalu_raw]. change (Z.land (zcanon 3) 63) with 3. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8.
assert (0 <= v / 8 < 2 ^ 44) by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
unfold shadow_addr, SHADOW_OFF. rewrite (zcanon_id (v / 8)) by (unfold M64; lia). rewrite zcanon_id by (unfold M64; lia). lia.
Qed.
(* a register outside a clobber list, decided by computation *)
Lemma w10_notin : forall (r : bv 5) (clob : list (bv 5)), existsb (fun c => bv_eqb c r) clob = false -> ~ In r clob.
Proof.
intros r clob H Hin. assert (Hx : existsb (fun c => bv_eqb c r) clob = true).
{ apply existsb_exists. exists r. split; [exact Hin | apply bv_eqb_refl]. }
congruence.
Qed.
(* the symbolic value of a register in a state, read off by computation *)
Ltac w10_sr_eval :=
  repeat lazymatch goal with |- context [sr_get ?l ?r] =>
    let v := eval vm_compute in (sr_get l r) in change (sr_get l r) with v end.
Lemma w10_U_atom : forall E n v, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> U E (SOff n 0) = v.
Proof. exact U_atom. Qed.

(* ======================================== 2. the model ======================================== *)
Lemma w10_byte_self : forall b : byte, Z_to_bv 8 (bv_unsigned b) = b.
Proof. intros b. apply bv_eq. rewrite Z_to_bv_unsigned. apply bv_wrap_small. apply bv_unsigned_in_range. Qed.

Lemma w10_overwrite_nil : forall (l : list byte) o, overwrite l o [] = l.
Proof. intros l o. unfold overwrite. cbn [app length]. rewrite Nat.add_0_r. apply firstn_skipn. Qed.

Lemma w10_list_split4 : forall (l : list byte) o nx ny, (o + nx + ny <= length l)%nat ->
  l = firstn o l ++ firstn nx (skipn o l) ++ firstn ny (skipn (o + nx) l) ++ skipn (o + nx + ny) l.
Proof.
  intros l o nx ny H.
  transitivity (firstn o l ++ skipn o l); [symmetry; apply firstn_skipn|]. f_equal.
  transitivity (firstn nx (skipn o l) ++ skipn nx (skipn o l)); [symmetry; apply firstn_skipn|]. f_equal.
  rewrite skipn_skipn. replace (nx + o)%nat with (o + nx)%nat by lia.
  transitivity (firstn ny (skipn (o + nx) l) ++ skipn ny (skipn (o + nx) l));
    [symmetry; apply firstn_skipn|]. f_equal.
  rewrite skipn_skipn. f_equal. lia.
Qed.

Lemma w10_overwrite_adj : forall (l x y : list byte) o,
  (o + length x + length y <= length l)%nat ->
  overwrite (overwrite l o x) (o + length x)%nat y = overwrite l o (x ++ y).
Proof.
  intros l x y o H.
  set (A := firstn o l). set (X := firstn (length x) (skipn o l)).
  set (Y := firstn (length y) (skipn (o + length x) l)). set (C := skipn (o + length x + length y) l).
  assert (LA : length A = o) by (subst A; rewrite length_firstn; lia).
  assert (LX : length x = length X) by (subst X; rewrite length_firstn, length_skipn; lia).
  assert (LY : length y = length Y) by (subst Y; rewrite length_firstn, length_skipn; lia).
  assert (El : l = A ++ X ++ Y ++ C) by (subst A X Y C; apply w10_list_split4; exact H).
  clearbody A X Y C. rewrite El, <- LA.
  rewrite (overwrite_mid A X (Y ++ C) x ltac:(lia)).
  replace (A ++ x ++ Y ++ C) with ((A ++ x) ++ Y ++ C) by (rewrite <- app_assoc; reflexivity).
  replace (length A + length x)%nat with (length (A ++ x)) by (rewrite length_app; lia).
  rewrite (overwrite_mid (A ++ x) Y C y ltac:(lia)).
  replace (A ++ X ++ Y ++ C) with (A ++ (X ++ Y) ++ C) by (rewrite <- app_assoc; reflexivity).
  rewrite (overwrite_mid A (X ++ Y) C (x ++ y) ltac:(rewrite !length_app; lia)).
  rewrite <- !app_assoc. reflexivity.
Qed.

(* ---- the corruption step, once its test has been decided ---- *)
Lemma w10_corr_none_nil : forall len, fst (corr_step len []) = None.
Proof.
  intros len. unfold corr_step. cbn [fuzz_u8].
  replace ((0 mod 16 =? 15) && (8 <? len)) with false by reflexivity. reflexivity.
Qed.

Lemma w10_corr_none : forall len (c : byte) (r1 : list byte), bv_unsigned c mod 16 <> 15 \/ len <= 8 ->
  fst (corr_step len (c :: r1)) = None.
Proof.
  intros len c r1 H. unfold corr_step. cbn [fuzz_u8].
  replace ((bv_unsigned c mod 16 =? 15) && (8 <? len)) with false; [reflexivity|].
  symmetry. apply andb_false_iff. destruct H as [H|H]; [left; apply Z.eqb_neq; exact H | right; apply Z.ltb_ge; lia].
Qed.

Lemma w10_corr_some : forall len (c : byte) (r1 : list byte), bv_unsigned c mod 16 = 15 -> 8 < len ->
  fst (corr_step len (c :: r1)) =
  Some (8 + fst (fuzz_u16 r1) mod (len - 8),
        fst (fuzz_u8s (Z.to_nat (Z.min (fst (fuzz_u8 (skipn 2 r1)) mod 8)
                                       (len - (8 + fst (fuzz_u16 r1) mod (len - 8))))) (skipn 1 (skipn 2 r1)))).
Proof.
  intros len c r1 Hc Hl. unfold corr_step. cbn [fuzz_u8].
  rewrite Hc. replace ((15 =? 15) && (8 <? len)) with true
    by (symmetry; apply andb_true_intro; split; [reflexivity | apply Z.ltb_lt; lia]).
  cbv iota beta.
  rewrite (surjective_pairing (fuzz_u16 r1)). cbv iota beta. rewrite fuzz_u16_rest.
  rewrite (surjective_pairing (fuzz_u8 (skipn 2 r1))). cbv iota beta. rewrite (fuzz_u8_spec (skipn 2 r1)).
  cbn [snd]. cbv zeta.
  rewrite (surjective_pairing (fuzz_u8s _ _)). cbv iota beta. reflexivity.
Qed.

Lemma w10_corr_empty_tail : forall (r1 : list byte), (length r1 <= 2)%nat -> fst (fuzz_u8 (skipn 2 r1)) = 0.
Proof. intros r1 H. rewrite skipn_all2 by lia. reflexivity. Qed.

Lemma w10_fuzz_u8s_cons : forall n (x : byte) (l : list byte),
  fst (fuzz_u8s (S n) (x :: l)) = x :: fst (fuzz_u8s n l).
Proof.
  intros n x l. cbn [fuzz_u8s fuzz_u8]. destruct (fuzz_u8s n l) as [bs r]. cbn [fst].
  f_equal. apply w10_byte_self.
Qed.

Lemma w10_fuzz_u8s_nil : forall n, fst (fuzz_u8s (S n) []) = Z_to_bv 8 0 :: fst (fuzz_u8s n []).
Proof. intros n. cbn [fuzz_u8s fuzz_u8]. destruct (fuzz_u8s n []) as [bs r]. reflexivity. Qed.

Lemma w10_length_fuzz_u8s : forall n l, length (fst (fuzz_u8s n l)) = n.
Proof.
  induction n as [|n IH]; intros l; [reflexivity|]. cbn [fuzz_u8s].
  destruct (fuzz_u8 l) as [b r]. specialize (IH r). destruct (fuzz_u8s n r) as [bs r']. cbn [fst length] in *. lia.
Qed.

(* ---- the record the piece ends with ---- *)
Lemma w10_pod_encode_co : forall sh ps co, pod_encode (PodRec sh ps co) = pod_encode (PodRec sh ps None).
Proof. intros sh ps co. reflexivity. Qed.

(* What a record the property loop can build gives about the object's bytes. *)
Lemma w10_wf_facts : forall sh ps, hs_wf sh ps ->
  8 <= Z.of_nat (length (pc_buf (PbCut sh ps None))) <= 5440 /\
  length (pod_encode (PodRec sh ps None)) = length (pc_buf (PbCut sh ps None)) /\
  (length (ents (PodRec sh ps None)) <= 32)%nat /\
  Forall (fun e => (length (e_body e) <= 96)%nat) (ents (PodRec sh ps None)) /\
  (8 | Z.of_nat (length (pc_buf (PbCut sh ps None)))).
Proof.
  intros sh ps (Hs & Hk & He & Hl).
  assert (Hv : Forall (fun kv => pval_wf (snd kv)) ps)
    by (eapply Forall_impl; [|exact Hk]; intros kv (_ & H); exact H).
  destruct (pc_buf_len_none sh ps Hv He) as (HB & HD).
  assert (H4 : (4 <= length (pc_buf (PbCut sh ps None)))%nat).
  { unfold pc_buf. cbn [pc_shape pc_props pc_open]. rewrite length_app, length_le32. lia. }
  assert (HPE : length (pod_encode (PodRec sh ps None)) = length (pc_buf (PbCut sh ps None))).
  { rewrite <- (pc_buf_top sh ps). apply length_overwrite. rewrite length_le32. lia. }
  destruct (pod_encode_len sh ps None Hv He Hl) as (P1 & P2 & P3).
  assert (HR : pod_rec_wf (PodRec sh ps None)).
  { unfold pod_rec_wf. cbn [p_shape p_props p_corr].
    split; [exact Hs|]. split; [exact Hk|]. split; [exact He|]. split; [exact Hl|].
    split; [lia | exact I]. }
  destruct (ents_wf (PodRec sh ps None) HR) as (HE1 & HE2).
  split; [rewrite <- HPE; lia|]. split; [exact HPE|]. split; [exact HE1|]. split; [|exact HD].
  eapply Forall_impl; [|exact HE2]. intros e (_ & Hb & Hsz). lia.
Qed.

(* The top size word (pod.h:440): the object as pod_encode writes it. *)
Lemma w10_img_top : forall sh ps, hs_wf sh ps ->
  overwrite (pc_image (PbCut sh ps None)) 0%nat (le32 (Z.of_nat (length (pc_buf (PbCut sh ps None))) - 8))
  = pp_image (pod_encode (PodRec sh ps None)) (is_props (PodRec sh ps None))
      (has_params (PodRec sh ps None)) (params_struct (PodRec sh ps None))
      (ents (PodRec sh ps None)) false.
Proof.
  intros sh ps Hwf. destruct (w10_wf_facts sh ps Hwf) as (HL1 & HL2 & _ & _).
  unfold pc_image. cbn [pc_shape pc_props]. rewrite (pc_ents_final sh ps None).
  rewrite <- pp_image_patch by (rewrite length_le32; lia).
  f_equal. apply pc_buf_top.
Qed.

(* One byte of the corruption (pod.h:446). *)
Lemma w10_img_step : forall sh ps (off : Z) (bsk : list byte) (x : byte),
  0 <= off -> (Z.to_nat off + length bsk + 1 <= length (pod_encode (PodRec sh ps None)))%nat ->
  overwrite (pp_image (overwrite (pod_encode (PodRec sh ps None)) (Z.to_nat off) bsk)
               (is_props (PodRec sh ps None)) (has_params (PodRec sh ps None))
               (params_struct (PodRec sh ps None)) (ents (PodRec sh ps None)) false)
            (Z.to_nat off + length bsk)%nat [x]
  = pp_image (overwrite (pod_encode (PodRec sh ps None)) (Z.to_nat off) (bsk ++ [x]))
      (is_props (PodRec sh ps None)) (has_params (PodRec sh ps None))
      (params_struct (PodRec sh ps None)) (ents (PodRec sh ps None)) false.
Proof.
  intros sh ps off bsk x Ho Hl.
  rewrite <- pp_image_patch by (rewrite length_overwrite by lia; cbn [length]; lia).
  f_equal. apply w10_overwrite_adj. cbn [length]. lia.
Qed.

(* corrupt = 1 (pod.h:447): the record's own image. *)
Lemma w10_img_corrupt : forall sh ps off bs, hs_wf sh ps -> 0 <= off ->
  (Z.to_nat off + length bs <= length (pod_encode (PodRec sh ps None)))%nat ->
  overwrite (pp_image (overwrite (pod_encode (PodRec sh ps None)) (Z.to_nat off) bs)
               (is_props (PodRec sh ps None)) (has_params (PodRec sh ps None))
               (params_struct (PodRec sh ps None)) (ents (PodRec sh ps None)) false)
            (Z.to_nat OFF_CORRUPT) (le32 1)
  = pp_bytes (PodRec sh ps (Some (off, bs))).
Proof.
  intros sh ps off bs Hwf Ho Hl. destruct (w10_wf_facts sh ps Hwf) as (HL1 & HL2 & HE1 & HE2 & _).
  replace (le32 1) with (le32 (Z.b2z true)) by reflexivity.
  rewrite (pp_image_corrupt (overwrite (pod_encode (PodRec sh ps None)) (Z.to_nat off) bs) _ _ _ _ false);
    [| rewrite length_overwrite by exact Hl; unfold POD_BUF_MAX; lia | exact HE1 | exact HE2].
  reflexivity.
Qed.

(* the no-corruption record's image is the image at RT's start with nothing written *)
Lemma w10_bytes_none : forall sh ps,
  pp_bytes (PodRec sh ps None)
  = pp_image (pod_encode (PodRec sh ps None)) (is_props (PodRec sh ps None))
      (has_params (PodRec sh ps None)) (params_struct (PodRec sh ps None)) (ents (PodRec sh ps None)) false.
Proof. intros sh ps. reflexivity. Qed.

(* the record pod_build makes, from the builder's end state (HPgSeg.hs_Pbody's ties) *)
Lemma w10_build_tie : forall rest sh np ps r,
  sh = hs_sh rest -> np = hs_np rest -> Z.of_nat (length ps) = np ->
  (ps, r) = props_loop sh (length ps) (hs_r0 rest) ->
  fst (pod_build rest) = PodRec sh ps (fst (corr_step (Z.of_nat (length (pod_encode (PodRec sh ps None)))) r)).
Proof.
intros rest sh np ps r Hsh Hnp Hl Hps. unfold hs_sh, hs_np, hs_r0 in *. unfold pod_build.
destruct (Cursor.fuzz_u8 rest) as [s r1]. cbn [fst snd] in *. destruct (Cursor.fuzz_u8 r1) as [n r2]. cbn [fst snd] in *.
assert (Hn : Z.to_nat (n mod 4) = length ps) by (rewrite <- Hnp, <- Hl; apply Nat2Z.id).
rewrite Hn, <- Hsh, <- Hps. cbv iota beta.
destruct (corr_step _ r) as [co r4]. reflexivity.
Qed.

(* the length of the object, as buf of either record *)
Lemma w10_buf_len : forall sh ps co, corr_wf (Z.of_nat (length (pod_encode (PodRec sh ps None)))) co ->
  length (buf (PodRec sh ps co)) = length (pod_encode (PodRec sh ps None)).
Proof.
  intros sh ps [[off bs]|] H; cbn [buf p_corr]; [|reflexivity].
  destruct H as (H1 & H2 & H3). rewrite w10_pod_encode_co. apply length_overwrite. lia.
Qed.

(* ======================================== 3. the run's context ======================================== *)
Section k. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Variable B : asyms.
Variable MT : ameter_ops.

(* What a run leaves of the bytes outside its write windows. *)
Lemma w10_frame_kept : forall E rs (H : word -> bool) m m',
  frame_of E rs (mrestrict H m) (mrestrict H m') ->
  forall a, 0 <= a < 2 ^ 64 -> ~ in_wrange E rs a -> aview rsegs H m' a = aview rsegs H m a.
Proof.
intros E rs H m m' HF a Ha Hn. unfold aview, mbyte.
rewrite (HF (Z_to_bv 64 a)); [reflexivity|]. rewrite unsigned_lit_small by exact Ha. exact Hn.
Qed.

(* The first block, the real frame and the stack window at a cut of the build segment. *)
Lemma w10_ctx : forall cx ly2 S2 W2 regs2 mem2 md2,
  hs_pre rsegs B cx (hi_shA headamp_himg_A) -> hs_core rsegs B MT cx (hs_E1 rsegs cx) ly2 S2 W2 regs2 mem2 md2 ->
  In (e_pp (x_e cx), PP_SIZE) (ablocks B ly2 S2) /\
  ~ In (e_pp (x_e cx), PP_SIZE) (ablocks B (x_ly cx) (x_S cx)) /\
  e_pp (x_e cx) mod 16 = 0 /\ 4096 <= e_pp (x_e cx) /\ e_pp (x_e cx) + 19744 <= alloc_ceiling /\
  in_app (e_pp (x_e cx)) 19744 /\
  (forall a, e_pp (x_e cx) <= a < e_pp (x_e cx) + 19744 -> apresent (w_H W2) mem2 a) /\
  getr regs2 (Z_to_bv 5 2) = w64 (e_R (x_e cx)) /\ e_R (x_e cx) mod 16 = 0 /\ e_R (x_e cx) + 0x1e0 <= x_sp0 cx /\
  x_sp0 cx - x_STK cx <= e_R (x_e cx) - T_SEG_STK /\ alloc_ceiling <= x_sp0 cx - x_STK cx /\ x_sp0 cx <= 2 ^ 47 /\
  AR rsegs B ly2 S2 W2 mem2 md2.
Proof.
intros cx ly2 S2 W2 regs2 mem2 md2 HP HC.
destruct HP as (HJ0 & Hev & H2 & Hgp & Htp & HS & HR32 & HRS & HSTK & Hown & HF & Hfsh & Hcap & Hnull & Hro & Hgl
  & Hrz & Hstr & Hcl & Hgd & Hrom & (Hpp0 & Hpp & Hfresh)).
destruct HC as (HJ & Hr234 & Hfr & Hperm & Hio & Hmo & Hkeep).
pose proof (AR_laws_ok rsegs B) as LAWS.
assert (Hin : In (e_pp (x_e cx), PP_SIZE) (ablocks B ly2 S2))
  by (eapply Permutation_in; [apply Permutation_sym; exact Hperm | exact Hpp]).
destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ (proj1 HJ) Hin) as (Hal & Hlo & Hhi & Happ & Hpres & _).
change (req_size PP_SIZE) with 19744 in *.
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstk & _).
destruct Hstk as (Hsp0al & Hstk0 & Hceil & Hslo & Hshi & H47 & _).
cbn [hi_rsz headamp_himg_A] in HRS.
assert (HR16 : e_R (x_e cx) mod 16 = 0).
{ apply Z.mod_divide in HR32; [|lia]. destruct HR32 as [q Hq]. apply Z.mod_divide; [lia|]. exists (2 * q). lia. }
rewrite (Hr234 2 (or_introl eq_refl)).
split; [exact Hin|]. split; [exact Hfresh|]. split; [exact Hal|]. split; [exact Hlo|]. split; [exact Hhi|].
split; [exact Happ|]. split; [intros a Ha; apply (Hpres a Ha)|]. split; [exact H2|].
split; [exact HR16|]. split; [lia|]. split; [exact HSTK|]. split; [lia|]. split; [lia|]. exact (proj1 HJ).
Qed.

(* A cut's journal clauses after an engine run inside the segment whose writes all lie in the segment's write set. *)
Lemma w10_core_run : forall cx ly2 S2 W2 regs2 mem2 md2 regs3 mem3 md3 (Wr : Z -> Prop),
  hs_core rsegs B MT cx (hs_E1 rsegs cx) ly2 S2 W2 regs2 mem2 md2 ->
  ajournal rsegs B (x_STK cx) (x_sp0 cx) (x_FP cx) (x_ly cx) (x_S cx) (x_W0 cx) (x_mem0 cx) (x_md0 cx) (x_own cx)
    ly2 S2 W2 mem3 md3 (x_k cx) ->
  (forall r : Z, r = 2 \/ r = 3 \/ r = 4 -> getr regs3 (Z_to_bv 5 r) = getr regs2 (Z_to_bv 5 r)) ->
  same_io md2 md3 ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ Wr a -> aview rsegs (w_H W2) mem3 a = aview rsegs (w_H W2) mem2 a) ->
  (forall a, Wr a -> hs_E1 rsegs cx a) ->
  hs_core rsegs B MT cx (hs_E1 rsegs cx) ly2 S2 W2 regs3 mem3 md3.
Proof.
intros cx ly2 S2 W2 regs2 mem2 md2 regs3 mem3 md3 Wr HC HJ3 H234 Hio3 HK HW.
destruct HC as (HJ & Hr234 & Hfr & Hperm & Hio & Hmo & Hkeep).
split; [exact HJ3|]. split; [intros r Hr; rewrite (H234 r Hr); exact (Hr234 r Hr)|].
split; [exact Hfr|]. split; [exact Hperm|]. split; [eapply same_io_trans; eassumption|]. split; [exact Hmo|].
intros a Ha Hs He. rewrite (HK a Ha (fun Hw => He (HW a Hw))). exact (Hkeep a Ha Hs He).
Qed.

(* the shadow obligation of an access inside the first block *)
Lemma w10_ob_blk : forall ly S (W : world rsegs) mem md E p m a n x,
  AR rsegs B ly S W mem md -> In (p, m) (ablocks B ly S) -> p <= a -> a + n <= p + req_size m ->
  U E W10Bx = SHADOW_OFF -> U E x = a ->
  range_addressable (rd_of rsegs (mrestrict (w_H W) mem)) (U E W10Bx) (U E x) n.
Proof.
intros ly S W mem md E p m a n x HAR Hin Hpa Han HB Hx. rewrite HB, Hx.
exact (proj1 (hm_blk_ra rsegs B ly S W mem md p m a n HAR Hin Hpa Han)).
Qed.

(* a shadow entry of the engine for a range inside a heap block (in the app band, so apart from the shadow span):
   the write windows of the first block are covered by such entries *)
Lemma w10_shent_blk : forall ly S (W : world rsegs) mem md E p m n lo hi,
  AR rsegs B ly S W mem md -> In (p, m) (ablocks B ly S) -> in_app p (req_size m) ->
  U E W10Bx = SHADOW_OFF -> p <= U E (SOff n 0) + lo -> U E (SOff n 0) + hi <= p + req_size m -> lo < hi ->
  shent_ok rsegs W10Bx E (mrestrict (w_H W) mem) (mkSHE n lo hi).
Proof.
intros ly S W mem md E p m n lo hi HAR Hin Happ HB H1 H2 H3. split; cbn [she_m she_lo she_hi].
- rewrite HB. exact (proj1 (hm_blk_ra rsegs B ly S W mem md p m (U E (SOff n 0) + lo) (hi - lo) HAR Hin H1 ltac:(lia))).
- unfold app_apart. cbn [she_m she_lo she_hi]. intros a Ha. rewrite HB. pose proof ASAN_CEIL_range as [CR _].
  rewrite Z.min_l, Z.max_r in Ha by lia.
  unfold in_app, kLowShadowBeg, kHighMemBeg, SHADOW_OFF in *. lia.
Qed.

(* the write right of a region inside the first block *)
Lemma w10_awr_cons_pp : forall E r rs STK sp0 FP bl0 blc ly own n b pp,
  r_base r = Some n -> bv_unsigned (ew E n) = b -> In (pp, PP_SIZE) blc -> ~ In (pp, PP_SIZE) bl0 ->
  pp <= b + r_wlo r -> b + r_whi r <= pp + PP_SIZE ->
  awr_ok E rs STK sp0 FP bl0 blc ly own -> awr_ok E (r :: rs) STK sp0 FP bl0 blc ly own.
Proof.
intros E r rs STK sp0 FP bl0 blc ly own n b pp Hb Hn Hin Hout Hlo Hhi H.
apply (w7_awr_cons E r rs STK sp0 FP bl0 blc ly own n b Hb Hn); [|exact H].
intros a Ha. replace a with (pp + (a - pp)) by lia.
apply (hd_fresh_awr STK sp0 FP bl0 blc ly own pp PP_SIZE (a - pp) Hin Hout).
change (req_size PP_SIZE) with 19744. unfold PP_SIZE in Hhi. lia.
Qed.

(* a register whose symbolic value the run left unchanged keeps its value *)
Lemma w10_reg_same : forall E E' K ss0 ss1 regs0 ms1 (H : word -> bool) (r : bv 5),
  regs_ok E (ss_regs ss0) regs0 -> st_ok rsegs E' ss1 (restrict H ms1) -> env_agree K E E' ->
  sv_eqb (sr_get (ss_regs ss1) r) (sr_get (ss_regs ss0) r) = true -> sv_atoms_lt K (sr_get (ss_regs ss0) r) = true ->
  getr (ms_regs ms1) r = getr regs0 r.
Proof.
intros E E' K ss0 ss1 regs0 ms1 H r H0 HS HA Heq Hat.
rewrite (st_ok_restrict_reg rsegs H E' ss1 ms1 r HS), (sv_eqb_eq _ _ Heq).
pose proof (sv_denot_agree K E E' _ HA Hat) as HD. first [rewrite <- HD | rewrite HD]. symmetry. apply H0.
Qed.

(* The first block's bytes, a cut's real-frame cells and the frame's shadow bytes are apart. *)
Lemma w10_cells_not_pp : forall (cx : hs_scx rsegs) o i,
  e_pp (x_e cx) + 19744 <= alloc_ceiling -> alloc_ceiling <= x_sp0 cx - x_STK cx ->
  x_sp0 cx - x_STK cx <= e_R (x_e cx) - T_SEG_STK -> 0 <= o -> 0 <= i ->
  ~ (e_pp (x_e cx) <= e_R (x_e cx) + o + i < e_pp (x_e cx) + PP_SIZE).
Proof. intros cx o i H1 H2 H3 H4 H5. unfold PP_SIZE, T_SEG_STK, ASTACK in *. lia. Qed.

Lemma w10_shadow_not_pp : forall pp F i,
  in_app pp 19744 -> in_app F 1024 -> 0 <= i < 128 -> ~ (pp <= shadow_addr F + i < pp + PP_SIZE).
Proof.
intros pp F i Hp HF Hi. pose proof ASAN_CEIL_range as [CR CR2].
destruct (shadow_addr_in_band F 1024 (8 * i) HF ltac:(lia)) as [B1|B1];
unfold in_band_rw, in_app, shadow_addr, kLowShadowBeg, kLowShadowEnd, kHighShadowBeg, kHighShadowEnd, kHighMemBeg,
  SHADOW_OFF, PP_SIZE in *;
replace ((F + 8 * i) / 8) with (F / 8 + i) in B1
  by (rewrite <- (Z.div_add F i 8) by lia; f_equal; lia);
lia.
Qed.

(* the frame for locals at the segment's start: class 4, 1024 bytes *)
Lemma w10_F_ctx : forall cx, hs_pre rsegs B cx (hi_shA headamp_himg_A) ->
  4096 <= e_F (x_e cx) /\ e_F (x_e cx) + 1024 <= alloc_ceiling /\ in_app (e_F (x_e cx)) 1024.
Proof.
intros cx HP.
destruct HP as (HJ0 & Hev & H2 & Hgp & Htp & HS & HR32 & HRS & HSTK & Hown & HF & _).
pose proof HJ0 as (HAR & _ & _ & _ & _ & Hfrs & _).
assert (Hin : In (4, x_pos cx) (frames (x_Sc cx))) by (rewrite Hfrs; apply in_or_app; left; exact Hown).
destruct (frames_bounds rsegs B (AR_laws_ok rsegs B) _ _ _ _ _ 4 (x_pos cx) HAR Hin) as (F1 & F2 & F3).
cbn [hi_cid headamp_himg_A] in HF. rewrite HF. change (fs_frame_bytes 4) with 1024 in *. auto.
Qed.

(* an 8-byte chunk from a cut's cell fact (HPgBase.hd_at: the value mod 2^64); fuzz_role's RPgPostTop w10t_ch8,
   here because the tail, the corruption loop and the arms all read R's cells *)
Lemma w10_ch8 : forall E m R off e v, sv_denot E e = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 ->
  val_mem rsegs m (R + off) 8 (v mod 2 ^ 64) -> YP09.chunk_ok rsegs E m R (YP09.mkChunk off (CVal 8 e)).
Proof.
intros E m R off e v He Hv V. rewrite Z.mod_small in V by lia.
apply (chunk_ok_val rsegs E m R off 8 e v He); [cbn; lia | cbn; lia | exact V].
Qed.

(* a register at the end of a run, through the agreement of the run's environment with the entry one; fuzz_role's
   RPgPostTop w10t_reg, here for the same reason *)
Lemma w10_reg : forall E0 E ss ms (H : word -> bool) (r : bv 5) k v w,
  st_ok rsegs E ss (restrict H ms) -> env_agree k E0 E -> sr_get (ss_regs ss) r = v -> sv_atoms_lt k v = true ->
  sv_denot E0 v = w -> getr (ms_regs ms) r = w.
Proof.
intros E0 E ss ms H r k v w HS HA Hv Hk Hw.
rewrite (st_ok_restrict_reg rsegs H E ss ms r HS), Hv, (sv_denot_agree k E0 E v HA Hk). exact Hw.
Qed.

(* The post cuts' value list without s4: what a cut after the piece's last write keeps of it. At P1 .. RT s4 holds
   the shadow address of &pp->len (HPgSeg hs_L_post); from 0x82e54 on it holds pp (C2's list). *)
Definition w10_Lc (cx : hs_scx rsegs) : list (hd_loc * Z) :=
let e := x_e cx in
[(LReg 8, e_S e); (LReg 9, e_R e); (LReg 19, shadow_addr (e_F e)); (LReg 23, SHADOW_OFF);
 (LReg 21, e_pp e + 0x4000); (LReg 26, e_F e); (LReg 18, e_pp e + 0x4d18);
 (LCell XR 0x20, e_F e); (LCell XR 0x28, e_cap e); (LCell XR 0x40, e_null e);
 (LCell XR 0x90, Z.shiftr (e_pp e + 0x4d14) 3); (LCell XR 0xa0, e_pp e + 0x4d14);
 (LCell XR 0x60, e_F e); (LCell XR 0xf0, e_pp e)].

Lemma w10_Lc_of_post : forall (cx : hs_scx rsegs) H mem regs,
  hs_at rsegs H mem regs (x_e cx) (hs_L_post rsegs cx) -> hs_at rsegs H mem regs (x_e cx) (w10_Lc cx).
Proof.
intros cx H mem regs Hp. unfold hs_at, hs_L_post in Hp. cbv zeta in Hp.
rewrite !Forall_cons_iff in Hp.
destruct Hp as (P8 & P9 & P19 & P23 & P21 & P26 & P20 & P18 & C20 & C28 & C40 & C90 & Ca0 & C60 & Cf0 & _).
unfold hs_at, w10_Lc. cbv zeta. repeat apply Forall_cons; [..|apply Forall_nil]; assumption.
Qed.

Lemma w10_post_of_Lc : forall (cx : hs_scx rsegs) H mem regs,
  hs_at rsegs H mem regs (x_e cx) (w10_Lc cx) ->
  getr regs (Z_to_bv 5 20) = w64 (shadow_addr (e_pp (x_e cx) + 0x4000)) ->
  hs_at rsegs H mem regs (x_e cx) (hs_L_post rsegs cx).
Proof.
intros cx H mem regs Hp H20. unfold hs_at, w10_Lc in Hp. cbv zeta in Hp.
rewrite !Forall_cons_iff in Hp.
destruct Hp as (P8 & P9 & P19 & P23 & P21 & P26 & P18 & C20 & C28 & C40 & C90 & Ca0 & C60 & Cf0 & _).
unfold hs_at, hs_L_post. cbv zeta. repeat apply Forall_cons; [..|apply Forall_nil]; assumption.
Qed.

(* C2's value list (HPgImgA.headamp_A_L23 XLenNZ) from w10_Lc, a0 = s8 = len and s4 = pp *)
Lemma w10_L2_of_Lc : forall (cx : hs_scx rsegs) H mem regs,
  hs_at rsegs H mem regs (x_e cx) (w10_Lc cx) ->
  getr regs (Z_to_bv 5 10) = w64 (e_len (x_e cx)) -> getr regs (Z_to_bv 5 24) = w64 (e_len (x_e cx)) ->
  getr regs (Z_to_bv 5 20) = w64 (e_pp (x_e cx)) ->
  0 < e_len (x_e cx) ->
  hd_cut rsegs H mem regs (x_e cx) (hi_L2 headamp_himg_A).
Proof.
intros cx H mem regs Hp H10 H24 H20 Hl. unfold hs_at, w10_Lc in Hp. cbv zeta in Hp.
unfold hd_cut. cbn [hi_L2 headamp_himg_A]. unfold headamp_A_L23.
rewrite !Forall_cons_iff in Hp.
destruct Hp as (P8 & P9 & P19 & P23 & P21 & P26 & P18 & C20 & C28 & C40 & C90 & Ca0 & C60 & Cf0 & _).
cbn [fst snd] in *.
repeat (apply Forall_cons; [cbn [fst snd hd_xv]|]); [..|apply Forall_nil]; try assumption;
try (rewrite Z.add_0_r; assumption).
cbn [hd_at]. rewrite (proj2 (Z.eqb_neq _ _)) by lia. rewrite Z.add_0_r. exact H10.
Qed.
End k.
