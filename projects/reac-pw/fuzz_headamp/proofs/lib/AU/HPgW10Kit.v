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
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_headamp/lib/AU/HPgPropKit.v; 486 of its 561 lines of code are new or changed and 336 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_role/lib/Prog/RoleBuild/Post.v at f3cc5e1ef75 (its image-
   independent lemmas: the corruption step once its test is decided, the record the piece ends with, the block's
   image under the piece's writes) and lib/Prog/RoleBuild/Facts.v lines 25-92 at the same commit (overwrite_adj),
   restated over lib/Pod's Model / Layout for the ASan walk; the plain image's machine-state predicates are left out. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_role/lib/A/RPgPostK.v and lib/A/RPgW6cKit.v part 1 at
   01f4363fe7d, for image B of reac-pw/fuzz_headamp: the w10_ prefix renamed to hw10_, rs_ -> hsu_ (the cut states of
   lib/AU/HPgSeg.v), rm_ -> hm_, rl_ -> hd_, the code table and the shadow base moved to image B, the run's context
   read at image B's record (a class-4 frame of 1024 bytes, a real frame of 0x220 bytes, three write ranges), and
   the cells of the first block reached from one atom for its address. *)
(* reac-pw/fuzz_headamp image B (fuzz_headamp.asan-ubsan, pinned sha256
   53edda9bdeeba1803865babfecb1af6732babe47ab83c64d38cc59a90d717a94; every address measured on the unstripped twin
   1674e30a0698f381704e66d2398d7906c881f4ba8fc619cb41b89fb97ad112ff, same loaded bytes except .note.gnu.build-id): the kit of the image-B
   builder's last pieces in LLVMFuzzerTestOneInput (0x80c40), lib/AU/HPgSeg.v's hsu_piece_W10_post / _corr / _req
   (cuts P 0x82bec, P1 0x82bf0, R 0x82e2c, RT 0x82ec8, C2 0x82efc). Proves no function (kind: segment lemma).
   1. The code table the engine reads: the pieces 0x82bec .. 0x82efc, the two UBSan traps `unimp` 0x83a10 / 0x83a14,
      and the out-of-line blocks the instrumented checks branch to (each check's second test `andi; [addi]; blt
      back` 0x83a18 .. 0x83a38, 0x83a78, 0x83b24, 0x83ba4 .. 0x83be8, and the report entries 0x83da4 .. 0x83de0,
      0x83e74, which the engine decodes to tell a report from a second test; the proof shows no report is reached).
      The registers and real-frame cells the pieces read: s0 = S, s1 = R, s3 = (F >> 3) + K, s11 = K (the shadow
      base of every check, atom 27), and the cells R+0x28 (0), R+0x30 (pp), R+0xf0 (~pp), R+0x120 (pp + 0x4d14),
      R+0x138 (pp + 0x4000), R+0x148 (pp) and R+0x150 ((pp + 0x4000 >> 3) + K: the code reloads this shadow address
      before every 8-byte read of pp->len).
   2. The model: the corruption step (pod.h:441-448) once its tests are decided, the record's image under the
      pieces' three writes (the top size word, one corruption byte, corrupt = 1), the bounds of a record the
      property loop can build.
   3. The run's context read off a cut: the first block (16-aligned, below the allocator ceiling, made since the
      segment's start so writable under the journal), the real frame and the stack window, the frame for locals,
      the input bytes and their shadow bytes at the cut's memory, and what a cut's journal clauses become after an
      engine run whose writes all lie in the first block. *)
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
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Pod Require Spa.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.A Require Import HPgBase HPgCSpec.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.AU Require Import Img0U HPgImgB HPgMem HPgSeg.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.AU Require HPgSteps.
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

(* ======================================== 1. the code ======================================== *)
Definition HW10_P : Z := 0x82bec.
Definition HW10_P1 : Z := 0x82bf0.
Definition HW10_R : Z := 0x82e2c.
Definition HW10_RT : Z := 0x82ec8.
Definition HW10_TAIL : Z := 0x82ee0.     (* `ld a0,0x150(s1)`: the reload of pp->len's shadow address before C2 *)
Definition HW10_C2 : Z := 0x82efc.
Lemma hw10_pcs : bi_P headamp_bld_B = HW10_P /\ bi_P1 headamp_bld_B = HW10_P1 /\ bi_R headamp_bld_B = HW10_R /\
  bi_RT headamp_bld_B = HW10_RT /\ hi_c2 headamp_himg_B = HW10_C2.
Proof. repeat split. Qed.

Definition hw10_tbl : ctable :=
  build_table rsegs HW10_P 197 (build_table rsegs 0x83a10 11 (build_table rsegs 0x83a78 4
  (build_table rsegs 0x83b24 5 (build_table rsegs 0x83ba4 20 (build_table rsegs 0x83da4 16
  (build_table rsegs 0x83e74 2 TEmpty)))))).
Lemma hw10_tbl_ok : table_ok rsegs hw10_tbl.
Proof.
unfold hw10_tbl. apply build_table_ok; [unfold HW10_P; lia|]. apply build_table_ok; [lia|].
apply build_table_ok; [lia|]. apply build_table_ok; [lia|]. apply build_table_ok; [lia|].
apply build_table_ok; [lia|]. apply build_table_ok0. lia.
Qed.
Lemma hw10_wx : wx_segs_nowrap rsegs.
Proof. exact HPgSteps.img_wx. Qed.
Lemma hw10_segs_low : forall a, in_img rsegs a -> 0 <= a < kLowMemEnd.
Proof. exact HPgSteps.img_segs_low. Qed.

(* the shadow base of the engine's shadow tokens: s11 holds K (the runtime's shadow offset), atom 27 *)
Definition hw10_Bx : sv := SOff 27 0.
Definition hw10_Bspan : Z * Z := (SHADOW_OFF, SHADOW_OFF + 2 ^ 44 - 1).
(* the highest address of the first block the atoms may name: pp + PP_SIZE <= the allocator's ceiling *)
Definition HW10_PPHI : Z := 0x7fffff800000 - 0x4d20.
(* the highest address an atom for a byte of the input may take: below 2^47, so that its shadow byte lies inside
   hw10_Bspan *)
Definition HW10_HI : Z := 2 ^ 47 - 16.
(* the shadow address of the atom n plus c, as the code forms it: `srli x,y,3; add x,x,s11` *)
Definition hw10_sh (n : nat) (c : Z) : sv := SAlu ALU_ADD (SAlu ALU_SRL (SOff n c) (SLit 3)) hw10_Bx.

(* ---- denotations of the symbolic values the pieces' states use ---- *)
Section den. Context {fx : YK11.FPState}.
Lemma hw10_den_atom : forall E n v, ew E n = Z_to_bv 64 v -> sv_denot E (SOff n 0) = Z_to_bv 64 v.
Proof. intros E n v H. cbn [sv_denot]. rewrite H, Z.add_0_r. apply Z_to_bv_bv_unsigned. Qed.
Lemma hw10_den_off : forall E n v c, ew E n = Z_to_bv 64 v -> sv_denot E (SOff n c) = Z_to_bv 64 (v + c).
Proof.
intros E n v c H. cbn [sv_denot]. rewrite H. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap.
rewrite Z.add_mod_idemp_l by (unfold bv_modulus; lia). reflexivity.
Qed.
Lemma hw10_den_sh : forall E n v c, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> 0 <= v + c < 2 ^ 47 ->
  ew E 27 = Z_to_bv 64 SHADOW_OFF -> sv_denot E (hw10_sh n c) = Z_to_bv 64 (shadow_addr (v + c)).
Proof.
intros E n v c Hn Hv Hc Hb. unfold hw10_sh, hw10_Bx. rewrite denot_lit_U. f_equal.
rewrite !U_SAlu, U_SLit, (U_atom_off E n v c Hn Hv ltac:(lia)), (U_atom E 27 SHADOW_OFF Hb ltac:(unfold SHADOW_OFF; lia)).
cbn [zalu_raw]. change (Z.land (zcanon 3) 63) with 3. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8.
assert (0 <= (v + c) / 8 < 2 ^ 44) by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
unfold shadow_addr, SHADOW_OFF. rewrite (zcanon_id ((v + c) / 8)) by (unfold M64; lia). rewrite zcanon_id by (unfold M64; lia). lia.
Qed.
Lemma hw10_U_atom : forall E n v, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> U E (SOff n 0) = v.
Proof. exact U_atom. Qed.
Lemma hw10_UB : forall E, ew E 27 = Z_to_bv 64 SHADOW_OFF -> U E hw10_Bx = SHADOW_OFF.
Proof. intros E H. unfold hw10_Bx. apply (U_atom E 27 SHADOW_OFF H). unfold SHADOW_OFF. lia. Qed.
End den.
(* a register outside a clobber list, decided by computation *)
Lemma hw10_notin : forall (r : bv 5) (clob : list (bv 5)), existsb (fun c => bv_eqb c r) clob = false -> ~ In r clob.
Proof.
intros r clob H Hin. assert (Hx : existsb (fun c => bv_eqb c r) clob = true).
{ apply existsb_exists. exists r. split; [exact Hin | apply bv_eqb_refl]. }
congruence.
Qed.
(* the symbolic value of a register in a state, read off by computation *)
Ltac hw10_sr_eval :=
  repeat lazymatch goal with |- context [sr_get ?l ?r] =>
    let v := eval vm_compute in (sr_get l r) in change (sr_get l r) with v end.

(* ======================================== 2. the model ======================================== *)
Lemma hw10_byte_self : forall b : byte, Z_to_bv 8 (bv_unsigned b) = b.
Proof. intros b. apply bv_eq. rewrite Z_to_bv_unsigned. apply bv_wrap_small. apply bv_unsigned_in_range. Qed.

Lemma hw10_overwrite_nil : forall (l : list byte) o, overwrite l o [] = l.
Proof. intros l o. unfold overwrite. cbn [app length]. rewrite Nat.add_0_r. apply firstn_skipn. Qed.

Lemma hw10_list_split4 : forall (l : list byte) o nx ny, (o + nx + ny <= length l)%nat ->
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

Lemma hw10_overwrite_adj : forall (l x y : list byte) o,
  (o + length x + length y <= length l)%nat ->
  overwrite (overwrite l o x) (o + length x)%nat y = overwrite l o (x ++ y).
Proof.
  intros l x y o H.
  set (A := firstn o l). set (X := firstn (length x) (skipn o l)).
  set (Y := firstn (length y) (skipn (o + length x) l)). set (C := skipn (o + length x + length y) l).
  assert (LA : length A = o) by (subst A; rewrite length_firstn; lia).
  assert (LX : length x = length X) by (subst X; rewrite length_firstn, length_skipn; lia).
  assert (LY : length y = length Y) by (subst Y; rewrite length_firstn, length_skipn; lia).
  assert (El : l = A ++ X ++ Y ++ C) by (subst A X Y C; apply hw10_list_split4; exact H).
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
Lemma hw10_corr_none_nil : forall len, fst (corr_step len []) = None.
Proof.
  intros len. unfold corr_step. cbn [fuzz_u8].
  replace ((0 mod 16 =? 15) && (8 <? len)) with false by reflexivity. reflexivity.
Qed.

Lemma hw10_corr_none : forall len (c : byte) (r1 : list byte), bv_unsigned c mod 16 <> 15 \/ len <= 8 ->
  fst (corr_step len (c :: r1)) = None.
Proof.
  intros len c r1 H. unfold corr_step. cbn [fuzz_u8].
  replace ((bv_unsigned c mod 16 =? 15) && (8 <? len)) with false; [reflexivity|].
  symmetry. apply andb_false_iff. destruct H as [H|H]; [left; apply Z.eqb_neq; exact H | right; apply Z.ltb_ge; lia].
Qed.

Lemma hw10_corr_some : forall len (c : byte) (r1 : list byte), bv_unsigned c mod 16 = 15 -> 8 < len ->
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

Lemma hw10_corr_empty_tail : forall (r1 : list byte), (length r1 <= 2)%nat -> fst (fuzz_u8 (skipn 2 r1)) = 0.
Proof. intros r1 H. rewrite skipn_all2 by lia. reflexivity. Qed.

Lemma hw10_fuzz_u8s_cons : forall n (x : byte) (l : list byte),
  fst (fuzz_u8s (S n) (x :: l)) = x :: fst (fuzz_u8s n l).
Proof.
  intros n x l. cbn [fuzz_u8s fuzz_u8]. destruct (fuzz_u8s n l) as [bs r]. cbn [fst].
  f_equal. apply hw10_byte_self.
Qed.

Lemma hw10_fuzz_u8s_nil : forall n, fst (fuzz_u8s (S n) []) = Z_to_bv 8 0 :: fst (fuzz_u8s n []).
Proof. intros n. cbn [fuzz_u8s fuzz_u8]. destruct (fuzz_u8s n []) as [bs r]. reflexivity. Qed.

Lemma hw10_length_fuzz_u8s : forall n l, length (fst (fuzz_u8s n l)) = n.
Proof.
  induction n as [|n IH]; intros l; [reflexivity|]. cbn [fuzz_u8s].
  destruct (fuzz_u8 l) as [b r]. specialize (IH r). destruct (fuzz_u8s n r) as [bs r']. cbn [fst length] in *. lia.
Qed.

(* ---- the record the pieces end with ---- *)
Lemma hw10_pod_encode_co : forall sh ps co, pod_encode (PodRec sh ps co) = pod_encode (PodRec sh ps None).
Proof. intros sh ps co. reflexivity. Qed.

(* What a record the property loop can build gives about the object's bytes. *)
Lemma hw10_wf_facts : forall sh ps, hsu_wf sh ps ->
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
Lemma hw10_img_top : forall sh ps, hsu_wf sh ps ->
  overwrite (pc_image (PbCut sh ps None)) 0%nat (le32 (Z.of_nat (length (pc_buf (PbCut sh ps None))) - 8))
  = pp_image (pod_encode (PodRec sh ps None)) (is_props (PodRec sh ps None))
      (has_params (PodRec sh ps None)) (params_struct (PodRec sh ps None))
      (ents (PodRec sh ps None)) false.
Proof.
  intros sh ps Hwf. destruct (hw10_wf_facts sh ps Hwf) as (HL1 & HL2 & _ & _).
  unfold pc_image. cbn [pc_shape pc_props]. rewrite (pc_ents_final sh ps None).
  rewrite <- pp_image_patch by (rewrite length_le32; lia).
  f_equal. apply pc_buf_top.
Qed.

(* One byte of the corruption (pod.h:446). *)
Lemma hw10_img_step : forall sh ps (off : Z) (bsk : list byte) (x : byte),
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
  f_equal. apply hw10_overwrite_adj. cbn [length]. lia.
Qed.

(* corrupt = 1 (pod.h:447): the record's own image. *)
Lemma hw10_img_corrupt : forall sh ps off bs, hsu_wf sh ps -> 0 <= off ->
  (Z.to_nat off + length bs <= length (pod_encode (PodRec sh ps None)))%nat ->
  overwrite (pp_image (overwrite (pod_encode (PodRec sh ps None)) (Z.to_nat off) bs)
               (is_props (PodRec sh ps None)) (has_params (PodRec sh ps None))
               (params_struct (PodRec sh ps None)) (ents (PodRec sh ps None)) false)
            (Z.to_nat OFF_CORRUPT) (le32 1)
  = pp_bytes (PodRec sh ps (Some (off, bs))).
Proof.
  intros sh ps off bs Hwf Ho Hl. destruct (hw10_wf_facts sh ps Hwf) as (HL1 & HL2 & HE1 & HE2 & _).
  replace (le32 1) with (le32 (Z.b2z true)) by reflexivity.
  rewrite (pp_image_corrupt (overwrite (pod_encode (PodRec sh ps None)) (Z.to_nat off) bs) _ _ _ _ false);
    [| rewrite length_overwrite by exact Hl; unfold POD_BUF_MAX; lia | exact HE1 | exact HE2].
  reflexivity.
Qed.

(* the no-corruption record's image is the image at RT's start with nothing written *)
Lemma hw10_bytes_none : forall sh ps,
  pp_bytes (PodRec sh ps None)
  = pp_image (pod_encode (PodRec sh ps None)) (is_props (PodRec sh ps None))
      (has_params (PodRec sh ps None)) (params_struct (PodRec sh ps None)) (ents (PodRec sh ps None)) false.
Proof. intros sh ps. reflexivity. Qed.

(* the record pod_build makes, from the builder's end state (HPgSeg.hsu_Pbody's ties) *)
Lemma hw10_build_tie : forall rest sh np ps r,
  sh = hsu_sh rest -> np = hsu_np rest -> Z.of_nat (length ps) = np ->
  (ps, r) = props_loop sh (length ps) (hsu_r0 rest) ->
  fst (pod_build rest) = PodRec sh ps (fst (corr_step (Z.of_nat (length (pod_encode (PodRec sh ps None)))) r)).
Proof.
intros rest sh np ps r Hsh Hnp Hl Hps. unfold hsu_sh, hsu_np, hsu_r0 in *. unfold pod_build.
destruct (Cursor.fuzz_u8 rest) as [s r1]. cbn [fst snd] in *. destruct (Cursor.fuzz_u8 r1) as [n r2]. cbn [fst snd] in *.
assert (Hn : Z.to_nat (n mod 4) = length ps) by (rewrite <- Hnp, <- Hl; apply Nat2Z.id).
rewrite Hn, <- Hsh, <- Hps. cbv iota beta.
destruct (corr_step _ r) as [co r4]. reflexivity.
Qed.

(* the length of the object, as buf of either record *)
Lemma hw10_buf_len : forall sh ps co, corr_wf (Z.of_nat (length (pod_encode (PodRec sh ps None)))) co ->
  length (buf (PodRec sh ps co)) = length (pod_encode (PodRec sh ps None)).
Proof.
  intros sh ps [[off bs]|] H; cbn [buf p_corr]; [|reflexivity].
  destruct H as (H1 & H2 & H3). rewrite hw10_pod_encode_co. apply length_overwrite. lia.
Qed.

(* the length of the pod the harness allocates (HPgSiteA.hd_len_bounds, restated here: that file is image A's) *)
Lemma hw10_len_bounds : forall rest, 8 <= hd_len rest <= 5440.
Proof.
intros rest. unfold hd_len.
destruct (Model.pod_build rest) as [r rest'] eqn:E. cbn [fst].
pose proof (Spa.buf_header r (Model.pod_build_wf rest r rest' E)) as (_ & _ & _ & H). exact H.
Qed.

(* the record pod_build makes is well formed, and its image's fields fit Layout's bounds *)
Lemma hw10_rec_facts : forall rest,
  pod_rec_wf (fst (pod_build rest)) /\
  Z.of_nat (length (buf (fst (pod_build rest)))) <= POD_BUF_MAX /\
  (length (ents (fst (pod_build rest))) <= 32)%nat /\
  Forall (fun e => (length (e_body e) <= 96)%nat) (ents (fst (pod_build rest))).
Proof.
intros rest. destruct (pod_build rest) as [r rest'] eqn:EB. cbn [fst].
pose proof (pod_build_wf rest r rest' EB) as Hwf. split; [exact Hwf|].
destruct (ents_wf r Hwf) as [HE1 HE2].
pose proof Hwf as (_ & _ & _ & _ & HL & Hc).
assert (Hb : length (buf r) = length (pod_encode r)).
{ unfold buf. destruct (p_corr r) as [[off bs]|] eqn:Ec; [|reflexivity].
  destruct Hc as (C1 & C2 & C3). apply length_overwrite. lia. }
split; [rewrite Hb; unfold POD_BUF_MAX; lia|]. split; [exact HE1|].
eapply Forall_impl; [|exact HE2]. intros e (_ & H1 & H2). lia.
Qed.

(* ======================================== 3. the run's context ======================================== *)
Section k. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Variable B : asyms.
Variable MT : ameter_ops.

(* What a run leaves of the bytes outside its write windows. *)
Lemma hw10_frame_kept : forall E rs (H : word -> bool) m m',
  frame_of E rs (mrestrict H m) (mrestrict H m') ->
  forall a, 0 <= a < 2 ^ 64 -> ~ in_wrange E rs a -> aview rsegs H m' a = aview rsegs H m a.
Proof.
intros E rs H m m' HF a Ha Hn. unfold aview, mbyte.
rewrite (HF (Z_to_bv 64 a)); [reflexivity|]. rewrite unsigned_lit_small by exact Ha. exact Hn.
Qed.

(* The first block, the real frame and the stack window at a cut of the build segment. *)
Lemma hw10_ctx : forall cx sh ly2 S2 W2 regs2 mem2 md2,
  hsu_pre rsegs B headamp_himg_B cx sh -> hsu_core rsegs B MT cx (hsu_E1 rsegs headamp_himg_B cx) ly2 S2 W2 regs2 mem2 md2 ->
  In (e_pp (x_e cx), PP_SIZE) (ablocks B ly2 S2) /\
  ~ In (e_pp (x_e cx), PP_SIZE) (ablocks B (x_ly cx) (x_S cx)) /\
  e_pp (x_e cx) mod 16 = 0 /\ 4096 <= e_pp (x_e cx) /\ e_pp (x_e cx) + 19744 <= alloc_ceiling /\
  in_app (e_pp (x_e cx)) 19744 /\
  (forall a, e_pp (x_e cx) <= a < e_pp (x_e cx) + 19744 -> apresent (w_H W2) mem2 a) /\
  getr regs2 (Z_to_bv 5 2) = w64 (e_R (x_e cx)) /\ e_R (x_e cx) mod 32 = 0 /\ e_R (x_e cx) + 0x220 <= x_sp0 cx /\
  x_sp0 cx - x_STK cx <= e_R (x_e cx) - T_SEG_STK /\ alloc_ceiling <= x_sp0 cx - x_STK cx /\ x_sp0 cx <= 2 ^ 47 /\
  AR rsegs B ly2 S2 W2 mem2 md2.
Proof.
intros cx sh ly2 S2 W2 regs2 mem2 md2 HP HC.
unfold hsu_pre, hd_seg_pre in HP.
destruct HP as (HJ0 & Hev & H2 & H3 & H4 & HS & HR32 & HRS & HSTK & Hown & HF & Hfsh & Hcap & Hnull & Hro &
  Hgl & Hrz & Hstr & Hcl & Hguard & Hrom & (Hpp0 & Hpp & Hfresh)).
destruct HC as (HJ & Hr234 & Hfr & Hperm & Hio & Hmo & Hkeep).
pose proof (AR_laws_ok rsegs B) as LAWS.
assert (Hin : In (e_pp (x_e cx), PP_SIZE) (ablocks B ly2 S2))
  by (eapply Permutation_in; [apply Permutation_sym; exact Hperm | exact Hpp]).
destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ (proj1 HJ) Hin) as (Hal & Hlo & Hhi & Happ & Hpres & _).
change (req_size PP_SIZE) with 19744 in *.
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstk & _).
destruct Hstk as (Hsp0al & Hstk0 & Hceil & Hslo & Hshi & H47 & _).
cbn [hi_rsz headamp_himg_B] in HRS.
rewrite (Hr234 2 (or_introl eq_refl)).
split; [exact Hin|]. split; [exact Hfresh|]. split; [exact Hal|]. split; [exact Hlo|]. split; [exact Hhi|].
split; [exact Happ|]. split; [intros a Ha; apply (Hpres a Ha)|]. split; [exact H2|].
split; [exact HR32|]. split; [lia|]. split; [exact HSTK|]. split; [lia|]. split; [lia|]. exact (proj1 HJ).
Qed.

(* the frame for locals at the segment's start: a class-4 side-stack frame of 1024 bytes *)
Lemma hw10_F_ctx : forall cx sh, hsu_pre rsegs B headamp_himg_B cx sh ->
  4096 <= e_F (x_e cx) /\ e_F (x_e cx) + 1024 <= alloc_ceiling /\ in_app (e_F (x_e cx)) 1024.
Proof.
intros cx sh HP. unfold hsu_pre, hd_seg_pre in HP.
destruct HP as (HJ0 & Hev & H2 & H3 & H4 & HS & HR32 & HRS & HSTK & Hown & HF & _).
pose proof HJ0 as (HAR & _ & _ & _ & _ & Hfrs & _).
assert (Hin : In (hi_cid headamp_himg_B, x_pos cx) (frames (x_Sc cx)))
  by (rewrite Hfrs; apply in_or_app; left; exact Hown).
destruct (frames_bounds rsegs B (AR_laws_ok rsegs B) _ _ _ _ _ _ _ HAR Hin) as (F1 & F2 & F3).
cbn [hi_cid headamp_himg_B] in HF, F1, F2, F3. rewrite <- HF in F1, F2, F3.
change (fs_frame_bytes 4) with 1024 in *. auto.
Qed.

(* A cut's journal clauses after an engine run inside the segment whose writes all lie in the segment's write set. *)
Lemma hw10_core_run : forall cx ly2 S2 W2 regs2 mem2 md2 regs3 mem3 md3 (Wr : Z -> Prop),
  hsu_core rsegs B MT cx (hsu_E1 rsegs headamp_himg_B cx) ly2 S2 W2 regs2 mem2 md2 ->
  ajournal rsegs B (x_STK cx) (x_sp0 cx) (x_FP cx) (x_ly cx) (x_S cx) (x_W0 cx) (x_mem0 cx) (x_md0 cx) (x_own cx)
    ly2 S2 W2 mem3 md3 (x_k cx) ->
  (forall r : Z, r = 2 \/ r = 3 \/ r = 4 -> getr regs3 (Z_to_bv 5 r) = getr regs2 (Z_to_bv 5 r)) ->
  same_io md2 md3 ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ Wr a -> aview rsegs (w_H W2) mem3 a = aview rsegs (w_H W2) mem2 a) ->
  (forall a, Wr a -> hsu_E1 rsegs headamp_himg_B cx a) ->
  hsu_core rsegs B MT cx (hsu_E1 rsegs headamp_himg_B cx) ly2 S2 W2 regs3 mem3 md3.
Proof.
intros cx ly2 S2 W2 regs2 mem2 md2 regs3 mem3 md3 Wr HC HJ3 H234 Hio3 HK HW.
destruct HC as (HJ & Hr234 & Hfr & Hperm & Hio & Hmo & Hkeep).
split; [exact HJ3|]. split; [intros r Hr; rewrite (H234 r Hr); exact (Hr234 r Hr)|].
split; [exact Hfr|]. split; [exact Hperm|]. split; [eapply same_io_trans; eassumption|]. split; [exact Hmo|].
intros a Ha Hs He. rewrite (HK a Ha (fun Hw => He (HW a Hw))). exact (Hkeep a Ha Hs He).
Qed.

(* the shadow obligation of an access inside the first block *)
Lemma hw10_ob_blk : forall ly S (W : world rsegs) mem md E p m a n x,
  AR rsegs B ly S W mem md -> In (p, m) (ablocks B ly S) -> p <= a -> a + n <= p + req_size m ->
  U E hw10_Bx = SHADOW_OFF -> U E x = a ->
  range_addressable (rd_of rsegs (mrestrict (w_H W) mem)) (U E hw10_Bx) (U E x) n.
Proof.
intros ly S W mem md E p m a n x HAR Hin Hpa Han HB Hx. rewrite HB, Hx.
exact (proj1 (hm_blk_ra rsegs B ly S W mem md p m a n HAR Hin Hpa Han)).
Qed.

(* a shadow entry of the engine for a range inside a heap block (in the app band, so apart from the shadow span):
   the write windows of the first block are covered by such entries *)
Lemma hw10_shent_blk : forall ly S (W : world rsegs) mem md E p m n lo hi,
  AR rsegs B ly S W mem md -> In (p, m) (ablocks B ly S) -> in_app p (req_size m) ->
  U E hw10_Bx = SHADOW_OFF -> p <= U E (SOff n 0) + lo -> U E (SOff n 0) + hi <= p + req_size m -> lo < hi ->
  shent_ok rsegs hw10_Bx E (mrestrict (w_H W) mem) (mkSHE n lo hi).
Proof.
intros ly S W mem md E p m n lo hi HAR Hin Happ HB H1 H2 H3. split; cbn [she_m she_lo she_hi].
- rewrite HB. exact (proj1 (hm_blk_ra rsegs B ly S W mem md p m (U E (SOff n 0) + lo) (hi - lo) HAR Hin H1 ltac:(lia))).
- unfold app_apart. cbn [she_m she_lo she_hi]. intros a Ha. rewrite HB. pose proof ASAN_CEIL_range as [CR _].
  rewrite Z.min_l, Z.max_r in Ha by lia.
  unfold in_app, kLowShadowBeg, kHighMemBeg, SHADOW_OFF in *. lia.
Qed.

(* the shadow entry of k input bytes at an atom: their shadow bytes say they are addressable, and they lie in the
   application's memory, apart from the shadow span *)
Lemma hw10_shent_in : forall E m n src left c k, amem_range src left -> U E hw10_Bx = SHADOW_OFF ->
  U E (SOff n 0) = c -> src <= c -> c + k <= src + left -> 0 < k ->
  range_addressable (rd_of rsegs m) SHADOW_OFF src left ->
  shent_ok rsegs hw10_Bx E m (mkSHE n 0 k).
Proof.
intros E m n src left c k Ham HB Hc H1 H2 Hk Hra. split; cbn [she_m she_lo she_hi].
- rewrite HB, Hc. eapply range_addressable_sub; [exact Hra | lia | lia].
- unfold app_apart. cbn [she_m she_lo she_hi]. intros a Ha. rewrite HB. rewrite Hc in Ha.
  rewrite Z.min_l, Z.max_r in Ha by lia.
  unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd, SHADOW_OFF in *. lia.
Qed.

(* the write right of a region inside the first block *)
Lemma hw10_awr_cons_pp : forall E r rs STK sp0 FP bl0 blc ly own n b pp,
  r_base r = Some n -> bv_unsigned (ew E n) = b -> In (pp, PP_SIZE) blc -> ~ In (pp, PP_SIZE) bl0 ->
  pp <= b + r_wlo r -> b + r_whi r <= pp + PP_SIZE ->
  awr_ok E rs STK sp0 FP bl0 blc ly own -> awr_ok E (r :: rs) STK sp0 FP bl0 blc ly own.
Proof.
intros E r rs STK sp0 FP bl0 blc ly own n b pp Hb Hn Hin Hout Hlo Hhi H a (r' & [<-|Hr] & Ha).
- rewrite Hb in Ha. cbn [base_val] in Ha. rewrite Hn in Ha.
  replace a with (pp + (a - pp)) by lia.
  apply (hd_fresh_awr STK sp0 FP bl0 blc ly own pp PP_SIZE (a - pp) Hin Hout).
  change (req_size PP_SIZE) with 19744. unfold PP_SIZE in Hhi. lia.
- apply H. exists r'. auto.
Qed.

(* a field of a region, read back after a run *)
Lemma hw10_field : forall E m n b cs lo hi wlo whi od (w : N) e v,
  region_ok rsegs E m (YP09.mkRegion (Some n) lo hi wlo whi cs) ->
  bv_unsigned (ew E n) = b -> In (YP09.mkChunk od (CVal w e)) cs -> sv_denot E e = Z_to_bv 64 v ->
  0 <= v < 2 ^ (8 * Z.of_N w) -> (Z.of_N w <= 8) ->
  val_mem rsegs m (b + od) (N.to_nat w) v.
Proof.
intros E m n b cs lo hi wlo whi od w e v (_ & _ & _ & Hcs) Hn Hc He Hv Hw.
pose proof (proj1 (Forall_forall _ _) Hcs _ Hc) as Hck. cbn [YP09.r_base base_val] in Hck. rewrite Hn in Hck.
exact (val_of_chunk_ok rsegs E m b od w e v Hck He Hv Hw).
Qed.

(* a register at the end of a run, through the agreement of the run's environment with the entry one *)
Lemma hw10_reg : forall E0 E ss ms (H : word -> bool) (r : bv 5) k v w,
  st_ok rsegs E ss (restrict H ms) -> env_agree k E0 E -> sr_get (ss_regs ss) r = v -> sv_atoms_lt k v = true ->
  sv_denot E0 v = w -> getr (ms_regs ms) r = w.
Proof.
intros E0 E ss ms H r k v w HS HA Hv Hk Hw.
rewrite (st_ok_restrict_reg rsegs H E ss ms r HS), Hv, (sv_denot_agree k E0 E v HA Hk). exact Hw.
Qed.

(* the first block's bytes and the frame's shadow bytes are apart *)
Lemma hw10_shadow_not_pp : forall pp F i,
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

(* C2's value list from the post cuts' list, a0 = len + 0 and s5 = len *)
Lemma hw10_L2_of_post : forall (cx : hsu_scx rsegs) H mem regs,
  hsu_at rsegs H mem regs (x_e cx) (hsu_L_post rsegs cx) ->
  getr regs (Z_to_bv 5 10) = w64 (e_len (x_e cx)) -> getr regs (Z_to_bv 5 21) = w64 (e_len (x_e cx)) ->
  0 < e_len (x_e cx) ->
  hd_cut rsegs H mem regs (x_e cx) (hi_L2 headamp_himg_B).
Proof.
intros cx H mem regs Hp H10 H21 Hl. unfold hsu_at, hsu_L_post in Hp. cbv zeta in Hp.
unfold hd_cut. cbn [hi_L2 headamp_himg_B]. unfold headamp_B_L23.
rewrite !Forall_cons_iff in Hp.
destruct Hp as (P8 & P9 & P19 & P27 & P7 & P18 & P24 & C08 & C18 & C20 & C38 & C48 & Ce0 & C108 & C120 & C148 & C150 & _).
cbn [fst snd] in *.
repeat (apply Forall_cons; [cbn [fst snd hd_xv]|]); [..|apply Forall_nil]; try assumption;
try (rewrite Z.add_0_r; assumption).
cbn [hd_at]. rewrite (proj2 (Z.eqb_neq _ _)) by lia. rewrite Z.add_0_r. exact H10.
Qed.

(* ---- the segment's start facts at a cut (port of RPgW6cKit part 1) ---- *)
(* what a cut may have changed since the segment's start: outside [0, 2^64), the callees' stack, hsu_E1 *)
Definition hw10_wr (cx : hsu_scx rsegs) (a : Z) : Prop :=
(a < 0 \/ 2 ^ 64 <= a) \/ (e_R (x_e cx) - T_SEG_STK <= a < e_R (x_e cx)) \/ hsu_E1 rsegs headamp_himg_B cx a.

(* the address facts of the segment's start: R above the shadow band, F and pp in the application's memory *)
Lemma hw10_pre_geom : forall cx sh, hsu_pre rsegs B headamp_himg_B cx sh ->
spZ (x_regs cx) = e_R (x_e cx) /\
kHighMemBeg <= e_R (x_e cx) - T_SEG_STK /\ e_R (x_e cx) + 0x220 <= 2 ^ 47 /\
in_app (e_F (x_e cx)) 1024 /\ in_app (e_pp (x_e cx)) PP_SIZE.
Proof.
intros cx sh HP. pose proof (hw10_F_ctx cx sh HP) as (_ & _ & HFapp).
unfold hsu_pre, hd_seg_pre in HP.
destruct HP as (HJ & Hev & Hsp & H3 & H4 & HeS & HR32 & HRS & HSTK & Hown & HF & Hfsh & Hcap & Hnull & Hro &
  Hgl & Hrz & Hstr & Hcl & Hguard & Hrom & (Hpp0 & Hpp & Hfresh)).
cbn [hi_rsz headamp_himg_B] in HRS.
pose proof HJ as (HAR & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstk & _).
destruct Hstk as (Hal & HSTK0 & Hceil & Hlo & Hhi & H47 & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct (al_blocks _ _ (AR_laws_ok rsegs B) _ _ _ _ _ (e_pp (x_e cx)) PP_SIZE HAR Hpp) as (_ & _ & _ & Happ & _).
replace (req_size PP_SIZE) with PP_SIZE in Happ by reflexivity.
assert (HR0 : 0 <= e_R (x_e cx) < 2 ^ 64) by (unfold T_SEG_STK, ASTACK in HSTK; lia).
split; [unfold spZ; rewrite Hsp; unfold w64; apply unsigned_lit_small; lia|].
split; [unfold T_SEG_STK, ASTACK in *; lia|].
split; [lia|]. split; [exact HFapp | exact Happ].
Qed.

Lemma hw10_core_kept : forall cx sh ly2 S2 W2 regs2 mem2 md2,
hsu_pre rsegs B headamp_himg_B cx sh ->
hsu_core rsegs B MT cx (hsu_E1 rsegs headamp_himg_B cx) ly2 S2 W2 regs2 mem2 md2 ->
forall a, ~ hw10_wr cx a -> aview rsegs (w_H W2) mem2 a = aview rsegs (w_H (x_W cx)) (x_memc cx) a.
Proof.
intros cx sh ly2 S2 W2 regs2 mem2 md2 HP HC a Ha.
destruct (hw10_pre_geom cx sh HP) as (Hsp & _).
destruct HC as (_ & _ & _ & _ & _ & _ & HK). unfold hw10_wr in Ha.
apply HK; [lia | rewrite Hsp; intros X; apply Ha; right; left; exact X | intros X; apply Ha; right; right; exact X].
Qed.

(* a shadow byte of an application address is never in hsu_E1 or the callees' stack *)
Lemma hw10_wr_shadow : forall cx x, hsu_pre rsegs B headamp_himg_B cx (hi_shA headamp_himg_B) -> 0 <= x < kHighMemEnd ->
range_addressable (aview rsegs (w_H (x_W cx)) (x_memc cx)) SHADOW_OFF x 1 ->
~ hw10_wr cx (shadow_of_addr SHADOW_OFF x).
Proof.
intros cx x HP Hx Hra.
destruct (hw10_pre_geom cx _ HP) as (_ & HRk & _ & HFapp & Happ).
pose proof (hm_shadow_band x Hx) as Hb.
assert (Hfsh : hd_fsh rsegs (w_H (x_W cx)) (x_memc cx) (e_F (x_e cx)) headamp_B_shA).
{ unfold hsu_pre, hd_seg_pre in HP. destruct HP as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & H & _). exact H. }
pose proof (hm_ra_not_fsh rsegs _ _ _ _ x 1 Hra Hfsh hmu_sh_P0_big x ltac:(lia)) as Hnf.
change (Z.of_nat (length headamp_B_shA)) with 116 in Hnf.
unfold hw10_wr, hsu_E1, hd_inw. cbn [hi_w1 headamp_himg_B].
intros [H|[H|[H|H]]].
- unfold kLowMemEnd, kHighMemBeg in Hb. lia.
- unfold kHighMemBeg in *. lia.
- apply Exists_cons in H as [H|H]; [|apply Exists_cons in H as [H|H]; [|apply Exists_cons in H as [H|H]; [|apply Exists_nil in H; destruct H]]];
  cbn [fst snd hd_xv] in H.
  + apply (hm_shadow_not_app x (e_F (x_e cx)) 1024 Hx HFapp). lia.
  + apply Hnf. unfold shadow_addr in *. lia.
  + unfold kHighMemBeg, T_SEG_STK, ASTACK in *. lia.
- apply (hm_shadow_not_app x (e_pp (x_e cx)) PP_SIZE Hx Happ). exact H.
Qed.

Lemma hw10_in_now : forall cx rest pat ly2 S2 W2 regs2 mem2 md2,
hsu_pre rsegs B headamp_himg_B cx (hi_shA headamp_himg_B) -> hsu_in rsegs headamp_himg_B cx rest ->
hsu_core rsegs B MT cx (hsu_E1 rsegs headamp_himg_B cx) ly2 S2 W2 regs2 mem2 md2 ->
hsu_fsh_at rsegs cx W2 mem2 pat -> length pat = 116%nat ->
garr8 rsegs (mrestrict (w_H W2) mem2) (e_src (x_e cx)) (hd_zbytes rest) /\
range_addressable (aview rsegs (w_H W2) mem2) SHADOW_OFF (e_src (x_e cx)) (e_left (x_e cx)) /\
(0 < e_left (x_e cx) -> shadow_hull_vis (aview rsegs (w_H W2) mem2) (e_src (x_e cx)) (e_left (x_e cx))).
Proof.
intros cx rest pat ly2 S2 W2 regs2 mem2 md2 HP HI HC Hfsh2 Hpat.
pose proof (hw10_core_kept cx _ ly2 S2 W2 regs2 mem2 md2 HP HC) as HK.
destruct (hw10_pre_geom cx _ HP) as (_ & HRk & _ & HFapp & Happ).
destruct HI as (Hleft & Hbytes & Hra & Hhull & Hamr & Hsrc0 & Hsrc63 & Hdisj).
set (src := e_src (x_e cx)) in *. set (n := e_left (x_e cx)) in *.
assert (Hx : forall x, src <= x < src + n -> 0 <= x < kHighMemEnd).
{ intros x Hx. unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in *. lia. }
split.
- apply (hm_bytes_kept_wr rsegs (hw10_wr cx) _ _ _ _ src rest Hbytes HK).
  intros x Hx'. assert (Hx'' : src <= x < src + n) by (rewrite Hleft; exact Hx').
  destruct (Hdisj x Hx'') as (D1 & D2 & D3).
  unfold hw10_wr, hsu_E1. intros [H|[H|[H|H]]]; [lia | exact (D1 H) | exact (D2 H) | exact (D3 H)].
- split.
  + apply (hm_ra_kept_wr rsegs (hw10_wr cx) _ _ _ _ SHADOW_OFF src n Hra HK).
    intros x Hx'. apply hw10_wr_shadow; [exact HP | exact (Hx x Hx') |].
    apply (range_addressable_sub _ _ src n); [exact Hra | lia | lia].
  + intros Hn. apply (hm_hull_kept rsegs _ _ _ _ src n (Hhull Hn)).
    intros s Hs Hnone.
    destruct (base.decide (hw10_wr cx s)) as [Hw|Hw].
    2:{ rewrite (HK s Hw). exact Hnone. }
    assert (Hsb : SHADOW_OFF <= s < kHighMemBeg).
    { pose proof (Hx src ltac:(lia)). pose proof (Hx (src + n - 1) ltac:(lia)).
      unfold shadow_addr, SHADOW_OFF, kHighMemBeg, kHighMemEnd in *.
      pose proof (Z.div_pos src 8 ltac:(lia) ltac:(lia)).
      assert (2147450880 <= (2147450880 + src / 8) / 8 * 8).
      { assert (268431360 <= (2147450880 + src / 8) / 8) by (apply Z.div_le_lower_bound; lia). lia. }
      assert ((src + n - 1) / 8 < 17592186044416) by (apply Z.div_lt_upper_bound; lia).
      assert ((2147450880 + (src + n - 1) / 8) / 8 < 2199291686912) by (apply Z.div_lt_upper_bound; lia).
      lia. }
    unfold hw10_wr, hsu_E1, hd_inw in Hw. cbn [hi_w1 headamp_himg_B] in Hw.
    destruct Hw as [H|[H|[H|H]]].
    * exfalso. unfold SHADOW_OFF, kHighMemBeg in Hsb. lia.
    * exfalso. unfold kHighMemBeg, T_SEG_STK, ASTACK in *. lia.
    * apply Exists_cons in H as [H|H]; [|apply Exists_cons in H as [H|H]; [|apply Exists_cons in H as [H|H]; [|apply Exists_nil in H; destruct H]]];
      cbn [fst snd hd_xv] in H.
      -- exfalso. unfold in_app, kLowShadowBeg, kHighMemBeg, SHADOW_OFF in *. lia.
      -- unfold hsu_fsh_at, hd_fsh in Hfsh2. rewrite Hpat in Hfsh2.
         replace s with (shadow_addr (e_F (x_e cx)) + (s - shadow_addr (e_F (x_e cx)))) by lia.
         rewrite (Hfsh2 (s - shadow_addr (e_F (x_e cx))) ltac:(cbn; lia)). discriminate.
      -- exfalso. unfold kHighMemBeg, T_SEG_STK, ASTACK in *. lia.
    * exfalso. unfold in_app, kLowShadowBeg, kHighMemBeg, SHADOW_OFF, PP_SIZE in *. lia.
Qed.

End k.

Print Assumptions hw10_tbl_ok.
Print Assumptions hw10_den_sh.
Print Assumptions hw10_img_top.
Print Assumptions hw10_img_step.
Print Assumptions hw10_img_corrupt.
Print Assumptions hw10_build_tie.
Print Assumptions hw10_len_bounds.
Print Assumptions hw10_rec_facts.
Print Assumptions hw10_ctx.
Print Assumptions hw10_shent_blk.
Print Assumptions hw10_L2_of_post.
Print Assumptions hw10_in_now.
