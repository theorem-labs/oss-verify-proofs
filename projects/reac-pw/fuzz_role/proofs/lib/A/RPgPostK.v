(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_role/lib/Prog/RoleBuild/Post.v at f3cc5e1ef75 (its image-
   independent lemmas: the corruption step once its test is decided, the record the piece ends with, the block's
   image under the piece's writes) and lib/Prog/RoleBuild/Facts.v lines 25-92 at the same commit (overwrite_adj),
   restated over lib/Pod's Model / Layout for the ASan walk; the plain image's machine-state predicates are left out. *)
(* reac-pw/fuzz_role image A (fuzz_role.asan, pinned sha256
   614cffc0864cc31d9d1ced61322c4efd567b64bc89fe09a227a05b5126e0debb; addresses measured on the unstripped twin
   6da77bafc5c050954dd89149e1e55a24064c2211e3cbd351822d1c0a20900ad6): the kit of the post piece of the walk of
   LLVMFuzzerTestOneInput (0x7ff88), lib/A/RPgSeg.v's rs_piece_W10_post / _corr / _req (cuts P 0x81ed4, P1 0x81ed8,
   R 0x82018, RT 0x82094, C2 0x820c0). Proves no function (kind: segment lemma).
   1. The code table the engine reads: the piece 0x81ed4 .. 0x820c0 and the out-of-line blocks its instrumented
      checks branch to (0x825d8 .. 0x825f8, 0x82634 .. 0x8263c, 0x82750 .. 0x827b0, 0x82b00 .. 0x82b5c: each check's
      second test `andi; [addi]; blt back` or its error path, which the proof shows is not reached).
   2. The model: the corruption step (pod.h:441-448) once its tests are decided, the record's image under the
      piece's three writes (the top size word, one corruption byte, corrupt = 1), the bounds of a record the
      property loop can build.
   3. The run's context read off a cut: the first block (16-aligned, below the allocator ceiling, made since the
      segment's start so writable under the journal), the real frame, and what a cut's journal clauses become after
      an engine run whose writes all lie in the first block. *)
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d YG0q.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YI16 YM05.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Pod Require Import Cursor Model Layout.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.A Require Import Img0 RPgBase RPgCSpec RPgImgA RPgMem RPgSeg RPgSiteA.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.A Require RPgCfgChanges.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.A Require Import RPgW7bBase.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

(* the fields of RPgSeg's segment record take the segments implicitly in this walk's files *)
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
Definition W10_A : Z := 0x81ed4.
Definition w10_tbl : ctable :=
  build_table rsegs W10_A 124 (build_table rsegs 0x825d8 9 (build_table rsegs 0x82634 3
  (build_table rsegs 0x82750 25 (build_table rsegs 0x82b00 24 TEmpty)))).
Lemma w10_tbl_ok : table_ok rsegs w10_tbl.
Proof.
unfold w10_tbl. apply build_table_ok; [unfold W10_A; lia|]. apply build_table_ok; [lia|]. apply build_table_ok; [lia|].
apply build_table_ok; [lia|]. apply build_table_ok0. lia.
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
Lemma w10_wf_facts : forall sh ps, rs_wf sh ps ->
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
Lemma w10_img_top : forall sh ps, rs_wf sh ps ->
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
Lemma w10_img_corrupt : forall sh ps off bs, rs_wf sh ps -> 0 <= off ->
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

(* the record pod_build makes, from the builder's end state (RPgSeg.rs_Pbody's ties) *)
Lemma w10_build_tie : forall rest sh np ps r,
  sh = rs_sh rest -> np = rs_np rest -> Z.of_nat (length ps) = np ->
  (ps, r) = props_loop sh (length ps) (rs_r0 rest) ->
  fst (pod_build rest) = PodRec sh ps (fst (corr_step (Z.of_nat (length (pod_encode (PodRec sh ps None)))) r)).
Proof.
intros rest sh np ps r Hsh Hnp Hl Hps. unfold rs_sh, rs_np, rs_r0 in *. unfold pod_build.
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
intros E rs H m m' HF a Ha Hn.
exact (RPgCfgChanges.kept_run (in_wrange E rs) E rs H m m m' (fun _ _ _ => eq_refl) HF (fun _ x => x) a Ha Hn).
Qed.

(* The first block, the real frame and the stack window at a cut of the build segment. *)
Lemma w10_ctx : forall cx ly2 S2 W2 regs2 mem2 md2,
  rs_pre rsegs B cx -> rs_core rsegs B MT cx (rs_E1 rsegs cx) ly2 S2 W2 regs2 mem2 md2 ->
  In (e_pp (x_e cx), PP_SIZE) (ablocks B ly2 S2) /\
  ~ In (e_pp (x_e cx), PP_SIZE) (ablocks B (x_ly cx) (x_S cx)) /\
  e_pp (x_e cx) mod 16 = 0 /\ 4096 <= e_pp (x_e cx) /\ e_pp (x_e cx) + 19744 <= alloc_ceiling /\
  in_app (e_pp (x_e cx)) 19744 /\
  (forall a, e_pp (x_e cx) <= a < e_pp (x_e cx) + 19744 -> apresent (w_H W2) mem2 a) /\
  getr regs2 (Z_to_bv 5 2) = w64 (e_R (x_e cx)) /\ e_R (x_e cx) mod 16 = 0 /\ e_R (x_e cx) + 0x1a0 <= x_sp0 cx /\
  x_sp0 cx - x_STK cx <= e_R (x_e cx) - T_SEG_STK /\ alloc_ceiling <= x_sp0 cx - x_STK cx /\ x_sp0 cx <= 2 ^ 47 /\
  AR rsegs B ly2 S2 W2 mem2 md2.
Proof.
intros cx ly2 S2 W2 regs2 mem2 md2 HP HC.
destruct HP as (HJ0 & Hev & H2 & Hgp & Htp & HS & HR16 & HRS & HSTK & Hown & HF & Hfsh & Hpp0 & Hpp & Hfl
  & Hro & Hgl & Hrz & Hstr & Hcl & Hrom & Hfresh).
destruct HC as (HJ & Hr234 & Hfr & Hperm & Hio & Hmo & Hkeep).
pose proof (AR_laws_ok rsegs B) as LAWS.
assert (Hin : In (e_pp (x_e cx), PP_SIZE) (ablocks B ly2 S2))
  by (eapply Permutation_in; [apply Permutation_sym; exact Hperm | exact Hpp]).
destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ (proj1 HJ) Hin) as (Hal & Hlo & Hhi & Happ & Hpres & _).
change (req_size PP_SIZE) with 19744 in *.
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstk & _).
destruct Hstk as (Hsp0al & Hstk0 & Hceil & Hslo & Hshi & H47 & _).
cbn [hi_rsz role_himg_A] in HRS.
rewrite (Hr234 2 (or_introl eq_refl)).
split; [exact Hin|]. split; [exact Hfresh|]. split; [exact Hal|]. split; [exact Hlo|]. split; [exact Hhi|].
split; [exact Happ|]. split; [intros a Ha; apply (Hpres a Ha)|]. split; [exact H2|].
split; [exact HR16|]. split; [lia|]. split; [exact HSTK|]. split; [lia|]. split; [lia|]. exact (proj1 HJ).
Qed.

(* A cut's journal clauses after an engine run inside the segment whose writes all lie in the segment's write set. *)
Lemma w10_core_run : forall cx ly2 S2 W2 regs2 mem2 md2 regs3 mem3 md3 (Wr : Z -> Prop),
  rs_core rsegs B MT cx (rs_E1 rsegs cx) ly2 S2 W2 regs2 mem2 md2 ->
  ajournal rsegs B (x_STK cx) (x_sp0 cx) (x_FP cx) (x_ly cx) (x_S cx) (x_W0 cx) (x_mem0 cx) (x_md0 cx) (x_own cx)
    ly2 S2 W2 mem3 md3 (x_k cx) ->
  (forall r : Z, r = 2 \/ r = 3 \/ r = 4 -> getr regs3 (Z_to_bv 5 r) = getr regs2 (Z_to_bv 5 r)) ->
  same_io md2 md3 ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ Wr a -> aview rsegs (w_H W2) mem3 a = aview rsegs (w_H W2) mem2 a) ->
  (forall a, Wr a -> rs_E1 rsegs cx a) ->
  rs_core rsegs B MT cx (rs_E1 rsegs cx) ly2 S2 W2 regs3 mem3 md3.
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
exact (proj1 (rm_blk_ra rsegs B ly S W mem md p m a n HAR Hin Hpa Han)).
Qed.

(* a shadow entry of the engine for a range inside a heap block (in the app band, so apart from the shadow span):
   the write windows of the first block are covered by such entries *)
Lemma w10_shent_blk : forall ly S (W : world rsegs) mem md E p m n lo hi,
  AR rsegs B ly S W mem md -> In (p, m) (ablocks B ly S) -> in_app p (req_size m) ->
  U E W10Bx = SHADOW_OFF -> p <= U E (SOff n 0) + lo -> U E (SOff n 0) + hi <= p + req_size m -> lo < hi ->
  shent_ok rsegs W10Bx E (mrestrict (w_H W) mem) (mkSHE n lo hi).
Proof.
intros ly S W mem md E p m n lo hi HAR Hin Happ HB H1 H2 H3. split; cbn [she_m she_lo she_hi].
- rewrite HB. exact (proj1 (rm_blk_ra rsegs B ly S W mem md p m (U E (SOff n 0) + lo) (hi - lo) HAR Hin H1 ltac:(lia))).
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
apply (rl_fresh_awr STK sp0 FP bl0 blc ly own pp PP_SIZE (a - pp) Hin Hout).
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
Lemma w10_cells_not_pp : forall (cx : rs_scx rsegs) o i,
  e_pp (x_e cx) + 19744 <= alloc_ceiling -> alloc_ceiling <= x_sp0 cx - x_STK cx ->
  x_sp0 cx - x_STK cx <= e_R (x_e cx) - T_SEG_STK -> 0 <= o -> 0 <= i ->
  ~ (e_pp (x_e cx) <= e_R (x_e cx) + o + i < e_pp (x_e cx) + PP_SIZE).
Proof. intros cx o i H1 H2 H3 H4 H5. unfold PP_SIZE, T_SEG_STK, ASTACK in *. lia. Qed.

Lemma w10_shadow_not_pp : forall pp F i,
  in_app pp 19744 -> in_app F 512 -> 0 <= i < 64 -> ~ (pp <= shadow_addr F + i < pp + PP_SIZE).
Proof.
intros pp F i Hp HF Hi. pose proof ASAN_CEIL_range as [CR CR2].
destruct (shadow_addr_in_band F 512 (8 * i) HF ltac:(lia)) as [B1|B1];
unfold in_band_rw, in_app, shadow_addr, kLowShadowBeg, kLowShadowEnd, kHighShadowBeg, kHighShadowEnd, kHighMemBeg,
  SHADOW_OFF, PP_SIZE in *;
replace ((F + 8 * i) / 8) with (F / 8 + i) in B1
  by (rewrite <- (Z.div_add F i 8) by lia; f_equal; lia);
lia.
Qed.

(* the frame for locals at the segment's start *)
Lemma w10_F_ctx : forall cx, rs_pre rsegs B cx ->
  4096 <= e_F (x_e cx) /\ e_F (x_e cx) + 512 <= alloc_ceiling /\ in_app (e_F (x_e cx)) 512.
Proof.
intros cx HP.
destruct HP as (HJ0 & Hev & H2 & Hgp & Htp & HS & HR16 & HRS & HSTK & Hown & HF & Hfsh & Hpp0 & Hpp & Hfl
  & Hro & Hgl & Hrz & Hstr & Hcl & Hrom & Hfresh).
pose proof HJ0 as (HAR & _ & _ & _ & _ & Hfrs & _).
assert (Hin : In (3, x_pos cx) (frames (x_Sc cx))) by (rewrite Hfrs; apply in_or_app; left; exact Hown).
destruct (frames_bounds rsegs B (AR_laws_ok rsegs B) _ _ _ _ _ 3 (x_pos cx) HAR Hin) as (F1 & F2 & F3).
cbn [hi_cid role_himg_A] in HF. rewrite HF. change (fs_frame_bytes 3) with 512 in *. auto.
Qed.

(* C2's value list from the post cuts' list, a0 = s8 = len *)
Lemma w10_L2_of_post : forall (cx : rs_scx rsegs) H mem regs,
  rs_at rsegs H mem regs (x_e cx) (rs_L_post rsegs cx) ->
  getr regs (Z_to_bv 5 10) = w64 (e_len (x_e cx)) -> getr regs (Z_to_bv 5 24) = w64 (e_len (x_e cx)) ->
  0 < e_len (x_e cx) ->
  rl_cut rsegs H mem regs (x_e cx) (hi_L2 role_himg_A).
Proof.
intros cx H mem regs Hp H10 H24 Hl. unfold rs_at, rs_L_post in Hp. cbv zeta in Hp.
unfold rl_cut. cbn [hi_L2 role_himg_A]. unfold role_A_L23.
rewrite !Forall_cons_iff in Hp. destruct Hp as (P8 & P9 & P19 & P23 & P21 & P27 & P25 & P20 & P26 & C8 & C28 & C30 & C68 & C78 & C80 & _).
cbn [fst snd] in *.
repeat (apply Forall_cons; [cbn [fst snd rl_xv]|]); [..|apply Forall_nil]; try assumption;
try (rewrite Z.add_0_r; assumption).
cbn [rl_at]. rewrite (proj2 (Z.eqb_neq _ _)) by lia. rewrite Z.add_0_r. exact H10.
Qed.
End k.
