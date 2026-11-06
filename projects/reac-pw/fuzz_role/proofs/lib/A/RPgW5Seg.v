(* reac-pw/fuzz_role image A (fuzz_role.asan, pinned sha256
   614cffc0864cc31d9d1ced61322c4efd567b64bc89fe09a227a05b5126e0debb): the bridge between the cut states of
   lib/A/RPgSeg.v and the core lemmas of the W5 pieces (lib/A/RPgW5Close.v and its two siblings), whose start and
   end are stated as explicit register, cell and byte facts with a w5_post (lib/A/RPgW5Kit.v). Proves no function
   (kind: segment lemma).
   - w5_getr5: a register named by Z_to_bv 5 r (rl_at's form) is the register named by the literal.
   - w5_at_reg / w5_at_cell: a fact of a cut's (location, value) list, read back.
   - w5_core_post: a cut's segment frame (rs_core) is carried across a piece's w5_post whose write set lies in
     the segment's. *)
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YN3v YI04 YI09 YI08.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YI16 YM05.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Pod Require Import Cursor Model Layout.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.A Require Import Img0 RPgBase RPgCSpec RPgImgA RPgMem RPgSeg RPgW5Kit.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope Z_scope.

Section a. Context {fx : YK11.FPState}.
Lemma w5_getr5 : forall (regs : bvmap 5 word) (r : bv 5) z, bv_unsigned r = z -> getr regs (Z_to_bv 5 z) = getr regs r.
Proof.
intros regs r z H. f_equal. apply bv_eq. rewrite Z_to_bv_unsigned. subst z.
unfold bv_wrap. apply Z.mod_small. pose proof (bv_unsigned_in_range 5 r) as Hr. exact Hr.
Qed.
End a.

(* ======================================== byte lists ======================================== *)
Lemma w5_nth_ow : forall (l bs : list byte) off j d, (off + length bs <= length l)%nat ->
nth j (overwrite l off bs) d = if ((off <=? j) && (j <? off + length bs))%nat then nth (j - off) bs d else nth j l d.
Proof.
intros l bs off j d Hl. unfold overwrite.
assert (Hf : length (firstn off l) = off) by (apply firstn_length_le; lia).
destruct (Nat.leb_spec off j) as [H1|H1]; cbn [andb].
- rewrite app_nth2 by lia. rewrite Hf.
  destruct (Nat.ltb_spec j (off + length bs)) as [H2|H2].
  + rewrite app_nth1 by lia. reflexivity.
  + rewrite app_nth2 by lia. rewrite nth_skipn. f_equal. lia.
- rewrite app_nth1 by lia. rewrite nth_firstn. destruct (Nat.ltb_spec j off); [reflexivity | lia].
Qed.
Lemma w5_len_ow : forall (l bs : list byte) off, (off + length bs <= length l)%nat ->
length (overwrite l off bs) = length l.
Proof. intros l bs off H. apply length_overwrite. exact H. Qed.

Section m. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
(* bytes rebuilt pointwise: the ones Pb marks are read off the new state, the others are the old list's and
   unchanged in memory *)
Lemma w5_bytes_merge : forall H mem H' mem' a (l l' : list byte) (Pb : Z -> bool),
rm_bytes rsegs H mem a l -> length l' = length l ->
(forall j, (j < length l)%nat -> Pb (a + Z.of_nat j) = false ->
  aview rsegs H' mem' (a + Z.of_nat j) = aview rsegs H mem (a + Z.of_nat j) /\
  nth j l' (Z_to_bv 8 0) = nth j l (Z_to_bv 8 0)) ->
(forall j, (j < length l)%nat -> Pb (a + Z.of_nat j) = true ->
  aview rsegs H' mem' (a + Z.of_nat j) = Some (bv_unsigned (nth j l' (Z_to_bv 8 0)))) ->
rm_bytes rsegs H' mem' a l'.
Proof.
intros H mem H' mem' a l l' Pb Hb Hlen Hout Hin. apply rm_bytes_aview. intros j Hj. rewrite Hlen in Hj.
destruct (Pb (a + Z.of_nat j)) eqn:E; [exact (Hin j Hj E)|].
destruct (Hout j Hj E) as [A N]. rewrite A, N. exact (proj1 (rm_bytes_aview rsegs H mem a l) Hb j Hj).
Qed.
End m.

(* ======================================== the record ======================================== *)
Lemma w5_find_none : forall (f : Z * pval -> bool) ps, existsb f ps = false -> find f ps = None.
Proof.
intros f ps. induction ps as [|x ps IH]; cbn; [reflexivity|].
intros H. apply orb_false_iff in H as [H1 H2]. rewrite H1. exact (IH H2).
Qed.
Lemma w5_find_some : forall (f : Z * pval -> bool) ps, existsb f ps = true -> exists x, find f ps = Some x.
Proof.
intros f ps. induction ps as [|x ps IH]; cbn; [discriminate|].
intros H. destruct (f x) eqn:E; [exists x; reflexivity|]. apply IH. exact H.
Qed.
Lemma w5_first1 : forall ps, rs_first ps = 1 -> first_params ps = None.
Proof.
intros ps H. unfold rs_first in H. unfold first_params.
destruct (existsb (fun kv => fst kv =? POD_PROP_PARAMS) ps) eqn:E; cbn in H; [discriminate|].
rewrite (w5_find_none _ ps E). reflexivity.
Qed.
Lemma w5_first0 : forall ps, rs_first ps <> 1 -> exists v, first_params ps = Some v.
Proof.
intros ps H. unfold rs_first in H. unfold first_params.
destruct (existsb (fun kv => fst kv =? POD_PROP_PARAMS) ps) eqn:E; cbn in H; [|lia].
destruct (w5_find_some _ ps E) as (x & Hx). rewrite Hx. exists (snd x). reflexivity.
Qed.
Lemma w5_first_range : forall ps, rs_first ps = 0 \/ rs_first ps = 1.
Proof. intros ps. unfold rs_first. destruct (negb _); cbn; lia. Qed.
Lemma w5_plen_lo : forall sh ps, sh <> 7 -> 16 <= rs_plen sh ps.
Proof.
intros sh ps Hsh. unfold rs_plen, pc_buf, body_bytes, hdr_bytes, open_bytes. cbn [pc_shape pc_props pc_open].
replace (sh =? 7) with false by (symmetry; apply Z.eqb_neq; exact Hsh).
rewrite !app_nil_r, !zlen_app, !zlen_le32. pose proof (Zle_0_nat (length (flat_map (prop_bytes sh) ps))). lia.
Qed.
Lemma w5_buf_open_len : forall sh ps es,
Z.of_nat (length (pc_buf (PbCut sh ps (Some es)))) =
rs_plen sh ps + 16 + Z.of_nat (length (flat_map enc_pod es)).
Proof.
intros sh ps es. unfold rs_plen, pc_buf, open_bytes. cbn [pc_shape pc_props pc_open].
rewrite app_nil_r, !zlen_app, !zlen_le32. lia.
Qed.

Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Variable B : asyms.
Variable MT : ameter_ops.
Hypothesis MTL : ameter_laws MT.

Lemma w5_at_reg : forall H mem regs e (L : list (rl_loc * Z)) r v,
rs_at rsegs H mem regs e L -> In (LReg r, v) L -> getr regs (Z_to_bv 5 r) = w64 v.
Proof. intros H mem regs e L r v HL Hin. exact (proj1 (Forall_forall _ _) HL _ Hin). Qed.
Lemma w5_at_cell : forall H mem regs e (L : list (rl_loc * Z)) o v,
rs_at rsegs H mem regs e L -> In (LCell XR o, v) L ->
val_mem rsegs (mrestrict H mem) (e_R e + o) 8 (v mod 2 ^ 64).
Proof. intros H mem regs e L o v HL Hin. exact (proj1 (Forall_forall _ _) HL _ Hin). Qed.

(* the cut's segment frame across a piece *)
Lemma w5_core_post : forall cx (E1 Ep : Z -> Prop) ly2 S2 W2 regs2 mem2 md2 pc clob
  (R : world rsegs -> bvmap 5 word -> (word -> option byte) -> Prop) W3 c3,
  rs_core rsegs B MT cx E1 ly2 S2 W2 regs2 mem2 md2 ->
  (forall a, Ep a -> E1 a) ->
  (forall r, (r = 2 \/ r = 3 \/ r = 4) -> ~ In (Z_to_bv 5 r) clob) ->
  w5_post B MT (x_STK _ cx) (x_sp0 _ cx) (x_FP _ cx) (x_ly _ cx) (x_S _ cx) (x_W0 _ cx) (x_mem0 _ cx) (x_md0 _ cx) (x_own _ cx)
    (x_k _ cx) regs2 ly2 S2 W2 mem2 md2 pc clob Ep R W3 c3 ->
  exists ly3 S3 regs3 mem3 md3, c3 = cfg_at rsegs pc regs3 mem3 md3 /\
    rs_core rsegs B MT cx E1 ly3 S3 W3 regs3 mem3 md3 /\
    (forall r : bv 5, bv_unsigned r <> 0 -> ~ In r clob -> getr regs3 r = getr regs2 r) /\
    (forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs2 - T_SEG_STK <= a < spZ regs2) -> ~ Ep a ->
     aview rsegs (w_H W3) mem3 a = aview rsegs (w_H W2) mem2 a) /\
    R W3 regs3 mem3.
Proof using MTL.
intros cx E1 Ep ly2 S2 W2 regs2 mem2 md2 pc clob R W3 c3 Hcore HE Hc
  (ly3 & S3 & regs3 & mem3 & md3 & Hcfg & HJ3 & Hregs & Hfr & Hperm & Hio & Hmo & Hmem & HR).
destruct Hcore as (HJ2 & Hr234 & Hfr2 & Hperm2 & Hio2 & Hmo2 & Hmem2).
assert (Hsp : spZ regs2 = spZ (x_regs _ cx)).
{ unfold spZ. rewrite <- !(w5_getr5 _ 2%bv 2) by reflexivity. rewrite (Hr234 2); [reflexivity | lia]. }
exists ly3, S3, regs3, mem3, md3. split; [exact Hcfg|].
split.
{ split; [exact HJ3|]. split.
  { intros r Hr. rewrite Hregs; [apply Hr234; exact Hr| |apply Hc; exact Hr].
    rewrite Z_to_bv_unsigned. unfold bv_wrap. destruct Hr as [-> | [-> | ->]]; vm_compute; discriminate. }
  split; [rewrite Hfr; exact Hfr2|].
  split; [eapply Permutation_trans; [exact Hperm | exact Hperm2]|].
  split; [eapply same_io_trans; [exact Hio2 | exact Hio]|].
  split; [exact (mo_le_trans MT MTL _ _ _ _ _ Hmo2 Hmo)|].
  intros a Ha Hst HnE. rewrite (Hmem a Ha); [apply Hmem2; assumption | rewrite Hsp; exact Hst |].
  intros HEp. exact (HnE (HE a HEp)). }
split; [exact Hregs|]. split; [exact Hmem | exact HR].
Qed.
End b.

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
Local Arguments x_e {segs} _.
Local Arguments x_pos {segs} _.

(* membership in a cut's (location, value) list, and a register outside a clobber list *)
Ltac w5_in := cbn [rs_L_KEY rs_L_pod rs_Rc rs_Rc0 rs_Kc rs_cur2 app In fst snd]; repeat (first [left; reflexivity | right]).
Ltac w5_notin :=
let H := fresh "H" in intros H; cbn [In] in H;
repeat (destruct H as [H|H]; [apply (f_equal (@bv_unsigned 5)) in H; vm_compute in H; discriminate H|]); exact H.
(* a location of the end cut that the piece kept: from the start cut's list Hat, its register outside the clobber
   list (Hkeep) or its 8 bytes in a range the piece did not write (Kc) *)
Ltac w5_kept Hat Hkeep Kc := lazymatch goal with |- rl_at _ _ _ _ _ ?l ?v =>
  apply (rm_at_kept rsegs _ _ _ _ _ _ _ l v (proj1 (Forall_forall _ _) Hat (l, v) ltac:(w5_in)));
  cbn [rm_keeps rl_xv];
  first [ apply Hkeep; [vm_compute; discriminate | w5_notin]
        | let j := fresh "j" in let Hj := fresh "Hj" in intros j Hj; apply Kc; lia ] end.

(* ======================================== the segment's start ======================================== *)
Section s. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Variable B : asyms.
Hypothesis LAWS : AR_laws rsegs B.
(* the real frame, the frame for locals and the first block, as the segment's start fixes them *)
Lemma w5_pre_facts : forall cx, rs_pre rsegs B cx ->
  x_sp0 cx - x_STK cx <= e_R (x_e cx) - T_SEG_STK /\ e_R (x_e cx) + 0x1a0 <= x_sp0 cx /\
  e_R (x_e cx) mod 16 = 0 /\ getr (x_regs cx) 2 = w64 (e_R (x_e cx)) /\
  alloc_ceiling + T_SEG_STK <= e_R (x_e cx) /\ x_sp0 cx <= 2 ^ 47 /\
  In (e_pp (x_e cx), Layout.PP_SIZE) (ablocks B (x_lyc cx) (x_Sc cx)) /\
  ~ In (e_pp (x_e cx), Layout.PP_SIZE) (ablocks B (x_ly cx) (x_S cx)) /\
  4096 <= e_pp (x_e cx) /\ e_pp (x_e cx) + Layout.PP_SIZE <= alloc_ceiling /\
  4096 <= e_F (x_e cx) /\ e_F (x_e cx) + 512 <= alloc_ceiling /\ in_app (e_pp (x_e cx)) Layout.PP_SIZE.
Proof using LAWS.
intros cx Hpre. unfold rs_pre, rl_seg_pre in Hpre.
destruct Hpre as (HJ & Hev & H2 & H3 & H4 & HS & HR16 & HRs & HRstk & Hown & HF & Hfsh & Hpp0 & Hpp & Hfl & Hro &
  Hglobs & Hrz & Hstrs & Hcells & Hrom & Hout).
pose proof HJ as (HAR & _ & _ & _ & _ & Hfrs & _).
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstk & _).
destruct Hstk as (Hal & HST0 & Hceil & Hslo & Hshi & H47 & _).
pose proof (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR Hpp) as (_ & Hp4096 & Hpceil & Happ & _).
assert (Hrq : req_size Layout.PP_SIZE = Layout.PP_SIZE) by reflexivity. rewrite Hrq in Hpceil, Happ.
assert (Hin : In (hi_cid role_himg_A, x_pos cx) (frames (x_Sc cx))) by (rewrite Hfrs; apply in_or_app; left; exact Hown).
pose proof (frames_bounds rsegs B LAWS _ _ _ _ _ _ _ HAR Hin) as (F1 & F2 & _).
rewrite <- HF in F1, F2. cbn [hi_cid role_himg_A] in F2. change (fs_frame_bytes 3) with 512 in F2.
pose proof asan_consts as (C1 & _). cbn [hi_rsz role_himg_A] in HRs.
unfold T_SEG_STK, ASTACK in *.
split; [lia|]. split; [lia|]. split; [exact HR16|]. split; [exact H2|]. split; [lia|]. split; [lia|].
split; [exact Hpp|]. split; [exact Hout|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. exact Happ.
Qed.
End s.

(* ======================================== the first block's image ======================================== *)
Section i. Context {fx : YK11.FPState}.
(* buf[0..len) of an image *)
Lemma w5_img_buf : forall H mem pp b isp hp pst es corr,
rm_bytes rsegs H mem pp (pp_image b isp hp pst es corr) -> rm_bytes rsegs H mem pp b.
Proof. intros H mem pp b isp hp pst es corr Hb. rewrite pp_image_tail in Hb. apply rm_bytes_app in Hb as [Hb _]. exact Hb. Qed.
(* the two flag words of an image, carried to a state that keeps them *)
Lemma w5_img_flags : forall H mem H' mem' pp b isp hp pst es corr,
Z.of_nat (length b) <= POD_BUF_MAX -> (length es <= 32)%nat -> Forall (fun e => (length (e_body e) <= 96)%nat) es ->
rm_bytes rsegs H mem pp (pp_image b isp hp pst es corr) ->
(forall y, pp + OFF_HAS_PARAMS <= y < pp + OFF_ENT -> aview rsegs H' mem' y = aview rsegs H mem y) ->
rm_bytes rsegs H' mem' (pp + OFF_HAS_PARAMS) (le32 (Z.b2z hp)) /\
rm_bytes rsegs H' mem' (pp + OFF_PARAMS_STRUCT) (le32 (Z.b2z pst)).
Proof.
intros H mem H' mem' pp b isp hp pst es corr Hb He Hs Old K.
pose proof (rm_pp_has_params rsegs b isp hp pst es corr Hb He Hs H mem pp Old) as V1.
pose proof (rm_pp_params_struct rsegs b isp hp pst es corr Hb He Hs H mem pp Old) as V2.
split; (eapply rm_bytes_kept; [apply rm_bytes_of_val; eassumption|]);
  intros y Hy; rewrite ?length_le32, ?length_Z_to_le_bytes in Hy; apply K; unfold OFF_HAS_PARAMS, OFF_PARAMS_STRUCT, OFF_ENT in *; lia.
Qed.
(* an image rebuilt from its parts: buf[0..len) grown or patched (b'), len, the two flag words, every other byte
   kept from the old image (the zeros after b', is_props, the entries and what follows them) *)
Lemma w5_img_gen : forall H mem H' mem' pp b b' isp hp pst hp' pst' es corr,
(length b <= length b')%nat -> Z.of_nat (length b') <= POD_BUF_MAX -> (length es <= 32)%nat ->
Forall (fun e => (length (e_body e) <= 96)%nat) es ->
rm_bytes rsegs H mem pp (pp_image b isp hp pst es corr) ->
rm_bytes rsegs H' mem' pp b' ->
val_mem rsegs (mrestrict H' mem') (pp + OFF_LEN) 8 (Z.of_nat (length b')) ->
rm_bytes rsegs H' mem' (pp + OFF_HAS_PARAMS) (le32 (Z.b2z hp')) ->
rm_bytes rsegs H' mem' (pp + OFF_PARAMS_STRUCT) (le32 (Z.b2z pst')) ->
(forall y, pp + Z.of_nat (length b') <= y < pp + OFF_LEN \/ pp + OFF_IS_PROPS <= y < pp + OFF_HAS_PARAMS \/
  pp + OFF_ENT <= y < pp + PP_SIZE -> aview rsegs H' mem' y = aview rsegs H mem y) ->
rm_bytes rsegs H' mem' pp (pp_image b' isp hp' pst' es corr).
Proof.
intros H mem H' mem' pp b b' isp hp pst hp' pst' es corr Hbb Hb' He Hs Old Nb Nlen Nh Np K.
assert (Hb : Z.of_nat (length b) <= POD_BUF_MAX) by lia.
pose proof (length_pp_image b isp hp pst es corr Hb He Hs) as LI.
rewrite pp_image_tail in LI, Old |- *. unfold pp_tail in LI, Old |- *.
remember (flat_map ent_mem es ++ zeros (Z.to_nat (ENT_SIZE * (POD_ENT_MAX - Z.of_nat (length es))))
  ++ le32 (Z.of_nat (length es)) ++ le32 (Z.b2z corr) ++ zeros 4) as T eqn:ET.
clear ET.
assert (Ez : zeros (Z.to_nat (POD_BUF_MAX - Z.of_nat (length b)))
  = zeros (length b' - length b) ++ zeros (Z.to_nat (POD_BUF_MAX - Z.of_nat (length b')))).
{ rewrite <- zeros_app. f_equal. unfold POD_BUF_MAX in *. lia. }
rewrite Ez in Old, LI. rewrite <- app_assoc in Old.
rewrite !length_app, !length_zeros, length_le64, !length_le32 in LI.
unfold PP_SIZE, POD_BUF_MAX in *.
apply rm_bytes_app in Old as [_ Old]. apply rm_bytes_app in Old as [_ Old].
apply rm_bytes_app in Old as [Ozk Old]. apply rm_bytes_app in Old as [_ Old].
apply rm_bytes_app in Old as [Oi Old]. apply rm_bytes_app in Old as [_ Old].
apply rm_bytes_app in Old as [_ OT].
repeat (first [rewrite length_zeros in Ozk | rewrite length_zeros in Oi | rewrite length_zeros in OT |
  rewrite length_le64 in Oi | rewrite length_le64 in OT | rewrite length_le32 in OT]).
apply rm_bytes_app. split; [exact Nb|].
apply rm_bytes_app. split.
{ eapply rm_bytes_kept.
  - replace (pp + Z.of_nat (length b')) with (pp + Z.of_nat (length b) + Z.of_nat (length b' - length b)) by lia.
    exact Ozk.
  - intros y Hy. rewrite length_zeros in Hy. apply K. left. unfold OFF_LEN. lia. }
rewrite length_zeros.
apply rm_bytes_app. split.
{ unfold le64. apply rm_bytes_of_val.
  replace (pp + Z.of_nat (length b') + Z.of_nat (Z.to_nat (16384 - Z.of_nat (length b')))) with (pp + OFF_LEN)
    by (unfold OFF_LEN; lia). exact Nlen. }
rewrite length_le64.
apply rm_bytes_app. split.
{ eapply rm_bytes_kept.
  - replace (pp + Z.of_nat (length b') + Z.of_nat (Z.to_nat (16384 - Z.of_nat (length b'))) + Z.of_nat 8)
      with (pp + Z.of_nat (length b) + Z.of_nat (length b' - length b) +
            Z.of_nat (Z.to_nat (16384 - Z.of_nat (length b'))) + Z.of_nat 8) by lia.
    exact Oi.
  - intros y Hy. rewrite length_le32 in Hy. apply K. right. left. unfold OFF_IS_PROPS, OFF_HAS_PARAMS. lia. }
rewrite length_le32.
apply rm_bytes_app. split.
{ replace (pp + Z.of_nat (length b') + Z.of_nat (Z.to_nat (16384 - Z.of_nat (length b'))) + Z.of_nat 8 + Z.of_nat 4)
    with (pp + OFF_HAS_PARAMS) by (unfold OFF_HAS_PARAMS; lia). exact Nh. }
rewrite length_le32.
apply rm_bytes_app. split.
{ replace (pp + Z.of_nat (length b') + Z.of_nat (Z.to_nat (16384 - Z.of_nat (length b'))) + Z.of_nat 8 + Z.of_nat 4
    + Z.of_nat 4) with (pp + OFF_PARAMS_STRUCT) by (unfold OFF_PARAMS_STRUCT; lia). exact Np. }
rewrite length_le32.
eapply rm_bytes_kept.
- replace (pp + Z.of_nat (length b') + Z.of_nat (Z.to_nat (16384 - Z.of_nat (length b'))) + Z.of_nat 8 + Z.of_nat 4
    + Z.of_nat 4 + Z.of_nat 4)
    with (pp + Z.of_nat (length b) + Z.of_nat (length b' - length b) +
          Z.of_nat (Z.to_nat (16384 - Z.of_nat (length b'))) + Z.of_nat 8 + Z.of_nat 4 + Z.of_nat 4 + Z.of_nat 4) by lia.
  exact OT.
- intros y Hy. apply K. right. right. unfold OFF_ENT. lia.
Qed.

(* the recorded pods of a cut: at most 32, each body at most 96 bytes *)
Lemma w5_ents_bounds : forall sh ps o, rs_wf sh ps ->
(match o with Some es => Forall ent_wf es /\ (length es <= 32)%nat | None => True end) ->
(length (pc_ents (PbCut sh ps o)) <= 32)%nat /\ Forall (fun e => (length (e_body e) <= 96)%nat) (pc_ents (PbCut sh ps o)).
Proof.
intros sh ps o (Hs & Hk & He & Hl) Ho.
assert (Hbody : forall l, Forall ent_wf l -> Forall (fun e => (length (e_body e) <= 96)%nat) l).
{ intros l Hl'. eapply Forall_impl; [|exact Hl']. intros e (_ & Hb & Hz). rewrite Hb. lia. }
unfold pc_ents. cbn [pc_props pc_open].
destruct (first_params ps) as [[iv|es']|] eqn:E.
- split; [cbn; lia | constructor].
- unfold first_params in E. destruct (find _ _) as [kv|] eqn:F; [|discriminate]. cbn in E. injection E as E.
  apply find_some in F as [Hin _].
  rewrite Forall_forall in Hk. destruct (Hk kv Hin) as [_ Hv']. rewrite E in Hv'. cbn in Hv'.
  split; [exact Hv'|]. apply Hbody.
  apply all_ents_Forall in He. rewrite Forall_forall in He. specialize (He kv Hin). rewrite E in He. exact He.
- destruct o as [es|]; [destruct Ho as [Ho1 Ho2]; split; [exact Ho2 | apply Hbody; exact Ho1] |
  split; [cbn; lia | constructor]].
Qed.
(* the image at the Struct's close (Model.pc_buf_close; pod.h:434-438): the size word patched, and the two flag
   words set when this Struct is the first params property *)
Lemma w5_img_close_eq : forall sh ps es, sh <> 7 ->
pc_image (PbCut sh (ps ++ [(POD_PROP_PARAMS, PStruct es)]) None) =
pp_image (overwrite (pc_buf (PbCut sh ps (Some es))) (Z.to_nat (rs_at_of sh ps))
           (le32 (Z.of_nat (length (pc_buf (PbCut sh ps (Some es)))) - rs_at_of sh ps - 8)))
  (is_props (PodRec sh ps None))
  (has_params (PodRec sh ps None) || (rs_first ps =? 1))
  (params_struct (PodRec sh ps None) || (rs_first ps =? 1))
  (pc_ents (PbCut sh ps (Some es))) false.
Proof.
intros sh ps es Hsh. unfold pc_image. cbn [pc_shape pc_props pc_open].
change (pc_buf (PbCut sh (ps ++ [(POD_PROP_PARAMS, PStruct es)]) None))
  with (pc_buf (pc_close (PbCut sh ps (Some es)))).
rewrite <- (pc_buf_close sh ps es Hsh).
replace (Z.to_nat (rs_at_of sh ps)) with (length (pc_buf (PbCut sh ps None)) + 8)%nat
  by (unfold rs_at_of, rs_plen; lia).
replace (Z.of_nat (length (pc_buf (PbCut sh ps (Some es)))) - rs_at_of sh ps - 8)
  with (Z.of_nat (length (pc_buf (PbCut sh ps (Some es)))) - Z.of_nat (length (pc_buf (PbCut sh ps None))) - 16)
  by (unfold rs_at_of, rs_plen; lia).
unfold has_params, params_struct, pc_ents. cbn [p_props pc_props pc_open]. rewrite first_params_app.
destruct (Z.eqb_spec (rs_first ps) 1) as [E|E].
- rewrite (w5_first1 ps E). cbn [fst snd]. rewrite Z.eqb_refl. reflexivity.
- destruct (w5_first0 ps E) as [v Hv]. rewrite Hv.
  destruct v; reflexivity.
Qed.
End i.
