(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: ported from proofs/cgif/cgif_file_fuzzer/lib/A/AChd.v (entry state, region and fact proofs, the run/branch loop and its leaf) with the caller-journal leaf of lib/A/ACeu.v rfc_A_ok, aview_frame_off of lib/A/AD28.v (as kept_step) and frm_off_img of lib/A/ACeh.v (as frame_not_img) at c8557374ad2e to libreac/fuzz_knock: lib_asan3_0_listing -> knock_asan_listing, AF_asan3_cmpPixel -> AF_asan_reac_knock_step, tcmp_spec / tcmp_post -> tknock_step_specX / kn_post_step of lib/A/APgCSpec.v, cmp_entry / cmp_regions / cmp_facts / ss_cmp / cmp_SH / cmp_extra / EC / CBx / CBspan / pb_cmpPixel -> step_entry / step_regions / step_facts / ss_step / step_SH / step_extra / EK / KBx / KBspan / pb_knock_stepX; constants: TCMP_STK 16 + ESTACK -> T_step_STK 16, shadow-base atom 42 -> 39, GOT shadow slot / shadow-base cell A_OBJ 0 / A_OBJ 12 -> A_OBJ 1 / A_OBJ 7 (lib/Reusable/YC1f.v got_regionP / bcell_regionP / PALib), image bounds only through lib/Reusable/YImgTop.v (knock's 0x10000 .. 0x5f3000); the struct kp lies in a caller frame (cid, pos) of any class, written through awr_byte's in_frames case by In (cid, pos) own. *)
(* Modified by Theorem Labs, 2026-10: made from proofs/reac-pw/fuzz_qdisc/lib/A/QPgCheck.v at 236fd9c95ca (itself made from proofs/libreac/fuzz_knock/lib/A/APgStep.v at origin/ossv/recipes 6ebe35ba632: the save-slot region, its write obligation awr_stk / kwr_stk, the run / keep / leaf chain) with the kit-only plumbing of lib/A/RPgCfgChanges.v at 964efd2f474 (the image's own code table, cfg_wx / cfg_segs_low, kept_run, the leaf into lib/A/RPgCSpec.v's rl_post) for reac-pw/fuzz_role's image A (fuzz_role.asan): it walks check_absent 0x82bb4, check_role 0x82bdc and check_malformed 0x82c04 against rl_check_absent_specX / rl_check_role_specX / rl_check_malformed_specX on the concrete image lib/A/Img0.v rsegs; the entry state carries the registers the contract fixes (a0, a1, and a2 = a1 for check_role) as literals or as the atom they equal, so the engine decides every abort branch itself; qdisc's divisor-constant region, its arithmetic lemmas and its branch splits are dropped. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_role/lib/A/RPgCheck.v at 77f59d02b018 for reac-pw/fuzz_rate's
   image A (fuzz_rate.asan): module paths changed; the image is images.Asan's loaded segments instead of a lib/A/Img0
   module; the contracts are lib/A/RtPgCSpec.v's rt_check_absent_specX / rt_check_rate_specX / rt_check_malformed_specX
   (rt_cpre / rt_cpost, the same texts as role's rl_pre / rl_post) at rate's addresses; check_absent's and
   check_malformed's second literal is 0x5a5a5a5a (`lui` + `addiw`) where role's is 0x5a; check_decide (a0 = a1, the
   override a1 := the atom of a0) is added; the code table covers the four functions; the call-cut plumbing of
   proofs/reac-pw/fuzz_role/lib/A/RPgCheckStr.v at 77f59d02b018 (cs_eq, cs_eq_trans, cs_eq_of_pres, cs_eq_of_st_ok,
   sp_of_st_ok, L_ANS, L_ANS_cs, pres_of_cs) is added for the walks with a call. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_rate/lib/A/RtPgCheck.v; 692 of its 736 lines of code are new or changed and 246 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_rate/lib/A/RtPgEnt0Hd.v, with its module paths and module names changed; 199 of its 356 lines of code are new or changed and 579 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_role/lib/A/RPgEnt0Hd.v at 97ea9c9eafa (its cut-side
   lemmas hd_at_move, hd_keep2, hd_keep1, hd_mem2, hd_zero_kept, hd_fsh_two, hd_core_step, hd_E1, hd_base_move,
   hd_cut_facts, hd_build_common, hd_build_DIG, hd_build_ODD, hd_sh_not_row, hd_suffix_tl) for reac-pw/fuzz_headamp's
   image B: restated over lib/AU/HPgSeg.v's cuts at headamp_himg_B (class-4 frame of 1024 bytes, M01's write ranges
   [F+0x20, F+0x278), [shF, shF+116), [R, R+0x198)), the arm cuts of lib/AU/HPgE0Def.v (R+0x110 = the cursor,
   t1 = what is left, s2 = &ch, s10 = p, a3 = c) and the shadow patterns of lib/AU/HPgMem.v (hmu_sh). *)
(* reac-pw/fuzz_headamp image B (fuzz_headamp.asan-ubsan, pinned sha256
   53edda9bdeeba1803865babfecb1af6732babe47ab83c64d38cc59a90d717a94; every address measured on the unstripped twin
   1674e30a0698f381704e66d2398d7906c881f4ba8fc619cb41b89fb97ad112ff, same loaded bytes except .note.gnu.build-id): the bridges between the
   cuts of ent_build's case 0 in LLVMFuzzerTestOneInput 0x80c40 (HPgSeg.hsu_cut_D / hsu_cut_D0E at the entries,
   HPgE0Def.e0_cut_DIG / e0_cut_ODD at the two arms) and the block lemmas of lib/AU/HPgE0HdB.v. Proves no function
   (kind: segment lemma).
   eh_base_ctx: the block context (HPgE0HdB.eh_ctx) of a cut inside the pod loop, and where F and pp lie.
   eh_build_DIG / eh_build_ODD: the arm's cut from the entry's cut and what the head's blocks did: the journal at
   the entry's state, every register outside eh_clob kept (s0 = S, s1 = R, s3 = shF, s11 = K, s8 = the multiplier,
   s6 = &r, s9 = &t are none of them), every byte outside the head's writes (t's twelve and ch's three shadow bytes,
   the cell R+0x110) kept, those writes (t and ch in scope, R+0x110 = the cursor after c and p), and the arm's
   registers t1 (x6), s2 (x18) = F + 0xa0, s10 (x26) = p, a3 (x13) = c and, at DIG, t0 (x5) = 4, t3 (x28) = 9,
   t2 (x7) = 10, s7 (x23) = -8. *)
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YN3v YI04 YI09 YI08.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YG0v YI00 YI0m.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YI16 YM05 YO09 YG0q.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Pod Require Import Cursor Model Layout Accessors Spa Tables.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.A Require Import HPgBase HPgCSpec.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.AU Require Import Img0U HPgImgB HPgSteps HPgMem HPgSeg.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.AU Require Import HPgE0Def HPgE0Base HPgCaseBJ HPgE0HdB.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.
(* the cut record's projections, with the segments implicit *)
Local Arguments x_STK {segs} _. Local Arguments x_sp0 {segs} _. Local Arguments x_FP {segs} _.
Local Arguments x_ly {segs} _. Local Arguments x_S {segs} _. Local Arguments x_W0 {segs} _.
Local Arguments x_mem0 {segs} _. Local Arguments x_md0 {segs} _. Local Arguments x_own {segs} _.
Local Arguments x_k {segs} _. Local Arguments x_regs {segs} _. Local Arguments x_lyc {segs} _.
Local Arguments x_Sc {segs} _. Local Arguments x_W {segs} _. Local Arguments x_memc {segs} _.
Local Arguments x_mdc {segs} _. Local Arguments x_RLO {segs} _. Local Arguments x_RHI {segs} _.
Local Arguments x_e {segs} _. Local Arguments x_pos {segs} _.

(* every register any block of the head writes *)
Definition eh_clob : list (bv 5) := [5; 6; 7; 10; 11; 12; 13; 16; 18; 20; 21; 26; 28]%bv.

(* a register outside a concrete clobber list *)
Ltac eh_notin :=
let H := fresh "H" in intros H; cbn [In eh_clob] in H;
repeat (destruct H as [H|H]; [apply (f_equal (@bv_unsigned 5)) in H; vm_compute in H; discriminate H|]); exact H.
(* a register a block kept: rewrite with its keep clause Hk, then close with R *)
Ltac eh_kr Hk R := rewrite Hk; [exact R | cbv; discriminate | eh_notin].
(* one clobber list inside another *)
Ltac eh_sub := let q := fresh "q" in let X := fresh "X" in
intros q X; cbn [In eh_clob] in X |- *; tauto.

Lemma eh_sh_not_row : forall F x, F mod 8 = 0 -> ~ (F + 0x20 <= x < F + 0x278) ->
~ (shadow_addr F + 4 <= shadow_of_addr SHADOW_OFF x < shadow_addr F + 23).
Proof.
intros F x HF Hx Hin. unfold shadow_addr, shadow_of_addr in Hin.
pose proof (Z.div_mod x 8 ltac:(lia)) as Dx. pose proof (Z.mod_pos_bound x 8 ltac:(lia)) as Mx.
pose proof (Z.div_mod F 8 ltac:(lia)) as DF. rewrite HF in DF. lia.
Qed.
Lemma eh_suffix_tl : forall (rest r : list byte) x, hsu_suffix rest (x :: r) -> hsu_suffix rest r.
Proof.
intros rest r x (j & Hj & E). exists (S j). split.
- destruct (Nat.le_gt_cases (length rest) j) as [Hle|Hlt]; [|lia].
  rewrite skipn_all2 in E by exact Hle. discriminate E.
- change (S j) with (1 + j)%nat. rewrite <- skipn_skipn, <- E. reflexivity.
Qed.
Lemma eh_suffix_nil : forall (rest : list byte), hsu_suffix rest [].
Proof. intros rest. exists (length rest). split; [lia | rewrite skipn_all; reflexivity]. Qed.
Lemma eh_fal : forall n ly ly' cid pos, layout_le n ly ly' -> frame_addr ly' cid pos = frame_addr ly cid pos.
Proof. intros n ly ly' cid pos Hle. unfold frame_addr. destruct Hle as (_ & _ & _ & _ & _ & EF & _). rewrite EF. reflexivity. Qed.

(* a byte of the real frame outside the cursor cell is none of the head's writes *)
Lemma eh_cell_out : forall R F x, 2 ^ 46 <= R -> shadow_addr F + 128 <= 0x7fff8000 + 2 ^ 44 -> R <= x ->
~ (R + 0x110 <= x < R + 0x118) -> ~ eh_wTCN R F x.
Proof. intros R F x H1 H2 H3 H4. unfold eh_wTCN, eh_wT, eh_wCh, eh_wN. lia. Qed.
(* a byte below the shadow band or above it, and below the ceiling C under R, is none of the head's writes *)
Lemma eh_app_out : forall C R F x, C + T_SEG_STK <= R -> 0x7fff8000 <= shadow_addr F ->
shadow_addr F + 128 <= 0x7fff8000 + 2 ^ 44 ->
(x < 0x7fff8000 \/ 0x7fff8000 + 2 ^ 44 <= x) -> x < C -> ~ eh_wTCN R F x.
Proof.
intros C R F x H1 H2 H3 H4 H5. unfold eh_wTCN, eh_wT, eh_wCh, eh_wN.
assert (0 <= T_SEG_STK) by (unfold T_SEG_STK, ASTACK; lia). lia.
Qed.

Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section d.
Variable B : asyms.
Variable MT : ameter_ops.

(* ======================================== moving facts across blocks ======================================== *)
Lemma eh_at_get : forall H mem regs e (L : list (hd_loc * Z)) l v,
hsu_at rsegs H mem regs e L -> In (l, v) L -> hd_at rsegs H mem regs e l v.
Proof. intros H mem regs e L l v HL Hin. exact (proj1 (Forall_forall _ _) HL (l, v) Hin). Qed.
Lemma eh_at_move : forall H mem regs mem' regs' e L,
hsu_at rsegs H mem regs e L -> Forall (fun f => hm_keeps rsegs H mem H mem' regs regs' e (fst f)) L ->
hsu_at rsegs H mem' regs' e L.
Proof.
intros H mem regs mem' regs' e L HL HK. unfold hsu_at in *.
induction L as [|[l v] L IH]; [constructor|].
inversion HL as [|? ? H1 H2]; subst. inversion HK as [|? ? K1 K2]; subst.
constructor; [|apply IH; assumption].
exact (hm_at_kept rsegs _ _ _ _ _ _ _ _ _ H1 K1).
Qed.
Lemma eh_keep2 : forall (r2 r3 r4 : bvmap 5 word) (c1 c2 c : list (bv 5)),
(forall q : bv 5, bv_unsigned q <> 0 -> ~ In q c1 -> getr r3 q = getr r2 q) ->
(forall q : bv 5, bv_unsigned q <> 0 -> ~ In q c2 -> getr r4 q = getr r3 q) ->
(forall q, In q c1 \/ In q c2 -> In q c) ->
forall q : bv 5, bv_unsigned q <> 0 -> ~ In q c -> getr r4 q = getr r2 q.
Proof.
intros r2 r3 r4 c1 c2 c K1 K2 Hs q Hq Hn.
rewrite (K2 q Hq ltac:(intros X; apply Hn, Hs; right; exact X)),
  (K1 q Hq ltac:(intros X; apply Hn, Hs; left; exact X)). reflexivity.
Qed.
Lemma eh_keep1 : forall (r2 r3 : bvmap 5 word) (c1 : list (bv 5)),
(forall q : bv 5, bv_unsigned q <> 0 -> ~ In q c1 -> getr r3 q = getr r2 q) ->
(forall q, In q c1 -> In q eh_clob) ->
forall q : bv 5, bv_unsigned q <> 0 -> ~ In q eh_clob -> getr r3 q = getr r2 q.
Proof. intros r2 r3 c1 K1 Hs q Hq Hn. exact (K1 q Hq (fun X => Hn (Hs q X))). Qed.
Lemma eh_mem2 : forall H m2 m3 m4 (W1 W2 Wt : Z -> Prop),
(forall a, 0 <= a < 2 ^ 64 -> ~ W1 a -> aview rsegs H m3 a = aview rsegs H m2 a) ->
(forall a, 0 <= a < 2 ^ 64 -> ~ W2 a -> aview rsegs H m4 a = aview rsegs H m3 a) ->
(forall a, W1 a \/ W2 a -> Wt a) ->
forall a, 0 <= a < 2 ^ 64 -> ~ Wt a -> aview rsegs H m4 a = aview rsegs H m2 a.
Proof.
intros H m2 m3 m4 W1 W2 Wt K1 K2 Hs a Ha Hn.
rewrite (K2 a Ha ltac:(intros X; apply Hn, Hs; right; exact X)),
  (K1 a Ha ltac:(intros X; apply Hn, Hs; left; exact X)). reflexivity.
Qed.
Lemma eh_zero_kept : forall W m m' F j n,
eh_zero W m F j n ->
(forall i, j <= i < j + n -> aview rsegs (w_H W) m' (shadow_addr F + i) = aview rsegs (w_H W) m (shadow_addr F + i)) ->
eh_zero W m' F j n.
Proof. intros W m m' F j n Z0 K i Hi. rewrite K by exact Hi. exact (Z0 i Hi). Qed.

(* the frame's shadow row after two scope stores of v *)
Lemma eh_fsh_two : forall H mem H' mem' F pat (j1 k1 j2 k2 : nat) v,
hd_fsh rsegs H mem F pat ->
(forall i, Z.of_nat j1 <= i < Z.of_nat (j1 + k1) -> aview rsegs H' mem' (shadow_addr F + i) = Some v) ->
(forall i, Z.of_nat j2 <= i < Z.of_nat (j2 + k2) -> aview rsegs H' mem' (shadow_addr F + i) = Some v) ->
(forall i, 0 <= i < Z.of_nat (length pat) -> ~ (Z.of_nat j1 <= i < Z.of_nat (j1 + k1)) ->
 ~ (Z.of_nat j2 <= i < Z.of_nat (j2 + k2)) ->
 aview rsegs H' mem' (shadow_addr F + i) = aview rsegs H mem (shadow_addr F + i)) ->
hd_fsh rsegs H' mem' F (hm_setn (hm_setn pat j1 k1 v) j2 k2 v).
Proof.
intros H mem H' mem' F pat j1 k1 j2 k2 v P S1 S2 K i Hi.
rewrite !hm_setn_len in Hi.
rewrite hm_nth_setn by (rewrite hm_setn_len; lia).
destruct ((j2 <=? Z.to_nat i)%nat && (Z.to_nat i <? j2 + k2)%nat) eqn:E2.
- apply andb_prop in E2 as [A1 A2]. apply Nat.leb_le in A1. apply Nat.ltb_lt in A2. apply S2. lia.
- rewrite hm_nth_setn by lia.
  destruct ((j1 <=? Z.to_nat i)%nat && (Z.to_nat i <? j1 + k1)%nat) eqn:E1.
  + apply andb_prop in E1 as [A1 A2]. apply Nat.leb_le in A1. apply Nat.ltb_lt in A2. apply S1. lia.
  + rewrite K; [exact (P i ltac:(lia)) | lia | |].
    * intros [A1 A2]. apply andb_false_iff in E1 as [E|E]; [apply Nat.leb_gt in E | apply Nat.ltb_ge in E]; lia.
    * intros [A1 A2]. apply andb_false_iff in E2 as [E|E]; [apply Nat.leb_gt in E | apply Nat.ltb_ge in E]; lia.
Qed.

(* ======================================== the cut's journal part ======================================== *)
Lemma eh_core_step : forall cx (Ew : Z -> Prop) ly2 S2 W2 regs2 mem2 md2 regs3 mem3 md3,
hsu_core rsegs B MT cx (hsu_E1 rsegs headamp_himg_B cx) ly2 S2 W2 regs2 mem2 md2 ->
ajournal rsegs B (x_STK cx) (x_sp0 cx) (x_FP cx) (x_ly cx) (x_S cx) (x_W0 cx) (x_mem0 cx) (x_md0 cx) (x_own cx)
  ly2 S2 W2 mem3 md3 (x_k cx) ->
(forall r : Z, r = 2 \/ r = 3 \/ r = 4 -> getr regs3 (Z_to_bv 5 r) = getr regs2 (Z_to_bv 5 r)) ->
same_io md2 md3 ->
(forall a, 0 <= a < 2 ^ 64 -> ~ Ew a -> aview rsegs (w_H W2) mem3 a = aview rsegs (w_H W2) mem2 a) ->
(forall a, Ew a -> hsu_E1 rsegs headamp_himg_B cx a) ->
hsu_core rsegs B MT cx (hsu_E1 rsegs headamp_himg_B cx) ly2 S2 W2 regs3 mem3 md3.
Proof.
intros cx Ew ly2 S2 W2 regs2 mem2 md2 regs3 mem3 md3 Hc HJ3 Hr3 Hio3 Hm3 HEw.
unfold hsu_core, hsu_mid in *. destruct Hc as (HJ & Hr & Hf & Hp & Hio & Hmo & Hm).
split; [exact HJ3|].
split; [intros r Hr'; rewrite (Hr3 r Hr'); exact (Hr r Hr')|].
split; [exact Hf|]. split; [exact Hp|].
split; [eapply same_io_trans; [exact Hio | exact Hio3]|].
split; [exact Hmo|].
intros a Ha Hs HE. rewrite <- (Hm a Ha Hs HE). apply Hm3; [exact Ha|]. intros HW. exact (HE (HEw a HW)).
Qed.
Lemma eh_E1 : forall cx a, eh_wTCN (e_R (x_e cx)) (e_F (x_e cx)) a -> hsu_E1 rsegs headamp_himg_B cx a.
Proof.
intros cx a Ha. left. unfold hd_inw. cbn [hi_w1 headamp_himg_B].
destruct Ha as [Ha|[Ha|Ha]]; cbv [eh_wT eh_wCh eh_wN] in Ha.
- apply Exists_cons_tl. apply Exists_cons_hd. cbn [hd_xv fst snd]. lia.
- apply Exists_cons_tl. apply Exists_cons_hd. cbn [hd_xv fst snd]. lia.
- apply Exists_cons_tl. apply Exists_cons_tl. apply Exists_cons_hd. cbn [hd_xv fst snd]. lia.
Qed.
Lemma eh_base_move : forall cx sh np ps cnt es rest rr r r' ly2 S2 W2 regs2 mem2 md2 ly3 S3 W3 regs3 mem3 md3,
hsu_pod_base rsegs B MT headamp_himg_B cx sh np ps cnt es rest rr r ly2 S2 W2 regs2 mem2 md2 ->
hsu_core rsegs B MT cx (hsu_E1 rsegs headamp_himg_B cx) ly3 S3 W3 regs3 mem3 md3 -> hsu_suffix rest r' ->
hsu_pod_base rsegs B MT headamp_himg_B cx sh np ps cnt es rest rr r' ly3 S3 W3 regs3 mem3 md3.
Proof.
intros cx sh np ps cnt es rest rr r r' ly2 S2 W2 regs2 mem2 md2 ly3 S3 W3 regs3 mem3 md3 (_ & Hin & _ & Hr) Hc Hs.
exact (conj Hc (conj Hin (conj Hs Hr))).
Qed.

(* a cut's context for the blocks, and where F and pp lie *)
Lemma eh_base_ctx : forall cx sh np ps cnt es rest rr r ly2 S2 W2 regs2 mem2 md2,
hsu_start_M01 rsegs B headamp_himg_B cx rest ->
hsu_pod_base rsegs B MT headamp_himg_B cx sh np ps cnt es rest rr r ly2 S2 W2 regs2 mem2 md2 ->
eh_ctx B (x_STK cx) (x_sp0 cx) (x_FP cx) (x_ly cx) (x_S cx) (x_W0 cx) (x_mem0 cx) (x_md0 cx) (x_own cx) (x_k cx)
  ly2 S2 W2 mem2 md2 (e_R (x_e cx)) (e_F (x_e cx)) (x_pos cx) /\
in_app (e_F (x_e cx)) 1024 /\ in_app (e_pp (x_e cx)) Layout.PP_SIZE /\
e_pp (x_e cx) + Layout.PP_SIZE <= alloc_ceiling.
Proof.
intros cx sh np ps cnt es rest rr r ly2 S2 W2 regs2 mem2 md2 Hst Hb.
pose proof (AR_laws_ok rsegs B) as LAWS.
destruct Hst as (Hpre & _).
destruct Hpre as (HJc & _ & _ & _ & _ & ES & ER32 & ERS & ESTK & Hown & EF & _ & _ & _ & _ & _ & _ & _ & _ & _ & _
  & Hfresh).
destruct Hfresh as (_ & Hppb & _).
destruct Hb as (Hcore & _). destruct Hcore as (HJ & _).
pose proof HJc as (HARc & Hlyc & _ & _ & _ & Hfrsc & _).
pose proof HJ as (_ & Hly & _).
cbn [hi_cid hi_rsz headamp_himg_B] in Hown, EF, ERS.
assert (Hin4 : In (4, x_pos cx) (frames (x_Sc cx))) by (rewrite Hfrsc; apply in_or_app; left; exact Hown).
destruct (frames_bounds rsegs B LAWS _ _ _ _ _ 4 (x_pos cx) HARc Hin4) as (_ & _ & HFapp).
destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HARc Hppb) as (_ & _ & Hp2 & Happ & _).
split; [|split; [|split]].
- split; [exact HJ|]. split; [exact ER32|]. split; [rewrite <- ES; exact ERS|]. split; [exact ESTK|].
  split; [exact Hown|]. rewrite EF.
  rewrite (eh_fal _ _ _ 4 (x_pos cx) Hly), (eh_fal _ _ _ 4 (x_pos cx) Hlyc). reflexivity.
- rewrite EF. exact HFapp.
- exact Happ.
- exact Hp2.
Qed.

(* ======================================== the cuts at the two arms ======================================== *)
Lemma eh_build_common : forall cx sh np ps cnt es rest rr r r3 pb ly2 S2 W2 regs2 mem2 md2 regs5 mem5 md5,
hsu_start_M01 rsegs B headamp_himg_B cx rest ->
hsu_pod_base rsegs B MT headamp_himg_B cx sh np ps cnt es rest rr r ly2 S2 W2 regs2 mem2 md2 ->
hsu_at_cx rsegs cx W2 mem2 regs2 (hsu_L_Dc rsegs cx sh np ps cnt es) ->
hsu_fsh_at rsegs cx W2 mem2 (hsu_PJ headamp_himg_B) ->
hsu_pp_at rsegs cx W2 mem2 (pc_image (PbCut sh ps (Some es))) ->
hsu_obj_at rsegs cx W2 mem2 HSU_E62 (zeros 104) ->
ajournal rsegs B (x_STK cx) (x_sp0 cx) (x_FP cx) (x_ly cx) (x_S cx) (x_W0 cx) (x_mem0 cx) (x_md0 cx) (x_own cx)
  ly2 S2 W2 mem5 md5 (x_k cx) ->
same_io md2 md5 ->
(forall q : bv 5, bv_unsigned q <> 0 -> ~ In q eh_clob -> getr regs5 q = getr regs2 q) ->
(forall a, 0 <= a < 2 ^ 64 -> ~ eh_wTCN (e_R (x_e cx)) (e_F (x_e cx)) a ->
 aview rsegs (w_H W2) mem5 a = aview rsegs (w_H W2) mem2 a) ->
eh_zero W2 mem5 (e_F (x_e cx)) 4 12 -> eh_zero W2 mem5 (e_F (x_e cx)) 20 3 ->
val_mem rsegs (mrestrict (w_H W2) mem5) (e_R (x_e cx) + 0x110) 8 (hsu_cur rsegs cx rest r3) ->
getr regs5 6 = w64 (Z.of_nat (length r3)) -> getr regs5 18 = w64 (e_F (x_e cx) + 0xa0) -> getr regs5 26 = w64 pb ->
hsu_suffix rest r3 ->
hsu_pod_base rsegs B MT headamp_himg_B cx sh np ps cnt es rest rr r3 ly2 S2 W2 regs5 mem5 md5 /\
hsu_at_cx rsegs cx W2 mem5 regs5 (e0_L_arm cx sh np ps cnt es rest r3 pb) /\
hsu_fsh_at rsegs cx W2 mem5 (hsu_PG headamp_himg_B) /\
hsu_pp_at rsegs cx W2 mem5 (pc_image (PbCut sh ps (Some es))) /\
hsu_obj_at rsegs cx W2 mem5 HSU_E62 (zeros 104).
Proof.
intros cx sh np ps cnt es rest rr r r3 pb ly2 S2 W2 regs2 mem2 md2 regs5 mem5 md5
  Hst Hb Hat0 Hfsh Hpp He HJ5 Hio5 Hk5 Hm5 Z1 Z2 V5 R6 R18 R26 Hsuf.
destruct (eh_base_ctx cx sh np ps cnt es rest rr r ly2 S2 W2 regs2 mem2 md2 Hst Hb) as (Hctx & HFapp & Hppapp & Hpp2).
destruct (eh_frame B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hctx)
  as (HF32 & HF0 & HFc & HRc & HR0 & HR1 & Has & _).
pose proof (@asan_consts rc) as (C1 & _).
destruct (eh_sF (e_F (x_e cx)) ltac:(lia) ltac:(lia)) as [SF0 SF1].
pose proof Hb as (Hcore & Hin & _ & _ & Hwf & _ & _ & _ & _ & _ & _ & _ & _ & Hps2 & _ & Hesw & Hes32 & _).
assert (HlenPP : Z.of_nat (length (pc_image (PbCut sh ps (Some es))))= Layout.PP_SIZE)
  by exact (cj_pc_len sh ps es Hwf Hesw Hes32 Hps2).
assert (Hcur : 0 <= hsu_cur rsegs cx rest r3 < 2 ^ 64).
{ destruct Hsuf as (j & Hj & ->). unfold hsu_cur. rewrite length_skipn.
  destruct Hin as (Hel & _ & _ & _ & _ & Hs0 & Hs63 & _).
  pose proof (Nat.le_sub_l (length rest) j) as Hle. apply Nat2Z.inj_le in Hle.
  rewrite Nat2Z.inj_sub by lia. lia. }
unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in HFapp, Hppapp.
assert (Hcore5 : hsu_core rsegs B MT cx (hsu_E1 rsegs headamp_himg_B cx) ly2 S2 W2 regs5 mem5 md5).
{ apply (eh_core_step cx (eh_wTCN (e_R (x_e cx)) (e_F (x_e cx))) ly2 S2 W2 regs2 mem2 md2 regs5 mem5 md5 Hcore HJ5).
  - intros q [->|[->| ->]]; (apply Hk5; [cbv; discriminate | eh_notin]).
  - exact Hio5.
  - exact Hm5.
  - apply eh_E1. }
split; [exact (eh_base_move cx sh np ps cnt es rest rr r r3 ly2 S2 W2 regs2 mem2 md2 ly2 S2 W2 regs5 mem5 md5
  Hb Hcore5 Hsuf)|].
split.
{ unfold hsu_at_cx, e0_L_arm. unfold hsu_at. apply Forall_app. split.
  - apply (eh_at_move _ _ _ mem5 regs5 _ _ Hat0).
    cbn [hsu_L_Dc hsu_Rc0 hsu_Kc app]; repeat apply Forall_cons; try apply Forall_nil; cbn [fst hm_keeps hd_xv].
    all: first [ apply Hk5; [cbv; discriminate | eh_notin]
               | let j := fresh "j" in let Hj := fresh "Hj" in
                 intros j Hj; apply Hm5; [lia | apply eh_cell_out; lia] ].
  - repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd hd_at hd_xv].
    + rewrite Z.mod_small by lia. exact V5.
    + exact R6.
    + exact R18.
    + exact R26. }
split.
{ unfold hsu_fsh_at in *. rewrite e0_PG_sh. rewrite e0_PJ_sh in Hfsh.
  replace (hmu_sh true true false false false true false false)
    with (hm_setn (hm_setn (hmu_sh false false false false false true false false) 4 12 0) 20 3 0)
    by (rewrite hmu_sh_t_in, hmu_sh_ch_in; reflexivity).
  apply (eh_fsh_two _ _ _ _ _ _ 4 12 20 3 0 Hfsh).
  - intros i Hi. simpl in Hi. apply Z1. lia.
  - intros i Hi. simpl in Hi. apply Z2. lia.
  - intros i Hi N1 N2. rewrite hmu_sh_len in Hi. simpl in Hi, N1, N2.
    apply Hm5; [lia | cbv [eh_wTCN eh_wT eh_wCh eh_wN]; lia]. }
split.
{ unfold hsu_pp_at in *.
  change (hm_bytes rsegs (w_H W2) mem5 (e_pp (x_e cx)) (pc_image (PbCut sh ps (Some es)))).
  apply (hm_bytes_kept rsegs (w_H W2) mem2); [exact Hpp|]. intros x Hx.
  rewrite HlenPP in Hx. unfold Layout.PP_SIZE in *.
  apply Hm5; [lia | apply (eh_app_out alloc_ceiling); lia]. }
{ unfold hsu_obj_at in *.
  change (hm_bytes rsegs (w_H W2) mem5 (e_F (x_e cx) + HSU_E62) (zeros 104)).
  apply (hm_bytes_kept rsegs (w_H W2) mem2); [exact He|]. intros x Hx.
  unfold zeros in Hx. rewrite repeat_length in Hx. unfold HSU_E62 in *.
  apply Hm5; [lia | apply (eh_app_out alloc_ceiling); lia]. }
Qed.

Lemma eh_build_DIG : forall cx sh np ps cnt es rest rr r r3 c pb ly2 S2 W2 regs2 mem2 md2 regs5 mem5 md5,
hsu_start_M01 rsegs B headamp_himg_B cx rest ->
hsu_pod_base rsegs B MT headamp_himg_B cx sh np ps cnt es rest rr r ly2 S2 W2 regs2 mem2 md2 ->
hsu_at_cx rsegs cx W2 mem2 regs2 (hsu_L_Dc rsegs cx sh np ps cnt es) ->
hsu_fsh_at rsegs cx W2 mem2 (hsu_PJ headamp_himg_B) ->
hsu_pp_at rsegs cx W2 mem2 (pc_image (PbCut sh ps (Some es))) ->
hsu_obj_at rsegs cx W2 mem2 HSU_E62 (zeros 104) ->
ajournal rsegs B (x_STK cx) (x_sp0 cx) (x_FP cx) (x_ly cx) (x_S cx) (x_W0 cx) (x_mem0 cx) (x_md0 cx) (x_own cx)
  ly2 S2 W2 mem5 md5 (x_k cx) ->
same_io md2 md5 ->
(forall q : bv 5, bv_unsigned q <> 0 -> ~ In q eh_clob -> getr regs5 q = getr regs2 q) ->
(forall a, 0 <= a < 2 ^ 64 -> ~ eh_wTCN (e_R (x_e cx)) (e_F (x_e cx)) a ->
 aview rsegs (w_H W2) mem5 a = aview rsegs (w_H W2) mem2 a) ->
eh_zero W2 mem5 (e_F (x_e cx)) 4 12 -> eh_zero W2 mem5 (e_F (x_e cx)) 20 3 ->
val_mem rsegs (mrestrict (w_H W2) mem5) (e_R (x_e cx) + 0x110) 8 (hsu_cur rsegs cx rest r3) ->
getr regs5 6 = w64 (Z.of_nat (length r3)) -> getr regs5 18 = w64 (e_F (x_e cx) + 0xa0) -> getr regs5 26 = w64 pb ->
getr regs5 13 = w64 c -> getr regs5 5 = w64 4 -> getr regs5 28 = w64 9 -> getr regs5 7 = w64 10 ->
getr regs5 23 = w64 (-8) ->
hsu_suffix rest r3 -> fst (Cursor.fuzz_u8 rr) mod 10 = 0 -> (c, pb, r3) = e0_cp_of rr ->
0 <= c < 200 -> 0 <= pb < 256 ->
e0_cut_DIG B MT cx sh np ps cnt es rest rr r3 c pb ly2 S2 W2 regs5 mem5 md5.
Proof.
intros cx sh np ps cnt es rest rr r r3 c pb ly2 S2 W2 regs2 mem2 md2 regs5 mem5 md5
  Hst Hb Hat0 Hfsh Hpp He HJ5 Hio5 Hk5 Hm5 Z1 Z2 V5 R6 R18 R26 R13 R5 R28 R7 R23 Hsuf Hkd Hcp Hc Hpb.
destruct (eh_build_common cx sh np ps cnt es rest rr r r3 pb ly2 S2 W2 regs2 mem2 md2 regs5 mem5 md5
  Hst Hb Hat0 Hfsh Hpp He HJ5 Hio5 Hk5 Hm5 Z1 Z2 V5 R6 R18 R26 Hsuf) as (Hb5 & Hat5 & Hfsh5 & Hpp5 & He5).
unfold e0_cut_DIG.
split; [exact Hb5|].
split.
{ unfold hsu_at_cx, hsu_at in *. apply Forall_app. split; [exact Hat5|].
  repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd hd_at].
  - exact R13. - exact R5. - exact R28. - exact R7. - exact R23. }
split; [exact Hfsh5|]. split; [exact Hpp5|]. split; [exact He5|].
split; [exact Hkd|]. split; [exact Hcp|]. split; [exact Hc | exact Hpb].
Qed.

Lemma eh_build_ODD : forall cx sh np ps cnt es rest rr r r3 c pb ly2 S2 W2 regs2 mem2 md2 regs5 mem5 md5,
hsu_start_M01 rsegs B headamp_himg_B cx rest ->
hsu_pod_base rsegs B MT headamp_himg_B cx sh np ps cnt es rest rr r ly2 S2 W2 regs2 mem2 md2 ->
hsu_at_cx rsegs cx W2 mem2 regs2 (hsu_L_Dc rsegs cx sh np ps cnt es) ->
hsu_fsh_at rsegs cx W2 mem2 (hsu_PJ headamp_himg_B) ->
hsu_pp_at rsegs cx W2 mem2 (pc_image (PbCut sh ps (Some es))) ->
hsu_obj_at rsegs cx W2 mem2 HSU_E62 (zeros 104) ->
ajournal rsegs B (x_STK cx) (x_sp0 cx) (x_FP cx) (x_ly cx) (x_S cx) (x_W0 cx) (x_mem0 cx) (x_md0 cx) (x_own cx)
  ly2 S2 W2 mem5 md5 (x_k cx) ->
same_io md2 md5 ->
(forall q : bv 5, bv_unsigned q <> 0 -> ~ In q eh_clob -> getr regs5 q = getr regs2 q) ->
(forall a, 0 <= a < 2 ^ 64 -> ~ eh_wTCN (e_R (x_e cx)) (e_F (x_e cx)) a ->
 aview rsegs (w_H W2) mem5 a = aview rsegs (w_H W2) mem2 a) ->
eh_zero W2 mem5 (e_F (x_e cx)) 4 12 -> eh_zero W2 mem5 (e_F (x_e cx)) 20 3 ->
val_mem rsegs (mrestrict (w_H W2) mem5) (e_R (x_e cx) + 0x110) 8 (hsu_cur rsegs cx rest r3) ->
getr regs5 6 = w64 (Z.of_nat (length r3)) -> getr regs5 18 = w64 (e_F (x_e cx) + 0xa0) -> getr regs5 26 = w64 pb ->
getr regs5 13 = w64 c ->
hsu_suffix rest r3 -> fst (Cursor.fuzz_u8 rr) mod 10 = 0 -> (c, pb, r3) = e0_cp_of rr ->
200 <= c < 256 -> 0 <= pb < 256 ->
e0_cut_ODD B MT cx sh np ps cnt es rest rr r3 c pb ly2 S2 W2 regs5 mem5 md5.
Proof.
intros cx sh np ps cnt es rest rr r r3 c pb ly2 S2 W2 regs2 mem2 md2 regs5 mem5 md5
  Hst Hb Hat0 Hfsh Hpp He HJ5 Hio5 Hk5 Hm5 Z1 Z2 V5 R6 R18 R26 R13 Hsuf Hkd Hcp Hc Hpb.
destruct (eh_build_common cx sh np ps cnt es rest rr r r3 pb ly2 S2 W2 regs2 mem2 md2 regs5 mem5 md5
  Hst Hb Hat0 Hfsh Hpp He HJ5 Hio5 Hk5 Hm5 Z1 Z2 V5 R6 R18 R26 Hsuf) as (Hb5 & Hat5 & Hfsh5 & Hpp5 & He5).
unfold e0_cut_ODD.
split; [exact Hb5|].
split.
{ unfold hsu_at_cx, hsu_at in *. apply Forall_app. split; [exact Hat5|].
  repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd hd_at]. exact R13. }
split; [exact Hfsh5|]. split; [exact Hpp5|]. split; [exact He5|].
split; [exact Hkd|]. split; [exact Hcp|]. split; [exact Hc | exact Hpb].
Qed.

End d.
End b.

Print Assumptions eh_base_ctx.
Print Assumptions eh_build_DIG.
Print Assumptions eh_build_ODD.
