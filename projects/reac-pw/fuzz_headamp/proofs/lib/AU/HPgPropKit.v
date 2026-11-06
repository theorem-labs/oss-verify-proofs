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
(* reac-pw/fuzz_headamp image B (fuzz_headamp.asan-ubsan, pinned sha256
   53edda9bdeeba1803865babfecb1af6732babe47ab83c64d38cc59a90d717a94; every address below is measured on its
   unstripped twin sha256 1674e30a0698f381704e66d2398d7906c881f4ba8fc619cb41b89fb97ad112ff): what the four pieces of
   one turn of the property loop of LLVMFuzzerTestOneInput (0x80c40) share -- lib/AU/HPgPropSel.v (N -> SEL7 / SELK),
   HPgPropInt.v (SEL7 -> LATCH), HPgPropKey.v (SELK -> SELS / SELI), HPgPropLatch.v (LATCH -> N / P1), the
   statements lib/AU/HPgSeg.v hsu_piece_W4_*_stmt at headamp_himg_B / headamp_bld_B. Proves no function (kind:
   segment lemma).

   THE CODE (pod.h:397-423, the inlined pod_build loop `for (i = 0; i < nprops; i++)`): the table hbp_tbl holds the
   1495 instruction words 0x81494 .. 0x82bec, which cover the four blocks (N 0x81494, SEL7 0x814d4, SELK 0x81590,
   LATCH 0x82ae4) and the out-of-line slow blocks of their instrumented checks (0x82afc .. 0x82bb4). The calls the
   Int pod block makes (__asan_memset 0x52228, pod_write_ent 0x84634) and the error and trap paths (0x83a14,
   0x83c14 .., 0x83d28 ..) lie outside it: a walk stops at the call, and never reaches the others.

   WHERE THE LOOP'S VALUES LIVE (image B; HPgSeg.v's cut lists): s0 = S, s1 = R, s3 = (F >> 3) + K, s11 = K,
   s8 = the `v / 10` multiplier, s6 = &r, s9 = &t, s7 = -8, s10 = 1; at N t0 = i, s4 = seen, s2 = the cursor,
   t3 = what is left; the R-relative constants of HPgSeg.hsu_Kc (R+0x70 = 0x10003, R+0xa8 = -0x4001,
   R+0xb0 = 0x80001, R+0xb8 = &e, R+0xa0 = &e + 8, R+0xf0 = ~pp, R+0xf8 = (sh = 7), R+0x100 = np, R+0x108 = -0x3ffd,
   R+0x138 = &pp->len, R+0x148 = pp, R+0x150 = the shadow address of &pp->len). *)
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
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YI16 YM05.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Pod Require Import Cursor Model Layout.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.A Require Import HPgBase HPgCSpec.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.AU Require Import Img0U HPgImgB HPgSteps HPgMem HPgSeg HPgCaseB.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.
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

(* ---- the pcs (HPgSeg.headamp_bld_B's) ---- *)
Definition HBP_N : Z := 0x81494.
Definition HBP_SEL7 : Z := 0x814d4.
Definition HBP_SELK : Z := 0x81590.
Definition HBP_SELS : Z := 0x816fc.
Definition HBP_SELI : Z := 0x828ec.
Definition HBP_LATCH : Z := 0x82ae4.
Definition HBP_P1 : Z := 0x82bf0.
Lemma hbp_pcs : bi_N headamp_bld_B = HBP_N /\ bi_SEL7 headamp_bld_B = HBP_SEL7 /\
bi_SELK headamp_bld_B = HBP_SELK /\ bi_SELS headamp_bld_B = HBP_SELS /\ bi_SELI headamp_bld_B = HBP_SELI /\
bi_LATCH headamp_bld_B = HBP_LATCH /\ bi_P1 headamp_bld_B = HBP_P1.
Proof. repeat split. Qed.
(* the 1495 instruction words 0x81494 .. 0x82bec: the four blocks and their out-of-line slow blocks *)
Definition hbp_tbl : ctable := build_table rsegs HBP_N 1495 TEmpty.
Lemma hbp_tbl_ok : table_ok rsegs hbp_tbl.
Proof. apply build_table_ok0. unfold HBP_N. lia. Qed.

(* ---- the walk's context: env slot 32 is the shadow offset K; slots 33.. the block's own quantities ---- *)
Definition HBPBx : sv := SOff 32 0.
Definition HBPspan : Z * Z := (SHADOW_OFF, SHADOW_OFF + 2 ^ 44 - 1).
Definition hbp_extra (l : list Z) : list word := Z_to_bv 64 SHADOW_OFF :: map (Z_to_bv 64) l.
Lemma hbp_extra_K : forall regs l, ew (Ereg regs (hbp_extra l)) 32 = Z_to_bv 64 SHADOW_OFF.
Proof. intros. reflexivity. Qed.

Section k. Context {fx : YK11.FPState}.
(* an 8-byte chunk from the cell's value *)
Lemma hbp_chunk8 : forall E m base off v val,
sv_denot E v = Z_to_bv 64 val -> 0 <= val < 2 ^ 64 -> val_mem rsegs m (base + off) 8 val ->
YP09.chunk_ok rsegs E m base (YP09.mkChunk off (CVal 8 v)).
Proof.
intros E m base off v val Hv Hval Hw i Hi. cbn [YP09.c_off YP09.c_val YP09.c_len YP09.cv_len cbyte] in Hi |- *.
exists (byte_of_word (sv_denot E v) i). split; [reflexivity|].
replace (base + off + i) with (base + off + Z.of_nat (Z.to_nat i)) by lia. rewrite (Hw (Z.to_nat i)) by lia.
f_equal. unfold byte_of_word, YO0f.le_byte. rewrite Hv, Z2Nat.id by lia. apply bv_eq. rewrite !Z_to_bv_unsigned.
unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64). change (bv_modulus 8) with 256.
change (8 * Z.of_nat 8) with 64. rewrite (Z.mod_small val (2 ^ 64)) by lia. rewrite Z.mod_mod by lia. reflexivity.
Qed.
End k.

(* ---- the walk's plumbing ---- *)
(* KE : every byte outside the zone Zn as at the block's start; a run whose write windows lie in Zn keeps it *)
Ltac hbp_keep kwr :=
lazymatch goal with HFr : frame_of _ _ (mrestrict _ _) (mrestrict _ _), KE : forall a, _ -> ~ _ -> aview _ _ _ a = _ |- _ =>
let KS := fresh "KS" in let KW := fresh "KW" in
pose proof (cb_kept_run _ _ _ _ _ _ _ KE HFr) as KS;
lazymatch type of KS with ?P -> _ => assert (KW : P) by kwr end;
specialize (KS KW); clear KW KE HFr; rename KS into KE
end;
repeat match goal with H : frame_of _ _ _ _ |- _ => clear H | H : mem_grows _ _ |- _ => clear H end.
(* the write windows of a state without one *)
Ltac hbp_kwr_ro :=
idtac; let a := fresh "a" in let r := fresh "r" in let Hr := fresh "Hr" in let Hb := fresh "Hb" in
intros a (r & Hr & Hb); cbv beta;
lazymatch type of Hr with In _ ?rs => let rs' := eval vm_compute in rs in change (In r rs') in Hr end;
repeat (destruct Hr as [<- | Hr]; [cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hb; lia | ]); destruct Hr.
Ltac hbp_run stop :=
lazymatch goal with HS : st_ok _ _ _ _, HJ : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _, SHOK : sh_ok _ _ _ _ _ |- _ =>
aj_run_to_tok hbp_tbl_ok HS HJ SHOK HBPspan stop; [awr_ok_tac | ] end.
Ltac hbp_runb :=
lazymatch goal with HS : st_ok _ _ _ _, HJ : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _, SHOK : sh_ok _ _ _ _ _ |- _ =>
aj_run_tok hbp_tbl_ok HS HJ SHOK HBPspan; [awr_ok_tac | ] end.
Ltac hbp_branch Hc :=
lazymatch goal with HS : st_ok _ _ _ _, SH : sh_ok _ _ _ _ _ |- _ => srr_branch_tok hbp_tbl_ok HS SH HBPspan end;
lazymatch goal with Hb : branch_taken _ _ _ = _ |- _ => rename Hb into Hc end.
(* the value of register r at the end of a run, as the symbolic state holds it *)
Ltac hbp_reg r :=
lazymatch goal with HS : st_ok ?sg ?E ?ssf (restrict ?H ?ms) |- context [getr (ms_regs ?ms) r] =>
rewrite (st_ok_restrict_reg sg H E ssf ms r HS);
let e := eval vm_compute in (sr_get (ss_regs ssf) r) in change (sr_get (ss_regs ssf) r) with e end.
(* the leaf: HPgSteps.hdu_blk_postE's first eight clauses, every register outside clob kept because its symbolic
   value is still its own atom; the relation is left *)
Ltac hbp_leaf extra :=
lazymatch goal with
| HS : st_ok _ ?E _ (restrict (w_H ?W) ?ms), HJ : ajournal _ _ _ _ _ _ _ _ _ _ _ ?lyc ?Sc _ _ _ _,
  HAE : env_agree 32 (Ereg ?regs _) ?E, KE : forall a, _ -> ~ _ -> aview _ _ _ a = _ |- _ =>
apply SRr_ret;
red; exists lyc, Sc, (ms_regs ms), (ms_mem ms); eexists;
split; [rewrite (st_ok_restrict_mkst rsegs (w_H W) _ _ ms HS eq_refl) at 1; reflexivity|];
split; [exact HJ|];
split; [eapply (regs_kept_of_st_ok rsegs _ _ ms regs extra (w_H W) _ HS HAE); vm_compute; reflexivity|];
split; [reflexivity|];
split; [apply Permutation_refl|];
split; [let rec kio := first [apply same_io_refl | eapply same_io_trans; [| apply same_io_wvb]; kio] in kio|];
split; [apply mo_le_refl; assumption|];
split; [intros a Ha Hz; exact (KE a Ha Hz)|]
end.

(* ---- membership in a concrete location list (the cut lists of HPgSeg.v are concatenations of definitions) ---- *)
Ltac hbp_in :=
cbn [hsu_Rc0 hsu_Rc1 hsu_Kc hsu_cur2 hsu_L_N hsu_L_SEL hsu_L_KEY hsu_L_P app In fst snd];
repeat (first [left; reflexivity | right]).
(* a register outside a concrete clobber list *)
Ltac hbp_notin :=
let H := fresh "H" in intros H; cbn [In] in H;
repeat (destruct H as [H|H]; [apply (f_equal (@bv_unsigned 5)) in H; vm_compute in H; discriminate H|]); exact H.

Section g. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Variable B : asyms.
Variable MT : ameter_ops.
Hypothesis MTL : ameter_laws MT.
Hypothesis LAWS : AR_laws rsegs B.

(* ---- the (location, value) facts of a cut ---- *)
Lemma hbp_at_get : forall H mem regs e L l v,
hsu_at rsegs H mem regs e L -> In (l, v) L -> hd_at rsegs H mem regs e l v.
Proof. intros H mem regs e L l v HL Hin. unfold hsu_at in HL. rewrite Forall_forall in HL. exact (HL (l, v) Hin). Qed.
Lemma hbp_at_app : forall H mem regs e L1 L2,
hsu_at rsegs H mem regs e L1 -> hsu_at rsegs H mem regs e L2 -> hsu_at rsegs H mem regs e (L1 ++ L2).
Proof. intros H mem regs e L1 L2 H1 H2. unfold hsu_at in *. apply Forall_app. auto. Qed.
(* what a location needs to keep its value between two states *)
Definition hbp_kept_loc (e : hd_env) (regs regs' : bvmap 5 word) (H H' : word -> bool)
(mem mem' : word -> option byte) (l : hd_loc) : Prop :=
match l with
| LReg r => getr regs' (Z_to_bv 5 r) = getr regs (Z_to_bv 5 r)
| LCell b o => forall j, 0 <= j < 8 -> aview rsegs H' mem' (hd_xv e b + o + j) = aview rsegs H mem (hd_xv e b + o + j)
end.
Lemma hbp_at_move : forall H mem regs H' mem' regs' e L,
hsu_at rsegs H mem regs e L -> Forall (fun f => hbp_kept_loc e regs regs' H H' mem mem' (fst f)) L ->
hsu_at rsegs H' mem' regs' e L.
Proof.
intros H mem regs H' mem' regs' e L HL HK. unfold hsu_at in *.
induction L as [|[l v] L IH]; [constructor|].
inversion HL as [|? ? H1 H2]; subst. inversion HK as [|? ? K1 K2]; subst.
constructor; [|apply IH; assumption].
cbn [fst snd] in *. destruct l as [r|b o]; cbn [hd_at hbp_kept_loc] in *.
- rewrite K1. exact H1.
- eapply val_mem_kept; [|exact H1]. intros j Hj. apply K1. lia.
Qed.

Lemma hbp_aview_mod : forall H mem a, aview rsegs H mem a = aview rsegs H mem (a mod 2 ^ 64).
Proof. intros H mem a. unfold aview, mbyte. rewrite Z_to_bv_mod64. reflexivity. Qed.
(* a block that writes nothing keeps every byte, also outside [0, 2^64) *)
Lemma hbp_mem_all : forall H mem H' mem',
(forall a, 0 <= a < 2 ^ 64 -> ~ False -> aview rsegs H' mem' a = aview rsegs H mem a) ->
forall a, aview rsegs H' mem' a = aview rsegs H mem a.
Proof.
intros H mem H' mem' K a. rewrite (hbp_aview_mod H' mem' a), (hbp_aview_mod H mem a).
apply K; [apply Z.mod_pos_bound; lia | tauto].
Qed.

(* ---- the journal-and-frame part of a cut, after a block ---- *)
Lemma hbp_core_step : forall cx E (Ew : Z -> Prop) ly2 S2 W2 regs2 mem2 md2 ly3 S3 W3 regs3 mem3 md3,
hsu_core rsegs B MT cx E ly2 S2 W2 regs2 mem2 md2 ->
ajournal rsegs B (x_STK cx) (x_sp0 cx) (x_FP cx) (x_ly cx) (x_S cx) (x_W0 cx) (x_mem0 cx) (x_md0 cx) (x_own cx)
  ly3 S3 W3 mem3 md3 (x_k cx) ->
(forall r : Z, r = 2 \/ r = 3 \/ r = 4 -> getr regs3 (Z_to_bv 5 r) = getr regs2 (Z_to_bv 5 r)) ->
frames S3 = frames S2 -> Permutation (ablocks B ly3 S3) (ablocks B ly2 S2) -> same_io md2 md3 -> mo_le MT S2 S3 0 ->
(forall a, 0 <= a < 2 ^ 64 -> ~ Ew a -> aview rsegs (w_H W3) mem3 a = aview rsegs (w_H W2) mem2 a) ->
(forall a, Ew a -> (spZ (x_regs cx) - T_SEG_STK <= a < spZ (x_regs cx)) \/ E a) ->
hsu_core rsegs B MT cx E ly3 S3 W3 regs3 mem3 md3.
Proof using MTL.
intros cx E Ew ly2 S2 W2 regs2 mem2 md2 ly3 S3 W3 regs3 mem3 md3 Hc HJ3 Hr3 Hf3 Hp3 Hio3 Hmo3 Hm3 HEw.
unfold hsu_core, hsu_mid in *. destruct Hc as (HJ & Hr & Hf & Hp & Hio & Hmo & Hm).
split; [exact HJ3|].
split; [intros r Hr'; rewrite (Hr3 r Hr'); exact (Hr r Hr')|].
split; [rewrite Hf3; exact Hf|].
split; [eapply Permutation_trans; [exact Hp3 | exact Hp]|].
split; [eapply same_io_trans; [exact Hio | exact Hio3]|].
split; [replace 0 with (0 + 0) by reflexivity; exact (mle_station MT _ _ _ 0 0 MTL Hmo Hmo3)|].
intros a Ha Hs HE. rewrite <- (Hm a Ha Hs HE). apply Hm3; [exact Ha|].
intros HW. destruct (HEw a HW) as [X|X]; [exact (Hs X) | exact (HE X)].
Qed.

(* ---- the segment's write set (HPgImgB: hi_w1 = [F+0x20, F+0x278), the 116 shadow bytes of F, [R, R+0x198)) ---- *)
Lemma hbp_E1_F : forall cx a, e_F (x_e cx) + 0x20 <= a < e_F (x_e cx) + 0x278 -> hsu_E1 rsegs headamp_himg_B cx a.
Proof.
intros cx a Ha. left. unfold hd_inw. cbn [hi_w1 headamp_himg_B].
apply Exists_cons_hd. cbn [fst snd hd_xv]. lia.
Qed.
Lemma hbp_E1_sh : forall cx a, shadow_addr (e_F (x_e cx)) <= a < shadow_addr (e_F (x_e cx)) + 116 ->
hsu_E1 rsegs headamp_himg_B cx a.
Proof.
intros cx a Ha. left. unfold hd_inw. cbn [hi_w1 headamp_himg_B].
apply Exists_cons_tl. apply Exists_cons_hd. cbn [fst snd hd_xv]. lia.
Qed.
Lemma hbp_E1_R : forall cx a, e_R (x_e cx) <= a < e_R (x_e cx) + 0x198 -> hsu_E1 rsegs headamp_himg_B cx a.
Proof.
intros cx a Ha. left. unfold hd_inw. cbn [hi_w1 headamp_himg_B].
apply Exists_cons_tl. apply Exists_cons_tl. apply Exists_cons_hd. cbn [fst snd hd_xv]. lia.
Qed.
Lemma hbp_E1_pp : forall cx a, e_pp (x_e cx) <= a < e_pp (x_e cx) + Layout.PP_SIZE -> hsu_E1 rsegs headamp_himg_B cx a.
Proof. intros cx a Ha. right. exact Ha. Qed.

(* ---- the first block's image at a property cut: its bounds ---- *)
Lemma hbp_img_bounds : forall sh ps, hsu_wf sh ps -> (length ps <= 2)%nat ->
Z.of_nat (length (pc_buf (PbCut sh ps None))) + 16 <= 5440 /\
Z.of_nat (length (pc_buf (PbCut sh ps None))) mod 8 = 0 /\
(length (pc_ents (PbCut sh ps None)) <= 32)%nat /\
Forall (fun e => (length (e_body e) <= 96)%nat) (pc_ents (PbCut sh ps None)).
Proof.
intros sh ps (Hs & Hk & He & Hl) H2.
assert (Hv : Forall (fun kv => pval_wf (snd kv)) ps) by (eapply Forall_impl; [|exact Hk]; intros kv [_ X]; exact X).
destruct (pc_buf_len_none sh ps Hv He) as [L1 [c Hc]].
assert (EW : (length (pc_ents (PbCut sh ps None)) <= 32)%nat /\ Forall ent_wf (pc_ents (PbCut sh ps None))).
{ unfold pc_ents. cbn [pc_props pc_open].
  destruct (first_params ps) as [[iv|es]|] eqn:E; try (split; [cbn; lia | constructor]).
  unfold first_params in E. destruct (find _ _) as [kv|] eqn:F; [|discriminate]. cbn in E. injection E as E.
  apply find_some in F as [Hin _]. split.
  - rewrite Forall_forall in Hk. destruct (Hk kv Hin) as [_ Hv']. rewrite E in Hv'. exact Hv'.
  - apply all_ents_Forall in He. rewrite Forall_forall in He. specialize (He kv Hin). rewrite E in He. exact He. }
destruct EW as [E1 E2].
split; [lia|]. split; [rewrite Hc; apply Z_mod_mult|]. split; [exact E1|].
eapply Forall_impl; [|exact E2]. intros e (_ & Hb & Hz). rewrite Hb. lia.
Qed.

(* ---- pod_put into the first block (pod.h:175-182): x appended at len, len := len + |x|, every other byte kept
   [Layout.pp_image_put] ---- *)
Lemma hbp_pp_append : forall H mem H' mem' pp b x isp hasp pst es corr,
Z.of_nat (length b + length x) <= Layout.POD_BUF_MAX -> (length es <= 32)%nat ->
Forall (fun e => (length (e_body e) <= 96)%nat) es ->
hm_bytes rsegs H mem pp (pp_image b isp hasp pst es corr) ->
hm_bytes rsegs H' mem' (pp + Z.of_nat (length b)) x ->
val_mem rsegs (mrestrict H' mem') (pp + Layout.OFF_LEN) 8 (Z.of_nat (length b + length x)) ->
(forall y, pp <= y < pp + Layout.PP_SIZE ->
 ~ (pp + Z.of_nat (length b) <= y < pp + Z.of_nat (length b) + Z.of_nat (length x)) ->
 ~ (pp + Layout.OFF_LEN <= y < pp + Layout.OFF_LEN + 8) -> aview rsegs H' mem' y = aview rsegs H mem y) ->
hm_bytes rsegs H' mem' pp (pp_image (b ++ x) isp hasp pst es corr).
Proof.
intros H mem H' mem' pp b x isp hasp pst es corr Hbx Hes Hbod Old Nx Nlen K.
pose proof (length_pp_image b isp hasp pst es corr ltac:(unfold Layout.POD_BUF_MAX in Hbx; lia) Hes Hbod) as LI.
rewrite pp_image_tail in LI, Old |- *. set (T := pp_tail isp hasp pst es corr) in *.
set (k := Z.to_nat (Layout.POD_BUF_MAX - Z.of_nat (length (b ++ x)))).
assert (Ez : zeros (Z.to_nat (Layout.POD_BUF_MAX - Z.of_nat (length b))) = zeros (length x) ++ zeros k).
{ rewrite <- zeros_app. f_equal. unfold k. rewrite length_app. unfold Layout.POD_BUF_MAX in Hbx |- *. lia. }
assert (Hk : Z.of_nat (length b) + Z.of_nat (length x) + Z.of_nat k = 16384).
{ unfold k. rewrite length_app. unfold Layout.POD_BUF_MAX in Hbx |- *. lia. }
clearbody k T.
rewrite Ez in Old, LI.
rewrite !length_app, !length_zeros, length_le64 in LI.
apply hm_bytes_app in Old as [Ob Old]. rewrite <- app_assoc in Old.
apply hm_bytes_app in Old as [_ Old]. apply hm_bytes_app in Old as [Ozk Old].
apply hm_bytes_app in Old as [_ OT].
rewrite length_zeros in Ozk, OT. rewrite length_zeros, length_le64 in OT.
rewrite <- app_assoc. apply hm_bytes_app. split.
{ eapply (hm_bytes_kept rsegs); [exact Ob|]. intros y Hy. apply K; unfold Layout.PP_SIZE, Layout.OFF_LEN in *; lia. }
apply hm_bytes_app. split; [exact Nx|].
apply hm_bytes_app. split.
{ eapply (hm_bytes_kept rsegs); [exact Ozk|]. intros y Hy. rewrite length_zeros in Hy.
  apply K; unfold Layout.PP_SIZE, Layout.OFF_LEN in *; lia. }
rewrite length_zeros. apply hm_bytes_app. split.
{ unfold le64. apply hm_bytes_of_val.
  replace (pp + Z.of_nat (length b) + Z.of_nat (length x) + Z.of_nat k) with (pp + Layout.OFF_LEN)
    by (unfold Layout.OFF_LEN; lia).
  rewrite length_app. exact Nlen. }
rewrite length_le64. eapply (hm_bytes_kept rsegs).
- replace (pp + Z.of_nat (length b) + Z.of_nat (length x) + Z.of_nat k + Z.of_nat 8)
    with (pp + Z.of_nat (length b) + Z.of_nat (length x) + Z.of_nat k + 8) by lia. exact OT.
- intros y Hy. apply K; unfold Layout.PP_SIZE, Layout.OFF_LEN in *; lia.
Qed.

(* ---- the first block at the segment's start: live, made since the journal's start, in application memory ---- *)
Lemma hbp_pp_blocks : forall cx sh, hsu_pre rsegs B headamp_himg_B cx sh ->
In (e_pp (x_e cx), Layout.PP_SIZE) (ablocks B (x_lyc cx) (x_Sc cx)) /\
~ In (e_pp (x_e cx), Layout.PP_SIZE) (ablocks B (x_ly cx) (x_S cx)) /\
amem_range (e_pp (x_e cx)) Layout.PP_SIZE.
Proof using LAWS.
intros cx sh Hpre. unfold hsu_pre, hd_seg_pre in Hpre.
destruct Hpre as (HJ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hfr).
destruct Hfr as (_ & Hpp & Hout).
split; [exact Hpp|]. split; [exact Hout|].
eapply (amem_range_of_block rsegs B LAWS); [exact (proj1 HJ) | exact Hpp | lia | reflexivity].
Qed.

(* ---- the model of one shape-7 property (Model.prop_step's first arm) ---- *)
Lemma hbp_loop7 : forall n inp, props_loop 7 (S n) inp =
(fst (props_loop 7 n inp) ++ [(0, PInt 0)], snd (fuzz_u8 (snd (props_loop 7 n inp)))).
Proof.
intros n inp. rewrite props_loop_S_end. destruct (props_loop 7 n inp) as [ps0 r0]. cbn [fst snd].
unfold prop_step. destruct (fuzz_u8 r0) as [sel r1]. reflexivity.
Qed.
Lemma hbp_seen7 : forall ps, hsu_seen (ps ++ [(0, PInt 0)]) = hsu_seen ps.
Proof. intros ps. unfold hsu_seen. rewrite existsb_app. cbn. rewrite orb_false_r. reflexivity. Qed.
Lemma hbp_img7 : forall ps, pc_image (PbCut 7 (ps ++ [(0, PInt 0)]) None) =
pp_image (pc_buf (PbCut 7 ps None) ++ prop_bytes 7 (0, PInt 0)) (is_props (PodRec 7 ps None))
  (has_params (PodRec 7 ps None)) (params_struct (PodRec 7 ps None)) (pc_ents (PbCut 7 ps None)) false.
Proof.
intros ps. unfold pc_image. cbn [pc_shape pc_props pc_open]. rewrite <- pc_buf_prop.
unfold has_params, params_struct, pc_ents. cbn [p_props pc_props pc_open]. rewrite first_params_app.
destruct (first_params ps); reflexivity.
Qed.
Lemma hbp_wf7 : forall ps, hsu_wf 7 ps -> (length ps <= 2)%nat -> hsu_wf 7 (ps ++ [(0, PInt 0)]).
Proof.
intros ps (Hs & Hk & He & Hl) H2. split; [exact Hs|]. split.
- apply Forall_app. split; [exact Hk|]. constructor; [cbn; split; [lia | exact I] | constructor].
- split; [unfold all_ents in *; rewrite flat_map_app; cbn; rewrite app_nil_r; exact He|].
  rewrite length_app. cbn. lia.
Qed.

(* ---- facts every piece takes from the segment's start ---- *)
Lemma hbp_R_bounds : forall cx sh, hsu_pre rsegs B headamp_himg_B cx sh ->
let e := x_e cx in
x_sp0 cx - x_STK cx + T_SEG_STK <= e_R e /\ e_R e + 0x220 <= x_sp0 cx /\ e_R e mod 16 = 0 /\
2 ^ 46 <= e_R e /\ x_sp0 cx <= 2 ^ 47 /\ getr (x_regs cx) 2 = w64 (e_R e) /\ alloc_ceiling + T_SEG_STK <= e_R e.
Proof.
intros cx sh Hpre e. unfold hsu_pre, hd_seg_pre in Hpre.
destruct Hpre as (HJ & Hev & H2 & H3 & H4 & HS & HR32 & HRs & HRstk & _).
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstk & _).
destruct Hstk as (Hal & HST0 & Hceil & Hslo & Hshi & H47 & _).
pose proof asan_consts as (C1 & _). cbn [hi_rsz headamp_himg_B] in HRs.
assert (HR16 : e_R (x_e cx) mod 16 = 0).
{ pose proof (Z.div_mod (e_R (x_e cx)) 32 ltac:(lia)) as D. rewrite HR32, Z.add_0_r in D.
  rewrite D. replace (32 * (e_R (x_e cx) / 32)) with ((2 * (e_R (x_e cx) / 32)) * 16) by ring.
  apply Z.mod_mul. lia. }
subst e. unfold T_SEG_STK, ASTACK in *. repeat split; try lia. exact H2.
Qed.
Lemma hbp_blk_bounds : forall cx sh, hsu_pre rsegs B headamp_himg_B cx sh ->
let e := x_e cx in
4096 <= e_pp e /\ e_pp e + Layout.PP_SIZE <= alloc_ceiling /\
4096 <= e_F e /\ e_F e + 1024 <= alloc_ceiling /\ in_app (e_F e) 1024.
Proof using LAWS.
intros cx sh Hpre e. unfold hsu_pre, hd_seg_pre in Hpre.
destruct Hpre as (HJ & _ & _ & _ & _ & _ & _ & _ & _ & Hown & HF & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hfr).
destruct Hfr as (_ & Hpp & _).
pose proof (al_blocks _ _ LAWS _ _ _ _ _ _ _ (proj1 HJ) Hpp) as (_ & Hp4096 & Hpceil & _).
assert (Hrq : req_size Layout.PP_SIZE = Layout.PP_SIZE) by reflexivity. rewrite Hrq in Hpceil.
pose proof HJ as (HAR & _ & _ & _ & _ & Hfrs & _).
assert (Hin : In (hi_cid headamp_himg_B, x_pos cx) (frames (x_Sc cx))) by (rewrite Hfrs; apply in_or_app; left; exact Hown).
pose proof (frames_bounds rsegs B LAWS _ _ _ _ _ _ _ HAR Hin) as (F1 & F2 & F3).
rewrite <- HF in F1, F2, F3. cbn [hi_cid headamp_himg_B] in F2, F3. change (fs_frame_bytes 4) with 1024 in F2, F3.
subst e. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia | exact F3].
Qed.

(* ---- the input at a cut of the build: its bytes and their shadow as at the segment's start (hsu_in) ---- *)
Lemma hbp_input_now : forall cx rest ly2 S2 W2 regs2 mem2 md2 c,
hsu_pre rsegs B headamp_himg_B cx (hi_shA headamp_himg_B) -> hsu_in rsegs headamp_himg_B cx rest ->
hsu_core rsegs B MT cx (hsu_E1 rsegs headamp_himg_B cx) ly2 S2 W2 regs2 mem2 md2 ->
hsu_fsh_at rsegs cx W2 mem2 (hsu_P0 headamp_himg_B) -> 0 <= c < Z.of_nat (length rest) ->
val_mem rsegs (mrestrict (w_H W2) mem2) (e_src (x_e cx) + c) 1 (nth (Z.to_nat c) (hd_zbytes rest) 0) /\
range_addressable (aview rsegs (w_H W2) mem2) SHADOW_OFF (e_src (x_e cx) + c) 1.
Proof using LAWS.
intros cx rest ly2 S2 W2 regs2 mem2 md2 c Hpre Hin Hcore Hfsh Hc.
pose proof (hbp_R_bounds cx _ Hpre) as (RB1 & RB2 & RB3 & RB4 & RB5 & RB6 & RB7).
pose proof (hbp_blk_bounds cx _ Hpre) as (PB1 & PB2 & FB1 & FB2 & FB3).
pose proof (hbp_pp_blocks cx _ Hpre) as (_ & _ & PA).
assert (PA' : e_pp (x_e cx) + Layout.PP_SIZE <= 0x7fff7fff \/ 0x10007fff8000 <= e_pp (x_e cx))
  by (destruct PA as [A|[A _]]; [left; exact A | right; exact A]). clear PA.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof Hpre as Hpre'. unfold hsu_pre, hd_seg_pre in Hpre'.
destruct Hpre' as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hfsh0 & _).
destruct Hin as (Hleft & Hgarr & Hra & Hhull & Hamr & Hsrc0 & Hsrcn & Hapart).
destruct Hcore as (_ & _ & _ & _ & _ & _ & Hkm).
assert (SP : spZ (x_regs cx) = e_R (x_e cx)) by (unfold spZ; rewrite RB6; unfold w64; apply unsigned_lit_small; lia).
rewrite SP in Hkm.
set (src := e_src (x_e cx)) in *.
(* the byte *)
assert (Ka : forall a, src <= a < src + e_left (x_e cx) ->
  aview rsegs (w_H W2) mem2 a = aview rsegs (w_H (x_W cx)) (x_memc cx) a).
{ intros a Ha. destruct (Hapart a Ha) as (N1 & N2 & N3). apply Hkm; [lia | exact N1 |].
  intros [X|X]; [exact (N2 X) | exact (N3 X)]. }
split.
- destruct (Hgarr (Z.to_nat c) ltac:(unfold hd_zbytes; rewrite length_map; lia)) as [V _]. rewrite Z2Nat.id in V by lia.
  eapply val_mem_kept; [|exact V]. intros k Hk. apply Ka. lia.
- pose proof (hm_in_ra _ _ _ _ c Hra ltac:(lia)) as R1. fold src in R1.
  intros y Hy. destruct (R1 y Hy) as (sv & Hs & Hok). exists sv. split; [|exact Hok].
  rewrite <- Hs. unfold shadow_of_addr.
  assert (Y8 : 0 <= y / 8 < 2 ^ 44) by (unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in Hamr;
    split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
  set (sa := SHADOW_OFF + y / 8).
  destruct (Z_lt_le_dec sa (shadow_addr (e_F (x_e cx)))) as [Lo|Lo];
  [| destruct (Z_lt_le_dec sa (shadow_addr (e_F (x_e cx)) + 116)) as [Hi|Hi]].
  2:{ unfold hsu_fsh_at, hd_fsh, hsu_P0 in Hfsh. unfold hd_fsh in Hfsh0.
      replace sa with (shadow_addr (e_F (x_e cx)) + (sa - shadow_addr (e_F (x_e cx)))) by lia.
      assert (L116 : Z.of_nat (length (hi_shA headamp_himg_B)) = 116) by reflexivity.
      rewrite (Hfsh (sa - shadow_addr (e_F (x_e cx))) ltac:(rewrite L116; lia)).
      rewrite (Hfsh0 (sa - shadow_addr (e_F (x_e cx))) ltac:(rewrite L116; lia)).
      reflexivity. }
  all: apply Hkm; [unfold sa, SHADOW_OFF; lia | unfold sa, SHADOW_OFF, T_SEG_STK, ASTACK in *; lia |].
  all: intros [X|X]; [unfold hd_inw in X; cbn [hi_w1 headamp_himg_B] in X;
       repeat (apply Exists_cons in X as [X|X]; [cbn [fst snd hd_xv] in X|]); [..|apply Exists_nil in X; exact X] | ].
  all: unfold sa, shadow_addr, SHADOW_OFF, in_app, kLowShadowBeg, kHighMemBeg, amem_range, kLowMemEnd, kHighMemEnd, Layout.PP_SIZE in *; lia.
Qed.

End g.

(* ---- the input cursor: one byte read ---- *)
Lemma hbp_nth_skipn : forall (l : list byte) j bb r, skipn j l = bb :: r ->
(j < length l)%nat /\ nth j l (Z_to_bv 8 0) = bb.
Proof.
induction l as [|x l IH]; intros j bb r H; destruct j as [|j]; cbn [skipn length nth] in *; try discriminate.
- injection H as <- <-. split; [lia | reflexivity].
- destruct (IH j bb r H) as [H1 H2]. split; [lia | exact H2].
Qed.
Lemma hbp_suffix_step : forall rest r, hsu_suffix rest r -> hsu_suffix rest (snd (fuzz_u8 r)).
Proof.
intros rest r (j & Hj & ->). destruct (skipn j rest) as [|bb r'] eqn:E; cbn [fuzz_u8 snd].
- exists j. split; [exact Hj | symmetry; exact E].
- destruct (hbp_nth_skipn rest j bb r' E) as [Hjl _]. exists (S j). split; [lia|].
  replace (S j) with (1 + j)%nat by lia. rewrite <- skipn_skipn, E. reflexivity.
Qed.

(* ---- the tactics of the pieces ---- *)
Ltac hbp_take Hat l v H := pose proof (hbp_at_get _ _ _ _ _ l v Hat ltac:(hbp_in)) as H; cbn [hd_at hd_xv] in H.
Ltac hbp_from Hat := lazymatch goal with |- hd_at _ _ _ _ _ ?l ?v => exact (hbp_at_get _ _ _ _ _ l v Hat ltac:(hbp_in)) end.
Ltac hbp_list := unfold hsu_at_cx, hsu_at;
cbn [hsu_L_N hsu_L_SEL hsu_L_KEY hsu_L_P hsu_Rc0 hsu_Rc1 hsu_Kc hsu_cur2 app];
repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd].
(* every location of a list keeps its value: registers outside clob (Hkeep), cells by celltac *)
Ltac hbp_kept Hkeep celltac :=
cbn [hsu_L_N hsu_L_SEL hsu_L_KEY hsu_L_P hsu_Rc0 hsu_Rc1 hsu_Kc hsu_cur2 app];
repeat apply Forall_cons; try apply Forall_nil; cbn [fst hbp_kept_loc hd_xv];
first [ apply Hkeep; [cbv; discriminate | hbp_notin]
      | let j := fresh "j" in let Hj := fresh "Hj" in intros j Hj; celltac ].
Ltac hbp_regs234 Hkeep := let r := fresh "r" in intros r [-> | [-> | ->]]; (apply Hkeep; [cbv; discriminate | hbp_notin]).

Print Assumptions hbp_tbl_ok.
Print Assumptions hbp_core_step.
Print Assumptions hbp_pp_append.
Print Assumptions hbp_input_now.
