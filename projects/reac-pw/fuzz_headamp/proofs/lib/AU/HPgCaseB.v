(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_role/lib/Reusable/YCbq.v aj_intrin_at (lines 2155-2206) restated for image A's code with the callee's same_but_materialized kept as same_io in the post. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_role/lib/A/RPgW8Call.v at 888d1ffb4c3 for reac-pw/fuzz_headamp image A: module paths changed, w_intrin_at renamed hd_intrin_at, role's RPgCfgChanges.cfg_segs_low replaced by HPgSteps.img_segs_low over headamp's segments; the two instances hd_memset_at / hd_memcpy_at are new. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_headamp/lib/A/HPgIntrin.v at 021dba8dbbd; hd_intrin_at renamed cb_intrin_at and stated over image B's segments (lib/AU/Img0U.v rsegs, lib/AU/HPgSteps.v img_segs_low, AR_laws from YG0q.AR_laws_ok), hd_memset_at / hd_memcpy_at renamed cb_memset_at / cb_memcpy_at with the entry pc made a parameter (image B's entries CB_ASAN_MEMSET 0x52228 and CB_ASAN_MEMCPY 0x51d8c stated as constants). *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_role/lib/A/RPgW6cKit.v at 80bf14ccf11 (PART 1, a segment's start facts at a cut); rs_ -> cb_, restated over lib/AU/HPgSeg.v (hsu_pre, hsu_core, hsu_E1, hsu_in, hsu_fsh_at) at image B's record headamp_himg_B: the frame for locals of class 4 (1024 bytes, 128 shadow bytes), the 116-byte prologue pattern in place of role's 52, R + 0x220 in place of 0x1a0, image B's three write ranges of hi_w1, the image fact segs_low taken from lib/AU/HPgSteps.v img_segs_low instead of a Section hypothesis. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_role/lib/A/RPgW6aBase.v at 80bf14ccf11 (w6_ctx, w6_caller_saved and Section seq only; w6_in as cb_in); w6_ -> cb_, the frame (4, pos) and R + 0x220 of image B, R's cells [R, R + 0x198), and the block post w6_post replaced by the shared layer's hdu_blk_postE (lib/AU/HPgSteps.v), rl_blk_post by hdu_blk_post. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_role/lib/A/RPgW6a.v at 80bf14ccf11 (its generic helpers only: the list tactics, the register and location-list lemmas, the geometry of a cut, the image's first write range, the suffix and cursor lemmas, pp's image length, the cut's geometry and context, the core step, the input kept, the block step and the side tactics); w6_ -> cb_, over lib/AU/HPgSeg.v at image B: w6_geo with image B's frame (1024 / 128 bytes, R + 0x220) and the conjuncts F mod 32 = 0 and in_app pp, its head- and tail-specific cell lemmas replaced by write-set-free disjointness lemmas, w6_in_kept and the side tactics generalised over the write set, cb_blkE_step added for a block that writes. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_role/lib/A/RPgW6aHead.v at 80bf14ccf11 (w6h_div, w6h_sh_e, w6h_e_mod8, w6h_bounds, w6h_callee, w6h_val_kept, w6h_chunk0, w6h_region_nth, w6h_chunks); w6h_ -> cb_, the shadow and alignment lemmas generalised over the offset, the bounds at class 4 (1024 bytes, 128 shadow bytes) and e62's 104 bytes at F + 0x210. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_role/lib/A/RPgW7bBase.v at f3898085bda (w7_post,
   w7_post_of_run), RPgW7bKit.v at f3898085bda (w7_kept, w7_hull, w7_ra_kept, w7_hull_kept, w7_strok, w7_strz and
   their lemmas), RPgCfgChanges.v at f3898085bda (kept_run), RPgW6aTail.v at f3898085bda (tl_byte, tl_val_of_chunk,
   tl_val_at), RPgW6aC2h.v at f3898085bda (c2_all256, c2_envz, c2_nz, c2_notin, c2_kio) and RPgW7bIter.v at
   f3898085bda (w7_cs_bv, w7_cs_out, w7_reg_eq), by way of lib/AU/HPgW6bC1k.v's and
   HPgW6bC1.v's hb1_* copies for reac-pw/fuzz_headamp's image B: moved here and renamed cb_* by the dedup, one copy
   kept for the equal helpers of 17 lib/AU files (HPgE0Base, HPgW7bBase, HPgW7bIter, HPgW6aTail, HPgW6aC2 and
   others); cb_val_at_rng is new. *)
(* reac-pw/fuzz_headamp image B (fuzz_headamp.asan-ubsan, pinned sha256
   53edda9bdeeba1803865babfecb1af6732babe47ab83c64d38cc59a90d717a94; every address measured on the unstripped twin
   1674e30a0698f381704e66d2398d7906c881f4ba8fc619cb41b89fb97ad112ff, whose loaded sections are byte-equal to the
   pin's except .note.gnu.build-id): the shared kit of the walk pieces of ent_build's switch (the pod loop of the build segment M01 of
   LLVMFuzzerTestOneInput 0x80c40, lib/AU/HPgSeg.v hsu_piece_W6a_* / W6b / W6c / W7a / W7b). Proves no function
   (kind: segment-lemma support): no instruction is stepped here.

   IMAGE B'S FACTS THE KIT USES (lib/AU/HPgImgB.v headamp_himg_B): the real frame [R, R + 0x220) below the entry sp
   (hi_rsz); the frame for locals F is the side-stack frame (4, pos) the harness holds (hi_cid = 4: 1024 bytes, 128
   shadow bytes from shadow_addr F); the prologue's frame-shadow pattern headamp_B_shA is 116 bytes, every one >= 8
   (lib/AU/HPgMem.v hmu_sh_P0_big); M01 writes hi_w1 = [F + 0x20, F + 0x278) (t .. e62), [shadow_addr F,
   shadow_addr F + 116) and R's cells [R, R + 0x198), the pp block and the callees' stack [R - T_SEG_STK, R);
   the frame objects t F+0x20, ch F+0xa0, r F+0xe0, e F+0xf0, e42 F+0x180, e62 F+0x210, res F+0x2a0, x F+0x2c0; the
   runtime's __asan_memset at 0x52228 and __asan_memcpy at 0x51d8c.

   WHAT IS HERE.
   1. Registers, R-relative cells and location lists (cb_regok, cb_reg_kept, cb_at_*, cb_side / cb_atl_tr: a
      location list carried across a block that keeps every register outside clob and every byte outside Wr).
   2. The geometry of a cut (cb_geo: R above the ceiling with the callees' stack below it, F and its shadow, pp)
      and the disjointness facts a caller instantiates for its own write set (cb_R_cell, cb_cell_not_*, cb_fsh_*,
      cb_pp_*, cb_shin); the image's first write range (cb_inw1); the frame's shadow and alignment arithmetic
      (cb_sh_off, cb_c_mod8, cb_bounds).
   3. The context every block runs in (cb_ctx) and the chaining of block posts: a block's post is the shared
      layer's hdu_blk_postE (a pure-read block's hdu_blk_post is one with any write set: cb_post_of_blk); two of
      them chain into one (cb_post_seq, cb_blk_seq).
   4. A segment's start facts at a cut (cb_wr, cb_pre_geom, cb_core_kept, cb_wr_shadow, cb_in_now, cb_rom_now) and
      a cut's geometry, context and core carried across a block (cb_geo_of, cb_ctx_of, cb_core_step,
      cb_pod_base_mv, cb_in_kept, cb_blkE_step, cb_blk_step).
   5. The step at a `jal` to __asan_memset / __asan_memcpy (cb_intrin_at, cb_memset_at, cb_memcpy_at), the entry
      pc a parameter: a caller passes CB_ASAN_MEMSET or CB_ASAN_MEMCPY with the kernel's contract at that pc.
   6. The tactics cb_unf, cb_mem, cb_subs and cb_sides (the side conditions of a carried list, the write set an
      argument). *)
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
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require YG0q.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YI16 YM05.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Pod Require Import Cursor Model Layout.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.AU Require Import Img0U.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.A Require Import HPgBase HPgCSpec.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.AU Require Import HPgImgB HPgMem HPgSteps HPgSeg.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

(* lia without the disjunctions of the context *)
Local Ltac zl := repeat match goal with H : _ \/ _ |- _ => clear H end; lia.

(* ======================================== list tactics ======================================== *)
(* the location lists of the pod loop's cuts (lib/AU/HPgSeg.v), as literal lists *)
Ltac cb_unf := cbv [hsu_L_pod hsu_Rc0 hsu_Rc1 hsu_Kc hsu_L_Dc hsu_L_D app].
(* membership in a literal list *)
Ltac cb_mem := cbn [In]; repeat first [left; reflexivity | right].

(* image B's runtime entries of the two memory intrinsics (the `jal` targets of the harness's calls) *)
Definition CB_ASAN_MEMSET : Z := 0x52228.
Definition CB_ASAN_MEMCPY : Z := 0x51d8c.

(* ======================================== registers ======================================== *)
Definition cb_regok (clob : list (bv 5)) (r : Z) : bool :=
negb (bv_unsigned (Z_to_bv 5 r) =? 0) && negb (existsb (fun c => bv_eqb c (Z_to_bv 5 r)) clob).

Lemma cb_kept_bv : forall (regs regs' : bvmap 5 word) (clob : list (bv 5)) (q : bv 5),
(forall r : bv 5, bv_unsigned r <> 0 -> ~ In r clob -> getr regs' r = getr regs r) ->
negb (bv_unsigned q =? 0) && negb (existsb (fun c => bv_eqb c q) clob) = true ->
getr regs' q = getr regs q.
Proof.
intros regs regs' clob q K H. apply andb_prop in H as [H1 H2]. apply negb_true_iff in H1. apply negb_true_iff in H2.
apply K.
- apply Z.eqb_neq. exact H1.
- intros Hin. assert (E : existsb (fun c => bv_eqb c q) clob = true).
  { apply existsb_exists. exists q. split; [exact Hin|]. unfold bv_eqb. apply Z.eqb_eq. reflexivity. }
  congruence.
Qed.

Lemma cb_reg_kept : forall (regs regs' : bvmap 5 word) clob r,
(forall q : bv 5, bv_unsigned q <> 0 -> ~ In q clob -> getr regs' q = getr regs q) ->
cb_regok clob r = true -> getr regs' (Z_to_bv 5 r) = getr regs (Z_to_bv 5 r).
Proof. intros regs regs' clob r K H. exact (cb_kept_bv regs regs' clob (Z_to_bv 5 r) K H). Qed.

Lemma cb_regZ : forall (regs : bvmap 5 word) (q : bv 5) r, bv_unsigned q = r -> getr regs (Z_to_bv 5 r) = getr regs q.
Proof. intros regs q r <-. rewrite (Z_to_bv_bv_unsigned 5 q). reflexivity. Qed.

(* the registers a call may change (everything but YG0d.acallee_saved and x0) *)
Definition cb_caller_saved : list (bv 5) :=
[1; 5; 6; 7; 10; 11; 12; 13; 14; 15; 16; 17; 28; 29; 30; 31]%bv.

(* the callee-saved registers are exactly the nonzero registers outside cb_caller_saved *)
Lemma cb_callee : forall r : bv 5, bv_unsigned r <> 0 -> ~ In r cb_caller_saved -> acallee_saved (bv_unsigned r).
Proof.
intros r H0 Hn. pose proof (in_nz_regs r H0) as Hin. cbv [nz_regs In] in Hin.
repeat (destruct Hin as [<- | Hin];
[ first
  [ (lazymatch goal with |- context [bv_unsigned ?x] => let v := eval vm_compute in (bv_unsigned x) in
       change (bv_unsigned x) with v end; unfold acallee_saved; lia)
  | (exfalso; apply Hn; cbv [cb_caller_saved In]; repeat (first [left; apply bv_eq; reflexivity | right])) ]
| ]).
destruct Hin.
Qed.

(* a list whose elements all satisfy P, from a list that does and a membership test *)
Lemma cb_fsub : forall {X} (P : X -> Prop) (L L' : list X), Forall P L -> Forall (fun f => In f L \/ P f) L' -> Forall P L'.
Proof.
intros X P L L' HL H. rewrite Forall_forall in *. intros f Hf.
destruct (H f Hf) as [Hi|Hp]; [exact (HL f Hi) | exact Hp].
Qed.

(* ======================================== frame arithmetic ======================================== *)
(* F mod 32 = 0, no division left for lia *)
Lemma cb_div : forall F, F mod 32 = 0 -> F = 32 * (F / 32) /\ shadow_addr F = SHADOW_OFF + 4 * (F / 32).
Proof.
intros F H. pose proof (Z.div_mod F 32 ltac:(lia)) as E. rewrite H, Z.add_0_r in E.
split; [exact E|]. unfold shadow_addr. f_equal. remember (F / 32) as q eqn:Hq. clear Hq. rewrite E.
replace (32 * q) with ((4 * q) * 8) by ring. apply Z.div_mul. lia.
Qed.

(* the shadow byte of the object at F + c, c a multiple of 8 *)
Lemma cb_sh_off : forall F c, F mod 8 = 0 -> c mod 8 = 0 -> shadow_of_addr SHADOW_OFF (F + c) = shadow_addr F + c / 8.
Proof.
intros F c HF Hc. unfold shadow_of_addr, shadow_addr.
pose proof (Z.div_mod F 8 ltac:(lia)) as E1. rewrite HF, Z.add_0_r in E1.
pose proof (Z.div_mod c 8 ltac:(lia)) as E2. rewrite Hc, Z.add_0_r in E2.
replace (F + c) with ((F / 8 + c / 8) * 8) by lia.
rewrite Z.div_mul by lia. ring.
Qed.

Lemma cb_c_mod8 : forall F c, F mod 32 = 0 -> c mod 8 = 0 -> (F + c) mod 8 = 0.
Proof.
intros F c HF Hc.
pose proof (Z.div_mod F 32 ltac:(lia)) as E1. rewrite HF, Z.add_0_r in E1.
pose proof (Z.div_mod c 8 ltac:(lia)) as E2. rewrite Hc, Z.add_0_r in E2.
rewrite E1, E2. replace (32 * (F / 32) + 8 * (c / 8)) with ((4 * (F / 32) + c / 8) * 8) by ring.
apply Z_mod_mult.
Qed.

(* the image's first write range, piece by piece *)
Lemma cb_inw1 : forall e a,
(e_F e + 0x20 <= a < e_F e + 0x278) \/ (shadow_addr (e_F e) <= a < shadow_addr (e_F e) + 116) \/
(e_R e <= a < e_R e + 0x198) -> hd_inw e (hi_w1 headamp_himg_B) a.
Proof.
intros e a H. unfold hd_inw. cbn [hi_w1 headamp_himg_B].
destruct H as [H|[H|H]].
- apply Exists_cons_hd. cbn [fst snd hd_xv]. lia.
- apply Exists_cons_tl, Exists_cons_hd. cbn [fst snd hd_xv]. lia.
- apply Exists_cons_tl, Exists_cons_tl, Exists_cons_hd. cbn [fst snd hd_xv]. lia.
Qed.

(* ======================================== the suffix ======================================== *)
Lemma cb_suffix_skip : forall rest r n, hsu_suffix rest r -> hsu_suffix rest (skipn n r).
Proof.
intros rest r n (j & Hj & ->). rewrite skipn_skipn.
destruct (Nat.le_gt_cases (n + j) (length rest)) as [Hle|Hgt].
- exists (n + j)%nat. split; [exact Hle | reflexivity].
- exists (length rest). split; [lia|]. rewrite !skipn_all2 by lia. reflexivity.
Qed.

Lemma cb_suffix_tl : forall rest b r', hsu_suffix rest (b :: r') -> hsu_suffix rest r'.
Proof.
intros rest b r' (j & Hj & E). exists (S j).
assert (Hl : length (skipn j rest) = S (length r')) by (rewrite <- E; reflexivity).
rewrite length_skipn in Hl. split; [lia|].
replace (S j) with (1 + j)%nat by lia. rewrite <- skipn_skipn, <- E. reflexivity.
Qed.

(* ======================================== pp's image ======================================== *)
Lemma cb_pc_ents_wf : forall sh ps es, Forall (fun kv => pval_wf (snd kv)) ps -> Forall ent_wf (all_ents ps) ->
Forall ent_wf es -> (length es <= 32)%nat ->
(length (pc_ents (PbCut sh ps (Some es))) <= 32)%nat /\ Forall ent_wf (pc_ents (PbCut sh ps (Some es))).
Proof.
intros sh ps es Hk He Hes Hl. unfold pc_ents. cbn [pc_props pc_open].
destruct (first_params ps) as [[iv|es']|] eqn:E.
- split; [cbn; lia | constructor].
- unfold first_params in E. destruct (find _ _) as [kv|] eqn:F; [|discriminate]. cbn in E. injection E as E.
  apply find_some in F as [Hin _]. split.
  + rewrite Forall_forall in Hk. specialize (Hk kv Hin). rewrite E in Hk. exact Hk.
  + apply all_ents_Forall in He. rewrite Forall_forall in He. specialize (He kv Hin). rewrite E in He. exact He.
- split; [exact Hl | exact Hes].
Qed.

Lemma cb_pp_len : forall sh ps es, hsu_wf sh ps -> Forall ent_wf es -> (length es < 32)%nat ->
Z.of_nat (length (pc_image (PbCut sh ps (Some es)))) = Layout.PP_SIZE.
Proof.
intros sh ps es (_ & Hkv & Hae & Hlp) Hes Hle.
assert (Hpv : Forall (fun kv => pval_wf (snd kv)) ps) by (eapply Forall_impl; [|exact Hkv]; intros kv [_ H]; exact H).
destruct (cb_pc_ents_wf sh ps es Hpv Hae Hes ltac:(lia)) as [Hn Hw].
unfold pc_image. cbn [pc_shape pc_props pc_open]. apply length_pp_image.
- destruct (pc_buf_len_open sh ps es Hpv Hae Hes) as [H _]. lia.
- exact Hn.
- eapply Forall_impl; [|exact Hw]. intros e (_ & H1 & H2). rewrite H1. lia.
Qed.

Lemma cb_notin : forall (r : bv 5) (l : list (bv 5)), existsb (fun c => bv_eqb c r) l = false -> ~ In r l.
Proof.
intros r l H Hin. induction l as [|c l IH]; [exact Hin|]. cbn [existsb] in H. apply orb_false_iff in H as [H1 H2].
destruct Hin as [<-|Hin]; [|exact (IH H2 Hin)]. unfold bv_eqb in H1. rewrite Z.eqb_refl in H1. discriminate H1.
Qed.
Lemma cb_nz : forall r : bv 5, (bv_unsigned r =? 0) = false -> bv_unsigned r <> 0.
Proof. intros r H. apply Z.eqb_neq. exact H. Qed.
Lemma cb_cs_bv : forall r, acallee_saved r -> bv_unsigned (Z_to_bv 5 r) = r.
Proof. intros r Hr. unfold acallee_saved in Hr. rewrite Z_to_bv_unsigned. apply bv_wrap_small. unfold bv_modulus. cbn. lia. Qed.
Lemma cb_cs_out : forall r (l : list (bv 5)), acallee_saved r -> ~ In r (map (fun c => bv_unsigned c) l) ->
  ~ In (Z_to_bv 5 r) l.
Proof.
intros r l Hr Hn Hin. apply Hn. rewrite <- (cb_cs_bv r Hr). exact (in_map (fun c => bv_unsigned c) l _ Hin).
Qed.
Lemma cb_reg_eq : forall (regs regs' : bvmap 5 word) (r : bv 5),
  getr regs' (Z_to_bv 5 (bv_unsigned r)) = getr regs (Z_to_bv 5 (bv_unsigned r)) -> getr regs' r = getr regs r.
Proof. intros regs regs' r H. rewrite !Z_to_bv_bv_unsigned in H. exact H. Qed.
Ltac cb_kio := first [apply same_io_refl | eapply same_io_trans; [| apply same_io_wvb]; cb_kio].
Definition cb_envz (z : Z) : env := mkEnv (fun _ => Z_to_bv 64 z) (fun _ => []).
Lemma cb_all256 : forall (P : Z -> bool), forallb P (map Z.of_nat (seq 0 256)) = true ->
  forall c, 0 <= c < 256 -> P c = true.
Proof.
intros P H c Hc. rewrite forallb_forall in H. apply H. apply in_map_iff. exists (Z.to_nat c).
split; [lia | apply in_seq; lia].
Qed.

Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.

(* an 8-byte cell holds v exactly when it holds v mod 2^64 *)
Lemma cb_val_mod : forall m a v, val_mem rsegs m a 8 (v mod 2 ^ 64) <-> val_mem rsegs m a 8 v.
Proof.
intros m a v. unfold val_mem.
assert (E : forall k, YO0f.le_byte (v mod 2 ^ 64) 8 k = YO0f.le_byte v 8 k).
{ intros k. unfold YO0f.le_byte. change (8 * Z.of_nat 8) with 64. rewrite Z.mod_mod by lia. reflexivity. }
split; intros H k Hk; specialize (H k Hk); [rewrite <- E | rewrite E]; exact H.
Qed.

(* a 4-byte cell holds v exactly when it holds v mod 2^32 *)
Lemma cb_val_mod32 : forall m a v, val_mem rsegs m a 4 (v mod 2 ^ 32) <-> val_mem rsegs m a 4 v.
Proof.
intros m a v. unfold val_mem.
assert (E : forall k, YO0f.le_byte (v mod 2 ^ 32) 4 k = YO0f.le_byte v 4 k).
{ intros k. unfold YO0f.le_byte. change (8 * Z.of_nat 4) with 32. rewrite Z.mod_mod by lia. reflexivity. }
split; intros H k Hk; specialize (H k Hk); [rewrite <- E | rewrite E]; exact H.
Qed.

(* an aview value kept, as a val_mem *)
Lemma cb_val_kept : forall H (m m' : word -> option byte) a n v,
(forall k, 0 <= k < Z.of_nat n -> aview rsegs H m' (a + k) = aview rsegs H m (a + k)) ->
val_mem rsegs (mrestrict H m) a n v -> val_mem rsegs (mrestrict H m') a n v.
Proof. intros H m m' a n v Hk Hv. exact (val_mem_kept rsegs H H m m' a n v Hk Hv). Qed.

(* a one-byte chunk of value 0 *)
Lemma cb_chunk0 : forall E H mem base o,
YP09.chunk_ok rsegs E (mrestrict H mem) base (YP09.mkChunk o (CVal 1 (SLit 0))) -> aview rsegs H mem (base + o) = Some 0.
Proof.
intros E H mem base o Hc. destruct (Hc 0 ltac:(cbn; lia)) as (b & Hb1 & Hb2).
assert (Hb3 : mbyte rsegs (mrestrict H mem) (base + o) = Some b) by (rewrite <- Hb2; f_equal; cbn; ring).
unfold aview. rewrite Hb3. cbn [cbyte YP09.c_val] in Hb1. injection Hb1 as <-.
first [reflexivity | (vm_compute; reflexivity)].
Qed.

(* a region of a run's state, and its chunks *)
Lemma cb_region_nth : forall E ss ms i r (H : word -> bool),
st_ok rsegs E ss (restrict H ms) -> nth_error (ss_mem ss) i = Some r -> region_ok rsegs E (mrestrict H (ms_mem ms)) r.
Proof.
intros E ss ms i r H HS Hi. destruct (st_ok_mem_ok rsegs E ss (restrict H ms) HS) as (_ & Hrs & _).
exact (proj1 (Forall_forall _ _) Hrs r (nth_error_In _ _ Hi)).
Qed.
Lemma cb_chunks : forall E m n b cs lo hi wlo whi,
region_ok rsegs E m (YP09.mkRegion (Some n) lo hi wlo whi cs) -> bv_unsigned (ew E n) = b ->
forall c, In c cs -> YP09.chunk_ok rsegs E m b c.
Proof.
intros E m n b cs lo hi wlo whi (_ & _ & _ & Hcs) Hn c Hc.
pose proof (proj1 (Forall_forall _ _) Hcs _ Hc) as Hck. cbn [YP09.r_base base_val] in Hck. rewrite Hn in Hck. exact Hck.
Qed.

(* ======================================== location lists ======================================== *)
Lemma cb_at_get : forall H mem regs e (L : list (hd_loc * Z)) l v,
hsu_at rsegs H mem regs e L -> In (l, v) L -> hd_at rsegs H mem regs e l v.
Proof. intros H mem regs e L l v A Hin. unfold hsu_at in A. rewrite Forall_forall in A. exact (A _ Hin). Qed.

Lemma cb_at_reg : forall H mem regs e (L : list (hd_loc * Z)) r v (q : bv 5),
hsu_at rsegs H mem regs e L -> In (LReg r, v) L -> bv_unsigned q = r -> getr regs q = w64 v.
Proof.
intros H mem regs e L r v q A Hin Hq. rewrite <- (cb_regZ regs q r Hq).
exact (cb_at_get H mem regs e L (LReg r) v A Hin).
Qed.

Lemma cb_at_cell8 : forall H mem regs e (L : list (hd_loc * Z)) b o v,
hsu_at rsegs H mem regs e L -> In (LCell b o, v) L -> val_mem rsegs (mrestrict H mem) (hd_xv e b + o) 8 v.
Proof. intros H mem regs e L b o v A Hin. apply cb_val_mod. exact (cb_at_get H mem regs e L (LCell b o) v A Hin). Qed.

(* a location list carried across a block that keeps every register outside clob and every byte outside Wr *)
Definition cb_side (clob : list (bv 5)) (Wr : Z -> Prop) (e : hd_env) (f : hd_loc * Z) : Prop :=
match fst f with
| LReg r => cb_regok clob r = true
| LCell b o => forall i, 0 <= i < 8 -> 0 <= hd_xv e b + o + i < 2 ^ 64 /\ ~ Wr (hd_xv e b + o + i)
end.
Lemma cb_atl_tr : forall (Wr : Z -> Prop) clob H mem H' mem' regs regs' e L,
(forall q : bv 5, bv_unsigned q <> 0 -> ~ In q clob -> getr regs' q = getr regs q) ->
(forall a, 0 <= a < 2 ^ 64 -> ~ Wr a -> aview rsegs H' mem' a = aview rsegs H mem a) ->
Forall (cb_side clob Wr e) L ->
hsu_at rsegs H mem regs e L -> hsu_at rsegs H' mem' regs' e L.
Proof.
intros Wr clob H mem H' mem' regs regs' e L K M C A. unfold hsu_at in *.
apply (hm_atl_kept rsegs H mem H' mem' regs regs' e L A).
intros f Hf. rewrite Forall_forall in C. specialize (C f Hf). unfold cb_side in C.
destruct f as [[r|b o] v]; cbn [fst hm_keeps] in *.
- exact (cb_reg_kept regs regs' clob r K C).
- intros i Hi. destruct (C i Hi) as [Hr Hn]. exact (M _ Hr Hn).
Qed.

(* ======================================== the geometry of a cut ========================================
   R's frame above the ceiling with the callees' stack below it, the frame for locals F (class 4: 1024 bytes) and
   its 128 shadow bytes and the block pp below the ceiling, apart from each other; F 32-aligned and pp in the
   application's memory. *)
Definition cb_geo (R F pp : Z) : Prop :=
alloc_ceiling + T_SEG_STK <= R /\ R + 0x220 <= 2 ^ 47 /\ kHighMemBeg <= R - T_SEG_STK /\
in_app F 1024 /\ 4096 <= F /\ F + 1024 <= alloc_ceiling /\ 0 <= shadow_addr F /\ shadow_addr F + 128 <= alloc_ceiling /\
(F + 1024 <= shadow_addr F \/ shadow_addr F + 128 <= F) /\
4096 <= pp /\ pp + Layout.PP_SIZE <= alloc_ceiling /\
(pp + Layout.PP_SIZE <= shadow_addr F \/ shadow_addr F + 128 <= pp) /\
(pp + Layout.PP_SIZE <= F \/ F + 1024 <= pp) /\
F mod 32 = 0 /\ in_app pp Layout.PP_SIZE.

(* an R-relative cell of M01's range [R, R + 0x198) is a machine address *)
Lemma cb_R_cell : forall R F pp o i, cb_geo R F pp -> ((0 <=? o) && (o + 8 <=? 0x198))%bool = true -> 0 <= i < 8 ->
0 <= R + o + i < 2 ^ 64.
Proof.
intros R F pp o i G Hb Hi. apply andb_prop in Hb as [H1 H2]. apply Z.leb_le in H1. apply Z.leb_le in H2.
destruct G as (G1 & G2 & _). unfold T_SEG_STK, ASTACK in G1. pose proof alloc_ceiling_value as (C1 & _). zl.
Qed.

(* the real frame's cells [R, R + 0x220) lie above the frame for locals, its shadow and pp *)
Lemma cb_cell_not_frame : forall R F pp o i, cb_geo R F pp -> 0 <= o -> o + 8 <= 0x220 -> 0 <= i < 8 ->
~ (F <= R + o + i < F + 1024).
Proof. intros R F pp o i G Ho Ho' Hi. destruct G as (G1 & _ & _ & _ & _ & G6 & _). unfold T_SEG_STK, ASTACK in G1. zl. Qed.

Lemma cb_cell_not_fsh : forall R F pp o i, cb_geo R F pp -> 0 <= o -> o + 8 <= 0x220 -> 0 <= i < 8 ->
~ (shadow_addr F <= R + o + i < shadow_addr F + 128).
Proof.
intros R F pp o i G Ho Ho' Hi. destruct G as (G1 & _ & _ & _ & _ & _ & _ & G8 & _). unfold T_SEG_STK, ASTACK in G1. zl.
Qed.

Lemma cb_cell_not_pp : forall R F pp o i, cb_geo R F pp -> 0 <= o -> o + 8 <= 0x220 -> 0 <= i < 8 ->
~ (pp <= R + o + i < pp + Layout.PP_SIZE).
Proof.
intros R F pp o i G Ho Ho' Hi. destruct G as (G1 & _ & _ & _ & _ & _ & _ & _ & _ & _ & G11 & _).
unfold T_SEG_STK, ASTACK in G1. zl.
Qed.

(* the frame's shadow bytes lie apart from the frame and from pp, and below the callees' stack *)
Lemma cb_fsh_not_frame : forall R F pp i, cb_geo R F pp -> 0 <= i < 128 -> ~ (F <= shadow_addr F + i < F + 1024).
Proof. intros R F pp i G Hi. destruct G as (_ & _ & _ & _ & _ & _ & _ & _ & G9 & _). lia. Qed.

Lemma cb_fsh_not_pp : forall R F pp i, cb_geo R F pp -> 0 <= i < 128 ->
~ (pp <= shadow_addr F + i < pp + Layout.PP_SIZE).
Proof. intros R F pp i G Hi. destruct G as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & G12 & _). lia. Qed.

Lemma cb_fsh_low : forall R F pp i, cb_geo R F pp -> 0 <= i < 128 ->
0 <= shadow_addr F + i /\ shadow_addr F + i < R - T_SEG_STK.
Proof. intros R F pp i G Hi. destruct G as (G1 & _ & _ & _ & _ & _ & G7 & G8 & _). zl. Qed.

(* pp's bytes lie apart from the frame, and below the callees' stack *)
Lemma cb_pp_not_frame : forall R F pp i, cb_geo R F pp -> 0 <= i < Layout.PP_SIZE -> ~ (F <= pp + i < F + 1024).
Proof. intros R F pp i G Hi. destruct G as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & G13 & _). lia. Qed.

Lemma cb_pp_low : forall R F pp i, cb_geo R F pp -> 0 <= i < Layout.PP_SIZE ->
0 <= pp + i /\ pp + i < R - T_SEG_STK.
Proof. intros R F pp i G Hi. destruct G as (G1 & _ & _ & _ & _ & _ & _ & _ & _ & G10 & G11 & _). zl. Qed.

(* the frame's bytes lie below the callees' stack *)
Lemma cb_frame_low : forall R F pp i, cb_geo R F pp -> 0 <= i < 1024 ->
0 <= F + i /\ F + i < R - T_SEG_STK.
Proof. intros R F pp i G Hi. destruct G as (G1 & _ & _ & _ & G5 & G6 & _). zl. Qed.

(* the shadow byte of an application address lies in the shadow band: a machine address, outside the frame, the
   callees' stack and R's frame, and pp; outside the frame's first 116 shadow bytes when the caller shows it *)
Lemma cb_shin : forall R F pp x, cb_geo R F pp -> 0 <= x < kHighMemEnd ->
~ (shadow_addr F <= shadow_of_addr SHADOW_OFF x < shadow_addr F + 116) ->
0 <= shadow_of_addr SHADOW_OFF x < 2 ^ 64 /\
~ (F <= shadow_of_addr SHADOW_OFF x < F + 1024) /\
~ (R - T_SEG_STK <= shadow_of_addr SHADOW_OFF x < R + 0x220) /\
~ (pp <= shadow_of_addr SHADOW_OFF x < pp + Layout.PP_SIZE) /\
~ (shadow_addr F <= shadow_of_addr SHADOW_OFF x < shadow_addr F + 116).
Proof.
intros R F pp x G Hx Hn.
destruct G as (G1 & G2 & G3 & G4 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & G15).
pose proof (hm_shadow_band x Hx) as Hb.
pose proof (hm_shadow_not_app x F 1024 Hx G4) as Hf.
pose proof (hm_shadow_not_app x pp Layout.PP_SIZE Hx G15) as Hp.
unfold kLowMemEnd, kHighMemBeg in Hb. unfold kHighMemBeg in G3.
split; [lia|]. split; [exact Hf|]. split; [lia|]. split; [exact Hp | exact Hn].
Qed.

(* the frame (class 4, 1024 bytes) of an in_app address F: its bounds, its shadow below the ceiling, apart from F,
   and e62's 104 bytes at F + 0x210 in the shadow map's range *)
Lemma cb_bounds : forall F, F mod 32 = 0 -> in_app F 1024 ->
4096 <= F /\ F + 1024 <= alloc_ceiling /\ 0 <= shadow_addr F /\ shadow_addr F + 128 <= alloc_ceiling /\
(F + 1024 <= shadow_addr F \/ shadow_addr F + 128 <= F) /\ amem_range (F + 0x210) 104.
Proof.
intros F Hm Ha. destruct (cb_div F Hm) as [E1 E2]. pose proof asan_consts as (C1 & _). rewrite E2.
remember (F / 32) as q eqn:Hq. clear Hq.
unfold in_app, amem_range, SHADOW_OFF, kLowShadowBeg, kLowMemEnd, kHighMemBeg, kHighMemEnd, ASAN_CEIL in *.
lia.
Qed.

(* ===================== what a cut may have changed since the segment's start =====================
   outside [0, 2^64), the callees' stack [R - T_SEG_STK, R), and M01's write set hsu_E1 (hi_w1 and pp) *)
Definition cb_wr (cx : hsu_scx rsegs) (a : Z) : Prop :=
(a < 0 \/ 2 ^ 64 <= a) \/ (e_R (x_e rsegs cx) - T_SEG_STK <= a < e_R (x_e rsegs cx)) \/
hsu_E1 rsegs headamp_himg_B cx a.

(* ======================================== the cursor ======================================== *)
Lemma cb_cur_skip : forall (cx : hsu_scx rsegs) rest r n,
hsu_cur rsegs cx rest (skipn n r) = hsu_cur rsegs cx rest r + Z.of_nat (Nat.min n (length r)).
Proof. intros cx rest r n. unfold hsu_cur. rewrite length_skipn. lia. Qed.

Lemma cb_cur_pos : forall (cx : hsu_scx rsegs) rest (b : byte) r, hsu_in rsegs headamp_himg_B cx rest ->
hsu_suffix rest (b :: r) -> 0 < hsu_cur rsegs cx rest r - 1.
Proof.
intros cx rest b r HI (j & Hj & E). destruct HI as (Hleft & _ & _ & _ & _ & Hsrc & _).
assert (Hl : length (skipn j rest) = S (length r)) by (rewrite <- E; reflexivity).
rewrite length_skipn in Hl. unfold hsu_cur. lia.
Qed.

(* the input bytes r at cursor cur, as headamp_build_contract gives them (garr8, range_addressable, 0 < cur,
   cur + |r| <= 2 ^ 63, amem_range) and outside the callees' stack below R and R's cells [R, R + 0x198) *)
Definition cb_in (W : world rsegs) (memc : word -> option byte) (R cur : Z) (r : list byte) : Prop :=
garr8 rsegs (mrestrict (w_H W) memc) cur (hd_zbytes r) /\
range_addressable (aview rsegs (w_H W) memc) SHADOW_OFF cur (Z.of_nat (length r)) /\
0 < cur /\ cur + Z.of_nat (length r) <= 2 ^ 63 /\ amem_range cur (Z.of_nat (length r)) /\
(forall a, cur <= a < cur + Z.of_nat (length r) -> ~ (R - T_SEG_STK <= a < R + 0x198)).

Lemma cb_kept_run : forall (Zn : Z -> Prop) E rs (H : word -> bool) (m0 m1 m2 : word -> option byte),
  (forall a, 0 <= a < 2 ^ 64 -> ~ Zn a -> aview rsegs H m1 a = aview rsegs H m0 a) ->
  frame_of E rs (mrestrict H m1) (mrestrict H m2) ->
  (forall a, in_wrange E rs a -> Zn a) ->
  forall a, 0 <= a < 2 ^ 64 -> ~ Zn a -> aview rsegs H m2 a = aview rsegs H m0 a.
Proof.
intros Zn E rs H m0 m1 m2 HK HF HW a Ha Hz. rewrite <- (HK a Ha Hz). unfold aview, mbyte.
rewrite (HF (Z_to_bv 64 a)); [reflexivity|]. rewrite unsigned_lit_small by exact Ha. intros X. exact (Hz (HW a X)).
Qed.
Lemma cb_byte : forall v (w k : nat), (k < w)%nat -> (w <= 8)%nat ->
  Z_to_bv 8 (Z.shiftr (bv_unsigned (Z_to_bv 64 v)) (8 * Z.of_nat k)) = Z_to_bv 8 (YO0f.le_byte v w k).
Proof.
intros v w k Hk Hw. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold YO0f.le_byte, bv_wrap.
change (bv_modulus 8) with (2 ^ 8). change (bv_modulus 64) with (2 ^ 64). change 256 with (2 ^ 8).
rewrite Z.mod_mod by lia.
apply Z.bits_inj'. intros i Hi.
destruct (Z_lt_le_dec i 8) as [Hi8|Hi8].
- rewrite !(Z.mod_pow2_bits_low _ 8 i) by lia. rewrite !Z.shiftr_spec by lia.
  rewrite (Z.mod_pow2_bits_low v 64) by lia. rewrite (Z.mod_pow2_bits_low v (8 * Z.of_nat w)) by lia. reflexivity.
- rewrite !(Z.mod_pow2_bits_high _ 8 i) by lia. reflexivity.
Qed.
Lemma cb_val_of_chunk : forall E mem base off (n : N) e v,
  YP09.chunk_ok rsegs E mem base (YP09.mkChunk off (CVal n e)) -> sv_denot E e = Z_to_bv 64 v -> (N.to_nat n <= 8)%nat ->
  val_mem rsegs mem (base + off) (N.to_nat n) v.
Proof.
intros E mem base off n e v H He Hn k Hk. unfold YP09.chunk_ok in H. cbn [YP09.c_off YP09.c_val YP09.c_len cv_len] in H.
pose proof (N_nat_Z n) as Hnn.
destruct (H (Z.of_nat k) ltac:(lia)) as (b & Hb1 & Hb2). cbn [YP09.cbyte] in Hb1. rewrite He in Hb1.
unfold YP09.byte_of_word in Hb1. injection Hb1 as <-. rewrite Hb2. f_equal. apply cb_byte; lia.
Qed.
Lemma cb_val_at : forall E ss H ms i r off (n : N) e v b a,
  st_ok rsegs E ss (restrict H ms) -> nth_error (ss_mem ss) i = Some r ->
  In (YP09.mkChunk off (CVal n e)) (YP09.r_chunks r) -> base_val E (YP09.r_base r) = b ->
  sv_denot E e = Z_to_bv 64 v -> (N.to_nat n <= 8)%nat -> a = b + off ->
  val_mem rsegs (mrestrict H (ms_mem ms)) a (N.to_nat n) v.
Proof.
intros E ss H ms i r off n e v b a HS Hi Hc Hb He Hn ->.
destruct (st_ok_mem_ok rsegs E ss (restrict H ms) HS) as (_ & Hok & _).
rewrite Forall_forall in Hok. specialize (Hok r (nth_error_In _ _ Hi)).
pose proof (YP09.region_ok_chunk rsegs E _ r _ Hok Hc) as Hck. rewrite Hb in Hck.
exact (cb_val_of_chunk E _ b off n e v Hck He Hn).
Qed.
Lemma cb_val_at_rng : forall E ss (H : word -> bool) ms i rg off (n : N) e v b a,
  st_ok rsegs E ss (restrict H ms) -> nth_error (ss_mem ss) i = Some rg ->
  In (YP09.mkChunk off (CVal n e)) (YP09.r_chunks rg) -> base_val E (YP09.r_base rg) = b ->
  sv_denot E e = Z_to_bv 64 v -> 0 <= v < 2 ^ (8 * Z.of_N n) -> Z.of_N n <= 8 -> a = b + off ->
  val_mem rsegs (mrestrict H (ms_mem ms)) a (N.to_nat n) v.
Proof.
intros E ss H ms i rg off n e v b a HS Hi Hc Hb He _ Hn Ha.
assert (Hn' : (N.to_nat n <= 8)%nat) by (pose proof (N_nat_Z n); lia).
exact (cb_val_at E ss H ms i rg off n e v b a HS Hi Hc Hb He Hn' Ha).
Qed.
Definition cb_kept (W : world rsegs) (m m' : word -> option byte) (Zn : Z -> Prop) : Prop :=
  forall a, 0 <= a < 2 ^ 64 -> ~ Zn a -> aview rsegs (w_H W) m' a = aview rsegs (w_H W) m a.
Definition cb_hull (x n a : Z) : Prop := shadow_addr x / 8 * 8 <= a < shadow_addr (x + n - 1) / 8 * 8 + 8.
Lemma cb_ra_kept : forall (W : world rsegs) m m' x n,
  range_addressable (aview rsegs (w_H W) m) SHADOW_OFF x n -> 0 <= x ->
  (forall a, cb_hull x n a -> aview rsegs (w_H W) m' a = aview rsegs (w_H W) m a) ->
  range_addressable (aview rsegs (w_H W) m') SHADOW_OFF x n.
Proof.
intros W m m' x n HR Hx HK y Hy. destruct (HR y Hy) as (s & Hs & Hok). exists s. split; [|exact Hok].
rewrite HK; [exact Hs|]. unfold cb_hull, shadow_of_addr. change SHADOW_OFF with 0x7fff8000.
unfold shadow_addr, SHADOW_OFF.
pose proof (Z.div_le_mono x y 8 ltac:(lia) ltac:(lia)) as M1.
pose proof (Z.div_le_mono y (x + n - 1) 8 ltac:(lia) ltac:(lia)) as M2.
pose proof (Z.mul_div_le (0x7fff8000 + x / 8) 8 ltac:(lia)) as D1.
pose proof (Z.mod_pos_bound (0x7fff8000 + (x + n - 1) / 8) 8 ltac:(lia)) as D2.
pose proof (Z.div_mod (0x7fff8000 + (x + n - 1) / 8) 8 ltac:(lia)) as D3.
assert (0x7fff8000 + x / 8 <= 0x7fff8000 + y / 8) by lia.
split; [|lia].
pose proof (Z.div_le_mono (0x7fff8000 + x / 8) (0x7fff8000 + y / 8) 8 ltac:(lia) H) as M3.
pose proof (Z.mul_div_le (0x7fff8000 + y / 8) 8 ltac:(lia)). nia.
Qed.
Lemma cb_hull_kept : forall (W : world rsegs) m m' x n,
  shadow_hull_vis (aview rsegs (w_H W) m) x n ->
  (forall a, cb_hull x n a -> aview rsegs (w_H W) m' a = aview rsegs (w_H W) m a) ->
  shadow_hull_vis (aview rsegs (w_H W) m') x n.
Proof. intros W m m' x n HV HK s Hs. rewrite HK by exact Hs. exact (HV s Hs). Qed.
Definition cb_strok (W : world rsegs) (mem : word -> option byte) (R x : Z) (s : list byte) : Prop :=
0 < x /\ Z.of_nat (length s) + 1 < 2 ^ 32 /\ x + Z.of_nat (length s) + 1 <= 2 ^ 63 /\
(forall j, (j < length s)%nat ->
 aview rsegs (w_H W) mem (x + Z.of_nat j) = Some (bv_unsigned (nth j s (Z_to_bv 8 0))) /\
 bv_unsigned (nth j s (Z_to_bv 8 0)) <> 0) /\
aview rsegs (w_H W) mem (x + Z.of_nat (length s)) = Some 0 /\
(forall a, x + Z.of_nat (length s) < a < x + Z.of_nat (length s) - (x + Z.of_nat (length s)) mod 8 + 8 ->
 aview rsegs (w_H W) mem a <> None) /\
(forall a, x <= a <= x + Z.of_nat (length s) -> ~ (R - 2 * ESTACK <= a < R)) /\
amem_range x (Z.of_nat (length s) + 1) /\
range_addressable (aview rsegs (w_H W) mem) SHADOW_OFF x (Z.of_nat (length s) + 1) /\
shadow_hull_vis (aview rsegs (w_H W) mem) x (Z.of_nat (length s) + 1).
Definition cb_strz (x : Z) (s : list byte) (a : Z) : Prop :=
(x <= a <= x + Z.of_nat (length s) + 8) \/ cb_hull x (Z.of_nat (length s) + 1) a.
Lemma cb_strok_kept : forall W m m' R x s,
  cb_strok W m R x s -> (forall a, cb_strz x s a -> aview rsegs (w_H W) m' a = aview rsegs (w_H W) m a) ->
  cb_strok W m' R x s.
Proof.
intros W m m' R x s (H0 & H1 & H2 & Hb & Hn & Ht & Hs & Ha & Hr & Hh) HK.
split; [exact H0|]. split; [exact H1|]. split; [exact H2|].
split; [intros j Hj; rewrite HK by (left; lia); exact (Hb j Hj)|].
split; [rewrite HK by (left; lia); exact Hn|].
split; [intros a Hx; rewrite HK; [exact (Ht a Hx)|];
  left; pose proof (Z.mod_pos_bound (x + Z.of_nat (length s)) 8); lia|].
split; [exact Hs|]. split; [exact Ha|].
split; [apply (cb_ra_kept W m m'); [exact Hr | lia | intros a Hx; apply HK; right; exact Hx]|].
apply (cb_hull_kept W m m'); [exact Hh | intros a Hx; apply HK; right; exact Hx].
Qed.
Lemma cb_strok_first_byte : forall W m R x s, cb_strok W m R x s ->
  first_byte rsegs W m x (Z.of_nat (length s) + 1) 0 (Z.of_nat (length s)).
Proof.
intros W m R x s (_ & _ & _ & Hb & Hn & _).
split; [lia|]. split.
- intros i Hi. destruct (Hb (Z.to_nat i) ltac:(lia)) as [Ha Hz].
  rewrite Z2Nat.id in Ha by lia. eexists. split; [exact Ha | exact Hz].
- intros _. exact Hn.
Qed.

Section d.
Variable B : asyms.
Variable MT : ameter_ops.
Hypothesis MTL : ameter_laws MT.
Let LAWS : AR_laws rsegs B := YG0q.AR_laws_ok rsegs B.

Definition cb_post (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (S : astate) (W0 : world rsegs)
(mem0 : word -> option byte) (md0 : Model) (own : list (Z * Z)) (lyc : alayout) (Sc : astate) (W : world rsegs)
(k : Z) (pc : Z) (regs : bvmap 5 word) (memc : word -> option byte) (mdc : Model) (clob : list (bv 5))
(Wr : Z -> Prop) (R : bvmap 5 word -> (word -> option byte) -> Prop) : world rsegs -> config -> Prop :=
fun W2 c2 => W2 = W /\ exists regs2 mem2 md2,
c2 = mkCfg (mkst regs2 (Z_to_bv 64 pc) mem2 (seg_rom rsegs)) md2 /\
ajournal rsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W mem2 md2 k /\ same_io mdc md2 /\
(forall r : bv 5, bv_unsigned r <> 0 -> ~ In r clob -> getr regs2 r = getr regs r) /\
(forall a, 0 <= a < 2 ^ 64 -> ~ Wr a -> aview rsegs (w_H W) mem2 a = aview rsegs (w_H W) memc a) /\
(forall a, apresent (w_H W) memc a -> apresent (w_H W) mem2 a) /\
R regs2 mem2.
Lemma cb_post_of_run : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W k pc regs memc mdc clob Wr R E ss ms md,
  st_ok rsegs E ss (restrict (w_H W) ms) -> ss_resv ss = None -> ss_pc ss = pc ->
  ajournal rsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W (ms_mem ms) md k -> same_io mdc md ->
  (forall r : bv 5, bv_unsigned r <> 0 -> ~ In r clob -> getr (ms_regs ms) r = getr regs r) ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ Wr a -> aview rsegs (w_H W) (ms_mem ms) a = aview rsegs (w_H W) memc a) ->
  mem_grows (mrestrict (w_H W) memc) (mrestrict (w_H W) (ms_mem ms)) ->
  R (ms_regs ms) (ms_mem ms) ->
  SRr rsegs W (mkCfg ms md) (cb_post STK sp0 FP ly S W0 mem0 md0 own lyc Sc W k pc regs memc mdc clob Wr R).
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W k pc regs memc mdc clob Wr R E ss ms md HS Hrv Hpc HJ Hio Hregs Hkept Hgr HR.
apply SRr_ret. split; [reflexivity|]. exists (ms_regs ms), (ms_mem ms), md.
split; [rewrite (st_ok_restrict_mkst rsegs (w_H W) E ss ms HS Hrv) at 1; rewrite Hpc; reflexivity|].
split; [exact HJ|]. split; [exact Hio|]. split; [exact Hregs|]. split; [exact Hkept|].
split; [intros a Ha; exact (apresent_grows (w_H W) memc (ms_mem ms) a Hgr Ha) | exact HR].
Qed.

(* ===================== the context every block runs in =====================
   The harness's journal from the segment's start (hsu_pre's first conjunct), the real frame [R, R + 0x220)
   inside the journal's stack window with the callees' stack below it, the frame for locals F = the side-stack
   frame (4, pos) the harness holds, and the read-only segments as in the image (hsu_pre's rom_view). *)
Definition cb_ctx (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (S : astate) (W0 : world rsegs)
(mem0 : word -> option byte) (md0 : Model) (own : list (Z * Z)) (k : Z)
(lyc : alayout) (Sc : astate) (W : world rsegs) (memc : word -> option byte) (mdc : Model) (R F pos : Z) : Prop :=
ajournal rsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k /\
R mod 32 = 0 /\ R + 0x220 <= sp0 /\ sp0 - STK <= R - T_SEG_STK /\
In (4, pos) own /\ F = frame_addr lyc 4 pos /\
rom_view rsegs W memc.

(* ===================== chaining the blocks =====================
   A block's post is the shared layer's hdu_blk_postE. A pure-read block (hdu_blk_post) is an hdu_blk_postE with
   any write set; two hdu_blk_postE blocks chain into one, with the union of the clobbered registers and of the
   write sets, and the second block's R. *)
Lemma cb_post_of_blk : forall STK sp0 FP ly S W0 mem0 md0 own k regs lyc Sc W memc mdc pc clob
(Rr : bvmap 5 word -> Prop) (Wr : Z -> Prop) W2 c2,
hdu_blk_post B MT STK sp0 FP ly S W0 mem0 md0 own k regs lyc Sc W memc mdc pc clob Rr W2 c2 ->
hdu_blk_postE B MT STK sp0 FP ly S W0 mem0 md0 own k regs lyc Sc W memc mdc pc clob Wr (fun _ regs2 _ => Rr regs2) W2 c2.
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own k regs lyc Sc W memc mdc pc clob Rr Wr W2 c2
(ly2 & S2 & regs2 & mem2 & md2 & Ec & HJ & Hr & Hf & Hp & Hio & Hmo & Hm & HR).
exists ly2, S2, regs2, mem2, md2. repeat (split; [eassumption|]).
split; [intros a _ _; apply Hm|]. exact HR.
Qed.

Lemma cb_post_seq : forall STK sp0 FP ly S W0 mem0 md0 own k regs lyc Sc W memc mdc pc0 pc1 pc2 clob1 clob2
(Wr1 Wr2 : Z -> Prop) (R1 R2 : world rsegs -> bvmap 5 word -> (word -> option byte) -> Prop),
SRr rsegs W (cfg_at rsegs pc0 regs memc mdc)
(hdu_blk_postE B MT STK sp0 FP ly S W0 mem0 md0 own k regs lyc Sc W memc mdc pc1 clob1 Wr1 R1) ->
(forall W1 ly1 S1 regs1 mem1 md1, wle W W1 ->
 ajournal rsegs B STK sp0 FP ly S W0 mem0 md0 own ly1 S1 W1 mem1 md1 k ->
 (forall r : bv 5, bv_unsigned r <> 0 -> ~ In r clob1 -> getr regs1 r = getr regs r) ->
 frames S1 = frames Sc -> Permutation (ablocks B ly1 S1) (ablocks B lyc Sc) -> same_io mdc md1 -> mo_le MT Sc S1 0 ->
 (forall a, 0 <= a < 2 ^ 64 -> ~ Wr1 a -> aview rsegs (w_H W1) mem1 a = aview rsegs (w_H W) memc a) ->
 R1 W1 regs1 mem1 ->
 SRr rsegs W1 (cfg_at rsegs pc1 regs1 mem1 md1)
 (hdu_blk_postE B MT STK sp0 FP ly S W0 mem0 md0 own k regs1 ly1 S1 W1 mem1 md1 pc2 clob2 Wr2 R2)) ->
SRr rsegs W (cfg_at rsegs pc0 regs memc mdc)
(hdu_blk_postE B MT STK sp0 FP ly S W0 mem0 md0 own k regs lyc Sc W memc mdc pc2 (clob1 ++ clob2)
 (fun a => Wr1 a \/ Wr2 a) R2).
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own k regs lyc Sc W memc mdc pc0 pc1 pc2 clob1 clob2 Wr1 Wr2 R1 R2 H1 H2.
eapply SRr_bind; [exact H1|].
intros W1 c1 Hw1 (ly1 & S1 & regs1 & mem1 & md1 & -> & HJ1 & Hr1 & Hf1 & Hp1 & Hio1 & Hmo1 & Hm1 & HR1).
eapply SRr_mono; [exact (H2 W1 ly1 S1 regs1 mem1 md1 Hw1 HJ1 Hr1 Hf1 Hp1 Hio1 Hmo1 Hm1 HR1)|].
intros W2 c2 _ (ly2 & S2 & regs2 & mem2 & md2 & -> & HJ2 & Hr2 & Hf2 & Hp2 & Hio2 & Hmo2 & Hm2 & HR2).
exists ly2, S2, regs2, mem2, md2. split; [reflexivity|]. split; [exact HJ2|].
split; [intros r Hr0 Hn; rewrite (Hr2 r Hr0 ltac:(intros X; apply Hn; apply in_or_app; right; exact X));
  apply Hr1; [exact Hr0 | intros X; apply Hn; apply in_or_app; left; exact X]|].
split; [rewrite Hf2; exact Hf1|].
split; [eapply Permutation_trans; [exact Hp2 | exact Hp1]|].
split; [eapply same_io_trans; [exact Hio1 | exact Hio2]|].
split; [exact (mle_station MT Sc S1 S2 0 0 MTL Hmo1 Hmo2)|].
split; [intros a Ha Hn; rewrite (Hm2 a Ha ltac:(intros X; apply Hn; right; exact X));
  exact (Hm1 a Ha ltac:(intros X; apply Hn; left; exact X))|].
exact HR2.
Qed.

Lemma cb_blk_seq : forall STK sp0 FP ly S W0 mem0 md0 own k regs lyc Sc W memc mdc pc0 pc1 pc2 clob1 clob2
(R1 R2 : bvmap 5 word -> Prop),
SRr rsegs W (cfg_at rsegs pc0 regs memc mdc)
(hdu_blk_post B MT STK sp0 FP ly S W0 mem0 md0 own k regs lyc Sc W memc mdc pc1 clob1 R1) ->
(forall W1 ly1 S1 regs1 mem1 md1, wle W W1 ->
 ajournal rsegs B STK sp0 FP ly S W0 mem0 md0 own ly1 S1 W1 mem1 md1 k ->
 (forall r : bv 5, bv_unsigned r <> 0 -> ~ In r clob1 -> getr regs1 r = getr regs r) ->
 frames S1 = frames Sc -> Permutation (ablocks B ly1 S1) (ablocks B lyc Sc) -> same_io mdc md1 -> mo_le MT Sc S1 0 ->
 (forall a, aview rsegs (w_H W1) mem1 a = aview rsegs (w_H W) memc a) ->
 R1 regs1 ->
 SRr rsegs W1 (cfg_at rsegs pc1 regs1 mem1 md1)
 (hdu_blk_post B MT STK sp0 FP ly S W0 mem0 md0 own k regs1 ly1 S1 W1 mem1 md1 pc2 clob2 R2)) ->
SRr rsegs W (cfg_at rsegs pc0 regs memc mdc)
(hdu_blk_post B MT STK sp0 FP ly S W0 mem0 md0 own k regs lyc Sc W memc mdc pc2 (clob1 ++ clob2) R2).
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own k regs lyc Sc W memc mdc pc0 pc1 pc2 clob1 clob2 R1 R2 H1 H2.
eapply SRr_bind; [exact H1|].
intros W1 c1 Hw1 (ly1 & S1 & regs1 & mem1 & md1 & -> & HJ1 & Hr1 & Hf1 & Hp1 & Hio1 & Hmo1 & Hm1 & HR1).
eapply SRr_mono; [exact (H2 W1 ly1 S1 regs1 mem1 md1 Hw1 HJ1 Hr1 Hf1 Hp1 Hio1 Hmo1 Hm1 HR1)|].
intros W2 c2 _ (ly2 & S2 & regs2 & mem2 & md2 & -> & HJ2 & Hr2 & Hf2 & Hp2 & Hio2 & Hmo2 & Hm2 & HR2).
exists ly2, S2, regs2, mem2, md2. split; [reflexivity|]. split; [exact HJ2|].
split; [intros r Hr0 Hn; rewrite (Hr2 r Hr0 ltac:(intros X; apply Hn; apply in_or_app; right; exact X));
  apply Hr1; [exact Hr0 | intros X; apply Hn; apply in_or_app; left; exact X]|].
split; [rewrite Hf2; exact Hf1|].
split; [eapply Permutation_trans; [exact Hp2 | exact Hp1]|].
split; [eapply same_io_trans; [exact Hio1 | exact Hio2]|].
split; [exact (mle_station MT Sc S1 S2 0 0 MTL Hmo1 Hmo2)|].
split; [intros a; rewrite (Hm2 a); exact (Hm1 a)|].
exact HR2.
Qed.

(* ===================================== a segment's start facts at a cut ===================================== *)
(* the address facts of the segment's start: R above the shadow band, F and pp in the application's memory *)
Lemma cb_pre_geom : forall cx sh, hsu_pre rsegs B headamp_himg_B cx sh ->
spZ (x_regs rsegs cx) = e_R (x_e rsegs cx) /\
kHighMemBeg <= e_R (x_e rsegs cx) - T_SEG_STK /\ e_R (x_e rsegs cx) + 0x220 <= 2 ^ 47 /\
In (4, x_pos rsegs cx) (frames (x_Sc rsegs cx)) /\
e_F (x_e rsegs cx) = frame_addr (x_lyc rsegs cx) 4 (x_pos rsegs cx) /\
in_app (e_F (x_e rsegs cx)) 1024 /\ e_F (x_e rsegs cx) mod 32 = 0 /\
in_app (e_pp (x_e rsegs cx)) Layout.PP_SIZE.
Proof.
intros [STK sp0 FP ly S W0 mem0 md0 own k regs lyc Sc W memc mdc RLO RHI e pos] sh HP.
unfold hsu_pre in HP.
cbn [x_STK x_sp0 x_FP x_ly x_S x_W0 x_mem0 x_md0 x_own x_k x_regs x_lyc x_Sc x_W x_memc x_mdc x_RLO x_RHI x_e x_pos] in *.
destruct HP as (HJ & _ & Hsp & _ & _ & HeS & HR32 & HRS & HSTK & Hown & HF & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hfb).
destruct Hfb as (_ & Hpp & _).
cbn [hi_cid hi_rsz headamp_himg_B] in HRS, Hown, HF.
pose proof HJ as (HAR & _ & _ & _ & _ & Hfrs & _ & _ & _ & _ & _ & _ & _ & _ & Hstk & _).
destruct Hstk as (Hal & HSTK0 & Hceil & Hlo & Hhi & H47 & _).
pose proof alloc_ceiling_value as (Hc1 & _).
assert (Hin4 : In (4, pos) (frames Sc)) by (rewrite Hfrs; apply in_or_app; left; exact Hown).
destruct (al_frames _ _ LAWS lyc Sc W memc mdc 4 pos HAR Hin4) as (HF32 & HFapp & _).
destruct (al_blocks _ _ LAWS lyc Sc W memc mdc (e_pp e) Layout.PP_SIZE HAR Hpp) as (_ & _ & _ & Happ & _).
change (fs_frame_bytes 4) with 1024 in HFapp. rewrite <- HF in HFapp, HF32.
replace (req_size Layout.PP_SIZE) with Layout.PP_SIZE in Happ by reflexivity.
assert (HR0 : 0 <= e_R e < 2 ^ 64) by (unfold T_SEG_STK, ASTACK in HSTK; zl).
split; [unfold spZ; rewrite Hsp; unfold w64; apply unsigned_lit_small; exact HR0|].
split; [unfold T_SEG_STK, ASTACK in *; unfold kHighMemBeg; zl|].
split; [zl|].
split; [exact Hin4|]. split; [exact HF|]. split; [exact HFapp|]. split; [exact HF32 | exact Happ].
Qed.

Lemma cb_core_kept : forall cx sh ly2 S2 W2 regs2 mem2 md2,
hsu_pre rsegs B headamp_himg_B cx sh ->
hsu_core rsegs B MT cx (hsu_E1 rsegs headamp_himg_B cx) ly2 S2 W2 regs2 mem2 md2 ->
forall a, ~ cb_wr cx a -> aview rsegs (w_H W2) mem2 a = aview rsegs (w_H (x_W rsegs cx)) (x_memc rsegs cx) a.
Proof.
intros cx sh ly2 S2 W2 regs2 mem2 md2 HP HC a Ha.
destruct (cb_pre_geom cx sh HP) as (Hsp & _).
destruct HC as (_ & _ & _ & _ & _ & _ & HK). unfold cb_wr in Ha.
apply HK; [lia | rewrite Hsp; intros X; apply Ha; right; left; exact X | intros X; apply Ha; right; right; exact X].
Qed.

(* a shadow byte of an application address is never in hsu_E1 or the callees' stack *)
Lemma cb_wr_shadow : forall cx x, hsu_pre rsegs B headamp_himg_B cx (hi_shA headamp_himg_B) -> 0 <= x < kHighMemEnd ->
range_addressable (aview rsegs (w_H (x_W rsegs cx)) (x_memc rsegs cx)) SHADOW_OFF x 1 ->
~ cb_wr cx (shadow_of_addr SHADOW_OFF x).
Proof.
intros cx x HP Hx Hra.
destruct (cb_pre_geom cx _ HP) as (_ & HRk & _ & _ & _ & HFapp & _ & Happ).
pose proof (hm_shadow_band x Hx) as Hb.
assert (Hfsh : hd_fsh rsegs (w_H (x_W rsegs cx)) (x_memc rsegs cx) (e_F (x_e rsegs cx)) headamp_B_shA).
{ destruct HP as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & H & _). exact H. }
pose proof (hm_ra_not_fsh rsegs _ _ _ _ x 1 Hra Hfsh hmu_sh_P0_big x ltac:(lia)) as Hnf.
change (Z.of_nat (length headamp_B_shA)) with 116 in Hnf.
unfold cb_wr, hsu_E1, hd_inw. cbn [hi_w1 headamp_himg_B].
intros [H|[H|[H|H]]].
- unfold kLowMemEnd, kHighMemBeg in Hb. lia.
- unfold kHighMemBeg in *. lia.
- apply Exists_cons in H as [H|H]; [|apply Exists_cons in H as [H|H]; [|apply Exists_cons in H as [H|H]; [|apply Exists_nil in H; destruct H]]];
  cbn [fst snd hd_xv] in H.
  + apply (hm_shadow_not_app x (e_F (x_e rsegs cx)) 1024 Hx HFapp). lia.
  + apply Hnf. lia.
  + unfold kHighMemBeg, T_SEG_STK, ASTACK in *. lia.
- apply (hm_shadow_not_app x (e_pp (x_e rsegs cx)) Layout.PP_SIZE Hx Happ). exact H.
Qed.

(* the input bytes, their shadow bytes and their shadow hull at a cut *)
Lemma cb_in_now : forall cx rest pat ly2 S2 W2 regs2 mem2 md2,
hsu_pre rsegs B headamp_himg_B cx (hi_shA headamp_himg_B) -> hsu_in rsegs headamp_himg_B cx rest ->
hsu_core rsegs B MT cx (hsu_E1 rsegs headamp_himg_B cx) ly2 S2 W2 regs2 mem2 md2 ->
hsu_fsh_at rsegs cx W2 mem2 pat -> length pat = 116%nat ->
garr8 rsegs (mrestrict (w_H W2) mem2) (e_src (x_e rsegs cx)) (hd_zbytes rest) /\
range_addressable (aview rsegs (w_H W2) mem2) SHADOW_OFF (e_src (x_e rsegs cx)) (e_left (x_e rsegs cx)) /\
(0 < e_left (x_e rsegs cx) -> shadow_hull_vis (aview rsegs (w_H W2) mem2) (e_src (x_e rsegs cx)) (e_left (x_e rsegs cx))).
Proof.
intros cx rest pat ly2 S2 W2 regs2 mem2 md2 HP HI HC Hfsh2 Hpat.
pose proof (cb_core_kept cx _ ly2 S2 W2 regs2 mem2 md2 HP HC) as HK.
destruct (cb_pre_geom cx _ HP) as (_ & HRk & _ & _ & _ & HFapp & _ & Happ).
destruct HI as (Hleft & Hbytes & Hra & Hhull & Hamr & Hsrc0 & Hsrc63 & Hdisj).
set (src := e_src (x_e rsegs cx)) in *. set (n := e_left (x_e rsegs cx)) in *.
assert (Hx : forall x, src <= x < src + n -> 0 <= x < kHighMemEnd).
{ intros x Hx. unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in *. lia. }
split.
- apply (hm_bytes_kept_wr rsegs (cb_wr cx) _ _ _ _ src rest Hbytes HK).
  intros x Hx'. rewrite <- Hleft in Hx'. fold n in Hx'. destruct (Hdisj x Hx') as (D1 & D2 & D3).
  unfold cb_wr, hsu_E1. intros [H|[H|[H|H]]]; [lia | exact (D1 H) | exact (D2 H) | exact (D3 H)].
- split.
  + apply (hm_ra_kept_wr rsegs (cb_wr cx) _ _ _ _ SHADOW_OFF src n Hra HK).
    intros x Hx'. apply cb_wr_shadow; [exact HP | exact (Hx x Hx') |].
    apply (range_addressable_sub _ _ src n); [exact Hra | lia | lia].
  + intros Hn. apply (hm_hull_kept rsegs _ _ _ _ src n (Hhull Hn)).
    intros s Hs Hnone.
    destruct (base.decide (cb_wr cx s)) as [Hw|Hw].
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
    unfold cb_wr, hsu_E1, hd_inw in Hw. cbn [hi_w1 headamp_himg_B] in Hw.
    destruct Hw as [H|[H|[H|H]]].
    * exfalso. unfold SHADOW_OFF, kHighMemBeg in Hsb. lia.
    * exfalso. unfold kHighMemBeg, T_SEG_STK, ASTACK in *. lia.
    * apply Exists_cons in H as [H|H]; [|apply Exists_cons in H as [H|H]; [|apply Exists_cons in H as [H|H]; [|apply Exists_nil in H; destruct H]]];
      cbn [fst snd hd_xv] in H.
      -- exfalso. unfold in_app, kLowShadowBeg, kHighMemBeg, SHADOW_OFF in *. lia.
      -- unfold hsu_fsh_at, hd_fsh in Hfsh2. rewrite Hpat in Hfsh2.
         replace s with (shadow_addr (e_F (x_e rsegs cx)) + (s - shadow_addr (e_F (x_e rsegs cx)))) by lia.
         rewrite (Hfsh2 (s - shadow_addr (e_F (x_e rsegs cx))) ltac:(cbn; lia)). discriminate.
      -- exfalso. unfold kHighMemBeg, T_SEG_STK, ASTACK in *. lia.
    * exfalso. unfold in_app, kLowShadowBeg, kHighMemBeg, SHADOW_OFF in *. lia.
Qed.

(* rom_view at a cut: the image lies below the shadow band, outside every block and frame *)
Lemma cb_rom_now : forall cx sh ly2 S2 W2 regs2 mem2 md2,
hsu_pre rsegs B headamp_himg_B cx sh ->
hsu_core rsegs B MT cx (hsu_E1 rsegs headamp_himg_B cx) ly2 S2 W2 regs2 mem2 md2 -> rom_view rsegs W2 mem2.
Proof.
intros cx sh ly2 S2 W2 regs2 mem2 md2 HP HC.
pose proof (cb_core_kept cx sh ly2 S2 W2 regs2 mem2 md2 HP HC) as HK.
destruct (cb_pre_geom cx sh HP) as (_ & HRk & _ & Hin4 & HF & HFapp & _ & Happ).
assert (Hrom : rom_view rsegs (x_W rsegs cx) (x_memc rsegs cx)).
{ destruct HP as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & H & _). exact H. }
assert (HAR : AR rsegs B (x_lyc rsegs cx) (x_Sc rsegs cx) (x_W rsegs cx) (x_memc rsegs cx) (x_mdc rsegs cx)).
{ destruct HP as (HJ & _). exact (proj1 HJ). }
assert (Hpp : In (e_pp (x_e rsegs cx), Layout.PP_SIZE) (ablocks B (x_lyc rsegs cx) (x_Sc rsegs cx))).
{ destruct HP as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & H).
  exact (proj1 (proj2 H)). }
apply (hm_rom_kept_wr rsegs (cb_wr cx) (x_W rsegs cx) W2 (x_memc rsegs cx) mem2 Hrom HK).
intros a (sg & Hsg & _ & Ha). assert (Himg : in_img rsegs a) by (exists sg; split; [exact Hsg | exact Ha]).
pose proof (img_segs_low a Himg) as Hlow.
pose proof (al_client_img _ _ LAWS _ _ _ _ _ a HAR) as Hcl.
unfold cb_wr, hsu_E1, hd_inw. cbn [hi_w1 headamp_himg_B].
intros [H|[H|[H|H]]].
- unfold kLowMemEnd in Hlow. lia.
- unfold kLowMemEnd, kHighMemBeg, T_SEG_STK, ASTACK in *. lia.
- apply Exists_cons in H as [H|H]; [|apply Exists_cons in H as [H|H]; [|apply Exists_cons in H as [H|H]; [|apply Exists_nil in H; destruct H]]];
  cbn [fst snd hd_xv] in H.
  + assert (HinF : frame_addr (x_lyc rsegs cx) 4 (x_pos rsegs cx) <= a <
      frame_addr (x_lyc rsegs cx) 4 (x_pos rsegs cx) + fs_frame_bytes 4)
      by (rewrite <- HF; change (fs_frame_bytes 4) with 1024; lia).
    apply (proj2 (Hcl (or_intror (or_introl (ex_intro _ 4 (ex_intro _ (x_pos rsegs cx) (conj Hin4 HinF))))))).
    exact Himg.
  + unfold shadow_addr, SHADOW_OFF, kLowMemEnd in *. pose proof (Z.div_pos (e_F (x_e rsegs cx)) 8).
    unfold in_app in HFapp. lia.
  + unfold kLowMemEnd, kHighMemBeg, T_SEG_STK, ASTACK in *. lia.
- assert (Hinp : e_pp (x_e rsegs cx) <= a < e_pp (x_e rsegs cx) + req_size Layout.PP_SIZE)
    by (change (req_size Layout.PP_SIZE) with Layout.PP_SIZE; lia).
  apply (proj2 (Hcl (or_introl (ex_intro _ (e_pp (x_e rsegs cx)) (ex_intro _ Layout.PP_SIZE (conj Hpp Hinp)))))).
  exact Himg.
Qed.

(* ======================================== a cut's geometry and context ======================================== *)
Lemma cb_geo_of : forall cx sh E ly2 S2 W2 regs2 mem2 md2,
hsu_pre rsegs B headamp_himg_B cx sh -> hsu_core rsegs B MT cx E ly2 S2 W2 regs2 mem2 md2 ->
cb_geo (e_R (x_e rsegs cx)) (e_F (x_e rsegs cx)) (e_pp (x_e rsegs cx)) /\
e_F (x_e rsegs cx) = frame_addr ly2 4 (x_pos rsegs cx) /\
spZ (x_regs rsegs cx) = e_R (x_e rsegs cx).
Proof.
intros cx sh E ly2 S2 W2 regs2 mem2 md2 HP HC.
destruct (cb_pre_geom cx sh HP) as (Hsp & HRk & HR47 & _ & HF0 & HFapp & HF32 & Happ).
pose proof HP as HP'.
destruct HP' as (HJ0 & _ & _ & _ & _ & HS & _ & HRs & HRstk & Hown & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hfb).
destruct Hfb as (_ & Hpp & _).
cbn [hi_cid hi_rsz headamp_himg_B] in HRs, Hown.
destruct HC as (HJ & _ & _ & Hperm & _).
destruct HJ as (HAR & Hly & _ & _ & _ & Hfrs & _ & _ & _ & _ & _ & _ & _ & _ & Hstk & _).
destruct HJ0 as (_ & Hly0 & _).
assert (HFa : e_F (x_e rsegs cx) = frame_addr ly2 4 (x_pos rsegs cx)).
{ rewrite HF0. unfold frame_addr. destruct Hly as (_ & _ & _ & _ & _ & E2 & _).
  destruct Hly0 as (_ & _ & _ & _ & _ & E0 & _). rewrite E2, E0. reflexivity. }
assert (Hin : In (4, x_pos rsegs cx) (frames S2)) by (rewrite Hfrs; apply in_or_app; left; exact Hown).
assert (Hpp2 : In (e_pp (x_e rsegs cx), Layout.PP_SIZE) (ablocks B ly2 S2))
  by (eapply Permutation_in; [apply Permutation_sym; exact Hperm | exact Hpp]).
pose proof (sep_block_frame rsegs B LAWS ly2 S2 W2 mem2 md2 _ _ 4 (x_pos rsegs cx) HAR Hpp2 Hin) as Hdj.
rewrite <- HFa in Hdj.
destruct (al_blocks _ _ LAWS ly2 S2 W2 mem2 md2 _ _ HAR Hpp2) as (_ & Hp4 & Hp1 & _).
destruct Hstk as (_ & _ & Hac & Hlo & _).
destruct (cb_bounds _ HF32 HFapp) as (B1 & B2 & B3 & B4 & B5 & _).
replace (req_size Layout.PP_SIZE) with Layout.PP_SIZE in Hp1, Hdj by reflexivity.
unfold zdisjoint in Hdj. cbn [fst snd] in Hdj. change (fs_frame_bytes 4) with 1024 in Hdj.
pose proof ASAN_CEIL_range as (HC1 & _). unfold ASAN_CEIL in HC1.
pose proof (Z.div_mod (e_F (x_e rsegs cx)) 8 ltac:(lia)) as D1.
pose proof (Z.mod_pos_bound (e_F (x_e rsegs cx)) 8 ltac:(lia)) as D2.
split; [|split; [exact HFa | exact Hsp]].
unfold cb_geo.
split; [unfold T_SEG_STK, ASTACK in *; zl|].
split; [exact HR47|]. split; [exact HRk|]. split; [exact HFapp|].
split; [exact B1|]. split; [exact B2|]. split; [exact B3|]. split; [exact B4|]. split; [exact B5|].
split; [exact Hp4|]. split; [exact Hp1|].
split; [|split; [exact Hdj | split; [exact HF32 | exact Happ]]].
clear Hdj B5.
unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Happ. unfold shadow_addr, SHADOW_OFF in *. unfold Layout.PP_SIZE in *.
lia.
Qed.

Lemma cb_ctx_of : forall cx sh ly2 S2 W2 regs2 mem2 md2,
hsu_pre rsegs B headamp_himg_B cx sh ->
hsu_core rsegs B MT cx (hsu_E1 rsegs headamp_himg_B cx) ly2 S2 W2 regs2 mem2 md2 ->
cb_ctx (x_STK rsegs cx) (x_sp0 rsegs cx) (x_FP rsegs cx) (x_ly rsegs cx) (x_S rsegs cx) (x_W0 rsegs cx)
  (x_mem0 rsegs cx) (x_md0 rsegs cx) (x_own rsegs cx) (x_k rsegs cx) ly2 S2 W2 mem2 md2
  (e_R (x_e rsegs cx)) (e_F (x_e rsegs cx)) (x_pos rsegs cx).
Proof.
intros cx sh ly2 S2 W2 regs2 mem2 md2 HP HC.
destruct (cb_geo_of cx sh _ ly2 S2 W2 regs2 mem2 md2 HP HC) as (_ & HFa & _).
pose proof (cb_rom_now cx sh ly2 S2 W2 regs2 mem2 md2 HP HC) as Hrom.
pose proof HP as HP'. destruct HP' as (_ & _ & _ & _ & _ & HS & HR32 & HRs & HRstk & Hown & _).
cbn [hi_cid hi_rsz headamp_himg_B] in HRs, Hown.
destruct HC as (HJ & _).
unfold cb_ctx. split; [exact HJ|]. split; [exact HR32|]. split; [rewrite <- HS; exact HRs|].
split; [exact HRstk|]. split; [exact Hown|]. split; [exact HFa | exact Hrom].
Qed.

(* the journal-and-frame part of a cut, carried across a block *)
Lemma cb_core_step : forall cx E ly2 S2 W2 regs2 mem2 md2 ly3 S3 W3 regs3 mem3 md3 (Wr : Z -> Prop),
hsu_core rsegs B MT cx E ly2 S2 W2 regs2 mem2 md2 ->
ajournal rsegs B (x_STK rsegs cx) (x_sp0 rsegs cx) (x_FP rsegs cx) (x_ly rsegs cx) (x_S rsegs cx) (x_W0 rsegs cx)
  (x_mem0 rsegs cx) (x_md0 rsegs cx) (x_own rsegs cx) ly3 S3 W3 mem3 md3 (x_k rsegs cx) ->
(forall r : Z, r = 2 \/ r = 3 \/ r = 4 -> getr regs3 (Z_to_bv 5 r) = getr regs2 (Z_to_bv 5 r)) ->
frames S3 = frames S2 -> Permutation (ablocks B ly3 S3) (ablocks B ly2 S2) -> same_io md2 md3 -> mo_le MT S2 S3 0 ->
(forall a, 0 <= a < 2 ^ 64 -> ~ Wr a -> aview rsegs (w_H W3) mem3 a = aview rsegs (w_H W2) mem2 a) ->
(forall a, Wr a -> (spZ (x_regs rsegs cx) - T_SEG_STK <= a < spZ (x_regs rsegs cx)) \/ E a) ->
hsu_core rsegs B MT cx E ly3 S3 W3 regs3 mem3 md3.
Proof.
intros cx E ly2 S2 W2 regs2 mem2 md2 ly3 S3 W3 regs3 mem3 md3 Wr HC HJ Hr Hf Hp Hio Hmo Hm Hsub.
unfold hsu_core, hsu_mid in *.
destruct HC as (_ & Hr2 & Hf2 & Hp2 & Hio2 & Hmo2 & Hm2).
split; [exact HJ|].
split; [intros r Hr0; rewrite (Hr r Hr0); exact (Hr2 r Hr0)|].
split; [rewrite Hf; exact Hf2|].
split; [eapply Permutation_trans; [exact Hp | exact Hp2]|].
split; [eapply same_io_trans; [exact Hio2 | exact Hio]|].
split; [exact (mle_station MT (x_Sc rsegs cx) S2 S3 0 0 MTL Hmo2 Hmo)|].
intros a Ha Hs HE. rewrite <- (Hm2 a Ha Hs HE). apply Hm; [exact Ha|].
intros HW. destruct (Hsub a HW) as [X|X]; [exact (Hs X) | exact (HE X)].
Qed.

Lemma cb_pod_base_mv : forall cx sh np ps cnt es rest rr r r' ly2 S2 W2 regs2 mem2 md2 ly3 S3 W3 regs3 mem3 md3,
hsu_pod_base rsegs B MT headamp_himg_B cx sh np ps cnt es rest rr r ly2 S2 W2 regs2 mem2 md2 ->
hsu_core rsegs B MT cx (hsu_E1 rsegs headamp_himg_B cx) ly3 S3 W3 regs3 mem3 md3 -> hsu_suffix rest r' ->
hsu_pod_base rsegs B MT headamp_himg_B cx sh np ps cnt es rest rr r' ly3 S3 W3 regs3 mem3 md3.
Proof.
intros cx sh np ps cnt es rest rr r r' ly2 S2 W2 regs2 mem2 md2 ly3 S3 W3 regs3 mem3 md3 (_ & H1 & _ & H3) HC HS.
split; [exact HC|]. split; [exact H1|]. split; [exact HS | exact H3].
Qed.

(* ======================================== the input at a cursor after a block ========================================
   The start's input bytes from rest's suffix r on, at the cursor that names r, after a block whose write set
   Wr lies in the callees' stack and the image's first write range. *)
Lemma cb_in_kept : forall cx rest r (Wr : Z -> Prop) (W2 : world rsegs) mem2 (W1 : world rsegs) mem1,
hsu_pre rsegs B headamp_himg_B cx (hi_shA headamp_himg_B) -> hsu_in rsegs headamp_himg_B cx rest ->
hsu_suffix rest r ->
cb_geo (e_R (x_e rsegs cx)) (e_F (x_e rsegs cx)) (e_pp (x_e rsegs cx)) ->
garr8 rsegs (mrestrict (w_H W2) mem2) (e_src (x_e rsegs cx)) (hd_zbytes rest) ->
range_addressable (aview rsegs (w_H W2) mem2) SHADOW_OFF (e_src (x_e rsegs cx)) (e_left (x_e rsegs cx)) ->
(forall a, Wr a -> (e_R (x_e rsegs cx) - T_SEG_STK <= a < e_R (x_e rsegs cx)) \/
 hd_inw (x_e rsegs cx) (hi_w1 headamp_himg_B) a) ->
(forall a, 0 <= a < 2 ^ 64 -> ~ Wr a -> aview rsegs (w_H W1) mem1 a = aview rsegs (w_H W2) mem2 a) ->
cb_in W1 mem1 (e_R (x_e rsegs cx)) (hsu_cur rsegs cx rest r) r.
Proof.
intros cx rest r Wr W2 mem2 W1 mem1 HP HI (j & Hj & ->) HG Hg Hra HWE Hm.
destruct HI as (Hleft & Hg0 & Hra0 & _ & Ham & Hsrc & Htop & Hx).
assert (Hfsh0 : hd_fsh rsegs (w_H (x_W rsegs cx)) (x_memc rsegs cx) (e_F (x_e rsegs cx)) headamp_B_shA).
{ destruct HP as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & H & _). exact H. }
assert (Hcur : hsu_cur rsegs cx rest (skipn j rest) = e_src (x_e rsegs cx) + Z.of_nat j)
  by (unfold hsu_cur; rewrite length_skipn; lia).
unfold cb_in. rewrite Hcur. rewrite length_skipn.
assert (Hn : forall x, e_src (x_e rsegs cx) <= x < e_src (x_e rsegs cx) + Z.of_nat (length rest) ->
  0 <= x < kHighMemEnd /\ ~ Wr x /\
  ~ (e_R (x_e rsegs cx) <= x < e_R (x_e rsegs cx) + 0x198) /\
  ~ (e_R (x_e rsegs cx) - T_SEG_STK <= x < e_R (x_e rsegs cx))).
{ intros x Hx'. rewrite <- Hleft in Hx'. destruct (Hx x Hx') as (D1 & D2 & _).
  split; [unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in *; lia|].
  split; [intros HW; destruct (HWE x HW) as [X|X]; [exact (D1 X) | exact (D2 X)]|].
  split; [intros X; apply D2; apply cb_inw1; right; right; exact X | exact D1]. }
split; [|split; [|split; [lia|split; [lia|split]]]].
- assert (Hg1 : hm_bytes rsegs (w_H W2) mem2 (e_src (x_e rsegs cx) + Z.of_nat j) (skipn j rest)).
  { pose proof (proj1 (hm_bytes_app rsegs (w_H W2) mem2 (e_src (x_e rsegs cx)) (firstn j rest) (skipn j rest))) as Happ.
    rewrite firstn_skipn in Happ. destruct (Happ Hg) as [_ H2].
    rewrite length_firstn, Nat.min_l in H2 by lia. exact H2. }
  apply (hm_bytes_kept rsegs (w_H W2) mem2 (w_H W1) mem1 _ _ Hg1).
  intros x Hx'. rewrite length_skipn in Hx'. destruct (Hn x ltac:(lia)) as (Hb & Hw & _).
  apply Hm; [unfold kHighMemEnd in Hb; lia | exact Hw].
- intros x Hx'. destruct (Hn x ltac:(lia)) as (Hb & _).
  pose proof (hm_ra_not_fsh rsegs _ _ _ _ (e_src (x_e rsegs cx)) (e_left (x_e rsegs cx)) Hra0 Hfsh0 hmu_sh_P0_big x
    ltac:(lia)) as Hnf.
  change (Z.of_nat (length headamp_B_shA)) with 116 in Hnf.
  destruct (cb_shin _ _ _ x HG Hb Hnf) as (Hb2 & Hf2 & HR2 & Hp2 & _).
  assert (Hw2 : ~ Wr (shadow_of_addr SHADOW_OFF x)).
  { intros HW. destruct (HWE _ HW) as [X|X]; [apply HR2; lia|].
    unfold hd_inw in X. cbn [hi_w1 headamp_himg_B] in X.
    apply Exists_cons in X as [X|X]; [|apply Exists_cons in X as [X|X]; [|apply Exists_cons in X as [X|X]; [|apply Exists_nil in X; destruct X]]];
    cbn [fst snd hd_xv] in X; [apply Hf2; lia | apply Hnf; lia | apply HR2; unfold T_SEG_STK, ASTACK; lia]. }
  rewrite (Hm _ Hb2 Hw2). apply Hra. lia.
- unfold amem_range in *. lia.
- intros a Ha. destruct (Hn a ltac:(lia)) as (_ & _ & D3 & D4). lia.
Qed.

(* ======================================== a block between two cuts ======================================== *)
(* a block that writes Wr, inside the callees' stack and hsu_E1: the cut's journal-and-frame part and a carried
   location list *)
Lemma cb_blkE_step : forall cx clob (Wr : Z -> Prop) L lyA SA WA regsA memA mdA lyB SB WB regsB memB mdB,
hsu_core rsegs B MT cx (hsu_E1 rsegs headamp_himg_B cx) lyA SA WA regsA memA mdA ->
ajournal rsegs B (x_STK rsegs cx) (x_sp0 rsegs cx) (x_FP rsegs cx) (x_ly rsegs cx) (x_S rsegs cx) (x_W0 rsegs cx)
  (x_mem0 rsegs cx) (x_md0 rsegs cx) (x_own rsegs cx) lyB SB WB memB mdB (x_k rsegs cx) ->
(forall r : bv 5, bv_unsigned r <> 0 -> ~ In r clob -> getr regsB r = getr regsA r) ->
frames SB = frames SA -> Permutation (ablocks B lyB SB) (ablocks B lyA SA) -> same_io mdA mdB -> mo_le MT SA SB 0 ->
(forall a, 0 <= a < 2 ^ 64 -> ~ Wr a -> aview rsegs (w_H WB) memB a = aview rsegs (w_H WA) memA a) ->
(forall a, Wr a -> (spZ (x_regs rsegs cx) - T_SEG_STK <= a < spZ (x_regs rsegs cx)) \/
 hsu_E1 rsegs headamp_himg_B cx a) ->
cb_regok clob 2 = true -> cb_regok clob 3 = true -> cb_regok clob 4 = true ->
Forall (cb_side clob Wr (x_e rsegs cx)) L ->
hsu_at rsegs (w_H WA) memA regsA (x_e rsegs cx) L ->
hsu_core rsegs B MT cx (hsu_E1 rsegs headamp_himg_B cx) lyB SB WB regsB memB mdB /\
hsu_at rsegs (w_H WB) memB regsB (x_e rsegs cx) L.
Proof.
intros cx clob Wr L lyA SA WA regsA memA mdA lyB SB WB regsB memB mdB HC HJ Hr Hf Hp Hio Hmo Hm Hsub R2 R3 R4 Hs A.
split.
- apply (cb_core_step cx _ lyA SA WA regsA memA mdA lyB SB WB regsB memB mdB Wr HC HJ).
  + intros q Hq. apply (cb_reg_kept regsA regsB clob q Hr). destruct Hq as [->|[->| ->]]; assumption.
  + exact Hf.
  + exact Hp.
  + exact Hio.
  + exact Hmo.
  + exact Hm.
  + exact Hsub.
- exact (cb_atl_tr Wr clob (w_H WA) memA (w_H WB) memB regsA regsB _ L Hr Hm Hs A).
Qed.

(* a block that writes no byte *)
Lemma cb_blk_step : forall cx clob L lyA SA WA regsA memA mdA lyB SB WB regsB memB mdB,
hsu_core rsegs B MT cx (hsu_E1 rsegs headamp_himg_B cx) lyA SA WA regsA memA mdA ->
ajournal rsegs B (x_STK rsegs cx) (x_sp0 rsegs cx) (x_FP rsegs cx) (x_ly rsegs cx) (x_S rsegs cx) (x_W0 rsegs cx)
  (x_mem0 rsegs cx) (x_md0 rsegs cx) (x_own rsegs cx) lyB SB WB memB mdB (x_k rsegs cx) ->
(forall r : bv 5, bv_unsigned r <> 0 -> ~ In r clob -> getr regsB r = getr regsA r) ->
frames SB = frames SA -> Permutation (ablocks B lyB SB) (ablocks B lyA SA) -> same_io mdA mdB -> mo_le MT SA SB 0 ->
(forall a, aview rsegs (w_H WB) memB a = aview rsegs (w_H WA) memA a) ->
cb_regok clob 2 = true -> cb_regok clob 3 = true -> cb_regok clob 4 = true ->
Forall (cb_side clob (fun _ => False) (x_e rsegs cx)) L ->
hsu_at rsegs (w_H WA) memA regsA (x_e rsegs cx) L ->
hsu_core rsegs B MT cx (hsu_E1 rsegs headamp_himg_B cx) lyB SB WB regsB memB mdB /\
hsu_at rsegs (w_H WB) memB regsB (x_e rsegs cx) L.
Proof.
intros cx clob L lyA SA WA regsA memA mdA lyB SB WB regsB memB mdB HC HJ Hr Hf Hp Hio Hmo Hm R2 R3 R4 Hs A.
exact (cb_blkE_step cx clob (fun _ => False) L lyA SA WA regsA memA mdA lyB SB WB regsB memB mdB HC HJ Hr Hf Hp Hio
  Hmo (fun a _ _ => Hm a) (fun a (H : False) => False_ind _ H) R2 R3 R4 Hs A).
Qed.

(* ===================================== the two memory intrinsics =====================================
   YCbq.aj_intrin_at with the I/O state's sameness kept in the post (the callee's same_but_materialized) *)
Lemma cb_intrin_at : forall op pc, aintrin_realizes rsegs B op pc ->
forall W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc mdc k d x n (o : Z) raw,
ajournal rsegs B STK sp0 FP ly S W0 mem md own lyc Sc W memT mdc k ->
getr regsT 10 = w64 d -> getr regsT 11 = w64 x -> getr regsT 12 = w64 n -> 0 <= n < 2 ^ 32 -> 0 <= d -> d + n <= 2 ^ 63 ->
spZ regsT = sp0 + o -> o mod 16 = 0 -> o <= 0 -> ESTACK - o <= STK ->
getr regsT 3 = w64 (as_gp B) -> getr regsT 4 = w64 (as_tp B) -> getr regsT 1 = raw -> YK0s.ret_ok raw ->
(forall a, d <= a < d + n -> awr_byte STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own a /\ ~ (sp0 + o - ESTACK <= a < sp0 + o)) ->
amem_range d n ->
range_addressable (aview rsegs (w_H W) memT) SHADOW_OFF d n ->
(0 < n -> shadow_hull_vis (aview rsegs (w_H W) memT) d n) ->
(match op with
| OCpy => 0 <= x /\ x + n <= 2 ^ 63 /\ src_ok rsegs W regsT memT x n /\ (d + n <= x \/ x + n <= d) /\ amem_range x n /\
range_addressable (aview rsegs (w_H W) memT) SHADOW_OFF x n /\ (0 < n -> shadow_hull_vis (aview rsegs (w_H W) memT) x n)
| OSet => True end) ->
SRr rsegs W (mkCfg (mkst regsT (Z_to_bv 64 pc) memT (seg_rom rsegs)) mdc)
(fun W2 c2 => W2 = W /\ exists regs2 mem2 md2,
c2 = mkCfg (mkst regs2 raw mem2 (seg_rom rsegs)) md2 /\
ajournal rsegs B STK sp0 FP ly S W0 mem md own lyc Sc W mem2 md2 k /\ same_io mdc md2 /\
aregs_preserved regsT regs2 /\ getr regs2 10 = w64 d /\
(forall i, 0 <= i < n -> aview rsegs (w_H W) mem2 (d + i) =
match op with OCpy => aview rsegs (w_H W) memT (x + i) | OSet => Some (x mod 256) end) /\
(forall a, 0 <= a < 2 ^ 64 -> ~ (d <= a < d + n) -> ~ (sp0 + o - ESTACK <= a < sp0 + o) -> aview rsegs (w_H W) mem2 a = aview rsegs (w_H W) memT a) /\
(forall a, apresent (w_H W) memT a -> apresent (w_H W) mem2 a)).
Proof.
pose proof img_segs_low as segs_low.
intros op pc AI W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc mdc k d x n o raw
HJ Ha0 Ha1 Ha2 Hn Hd0 Hdn Hsp' Hal Hneg Hbud Hgp Htp Hra Hraw Hdest Hamr Hra_d Hhull Hsrc.
pose proof HJ as (HAR & Hly & Hsecs & Hwle & Hio & Hfrs & Hnev & Hk & _ & _ & _ & _ & _ & Hpres & Hstatic & F5 & HQT).
pose proof Hstatic as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop).
assert (ESTACK = 4096) as Hes by reflexivity. assert (ASTACK = 16384) as Has by reflexivity.
assert (HPRE : ecall_pre rsegs B lyc Sc W regsT memT mdc).
{ eapply (ecall_pre_at rsegs B STK sp0 FP ly S W0 mem md own lyc Sc W memT mdc k regsT o); try eassumption. rewrite Hra. exact Hraw. }
assert (HDEST : dest_ok rsegs B lyc Sc W regsT memT d n).
{ intros a Ha. destruct (Hdest a Ha) as [Hw Hns].
destruct (awr_byte_present rsegs B LAWS _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ a HJ Hw) as [Hp Hno]. rewrite Hsp'.
split; [apply apresent_writable; exact Hp | auto]. }
eapply SRr_mono.
{ exact (AI lyc Sc W regsT memT mdc d x n HPRE Ha0 Ha1 Ha2 Hn Hd0 Hdn HDEST Hamr Hra_d Hhull Hsrc). }
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HAR2 & HP & Hsame & Hres & Heff & Hfr & Hpres2).
rewrite Hsp' in Hfr.
split; [reflexivity|]. exists regs2, mem2, md2.
split; [unfold cfg_at, raZ; rewrite Hra; unfold w64; rewrite Z_to_bv_bv_unsigned; reflexivity|].
split.
{ eapply (ajournal_after_write rsegs B LAWS segs_low STK sp0 FP ly S W0 mem md own lyc Sc W memT mdc k mem2 md2
(fun a => (d <= a < d + n) \/ (sp0 + o - ESTACK <= a < sp0 + o)) Sc own HJ).
- intros a Ha Hna. apply (Hfr a Ha); intros H'; apply Hna; [left | right]; exact H'.
- exact Hpres2.
- exact Hsame.
- intros a [Ha | Ha]; left; [exact (proj1 (Hdest a Ha)) | left; zlia].
- exact HAR2.
- reflexivity. - reflexivity. - zlia. - exact Hfrs. - exact HQT. }
split; [apply same_io_materialized; exact Hsame|].
split; [exact HP|]. split; [exact Hres|]. split; [exact Heff|]. split; [exact Hfr | exact Hpres2].
Qed.

(* __asan_memset(d, c, n) at the entry pc (image B: CB_ASAN_MEMSET): the n bytes at d hold c mod 256 *)
Lemma cb_memset_at : forall pc, aintrin_realizes rsegs B OSet pc ->
forall W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc mdc k d c n (o : Z) raw,
ajournal rsegs B STK sp0 FP ly S W0 mem md own lyc Sc W memT mdc k ->
getr regsT 10 = w64 d -> getr regsT 11 = w64 c -> getr regsT 12 = w64 n -> 0 <= n < 2 ^ 32 -> 0 <= d -> d + n <= 2 ^ 63 ->
spZ regsT = sp0 + o -> o mod 16 = 0 -> o <= 0 -> ESTACK - o <= STK ->
getr regsT 3 = w64 (as_gp B) -> getr regsT 4 = w64 (as_tp B) -> getr regsT 1 = raw -> YK0s.ret_ok raw ->
(forall a, d <= a < d + n -> awr_byte STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own a /\ ~ (sp0 + o - ESTACK <= a < sp0 + o)) ->
amem_range d n ->
range_addressable (aview rsegs (w_H W) memT) SHADOW_OFF d n ->
(0 < n -> shadow_hull_vis (aview rsegs (w_H W) memT) d n) ->
SRr rsegs W (mkCfg (mkst regsT (Z_to_bv 64 pc) memT (seg_rom rsegs)) mdc)
(fun W2 c2 => W2 = W /\ exists regs2 mem2 md2,
c2 = mkCfg (mkst regs2 raw mem2 (seg_rom rsegs)) md2 /\
ajournal rsegs B STK sp0 FP ly S W0 mem md own lyc Sc W mem2 md2 k /\ same_io mdc md2 /\
aregs_preserved regsT regs2 /\ getr regs2 10 = w64 d /\
(forall i, 0 <= i < n -> aview rsegs (w_H W) mem2 (d + i) = Some (c mod 256)) /\
(forall a, 0 <= a < 2 ^ 64 -> ~ (d <= a < d + n) -> ~ (sp0 + o - ESTACK <= a < sp0 + o) -> aview rsegs (w_H W) mem2 a = aview rsegs (w_H W) memT a) /\
(forall a, apresent (w_H W) memT a -> apresent (w_H W) mem2 a)).
Proof.
intros pc AI W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc mdc k d c n o raw
HJ Ha0 Ha1 Ha2 Hn Hd0 Hdn Hsp' Hal Hneg Hbud Hgp Htp Hra Hraw Hdest Hamr Hra_d Hhull.
exact (cb_intrin_at OSet pc AI W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc mdc k d c n o raw
  HJ Ha0 Ha1 Ha2 Hn Hd0 Hdn Hsp' Hal Hneg Hbud Hgp Htp Hra Hraw Hdest Hamr Hra_d Hhull I).
Qed.

(* __asan_memcpy(d, x, n) at the entry pc (image B: CB_ASAN_MEMCPY): the n bytes at d are the n bytes at x *)
Lemma cb_memcpy_at : forall pc, aintrin_realizes rsegs B OCpy pc ->
forall W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc mdc k d x n (o : Z) raw,
ajournal rsegs B STK sp0 FP ly S W0 mem md own lyc Sc W memT mdc k ->
getr regsT 10 = w64 d -> getr regsT 11 = w64 x -> getr regsT 12 = w64 n -> 0 <= n < 2 ^ 32 -> 0 <= d -> d + n <= 2 ^ 63 ->
spZ regsT = sp0 + o -> o mod 16 = 0 -> o <= 0 -> ESTACK - o <= STK ->
getr regsT 3 = w64 (as_gp B) -> getr regsT 4 = w64 (as_tp B) -> getr regsT 1 = raw -> YK0s.ret_ok raw ->
(forall a, d <= a < d + n -> awr_byte STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own a /\ ~ (sp0 + o - ESTACK <= a < sp0 + o)) ->
amem_range d n ->
range_addressable (aview rsegs (w_H W) memT) SHADOW_OFF d n ->
(0 < n -> shadow_hull_vis (aview rsegs (w_H W) memT) d n) ->
0 <= x -> x + n <= 2 ^ 63 -> src_ok rsegs W regsT memT x n -> (d + n <= x \/ x + n <= d) -> amem_range x n ->
range_addressable (aview rsegs (w_H W) memT) SHADOW_OFF x n -> (0 < n -> shadow_hull_vis (aview rsegs (w_H W) memT) x n) ->
SRr rsegs W (mkCfg (mkst regsT (Z_to_bv 64 pc) memT (seg_rom rsegs)) mdc)
(fun W2 c2 => W2 = W /\ exists regs2 mem2 md2,
c2 = mkCfg (mkst regs2 raw mem2 (seg_rom rsegs)) md2 /\
ajournal rsegs B STK sp0 FP ly S W0 mem md own lyc Sc W mem2 md2 k /\ same_io mdc md2 /\
aregs_preserved regsT regs2 /\ getr regs2 10 = w64 d /\
(forall i, 0 <= i < n -> aview rsegs (w_H W) mem2 (d + i) = aview rsegs (w_H W) memT (x + i)) /\
(forall a, 0 <= a < 2 ^ 64 -> ~ (d <= a < d + n) -> ~ (sp0 + o - ESTACK <= a < sp0 + o) -> aview rsegs (w_H W) mem2 a = aview rsegs (w_H W) memT a) /\
(forall a, apresent (w_H W) memT a -> apresent (w_H W) mem2 a)).
Proof.
intros pc AI W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc mdc k d x n o raw
HJ Ha0 Ha1 Ha2 Hn Hd0 Hdn Hsp' Hal Hneg Hbud Hgp Htp Hra Hraw Hdest Hamr Hra_d Hhull Hx0 Hxn Hsx Hdis Hamx Hrax Hhx.
exact (cb_intrin_at OCpy pc AI W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc mdc k d x n o raw
  HJ Ha0 Ha1 Ha2 Hn Hd0 Hdn Hsp' Hal Hneg Hbud Hgp Htp Hra Hraw Hdest Hamr Hra_d Hhull
  (conj Hx0 (conj Hxn (conj Hsx (conj Hdis (conj Hamx (conj Hrax Hhx))))))).
Qed.

End d.
End b.

(* ======================================== side tactics ======================================== *)
(* a write-set membership HW refuted by lia: each disjunct in turn, the write set's definitions unfolded by hnf *)
Ltac cb_wr_lia HW :=
  lazymatch type of HW with
  | False => destruct HW
  | _ \/ _ => let H1 := fresh "HW" in let H2 := fresh "HW" in
      destruct HW as [H1|H2]; [cb_wr_lia H1 | cb_wr_lia H2]
  | _ /\ _ => lia
  | Z.le _ _ => lia
  | Z.lt _ _ => lia
  | _ => progress hnf in HW; cb_wr_lia HW
  end.
(* the cell R + o + ii is not in the write set Wr: the cell lies above the frame, its shadow and pp (cb_geo) *)
Ltac cb_not_wr HG Wr o ii Hii :=
  let A1 := fresh "A" in let A2 := fresh "A" in let A3 := fresh "A" in
  pose proof (cb_cell_not_frame _ _ _ o ii HG ltac:(lia) ltac:(lia) Hii) as A1;
  pose proof (cb_cell_not_fsh _ _ _ o ii HG ltac:(lia) ltac:(lia) Hii) as A2;
  pose proof (cb_cell_not_pp _ _ _ o ii HG ltac:(lia) ltac:(lia) Hii) as A3;
  let HW := fresh "HW" in intro HW; first [unfold Wr in HW | idtac]; cbv beta in HW;
  try cbv [HSU_T HSU_CH HSU_R4 HSU_E HSU_E42 HSU_E62 HMU_T HMU_CH HMU_R HMU_E HMU_E42 HMU_E62 HMU_RES HMU_X
    ESTACK ASTACK T_SEG_STK Layout.PP_SIZE Layout.OFF_LEN Layout.OFF_IS_PROPS Layout.OFF_HAS_PARAMS
    Layout.OFF_PARAMS_STRUCT Layout.OFF_ENT Layout.ENT_SIZE Layout.OFF_N_ENT Layout.OFF_CORRUPT] in HW, A3;
  clear - A1 A2 A3 Hii HW; cb_wr_lia HW.
(* one R-relative cell of a carried list *)
Ltac cb_side_cell HG Wr :=
  let ii := fresh "ii" in let Hii := fresh "Hii" in intros ii Hii;
  lazymatch goal with
  | |- 0 <= ?R + ?o + ii < _ /\ _ =>
      split; [apply (cb_R_cell _ _ _ o ii HG); [reflexivity | exact Hii] | cb_not_wr HG Wr o ii Hii]
  end.
(* the side conditions of a carried list (Forall (cb_side clob Wr e) L): registers by computation, R-relative
   cells by cb_R_cell and the write set Wr refuted from the cut's geometry HG *)
Ltac cb_sides HG Wr :=
  cb_unf;
  repeat (apply Forall_cons; [unfold cb_side; cbn [fst hd_xv];
    lazymatch goal with
    | |- cb_regok _ _ = true => vm_compute; reflexivity
    | |- forall _, _ => cb_side_cell HG Wr
    end|]); apply Forall_nil.
(* a list whose elements all lie in a literal list *)
Ltac cb_subs := cb_unf; repeat (apply Forall_cons; [cbv beta; left; cb_mem|]); apply Forall_nil.

Print Assumptions cb_kept_bv.
Print Assumptions cb_reg_kept.
Print Assumptions cb_regZ.
Print Assumptions cb_callee.
Print Assumptions cb_fsub.
Print Assumptions cb_div.
Print Assumptions cb_sh_off.
Print Assumptions cb_c_mod8.
Print Assumptions cb_inw1.
Print Assumptions cb_suffix_skip.
Print Assumptions cb_suffix_tl.
Print Assumptions cb_pc_ents_wf.
Print Assumptions cb_pp_len.
Print Assumptions cb_val_mod.
Print Assumptions cb_val_mod32.
Print Assumptions cb_val_kept.
Print Assumptions cb_chunk0.
Print Assumptions cb_region_nth.
Print Assumptions cb_chunks.
Print Assumptions cb_at_get.
Print Assumptions cb_at_reg.
Print Assumptions cb_at_cell8.
Print Assumptions cb_atl_tr.
Print Assumptions cb_R_cell.
Print Assumptions cb_cell_not_frame.
Print Assumptions cb_cell_not_fsh.
Print Assumptions cb_cell_not_pp.
Print Assumptions cb_fsh_not_frame.
Print Assumptions cb_fsh_not_pp.
Print Assumptions cb_fsh_low.
Print Assumptions cb_pp_not_frame.
Print Assumptions cb_pp_low.
Print Assumptions cb_frame_low.
Print Assumptions cb_shin.
Print Assumptions cb_bounds.
Print Assumptions cb_cur_skip.
Print Assumptions cb_cur_pos.
Print Assumptions cb_post_of_blk.
Print Assumptions cb_post_seq.
Print Assumptions cb_blk_seq.
Print Assumptions cb_pre_geom.
Print Assumptions cb_core_kept.
Print Assumptions cb_wr_shadow.
Print Assumptions cb_rom_now.
Print Assumptions cb_ctx_of.
Print Assumptions cb_core_step.
Print Assumptions cb_pod_base_mv.
Print Assumptions cb_in_kept.
Print Assumptions cb_blkE_step.
Print Assumptions cb_memset_at.
Print Assumptions cb_memcpy_at.
Print Assumptions cb_intrin_at.
Print Assumptions cb_in_now.
Print Assumptions cb_geo_of.
Print Assumptions cb_blk_step.
Print Assumptions cb_notin.
Print Assumptions cb_nz.
Print Assumptions cb_cs_bv.
Print Assumptions cb_cs_out.
Print Assumptions cb_reg_eq.
Print Assumptions cb_all256.
Print Assumptions cb_kept_run.
Print Assumptions cb_byte.
Print Assumptions cb_val_of_chunk.
Print Assumptions cb_val_at.
Print Assumptions cb_val_at_rng.
Print Assumptions cb_ra_kept.
Print Assumptions cb_hull_kept.
Print Assumptions cb_strok_kept.
Print Assumptions cb_strok_first_byte.
Print Assumptions cb_post_of_run.
