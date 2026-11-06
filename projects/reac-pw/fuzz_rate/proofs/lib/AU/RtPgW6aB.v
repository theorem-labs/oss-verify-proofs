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
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_headamp/lib/AU/HPgCaseB.v, with its module paths, module names and numbers changed; 789 of its 966 lines of code are new or changed and 912 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_role/lib/A/RPgW6a.v at 80bf14ccf117 for reac-pw/fuzz_rate's
   image A: module paths changed; the image is fuzz_rate.asan (images.Asan) instead of a lib/A/Img0 module; role's
   RPgSeg / RPgMem vocabulary (e_R, e_F, e_pp, rl_loc, rl_at, rl_xv, rl_inw, rm_, role_himg_A) becomes rate's (q_R,
   q_F, q_pp, rt_loc, rt_at, rt_xv, rt_inw, rtm_, rate_himg_A); the real frame is 0x1e0 bytes and the frame's shadow
   pattern 56; the image's first write range has six ranges; the pod index cell is R+0x128 and the address of e is in
   R+0x138; what is left of the input is the register s8 and the cursor s9 (role: the cell R+0xf8 and s9 / s8), so
   the kind block's outcome carries them in registers; the case tail writes no real-frame cell; the block chaining
   lemmas are RtPgSteps' rts_post / rts_post_seq / rts_blk_seq and AR_laws comes from the kernel theorem
   AR_laws_ok. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_rate/lib/A/RtPgW6a.v at 88912827c774 for the same unit's
   image B (fuzz_rate.asan-ubsan): images.AsanUbsan, lib/AU/RtPgSegB.v's cuts (rsb_), RtPgMemB (rtmb_), RtPgStepsB
   (rtsb_) and the statements of lib/AU/RtPgW6aBaseB.v; the helper prefix w6_ becomes w6m_; the frame for locals is
   class 4 (1024 bytes, 88 prologue shadow bytes), the pod object is e62 at F + 0x210 (granules 66 .. 78), the real
   frame is 0x220 bytes and the pod index cell R+0x178; the cursor is s10 and what is left s9 at C, and after the kind
   byte s2 / s6 / t1 / a6 (RtPgSegB rsb_L_D); the head block reads e62's address from s6; the case heads reload s6 from
   R+0x150 and the tail s2 from R+0x158, so the case blocks carry rsb_L_Dc0 and the tail takes the u32 block's or the
   head's cursor and in.n; the chaining is proved over the block STATEMENTS (w6b_disp_of, w6b_cases_of, in Section
   blocks). *)
(* reac-pw/fuzz_rate image B (fuzz_rate.asan-ubsan, pinned sha256
   c30584a7214902c43e35abebe35194418b7fdefacb6e7ed16fe0492228ec1d14; every address measured on the unstripped twin
   a1e5fa55ae27e657ea2719297ec4c037110f10fa9047c3ea7bb6ea7fcb358cb1, same loaded bytes): the two piece lemmas of the
   walk piece "ent_build A" of LLVMFuzzerTestOneInput (0x8076c), lib/AU/RtPgSegB.v's rsb_piece_W6a_disp_stmt and
   rsb_piece_W6a_cases_stmt at image B's segments, chained from the block statements of lib/AU/RtPgW6aBaseB.v.
   Proves no function (kind: segment lemma).

   THE DISPATCH (w6b_disp_of). From the pod loop's head C (0x813a0): the head block (w6b_head: [R+0x178] := k, e62's
   13 shadow granules := 0, the memset of e62) and the kind block (w6b_kind: the kind byte, kind % 10, the branch to
   case 9 or the jump table) end at one of the switch's entries; there the state is the cut D of that kind (or D0E
   when no input is left). The cut's journal, frames, blocks and the bytes outside the callees' stack and rsb_E1 come
   from the cut C through the two blocks' posts; the R cells, the registers and pp's image are kept (the head writes
   only [R - ESTACK, R), [R+0x178, R+0x180), e62 and its shadow); e62's shadow is the pattern rsb_PJ and e62 holds
   104 zeros.

   THE CASES 2 AND 3 (w6b_cases_of). From the cut D of kind % 10 = 2 (3): the case's head block (w6b_c2h /
   w6b_c3h), on an odd m the fuzz_u32 read-ahead block (lib/AU/RtPgStepsB.v rtsb_u32_block2 / 3), and the tail
   (w6b_tail at its four entries) end at J with e62 holding Layout.ent_mem of Model.ent_build's pod of the turn's
   input. *)
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d YG0q.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YI16 YM05.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Pod Require Import Cursor Model Layout.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Pod Require Tables.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.A Require Import RtPgBase RtPgCSpec.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.AU Require Import RtPgImgB RtPgMemB RtPgStepsB RtPgSegB.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.AU Require Import RtPgW6aKitB RtPgW6aBaseB.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.AU Require Import RtPgW6aHeadB RtPgW6aKindB RtPgW6aC2hB RtPgW6aC3hB.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.AU Require Import RtPgW6aTailB.
Require OSSVerify.reac_pw.fuzz_rate.images.AsanUbsan.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

(* image B's loaded segments; an abbreviation, so every statement names the image module's own term *)
Local Abbreviation rsegs := OSSVerify.reac_pw.fuzz_rate.images.AsanUbsan.M.loaded_segments.

(* ======================================== list tactics ======================================== *)
(* the location lists of the cuts, as literal lists *)
Ltac w6m_unf := cbv [rsb_L_pod rsb_Rc rsb_Rc0 rsb_Kc rsb_Hc rsb_podc rsb_L_Dc rsb_L_Dc0 rsb_L_D app].
(* membership in a literal list *)
Ltac w6m_mem := cbn [In]; repeat first [left; reflexivity | right].

Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Local Notation u8s l := (map (fun x : byte => bv_unsigned x) l).

(* ======================================== registers ======================================== *)
Definition w6m_regok (clob : list (bv 5)) (r : Z) : bool :=
negb (bv_unsigned (Z_to_bv 5 r) =? 0) && negb (existsb (fun c => bv_eqb c (Z_to_bv 5 r)) clob).

Lemma w6m_kept_bv : forall (regs regs' : bvmap 5 word) (clob : list (bv 5)) (q : bv 5),
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

Lemma w6m_reg_kept : forall (regs regs' : bvmap 5 word) clob r,
(forall q : bv 5, bv_unsigned q <> 0 -> ~ In q clob -> getr regs' q = getr regs q) ->
w6m_regok clob r = true -> getr regs' (Z_to_bv 5 r) = getr regs (Z_to_bv 5 r).
Proof. intros regs regs' clob r K H. exact (w6m_kept_bv regs regs' clob (Z_to_bv 5 r) K H). Qed.

Lemma w6m_regZ : forall (regs : bvmap 5 word) (q : bv 5) r, bv_unsigned q = r -> getr regs (Z_to_bv 5 r) = getr regs q.
Proof. intros regs q r <-. rewrite (Z_to_bv_bv_unsigned 5 q). reflexivity. Qed.

(* an 8-byte cell holds v exactly when it holds v mod 2^64 *)
Lemma w6m_val_mod : forall m a v, val_mem rsegs m a 8 (v mod 2 ^ 64) <-> val_mem rsegs m a 8 v.
Proof.
intros m a v. unfold val_mem.
assert (E : forall k, YO0f.le_byte (v mod 2 ^ 64) 8 k = YO0f.le_byte v 8 k).
{ intros k. unfold YO0f.le_byte. change (8 * Z.of_nat 8) with 64. rewrite Z.mod_mod by lia. reflexivity. }
split; intros H k Hk; specialize (H k Hk); [rewrite <- E | rewrite E]; exact H.
Qed.

(* a 4-byte cell holds v exactly when it holds v mod 2^32 *)
Lemma w6m_val_mod32 : forall m a v, val_mem rsegs m a 4 (v mod 2 ^ 32) <-> val_mem rsegs m a 4 v.
Proof.
intros m a v. unfold val_mem.
assert (E : forall k, YO0f.le_byte (v mod 2 ^ 32) 4 k = YO0f.le_byte v 4 k).
{ intros k. unfold YO0f.le_byte. change (8 * Z.of_nat 4) with 32. rewrite Z.mod_mod by lia. reflexivity. }
split; intros H k Hk; specialize (H k Hk); [rewrite <- E | rewrite E]; exact H.
Qed.

(* ======================================== location lists ======================================== *)
Lemma w6m_at_get : forall H mem regs e (L : list (rt_loc * Z)) l v,
rsb_at rsegs H mem regs e L -> In (l, v) L -> rt_at rsegs H mem regs e l v.
Proof. intros H mem regs e L l v A Hin. unfold rsb_at in A. rewrite Forall_forall in A. exact (A _ Hin). Qed.

Lemma w6m_at_reg : forall H mem regs e (L : list (rt_loc * Z)) r v (q : bv 5),
rsb_at rsegs H mem regs e L -> In (LReg r, v) L -> bv_unsigned q = r -> getr regs q = w64 v.
Proof.
intros H mem regs e L r v q A Hin Hq. rewrite <- (w6m_regZ regs q r Hq).
exact (w6m_at_get H mem regs e L (LReg r) v A Hin).
Qed.

Lemma w6m_at_cell8 : forall H mem regs e (L : list (rt_loc * Z)) b o v,
rsb_at rsegs H mem regs e L -> In (LCell b o, v) L -> val_mem rsegs (mrestrict H mem) (rt_xv e b + o) 8 v.
Proof. intros H mem regs e L b o v A Hin. apply w6m_val_mod. exact (w6m_at_get H mem regs e L (LCell b o) v A Hin). Qed.

Lemma w6m_fsub : forall {X} (P : X -> Prop) (L L' : list X), Forall P L -> Forall (fun f => In f L \/ P f) L' -> Forall P L'.
Proof.
intros X P L L' HL H. rewrite Forall_forall in *. intros f Hf.
destruct (H f Hf) as [Hi|Hp]; [exact (HL f Hi) | exact Hp].
Qed.

(* a location list carried across a block that keeps every register outside clob and every byte outside Wr *)
Definition w6m_side (clob : list (bv 5)) (Wr : Z -> Prop) (e : rt_renv) (f : rt_loc * Z) : Prop :=
match fst f with
| LReg r => w6m_regok clob r = true
| LCell b o => forall i, 0 <= i < 8 -> 0 <= rt_xv e b + o + i < 2 ^ 64 /\ ~ Wr (rt_xv e b + o + i)
end.
Lemma w6m_atl_tr : forall (Wr : Z -> Prop) clob H mem H' mem' regs regs' e L,
(forall q : bv 5, bv_unsigned q <> 0 -> ~ In q clob -> getr regs' q = getr regs q) ->
(forall a, 0 <= a < 2 ^ 64 -> ~ Wr a -> aview rsegs H' mem' a = aview rsegs H mem a) ->
Forall (w6m_side clob Wr e) L ->
rsb_at rsegs H mem regs e L -> rsb_at rsegs H' mem' regs' e L.
Proof.
intros Wr clob H mem H' mem' regs regs' e L K M C A. unfold rsb_at in *.
apply (rtmb_atl_kept rsegs H mem H' mem' regs regs' e L A).
intros f Hf. rewrite Forall_forall in C. specialize (C f Hf). unfold w6m_side in C.
destruct f as [[r|b o] v]; cbn [fst rtmb_keeps] in *.
- exact (w6m_reg_kept regs regs' clob r K C).
- intros i Hi. destruct (C i Hi) as [Hr Hn]. exact (M _ Hr Hn).
Qed.

(* ======================================== the geometry of a cut ========================================
   R's frame above the ceiling with the callees' stack below it, the frame for locals F (class 4: 1024 bytes) and its
   128 shadow bytes and the block pp below the ceiling, apart from each other *)
Definition w6m_geo (R F pp : Z) : Prop :=
alloc_ceiling + T_SEG_STK <= R /\ R + 0x220 <= 2 ^ 47 /\ kHighMemBeg <= R - T_SEG_STK /\
in_app F 1024 /\ 4096 <= F /\ F + 1024 <= alloc_ceiling /\ 0 <= shadow_addr F /\ shadow_addr F + 128 <= alloc_ceiling /\
(F + 1024 <= shadow_addr F \/ shadow_addr F + 128 <= F) /\
4096 <= pp /\ pp + Layout.PP_SIZE <= alloc_ceiling /\
(pp + Layout.PP_SIZE <= shadow_addr F \/ shadow_addr F + 128 <= pp) /\
(pp + Layout.PP_SIZE <= F \/ F + 1024 <= pp).

Lemma w6m_hw_cell : forall R F pp o i, w6m_geo R F pp ->
((0 <=? o) && (o + 8 <=? 0x220) && ((o + 8 <=? 0x178) || (0x180 <=? o)))%bool = true -> 0 <= i < 8 ->
0 <= R + o + i < 2 ^ 64 /\ ~ w6b_head_wr R F (R + o + i).
Proof.
intros R F pp o i G Hb Hi.
apply andb_prop in Hb as [Hb H3]. apply andb_prop in Hb as [H1 H2].
apply Z.leb_le in H1. apply Z.leb_le in H2. apply orb_prop in H3.
unfold w6m_geo, w6b_head_wr, T_SEG_STK, ASTACK, ESTACK in *.
destruct G as (G1 & G2 & _ & _ & G5 & G6 & G7 & G8 & _).
destruct H3 as [H3|H3]; apply Z.leb_le in H3; lia.
Qed.

Lemma w6m_R_cell : forall R F pp o i, w6m_geo R F pp -> ((0 <=? o) && (o + 8 <=? 0x220))%bool = true -> 0 <= i < 8 ->
0 <= R + o + i < 2 ^ 64.
Proof.
intros R F pp o i G Hb Hi. apply andb_prop in Hb as [H1 H2]. apply Z.leb_le in H1. apply Z.leb_le in H2.
unfold w6m_geo, T_SEG_STK, ASTACK in *. destruct G as (G1 & G2 & _ & _ & _ & _ & G7 & G8 & _). lia.
Qed.

Lemma w6m_hw_fsh : forall R F pp i, w6m_geo R F pp -> 0 <= i < 88 -> ~ (66 <= i < 79) ->
0 <= shadow_addr F + i < 2 ^ 64 /\ ~ w6b_head_wr R F (shadow_addr F + i).
Proof.
intros R F pp i G Hi Hn. unfold w6m_geo, w6b_head_wr, T_SEG_STK, ASTACK, ESTACK in *.
destruct G as (G1 & G2 & _ & _ & G5 & G6 & G7 & G8 & G9 & _). lia.
Qed.

Lemma w6m_hw_pp : forall R F pp i, w6m_geo R F pp -> 0 <= i < Layout.PP_SIZE ->
0 <= pp + i < 2 ^ 64 /\ ~ w6b_head_wr R F (pp + i).
Proof.
intros R F pp i G Hi. unfold w6m_geo, w6b_head_wr, T_SEG_STK, ASTACK, ESTACK in *.
destruct G as (G1 & G2 & _ & _ & G5 & G6 & G7 & G8 & G9 & G10 & G11 & G12 & G13). unfold Layout.PP_SIZE in *. lia.
Qed.

Lemma w6m_hw_shin : forall R F pp x, w6m_geo R F pp -> 0 <= x < kHighMemEnd ->
~ (shadow_addr F <= shadow_of_addr SHADOW_OFF x < shadow_addr F + 88) ->
0 <= shadow_of_addr SHADOW_OFF x < 2 ^ 64 /\ ~ w6b_head_wr R F (shadow_of_addr SHADOW_OFF x).
Proof.
intros R F pp x G Hx Hn.
destruct G as (G1 & G2 & G3 & G4 & _).
pose proof (rtmb_shadow_band x Hx) as Hb.
pose proof (rtmb_shadow_not_app x F 1024 Hx G4) as Hna.
unfold kLowMemEnd, kHighMemBeg in Hb. unfold kHighMemBeg in G3.
split; [lia|].
unfold w6b_head_wr, T_SEG_STK, ASTACK, ESTACK in *. intros [H|[H|[H|H]]]; [lia | lia | apply Hn; lia | apply Hna; lia].
Qed.

(* the image's first write range (RtPgImgB hi_w1: six ranges), piece by piece *)
Lemma w6m_inw1 : forall e a,
(q_F e + 0x20 <= a < q_F e + 0x278) \/
(shadow_addr (q_F e) + 4 <= a < shadow_addr (q_F e) + 79) \/
(q_R e <= a < q_R e + 0x30) \/
(q_R e + 0x58 <= a < q_R e + 0x148) \/
(q_R e + 0x150 <= a < q_R e + 0x180) \/
(q_R e + 0x198 <= a < q_R e + 0x1b8) -> rt_inw e (hi_w1 rate_himg_B) a.
Proof.
intros e a H. unfold rt_inw. cbn [hi_w1 rate_himg_B].
destruct H as [H|[H|[H|[H|[H|H]]]]].
- apply Exists_cons_hd. cbn [fst snd rt_xv]. lia.
- apply Exists_cons_tl, Exists_cons_hd. cbn [fst snd rt_xv]. lia.
- apply Exists_cons_tl, Exists_cons_tl, Exists_cons_hd. cbn [fst snd rt_xv]. lia.
- apply Exists_cons_tl, Exists_cons_tl, Exists_cons_tl, Exists_cons_hd. cbn [fst snd rt_xv]. lia.
- apply Exists_cons_tl, Exists_cons_tl, Exists_cons_tl, Exists_cons_tl, Exists_cons_hd. cbn [fst snd rt_xv]. lia.
- apply Exists_cons_tl, Exists_cons_tl, Exists_cons_tl, Exists_cons_tl, Exists_cons_tl, Exists_cons_hd.
  cbn [fst snd rt_xv]. lia.
Qed.

(* what the head writes is in the callees' stack or in the image's first write range *)
Lemma w6m_hw_E1 : forall e a, w6b_head_wr (q_R e) (q_F e) a ->
(q_R e - T_SEG_STK <= a < q_R e) \/ rt_inw e (hi_w1 rate_himg_B) a.
Proof.
intros e a H. unfold w6b_head_wr in H.
destruct H as [H|[H|[H|H]]].
- left. unfold T_SEG_STK, ASTACK, ESTACK in *. lia.
- right. apply w6m_inw1. right. right. right. right. left. lia.
- right. apply w6m_inw1. right. left. lia.
- right. apply w6m_inw1. left. lia.
Qed.

(* what the tail writes: e62's first 12 bytes *)
Lemma w6m_tw_E1 : forall e a, w6b_tail_wr (q_F e) a -> rt_inw e (hi_w1 rate_himg_B) a.
Proof. intros e a H. unfold w6b_tail_wr in H. apply w6m_inw1. left. lia. Qed.

Lemma w6m_tw_cell : forall R F pp o i, w6m_geo R F pp -> ((0 <=? o) && (o + 8 <=? 0x220))%bool = true -> 0 <= i < 8 ->
0 <= R + o + i < 2 ^ 64 /\ ~ w6b_tail_wr F (R + o + i).
Proof.
intros R F pp o i G Hb Hi. pose proof (w6m_R_cell R F pp o i G Hb Hi) as Hr.
apply andb_prop in Hb as [H1 H2]. apply Z.leb_le in H1. apply Z.leb_le in H2.
split; [exact Hr|].
unfold w6m_geo, w6b_tail_wr, T_SEG_STK, ASTACK in *.
destruct G as (G1 & G2 & _ & _ & G5 & G6 & _). lia.
Qed.

Lemma w6m_tw_fsh : forall R F pp i, w6m_geo R F pp -> 0 <= i < 88 ->
0 <= shadow_addr F + i < 2 ^ 64 /\ ~ w6b_tail_wr F (shadow_addr F + i).
Proof.
intros R F pp i G Hi. unfold w6m_geo, w6b_tail_wr, T_SEG_STK, ASTACK in *.
destruct G as (G1 & G2 & _ & _ & G5 & G6 & G7 & G8 & G9 & _). lia.
Qed.

Lemma w6m_tw_pp : forall R F pp i, w6m_geo R F pp -> 0 <= i < Layout.PP_SIZE ->
0 <= pp + i < 2 ^ 64 /\ ~ w6b_tail_wr F (pp + i).
Proof.
intros R F pp i G Hi. unfold w6m_geo, w6b_tail_wr, T_SEG_STK, ASTACK in *.
destruct G as (G1 & G2 & _ & _ & G5 & G6 & G7 & G8 & G9 & G10 & G11 & G12 & G13). unfold Layout.PP_SIZE in *. lia.
Qed.

Lemma w6m_tw_e : forall R F pp i, w6m_geo R F pp -> 12 <= i < 104 ->
0 <= F + 0x210 + i < 2 ^ 64 /\ ~ w6b_tail_wr F (F + 0x210 + i).
Proof.
intros R F pp i G Hi. unfold w6m_geo, w6b_tail_wr, T_SEG_STK, ASTACK in *.
destruct G as (G1 & G2 & _ & _ & G5 & G6 & _). lia.
Qed.

(* e62's address (the cases' [R+0x150]) and &pp->len (the tail's [R+0x158]) are 64-bit words *)
Lemma w6m_e62_range : forall R F pp, w6m_geo R F pp -> 0 <= F + 0x210 < 2 ^ 64.
Proof.
intros R F pp G. unfold w6m_geo, T_SEG_STK, ASTACK in *. destruct G as (G1 & G2 & _ & _ & G5 & G6 & _). lia.
Qed.

Lemma w6m_ppl_range : forall R F pp, w6m_geo R F pp -> 0 <= pp + 0x4000 < 2 ^ 64.
Proof.
intros R F pp G. unfold w6m_geo, T_SEG_STK, ASTACK in *.
destruct G as (G1 & G2 & _ & _ & _ & _ & _ & _ & _ & G10 & G11 & _). unfold Layout.PP_SIZE in *. lia.
Qed.

(* ======================================== the cursor and the suffix ======================================== *)
Lemma w6m_suffix_skip : forall rest r n, rsb_suffix rest r -> rsb_suffix rest (skipn n r).
Proof.
intros rest r n (j & Hj & ->). rewrite skipn_skipn.
destruct (Nat.le_gt_cases (n + j) (length rest)) as [Hle|Hgt].
- exists (n + j)%nat. split; [exact Hle | reflexivity].
- exists (length rest). split; [lia|]. rewrite !skipn_all2 by lia. reflexivity.
Qed.

Lemma w6m_cur_skip : forall (cx : rsb_scx rsegs) rest r n,
rsb_cur rsegs cx rest (skipn n r) = rsb_cur rsegs cx rest r + Z.of_nat (Nat.min n (length r)).
Proof. intros cx rest r n. unfold rsb_cur. rewrite length_skipn. lia. Qed.

Lemma w6m_cur_pos : forall (cx : rsb_scx rsegs) rest (b : byte) r, rsb_in rsegs cx rest -> rsb_suffix rest (b :: r) ->
0 < rsb_cur rsegs cx rest r - 1.
Proof.
intros cx rest b r HI (j & Hj & E). destruct HI as (Hleft & _ & _ & _ & _ & Hsrc & _).
assert (Hl : length (skipn j rest) = S (length r)) by (rewrite <- E; reflexivity).
rewrite length_skipn in Hl. unfold rsb_cur. lia.
Qed.

Lemma w6m_suffix_tl : forall rest b r', rsb_suffix rest (b :: r') -> rsb_suffix rest r'.
Proof.
intros rest b r' (j & Hj & E). exists (S j).
assert (Hl : length (skipn j rest) = S (length r')) by (rewrite <- E; reflexivity).
rewrite length_skipn in Hl. split; [lia|].
replace (S j) with (1 + j)%nat by lia. rewrite <- skipn_skipn, <- E. reflexivity.
Qed.

(* Model.ent_build's cases 2 and 3: the int / float pod of m, with the fuzz_u32 read-ahead on an odd m *)
Lemma w6m_ent_build : forall (c3 : bool) (b : byte) r, bv_unsigned b mod 10 = (if c3 then 3 else 2) ->
ent_build (b :: r) =
(Ent (if c3 then POD_FLOAT else POD_INT) 4
  (le32 (if Z.odd (fst (fuzz_u8 r)) then fst (fuzz_u32 (snd (fuzz_u8 r)))
         else if c3 then w6b_float_even (fst (fuzz_u8 r)) else w6b_int_even (fst (fuzz_u8 r)))),
 if Z.odd (fst (fuzz_u8 r)) then snd (fuzz_u32 (snd (fuzz_u8 r))) else snd (fuzz_u8 r)).
Proof.
intros c3 b r H. unfold ent_build.
change (fuzz_u8 (b :: r)) with (bv_unsigned b, r). cbv beta iota zeta.
rewrite H. destruct (fuzz_u8 r) as [m r1]. cbn [fst snd].
destruct c3; [change (Z.to_nat 3) with 3%nat | change (Z.to_nat 2) with 2%nat]; cbv beta iota;
destruct (Z.odd m); cbv beta iota.
- destruct (fuzz_u32 r1) as [v r2]. reflexivity.
- unfold w6b_float_even. destruct (m / 2 =? 127); [reflexivity|]. destruct (m / 2 =? 126); reflexivity.
- destruct (fuzz_u32 r1) as [v r2]. reflexivity.
- reflexivity.
Qed.

Lemma w6m_pc_23 : forall (c3 : bool) kd, kd mod 10 = (if c3 then 3 else 2) ->
rsb_pc_D kd = (if c3 then W6B_D3 else W6B_D2).
Proof. intros c3 kd H. unfold rsb_pc_D. rewrite H. destruct c3; reflexivity. Qed.

(* ======================================== pp's image ======================================== *)
Lemma w6m_pc_ents_wf : forall sh ps es, Forall (fun kv => pval_wf (snd kv)) ps -> Forall ent_wf (all_ents ps) ->
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

Lemma w6m_pp_len : forall sh ps es, rsb_wf sh ps -> Forall ent_wf es -> (length es < 32)%nat ->
Z.of_nat (length (pc_image (PbCut sh ps (Some es)))) = Layout.PP_SIZE.
Proof.
intros sh ps es (_ & Hkv & Hae & Hlp) Hes Hle.
assert (Hpv : Forall (fun kv => pval_wf (snd kv)) ps) by (eapply Forall_impl; [|exact Hkv]; intros kv [_ H]; exact H).
destruct (w6m_pc_ents_wf sh ps es Hpv Hae Hes ltac:(lia)) as [Hn Hw].
unfold pc_image. cbn [pc_shape pc_props pc_open]. apply length_pp_image.
- destruct (pc_buf_len_open sh ps es Hpv Hae Hes) as [H _]. lia.
- exact Hn.
- eapply Forall_impl; [|exact Hw]. intros e (_ & H1 & H2). rewrite H1. lia.
Qed.

(* ======================================== kind % 10 and the switch's entries ======================================== *)
Lemma w6m_case_pc_D : forall kd, w6b_case_pc kd = rsb_pc_D kd.
Proof.
intros kd. unfold w6b_case_pc, rsb_pc_D.
pose proof (Z.mod_pos_bound kd 10 ltac:(lia)) as Hm.
destruct jtb_tgt_vals as (J0 & J1 & J2 & J3 & J4 & J5 & J6 & J7 & J8).
assert (H : kd mod 10 = 0 \/ kd mod 10 = 1 \/ kd mod 10 = 2 \/ kd mod 10 = 3 \/ kd mod 10 = 4 \/
  kd mod 10 = 5 \/ kd mod 10 = 6 \/ kd mod 10 = 7 \/ kd mod 10 = 8 \/ kd mod 10 = 9) by lia.
destruct H as [H|[H|[H|[H|[H|[H|[H|[H|[H|H]]]]]]]]]; rewrite H;
[rewrite J0 | rewrite J1 | rewrite J2 | rewrite J3 | rewrite J4 | rewrite J5 | rewrite J6 | rewrite J7 | rewrite J8 | ];
reflexivity.
Qed.

Section d.
Variable B : asyms.
Variable MT : ameter_ops.
Hypothesis MTL : ameter_laws MT.

(* the kept registers and cells of the pod loop, from C to D: everything of the cut C that neither the head block
   (which writes [R+0x178, R+0x180), e62 and its shadow, and clobbers the caller-saved registers) nor the kind block
   (which writes nothing and clobbers t1, a0, a1, a2, a3, a6, s2, s6) changes *)
Definition w6m_Lk (cx : rsb_scx rsegs) (sh np : Z) (ps : list (Z * pval)) (cnt : Z) : list (rt_loc * Z) :=
rsb_Rc rsegs cx ++ rsb_Kc rsegs cx sh np ++ rsb_Hc rsegs cx ++
[(LCell XR 0xb0, Z.of_nat (length ps)); (LCell XR 0xa0, rsb_at_of sh ps);
 (LCell XR 0xa8, q_pp (x_e rsegs cx) + rsb_at_of sh ps); (LCell XR 0x140, cnt); (LCell XR 0x98, 1);
 (LCell XR 0x160, rsb_first ps)].

(* ======================================== a cut's geometry and context ======================================== *)
Lemma w6m_geo_of : forall cx E ly2 S2 W2 regs2 mem2 md2,
rsb_pre rsegs B cx -> rsb_core rsegs B MT cx E ly2 S2 W2 regs2 mem2 md2 ->
w6m_geo (q_R (x_e rsegs cx)) (q_F (x_e rsegs cx)) (q_pp (x_e rsegs cx)) /\
q_F (x_e rsegs cx) = frame_addr ly2 4 (x_pos rsegs cx) /\
spZ (x_regs rsegs cx) = q_R (x_e rsegs cx).
Proof.
intros cx E ly2 S2 W2 regs2 mem2 md2 HP HC.
destruct (w6k_pre_geom rsegs B cx HP) as (Hsp & HRk & HR47 & _ & HF0 & HFapp & HF32 & Happ).
pose proof HP as HP'.
destruct HP' as (HJ0 & _ & _ & _ & _ & HS & _ & HRs & HRstk & Hown & _ & _ & Hpp & _).
cbn [hi_cid hi_rsz rate_himg_B] in HRs, Hown.
destruct HC as (HJ & _ & _ & Hperm & _).
destruct HJ as (HAR & Hly & _ & _ & _ & Hfrs & _ & _ & _ & _ & _ & _ & _ & _ & Hstk & _).
destruct HJ0 as (_ & Hly0 & _).
assert (HFa : q_F (x_e rsegs cx) = frame_addr ly2 4 (x_pos rsegs cx)).
{ rewrite HF0. unfold frame_addr. destruct Hly as (_ & _ & _ & _ & _ & E2 & _).
  destruct Hly0 as (_ & _ & _ & _ & _ & E0 & _). rewrite E2, E0. reflexivity. }
assert (Hin : In (4, x_pos rsegs cx) (frames S2)) by (rewrite Hfrs; apply in_or_app; left; exact Hown).
assert (Hpp2 : In (q_pp (x_e rsegs cx), Layout.PP_SIZE) (ablocks B ly2 S2))
  by (eapply Permutation_in; [apply Permutation_sym; exact Hperm | exact Hpp]).
pose proof (sep_block_frame rsegs B (AR_laws_ok rsegs B) ly2 S2 W2 mem2 md2 _ _ 4 (x_pos rsegs cx) HAR Hpp2 Hin) as Hdj.
rewrite <- HFa in Hdj.
destruct (al_blocks _ _ (AR_laws_ok rsegs B) ly2 S2 W2 mem2 md2 _ _ HAR Hpp2) as (_ & Hp4 & Hp1 & _).
destruct Hstk as (_ & _ & Hac & Hlo & _).
pose proof (rtsb_fbounds (q_F (x_e rsegs cx)) HF32 HFapp) as (B1 & B2 & B3 & B4 & B5 & _).
replace (req_size Layout.PP_SIZE) with Layout.PP_SIZE in Hp1, Hdj by reflexivity.
unfold zdisjoint in Hdj. cbn [fst snd] in Hdj. change (fs_frame_bytes 4) with 1024 in Hdj.
pose proof ASAN_CEIL_range as (HC1 & _). unfold ASAN_CEIL in HC1.
pose proof (Z.div_mod (q_F (x_e rsegs cx)) 8 ltac:(lia)) as D1.
pose proof (Z.mod_pos_bound (q_F (x_e rsegs cx)) 8 ltac:(lia)) as D2.
split; [|split; [exact HFa | exact Hsp]].
unfold w6m_geo. split; [unfold T_SEG_STK, ASTACK in *; lia|].
split; [exact HR47|]. split; [exact HRk|]. split; [exact HFapp|].
do 5 (split; [lia|]). split; [exact Hp4|]. split; [lia|]. split; [|exact Hdj].
unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Happ. unfold shadow_addr, SHADOW_OFF in *.
unfold Layout.PP_SIZE in *. lia.
Qed.

Lemma w6m_ctx_of : forall cx ly2 S2 W2 regs2 mem2 md2,
rsb_pre rsegs B cx -> rsb_core rsegs B MT cx (rsb_E1 rsegs cx) ly2 S2 W2 regs2 mem2 md2 ->
w6b_ctx B (x_STK rsegs cx) (x_sp0 rsegs cx) (x_FP rsegs cx) (x_ly rsegs cx) (x_S rsegs cx) (x_W0 rsegs cx)
  (x_mem0 rsegs cx) (x_md0 rsegs cx) (x_own rsegs cx) (x_k rsegs cx) ly2 S2 W2 mem2 md2
  (q_R (x_e rsegs cx)) (q_F (x_e rsegs cx)) (x_pos rsegs cx).
Proof.
intros cx ly2 S2 W2 regs2 mem2 md2 HP HC.
destruct (w6m_geo_of cx _ ly2 S2 W2 regs2 mem2 md2 HP HC) as (_ & HFa & _).
pose proof (w6k_rom_now rsegs B MT rtsb_segs_low cx ly2 S2 W2 regs2 mem2 md2 HP HC) as Hrom.
pose proof HP as HP'. destruct HP' as (_ & _ & _ & _ & _ & HS & HR16 & HRs & HRstk & Hown & _).
cbn [hi_cid hi_rsz rate_himg_B] in HRs, Hown.
destruct HC as (HJ & _).
unfold w6b_ctx. split; [exact HJ|]. split; [exact HR16|]. split; [rewrite <- HS; exact HRs|].
split; [exact HRstk|]. split; [exact Hown|]. split; [exact HFa | exact Hrom].
Qed.

(* the journal-and-frame part of a cut, carried across a block *)
Lemma w6m_core_step : forall cx E ly2 S2 W2 regs2 mem2 md2 ly3 S3 W3 regs3 mem3 md3 (Wr : Z -> Prop),
rsb_core rsegs B MT cx E ly2 S2 W2 regs2 mem2 md2 ->
ajournal rsegs B (x_STK rsegs cx) (x_sp0 rsegs cx) (x_FP rsegs cx) (x_ly rsegs cx) (x_S rsegs cx) (x_W0 rsegs cx)
  (x_mem0 rsegs cx) (x_md0 rsegs cx) (x_own rsegs cx) ly3 S3 W3 mem3 md3 (x_k rsegs cx) ->
(forall r : Z, r = 2 \/ r = 3 \/ r = 4 -> getr regs3 (Z_to_bv 5 r) = getr regs2 (Z_to_bv 5 r)) ->
frames S3 = frames S2 -> Permutation (ablocks B ly3 S3) (ablocks B ly2 S2) -> same_io md2 md3 -> mo_le MT S2 S3 0 ->
(forall a, 0 <= a < 2 ^ 64 -> ~ Wr a -> aview rsegs (w_H W3) mem3 a = aview rsegs (w_H W2) mem2 a) ->
(forall a, Wr a -> (spZ (x_regs rsegs cx) - T_SEG_STK <= a < spZ (x_regs rsegs cx)) \/ E a) ->
rsb_core rsegs B MT cx E ly3 S3 W3 regs3 mem3 md3.
Proof using MTL.
intros cx E ly2 S2 W2 regs2 mem2 md2 ly3 S3 W3 regs3 mem3 md3 Wr HC HJ Hr Hf Hp Hio Hmo Hm Hsub.
unfold rsb_core, rsb_mid in *.
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

Lemma w6m_pod_base_mv : forall cx sh np ps cnt es rest rr r r' ly2 S2 W2 regs2 mem2 md2 ly3 S3 W3 regs3 mem3 md3,
rsb_pod_base rsegs B MT cx sh np ps cnt es rest rr r ly2 S2 W2 regs2 mem2 md2 ->
rsb_core rsegs B MT cx (rsb_E1 rsegs cx) ly3 S3 W3 regs3 mem3 md3 -> rsb_suffix rest r' ->
rsb_pod_base rsegs B MT cx sh np ps cnt es rest rr r' ly3 S3 W3 regs3 mem3 md3.
Proof.
intros cx sh np ps cnt es rest rr r r' ly2 S2 W2 regs2 mem2 md2 ly3 S3 W3 regs3 mem3 md3 (_ & H1 & _ & H3) HC HS.
split; [exact HC|]. split; [exact H1|]. split; [exact HS | exact H3].
Qed.

(* ======================================== the input at the cursor after a block ======================================== *)
Lemma w6m_in_kept : forall cx rest r (W2 : world rsegs) mem2 (W1 : world rsegs) mem1,
rsb_pre rsegs B cx -> rsb_in rsegs cx rest -> rsb_suffix rest r ->
w6m_geo (q_R (x_e rsegs cx)) (q_F (x_e rsegs cx)) (q_pp (x_e rsegs cx)) ->
rt_fsh rsegs (w_H (x_W rsegs cx)) (x_memc rsegs cx) (q_F (x_e rsegs cx)) (hi_shA rate_himg_B) ->
garr8 rsegs (mrestrict (w_H W2) mem2) (q_src (x_e rsegs cx)) (rsb_u8s rest) ->
range_addressable (aview rsegs (w_H W2) mem2) SHADOW_OFF (q_src (x_e rsegs cx)) (q_left (x_e rsegs cx)) ->
(forall a, 0 <= a < 2 ^ 64 -> ~ w6b_head_wr (q_R (x_e rsegs cx)) (q_F (x_e rsegs cx)) a ->
 aview rsegs (w_H W1) mem1 a = aview rsegs (w_H W2) mem2 a) ->
w6b_in W1 mem1 (q_R (x_e rsegs cx)) (rsb_cur rsegs cx rest r) r.
Proof.
intros cx rest r W2 mem2 W1 mem1 HP HI (j & Hj & ->) HG Hfsh0 Hg Hra Hm.
destruct HI as (Hleft & Hg0 & Hra0 & _ & Ham & Hsrc & Htop & Hx).
assert (Hcur : rsb_cur rsegs cx rest (skipn j rest) = q_src (x_e rsegs cx) + Z.of_nat j)
  by (unfold rsb_cur; rewrite length_skipn; lia).
unfold w6b_in. rewrite Hcur. rewrite length_skipn.
assert (Hn : forall x, q_src (x_e rsegs cx) <= x < q_src (x_e rsegs cx) + Z.of_nat (length rest) ->
  0 <= x < kHighMemEnd /\ ~ w6b_head_wr (q_R (x_e rsegs cx)) (q_F (x_e rsegs cx)) x /\
  ~ (q_R (x_e rsegs cx) + 0x150 <= x < q_R (x_e rsegs cx) + 0x180) /\
  ~ (q_R (x_e rsegs cx) - T_SEG_STK <= x < q_R (x_e rsegs cx))).
{ intros x Hx'. rewrite <- Hleft in Hx'. destruct (Hx x Hx') as (D1 & D2 & _).
  split; [unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in *; lia|].
  split; [intros HW; destruct (w6m_hw_E1 (x_e rsegs cx) x HW) as [X|X]; [exact (D1 X) | exact (D2 X)]|].
  split; [intros X; apply D2; apply w6m_inw1; right; right; right; right; left; exact X | exact D1]. }
split; [|split; [|split; [lia|split; [lia|split]]]].
- assert (Hg1 : rtmb_bytes rsegs (w_H W2) mem2 (q_src (x_e rsegs cx) + Z.of_nat j) (skipn j rest)).
  { pose proof (proj1 (rtmb_bytes_app rsegs (w_H W2) mem2 (q_src (x_e rsegs cx)) (firstn j rest) (skipn j rest))) as Happ.
    rewrite firstn_skipn in Happ. destruct (Happ Hg) as [_ H2].
    rewrite length_firstn, Nat.min_l in H2 by lia. exact H2. }
  apply (rtmb_bytes_kept rsegs (w_H W2) mem2 (w_H W1) mem1 _ _ Hg1).
  intros x Hx'. rewrite length_skipn in Hx'. destruct (Hn x ltac:(lia)) as (Hb & Hw & _).
  apply Hm; [unfold kHighMemEnd in Hb; lia | exact Hw].
- intros x Hx'. destruct (Hn x ltac:(lia)) as (Hb & _).
  pose proof (rtmb_ra_not_fsh rsegs _ _ _ _ (q_src (x_e rsegs cx)) (q_left (x_e rsegs cx)) Hra0 Hfsh0 rtmb_sh_P0_big x
    ltac:(lia)) as Hnf.
  change (Z.of_nat (length (hi_shA rate_himg_B))) with 88 in Hnf.
  destruct (w6m_hw_shin _ _ _ x HG Hb Hnf) as [Hb2 Hw2].
  rewrite (Hm _ Hb2 Hw2). apply Hra. lia.
- unfold amem_range in *. lia.
- intros a Ha. destruct (Hn a ltac:(lia)) as (_ & _ & D3 & D4).
  split; [exact D4 | exact D3].
Qed.

(* ======================================== the location lists of D and D0E ======================================== *)
Lemma w6m_at_D0E : forall cx sh np ps cnt es rest H mem regs,
rsb_at rsegs H mem regs (x_e rsegs cx) (w6m_Lk cx sh np ps cnt ++ [(LCell XR 0x178, Z.of_nat (length es))]) ->
getr regs 26 = w64 (rsb_cur rsegs cx rest []) -> getr regs 25 = w64 0 ->
rsb_at rsegs H mem regs (x_e rsegs cx)
  (rsb_L_Dc rsegs cx sh np ps cnt es ++ [(LReg 26, rsb_cur rsegs cx rest []); (LReg 25, 0)]).
Proof.
intros cx sh np ps cnt es rest H mem regs A R26 R25.
pose proof A as A'. unfold rsb_at in A' |- *. apply Forall_app. split.
- apply (w6m_fsub _ _ _ A'). unfold w6m_Lk. w6m_unf.
  repeat (apply Forall_cons; [cbv beta; left; w6m_mem|]). apply Forall_nil.
- apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]; cbn [fst snd rt_at].
  + rewrite (w6m_regZ regs (26%bv : bv 5) 26 eq_refl). exact R26.
  + rewrite (w6m_regZ regs (25%bv : bv 5) 25 eq_refl). exact R25.
Qed.

Lemma w6m_at_D : forall cx sh np ps cnt es rest (b : byte) r' H mem regs,
rsb_at rsegs H mem regs (x_e rsegs cx) (w6m_Lk cx sh np ps cnt ++ [(LCell XR 0x178, Z.of_nat (length es))]) ->
getr regs 26 = w64 (rsb_cur rsegs cx rest (b :: r')) ->
w6b_kind_R (bv_unsigned b) (rsb_cur rsegs cx rest (b :: r')) (Z.of_nat (length r')) regs ->
rsb_at rsegs H mem regs (x_e rsegs cx) (rsb_L_D rsegs cx sh np ps cnt es rest r' (bv_unsigned b)).
Proof.
intros cx sh np ps cnt es rest b r' H mem regs A R26 (R18 & R16 & R6 & R22 & RK).
pose proof (rtmb_byte_range b) as Hb.
assert (Hcur : rsb_cur rsegs cx rest r' = rsb_cur rsegs cx rest (b :: r') + 1)
  by (unfold rsb_cur; cbn [length]; lia).
pose proof A as A'. unfold rsb_at in A' |- *. unfold rsb_L_D. apply Forall_app. split; [|apply Forall_app; split].
- apply (w6m_fsub _ _ _ A'). unfold w6m_Lk. w6m_unf.
  repeat (apply Forall_cons; [cbv beta; left; w6m_mem|]). apply Forall_nil.
- apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons;
    [|apply Forall_nil]]]]]; cbn [fst snd rt_at].
  + rewrite (w6m_regZ regs (6%bv : bv 5) 6 eq_refl). exact R6.
  + rewrite (w6m_regZ regs (26%bv : bv 5) 26 eq_refl), Hcur.
    replace (rsb_cur rsegs cx rest (b :: r') + 1 - 1) with (rsb_cur rsegs cx rest (b :: r')) by lia. exact R26.
  + rewrite (w6m_regZ regs (18%bv : bv 5) 18 eq_refl), Hcur. exact R18.
  + rewrite (w6m_regZ regs (22%bv : bv 5) 22 eq_refl). exact R22.
  + rewrite (w6m_regZ regs (16%bv : bv 5) 16 eq_refl). exact R16.
- destruct (bv_unsigned b mod 10 =? 9).
  + apply Forall_cons; [|apply Forall_nil]; cbn [fst snd rt_at].
    rewrite (w6m_regZ regs (12%bv : bv 5) 12 eq_refl). exact RK.
  + destruct RK as (R10 & R12 & R13).
    apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]]; cbn [fst snd rt_at].
    * rewrite (w6m_regZ regs (12%bv : bv 5) 12 eq_refl). exact R12.
    * rewrite (w6m_regZ regs (13%bv : bv 5) 13 eq_refl), R13. f_equal. unfold sext8.
      destruct (Z.ltb_spec (bv_unsigned b) 128) as [Hl|Hl]; cbv beta iota.
      -- rewrite (Z.div_small (bv_unsigned b) 128) by lia. lia.
      -- rewrite <- (Z.div_unique (bv_unsigned b) 128 1 (bv_unsigned b - 128)) by lia. lia.
    * rewrite (w6m_regZ regs (10%bv : bv 5) 10 eq_refl). apply bv_eq. rewrite R10. unfold w64.
      rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
      rewrite (Z.mod_small (bv_unsigned b) 256) by lia. rewrite Z.mod_small; [reflexivity | lia].
Qed.

(* the side conditions of a carried list: registers by computation, cells by w6m_hw_cell / w6m_tw_cell / w6m_R_cell *)
Ltac w6m_sides_head HG :=
try unfold w6m_Lk; w6m_unf;
repeat (apply Forall_cons; [unfold w6m_side; cbn [fst rt_xv];
  lazymatch goal with
  | |- w6m_regok _ _ = true => vm_compute; reflexivity
  | |- forall _, _ => let ii := fresh "ii" in let Hii := fresh "Hii" in
      intros ii Hii; apply (w6m_hw_cell _ _ _ _ ii HG); [reflexivity | exact Hii]
  end|]); apply Forall_nil.
Ltac w6m_sides_tail HG :=
try unfold w6m_Lk; w6m_unf;
repeat (apply Forall_cons; [unfold w6m_side; cbn [fst rt_xv];
  lazymatch goal with
  | |- w6m_regok _ _ = true => vm_compute; reflexivity
  | |- forall _, _ => let ii := fresh "ii" in let Hii := fresh "Hii" in
      intros ii Hii; apply (w6m_tw_cell _ _ _ _ ii HG); [reflexivity | exact Hii]
  end|]); apply Forall_nil.
Ltac w6m_sides_all HG :=
try unfold w6m_Lk; w6m_unf;
repeat (apply Forall_cons; [unfold w6m_side; cbn [fst rt_xv];
  lazymatch goal with
  | |- w6m_regok _ _ = true => vm_compute; reflexivity
  | |- forall _, _ => let ii := fresh "ii" in let Hii := fresh "Hii" in
      intros ii Hii; split; [apply (w6m_R_cell _ _ _ _ ii HG); [reflexivity | exact Hii] | tauto]
  end|]); apply Forall_nil.
(* a list whose elements all lie in a literal list *)
Ltac w6m_subs := try unfold w6m_Lk; w6m_unf; repeat (apply Forall_cons; [cbv beta; left; w6m_mem|]); apply Forall_nil.

(* a block that writes no byte: the cut's journal-and-frame part and a carried location list *)
Lemma w6m_blk_step : forall cx clob L lyA SA WA regsA memA mdA lyB SB WB regsB memB mdB,
rsb_core rsegs B MT cx (rsb_E1 rsegs cx) lyA SA WA regsA memA mdA ->
ajournal rsegs B (x_STK rsegs cx) (x_sp0 rsegs cx) (x_FP rsegs cx) (x_ly rsegs cx) (x_S rsegs cx) (x_W0 rsegs cx)
  (x_mem0 rsegs cx) (x_md0 rsegs cx) (x_own rsegs cx) lyB SB WB memB mdB (x_k rsegs cx) ->
(forall r : bv 5, bv_unsigned r <> 0 -> ~ In r clob -> getr regsB r = getr regsA r) ->
frames SB = frames SA -> Permutation (ablocks B lyB SB) (ablocks B lyA SA) -> same_io mdA mdB -> mo_le MT SA SB 0 ->
(forall a, aview rsegs (w_H WB) memB a = aview rsegs (w_H WA) memA a) ->
w6m_regok clob 2 = true -> w6m_regok clob 3 = true -> w6m_regok clob 4 = true ->
Forall (w6m_side clob (fun _ => False) (x_e rsegs cx)) L ->
rsb_at rsegs (w_H WA) memA regsA (x_e rsegs cx) L ->
rsb_core rsegs B MT cx (rsb_E1 rsegs cx) lyB SB WB regsB memB mdB /\ rsb_at rsegs (w_H WB) memB regsB (x_e rsegs cx) L.
Proof using MTL.
intros cx clob L lyA SA WA regsA memA mdA lyB SB WB regsB memB mdB HC HJ Hr Hf Hp Hio Hmo Hm R2 R3 R4 Hs A.
split.
- apply (w6m_core_step cx _ lyA SA WA regsA memA mdA lyB SB WB regsB memB mdB (fun _ => False) HC HJ).
  + intros q Hq. apply (w6m_reg_kept regsA regsB clob q Hr). destruct Hq as [->|[->| ->]]; assumption.
  + exact Hf.
  + exact Hp.
  + exact Hio.
  + exact Hmo.
  + intros a _ _. exact (Hm a).
  + intros a [].
- exact (w6m_atl_tr (fun _ => False) clob (w_H WA) memA (w_H WB) memB regsA regsB _ L Hr (fun a _ _ => Hm a) Hs A).
Qed.

(* ======================================== the chaining over the block statements ======================================== *)
Section blocks.
(* the five block statements of lib/AU/RtPgW6aBaseB.v; the fuzz_u32 read-ahead blocks are RtPgStepsB's
   rtsb_u32_block2 / rtsb_u32_block3 *)
Hypothesis HHEAD : w6b_head_stmt B MT.
Hypothesis HKIND : w6b_kind_stmt B MT.
Hypothesis HC2 : w6b_c2h_stmt B MT.
Hypothesis HC3 : w6b_c3h_stmt B MT.
Hypothesis HTAIL : forall c3 a, w6b_tail_stmt B MT c3 a.

(* ---------------------------------------- W6a, the dispatch ---------------------------------------- *)
Lemma w6b_disp_of : rsb_piece_W6a_disp_stmt rsegs B MT.
Proof using MTL HHEAD HKIND.
intros cx POST rest i k Hst HD HD0E.
unfold rsb_from_D in HD. unfold rsb_from_D0E in HD0E. unfold rsb_from_C.
intros lyC SC WC regsC memC mdC sh np ps cnt es r Hlp Hle HC.
destruct Hst as (HP & HFSH0 & _ & _ & HIN).
destruct HC as (HB & HAT & HFSH & HPP).
pose proof HB as HB0.
destruct HB as (HCORE & _ & HSUF & _ & Hwf & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hesw & Hesl & _).
destruct (w6m_geo_of cx _ _ _ _ _ _ _ HP HCORE) as (HG & HFa & HspZ).
pose proof (w6m_ctx_of cx _ _ _ _ _ _ HP HCORE) as HCTX.
pose proof (w6m_pp_len sh ps es Hwf Hesw Hesl) as Hppl.
unfold rsb_at_cx in HAT.
(* the registers the two blocks read, at C *)
assert (A9 : getr regsC 9 = w64 (q_R (x_e rsegs cx)))
  by (apply (w6m_at_reg _ _ _ _ _ 9 _ _ HAT); [w6m_unf; w6m_mem | reflexivity]).
assert (A19 : getr regsC 19 = w64 (shadow_addr (q_F (x_e rsegs cx))))
  by (apply (w6m_at_reg _ _ _ _ _ 19 _ _ HAT); [w6m_unf; w6m_mem | reflexivity]).
assert (A20 : getr regsC 20 = w64 SHADOW_OFF)
  by (apply (w6m_at_reg _ _ _ _ _ 20 _ _ HAT); [w6m_unf; w6m_mem | reflexivity]).
assert (A26 : getr regsC 26 = w64 (rsb_cur rsegs cx rest r))
  by (apply (w6m_at_reg _ _ _ _ _ 26 _ _ HAT); [w6m_unf; w6m_mem | reflexivity]).
assert (A25 : getr regsC 25 = w64 (Z.of_nat (length r)))
  by (apply (w6m_at_reg _ _ _ _ _ 25 _ _ HAT); [w6m_unf; w6m_mem | reflexivity]).
assert (A22 : getr regsC 22 = w64 (q_F (x_e rsegs cx) + 0x210))
  by (apply (w6m_at_reg _ _ _ _ _ 22 _ _ HAT); [w6m_unf; w6m_mem | reflexivity]).
assert (A11 : getr regsC 11 = w64 (Z.of_nat (length es)))
  by (apply (w6m_at_reg _ _ _ _ _ 11 _ _ HAT); [w6m_unf; w6m_mem | reflexivity]).
assert (A234 : forall q : Z, q = 2 \/ q = 3 \/ q = 4 -> getr regsC (Z_to_bv 5 q) = getr (x_regs rsegs cx) (Z_to_bv 5 q))
  by (destruct HCORE as (_ & Hq & _); exact Hq).
assert (A2 : getr regsC 2 = w64 (q_R (x_e rsegs cx))).
{ rewrite <- (w6m_regZ regsC (2%bv : bv 5) 2 eq_refl), (A234 2 ltac:(lia)), (w6m_regZ _ (2%bv : bv 5) 2 eq_refl).
  destruct HP as (_ & _ & H2 & _). exact H2. }
assert (A3 : getr regsC 3 = w64 (as_gp B)).
{ rewrite <- (w6m_regZ regsC (3%bv : bv 5) 3 eq_refl), (A234 3 ltac:(lia)), (w6m_regZ _ (3%bv : bv 5) 3 eq_refl).
  destruct HP as (_ & _ & _ & H3 & _). exact H3. }
assert (A4 : getr regsC 4 = w64 (as_tp B)).
{ rewrite <- (w6m_regZ regsC (4%bv : bv 5) 4 eq_refl), (A234 4 ltac:(lia)), (w6m_regZ _ (4%bv : bv 5) 4 eq_refl).
  destruct HP as (_ & _ & _ & _ & H4 & _). exact H4. }
(* the input at C *)
destruct (w6k_in_now rsegs B MT cx rest rsb_P0 lyC SC WC regsC memC mdC HP HFSH0 HIN HCORE HFSH eq_refl)
  as (HgC & HraC & _).
(* ---------------- the head block ---------------- *)
pose proof (HHEAD _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ regsC _ _ _ (Z.of_nat (length es))
  HCTX A2 A9 A19 A3 A4 A11 A22) as HH.
eapply SRr_bind; [exact HH|]. clear HH.
intros W1 c1 Hw1 (ly1 & S1 & regs1 & mem1 & md1 & -> & HJ1 & Hr1 & Hf1 & Hp1 & Hio1 & Hmo1 & Hm1 & _ & H178 & Hsh0 & He0).
assert (HCORE1 : rsb_core rsegs B MT cx (rsb_E1 rsegs cx) ly1 S1 W1 regs1 mem1 md1).
{ apply (w6m_core_step cx _ lyC SC WC regsC memC mdC ly1 S1 W1 regs1 mem1 md1
    (w6b_head_wr (q_R (x_e rsegs cx)) (q_F (x_e rsegs cx))) HCORE HJ1).
  - intros q Hq. apply (w6m_reg_kept regsC regs1 rtsb_caller_saved q Hr1).
    destruct Hq as [->|[->| ->]]; vm_compute; reflexivity.
  - exact Hf1.
  - exact Hp1.
  - exact Hio1.
  - exact Hmo1.
  - exact Hm1.
  - intros a Ha. rewrite HspZ. destruct (w6m_hw_E1 (x_e rsegs cx) a Ha) as [X|X];
    [left; exact X | right; left; exact X]. }
(* the kept registers and cells, at the head's end *)
assert (HAT1a : rsb_at rsegs (w_H W1) mem1 regs1 (x_e rsegs cx) (w6m_Lk cx sh np ps cnt)).
{ apply (w6m_atl_tr (w6b_head_wr (q_R (x_e rsegs cx)) (q_F (x_e rsegs cx))) rtsb_caller_saved (w_H WC) memC _ _
    regsC _ _ _ Hr1 Hm1).
  - w6m_sides_head HG.
  - apply (w6m_fsub _ _ _ HAT). unfold w6m_Lk. w6m_unf.
    repeat (apply Forall_cons; [cbv beta; left; w6m_mem|]). apply Forall_nil. }
assert (HAT1 : rsb_at rsegs (w_H W1) mem1 regs1 (x_e rsegs cx)
  (w6m_Lk cx sh np ps cnt ++ [(LCell XR 0x178, Z.of_nat (length es))])).
{ unfold rsb_at in *. apply Forall_app. split; [exact HAT1a|].
  apply Forall_cons; [|apply Forall_nil]. cbn [fst snd rt_at rt_xv].
  exact H178. }
clear HAT1a.
assert (B20 : getr regs1 20 = w64 SHADOW_OFF)
  by (rewrite (w6m_kept_bv regsC regs1 rtsb_caller_saved (20%bv : bv 5) Hr1 ltac:(vm_compute; reflexivity)); exact A20).
assert (B26 : getr regs1 26 = w64 (rsb_cur rsegs cx rest r))
  by (rewrite (w6m_kept_bv regsC regs1 rtsb_caller_saved (26%bv : bv 5) Hr1 ltac:(vm_compute; reflexivity)); exact A26).
assert (B25 : getr regs1 25 = w64 (Z.of_nat (length r)))
  by (rewrite (w6m_kept_bv regsC regs1 rtsb_caller_saved (25%bv : bv 5) Hr1 ltac:(vm_compute; reflexivity)); exact A25).
(* e62's shadow and e62, the block pp and the input, at the head's end *)
assert (HFSH1 : rt_fsh rsegs (w_H W1) mem1 (q_F (x_e rsegs cx)) rsb_PJ).
{ replace rsb_PJ with (rtmb_setn rsb_P0 66 13 0)
    by (exact (rtmb_sh_e62_in false false false false false false false)).
  apply (rtmb_fsh_set rsegs (w_H WC) memC (w_H W1) mem1 _ rsb_P0 66 13 0 HFSH).
  - intros ii Hii. change (Z.of_nat 66) with 66 in Hii. change (Z.of_nat (66 + 13)) with 79 in Hii.
    replace (shadow_addr (q_F (x_e rsegs cx)) + ii) with (shadow_addr (q_F (x_e rsegs cx)) + 66 + (ii - 66)) by lia.
    apply Hsh0. lia.
  - intros ii Hii Hn. change (Z.of_nat (length rsb_P0)) with 88 in Hii.
    change (Z.of_nat 66) with 66 in Hn. change (Z.of_nat (66 + 13)) with 79 in Hn.
    destruct (w6m_hw_fsh _ _ _ ii HG ltac:(lia) ltac:(lia)) as [Hb Hw]. exact (Hm1 _ Hb Hw). }
assert (HE1 : rtmb_bytes rsegs (w_H W1) mem1 (q_F (x_e rsegs cx) + 0x210) (zeros 104)).
{ change (zeros 104) with (repeat (Z_to_bv 8 0) 104). apply (rtmb_memset_bytes rsegs (w_H W1) mem1 _ 0 104).
  intros ii Hii. exact (He0 ii Hii). }
assert (HPP1 : rsb_pp_at rsegs cx W1 mem1 (pc_image (PbCut sh ps (Some es)))).
{ unfold rsb_pp_at in *. apply (rtmb_bytes_kept rsegs (w_H WC) memC (w_H W1) mem1 _ _ HPP).
  intros x Hx. rewrite Hppl in Hx.
  destruct (w6m_hw_pp _ _ _ (x - q_pp (x_e rsegs cx)) HG ltac:(lia)) as [Hb Hw].
  replace x with (q_pp (x_e rsegs cx) + (x - q_pp (x_e rsegs cx))) by lia. exact (Hm1 _ Hb Hw). }
pose proof (w6m_in_kept cx rest r WC memC W1 mem1 HP HIN HSUF HG HFSH0 HgC HraC Hm1) as HIN1.
pose proof (w6m_ctx_of cx ly1 S1 W1 regs1 mem1 md1 HP HCORE1) as HCTX1.
(* ---------------- the kind block ---------------- *)
pose proof (HKIND _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ regs1 _ _ _ (rsb_cur rsegs cx rest r) r
  HCTX1 B20 B26 B25 HIN1) as HK.
eapply SRr_bind; [exact HK|]. clear HK.
intros W3 c3 Hw3 [(Hr0 & HPOST) | (b & r' & Hr & HPOST)].
- (* no input left: D0E *)
  subst r.
  destruct HPOST as (ly3 & S3 & regs3 & mem3 & md3 & -> & HJ3 & Hr3 & Hf3 & Hp3 & Hio3 & Hmo3 & Hm3 & _).
  assert (HCORE3 : rsb_core rsegs B MT cx (rsb_E1 rsegs cx) ly3 S3 W3 regs3 mem3 md3).
  { apply (w6m_core_step cx _ ly1 S1 W1 regs1 mem1 md1 ly3 S3 W3 regs3 mem3 md3 (fun _ => False) HCORE1 HJ3).
    - intros q Hq. apply (w6m_reg_kept regs1 regs3 [] q Hr3). destruct Hq as [->|[->| ->]]; vm_compute; reflexivity.
    - exact Hf3.
    - exact Hp3.
    - exact Hio3.
    - exact Hmo3.
    - intros a _ _. exact (Hm3 a).
    - intros a []. }
  apply (HD0E ly3 S3 W3 regs3 mem3 md3 sh np ps cnt es Hlp Hle).
  split; [exact (w6m_pod_base_mv cx sh np ps cnt es rest [] [] [] _ _ _ _ _ _ _ _ _ _ _ _ HB0 HCORE3 HSUF)|].
  split.
  { unfold rsb_at_cx. apply (w6m_at_D0E cx sh np ps cnt es rest).
    - apply (w6m_atl_tr (fun _ => False) [] (w_H W1) mem1 _ _ regs1 _ _ _ Hr3 (fun a _ _ => Hm3 a)); [|exact HAT1].
      w6m_sides_all HG.
    - rewrite (w6m_kept_bv regs1 regs3 [] (26%bv : bv 5) Hr3 ltac:(vm_compute; reflexivity)). exact B26.
    - rewrite (w6m_kept_bv regs1 regs3 [] (25%bv : bv 5) Hr3 ltac:(vm_compute; reflexivity)). exact B25. }
  split; [exact (rtmb_fsh_kept rsegs _ _ _ _ _ _ HFSH1 (fun ii _ => Hm3 _))|].
  split; [exact (rtmb_bytes_kept rsegs _ _ _ _ _ _ HPP1 (fun x _ => Hm3 x))|].
  exact (rtmb_bytes_kept rsegs _ _ _ _ _ _ HE1 (fun x _ => Hm3 x)).
- (* the kind byte b: the entry of kind % 10 *)
  subst r.
  destruct HPOST as (ly3 & S3 & regs3 & mem3 & md3 & -> & HJ3 & Hr3 & Hf3 & Hp3 & Hio3 & Hmo3 & Hm3 & HR3).
  assert (HCORE3 : rsb_core rsegs B MT cx (rsb_E1 rsegs cx) ly3 S3 W3 regs3 mem3 md3).
  { apply (w6m_core_step cx _ ly1 S1 W1 regs1 mem1 md1 ly3 S3 W3 regs3 mem3 md3 (fun _ => False) HCORE1 HJ3).
    - intros q Hq. apply (w6m_reg_kept regs1 regs3 w6b_kind_clob q Hr3).
      destruct Hq as [->|[->| ->]]; vm_compute; reflexivity.
    - exact Hf3.
    - exact Hp3.
    - exact Hio3.
    - exact Hmo3.
    - intros a _ _. exact (Hm3 a).
    - intros a []. }
  rewrite (w6m_case_pc_D (bv_unsigned b)).
  apply (HD (bv_unsigned b) ly3 S3 W3 regs3 mem3 md3 sh np ps cnt es (b :: r') r' Hlp Hle).
  pose proof (w6m_suffix_tl rest b r' HSUF) as HSUF'.
  split; [exact (w6m_pod_base_mv cx sh np ps cnt es rest (b :: r') (b :: r') r' _ _ _ _ _ _ _ _ _ _ _ _
    HB0 HCORE3 HSUF')|].
  split.
  { unfold rsb_at_cx. apply (w6m_at_D cx sh np ps cnt es rest b r').
    - apply (w6m_atl_tr (fun _ => False) w6b_kind_clob (w_H W1) mem1 _ _ regs1 _ _ _ Hr3
        (fun a _ _ => Hm3 a)); [|exact HAT1].
      w6m_sides_all HG.
    - rewrite (w6m_kept_bv regs1 regs3 w6b_kind_clob (26%bv : bv 5) Hr3 ltac:(vm_compute; reflexivity)).
      exact B26.
    - exact HR3. }
  split; [exact (rtmb_fsh_kept rsegs _ _ _ _ _ _ HFSH1 (fun ii _ => Hm3 _))|].
  split; [exact (rtmb_bytes_kept rsegs _ _ _ _ _ _ HPP1 (fun x _ => Hm3 x))|].
  split; [exact (rtmb_bytes_kept rsegs _ _ _ _ _ _ HE1 (fun x _ => Hm3 x))|].
  split; [exact HSUF|].
  split; [reflexivity|].
  split; [exact (rtmb_byte_range b)|].
  discriminate.
Qed.

(* ---------------------------------------- W6a, the cases 2 and 3 ---------------------------------------- *)
(* the tail block from one of its four entries and the cut J it ends at *)
Lemma w6m_tail_J : forall (c3 a : bool) cx POST rest i k sh np ps cnt es rr rD lyD SD WD regsD memD mdD
  lyT ST WT regsT memT mdT rJ vm v,
rsb_pre rsegs B cx -> rsb_from_J rsegs B MT cx POST rest i k -> (length ps = i)%nat -> (length es = k)%nat ->
rsb_pod_base rsegs B MT cx sh np ps cnt es rest rr rD lyD SD WD regsD memD mdD ->
rsb_core rsegs B MT cx (rsb_E1 rsegs cx) lyT ST WT regsT memT mdT ->
rsb_at rsegs (w_H WT) memT regsT (x_e rsegs cx) (rsb_L_Dc0 rsegs cx sh np ps cnt es) ->
getr regsT 22 = w64 (q_F (x_e rsegs cx) + 0x210) ->
getr regsT 11 = w64 v -> getr regsT 12 = w64 (Z.of_nat (length rJ)) ->
getr regsT 18 = w64 (rsb_cur rsegs cx rest rJ) ->
(if a then True else getr regsT 14 = w64 4) ->
v mod 2 ^ 32 = vm mod 2 ^ 32 ->
(Ent (if c3 then POD_FLOAT else POD_INT) 4 (le32 vm), rJ) = ent_build rr ->
rsb_suffix rest rJ ->
rtmb_bytes rsegs (w_H WT) memT (q_F (x_e rsegs cx) + 0x210) (zeros 104) ->
rsb_fsh_at rsegs cx WT memT rsb_PJ ->
rsb_pp_at rsegs cx WT memT (pc_image (PbCut sh ps (Some es))) ->
SRr rsegs WT (cfg_at rsegs (w6b_tail_pc c3 a) regsT memT mdT) POST.
Proof using MTL HTAIL.
intros c3 a cx POST rest i k sh np ps cnt es rr rD lyD SD WD regsD memD mdD lyT ST WT regsT memT mdT rJ vm v
  HP HJ Hlp Hle HB HCT HAT T22 T11 T12 T18 T14 Hv Hed HsJ HZ HFSH HPP.
pose proof HB as HB0.
destruct HB as (_ & _ & _ & _ & Hwf & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hesw & Hesl & _).
destruct (w6m_geo_of cx _ _ _ _ _ _ _ HP HCT) as (HG & HFa & HspZ).
pose proof (w6m_ctx_of cx _ _ _ _ _ _ HP HCT) as HCTX.
pose proof (w6m_pp_len sh ps es Hwf Hesw Hesl) as Hppl.
assert (T9 : getr regsT 9 = w64 (q_R (x_e rsegs cx)))
  by (apply (w6m_at_reg _ _ _ _ _ 9 _ _ HAT); [w6m_unf; w6m_mem | reflexivity]).
assert (T158 : val_mem rsegs (mrestrict (w_H WT) memT) (q_R (x_e rsegs cx) + 0x158) 8 (q_pp (x_e rsegs cx) + 0x4000))
  by (exact (w6m_at_cell8 _ _ _ _ _ XR 0x158 _ HAT ltac:(w6m_unf; w6m_mem))).
pose proof (HTAIL c3 a _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ regsT _ _ _ (Z.of_nat (length rJ)) v (rsb_cur rsegs cx rest rJ)
  (q_pp (x_e rsegs cx) + 0x4000) HCTX T9 T22 T11 T12 T18 T14 T158 (w6m_ppl_range _ _ _ HG)) as HTT.
eapply SRr_bind; [exact HTT|]. clear HTT.
intros WJ cJ HwJ (lyJ & SJ & regsJ & memJ & mdJ & -> & HJJ & HrJ & HfJ & HpJ & HioJ & HmoJ & HmJ &
  (J6 & J26 & J18 & Vt & Vs & Vv)).
assert (HCJ : rsb_core rsegs B MT cx (rsb_E1 rsegs cx) lyJ SJ WJ regsJ memJ mdJ).
{ apply (w6m_core_step cx _ lyT ST WT regsT memT mdT lyJ SJ WJ regsJ memJ mdJ
    (w6b_tail_wr (q_F (x_e rsegs cx))) HCT HJJ).
  - intros q Hq. apply (w6m_reg_kept regsT regsJ w6b_tail_clob q HrJ).
    destruct Hq as [->|[->| ->]]; vm_compute; reflexivity.
  - exact HfJ.
  - exact HpJ.
  - exact HioJ.
  - exact HmoJ.
  - exact HmJ.
  - intros x Hx. right. left. exact (w6m_tw_E1 (x_e rsegs cx) x Hx). }
unfold rsb_from_J in HJ.
apply (HJ lyJ SJ WJ regsJ memJ mdJ sh np ps cnt es rr rJ (Ent (if c3 then POD_FLOAT else POD_INT) 4 (le32 vm))
  Hlp Hle).
split; [exact (w6m_pod_base_mv cx sh np ps cnt es rest rr rD rJ _ _ _ _ _ _ _ _ _ _ _ _ HB0 HCJ HsJ)|].
split.
{ assert (HATJ : rsb_at rsegs (w_H WJ) memJ regsJ (x_e rsegs cx) (rsb_L_Dc0 rsegs cx sh np ps cnt es)).
  { apply (w6m_atl_tr (w6b_tail_wr (q_F (x_e rsegs cx))) w6b_tail_clob (w_H WT) memT _ _ regsT _ _ _
      HrJ HmJ); [|exact HAT].
    w6m_sides_tail HG. }
  unfold rsb_at_cx. pose proof HATJ as HATJ'. unfold rsb_at in HATJ' |- *.
  apply Forall_app. split; [exact HATJ'|].
  apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]]];
  cbn [fst snd rt_at rt_xv].
  - rewrite (w6m_regZ regsJ (18%bv : bv 5) 18 eq_refl). exact J18.
  - rewrite (w6m_regZ regsJ (22%bv : bv 5) 22 eq_refl).
    rewrite (w6m_kept_bv regsT regsJ w6b_tail_clob (22%bv : bv 5) HrJ ltac:(vm_compute; reflexivity)). exact T22.
  - rewrite (w6m_regZ regsJ (26%bv : bv 5) 26 eq_refl). exact J26.
  - rewrite (w6m_regZ regsJ (6%bv : bv 5) 6 eq_refl). exact J6. }
split.
{ unfold rsb_fsh_at in *. apply (rtmb_fsh_kept rsegs (w_H WT) memT (w_H WJ) memJ _ _ HFSH).
  intros ii Hii. change (Z.of_nat (length rsb_PJ)) with 88 in Hii.
  destruct (w6m_tw_fsh _ _ _ ii HG Hii) as [Hb Hw]. exact (HmJ _ Hb Hw). }
split.
{ unfold rsb_pp_at in *. apply (rtmb_bytes_kept rsegs (w_H WT) memT (w_H WJ) memJ _ _ HPP).
  intros x Hx. rewrite Hppl in Hx.
  destruct (w6m_tw_pp _ _ _ (x - q_pp (x_e rsegs cx)) HG ltac:(lia)) as [Hb Hw].
  replace x with (q_pp (x_e rsegs cx) + (x - q_pp (x_e rsegs cx))) by lia. exact (HmJ _ Hb Hw). }
split.
{ (* e62: the type, the size 4, the value's four bytes, 92 zeros *)
  assert (HEJ : rtmb_bytes rsegs (w_H WJ) memJ (q_F (x_e rsegs cx) + 0x210)
    (ent_mem (Ent (if c3 then POD_FLOAT else POD_INT) 4 (le32 vm)))).
  { unfold ent_mem. cbn [e_type e_size e_body].
    replace (96 - length (le32 vm))%nat with 92%nat by (unfold le32; rewrite length_Z_to_le_bytes; reflexivity).
    apply rtmb_bytes_app. split.
    { unfold le32. apply rtmb_bytes_of_val. exact Vt. }
    replace (Z.of_nat (length (le32 (if c3 then POD_FLOAT else POD_INT)))) with 4
      by (unfold le32; rewrite length_Z_to_le_bytes; reflexivity).
    apply rtmb_bytes_app. split.
    { replace (q_F (x_e rsegs cx) + 0x210 + 4) with (q_F (x_e rsegs cx) + 0x214) by lia.
      unfold le32. apply rtmb_bytes_of_val. exact Vs. }
    replace (Z.of_nat (length (le32 4))) with 4 by (unfold le32; rewrite length_Z_to_le_bytes; reflexivity).
    apply rtmb_bytes_app. split.
    { replace (q_F (x_e rsegs cx) + 0x210 + 4 + 4) with (q_F (x_e rsegs cx) + 0x218) by lia.
      unfold le32. apply rtmb_bytes_of_val. apply (proj1 (w6m_val_mod32 _ _ vm)). rewrite <- Hv. exact Vv. }
    replace (Z.of_nat (length (le32 vm))) with 4 by (unfold le32; rewrite length_Z_to_le_bytes; reflexivity).
    pose proof (rtmb_bytes_slice rsegs _ _ _ (zeros 104) 12 92 HZ ltac:(unfold zeros; rewrite repeat_length; lia)) as HZ1.
    change (rtmb_slice (zeros 104) 12 92) with (zeros 92) in HZ1.
    replace (q_F (x_e rsegs cx) + 0x210 + 4 + 4 + 4) with (q_F (x_e rsegs cx) + 0x210 + Z.of_nat 12) by lia.
    apply (rtmb_bytes_kept rsegs (w_H WT) memT (w_H WJ) memJ _ _ HZ1).
    intros x Hx. change (Z.of_nat (length (zeros 92))) with 92 in Hx.
    destruct (w6m_tw_e _ _ _ (x - (q_F (x_e rsegs cx) + 0x210)) HG ltac:(lia)) as [Hb Hw].
    replace x with (q_F (x_e rsegs cx) + 0x210 + (x - (q_F (x_e rsegs cx) + 0x210))) by lia. exact (HmJ _ Hb Hw). }
  exact HEJ. }
split; [exact Hed|].
pose proof (ent_build_wf rr) as X. rewrite <- Hed in X. exact X.
Qed.

(* one of the two cases, from its entry D to J *)
Lemma w6m_case_gen : forall c3 : bool,
w6b_case_head_stmt B MT c3 ->
rtsb_u32_stmt B MT (if c3 then W6B_U3 else W6B_U2) (if c3 then W6B_TA3 else W6B_TA2) ->
forall cx POST rest i k kd, kd mod 10 = (if c3 then 3 else 2) ->
rsb_start_M01 rsegs B cx rest -> rsb_from_J rsegs B MT cx POST rest i k -> rsb_from_D rsegs B MT cx POST rest i k kd.
Proof using MTL HTAIL.
intros c3 HH HU cx POST rest i k kd Hkd Hst HJ.
unfold rsb_from_D.
intros lyD SD WD regsD memD mdD sh np ps cnt es rr r Hlp Hle HD.
destruct Hst as (HP & HFSH0 & _ & _ & HIN).
destruct HD as (HB & HAT & HFSH & HPP & HE & Hsrr & Hfu & Hkd256 & Hrr).
pose proof HB as HB0.
destruct HB as (HCORE & _ & HSUF & _).
destruct (w6m_geo_of cx _ _ _ _ _ _ _ HP HCORE) as (HG & HFa & HspZ).
pose proof (w6m_ctx_of cx _ _ _ _ _ _ HP HCORE) as HCTX.
unfold rsb_at_cx in HAT. unfold rsb_fsh_at in HFSH.
destruct rr as [|b r0]; [exfalso; exact (Hrr eq_refl)|].
cbn [Cursor.fuzz_u8] in Hfu. injection Hfu as Ekd Er. subst kd. subst r0.
rewrite (w6m_pc_23 c3 (bv_unsigned b) Hkd).
(* the registers and cells at D *)
assert (D9 : getr regsD 9 = w64 (q_R (x_e rsegs cx)))
  by (apply (w6m_at_reg _ _ _ _ _ 9 _ _ HAT); [w6m_unf; w6m_mem | reflexivity]).
assert (D20 : getr regsD 20 = w64 SHADOW_OFF)
  by (apply (w6m_at_reg _ _ _ _ _ 20 _ _ HAT); [w6m_unf; w6m_mem | reflexivity]).
assert (D18 : getr regsD 18 = w64 (rsb_cur rsegs cx rest r))
  by (apply (w6m_at_reg _ _ _ _ _ 18 _ _ HAT); [w6m_unf; w6m_mem | reflexivity]).
assert (D22 : getr regsD 22 = w64 (Z.of_nat (length r)))
  by (apply (w6m_at_reg _ _ _ _ _ 22 _ _ HAT); [w6m_unf; w6m_mem | reflexivity]).
assert (D26 : getr regsD 26 = w64 (rsb_cur rsegs cx rest r - 1))
  by (apply (w6m_at_reg _ _ _ _ _ 26 _ _ HAT); [w6m_unf; w6m_mem | reflexivity]).
assert (D6 : getr regsD 6 = w64 (Z.of_nat (length r) + 1))
  by (apply (w6m_at_reg _ _ _ _ _ 6 _ _ HAT); [w6m_unf; w6m_mem | reflexivity]).
assert (D16 : getr regsD 16 = w64 1)
  by (apply (w6m_at_reg _ _ _ _ _ 16 _ _ HAT); [w6m_unf; w6m_mem | reflexivity]).
assert (D150 : val_mem rsegs (mrestrict (w_H WD) memD) (q_R (x_e rsegs cx) + 0x150) 8 (q_F (x_e rsegs cx) + 0x210))
  by (exact (w6m_at_cell8 _ _ _ _ _ XR 0x150 _ HAT ltac:(w6m_unf; w6m_mem))).
(* the list the case's blocks carry *)
assert (HATc : rsb_at rsegs (w_H WD) memD regsD (x_e rsegs cx) (rsb_L_Dc0 rsegs cx sh np ps cnt es)).
{ pose proof HAT as HAT'. unfold rsb_at in HAT' |- *. apply (w6m_fsub _ _ _ HAT'). w6m_subs. }
(* the input at the cursor, at D *)
destruct (w6k_in_now rsegs B MT cx rest rsb_PJ lyD SD WD regsD memD mdD HP HFSH0 HIN HCORE HFSH eq_refl)
  as (HgD & HraD & _).
pose proof (w6m_in_kept cx rest r WD memD WD memD HP HIN HSUF HG HFSH0 HgD HraD (fun a _ _ => eq_refl)) as HIND.
assert (HHIN : w6b_head_in WD memD regsD (q_R (x_e rsegs cx)) (q_F (x_e rsegs cx)) (rsb_cur rsegs cx rest r) r).
{ unfold w6b_head_in.
  split; [exact D9|]. split; [exact D20|]. split; [exact D18|]. split; [exact D22|].
  split; [exact D26|]. split; [exact D6|]. split; [exact D16|]. split; [exact D150|].
  split; [exact (w6m_e62_range _ _ _ HG)|].
  split; [exact (w6m_cur_pos cx rest b r HIN Hsrr) | exact HIND]. }
(* the table's shadow, at D *)
assert (HRT : range_addressable (aview rsegs (w_H WD) memD) SHADOW_OFF (if c3 then W6B_FLOATS else W6B_INTS)
  (if c3 then 84 else 56)).
{ assert (Hg0 : range_addressable (aview rsegs (w_H (x_W rsegs cx)) (x_memc rsegs cx)) SHADOW_OFF
    (if c3 then W6B_FLOATS else W6B_INTS) (if c3 then 84 else 56)).
  { pose proof HP as HP'.
    destruct HP' as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hgl & _).
    change (hi_globs rate_himg_B) with rate_B_globs in Hgl. rewrite Forall_forall in Hgl.
    destruct c3.
    - exact (Hgl (0x21140, 84) ltac:(unfold rate_B_globs; w6m_mem)).
    - exact (Hgl (0x210e0, 56) ltac:(unfold rate_B_globs; w6m_mem)). }
  intros x Hx.
  rewrite (w6k_core_kept rsegs B MT cx _ _ _ _ _ _ HP HCORE (shadow_of_addr SHADOW_OFF x)); [exact (Hg0 x Hx)|].
  apply (w6k_wr_shadow rsegs B cx x HP HFSH0).
  - destruct c3; cbv beta iota in Hx; unfold kHighMemEnd, W6B_FLOATS, W6B_INTS in *; lia.
  - intros y Hy. apply Hg0. lia. }
(* ---------------- the case's head block ---------------- *)
pose proof (HH _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ regsD _ _ _ (rsb_cur rsegs cx rest r) r HCTX HHIN HRT) as HH1.
eapply SRr_bind; [exact HH1|]. clear HH1.
intros WH cH HwH HPOST. cbv beta zeta in HPOST.
revert HPOST. destruct (Z.odd (fst (Cursor.fuzz_u8 r))) eqn:Eodd; intros HPOST.
- (* m odd: the fuzz_u32 block, then the tail *)
  destruct r as [|b' r1]; [cbn in Eodd; discriminate Eodd|].
  cbn [Cursor.fuzz_u8 fst snd] in HPOST, Eodd.
  destruct HPOST as (lyH & SH & regsH & memH & mdH & -> & HJH & HrH & HfH & HpH & HioH & HmoH & HmH &
    (H12 & H18 & H22)).
  destruct (w6m_blk_step cx w6b_head_clob (rsb_L_Dc0 rsegs cx sh np ps cnt es)
    lyD SD WD regsD memD mdD lyH SH WH regsH memH mdH HCORE HJH HrH
    HfH HpH HioH HmoH HmH eq_refl eq_refl eq_refl ltac:(w6m_sides_all HG) HATc) as [HCH HATH].
  assert (H26 : getr regsH 26 = w64 (rsb_cur rsegs cx rest (b' :: r1) + 1 - 2)).
  { replace (rsb_cur rsegs cx rest (b' :: r1) + 1 - 2) with (rsb_cur rsegs cx rest (b' :: r1) - 1) by lia.
    rewrite (w6m_kept_bv regsD regsH w6b_head_clob (26%bv : bv 5) HrH ltac:(vm_compute; reflexivity)).
    exact D26. }
  assert (H6 : getr regsH 6 = w64 (Z.of_nat (length r1) + 2)).
  { replace (Z.of_nat (length r1) + 2) with (Z.of_nat (length (b' :: r1)) + 1) by (cbn [length]; lia).
    rewrite (w6m_kept_bv regsD regsH w6b_head_clob (6%bv : bv 5) HrH ltac:(vm_compute; reflexivity)).
    exact D6. }
  assert (H20 : getr regsH 20 = w64 SHADOW_OFF).
  { rewrite (w6m_kept_bv regsD regsH w6b_head_clob (20%bv : bv 5) HrH ltac:(vm_compute; reflexivity)).
    exact D20. }
  assert (H16 : getr regsH 16 = w64 1).
  { rewrite (w6m_kept_bv regsD regsH w6b_head_clob (16%bv : bv 5) HrH ltac:(vm_compute; reflexivity)).
    exact D16. }
  destruct HIND as (HgI & HraI & HcI & HtI & HamI & HexI).
  cbn [length] in HraI, HtI, HamI, HexI. rewrite Nat2Z.inj_succ in HraI, HtI, HamI, HexI.
  assert (HgH : garr8 rsegs (mrestrict (w_H WH) memH) (rsb_cur rsegs cx rest (b' :: r1) + 1) (u8s r1)).
  { pose proof (proj1 (rtmb_bytes_app rsegs (w_H WD) memD (rsb_cur rsegs cx rest (b' :: r1)) [b'] r1) HgI) as [_ X].
    change (Z.of_nat (length [b'])) with 1 in X.
    exact (rtmb_bytes_kept rsegs _ _ _ _ _ _ X (fun x _ => HmH x)). }
  assert (HraH : range_addressable (aview rsegs (w_H WH) memH) SHADOW_OFF (rsb_cur rsegs cx rest (b' :: r1) + 1)
    (Z.of_nat (length r1))).
  { intros x Hx. rewrite HmH. apply HraI. lia. }
  pose proof (HU _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ regsH (rsb_cur rsegs cx rest (b' :: r1) + 1)
    (Z.of_nat (length r1)) (Z.of_nat (length r1) + 2) r1 eq_refl eq_refl HJH H12 H26 H6 H20 H18 H16) as HU1.
  pose proof (HU1 ltac:(pose proof (w6m_cur_pos cx rest b (b' :: r1) HIN Hsrr); lia)
    ltac:(unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in *; lia) HgH HraH) as HU2'. clear HU1.
  eapply SRr_bind; [exact HU2'|]. clear HU2'.
  intros WU cU HwU (lyU & SU & regsU & memU & mdU & -> & HJU & HrU & HfU & HpU & HioU & HmoU & HmU &
    (U11 & U12 & U18 & U20)).
  destruct (w6m_blk_step cx [11; 12; 13; 14; 15; 18]%bv (rsb_L_Dc0 rsegs cx sh np ps cnt es)
    lyH SH WH regsH memH mdH lyU SU WU regsU memU mdU HCH HJU HrU HfU HpU HioU HmoU HmU eq_refl eq_refl eq_refl
    ltac:(w6m_sides_all HG) HATH) as [HCU HATU].
  apply (w6m_tail_J c3 true cx POST rest i k sh np ps cnt es (b :: b' :: r1) (b' :: r1) lyD SD WD regsD memD mdD
    lyU SU WU regsU memU mdU (snd (Cursor.fuzz_u32 r1)) (fst (Cursor.fuzz_u32 r1)) (fst (Cursor.fuzz_u32 r1))
    HP HJ Hlp Hle HB0 HCU HATU).
  + rewrite (w6m_kept_bv regsH regsU [11; 12; 13; 14; 15; 18]%bv (22%bv : bv 5) HrU
      ltac:(vm_compute; reflexivity)).
    exact H22.
  + exact U11.
  + rewrite fuzz_u32_rest_len. exact U12.
  + rewrite Cursor.fuzz_u32_rest, w6m_cur_skip.
    replace (rsb_cur rsegs cx rest r1) with (rsb_cur rsegs cx rest (b' :: r1) + 1)
      by (unfold rsb_cur; cbn [length]; lia).
    exact U18.
  + exact I.
  + reflexivity.
  + rewrite (w6m_ent_build c3 b (b' :: r1) Hkd). cbn [Cursor.fuzz_u8 fst snd]. rewrite Eodd. reflexivity.
  + rewrite Cursor.fuzz_u32_rest. apply w6m_suffix_skip. exact (w6m_suffix_tl rest b' r1 HSUF).
  + apply (rtmb_bytes_kept rsegs _ _ _ _ _ _ HE). intros x _. rewrite HmU. exact (HmH x).
  + unfold rsb_fsh_at. apply (rtmb_fsh_kept rsegs _ _ _ _ _ _ HFSH). intros ii _. rewrite HmU. exact (HmH _).
  + unfold rsb_pp_at in *. apply (rtmb_bytes_kept rsegs _ _ _ _ _ _ HPP). intros x _. rewrite HmU. exact (HmH x).
- (* m even (or no byte): the tail *)
  destruct HPOST as (lyH & SH & regsH & memH & mdH & -> & HJH & HrH & HfH & HpH & HioH & HmoH & HmH &
    ((v & H11 & Hv) & H14 & H12 & H18 & H22)).
  destruct (w6m_blk_step cx w6b_head_clob (rsb_L_Dc0 rsegs cx sh np ps cnt es) lyD SD WD regsD memD mdD
    lyH SH WH regsH memH mdH HCORE HJH HrH HfH HpH HioH HmoH HmH eq_refl eq_refl eq_refl ltac:(w6m_sides_all HG)
    HATc) as [HCH HATH].
  apply (w6m_tail_J c3 false cx POST rest i k sh np ps cnt es (b :: r) r lyD SD WD regsD memD mdD
    lyH SH WH regsH memH mdH (snd (Cursor.fuzz_u8 r))
    (if c3 then w6b_float_even (fst (Cursor.fuzz_u8 r)) else w6b_int_even (fst (Cursor.fuzz_u8 r))) v
    HP HJ Hlp Hle HB0 HCH HATH).
  + exact H22.
  + exact H11.
  + exact H12.
  + rewrite H18. f_equal. rewrite Cursor.fuzz_u8_spec. cbn [snd]. rewrite w6m_cur_skip, length_skipn. lia.
  + exact H14.
  + exact Hv.
  + rewrite (w6m_ent_build c3 b r Hkd), Eodd. reflexivity.
  + rewrite Cursor.fuzz_u8_spec. cbn [snd]. apply w6m_suffix_skip. exact HSUF.
  + exact (rtmb_bytes_kept rsegs _ _ _ _ _ _ HE (fun x _ => HmH x)).
  + exact (rtmb_fsh_kept rsegs _ _ _ _ _ _ HFSH (fun ii _ => HmH _)).
  + exact (rtmb_bytes_kept rsegs _ _ _ _ _ _ HPP (fun x _ => HmH x)).
Qed.

Lemma w6b_cases_of : rsb_piece_W6a_cases_stmt rsegs B MT.
Proof using MTL HC2 HC3 HTAIL.
intros cx POST rest i k kd Hst Hin HJ.
cbn [In] in Hin. destruct Hin as [H2|[H3|[]]].
- exact (w6m_case_gen false HC2 (rtsb_u32_block2 B MT MTL (AR_laws_ok rsegs B))
    cx POST rest i k kd (eq_sym H2) Hst HJ).
- exact (w6m_case_gen true HC3 (rtsb_u32_block3 B MT MTL (AR_laws_ok rsegs B))
    cx POST rest i k kd (eq_sym H3) Hst HJ).
Qed.

End blocks.

(* __asan_memset at 0x51d54 (the head block's call): the kernel's contract of the intrinsic. Discharged by the
   lane's runtime layer. The block lemmas take MTL and the kernel's AR_laws_ok, so no other hypothesis is left. *)
Hypothesis AMEMSET : aintrin_realizes rsegs B OSet W6B_MEMSET.

Theorem w6b_disp : rsb_piece_W6a_disp_stmt rsegs B MT.
Proof using MTL AMEMSET.
exact (w6b_disp_of (w6b_head B MT MTL (AR_laws_ok rsegs B) AMEMSET) (w6b_kind B MT MTL (AR_laws_ok rsegs B))).
Qed.

Theorem w6b_cases : rsb_piece_W6a_cases_stmt rsegs B MT.
Proof using MTL.
exact (w6b_cases_of (w6b_c2h B MT MTL (AR_laws_ok rsegs B)) (w6b_c3h B MT MTL (AR_laws_ok rsegs B))
  (w6b_tail_all B MT MTL (AR_laws_ok rsegs B))).
Qed.

End d.
End b.

Check w6b_disp.
Check w6b_cases.
Print Assumptions w6b_disp.
Print Assumptions w6b_cases.
