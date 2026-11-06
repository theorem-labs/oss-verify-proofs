(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: restates text of proofs/reac-pw/fuzz_rate/lib/Reusable/YCbq.v at 7379c28ff70f
   [Apache-2.0 OR MIT] (SRr_run_AJ / SRr_run_to_AJ and the tactics aj_run / aj_run_to, here over the shadow-aware runs
   of YP0i; aj_stack_malloc_at, here with the conjunct S2 = set_fs f Sc added to its post), of
   proofs/reac-pw/fuzz_rate/lib/A/RtPgSteps.v at 816e60e510b7 (rts_fbounds and the four frame write rights, here for
   a general side-stack class) and of proofs/reac-pw/fuzz_role/lib/A/RPgX01.v at 9bffaa83ff88 [Apache-2.0] (rx_jF,
   rx_ffacts, here for a general class), for reac-pw/fuzz_rate's image A. The [Apache-2.0 OR MIT] text is used under
   Apache-2.0. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_rate/lib/A/RtPgCcsvKit.v at b929052adf57; the same kit for
   image B (fuzz_rate.asan-ubsan): the image is images.AsanUbsan, the step kit lib/AU/RtPgStepsB.v (rts_segs_low,
   rts_wx, rts_fdiv become rtsb_segs_low, rtsb_wx, rtsb_fdiv); part (7), closed_list after the class-2 frame from
   RtPgCSpec.rt_img_facts at image B's record (the image-B form of lib/A/RtPgSiteA.v rate_A_i32_glob /
   rate_A_i32_unowned / rate_A_i32tab_at), is new. *)
(* reac-pw/fuzz_rate image B (fuzz_rate.asan-ubsan, pinned sha256
   c30584a7214902c43e35abebe35194418b7fdefacb6e7ed16fe0492228ec1d14; every address is measured on its unstripped twin
   sha256 a1e5fa55ae27e657ea2719297ec4c037110f10fa9047c3ea7bb6ea7fcb358cb1): the engine kit of the walk of check_csv
   (0x837c0, a class-2 side-stack frame of 256 bytes). Proves no function (kind: segment lemma). Every lemma is
   stated over image B's segments (images.AsanUbsan loaded_segments) and the kit's engine (lib/Reusable).

   (1) rck_run_sh_AJ / rck_run_to_sh_AJ and the tactics rck_aj_run_sh / rck_aj_run_to_sh: a run of the
       shadow-aware plain engine (YP0i sym_runN_sh / sym_run_toN_sh, whose loads and stores resolve the address
       (x >> 3) + s9 of an instrumented check through a shadow declaration) under the caller's journal.
   (2) rck_shadow_decl / rck_shadow_decl_sv: the shadow declaration of one base object (an atom fact for its base
       atom p, 32-aligned, and the alias pair ((p >> 3) + K, s) that YP0i shadow_norm reads), in one step.
   (3) rck_fbytes, rck_fbounds and rck_awr_fobj / rck_awr_fsh / rck_awr_ok_fobj / rck_awr_ok_fsh: the frame
       arithmetic and the frame write rights of a side-stack frame of any class.
   (4) rck_jF / rck_ffacts: the facts of a frame of any class and of its flag byte at a state of the journal.
   (5) rck_aowned_of, rck_free_eqs, rck_aowned_free: the owned-set clause of RtPgCSpec.rt_cpost_o from the layout,
       the chunks and the frames, and for the walk's state stack_free_state cid pos (set_fs f Sc).
   (6) rck_stack_malloc_at: YCbq aj_stack_malloc_at with S2 = set_fs f Sc in its post, the fact (5) needs at the
       return (aj_stack_malloc_at's post keeps only ablocks, frames, st_nev and blocks_bytes of S2).
   (7) rckb_tab_in, rckb_i32_glob, rckb_i32_unowned, rckb_i32tab_at: closed_list (0x21520, a table of image B's record
       RtPgImgB.rate_himg_B) is a registered global with room for its 12 bytes, its bytes are no owned static under
       RtPgCSpec.rt_img_facts at image B's record and range [IMG_LO, IMG_TOP), and its rt_i32tab holds again at an AR
       state whose bytes there are the call's (RtPgBase.rt_i32tab_at). *)
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YI04.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YI16 YM05.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YImgTop.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Pod Require RateCfg.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.A Require Import RtPgBase RtPgCSpec.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.AU Require Import RtPgImgB RtPgStepsB.
Require OSSVerify.reac_pw.fuzz_rate.images.AsanUbsan.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

(* image B's loaded segments, as lib/AU/RtPgStepsB.v names them *)
Local Abbreviation rsegs := OSSVerify.reac_pw.fuzz_rate.images.AsanUbsan.M.loaded_segments.

Section k. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.

(* ================================ (1) the shadow-aware runs under the journal ================================ *)
Section runs.
Variable B : asyms.
Hypothesis LAWS : AR_laws rsegs B.
Variable tbl : ctable.
Hypothesis tbl_ok : table_ok rsegs tbl.
(* YCbq SRr_run_AJ with the run of the shadow-aware engine *)
Lemma rck_run_sh_AJ : forall W n E ss ss' st ms STK sp0 FP ly S W0 mem md own lyc Sc mdc k Q,
st_ok rsegs E ss (restrict (w_H W) ms) ->
sym_runN_sh rsegs tbl n ss = (ss', st) ->
match st with RS_ecall => False | _ => True end ->
ajournal rsegs B STK sp0 FP ly S W0 mem md own lyc Sc W (ms_mem ms) mdc k ->
awr_ok E (ss_mem ss) STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own ->
run_post_AJ rsegs B W E ss ss' ms STK sp0 FP ly S W0 mem md own lyc Sc mdc k Q ->
SRr rsegs W (mkCfg ms mdc) Q.
Proof.
intros W n E ss ss' st ms STK sp0 FP ly S W0 mem md own lyc Sc mdc k Q HS Hrun Hst HJ Hwr Hk.
destruct (msteps_run_sh rsegs tbl tbl_ok n E ss ss' st _ HS Hrun) as (msr' & Hms & HS' & Hfr).
eapply (SRr_chain_AJ rsegs B LAWS rtsb_segs_low rtsb_wx);
[exact Hms | destruct st; [exact HS' | destruct Hst | exact HS'] | exact Hfr | exact HJ | exact Hwr | exact Hk].
Qed.
(* YCbq SRr_run_to_AJ with the run of the shadow-aware engine *)
Lemma rck_run_to_sh_AJ : forall W n stop E ss ss' st ms STK sp0 FP ly S W0 mem md own lyc Sc mdc k Q,
st_ok rsegs E ss (restrict (w_H W) ms) ->
sym_run_toN_sh rsegs tbl n stop ss = (ss', st) ->
match st with RS_ecall => False | _ => True end ->
ajournal rsegs B STK sp0 FP ly S W0 mem md own lyc Sc W (ms_mem ms) mdc k ->
awr_ok E (ss_mem ss) STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own ->
run_post_AJ rsegs B W E ss ss' ms STK sp0 FP ly S W0 mem md own lyc Sc mdc k Q ->
SRr rsegs W (mkCfg ms mdc) Q.
Proof.
intros W n stop E ss ss' st ms STK sp0 FP ly S W0 mem md own lyc Sc mdc k Q HS Hrun Hst HJ Hwr Hk.
destruct (msteps_run_to_sh rsegs tbl tbl_ok n stop E ss ss' st _ HS Hrun) as (msr' & Hms & HS' & Hfr).
eapply (SRr_chain_AJ rsegs B LAWS rtsb_segs_low rtsb_wx);
[exact Hms | destruct st; [exact HS' | destruct Hst | exact HS'] | exact Hfr | exact HJ | exact Hwr | exact Hk].
Qed.
End runs.

(* ================================ (2) the shadow declaration of a base object ================================ *)
(* YP0i shadow_decl_ok with the shadow offset held by any sv bx (an atom, or the literal a load left) *)
Lemma rck_shadow_decl_sv_ok : forall E (p s : nat) (bx : sv) (F : Z),
ew E p = Z_to_bv 64 F -> 0 <= F < 2 ^ 64 ->
sv_denot E bx = Z_to_bv 64 SHADOW_OFF ->
ew E s = Z_to_bv 64 (SHADOW_OFF + F / 8) ->
sv_denot E (SAlu ALU_ADD (SAlu ALU_SRL (SOff p 0) (SLit 3)) bx) = sv_denot E (SOff s 0).
Proof.
intros E p s bx F Hp HF Hbx Hs. apply U_inj.
assert (H8 : 0 <= F / 8 < 2 ^ 61) by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
assert (Ub : U E bx = SHADOW_OFF) by (unfold U; rewrite Hbx; apply unsigned_lit_small; unfold SHADOW_OFF; lia).
rewrite U_SAlu, Ub. cbn [zalu_raw]. rewrite U_srl3, !U_SOff, Hp, Hs, !Z.add_0_r.
rewrite (unsigned_lit_small F) by lia. rewrite (zcanon_id F) by (unfold M64; lia).
rewrite (unsigned_lit_small (SHADOW_OFF + F / 8)) by (unfold SHADOW_OFF; lia).
f_equal. lia.
Qed.
(* the state with the atom fact of p (bounds lo .. hi, 32-aligned: af_al2 = 5) and the alias pair
   ((p >> 3) + bx, s) added: after it, YP0i shadow_norm rewrites the shadow address (SOff p c >> 3) + bx of every
   offset c of p (with lo + c >= 0 and hi + c < 2 ^ 64) to SOff s (c / 8) *)
Lemma rck_shadow_decl_sv : forall E ss ms (p s : nat) (bx : sv) (F lo hi : Z),
st_ok rsegs E ss ms ->
ew E p = Z_to_bv 64 F -> 0 <= F < 2 ^ 64 -> F mod 32 = 0 -> lo <= F <= hi ->
sv_denot E bx = Z_to_bv 64 SHADOW_OFF ->
ew E s = Z_to_bv 64 (SHADOW_OFF + F / 8) ->
st_ok rsegs E (add_alias (add_atom ss p (mkAF lo hi 5))
  (SAlu ALU_ADD (SAlu ALU_SRL (SOff p 0) (SLit 3)) bx) (SOff s 0)) ms.
Proof.
intros E ss ms p s bx F lo hi HS Hp HF H32 Hlh Hbx Hs.
apply st_ok_add_alias; [|exact (rck_shadow_decl_sv_ok E p s bx F Hp HF Hbx Hs)].
apply st_ok_add_fact; [exact HS|].
unfold afact_ok; cbn [af_lo af_hi af_al2]. rewrite Hp, unsigned_lit_small by lia.
change (2 ^ 5) with 32. split; [exact Hlh|]. split; [exact H32 | lia].
Qed.
(* the same with the shadow offset in an atom b (YP0i shadow_decl_ok's shape) *)
Lemma rck_shadow_decl : forall E ss ms (p b s : nat) (F lo hi : Z),
st_ok rsegs E ss ms ->
ew E p = Z_to_bv 64 F -> 0 <= F < 2 ^ 64 -> F mod 32 = 0 -> lo <= F <= hi ->
ew E b = Z_to_bv 64 SHADOW_OFF ->
ew E s = Z_to_bv 64 (SHADOW_OFF + F / 8) ->
st_ok rsegs E (add_alias (add_atom ss p (mkAF lo hi 5))
  (SAlu ALU_ADD (SAlu ALU_SRL (SOff p 0) (SLit 3)) (SOff b 0)) (SOff s 0)) ms.
Proof.
intros E ss ms p b s F lo hi HS Hp HF H32 Hlh Hb Hs.
apply (rck_shadow_decl_sv E ss ms p s (SOff b 0) F lo hi HS Hp HF H32 Hlh); [|exact Hs].
rewrite denot_lit_U, (U_atom E b SHADOW_OFF Hb) by (unfold SHADOW_OFF; lia). reflexivity.
Qed.

(* ================================ (3) a side-stack frame of class cid ================================ *)
(* the frame's size and its shadow's: fs_frame_bytes cid = 64 << cid, a multiple of 8 *)
Lemma rck_fbytes : forall cid, 0 <= cid -> fs_frame_bytes cid = 8 * (fs_frame_bytes cid / 8) /\ 64 <= fs_frame_bytes cid.
Proof.
intros cid Hc. unfold fs_frame_bytes. rewrite Z.shiftl_mul_pow2 by lia. pose proof (Z.pow_pos_nonneg 2 cid ltac:(lia) Hc) as Hp.
replace (64 * 2 ^ cid) with ((8 * 2 ^ cid) * 8) by ring. rewrite Z.div_mul by lia. split; lia.
Qed.
Lemma rck_fbytes2 : fs_frame_bytes 2 = 256.
Proof. reflexivity. Qed.
(* RtPgStepsB rtsb_fbounds for a frame of class cid: its bounds, its shadow below the ceiling and apart from it,
   every object range in it inside the low or high application memory *)
Lemma rck_fbounds : forall cid F, 0 <= cid -> F mod 32 = 0 -> in_app F (fs_frame_bytes cid) ->
4096 <= F /\ F + fs_frame_bytes cid <= alloc_ceiling /\ 0 <= shadow_addr F /\
shadow_addr F + fs_frame_bytes cid / 8 <= alloc_ceiling /\
(F + fs_frame_bytes cid <= shadow_addr F \/ shadow_addr F + fs_frame_bytes cid / 8 <= F) /\
(forall o n, 0 <= o -> 0 <= n -> o + n < fs_frame_bytes cid -> amem_range (F + o) n).
Proof.
intros cid F Hc Hm Ha. destruct (rck_fbytes cid Hc) as [EX HX].
destruct (rtsb_fdiv F Hm) as [E1 E2]. pose proof asan_consts as (C1 & _). rewrite E2.
remember (fs_frame_bytes cid / 8) as Y eqn:HY. remember (fs_frame_bytes cid) as X eqn:HXd. clear HY HXd.
remember (F / 32) as q eqn:Hq. clear Hq.
unfold in_app, amem_range, SHADOW_OFF, kLowShadowBeg, kLowMemEnd, kHighMemBeg, kHighMemEnd, ASAN_CEIL in *.
split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|].
intros o n Ho Hn Hon. lia.
Qed.
(* RtPgStepsB rtsb_awr_fobj / rtsb_awr_fsh / rtsb_awr_ok_fsh / rtsb_awr_ok_fobj for a frame of class cid *)
Lemma rck_awr_fobj : forall STK sp0 FP bl0 blc ly own cid pos a,
In (cid, pos) own -> frame_addr ly cid pos <= a < frame_addr ly cid pos + fs_frame_bytes cid ->
awr_byte STK sp0 FP bl0 blc ly own a.
Proof.
intros STK sp0 FP bl0 blc ly own cid pos a Hown Ha. right; right; right. exists cid, pos. split; [exact Hown|]. left.
unfold in_zr; cbn [fst snd]. lia.
Qed.
Lemma rck_awr_fsh : forall STK sp0 FP bl0 blc ly own cid pos a,
In (cid, pos) own ->
shadow_addr (frame_addr ly cid pos) <= a < shadow_addr (frame_addr ly cid pos) + fs_frame_bytes cid / 8 ->
awr_byte STK sp0 FP bl0 blc ly own a.
Proof.
intros STK sp0 FP bl0 blc ly own cid pos a Hown Ha. right; right; right. exists cid, pos. split; [exact Hown|]. right.
unfold in_zr; cbn [fst snd]. lia.
Qed.
Lemma rck_awr_ok_fsh : forall E r rs STK sp0 FP bl0 blc ly own (kreg : nat) cid pos,
YP09.r_base r = Some kreg -> bv_unsigned (ew E kreg) = shadow_addr (frame_addr ly cid pos) -> In (cid, pos) own ->
0 <= YP09.r_wlo r -> YP09.r_whi r <= fs_frame_bytes cid / 8 ->
awr_ok E rs STK sp0 FP bl0 blc ly own -> awr_ok E (r :: rs) STK sp0 FP bl0 blc ly own.
Proof.
intros E r rs STK sp0 FP bl0 blc ly own kreg cid pos Hb Hk Hown Hlo Hhi Hrs.
apply (awr_ok_cons_gen E r rs STK sp0 FP bl0 blc ly own kreg _ Hb Hk); [|exact Hrs].
intros a Ha. apply (rck_awr_fsh STK sp0 FP bl0 blc ly own cid pos a Hown). lia.
Qed.
Lemma rck_awr_ok_fobj : forall E r rs STK sp0 FP bl0 blc ly own (kreg : nat) cid pos off,
YP09.r_base r = Some kreg -> bv_unsigned (ew E kreg) = frame_addr ly cid pos + off -> In (cid, pos) own ->
0 <= off + YP09.r_wlo r -> off + YP09.r_whi r <= fs_frame_bytes cid ->
awr_ok E rs STK sp0 FP bl0 blc ly own -> awr_ok E (r :: rs) STK sp0 FP bl0 blc ly own.
Proof.
intros E r rs STK sp0 FP bl0 blc ly own kreg cid pos off Hb Hk Hown Hlo Hhi Hrs.
apply (awr_ok_cons_gen E r rs STK sp0 FP bl0 blc ly own kreg _ Hb Hk); [|exact Hrs].
intros a Ha. apply (rck_awr_fobj STK sp0 FP bl0 blc ly own cid pos a Hown). lia.
Qed.

(* ================================ (4) the frame facts at a state of the journal ================================ *)
Section ff.
Variable B : asyms.
Hypothesis LAWS : AR_laws rsegs B.
Hypothesis FFL : frame_flag_lawP rsegs B.
(* every journal keeps ly_F, so a frame's and its flag's addresses are the entry layout's (RPgX01 rx_jF) *)
Lemma rck_jF : forall STK sp0 FP ly S W mem md own ly' S' W' mem' md' k c q,
ajournal rsegs B STK sp0 FP ly S W mem md own ly' S' W' mem' md' k ->
frame_addr ly' c q = frame_addr ly c q /\ flag_addr ly' c q = flag_addr ly c q.
Proof.
intros STK sp0 FP ly S W mem md own ly' S' W' mem' md' k c q (_ & Hly & _).
destruct Hly as (_ & _ & _ & _ & _ & EF & _). unfold frame_addr, flag_addr. rewrite EF. split; reflexivity.
Qed.
(* a frame of class cid (fs_frame_bytes cid bytes, fs_frame_bytes cid / 8 shadow bytes) and its flag byte at a
   state of the journal (RPgX01 rx_ffacts for a general class, with the shadow bytes' "not owned" and the flag
   law's app_addr / ~ in_img / zone2 kept) *)
Lemma rck_ffacts : forall STK sp0 FP ly S W mem md own ly' S' W' mem' md' k cid pos,
ajournal rsegs B STK sp0 FP ly S W mem md own ly' S' W' mem' md' k -> In (cid, pos) (frames S') ->
frame_addr ly cid pos mod 32 = 0 /\ in_app (frame_addr ly cid pos) (fs_frame_bytes cid) /\
4096 <= frame_addr ly cid pos /\ frame_addr ly cid pos + fs_frame_bytes cid <= alloc_ceiling /\
(forall a, frame_addr ly cid pos <= a < frame_addr ly cid pos + fs_frame_bytes cid ->
  apresent (w_H W') mem' a /\ ~ aowned B ly' S' a) /\
(forall i, 0 <= i < fs_frame_bytes cid / 8 ->
  apresent (w_H W') mem' (shadow_addr (frame_addr ly cid pos) + i) /\
  ~ aowned B ly' S' (shadow_addr (frame_addr ly cid pos) + i)) /\
apresent (w_H W') mem' (flag_addr ly cid pos) /\ aowned B ly' S' (flag_addr ly cid pos) /\
app_addr (flag_addr ly cid pos) /\ ~ in_img rsegs (flag_addr ly cid pos) /\
4096 <= flag_addr ly cid pos /\ zone2 (flag_addr ly cid pos) 1 /\ flag_addr ly cid pos < alloc_ceiling.
Proof.
intros STK sp0 FP ly S W mem md own ly' S' W' mem' md' k cid pos HJ Hin.
pose proof (proj1 HJ) as HAR.
destruct (rck_jF STK sp0 FP ly S W mem md own ly' S' W' mem' md' k cid pos HJ) as [EFA EFL].
destruct (al_frames _ _ LAWS _ _ _ _ _ cid pos HAR Hin) as (HFal & HFapp & HFpres & HFSpres).
destruct (frames_bounds rsegs B LAWS _ _ _ _ _ cid pos HAR Hin) as (HF4096 & HFceil & _).
destruct (FFL _ _ _ _ _ cid pos HAR Hin) as (HFLp & HFLo & (HFLapp & HFLimg) & (HFL4096 & HFLz & HFLceil)).
rewrite EFA in HFal, HFapp, HFpres, HFSpres, HF4096, HFceil.
rewrite EFL in HFLp, HFLo, HFLapp, HFLimg, HFL4096, HFLz, HFLceil.
split; [exact HFal|]. split; [exact HFapp|]. split; [exact HF4096|]. split; [exact HFceil|].
split; [exact HFpres|]. split; [exact HFSpres|].
split; [exact HFLp|]. split; [exact HFLo|]. split; [exact HFLapp|]. split; [exact HFLimg|].
split; [exact HFL4096|]. split; [exact HFLz | exact HFLceil].
Qed.
End ff.

(* ================================ (5) the owned-set clause ================================ *)
Section ow.
Variable B : asyms.
(* aowned reads the layout, st_chunks (sec_extents, the allocated chunks) and frames, nothing else of the state *)
Lemma rck_aowned_of : forall ly2 S2 lyc Sc,
ly2 = lyc -> st_chunks S2 = st_chunks Sc -> frames S2 = frames Sc ->
forall a, aowned B ly2 S2 a -> aowned B lyc Sc a.
Proof.
intros ly2 S2 lyc Sc -> Ech Efr a H.
unfold aowned, sec_extents, aclient_byte in *. rewrite Ech, Efr in H. exact H.
Qed.
(* the walk's state at the return: the allocation's set_fs f Sc (which pushed (cid, pos)), then the release
   stack_free_state cid pos *)
Lemma rck_free_eqs : forall cid pos f Sc,
frames (set_fs f Sc) = (cid, pos) :: frames Sc ->
st_chunks (stack_free_state cid pos (set_fs f Sc)) = st_chunks Sc /\
st_sec_arr (stack_free_state cid pos (set_fs f Sc)) = st_sec_arr Sc /\
st_sec_reserved (stack_free_state cid pos (set_fs f Sc)) = st_sec_reserved Sc /\
frames (stack_free_state cid pos (set_fs f Sc)) = frames Sc.
Proof.
intros cid pos f Sc Hf. change (frames (set_fs f Sc)) with (fs_live f) in Hf.
split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
change (del_pos (fs_live f) cid pos = frames Sc). rewrite Hf. cbn [del_pos]. rewrite !Z.eqb_refl. reflexivity.
Qed.
Lemma rck_aowned_free : forall ly cid pos f Sc,
frames (set_fs f Sc) = (cid, pos) :: frames Sc ->
forall a, aowned B ly (stack_free_state cid pos (set_fs f Sc)) a -> aowned B ly Sc a.
Proof.
intros ly cid pos f Sc Hf. destruct (rck_free_eqs cid pos f Sc Hf) as (E1 & _ & _ & E4).
exact (rck_aowned_of ly _ ly Sc eq_refl E1 E4).
Qed.
End ow.

(* ================================ (6) the side-stack allocation, keeping S2 = set_fs f Sc ================================ *)
Section sm.
Variable B : asyms.
Hypothesis LAWS : AR_laws rsegs B.
Hypothesis HAPI : api_env rsegs B.
Hypothesis ML : model_laws (as_universe B).
Hypothesis SMP : stack_malloc_progressP B.
(* YCbq aj_stack_malloc_at, with (exists f, S2 = set_fs f Sc), the contract's same_but_materialized and its
   non-owned-kept clause added after frames S2 = (cid, pos) :: frames Sc *)
Lemma rck_stack_malloc_at : forall cid, astack_malloc_realizes rsegs B cid -> 0 <= cid <= 10 ->
forall W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc mdc k (o : Z) raw,
ajournal rsegs B STK sp0 FP ly S W0 mem md own lyc Sc W memT mdc k ->
spZ regsT = sp0 + o -> o mod 16 = 0 -> o <= 0 -> ESTACK - o <= STK ->
getr regsT 3 = w64 (as_gp B) -> getr regsT 4 = w64 (as_tp B) ->
getr regsT 1 = raw -> YK0s.ret_ok raw ->
count_cid cid (frames Sc) < fs_frames cid ->
SRr rsegs W (mkCfg (mkst regsT (Z_to_bv 64 (pc_stack_malloc (as_code B) cid)) memT (seg_rom rsegs)) mdc)
(fun W2 c2 => W2 = W /\ exists S2 regs2 mem2 md2 pos,
c2 = mkCfg (mkst regs2 raw mem2 (seg_rom rsegs)) md2 /\
ajournal rsegs B STK sp0 FP ly S W0 mem md ((cid, pos) :: own) lyc S2 W mem2 md2 k /\
aregs_preserved regsT regs2 /\ getr regs2 10 = w64 (frame_addr lyc cid pos) /\
ablocks B lyc S2 = ablocks B lyc Sc /\ frames S2 = (cid, pos) :: frames Sc /\ (exists f, S2 = set_fs f Sc) /\
same_but_materialized mdc md2 /\
(forall a, 0 <= a < 2 ^ 64 -> ~ aowned B lyc Sc a -> ~ aowned B lyc S2 a -> ~ (sp0 + o - ESTACK <= a < sp0 + o) ->
 aview rsegs (w_H W) mem2 a = aview rsegs (w_H W) memT a) /\
~ In (cid, pos) (frames Sc) /\
st_nev S2 = st_nev Sc /\ blocks_bytes S2 = blocks_bytes Sc /\
zero_shadow (aview rsegs (w_H W) mem2) SHADOW_OFF (frame_addr lyc cid pos) (fs_frame_bytes cid) /\
rdword (aview rsegs (w_H W) mem2) (frame_addr lyc cid pos + fs_frame_bytes cid - 8) = Some (flag_addr lyc cid pos) /\
acall_kept rsegs B lyc Sc W memT W mem2 (sp0 + o - ESTACK) (sp0 + o) (fun _ => False)).
Proof.
intros cid ASM Hcid W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc mdc k o raw
HJ Hsp' Hal Hneg Hbud Hgp Htp Hra Hraw Hcnt.
pose proof HJ as (HAR & Hly & Hsecs & Hwle & Hio & Hfrs & Hnev & Hk & F1 & F2 & F3 & F4 & Hgone & Hpres & Hstatic & F5 & HQT).
pose proof Hstatic as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5). pose proof (proj1 HAPI) as [He0 He1].
assert (ASTACK = 16384) as Has by reflexivity. assert (ESTACK = 4096) as Hes by reflexivity.
pose proof Hly as (_ & _ & _ & _ & _ & _ & _ & _ & Etop & Eslo & Eshi & _).
assert (HstkC : astk_ok ESTACK lyc (spZ regsT)).
{ unfold astk_ok, ly_bot in *. rewrite Hsp', Eslo, Eshi, Etop. repeat split; try zlia.
all: rewrite Z.add_mod, Hal16, Hal by zlia; reflexivity. }
assert (HPRE : ecall_pre rsegs B lyc Sc W regsT memT mdc).
{ split; [exact HAR|]. split; [rewrite Hra; exact Hraw|]. split; [destruct HstkC as (Q1 & _); exact Q1|].
split; [rewrite Eslo, Hsp'; zlia|]. split; [rewrite Eshi, Hsp'; zlia|].
split; [intros a Ha; apply Hpres; rewrite Hsp' in Ha; zlia|]. split; [exact Hgp | exact Htp]. }
pose proof (am_wf _ _ _ _ (proj1 HAR)) as HWF.
destruct (SMP Sc cid HWF Hcid Hcnt) as (pos & S2 & Hpath).
pose proof (ml_stack_malloc _ ML Sc cid HWF Hcid) as HTOK.
destruct (atok_apath _ _ _ [] (PFake cid pos, S2) HTOK Hpath) as (ns' & HQ). unfold stack_malloc_post in HQ.
destruct HQ as (HWF2 & (f & ES2) & _ & Hpos & Hfrs2 & Hfresh).
eapply SRr_mono; [exact (ASM lyc Sc W regsT memT mdc pos S2 HPRE Hcnt Hpath)|].
cbv beta. intros W2 c2 HwleW (-> & regs2 & mem2 & md2 & -> & HAR2 & HP & Hsame & Hres & Hz & Hflag & Hfpres & Hfr & Hpres2).
assert (Hblk : blocks S2 = blocks Sc) by (rewrite ES2; reflexivity).
assert (Eab2 : ablocks B lyc S2 = ablocks B lyc Sc) by (unfold ablocks; rewrite Hblk; reflexivity).
assert (Hnev2 : st_nev S2 = st_nev Sc) by (rewrite ES2; reflexivity).
assert (Hbb : blocks_bytes S2 = blocks_bytes Sc) by (rewrite ES2; reflexivity).
assert (Hsecs2 : st_secs S2 = st_secs Sc) by (rewrite ES2; reflexivity).
assert (HJ1 : ajournal rsegs B ESTACK (spZ regsT) [] lyc Sc W memT mdc [(cid, pos)] lyc S2 W mem2 md2 0).
{ eapply (call_effect_journal rsegs B LAWS rtsb_segs_low HAPI ESTACK lyc Sc W regsT memT mdc lyc S2 W mem2 md2
    (fun _ => False) [] [(cid, pos)] 0);
[exact HAR2 | apply layout_le_refl | apply wle_refl | apply same_io_materialized; exact Hsame | | exact Hpres2 | exact HAR | exact HstkC
| cbn; exact Hfrs2 | zlia | zlia | rewrite Hsecs2; zlia | intros a [] | | ].
- intros a H0 H1 H2 H3 _. apply (Hfr a H0 H1 H2). intros H. apply H3. left. exact H.
- intros p n i Hp Hnp. exfalso. apply Hnp. rewrite Eab2. exact Hp.
- rewrite ES2. apply (qtight_ext Sc); [reflexivity | reflexivity | reflexivity | exact HQT]. }
split; [reflexivity|]. exists S2, regs2, mem2, md2, pos.
split; [unfold cfg_at, raZ; rewrite Hra; unfold w64; rewrite Z_to_bv_bv_unsigned; reflexivity|].
split.
{ rewrite Hsp' in HJ1. replace k with (k + 0) by zlia. change ((cid, pos) :: own) with ([(cid, pos)] ++ own).
eapply (ajournal_sub rsegs B LAWS rtsb_segs_low); [exact HJ | exact HJ1 | zlia | zlia | intros a (rg & [] & _)]. }
split; [exact HP|]. split; [exact Hres|]. split; [exact Eab2|]. split; [exact Hfrs2|].
split; [exists f; exact ES2|].
split; [exact Hsame|].
split; [intros a H0 H1 H2 H3; apply (Hfr a H0 H1 H2); rewrite Hsp'; exact H3|].
split; [exact Hfresh|].
split; [exact Hnev2|]. split; [exact Hbb|]. split; [exact Hz|]. split; [exact Hflag|].
rewrite Hsp' in HJ1. eapply (acall_kept_of_journal rsegs B rtsb_segs_low);
[exact HJ1 | exact HAR | intros a (rg & [] & _) | | exact sink_closed_nil].
intros b m i Hb Hi _. rewrite Eab2. exact Hb.
Qed.
End sm.
End k.

(* ================================ (7) closed_list after the class-2 frame ================================
   RtPgCSpec.rt_img_facts at image B's record rate_himg_B and range [IMG_LO, IMG_TOP) (lib/Reusable/YImgTop.v) is the
   hypothesis the segments after the frame call take to rebuild the contract's rt_i32tab premise of closed_list at
   their own state: the class-2 allocation keeps only the bytes owned at neither state (YG0d.v
   astack_malloc_realizes), and every shadow byte is runtime-owned, so the premise does not reach them by itself.
   closed_list (0x21520, 12 bytes) is a registered global of rate_B_globs with room for it, its bytes are no owned
   static, so RtPgBase.rt_img_unowned and rt_i32tab_at apply (lib/A/RtPgSiteA.v rate_A_i32_glob /
   rate_A_i32_unowned / rate_A_i32tab_at, at image B's record). Image B's close proves the hypothesis at its symbol
   record. *)
Lemma rckb_tab_in : In (0x21520, RateCfg.closed_list) rate_B_i32.
Proof. unfold rate_B_i32. left. reflexivity. Qed.
Definition rckb_i32_chk : bool :=
  forallb (fun t => existsb (fun g => (fst g =? fst t) && (4 * Z.of_nat (length (snd t)) <=? snd g)) rate_B_globs)
    rate_B_i32.
Lemma rckb_i32_chk_ok : rckb_i32_chk = true.
Proof. vm_compute. reflexivity. Qed.
Lemma rckb_i32_glob : forall t vs, In (t, vs) rate_B_i32 ->
  exists sz, In (t, sz) rate_B_globs /\ 4 * Z.of_nat (length vs) <= sz.
Proof.
intros t vs Hin. pose proof rckb_i32_chk_ok as E. unfold rckb_i32_chk in E.
rewrite forallb_forall in E. specialize (E (t, vs) Hin). cbv beta in E. cbn [fst snd] in E.
exact (rt_glob_of_b t _ rate_B_globs E).
Qed.
Section imgf. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : asyms.
Lemma rckb_i32_unowned : forall t vs, rt_img_facts rsegs B rate_himg_B IMG_LO IMG_TOP -> In (t, vs) rate_B_i32 ->
  rt_ro_unowned B t (4 * Z.of_nat (length vs)).
Proof.
intros t vs (HU & _ & _) Hin. rewrite Forall_forall in HU.
apply (HU (t, 4 * Z.of_nat (length vs))). unfold rt_ro_ranges. apply in_or_app. right. apply in_or_app. left.
exact (in_map (fun t0 : Z * list Z => (fst t0, 4 * Z.of_nat (length (snd t0)))) rate_B_i32 (t, vs) Hin).
Qed.
Lemma rckb_i32tab_at : forall t vs ly S (W : world rsegs) mem md (H0 : word -> bool) mem0,
  rt_img_facts rsegs B rate_himg_B IMG_LO IMG_TOP -> In (t, vs) rate_B_i32 -> AR rsegs B ly S W mem md ->
  rt_i32tab rsegs H0 mem0 t vs ->
  (forall i, 0 <= i < 4 * Z.of_nat (length vs) -> aview rsegs (w_H W) mem (t + i) = aview rsegs H0 mem0 (t + i)) ->
  rt_i32tab rsegs (w_H W) mem t vs.
Proof.
intros t vs ly S W mem md H0 mem0 (_ & HG & _) Hin HAR Hc Heq.
destruct (rckb_i32_glob t vs Hin) as (sz & Hg & Hsz).
exact (rt_i32tab_at rsegs B rate_B_globs ly S W mem md H0 mem0 t vs sz HG HAR Hg Hsz Hc Heq).
Qed.
End imgf.

(* ================================ (1) the tactics ================================ *)
(* rck_aj_run_sh tblok HS HJ: from HS : st_ok rsegs E ss (restrict (w_H W) ms), HJ : the caller's journal at
   (ms_mem ms), tblok : table_ok rsegs tbl and an AR_laws hypothesis in the context, computes the shadow-aware run
   (vm_compute) and applies rck_run_sh_AJ: the awr_ok goal first, then the after-run continuation with the new
   HS / HJ (YCbq aj_after_run). *)
Ltac rck_aj_run_sh tblok HS HJ :=
lazymatch type of HS with
| st_ok ?segs ?E ?ss (restrict (w_H ?W) ?ms) =>
lazymatch type of tblok with
| table_ok _ ?tbl =>
let r := eval vm_compute in (sym_runN_sh segs tbl FUEL ss) in
lazymatch r with
| (?ss', ?st) =>
let Hrun := fresh "Hrun" in
assert (Hrun : sym_runN_sh segs tbl FUEL ss = (ss', st)) by (vm_compute; reflexivity);
let HL := aj_laws in
eapply (rck_run_sh_AJ _ HL tbl tblok W FUEL E ss ss' st ms _ _ _ _ _ _ _ _ _ _ _ _ _ _ HS Hrun I HJ);
[ clear Hrun | clear Hrun HS HJ; aj_after_run HS HJ ]
end
end
| _ => fail "rck_aj_run_sh: HS must be  st_ok segs E ss (restrict (w_H W) ms)"
end.
(* rck_aj_run_to_sh tblok HS HJ stop: the same, the run stopping at pc = stop (rck_run_to_sh_AJ) *)
Ltac rck_aj_run_to_sh tblok HS HJ stop :=
lazymatch type of HS with
| st_ok ?segs ?E ?ss (restrict (w_H ?W) ?ms) =>
lazymatch type of tblok with
| table_ok _ ?tbl =>
let r := eval vm_compute in (sym_run_toN_sh segs tbl FUEL stop ss) in
lazymatch r with
| (?ss', ?st) =>
let Hrun := fresh "Hrun" in
assert (Hrun : sym_run_toN_sh segs tbl FUEL stop ss = (ss', st)) by (vm_compute; reflexivity);
let HL := aj_laws in
eapply (rck_run_to_sh_AJ _ HL tbl tblok W FUEL stop E ss ss' st ms _ _ _ _ _ _ _ _ _ _ _ _ _ _ HS Hrun I HJ);
[ clear Hrun | clear Hrun HS HJ; cbv beta iota; aj_after_run HS HJ ]
end
end
| _ => fail "rck_aj_run_to_sh: HS must be  st_ok segs E ss (restrict (w_H W) ms)"
end.

Print Assumptions rck_run_sh_AJ.
Print Assumptions rck_run_to_sh_AJ.
Print Assumptions rck_shadow_decl_sv_ok.
Print Assumptions rck_shadow_decl_sv.
Print Assumptions rck_shadow_decl.
Print Assumptions rck_fbytes.
Print Assumptions rck_fbytes2.
Print Assumptions rck_fbounds.
Print Assumptions rck_awr_fobj.
Print Assumptions rck_awr_fsh.
Print Assumptions rck_awr_ok_fsh.
Print Assumptions rck_awr_ok_fobj.
Print Assumptions rck_jF.
Print Assumptions rck_ffacts.
Print Assumptions rck_aowned_of.
Print Assumptions rck_free_eqs.
Print Assumptions rck_aowned_free.
Print Assumptions rck_stack_malloc_at.
Print Assumptions rckb_tab_in.
Print Assumptions rckb_i32_glob.
Print Assumptions rckb_i32_unowned.
Print Assumptions rckb_i32tab_at.
