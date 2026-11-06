(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Theorem Labs, 2026-10: what a PROGRAM CALL keeps of pj_set's image-B walk state (fuzz_preset asan-ubsan,
   B 0x86e8c; the cuts of lib/B/Prog/pj_set_defs.v): the bytes, the placement and the SHADOW facts of the structs
   and the key the kit's text names, from a callee's journal (YCbqG.v ajournal_xR at any world relation R, own = []: the
   calls before pj_set's first free at wle, those after at the re-hiding relation wle') and the allocator laws at the
   harness head length (AR_laws_x at hl := cf_head; at ARcf it is YGcallcf.v AR_laws_x_xs). No lemma reads the
   journal's world conjunct but pjs_aj_widen, which passes it through.
   proves no function (kind: glue lemma).
   - The bytes ride on the journal's clauses: a block live at both states (the block clause), the caller's window
     (the stack clause: every stack byte lies at or above the allocator ceiling), a fake frame (the frame clause),
     a read-only image byte (the image clause).
   - The SHADOW facts of a struct after a call, one law per case of PRH_FnReader.v prhReader_at:
     1. a harness block of the ledger: alx_hshadow (YCbqG.v ARx_hshadow_law at cf_head);
     2. a live allocator block that is no harness block: alx_shadow (YCbqG.v ARx_shadow_law), whose premise - no
        hidden head inside the block - FOLLOWS from the ledger (Hp is exactly the harness bases) and the blocks'
        separation (pjs_no_head_in, transcribed from pj_parse_seg_c1.v@175b3601c4e pjp_no_head_in): no Section
        premise is needed for it;
     3. a fake frame: the frame clause keeps its shadow bytes, pjs_g_vis' frame hull gives the hull;
     4. the caller's window: alx_zshadow_byte gives each byte's shadow; the HULL of such a struct reads shadow bytes
        up to 63 bytes past it, past the stack's top when that top is not 64-aligned, and no law at a generic ARx
        gives the alignment, so the cuts after a call carry the object by pjs_place (pj_set_defs.v), which has no
        hull; no later step reads it.
   - The key (cstr_ok + kept_at): the bytes by the block / image clause, the shadow by kept_at's three cases
     (alx_hshadow; pjs_g_vis' zero-shadow conjunct; the const cells alx_const_cells and pjs_g_vis' image shadow map),
     as pj_parse_seg_c1.v@175b3601c4e pjp_text_kept.
   - pjs_aj_widen: a callee journal at its own window (STK, sp) is one at the caller's widened window (STK + e,
     sp + e), with the bytes of [sp, sp + e) outside FP kept - so an apost_base_x callee (pj_get, fuzz_strdup) called
     by YCbqGcallW.v aj_call_xW at e1 = 0 (fpostW_x_of_apost) meets pj_set_defs.v pjs_frame_kept_stmt.
   Small arithmetic lemmas are transcribed from blob e1728eec497a (pj_parse_seg_c1.v, no longer in this tree), at its lines
   (pjp_req :80, pjp_hull_sub :163, pjp_hull_img :145, pjp_garr8_move :204, pjp_ro_img :217, pjp_hp_block :296,
   pjp_no_head_in :307), cited per lemma.
   Numerals: 56 (LENGTH: the struct pj); 8 / 64 (LENGTH: the shadow granule and its hull); no ADDRESS. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn YP0b YP0a.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YN3v YI04 YI00 YG0s YP07 YI16.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05 YG0p YCbqG FCiface YGcallMx.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfNames YGcfRoomKeep YG0dcf YGcfRoomPre.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK0o YK06 YGcfFsVis.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YP0d YP0c YC80 YPsym YC4aP YImgTop.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YB1v YB13.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Ledger ReaderRes.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PjTree PjGrammar.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_Base PRH_Reader PRH_Charge PRH_FnReader.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_FnPj PRH_FnAlloc.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B Require Import Img0 Listing_prog PAImg_prog PRH_ImgB.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog Require Import S1ImgB pj_set_defs pj_set_trans.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Set Warnings "-notation-for-abbreviation".
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Local Open Scope Z_scope.
#[local] Existing Instance prh_img_B.

#[local] Notation PA := PI_prog_B.
#[local] Notation SEGS := (@pa_segs _ B_prog_listing PA).
#[local] Notation RLO := (@pa_relro_lo _ B_prog_listing PA).
#[local] Notation RHI := (@pa_relro_hi _ B_prog_listing PA).

(* ---- arithmetic (pj_parse_seg_c1.v@175b3601c4e, transcribed) ---- *)
(* pjp_req :80 *)
Lemma pjs_req : forall n, 0 <= n -> n <= req_size n /\ 1 <= req_size n /\ (0 < n -> req_size n = n).
Proof. intros n Hn. unfold req_size. destruct (Z.eqb_spec n 0); lia. Qed.

(* pjp_hull_sub :163: the hull is closed under sub-ranges *)
Lemma pjs_hull_sub : forall rd x n x' n',
  shadow_hull_vis rd x n -> x <= x' -> x' + n' <= x + n -> shadow_hull_vis rd x' n'.
Proof.
intros rd x n x' n' H H1 H2 s Hs. apply H. unfold shadow_addr in *.
pose proof (Z.div_le_mono x x' 8 ltac:(lia) H1) as D1.
pose proof (Z.div_le_mono (x' + n' - 1) (x + n - 1) 8 ltac:(lia) ltac:(lia)) as D2.
pose proof (Z.div_le_mono (SHADOW_OFF + x / 8) (SHADOW_OFF + x' / 8) 8 ltac:(lia) ltac:(lia)) as D3.
pose proof (Z.div_le_mono (SHADOW_OFF + (x' + n' - 1) / 8) (SHADOW_OFF + (x + n - 1) / 8) 8 ltac:(lia) ltac:(lia)) as D4.
lia.
Qed.

(* pjp_hull_img :145: the hull of an image range away from the image's ends maps into the image's shadow *)
Lemma pjs_hull_img : forall a n s, 0 < n -> IMG_LO_B + 64 <= a -> a + n + 64 <= IMG_TOP_B ->
  shadow_addr a / 8 * 8 <= s < shadow_addr (a + n - 1) / 8 * 8 + 8 ->
  s = shadow_addr (8 * (s - SHADOW_OFF)) /\ IMG_LO_B <= 8 * (s - SHADOW_OFF) < IMG_TOP_B.
Proof.
intros a n s Hn Hlo Hhi Hs. unfold IMG_LO_B, IMG_TOP_B in *. unfold shadow_addr in *.
assert (Hdlo : a / 8 <= (a + n - 1) / 8) by (apply Z.div_le_mono; lia).
pose proof (Z.div_mod a 8 ltac:(lia)) as Ha8. pose proof (Z.mod_pos_bound a 8 ltac:(lia)) as Ha8b.
pose proof (Z.div_mod (a + n - 1) 8 ltac:(lia)) as Hb8. pose proof (Z.mod_pos_bound (a + n - 1) 8 ltac:(lia)) as Hb8b.
pose proof (Z.div_mod (SHADOW_OFF + a / 8) 8 ltac:(lia)) as Hc8.
pose proof (Z.mod_pos_bound (SHADOW_OFF + a / 8) 8 ltac:(lia)) as Hc8b.
pose proof (Z.div_mod (SHADOW_OFF + (a + n - 1) / 8) 8 ltac:(lia)) as Hd8.
pose proof (Z.mod_pos_bound (SHADOW_OFF + (a + n - 1) / 8) 8 ltac:(lia)) as Hd8b.
unfold SHADOW_OFF in *.
split; [rewrite Z.mul_comm, Z.div_mul by lia; lia | lia].
Qed.

(* the shadow byte of an address below 2^47 lies in the shadow region, off every application byte *)
Lemma pjs_shadow_reg : forall x, 0 <= x < 2 ^ 47 ->
  kLowShadowBeg <= shadow_of_addr SHADOW_OFF x < kHighMemBeg.
Proof.
intros x Hx. unfold shadow_of_addr, SHADOW_OFF, kLowShadowBeg, kHighMemBeg.
assert (x / 8 < 2 ^ 44) by (apply Z.div_lt_upper_bound; lia).
pose proof (Z.div_pos x 8 ltac:(lia) ltac:(lia)). lia.
Qed.

Section w. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
(* pjp_garr8_move :204: a byte list survives a memory change that keeps each of its bytes' views *)
Lemma pjs_garr8_move : forall (W W' : world SEGS) m m' x l, garr8 SEGS (mrestrict (w_H W) m) x l ->
  (forall j, (j < length l)%nat -> aview SEGS (w_H W') m' (x + Z.of_nat j) = aview SEGS (w_H W) m (x + Z.of_nat j)) ->
  garr8 SEGS (mrestrict (w_H W') m') x l.
Proof.
intros W W' m m' x l H HA j Hj. destruct (H j Hj) as [V R]. split; [|exact R].
intros kk Hkk. assert (kk = 0%nat) by lia. subst kk. cbn [Z.of_nat]. rewrite Z.add_0_r.
specialize (V 0%nat Hkk). cbn [Z.of_nat] in V. rewrite Z.add_0_r in V.
specialize (HA j Hj). unfold aview in HA. rewrite V in HA. cbn [option_map] in HA.
destruct (mbyte SEGS (mrestrict (w_H W') m') (x + Z.of_nat j)) as [b|] eqn:Eb; cbn [option_map] in HA; [|discriminate HA].
injection HA as Hb. f_equal. apply bv_eq. exact Hb.
Qed.

(* pjp_ro_img :217: a read-only byte is an image byte *)
Lemma pjs_ro_img : forall a, in_roP SEGS RLO RHI a -> in_img SEGS a.
Proof.
intros a [(sg & Hin & _ & Hr) | Hr]; [exists sg; split; [exact Hin | exact Hr] | exact (@pa_relro_img _ _ PA a Hr)].
Qed.

(* every byte of the image band [IMG_LO_B, IMG_TOP_B) is in image B's ROM (YB13.v tfib_rom_all, a scan of the
   segments' bytes), so its view is defined at every state: mbyte falls back to the ROM where the memory has no
   byte. What the trailing granule of an image string (kept_at's second and third cases) needs after a call. *)
Lemma pjs_img_view : forall (H : word -> bool) (m : word -> option byte) a, IMG_LO_B <= a < IMG_TOP_B ->
  aview SEGS H m a <> None.
Proof.
intros H m a Ha. pose proof (YB13.tfib_rom_all a ltac:(unfold IMG_LO_B, IMG_TOP_B in Ha; lia)) as Hr.
unfold aview, mbyte. destruct (mrestrict H m (Z_to_bv 64 a)) as [b|]; [discriminate|].
change (seg_rom SEGS (Z_to_bv 64 a)) with (seg_rom YB1v.tfibsegs (Z_to_bv 64 a)).
destruct (seg_rom YB1v.tfibsegs (Z_to_bv 64 a)); [discriminate | exfalso; exact (Hr eq_refl)].
Qed.
End w.

Section v. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams} {RL : PrhRoomLive}.
Context {SK : YI16.sink_head}.
#[local] Notation PST := (prh_pst (PI := prh_img_B)).
(* the journals' world relation (implicit: each lemma takes it from its journal hypothesis) *)
Context {R : world SEGS -> world SEGS -> Prop}.
Variable B : asyms.
Variable ARx : alayout -> astate -> list Z -> world SEGS -> (word -> option byte) -> Model -> Prop.
#[local] Abbreviation rdW W mem := (mrestrict (w_H W) mem).
#[local] Notation AJ := (ajournal_xR (SK := SK) SEGS B PST ARx R).
(* the allocator's laws at the harness head length *)
Hypothesis LAWS : AR_laws_x SEGS B ARx cf_head.
(* the MARKED shadow-visibility kit facts of pj_set_defs.v (frame hull, zero-shadow statics, image shadow map) *)
Hypothesis VIS : pjs_g_vis B ARx.

(* ---- the journal at a wider window ---- *)
(* a journal at (STK, sp) is one at (STK + e, sp + e) when the wider window is a stack window present at the later
   state; the bytes of [sp, sp + e) outside FP are kept *)
Lemma pjs_aj_widen : forall STK sp FP ly S Hp W mem md own ly' S' Hp' W' mem' md' k e,
  AJ STK sp FP ly S Hp W mem md own ly' S' Hp' W' mem' md' k -> 0 <= e ->
  astk_ok (STK + e) ly (sp + e) -> (forall a, sp <= a < sp + e -> apresent (w_H W') mem' a) ->
  AJ (STK + e) (sp + e) FP ly S Hp W mem md own ly' S' Hp' W' mem' md' k /\
  (forall a, sp <= a < sp + e -> ~ inFP FP a -> aview SEGS (w_H W') mem' a = aview SEGS (w_H W) mem a).
Proof.
intros STK sp FP ly S Hp W mem md own ly' S' Hp' W' mem' md' k e HJ He Hast' Hpe.
pose proof (ajxR_hi HJ) as F1. pose proof (ajxR_pres HJ) as Hpres. pose proof (ajxR_stk HJ) as Hast.
pose proof Hast as (_ & HS0 & Hceil & Hslo & _ & _ & _ & _ & _).
pose proof Hast' as (_ & _ & _ & _ & Hshi' & H47' & _ & _ & _).
split.
- (* the journal by its constructor: every conjunct is the old one's but the window's three (hi, pres, stk) *)
  refine (ajxR_intro (ajxR_ar HJ) (ajxR_ly HJ) (ajxR_secs HJ) (ajxR_rel HJ) (ajxR_io HJ) (ajxR_frs HJ) (ajxR_nev HJ)
    (ajxR_k HJ) _ (ajxR_blk HJ) (ajxR_img HJ) (ajxR_frm HJ) (ajxR_gone HJ) _ Hast' (ajxR_extra HJ) (ajxR_qt HJ)
    (ajxR_wild HJ)).
  + intros a Ha Hw. apply F1; [exact Ha | lia].
  + intros a Ha. destruct (Z_lt_le_dec a sp) as [Hl | Hl]; [apply Hpres; lia | apply Hpe; lia].
- intros a Ha _. apply F1; lia.
Qed.

(* ---- the ledger's harness bases (pj_parse_seg_c1.v@175b3601c4e, transcribed) ---- *)
(* pjp_hp_block :296 *)
Lemma pjs_hp_block : forall ly S Hp W mem Lam peak cnt fail ran most own h,
  prh_ledger (PA := PA) B ly S Hp W mem Lam peak cnt fail ran most own -> In h Hp ->
  exists a k, In (a, k) Lam /\ h = a - cf_head /\ 0 <= k /\ In (a - cf_head, k + cf_head) (ablocks B ly S).
Proof.
intros ly S Hp W mem Lam peak cnt fail ran most own h (_ & _ & HF & HP) Hh.
apply (Permutation_in _ HP) in Hh. apply in_map_iff in Hh as ([a k] & Ea & Hin). cbn [fst] in Ea.
pose proof (proj1 (Forall_forall _ _) HF (a, k) Hin) as (Hk0 & Hab & _). cbn [fst snd] in Hk0, Hab.
exists a, k. split; [exact Hin | split; [lia | split; [exact Hk0 | exact Hab]]].
Qed.

(* pjp_no_head_in :307: no harness base of the ledger lies in a live block that is not that harness block's *)
Lemma pjs_no_head_in : forall ly S Hp W mem md Lam peak cnt fail ran most own b m,
  ARx ly S Hp W mem md -> prh_ledger (PA := PA) B ly S Hp W mem Lam peak cnt fail ran most own ->
  In (b, m) (ablocks B ly S) -> ~ In (b + cf_head, m - cf_head) Lam ->
  forall h, In h Hp -> ~ (b <= h < b + req_size m).
Proof.
intros ly S Hp W mem md Lam peak cnt fail ran most own b m HAR HL Hbm HnL h Hh Hr.
pose proof (@cf_head_nonneg cp) as Hh0.
destruct (pjs_hp_block ly S Hp W mem Lam peak cnt fail ran most own h HL Hh) as (a & k & Hin & -> & Hk0 & Hab).
pose proof (pjs_req (k + cf_head) (Z.add_nonneg_nonneg _ _ Hk0 Hh0)) as (_ & Rq & _).
destruct (Z.eq_dec b (a - cf_head)) as [Eb | Nb]; [destruct (Z.eq_dec m (k + cf_head)) as [Em | Nm] |].
- apply HnL. replace (b + cf_head, m - cf_head) with (a, k) by (f_equal; lia). exact Hin.
- assert (Hne : (b, m) <> (a - cf_head, k + cf_head)) by (intros E; injection E as _ E2; exact (Nm E2)).
  pose proof (sep_blocks_x SEGS B ARx LAWS ly S Hp W mem md b m _ _ HAR Hbm Hab Hne) as Hd.
  unfold zdisjoint in Hd. cbn [fst snd] in Hd. lia.
- assert (Hne : (b, m) <> (a - cf_head, k + cf_head)) by (intros E; injection E as E1 _; exact (Nb E1)).
  pose proof (sep_blocks_x SEGS B ARx LAWS ly S Hp W mem md b m _ _ HAR Hbm Hab Hne) as Hd.
  unfold zdisjoint in Hd. cbn [fst snd] in Hd. lia.
Qed.

(* ---- the shadow facts at a state, one per placement ---- *)
(* 1. inside a harness block of the ledger *)
Lemma pjs_vis_lam : forall ly S Hp W mem md Lam peak cnt fail ran most own a k p n,
  ARx ly S Hp W mem md -> prh_ledger (PA := PA) B ly S Hp W mem Lam peak cnt fail ran most own ->
  In (a, k) Lam -> a <= p -> p + n <= a + k -> 0 < n ->
  range_addressable (aview SEGS (w_H W) mem) SHADOW_OFF p n /\ shadow_hull_vis (aview SEGS (w_H W) mem) p n.
Proof.
intros ly S Hp W mem md Lam peak cnt fail ran most own a k p n HAR HL Hin Hap Hn Hn0.
pose proof (@cf_head_nonneg cp) as Hh0.
pose proof HL as (_ & _ & HLF & _).
pose proof (proj1 (Forall_forall _ _) HLF (a, k) Hin) as (Hk0 & Hab & Hhp & _). cbn [fst snd] in Hk0, Hab, Hhp.
destruct (alx_hshadow SEGS B ARx LAWS ly S Hp W mem md (a - cf_head) (k + cf_head) HAR Hab Hhp) as [Hbs Hbh].
pose proof (pjs_req (k + @cf_head cp) ltac:(lia)) as (_ & _ & Rq). rewrite Rq in Hbs, Hbh by lia.
replace (a - cf_head + cf_head) with a in Hbs, Hbh by lia.
replace (k + cf_head - cf_head) with k in Hbs, Hbh by lia.
split; [exact (block_shadow_range _ SHADOW_OFF a k p n Hbs Hap Hn)|].
exact (pjs_hull_sub _ a k p n (Hbh ltac:(lia)) Hap Hn).
Qed.

(* 2. inside a live allocator block that is no harness block *)
Lemma pjs_vis_blk : forall ly S Hp W mem md Lam peak cnt fail ran most own b m p n,
  ARx ly S Hp W mem md -> prh_ledger (PA := PA) B ly S Hp W mem Lam peak cnt fail ran most own ->
  In (b, m) (ablocks B ly S) -> ~ In (b + cf_head, m - cf_head) Lam -> b <= p -> p + n <= b + m -> 0 < n ->
  range_addressable (aview SEGS (w_H W) mem) SHADOW_OFF p n /\ shadow_hull_vis (aview SEGS (w_H W) mem) p n.
Proof.
intros ly S Hp W mem md Lam peak cnt fail ran most own b m p n HAR HL Hbm HnL Hb Hm Hn0.
destruct (alx_shadow SEGS B ARx LAWS ly S Hp W mem md b m HAR Hbm
  (pjs_no_head_in ly S Hp W mem md Lam peak cnt fail ran most own b m HAR HL Hbm HnL)) as [Hbs Hbh].
pose proof (pjs_req m ltac:(lia)) as (_ & _ & Rm). rewrite Rm in Hbs, Hbh by lia.
split; [exact (block_shadow_range _ SHADOW_OFF b m p n Hbs Hb Hm)|].
exact (pjs_hull_sub _ b m p n Hbh Hb Hm).
Qed.

(* 3. inside a live fake frame: the hull (pjs_g_vis); the bytes' shadow rides on the frame clause (below) *)
Lemma pjs_vis_frm : forall ly S Hp W mem md cid pos p n,
  ARx ly S Hp W mem md -> In (cid, pos) (frames S) ->
  frame_addr ly cid pos <= p -> p + n <= frame_addr ly cid pos + fs_frame_bytes cid ->
  shadow_hull_vis (aview SEGS (w_H W) mem) p n.
Proof.
intros ly S Hp W mem md cid pos p n HAR Hcp H1 H2. destruct VIS as (VF & _ & _).
exact (pjs_hull_sub _ _ _ p n (VF ly S Hp W mem md cid pos HAR Hcp) H1 H2).
Qed.

(* 4. inside the real stack: each byte's shadow is 0 *)
Lemma pjs_vis_stk : forall ly S Hp W mem md p n,
  ARx ly S Hp W mem md -> ly_stk_lo ly <= p -> p + n <= ly_stk_hi ly ->
  range_addressable (aview SEGS (w_H W) mem) SHADOW_OFF p n.
Proof.
intros ly S Hp W mem md p n HAR H1 H2 x Hx. exists 0. split; [|left; reflexivity].
unfold shadow_of_addr. exact (alx_zshadow_byte SEGS B ARx LAWS ly S Hp W mem md x HAR ltac:(lia)).
Qed.

(* the hull of a struct off the real stack, at any state *)
Lemma pjs_hull_low : forall ly S Hp W mem md Lam peak cnt fail ran most own (regs : bvmap 5 word) e p,
  ARx ly S Hp W mem md -> prh_ledger (PA := PA) B ly S Hp W mem Lam peak cnt fail ran most own ->
  prhReader_at B ly S Lam regs e p 56 -> p < spZ regs ->
  shadow_hull_vis (aview SEGS (w_H W) mem) p 56.
Proof.
intros ly S Hp W mem md Lam peak cnt fail ran most own regs e p HAR HL Hat Hsp.
destruct Hat as [(a & k & Hin & H1 & H2) | [(b & m & Hbm & HnL & H1 & H2) | [(cid & pos & Hcp & H1 & H2) | (H1 & _)]]].
- exact (proj2 (pjs_vis_lam ly S Hp W mem md Lam peak cnt fail ran most own a k p 56 HAR HL Hin H1 H2 ltac:(lia))).
- exact (proj2 (pjs_vis_blk ly S Hp W mem md Lam peak cnt fail ran most own b m p 56 HAR HL Hbm HnL H1 H2 ltac:(lia))).
- exact (pjs_vis_frm ly S Hp W mem md cid pos p 56 HAR Hcp H1 H2).
- lia.
Qed.

(* ---- writability and agreement ---- *)
Lemma pjs_blk_writable : forall ly S Hp W mem md b m x,
  ARx ly S Hp W mem md -> In (b, m) (ablocks B ly S) -> b <= x < b + req_size m ->
  writable_at SEGS (rdW W mem) x.
Proof.
intros ly S Hp W mem md b m x HAR Hbm Hx.
destruct (alx_blocks SEGS B ARx LAWS ly S Hp W mem md b m HAR Hbm) as (_ & _ & _ & _ & Hpo & _).
exact (apresent_writable SEGS (w_H W) mem x (proj1 (Hpo x Hx))).
Qed.

Lemma pjs_agree : forall (W W2 : world SEGS) mem mem2 (X : Z -> Prop),
  (forall x, X x -> aview SEGS (w_H W2) mem2 x = aview SEGS (w_H W) mem x) ->
  (forall x, X x -> writable_at SEGS (rdW W mem) x -> writable_at SEGS (rdW W2 mem2) x) ->
  pj_agreeR SEGS (rdW W mem) (rdW W2 mem2) X.
Proof.
intros W W2 mem mem2 X HA HW x Hx. split; [exact (mbyte_of_aview SEGS (w_H W) (w_H W2) mem mem2 x (HA x Hx)) | exact (HW x Hx)].
Qed.

Lemma pjs_agree_trans : forall m0 m1 m2 (X : Z -> Prop),
  pj_agreeR SEGS m0 m1 X -> pj_agreeR SEGS m1 m2 X -> pj_agreeR SEGS m0 m2 X.
Proof.
intros m0 m1 m2 X H1 H2 x Hx. destruct (H1 x Hx) as [E1 W1]. destruct (H2 x Hx) as [E2 W2].
split; [rewrite E2; exact E1 | intros Hw; exact (W2 (W1 Hw))].
Qed.

(* the bytes of a block live at both states and outside the callee's footprint *)
Lemma pjs_blk_bytes : forall ly S Hp W mem md STK1 sp FP1 ly2 S2 Hp2 W2 mem2 md2 k1 b m x,
  AJ STK1 sp FP1 ly S Hp W mem md [] ly2 S2 Hp2 W2 mem2 md2 k1 ->
  In (b, m) (ablocks B ly S) -> In (b, m) (ablocks B ly2 S2) -> b <= x < b + req_size m -> ~ inFP FP1 x ->
  aview SEGS (w_H W2) mem2 x = aview SEGS (w_H W) mem x.
Proof.
intros ly S Hp W mem md STK1 sp FP1 ly2 S2 Hp2 W2 mem2 md2 k1 b m x HJ H1 H2 Hx Hf.
pose proof (ajxR_blk HJ) as F2.
replace x with (b + (x - b)) by lia. apply (F2 b m (x - b) H1 H2); [lia|]. replace (b + (x - b)) with x by lia. exact Hf.
Qed.

(* the bytes of a harness block of both ledgers *)
Lemma pjs_lam_bytes : forall ly S Hp W mem md STK1 sp FP1 ly2 S2 Hp2 W2 mem2 md2 k1
    Lam peak cnt fail ran most own Lam2 peak2 cnt2 fail2 ran2 most2 own2 a k x,
  AJ STK1 sp FP1 ly S Hp W mem md [] ly2 S2 Hp2 W2 mem2 md2 k1 ->
  prh_ledger (PA := PA) B ly S Hp W mem Lam peak cnt fail ran most own ->
  prh_ledger (PA := PA) B ly2 S2 Hp2 W2 mem2 Lam2 peak2 cnt2 fail2 ran2 most2 own2 ->
  In (a, k) Lam -> In (a, k) Lam2 -> a <= x < a + k -> ~ inFP FP1 x ->
  aview SEGS (w_H W2) mem2 x = aview SEGS (w_H W) mem x.
Proof.
intros ly S Hp W mem md STK1 sp FP1 ly2 S2 Hp2 W2 mem2 md2 k1 Lam peak cnt fail ran most own Lam2 peak2 cnt2 fail2 ran2 most2 own2 a k x
  HJ HL HL2 Hin Hin2 Hx Hf.
pose proof (@cf_head_nonneg cp) as Hh0.
pose proof HL as (_ & _ & HLF & _). pose proof HL2 as (_ & _ & HLF2 & _).
pose proof (proj1 (Forall_forall _ _) HLF (a, k) Hin) as (Hk0 & Hab & _).
pose proof (proj1 (Forall_forall _ _) HLF2 (a, k) Hin2) as (_ & Hab2 & _). cbn [fst snd] in Hk0, Hab, Hab2.
pose proof (pjs_req (k + @cf_head cp) ltac:(lia)) as (Rq & _).
exact (pjs_blk_bytes ly S Hp W mem md STK1 sp FP1 ly2 S2 Hp2 W2 mem2 md2 k1 _ _ x HJ Hab Hab2 ltac:(lia) Hf).
Qed.

(* the bytes of a struct placed as prhReader_at says, when its block (if any) lives on and the callee's stack window
   lies below the caller's *)
Lemma pjs_at_bytes : forall ly S Hp W mem md STK1 sp FP1 ly2 S2 Hp2 W2 mem2 md2 k1
    Lam peak cnt fail ran most own (regs : bvmap 5 word) e p,
  AJ STK1 sp FP1 ly S Hp W mem md [] ly2 S2 Hp2 W2 mem2 md2 k1 ->
  prh_ledger (PA := PA) B ly S Hp W mem Lam peak cnt fail ran most own ->
  sp <= spZ regs -> spZ regs + e < 2 ^ 64 ->
  (forall b m, In (b, m) (ablocks B ly S) -> b <= p -> p + 56 <= b + m -> In (b, m) (ablocks B ly2 S2)) ->
  prhReader_at B ly S Lam regs e p 56 ->
  forall x, p <= x < p + 56 -> ~ inFP FP1 x -> aview SEGS (w_H W2) mem2 x = aview SEGS (w_H W) mem x.
Proof.
intros ly S Hp W mem md STK1 sp FP1 ly2 S2 Hp2 W2 mem2 md2 k1 Lam peak cnt fail ran most own regs e p HJ HL Hsp He HSB Hat x Hx Hf.
pose proof (@cf_head_nonneg cp) as Hh0.
pose proof (ajxR_hi HJ) as F1. pose proof (ajxR_blk HJ) as F2. pose proof (ajxR_frm HJ) as F4. pose proof (ajxR_stk HJ) as Hast.
pose proof Hast as (_ & HS0 & Hceil & Hslo & _ & _ & _ & _ & _).
destruct Hat as [(a & k & Hin & H1 & H2) | [(b & m & Hbm & _ & H1 & H2) | [(cid & pos & Hcp & H1 & H2) | (H1 & H2)]]].
- pose proof HL as (_ & _ & HLF & _).
  pose proof (proj1 (Forall_forall _ _) HLF (a, k) Hin) as (Hk0 & Hab & _). cbn [fst snd] in Hk0, Hab.
  pose proof (pjs_req (k + @cf_head cp) ltac:(lia)) as (Rq & _).
  exact (pjs_blk_bytes ly S Hp W mem md STK1 sp FP1 ly2 S2 Hp2 W2 mem2 md2 k1 _ _ x HJ Hab
    (HSB _ _ Hab ltac:(lia) ltac:(lia)) ltac:(lia) Hf).
- pose proof (pjs_req m ltac:(lia)) as (Rm & _).
  exact (pjs_blk_bytes ly S Hp W mem md STK1 sp FP1 ly2 S2 Hp2 W2 mem2 md2 k1 _ _ x HJ Hbm
    (HSB _ _ Hbm H1 H2) ltac:(lia) Hf).
- apply (F4 cid pos x Hcp); [left; unfold in_zr, frame_rng; cbn [fst snd]; lia | exact Hf].
- apply F1; lia.
Qed.

(* ---- the PLACEMENT of a struct across a call (pjs_place, pj_set_defs.v) ---- *)
Lemma pjs_place_kept : forall dd en ly S Hp W mem md Lam peak cnt fail ran most own
    STK1 sp FP1 ly2 S2 Hp2 W2 mem2 md2 k1 Lam2 peak2 cnt2 fail2 ran2 most2 own2 p,
  ARx ly S Hp W mem md ->
  AJ STK1 sp FP1 ly S Hp W mem md [] ly2 S2 Hp2 W2 mem2 md2 k1 ->
  prh_ledger (PA := PA) B ly S Hp W mem Lam peak cnt fail ran most own ->
  prh_ledger (PA := PA) B ly2 S2 Hp2 W2 mem2 Lam2 peak2 cnt2 fail2 ran2 most2 own2 ->
  (forall x, inFP FP1 x -> x < kLowShadowBeg \/ kHighMemBeg <= x) ->
  ly_stk_lo ly <= js_sp0 en -> js_sp0 en + js_d en <= ly_stk_hi ly ->
  (forall x, js_sp0 en <= x < js_sp0 en + js_d en -> apresent (w_H W2) mem2 x) ->
  (forall a k, In (a, k) Lam -> a <= p -> p + 56 <= a + k -> In (a, k) Lam2) ->
  (forall b m, In (b, m) (ablocks B ly S) -> ~ In (b + cf_head, m - cf_head) Lam -> b <= p -> p + 56 <= b + m ->
     In (b, m) (ablocks B ly2 S2) /\ ~ In (b + cf_head, m - cf_head) Lam2) ->
  pjs_place B dd en ly S Lam W mem p ->
  pjs_place B dd en ly2 S2 Lam2 W2 mem2 p.
Proof.
intros dd en ly S Hp W mem md Lam peak cnt fail ran most own STK1 sp FP1 ly2 S2 Hp2 W2 mem2 md2 k1 Lam2 peak2 cnt2 fail2 ran2 most2 own2 p
  HAR HJ HL HL2 HFPs Hslo Hshi HPR HS1 HS2 (H4096 & Hat & Hrw & Hamr & Hown & Hra).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5). pose proof (@cf_head_nonneg cp) as Hh0.
pose proof (ajxR_ar HJ) as HAR2. pose proof (ajxR_ly HJ) as Hly. pose proof (ajxR_frs HJ) as Hfr. pose proof (ajxR_frm HJ) as F4.
assert (Efa : forall cid pos, frame_addr ly2 cid pos = frame_addr ly cid pos).
{ intros cid pos. unfold frame_addr. destruct Hly as (_ & _ & _ & _ & _ & EF & _). rewrite EF. reflexivity. }
pose proof Hly as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Eslo & Eshi & _).
rewrite app_nil_l in Hfr.
pose proof HL2 as (_ & _ & HLF2 & _).
destruct Hrw as (Hal8 & _).
destruct Hat as [(a & k & Hin & Ha1 & Ha2) | [(b & m & Hbm & HnL & Hb1 & Hb2) | [(cid & pos & Hcp & Hf1 & Hf2) | (Hs1 & Hs2)]]].
- (* a harness block of the ledger *)
  pose proof (HS1 a k Hin Ha1 Ha2) as Hin2.
  pose proof (proj1 (Forall_forall _ _) HLF2 (a, k) Hin2) as (Hk0 & Hab2 & _). cbn [fst snd] in Hk0, Hab2.
  destruct (alx_blocks SEGS B ARx LAWS ly2 S2 Hp2 W2 mem2 md2 _ _ HAR2 Hab2) as (_ & _ & _ & _ & Hbpo & _).
  pose proof (pjs_req (k + @cf_head cp) ltac:(lia)) as (Rq1 & _).
  split; [exact H4096|].
  split; [left; exists a, k; split; [exact Hin2 | lia]|].
  split; [split; [exact Hal8 | intros x Hx; exact (apresent_writable SEGS _ _ x (proj1 (Hbpo x ltac:(lia))))]|].
  split; [exact Hamr|].
  split; [intros x Hx; split; [exact (proj2 (Hbpo x ltac:(lia))) | exact (proj2 (Hown x Hx))]|].
  exact (proj1 (pjs_vis_lam ly2 S2 Hp2 W2 mem2 md2 Lam2 peak2 cnt2 fail2 ran2 most2 own2 a k p 56 HAR2 HL2 Hin2 Ha1 Ha2 ltac:(lia))).
- (* a live allocator block that is no harness block *)
  destruct (HS2 b m Hbm HnL Hb1 Hb2) as (Hbm2 & HnL2).
  destruct (alx_blocks SEGS B ARx LAWS ly2 S2 Hp2 W2 mem2 md2 _ _ HAR2 Hbm2) as (_ & _ & _ & _ & Hbpo & _).
  pose proof (pjs_req m ltac:(lia)) as (Rm1 & _).
  split; [exact H4096|].
  split; [right; left; exists b, m; split; [exact Hbm2 | split; [exact HnL2 | lia]]|].
  split; [split; [exact Hal8 | intros x Hx; exact (apresent_writable SEGS _ _ x (proj1 (Hbpo x ltac:(lia))))]|].
  split; [exact Hamr|].
  split; [intros x Hx; split; [exact (proj2 (Hbpo x ltac:(lia))) | exact (proj2 (Hown x Hx))]|].
  exact (proj1 (pjs_vis_blk ly2 S2 Hp2 W2 mem2 md2 Lam2 peak2 cnt2 fail2 ran2 most2 own2 b m p 56 HAR2 HL2 Hbm2 HnL2 Hb1 Hb2 ltac:(lia))).
- (* a live fake frame *)
  assert (Hcp2 : In (cid, pos) (frames S2)) by (rewrite Hfr; exact Hcp).
  destruct (alx_frames SEGS B ARx LAWS ly2 S2 Hp2 W2 mem2 md2 cid pos HAR2 Hcp2) as (_ & _ & Hfpo & _).
  rewrite Efa in Hfpo.
  destruct (frames_bounds_x SEGS B ARx LAWS ly S Hp W mem md cid pos HAR Hcp) as (Hf0 & Hfc & Hfapp).
  destruct (alx_frames SEGS B ARx LAWS ly S Hp W mem md cid pos HAR Hcp) as (Hfal & _).
  split; [exact H4096|].
  split; [right; right; left; exists cid, pos; rewrite Efa; split; [exact Hcp2 | lia]|].
  split; [split; [exact Hal8 | intros x Hx; exact (apresent_writable SEGS _ _ x (proj1 (Hfpo x ltac:(lia))))]|].
  split; [exact Hamr|].
  split; [intros x Hx; split; [exact (proj2 (Hfpo x ltac:(lia))) | exact (proj2 (Hown x Hx))]|].
  eapply range_addressable_agree; [|exact Hra]. intros x Hx.
  apply (F4 cid pos); [exact Hcp | right | ].
  + unfold in_zr, shadow_of_addr, shadow_addr. cbn [fst snd].
    assert (Hx8 : x / 8 < p / 8 + 7).
    { apply Z.div_lt_upper_bound; [lia|]. pose proof (Z.div_mod p 8 ltac:(lia)). lia. }
    assert (Ho8 : frame_addr ly cid pos / 8 <= p / 8) by (apply Z.div_le_mono; lia).
    assert (He8 : p / 8 + 7 <= (frame_addr ly cid pos + fs_frame_bytes cid) / 8).
    { apply Z.div_le_lower_bound; [lia|]. pose proof (Z.div_mod p 8 ltac:(lia)). lia. }
    assert (Hs8 : (frame_addr ly cid pos + fs_frame_bytes cid) / 8 = frame_addr ly cid pos / 8 + fs_frame_bytes cid / 8).
    { rewrite (Z.div_mod (frame_addr ly cid pos) 8) at 1 by lia.
      replace (frame_addr ly cid pos mod 8) with 0 by lia.
      replace (8 * (frame_addr ly cid pos / 8) + 0 + fs_frame_bytes cid) with
        (fs_frame_bytes cid + (frame_addr ly cid pos / 8) * 8) by lia.
      rewrite Z.div_add by lia. lia. }
    assert (Hx0 : p / 8 <= x / 8) by (apply Z.div_le_mono; lia).
    lia.
  + intros Hin. pose proof (pjs_shadow_reg x ltac:(lia)) as Hsr. destruct (HFPs _ Hin) as [Hc | Hc]; lia.
- (* the caller's window on the real stack *)
  unfold js_sp0 in *.
  split; [exact H4096|].
  split; [right; right; right; split; [exact Hs1 | exact Hs2]|].
  split; [split; [exact Hal8 | intros x Hx; exact (apresent_writable SEGS _ _ x (HPR x ltac:(lia)))]|].
  split; [exact Hamr|].
  split; [intros x Hx; split; [apply (alx_stack SEGS B ARx LAWS ly2 S2 Hp2 W2 mem2 md2 x HAR2); rewrite Eslo, Eshi; lia
                              | exact (proj2 (Hown x Hx))]|].
  apply (pjs_vis_stk ly2 S2 Hp2 W2 mem2 md2 p 56 HAR2); rewrite ?Eslo, ?Eshi; lia.
Qed.

(* a full slot from a placement and a hull *)
Lemma pjs_slot_of_place : forall dd en ly S Lam W mem p,
  pjs_place B dd en ly S Lam W mem p -> shadow_hull_vis (aview SEGS (w_H W) mem) p 56 ->
  prhPj_slot (PA := PA) B (STK_pj_set dd) (js_d en) ly S Lam W (js_regs en) mem p.
Proof.
intros dd en ly S Lam W mem p (H1 & H2 & H3 & H4 & H5 & H6) H7.
split; [exact H1|]. split; [exact H2|]. split; [exact H3|]. split; [exact H4|]. split; [exact H5|]. split; [exact H6 | exact H7].
Qed.

Lemma pjs_place_of_slot : forall dd en ly S Lam W mem p,
  prhPj_slot (PA := PA) B (STK_pj_set dd) (js_d en) ly S Lam W (js_regs en) mem p -> pjs_place B dd en ly S Lam W mem p.
Proof.
intros dd en ly S Lam W mem p (H1 & H2 & H3 & H4 & H5 & H6 & _).
split; [exact H1|]. split; [exact H2|]. split; [exact H3|]. split; [exact H4|]. split; [exact H5 | exact H6].
Qed.

(* ---- the KEY across a call: cstr_ok and kept_at (pjp_text_kept's three kept_at cases) ---- *)
Lemma pjs_cstr_kept : forall ly S Hp W mem md Lam peak cnt fail ran most own STK1 sp FP1 ly2 S2 Hp2 W2 mem2 md2 k1
    Lam2 peak2 cnt2 fail2 ran2 most2 own2 p (l : list Z),
  ARx ly S Hp W mem md ->
  AJ STK1 sp FP1 ly S Hp W mem md [] ly2 S2 Hp2 W2 mem2 md2 k1 ->
  prh_ledger (PA := PA) B ly S Hp W mem Lam peak cnt fail ran most own ->
  prh_ledger (PA := PA) B ly2 S2 Hp2 W2 mem2 Lam2 peak2 cnt2 fail2 ran2 most2 own2 ->
  ~ YI16.sink_open_fp FP1 ->
  (forall x, p <= x < p + Z.of_nat (length l) + 1 -> ~ inFP FP1 x) ->
  (forall a k, In (a, k) Lam -> a <= p -> p + Z.of_nat (length l) + 1 <= a + k -> In (a, k) Lam2) ->
  ((exists b m, In (b, m) Lam /\ b <= p /\ p + Z.of_nat (length l) + 1 <= b + m) \/
   (forall a, p + Z.of_nat (length l) < a < p + Z.of_nat (length l) - (p + Z.of_nat (length l)) mod 8 + 8 ->
      aview SEGS (w_H W2) mem2 a <> None)) ->
  cstr_ok (PA := PA) W mem p l -> kept_at (PA := PA) B Lam p (Z.of_nat (length l) + 1) ->
  cstr_ok (PA := PA) W2 mem2 p l /\ kept_at (PA := PA) B Lam2 p (Z.of_nat (length l) + 1).
Proof.
intros ly S Hp W mem md Lam peak cnt fail ran most own STK1 sp FP1 ly2 S2 Hp2 W2 mem2 md2 k1 Lam2 peak2 cnt2 fail2 ran2 most2 own2 p l
  HAR HJ HL HL2 Hsink HFP HS1 HTL ((Hby & Hnz) & H4096 & Hceil & Hlen & Hamr8 & _ & _ & _) Hkept.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5). pose proof (@cf_head_nonneg cp) as Hh0.
pose proof (ajxR_ar HJ) as HAR2. pose proof (ajxR_img HJ) as F3.
pose proof HL as (_ & _ & HLF & _). pose proof HL2 as (_ & _ & HLF2 & _).
set (n := Z.of_nat (length l) + 1) in *.
assert (En : n = Z.of_nat (length l) + 1) by reflexivity. clearbody n.
(* a harness block holding the key, at both states *)
assert (HBLK : forall b m, In (b, m) Lam -> b <= p -> p + n <= b + m ->
  In (b, m) Lam2 /\ (forall x, b <= x < b + m -> ~ inFP FP1 x -> aview SEGS (w_H W2) mem2 x = aview SEGS (w_H W) mem x) /\
  (forall x, b <= x < b + m -> aview SEGS (w_H W2) mem2 x <> None) /\
  (forall x, b + m <= x < (b + m + 7) / 8 * 8 -> aview SEGS (w_H W2) mem2 x <> None)).
{ intros b m Hin H1 H2. pose proof (HS1 b m Hin H1 ltac:(lia)) as Hin2.
  pose proof (proj1 (Forall_forall _ _) HLF2 (b, m) Hin2) as (Hm0 & Hab2 & _). cbn [fst snd] in Hm0, Hab2.
  pose proof (pjs_req (m + @cf_head cp) ltac:(lia)) as (_ & _ & Rq). specialize (Rq ltac:(lia)).
  destruct (alx_blocks SEGS B ARx LAWS ly2 S2 Hp2 W2 mem2 md2 _ _ HAR2 Hab2) as (_ & _ & _ & _ & Hbpo & _).
  rewrite Rq in Hbpo.
  split; [exact Hin2|].
  split; [intros x Hx Hf; exact (pjs_lam_bytes ly S Hp W mem md STK1 sp FP1 ly2 S2 Hp2 W2 mem2 md2 k1
            Lam peak cnt fail ran most own Lam2 peak2 cnt2 fail2 ran2 most2 own2 b m x HJ HL HL2 Hin Hin2 Hx Hf)|].
  split; [intros x Hx; exact (aview_some_of_apresent SEGS _ _ x (proj1 (Hbpo x ltac:(lia))))|].
  intros x Hx. apply (alx_blocks_tail SEGS B ARx LAWS ly2 S2 Hp2 W2 mem2 md2 _ _ x HAR2 Hab2).
  rewrite Rq. replace (b - cf_head + (m + cf_head)) with (b + m) by lia. exact Hx. }
(* the bytes of the string, the view at the trailing granule, and the shadow facts, by kept_at's case *)
assert (HK : (forall x, p <= x < p + n -> aview SEGS (w_H W2) mem2 x = aview SEGS (w_H W) mem x) /\
  range_addressable (aview SEGS (w_H W2) mem2) SHADOW_OFF p n /\
  shadow_hull_vis (aview SEGS (w_H W2) mem2) p n /\
  kept_at (PA := PA) B Lam2 p n).
{ destruct Hkept as [(b & m & Hin & Hb & Hm) | [(Hzs & Hlo & Hhi & Hro) | (Hlo & Hhi & Hro)]].
  - destruct (HBLK b m Hin Hb Hm) as (Hin2 & Hkb & _ & _).
    destruct (pjs_vis_lam ly2 S2 Hp2 W2 mem2 md2 Lam2 peak2 cnt2 fail2 ran2 most2 own2 b m p n HAR2 HL2 Hin2 Hb Hm ltac:(lia))
      as [Hra2 Hh2].
    split; [intros x Hx; exact (Hkb x ltac:(lia) (HFP x ltac:(lia)))|].
    split; [exact Hra2|]. split; [exact Hh2|]. left. exists b, m. split; [exact Hin2 | split; [exact Hb | exact Hm]].
  - destruct VIS as (_ & VZ & _).
    split; [intros x Hx; destruct (Hro x Hx) as (Hr & Hno & Her);
            apply F3; [exact (pjs_ro_img x Hr) | exact Hno | exact Her | exact (fun Hx' => pst_not_ro_B x Hx' Hr)
                      | apply fp_spares_closed; exact Hsink]|].
    split; [exact (proj1 (VZ ly2 S2 Hp2 W2 mem2 md2 p n HAR2 Hzs ltac:(lia)))|].
    split; [exact (proj2 (VZ ly2 S2 Hp2 W2 mem2 md2 p n HAR2 Hzs ltac:(lia)))|].
    right. left. split; [exact Hzs | split; [exact Hlo | split; [exact Hhi | exact Hro]]].
  - destruct VIS as (_ & VZ & VI).
    split; [intros x Hx; destruct (Hro x Hx) as (Hr & Hno & Her & _);
            apply F3; [exact (pjs_ro_img x Hr) | exact Hno | exact Her | exact (fun Hx' => pst_not_ro_B x Hx' Hr)
                      | apply fp_spares_closed; exact Hsink]|].
    split.
    { intros x Hx. destruct (Hro x Hx) as (_ & _ & _ & [Hzs8 | (v & Hcell & Hv)]).
      - exact (proj1 (VZ ly2 S2 Hp2 W2 mem2 md2 (x - x mod 8) 8 HAR2 Hzs8 ltac:(lia)) x ltac:(lia)).
      - pose proof (proj1 (Forall_forall _ _) (alx_const_cells SEGS B ARx LAWS ly2 S2 Hp2 W2 mem2 md2 HAR2) _ (Hcell ly2)) as Hc.
        specialize (Hc 0%nat ltac:(cbn; lia)). cbn [aeval c_at c_val c_w z1 c1 Z.of_nat] in Hc.
        exists v. split; [|exact Hv].
        unfold shadow_of_addr. unfold shadow_addr in Hc. rewrite Z.add_0_r in Hc. rewrite Hc. f_equal.
        unfold le_byte. cbn [Z.of_nat Z.mul]. rewrite Z.shiftr_0_r.
        destruct Hv as [-> | Hv]; [reflexivity|]. rewrite !Z.mod_small; lia. }
    split.
    { intros s Hs. destruct (pjs_hull_img p n s ltac:(lia) Hlo Hhi Hs) as [E Hr]. rewrite E.
      exact (VI ly2 S2 Hp2 W2 mem2 md2 _ HAR2 Hr). }
    right. right. split; [exact Hlo | split; [exact Hhi | exact Hro]]. }
destruct HK as (Hkv & Hra2 & Hhull2 & Hkept2). subst n.
split; [|exact Hkept2].
split.
- split; [|exact Hnz].
  apply (pjs_garr8_move W W2 mem mem2 p (l ++ [0]) Hby). intros j Hj. rewrite length_app in Hj. cbn [length] in Hj.
  apply Hkv. lia.
- split; [exact H4096|]. split; [exact Hceil|]. split; [exact Hlen|]. split; [exact Hamr8|].
  split; [exact Hra2|]. split; [exact Hhull2|].
  intros a Ha. destruct HTL as [(b & m & Hin & Hb & Hm) | HT2]; [|exact (HT2 a Ha)].
  destruct (HBLK b m Hin Hb ltac:(lia)) as (_ & _ & Hin3 & Htail).
  destruct (Z_lt_le_dec a (b + m)) as [Hlt | Hge]; [apply Hin3; lia|].
  apply Htail. split; [exact Hge|].
  pose proof (Z.div_mod (p + Z.of_nat (length l)) 8 ltac:(lia)) as D1.
  pose proof (Z.mod_pos_bound (p + Z.of_nat (length l)) 8 ltac:(lia)) as M1.
  pose proof (Z.div_mod (b + m + 7) 8 ltac:(lia)) as D2.
  pose proof (Z.mod_pos_bound (b + m + 7) 8 ltac:(lia)) as M2.
  assert (Hq : (p + Z.of_nat (length l)) / 8 <= (b + m + 7) / 8 - 1).
  { assert (Hq0 : (p + Z.of_nat (length l)) / 8 < (b + m + 7) / 8) by (apply Z.div_lt_upper_bound; lia). lia. }
  lia.
Qed.

(* the key across a call, the trailing granule discharged by kept_at's case: a harness block (its block and tail
   laws) or an image string (the ROM, pjs_img_view) *)
Lemma pjs_key_kept : forall ly S Hp W mem md Lam peak cnt fail ran most own STK1 sp FP1 ly2 S2 Hp2 W2 mem2 md2 k1
    Lam2 peak2 cnt2 fail2 ran2 most2 own2 p (l : list Z),
  ARx ly S Hp W mem md ->
  AJ STK1 sp FP1 ly S Hp W mem md [] ly2 S2 Hp2 W2 mem2 md2 k1 ->
  prh_ledger (PA := PA) B ly S Hp W mem Lam peak cnt fail ran most own ->
  prh_ledger (PA := PA) B ly2 S2 Hp2 W2 mem2 Lam2 peak2 cnt2 fail2 ran2 most2 own2 ->
  ~ YI16.sink_open_fp FP1 ->
  (forall x, p <= x < p + Z.of_nat (length l) + 1 -> ~ inFP FP1 x) ->
  (forall a k, In (a, k) Lam -> a <= p -> p + Z.of_nat (length l) + 1 <= a + k -> In (a, k) Lam2) ->
  cstr_ok (PA := PA) W mem p l -> kept_at (PA := PA) B Lam p (Z.of_nat (length l) + 1) ->
  cstr_ok (PA := PA) W2 mem2 p l /\ kept_at (PA := PA) B Lam2 p (Z.of_nat (length l) + 1).
Proof.
intros ly S Hp W mem md Lam peak cnt fail ran most own STK1 sp FP1 ly2 S2 Hp2 W2 mem2 md2 k1 Lam2 peak2 cnt2 fail2 ran2 most2 own2 p l
  HAR HJ HL HL2 Hsink HFP HS1 Hcs Hkept.
apply (pjs_cstr_kept ly S Hp W mem md Lam peak cnt fail ran most own STK1 sp FP1 ly2 S2 Hp2 W2 mem2 md2 k1
  Lam2 peak2 cnt2 fail2 ran2 most2 own2 p l HAR HJ HL HL2 Hsink HFP HS1); [|exact Hcs | exact Hkept].
destruct Hkept as [(b & m & Hin & Hb & Hm) | [(_ & Hlo & Hhi & _) | (Hlo & Hhi & _)]].
- left. exists b, m. split; [exact Hin | split; [exact Hb | lia]].
- right. intros a Ha. apply pjs_img_view.
  change (@pa_lo _ _ PA) with IMG_LO_B in Hlo. change (@pa_hi _ _ PA) with IMG_TOP_B in Hhi.
  pose proof (Z.mod_pos_bound (p + Z.of_nat (length l)) 8 ltac:(lia)). lia.
- right. intros a Ha. apply pjs_img_view.
  change (@pa_lo _ _ PA) with IMG_LO_B in Hlo. change (@pa_hi _ _ PA) with IMG_TOP_B in Hhi.
  pose proof (Z.mod_pos_bound (p + Z.of_nat (length l)) 8 ltac:(lia)). lia.
Qed.

(* ---- a TREE across a call: its header where prhReader_at places it, its blocks harness blocks of both ledgers,
   its footprint outside the callee's (pj_set_trans.v pjst_node_frame, the block predicate moving to Lam2) ---- *)
Lemma pjs_tree_kept : forall ly S Hp W mem md Lam peak cnt fail ran most own STK1 sp FP1 ly2 S2 Hp2 W2 mem2 md2 k1
    Lam2 peak2 cnt2 fail2 ran2 most2 own2 (regs : bvmap 5 word) e p t D,
  AJ STK1 sp FP1 ly S Hp W mem md [] ly2 S2 Hp2 W2 mem2 md2 k1 ->
  prh_ledger (PA := PA) B ly S Hp W mem Lam peak cnt fail ran most own ->
  prh_ledger (PA := PA) B ly2 S2 Hp2 W2 mem2 Lam2 peak2 cnt2 fail2 ran2 most2 own2 ->
  sp <= spZ regs -> spZ regs + e < 2 ^ 64 ->
  (forall b m, In (b, m) (ablocks B ly S) -> b <= p -> p + 56 <= b + m -> In (b, m) (ablocks B ly2 S2)) ->
  prhReader_at B ly S Lam regs e p 56 ->
  pj_rwR SEGS (rdW W2 mem2) p ->
  (forall a k, In (a, k) D -> In (a, k) Lam2) ->
  (forall x, pj_footR p D x -> ~ inFP FP1 x) ->
  pj_nodeR SEGS (rdW W mem) (prh_lin Lam) p t D ->
  pj_nodeR SEGS (rdW W2 mem2) (prh_lin Lam2) p t D.
Proof.
intros ly S Hp W mem md Lam peak cnt fail ran most own STK1 sp FP1 ly2 S2 Hp2 W2 mem2 md2 k1 Lam2 peak2 cnt2 fail2 ran2 most2 own2 regs e p t D
  HJ HL HL2 Hsp He HSB Hat Hrw2 HDL2 HFP HN.
pose proof (@cf_head_nonneg cp) as Hh0.
pose proof (ajxR_ar HJ) as HAR2.
pose proof HL2 as (_ & _ & HLF2 & _).
apply (pjst_node_frame SEGS t (rdW W mem) (rdW W2 mem2) (prh_lin Lam) (prh_lin Lam2) p D HN); [|exact HDL2].
apply pjs_agree.
- intros x [Hx | ((a, k) & Hb & Hx)].
  + exact (pjs_at_bytes ly S Hp W mem md STK1 sp FP1 ly2 S2 Hp2 W2 mem2 md2 k1 Lam peak cnt fail ran most own regs e p
      HJ HL Hsp He HSB Hat x Hx (HFP x (or_introl Hx))).
  + pose proof (pjst_node_lblk SEGS t _ _ p D HN a k Hb) as HinL. unfold prh_lin in HinL.
    unfold pj_holdsR in Hx. cbn [fst snd] in Hx.
    exact (pjs_lam_bytes ly S Hp W mem md STK1 sp FP1 ly2 S2 Hp2 W2 mem2 md2 k1 Lam peak cnt fail ran most own
      Lam2 peak2 cnt2 fail2 ran2 most2 own2 a k x HJ HL HL2 HinL (HDL2 a k Hb) Hx
      (HFP x (or_intror (ex_intro _ (a, k) (conj Hb Hx))))).
- intros x [Hx | ((a, k) & Hb & Hx)] _.
  + exact (proj2 Hrw2 x Hx).
  + unfold pj_holdsR in Hx. cbn [fst snd] in Hx.
    pose proof (proj1 (Forall_forall _ _) HLF2 (a, k) (HDL2 a k Hb)) as (Hk0 & Hab2 & _). cbn [fst snd] in Hk0, Hab2.
    pose proof (pjs_req (k + @cf_head cp) ltac:(lia)) as (Rq & _).
    exact (pjs_blk_writable ly2 S2 Hp2 W2 mem2 md2 _ _ x HAR2 Hab2 ltac:(lia)).
Qed.

(* ---- pjs_data_c across a call: the object's placement, val's slot, the key ---- *)
Lemma pjs_datac_kept : forall dd en ly S Hp W mem md Lam peak cnt fail ran most own
    STK1 sp FP1 ly2 S2 Hp2 W2 mem2 md2 k1 Lam2 peak2 cnt2 fail2 ran2 most2 own2,
  ARx ly S Hp W mem md ->
  AJ STK1 sp FP1 ly S Hp W mem md [] ly2 S2 Hp2 W2 mem2 md2 k1 ->
  prh_ledger (PA := PA) B ly S Hp W mem Lam peak cnt fail ran most own ->
  prh_ledger (PA := PA) B ly2 S2 Hp2 W2 mem2 Lam2 peak2 cnt2 fail2 ran2 most2 own2 ->
  (forall x, inFP FP1 x -> x < kLowShadowBeg \/ kHighMemBeg <= x) -> ~ YI16.sink_open_fp FP1 ->
  (forall x, js_k en <= x < js_k en + js_klen en + 1 -> ~ inFP FP1 x) ->
  ly_stk_lo ly <= js_sp0 en -> js_sp0 en + js_d en <= ly_stk_hi ly ->
  (forall x, js_sp0 en <= x < js_sp0 en + js_d en -> apresent (w_H W2) mem2 x) ->
  js_w en < js_sp0 en ->
  (forall a k p, p = js_o en \/ p = js_w en -> In (a, k) Lam -> a <= p -> p + 56 <= a + k -> In (a, k) Lam2) ->
  (forall b m p, p = js_o en \/ p = js_w en -> In (b, m) (ablocks B ly S) -> ~ In (b + cf_head, m - cf_head) Lam ->
     b <= p -> p + 56 <= b + m -> In (b, m) (ablocks B ly2 S2) /\ ~ In (b + cf_head, m - cf_head) Lam2) ->
  (forall a k, In (a, k) Lam -> a <= js_k en -> js_k en + js_klen en + 1 <= a + k -> In (a, k) Lam2) ->
  room_live_cf S2 ->
  pjs_data_c B dd en ly S Lam W mem ->
  pjs_data_c B dd en ly2 S2 Lam2 W2 mem2.
Proof.
intros dd en ly S Hp W mem md Lam peak cnt fail ran most own STK1 sp FP1 ly2 S2 Hp2 W2 mem2 md2 k1 Lam2 peak2 cnt2 fail2 ran2 most2 own2
  HAR HJ HL HL2 HFPs Hsink HFPk Hslo Hshi HPR Hwlt HSL HSB HSK HR2 (_ & Ho & Hw & Hcs & Hka).
pose proof (ajxR_ar HJ) as HAR2.
pose proof (pjs_place_of_slot dd en ly S Lam W mem (js_w en) Hw) as Pw.
pose proof (pjs_place_kept dd en ly S Hp W mem md Lam peak cnt fail ran most own STK1 sp FP1 ly2 S2 Hp2 W2 mem2 md2 k1
  Lam2 peak2 cnt2 fail2 ran2 most2 own2 (js_w en) HAR HJ HL HL2 HFPs Hslo Hshi HPR
  (fun a k => HSL a k (js_w en) (or_intror eq_refl)) (fun b m => HSB b m (js_w en) (or_intror eq_refl)) Pw) as Pw2.
split; [exact HR2|].
split; [exact (pjs_place_kept dd en ly S Hp W mem md Lam peak cnt fail ran most own STK1 sp FP1 ly2 S2 Hp2 W2 mem2 md2 k1
  Lam2 peak2 cnt2 fail2 ran2 most2 own2 (js_o en) HAR HJ HL HL2 HFPs Hslo Hshi HPR
  (fun a k => HSL a k (js_o en) (or_introl eq_refl)) (fun b m => HSB b m (js_o en) (or_introl eq_refl)) Ho)|].
split.
{ apply (pjs_slot_of_place dd en ly2 S2 Lam2 W2 mem2 (js_w en) Pw2).
  destruct Pw2 as (_ & Hat2 & _).
  apply (pjs_hull_low ly2 S2 Hp2 W2 mem2 md2 Lam2 peak2 cnt2 fail2 ran2 most2 own2 (js_regs en) (js_d en) (js_w en) HAR2 HL2 Hat2).
  unfold js_sp0 in Hwlt. exact Hwlt. }
unfold js_klen in *.
exact (pjs_key_kept ly S Hp W mem md Lam peak cnt fail ran most own STK1 sp FP1 ly2 S2 Hp2 W2 mem2 md2 k1 Lam2 peak2 cnt2 fail2 ran2 most2 own2
  (js_k en) (js_kname en) HAR HJ HL HL2 Hsink HFPk HSK Hcs Hka).
Qed.

End v.
