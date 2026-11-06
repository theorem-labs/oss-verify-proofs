(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Theorem Labs, 2026-10: segment C1 of pj_parse's image-B walk (fuzz_preset asan-ubsan, B 0x862ec; the cuts of
   lib/B/Prog/pj_parse_defs.v): from the cut pjp_C1 at +0x4c (`jal parse_value`) through parse_value's STATED text
   (pjp_texts' first conjunct: lib/A/PRH_FnParse.v tparse_value_specX 0, at the float state fx and the call context
   [[return site]]) and the `bnez a0` at +0x50, to the cuts pjp_C2ok (+0x54, a0 = 0) and pjp_C2ref (+0x68, a0 = -1),
   whose segment statements are hypotheses (lib/B/Prog/pj_parse_defs.v).
   The call: YCbqGcallW.v aj_call_xWF at callee window e1 = 32 (the cursor [sp1 + 8, sp1 + 32) lies in pj_parse's own
   window, fp_sub_x's fourth disjunct; the node out is in pj_parse's FP), o = - (48 + d). After it: pjp_frame_kept_stmt
   for pj_parse's frame, parse_value's post for the outcome, the callee's journal and rd_blocks_move for out's place
   and the text's bytes, and the allocator laws (AR_laws_x at hl := cf_head) with pjp_g_vis for the shadow facts no
   journal clause keeps.
   parse_value's text is the kit f97c8b2f046b's tparse_value_specX (PRH_FnParse.v 105eb463e190) in the form ruled at
   19:08Z (pj_parse_defs.v tparse_value_specX_len0: rd_pre's text-node apartness under 0 < len), in the
   POST-IMPLICATION form: no position and no run premise at entry; its two room counts at the call come from the
   text's two room-count premises (pj_parse_counts.v pjc_pkR_gtrace: parse_value's all-granted events are the first part of
   pj_parse's); after it the cuts carry its position transfer and its live-set move (pjp_pos_pv). The memory
   overlay's normal form at the call is pjp_inv's; after it, parse_value's m-form keep.
   THE RE-HIDING MOVE AND THE HULL: parse_value's text concludes SRr' segs RZ_cf with its post at wle', so the call is
   YCbqGwild.aj_call_xWFbR at wle' SEGS RZ_cf (the cut's journal moved from wle by YCbqG.ajournal_xwR_mono, its frame
   by pj_parse_defs.v pjp_inv_lift) and the segment concludes SRr'; the jal and the bnez are SRr steps, lifted
   (YGcfRhLift.ra_rh_of_SRr). parse_value's hull budget is pj_parse's (pj_parse_counts.v pjc_hull_budget_pv); its hull
   use is the later cuts' (C2ok / C2ref). The callee's premises are met by shape (eassumption over the named facts).
   THE OUTCOME OF AN INJECTED READING: parse_value's conjunct, carried by the later cuts (pjp_inj). parse_value's post
   is read through its kit names (PRH_FnParse.v tpvP_R_of and the tpvP_R fields).
   proves no function (kind: segment lemma).
   Numerals: 48 / 56 / 32 / 24 / 16 / 8 / 4 (LENGTH: frame, node, callee window, cursor, slot offsets, granule,
   instruction); register numbers (WORD); every pc offset is DERIVED (the defs' PJP_*, by vm_compute). No ADDRESS. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn YP0b YP0a.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YN3v YI04 YI00 YG0s YP07 YI16.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG0p YCbqG YCbqGcall YCbqGcallW FCiface YGcallMx.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfNames YGcfRoomKeep YG0dcf YGcfRoomPre.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK0o YGcfFsVis.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YP0d YP0c YC80 YPsym YC4aP YImgTop YC1fP.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YAkMemnorm YCbqGwild.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YA0nH YSRrG.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YGcfRehidePost YGcfRhLift.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PresetHullBudget.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Ledger ReaderRes.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PjTree PjGrammar PjRoundTrip.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PresetReqAt.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_Base PRH_Reader PRH_Charge PRH_FnReader.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_FnPj PRH_FnParse PRH_PjOrder.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B Require Import Img0 Listing_prog PAImg_prog PRH_ImgB.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog Require Import S1ImgB.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog Require Import pj_parse_defs.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog Require pj_parse_counts.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PresetRun PresetRoom PresetLiveBounds.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YGcfRoomLive YGcfRoom.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Set Warnings "-notation-for-abbreviation".
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope bv_scope.
Open Scope Z_scope.
#[local] Existing Instance prh_img_B.

#[local] Notation PA := PI_prog_B.
#[local] Notation PL := PL_prog_B.
#[local] Notation SEGS := (@pa_segs _ B_prog_listing PA).
#[local] Notation VAL := (@pa_val _ B_prog_listing PA).
#[local] Notation SIGMA := (@pa_sigma _ B_prog_listing PA).
#[local] Notation BASE := (@pa_val _ B_prog_listing PA A_TEXT).
#[local] Notation RLO := (@pa_relro_lo _ B_prog_listing PA).
#[local] Notation RHI := (@pa_relro_hi _ B_prog_listing PA).

(* two registers differ (closed bit-vectors) *)
Ltac pjp_regne := let E := fresh "E" in intro E; apply (f_equal bv_unsigned) in E; vm_compute in E; discriminate E.

Section t. Context {rc : YM05.RunCeil}.

(* ---- numbers of the image and the listing (computed; no number typed) ---- *)
Lemma pjp_code_rng : 4096 <= BASE /\ BASE mod 4 = 0 /\ 0 <= PJP_C1 /\ PJP_C1 mod 4 = 0 /\
  BASE + PJP_C1 + 32 < kLowMemEnd /\ PJP_C1 + 32 < 2 ^ 39.
Proof.
assert (H : ((4096 <=? BASE) && (BASE mod 4 =? 0) && (0 <=? PJP_C1) && (PJP_C1 mod 4 =? 0) &&
  (BASE + PJP_C1 + 32 <? kLowMemEnd) && (PJP_C1 + 32 <? 2 ^ 39))%bool = true) by (vm_compute; reflexivity).
rewrite !andb_true_iff in H. destruct H as (((((H1 & H2) & H3) & H4) & H5) & H6).
apply Z.leb_le in H1, H3. apply Z.eqb_eq in H2, H4. apply Z.ltb_lt in H5, H6. lia.
Qed.

Lemma pjp_stk : 0 <= STK_parse_value 0 /\ STK_parse_value 0 + 48 <= STK_pj_parse.
Proof.
assert (H : ((0 <=? STK_parse_value 0) && (STK_parse_value 0 + 48 <=? STK_pj_parse))%bool = true)
  by (vm_compute; reflexivity).
rewrite andb_true_iff in H. destruct H as [H1 H2]. apply Z.leb_le in H1, H2. lia.
Qed.

Lemma pjp_req : forall n, 0 <= n -> n <= req_size n /\ 1 <= req_size n /\ (0 < n -> req_size n = n).
Proof. intros n Hn. unfold req_size. destruct (Z.eqb_spec n 0); lia. Qed.

(* ---- the two instructions of the segment, at any float state ---- *)
(* +0x4c `jal ra, parse_value` (listing slot PCall AS_parse_value, checked by the image certificate pa_cert) *)
Lemma pjp_jal_step : forall (fy : YK11.FPState) regs mem rom,
  RiscvSemantics.step SEGS (@YK11.mkst fy regs (Z_to_bv 64 (BASE + PJP_C1)) mem rom) =
  MachineOk (@YK11.mkst fy (regupd regs 1%bv (Z_to_bv 64 (BASE + (PJP_C1 + 4))))
    (Z_to_bv 64 (SIGMA AS_parse_value)) mem rom).
Proof.
intros fy regs mem rom.
pose proof pjp_code_rng as (R1 & R2 & R3 & R4 & R5 & R6). pose proof (@pa_B_ok _ B_prog_listing PA) as (HB0 & HB1 & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (Hpl : plookup (@pl_tpi B_prog_listing PL) PJP_C1 = Some (PCall AS_parse_value (1%bv : bv 5)))
  by (vm_compute; reflexivity).
rewrite <- (@pl_tpi_eq B_prog_listing PL) in Hpl.
pose proof (cert_slot asym (clookup (@pa_tbl _ B_prog_listing PA)) VAL SIGMA B_prog_listing
  (@pa_cert _ B_prog_listing PA) _ _ Hpl) as (Hck & _ & _).
unfold pi_slot_check in Hck.
destruct (clookup (@pa_tbl _ B_prog_listing PA) (VAL A_TEXT + PJP_C1)) as [wz|] eqn:Hl; [|discriminate Hck].
destruct (decode_any (Z_to_bv 32 wz)) as [[i isz]|] eqn:Hdec; [|discriminate Hck].
apply andb_prop in Hck as [Hsz Hck]. apply Z.eqb_eq in Hsz. subst isz.
destruct i; try discriminate Hck.
apply andb_prop in Hck as [Hck Ht]. apply andb_prop in Hck as [Hrd _]. apply reg_eqb_eq in Hrd. apply Z.eqb_eq in Ht.
subst.
pose proof (pa_fetch_ok (L := B_prog_listing) (PI := PA) _ _ Hl) as Hf.
pose proof (not_ecall_of_decode _ _ _ Hdec ltac:(discriminate)) as Hec.
rewrite (step_jal_link (fx := fy) SEGS regs _ mem rom _ _ _ Hf Hec Hdec).
lazymatch goal with |- context [if ?c then _ else _] => destruct c eqn:E1 end.
{ exfalso. vm_compute in E1. discriminate E1. }
unfold btgt, v_addi. rewrite unsigned_lit_small by lia.
rewrite <- Ht, lit_canon. replace (VAL A_TEXT + PJP_C1 + 4) with (VAL A_TEXT + (PJP_C1 + 4)) by lia.
reflexivity.
Qed.

(* +0x50 `bnez a0, +0x68`: falls through to +0x54 (PJP_C2OK) on a0 = 0, else to PJP_C2REF *)
Lemma pjp_bnez_step : forall (fy : YK11.FPState) regs mem rom,
  RiscvSemantics.step SEGS (@YK11.mkst fy regs (Z_to_bv 64 (BASE + (PJP_C1 + 4))) mem rom) =
  MachineOk (@YK11.mkst fy regs
    (if c_eq (getr regs 10%bv) (Z_to_bv 64 0) then Z_to_bv 64 (BASE + PJP_C2OK) else Z_to_bv 64 (BASE + PJP_C2REF))
    mem rom).
Proof.
intros fy regs mem rom.
pose proof pjp_code_rng as (R1 & R2 & R3 & R4 & R5 & R6). pose proof (@pa_B_ok _ B_prog_listing PA) as (HB0 & HB1 & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct (plookup (@pl_tpi B_prog_listing PL) (PJP_C1 + 4)) as [e|] eqn:He; [|vm_compute in He; discriminate He].
pose proof He as He'. vm_compute in He'. injection He' as Ee. subst e.
pose proof (pa_fetch_pw (L := B_prog_listing) (PL := PL) (PI := PA) _ _ He) as Hf.
lazymatch type of He with _ = Some (PW ?w) =>
  destruct (decode_any (Z_to_bv 32 w)) as [[i isz]|] eqn:Hd; [|vm_compute in Hd; discriminate Hd] end.
pose proof Hd as Hd'. vm_compute in Hd'. injection Hd' as Ei Es. subst i isz.
pose proof (not_ecall_of_decode _ _ _ Hd ltac:(discriminate)) as Hec.
destruct (c_eq (getr regs 10%bv) (Z_to_bv 64 0)) eqn:Hc.
- rewrite (step_bne_ft (fx := fy) SEGS regs _ mem rom _ _ _ _ Hf Hec Hd) by exact Hc.
  unfold v_addi. rewrite unsigned_lit_small by lia.
  replace (BASE + (PJP_C1 + 4) + 4) with (BASE + PJP_C2OK) by (unfold PJP_C2OK, PJP_C1; lia). reflexivity.
- rewrite (step_bne_tk (fx := fy) SEGS regs _ mem rom _ _ _ _ Hf Hec Hd) by exact Hc.
  unfold btgt, v_addi. rewrite unsigned_lit_small by lia.
  lazymatch goal with |- context [bv_signed ?im] =>
    assert (Eim : PJP_C1 + 4 + bv_signed im = PJP_C2REF) by (vm_compute; reflexivity) end.
  replace (BASE + (PJP_C1 + 4) + bv_signed _) with (BASE + PJP_C2REF) by lia. reflexivity.
Qed.

(* ---- small lemmas of bytes and shadow ---- *)
(* the image hull arithmetic (FuzzStrdupB.v sd_hull_img), at any image bounds L / H (here the instance's own pa_lo /
   pa_hi: kept_at's image cases and pjp_g_vis' image clause are stated at them) *)
Lemma pjp_hull_img : forall L H a n s, 0 < n -> L + 64 <= a -> a + n + 64 <= H ->
  shadow_addr a / 8 * 8 <= s < shadow_addr (a + n - 1) / 8 * 8 + 8 ->
  s = shadow_addr (8 * (s - SHADOW_OFF)) /\ L <= 8 * (s - SHADOW_OFF) < H.
Proof.
intros L H a n s Hn Hlo Hhi Hs. unfold shadow_addr in *.
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

(* the hull is closed under sub-ranges (YGcfHeadSh.v shadow_hull_vis_sub_cf, restated: that file's own imports are
   the cf instance's) *)
Lemma pjp_hull_sub : forall rd x n x' n',
  shadow_hull_vis rd x n -> x <= x' -> x' + n' <= x + n -> shadow_hull_vis rd x' n'.
Proof.
intros rd x n x' n' H H1 H2 s Hs. apply H. unfold shadow_addr in *.
pose proof (Z.div_le_mono x x' 8 ltac:(lia) H1) as D1.
pose proof (Z.div_le_mono (x' + n' - 1) (x + n - 1) 8 ltac:(lia) ltac:(lia)) as D2.
pose proof (Z.div_le_mono (SHADOW_OFF + x / 8) (SHADOW_OFF + x' / 8) 8 ltac:(lia) ltac:(lia)) as D3.
pose proof (Z.div_le_mono (SHADOW_OFF + (x' + n' - 1) / 8) (SHADOW_OFF + (x + n - 1) / 8) 8 ltac:(lia) ltac:(lia)) as D4.
lia.
Qed.

(* a word read back (YCem.v rdword_of_val_mem, restated: YCem's own dependency YCeh does not build at this base) *)
Lemma pjp_rdword_of_val_mem : forall (H : word -> bool) mem a v,
  val_mem SEGS (mrestrict H mem) a 8 v -> 0 <= v < 2 ^ 64 -> rdword (aview SEGS H mem) a = Some v.
Proof.
intros H mem a v Hv Hr.
assert (B : forall k, (k < 8)%nat -> aview SEGS H mem (a + Z.of_nat k) = Some (le_byte v 8 k)).
{ intros k Hk. unfold aview. rewrite (Hv k Hk). cbn [option_map]. f_equal.
  rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256. unfold le_byte. apply Z.mod_mod. lia. }
unfold rdword.
rewrite <- (Z.add_0_r a) at 1. change 0 with (Z.of_nat 0) at 1. rewrite (B 0%nat) by lia.
change 1 with (Z.of_nat 1). rewrite (B 1%nat) by lia. change 2 with (Z.of_nat 2) at 1. rewrite (B 2%nat) by lia.
change 3 with (Z.of_nat 3). rewrite (B 3%nat) by lia. change 4 with (Z.of_nat 4). rewrite (B 4%nat) by lia.
change 5 with (Z.of_nat 5). rewrite (B 5%nat) by lia. change 6 with (Z.of_nat 6). rewrite (B 6%nat) by lia.
change 7 with (Z.of_nat 7). rewrite (B 7%nat) by lia.
f_equal. apply le_bytes8. exact Hr.
Qed.

(* the shadow byte of an application address is no application byte of a range inside [4096, alloc_ceiling) *)
Lemma pjp_shadow_out : forall lo len x, in_app lo len -> lo + len <= YM05.alloc_ceiling -> lo <= x < lo + len ->
  ~ (lo <= shadow_of_addr SHADOW_OFF x < lo + len) /\ shadow_of_addr SHADOW_OFF x < YM05.alloc_ceiling.
Proof.
intros lo len x Happ Hc Hx. pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Happ. unfold shadow_of_addr, SHADOW_OFF.
pose proof (Z.div_pos x 8 ltac:(lia) ltac:(lia)).
assert (x / 8 <= YM05.alloc_ceiling / 8) by (apply Z.div_le_mono; lia).
assert (YM05.alloc_ceiling / 8 <= 2 ^ 44 - 2 ^ 20) by (apply Z.div_le_upper_bound; lia).
split; lia.
Qed.

(* a byte list survives a memory change that keeps each of its bytes' views (FuzzStrdupB.v sd_garr8_move at d = x) *)
Lemma pjp_garr8_move : forall (W W' : world SEGS) m m' x l, garr8 SEGS (mrestrict (w_H W) m) x l ->
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

(* a read-only byte is an image byte (FuzzStrdupB.v sd_ro_img) *)
Lemma pjp_ro_img : forall a, in_roP SEGS RLO RHI a -> in_img SEGS a.
Proof.
intros a [(sg & Hin & _ & Hr) | Hr]; [exists sg; split; [exact Hin | exact Hr] | exact (@pa_relro_img _ _ PA a Hr)].
Qed.

(* a callee-saved register other than ra keeps its value across a call made with ra := v *)
Lemma pjp_preserved : forall regs regs2 v r, aregs_preserved (regupd regs 1%bv v) regs2 -> acallee_saved r ->
  Z_to_bv 5 r <> 1%bv -> getr regs2 (Z_to_bv 5 r) = getr regs (Z_to_bv 5 r).
Proof. intros regs regs2 v r HP Hr Hne. rewrite (HP r Hr). apply getr_other. exact Hne. Qed.

Section s. Context {fx : YK11.FPState} {ci : CfImg} {cp : CfParams} {RL : PrhRoomLive}.
Context {SK : YI16.sink_head}.
#[local] Notation PST := (prh_pst (PI := prh_img_B)).
Variable B : asyms.
Variable ARx : alayout -> astate -> list Z -> world SEGS -> (word -> option byte) -> Model -> Prop.
#[local] Abbreviation rdW W mem := (mrestrict (w_H W) mem).
#[local] Notation AJ := (ajournal_x (SK := SK) SEGS B PST ARx).

(* the allocator's laws at the harness head length (FuzzStrdupB / OwnB take them at cf_head; at ARcf they are
   YGcallcf.v AR_laws_x_xs) *)
Hypothesis LAWS : AR_laws_x SEGS B ARx cf_head.
(* glue (pj_parse_defs.v): the allocator-trace premises from the closure, the depth monotonicity of a freeable tree,
   and the image shadow facts (pjp_g_vis: discharged at the instance, pj_parse_inst.v) *)
Hypothesis GU : pjp_g_univ B.
Hypothesis VIS : pjp_g_vis B ARx.
(* CFHEAD-16, the walk's Section hypothesis (PRH_Base.v prh_head16; reflexivity at CfParams_preset): the trees'
   free order in parse_value's post is stated under it, and pj_parse's live sum bounds parse_value's per-event room
   at it *)
Hypothesis HH : prh_head16.
(* parse_value's per-event live room (the third conjunct of the kit's rd_room, PRH_Base.prh_live_evs) from pj_parse's live sum
   (lib/B/Prog/pj_parse_live.v pjl_live_evs, a pure model lemma) *)
Hypothesis G_LIVE : forall (S : astate) (tl : list Z), cf_head = PresetReqAt.HEAD ->
  blocks_bytes S + LIVE_pj_parse tl <= LIVE_MAX ->
  prh_live_evs S (PresetReqAt.rd_hevs (prhPv_gtrace 0 tl)).

(* the one place pjp_g_univ is used (rd_pre's trace premises, pc0-filtered: parse text blob dcff6bfa302a) *)
Lemma pjp_c1_univ : forall CTX0, prh_univ_closure B CTX0 ->
  prh_malloc_univ B /\ In [cf_pc_realloc_ra0] (u_fix (as_universe B)) /\
  In (prh_trace cf_pc_realloc_ra0 pi_ret_realloc []) (u_fix (as_universe B)).
Proof. intros CTX0 H. exact (GU CTX0 H). Qed.

(* a zero-shadow static range is addressable: the zero-shadow law (alx_zshadow) over the whole-granule image range
   that holds it (pjp_g_vis' second conjunct; YG0v.v zero_shadow_range) *)
Lemma pjp_zs_addr : forall ly S Hp W mem md a n,
  (forall q m, In (q, m) (as_zero_shadow B) -> q mod 8 = 0 /\ m mod 8 = 0) ->
  ARx ly S Hp W mem md -> in_zs B a n ->
  range_addressable (aview SEGS (w_H W) mem) SHADOW_OFF a n.
Proof.
intros ly S Hp W mem md a n AL HAR (q & m & Hin & Hqa & Han).
destruct (AL q m Hin) as [Hq Hm].
pose proof (alx_zshadow SEGS B ARx LAWS ly S Hp W mem md (q, m) HAR
  ltac:(unfold zero_shadow_ranges; apply in_cons; exact Hin)) as HZ.
cbn [fst snd] in HZ.
exact (range_addressable_sub _ _ q m a n (zero_shadow_range _ _ q m Hq Hm HZ) Hqa Han).
Qed.

(* out is below alloc_ceiling with its 56 bytes, and 8-aligned *)
Lemma pjp_out_low : forall en ly S Hp W mem md Lam, pjp_out_ok B en ly S Lam W mem -> ARx ly S Hp W mem md ->
  je_out en + 56 <= YM05.alloc_ceiling /\ je_out en mod 8 = 0.
Proof.
intros en ly S Hp W mem md Lam HO HAR.
destruct HO as (_ & _ & Hpl & _ & (Hal & _) & _).
split; [|exact Hal].
destruct Hpl as [(b & m & Hbm & _ & Hb & Hm) | (cid & pos & Hcp & Hf1 & Hf2)].
- destruct (alx_blocks SEGS B ARx LAWS ly S Hp W mem md b m HAR Hbm) as (_ & _ & Hc & _).
  pose proof (pjp_req m ltac:(lia)) as (Rq1 & _). lia.
- destruct (frames_bounds_x SEGS B ARx LAWS ly S Hp W mem md cid pos HAR Hcp) as (_ & Hc & _). lia.
Qed.

(* ---- parse_value's cursor words, as pj_parse supplies them at the call (the kit's prh_cur_entry): no entry chain from
   s0 = out (below alloc_ceiling, so the chain is empty: the kit's prh_cur_entry_cases, case 1); the chain stop words at
   prh_s0 F q - 16: on image B parse_string's is the callee's own saved ra at sp1 - 8 (a code address), parse_items'
   the cursor's p at sp1 + 8 (a text address, below alloc_ceiling) ---- *)
Lemma pjp_cur_ok : forall (W : world SEGS) mem (regs1 : bvmap 5 word) sp1 t0 len tl,
  spZ regs1 = sp1 -> s0Z regs1 < sp1 + 16 -> YM05.alloc_ceiling <= sp1 + 8 ->
  raZ regs1 < YM05.alloc_ceiling -> t0 < YM05.alloc_ceiling ->
  pj_in_okR SEGS (mrestrict (w_H W) mem) (sp1 + 8) t0 len t0 0 tl ->
  prh_cur_entry (PA := PA) W mem regs1 (sp1 + 8).
Proof.
intros W mem regs1 sp1 t0 len tl Hsp Hs0 Hq Hra Ht0 Hcur.
split.
{ apply (prh_cur_entry_cases W mem regs1 (sp1 + 8) Hq). left. rewrite Hsp. exact Hs0. }
intros F HF.
destruct Hcur as (Vp & Ve & _ & _ & _ & H0t & Hlt & _ & Hlen & _).
assert (Rp : rdword (aview SEGS (w_H W) mem) (sp1 + 8) = Some t0)
  by (apply pjp_rdword_of_val_mem; [exact Vp | lia]).
assert (Hk : prh_s0 F (sp1 + 8) = sp1 + 8 + 0 \/ prh_s0 F (sp1 + 8) = sp1 + 8 + 16)
  by (destruct HF as [-> | ->]; [left | right]; reflexivity).
unfold prh_word_entry. rewrite Hsp.
destruct Hk as [Hk | Hk]; rewrite Hk; intros w Hw.
- rewrite (proj2 (Z.eqb_eq (sp1 + 8 + 0 - 16) (sp1 - 8)) ltac:(lia)) in Hw. subst w. exact Hra.
- rewrite (proj2 (Z.eqb_neq (sp1 + 8 + 16 - 16) (sp1 - 8)) ltac:(lia)) in Hw.
  rewrite (proj2 (Z.eqb_neq (sp1 + 8 + 16 - 16) (sp1 - 16)) ltac:(lia)) in Hw.
  replace (sp1 + 8 + 16 - 16) with (sp1 + 8) in Hw by lia. rewrite Rp in Hw. injection Hw as <-. exact Ht0.
Qed.

(* ---- THE CURSOR SET at the call (the kit's prh_cw_entry): each cursor free's trace from the word at prh_s0 F q - 8 is in
   CW, by the B' arms of pjp_pre's prh_cw_pj (the kit's, PRH_Base.v :1521-1527): parse_string reads the never-written
   slot at sp1 (the C1 cut's slot arm), parse_items the cursor's end t0 + len at sp1 + 16 (pj_in_okR's end
   word) ---- *)
Lemma pjp_cw_ok : forall CW (W : world SEGS) mem (regs1 : bvmap 5 word) sp1 t0 len tl,
  spZ regs1 = sp1 ->
  (forall r, In r (prh_free_sites F_parse_items) -> In (prh_trace (pc_free_ra0 (as_code B)) r [t0 + len]) CW) ->
  (forall r, In r (prh_free_sites F_parse_string) ->
     forall w0, rdword (aview SEGS (w_H W) mem) sp1 = Some w0 -> In (prh_trace (pc_free_ra0 (as_code B)) r [w0]) CW) ->
  pj_in_okR SEGS (mrestrict (w_H W) mem) (sp1 + 8) t0 len t0 0 tl ->
  prh_cw_entry (PA := PA) B CW W mem regs1 (sp1 + 8).
Proof.
intros CW W mem regs1 sp1 t0 len tl Hsp Hpi Hps Hcur F r w HF Hr Hw.
destruct Hcur as (Vp & Ve & _ & _ & _ & H0t & Hlt & _ & Hlen & _).
assert (Re : rdword (aview SEGS (w_H W) mem) (sp1 + 8 + 8) = Some (t0 + len))
  by (apply pjp_rdword_of_val_mem; [exact Ve | lia]).
unfold prh_word_entry in Hw. rewrite Hsp in Hw. left.
destruct HF as [-> | ->].
- change (prh_s0 F_parse_string (sp1 + 8)) with (sp1 + 8 + 0) in Hw.
  rewrite (proj2 (Z.eqb_neq (sp1 + 8 + 0 - 8) (sp1 - 8)) ltac:(lia)) in Hw.
  rewrite (proj2 (Z.eqb_neq (sp1 + 8 + 0 - 8) (sp1 - 16)) ltac:(lia)) in Hw.
  replace (sp1 + 8 + 0 - 8) with sp1 in Hw by lia. exact (Hps r Hr w Hw).
- change (prh_s0 F_parse_items (sp1 + 8)) with (sp1 + 8 + 16) in Hw.
  rewrite (proj2 (Z.eqb_neq (sp1 + 8 + 16 - 8) (sp1 - 8)) ltac:(lia)) in Hw.
  rewrite (proj2 (Z.eqb_neq (sp1 + 8 + 16 - 8) (sp1 - 16)) ltac:(lia)) in Hw.
  replace (sp1 + 8 + 16 - 8) with (sp1 + 8 + 8) in Hw by lia. rewrite Re in Hw. injection Hw as <-.
  exact (Hpi r Hr).
Qed.

(* ---- the ledger's harness bases: a base of Hp is the base of a live allocator block of the ledger ---- *)
Lemma pjp_hp_block : forall ly S Hp W mem Lam peak cnt fail ran most own h,
  prh_ledger (PA := PA) B ly S Hp W mem Lam peak cnt fail ran most own -> In h Hp ->
  exists a k, In (a, k) Lam /\ h = a - cf_head /\ 0 <= k /\ In (a - cf_head, k + cf_head) (ablocks B ly S).
Proof.
intros ly S Hp W mem Lam peak cnt fail ran most own h HL Hh.
pose proof HL as HF. apply prh_ledger_blocks in HF. pose proof HL as HP. apply prh_ledger_heads in HP. clear HL.
apply (Permutation_in _ HP) in Hh. apply in_map_iff in Hh as ([a k] & Ea & Hin). cbn [fst] in Ea.
pose proof (proj1 (Forall_forall _ _) HF (a, k) Hin) as (Hk0 & Hab & _). cbn [fst snd] in Hk0, Hab.
exists a, k. split; [exact Hin | split; [lia | split; [exact Hk0 | exact Hab]]].
Qed.

(* no harness base of the ledger lies in a live block that is not that harness block's *)
Lemma pjp_no_head_in : forall ly S Hp W mem md Lam peak cnt fail ran most own b m,
  ARx ly S Hp W mem md -> prh_ledger (PA := PA) B ly S Hp W mem Lam peak cnt fail ran most own ->
  In (b, m) (ablocks B ly S) -> ~ In (b + cf_head, m - cf_head) Lam ->
  forall h, In h Hp -> ~ (b <= h < b + req_size m).
Proof.
intros ly S Hp W mem md Lam peak cnt fail ran most own b m HAR HL Hbm HnL h Hh Hr.
pose proof (@cf_head_nonneg cp) as Hh0.
destruct (pjp_hp_block ly S Hp W mem Lam peak cnt fail ran most own h HL Hh) as (a & k & Hin & -> & Hk0 & Hab).
pose proof (pjp_req (k + cf_head) (Z.add_nonneg_nonneg _ _ Hk0 Hh0)) as (_ & Rq & _).
destruct (Z.eq_dec b (a - cf_head)) as [Eb | Nb]; [destruct (Z.eq_dec m (k + cf_head)) as [Em | Nm] |].
- apply HnL. replace (b + cf_head, m - cf_head) with (a, k) by (f_equal; lia). exact Hin.
- assert (Hne : (b, m) <> (a - cf_head, k + cf_head)) by (intros E; injection E as _ E2; exact (Nm E2)).
  pose proof (sep_blocks_x SEGS B ARx LAWS ly S Hp W mem md b m _ _ HAR Hbm Hab Hne) as Hd.
  unfold zdisjoint in Hd. cbn [fst snd] in Hd. lia.
- assert (Hne : (b, m) <> (a - cf_head, k + cf_head)) by (intros E; injection E as E1 _; exact (Nb E1)).
  pose proof (sep_blocks_x SEGS B ARx LAWS ly S Hp W mem md b m _ _ HAR Hbm Hab Hne) as Hd.
  unfold zdisjoint in Hd. cbn [fst snd] in Hd. lia.
Qed.

(* ---- OUT'S PLACE AND SHADOW AFTER THE CALL: pjp_out_ok at the return state, from pjp_out_ok at the call state, the
   callee's journal from the call state, rd_blocks_move (the subtree's blocks D are new: out stays out of them, and
   Lam' = D ++ Lam) and the ledger at the return state; pj_rwR at the return state is the post's (the node's header) ---- *)
Lemma pjp_out_kept {R : world SEGS -> world SEGS -> Prop} : forall en ly S Hp W mem md Lam ly2 S2 Hp2 W2 mem2 md2
    STK1 sp FP1 k1 D tr rest d0 Lam' peak' cnt' fail' ran' most own WS1,
  pjp_out_ok B en ly S Lam W mem ->
  ajournal_xwR (SK := SK) SEGS B PST ARx R STK1 sp FP1 ly S Hp W mem md [] ly2 S2 Hp2 W2 mem2 md2 k1 WS1 ->
  ARx ly S Hp W mem md ->
  (forall x, inFP FP1 x -> YM05.alloc_ceiling <= x \/ je_out en <= x < je_out en + 56) ->
  rd_blocks_move B ly S ly2 S2 D tr rest d0 ->
  Permutation Lam' (D ++ Lam) ->
  prh_ledger (PA := PA) B ly2 S2 Hp2 W2 mem2 Lam' peak' cnt' fail' ran' most own ->
  pj_rwR SEGS (rdW W2 mem2) (je_out en) ->
  pjp_out_ok B en ly2 S2 Lam' W2 mem2.
Proof.
intros en ly S Hp W mem md Lam ly2 S2 Hp2 W2 mem2 md2 STK1 sp FP1 k1 D tr rest d0 Lam' peak' cnt' fail' ran' most own WS1
  HO HJ HAR HFP (Hfresh & Hab & Hfr & _) HLam HL2 Hrw.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5). pose proof (@cf_head_nonneg cp) as Hh0.
destruct (pjp_out_low en ly S Hp W mem md Lam HO HAR) as (Hlow & Hal8).
destruct HO as (H4096 & Hceil & Hplace & Hapart & _ & Hamr & _ & Hra & _).
destruct HJ as (HAR2 & Hly & _ & _ & _ & _ & _ & _ & _ & _ & _ & F4 & _).
pose proof HL2 as HLF2. apply prh_ledger_blocks in HLF2.
assert (Hkeep : forall x, In x (ablocks B ly S) -> In x (ablocks B ly2 S2))
  by (intros x Hx; apply (Permutation_in _ (Permutation_sym Hab)); apply in_or_app; right; exact Hx).
assert (HDb : forall a k, In (a, k) D -> In (a - cf_head, k + cf_head) (ablocks B ly2 S2)).
{ intros a k Hin. apply (Permutation_in _ (Permutation_sym Hab)). apply in_or_app; left.
  exact (in_map (fun ak : Z * Z => (fst ak - cf_head, snd ak + cf_head)) D (a, k) Hin). }
assert (HLs : forall a k, In (a, k) Lam' -> In (a, k) D \/ In (a, k) Lam)
  by (intros a k Hin; apply in_app_or; exact (Permutation_in _ HLam Hin)).
assert (HLk : forall a k, In (a, k) Lam' -> 0 <= k)
  by (intros a k Hin; exact (proj1 (proj1 (Forall_forall _ _) HLF2 (a, k) Hin))).
destruct Hplace as [(b & m & Hbm & HnL & Hb & Hm) | (cid & pos & Hcp & Hf1 & Hf2)].
- (* out in a live allocator block that is no harness block *)
  pose proof (Hkeep _ Hbm) as Hbm2.
  destruct (alx_blocks SEGS B ARx LAWS ly2 S2 Hp2 W2 mem2 md2 b m HAR2 Hbm2) as (_ & _ & _ & _ & Hbown & _).
  pose proof (pjp_req m ltac:(lia)) as (_ & _ & Rm). specialize (Rm ltac:(lia)).
  assert (HnL' : ~ In (b + cf_head, m - cf_head) Lam').
  { intros Hin. destruct (HLs _ _ Hin) as [HinD | HinL]; [|exact (HnL HinL)].
    apply (Hfresh _ _ HinD). replace (b + cf_head - cf_head, m - cf_head + cf_head) with (b, m) by (f_equal; lia).
    exact Hbm. }
  destruct (alx_shadow SEGS B ARx LAWS ly2 S2 Hp2 W2 mem2 md2 b m HAR2 Hbm2
    (pjp_no_head_in ly2 S2 Hp2 W2 mem2 md2 Lam' peak' cnt' fail' ran' most own b m HAR2 HL2 Hbm2 HnL')) as [Hbs Hbh].
  rewrite Rm in Hbs, Hbh.
  split; [exact H4096|]. split; [exact Hceil|].
  split; [left; exists b, m; split; [exact Hbm2 | split; [exact HnL' | split; [exact Hb | exact Hm]]]|].
  split.
  { intros a k Hin. destruct (HLs a k Hin) as [HinD | HinL]; [|exact (Hapart a k HinL)].
    pose proof (HDb a k HinD) as Hin2. pose proof (Hfresh a k HinD) as Hn1. pose proof (HLk a k Hin) as Hk0.
    assert (Hne : (b, m) <> (a - cf_head, k + cf_head)) by (intros E; rewrite E in Hbm; exact (Hn1 Hbm)).
    pose proof (sep_blocks_x SEGS B ARx LAWS ly2 S2 Hp2 W2 mem2 md2 b m _ _ HAR2 Hbm2 Hin2 Hne) as Hd.
    pose proof (pjp_req (k + @cf_head cp) ltac:(lia)) as (Rq & _).
    unfold zdisjoint in Hd. cbn [fst snd] in Hd. rewrite Rm in Hd. lia. }
  split; [exact Hrw|]. split; [exact Hamr|].
  split; [intros a Ha; exact (proj2 (Hbown a ltac:(rewrite Rm; lia)))|].
  split; [exact (block_shadow_range _ SHADOW_OFF b m (je_out en) 56 Hbs ltac:(lia) ltac:(lia))|].
  exact (pjp_hull_sub _ b m (je_out en) 56 Hbh ltac:(lia) ltac:(lia)).
- (* out in a live fake frame of a caller *)
  pose proof (Permutation_in _ (Permutation_sym Hfr) Hcp) as Hcp2.
  assert (Efa : frame_addr ly2 cid pos = frame_addr ly cid pos).
  { unfold frame_addr. destruct Hly as (_ & _ & _ & _ & _ & EF & _). rewrite EF. reflexivity. }
  destruct (frames_bounds_x SEGS B ARx LAWS ly S Hp W mem md cid pos HAR Hcp) as (Hf0 & Hfc & Hfapp).
  destruct (alx_frames SEGS B ARx LAWS ly S Hp W mem md cid pos HAR Hcp) as (Hfal & _).
  destruct (alx_frames SEGS B ARx LAWS ly2 S2 Hp2 W2 mem2 md2 cid pos HAR2 Hcp2) as (_ & _ & Hfown & _).
  rewrite Efa in Hfown.
  destruct VIS as (VF & _ & _).
  pose proof (VF ly2 S2 Hp2 W2 mem2 md2 cid pos HAR2 Hcp2) as Hfh. rewrite Efa in Hfh.
  split; [exact H4096|]. split; [exact Hceil|].
  split; [right; exists cid, pos; rewrite Efa; split; [exact Hcp2 | split; [exact Hf1 | exact Hf2]]|].
  split.
  { intros a k Hin. destruct (HLs a k Hin) as [HinD | HinL]; [|exact (Hapart a k HinL)].
    pose proof (HDb a k HinD) as Hin2. pose proof (HLk a k Hin) as Hk0.
    pose proof (sep_block_frame_x SEGS B ARx LAWS ly2 S2 Hp2 W2 mem2 md2 _ _ cid pos HAR2 Hin2 Hcp2) as Hd.
    pose proof (pjp_req (k + @cf_head cp) ltac:(lia)) as (Rq & _).
    unfold zdisjoint in Hd. cbn [fst snd] in Hd. rewrite Efa in Hd. lia. }
  split; [exact Hrw|]. split; [exact Hamr|].
  split; [intros a Ha; exact (proj2 (Hfown a ltac:(lia)))|].
  split.
  + eapply range_addressable_agree; [|exact Hra]. intros x Hx.
    destruct (pjp_shadow_out (frame_addr ly cid pos) (fs_frame_bytes cid) x Hfapp Hfc ltac:(lia)) as (Hso & Hsc).
    apply (F4 cid pos); [exact Hcp | right | ].
    * unfold in_zr, shadow_of_addr, shadow_addr. cbn [fst snd].
      assert (Hx8 : x / 8 < je_out en / 8 + 7).
      { apply Z.div_lt_upper_bound; [lia|]. pose proof (Z.div_mod (je_out en) 8 ltac:(lia)). lia. }
      assert (Ho8 : frame_addr ly cid pos / 8 <= je_out en / 8) by (apply Z.div_le_mono; lia).
      assert (He8 : je_out en / 8 + 7 <= (frame_addr ly cid pos + fs_frame_bytes cid) / 8).
      { apply Z.div_le_lower_bound; [lia|]. pose proof (Z.div_mod (je_out en) 8 ltac:(lia)). lia. }
      assert (Hs8 : (frame_addr ly cid pos + fs_frame_bytes cid) / 8 = frame_addr ly cid pos / 8 + fs_frame_bytes cid / 8).
      { rewrite (Z.div_mod (frame_addr ly cid pos) 8) at 1 by lia.
        replace (frame_addr ly cid pos mod 8) with 0 by lia.
        replace (8 * (frame_addr ly cid pos / 8) + 0 + fs_frame_bytes cid) with
          (fs_frame_bytes cid + (frame_addr ly cid pos / 8) * 8) by lia.
        rewrite Z.div_add by lia. lia. }
      assert (Hx0 : je_out en / 8 <= x / 8) by (apply Z.div_le_mono; lia).
      lia.
    * intros Hin. destruct (HFP _ Hin) as [Hc | Hc]; [lia|]. apply Hso. lia.
  + exact (pjp_hull_sub _ _ _ (je_out en) 56 Hfh ltac:(lia) ltac:(lia)).
Qed.

(* ---- THE TEXT AFTER THE CALL: pjp_text_ok at the return state. Its bytes ride on the callee's journal (a harness or
   other live block: the block clause; a read-only global or image string: the image clause), its home on the blocks
   rd_blocks_move keeps, its shadow on the laws at the return state (harness block: alx_hshadow at cf_head; other block:
   alx_shadow; registered global: pjp_g_vis' zero-shadow conjunct; image string: its const cells and pjp_g_vis' image
   shadow map) ---- *)
Lemma pjp_text_kept {R : world SEGS -> world SEGS -> Prop} : forall en ly S Hp W mem md Lam peak cnt fail ran ly2 S2
    Hp2 W2 mem2 md2 STK1 sp FP1 k1 D tr rest d0 Lam' peak' cnt' fail' ran' most own WS1,
  pjp_text_ok B en ly S Hp Lam W mem ->
  prh_ledger (PA := PA) B ly S Hp W mem Lam peak cnt fail ran most own ->
  ajournal_xwR (SK := SK) SEGS B PST ARx R STK1 sp FP1 ly S Hp W mem md [] ly2 S2 Hp2 W2 mem2 md2 k1 WS1 ->
  ARx ly S Hp W mem md ->
  ~ YI16.sink_open_fp FP1 ->
  (forall x, je_t0 en <= x < je_t0 en + je_len en -> ~ inFP FP1 x) ->
  Z.of_nat (length (je_tl en)) = je_len en ->
  rd_blocks_move B ly S ly2 S2 D tr rest d0 ->
  Permutation Lam' (D ++ Lam) ->
  prh_ledger (PA := PA) B ly2 S2 Hp2 W2 mem2 Lam' peak' cnt' fail' ran' most own ->
  pjp_text_ok B en ly2 S2 Hp2 Lam' W2 mem2.
Proof.
intros en ly S Hp W mem md Lam peak cnt fail ran ly2 S2 Hp2 W2 mem2 md2 STK1 sp FP1 k1 D tr rest d0
  Lam' peak' cnt' fail' ran' most own WS1 (Hsrc & Hhome) HL HJ HAR Hsink HFP Hlen (Hfresh & Hab & _ & _) HLam HL2.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5). pose proof (@cf_head_nonneg cp) as Hh0.
destruct Hsrc as (Hby & H4096 & Hceil & Hamr & Hra & Hhull).
pose proof HJ as (HAR2 & _ & _ & _ & _ & _ & _ & _ & _ & F2 & F3 & _).
pose proof HL as HLF. apply prh_ledger_blocks in HLF. pose proof HL as HHp. apply prh_ledger_heads in HHp.
pose proof HL2 as HLF2. apply prh_ledger_blocks in HLF2. pose proof HL2 as HHp2. apply prh_ledger_heads in HHp2.
rewrite Hlen in Hceil, Hamr, Hra, Hhull.
assert (Hkeep : forall x, In x (ablocks B ly S) -> In x (ablocks B ly2 S2))
  by (intros x Hx; apply (Permutation_in _ (Permutation_sym Hab)); apply in_or_app; right; exact Hx).
assert (HLs : forall a k, In (a, k) Lam' -> In (a, k) D \/ In (a, k) Lam)
  by (intros a k Hin; apply in_app_or; exact (Permutation_in _ HLam Hin)).
assert (HLin : forall a k, In (a, k) Lam -> In (a, k) Lam')
  by (intros a k Hin; apply (Permutation_in _ (Permutation_sym HLam)); apply in_or_app; right; exact Hin).
(* a block of the call state whose base is no harness base stays one *)
assert (HnoHp2 : forall b m, In (b, m) (ablocks B ly S) -> 0 <= m -> ~ In b Hp -> ~ In b Hp2).
{ intros b m Hbm Hm0 Hn Hb2.
  destruct (pjp_hp_block ly2 S2 Hp2 W2 mem2 Lam' peak' cnt' fail' ran' most own b HL2 Hb2) as (a & k & Hin & Eb & Hk0 & Hab2).
  destruct (HLs a k Hin) as [HinD | HinL].
  - pose proof (Hfresh a k HinD) as Hn1.
    assert (Hne : (b, m) <> (a - cf_head, k + cf_head)) by (intros E; rewrite E in Hbm; exact (Hn1 Hbm)).
    pose proof (sep_blocks_x SEGS B ARx LAWS ly2 S2 Hp2 W2 mem2 md2 b m _ _ HAR2 (Hkeep _ Hbm) Hab2 Hne) as Hd.
    pose proof (pjp_req (k + @cf_head cp) ltac:(lia)) as (_ & Rq & _). pose proof (pjp_req m Hm0) as (_ & Rm & _).
    unfold zdisjoint in Hd. cbn [fst snd] in Hd. lia.
  - apply Hn. apply (Permutation_in _ (Permutation_sym HHp)). apply in_map_iff. exists (a, k).
    split; [cbn; lia | exact HinL]. }
(* the bytes and the shadow, by the text's home *)
assert (HK : (forall x, je_t0 en <= x < je_t0 en + je_len en -> aview SEGS (w_H W2) mem2 x = aview SEGS (w_H W) mem x) /\
  range_addressable (aview SEGS (w_H W2) mem2) SHADOW_OFF (je_t0 en) (je_len en) /\
  (0 < je_len en -> shadow_hull_vis (aview SEGS (w_H W2) mem2) (je_t0 en) (je_len en))).
{ destruct Hhome as [[(b & m & Hin & Hb & Hm) | [(Hzs & Hlo & Hhi & Hro) | (Hlo & Hhi & Hro)]] | (b & m & Hbm & HnHp & Hb & Hm)].
  - (* a live harness block *)
    pose proof (proj1 (Forall_forall _ _) HLF (b, m) Hin) as (Hm0 & Hab1 & _). cbn [fst snd] in Hm0, Hab1.
    pose proof (proj1 (Forall_forall _ _) HLF2 (b, m) (HLin _ _ Hin)) as (_ & Hab2 & Hhp2 & _).
    cbn [fst snd] in Hab2, Hhp2.
    destruct (alx_hshadow SEGS B ARx LAWS ly2 S2 Hp2 W2 mem2 md2 (b - cf_head) (m + cf_head) HAR2 Hab2 Hhp2) as [Hbs Hbh].
    split; [|split].
    + intros x Hx. replace x with (b - cf_head + (x - (b - cf_head))) by lia.
      apply (F2 (b - cf_head) (m + cf_head) (x - (b - cf_head)) Hab1 (Hkeep _ Hab1)).
      * pose proof (pjp_req (m + @cf_head cp) ltac:(lia)) as (Rq & _). lia.
      * replace (b - cf_head + (x - (b - cf_head))) with x by lia. exact (HFP x Hx).
    + destruct (Z_lt_le_dec 0 (je_len en)) as [Hl0 | Hl0]; [|apply range_addressable_nil; lia].
      pose proof (pjp_req (m + @cf_head cp) ltac:(lia)) as (_ & _ & Rq). rewrite Rq in Hbs by lia.
      replace (b - cf_head + cf_head) with b in Hbs by lia. replace (m + cf_head - cf_head) with m in Hbs by lia.
      exact (block_shadow_range _ SHADOW_OFF b m (je_t0 en) (je_len en) Hbs ltac:(lia) ltac:(lia)).
    + intros Hl0. pose proof (pjp_req (m + @cf_head cp) ltac:(lia)) as (_ & _ & Rq). rewrite Rq in Hbh by lia.
      specialize (Hbh ltac:(lia)).
      replace (b - cf_head + cf_head) with b in Hbh by lia. replace (m + cf_head - cf_head) with m in Hbh by lia.
      exact (pjp_hull_sub _ b m (je_t0 en) (je_len en) Hbh ltac:(lia) ltac:(lia)).
  - (* a registered read-only global: its bytes by the journal, its shadow by the zero-shadow law over the whole-granule
       range that holds it (pjp_zs_addr), its hull by the image shadow map (it lies 64 bytes inside the image) *)
    destruct VIS as (_ & VZ & VI).
    split; [|split].
    + intros x Hx. destruct (Hro x Hx) as (Hr & Hno & Her).
      apply F3; [exact (pjp_ro_img x Hr) | exact Hno | exact Her | exact (fun Hx' => pst_not_ro_B x Hx' Hr) |].
      apply fp_spares_closed. exact Hsink.
    + exact (pjp_zs_addr ly2 S2 Hp2 W2 mem2 md2 (je_t0 en) (je_len en) VZ HAR2 Hzs).
    + intros Hl0 s Hs. destruct (pjp_hull_img _ _ (je_t0 en) (je_len en) s Hl0 Hlo Hhi Hs) as [E Hr]. rewrite E.
      exact (VI ly2 S2 Hp2 W2 mem2 md2 _ HAR2 Hr).
  - (* an image string, by its const-shadow cells *)
    destruct VIS as (_ & VZ & VI).
    split; [|split].
    + intros x Hx. destruct (Hro x Hx) as (Hr & Hno & Her & _).
      apply F3; [exact (pjp_ro_img x Hr) | exact Hno | exact Her | exact (fun Hx' => pst_not_ro_B x Hx' Hr) |].
      apply fp_spares_closed. exact Hsink.
    + intros x Hx. destruct (Hro x Hx) as (_ & _ & _ & [Hzs8 | (v & Hcell & Hv)]).
      * exact (pjp_zs_addr ly2 S2 Hp2 W2 mem2 md2 (x - x mod 8) 8 VZ HAR2 Hzs8 x ltac:(clear - Hx; lia)).
      * pose proof (proj1 (Forall_forall _ _) (alx_const_cells SEGS B ARx LAWS ly2 S2 Hp2 W2 mem2 md2 HAR2) _ (Hcell ly2)) as Hc.
        specialize (Hc 0%nat ltac:(cbn; lia)). cbn [aeval c_at c_val c_w z1 c1 Z.of_nat] in Hc.
        exists v. split; [|exact Hv].
        unfold shadow_of_addr. unfold shadow_addr in Hc. rewrite Z.add_0_r in Hc. rewrite Hc. f_equal.
        unfold le_byte. cbn [Z.of_nat Z.mul]. rewrite Z.shiftr_0_r.
        destruct Hv as [-> | Hv]; [reflexivity|]. rewrite !Z.mod_small; lia.
    + intros Hl0 s Hs. destruct (pjp_hull_img _ _ (je_t0 en) (je_len en) s Hl0 Hlo Hhi Hs) as [E Hr]. rewrite E.
      exact (VI ly2 S2 Hp2 W2 mem2 md2 _ HAR2 Hr).
  - (* a live allocator block whose base is no hidden head *)
    destruct (Z_lt_le_dec 0 (je_len en)) as [Hl0 | Hl0].
    + pose proof (Hkeep _ Hbm) as Hbm2.
      pose proof (pjp_req m ltac:(lia)) as (_ & _ & Rm). specialize (Rm ltac:(lia)).
      assert (HnL' : ~ In (b + cf_head, m - cf_head) Lam').
      { intros Hin. apply (HnoHp2 b m Hbm ltac:(lia) HnHp). apply (Permutation_in _ (Permutation_sym HHp2)).
        apply in_map_iff. exists (b + cf_head, m - cf_head). split; [cbn; lia | exact Hin]. }
      destruct (alx_shadow SEGS B ARx LAWS ly2 S2 Hp2 W2 mem2 md2 b m HAR2 Hbm2
        (pjp_no_head_in ly2 S2 Hp2 W2 mem2 md2 Lam' peak' cnt' fail' ran' most own b m HAR2 HL2 Hbm2 HnL')) as [Hbs Hbh].
      rewrite Rm in Hbs, Hbh.
      split; [|split].
      * intros x Hx. replace x with (b + (x - b)) by lia.
        apply (F2 b m (x - b) Hbm Hbm2); [rewrite Rm; lia|]. replace (b + (x - b)) with x by lia. exact (HFP x Hx).
      * exact (block_shadow_range _ SHADOW_OFF b m (je_t0 en) (je_len en) Hbs ltac:(lia) ltac:(lia)).
      * intros _. exact (pjp_hull_sub _ b m (je_t0 en) (je_len en) Hbh ltac:(lia) ltac:(lia)).
    + split; [intros x Hx; lia|]. split; [apply range_addressable_nil; lia | intros H; lia]. }
destruct HK as (Hkv & Hra2 & Hhull2).
split.
- split; [|split; [exact H4096|]].
  + unfold bytes_at. apply (pjp_garr8_move W W2 mem mem2 (je_t0 en) (je_tl en) Hby). intros j Hj. apply Hkv. lia.
  + rewrite Hlen. split; [exact Hceil|]. split; [exact Hamr|]. split; [exact Hra2 | exact Hhull2].
- destruct Hhome as [[(b & m & Hin & Hb & Hm) | Hro] | (b & m & Hbm & HnHp & Hb & Hm)].
  + left. left. exists b, m. split; [exact (HLin _ _ Hin) | split; [exact Hb | exact Hm]].
  + left. right. exact Hro.
  + right. exists b, m. split; [exact (Hkeep _ Hbm)|].
    split; [exact (HnoHp2 b m Hbm ltac:(lia) HnHp)|]. split; [exact Hb | exact Hm].
Qed.

(* ---- THE SEGMENT ---- *)
Theorem pjp_seg_C1_holds : forall CTX0 CW,
  pjp_texts B ARx CTX0 CW -> pjp_frame_kept_stmt B ARx ->
  pjp_seg_C2ok B ARx CTX0 CW -> pjp_seg_C2ref B ARx CTX0 CW -> pjp_seg_C1 B ARx CTX0 CW.
Proof.
intros CTX0 CW TX FK SOK SREF en regs mem md k HPRE HC1.
destruct TX as (PV & _ & _ & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof pjp_code_rng as (K1 & K2 & K3 & K4 & K5 & K6).
pose proof pjp_stk as (HSt1 & HSt2).
pose proof (@cf_head_nonneg cp) as Hh0.
pose proof HPRE as (HFPRE & HCL & HCW & HWR & HROOM & _ & _ & _ & _ & HLEN & _ & _ & HMAXRUN & HFWIN & _ & HOUTC &
  HLAMAP & HTSEP & _ & HCNT & HRQ & HLIVE & HFRAMES & HMN0 & HPKS & HPK24 & HTCEIL & HRQM & HHB0).
(* the kit's cursor set at the entry, by name: its parse_items arm (the cursor end t0 + len); its parse_string arm is the
   C1 cut's slot conjunct HSLOT1 *)
unfold prh_cw_pj in HCW. destruct HCW as (HCWitems & _).
destruct HFPRE as (HAFN & _ & HSTKHI & _ & _).
destruct HAFN as (HAR0 & _ & _ & Hgp0 & Htp0 & Hstk0 & _ & _ & _).
destruct Hstk0 as (Hal16 & HSTK0 & Hceil0 & Hslo0 & Hshi0 & H470 & _ & Htop0 & Htop20).
destruct HFWIN as (Hd0 & Hd16 & Hdtop & _).
destruct HC1 as (HINV & HSLOT1 & R10 & R11 & HCUR & HZERO & HOUT & HTEXT & HLED).
destruct HINV as (HFZ & HFK & HJ & HWINK & HSP & HRAS & HS0S & R8 & RKEPT & HPRES & HADDR & HROD & HMN).
pose proof HJ as (HARc & _).
destruct (pjp_out_low en (je_ly en) (je_S en) (je_Hp en) (je_W en) mem md (je_Lam en) HOUT HARc) as (Hout56 & Hout8).
pose proof HOUT as (HO4096 & HOceil & HOplace & HOapart & HOrw & HOamr & HOown & HOra & HOhull).
pose proof HTEXT as (HSRC & HHOME).
pose proof HSRC as (_ & HT4096 & HTceil & _).
assert (Esp1 : je_sp1 en = je_sp0 en - 48) by reflexivity.
assert (Esp0 : je_sp0 en = spZ (je_regs en)) by reflexivity.
set (raw := Z_to_bv 64 (BASE + (PJP_C1 + 4))).
set (regs1 := regupd regs 1%bv raw).
assert (Hraw : bv_unsigned raw = BASE + PJP_C1 + 4) by (unfold raw; rewrite unsigned_lit_small by lia; lia).
assert (Esp : spZ regs1 = je_sp1 en) by (unfold regs1, spZ; rewrite getr_other by pjp_regne; exact HSP).
assert (Ers0 : s0Z regs1 = je_out en).
{ unfold regs1, s0Z. rewrite getr_other by pjp_regne. rewrite R8. unfold w64. apply unsigned_lit_small. lia. }
assert (Era : raZ regs1 = BASE + PJP_C1 + 4) by (unfold regs1, raZ; rewrite getr_same by pjp_regne; exact Hraw).
assert (Hrest : rest_atR (je_tl en) (je_t0 en) (je_t0 en) = je_tl en)
  by (unfold rest_atR; rewrite Z.sub_diag; reflexivity).
assert (Htrace : prhPj_ptrace (je_tl en) = prhPv_gtrace 0 (je_tl en)).
{ unfold prhPj_ptrace, prhPv_gtrace, PjGrammar.jr_run.
  destruct (PjGrammar.jr_value prh_jr_strtod 0%nat (je_tl en) []) as [[[[t r]|] tr] okr]; reflexivity. }
(* +0x4c: the jal, an SRr step lifted once into SRr' SEGS RZ_cf (the continuations' relation) *)
unfold pjp_cfg.
apply (YGcfRhLift.ra_rh_of_SRr SEGS YGcfRehidePost.RZ_cf).
eapply (SRr_step SEGS (@pa_wx _ B_prog_listing PA) (je_W en)); [reflexivity | rewrite restrict_mkst_fx; apply pjp_jal_step |].
intros md1 Hsame. cbn [ms_regs ms_mem YK11.mkst]. rewrite unrestrict_mkst_mrestrict.
rewrite (same_but_materialized_wvb md md1 Hsame).
apply SRr_ret. cbv beta.
pose proof (ajournal_x_materialize (SK := SK) SEGS B PST ARx LAWS (@pa_segs_low _ B_prog_listing PA)
  _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (m_vm_materialized md1) HJ) as HJ1.
set (md1' := with_vm_backing (m_vm_lazy md) (m_vm_materialized md1) md) in *.
pose proof HJ1 as (HAR1 & _).
(* the journal at the call moved to wle' SEGS RZ_cf, the relation of parse_value's post *)
pose proof (ajournal_xwR_mono (SK := SK) SEGS B PST ARx (@wle SEGS) (wle' SEGS YGcfRehidePost.RZ_cf)
  (wle_wle' SEGS YGcfRehidePost.RZ_cf) _ _ _ _ _ (je_Hp en) _ _ _ _ _ _ _ _ _ _ _ _ HJ1) as HJ1R.
(* pj_parse's frame at the call state, with the materialized model *)
assert (HINV1 : pjp_inv (fx := fx) B ARx en (je_S en) fx (je_ly en) (je_S en) (je_Hp en) (je_W en) regs mem md1' k).
{ split; [exact HFZ|]. split; [exact HFK|]. split; [exact HJ1|]. split; [exact HWINK|]. split; [exact HSP|].
  split; [exact HRAS|]. split; [exact HS0S|]. split; [exact R8|]. split; [exact RKEPT|].
  split; [exact HPRES|]. split; [exact HADDR|]. split; [exact HROD | exact HMN]. }
(* the call of parse_value; its hull budget is pj_parse's (the first part of pj_parse's all-granted list) *)
assert (HHB1 : PresetHullBudget.hull_budget (je_S en)
  (PresetReqAt.rd_hevs (prhPv_gtrace 0 (rest_atR (je_tl en) (je_t0 en) (je_t0 en))))).
{ rewrite Hrest. unfold prhPv_gtrace. change prh_jr_strtod with ReaderRes.jr_strtod.
  exact (pj_parse_counts.pjc_hull_budget_pv ReaderRes.jr_strtod cp (je_S en) (je_tl en) HHB0). }
assert (HFRAMES1 : Z.of_nat (length (frames (je_S en))) + Z.of_nat (Nat.succ (PjGrammar.MAXD - 0)%nat) <= fs_frames 0)
  by (rewrite Nat.sub_0_r; exact HFRAMES).
assert (HROOM1 : rd_room (je_S en) (prhPv_gtrace 0 (rest_atR (je_tl en) (je_t0 en) (je_t0 en)))).
{ rewrite Hrest. split; [exact HROOM|]. split; [rewrite <- Htrace; exact HRQ|]. exact (G_LIVE _ _ HH HLIVE). }
destruct (pjp_c1_univ CTX0 HCL) as (HMU & HRU1 & HRU2).
eapply (SRr'_bind SEGS YGcfRehidePost.RZ_cf).
{ eapply (YCbqGwild.aj_call_xWFbR (fx := fx) (SK := SK) SEGS B PST ARx LAWS (@pa_segs_low _ B_prog_listing PA)
    (wle' SEGS YGcfRehidePost.RZ_cf) (wle'_refl SEGS YGcfRehidePost.RZ_cf) (wle'_trans SEGS YGcfRehidePost.RZ_cf)
    (je_W en) regs1 mem
    (SIGMA AS_parse_value) (STK_pj_parse + je_d en) (je_sp0 en + je_d en) [(je_out en, je_out en + 56)]
    (je_ly en) (je_S en) (je_Hp en) (je_W en) (je_mem en) (je_md en) [] (je_ly en) (je_S en) (je_Hp en) md1' k []
    (STK_parse_value 0) 32 (rd_fp (je_sp1 en + 8) (je_out en)) (- (48 + je_d en)) raw [] (YCbqGwild.wbudget CW 0) _
    HJ1R).
  - rewrite Esp, Esp1. lia.
  - lia.
  - lia.
  - exact HSt1.
  - lia.
  - lia.
  - reflexivity.
  - lia.
  - unfold regs1. rewrite getr_other by pjp_regne. rewrite (RKEPT 3%bv ltac:(left; reflexivity)). exact Hgp0.
  - unfold regs1. rewrite getr_other by pjp_regne. rewrite (RKEPT 4%bv ltac:(right; left; reflexivity)). exact Htp0.
  - unfold regs1. apply getr_same. pjp_regne.
  - unfold raw. apply (ret_ok_codeptr_v (PI := PA)); lia.
  - rewrite Hraw. lia.
  - rewrite Ers0. apply achain_low. lia.
  - intros HPRE1 HWIN1.
    assert (HCUR1 : prh_cur_entry (PA := PA) (je_W en) mem regs1 (je_sp1 en + 8)).
    { apply (pjp_cur_ok (je_W en) mem regs1 (je_sp1 en) (je_t0 en) (je_len en) (je_tl en) Esp);
        [rewrite Ers0; lia | lia | rewrite Era; lia | lia | exact HCUR]. }
    assert (HCW1 : prh_cw_entry (PA := PA) B CW (je_W en) mem regs1 (je_sp1 en + 8)).
    { exact (pjp_cw_ok CW (je_W en) mem regs1 (je_sp1 en) (je_t0 en) (je_len en) (je_tl en) Esp
        HCWitems HSLOT1 HCUR). }
    assert (HNODE : prhPv_node (PA := PA) B (STK_parse_value 0) 32 (je_ly en) (je_S en) (je_W en) regs1 mem
      (je_Lam en) (je_out en)).
    { split; [exact HO4096|]. split; [exact Hout8|]. split; [exact HOrw|]. split; [exact HZERO|].
      split.
      { destruct HOplace as [(b & m & Hbm & HnL & Hb & Hm) | (cid & pos & Hcp & Hf1 & Hf2)].
        - right; left. exists b, m. split; [exact Hbm | split; [exact HnL | split; [exact Hb | exact Hm]]].
        - right; right; left. exists cid, pos. split; [exact Hcp | split; [exact Hf1 | exact Hf2]]. }
      split; [exact HOamr|].
      split; [intros a Ha; split; [exact (HOown a Ha) | rewrite Esp; lia]|].
      exact HOra. }
    assert (HRDPRE : rd_pre (fx := fx) (PA := PA) B (STK_parse_value 0) (je_ly en) (je_S en) (je_Hp en) (je_W en)
      regs1 mem (je_Lam en) (je_peak en) (je_cnt en) (je_fail en) (je_ran en) (je_most en) (je_own en) 32
      (je_sp1 en + 8) (je_t0 en) (je_len en) (je_t0 en) 0%nat (je_tl en) (je_out en)).
    { split; [exact HFZ|]. split; [exact HMU|]. split; [exact HRU1|]. split; [exact HRU2|]. split; [exact HCUR|].
      split; [exact HWIN1|]. split; [rewrite Esp; lia|]. split; [rewrite Esp; lia|]. split; [exact HADDR|].
      split; [exact HSRC|]. split; [exact HHOME|]. split; [exact HMAXRUN|]. split; [exact HNODE|].
      split; [right; lia|]. split; [exact HTSEP|]. split; [left; rewrite Esp; lia|]. split; [exact HLED|].
      split; [apply Nat.le_0_l|]. split; [rewrite Hrest, HLEN; lia | exact HTCEIL]. }
    assert (P5 : exists ch', achain (je_ly en) (aview SEGS (w_H (je_W en)) mem) (spZ regs1) (s0Z regs1) ch' /\
      spine ch' = spine []) by (exists []; split; [apply achain_low; rewrite Ers0; lia | reflexivity]).
    assert (P6 : spZ regs1 <= je_sp1 en + 8 < spZ regs1 + 16) by (rewrite Esp; lia).
    assert (P7 : getr regs1 10%bv = w64 (je_sp1 en + 8)) by (unfold regs1; rewrite getr_other by pjp_regne; exact R10).
    assert (P8 : getr regs1 11%bv = w64 (je_out en)) by (unfold regs1; rewrite getr_other by pjp_regne; exact R11).
    assert (P1 : spZ regs1 + 64 <= ly_stk_hi (je_ly en)) by (rewrite Esp; lia).
    (* the two room counts parse_value asks, over its all-granted events: a prefix of pj_parse's, whose peaks the
       text's two room-count premises bound (pj_parse_counts.v pjc_pkR_gtrace) *)
    assert (HPKS1 : Z.of_nat (PresetRun.pkR YGcfRoomLive.rl_sec_req (PresetRoom.rs_live (YGcfRoom.room_of_cf (je_S en)))
      (PresetReqAt.rd_hevs (prhPv_gtrace 0 (rest_atR (je_tl en) (je_t0 en) (je_t0 en)))))
      <= PresetLiveBounds.LSEC + PresetLiveBounds.DRV).
    { rewrite Hrest. unfold prhPv_gtrace. change prh_jr_strtod with ReaderRes.jr_strtod.
      pose proof (pj_parse_counts.pjc_pkR_gtrace ReaderRes.jr_strtod YGcfRoomLive.rl_sec_req
        (PresetRoom.rs_live (YGcfRoom.room_of_cf (je_S en))) (je_tl en)) as Hg. clear - Hg HPKS; lia. }
    assert (HPK241 : Z.of_nat (PresetRun.pkR (PresetRoom.in_cls YG00.kBatchClass)
      (PresetRoom.rs_live (YGcfRoom.room_of_cf (je_S en)))
      (PresetReqAt.rd_hevs (prhPv_gtrace 0 (rest_atR (je_tl en) (je_t0 en) (je_t0 en)))))
      <= PresetLiveBounds.L24 + PresetLiveBounds.DRV).
    { rewrite Hrest. unfold prhPv_gtrace. change prh_jr_strtod with ReaderRes.jr_strtod.
      pose proof (pj_parse_counts.pjc_pkR_gtrace ReaderRes.jr_strtod (PresetRoom.in_cls YG00.kBatchClass)
        (PresetRoom.rs_live (YGcfRoom.room_of_cf (je_S en))) (je_tl en)) as Hg. clear - Hg HPK24; lia. }
    assert (HRAc : raZ regs1 < YM05.alloc_ceiling) by (rewrite Era; lia).
    (* parse_value's premises, met by shape *)
    assert (HFPRE1 : fpre (PA := PA) B ARx (STK_parse_value 0) (je_ly en) (je_S en) (je_Hp en) (je_W en) regs1 mem md1' [])
      by exact (conj HPRE1 (conj HROD (conj P1 (conj HRAc HFZ)))).
    assert (HCTX1 : In (raZ regs1 :: spine []) [[raZ regs1]]) by (left; reflexivity).
    assert (HCUR1' : (spZ regs1 <= je_sp1 en + 8 < spZ regs1 + 16) \/
      (spZ regs1 + 16 <= je_sp1 en + 8 /\ exists ch', achain (je_ly en) (aview SEGS (w_H (je_W en)) mem) (spZ regs1)
         (prh_s0 F_parse_string (je_sp1 en + 8)) ch')) by (left; exact P6).
    eapply (PV fx [[raZ regs1]] (je_ly en) (je_S en) (je_Hp en) (je_W en) regs1 mem md1' [] 32 (je_sp1 en + 8)
      (je_t0 en) (je_len en) (je_t0 en) (je_tl en) (je_out en) (je_Lam en) (je_peak en) (je_cnt en) (je_fail en)
      (je_ran en) (je_most en) (je_own en)); eassumption.
  - intros a Ha. unfold rd_fp in Ha. rewrite !inFP_cons in Ha.
    destruct Ha as [Ha | [Ha | [Ha | Ha]]].
    + right; right; right. lia.
    + right; right; right. lia.
    + left. apply inFP_cons. left. exact Ha.
    + exfalso. exact (inFP_nil a Ha). }
cbv beta. intros W2 c2 Hwle (fx' & ly2 & S2 & Hp2 & regs2 & mem2 & md2 & k1 & WS1 & -> & HFZ2 & HFK2 & HPW & HJ2w & HJc &
  _ & HP2 & HQ).
replace (je_sp0 en + je_d en + - (48 + je_d en) + 32) with (je_sp1 en + 32) in HJc by (rewrite Esp1; lia).
(* THE REBASE (pj_parse_defs.v pjp_wb): pj_parse's journal from the entry with its depot moved to the return's, at
   the empty budget; parse_value's budget WS1 (wbudget CW 0) and the depot's wild-part inclusion are the cuts' pjp_wb *)
pose proof (YCbqGwild.ajournal_xw_rebaseR (SK := SK) SEGS B PST ARx (wle' SEGS YGcfRehidePost.RZ_cf)
  _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ2w) as HJ2.
assert (HWB2 : pjp_wb B CW en (set_depot (st_depot S2) (je_S en))).
{ exists (st_depot S2), WS1. split; [reflexivity|]. split; [exact HPW|]. exact (ajxR_wild HJ2w). }
unfold fQmn in HQ. cbv beta in HQ. destruct HQ as (HQ & HMK2).
(* parse_value's post, read through its kit names (PRH_FnParse.v tpvP_R_of, the fields of tpvP_R) *)
assert (HQv : tpvP_Q (PA := PA) B 0 (je_ly en) (je_S en) (je_sp1 en + 8) (je_t0 en) (je_len en) (je_t0 en) (je_tl en)
  (je_out en) (je_Lam en) (je_peak en) (je_cnt en) (je_fail en) (je_ran en) (je_most en) (je_own en)
  ly2 S2 Hp2 W2 regs2 mem2 md2) by exact HQ.
destruct (tpvP_R_of HQv) as (ok & res & tr & okr & D & Lam' & peak' & cnt' & fail' & ran' & HRv).
pose proof (tpvP_run HRv) as Hjr. pose proof (tpvP_ledger HRv) as HL2. pose proof (tpvP_room HRv) as HROOM2.
pose proof (tpvP_hull HRv) as HHU2. pose proof (tpvP_live HRv) as HLIVE2. pose proof (tpvP_pos HRv) as HADV.
pose proof (tpvP_outcome HRv) as HOUT1. pose proof (tpvP_injected HRv) as HINJ1.
pose proof (tpvP_ledger_move HRv) as HLM. pose proof (tpvP_blocks_move HRv) as HBM. pose proof (tpvP_arm HRv) as HRES.
clear HRv HQv HQ.
rewrite Hrest in Hjr, HLM, HBM, HOUT1, HHU2, HINJ1.
unfold tpvP_ASome, tpvP_ANone in HRES. rewrite Hrest in HRES.
pose proof HLM as (Hoks & _ & _ & HLam & _).
(* the memory overlay after the call: parse_value's m-form keep *)
assert (HMN2 : YAkMemnorm.memnorm SEGS mem2) by exact (HMK2 HMN).
(* parse_value's position transfer and live-set move after the call, from the entry state (the cut pjp_pos_pv) *)
assert (HPOS2 : pjp_pos_pv en S2 tr) by exact (conj HADV HLIVE2).
assert (Hsink1 : ~ YI16.sink_open_fp (rd_fp (je_sp1 en + 8) (je_out en))).
{ apply sink_closed_pos. unfold rd_fp. repeat constructor; cbn [fst]; lia. }
assert (HFP1 : forall a, inFP (rd_fp (je_sp1 en + 8) (je_out en)) a -> ~ (je_sp1 en + 32 <= a < je_sp0 en + je_d en)).
{ intros a Ha. unfold rd_fp in Ha. rewrite !inFP_cons in Ha. destruct Ha as [Ha | [Ha | [Ha | Ha]]].
  - lia.
  - lia.
  - rewrite Esp1. lia.
  - exfalso. exact (inFP_nil a Ha). }
destruct (FK en (je_S en) fx (je_ly en) (je_S en) (je_Hp en) (je_W en) regs mem md1' k (STK_parse_value 0) 32
  (rd_fp (je_sp1 en + 8) (je_out en)) ly2 S2 Hp2 W2 mem2 md2 k1 WS1 (pjp_inv_lift B ARx _ _ _ _ _ _ _ _ _ _ _ HINV1)
  HJc HSt1 ltac:(lia) Hd0 Hsink1 HFP1)
  as (KW & KRA & KS0 & KPRES & KADDR & KROD).
assert (Esp2 : spZ regs2 = je_sp1 en).
{ rewrite <- HSP. unfold spZ.
  exact (f_equal bv_unsigned (pjp_preserved regs regs2 raw 2 HP2 ltac:(unfold acallee_saved; lia) ltac:(pjp_regne))). }
assert (R8' : getr regs2 8%bv = w64 (je_out en)).
{ rewrite <- R8. exact (pjp_preserved regs regs2 raw 8 HP2 ltac:(unfold acallee_saved; lia) ltac:(pjp_regne)). }
assert (RKEPT2 : forall r, In r PJP_KEPT -> getr regs2 r = getr (je_regs en) r).
{ intros r Hr. rewrite <- (RKEPT r Hr). cbv [PJP_KEPT In] in Hr.
  repeat match type of Hr with _ \/ _ => destruct Hr as [Hr | Hr] | False => destruct Hr | _ = _ => subst r end;
  lazymatch goal with |- getr _ ?x = _ =>
    let z := eval vm_compute in (bv_unsigned x) in
    exact (pjp_preserved regs regs2 raw z HP2 ltac:(unfold acallee_saved; lia) ltac:(pjp_regne)) end. }
pose proof HJc as (HAR2 & _).
(* +0x50: the bnez, an SRr step lifted into SRr' *)
apply (YGcfRhLift.ra_rh_of_SRr SEGS YGcfRehidePost.RZ_cf).
eapply (SRr_step SEGS (@pa_wx _ B_prog_listing PA) W2); [reflexivity | rewrite restrict_mkst_fx; apply pjp_bnez_step |].
intros md3 Hsame3. cbn [ms_regs ms_mem YK11.mkst]. rewrite unrestrict_mkst_mrestrict.
rewrite (same_but_materialized_wvb md2 md3 Hsame3).
apply SRr_ret. cbv beta.
pose proof (ajournal_x_materializeR (SK := SK) SEGS B PST ARx LAWS (@pa_segs_low _ B_prog_listing PA)
  (wle' SEGS YGcfRehidePost.RZ_cf) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (m_vm_materialized md3) HJ2) as HJ3.
set (md3' := with_vm_backing (m_vm_lazy md2) (m_vm_materialized md3) md2) in *.
assert (HINV2 : pjp_invR (fx := fx) B ARx (wle' SEGS YGcfRehidePost.RZ_cf) en (set_depot (st_depot S2) (je_S en)) fx'
  ly2 S2 Hp2 W2 regs2 mem2 md3' (k + k1)).
{ split; [exact HFZ2|]. split; [exact HFK2|]. split; [exact HJ3|]. split; [exact KW|]. split; [exact Esp2|].
  split; [exact KRA|]. split; [exact KS0|]. split; [exact R8'|]. split; [exact RKEPT2|].
  split; [exact KPRES|]. split; [exact KADDR|]. split; [exact KROD | exact HMN2]. }
assert (HOUTFP : forall x, inFP (rd_fp (je_sp1 en + 8) (je_out en)) x ->
  YM05.alloc_ceiling <= x \/ je_out en <= x < je_out en + 56).
{ intros x Hx. unfold rd_fp in Hx. rewrite !inFP_cons in Hx.
  destruct Hx as [Hx | [Hx | [Hx | Hx]]]; [left; lia | left; lia | right; exact Hx | exfalso; exact (inFP_nil x Hx)]. }
destruct res as [[t r]|].
- (* a0 = 0: parse_value accepted a value; C2ok *)
  destruct HRES as (HR10 & HFOS & HCUR2 & HNODE2 & HNCAP2 & _).
  rewrite HR10. unfold w64. rewrite c_eq_refl.
  assert (Hrw2 : pj_rwR SEGS (rdW W2 mem2) (je_out en)).
  { destruct t; cbn [pj_nodeR] in HNODE2; destruct HNODE2 as (_ & _ & ? & ? & ? & ? & ? & ? & (Hrw & _) & _); exact Hrw. }
  apply (SOK en (set_depot (st_depot S2) (je_S en)) fx' ly2 S2 Hp2 W2 regs2 mem2 md3' (k + k1) HPRE HWB2).
  split; [exact HINV2|]. split; [exact HROOM2|]. split; [exact HHU2|].
  exists ok, t, r, tr, D, Lam', peak', cnt', fail', ran'.
  split; [split; [exists okr; exact Hjr | split; [exact HL2 | split; [exact HLM | exact HBM]]]|].
  split; [exact HPOS2|].
  split; [exact HOUT1|].
  split; [exact HCUR2|]. split; [exact HNODE2|]. split; [exact HNCAP2|].
  split.
  + exact (pjp_out_kept en (je_ly en) (je_S en) (je_Hp en) (je_W en) mem md1' (je_Lam en) ly2 S2 Hp2 W2 mem2 md2
      (STK_parse_value 0 + 32) (je_sp1 en + 32) (rd_fp (je_sp1 en + 8) (je_out en)) k1 D tr (je_tl en) 0%nat
      Lam' peak' cnt' fail' ran' (je_most en) (je_own en) WS1 HOUT HJc HAR1 HOUTFP HBM HLam HL2 Hrw2).
  + split; [|exact (conj HFOS HINJ1)].
    assert (HTFP : forall x, je_t0 en <= x < je_t0 en + je_len en -> ~ inFP (rd_fp (je_sp1 en + 8) (je_out en)) x).
    { intros x Hx Hin. unfold rd_fp in Hin. rewrite !inFP_cons in Hin.
      destruct Hin as [Hin | [Hin | [Hin | Hin]]]; [lia | lia | lia | exact (inFP_nil x Hin)]. }
    exact (pjp_text_kept en (je_ly en) (je_S en) (je_Hp en) (je_W en) mem md1' (je_Lam en) (je_peak en) (je_cnt en)
      (je_fail en) (je_ran en) ly2 S2 Hp2 W2 mem2 md2 (STK_parse_value 0 + 32) (je_sp1 en + 32)
      (rd_fp (je_sp1 en + 8) (je_out en)) k1 D tr (je_tl en) 0%nat Lam' peak' cnt' fail' ran' (je_most en) (je_own en)
      WS1 HTEXT HLED HJc HAR1
      Hsink1 HTFP HLEN HBM HLam HL2).
- (* a0 = -1: parse_value refused; C2ref *)
  destruct HRES as (HR10 & HFON & _ & HFD2).
  assert (Hc : c_eq (getr regs2 10%bv) (Z_to_bv 64 0) = false) by (rewrite HR10; vm_compute; reflexivity).
  rewrite Hc.
  assert (Hrw2 : pj_rwR SEGS (rdW W2 mem2) (je_out en)).
  { revert HFD2. generalize (PjGrammar.MAXD - 0)%nat. intros nd HFD2.
    destruct nd; cbn [pj_fdR] in HFD2; unfold pj_fshapeR in HFD2;
    destruct HFD2 as (_ & _ & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & (Hrw & _) & _); exact Hrw. }
  apply (SREF en (set_depot (st_depot S2) (je_S en)) fx' ly2 S2 Hp2 W2 regs2 mem2 md3' (k + k1) HPRE HWB2).
  split; [exact HINV2|]. split; [exact HROOM2|]. split; [exact HHU2|].
  (* pj_free's order list of the refused tree at DOC_D and its tie to the model's pj_frees (parse_value's None arm,
     in the kit's text: the partial tree's free order, at every bound >= MAXD) *)
  destruct (HFON HH DOC_D ltac:(unfold DOC_D; lia)) as (F & HFO & HTIEF).
  exists ok, None, tr, D, F, Lam', peak', cnt', fail', ran'.
  split; [split; [exists okr; exact Hjr | split; [exact HL2 | split; [exact HLM | exact HBM]]]|].
  split; [exact HPOS2|].
  split; [exact HOUT1|].
  split; [reflexivity|].
  split; [exact HFO|].
  split; [exact HTIEF|].
  split; [exact (pjp_out_kept en (je_ly en) (je_S en) (je_Hp en) (je_W en) mem md1' (je_Lam en) ly2 S2 Hp2 W2 mem2 md2
    (STK_parse_value 0 + 32) (je_sp1 en + 32) (rd_fp (je_sp1 en + 8) (je_out en)) k1 D tr (je_tl en) 0%nat
    Lam' peak' cnt' fail' ran' (je_most en) (je_own en) WS1 HOUT HJc HAR1 HOUTFP HBM HLam HL2 Hrw2)|].
  exact HINJ1.
Qed.

End s.
End t.
