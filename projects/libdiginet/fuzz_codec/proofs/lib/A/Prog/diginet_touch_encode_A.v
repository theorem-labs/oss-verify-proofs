(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: the run / keep / branch / leaf tactics, kept_run and same_io_wvb are the text of
   projects/reac-pw/fuzz_qdisc/proofs/lib/A/QPgSlots.v:123-188 (made there from proofs/libreac/fuzz_knock/lib/A/APgStep.v,
   origin/ossv/recipes 6ebe35ba632), the stack-slot write tactics that of QPgCheck.v:52-69, the entry regions those of
   QPgRt.v:61-65 / 193-243, the shadow entry that of proofs/libreac/fuzz_identity/lib/A/Prog/sb_dec.v:354-370
   (origin/ossv/recipes 4b6f0df50aa7), cw_U_sx32_eqb that of proofs/libreac/fuzz_knock/lib/A/APgStep.v:54-68
   (U_sx32_eqb, origin/ossv/recipes 4b6f0df50aa7), cw_join_win that of proofs/reac-pw/fuzz_qdisc/lib/A/QPgLoop0.v:169-196
   (ra_join_win, a working branch b0f706c04a19), cw_bcmp_at that of lib/Reusable/YCbq.v:2262-2310 (aj_bcmp_at) with
   the wrapper's same_but_materialized kept in its post, cw_st_ok_at that of lib/Reusable/YI04.v:342-356 (entry_st_ok_full)
   with the env apart from the registers, renamed with the prefix cw_ and moved to libdiginet/fuzz_codec's ASan
   build (image A); the leaf ends in lib/A/Prog/CPgBase.v's cdc_post, whose memory clause is CodecCJ's tcj_kept. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_codec/lib/A/Prog/CPgWalk.v; 220 of its 261 lines of code are new or changed and 592 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_codec/lib/A/Prog/check_range_A.v, with its numbers changed; 195 of its 237 lines of code are new or changed and 219 lines of the source are left out. *)
(* diginet_touch_encode in image A (0x84eb8, 93 instructions, frame 16, no call) against lib/A/Prog/CPgEncC.v's
   cdc_touch_specX. a0 = the personality p, a1 = strip (lw: the register holds s32 strip), a2 = on (an int),
   a3 = out. The engine stops, and each stop is split with its condition turned into a Z fact:
   0x84ec8 beqz a4 (a4 = p): with pd = None (p = 0) the TAKEN side returns a0 = -1 = E_ARG and writes nothing;
      the other side is refuted by p = 0 (tc_br_null). With pd = Some d the atom fact of p (p >= 1) decides it.
   0x84ecc beqz a3: decided by the atom fact of out (out >= 1).
   0x84ed0-0x84ed8 load the shadow offset through the .got slot 0x9db10; the walk stops at 0x84edc, drops the two
      cell regions and adds the personality byte 17 (the atom of d_strips d).
   0x84ee0-0x84eec, 0x84fc8-0x84fcc: the instrumented check of p + 17, decided by the shadow entry of [p + 16, p + 20).
   0x84ef4 bgeu a1,a0 (a0 = p->strips): TAKEN (d_strips d <= strip, tc_br_strips) returns a0 = -11 = E_RANGE and
      writes nothing; not taken: strip < d_strips d <= 64.
   0x84efc bgeu a0,a1 (a0 = 63): not taken (63 < strip, the path 0x84fa0-0x84fb8 that stores out->key after a failed
      button_encode) is refuted by strip < d_strips d <= 64 (tc_br_63); TAKEN: the stores out[0] = 0x90, out[1] = 9,
      out[2] = ((on != 0) << 6) | strip (tc_U_b2), out[24] = 3 (len), out[25] = 0 (display) and the 4-byte key
      0x80000 = KEY 8 0 at out + 28, each after its instrumented check (decided by the shadow entry of out), then
      a0 = 0. *)
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YN3v YI04 YI09 YI08.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YI16 YM05.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.A Require Import AWalkFw0 ACef AF0l ACej ACeh ACem ACep.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.A Require Import AWalkFw1 AWalkFw2 ACfm.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Spec Require Import DgnSpec DgnLib.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.A.Prog Require Import CodecCJ CPgBase CPgEncC CPgWalk CPgEncPers CPgEncOut.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

Definition A_TOUCH : Z := 0x84eb8.

(* ---- the arithmetic of the walk, over the engine's symbolic values ---- *)
(* the strip register: arg_u32A puts s32 strip there, so a strip >= 2^31 reads as a number >= 2^64 - 2^31 *)
Lemma tc_U11 : forall E n strip, ew E n = Z_to_bv 64 (s32 strip) -> 0 <= strip < 2 ^ 32 ->
U E (SOff n 0) = if strip <? 2 ^ 31 then strip else strip + (2 ^ 64 - 2 ^ 32).
Proof.
intros E n strip H Hs. rewrite U_SOff, H, Z.add_0_r, unsigned_lit. unfold zcanon, M64. rewrite Zmod_mod. unfold s32.
destruct (Z.ltb_spec strip (2 ^ 31)).
- apply Z.mod_small. lia.
- replace (strip - 2 ^ 32) with ((strip + (2 ^ 64 - 2 ^ 32)) + (-1) * 2 ^ 64) by lia.
  rewrite Z.mod_add by lia. apply Z.mod_small. lia.
Qed.
(* an int argument: the register holds on sign-extended; it reads as 0 exactly when on = 0 *)
Lemma tc_U12_pos : forall E n on, ew E n = Z_to_bv 64 on -> - 2 ^ 31 <= on < 2 ^ 31 -> on <> 0 -> 0 < U E (SOff n 0).
Proof.
intros E n on H Hon Hne. rewrite U_SOff, H, Z.add_0_r, unsigned_lit. unfold zcanon, M64. rewrite Zmod_mod.
destruct (Z.ltb_spec on 0).
- rewrite <- (Z.mod_add on 1 (2 ^ 64)) by lia. rewrite Z.mod_small by lia. lia.
- rewrite Z.mod_small by lia. lia.
Qed.
Lemma tc_U12_0 : forall E n, ew E n = Z_to_bv 64 0 -> U E (SOff n 0) = 0.
Proof. intros E n H. apply (U_atom E n 0 H). lia. Qed.
(* 0x84ec8 beqz a4 with p = 0: TAKEN *)
Lemma tc_br_null : forall E n, ew E n = Z_to_bv 64 0 ->
branch_taken BC_EQ (sv_denot E (SOff n 0)) (sv_denot E (SLit 0)) = true.
Proof. intros E n H. rewrite branch_eq_U, (tc_U12_0 E n H), U_lit by lia. reflexivity. Qed.
(* 0x84ef4 bgeu a1,a0: a1 the strip register, a0 = p->strips (the atom ds of the personality byte) *)
Lemma tc_br_strips : forall E n m strip ds, ew E n = Z_to_bv 64 (s32 strip) -> ew E m = Z_to_bv 64 ds ->
0 <= strip < 2 ^ 32 -> 0 <= ds < 256 ->
branch_taken BC_GEU (sv_denot E (SOff n 0)) (sv_denot E (SOff m 0)) = (ds <=? strip).
Proof.
intros E n m strip ds Hn Hm Hs Hd. rewrite branch_geu_U, (tc_U11 E n strip Hn Hs), (U_atom E m ds Hm) by lia.
destruct (Z.ltb_spec strip (2 ^ 31)).
- destruct (Z.ltb_spec strip ds); destruct (Z.leb_spec ds strip); cbn [negb]; first [reflexivity | lia].
- destruct (Z.ltb_spec (strip + (2 ^ 64 - 2 ^ 32)) ds); destruct (Z.leb_spec ds strip); cbn [negb]; first [reflexivity | lia].
Qed.
(* 0x84efc bgeu a0,a1 with a0 = 63, below 2^31 *)
Lemma tc_br_63 : forall E n strip, ew E n = Z_to_bv 64 (s32 strip) -> 0 <= strip < 2 ^ 31 ->
branch_taken BC_GEU (sv_denot E (SLit 63)) (sv_denot E (SOff n 0)) = (strip <=? 63).
Proof.
intros E n strip Hn Hs. rewrite branch_geu_U, U_lit, (tc_U11 E n strip Hn) by lia.
destruct (Z.ltb_spec strip (2 ^ 31)); [|lia].
destruct (Z.ltb_spec 63 strip); destruct (Z.leb_spec strip 63); cbn [negb]; first [reflexivity | lia].
Qed.
(* the byte 0x84f58-0x84f68 store at out + 2: snez a2; slli 6; or a1 *)
Definition tc_b2 : sv :=
SAlu ALU_OR (SAlu ALU_SLL (SAlu ALU_SLTU (SLit 0) (SOff 12 0)) (SLit 6)) (SOff 11 0).
Lemma tc_U_b2 : forall E strip on, ew E 11 = Z_to_bv 64 (s32 strip) -> ew E 12 = Z_to_bv 64 on ->
0 <= strip <= 63 -> - 2 ^ 31 <= on < 2 ^ 31 ->
U E tc_b2 mod 256 = u8 (Z.lor (bit_or_0 (negb (on =? 0)) 0x40) strip).
Proof.
intros E strip on H11 H12 Hs Hon. unfold tc_b2, u8. rewrite U_SAlu. unfold zcanon at 1, M64.
rewrite (Z.mod_mod_divide _ (2 ^ 64) 256) by (exists (2 ^ 56); reflexivity).
rewrite !U_SAlu, !U_SLit, (tc_U11 E 11 strip H11) by lia.
destruct (Z.ltb_spec strip (2 ^ 31)); [|lia]. cbn [zalu_raw].
change (zcanon 0) with 0. change (zcanon 6) with 6. change (Z.land 6 63) with 6.
destruct (Z.eqb_spec on 0) as [->|Hne].
- rewrite (tc_U12_0 E 12 H12). reflexivity.
- rewrite (proj2 (Z.ltb_lt 0 (U E (SOff 12 0)))) by exact (tc_U12_pos E 12 on H12 Hon Hne). reflexivity.
Qed.
(* ---- the result on each path ---- *)
Lemma tc_spec_null : forall strip on, touch_spec None strip on = (E_ARG, None).
Proof. reflexivity. Qed.
Lemma tc_spec_range : forall d strip on, d_strips d <= strip -> touch_spec (Some d) strip on = (E_RANGE, None).
Proof. intros d strip on H. unfold touch_spec. cbv iota beta. rewrite (proj2 (Z.leb_le _ _) H). reflexivity. Qed.
Lemma tc_spec_ok : forall d strip on, 0 <= strip < d_strips d -> d_strips d <= 64 ->
touch_spec (Some d) strip on = (0, Some ([0x90; 9; u8 (Z.lor (bit_or_0 (negb (on =? 0)) 0x40) strip)], KEY 8 0, 0)).
Proof.
intros d strip on Hs Hd. unfold touch_spec, button_spec, with_key. cbv iota beta.
rewrite (proj2 (Z.leb_gt (d_strips d) strip)) by lia. rewrite (proj2 (Z.ltb_ge 0x3f strip)) by lia.
reflexivity.
Qed.

(* ---- the walk ---- *)
Ltac tc_ew := rewrite ?ew_ewset_other, ?ew_havoc_old by (cbn; lia).
(* an atom equation of the walk's base env, restated for the current env *)
Ltac tc_atom En := first [exact En | tc_ew; exact En].
(* a0 at the `ret`: the engine's literal is the return code mod 2 ^ 64 *)
Ltac tc_a0 :=
lazymatch goal with R10 : getr _ (10%bv : bv 5) = _ |- _ => rewrite R10 end;
cbn [fst sv_denot]; unfold w64, E_ARG, E_RANGE; apply bv_eq; rewrite !Z_to_bv_unsigned; reflexivity.
Ltac tc_side := idtac; lia.
(* the byte goal at out + o from the 1-byte chunk at offset o of a window of out *)
Ltac tc_byte :=
lazymatch goal with |- _ _ _ (?q + ?o) = Some (Z_to_bv 8 _) =>
lazymatch goal with Hc : YP09.chunk_ok _ _ _ q (YP09.mkChunk o (CVal 1 _)) |- _ => apply (ceo_chunk1 _ _ _ _ _ _ Hc) end end.

Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section d.
Variable B : asyms.
Variable MT : ameter_ops.
Hypothesis MTL : ameter_laws MT.
Hypothesis TL : TfibLib B.
Hypothesis LAWS : AR_laws tfibsegs B.

Theorem diginet_touch_encode_A_holds : cdc_touch_specX tfibsegs B MT A_TOUCH.
Proof using MTL TL LAWS.
unfold cdc_touch_specX.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs pd p strip on out before HE H10 HP H64 H11 H12 H13 HO HD.
pose proof Hwx_tfa as Hwx. pose proof tfib_segs_low as Hsegs.
pose proof (cw_entry_stack B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs T_touch HE ltac:(unfold T_touch; lia))
  as (Hceil & H47 & H46 & Hal & Hpres).
pose proof HE as (HJ & Hra & Hra4 & Hgp & Htp & _ & Hwlo & Hwhi & _).
pose proof HJ as HJw. pose proof (proj1 HJ) as HAR.
destruct H11 as [Hs H11]. destruct H12 as [Hon H12].
destruct HO as (Hcd & Hbef & Hlen).
pose proof Hcd as (Hout0 & Hout1 & Htd & Htw & Hra32 & Hhull & Ham & Hwin).
unfold T_touch in *. unfold coff_win in Hwin.
assert (Hob : out + 32 <= 2 ^ 47 - 1) by (unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in Ham; lia).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
(* the kept-memory fact: everything off the save area, until the success path opens out's windows *)
assert (KE : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 16 <= a < spZ regs) ->
  aview tfibsegs (w_H W) memc a = aview tfibsegs (w_H W) memc a) by (intros; reflexivity).
unfold cfg_at. change (w64 A_TOUCH) with (Z_to_bv 64 A_TOUCH).
destruct pd as [d|].
2: {
(* p = NULL *)
cbn [pers_argA] in HP. subst p.
set (E := Ereg regs (cw_extra [])).
assert (HAE : env_agree 32 (Ereg regs (cw_extra [])) E) by (subst E; apply env_agree_refl).
assert (E1 : ew E 1 = getr regs 1) by (subst E; exact (cw_ew_reg regs _ 1 1%bv eq_refl)).
assert (B2 : bv_unsigned (ew E 2) = spZ regs) by (subst E; rewrite (cw_ew_reg regs _ 2 2%bv eq_refl); reflexivity).
assert (E10 : ew E 10 = Z_to_bv 64 0) by (subst E; rewrite (cw_ew_reg regs _ 10 10%bv eq_refl); exact H10).
assert (E13 : ew E 13 = Z_to_bv 64 out) by (subst E; rewrite (cw_ew_reg regs _ 13 13%bv eq_refl); exact H13).
assert (E32 : ew E 32 = Z_to_bv 64 SB) by (subst E; apply cw_ew_SB).
assert (B13 : bv_unsigned (ew E 13) = out) by (rewrite E13; apply unsigned_lit_small; lia).
pose proof (ceo_entry B TL LAWS A_TOUCH [] 13 13%bv [] STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs 16 out
  HE ltac:(lia) eq_refl H13 Hcd I) as HS.
fold E in HS.
assert (SHOK : sh_ok tfibsegs CW_Bx [mkSHE 13 0 32] E (mrestrict (w_H W) memc)).
{ apply Forall_cons; [|apply Forall_nil].
  exact (cw_shent_cdst B STK sp0 FP ly S lyc Sc own W memc (spZ regs) 16 E 13 out 32 Hcd E13 E32 ltac:(lia)). }
clearbody E.
(* 0x84eb8-0x84ec4: frame, a4 = p, a0 = -1; stop at 0x84ec8 beqz a4 *)
cw_run ltac:(ceo_awr Htw). cw_keep ceo_kwr.
cw_branch Hc.
- (* TAKEN: to 0x84fbc, a0 = -1 = E_ARG, nothing written *)
  clear Hc. cw_run ltac:(ceo_awr Htw). cw_keep ceo_kwr.
  cw_leaf ltac:(idtac; cw_kept HJ KE ltac:(idtac; intros a Ha Himg; exact (ceo_eimg B LAWS _ _ _ _ _ _ _ _ _ _ mdc _ _ out a HAR Hcd Ha Himg))
     ltac:(idtac; intros a Ha; left; exact Ha))
   ltac:(rewrite (tc_spec_null strip on);
         eapply ceo_res_fail; [exact Hbef | exact Hlen | lia | lia | exact Hwin | eassumption | tc_a0]).
- (* not taken: refuted by p = 0 *)
  exfalso. rewrite (tc_br_null _ 10 ltac:(tc_atom E10)) in Hc. discriminate Hc.
}
(* pd = Some d *)
specialize (H64 d eq_refl).
pose proof (pers_some B W memc (spZ regs) 16 p d HP) as (Hp & Bds & Hv17 & Hpwin & Hcrd).
pose proof (pers_off_zone B W memc (spZ regs) 16 p d out 32 HP HD) as (Hz17s & Hz17o).
cbn [cpers_disj] in HD. unfold PERS_HI in Hp.
set (E := Ereg regs (cw_extra [d_strips d])).
assert (HAE : env_agree 32 (Ereg regs (cw_extra [d_strips d])) E) by (subst E; apply env_agree_refl).
assert (E1 : ew E 1 = getr regs 1) by (subst E; exact (cw_ew_reg regs _ 1 1%bv eq_refl)).
assert (B2 : bv_unsigned (ew E 2) = spZ regs) by (subst E; rewrite (cw_ew_reg regs _ 2 2%bv eq_refl); reflexivity).
assert (E10 : ew E 10 = Z_to_bv 64 p) by (subst E; rewrite (cw_ew_reg regs _ 10 10%bv eq_refl); exact H10).
assert (E11 : ew E 11 = Z_to_bv 64 (s32 strip)) by (subst E; rewrite (cw_ew_reg regs _ 11 11%bv eq_refl); exact H11).
assert (E12 : ew E 12 = Z_to_bv 64 on) by (subst E; rewrite (cw_ew_reg regs _ 12 12%bv eq_refl); exact H12).
assert (E13 : ew E 13 = Z_to_bv 64 out) by (subst E; rewrite (cw_ew_reg regs _ 13 13%bv eq_refl); exact H13).
assert (E32 : ew E 32 = Z_to_bv 64 SB) by (subst E; apply cw_ew_SB).
assert (E33 : ew E 33 = Z_to_bv 64 (d_strips d)) by (subst E; exact (cw_ew_x regs [d_strips d] 0)).
assert (B13 : bv_unsigned (ew E 13) = out) by (rewrite E13; apply unsigned_lit_small; lia).
assert (B10 : bv_unsigned (ew E 10) = p) by (rewrite E10; apply unsigned_lit_small; lia).
pose proof (ceo_entry B TL LAWS A_TOUCH [d_strips d] 13 13%bv (pers_AF 33) STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc
  k regs 16 out HE ltac:(lia) eq_refl H13 Hcd) as HS.
specialize (HS (pers_atoms_ok _ 33 p (d_strips d) E10 E33 ltac:(unfold PERS_HI; lia) Bds)).
fold E in HS.
assert (SHOK : sh_ok tfibsegs CW_Bx [mkSHE 13 0 32; pers_SH] E (mrestrict (w_H W) memc)).
{ apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
  - exact (cw_shent_cdst B STK sp0 FP ly S lyc Sc own W memc (spZ regs) 16 E 13 out 32 Hcd E13 E32 ltac:(lia)).
  - exact (pers_shent B lyc Sc W memc mdc (spZ regs) 16 E p d HAR HP E10 E32). }
clearbody E.
(* 0x84eb8-0x84ed8: frame, the two beqz decided by the atom facts, the two cell loads; stop at 0x84edc *)
cw_run_to ltac:(ceo_awr Htw) 0x84edc. cw_keep ceo_kwr.
(* drop the two cell regions, add the byte p + 17 (kept since the entry: it is off the save area) *)
pers_swap_tac E10 E33 Hv17 ltac:(idtac; apply KE; [lia | exact Hz17s]) pers_disj.
(* 0x84edc-0x84ef0: the check of p + 17 (decided), lbu p->strips; stop at 0x84ef4 bgeu a1,a0 *)
cw_run ltac:(ceo_awr Htw). cw_keep ceo_kwr.
cw_branch Hc1.
- (* TAKEN: d_strips d <= strip, to 0x84fbc with a0 = -11 = E_RANGE, nothing written *)
  lazymatch type of Hc1 with branch_taken _ (sv_denot ?Ev _) _ = _ =>
    rewrite (tc_br_strips Ev 11 33 strip (d_strips d) ltac:(tc_atom E11) ltac:(tc_atom E33) Hs ltac:(lia)) in Hc1 end.
  apply Z.leb_le in Hc1.
  cw_run ltac:(ceo_awr Htw). cw_keep ceo_kwr.
  cw_leaf ltac:(idtac; cw_kept HJ KE ltac:(idtac; intros a Ha Himg; exact (ceo_eimg B LAWS _ _ _ _ _ _ _ _ _ _ mdc _ _ out a HAR Hcd Ha Himg))
     ltac:(idtac; intros a Ha; left; exact Ha))
   ltac:(rewrite (tc_spec_range d strip on Hc1);
         eapply ceo_res_fail; [exact Hbef | exact Hlen | lia | lia | exact Hwin | eassumption | tc_a0]).
- (* not taken: strip < d_strips d <= 64 *)
  lazymatch type of Hc1 with branch_taken _ (sv_denot ?Ev _) _ = _ =>
    rewrite (tc_br_strips Ev 11 33 strip (d_strips d) ltac:(tc_atom E11) ltac:(tc_atom E33) Hs ltac:(lia)) in Hc1 end.
  apply Z.leb_gt in Hc1.
  cw_run ltac:(ceo_awr Htw). cw_keep ceo_kwr.
  cw_branch Hc2.
  + (* TAKEN (strip <= 63): 0x84f10-0x84f1c check out + 0 (decided); stop at the first store 0x84f28 *)
    clear Hc2.
    cw_run ltac:(ceo_awr Htw). cw_keep ceo_kwr.
    (* open out's three windows [0, 3), [24, 26), [28, 32) (out is off the save area, so kept since the entry) *)
    lazymatch goal with HS : YP0l.st_ok _ ?Ev ?ss (restrict (w_H W) ?ms), K : forall a, _ -> ~ _ -> aview _ _ _ a = _ |- _ =>
      assert (KO : forall a, out <= a < out + 32 -> aview tfibsegs (w_H W) (ms_mem ms) a = aview tfibsegs (w_H W) memc a)
        by (intros a Ha; apply K; lia);
      assert (B13e : bv_unsigned (ew Ev 13) = out) by (tc_ew; exact B13);
      pose proof (ceo_add3 B LAWS STK sp0 FP ly S lyc Sc own W memc mdc (spZ regs) 16 Ev ss ms 13 out 3 HAR Hcd HS B13e
        ltac:(lia) KO) as HS3;
      pose proof (ceo_KE_widen _ _ _ _ out 3 K) as KE3 end.
    specialize (HS3 ltac:(ceo_disj tc_side) ltac:(ceo_disj tc_side) ltac:(ceo_disj tc_side)).
    clear KE. rename KE3 into KE. clear KO B13e HS. rename HS3 into HS.
    lazymatch type of HS with YP0l.st_ok _ ?Ev ?ss2 ?msx =>
      let ss3 := eval vm_compute in ss2 in change (YP0l.st_ok tfibsegs Ev ss3 msx) in HS end.
    (* 0x84f20-0x84fb8: out[0] = 0x90, out[1] = 9, out[2] = ((on != 0) << 6) | strip, out[24] = 3, out[25] = 0, the
       key 0x80000 at out + 28, each check decided; a0 = 0 at the `ret` *)
    cw_run ltac:(ceo_awr Htw). cw_keep ceo_kwr.
    cw_leaf ltac:(idtac; cw_kept HJ KE ltac:(idtac; intros a Ha Himg; exact (ceo_eimg B LAWS _ _ _ _ _ _ _ _ _ _ mdc _ _ out a HAR Hcd Ha Himg))
       ltac:(idtac; intros a Ha; unfold ceo_zone in Ha; unfold cenc_wr; lia))
     idtac.
    rewrite (tc_spec_ok d strip on ltac:(lia) H64). unfold cenc_res. cbn [fst snd]. split; [tc_a0|].
    lazymatch goal with HS : YP0l.st_ok _ ?Ev _ _ |- _ => ceo_chunks HS;
      pose proof (tc_U_b2 Ev strip on ltac:(tc_atom E11) ltac:(tc_atom E12) ltac:(lia) Hon) as Hb2 end.
    unfold tc_b2 in Hb2.
    apply (ceo_res_ok (w_H W) memc _ out before [0x90; 9; u8 (Z.lor (bit_or_0 (negb (on =? 0)) 0x40) strip)] (KEY 8 0) 0
      Hlen ltac:(cbn; lia) Hbef).
    * intros j Hj. cbn [length] in Hj.
      destruct j as [|[|[|j]]];
      [change (Z.of_nat 0) with 0 | change (Z.of_nat 1) with 1 | change (Z.of_nat 2) with 2 | lia];
      cbn [nth]; tc_byte.
      -- rewrite U_lit by lia. reflexivity.
      -- rewrite U_lit by lia. reflexivity.
      -- rewrite Hb2. unfold u8. rewrite Z.mod_mod by lia. reflexivity.
    * cbn [length Z.of_nat]. tc_byte. rewrite U_lit by lia. reflexivity.
    * tc_byte. rewrite U_lit by lia. reflexivity.
    * lazymatch goal with Hc : YP09.chunk_ok _ _ _ out (YP09.mkChunk 28 (CVal 4 _)) |- _ =>
        apply (ceo_chunk4 _ _ _ _ _ _ Hc) end.
      rewrite U_lit by lia. reflexivity.
    * intros a Ha. cbn [length Z.of_nat] in Ha. apply KE; [lia | unfold ceo_zone; lia].
  + (* not taken: 63 < strip, refuted by strip < d_strips d <= 64 (the path 0x84fa0-0x84fb8) *)
    exfalso. lazymatch type of Hc2 with branch_taken _ _ (sv_denot ?Ev _) = _ =>
      rewrite (tc_br_63 Ev 11 strip ltac:(tc_atom E11) ltac:(lia)) in Hc2 end. apply Z.leb_gt in Hc2. lia.
Qed.
End d.
End b.
