(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: proofs/libreac/fuzz_knock/lib/A/APgRt.v (rt_hand, fs_roF / fs_rwF) and
   APgStep.v (same_io_wvb) at 6ebe35ba632; adapted to the class-0 frame and the exit of reac_box_pin_parse. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_pin/lib/A/PPgParse4.v, with its module paths and module names changed; 262 of its 291 lines of code are new or changed and 251 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_codec/lib/A/Prog/check_personality_A.v, with its module paths and module names changed; 165 of its 198 lines of code are new or changed and 258 lines of the source are left out. *)
(* diginet_button_encode (diginet_codec.c:113-122), image B 0x855dc, 90 instructions, frame 16, no call: the walk
   against lib/AU/Prog/CPgEncU.v's cdcU_button_specX. a0 = button, a1 = id (both lw: sign-extended from bit 31),
   a2 = on (an int), a3 = out (atom 13). The image-A walk's paths (lib/A/Prog/diginet_button_encode_A.v) with image
   B's addresses; image B adds one UBSan check, 0x855fc andi a4,a3,3; bnez a4 (out not 4-aligned, trap at 0x856dc
   unimp), which the engine decides from out's atom fact ceo_fact 13 (out mod 4 = 0).
   0x855dc addi sp,sp,-16 and 0x855e0 sd ra,8(sp) open the frame (the save area [sp - 16, sp)); 0x855e4 beqz a3 is
   decided by out's fact. The engine stops at two branches (a4 = -11 is set before both):
   B1 0x855f0 bltu a5,a0 with a5 = 127: BC_LTU 127 a0, which btn_lt turns into 127 < button.
      TAKEN: to 0x856cc mv a0,a4; ld ra; addi sp; ret: a0 = -11 = E_RANGE, nothing written (ceo_res_fail).
   B2 0x855f8 bltu a5,a1 with a5 = 63: 63 < id.  TAKEN: the same return with -11.
      not taken (button <= 127, id <= 63): out's three windows are added (ceo_add3). The alignment check of out is
      decided; 0x85604-0x8560c load the shadow base through the .got slot 0x9e430; the instrumented checks before the
      stores at out + 0, 1, 2, 24, 25 (1 byte) and out + 28 (4 bytes) are decided by the shadow entry mkSHE 13 0 32;
      the stores put 0x90, button, (on <> 0) << 6 | id at out[0..3) (btn_byte1, btn_byte2), 3 and 0 at out[24],
      out[25], and button << 8 | id | 0x20000 = KEY 2 (button * 256 | id) at out[28..32) (btn_key); a0 = 0 at
      `ret` (ceo_res_ok). *)
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
(* the spec first: DgnLib's st_ok (a running status) must not hide the engine's st_ok *)
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Spec Require Import DgnSpec DgnLib.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YI16 YM05.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.AU Require YImgTopU.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.AU Require Import AWalkFw0 YCef YF0l YCej YCeh YCem YCep.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.AU Require Import AWalkFw1 AWalkFw2 YCfm.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.A.Prog Require Import CodecCJ CPgBase CPgEncC.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.AU.Prog Require Import CPgBaseU CPgEncU CPgWalkU CPgEncOutU.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

(* ---- the two branches and the stored values ---- *)
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
(* `bltu c, a` with a = the lw of an unsigned v (sign-extended from bit 31): taken exactly when c < v *)
Lemma btn_lt : forall E n v c, ew E n = Z_to_bv 64 (s32 v) -> 0 <= v < 2 ^ 32 -> 0 <= c < 2 ^ 31 ->
(U E (SLit c) <? U E (SOff n 0)) = (c <? v).
Proof.
intros E n v c H Hv Hc. rewrite U_lit by lia. rewrite U_SOff, H, Z_to_bv_unsigned, Z.add_0_r.
unfold zcanon, M64, bv_wrap. change (bv_modulus 64) with (2 ^ 64). unfold s32.
destruct (Z.ltb_spec v (2 ^ 31));
match goal with |- (c <? ?x) = _ => destruct (Z.ltb_spec c x) end; destruct (Z.ltb_spec c v);
first [reflexivity | exfalso; lia].
Qed.
(* a or b = a + b when b is below 2 ^ k and a is a multiple of 2 ^ k *)
Lemma btn_lor_add : forall a b k, 0 <= k -> 0 <= a < 2 ^ k -> b mod 2 ^ k = 0 -> Z.lor a b = a + b.
Proof.
intros a b k Hk Ha Hb.
assert (Hl : Z.land a b = 0).
{ apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec, Z.bits_0. destruct (Z.ltb_spec i k).
  - rewrite <- (Z.mod_pow2_bits_low b k i) by lia. rewrite Hb, Z.bits_0. apply andb_false_r.
  - rewrite <- (Z.mod_small a (2 ^ k)) by lia. rewrite (Z.mod_pow2_bits_high a k i) by lia. reflexivity. }
rewrite <- (Z.lxor_lor _ _ Hl). symmetry. exact (Z.add_nocarry_lxor _ _ Hl).
Qed.
(* out[1] = button *)
Lemma btn_byte1 : forall E button, ew E 10 = Z_to_bv 64 (s32 button) -> 0 <= button <= 127 ->
U E (SOff 10 0) mod 256 = u8 button mod 256.
Proof.
intros E button H Hb. rewrite (ceo_U_off E 10 (s32 button) 0 H). unfold s32, u8.
destruct (Z.ltb_spec button (2 ^ 31)); [|lia]. rewrite Z.add_0_r, Z.mod_mod by lia. reflexivity.
Qed.
(* out[2] = (on <> 0) << 6 | id *)
Lemma btn_byte2 : forall E on id, ew E 12 = Z_to_bv 64 on -> - 2 ^ 31 <= on < 2 ^ 31 ->
ew E 11 = Z_to_bv 64 (s32 id) -> 0 <= id <= 63 ->
U E (SAlu ALU_OR (SAlu ALU_SLL (SAlu ALU_SLTU (SLit 0) (SOff 12 0)) (SLit 6)) (SOff 11 0)) mod 256
= u8 (Z.lor (bit_or_0 (negb (on =? 0)) 0x40) id) mod 256.
Proof.
intros E on id H12 Hon H11 Hid.
assert (U12 : U E (SOff 12 0) = on mod 2 ^ 64).
{ rewrite U_SOff, H12, Z_to_bv_unsigned, Z.add_0_r. unfold zcanon, M64, bv_wrap. change (bv_modulus 64) with (2 ^ 64).
  apply Z.mod_mod. lia. }
assert (U11 : U E (SOff 11 0) = id).
{ apply U_atom; [rewrite H11; unfold s32; destruct (Z.ltb_spec id (2 ^ 31)); [reflexivity | lia] | lia]. }
rewrite !U_SAlu. cbn [zalu_raw]. rewrite U12, U11, !U_lit by lia.
change (Z.land 6 63) with 6. unfold zcanon, M64, u8.
rewrite (Z.mod_mod_divide _ (2 ^ 64) 256) by (exists (2 ^ 56); reflexivity).
rewrite Z.mod_mod by lia. f_equal. f_equal.
destruct (Z.eqb_spec on 0) as [-> | Hne]; [reflexivity|].
assert (Hp : 0 < on mod 2 ^ 64) by lia.
destruct (Z.ltb_spec 0 (on mod 2 ^ 64)); [reflexivity | lia].
Qed.
(* out[28..32) = button << 8 | id | 0x20000 = KEY 2 (button * 256 | id) *)
Lemma btn_key : forall E button id, ew E 10 = Z_to_bv 64 (s32 button) -> 0 <= button <= 127 ->
ew E 11 = Z_to_bv 64 (s32 id) -> 0 <= id <= 63 ->
U E (SAlu ALU_OR (SAlu ALU_OR (SAlu ALU_SLL (SOff 10 0) (SLit 8)) (SOff 11 0)) (SLit 131072)) mod 2 ^ 32
= KEY 2 (Z.lor ((button * 256) mod 2 ^ 32) id) mod 2 ^ 32.
Proof.
intros E button id H10 Hb H11 Hid.
assert (U10 : U E (SOff 10 0) = button).
{ apply U_atom; [rewrite H10; unfold s32; destruct (Z.ltb_spec button (2 ^ 31)); [reflexivity | lia] | lia]. }
assert (U11 : U E (SOff 11 0) = id).
{ apply U_atom; [rewrite H11; unfold s32; destruct (Z.ltb_spec id (2 ^ 31)); [reflexivity | lia] | lia]. }
assert (L1 : Z.lor (button * 256) id = id + button * 256).
{ rewrite Z.lor_comm. apply (btn_lor_add id (button * 256) 8); [lia | lia | change (2 ^ 8) with 256; apply Z.mod_mul; lia]. }
assert (L2 : Z.lor (id + button * 256) 131072 = id + button * 256 + 131072).
{ apply (btn_lor_add _ _ 17); [lia | lia | reflexivity]. }
rewrite !U_SAlu. cbn [zalu_raw]. rewrite U10, U11, !U_lit by lia. change (Z.land 8 63) with 8.
rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 8) with 256. unfold zcanon, M64.
rewrite (Z.mod_small (button * 256)) by lia. rewrite L1. rewrite (Z.mod_small (id + button * 256)) by lia.
rewrite L2. rewrite (Z.mod_small (id + button * 256 + 131072)) by lia.
unfold KEY. rewrite (Z.mod_small (button * 256) (2 ^ 32)) by lia. rewrite L1.
change 0xffff with (Z.ones 16). rewrite Z.land_ones by lia. rewrite (Z.mod_small (id + button * 256)) by lia.
rewrite Z.lor_comm. change (2 * 65536) with 131072. rewrite L2. reflexivity.
Qed.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Lemma btn_spec_ok : forall button id on, 0 <= button <= 127 -> 0 <= id <= 63 ->
button_spec button id on = (0, Some ([0x90; u8 button; u8 (Z.lor (bit_or_0 (negb (on =? 0)) 0x40) id)],
  KEY 2 (Z.lor ((button * 256) mod 2 ^ 32) id), 0)).
Proof.
intros button id on Hb Hi. unfold button_spec. destruct (Z.ltb_spec 0x7f button); [lia|].
destruct (Z.ltb_spec 0x3f id); [lia|]. reflexivity.
Qed.
Lemma btn_spec_fail : forall button id on, 127 < button \/ 63 < id -> button_spec button id on = (E_RANGE, None).
Proof.
intros button id on H. unfold button_spec. destruct (Z.ltb_spec 0x7f button); [reflexivity|].
destruct (Z.ltb_spec 0x3f id); [reflexivity | lia].
Qed.

Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Variable B : asyms.
Variable MT : ameter_ops.
Hypothesis MTL : ameter_laws MT.
Hypothesis TL : TfibLib B.
Hypothesis LAWS : AR_laws tfibsegs B.
(* the failing return: run to `ret`, then the leaf with out kept *)
Ltac btn_fail HJ0 KE Hfail eimg Hcw HG HL :=
  cw_run cw_awr_stk; cw_keep cw_kwr_stk;
  cw_leaf ltac:(idtac; cw_kept HJ0 KE eimg ltac:(intros ? Ha; cbv beta in Ha; unfold cenc_wr, TB_button; lia)) idtac;
  rewrite (btn_spec_fail _ _ _ Hfail);
  lazymatch goal with R10 : getr _ _ = _ |- cenc_res _ ?o ?bf _ ?W _ _ =>
    apply (ceo_res_fail W _ _ _ o bf _ E_RANGE HG HL ltac:(lia) ltac:(lia) Hcw KE); ceo_a0 R10 end.
Theorem diginet_button_encode_B_holds : cdcU_button_specX tfibsegs B MT 0x855dc.
Proof using MTL TL LAWS.
unfold cdcU_button_specX.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs button id on out before HE Hab Hai Hao H13 Hoal HO.
pose proof HE as HE0.
destruct HE as (HJ0 & Hra & Hra4 & Hgp & Htp & Hal16 & Hwlo & Hwhi & Hev & Hlive).
pose proof (proj1 HJ0) as HAR. pose proof HJ0 as HJ.
destruct Hab as (Hbr & H10). destruct Hai as (Hir & H11). destruct Hao as (Honr & H12).
pose proof HO as (HD & HG & HL).
pose proof HD as (Hq & Hqn & Htd & Htw & _ & _ & _ & Hcw).
unfold coff_win, TB_button in Hcw. unfold TB_button in Hwlo.
pose proof (ceo_off_img B STK sp0 FP ly S lyc Sc own W memc mdc (spZ regs) TB_button out HAR HD) as Himg.
unfold YImgTopU.IMG_LO, YImgTopU.IMG_TOP in Himg.
pose proof Hwx_tfa as Hwx. pose proof tfib_segs_low as Hsegs.
pose proof (ceo_entry B TL LAWS 0x855dc [] 13 (13%bv) [] STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs
  TB_button out HE0 ltac:(unfold TB_button; lia) eq_refl H13 Hoal HD I) as HS.
remember (Ereg regs (cw_extra [])) as E eqn:HEq.
assert (HAE : env_agree 32 (Ereg regs (cw_extra [])) E) by (subst E; apply env_agree_refl).
assert (E1 : ew E 1 = getr regs 1) by (subst E; exact (cw_ew_reg regs [] 1 1%bv eq_refl)).
assert (B2 : bv_unsigned (ew E 2) = spZ regs) by (subst E; rewrite (cw_ew_reg regs [] 2 2%bv eq_refl); reflexivity).
assert (E10 : ew E 10 = Z_to_bv 64 (s32 button)) by (subst E; rewrite (cw_ew_reg regs [] 10 10%bv eq_refl); exact H10).
assert (E11 : ew E 11 = Z_to_bv 64 (s32 id)) by (subst E; rewrite (cw_ew_reg regs [] 11 11%bv eq_refl); exact H11).
assert (E12 : ew E 12 = Z_to_bv 64 on) by (subst E; rewrite (cw_ew_reg regs [] 12 12%bv eq_refl); exact H12).
assert (E13 : ew E 13 = Z_to_bv 64 out) by (subst E; rewrite (cw_ew_reg regs [] 13 13%bv eq_refl); exact H13).
assert (BO : bv_unsigned (ew E 13) = out) by (rewrite E13; apply unsigned_lit_small; lia).
assert (E32 : ew E 32 = Z_to_bv 64 SB) by (subst E; apply cw_ew_SB).
assert (SHOK : sh_ok tfibsegs CW_Bx [mkSHE 13 0 32] E (mrestrict (w_H W) memc)).
{ constructor; [|constructor].
  exact (cw_shent_cdst B STK sp0 FP ly S lyc Sc own W memc (spZ regs) TB_button E 13 out 32 HD E13 E32 ltac:(lia)). }
clear HEq.
assert (KE : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 16 <= a < spZ regs) ->
  aview tfibsegs (w_H W) memc a = aview tfibsegs (w_H W) memc a) by (intros; reflexivity).
unfold cfg_at. change (w64 0x855dc) with (Z_to_bv 64 0x855dc).
(* 0x855dc-0x855ec; stop at 0x855f0 bltu a5,a0 *)
cw_run cw_awr_stk. cw_keep cw_kwr_stk.
cw_branch Hb1.
all: rewrite branch_ltu_U, (btn_lt E 10 button 127 E10 ltac:(lia) ltac:(lia)) in Hb1.
- (* TAKEN: 127 < button, a0 = -11 at ret *)
  apply Z.ltb_lt in Hb1.
  btn_fail HJ0 KE (@or_introl (127 < button) (63 < id) Hb1)
    ltac:(intros a Ha Him; exact (ceo_eimg B LAWS STK sp0 FP ly S lyc Sc own W memc mdc (spZ regs) TB_button out a HAR HD Ha Him))
    Hcw HG HL.
- apply Z.ltb_ge in Hb1.
  (* 0x855f4; stop at 0x855f8 bltu a5,a1 *)
  cw_run cw_awr_stk. cw_keep cw_kwr_stk.
  cw_branch Hb2.
  all: rewrite branch_ltu_U, (btn_lt E 11 id 63 E11 ltac:(lia) ltac:(lia)) in Hb2.
  + (* TAKEN: 63 < id, a0 = -11 at ret *)
    apply Z.ltb_lt in Hb2.
    btn_fail HJ0 KE (@or_intror (127 < button) (63 < id) Hb2)
      ltac:(intros a Ha Him; exact (ceo_eimg B LAWS STK sp0 FP ly S lyc Sc own W memc mdc (spZ regs) TB_button out a HAR HD Ha Him))
      Hcw HG HL.
  + (* not taken: button <= 127, id <= 63 *)
    apply Z.ltb_ge in Hb2.
    lazymatch goal with HS0 : st_ok _ _ ?ss (restrict (w_H W) ?ms) |- _ =>
      pose proof (ceo_add3 B LAWS STK sp0 FP ly S lyc Sc own W memc mdc (spZ regs) TB_button E ss ms 13 out 3 HAR HD HS0 BO
        ltac:(lia) ltac:(intros a Ha; apply KE; lia)
        ltac:(ceo_disj ltac:(clear - Hcw Himg; lia)) ltac:(ceo_disj ltac:(clear - Hcw Himg; lia))
        ltac:(ceo_disj ltac:(clear - Hcw Himg; lia))) as HS1;
      clear HS0; rename HS1 into HS end.
    pose proof (ceo_KE_widen _ _ _ (spZ regs) out 3 KE) as KE1. clear KE. rename KE1 into KE.
    (* 0x855fc-0x856d8: the alignment check of out, the shadow base, the six checks, the stores; stop at ret *)
    cw_run ltac:(ceo_awr Htw). cw_keep ceo_kwr.
    cw_leaf ltac:(idtac; cw_kept HJ0 KE
        ltac:(intros a Ha Him; exact (ceo_eimg B LAWS STK sp0 FP ly S lyc Sc own W memc mdc (spZ regs) TB_button out a HAR HD Ha Him))
        ltac:(intros a Ha; cbv beta in Ha; unfold cenc_wr, TB_button; try unfold ceo_zone in Ha; lia))
      idtac.
    rewrite (btn_spec_ok button id on ltac:(lia) ltac:(lia)). unfold cenc_res. cbn [fst snd].
    split; [ceo_a0 R10|].
    lazymatch goal with HS0 : st_ok _ _ _ _ |- _ => ceo_chunks HS0 end.
    eapply (ceo_res_ok _ memc _ out before [0x90; u8 button; u8 (Z.lor (bit_or_0 (negb (on =? 0)) 0x40) id)]
      (KEY 2 (Z.lor ((button * 256) mod 2 ^ 32) id)) 0 HL ltac:(cbn; lia) HG).
    * intros j Hj. cbn [length] in Hj.
      destruct j as [|[|[|j]]]; [| | | lia]; cbn [nth Z.of_nat]; (eapply ceo_chunk1; [eassumption|]).
      -- rewrite U_lit by lia. reflexivity.
      -- lazymatch goal with |- U ?Ex _ mod _ = _ => exact (btn_byte1 Ex button E10 ltac:(lia)) end.
      -- lazymatch goal with |- U ?Ex _ mod _ = _ => exact (btn_byte2 Ex on id E12 Honr E11 ltac:(lia)) end.
    * eapply ceo_chunk1; [eassumption|]. rewrite U_lit by lia. reflexivity.
    * eapply ceo_chunk1; [eassumption|]. rewrite U_lit by lia. reflexivity.
    * intros j Hj. eapply ceo_chunk4; [eassumption | | exact Hj].
      lazymatch goal with |- U ?Ex _ mod _ = _ => exact (btn_key Ex button id E10 ltac:(lia) E11 ltac:(lia)) end.
    * intros a Ha.
      change (Z.of_nat (length [0x90; u8 button; u8 (Z.lor (bit_or_0 (negb (on =? 0)) 0x40) id)])) with 3 in Ha.
      apply KE; [lia | unfold ceo_zone; lia].
Qed.
End b.
